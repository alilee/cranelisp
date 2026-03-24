#!/usr/bin/env python3
"""Play Cranelisp REPL .demo scripts with typing effects via a live PTY.

Usage:
    python3 demo-player.py <script.demo> [cranelisp-binary]

    # With explicit run directory (used by showcase):
    python3 demo-player.py <script.demo> <cranelisp-binary> --run-dir <dir>

The REPL runs in a clean timestamped directory under repl/demos/runs/
(or a caller-specified directory) to isolate .cache artifacts.

Interactive controls (when stdin is a TTY):
    space   pause / unpause playback
    q       quit playback immediately

Environment:
    DEMO_TYPING_MS        ms between characters (default: 30)
    DEMO_LINE_PAUSE_MS    ms after REPL response (default: 1500)
    DEMO_COMMENT_PAUSE_MS ms after comment line (default: 800)
    DEMO_FAST             if set, all delays are zero (CI mode)
"""

import os
import pty
import select
import shutil
import sys
import termios
import time
import tty
from datetime import datetime
from pathlib import Path


def env_ms(name, default):
    """Read a millisecond timing from environment, return seconds."""
    if os.environ.get("DEMO_FAST"):
        return 0.0
    return int(os.environ.get(name, default)) / 1000.0


TYPING_DELAY = env_ms("DEMO_TYPING_MS", "30")
LINE_PAUSE = env_ms("DEMO_LINE_PAUSE_MS", "1500")
COMMENT_PAUSE = env_ms("DEMO_COMMENT_PAUSE_MS", "800")

DIM = "\033[90m"
RESET = "\033[0m"


class KeyboardController:
    """Non-blocking keyboard input for pause/quit during demo playback."""

    def __init__(self):
        self.active = sys.stdin.isatty() and not os.environ.get("DEMO_FAST")
        self.paused = False
        self.quit_requested = False
        self._old_settings = None

    def __enter__(self):
        if self.active:
            self._old_settings = termios.tcgetattr(sys.stdin)
            tty.setcbreak(sys.stdin.fileno())
        return self

    def __exit__(self, *args):
        if self._old_settings is not None:
            termios.tcsetattr(sys.stdin, termios.TCSADRAIN, self._old_settings)

    def check(self):
        """Poll for keyboard input. Call frequently during delays."""
        if not self.active:
            return
        while True:
            ready, _, _ = select.select([sys.stdin], [], [], 0)
            if not ready:
                break
            ch = sys.stdin.read(1)
            if ch == ' ':
                self.paused = not self.paused
                if self.paused:
                    sys.stdout.write(f"\n{DIM}; [paused — space to resume, q to quit]{RESET}")
                    sys.stdout.flush()
                else:
                    sys.stdout.write(f"\r\033[K")  # clear the paused message
                    sys.stdout.flush()
            elif ch in ('q', 'Q'):
                self.quit_requested = True
                return

    def wait(self, seconds):
        """Sleep for the given duration, checking for pause/quit periodically."""
        if seconds <= 0:
            return
        end = time.monotonic() + seconds
        while time.monotonic() < end:
            self.check()
            if self.quit_requested:
                return
            while self.paused and not self.quit_requested:
                self.check()
                time.sleep(0.05)
            if self.quit_requested:
                return
            remaining = end - time.monotonic()
            time.sleep(min(0.05, max(0, remaining)))


def drain_output(master_fd, timeout=0.5, wait_for_prompt=False):
    """Read and display REPL output until no more data arrives.

    If wait_for_prompt is True, keeps reading until the output ends with
    the REPL prompt pattern (text ending with '> '). This prevents the
    prompt from being lost when REPL response arrives in multiple chunks.
    """
    output = []
    deadline = time.monotonic() + timeout
    while True:
        remaining = deadline - time.monotonic()
        if remaining <= 0 and not wait_for_prompt:
            break
        wait_time = min(remaining, 0.1) if remaining > 0 else 0.1
        ready, _, _ = select.select([master_fd], [], [], wait_time)
        if not ready:
            if wait_for_prompt and time.monotonic() < deadline + 5.0:
                # Check if we already have the prompt.
                joined = "".join(output)
                if joined.rstrip().endswith(">") or "> " in joined[joined.rfind("\n") + 1:] if "\n" in joined else "> " in joined:
                    break
                # Extend deadline slightly to wait for prompt.
                continue
            break
        try:
            data = os.read(master_fd, 4096)
        except OSError:
            break
        if not data:
            break
        text = data.decode(errors="replace")
        output.append(text)
        sys.stdout.write(text)
        sys.stdout.flush()
        # Reset deadline after receiving data — more may follow.
        deadline = time.monotonic() + 0.2
        if wait_for_prompt:
            # Check if prompt has appeared.
            joined = "".join(output)
            # The REPL prompt ends with "> " (with timing info before it).
            last_line = joined[joined.rfind("\n") + 1:] if "\n" in joined else joined
            if "> " in last_line and not last_line.strip().startswith(";"):
                break
    return "".join(output)


def type_slowly(text, master_fd, kb):
    """Send text to REPL character by character with delays."""
    for char in text:
        kb.check()
        if kb.quit_requested:
            return
        while kb.paused and not kb.quit_requested:
            kb.check()
            time.sleep(0.05)
        os.write(master_fd, char.encode())
        kb.wait(TYPING_DELAY)
    os.write(master_fd, b"\n")


def create_run_dir(demo_path):
    """Create a timestamped run directory for REPL cache isolation."""
    demos_dir = Path(__file__).parent
    runs_dir = demos_dir / "runs"
    runs_dir.mkdir(exist_ok=True)

    demo_name = Path(demo_path).stem
    timestamp = datetime.now().strftime("%Y-%m-%dT%H-%M-%S")
    run_dir = runs_dir / f"{timestamp}_{demo_name}"
    run_dir.mkdir()

    return run_dir


def start_repl(repl_binary, run_dir):
    """Start a REPL process with a PTY. Returns (master_fd, pid)."""
    master_fd, slave_fd = pty.openpty()
    pid = os.fork()

    if pid == 0:
        # Child: chdir to run dir, become the REPL process.
        os.close(master_fd)
        os.chdir(str(run_dir))
        os.setsid()
        os.dup2(slave_fd, 0)
        os.dup2(slave_fd, 1)
        os.dup2(slave_fd, 2)
        if slave_fd > 2:
            os.close(slave_fd)
        os.execv(repl_binary, [repl_binary])
        sys.exit(1)

    os.close(slave_fd)
    return master_fd, pid


def stop_repl(master_fd, pid):
    """Clean up a REPL process."""
    try:
        os.write(master_fd, b"\x04")
    except OSError:
        pass
    os.close(master_fd)
    try:
        os.waitpid(pid, 0)
    except ChildProcessError:
        pass


def play_demo(demo_path, repl_binary, run_dir=None):
    """Play a .demo script through the REPL via a live PTY.

    Supports trampoline: when /quit is encountered in the script,
    the REPL exits and a new one is started in the same run directory.
    The demo continues with the remaining lines in the fresh session.
    This lets demos show session restart (e.g., persistence across /quit).

    Interactive controls (when stdin is a TTY):
        space   pause / unpause playback
        q       quit playback immediately

    Args:
        demo_path: Path to the .demo script file.
        repl_binary: Path to the cranelisp binary.
        run_dir: Working directory for the REPL. If None, creates a
                 timestamped directory under repl/demos/runs/.
    """
    # Read the demo script.
    with open(demo_path) as f:
        lines = [line.rstrip("\n") for line in f]

    # Create or use the provided run directory.
    if run_dir is None:
        run_dir = create_run_dir(demo_path)
        sys.stdout.write(f"{DIM}; run dir: {run_dir}{RESET}\n")
        sys.stdout.flush()

    # Resolve binary to absolute path before chdir.
    repl_binary = shutil.which(repl_binary) or os.path.abspath(repl_binary)

    # Start the first REPL session.
    master_fd, pid = start_repl(repl_binary, run_dir)

    with KeyboardController() as kb:
        try:
            # Wait for the initial prompt (banner + prompt).
            drain_output(master_fd, timeout=2.0, wait_for_prompt=True)

            for line in lines:
                kb.check()
                if kb.quit_requested:
                    break

                if line.strip() in ("/quit", "/q"):
                    # Trampoline: send /quit, wait for exit, start fresh REPL.
                    type_slowly(line, master_fd, kb)
                    if kb.quit_requested:
                        break
                    drain_output(master_fd, timeout=1.0)
                    kb.wait(LINE_PAUSE)
                    stop_repl(master_fd, pid)

                    # Brief pause to show the session ended.
                    sys.stdout.write(f"\n{DIM}; [restarting session]{RESET}\n")
                    sys.stdout.flush()
                    kb.wait(LINE_PAUSE)
                    if kb.quit_requested:
                        # Don't start a new REPL if quitting.
                        master_fd, pid = None, None
                        break

                    # Start a new REPL in the same run directory.
                    master_fd, pid = start_repl(repl_binary, run_dir)
                    drain_output(master_fd, timeout=2.0, wait_for_prompt=True)

                elif line.startswith(";"):
                    # Comment line — visual structure for the viewer, not REPL input.
                    # Display as dimmed section header above the waiting prompt.
                    sys.stdout.write(f"\n{DIM}{line}{RESET}\n")
                    sys.stdout.flush()
                    kb.wait(COMMENT_PAUSE)

                elif line.strip() == "":
                    # Blank line — visual pause for the viewer.
                    kb.wait(COMMENT_PAUSE / 2)

                else:
                    # REPL input — type slowly, then show response + prompt.
                    type_slowly(line, master_fd, kb)
                    if kb.quit_requested:
                        break
                    drain_output(master_fd, timeout=1.0, wait_for_prompt=True)
                    kb.wait(LINE_PAUSE)

            # Clean exit.
            sys.stdout.write(f"\n{DIM}; [demo complete]{RESET}\n")
            sys.stdout.flush()

        finally:
            if master_fd is not None and pid is not None:
                stop_repl(master_fd, pid)


def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <script.demo> [cranelisp-binary] [--run-dir <dir>]")
        sys.exit(1)

    demo_path = sys.argv[1]
    repl_binary = "cranelisp"
    run_dir = None

    # Parse remaining arguments.
    i = 2
    while i < len(sys.argv):
        if sys.argv[i] == "--run-dir" and i + 1 < len(sys.argv):
            run_dir = Path(sys.argv[i + 1])
            run_dir.mkdir(parents=True, exist_ok=True)
            i += 2
        else:
            repl_binary = sys.argv[i]
            i += 1

    if not os.path.exists(demo_path):
        print(f"Error: {demo_path} not found")
        sys.exit(1)

    play_demo(demo_path, repl_binary, run_dir=run_dir)


if __name__ == "__main__":
    main()
