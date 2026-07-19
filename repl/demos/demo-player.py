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
import re
import select
import shutil
import sys
import termios
import time
import tty
from datetime import datetime
from pathlib import Path


# The REPL's line editor wraps every primary prompt in bracketed-paste toggles:
# `\x1b[?2004h` (enable) is emitted immediately BEFORE the prompt frame and
# nowhere else, and `\x1b[?2004l` (disable) is emitted the instant input is
# submitted. The prompt frame itself is `{compile_ms}+{eval_ms}ms; {module}> `
# (repl/spec.md §2.1). Together these give a definitive "REPL is idle, waiting
# for input" sentinel — far more reliable than scanning for a bare `> `, which
# also appears in echoed input like `(> 3 2)` and in result values. Matching on
# the loose `> ` was the leading-chars-dropped race: drain returned while the
# REPL was still echoing/evaluating, so the next keystrokes landed in a busy
# process.
PROMPT_ENABLE = "\x1b[?2004h"
PROMPT_DISABLE = "\x1b[?2004l"
# Any CSI escape sequence (line-clear `\x1b[K`, cursor-forward `\x1b[13C`,
# colour, the bracketed-paste toggles themselves, ...).
ANSI_RE = re.compile(r"\x1b\[[0-9;?]*[a-zA-Z]")
# The REPL is awaiting input when the stripped tail ends at EITHER a primary
# prompt frame — digits, `+`, digits, `ms; `, a module name (no space, no `>`),
# then `> ` (repl/spec.md §2.1) — OR a continuation prompt `...` (§2.2), emitted
# when a multi-line form has unmatched brackets. Both are quiescent "type the
# next line" states; a multi-line definition steps through several continuations
# before the closing line yields the primary frame.
PROMPT_TAIL_RE = re.compile(r"(?:\d+\+\d+ms;\s+[^\s>]+>|\.\.\.)\s*$")


def at_definitive_prompt(buf):
    """True iff buf ends at a prompt awaiting input (primary OR continuation).

    Requires the last bracketed-paste toggle to be ENABLE (not a submitted
    line still being evaluated) AND the tail — once the line editor's escape
    noise is stripped — to end at a fully-rendered prompt frame. This is a
    real quiescence check: a prompt is the last thing the REPL emits before
    blocking on input, so a prompt frame at end-of-buffer means it is safe to
    type again. The continuation prompt (`...`) carries the same ENABLE marker,
    so multi-line forms advance without stalling on the 15s cap per line.

    The stripping matters: after drawing the prompt the editor emits a cursor
    reposition (`\\r\\x1b[13C`), so the raw buffer ends with that, never with a
    bare `> ` or `...`. Removing CSI sequences and carriage returns exposes the
    frame.
    """
    enable = buf.rfind(PROMPT_ENABLE)
    if enable == -1:
        return False
    if buf.rfind(PROMPT_DISABLE) > enable:
        # A line was submitted after the last prompt appeared — the REPL is
        # busy evaluating; the next prompt has not yet been rendered.
        return False
    tail = buf[enable + len(PROMPT_ENABLE):]
    clean = ANSI_RE.sub("", tail).replace("\r", "")
    return bool(PROMPT_TAIL_RE.search(clean))


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


def drain_output(master_fd, timeout=0.5, wait_for_prompt=False, prompt_timeout=15.0):
    """Read and display REPL output.

    Two modes:

    - wait_for_prompt=False: read until no data has arrived for `timeout`
      seconds (idle drain — used after /quit and other non-prompting output).
    - wait_for_prompt=True: read until the buffer ends at a definitive primary
      prompt (see at_definitive_prompt). This is the quiescence gate that keeps
      the caller from typing into a busy REPL. `prompt_timeout` is an absolute
      safety cap so a wedged REPL cannot hang playback forever.
    """
    output = []
    idle_deadline = time.monotonic() + timeout
    hard_deadline = time.monotonic() + prompt_timeout
    while True:
        if wait_for_prompt and at_definitive_prompt("".join(output)):
            break
        now = time.monotonic()
        if wait_for_prompt:
            if now > hard_deadline:
                break
            wait_time = 0.1
        else:
            remaining = idle_deadline - now
            if remaining <= 0:
                break
            wait_time = min(remaining, 0.1)
        ready, _, _ = select.select([master_fd], [], [], wait_time)
        if not ready:
            continue
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
        # Reset the idle window after receiving data — more may follow. Reset
        # the hard cap too: as long as the REPL is emitting output it is making
        # progress (a long solve that prints incrementally must not be capped);
        # the cap only fires after genuine silence with no prompt in sight.
        now = time.monotonic()
        idle_deadline = now + timeout
        hard_deadline = now + prompt_timeout
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
    """Create a unique run directory for REPL cache isolation.

    The name carries microsecond-resolution timestamp AND pid so that
    back-to-back runs (a stability sweep replays the same demo many times
    within the same second) never collide. A counter loop is a final
    belt-and-suspenders guard against the astronomically-unlikely tie.
    """
    demos_dir = Path(__file__).parent
    runs_dir = demos_dir / "runs"
    runs_dir.mkdir(exist_ok=True)

    demo_name = Path(demo_path).stem
    stamp = datetime.now().strftime("%Y-%m-%dT%H-%M-%S-%f")
    pid = os.getpid()
    counter = 0
    while True:
        suffix = f"-{counter}" if counter else ""
        run_dir = runs_dir / f"{stamp}_{pid}_{demo_name}{suffix}"
        try:
            run_dir.mkdir()
            return run_dir
        except FileExistsError:
            counter += 1


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
