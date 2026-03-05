#!/usr/bin/env python3
"""Play Cranelisp REPL .demo scripts with typing effects.

Usage:
    python3 demo-player.py <script.demo> [cranelisp-binary]

The REPL runs in a clean timestamped directory under tests/repl/demos/runs/
to isolate .cache artifacts. Each run creates a new directory like:
    runs/2026-03-05T14-30-00_ring1/

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
import time
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


def drain_output(master_fd, timeout=0.5):
    """Read and display REPL output until no more data arrives."""
    output = []
    while True:
        ready, _, _ = select.select([master_fd], [], [], timeout)
        if not ready:
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
        # After first chunk, use shorter timeout for remaining data.
        timeout = 0.1
    return "".join(output)


def type_slowly(text, master_fd):
    """Send text to REPL character by character with delays."""
    for char in text:
        os.write(master_fd, char.encode())
        time.sleep(TYPING_DELAY)
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


def play_demo(demo_path, repl_binary):
    """Play a .demo script through the REPL."""
    # Read the demo script.
    with open(demo_path) as f:
        lines = [line.rstrip("\n") for line in f]

    # Create a clean run directory for cache isolation.
    run_dir = create_run_dir(demo_path)
    sys.stdout.write(f"{DIM}; run dir: {run_dir}{RESET}\n")
    sys.stdout.flush()

    # Resolve binary to absolute path before chdir.
    repl_binary = shutil.which(repl_binary) or os.path.abspath(repl_binary)

    # Start the REPL with a pty for interactive control.
    master_fd, slave_fd = pty.openpty()
    pid = os.fork()

    if pid == 0:
        # Child: chdir to run dir, become the REPL process.
        os.close(master_fd)
        os.chdir(run_dir)
        os.setsid()
        os.dup2(slave_fd, 0)
        os.dup2(slave_fd, 1)
        os.dup2(slave_fd, 2)
        if slave_fd > 2:
            os.close(slave_fd)
        os.execv(repl_binary, [repl_binary])
        sys.exit(1)

    # Parent: drive the demo.
    os.close(slave_fd)

    try:
        # Wait for the initial prompt.
        drain_output(master_fd, timeout=2.0)

        for line in lines:
            if line.startswith(";"):
                # Comment line — display as dimmed section header.
                sys.stdout.write(f"\n{DIM}{line}{RESET}\n")
                sys.stdout.flush()
                time.sleep(COMMENT_PAUSE)

            elif line.strip() == "":
                # Blank line — brief pause.
                time.sleep(COMMENT_PAUSE / 2)

            else:
                # REPL input — type slowly, then show response.
                type_slowly(line, master_fd)
                drain_output(master_fd, timeout=1.0)
                time.sleep(LINE_PAUSE)

        # Clean exit.
        sys.stdout.write(f"\n{DIM}; [demo complete]{RESET}\n")
        sys.stdout.flush()

    finally:
        # Send Ctrl-D to exit the REPL, then clean up.
        try:
            os.write(master_fd, b"\x04")
        except OSError:
            pass
        os.close(master_fd)
        try:
            os.waitpid(pid, 0)
        except ChildProcessError:
            pass


def main():
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} <script.demo> [cranelisp-binary]")
        sys.exit(1)

    demo_path = sys.argv[1]
    repl_binary = sys.argv[2] if len(sys.argv) > 2 else "cranelisp"

    if not os.path.exists(demo_path):
        print(f"Error: {demo_path} not found")
        sys.exit(1)

    play_demo(demo_path, repl_binary)


if __name__ == "__main__":
    main()
