"""Focused PTY controls for the early-exit maintenance check (S123 M-5)."""

import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


PLAYER = Path(__file__).with_name("demo-player.py")


class PlaybackCompletion(unittest.TestCase):
    def play(self, script, exit_on="exit", startup_exit=False):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fake = root / "repl"
            fake.write_text(
                f"#!{sys.executable}\n"
                "import sys\n"
                f"if {startup_exit!r}: sys.exit(0)\n"
                "def prompt():\n"
                "    print('\\x1b[?2004h0+0ms; user> ', end='', flush=True)\n"
                "prompt()\n"
                "for line in sys.stdin:\n"
                "    print('\\x1b[?2004l', end='', flush=True)\n"
                f"    if line.strip() == {exit_on!r}: break\n"
                "    prompt()\n"
            )
            fake.chmod(0o755)
            demo = root / "test.demo"
            demo.write_text(script)
            return subprocess.run(
                [sys.executable, str(PLAYER), str(demo), str(fake),
                 "--run-dir", str(root)],
                env={**os.environ, "DEMO_FAST": "1"},
                capture_output=True, text=True, timeout=10,
            )

    def test_early_clean_exit_is_failure(self):
        out = self.play("exit\nafter\n")
        self.assertNotEqual(out.returncode, 0, out.stdout + out.stderr)
        self.assertNotIn("[demo complete]", out.stdout)
        self.assertIn("line 1", out.stderr)

    def test_startup_exit_is_failure(self):
        out = self.play("after\n", startup_exit=True)
        self.assertNotEqual(out.returncode, 0, out.stdout + out.stderr)

    def test_complete_input_succeeds(self):
        out = self.play("first\nsecond\n")
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertIn("[demo complete]", out.stdout)

    def test_terminal_exit_needs_no_further_prompt(self):
        out = self.play("first\nexit\n")
        self.assertEqual(out.returncode, 0, out.stderr)

    def test_quit_restarts_before_remaining_input(self):
        out = self.play("/quit\nafter\n", exit_on="/quit")
        self.assertEqual(out.returncode, 0, out.stderr)
        self.assertIn("[restarting session]", out.stdout)


if __name__ == "__main__":
    unittest.main()
