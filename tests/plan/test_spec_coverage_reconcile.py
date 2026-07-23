#!/usr/bin/env python3
"""Unit tests for the spec coverage invalidation marker (FIXME 0803)."""

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("spec_coverage_reconcile.py")
SPEC = importlib.util.spec_from_file_location("reconcile", SCRIPT)
reconcile = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = reconcile
SPEC.loader.exec_module(reconcile)


class ClearedCoverageTests(unittest.TestCase):
    def test_cleared_marker_preserves_sprint_and_prior_covers(self):
        text = "[Uncovered S116 — was tests/spec_07_traits::occurrence]\n"
        match = reconcile.CLEARED_RE.search(text)
        self.assertIsNotNone(match)
        self.assertEqual(match.group("sprint"), "116")
        self.assertEqual(match.group("was"),
                         "tests/spec_07_traits::occurrence")

    def test_scan_classifies_cleared_separately_from_pending(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            md = root / "spec" / "sample.md"
            md.parent.mkdir()
            md.write_text(
                "## 1.2 Changed requirement "
                "[Uncovered S116 — was tests/sample::old_cover]\n"
            )
            scan = reconcile.scan_spec(md, root)
            self.assertEqual(len(scan.cleared), 1)
            self.assertEqual(scan.cleared[0].anchor, "1.2")
            self.assertEqual(scan.pending, [])


if __name__ == "__main__":
    unittest.main()
