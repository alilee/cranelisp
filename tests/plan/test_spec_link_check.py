#!/usr/bin/env python3
"""Unit tests for split-REPL logical citation resolution."""

import importlib.util
import sys
import tempfile
import unittest
from pathlib import Path


SCRIPT = Path(__file__).with_name("spec_link_check.py")
SPEC = importlib.util.spec_from_file_location("spec_link_check", SCRIPT)
checker = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = checker
SPEC.loader.exec_module(checker)


class ReplAliasTests(unittest.TestCase):
    def test_alias_finds_normative_leaf_but_not_index(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            leaves = root / "repl" / "spec"
            leaves.mkdir(parents=True)
            (leaves / "index.md").write_text("## 99. Navigation only\n")
            (leaves / "18-redefinition.md").write_text(
                "## 18. Redefinition\n### 18.2 Blocking Dependents\n"
            )
            headings, duplicates = checker.repl_alias_headings(root)
            self.assertTrue(checker.anchor_matches("18.2", headings))
            self.assertFalse(checker.anchor_matches("18.99", headings))
            self.assertFalse(checker.anchor_matches("99", headings))
            self.assertEqual(duplicates, [])

    def test_duplicate_numeric_heading_is_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            leaves = root / "repl" / "spec"
            leaves.mkdir(parents=True)
            (leaves / "01-one.md").write_text("## 1. First\n")
            (leaves / "01-two.md").write_text("## 1. Second\n")
            _headings, duplicates = checker.repl_alias_headings(root)
            self.assertEqual(duplicates, ["1"])


if __name__ == "__main__":
    unittest.main()
