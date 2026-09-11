#!/usr/bin/env python3
"""Independent candidate-CLI acceptance for the shared document checker.

The candidate owns TOML, discovery and reference parsing. This driver creates
one small real Git working tree, invokes the public CLI, and inspects its JSON
contract. Before implementation exists, absence is reported as a separate
setup result rather than mislabelled as a behavioral failure.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest


WORKSPACE = Path(__file__).resolve().parents[2]
FIXTURE = WORKSPACE / "tests/fixtures/document_checker_cli"
CANDIDATE: Path


def git(root: Path, *args: str) -> str:
    completed = subprocess.run(
        ["git", *args],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if completed.returncode != 0:
        raise AssertionError(
            f"git {' '.join(args)} failed ({completed.returncode})\n"
            f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        )
    return completed.stdout.strip()


def project() -> tuple[tempfile.TemporaryDirectory[str], Path]:
    temporary = tempfile.TemporaryDirectory(prefix="s122-document-checker-")
    root = Path(temporary.name) / "project"
    shutil.copytree(FIXTURE, root)
    for template in sorted(root.rglob("*.fixture")):
        template.rename(template.with_suffix(""))
    git(root, "init", "-q")
    git(root, "config", "user.name", "Document Checker Fixture")
    git(root, "config", "user.email", "fixture@example.invalid")
    git(root, "add", ".")
    git(root, "commit", "-qm", "fixture")
    head = git(root, "rev-parse", "HEAD")
    git(root, "update-index", "--add", "--cacheinfo", f"160000,{head},vendor/package")
    return temporary, root


def invoke_raw(
    root: Path, *extra: str, output_format: str = "json"
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [
            sys.executable,
            str(CANDIDATE),
            "--root",
            str(root),
            "--config",
            "standing-documents.toml",
            "--format",
            output_format,
            *extra,
        ],
        cwd=root,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )


def invoke(root: Path, *extra: str) -> tuple[int, dict[str, object], str]:
    completed = invoke_raw(root, *extra)
    detail = f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
    try:
        report = json.loads(completed.stdout)
    except json.JSONDecodeError as error:
        raise AssertionError(
            f"candidate did not emit its JSON report (exit {completed.returncode}): {error}\n{detail}"
        ) from error
    if not isinstance(report, dict):
        raise AssertionError(f"candidate JSON root must be an object\n{detail}")
    return completed.returncode, report, detail


def corpus_paths(report: dict[str, object]) -> set[str]:
    corpus = report.get("corpus")
    if not isinstance(corpus, list):
        raise AssertionError(f"JSON report must contain a corpus list: {report}")
    paths: set[str] = set()
    for item in corpus:
        if isinstance(item, str):
            paths.add(item)
        elif isinstance(item, dict) and isinstance(item.get("path"), str):
            paths.add(item["path"])
        else:
            raise AssertionError(f"corpus member must expose a path: {item!r}")
    return paths


def findings(report: dict[str, object]) -> list[dict[str, object]]:
    value = report.get("findings")
    if not isinstance(value, list) or not all(isinstance(item, dict) for item in value):
        raise AssertionError(f"JSON report must contain a findings object list: {report}")
    return value  # type: ignore[return-value]


def matching_findings(report: dict[str, object], needle: str) -> list[dict[str, object]]:
    return [item for item in findings(report) if needle in json.dumps(item, sort_keys=True)]


class CandidateCliAcceptance(unittest.TestCase):
    def test_clean_graph_live_references_historical_count_and_status_zero(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        code, report, detail = invoke(root)
        self.assertEqual(code, 0, detail)
        self.assertEqual(report.get("schema_version"), 1, detail)
        self.assertEqual(report.get("root"), str(root.resolve()), detail)
        self.assertIn("docs/guide.md", corpus_paths(report), detail)
        self.assertEqual(findings(report), [], detail)
        self.assertTrue(report.get("enabled_rules"), detail)
        self.assertTrue(any("suppress" in key.lower() for key in report), detail)
        rendered = json.dumps(report, sort_keys=True).lower()
        self.assertIn("historical", rendered, detail)
        self.assertIn("excluded", rendered, detail)

    def test_discovery_ignores_declarations_and_respects_ignore_and_gitlink(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        (root / "tracked-extra.md").write_text("# Tracked but undeclared\n", encoding="utf-8")
        git(root, "add", "tracked-extra.md")
        (root / "untracked-extra.md").write_text("# Untracked and undeclared\n", encoding="utf-8")
        (root / "vendor/package").mkdir(parents=True)
        (root / "vendor/package/inside.md").write_text("# Foreign package file\n", encoding="utf-8")

        list_code, listed, list_detail = invoke(root, "--list-docs")
        self.assertEqual(list_code, 0, list_detail)
        paths = corpus_paths(listed)
        self.assertIn("tracked-extra.md", paths, list_detail)
        self.assertIn("untracked-extra.md", paths, list_detail)
        self.assertNotIn("ignored.md", paths, list_detail)
        self.assertFalse(any(path.startswith("vendor/package/") for path in paths), list_detail)

        code, report, detail = invoke(root)
        self.assertEqual(code, 1, detail)
        for path in ("tracked-extra.md", "untracked-extra.md"):
            observed = matching_findings(report, path)
            self.assertTrue(observed, f"missing finding for {path}\n{detail}")
            self.assertTrue(
                any("establish" in str(item.get("rule", "")).lower() for item in observed),
                f"{path} must fail establishment, not an unrelated rule\n{detail}",
            )

    def test_live_exemption_still_checks_reference_and_resolution_clears_it(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        note = root / "notes/exempt.md"
        original = note.read_text(encoding="utf-8")
        note.write_text(original + "\n[Broken live target](missing-live.md)\n", encoding="utf-8")
        code, report, detail = invoke(root)
        self.assertEqual(code, 1, detail)
        self.assertTrue(matching_findings(report, "missing-live.md"), detail)

        (root / "notes/missing-live.md").write_text("# Resolved live target\n", encoding="utf-8")
        fixed_code, fixed, fixed_detail = invoke(root)
        self.assertEqual(fixed_code, 0, fixed_detail)
        self.assertEqual(findings(fixed), [], fixed_detail)

    def test_reference_and_source_guards_report_independent_targets(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\n[Missing path](missing.md)\n"
            + "[Missing anchor](../CLAUDE.md#absent-heading)\n"
            + "The missing section is `CLAUDE.md` §Absent section.\n"
            + "The ambiguous shorthand is `topic.md` §Shared topic.\n",
            encoding="utf-8",
        )
        source = root / "src/lib.rs"
        source.write_text(
            source.read_text(encoding="utf-8")
            + "\n//! Missing path: `src/absent.rs`.\n"
            + "//! Bad line: `src/lib.rs:999`.\n"
            + "//! Bad symbol: `src/lib.rs::absent_fixture_symbol`.\n",
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 1, detail)
        for target in (
            "missing.md",
            "absent-heading",
            "Absent section",
            "topic.md",
            "src/absent.rs",
            "src/lib.rs:999",
            "absent_fixture_symbol",
        ):
            self.assertTrue(matching_findings(report, target), f"missing independent {target}\n{detail}")
        ambiguous = matching_findings(report, "topic.md")
        self.assertTrue(
            any("ambig" in json.dumps(item, sort_keys=True).lower() for item in ambiguous),
            f"ambiguous shorthand must not resolve to a convenient match\n{detail}",
        )

    def test_finding_identity_is_stable_and_invalid_config_is_status_two(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        (root / "untracked-extra.md").write_text("# Untracked and undeclared\n", encoding="utf-8")
        first_code, first, first_detail = invoke(root)
        second_code, second, second_detail = invoke(root)
        self.assertEqual((first_code, second_code), (1, 1), first_detail + second_detail)
        first_raw = [item.get("identity") for item in findings(first)]
        second_raw = [item.get("identity") for item in findings(second)]
        self.assertTrue(first_raw and all(isinstance(item, str) for item in first_raw), first_detail)
        self.assertTrue(second_raw and all(isinstance(item, str) for item in second_raw), second_detail)
        first_ids = sorted(first_raw)
        second_ids = sorted(second_raw)
        self.assertEqual(first_ids, second_ids, first_detail + second_detail)

        config = root / "standing-documents.toml"
        config.write_text(
            config.read_text(encoding="utf-8").replace(
                'root_memory = "CLAUDE.md"', 'root_memory = "../outside.md"'
            ),
            encoding="utf-8",
        )
        invalid = invoke_raw(root)
        invalid_detail = f"stdout:\n{invalid.stdout}\nstderr:\n{invalid.stderr}"
        self.assertEqual(invalid.returncode, 2, invalid_detail)

    def test_non_reference_tokens_are_ignored_but_a_missing_link_is_reported(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        (root / "sprints/actions").mkdir(parents=True)
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\nA field access may use `self.impl_registry`.\n"
            + "The example amount is `$5.25`.\n"
            + "The retired role was `/port`.\n"
            + "Action filenames follow this explicitly labelled pattern:\n\n"
            + "```text\n"
            + "sprints/actions/ACT-NNNN-short-name.md\n"
            + "```\n"
            + "[Missing control](missing-control.md)\n",
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 1, detail)
        self.assertTrue(matching_findings(report, "missing-control.md"), detail)
        self.assertFalse(matching_findings(report, "self.impl_registry"), detail)
        self.assertFalse(matching_findings(report, "$5.25"), detail)
        self.assertFalse(matching_findings(report, "/port"), detail)
        self.assertFalse(matching_findings(report, "ACT-NNNN-short-name.md"), detail)

    def test_magic_heading_bold_list_and_table_section_forms_resolve(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        topic = root / "docs/one/topic.md"
        topic.write_text(
            topic.read_text(encoding="utf-8")
            + "\n## Complete crossing graph gives a stable result — details\n"
            + "\n**Not settings.** This label opens a paragraph.\n"
            + "\n- **List item label.** This label opens a list item.\n"
            + "\n| Term label | Meaning |\n"
            + "|---|---|\n"
            + "| value | example |\n",
            encoding="utf-8",
        )
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\nThe heading is `one/topic.md` §Complete crossing graph gives.\n"
            + "The paragraph is `one/topic.md` §Not settings.\n"
            + "The list item is `one/topic.md` §List item label.\n"
            + "The table label is `one/topic.md` §Term label.\n",
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 0, detail)
        self.assertEqual(findings(report), [], detail)

    def test_section_label_is_resolved_only_in_its_named_target(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\n| Guide-only label | This belongs to the citing document. |\n"
            + "|---|---|\n"
            + "The target must not borrow `one/topic.md` §Guide-only label.\n",
            encoding="utf-8",
        )
        bad_code, bad_report, bad_detail = invoke(root)
        self.assertEqual(bad_code, 1, bad_detail)
        self.assertTrue(matching_findings(bad_report, "Guide-only label"), bad_detail)

    def test_magic_numbered_composite_and_gloss_section_forms_resolve(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        topic = root / "docs/one/topic.md"
        topic.write_text(
            topic.read_text(encoding="utf-8")
            + "\n## 10. The command surface\n"
            + "\n### Two guards over the working tree\n"
            + "\n## A second neutral seam awaiting approval: configuration resolution\n",
            encoding="utf-8",
        )
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\nThe guard contract is `one/topic.md` §10 §Two guards over the working\n"
            + "tree.\n"
            + "The seam is `one/topic.md` §A second neutral seam awaiting approval: the\n"
            + "adapter remains bounded.\n",
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 0, detail)
        self.assertEqual(findings(report), [], detail)

    def test_bare_memory_reference_uses_the_nearest_applicable_memory(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        memory = root / "docs/CLAUDE.md"
        memory.write_text(
            memory.read_text(encoding="utf-8") + "\n## Protected values\n",
            encoding="utf-8",
        )
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\nThe local rule is `CLAUDE.md` §Protected values.\n",
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 0, detail)
        self.assertEqual(findings(report), [], detail)

    def test_equivalent_missing_target_spellings_share_one_identity(self) -> None:
        identities: list[str] = []
        for spelling in ("absent.md", "missing/../absent.md"):
            temporary, root = project()
            self.addCleanup(temporary.cleanup)
            guide = root / "docs/guide.md"
            guide.write_text(
                guide.read_text(encoding="utf-8")
                + f"\n[Normalized missing target]({spelling})\n",
                encoding="utf-8",
            )
            code, report, detail = invoke(root)
            self.assertEqual(code, 1, detail)
            observed = matching_findings(report, "absent.md")
            self.assertEqual(len(observed), 1, detail)
            identity = observed[0].get("identity")
            self.assertIsInstance(identity, str, detail)
            identities.append(str(identity))
        self.assertEqual(identities[0], identities[1])

    def test_unreadable_discovered_input_is_inspection_failure(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        note = root / "notes/exempt.md"
        note.chmod(0)
        completed = invoke_raw(root)
        detail = f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        self.assertEqual(completed.returncode, 2, detail)

    def test_existing_non_text_source_path_is_checked_without_decoding_it(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        executable = root / "src/tool"
        executable.write_bytes(b"\x7fELF\x00\xff fixture executable")
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\n`src/tool`, clean run):\n\n"
            + "**Face 1 — the result remains visible (§1.3).**\n",
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 0, detail)
        self.assertEqual(findings(report), [], detail)

    def test_historical_reference_policy_is_valid_for_an_established_class(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        config = root / "standing-documents.toml"
        config.write_text(
            config.read_text(encoding="utf-8").replace(
                'disposition = "exempt"\nreason = "Dated records preserve',
                'disposition = "established"\nreason = "Dated records preserve',
                1,
            ),
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 0, detail)
        self.assertEqual(findings(report), [], detail)
        suppression = report.get("suppression_status")
        self.assertIsInstance(suppression, dict, detail)
        self.assertEqual(suppression.get("historical_excluded"), 1, detail)

    def test_declared_non_markdown_text_document_sections_are_checked(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        target = root / "docs/notes.txt"
        target.write_text("Fixture notes\n\n## Details\n", encoding="utf-8")
        memory = root / "docs/CLAUDE.md"
        memory.write_text(
            memory.read_text(encoding="utf-8")
            + "\n`docs/notes.txt` supplies a non-Markdown section target.\n",
            encoding="utf-8",
        )
        config = root / "standing-documents.toml"
        config.write_text(
            config.read_text(encoding="utf-8")
            + "\n[[document]]\n"
            + 'path = "docs/notes.txt"\n'
            + 'kind = "standing"\n'
            + 'owner = "docs"\n'
            + 'purpose = "Supplies a non-Markdown section target."\n'
            + 'established_by = "docs/CLAUDE.md"\n',
            encoding="utf-8",
        )
        guide = root / "docs/guide.md"
        original = guide.read_text(encoding="utf-8")
        guide.write_text(original + "\nThe detail is `notes.txt` §Details.\n", encoding="utf-8")
        good_code, good_report, good_detail = invoke(root)
        self.assertEqual(good_code, 0, good_detail)
        self.assertEqual(findings(good_report), [], good_detail)

        guide.write_text(original + "\nThe detail is `notes.txt` §Missing.\n", encoding="utf-8")
        bad_code, bad_report, bad_detail = invoke(root)
        self.assertEqual(bad_code, 1, bad_detail)
        observed = matching_findings(bad_report, "Missing")
        self.assertEqual(len(observed), 1, bad_detail)
        self.assertEqual(observed[0].get("rule"), "document-section", bad_detail)

    def test_relative_establishment_link_with_directory_is_resolved_beside_memory(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        nested = root / "docs/nested/guide.md"
        nested.parent.mkdir()
        nested.write_text("# Nested guide\n", encoding="utf-8")
        memory = root / "docs/CLAUDE.md"
        memory.write_text(
            memory.read_text(encoding="utf-8")
            + "\n[Nested guide](nested/guide.md) is the nested fixture guide.\n",
            encoding="utf-8",
        )
        config = root / "standing-documents.toml"
        config.write_text(
            config.read_text(encoding="utf-8")
            + "\n[[document]]\n"
            + 'path = "docs/nested/guide.md"\n'
            + 'kind = "standing"\n'
            + 'owner = "docs"\n'
            + 'purpose = "The nested fixture guide."\n'
            + 'established_by = "docs/CLAUDE.md"\n',
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 0, detail)
        self.assertEqual(findings(report), [], detail)

    def test_python_module_and_function_docstrings_are_reference_inputs(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        source = root / "src/docstrings.py"
        source.write_text(
            source.read_text(encoding="utf-8").replace(
                "docs/guide.md", "docs/missing-docstring.md"
            ),
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 1, detail)
        observed = matching_findings(report, "docs/missing-docstring.md")
        self.assertTrue(observed, detail)
        self.assertTrue(
            all(item.get("rule") == "source-path" for item in observed), detail
        )

    def test_optional_package_declaration_requires_a_gitlink(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        git(root, "update-index", "--force-remove", "vendor/package")
        missing_link_code, missing_link, missing_link_detail = invoke(root)
        self.assertEqual(missing_link_code, 1, missing_link_detail)
        self.assertTrue(matching_findings(missing_link, "vendor/package"), missing_link_detail)

    def test_absent_optional_package_target_is_explicitly_unverified(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\n[Optional package document](../vendor/package/guide.md)\n",
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 1, detail)
        self.assertTrue(matching_findings(report, "vendor/package/guide.md"), detail)
        status = report.get("reference_status")
        self.assertIsInstance(status, dict, detail)
        self.assertEqual(status.get("unverified"), 1, detail)  # type: ignore[union-attr]

    def test_optional_gitlink_distinguishes_deinitialized_and_initialized_trees(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        (root / "vendor/package").mkdir(parents=True)
        clean_code, clean, clean_detail = invoke(root)
        self.assertEqual(clean_code, 0, clean_detail)
        self.assertEqual(findings(clean), [], clean_detail)

        (root / "vendor/package/.git").write_text(
            "gitdir: ../.git/modules/vendor/package\n", encoding="utf-8"
        )
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\n[Missing initialized package file](../vendor/package/missing.md)\n",
            encoding="utf-8",
        )
        code, report, detail = invoke(root)
        self.assertEqual(code, 1, detail)
        self.assertTrue(matching_findings(report, "vendor/package/missing.md"), detail)
        status = report.get("reference_status")
        self.assertIsInstance(status, dict, detail)
        self.assertEqual(status.get("unverified"), 0, detail)  # type: ignore[union-attr]

    def test_text_report_preserves_counts_stale_identity_and_duplicate_locations(self) -> None:
        temporary, root = project()
        self.addCleanup(temporary.cleanup)
        guide = root / "docs/guide.md"
        guide.write_text(
            guide.read_text(encoding="utf-8")
            + "\n[Repeated missing target](repeated-missing.md)\n"
            + "[Repeated missing target](repeated-missing.md)\n"
            + "Future: [proposed target](future.md)\n",
            encoding="utf-8",
        )
        lines = guide.read_text(encoding="utf-8").splitlines()
        locations = [
            index for index, line in enumerate(lines, start=1)
            if "Repeated missing target" in line
        ]
        baseline = root / "stale-baseline.txt"
        baseline.write_text("stale-test-identity\n", encoding="utf-8")
        completed = invoke_raw(
            root,
            "--baseline",
            baseline.name,
            output_format="text",
        )
        detail = f"stdout:\n{completed.stdout}\nstderr:\n{completed.stderr}"
        self.assertEqual(completed.returncode, 1, detail)
        rendered = completed.stdout.lower()
        missing: list[str] = []
        if "historical" not in rendered:
            missing.append("historical exclusion count")
        if "proposed" not in rendered:
            missing.append("proposed-reference count")
        if "stale-test-identity" not in completed.stdout:
            missing.append("stale baseline identity")
        for line in locations:
            if f"docs/guide.md:{line}" not in completed.stdout:
                missing.append(f"duplicate location docs/guide.md:{line}")
        self.assertEqual(missing, [], f"text report omitted: {missing}\n{detail}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--candidate",
        type=Path,
        default=WORKSPACE / ".agents/tools/check_documents.py",
    )
    args = parser.parse_args()
    global CANDIDATE
    CANDIDATE = args.candidate.resolve()
    if not CANDIDATE.is_file():
        print(
            f"CANDIDATE ABSENT: {CANDIDATE}\n"
            "Behavioral CLI validation has not run; implement the approved shared tool first.",
            file=sys.stderr,
        )
        return 2
    suite = unittest.defaultTestLoader.loadTestsFromTestCase(CandidateCliAcceptance)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
