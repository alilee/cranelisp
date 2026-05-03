#!/usr/bin/env python3
"""spec_link_check.py — structural verifier for `// spec:` test annotations.

Scans top-level test files in `tests/*.rs` for `// spec:` (and `///
spec:`) annotations that trace each test back to a normative document
(`spec/NN-name.md`, `repl/spec.md`, or `design/...md`). For each
citation, opens the cited file and checks whether the cited section
anchor exists as a Markdown heading.

Two failure classes:

  MIS-CITED   — citation is well-formed and the file exists, but the
                cited section anchor cannot be located in that file.
  MALFORMED   — the annotation's cited path cannot be resolved (file
                does not exist; or no path/file extractable from the
                annotation text). Free-form notes like
                `// spec: (same anchor) — ...` are skipped, not flagged.

Exit code:
  0   all citations resolve.
  1   one or more MIS-CITED or MALFORMED.

Usage:
  python3 tests/plan/spec_link_check.py [--root <project-root>] [--verbose]

The linter does NOT verify semantic match (does the assertion test
what the spec promises) — that is a human-review concern at audit
time per memory/feedback_validate_tests_against_spec.md. This is a
structural check only.

Motivated by Wave 3.5 (Sprint 64) audit: 42 mis-cites across 7 e2e
files. See tests/plan/wave-3.5-audit.md.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass
from pathlib import Path


# ---- Annotation extraction --------------------------------------------------

# `// spec: ...` or `/// spec: ...` (allow leading whitespace and 2-3 slashes)
SPEC_ANN_RE = re.compile(r"^\s*///?\s*spec:\s*(.*?)\s*$")

# Continuation comment line (`//   ` or `///   ...`) that follows a spec line.
CONT_RE = re.compile(r"^\s*///?\s+(.*?)\s*$")

# `#[test]` attribute (start of a test fn). May appear above `fn` or above
# `#[ignore]` etc.
TEST_ATTR_RE = re.compile(r"^\s*#\[\s*test\s*\]")


@dataclass
class Citation:
    file: Path        # the .rs file the annotation lives in
    line: int         # 1-based line number of the `// spec:` line
    raw: str          # the full raw text after `spec:`
    # Parsed:
    cite_path: str | None    # e.g. "repl/spec.md", "spec/10-io.md", or None
    cite_anchor: str | None  # e.g. "1.2", "10.6.1", or "Cache directory layout"


# ---- Citation parsing -------------------------------------------------------

# Path forms recognised:
#   repl/spec.md
#   spec/NN-name.md
#   design/.../foo.md
#   foo.md  (rare; allowed)
PATH_RE = re.compile(r"(?P<path>(?:[A-Za-z0-9_./-]+\.md))")

# Shortform: "NN-name §..." or "NN-name.md §..." stripped of dir prefix.
# Recognise shortforms where NN is two digits, or "appendix-X-name".
SHORT_RE = re.compile(
    r"\b(?P<short>(?:(?:0[0-9]|1[0-9])-[A-Za-z0-9_-]+)"
    r"|(?:appendix-[a-z]-[A-Za-z0-9_-]+))\b")

# Section anchor forms:
#   §1.2  / § 1.2 / § 1.2.3
#   §"Quoted Section Name"
#   §Cache directory layout         (until em-dash, comma, or end-of-line)
ANCHOR_NUMERIC_RE = re.compile(r"§\s*(?P<num>\d+(?:\.\d+)*[a-z]?)")
ANCHOR_QUOTED_RE = re.compile(r"§\s*[\"“](?P<name>[^\"”]+)[\"”]")
ANCHOR_NAMED_RE = re.compile(r"§\s*(?P<name>[A-Za-z][^,—\-\(\n]*?)(?=[,—\-\(]|$)")


def parse_citation(raw: str) -> tuple[str | None, str | None]:
    """Extract (path, anchor) from a single `// spec:` payload.

    Returns (None, None) if neither could be parsed (malformed).
    """
    path: str | None = None
    anchor: str | None = None

    m = PATH_RE.search(raw)
    if m:
        path = m.group("path")
        # If the path is just `NN-name.md` with no directory, it's the
        # shortform spec form — promote to `spec/NN-name.md`.
        if "/" not in path and re.match(r"^\d{2}-", path):
            path = f"spec/{path}"
    else:
        # Try shortform like "08-modules §8.3" — resolve to spec/08-modules.md.
        sm = SHORT_RE.search(raw)
        if sm:
            short = sm.group("short")
            # Map historical aliases observed in legacy annotations.
            # `02-syntax` was renamed to `02-grammar`; `03-type-system` to
            # `03-types`. Probe for the file as-is first, fall back to alias.
            path = f"spec/{short}.md"

    # Anchor — try in priority order: quoted > numeric > named.
    qm = ANCHOR_QUOTED_RE.search(raw)
    if qm:
        anchor = qm.group("name").strip()
    else:
        nm = ANCHOR_NUMERIC_RE.search(raw)
        if nm:
            anchor = nm.group("num").strip()
        else:
            am = ANCHOR_NAMED_RE.search(raw)
            if am:
                candidate = am.group("name").strip()
                # Filter junk that doesn't look like a section name —
                # one or two short words is likely a real anchor; else skip.
                if 1 <= len(candidate.split()) <= 6 and len(candidate) <= 80:
                    anchor = candidate

    return path, anchor


# ---- Heading index ----------------------------------------------------------

# Captures `# 5. Foo`, `## 5.1 Foo`, `### 5.1.2 Foo`, `## Cache Key Design`.
HEADING_RE = re.compile(r"^\s*(#{1,6})\s+(?P<rest>.+?)\s*$")
HEADING_NUM_PREFIX_RE = re.compile(r"^(?P<num>\d+(?:\.\d+)*[a-z]?)\.?\s+(?P<title>.+)$")


def extract_headings(md_path: Path) -> list[tuple[str, str]]:
    """Return a list of (numeric-prefix-or-empty, full-title) for each heading.

    Both legs lower-cased for matching.
    """
    out: list[tuple[str, str]] = []
    try:
        text = md_path.read_text(encoding="utf-8")
    except FileNotFoundError:
        return out
    for raw in text.splitlines():
        m = HEADING_RE.match(raw)
        if not m:
            continue
        rest = m.group("rest")
        # Strip trailing `[Tested ...]` or `[R4 S52]` annotations.
        rest_clean = re.sub(r"\s*\[[^\]]+\]\s*$", "", rest).strip()
        nm = HEADING_NUM_PREFIX_RE.match(rest_clean)
        if nm:
            out.append((nm.group("num"), nm.group("title").lower()))
        else:
            out.append(("", rest_clean.lower()))
    return out


def anchor_matches(anchor: str, headings: list[tuple[str, str]]) -> bool:
    """True iff the anchor matches some heading.

    Numeric anchors (e.g. "10.6.1") match a heading whose numeric prefix is
    exactly that string. Named anchors match (case-insensitive) when the
    heading title equals or contains the anchor as a contiguous phrase.
    """
    a = anchor.strip().lower()
    if not a:
        return False
    # Numeric?
    if re.fullmatch(r"\d+(?:\.\d+)*[a-z]?", a):
        return any(num == a for num, _title in headings)
    # Named — accept exact title match OR title contains the phrase.
    for _num, title in headings:
        if a == title or a in title:
            return True
    return False


# ---- Walking tests/ ---------------------------------------------------------

EXCLUDE_DIRS = {"legacy", "helpers", "fixtures", "e2e", "plan",
                "sprint23", "sprint59", "sprint60", "sprint61",
                "v4_pipeline", "v4_repl_eval", "wave6_demo_repros"}


def find_test_files(tests_dir: Path) -> list[Path]:
    """Top-level `tests/*.rs` files only — no recursion into subdirs."""
    return sorted(p for p in tests_dir.glob("*.rs") if p.is_file())


def collect_citations(rs_path: Path) -> list[Citation]:
    """Scan a single .rs file for `// spec:` annotations (with continuations)."""
    out: list[Citation] = []
    try:
        text = rs_path.read_text(encoding="utf-8")
    except (FileNotFoundError, UnicodeDecodeError):
        return out
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        m = SPEC_ANN_RE.match(lines[i])
        if not m:
            i += 1
            continue
        payload = m.group(1)
        cite_line = i + 1  # 1-based
        # Greedily fold continuation lines (must look like `//   <text>`).
        j = i + 1
        while j < len(lines):
            cm = CONT_RE.match(lines[j])
            if not cm:
                break
            # Stop if the continuation looks like a new test header / attr.
            if SPEC_ANN_RE.match(lines[j]) or TEST_ATTR_RE.match(lines[j]):
                break
            payload += " " + cm.group(1)
            j += 1
        path, anchor = parse_citation(payload)
        out.append(Citation(
            file=rs_path,
            line=cite_line,
            raw=payload,
            cite_path=path,
            cite_anchor=anchor,
        ))
        i = j
    return out


# ---- Main -------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description="Verify // spec: citations in tests/*.rs resolve to real "
                    "spec sections.")
    ap.add_argument("--root", default=None,
                    help="Project root. Defaults to detecting upward from the "
                         "script location.")
    ap.add_argument("--verbose", "-v", action="store_true",
                    help="Print every citation and its disposition.")
    ap.add_argument("--scope", action="append", default=None,
                    help="Limit the scan to the given test file (name only, "
                         "no path). Repeat to specify multiple. Default: "
                         "scan every tests/*.rs.")
    args = ap.parse_args()

    if args.root:
        root = Path(args.root).resolve()
    else:
        # Walk up from this script: tests/plan/spec_link_check.py → project root.
        root = Path(__file__).resolve().parent.parent.parent

    tests_dir = root / "tests"
    if not tests_dir.is_dir():
        print(f"error: tests directory not found at {tests_dir}",
              file=sys.stderr)
        return 2

    # Heading cache, keyed by relative md path.
    heading_cache: dict[Path, list[tuple[str, str]]] = {}

    def get_headings(rel_path: str) -> list[tuple[str, str]] | None:
        md_path = (root / rel_path).resolve()
        if md_path in heading_cache:
            return heading_cache[md_path]
        if not md_path.is_file():
            return None
        h = extract_headings(md_path)
        heading_cache[md_path] = h
        return h

    miscited: list[tuple[Citation, str]] = []
    malformed: list[tuple[Citation, str]] = []
    skipped: list[tuple[Citation, str]] = []  # informational
    ok_count = 0
    total = 0

    test_files = find_test_files(tests_dir)
    if args.scope:
        keep = set(args.scope)
        test_files = [p for p in test_files if p.name in keep]
        if not test_files:
            print(f"error: --scope matched no files (available: "
                  f"{sorted(p.name for p in find_test_files(tests_dir))[:5]} ...)",
                  file=sys.stderr)
            return 2
    for rs in test_files:
        for cite in collect_citations(rs):
            total += 1
            if cite.cite_path is None:
                # No path could be parsed at all. If anchor also missing,
                # this is junk — but allow free-form notes like
                # "// spec: (same anchor) — ...".
                if "(same anchor)" in cite.raw or cite.raw.strip().startswith("("):
                    skipped.append((cite, "free-form note (no path)"))
                else:
                    malformed.append(
                        (cite, "no resolvable path/file in annotation"))
                continue
            # Path is set — try to resolve it.
            headings = get_headings(cite.cite_path)
            if headings is None:
                # Try alias fallbacks for legacy shortforms.
                alias_attempts = []
                p = cite.cite_path
                if p == "spec/02-syntax.md":
                    alias_attempts.append("spec/02-grammar.md")
                if p == "spec/03-type-system.md":
                    alias_attempts.append("spec/03-types.md")
                resolved = None
                for alt in alias_attempts:
                    h = get_headings(alt)
                    if h is not None:
                        resolved = (alt, h)
                        break
                if resolved is None:
                    malformed.append(
                        (cite, f"cited file does not exist: {cite.cite_path}"))
                    continue
                _alias, headings = resolved
                # Note: continue with anchor check against alias.
            if cite.cite_anchor is None:
                # Have a real file but no anchor — file-level citation.
                # Treat as OK (file resolves; some legacy annotations cite
                # whole files like "spec/12-runtime.md").
                ok_count += 1
                if args.verbose:
                    print(f"OK  {cite.file.name}:{cite.line}  "
                          f"{cite.cite_path} (no anchor)")
                continue
            if anchor_matches(cite.cite_anchor, headings):
                ok_count += 1
                if args.verbose:
                    print(f"OK  {cite.file.name}:{cite.line}  "
                          f"{cite.cite_path} §{cite.cite_anchor}")
            else:
                miscited.append((cite,
                                 f"anchor §{cite.cite_anchor!r} not found in "
                                 f"{cite.cite_path}"))

    # ---- Report -------------------------------------------------------------

    print(f"spec_link_check: scanned {total} citations across "
          f"{len(test_files)} test files", file=sys.stderr)
    print(f"  OK:        {ok_count}", file=sys.stderr)
    print(f"  MIS-CITED: {len(miscited)}", file=sys.stderr)
    print(f"  MALFORMED: {len(malformed)}", file=sys.stderr)
    print(f"  skipped:   {len(skipped)} (free-form / non-path notes)",
          file=sys.stderr)

    def emit(label: str, items: list[tuple[Citation, str]]) -> None:
        if not items:
            return
        print(f"\n{label} ({len(items)}):", file=sys.stderr)
        for cite, why in items:
            rel = cite.file.relative_to(root) if cite.file.is_absolute() \
                else cite.file
            print(f"  {rel}:{cite.line}: {why}", file=sys.stderr)
            print(f"      → {cite.raw[:120]}", file=sys.stderr)

    emit("MIS-CITED", miscited)
    emit("MALFORMED", malformed)

    fail = bool(miscited) or bool(malformed)
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
