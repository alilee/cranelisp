#!/usr/bin/env python3
"""verify-citations.py — mechanical record-vs-source drift detector.

The project's documents cite source constantly: FIXME `refers_to:` frontmatter,
design-doc loci, crate `CLAUDE.md` pointers, plan rows. Those citations decay
silently. METHOD §3.3 makes "verify the claim against its `refers_to` source"
the binding first act of any FIXME disposition — but a discipline that depends
on someone remembering is not a mechanism. This is the mechanism.

It is deliberately narrow. Three checks, and they are exactly this much:

  1. PATH    — a cited repository path exists.
  2. LINE    — a `path:N` or `path:N-M` citation names a line inside the file.
  3. SYMBOL  — a `path::symbol` or `bare_file.rs::symbol` citation names an
               identifier that occurs *somewhere in the text* of that file.

WHAT IT CATCHES, with real instances from this repo's record:

  * a citation to a file that does not exist — the ownership option paper
    scoped a whole tranche at `marshal.rs` in a crate that has no `marshal.rs`
  * a symbol cited against a file that never mentions it — FIXME 0708 cites
    `ast_builder.rs::try_consume_annotation`, which lives only in a test; FIXME
    0782 cites a test function that exists nowhere in the tree
  * line numbers drifted past end of file — six in one crate `CLAUDE.md` at the
    S118 audit; `src/worker.rs:4163` against a 2,704-line file

WHAT IT DOES NOT CATCH — stated plainly, because an overstated instrument is
worse than a narrow one:

  * **"the symbol is mentioned here but defined elsewhere."** SYMBOL is a
    substring test, not a definition test. FIXME 0917 cited
    `fn_compiler.rs::protect_return_value` when the definition has only ever
    been in `rc_emission.rs` — and this check PASSES it, because
    `fn_compiler.rs` calls the function ten times. Catching that needs a
    definition-site test (a `fn <name>` / `struct <name>` scan), which is not
    implemented.
  * **a documented API with no implementation.** `SymbolTable::write_structural_decls`
    is cited at two sites and implemented nowhere — but the string does occur in
    both files (in the comments citing it), so a substring test cannot see it.
    Catching that needs the same definition-site test.
  * **whether the cited line still means what the document claims.** That is
    semantic and stays human. This tool narrows the human's job; it does not
    remove it.

Usage:
    scripts/verify-citations.py [--fix-hints] [--json] [PATH ...]

Exit status is 1 if any citation fails, so it can gate a commit or a test.
With no PATH arguments it scans the documentation corpus (see DOC_GLOBS).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# Documentation corpora that cite source.
DOC_GLOBS = [
    "design/**/*.md",
    "audits/*.md",
    "tests/plan/*.md",
    "spec/*.md",
    "repl/*.md",
    "CLAUDE.md",
    "**/CLAUDE.md",
]

# Source trees a citation may legitimately point into.
SOURCE_ROOTS = ("src/", "crates/", "tests/", "platforms/", "stdlib/", "examples/",
                "exemplar/", "repl/", "scripts/", "benches/")

# Extensions we can count lines in.
COUNTABLE = {".rs", ".md", ".cl", ".toml", ".txt", ".json", ".sh", ".py", ".mmd"}

# A path-like token: at least one directory separator or a known extension,
# optionally followed by :N, :N-M, or ::symbol.
PATH_RE = re.compile(
    r"(?P<path>(?:[A-Za-z0-9_.\-]+/)+[A-Za-z0-9_.\-]+\.[A-Za-z0-9]+)"
    r"(?::(?P<line>\d+)(?:-(?P<endline>\d+))?)?"
    r"(?:::(?P<symbol>[A-Za-z_][A-Za-z0-9_]*))?"
)

# `path.rs::symbol` where the path has no directory (e.g. `fn_compiler.rs::foo`).
BARE_FILE_SYMBOL_RE = re.compile(
    r"\b(?P<file>[A-Za-z0-9_\-]+\.rs)::(?P<symbol>[A-Za-z_][A-Za-z0-9_]*)"
)

# Lines that are prose about a *retired* or *hypothetical* thing are exempt when
# the citing line carries one of these markers.
EXEMPT_MARKERS = (
    "retired", "deleted", "removed", "no such", "does not exist", "phantom",
    "historical", "git history", "recover from", "tombstone", "superseded",
    "formerly", "was at", "hypothetical", "would be", "proposed", "if adopted",
    "e.g.", "example:", "renamed",
)

# Frontmatter key whose value is a citation list.
REFERS_TO_RE = re.compile(r"^refers_to:\s*(?P<value>.+)$", re.MULTILINE)


@dataclass
class Finding:
    doc: str
    line_no: int
    kind: str          # PATH | LINE | SYMBOL | PHANTOM
    citation: str
    detail: str
    excerpt: str = ""

    def as_dict(self) -> dict:
        return {
            "doc": self.doc, "line": self.line_no, "kind": self.kind,
            "citation": self.citation, "detail": self.detail,
        }


@dataclass
class Stats:
    docs: int = 0
    citations: int = 0
    checked_paths: int = 0
    checked_lines: int = 0
    checked_symbols: int = 0
    exempt: int = 0
    findings: list = field(default_factory=list)


def line_count(p: Path) -> int | None:
    if p.suffix not in COUNTABLE:
        return None
    try:
        with p.open("rb") as fh:
            return sum(1 for _ in fh)
    except OSError:
        return None


def file_contains(p: Path, symbol: str) -> bool:
    try:
        return symbol in p.read_text(errors="replace")
    except OSError:
        return False


_repo_index: set[str] | None = None


def repo_has_identifier(symbol: str) -> bool:
    """True if `symbol` occurs anywhere under a source root. Cached via ripgrep/grep."""
    global _repo_index
    if _repo_index is None:
        _repo_index = set()
    if symbol in _repo_index:
        return True
    tool = "rg" if _which("rg") else "grep"
    if tool == "rg":
        cmd = ["rg", "-l", "--fixed-strings", "--", symbol, *SOURCE_ROOTS]
    else:
        cmd = ["grep", "-rlF", "--", symbol, *SOURCE_ROOTS]
    try:
        res = subprocess.run(cmd, cwd=REPO, capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired):
        return True  # fail open — never fabricate a finding from a tool failure
    if res.stdout.strip():
        _repo_index.add(symbol)
        return True
    return False


def _which(name: str) -> bool:
    return any((Path(d) / name).exists() for d in os.environ.get("PATH", "").split(os.pathsep) if d)


def is_exempt(text: str) -> bool:
    low = text.lower()
    return any(m in low for m in EXEMPT_MARKERS)


# Template/placeholder citations are not claims about source.
PLACEHOLDER_RE = re.compile(r"NN|\{|\}|<|>|\*|\.\.\.|XXX|FOO|BAR")

# Historical corpora: a dated record citing a line that has since moved is an
# accurate record of its moment, not drift. Excluded from the live corpus.
HISTORICAL_RE = re.compile(
    r"(^|/)(archive|review)/|"          # design/**/archive/, design/review/
    r"sprint-?\d+|"                     # sprint58-wave2-review.md, sprint-84
    r"-s\d{2,3}\.md$|"                  # audits/frontend-s113.md
    r"-\d{8}"                           # typecheck-20260423.md
)


def is_historical(rel_path: str) -> bool:
    return bool(HISTORICAL_RE.search(rel_path))


def looks_like_source_path(raw: str) -> bool:
    if PLACEHOLDER_RE.search(raw):
        return False
    return raw.startswith(SOURCE_ROOTS) or raw.endswith(("CLAUDE.md",))


def check_document(doc: Path, stats: Stats) -> None:
    try:
        text = doc.read_text(errors="replace")
    except OSError:
        return
    stats.docs += 1
    try:
        rel_doc = str(doc.relative_to(REPO))
    except ValueError:
        # An out-of-tree document (a scratch file, a detection-proof fixture).
        # Check it anyway — citations inside it still resolve against this repo.
        rel_doc = str(doc)
    lines = text.splitlines()
    # (line, symbol) pairs already reported via the full-path form, so the
    # bare-filename pass does not double-report the same citation.
    seen_symbols: set[tuple[int, str]] = set()

    for idx, raw_line in enumerate(lines, start=1):
        exempt_line = is_exempt(raw_line)

        for m in PATH_RE.finditer(raw_line):
            raw_path = m.group("path")
            if not looks_like_source_path(raw_path):
                continue
            stats.citations += 1
            citation = m.group(0)
            target = REPO / raw_path

            if not target.exists():
                if exempt_line:
                    stats.exempt += 1
                    continue
                stats.findings.append(Finding(
                    rel_doc, idx, "PATH", citation,
                    f"cited path does not exist: {raw_path}",
                    raw_line.strip()[:160]))
                continue
            stats.checked_paths += 1

            lineno = m.group("line")
            if lineno:
                total = line_count(target)
                if total is not None:
                    stats.checked_lines += 1
                    hi = int(m.group("endline") or lineno)
                    if int(lineno) > total or hi > total:
                        if exempt_line:
                            stats.exempt += 1
                        else:
                            stats.findings.append(Finding(
                                rel_doc, idx, "LINE", citation,
                                f"line {lineno}{'-' + m.group('endline') if m.group('endline') else ''} "
                                f"is past end of {raw_path} ({total} lines)",
                                raw_line.strip()[:160]))

            symbol = m.group("symbol")
            if symbol and target.is_file():
                stats.checked_symbols += 1
                if not file_contains(target, symbol):
                    seen_symbols.add((idx, symbol))
                    if exempt_line:
                        stats.exempt += 1
                    else:
                        homes = [str(p.relative_to(REPO)) for p in _source_files()
                                 if file_contains(p, symbol)][:3]
                        where = ("actually in " + ", ".join(homes) if homes
                                 else "found nowhere in the tree")
                        stats.findings.append(Finding(
                            rel_doc, idx, "SYMBOL", citation,
                            f"`{symbol}` does not occur in {raw_path} — {where}",
                            raw_line.strip()[:160]))
                else:
                    seen_symbols.add((idx, symbol))

        # `bare_file.rs::symbol` — no directory component. Resolve by basename.
        for m in BARE_FILE_SYMBOL_RE.finditer(raw_line):
            fname, symbol = m.group("file"), m.group("symbol")
            if (idx, symbol) in seen_symbols:
                continue  # already handled by the full-path form on this line
            stats.citations += 1
            matches = [p for p in _source_files() if p.name == fname]
            if not matches:
                continue  # ambiguous or non-repo file; not our business
            if any(file_contains(p, symbol) for p in matches):
                stats.checked_symbols += 1
                continue
            if exempt_line:
                stats.exempt += 1
                continue
            where = "found nowhere in the tree"
            if repo_has_identifier(symbol):
                homes = [str(p.relative_to(REPO)) for p in _source_files()
                         if file_contains(p, symbol)][:3]
                where = "actually in " + ", ".join(homes) if homes else where
            stats.findings.append(Finding(
                rel_doc, idx, "SYMBOL", m.group(0),
                f"`{symbol}` does not occur in {fname} — {where}",
                raw_line.strip()[:160]))


_source_cache: list[Path] | None = None


def _source_files() -> list[Path]:
    global _source_cache
    if _source_cache is None:
        _source_cache = []
        for root in SOURCE_ROOTS:
            base = REPO / root
            if not base.exists():
                continue
            for p in base.rglob("*.rs"):
                if "target" not in p.parts:
                    _source_cache.append(p)
    return _source_cache


def collect_docs(explicit: list[str], corpus: str) -> list[Path]:
    if explicit:
        return [REPO / e if not Path(e).is_absolute() else Path(e) for e in explicit]
    seen: set[Path] = set()
    for pattern in DOC_GLOBS:
        for p in REPO.glob(pattern):
            if "target" in p.parts or "/.git/" in str(p):
                continue
            if p.is_file():
                seen.add(p)
    # FIXMEs are the highest-value corpus: they drive scheduling.
    for p in (REPO / "design/arch/fixmes").glob("*.md"):
        seen.add(p)

    if corpus == "fixmes":
        seen = {p for p in seen if "fixmes" in p.parts}
    elif corpus == "live":
        seen = {p for p in seen if not is_historical(str(p.relative_to(REPO)))}
    return sorted(seen)


def fingerprint(f: Finding) -> str:
    """Stable identity for the ratchet: survives line renumbering in the doc."""
    return f"{f.doc}\t{f.kind}\t{f.detail}"


def load_baseline(path: Path) -> set[str]:
    if not path.exists():
        return set()
    return {ln.rstrip("\n") for ln in path.read_text().splitlines()
            if ln.strip() and not ln.startswith("#")}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="*", help="documents to check (default: the doc corpus)")
    ap.add_argument("--corpus", choices=("live", "all", "fixmes"), default="live",
                    help="live (default): plan-of-record documents only, excluding dated "
                         "records and archives; all: everything; fixmes: FIXMEs only")
    ap.add_argument("--baseline", metavar="FILE",
                    help="ratchet file: findings listed there are tolerated; anything "
                         "new fails. This lets the check gate a repo with an existing "
                         "backlog — the backlog can only shrink.")
    ap.add_argument("--write-baseline", metavar="FILE",
                    help="record current findings as the accepted backlog and exit 0")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    ap.add_argument("--quiet", action="store_true", help="findings only, no summary")
    args = ap.parse_args()

    stats = Stats()
    for doc in collect_docs(args.paths, args.corpus):
        check_document(doc, stats)

    if args.write_baseline:
        out = Path(args.write_baseline)
        prints = sorted({fingerprint(f) for f in stats.findings})
        out.write_text(
            "# Citation-drift ratchet baseline — scripts/verify-citations.py\n"
            "# Every line is a KNOWN-STALE citation, tolerated so the check can gate a\n"
            "# repo with an existing backlog. Entries may be DELETED (when the citation\n"
            "# is repaired) but must never be ADDED by hand: a new finding is a new\n"
            "# stale record, and the check exists to stop those landing.\n"
            f"# {len(prints)} entries.\n"
            + "\n".join(prints) + "\n")
        print(f"Wrote {len(prints)} baseline entries to {out}.")
        return 0

    if args.baseline:
        allowed = load_baseline(Path(args.baseline))
        kept, tolerated = [], 0
        for f in stats.findings:
            if fingerprint(f) in allowed:
                tolerated += 1
            else:
                kept.append(f)
        stats.findings = kept
        stats.exempt += tolerated

    if args.json:
        print(json.dumps({
            "docs": stats.docs, "citations": stats.citations,
            "checked": {"paths": stats.checked_paths, "lines": stats.checked_lines,
                        "symbols": stats.checked_symbols},
            "exempt": stats.exempt,
            "findings": [f.as_dict() for f in stats.findings],
        }, indent=2))
        return 1 if stats.findings else 0

    by_kind: dict[str, list[Finding]] = {}
    for f in stats.findings:
        by_kind.setdefault(f.kind, []).append(f)

    for kind in ("PATH", "SYMBOL", "LINE"):
        group = by_kind.get(kind, [])
        if not group:
            continue
        print(f"\n=== {kind} ({len(group)}) ===")
        for f in group:
            print(f"  {f.doc}:{f.line_no}")
            print(f"      {f.detail}")
            if f.excerpt:
                print(f"      | {f.excerpt}")

    if not args.quiet:
        print(f"\n{stats.docs} documents, {stats.citations} citations "
              f"({stats.checked_paths} paths, {stats.checked_lines} line refs, "
              f"{stats.checked_symbols} symbols verified; {stats.exempt} exempt).")
        print(f"{len(stats.findings)} finding(s).")

    return 1 if stats.findings else 0


if __name__ == "__main__":
    sys.exit(main())
