#!/usr/bin/env python3
"""spec_coverage_reconcile.py — spec→test direction checker + reconciliation engine.

This is the FIXME-0414 guard (the durable, reusable spec→test linter) PLUS the
one-time reconciliation engine for FIXMEs 0412/0413 (rewrite rotted
`[Tested tests/<deleted>::name]` annotations to the real `tests/spec_NN_*.rs`
test names).

The existing `spec_link_check.py` checks only the **test→spec** direction (does
a test's `// spec:` anchor exist in the spec). It cannot catch citation rot:
a spec that cites `tests/ring0.rs::foo` when `ring0.rs` was deleted and the test
re-authored as `tests/spec_04_expressions.rs::bar`.

This script adds the reverse:

  1. Parse every `[Tested tests/FILE::name]` / `[Tested+Neg tests/FILE::name]`
     in spec/*.md + repl/spec.md (capturing file:line + the governing §anchor).
  2. Assert `tests/FILE.rs` exists AND contains `fn name`.
  3. Build a test→spec index over tests/*.rs + crates/** + src/** (the healthy
     direction) keyed by (spec-file, §anchor).
  4. For dead citations, propose the real covering test by matching the
     governing §anchor against that index (the reliable join key).
  5. Detect stale-pending: `[S{M}]` sections whose anchor has a covering test.
  6. Detect true gaps: heading/MUST sections with NO covering test.

Modes:
  --check     (default) report dead citations + stale-pending + true gaps; exit
              non-zero if any dead citation remains. The CI/wave guard.
  --propose   print the proposed crosswalk (dead citation -> real test) without
              writing.
  --apply     rewrite the bracketed annotation tokens in place using the
              high-confidence crosswalk.

Verification discipline (false-positive guards from the prior audit):
  - A fn name is only accepted as a cover if it lives in a tests/ file OR a
    crate `#[cfg(test)]` module (not a production fn). The index is built only
    from fns that carry a `// spec:` back-reference, which production fns do not.
  - A proposed cover must match BOTH the cited spec file AND the governing
    §anchor — never a bare name match. (`zero` matches a production fn in
    src/session_v4.rs; `display_int_result` exists but under a different file —
    anchor-matching rejects both.)
"""
from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path


# ---------------------------------------------------------------------------
# Spec-side annotation parsing
# ---------------------------------------------------------------------------

# A single `tests/FILE::name` OR `tests/FILE.rs::name` token inside a
# [Tested ...] bracket. Both forms appear in the spec annotations; the `.rs`
# is optional and stripped to a canonical file stem.
CITE_TOKEN_RE = re.compile(r"tests/([A-Za-z0-9_]+)(\.rs)?::([A-Za-z0-9_*]+)")
# The whole bracket: [Tested ...] or [Tested+Neg ...]
TESTED_BRACKET_RE = re.compile(r"\[Tested(\+Neg)?\b([^\]]*)\]")
# [S{M}] / [S{M} — ...] / [R{N} S{M}] pending tags.
PENDING_RE = re.compile(r"\[(?:R\d+\s+)?S\d+[^\]]*\]")
# Heading line with a numeric/appendix anchor.
HEADING_RE = re.compile(r"^(#{1,6})\s+(.*)$")
HEADING_NUM_RE = re.compile(r"^(?P<num>\d+(?:\.\d+)*[a-z]?)\.?\s")

# RFC-2119 keywords for true-gap detection (MUST / SHOULD clauses).
RFC2119_RE = re.compile(r"\b(MUST(?: NOT)?|SHALL(?: NOT)?|REQUIRED|SHOULD(?: NOT)?)\b")


@dataclass
class SpecLine:
    md: Path
    lineno: int          # 1-based
    text: str
    anchor: str          # governing §anchor (numeric prefix or heading title)
    anchor_kind: str     # 'num' or 'title'


@dataclass
class DeadCite:
    md: Path
    lineno: int
    token_file: str      # e.g. "ring0"
    token_name: str      # e.g. "dual_mode_simple_int"
    anchor: str


# ---------------------------------------------------------------------------
# Build test→spec index (the healthy direction)
# ---------------------------------------------------------------------------

SPEC_ANN_RE = re.compile(r"^\s*///?\s*spec:\s*(.*?)\s*$")
CONT_RE = re.compile(r"^\s*///?\s+(.*?)\s*$")
FN_RE = re.compile(r"^\s*(?:pub\s+)?(?:async\s+)?fn\s+([A-Za-z0-9_]+)")

PATH_RE = re.compile(r"(?:[A-Za-z0-9_./-]+\.md)")
SHORT_RE = re.compile(
    r"\b((?:(?:0[0-9]|1[0-9])-[A-Za-z0-9_-]+)|(?:appendix-[a-z]-[A-Za-z0-9_-]+))\b")
ANCHOR_NUM_RE = re.compile(r"§\s*(\d+(?:\.\d+)*[a-z]?)")
ANCHOR_QUOTED_RE = re.compile(r"§\s*[\"“]([^\"”]+)[\"”]")


@dataclass
class TestFn:
    file: str            # relative path, e.g. "tests/spec_04_expressions.rs"
    name: str
    is_test_file: bool   # under tests/ (top-level e2e)
    spec_md: str | None  # normalized spec md path, e.g. "spec/04-expressions.md"
    spec_anchor: str | None
    spec_anchor_kind: str  # 'num' / 'title' / ''
    asserts_neg: bool    # heuristic: name has _neg_/_not_ or file is repl_negative


def normalize_spec_path(raw: str) -> str | None:
    m = PATH_RE.search(raw)
    if m:
        p = m.group(0)
        if "/" not in p and re.match(r"^\d{2}-", p):
            p = f"spec/{p}"
        # alias fixups
        if p == "spec/02-syntax.md":
            p = "spec/02-grammar.md"
        if p == "spec/03-type-system.md":
            p = "spec/03-types.md"
        return p
    sm = SHORT_RE.search(raw)
    if sm:
        short = sm.group(1)
        if short == "02-syntax":
            short = "02-grammar"
        if short == "03-type-system":
            short = "03-types"
        return f"spec/{short}.md"
    if "repl/spec" in raw or raw.strip().startswith("§") and "repl" in raw.lower():
        return "repl/spec.md"
    return None


def parse_backref(raw: str) -> tuple[str | None, str | None, str]:
    """Return (spec_md, anchor, anchor_kind) for a // spec: payload."""
    md = normalize_spec_path(raw)
    # repl/spec.md is often cited bare as 'repl/spec.md §...'
    if md is None and "repl/spec" in raw:
        md = "repl/spec.md"
    anchor = None
    kind = ""
    qm = ANCHOR_QUOTED_RE.search(raw)
    if qm:
        anchor = qm.group(1).strip().lower()
        kind = "title"
    else:
        nm = ANCHOR_NUM_RE.search(raw)
        if nm:
            anchor = nm.group(1).strip()
            kind = "num"
    return md, anchor, kind


def build_test_index(root: Path) -> list[TestFn]:
    out: list[TestFn] = []
    for sub in ("tests", "crates", "src"):
        base = root / sub
        if not base.is_dir():
            continue
        for rs in base.rglob("*.rs"):
            if "/target/" in str(rs):
                continue
            try:
                lines = rs.read_text(errors="replace").splitlines()
            except OSError:
                continue
            rel = str(rs.relative_to(root))
            is_test_file = rel.startswith("tests/") and rs.parent == base
            pending: list[str] = []
            for l in lines:
                sm = SPEC_ANN_RE.match(l)
                fm = FN_RE.match(l)
                if sm:
                    pending.append(sm.group(1))
                    continue
                if fm:
                    if pending:
                        joined = " ".join(pending)
                        md, anchor, kind = parse_backref(joined)
                        nm = fm.group(1)
                        neg = ("_neg" in nm or "_not_" in nm
                               or "repl_negative" in rel)
                        out.append(TestFn(
                            file=rel, name=nm, is_test_file=is_test_file,
                            spec_md=md, spec_anchor=anchor,
                            spec_anchor_kind=kind, asserts_neg=neg))
                    pending = []
                    continue
                s = l.strip()
                if s == "" or s.startswith("#[") or s.startswith("//"):
                    # keep pending across attrs / blank / continuation comments
                    continue
                pending = []
    return out


# ---------------------------------------------------------------------------
# Spec-side scan: citations + pending + governing anchor + headings
# ---------------------------------------------------------------------------

def heading_anchor(text: str) -> tuple[str, str]:
    """Return (anchor, kind) for a heading body (after the #'s)."""
    body = re.sub(r"\s*\[[^\]]+\]\s*$", "", text).strip()
    m = HEADING_NUM_RE.match(body)
    if m:
        return m.group("num"), "num"
    return body.lower(), "title"


@dataclass
class SpecScan:
    dead: list[DeadCite] = field(default_factory=list)
    live: list[DeadCite] = field(default_factory=list)  # cite to a real file
    pending: list[SpecLine] = field(default_factory=list)
    headings: list[SpecLine] = field(default_factory=list)
    must_lines: list[SpecLine] = field(default_factory=list)


def scan_spec(md: Path, root: Path) -> SpecScan:
    sc = SpecScan()
    cur_anchor, cur_kind = "", ""
    for i, raw in enumerate(md.read_text().splitlines(), start=1):
        hm = HEADING_RE.match(raw)
        if hm:
            cur_anchor, cur_kind = heading_anchor(hm.group(2))
            sl = SpecLine(md, i, raw, cur_anchor, cur_kind)
            sc.headings.append(sl)
        # the governing anchor for any line is the most recent heading
        # citations
        for bm in TESTED_BRACKET_RE.finditer(raw):
            inner = bm.group(2)
            for tm in CITE_TOKEN_RE.finditer(inner):
                tf, tn = tm.group(1), tm.group(3)
                rel = f"tests/{tf}.rs"
                dc = DeadCite(md, i, tf, tn, cur_anchor)
                if (root / rel).is_file():
                    sc.live.append(dc)
                else:
                    sc.dead.append(dc)
        # pending
        if PENDING_RE.search(raw):
            sc.pending.append(SpecLine(md, i, raw, cur_anchor, cur_kind))
        # MUST/SHOULD lines (for true-gap detection)
        if RFC2119_RE.search(raw) and not raw.lstrip().startswith("|"):
            sc.must_lines.append(SpecLine(md, i, raw, cur_anchor, cur_kind))
    return sc


# ---------------------------------------------------------------------------
# Reaudit crosswalk: explicit old-test-name -> new-test (file, name)
# ---------------------------------------------------------------------------

# New-test references appearing in the reaudit "Notes" columns.
REAUDIT_NEWREF_RE = re.compile(
    r"`?(spec_[0-9a-z_]+|build_confidence|repl_introspection|repl_negative|"
    r"repl_lifecycle|trace|repl_shell|repl_watch|repl_persist|cache|link|"
    r"regression)\.rs::([A-Za-z0-9_]+)`?")
REAUDIT_OLD_RE = re.compile(r"^`([a-z][A-Za-z0-9_]+)`$")


BARE_NAME_RE = re.compile(r"`([a-z][A-Za-z0-9_]+)`")


def load_reaudit_crosswalk(root: Path,
                           fn_to_files: dict[str, list[str]]
                           ) -> dict[str, list[tuple[str, str]]]:
    """Parse tests/plan/wave-5.6-*-reaudit.md tables for explicit
    old-test-name -> new (file, fn) mappings. The reaudit "Notes" column names
    the real covering test for each old test; this is the authoritative join for
    cases the §anchor heuristic cannot resolve.

    Two forms of new-ref in the Notes:
      - `file.rs::name` (explicit) — taken verbatim;
      - bare `name` (no file) — resolved to a file via `fn_to_files` (the live
        suite index), accepted only when the name resolves to exactly one
        current test file (avoids ambiguity)."""
    cw: dict[str, list[tuple[str, str]]] = {}
    docs = ["wave-5.6-ring0-reaudit.md", "wave-5.6-ring1-reaudit.md",
            "wave-5.6-ring2-reaudit.md", "wave-5.6-e2e-reaudit.md",
            "wave-5.6-sketch-port-reaudit.md"]
    for d in docs:
        p = root / "tests/plan" / d
        if not p.is_file():
            continue
        for line in p.read_text().splitlines():
            if not line.strip().startswith("|"):
                continue
            cells = [c.strip() for c in line.split("|")]
            if len(cells) < 3:
                continue
            # The old-test-name cell is the FIRST backtick-quoted-only cell
            # (some tables have a leading row-number column before it).
            old = None
            old_idx = None
            for ci, c in enumerate(cells):
                m0 = REAUDIT_OLD_RE.match(c)
                if m0:
                    old = m0.group(1)
                    old_idx = ci
                    break
            if old is None:
                continue

            def add(pair):
                cw.setdefault(old, [])
                if pair not in cw[old]:
                    cw[old].append(pair)

            explicit = list(REAUDIT_NEWREF_RE.finditer(line))
            for m in explicit:
                add((f"tests/{m.group(1)}.rs", m.group(2)))
            if not explicit:
                # Bare current-test-name references in cells AFTER the old name.
                for bm in BARE_NAME_RE.finditer(" ".join(cells[old_idx + 1:])):
                    nm = bm.group(1)
                    if nm == old:
                        continue
                    files = fn_to_files.get(nm, [])
                    if len(files) == 1:
                        add((files[0], nm))
    return cw


# ---------------------------------------------------------------------------
# Crosswalk: dead cite -> real covering test(s) via governing §anchor
# ---------------------------------------------------------------------------

def anchor_index(tests: list[TestFn]) -> dict[tuple[str, str], list[TestFn]]:
    """Map (spec_md, anchor) -> covering tests. Numeric anchors keyed exactly;
    a test on a more-specific anchor (10.6.1) also covers its parents (10.6, 10)
    for gap purposes — handled at lookup, not here."""
    idx: dict[tuple[str, str], list[TestFn]] = {}
    for t in tests:
        if not t.spec_md or not t.spec_anchor:
            continue
        if not t.is_test_file:
            # crate/src unit tests are valid covers too, but we prefer e2e;
            # keep them, tagged by file.
            pass
        idx.setdefault((t.spec_md, t.spec_anchor), []).append(t)
    return idx


def covers_for_anchor(spec_md: str, anchor: str,
                      idx: dict[tuple[str, str], list[TestFn]],
                      allow_parent: bool = True
                      ) -> list[TestFn]:
    """Tests whose anchor covers `anchor`.

    Match priority:
      1. exact anchor match;
      2. a child anchor (a test on §10.6.1 covers a §10.6 citation);
      3. (if allow_parent) the nearest parent anchor (a test on §4.6 covers a
         §4.6.1 citation) — used as fallback when the spec sub-heading is finer
         than the test's back-reference granularity.
    Returns exact/child covers if any exist; only falls back to parent covers
    when nothing finer is found.
    """
    is_num = bool(re.fullmatch(r"\d+(?:\.\d+)*[a-z]?", anchor or ""))
    exact_child: list[TestFn] = []
    parent: list[TestFn] = []
    seen = set()

    def add(bucket, t):
        k = (t.file, t.name)
        if k not in seen:
            seen.add(k)
            bucket.append(t)

    # IMMEDIATE parent anchor only (one level up). Falling back to grand-parents
    # or the chapter heading (§4, §5) overstates coverage — a §4 test does not
    # cover §4.8.1's specific requirement. Restricting to one level keeps the
    # fallback topically adjacent (§4.6.1 Direct Calls -> a §4.6 application
    # test), and anything coarser is left UNRESOLVED for honest annotation.
    parents = []
    if is_num and "." in anchor:
        parts = anchor.split(".")
        parents.append(".".join(parts[:-1]))

    for (m, a), ts in idx.items():
        if m != spec_md:
            continue
        if a == anchor or (is_num and a.startswith(anchor + ".")):
            for t in ts:
                add(exact_child, t)
        elif allow_parent and a in parents:
            for t in ts:
                add(parent, t)

    if exact_child:
        return exact_child, "exact"
    return parent, "parent"


def spec_md_for(md: Path, root: Path) -> str:
    return str(md.relative_to(root))


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=None)
    ap.add_argument("--mode",
                    choices=["check", "propose", "apply", "dedupe",
                             "stale", "apply-stale"],
                    default="check")
    ap.add_argument("--stale-scope", default=None,
                    help="limit apply-stale to a single spec file "
                         "(e.g. spec/10-io.md). Default: all (report only).")
    ap.add_argument("--tiers", default="exact,override,reaudit",
                    help="comma-separated confidence tiers to apply "
                         "(exact,reaudit,parent). Default: exact,reaudit "
                         "(parent fallback is review-grade, excluded).")
    ap.add_argument("--gaps", action="store_true",
                    help="emit the true-gap list (MUST/SHOULD with no cover)")
    args = ap.parse_args()

    root = Path(args.root).resolve() if args.root else \
        Path(__file__).resolve().parent.parent.parent

    spec_files = sorted((root / "spec").glob("*.md")) + [root / "repl/spec.md"]
    spec_files = [p for p in spec_files if p.is_file()
                  and p.name not in ("CLAUDE.md",)]

    tests = build_test_index(root)
    idx = anchor_index(tests)
    # validate reaudit targets exist on disk (the named fn in the named file)
    fn_by_file_all: dict[str, set[str]] = {}
    fn_to_files: dict[str, list[str]] = {}
    for sub in ("tests",):
        base = root / sub
        for rs in base.glob("*.rs"):
            txt = rs.read_text(errors="replace")
            names = set(re.findall(r"\bfn ([A-Za-z0-9_]+)", txt))
            fn_by_file_all[f"tests/{rs.stem}.rs"] = names
            for n in names:
                fn_to_files.setdefault(n, []).append(f"tests/{rs.stem}.rs")
    reaudit = load_reaudit_crosswalk(root, fn_to_files)

    all_dead: list[DeadCite] = []
    all_live: list[DeadCite] = []
    scans: dict[Path, SpecScan] = {}
    for md in spec_files:
        sc = scan_spec(md, root)
        scans[md] = sc
        all_dead.extend(sc.dead)
        all_live.extend(sc.live)

    # live-cite validation: does the named fn actually exist in that file?
    fn_by_file: dict[str, set[str]] = {}
    for t in tests:
        fn_by_file.setdefault(t.file, set()).add(t.name)
    live_broken = []
    for dc in all_live:
        rel = f"tests/{dc.token_file}.rs"
        names = fn_by_file.get(rel, set())
        if dc.token_name != "*" and "*" not in dc.token_name \
                and dc.token_name not in names:
            # also accept any fn (not just spec-annotated) in that file
            txt = (root / rel).read_text(errors="replace")
            if not re.search(rf"\bfn {re.escape(dc.token_name)}\b", txt):
                live_broken.append(dc)

    # Build crosswalk for dead cites.
    resolved: list[tuple[DeadCite, TestFn]] = []
    unresolved: list[DeadCite] = []
    confidence: dict[int, str] = {}  # id(dc) -> 'exact'|'reaudit'|'parent'

    def reaudit_pick(old_name: str) -> TestFn | None:
        pairs = reaudit.get(old_name)
        if not pairs:
            return None
        for f, n in pairs:
            if n in fn_by_file_all.get(f, set()):
                # synthesize a TestFn-shaped pick (test-file cover)
                return TestFn(file=f, name=n, is_test_file=True,
                              spec_md=None, spec_anchor=None,
                              spec_anchor_kind="", asserts_neg=("_neg" in n))
        return None

    # name -> [TestFn] index (real tests, exact fn-name) for rename-in-place.
    by_name: dict[str, list[TestFn]] = {}
    for t in tests:
        if t.is_test_file:
            by_name.setdefault(t.name, []).append(t)

    # Manually-verified overrides for dead cites the §anchor/name heuristics
    # cannot resolve (cross-chapter covers, renamed tests). Each entry was
    # confirmed by reading the named test's body + its // spec: back-reference
    # during the S86 /qa reconciliation. Keyed by old "file::name".
    OVERRIDES: dict[str, tuple[str, str] | None] = {
        # §12.7.1 macro-expansion-error list item — real covers live in
        # spec_09_macros.rs (cross-chapter; the spec/12 list cites macro errors).
        "macros::neg_macro_non_sexp_return_type_batch":
            ("tests/spec_09_macros.rs", "macro_body_non_sexp_int_rejected_neg"),
        "macros::neg_macro_expansion_depth_limit_exceeded":
            ("tests/spec_09_macros.rs", "neg_macro_expansion_depth_limit_exceeded"),
        # §4.5.3 Calling Convention — closure capture is covered by the
        # closure-capture e2e tests (§4.5).
        "ring1::closure_simple_capture":
            ("tests/spec_04_expressions.rs", "lambda_closure_captures"),
        "ring1::closure_returned_from_function":
            ("tests/spec_04_expressions.rs",
             "closure_composition_returns_capturing_two_fn_args"),
        # §4.5.2 Parameter Type Annotations on lambdas — covered by the
        # annotated-params type test (§3.x annotation coverage applies to
        # lambda params too via the same annotation machinery).
        "ring2::annotated_lambda":
            ("tests/spec_03_types.rs", "annotated_params_int"),
        # §4.6.2 higher-order application.
        "ring1::closure_with_higher_order":
            ("tests/spec_04_expressions.rs",
             "lambda_passed_as_argument_invoked_inside_callee"),
        "e2e::e2e_ring1_higher_order":
            ("tests/spec_04_expressions.rs",
             "lambda_passed_as_argument_invoked_inside_callee"),
        # §4.12.8 trace over a composed expression.
        "ring4_trace::trace_composed_expression":
            ("tests/spec_04_expressions.rs", "trace_returns_trace_type"),
        # §5.3.x user-defined traits — deftrait+impl+dispatch e2e.
        "ring2::repl_user_trait":
            ("tests/spec_05_definitions.rs", "deftrait_impl_and_dispatch"),
        "repl_experience::ring2a_deftrait_in_repl":
            ("tests/spec_05_definitions.rs", "deftrait_impl_and_dispatch"),
        "ring2::trait_plus_int":
            ("tests/spec_05_definitions.rs", "deftrait_impl_and_dispatch"),
        # ring2::error_plus_bool (§5.3.3 / §5.4.5) — no precise negative
        # trait-dispatch cover located; left UNRESOLVED (honest gap flag).

        # --- residual, verified by S86 subagent + fn-existence grep ---
        # spec/04 §4.8.x ADT match (documented in both ch.4 and ch.6; covers
        # live in spec_06_pattern_matching.rs).
        "ring1::adt_sum_nested_match":
            ("tests/spec_06_pattern_matching.rs", "nested_match_in_arm_body"),
        "ring1::adt_sum_var_pattern":
            ("tests/spec_06_pattern_matching.rs", "pattern_variable_binds_value"),
        "ring1::repl_adt_product_match":
            ("tests/spec_06_pattern_matching.rs",
             "pattern_data_constructor_binds_fields"),
        "ring1::adt_sum_wildcard_pattern":
            ("tests/spec_06_pattern_matching.rs", "pattern_wildcard_catchall"),
        # spec/04 §4.9.x concrete type annotations.
        "ring2::annotation_concrete_type_int":
            ("tests/spec_03_types.rs", "annotation_expression_standalone"),
        "ring2::annotation_concrete_type_float":
            ("tests/spec_03_types.rs", "annotation_expression_applied_type"),
        "ring2::annotation_constrains_body":
            ("tests/spec_03_types.rs", "annotated_params_int"),
        # ring2::annotation_on_both_params (§4.9.3) — GAP (no multi-param
        # annotation test). ring2::annotation_wrong_type_error (§4.9.3) — GAP
        # (no annotation-specific type-mismatch negative). Left UNRESOLVED.
        # spec/05 §5.4.x user traits (covers live in spec_07_traits.rs).
        "ring2::user_trait_simple":
            ("tests/spec_07_traits.rs", "user_trait_simple"),
        "ring2::user_trait_adt":
            ("tests/spec_07_traits.rs",
             "trait_impl_on_enum_adt_with_match_over_all_constructors"),
        "ring2::user_trait_multiple_impls":
            ("tests/spec_07_traits.rs", "trait_multiple_impls"),
        # spec/05 §5.8 modules.
        "ring2::module_cycle_detection":
            ("tests/spec_08_modules.rs", "module_cycle_detection_neg"),
        # ring2::single_file_via_run_project (§5.8) — GAP located (no test by
        # that angle in spec_08_modules.rs/cache.rs). ring2::module_missing_file_error
        # (§5.8) — GAP. Left UNRESOLVED.
        # spec/05 §5.6/§5.7 const/def macros — GAP (no isolated const/def macro
        # test in spec_09_macros.rs). Left UNRESOLVED.
        # spec/06 §6.5.3 / §6.7.x pattern matching.
        "ring1::non_exhaustive_match_panics":
            ("tests/spec_06_pattern_matching.rs",
             "pattern_non_exhaustive_match_on_adt_neg"),
        "ring1::repl_adt_match":
            ("tests/spec_06_pattern_matching.rs", "match_enum_basic"),
        # e2e::e2e_ring1_pattern_matching (§6.7.2) — umbrella; covered
        # collectively by the spec_06 pattern_* family. Point at the
        # constructor-binding canonical test.
        "e2e::e2e_ring1_pattern_matching":
            ("tests/spec_06_pattern_matching.rs",
             "pattern_data_constructor_binds_fields"),
        # spec/appendix-a §A.5 builtin docstrings / macro display.
        "ring3_repl::r3_defmacro_display_single_clause":
            ("tests/repl_introspection.rs", "defmacro_display_single_clause"),
        "ring3_repl::r3_defmacro_display_multi_clause":
            ("tests/repl_introspection.rs", "defmacro_display_multi_clause"),
        # repl/spec.md §4.1.2 constructor lookup. The legacy test asserted
        # BOTH the dot-notation ctor and the qualified type home — matched
        # by the S108 §4.1.2 guard (the earlier target
        # nullary_constructor_bare_lookup_dot_notation under-asserted and
        # was deleted S108, FIXME 0557).
        "e2e::e2e_s1_1_constructor_lookup":
            ("tests/repl_introspection.rs",
             "nullary_constructor_bare_lookup_shows_deftype_and_qualified_home"),
        # repl/spec.md §5.3 — type_error_mentions_expected_and_actual,
        # e2e_s5_3_type_error_shows_expected_actual, error_has_source_span:
        # current type-error tests assert "type error" surfaces but NOT that
        # BOTH expected+actual are named, nor a type-error source span. GAP
        # (precision). Left UNRESOLVED.
        # repl/spec.md §6.1/§6.3 first_five_minutes_workflow — GAP (no
        # multi-step tutorial workflow test). Left UNRESOLVED.
        # repl/spec.md §7.2 perf budget.
        "repl_experience::simple_eval_under_50ms":
            ("tests/build_confidence.rs",
             "perf_simple_eval_latency_under_2000ms"),
        # repl/spec.md §11.3 defmacro result display.
        "macros::repl_defmacro_display_single_clause":
            ("tests/repl_introspection.rs", "defmacro_display_single_clause"),
        "macros::repl_defmacro_display_multi_clause":
            ("tests/repl_introspection.rs", "defmacro_display_multi_clause"),
        # repl/spec.md §11.2.3 /sig on macro.
        "ring3_repl::r3_sig_macro_params":
            ("tests/repl_introspection.rs",
             "bare_macro_lookup_shows_clause_signature"),
        "ring3_repl::r3_sig_macro_variadic":
            ("tests/repl_introspection.rs",
             "bare_macro_lookup_shows_clause_signature"),
        # repl/spec.md §11.2.2 /info on macro.
        "ring3_repl::r3_info_macro_docstring":
            ("tests/repl_introspection.rs", "doc_macro_with_docstring"),
        # ring3_repl::r3_info_macro_clause_count (§11.2.2/§11.5) — GAP
        # (no test asserts a macro clause COUNT via /info). Left UNRESOLVED.
        # repl/spec.md §11.5 /list macros category.
        "ring3_repl::r3_list_macros_category_via_symbol_table":
            ("tests/repl_introspection.rs", "list_shows_macros_after_defmacro"),
        "ring3_repl::r3_bare_macro_lookup":
            ("tests/repl_introspection.rs", "bare_macro_lookup"),

        # --- final residual batch (S86 /qa, verified by grep) ---
        # appendix-a §A.3/extern/inline primitives (current names primitive_*).
        "ring1::str_concat":
            ("tests/spec_appendix_a_builtins.rs", "primitive_str_concat"),
        "ring1::int_to_string":
            ("tests/spec_appendix_a_builtins.rs", "primitive_int_to_string"),
        "ring1::string_identity_returns_same":
            ("tests/spec_appendix_a_builtins.rs",
             "primitive_string_identity_returns_same"),
        "ring1::parse_int_valid":
            ("tests/spec_appendix_a_builtins.rs", "primitive_parse_int_valid"),
        # float sub/mul/div absorbed by add-f64 per ring0 reaudit.
        "ring0::float_subtraction":
            ("tests/spec_appendix_a_builtins.rs", "primitive_add_f64"),
        "ring0::float_multiplication":
            ("tests/spec_appendix_a_builtins.rs", "primitive_add_f64"),
        "ring0::float_division":
            ("tests/spec_appendix_a_builtins.rs", "primitive_add_f64"),
        "repl_experience::all_float_comparison_primitives_work_in_repl":
            ("tests/spec_appendix_a_builtins.rs", "primitive_lt_f64"),
        # §A.2 compound types — macro/quasiquote display (macro_basic_repl old).
        "macros::macro_basic_repl":
            ("tests/spec_09_macros.rs", "defmacro_identity_expands"),
        "macros::macro_multi_clause_repl":
            ("tests/spec_09_macros.rs", "defmacro_multi_clause_dispatch"),
        "macros::macro_basic_batch":
            ("tests/spec_09_macros.rs", "batch_defmacro_begin_splicing"),
        "macros::macro_quasiquote_repl":
            ("tests/spec_09_macros.rs", "quasiquote_with_unquote"),
        "macros::macro_uses_another_batch":
            ("tests/spec_09_macros.rs", "defmacro_identity_expands"),
        # §9.11 quasiquote.
        # §5.6 const / §5.7 def macros (covers live in spec_11_stdlib.rs via
        # the TestPrelude fixture).
        "stdlib::macro_const_int_batch":
            ("tests/spec_11_stdlib.rs", "macro_const_int"),
        "stdlib::macro_const_string_batch":
            ("tests/spec_11_stdlib.rs", "macro_const_string"),
        "stdlib::macro_def_basic_batch":
            ("tests/spec_11_stdlib.rs", "macro_def_basic"),
        "stdlib::macro_def_expression_batch":
            ("tests/spec_11_stdlib.rs", "macro_def_expression"),
        # §9.10 prelude convenience macros.
        "stdlib::prelude_when_true":
            ("tests/spec_11_stdlib.rs", "macro_when_true"),
        "stdlib::prelude_cond_first":
            ("tests/spec_11_stdlib.rs", "macro_cond_first_match"),
        "stdlib::prelude_thread_first_single":
            ("tests/spec_11_stdlib.rs", "macro_thread_first_single"),
        "stdlib::prelude_vec_elements":
            ("tests/spec_11_stdlib.rs", "macro_vec_elements"),
        # §11.3/§11.4 prelude loads.
        "stdlib::prelude_loads_without_errors":
            ("tests/spec_11_stdlib.rs", "prelude_loads_without_errors"),
        # §12.x RC / heap behaviour (current covers in spec_12_runtime.rs).
        "rc::rc_string_alloc_and_drop":
            ("tests/spec_12_runtime.rs", "string_literal_alloc_drop_balanced"),
        "rc::rc_vec_set_copy":
            ("tests/spec_12_runtime.rs", "vec_set_cow_preserves_original"),
        "rc::rc_string_passed_to_function":
            ("tests/spec_12_runtime.rs", "string_returned_from_function_freed"),
        "rc::rc_adt_in_match_arms":
            ("tests/spec_12_runtime.rs", "adt_product_alloc_and_match_unwrap"),
        "rc::rc_adt_enum_no_alloc":
            ("tests/spec_12_runtime.rs", "adt_sum_none_no_heap_alloc"),
        # §12.9 display (covers in repl_introspection.rs).
        "repl_experience::display_int_result":
            ("tests/repl_introspection.rs", "display_int_result"),
        # §C.6 NFR latency.
        "repl_experience::simple_eval_is_fast":
            ("tests/build_confidence.rs", "perf_simple_eval_latency_under_2000ms"),
        # repl/spec.md §4.1.7 primitive bare-symbol lookup.
        "e2e::e2e_s4_1_7_primitive_bare_symbol_lookup":
            ("tests/repl_introspection.rs",
             "bare_primitive_add_i64_at_prompt_displays_type_and_fqn"),
        # e2e_s4_1_7_neg_primitive_lookup_not_empty — the neg angle
        # ("lookup not empty") has no exact equivalent; closest is the
        # unknown-name neg, a different assertion. Left UNRESOLVED to avoid a
        # neg->pos mis-cite.

        # --- HKT (§3.7 / §5.3.2 / §7.3.4 / §7.7.5) covers in spec_07_traits ---
        "ring2::hkt_trait_declaration":
            ("tests/spec_07_traits.rs",
             "hkt_deftrait_declaration_with_type_constructor_parameter_succeeds"),
        "ring2::hkt_impl_bare_constructor":
            ("tests/spec_07_traits.rs",
             "hkt_impl_targets_bare_type_constructor_not_applied_form"),
        # ring2::neg_hkt_impl_primitive_type_rejected (§3.7) — no negative HKT
        # test in the current suite. Left UNRESOLVED (true gap).
        # §12.2.3 named fn as value.
        "ring0::named_function_as_value":
            ("tests/spec_04_expressions.rs",
             "named_defn_passed_as_value_to_higher_order_fn"),
        # §11.2 / §A.2 trace type + IO type are importable / usable.
        "ring4_trace::trace_type_importable_from_primitives":
            ("tests/spec_04_expressions.rs", "trace_returns_trace_type"),
        "ring4_trace::trace_returns_trace_type_int":
            ("tests/spec_04_expressions.rs", "trace_returns_trace_type"),
        "io::io_pure_int_type":
            ("tests/spec_10_io.rs", "pure_int_unwraps_inline"),
        # ring4_trace::trace_field_accessors_importable (§11.2) — no test for
        # Trace field accessor import specifically. Left UNRESOLVED (true gap).
        # §12.4.2 lazy sequences — no lazy-seq tests in the current suite.
        # Left UNRESOLVED (true gap; the parent-fallback to a drop-glue
        # regression test is NOT a lazy-seq cover).
        # §9.8 auto-gensym hygiene — no gensym hygiene test. Left UNRESOLVED.
    }

    for dc in all_dead:
        smd = spec_md_for(dc.md, root)
        pick = None
        chosen_conf = None
        # Tier 0: exact fn-NAME match in a real test file (the suite reorg
        # preserved many names verbatim — ring0::foo -> spec_NN::foo). Accept
        # only when the surviving test back-references the same spec file (or
        # has no back-ref but the name is unique), so a name collision across
        # chapters can't mis-resolve.
        same = by_name.get(dc.token_name, [])
        if same:
            sf = [t for t in same if t.spec_md == smd]
            if len(sf) == 1:
                pick = sf[0]
            elif len(same) == 1 and same[0].spec_md in (None, smd):
                pick = same[0]
            if pick is not None:
                chosen_conf = "exact"
        if pick is not None:
            resolved.append((dc, pick))
            confidence[id(dc)] = chosen_conf
            continue
        # Tier 0.5: manually-verified override (cross-chapter / renamed).
        ov = OVERRIDES.get(f"{dc.token_file}::{dc.token_name}")
        if ov is not None:
            f, n = ov
            if n in fn_by_file_all.get(f, set()):
                pick = TestFn(file=f, name=n, is_test_file=True,
                              spec_md=None, spec_anchor=None,
                              spec_anchor_kind="", asserts_neg=("_neg" in n))
                resolved.append((dc, pick))
                confidence[id(dc)] = "override"
                continue
        # Tier 1: exact/child §anchor match (highest confidence).
        covers, conf = covers_for_anchor(smd, dc.anchor, idx,
                                         allow_parent=False)
        e2e = [t for t in covers if t.is_test_file]
        pick = None
        chosen_conf = conf
        if e2e:
            num = re.match(r"spec/(\d{2})-", smd)
            if num:
                pref = [t for t in e2e if f"spec_{num.group(1)}_" in t.file]
                if pref:
                    pick = pref[0]
            if pick is None:
                pick = e2e[0]
        elif covers:
            pick = covers[0]
        # Tier 2: explicit reaudit-doc crosswalk by old test name.
        if pick is None:
            rp = reaudit_pick(dc.token_name)
            if rp is not None:
                pick = rp
                chosen_conf = "reaudit"
        # Tier 3: immediate-parent §anchor fallback (review-grade).
        if pick is None:
            pcovers, pconf = covers_for_anchor(smd, dc.anchor, idx,
                                               allow_parent=True)
            pe2e = [t for t in pcovers if t.is_test_file]
            if pe2e:
                num = re.match(r"spec/(\d{2})-", smd)
                if num:
                    pref = [t for t in pe2e if f"spec_{num.group(1)}_" in t.file]
                    pick = pref[0] if pref else pe2e[0]
                else:
                    pick = pe2e[0]
                chosen_conf = "parent"
        if pick:
            resolved.append((dc, pick))
            confidence[id(dc)] = chosen_conf
        else:
            unresolved.append(dc)

    if args.mode == "propose":
        for tier, label in (("exact", "EXACT/CHILD anchor match — high conf"),
                            ("override", "MANUAL OVERRIDE (verified)"),
                            ("reaudit", "REAUDIT crosswalk (old->new by name)"),
                            ("parent", "PARENT-anchor fallback — REVIEW")):
            items = [(dc, t) for dc, t in resolved
                     if confidence.get(id(dc)) == tier]
            print(f"\n# {label} ({len(items)})\n")
            for dc, t in items:
                extra = f"  [parent: {t.spec_anchor}]" if tier == "parent" \
                    else ""
                print(f"{spec_md_for(dc.md, root)}:{dc.lineno}  §{dc.anchor}  "
                      f"tests/{dc.token_file}::{dc.token_name}"
                      f"  ->  {t.file}::{t.name}{extra}")
        print(f"\n# UNRESOLVED ({len(unresolved)}):")
        for dc in unresolved:
            print(f"{spec_md_for(dc.md, root)}:{dc.lineno}  §{dc.anchor}  "
                  f"tests/{dc.token_file}::{dc.token_name}")
        return 0

    if args.mode == "apply":
        apply_tiers = set(args.tiers.split(","))
        # Group resolutions by (md, lineno) -> replacements for each token.
        by_line: dict[tuple[Path, int], list[tuple[DeadCite, TestFn]]] = {}
        for dc, t in resolved:
            if confidence.get(id(dc)) not in apply_tiers:
                continue
            by_line.setdefault((dc.md, dc.lineno), []).append((dc, t))
        changed_files = set()
        for md in spec_files:
            lines = md.read_text().splitlines(keepends=True)
            dirty = False
            for ln in range(1, len(lines) + 1):
                key = (md, ln)
                if key not in by_line:
                    continue
                text = lines[ln - 1]
                for dc, t in by_line[key]:
                    # the source may write either tests/X::n or tests/X.rs::n
                    olds = [f"tests/{dc.token_file}::{dc.token_name}",
                            f"tests/{dc.token_file}.rs::{dc.token_name}"]
                    if t.is_test_file:
                        new_file = t.file[len("tests/"):-len(".rs")]
                        new = f"tests/{new_file}::{t.name}"
                    else:
                        # crate/src unit test: cite full path
                        new = f"{t.file}::{t.name}"
                    for old in olds:
                        if old in text:
                            text = text.replace(old, new)
                            dirty = True
                            break
                lines[ln - 1] = text
            if dirty:
                md.write_text("".join(lines))
                changed_files.add(md)
        print(f"applied {len(resolved)} rewrites across "
              f"{len(changed_files)} files")
        for f in sorted(changed_files):
            print("  ", spec_md_for(f, root))
        return 0

    if args.mode == "dedupe":
        # Remove duplicate `file::name` tokens within each [Tested ...] bracket
        # (an artifact of distinct old tests collapsing to one current cover).
        tok_re = re.compile(
            r"((?:tests/[A-Za-z0-9_]+|crates/[A-Za-z0-9_/]+\.rs|"
            r"src/[A-Za-z0-9_/]+\.rs)::[A-Za-z0-9_]+)")

        def dedupe_bracket(m: re.Match) -> str:
            inner = m.group(2)
            seen = []
            # split on commas, preserve order, drop duplicate tokens
            parts = [p.strip() for p in inner.split(",")]
            kept = []
            seen_tok = set()
            for p in parts:
                tm = tok_re.search(p)
                if tm:
                    t = tm.group(1)
                    if t in seen_tok:
                        continue
                    seen_tok.add(t)
                kept.append(p)
            return f"[Tested{m.group(1) or ''} " + ", ".join(kept) + "]"

        changed = set()
        for md in spec_files:
            text = md.read_text()
            new = TESTED_BRACKET_RE.sub(
                lambda m: dedupe_bracket(m) if tok_re.search(m.group(2))
                else m.group(0), text)
            if new != text:
                md.write_text(new)
                changed.add(md)
        print(f"deduped brackets in {len(changed)} files")
        for f in sorted(changed):
            print("  ", spec_md_for(f, root))
        return 0

    if args.mode in ("stale", "apply-stale"):
        # Stale-pending detector: heading lines tagged [S{M}] / [R{N} S{M}]
        # whose §anchor HAS a covering test. These are covered-but-mislabelled.
        changed = set()
        proposals = []  # (md, lineno, anchor, tag, cover_TestFn)
        for md in spec_files:
            smd = spec_md_for(md, root)
            lines = md.read_text().splitlines(keepends=True)
            for ln, raw in enumerate(lines, start=1):
                hm = HEADING_RE.match(raw)
                pm = PENDING_RE.search(raw)
                if not (hm and pm):
                    continue
                anchor, kind = heading_anchor(hm.group(2))
                if kind != "num":
                    continue
                covers, _conf = covers_for_anchor(smd, anchor, idx,
                                                  allow_parent=False)
                e2e = [t for t in covers if t.is_test_file]
                pick = None
                if e2e:
                    num = re.match(r"spec/(\d{2})-", smd)
                    pref = ([t for t in e2e
                             if num and f"spec_{num.group(1)}_" in t.file]
                            if num else [])
                    pick = pref[0] if pref else e2e[0]
                elif covers:
                    pick = covers[0]
                if pick:
                    proposals.append((md, ln, anchor, pm.group(0), pick))
        if args.mode == "stale":
            print(f"# STALE-PENDING [S]/[R S] sections WITH a covering test "
                  f"({len(proposals)})\n")
            for md, ln, anchor, tag, t in proposals:
                fcite = (f"tests/{t.file[len('tests/'):-len('.rs')]}::{t.name}"
                         if t.is_test_file else f"{t.file}::{t.name}")
                print(f"{spec_md_for(md, root)}:{ln}  §{anchor}  {tag}  "
                      f"->  [Tested {fcite}]")
            return 0
        # apply-stale: rewrite the pending tag to [Tested ...].
        # Scoped to --stale-scope (the FIXME-sanctioned io sweep is
        # spec/10-io.md only; chapter-level headings elsewhere are NOT safe to
        # bulk-flip — a section earns [Tested] only when ALL children are).
        scope = args.stale_scope
        by_md: dict[Path, list] = {}
        for md, ln, anchor, tag, t in proposals:
            if scope and spec_md_for(md, root) != scope:
                continue
            by_md.setdefault(md, []).append((ln, tag, t))
        for md, items in by_md.items():
            lines = md.read_text().splitlines(keepends=True)
            for ln, tag, t in items:
                fcite = (f"tests/{t.file[len('tests/'):-len('.rs')]}::{t.name}"
                         if t.is_test_file else f"{t.file}::{t.name}")
                lines[ln - 1] = lines[ln - 1].replace(
                    tag, f"[Tested {fcite}]", 1)
            md.write_text("".join(lines))
            changed.add(md)
        n_applied = sum(len(v) for v in by_md.values())
        print(f"apply-stale: upgraded {n_applied} [S] tags across "
              f"{len(changed)} files"
              + (f" (scope={scope})" if scope else ""))
        for f in sorted(changed):
            print("  ", spec_md_for(f, root))
        return 0

    # ---- check mode ----
    print("=== spec_coverage_reconcile: spec->test direction ===",
          file=sys.stderr)
    print(f"  dead citations (file deleted): {len(all_dead)}", file=sys.stderr)
    print(f"  live citations (file exists):  {len(all_live)}", file=sys.stderr)
    print(f"  ...of which name not found:    {len(live_broken)}",
          file=sys.stderr)
    print(f"  dead resolvable by anchor:     {len(resolved)}", file=sys.stderr)
    print(f"  dead UNRESOLVABLE:             {len(unresolved)}",
          file=sys.stderr)

    if live_broken:
        print("\nLIVE-BUT-BROKEN (file exists, fn missing):", file=sys.stderr)
        for dc in live_broken:
            print(f"  {spec_md_for(dc.md, root)}:{dc.lineno}  "
                  f"tests/{dc.token_file}::{dc.token_name}", file=sys.stderr)

    if unresolved:
        print("\nDEAD-UNRESOLVABLE (no covering test by anchor):",
              file=sys.stderr)
        for dc in unresolved:
            print(f"  {spec_md_for(dc.md, root)}:{dc.lineno}  §{dc.anchor}  "
                  f"tests/{dc.token_file}::{dc.token_name}", file=sys.stderr)

    fail = bool(all_dead) or bool(live_broken)
    return 1 if fail else 0


if __name__ == "__main__":
    sys.exit(main())
