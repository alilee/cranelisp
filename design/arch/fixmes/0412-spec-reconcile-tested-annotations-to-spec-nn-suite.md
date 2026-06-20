---
number: 0412
target: /spec
filed_by: /sprint
filed_at: 2026-06-20
sprint_filed: 86
refers_to: spec/*.md ([Tested …] annotations), tests/plan/wave-5.6-ring0-reaudit.md, wave-5.6-ring1-reaudit.md, wave-5.6-ring2-reaudit.md, wave-5.6-e2e-reaudit.md, tests/spec_NN_*.rs
status: open
---

# Spec-side `[Tested …]` annotations cite deleted test files/names (false coverage at scale)

## Issue

S86 UAT spec-coverage audit (/qa, read-only) found the spec→test traceability
layer is ~96% broken. The `[Tested tests/X::name]` annotations were written
against the OLD ring-based test organisation (`tests/ring0.rs`, `tests/ring1.rs`,
`tests/ring2.rs`, `tests/e2e.rs`, `tests/macros.rs`, `tests/rc.rs`,
`tests/modules.rs`, `tests/stdlib.rs`, …). That suite was re-authored into
`tests/spec_NN_*.rs` with new test names; the crosswalk was captured in
`tests/plan/wave-5.6-*-reaudit.md` but **never applied back to the spec
annotations**.

Hard numbers (cross-checked across `spec/*.md` + `repl/spec.md`, not sampled):

| Metric | Count |
|---|---|
| Spec-side `tests/X::` citations total | 670 |
| …pointing at a dead/nonexistent test file | 641 (96%) |
| …pointing at a real test file | 29 (4%) |
| Unique cited test names | 476 |
| …that exist as a `fn` anywhere | 80 (17%, incl. ≥2 false positives) |
| …that do not exist anywhere | 396 (83%) |

The *underlying coverage is largely real* — the tests exist under new names
(test→spec back-refs are a near-perfect ~1:1 in `spec_NN_*.rs`). It is the
**spec-side annotations that lie about where** the covering test lives.

This FIXME covers `spec/*.md` (the language spec, /spec-owned). `repl/spec.md`
is the worst-affected single file (~160+ dead citations) and is /repl-owned —
tracked separately as **FIXME 0413 (→/repl)**.

Per-file dead-citation breakdown (to nonexistent files):
- `spec/04-expressions.md` — ring0(31), ring1(21), ring2(11), e2e(5), ring4_trace(6)
- `spec/appendix-a-builtins.md` — ring1(38), ring0(22)
- `spec/06-pattern-matching.md` — ring1(37), ring0(9) → real: `tests/spec_06_pattern_matching.rs`
- `spec/05-definitions.md` — ring2(25), ring1(12), ring0(9) → real: `tests/spec_05_definitions.rs`
- `spec/07-traits.md` — ring2(21) → real: `tests/spec_07_traits.rs`
- `spec/02-grammar.md` — ring2(11), ring0(10) → many real names live in frontend-crate `#[cfg(test)]` (`test_parse_*`), not a `tests/` file
- `spec/08-modules.md` — ring2(18), modules(9), sprint59_neg(4) + 7 already-correct `spec_08_modules::*`
- `spec/12-runtime.md` — ring0(11), rc(9), repl_experience(6); §12.5 TCO `tco_*`→`spec_12_runtime.rs` ALREADY correct (partial reconcile)
- `spec/09-macros.md` — macros(20), ring3_repl(8), stdlib(7) → real: `tests/spec_09_macros.rs`
- `spec/03-types.md` — ring1/ring2/ring0/ring4_trace → real: `tests/spec_03_types.rs`
- `spec/01-lexical.md`, `spec/11-stdlib.md`, `spec/appendix-c-nfr.md` — similar

## Also: stale-pending (`[S{M}]` that is now covered)

- **`spec/10-io.md` — the whole file** carries ~45 `[S10]` (untested/scheduled)
  tags on requirements that `tests/spec_10_io.rs` (52 tests, `// spec:` refs to
  §10.1/§10.2/§10.3/§10.6.2/…) already covers. High-confidence,
  independently actionable: upgrade those `[S10]` → `[Tested tests/spec_10_io.rs::…]`.
- `spec/12-runtime.md` (22 `[S]`), `spec/03-types.md` (22 `[S]`),
  `spec/02-grammar.md` (6 `[S]`) — mixed stale-pending vs true gaps; triage
  per-anchor against the `spec_NN_*.rs` `// spec:` refs after the crosswalk.

## Proposed resolution

1. Apply the `tests/plan/wave-5.6-*-reaudit.md` crosswalk to rewrite every
   `[Tested tests/ringN::oldname]` → `[Tested tests/spec_NN_*.rs::realname]`
   (e.g. `ring2.rs::user_trait_simple` → `spec_07_traits.rs::…`). Where the real
   test is a frontend/typecheck crate unit test (`test_parse_*`), cite it as
   such or downgrade to the appropriate annotation.
2. Sweep `spec/10-io.md` `[S10]` → `[Tested …]` (covered).
3. Triage the remaining `[S]` tags (runtime/types/grammar) into stale-pending vs
   true gap; retag accordingly (request /qa confirmation for ambiguous anchors).
4. Coordinate with **FIXME 0414 (→/qa)**: the extended `spec_link_check.py`
   (spec→test direction) should be run to verify the reconciliation lands clean
   and to prevent recurrence — ideally action this FIXME *after* 0414 exists so
   the linter mechanically validates every rewritten citation.

## Operational implication / Context

- Large but mostly mechanical (crosswalk-driven). Not a missing-tests problem —
  a labelling/bookkeeping rot from the suite reorg.
- Best sequenced behind FIXME 0414 (the guard) so it can't silently re-rot.
- Candidate for the S87 deep-audit arc rather than S86 close (volume), but the
  `spec/10-io.md` sweep is small enough to do standalone if desired.
