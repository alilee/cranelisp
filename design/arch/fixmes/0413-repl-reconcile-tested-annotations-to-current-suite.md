---
number: 0413
target: /repl
filed_by: /sprint
filed_at: 2026-06-20
sprint_filed: 86
refers_to: repl/spec.md ([Tested …] annotations), tests/plan/wave-5.6-e2e-reaudit.md, tests/repl_introspection.rs, tests/repl_negative.rs, tests/spec_NN_*.rs
status: open
---

# repl/spec.md `[Tested …]` annotations cite deleted test files (worst-affected file)

## Issue

The S86 UAT spec-coverage audit (/qa) found `repl/spec.md` is the single
worst-affected file in the project-wide spec→test annotation rot (see
**FIXME 0412 (→/spec)** for the full picture and numbers). Its `[Tested …]`
citations point overwhelmingly at test files that **no longer exist**:

- `tests/e2e::*` — 88 citations (file deleted)
- `tests/repl_experience::*` — 41 citations (file deleted)
- `tests/ring3_repl::*` — 23 citations (file deleted)
- plus `tests/ring2::*`, `tests/macros::*`, `tests/sprint23::*`,
  `tests/wave6_demo_repros::*`
- `tests/repl_introspection.rs` *does* exist, but most cited names don't match
  the current ones.

**~160+ dead citations** in this one file. The actual REPL coverage is strong
and well-organised — `tests/repl_introspection.rs` (126 tests, 1:1 `// spec:`
back-refs), `tests/repl_negative.rs` (48 tests) — so this is a labelling rot,
not a coverage gap. The test→spec direction is healthy; only the spec→test
annotations lie.

Note the related dead `/disasm` finding (the dead-`/disasm` defect (resolver /int; failing test `disasm_command_shows_native_code_for_compiled_fn` is the record — no FIXME)): the spec
command table marks `/disasm` `[R4 S10]` — which in that case is *honest*
(the command genuinely never worked). Distinguish honest `[S…]`/`[R4 S…]` tags
(real gaps) from the rotted `[Tested tests/<deleted>::…]` tags (false coverage)
during the sweep.

## Proposed resolution

1. Apply the `tests/plan/wave-5.6-e2e-reaudit.md` crosswalk (+ the introspection
   reaudit, if present) to rewrite every `[Tested tests/e2e::old]` /
   `[Tested tests/repl_experience::old]` / `[Tested tests/ring3_repl::old]` →
   the real `tests/repl_introspection.rs::…` / `tests/repl_negative.rs::…` /
   `tests/spec_NN_*.rs::…` name.
2. Re-examine the `[Tested]` (positive-only) annotations on sections whose text
   makes exclusion/MUST-NOT claims — candidates from the audit: §1.2 Expression
   Results, §1.3 Definition Results — and upgrade to `[Tested+Neg]` where the
   real test (once identified) asserts the negative.
3. Coordinate with **FIXME 0414 (→/qa)**: run the extended `spec_link_check.py`
   (spec→test direction) over `repl/spec.md` to verify every rewritten citation
   resolves; sequence this work after 0414 so the linter validates it.

## Operational implication / Context

- /repl owns `repl/spec.md`. Mechanical crosswalk pass; high volume but
  low-risk.
- Same root cause as FIXME 0412; same recommended sequencing (behind the 0414
  guard). Good fit for the S87 deep-audit arc.
