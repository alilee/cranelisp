---
number: 0414
target: /qa
filed_by: /sprint
filed_at: 2026-06-20
sprint_filed: 86
refers_to: tests/plan/spec_link_check.py, spec/*.md, repl/spec.md, tests/spec_NN_*.rs
status: open
---

# Extend `spec_link_check.py` to validate the spec→test direction (guard against citation rot)

## Issue

The S86 UAT spec-coverage audit (/qa) found 641/670 spec-side `[Tested tests/X::name]`
citations point at deleted test files, and 396/476 cited test names don't exist
anywhere (FIXME 0412 / 0413). Root cause: the test suite was reorganised
(`tests/ringN.rs` → `tests/spec_NN_*.rs`) and the spec annotations were never
updated — and **nothing caught it**, because the existing linter
(`tests/plan/spec_link_check.py`) only checks the **test→spec** direction (does a
test's `// spec:` `§anchor` exist in the spec). The reverse direction — does a
spec's cited test actually exist — is unchecked, and that is exactly the
direction that rotted.

## Proposed resolution

Extend `spec_link_check.py` (or add a sibling check) to validate the spec→test
direction:

1. Parse every `[Tested tests/FILE::name]` / `[Tested+Neg tests/FILE::name]`
   annotation in `spec/*.md` + `repl/spec.md`.
2. Assert `tests/FILE.rs` exists.
3. Assert it contains `fn name` (accounting for macro-generated tests — the
   audit found a few names that are macro-produced; either expand the macro
   forms or whitelist the generator).
4. Report violations with `file:line` + the dead citation, and exit non-zero so
   it can gate CI / the sprint wave check.

Bonus (optional): flag `[S{M}]` annotations whose section IS now covered by a
test with a matching `// spec:` anchor (the stale-pending detector) — this would
have caught the `spec/10-io.md` 45-tag block automatically.

## Operational implication / Context

- /qa owns the test plan + `spec_link_check.py`.
- **Sequence this FIRST** — before FIXME 0412 / 0413 reconciliation — so the
  linter mechanically validates the rewritten citations as they land and the rot
  cannot silently recur after the cleanup. This is the durable guard; the
  reconciliation is the one-time cleanup.
- Once green, the spec→test check becomes a wave-gate / CI invariant.
