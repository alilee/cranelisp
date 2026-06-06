---
number: 0276
target: /qa
filed_by: /sprint
filed_at: 2026-06-06
sprint_filed: 76
refers_to: src/bootstrap.rs (synthetic accessor Defs with ast: Some), src/exe.rs / the link-mode codegen batch, tests/CLAUDE.md §"Isolating Cross-Crate Failures", design/arch/fixmes/0275-dev-backend-trace-object-mode-relocations.md
status: open
---

# Link mode: bootstrap-synthesised accessor Defs unresolved (`can't resolve symbol nanos`) + the failure parks the session instead of erroring

## Issue

Probe (2026-06-06, /sprint): `--link` of a program consuming a trace via the
`nanos` accessor fails with `can't resolve symbol nanos`, and then the compiler
**parks forever** (worker panic → main thread waits; ~0:01 CPU, no exit, no
binary). Two distinct defects:

1. **Synthetic accessor Defs are not emitted in link mode.** `nanos` (and
   presumably the other bootstrap-synthesised Defs with `ast: Some` — Trace
   accessors, possibly others) resolve and run fine in REPL/`--run` but are
   missing from object emission. Likely the link-mode codegen batch never
   includes the bootstrap-seeded synthetic Defs (adjacent to the 0249-b
   constructor-batch derivation, which was fixed for the JIT path in S76 W2 —
   verify whether the link path shares that derivation).
2. **Failure mode is a hang, not an error.** The unresolved-symbol panic kills
   a worker; the session parks instead of surfacing the error and exiting
   non-zero. Same stuck-owner robustness family as the trace-guard panic note
   (0258 NOTE-2) and the historical FIXME 0018 publish-vs-flag race.

## Proposed resolution

1. /qa authors the minimal failing e2e repros (failing-not-ignored,
   `// spec:` appendix-A accessor rows / §4.12.9):
   - link-mode accessor consumption: 3-line `(nanos (trace (work 41)))` shape
     — asserts exit 0 + correct value; currently hangs, so the test needs the
     harness timeout to convert the park into a failure (assert the compile
     completes — the hang IS part of the defect).
   - if isolable cheaply, a trace-free variant proving the defect is the
     synthetic-Def emission, not trace (e.g. link-mode use of another
     bootstrap-synthesised Def — an Option/Sexp helper accessor if one exists,
     else note that trace accessors are the only synthetic-AST Defs and say so).
2. Triage routes the fix: defect 1 → /dev (int) link-batch derivation or
   /dev (backend) object emission (the repro decides); defect 2 → the
   worker-panic→park robustness fix is its own item — name it in the ledger
   even if the fix defers (it converts every future link-mode defect from
   "clear error" into "hang", multiplying triage cost).

## Operational implication / Context

User-decided 2026-06-06: the trace `--link` story is fixed in-sprint (0275);
this defect blocks the accessor-shaped half of that acceptance. Sequencing:
repros land with 0258's batch (Wave 3/4); fix follows triage. Probe record in
0275 §Context.
