---
id: ACT-0976
title: Assess ownership residue after a macro clause reports a runtime error
status: deferred
priority: normal
from: design
to: qa
sprint: 122
filed_at: 2026-09-21
refers_to:
  - design/int/macro-turn-ownership.md
  - src/expander.rs
  - crates/cranelisp-intrinsics/src/panic.rs
  - crates/cranelisp-backend/src/primitives_inline.rs
  - tests/macro_turn_marshal_leak_0889.rs
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **S122 work (K2), evidence only.** `test` measures one marginal pair for the residue after a macro runtime error. A balanced pair retires this action. A confirmed ordinary leak becomes a committed RED carried to S123 under K7. A double discharge, use-after-free or corruption returns to the user with its attribution for a fix decision.

## S122 K2 result (qa, 2026-09-30): ordinary leak, carried to S123 under K7

This is the first deferral.

**Measurement.** `macro_turn_marshal_leak_0889::macro_runtime_error_expansion_balances_against_successful_twin`
is RED. Source `f0d1006f…`; log `.local/s122-final-test/k2-pairs.log`.
- Control `(okm 42)`: 2 allocations, 2 deallocations.
- Subject `(boom 42)` (`div-i64 1 0`): 2 allocations, 0 deallocations.
- Residual: +2. Both exits are 0, and there is no seam violation.

**Leak, not a safety fault.** The two cells are the marshalled argument tree.
The session continued.

**The residue is the argument tree only.** Nothing is allocated before the
error, so the pair observes the skipped frame cleanup, not a discarded result
word. The result-word face stays unobserved.

**Authority.** spec §12.3.1 item 1 requires the release.
`design/int/macro-turn-ownership.md` Rule 3 records this path as an unbounded
as-built residual. It does not relax the requirement.
- The cell asserts spec conformance. It claims no protocol regression, so it
  is consistent with Rule 3's warning against misattribution.
- The RED stays failing and un-ignored as the carried record.

**Mechanism (provisional).** The residue is consistent with Rule 3's path:
`runtime/panic` returns, and the panicking clause frame skips the compiled
cleanup that owns the argument. It was not observed at that seam.
- **Refuted if** the clause's CLIF shows the argument release on the error
  path, or the residue changes with the discarded-result face alone.
- The cell's provisional `locus=src/expander.rs::invoke_clause` names the
  host's discard site, not the skipped cleanup. `test` re-points it when the
  mechanism is observed.

**When resumed.** Attribute at the runtime-error return path, which spans
backend panic emission and `intrinsics` `runtime/panic`. The repair is
cross-context, so it goes through `arch` before `design`.

## Observation and limit

The ownership-document review found a runtime-error path distinct from a
hardware trap or Rust panic. `runtime/panic` sets an error flag and returns;
the generated panicking function returns a dummy zero without its compiled
cleanup, while callers can continue. `invoke_jit_protected` observes the error
flag before handing the returned word to `invoke_clause`, so int discards that
word without adopting or releasing it.

The macro ownership contract now states this accurately in Rules 3–4. The
trap-path argument-tree bound does not establish a bound for this path.
Source was read; residue has not been measured or reproduced in a dedicated
language-level test. A returned word after continued execution is not assumed
to be a valid tree that can safely be released.

## Required disposition

QA assesses risk and existing evidence before allocating work. Establish a
minimal macro invocation and discriminating control if reproduction is needed;
separate skipped frame cleanup from any discarded result allocation. If a
violated requirement is confirmed, retain a permanent failing, unignored
spec-traced reproduction before routing repair. Do not add an unsafe release
or infer a new acceptable residue bound from this source observation.

Provenance: review `efb40737-5c22-4171-bf5a-8267915c8ce5` and design
`01c55402-0673-4b8e-a49e-4a68efb98d00`, S122 ownership-document consolidation.
