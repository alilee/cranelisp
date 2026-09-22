---
id: ACT-0976
title: Assess ownership residue after a macro clause reports a runtime error
status: open
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
---

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
