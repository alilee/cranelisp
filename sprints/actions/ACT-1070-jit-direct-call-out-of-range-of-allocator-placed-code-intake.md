---
id: ACT-1070
title: A JIT-compiled direct call lands outside its range when the allocator places two functions more than 128 MB apart
status: open
priority: blocking
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - crates/cranelisp-backend/src/jit.rs::finish_builder
  - spec/03-types.md §3.10
  - tests/spec_07_traits.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on `target/debug/cranelisp` built from `24c42430`, aarch64 Linux,
2026-11-18. Found by `dev` as the run-dependent cells
`spec_07_traits::s124_two_member_depth_64_run` and `_link`.

Subject: T-DEPTH-c's 64-level program (`s124_two_member_depth_program(64)`)
as `user.cl`, beside the primitives-only prelude fixture as `prelude.cl`, run
with `--run user.cl`. It must exit 64.

| Leg | Runs | Exit 64 | Signal 11 | `cranelift-jit` assertion |
|---|---|---|---|---|
| Subject, 16 at once, fresh directories | 96 | 55 | 38 | 3 |
| Subject, one at a time | 20 | 14 | 6 | 0 |
| Control: `MALLOC_ARENA_MAX=1`, 16 at once and one at a time | 84 | 84 | 0 | 0 |
| `MALLOC_ARENA_MAX=2`, one at a time | 12 | 5 | 0 | 7 |
| The same program with no `prelude.cl` beside it, `--run` and `--link` | 440 | 440 | 0 | 0 |
| One member at 64 levels; two members at 32, 48 and 56 levels | 48 each | all | 0 | 0 |

## Classification: a defect, memory-unsafe

A legal program ends on a signal, or jumps to an address that holds no
function. Spec §3.10 requires the 64-level chain to compile and run.

## Attribution

- **Mechanism, observed at its seam.** A fault handler preloaded into the
  failing process reported, on both signal-11 runs read, a fault at the
  program counter in a writable, non-executable mapping, reached from a JIT
  code page. On the run whose instruction was decoded, the caller is a `bl`
  whose encoded target is exactly 256 MB below a mapped JIT code page: the
  real distance exceeded the instruction's ±128 MB range and the
  displacement wrapped.
- **The two faces are one mechanism.** `cranelift-jit` 0.116.1 takes each
  function's code memory from the global allocator (its `PtrLen::with_size`),
  so placement follows the allocating thread's arena. Its range check for
  the `Arm64Call` relocation tests 27 bits of a 26-bit signed field, so a distance between 128 MB and 256 MB passes the
  check and wraps (signal 11), and a distance of 256 MB or more fails it
  (the assertion, reported as a codegen error).
- **Control.** `MALLOC_ARENA_MAX=1` differs from the subject only in where
  the allocator places memory, and never fails.
- **Owner: backend** (`jit.rs` constructs the JIT with the default memory).
- **Not established:** why this program needs a `prelude.cl` beside it to
  reach the distance, and whether a program that compiled before S124 W3
  reaches it. Two trait-free programs with 64 and 96 generic instances did
  not (96 runs each). The subject itself did not compile before T4.
- **Refuted if** a failing run shows the `bl` target inside a mapped,
  executable JIT page.

## Evidence allocation

- **`test`:** one cell beside T-DEPTH-c in `tests/spec_07_traits.rs`,
  aarch64 Linux only. The subject runs 16 times and each run must exit 64;
  the control runs 16 times with `MALLOC_ARENA_MAX=1`. Cite
  `// spec: spec/03-types.md §3.10` and
  `// defect: class=jit-call-out-of-range locus=crates/cranelisp-backend/src/jit.rs::finish_builder found=S124 owner=/dev`.
  At the observed rate the subject fails in more than 99 of 100 executions
  of the cell.
- **`dev`(backend):** a module row that places two functions of one JIT
  module further apart than the direct-call range and calls one from the
  other.
- T-DEPTH-c's 64-level `--run` and `--link` cells are unchanged. They are
  run-dependent on this defect until it is corrected.

## Completion evidence

The cell fails on a signal or the assertion before the correction and passes
after it; the control passes throughout. `qa` re-runs the subject 96 times,
16 at once, on the corrected build and records the count.
