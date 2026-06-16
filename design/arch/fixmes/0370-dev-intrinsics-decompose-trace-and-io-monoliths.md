---
number: 0370
target: /dev
filed_by: /sprint
filed_at: 2026-06-16
sprint_filed: 83
refers_to: audits/intrinsics-2026-06-14.md (HIGH-3, MED-1, LOW), crates/cranelisp-intrinsics/src/trace.rs (~2297 LOC), crates/cranelisp-intrinsics/src/io.rs (~1254 LOC)
status: open
---

# cranelisp-intrinsics: decompose the trace.rs / io.rs monoliths + dedup heap_access

## Issue (0101 audit — intrinsics, 2026-06-14)

From `audits/intrinsics-2026-06-14.md`:
- **HIGH-3 — monoliths:** `trace.rs` (~2,297 LOC) and `io.rs` (~1,254 LOC) with overlong functions (`run_io_trampoline_inner` ~245 LOC; `cranelisp_trace_swap_got` ~126 LOC), past the project ~100-line guidance. Lower correctness-risk than the backend equivalents (dense local tests) but high extension cost. The pure `DisplayDescriptor` formatter is the obvious self-contained split out of `trace.rs`.
- **MED-1 — heap read/write duplication:** extract a single `heap_access` read/write module (the offset-arithmetic is open-coded in several places).
- **LOW — dead `dispatch_par_branches` stub** (delete); **io_observer::emit data↔fn transmute** (replace/bless).

## Proposed resolution
`/dev` narrow-deployed on `cranelisp-intrinsics`: split the pure `DisplayDescriptor` formatter out of `trace.rs`; decompose `run_io_trampoline_inner`; extract a `heap_access` module (Principle 7); delete the dead `dispatch_par_branches` stub; bless or replace the io_observer transmute. Behaviour-preserving refactor — the dense local tests are the guard; keep them green (`--workspace`).

## Context
0101 audit pass. Structural debt, not defects. Paired with FIXME 0369 (the /arch BC/count half). Forward-flow; not S83-blocking.
