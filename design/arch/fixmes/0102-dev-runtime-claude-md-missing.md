---
number: 0102
target: /dev
filed_by: /design (runtime)
filed_at: 2026-05-02
sprint_filed: 64
refers_to: crates/cranelisp-runtime/CLAUDE.md (missing), design/runtime/runtime.md §10, sprints/triad-shared.md
status: open
---

# Author `crates/cranelisp-runtime/CLAUDE.md`

## Issue

`crates/cranelisp-runtime/CLAUDE.md` does not exist. Every other implementation crate in the workspace ships a per-crate `CLAUDE.md` carrying local conventions, API gotchas, and data-structure-specific-to-the-crate notes per `triad-shared.md` step 4 (e.g., `crates/cranelisp-frontend/CLAUDE.md`, `crates/cranelisp-typecheck/CLAUDE.md`).

When `/dev` next narrow-deploys to the runtime crate, there is nothing local to read — the agent reads `design/runtime/runtime.md` (the design layer, not the working layer) and the source files directly. This is a workflow gap, not a correctness gap, but it adds onboarding friction every sprint.

## Proposed resolution

When `/dev` next narrow-deploys to runtime (e.g., as part of FIXME 0098 work, or any future runtime change), author `crates/cranelisp-runtime/CLAUDE.md` covering at minimum:

- Heap layout offsets (`HeapHeader::SIZE`, `HeapHeader::RC_OFFSET`, closure layout `+24 = drop_glue_ptr`, Vec layout, HeapString layout).
- RC discipline split: `consume_shallow` (no heap sub-refs) vs `consume_*` (recursive) vs `dec_shallow_io` (Decision 29 IO-trampoline carve-out).
- The IO-trampoline `is_fresh` invariant (load-bearing per `io.rs` §3.5; see `design/runtime/runtime.md` §7).
- The Decision 24 extern boundary contract — every `extern "C"` function consumes its heap args; internal Rust helpers may use any local convention.
- The Decision 40 observer pattern — `io.rs` event emission goes through `io_observer::current()`; observer state lives in int.
- JIT-symbol-naming gotcha — runtime extern functions are named by string at codegen time; renaming `vec_push_grow` is a backend-codegen change as much as a runtime-API change.
- The Cranelift JIT can't unwind through JIT frames — `runtime_panic` uses a thread-local sentinel + `take_runtime_error()` poll, NOT `panic!()`.

Reference `design/runtime/runtime.md` for the full architectural narrative; the CLAUDE.md is the working-layer cheat sheet, not the design layer.

## Operational implication / Context

Workflow consistency across crates. The CLAUDE.md gap is the smallest possible — every other crate has one, runtime should too. Bundling with the next runtime change is the cheapest path; standalone authoring is also fine if the user wants to close the gap proactively.
