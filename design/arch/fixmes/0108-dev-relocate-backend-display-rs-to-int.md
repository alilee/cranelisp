---
number: 0108
target: /dev
filed_by: /design
filed_at: 2026-05-02
sprint_filed: 64
refers_to: design/arch/bounded-contexts.md §6 (int — owns REPL display), design/backend/backend.md §3.1 (display.rs row), crates/cranelisp-backend/src/display.rs, src/
status: open
---

# Relocate `display.rs` from `cranelisp-backend` to `int` (REPL display ownership)

## Issue

`crates/cranelisp-backend/src/display.rs` (831 LOC) implements value/type formatting for REPL output. Per `design/arch/bounded-contexts.md` §6, REPL display orchestration belongs to `int`, not `cranelisp-backend`. The current placement is historical — value-formatting helpers landed alongside backend's own debug printing (CLIF dump, disasm) and accreted into a full REPL display layer over time.

The backend bounded context (BC §3) is "typed AST → executable". REPL display is downstream of execution and crosses no boundary backend exposes — it consumes `ModuleEntry::Def` and runtime values via the public `cranelisp-runtime` and `cranelisp-types` surfaces. There is no backend-internal type that REPL display needs to reach into.

The 831 LOC is the second-largest file in `cranelisp-backend` after `lib.rs`. Relocation reduces backend's footprint by ~10% and aligns the source layout with the BC.

## Proposed resolution

Move `crates/cranelisp-backend/src/display.rs` to `src/display.rs` (or a sub-module of the existing `src/` REPL session structure — `/dev` to determine the best landing spot). Update `crates/cranelisp-backend/src/lib.rs` to remove the module declaration and the `pub use` line (if present). Update `int` callsites: `use cranelisp_backend::display::*` → `use crate::display::*` (or whatever the new path becomes).

If `display.rs` reaches into any backend-private type, those types should already be public per the facade — confirm before moving. If not, a small refactor to expose them (or to inline the access) precedes the move.

Bundle naturally with FIXME 0099 (GotObserver) or FIXME 0100 (single-consumer-type relocation) — both are `/dev`-narrow to backend + int and touch the same boundary.

## Operational implication / Context

`display.rs` likely depends on `cranelisp-runtime` for value introspection and `cranelisp-types` for `ModuleEntry::Def`/`Type`/`Scheme` shapes. These deps move with the file — `int` already depends on both crates, so the move is dep-graph-neutral.

The relocation is mechanical (no semantic change); the test surface for display formatting moves alongside the file. Pre-existing display tests in `display.rs` continue to live next to the implementation.

After this lands, backend's `lib.rs` test bulk (per audit MED-2 — currently 3,932 lines of tests in `lib.rs`) becomes the next-largest file-relocation target, and the backend crate is closer to its BC §3 footprint.
