---
number: 0255
target: /dev (backend)
filed_by: /arch
filed_at: 2026-06-04
sprint_filed: 76
refers_to: design/arch/tracing.md §3.3 §3.4 §5, design/arch/bounded-contexts.md §3 (the (trace ...) codegen role), crates/cranelisp-backend/src/compiler/trace_codegen.rs
status: open
---

# Bake display descriptors, move discovery into codegen (swap ALL symbol tables), rework trace_codegen, force-link trace into exe-bundle

## Issue

Per the 2026-06-04 trace ruling (`design/arch/tracing.md` TARGET STATE + BC §3 "the `(trace ...)`
codegen role"), backend gains three trace responsibilities and `--link` support.

## Proposed resolution

1. **Discovery moves into backend codegen (swap ALL symbol tables).** Delete the dependence on int's
   pre-built `traced_fns`. In `trace_codegen.rs`, compute the traced set by iterating `symbol_tables`
   (which `compile_to_module` already receives — BC §3 "`symbol_tables` is the single codegen source"):
   - Iterate **every module** (no project-root filter; primitives included — user "all symbol tables"
     ruling). Per module take `got().base_ptr()`; select `Def { got_slot: Some, .. }` entries whose GOT
     slot holds a non-zero callable address; skip constrained-poly base names. Read the callable address
     from the **GOT slot** (the single source of truth, BC §3 invariant 3), NOT from `entry.code` — this
     naturally includes primitives (whose entries are `code: None` but whose fn ptrs live in
     `PRIMITIVES_TABLE.got()`) without a code-marker special case. Take arity/param_types/result_type
     from `entry.scheme.ty` (`Type::Fn`, else skip).
   - `TracedFnInfo` becomes backend-internal (it leaves the cross-crate boundary). Remove the
     compile-context `traced_fns: Option<&[TracedFnInfo]>` field from `compiler/mod.rs`.

2. **Display-descriptor baking** (`tracing.md` §3.4 — the meatiest element). For each traced param +
   result, build a self-contained `DisplayDescriptor` (the `#[repr(C)]` type is intrinsics-owned per
   FIXME 0254; co-design its layout). Resolve it once at wrapper-compile time from `param_types` /
   `result_type` + the module's `TypeDefInfo` (in `symbol_tables`), **substituting the call site's
   concrete type args** into polymorphic ADT fields (the same substitution `src/display.rs::build_adt_subst`
   does today). The descriptor replaces today's leaked `Box<Type>` second arg to `cranelisp_trace_format`.
   Emit it as program-lifetime data in **both** module modes:
   - **JIT** — leak the descriptor tree (arena/`Box`) and embed its address as `iconst` (as the
     `Box<Type>` is embedded today).
   - **Object (`--link`)** — emit the descriptor tree as a read-only data symbol (`DataDescription`) and
     reference it via a **relocation** (same family as the GOT data symbol + literal pools). `/arch`'s
     target encoding: a flat position-independent **arena blob** — descriptors as fixed-size records with
     child references as byte-offsets-within-the-blob, one data symbol per wrapper's descriptor set, one
     relocation per wrapper reference, no intra-blob relocations. Confirm the exact encoding with /dev
     (intrinsics) since intrinsics walks it.

3. **`trace_codegen.rs` rework.** Update `compile_trace` / `compile_trace_wrapper_fn` to (a) call
   discovery internally, (b) pass `descriptor_ptr` (not `type_ptr`) to `cranelisp_trace_format`, (c) emit
   the `TRACE_BODY_RUNNING` set/clear around the body if FIXME 0254's guard needs a codegen touch-point
   (coordinate — the alternative is the swap/collect bracketing it at runtime). The extern declarations,
   GOT copy-swap, body-discard, restore, and collect sequence are otherwise unchanged. The externs now
   resolve from `intrinsics_table()` (FIXME 0254), not int's `int_intrinsics()`.

4. **Exe-bundle force-link (all-modes support).** Trace now works in `--link`. Restore the
   `pub use cranelisp_intrinsics::trace;` force-link line in `crates/cranelisp-exe-bundle/src/lib.rs`
   (it was deleted under D40). NOTE: exe-bundle is an `/int` implementation detail (BC §6) — coordinate
   the actual edit with /dev (int) / /sprint; the *reason* for the line (trace is now an ordinary
   force-linked intrinsic) is this FIXME's. Update the exe-bundle crate-root `//!` to list `trace` among
   the force-linked intrinsics submodules.

5. Run `cargo nextest run -p cranelisp-backend` + regenerate `crates/cranelisp-backend/public-api.txt`
   if the surface changed (TracedFnInfo demotion to internal). Fix introduced warnings.

## Operational implication / Context

Co-design the `DisplayDescriptor` `#[repr(C)]` layout with /dev (intrinsics) (FIXME 0254) — backend
emits it, intrinsics reads it. Depends on FIXME 0254 (the descriptor type + formatter) and 0256 (int
deletions) landing in concert. Sequencing within S76 is **/sprint + user's call** — this is likely a
dedicated trace wave (descriptor object-mode emission + discovery rework are substantial).
