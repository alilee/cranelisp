---
number: 0292
target: /dev
filed_by: /dev
filed_at: 2026-06-08
sprint_filed: 76
target_sprint: 77
refers_to: crates/cranelisp-backend/src/compiler/apply.rs (is_extern_primitive + compile_resolved_call BuiltinFn arm), crates/cranelisp-intrinsics/src/trace.rs (cranelisp_trace_name/_params/_result/_children/_nanos), design/arch/fixmes/0285-int-synthetic-accessor-defs-not-in-codegen-batch.md, design/arch/tracing.md §2.2
status: open
---

# Backend: Trace field-accessor calls (`nanos`/`name`/…) do not resolve to the `cranelisp_trace_*` intrinsics

Crate: `cranelisp-backend` (`/dev` narrow, backend mode).

## Issue

The Trace ADT field accessors are seeded in the `primitives` synthetic module by
int's bootstrap (`src/bootstrap.rs::register_trace_type`) as bare-named
`DefKind::Primitive` entries with `ast: None`: `name`, `params`, `result`,
`children`, `nanos`. Their runtime bodies are the `cranelisp-intrinsics::trace`
externs `cranelisp_trace_name` / `_params` / `_result` / `_children` / `_nanos`
(in `intrinsics_table()` since the W1.5 trace relocation, FIXME 0256).

There is **no connection** between the language-level accessor name (`nanos`) and
the intrinsic ABI name (`cranelisp_trace_nanos`):

- `is_extern_primitive` (`apply.rs:886-892`) recognises only the
  `cranelisp_trace_*` names, NOT the bare `nanos`/`name`/….
- typecheck assigns the accessor call `resolved_call = BuiltinFn { name: "nanos" }`
  (no rewrite).
- backend's `compile_resolved_call` BuiltinFn arm therefore treats `nanos` as an
  unknown extern → `compile_extern_call("nanos")` → `Linkage::Import` for the
  symbol `nanos`, which nothing defines.

Result (reproduced HEAD + S76 W4b): `(nanos (trace …))` fails with
`can't resolve symbol nanos` — in the REPL/JIT (panic) and in `--link`. This is
**defect 1** of FIXME 0285/0276. (The pre-relocation design resolved accessors as
extern intrinsics; the bare-name→intrinsic-name mapping was lost when the trace
family moved to `cranelisp-intrinsics`.)

The int side of 0285 is done: **defect 2 (worker-panic→park)** is fixed in
`src/worker.rs::priority_worker_loop_shared` (the unresolved-symbol panic now
surfaces as a clean `ModuleFailed` error + non-zero exit in ≈1s, not a hang); and
`derive_codegen_batch` now also enumerates bootstrap-synthesised `ast: Some`
non-constructor `Primitive` Defs (forward-looking — supports synthesised accessor
bodies should the resolution route through a batch). What remains is the call
resolution itself, which is backend's.

## Proposed resolution (backend's call — minimum mechanism)

Recognise the five bare Trace-accessor names at the call site and lower them to
the existing `cranelisp_trace_*` intrinsics (the same consuming convention the
intrinsic names already use in `is_extern_primitive` / `compile_consuming_arg_list`):

- Add `name`/`params`/`result`/`children`/`nanos` to the accessor recognition,
  rewriting to `cranelisp_trace_<field>` for the emitted `Linkage::Import` (or the
  GOT/extern path the other `cranelisp_trace_*` externs already take).
- Scope the rewrite to a Trace-typed receiver so a user `nanos`/`name` field on an
  unrelated ADT is not hijacked (the accessor's scheme is
  `(Fn [Trace] FieldTy)` — the inferred arg type pins it; or gate on the resolved
  callee FQ being `primitives/<accessor>`).

Alternative (rejected as heavier): int synthesises a `(match t [(TraceCall …) f])`
body for each accessor and compiles it into a batch — but the accessors live in
`primitives`, which is never batch-compiled, so this would also require a new
"compile synthetic primitives bodies" pass. The call-site rewrite is the minimal
mechanism and matches the pre-relocation architecture.

## Acceptance

- `(nanos (trace (work 41)))` resolves and returns `:primitives/Int …` in the
  REPL (e2e `tests/trace.rs::trace_nanos_accessor_resolves_in_repl`).
- The `--link` accessor build completes and the produced binary runs
  (`tests/trace.rs::trace_linked_accessor_consumption_parks_defect` — the no-hang
  half already passes via the int defect-2 fix; this completes the success half).
- `cargo nextest run -p cranelisp-backend` green; backend baseline unchanged
  (call-site recognition, no public-surface change).

## Context

Defect 1 of FIXME 0285 / 0276. The int half (defect 2 + batch derivation) landed
S76 W4b; this is the backend half. tracing.md is normative for the trace family.
