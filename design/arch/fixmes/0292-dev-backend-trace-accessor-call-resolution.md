---
number: 0292
target: /int
filed_by: /dev
filed_at: 2026-06-08
sprint_filed: 76
target_sprint: 77
refers_to: crates/cranelisp-backend/src/compiler/apply.rs (trace_accessor_intrinsic + compile_resolved_call BuiltinFn arm — RESOLVED), tests/trace.rs::{trace_nanos_accessor_resolves_in_repl, trace_linked_accessor_consumption_parks_defect}, design/arch/fixmes/0285-int-synthetic-accessor-defs-not-in-codegen-batch.md
status: open
---

# BACKEND HALF DONE (S76 W4b /dev). Two NON-backend defects now block the e2e tests — re-targeted /int.

## Resolution — backend call resolution LANDED + VERIFIED (S76 W4b /dev)

The backend half is done. `crates/cranelisp-backend/src/compiler/apply.rs` now
maps the five bare Trace field-accessor names → their `cranelisp_trace_*`
intrinsics, scoped to a `primitives/Trace`-typed receiver:

- New free fns `trace_accessor_abi_name(name) -> Option<&str>`
  (`nanos`→`cranelisp_trace_nanos`, etc.; `first_child_nanos` deliberately
  excluded — it is the `/run-tests` internal reader, never a `BuiltinFn` head)
  and `is_trace_typed(Option<&Type>)` (the receiver-scope gate).
- New method `FnCompiler::trace_accessor_intrinsic(name, args)` combines them and
  is intercepted in the `BuiltinFn` arm BEFORE the unknown-builtin extern
  fallthrough; it routes through `compile_consuming_arg_list` +
  `compile_extern_call(intrinsic, …)` (the consuming convention the other
  `cranelisp_trace_*` externs use). The catalog
  (`cranelisp_intrinsics::catalog::intrinsics_table()`) resolves the rewritten
  name identically in JIT (`JITBuilder::symbol`), cache-hit
  (`Linker::register_symbol`), and `--link` (archive force-link).
- 4 unit tests (`trace_accessor_tests` in apply.rs). `cargo nextest run -p
  cranelisp-backend` = 197/197. No public-surface change (all private fns).

**Verified end-to-end in JIT.** Clean path (correct def order, `CRANELISP_LIB`
set so the prelude does not load as a cwd project):
`(nanos (trace (work 41)))` → `:primitives/Int 247833`. The SAME path at the
pre-fix baseline panics `can't resolve symbol nanos` in cranelift-jit. The
bare-name→intrinsic mapping lost in the W1.5 relocation is restored. **Backend
half = DONE.**

## What still blocks the two e2e tests — two SEPARATE non-backend defects

Both target tests stay red, but for layered reasons OUTSIDE the accessor
call-resolution (the classic "fixing the visible error exposes the next layer"
situation the cross-skill protocol warns about):

### Defect A (int — REPL forward-reference / prelude-as-project) blocks `trace_nanos_accessor_resolves_in_repl`

The test source defines `(defn work [x] (id x))` BEFORE `(defn id [x] x)`. In
the harness REPL (`repl_prims`, cwd = tmpdir with `prelude.cl`, `CRANELISP_LIB`
UNSET) the prelude loads as a cwd PROJECT and the second form fails
`type error: undefined variable: id` — the program NEVER reaches the `nanos`
accessor. Proven environmental: the IDENTICAL input with `CRANELISP_LIB` set (or
with `id` defined first) returns `:primitives/Int` correctly. So this is a REPL
forward-reference / prelude-loading-mode behaviour, NOT accessor resolution.
**Minimal repro:** with `prelude.cl` (primitives-only) in cwd and NO
`CRANELISP_LIB`, piping `(defn work [x] (id x))\n(defn id [x] x)\n` to the REPL
errors `undefined variable: id`; setting `CRANELISP_LIB=<cwd>` makes it resolve.
Owner: /int (prelude-as-cwd-project module-resolution mode). NOTE: /qa may also
choose to fix the test's def order — but the underlying REPL behaviour is real.

### Defect B (int/runtime — `--link` trace-consume non-deterministic crash) blocks `trace_linked_accessor_consumption_parks_defect`

The park/timeout (0285 defect-2) is GONE and the accessor now resolves at link
(`can't resolve symbol nanos` no longer fires) — the build COMPLETES and the
binary LINKS (`-o prog`, link exit 0). But the produced binary crashes
**non-deterministically** (observed exit codes 14/20/23/32/68/104/116/145/146/
193/198/202/234 across runs) — classic heap corruption / use-after-free in the
trace-consume path under `--link`. The SAME program in JIT/REPL runs clean
(returns the Int; `CRANELISP_RC_TRACE` shows a clean drop sequence). JIT and
`--link` share the identical codegen path (only symbol resolution / relocation
differs), and the sibling `trace_linked_binary_match_consumption_runs` (match
extraction, no accessor) PASSES — so this is a `--link`-specific defect in the
trace runtime/relocation/startup exposed by accessor consumption
(`consume_trace_call` over the full Trace tree returned by
`cranelisp_collect_trace`), in the same family as FIXME 0275. Owner:
/int (runtime/startup) or a future backend trace-`--link` relocation pass — needs
triage; NOT the call-resolution this FIXME originally covered.

## Original issue (kept for context)

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
