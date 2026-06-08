---
number: 0285
target: /int
filed_by: /qa
filed_at: 2026-06-07
sprint_filed: 76
refers_to: tests/trace.rs::{trace_nanos_accessor_resolves_in_repl,trace_linked_accessor_consumption_parks_defect} (FAILING), src/bootstrap.rs (Trace accessor Defs with ast: Some), src/worker.rs (derive_codegen_batch), design/arch/fixmes/0276-qa-link-mode-synthetic-accessor-unresolved-and-park.md (/qa resolution status)
status: open
---

# Bootstrap-synthesised accessor Defs never compiled — broken in REPL/JIT too, not just --link

## Issue

0276's triage found the defect is NOT link-specific: the bootstrap-synthesised
Trace accessor Defs (`nanos`, `name`, …, seeded with `ast: Some` by the S76
mount) are absent from the JIT codegen batch as well — `(nanos (trace …))`
panics "can't resolve symbol nanos" in the REPL and PARKS the session in
--link (the park is the 0276 defect-2 robustness item). Match-based TraceCall
extraction works; only the accessor FUNCTIONS are missing. The S76 W2 0249-b
fix covered synthesised CONSTRUCTORS; the accessor Defs are the uncovered
sibling.

Failing tests: tests/trace.rs::trace_nanos_accessor_resolves_in_repl,
trace_linked_accessor_consumption_parks_defect.

## Proposed resolution

1. Extend the codegen-batch derivation to include bootstrap-synthesised
   non-constructor Defs with `ast: Some` (the accessor family) — both JIT and
   link batches; unit test alongside the 0249-b constructor test.
2. The worker-panic→park robustness item (defect 2) stays named in the ledger
   (every unresolved-symbol panic currently converts to a hang) — fix here if
   cheap, else carry explicitly.

## Operational implication / Context

Blocks accessor-based trace consumption in ALL modes. S76 W4 or S77. The
failing tests are the durable record; 0276 carries the triage history.

## Status — S76 W4b (/dev int)

**Defect 2 (worker-panic→park) FIXED (int).** `src/worker.rs::priority_worker_loop_shared`
now wraps both work-item handlers (`handle_typecheck_work_shared`,
`handle_cached_codegen`) in `catch_unwind` (`AssertUnwindSafe`); a panic — e.g.
the cranelift `can't resolve symbol …` unresolved-import panic at finalize, or any
`unreachable!` — is converted to a `CranelispError::CodegenError` and routed
through `scheduler.notify_module_failed`, so `wait_inmem_complete_blocking`
returns `ModuleFailed` instead of the main thread parking on the completion
condvar forever. Verified: the `--link` accessor build now **completes in ≈1.2s
with a clean error + exit 1** ("worker thread panicked while compiling module
'prog_acc': can't resolve symbol nanos") rather than hanging. `panic_message`
extracts the payload string. The hang IS the defect (per the failing test
comment); it is resolved.

**Batch derivation (proposed resolution #1) DONE (int).**
`src/worker.rs::derive_codegen_batch`'s final symbol-table sweep now enumerates
bootstrap-synthesised `ast: Some` NON-constructor `DefKind::Primitive` Defs (the
accessor family), not just constructors — forward-looking, so any synthesised
accessor body that routes through a module batch is lowered. (Inert today because
the accessors live in `primitives`, which is never batch-compiled — see below.)

**Defect 1 (accessor resolution) is BACKEND — filed as FIXME 0292.** Triage
showed the accessor call does NOT route through `derive_codegen_batch` for the
primitives-module accessors: a `(nanos t)` call resolves as
`BuiltinFn { name: "nanos" }`, but `is_extern_primitive` recognises only the
intrinsic ABI names (`cranelisp_trace_nanos`), not the bare `nanos`. The
bare-name→intrinsic-name mapping was lost in the W1.5 trace relocation. The
minimal fix is a backend call-site rewrite (`nanos`→`cranelisp_trace_nanos`,
Trace-receiver-scoped) — backend's call, filed as FIXME 0292. (The int
synthesised-body alternative can't be compiled because `primitives` is never
batch-compiled.)

Keep this FIXME OPEN until 0292 lands and
`tests/trace.rs::{trace_nanos_accessor_resolves_in_repl,
trace_linked_accessor_consumption_parks_defect}` both pass.

## Status — S76 W4b (/dev backend)

**Defect 1 (accessor call resolution) FIXED IN BACKEND + VERIFIED.** FIXME 0292's
backend half landed: `crates/cranelisp-backend/src/compiler/apply.rs` now rewrites
the bare accessor names (`name`/`params`/`result`/`children`/`nanos`) to their
`cranelisp_trace_*` intrinsics, Trace-receiver-scoped, routed through the consuming
extern path. Proven: clean-path JIT `(nanos (trace (work 41)))` → `:primitives/Int`
(baseline panicked `can't resolve symbol nanos`). `cargo nextest run -p
cranelisp-backend` = 197/197 incl. 4 new unit tests. The bare-name→intrinsic
mapping lost in the W1.5 relocation is restored.

**Both target tests STILL RED — two SEPARATE non-backend defects (see 0292 re-targeted /int):**
- `trace_nanos_accessor_resolves_in_repl`: blocked by an int REPL
  forward-reference / prelude-as-cwd-project defect — the test defines `work`
  before `id`, and in the harness REPL (no `CRANELISP_LIB`) the prelude loads as a
  project and `(defn work [x] (id x))` errors `undefined variable: id` BEFORE
  reaching the accessor. Environmental: with `CRANELISP_LIB` set or `id` first, it
  returns the Int. (0292 §Defect A.)
- `trace_linked_accessor_consumption_parks_defect`: park/timeout (defect-2) GONE
  and accessor resolves at link — the binary now LINKS (exit 0), but the produced
  binary crashes NON-deterministically (heap corruption in the `--link`
  trace-consume path; JIT runs the same program clean; sibling match-based
  `--link` test passes). A `--link`-specific trace runtime/relocation defect in
  the FIXME 0275 family. (0292 §Defect B.)

Keep this FIXME and 0292 OPEN until both defects (A REPL forward-ref / prelude,
B `--link` trace-consume crash) are resolved and both tests pass.
