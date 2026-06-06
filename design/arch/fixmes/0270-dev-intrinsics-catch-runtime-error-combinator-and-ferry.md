---
number: 0270
target: /dev
filed_by: /arch
filed_at: 2026-06-06
sprint_filed: 76
target_sprint: 77
refers_to: design/arch/test-discovery.md §5 "catch-runtime-error" + §6 "Publishing catch-runtime-error" + §6 "The fork-join error-slot ferry requirement", design/arch/bounded-contexts.md §4b invariant 13, crates/cranelisp-intrinsics/src/panic.rs, crates/cranelisp-intrinsics/src/{ivar.rs,io.rs}, crates/cranelisp-intrinsics/src/catalog.rs
status: open
---

# Intrinsics: `catch-runtime-error` combinator + the fork-join error-slot ferry

Crate: `cranelisp-intrinsics` (`/dev` narrow, backend mode — paired). Normative spec:
`design/arch/test-discovery.md` §5/§6. This is a plain runtime intrinsic — NO backend
codegen change (calling a language closure from intrinsic code is established as-built:
`io::call_continuation`, `ivar`, `run_test_by_name`).

## Scope

1. **The `catch-runtime-error` C-ABI combinator** — a new `extern "C"` fn
   `#[export_name = "catch-runtime-error"]`, signature `fn(thunk_closure: i64) -> i64`,
   in `cranelisp-intrinsics::panic`. Body: clear the slot (discard via the internal
   `take_runtime_error()`); load `code_ptr` from the thunk at `CLOSURE_CODE_PTR_OFFSET`
   (16) and call `extern "C" fn(env_ptr) -> i64` with the closure as `env_ptr`; read the
   slot via `take_runtime_error()`; marshal `Some(msg)` → heap `(Err msg)` / `None` →
   heap `(Ok result)`. One body serves every `a` (uniform i64 ABI). Both `Result`
   variants carry data → both heap-allocated.
2. **Two-layer naming.** The language/ABI name is `catch-runtime-error`. The internal
   Rust slot-reader `take_runtime_error()` (`panic.rs:43`) KEEPS its name as the
   combinator's mechanism — it is NOT a C-ABI export and NOT a language name.
3. **`intrinsics_table()` entry** — register `IntrinsicEntry { name: "catch-runtime-error",
   ptr, param_count: 1, has_return: true, is_runtime: false }` in `catalog.rs` so all
   three resolution points (JIT setup, cache-hit `Linker::register_symbol`, `--link`
   archive) pick it up. Works in ALL modes incl. `--link` (self-contained — no live
   session). (Catalog count grows by one beyond the trace addendum.)
4. **The fork-join error-slot ferry (owed on the join paths, NOT the combinator).**
   - `panic.rs` gains a `set_runtime_error(msg)` companion to `take_runtime_error()`
     (internal Rust, not C-ABI, not a language name) — the join-side re-raise primitive.
   - **IVar lenient-let join** — `ivar_spark`/`ivar_force` (`ivar.rs:84/115/137`):
     worker-side calls `take_runtime_error()` after running the thunk and ferries any
     `Some(err)` back; the joining `ivar_force`/spin-wait re-raises the FIRST error via
     `set_runtime_error` and yields the sentinel.
   - **Par fork-join** — `dispatch_par_branches_with_trace` (`io.rs:405–484`; rayon map
     :456–473): same worker-side `take_runtime_error()` → `(result, Option<err>)`,
     join-side first-error re-raise.
   - **First-error-wins** matches sequential semantics (first panic aborts the whole
     expression); aggregation is rejected.

## Acceptance

- `(catch-runtime-error (fn [] (/ 1 0)))` returns `(Err …)`; a passing thunk returns
  `(Ok result)`. Unit coverage in the intrinsics crate (`/dev` owns unit tests).
- A panic inside a lenient-sparked binding and inside a Par branch propagates to the
  joining thread (no silent swallow, no slot pollution). The observational-equivalence
  defect this repairs has a /qa repro (FIXME 0272) — coordinate so the repro goes green
  when this lands.
- `RUNTIME_ERROR` thread-local is left clean after each combinator call (the RC
  mid-panic indeterminacy caveat is documented, not fixed).
- Workspace green; intrinsics `public-api.txt` regenerated (`intrinsics_table()` content
  changes but its signature does not — confirm baseline delta is only the entry, if any
  surfaces).
