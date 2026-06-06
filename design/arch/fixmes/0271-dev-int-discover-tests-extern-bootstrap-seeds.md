---
number: 0271
target: /dev
filed_by: /arch
filed_at: 2026-06-06
sprint_filed: 76
target_sprint: 77
refers_to: design/arch/test-discovery.md §5 "discover-tests" + §6 "Int — bootstrap publication + the live-scan discovery extern" + §6 "Pair + Result seeding delta", design/arch/bounded-contexts.md §6 (int) + §7, src/bootstrap.rs, src/session_v4.rs (discover_tests_extern, int_intrinsics), src/worker.rs
status: open
---

# Int: `discover-tests` PrimitiveExtern publication + live-scan extern + Pair/Result seeds + `int_intrinsics()` deletion

Crate: `src/` (`/dev` narrow, int mode). Normative spec:
`design/arch/test-discovery.md` §5/§6. Coordinate with FIXME 0269 (backend
`Jit::define_symbol`) — int is the host that promises the body.

## Scope

1. **Bootstrap seeds for `Pair` and `Result`** in `src/bootstrap.rs`
   (`mount_synthetic_modules`), each modelled on `register_option_type`: a
   `register_pair_type` seeding `(Pair a b)` with one 2-field data ctor, and a
   `register_result_type` seeding `(Result a b)` with `Ok`/`Err` data ctors, both into
   the `primitives` module. (`Option` is already seeded.) All ctors are heap-allocated
   (no nullary).
2. **`discover-tests` publication as `DefKind::PrimitiveExtern`** — at the synthetic-module
   mount, publish `discover-tests` in the `primitives` table with an ordinary scheme,
   `kind: DefKind::PrimitiveExtern`, `got_slot: None`, `code: None`, key
   `"discover-tests"`.
3. **`Jit::define_symbol` registration at session init** — int calls
   `Jit::define_symbol("discover-tests", discover_tests_extern as *const u8)` once at
   session init (the host promise; backend FIXME 0269 supplies the API).
4. **The live-scan extern** — reshape `discover_tests_extern` (`session_v4.rs`) to:
   - take the canonical `(Vec String)` of module paths (the no-arg "current module" and
     single-`String` shapes are STDLIB-macro sugar, NOT int's concern — int's extern
     takes the `Vec String`; FIXME 0273 owns the sugar);
   - scan the live `TestRunnerState` per-module `SymbolTable` + GOT for eligible
     `test-*` fns — eligibility = the `test-` name prefix AND the EXACT scheme
     `(Fn [] (Option String))` (tighten the as-built prefix-only `discover_test_names`),
     warn-and-exclude a mis-typed `test-*`;
   - for each, build a `(Pair name callable)`: a heap `String` FQ name, and a heap
     closure `[header | code_ptr=wrapper | drop_glue_ptr | slot-capture]` whose wrapper
     does a GOT-slot-indirect call to the test (late-bound — a redefined test runs its
     current body);
   - union across the named modules; return a heap
     `(Vec (Pair String (Fn [] (Option String))))`.
5. **`int_intrinsics()` remnant deletion** — `run-test` is subsumed (running = invoking
   a discovered wrapper under `catch-runtime-error`); delete `run_test_extern` and the
   `int_intrinsics()` table that hosted the two parked test symbols. Trace's deletion of
   the table half is FIXME 0256; this FIXME removes the test half — coordinate so the
   table empties and is removed cleanly.

## Acceptance

- A user program calling `(discover-tests ["mod"])` resolves the extern at JIT-finalize
  (via the define_symbol promise) and returns name+late-bound-wrapper pairs.
- A redefined `test-*` runs its new body through an already-discovered wrapper (freshness).
- A mis-typed `test-*` is excluded + warned.
- `int_intrinsics()` is gone; no dead-remnant table remains.
- Workspace green; no new warnings on the int path.
