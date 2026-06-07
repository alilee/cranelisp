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

## Status — S76 W4b (/dev int)

**Int side LANDED (all five scope items done):**

1. `Pair` (`register_pair_type`) + `Result` (`register_result_type`, tag Ok=0/Err=1)
   bootstrap seeds in `src/bootstrap.rs`, modelled on `register_option_type`. ✅
2. `discover-tests` published as `DefKind::PrimitiveExtern` (`got_slot: None`,
   `code: None`, scheme `(Fn [(Vec String)] (Vec (Pair String (Fn [] (Option
   String)))))`) in `register_test_infrastructure`. ✅
3. `Jit::define_symbol("discover-tests", discover_tests_extern)` at session init
   (in `worker::build_session_jit`). ✅
4. Live-scan extern reshaped (`session_v4.rs::discover_tests_extern`): takes the
   `(Vec String)` of module paths, scans for `test-` prefix AND the EXACT scheme
   `(Fn [] (Option String))` (`test_scheme_is_eligible`), builds late-bound wrapper
   closures (`discovered_test_wrapper` — GOT-slot-address capture, indirect call →
   freshness), unions across modules, returns a heap `(Vec (Pair String callable))`.
   Unit-tested (`discover_tests_extern_tests`: eligibility, late-binding, empty-vec). ✅
5. `int_intrinsics()` + `run_test_extern` + the SList/IO/TestResult marshalling
   helpers deleted; `TestResult`/`run-test` retired from bootstrap. ✅

**E2E acceptance BLOCKED on frontend (FIXME 0291).** `(discover-tests ["mod"])`
fails at PARSE because `cranelisp-frontend` still intercepts `discover-tests` /
`run-test` in head position (`ast_builder.rs:1021-1022` + `build_discover_tests`)
— a producer the test-discovery cascade owes to /frontend that Wave 4a did not
land. test-discovery.md §"Frontend — nothing" requires deleting those arms.
Filed as FIXME 0291 (`target: /dev`, frontend crate). The int extern, bootstrap
seed, and define_symbol promise are all in place; once 0291 lands, e2e resolves.
`catch-runtime-error` (FIXME 0290, also int) is already e2e-verified — it has no
frontend arm: `(catch-runtime-error (fn [] (/ 1 0)))` → `(Err "runtime panic:
division by zero")`; `(catch-runtime-error (fn [] (+ 1 2)))` → `(Ok 3)`.

Keep this FIXME OPEN until 0291 lands and the discover-tests e2e (0289 /qa)
demonstrates the pairs.
