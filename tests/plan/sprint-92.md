# Sprint 92 — Slice 1 (apply-arg sparking) — Failing-test PLAN (Phase 3 deliverable)

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests land in
**Phase 5 Stage 1** (QA-first, sprint-wide, before any per-crate D/D/R cycle). This
document enumerates the test surface so `/sprint` + the user can review coverage before
implementation waves are allocated.

**Scope source:** `sprints/SPRINT.md` (Sprint 92, Slice 1 — CPU-parallelism widening,
FIXME 0424(i)); `design/backend/lenient-eval.md` §2.5, §4.4, §5, §8, §9 (acceptance
criteria + the as-built ferry); spec anchors `spec/12-runtime.md` §12.4.3 (widened),
§12.4.1, and `spec/04-expressions.md` §4.11.

**Design of record:** `design/backend/lenient-eval.md`. New analysis seam:
`find_sparkable_args(args, constructors) -> Vec<usize>` in
`crates/cranelisp-backend/src/compiler/control_flow/sparkability.rs` (sibling of
`find_sparkable_bindings`, reusing `is_worth_sparking` + the cheap/ctor sets + the ≥2
gate). New lenient pre-pass at the top of `compile_apply`'s non-tail arm
(`apply.rs`). IVar machinery + ferry reused unchanged.

## Conventions / legend

- **Tier**: `unit` (`/dev`-authored, `crates/cranelisp-backend/src/.../sparkability_tests.rs`,
  `#[cfg(test)]`) or `e2e` (`/qa`-authored, `tests/spec_12_runtime.rs`, subprocess).
  No middle tier (`tests/CLAUDE.md`). Unit rows are NAMED for surface completeness but
  `/dev` lands them in the same change-set as the fix (mandatory-unit-test discipline);
  `/qa` authors the e2e rows.
- **Posture**: `RED-first` = a failing guard `/dev` flips green (apply-arg sparking does
  not exist on HEAD, so every row is RED-first).
- **P/N**: positive (correct behaviour appears) / negative (wrong behaviour absent).
- All e2e tests are **free-standing** — zero `stdlib/` dependency;
  `PreludeVariant::PrimitivesOnly`; `fib`/`work`/`pmr`/`fmap` defined inline with
  primitives + special forms.
- Every e2e cross-checks lenient-ON (default) against `CRANELISP_NO_LENIENT=1` — the
  opt-out IS the equivalence oracle (§12.4.3 semantic transparency).

---

## ⚠ Risk callout — existing fib-based perf tests start over-sparking under Slice 1

The cost heuristic is **syntactic** (callee identity), not value-based: any non-cheap,
non-constructor `Apply` argument is "worth sparking" regardless of its actual runtime
cost. Therefore **naive `fib`** — `(add-i64 (fib (sub n 1)) (fib (sub n 2)))` — becomes a
**2-expensive-apply-arg site that sparks at every internal node** once apply-arg sparking
ships. Two consequences `/dev` and `/sprint` must weigh:

1. **Existing `let` perf tests will change behaviour.** `tests/spec_12_runtime.rs::lenient_vec_map_reduce_parallelizes`
   and `::lenient_vec_map_reduce_prior_binding_stays_serial` both use a naive-`fib` leaf.
   Today fib's internal `(add-i64 (fib…) (fib…))` does NOT spark; under Slice 1 it WILL,
   over-sparking tiny `fib(2)` calls. This can flip the negative control
   (`prior_binding_stays_serial`) — which asserts NO speedup — into a spurious speedup,
   and can make the positive test's timing noisier. **`/qa` flags:** these two tests need
   their leaf swapped to a non-over-sparking shape (see point 2) in the same Phase-5
   change-set, OR re-validated as still-correct under Slice 1. This is a regression risk,
   not a new test.
2. **Slice-1 perf workloads MUST use a leaf with no internal ≥2-expensive-apply-arg
   shape**, so the perf signal is the *top-level* apply-arg D&C and not internal
   over-spark noise. The canonical leaf for perf rows below is a **tail-recursive
   accumulator** `work` (single self-call, gated off sparking by TCO, args cheap):
   `(defn work [:Int n :Int acc] (if (le-i64 n 0) acc (work (sub-i64 n 1) (add-i64 acc (mul-i64 n n)))))`.
   Equivalence rows (correctness only) MAY keep naive `fib` at small `n` (≤20) since
   over-sparking is still *correct* — it only matters for timing.

---

## Unit tier — `find_sparkable_args` analysis (`cranelisp-backend`, `/dev`-authored)

Pure analysis over `&[MonoExpr]`; no session/runtime/env-var. Table-driven, mirrors
`sparkability_tests.rs::find_sparkable_bindings` cases. Trace:
`design/backend/lenient-eval.md §2.5.2`.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `sparkable_args_two_expensive_independent` | unit | `find_sparkable_args([call("compute"), call("derive")], ∅) == [0,1]` | §2.5.2 | P | RED-first |
| `sparkable_args_constructor_pair_case` | unit | FIXME canonical `(Pair (fib a)(fib b))`: args `[call("fib"),call("fib")]` → `[0,1]` (outer ctor `Pair` is the callee, irrelevant — the *args* spark) | §2.5.2 | P | RED-first |
| `sparkable_args_three_mixed_var_skipped` | unit | `[call("fib"), var("x"), call("derive")] == [0,2]` (var ref excluded; ≥2 still holds) | §2.5.2 / §2.2 | P | RED-first |
| `sparkable_args_single_expensive_below_gate` | unit | `[call("compute"), call("+")] == []` (only 1 candidate < ≥2 gate) | §2.5.2 / §2.1 | N | RED-first |
| `sparkable_args_all_cheap_empty` | unit | `[call("+"), call("<")] == []` (cheap-builtin exclusion) | §2.2 | N | RED-first |
| `sparkable_args_constructor_arg_excluded` | unit | ctors `{Some,Cons}`; `[call("Some"), call("Cons")] == []` (constructor-callee args excluded) | §2.2 | N | RED-first |
| `sparkable_args_literal_var_excluded` | unit | `[var("x"), literal(1), call("compute")] == []` (only 1 real candidate after excluding var+literal) | §2.2 | N | RED-first |

> No `depends_on_earlier` analogue exists for apply-args (§2.5.2): arguments bind nothing
> into sibling scope, so there is no inter-argument data-dependence case to test. This is
> the one `let`-path test class that is *correctly absent* here.

---

## E2E tier — positive equivalence (`tests/spec_12_runtime.rs`, `/qa`-authored)

Each runs the SAME program lenient-ON and lenient-OFF and asserts identical result equal
to the known value — so each is simultaneously a correctness check AND the determinism
oracle (§12.4.3 transparency).

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `apply_arg_pair_equiv_run` | e2e | `(Pair (fib a)(fib b))` destructured-sum → `main:IO Int`: ON exit == OFF exit == known value, `--run` | §12.4.3 (widened) | P | RED-first |
| `apply_arg_pair_equiv_link` | e2e | same program under `--link` (`link_then_run`) | §12.4.3 | P | RED-first |
| `apply_arg_pair_equiv_repl` | e2e | same in REPL → `:primitives/Int N` (the constructor-arg apply at top level) | §12.4.3 | P | RED-first |
| `apply_arg_dc_map_reduce_equiv_run` | e2e | par-map D&C `(add-i64 (pmr v lo mid) (pmr v mid hi))` (the two recursive halves are apply-args → both spark): ON == OFF == value — closes FIXME 0424(i) | §12.4.3 (par-map) | P | RED-first |
| `apply_arg_no_lenient_determinism_oracle` | e2e | explicit oracle: a representative apply-arg program produces byte-identical stdout ON vs OFF (the §12.4.3 governing invariant) | §12.4.3 transparency | P | RED-first |

---

## E2E tier — negative / gating (the `[Tested+Neg]` half)

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `apply_arg_single_expensive_stays_serial` | e2e | `(add-i64 (work big) cheap)` — only ONE expensive arg → NOT sparked → majority-of-N **no** speedup (ON ≥ 0.7·OFF) + same result. The ≥2 gate at the apply site (apply analogue of `lenient_vec_map_reduce_prior_binding_stays_serial`) | §12.4.3 | N | RED-first |
| `apply_arg_all_cheap_stays_serial` | e2e | an apply with all-cheap args (e.g. `(add-i64 (add-i64 a b) (mul-i64 c d))`) is unchanged + correct (cost-heuristic floor; never-slower-than-serial) | §12.4.3 | N | RED-first |

> The runtime-observable ≥2-gate + cost-heuristic are *also* pinned at the analysis seam
> by the unit rows above; these e2e rows prove the gate survives into codegen/runtime.

---

## E2E tier — ferry at the NEW apply entry point (MANDATORY — `design/backend/lenient-eval.md §5, §9`)

Existing ferry tests (`lenient_binding_panic_*`) cover the `let`/`Par` entry only. These
are the apply-site analogues, modelled on `CATCH_ERR_PROGRAM`.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `apply_arg_panic_ferried_caught_run` | e2e | `(catch-runtime-error (fn [] (add-i64 (div-i64 10 0) (work n))))` — div-by-zero in one of ≥2 sparked args is ferried to the joining thread → `Err` arm fires (exit proves caught, not silently dropped), `--run` | §12.4.3 ferry / §5 | P | RED-first |
| `apply_arg_panic_ferried_caught_link` | e2e | same under `--link` (ferry sound across modes) | §12.4.3 / §5 | P | RED-first |
| `apply_arg_panic_not_swallowed_neg` | e2e | UNCAUGHT: same sparked-arg panic surfaces "division by zero" on the joining thread — MUST NOT be silently discarded | §12.4.3 | N | RED-first |
| `apply_arg_dual_panic_first_error_wins` | e2e | both args panic with **distinct** messages (e.g. left `(div-i64 10 0)` "division by zero" vs right `(vec-get [] 5)` out-of-bounds); the **left** (first L-to-R) message wins — barrier forces left first → `set_runtime_error` first-error-wins is deterministic regardless of worker finish order, matching sequential | §12.4.3 first-error-wins / §8 | P+N | RED-first |

---

## E2E tier — barrier / TCO-gating invariant (the load-bearing guard — §4.4 Phase 2, §2.5.3)

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `apply_arg_tail_panic_ferried` | e2e | a **tail-position** (non-self) sparking apply `(add-i64 (div-i64 10 0) (work n))` whose result is `f`'s body, wrapped in `catch-runtime-error` → `Err`. Fails if any path reaches the call with an unforced arg IVar (panic dropped) — pins barrier-before-call in tail position | §12.4.3 / §4.4 / §5 | N | RED-first |
| `apply_arg_tco_self_call_not_sparked` | e2e | a **tail self-recursive** call carrying ≥2 expensive args — `(defn loop [n x y] (if (eq-i64 n 0) (add-i64 x y) (loop (sub-i64 n 1) (work x) (work y))))` at large `n` — must still TCO (no stack overflow) + correct result; proves apply-arg sparking is gated OFF the TCO self-call fast path (§2.5.3), so the barrier is never bypassed by the loop-header jump | §12.5 / §2.5.3 | N | RED-first |

---

## E2E tier — performance evidence

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `apply_arg_par_map_parallelizes` | e2e | best-of-N wall-clock: ON < 0.7·OFF in ≥1 of N attempts over the D&C apply-arg map-reduce with the **non-over-sparking `work` leaf** (Risk-callout pt.2); semantic-transparency (ON exit == OFF exit) asserted on EVERY attempt. Reuses the `pmr_run_elapsed_ms` + best-of-N harness verbatim | §12.4.3 | P | RED-first |
| `apply_arg_single_expensive_stays_serial` | e2e | (negative control above) majority-of-N no-speedup — the never-slower-than-serial / overhead-bounded floor | §12.4.3 | N | RED-first |

### Perf-evidence recommendation — (c) BOTH, with a clear CI/demo split

Wall-clock perf is genuinely flaky under the saturated `cargo nextest` harness (the
30s-budget, CPU-bound contention documented at length in the existing
`lenient_vec_map_reduce_parallelizes` banner). Recommendation:

- **In the CI suite (loosely-bounded, best-of-N):**
  - `apply_arg_par_map_parallelizes` — the **best-of-N, ON < 0.7·OFF** witness (≥1.43×
    required vs the ~2.8–3.1× observed for the `let` analogue; a purely-sequential impl
    can never qualify in *any* attempt, so one qualifying attempt is a sound parallelism
    proof). This is the *only* speedup assertion in CI, and it is generous by design.
  - `apply_arg_single_expensive_stays_serial` — **majority-of-N no-speedup** floor (the
    never-slower-than-serial guard). Contention-tolerant by the same best-of-N logic.
  - Semantic-transparency equality (ON == OFF) is asserted on **every** attempt of both —
    it is contention-immune and never relaxed.
- **NOT in CI — handed to Phase-6 `/repl` + `/port` as a witnessed demo corpus:**
  - The **near-linear-speedup-to-N-cores** claim (SPRINT.md acceptance). Core-count- and
    hardware-dependent; too fragile for a fixed CI ratio. Target: the **0408 parallel
    Sudoku** showcase (`/port`) re-expressed with `par-map`, plus a `/repl` `par-map`
    benchmark transcript. These produce the "near-linear to N cores for ≥1µs/element"
    evidence as a reviewed artefact, not a CI assertion.

Rationale: the CI rows answer "did it parallelise at all, and is it never slower than
serial, and is it always correct?" (the durable regression guards). The demo corpus
answers "how *well* does it scale?" (the acceptance showcase) without importing
core-count flakiness into the 30s suite.

---

## Spark budget (slice-1 scope addition — option (b)) — global in-flight-spark cap

Added per `sprints/SPRINT.md` "Spark budget (added — option (b))" and
`design/backend/lenient-eval.md §3.6` (mechanism) + §9 (acceptance). The budget is a
**runtime, scheduling-only** decision inside `cranelisp-intrinsics::ivar_spark` — codegen is
unchanged, so every budget test asserts the budget alters *scheduling* (spawn vs inline)
**without ever changing the answer**. The cap defaults to `4 × rayon::current_num_threads()`;
`CRANELISP_SPARK_BUDGET=N` overrides; `=0` degenerates to all-inline (≡ serial); non-parsing
falls back to default.

> **Why budget tests are needed at all:** the budget exists to restore the never-slower-than-serial
> floor for the over-sparking shapes the apply-arg widening introduces (naive recursive
> `(add-i64 (fib…)(fib…))`). Without it, slice 1 would regress the floor for arbitrary recursive
> user code. The budget rows below are therefore the floor-guard half of slice 1, not an optional add-on.

### Unit tier — in-flight counter (`cranelisp-intrinsics`, `ivar/tests.rs`, `/dev`-authored)

The budget is `cranelisp-intrinsics`-internal (a module-static `AtomicIsize IN_FLIGHT_SPARKS`
+ `SPARK_BUDGET` `LazyLock` + `InFlightGuard` RAII, all private to `ivar.rs`), so its unit tests
live in `crates/cranelisp-intrinsics/src/ivar/tests.rs` — a **second crate touched for unit tests**
this sprint, alongside the existing `cranelisp-backend` `find_sparkable_args` units. These exercise
`ivar_create`/`ivar_spark`/`ivar_force` directly (no session, no codegen); env-var-driven rows
set `CRANELISP_SPARK_BUDGET` in-process (serial, `--test-threads=1`-safe — they mutate a process
global). Trace: `design/backend/lenient-eval.md §3.6` + §9.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `spark_budget_panicking_spawned_thunk_counter_returns_to_zero` | unit | **MANDATORY.** A sparked thunk that Rust-**unwinds** inside the rayon closure leaves `IN_FLIGHT_SPARKS == 0` afterward — the `InFlightGuard::drop` decrement runs on the panic path. A leaked increment would drift the cap toward permanent-inline (silent serial degradation no other test catches). | §3.6 "Decrement correctness under panic" / §9 | P | RED-first |
| `spark_budget_spawn_path_increments_then_decrements_net_zero` | unit | under-cap spark: counter rises by 1 while the task is in flight and returns to its prior value on normal completion (the `fetch_add`/`InFlightGuard` pair) | §3.6 "Increment / decrement points" / §9 | P | RED-first |
| `spark_budget_over_cap_resolves_inline_no_spawn` | unit | with a saturated/low cap, an over-budget `ivar_spark` leaves the cell **RESOLVED on return** with **no** rayon task spawned (synchronous inline force; reservation released via the immediate `fetch_sub`) | §3.6 decision point / §9 | N | RED-first |
| `spark_budget_zero_resolves_inline_synchronously` | unit | `CRANELISP_SPARK_BUDGET=0` ⇒ `prev >= 0` always ⇒ every spark resolves inline on the calling thread, cell RESOLVED on return, never spawns | §3.6 "budget=0" / §9 | N | RED-first |
| `spark_budget_panicking_inline_thunk_ferries_and_counter_net_zero` | unit | a panicking **inline** (over-cap) thunk surfaces its error into the **calling thread's** slot (ferry-on-inline soundness, §3.6) AND leaves the counter net-zero (add/sub immediately paired, no guard needed on the inline branch) | §3.6 "Ferry soundness — inline spark" / §9 | P+N | RED-first |

### E2E tier — budget (`tests/spec_12_runtime.rs`, `/qa`-authored)

All free-standing (`PreludeVariant::None` / `PrimitivesOnly`); the over-sparking naive-`fib`
leaf is defined inline. Equivalence rows are scheduling-only oracles (§12.4.3 transparency):
the budget is *never* allowed to change the answer.

| Test name | Tier | Asserts | Trace | P/N | Posture |
|---|---|---|---|---|---|
| `budget_naive_fib_floor_not_slower_than_serial` | e2e | the over-sparking shape `(add-i64 (fib…)(fib…))` with the **default budget on** is **not dramatically slower than serial** (`CRANELISP_NO_LENIENT=1`) — majority-of-N, loose `ON < 1.3·OFF` floor witness (the regression the budget exists to prevent). Result equality (ON == OFF) asserted every attempt. | §3.6 "Problem" / §9 "Floor restored" / §12.4.3 | N | RED-first |
| `budget_three_regime_result_equivalence` | e2e | the SAME program run three ways — **inline** (cap saturated, `CRANELISP_SPARK_BUDGET=1`), **under-cap** (spawned, `CRANELISP_SPARK_BUDGET` high), and **serial** (`CRANELISP_NO_LENIENT=1`) — yields one identical result. Proves the budget is scheduling-only (observational equivalence). | §3.6 "Observational equivalence" / §9 "Inline equivalence" / §12.4.3 | P | RED-first |
| `budget_zero_equiv_no_lenient` | e2e | `CRANELISP_SPARK_BUDGET=0` (runtime-layer serial) produces byte-identical stdout to `CRANELISP_NO_LENIENT=1` (codegen-layer serial) — the two degeneracies at different layers coincide observationally. | §3.6 "Two degenerate-to-serial paths" / §9 "Degenerate-to-serial" / §12.4.3 | P | RED-first |
| `budget_knob_default_override_and_garbage` | e2e | knob behaviour: unset ⇒ default cap applies (correct result, parallel); `CRANELISP_SPARK_BUDGET=N` respected (correct result); a **non-parsing** value (`CRANELISP_SPARK_BUDGET=banana`) falls back to default — **no crash**, correct result. | §3.6 "Cap default + knob" / §9 "Knob" / §12.4.3 | P+N | RED-first |

### Perf-treatment call — `budget_naive_fib_floor_not_slower_than_serial`

**Loose CI witness, NOT a demo.** The floor is the budget's entire reason to exist, so it MUST be
a durable CI regression guard — the same posture as the existing `apply_arg_single_expensive_stays_serial`
floor row. Treatment:

- **In CI:** majority-of-N **never-slower bound** `ON < 1.3·OFF` (generous — the assertion is
  "the budget kept the explosion bounded," not "it sped up"; naive fib is *not* expected to
  speed up, only to not blow up). Contention-tolerant via the same best-of-N logic as the other
  perf rows. Result equality (ON == OFF) asserted on **every** attempt (contention-immune).
- **NOT split to the demo corpus.** Unlike the `near-linear-to-N-cores` speedup claim (handed to
  `/repl`+`/port`), the floor is a correctness-adjacent regression guard, not a scaling showcase —
  it belongs in the 30s suite. The `1.3×` bound is loose enough to survive the saturated harness
  while still catching an `O(2ⁿ)` spark explosion (which would be many-× slower, not 1.3×).

### `let`-path perf re-validation (§3.6 flag → `/qa`, Phase 5)

§3.6 + the existing risk callout both flag that `lenient_vec_map_reduce_parallelizes` and its
negative control `lenient_vec_map_reduce_prior_binding_stays_serial` could shift if they assume
**more than `cap` (`4×threads`) concurrent bindings** — the excess would resolve inline under the
default budget. **Approach (no new test):** in the Phase-5 change-set, **pin `CRANELISP_SPARK_BUDGET`
high** for these two existing tests (e.g. via the harness env) so all their bindings spawn — the
cheapest way to decouple the existing `let` perf signal from the new cap. This is the same surface
already flagged for naive-fib (risk callout pt.1); both get re-validated/re-pinned in one change-set.
A budget value high enough that the test's binding count never reaches it restores byte-for-byte the
pre-budget behaviour these tests were written against.

## Spec annotation flips (Phase 5 — coordinated with `/spec`; gated on FIXME 0441)

> **Dependency:** `/spec` must land **FIXME 0441** (widen §12.4.3's permission to
> independent apply-arguments + forward-note §12.4.1/§4.11 "observable order") BEFORE the
> `[Tested …]` flips are meaningful — the spec must *authorize* apply-arg sparking for the
> conformance suite to read these rows as covered. `/qa` adds the test-side `// spec:`
> comments in Phase 5; the spec-side `[Tested …]` edits are `/spec`-owned.

| Spec row (current) | Flips to | Driven by |
|---|---|---|
| `spec/12-runtime.md §12.4.3` para 1 + 2 `[S92]` | `[Tested+Neg tests/spec_12_runtime::apply_arg_pair_equiv_run, …::apply_arg_dc_map_reduce_equiv_run, …::apply_arg_single_expensive_stays_serial]` | positive equiv + par-map (P) and ≥2-gate/cheap floor (N) |
| `spec/12-runtime.md §12.4.3` error-propagation para `[S77 … S92 — apply-arg extension]` | append `, tests/spec_12_runtime::apply_arg_panic_ferried_caught_run, …::apply_arg_panic_not_swallowed_neg, …::apply_arg_dual_panic_first_error_wins` | apply-site ferry + first-error-wins |
| `spec/12-runtime.md §12.4.1` (Strict Evaluation) `[S92]` | `[Tested tests/spec_12_runtime::apply_arg_pair_equiv_run]` | observable-as-if L-to-R for arguments |
| `spec/04-expressions.md §4.11` (Evaluation Order Summary) closing note `[S92]` | `[Tested tests/spec_12_runtime::apply_arg_pair_equiv_run]` | apply-arg concurrency permitted under observable L-to-R |

---

## Phase-3 exit gate confirmation

`/qa` confirms it has enough to draft the failing tests Phase 5 Stage 1 calls for:
**12 unit rows** (`/dev` — 7 `cranelisp-backend` `find_sparkable_args` + 5
`cranelisp-intrinsics` `ivar/tests.rs` budget), **17 e2e rows** (`/qa` — 13 apply-arg + 4
budget). All RED-first (apply-arg sparking + budget both absent on HEAD). The budget adds a
**second crate touched for unit tests** (`cranelisp-intrinsics`) and one **mandatory** unit
(`spark_budget_panicking_spawned_thunk_counter_returns_to_zero` — the panic-safe-decrement
invariant the design owes). Two regression risks flagged on the **same** existing-fib-leaf
`let` perf surface: (1) apply-arg over-sparking (risk callout) and (2) the budget cap shifting
concurrent-binding assumptions (§3.6) — both resolved in one Phase-5 change-set by pinning
`CRANELISP_SPARK_BUDGET` high / re-leafing. One spec dependency flagged (FIXME 0441 must land
for the `[Tested]` flips to be meaningful — does NOT block implementation, the capability is
observationally equivalent).
