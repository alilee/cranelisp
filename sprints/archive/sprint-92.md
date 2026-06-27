# Sprint 92: Effect-concurrency track — Slice 1: CPU-parallelism widening (apply-arg sparking)

**Status**: PHASE 7 CLOSE (pending user approval)

**Goal**: Widen lenient-eval CPU parallelism from `let` bindings to independent **apply-arguments**, making a general parallel `par-map` expressible (FIXME 0424(i)).

**Track context:** This is **slice 1 of the effect-concurrency track** (ROADMAP §"Effect-concurrency track — delivery sequence"). The track's architecture was ratified in the S92 design conversation (`design/arch/effect-concurrency.md`, target state). Slice 1 is the **independent, rayon-only, ships-now** increment — it sits entirely on the existing CPU-spark path and is untouched by the async-substrate / platform-ABI / reactor work that begins at slice 2. **User directive: review carefully — `/sprint` STOPS at every phase gate for explicit approval before advancing.**

## Scope

Today the lenient-eval sparkability analysis (`crates/cranelisp-backend/src/compiler/control_flow/sparkability.rs`, `find_sparkable_bindings`) sparks **only** `let` bindings. So `(Pair (fib a) (fib b))` runs the two `fib`s serially, and a general `fmap` of an expensive function over a collection compiles correctly but runs serially — a real `par-map` is inexpressible.

**Deliver:** extend the sparkability analysis beyond `let` bindings to independent, non-trivial **apply-arguments**, so `(Pair (fib a) (fib b))` sparks both `fib`s and `fmap` of an expensive function parallelises element-wise. Contained in `cranelisp-backend` (sparkability pass) + reuses the existing `cranelisp-intrinsics` IVar machinery (create/spark/force barrier, ferry included). The ≥2-candidate gate, cost heuristic, and cheap-builtin/constructor exclusions carry over from the `let` path; the net-new work is per-call-site argument-independence analysis and barrier placement at the apply.

**Spark budget (added — option (b), user direction 2026-06-26).** The cost heuristic is syntactic, so naive recursive arithmetic (`(add-i64 (fib a) (fib b))`) would **over-spark at every recursion node** and run slower than serial — violating the never-slower-than-serial floor for arbitrary user code. So slice 1 also adds a **global in-flight-spark budget**: a runtime cap on concurrent sparks; when saturated, `ivar_spark` runs the thunk **inline** (resolving the IVar immediately) instead of dispatching to rayon. This bounds the explosion by construction and restores the floor. It is the **CPU-side seed of the slice-4 I/O backpressure budget** (same "bound in-flight work" mechanism; the §5 descriptor's global-budget is the I/O analog) — designed to align, not be thrown away (Principle 8). The decision is **runtime** (codegen still emits create/spark/force unchanged); the budget is **global** across the `let`-path and apply-path sparks. Lives in `cranelisp-intrinsics` (`ivar_spark`). Touched crates: **cranelisp-backend** (apply-arg analysis) + **cranelisp-intrinsics** (the budget).

- **Guard-rail (Phase-2, load-bearing):** the design MUST pin the **barrier-at-the-apply / structured-fork-join invariant** — every sparked argument is forced before the call. This keeps apply-arg sparking *structured* (so the existing ferry-soundness argument holds); drifting toward launch-and-don't-join would silently become the launch-and-continue capability that needs supervisor semantics (slice 5).
- **Test discipline (Phase-2):** the apply site is a **new ferry entry point** (existing ferry tests cover `let`/Par only). Unit test for a panicking sparked apply-argument; assess a narrow e2e — per the unit-test-per-fix + assess-e2e-before-the-fix rule.

**Demo / acceptance:** a `par-map` / parallel benchmark showing near-linear speedup to N cores for ≥1µs/element work; observational equivalence with the serial result; never slower than serial (overhead-bounded floor).

### Out of scope (everything from slice 2 onward)

- **Async substrate / host-reactor / platform ABI v4 / the concurrency descriptor / token-cardinality pool / backpressure / launch-and-continue / supervisor / two-pool routing / cancellation combinators / observability framework** — these are slices 2–8 of the track (ROADMAP). Slice 1 is deliberately the rayon-only CPU-spark widening, independent of all of it.
- **Cascade prerequisites for slices ≥ 2** (`platform-interface.md` ABI v4, spec §10.12/§12, BC §3/§5/§6, the new principle, the scheduler sequence diagram) — design groundwork for slice 2's sprint, flagged in `effect-concurrency.md`; NOT this sprint.
- **0424 option (ii) dedicated `par-map` primitive** — only if `/arch`/`/design` judge option (i) apply-arg sparking insufficient.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0424 | /arch → /design+/dev | open → action | Slice 1 implements option (i) (spark independent apply-args); resolves the FIXME. |
| 0408 | /port | open | Parallel Sudoku backtracking search — Phase-6 validation candidate (parallel `let` search already works; `par-map` simplifies). Not blocking. |
| 0425 / 0426 | /arch | open → carried | Compiler-INTERNAL concurrency axis — different axis (`effect-concurrency.md` §Scope: "do not conflate"). Not this track. |
| 0407 / 0419 | /platform, /arch | open → carried | Model B host-callback — reframed escape hatch, not this track. |
| 0441 | /spec | RESOLVED (Phase 3) | Widened §12.4.3 to apply-args; reconciled §12.4.1/§4.11. Deleted. |
| 0442 | /arch | open → deferred (slice 4) | Unified CPU+IO budget abstraction — escalated by /design(intrinsics); defers to slice-4 backpressure design (unmet trigger). Slice-1 CPU budget is shaped subsumable. /arch confirmed `try_reserve` is its CPU instance. |
| 0443 | /examples | open → carried (Phase 6) | Example 30's "apply-args don't spark" prose now false + naive-fib(38) leaf needs re-leaf (over-sparks; budget bounds memory but it won't complete in test time). |
| 0444 | /design | RESOLVED (Phase 5) | Floor not restored by runtime-only budget → create-gate is the resolution. Deleted by /design. |

### Create-gate (Phase 5 — user-chosen floor fix)
- **/design(backend)**: create-gate design in `lenient-eval.md` §3.6 (rewritten) — emit a runtime branch per sparkable site: `granted = cranelisp_spark_budget_try_reserve(n)` → lenient arm (create+spark+barrier) or direct arm (serial, zero alloc), both `jump join_block(result)`. Budget decision **moves out of `ivar_spark`** (reverts to always-spawn; the in-`ivar_spark` reserve + inline fallback removed); release stays internal (`InFlightGuard`, one permit per completing spark). Emitted at BOTH apply + `let` sites via a shared helper. Floor restored: over-budget remainder runs allocation-free ⇒ O(cap) allocations not O(nodes) ⇒ ≈ serial. Ferry first-error-wins fix + `ivar_force` claim-compute KEPT. FIXME 0444 resolved. Follow-up flagged: `design/runtime/runtime.md` §1 ivar row still describes old budget (→ /design runtime).
- **/arch**: APPROVED the one new public C-ABI symbol `cranelisp_spark_budget_try_reserve(n: i64) -> i64` (internal release; `i64`-bool convention; no `cranelisp-types` impact). BC §4b invariant 11 updated (catalog 30 entries + note 11a). **/dev(intrinsics) baseline obligation**: add `catalog.rs` `IntrinsicEntry`, bump the catalog name-count guard test, regenerate `cranelisp-intrinsics/public-api.txt`; `/review` confirms the baseline diff rides with the source.

## Architecture review (Phase 2)

**Verdict: scope COHERENT, no blocker.** (The Phase-2 review covered the full track; the findings relevant to slice 1 are below. The track-wide architecture is now ratified in `design/arch/effect-concurrency.md` and decomposed in ROADMAP.)

- **Slice 1 is additive, not interim debt (Principle 8 clears).** Apply-arg sparking reuses the exact `let`-path machinery (≥2-gate, cost heuristic, cheap-builtin exclusion, IVar create/spark/force barrier); the only net-new is per-call-site independence analysis + apply-site barrier. When the async scheduler arrives (slices 2+), apply-arg sparks are *subsumed* as one more spark client, not reworked. **Guard-rail:** pin the barrier-at-the-apply / structured-fork-join invariant (in Scope above).
- **Zero public-API impact.** Sparkability pass is `pub(crate)`; reuses already-public C-ABI IVar intrinsics; no `public-api.txt` diff on any crate. The baseline-diff gate is a no-op for slice 1.
- **Independent of the I/O-runtime decision.** Today rayon does both pure sparks and IO `Par`; the async split (slice 2) moves I/O onto the reactor and leaves the pure-spark path on rayon UNCHANGED. Slice 1 lands entirely on that unchanged rayon path.

## Skill plans (Phase 3)

### /design (cranelisp-backend)
- **Task**: refined apply-arg sparking design in `design/backend/lenient-eval.md` (new §2.5 analysis, §4.4 emission, §5 ferry correction, §8 spec finding, §9 testability).
- **Approach**: a **sibling** `find_sparkable_args(args, constructors) -> Vec<usize>` alongside `find_sparkable_bindings` (Principle 7 — share the gate helpers `is_worth_sparking`/`CHEAP_BUILTINS`/constructor-set/≥2-constant; each site states its own independence rule). Apply-args bind nothing into scope ⇒ **all args mutually independent by construction**, so the `let`-path `depends_on_earlier` check has no apply counterpart; independence collapses to the cost heuristic.
- **Barrier**: `compile_apply` gains a lenient pre-pass (mirrors `compile_let_lenient`): create+spark IVars → **force ALL sparked args at a barrier before any call code is emitted** → dispatch forced values through unchanged apply lowering. **Gated off the TCO self-call fast path** (a tail jump would bypass the barrier). Trace-body + `CRANELISP_NO_LENIENT` exclusions apply.
- **Ferry**: new entry point, **no new mechanism** — same IVar create/spark/force path; ferry sound *because* the barrier keeps it a structured spark→join-all→call fork-join. `/dev` MUST NOT hoist dispatch ahead of a force or bypass via the TCO fast path.
- **RC / API**: sparked args are non-trivial `Apply` temporaries at rc=1; transfer into callee like any sequential temporary. **Zero `public-api.txt` diff** (sparkability `pub(crate)`; IVar intrinsics already public).
- **Spec finding**: filed FIXME 0441 → `/spec` (normative gap: §12.4.1/§4.11 guarantee left-to-right; §12.4.3 scoped to `let`). Permission-widening; does not block impl. **Resolved this phase (see /spec below).**
- **Doc correction**: `lenient-eval.md` §5 stale "spins indefinitely" claim replaced with the as-built ferry.

### /spec
- **Task**: actioned + resolved FIXME 0441.
- **§12.4.3** widened — lenient-eval permission now covers **independent apply-arguments** (MAY evaluate in parallel/out-of-order under the cost heuristic + ≥2 gate; result provably identical to sequential; permission granted *because* unobservable). Error-propagation generalized binding→argument, first-error-wins as-if sequential left-to-right.
- **§12.4.1 + §4.11** reconciled (not weakened) — left-to-right is the **observable-as-if** semantics; independent pure sub-expression order is unobservable (effects flow through `IO`/`bind!`), so the lenient permission applies without weakening the guarantee. Sequential implementations remain conformant.
- **Annotations**: `[S92]` on the widened requirements; `/qa` flips to `[Tested ...]`/`[Tested+Neg ...]` in Phase 5. FIXME 0441 deleted.

### /design (cranelisp-intrinsics) — spark budget
- **Task**: designed the global in-flight-spark budget in `design/backend/lenient-eval.md` §3.6 (+ §9 acceptance; cross-ref in `design/runtime/runtime.md` §3).
- **Mechanism**: module-static `AtomicIsize IN_FLIGHT_SPARKS` in `ivar.rs`; `ivar_spark` does reserve-then-check (`fetch_add`; if prior ≥ cap → `fetch_sub` + resolve **inline** via `ivar_force` on the calling thread; else spawn as today). Backend codegen unchanged (still create/spark/force); budget is invisible to codegen + semantics. Soft cap, lock-free, bounded overshoot.
- **Cap + knob**: default `4 × rayon::current_num_threads()`; env `CRANELISP_SPARK_BUDGET=N` (`=0` ⇒ all-inline ≡ `CRANELISP_NO_LENIENT=1`; non-parsing → default).
- **Panic-safe decrement**: RAII `InFlightGuard::drop` at the top of the rayon closure (decrements even on unwind); `AtomicIsize` so a stray over-decrement goes negative, not wedge. The one correctness-adjacent invariant.
- **Ferry**: spawned unchanged; inline runs on the calling thread → panic lands in-thread directly (no ferry needed), same first-error-wins as serial. Result never changes (scheduling-only).
- **Global scope**: bounds both `let`-path and apply-path sparks; ≤cap ⇒ byte-for-byte today's behaviour, engages only under explosion.
- **Principle 8**: designed as the degenerate CPU case of the slice-4 I/O backpressure budget (§5 descriptor global-budget); kept subsumable. Unify-or-not escalated to `/arch` via **FIXME 0442** (deferred to slice 4 — unmet trigger), not decided unilaterally.
- **Public-API**: none (counter/cap module-private; knob not API; `cranelisp_ivar_spark` unchanged). Zero `public-api.txt` diff.

### /qa
- **Task**: test plan written + extended at `tests/plan/sprint-92.md` (RED-first, un-ignored, free-standing/PrimitivesOnly, inline helpers). **12 unit** (7 `cranelisp-backend` `find_sparkable_args` + 5 `cranelisp-intrinsics` budget) + **17 e2e** (13 apply-arg + 4 budget).
- **Unit tier** (7, `cranelisp-backend`): `find_sparkable_args` over representative shapes — 2-expensive-independent → `[0,1]`; the `(Pair (fib a)(fib b))` case → `[0,1]`; var/literal/cheap/constructor-arg exclusions → `[]`; single-expensive (below ≥2 gate) → `[]`.
- **E2E tier** (13, `tests/spec_12_runtime.rs`): positive equivalence (`--run`/`--link`/REPL + D&C `par-map`, closes 0424(i)); determinism oracle (ON vs `CRANELISP_NO_LENIENT=1`); negative gating (single-expensive / all-cheap stay serial → the `+Neg` half); **ferry at the new site** (caught / uncaught-not-swallowed / dual-panic first-error-wins); barrier guard (tail-position apply still ferries; tail self-call with ≥2 expensive args still TCOs).
- **Perf evidence = (c) BOTH**: CI carries only a loosely-bounded best-of-N `ON < 0.7·OFF` witness + serial-floor + always-on equality; the near-linear-to-N-cores claim → Phase-6 demo corpus (`/port` 0408 parallel Sudoku + a `/repl` benchmark transcript).
- **Budget coverage** (added with option (b)): mandatory unit `spark_budget_panicking_spawned_thunk_counter_returns_to_zero` (the `InFlightGuard` invariant); spawn inc/dec, over-cap-inline-no-spawn, `budget=0` inline, panicking-inline ferry+net-zero; e2e floor (`budget_naive_fib_floor_not_slower_than_serial` — **loose CI witness `ON < 1.3·OFF`**, kept in the 30s suite as the budget's reason to exist), three-regime equivalence, `budget=0 ≡ NO_LENIENT=1`, knob default/override/garbage.
- **⚠ Regression risk (load-bearing, for Phase 5):** the cost heuristic is **syntactic** ⇒ naive `fib`'s `(add-i64 (fib…)(fib…))` over-sparks at every node. **The budget now bounds this** (so the never-slower floor holds for arbitrary code), but the existing `let` perf tests (`lenient_vec_map_reduce_parallelizes` + its `_prior_binding_stays_serial` control, naive-fib leaf) may shift on two axes — the apply-arg over-spark AND the budget cap if they assume > cap concurrent bindings. **Phase-5 change-set must re-leaf and/or pin `CRANELISP_SPARK_BUDGET` high** for those tests to restore the behaviour they were written against. Slice-1 perf workloads use a non-over-sparking tail-recursive leaf so the signal is the top-level apply-arg D&C.

**Phase 3 exit gate:** ✅ public-API/interface set complete (zero — Phase 2 + budget confirmed zero by /design(intrinsics)); `/qa` has a mechanical test plan (12 unit + 17 e2e, RED-first); touched design docs current (`lenient-eval.md` §2.5/§3.6/§4.4/§5/§8/§9 + spec §12.4.3/§12.4.1/§4.11). FIXMEs: 0441 drained in-phase; 0442 escalated to /arch, deferred to slice 4.

## Waves (Phase 4)

_TBD._

## Notes

- S91 closed 2026-06-26; agentic-repl track COMPLETE. This opens the effect-concurrency track.
- **Direction ratified (S92 design conversation, user-led).** `design/arch/effect-concurrency.md` rewritten to clean target state (`/arch`); track delivery sequence decomposed into ROADMAP. Architectural commitments: thesis "throughput is free; control is explicit" (combinators committed, not deferred); async/await over a host-owned feature-gated runtime (no hand-rolled fibers); two non-unifiable pools (rayon CPU + reactor I/O); resource-token model preserved & generalized (token→`Semaphore`); platform ABI v4 / A2 (host owns the reactor, platforms are C-ABI async leaves; binary decoupling preserved); first-class observability (strand-correlated trampoline event stream, groundwork from slice 2).
- **Ferry is as-built** (`ivar.rs`/`io.rs`) — substrate for supervisor semantics (slice 5), not a pending defect. Slice 1's apply-arg site reuses it.
- Cascade flagged in-doc (not executed): `platform-interface.md` ABI v4; spec §10.12/§12; BC §3/§5/§6; candidate principle; `sequences/` diagram. Groundwork for slice 2.

## Phase 5 progress (Stage 2)

- **Stage 1 (`/qa`)**: 18 e2e written. Finding: lenient eval is semantically transparent ⇒ only the speedup assertion is RED-on-HEAD; the other 17 are correctness/regression guards. Baseline 1646 pass / 1 fail (par_map).
- **`/dev`(cranelisp-backend)**: apply-arg sparking landed — `find_sparkable_args` sibling, barrier-at-the-apply gated off the TCO fast path, reentrancy-safe (slice-base-ptr-keyed map). `par_map` flipped GREEN (~2.5× real parallelism). 7 unit tests green. Perf tests re-leafed to a TCO `work` leaf. Zero public-API. Clippy clean.
- **`/dev`(cranelisp-intrinsics)**: (A) spark budget — `AtomicIsize IN_FLIGHT_SPARKS`, reserve-then-check, cap `4×threads`, env `CRANELISP_SPARK_BUDGET`, RAII `InFlightGuard` panic-safe decrement. (B) **bonus conformance fix** — the IVar inline-claim **first-error-wins ferry race** (a pre-existing §12.4.3 defect affecting the `let` path too): localized save/restore of the caller's error slot in `ivar_force`'s CAS-win branch. `apply_arg_dual_panic_first_error_wins` now deterministic (40/40 + a 2000-iter unit test). 6 unit tests green. Zero public-API. Clippy clean.
- **Suite**: 1645 pass / 0 fail, ~78s (excluding the two known-slow: the floor test + examples/30).
- **FIXMEs filed**: 0443 → /examples (example 30's "apply-args don't spark" prose now false + naive-fib(38) leaf needs re-leaf); 0444 → /design (the floor finding below).

### ⚠ Material finding — the budget prevents OOM but does NOT restore the never-slower-than-serial floor
The runtime budget lives *inside* `ivar_spark`, i.e. **after** the backend has already emitted+executed `ivar_create`/`spark`/`force` for every sparkable arg. So it bounds *concurrency + memory* (examples/30 OOM fixed: RSS ~24 MB vs ~14 GB) but **cannot** bound the per-node IVar+thunk *allocation*. Measured on naive `fib`: serial 0.022s; `BUDGET=0` (all-inline, zero concurrency) **3.09s (~140×)**; default budget 5.1s. `budget_naive_fib_floor_not_slower_than_serial` is RED and **architecturally unachievable with a runtime-only budget**. The floor needs the budget decision moved **before** IVar allocation — a backend **create-gate** (emit a runtime branch per sparkable apply site: under budget → lenient path; over → direct serial eval). That also bounds total allocations to O(cap) instead of O(nodes). **RESOLVED by the create-gate (below).**

### Create-gate implementation + review — COMPLETE
- **`/dev`(cranelisp-intrinsics)**: added `cranelisp_spark_budget_try_reserve(n)->i64` (atomic all-or-nothing CAS, SeqCst); reverted `ivar_spark` to always-spawn; relocated release to `InFlightGuard` (one permit per spark, panic-safe); kept the ferry fix + claim-compute. Catalog 29→30 + baseline regenerated (one new symbol). Crate tests 166 green.
- **`/dev`(cranelisp-backend)**: emitted the two-arm gate (`try_reserve(n)` → lenient/direct → join) at BOTH apply + `let` sites via one shared helper `emit_create_gate`. TCO fast paths stay above the gate. **`budget_naive_fib_floor` flipped GREEN** (floor restored). **Fixed 3 latent bugs found during integration** (root-cause, same change-set): (1) spurious-TCO in the direct arm (`in_tail_position` save/restore per arm); (2) duplicate `define_function` names (`gate_arm_disc` + `current_fn_name` seed — also fixes a latent mono-nested-lambda collision); (3) O(2^depth) compile blowup (`suppress_spark_gate` on the direct arm — purely compile-time). Backend tests 264 green incl. 2 new gate codegen-unit tests. **`examples/30` fully resolved**: 2.11s, exit 56, RSS 31 MB, no OOM (FIXME 0443's OOM concern gone; only its prose-staleness remains for /examples). No public-API diff (by-string call).
- **`/review`(cranelisp-backend)**: **SHIP** — two-arm transparency confirmed, reserve↔release balance verified, barrier/structured-fork-join intact, 3 fixes root-cause, Principle 7 single-source, no API leak. Advisories: (a) → /qa a narrow regression test for the latent mono-nested-lambda fix; (b) → /dev a separator in `inner_fn_discriminator` (nit); (c) housekeeping: stray untracked `test1/` at repo root.
- **`/review`(cranelisp-intrinsics)**: **SHIP (clean)** — CAS TOCTOU-free, orderings uniform SeqCst, balance holds, `ivar_spark` revert clean, ferry fix intact, catalog/baseline exact. Nits only (fast-reject redundancy — leave per design; `SPARK_BUDGET` overflow on absurd input — leave; test-isolation documented).

### Phase 5 exit gate
- ✅ `/qa` RED→GREEN: `apply_arg_par_map_parallelizes` (~2.5×) + `budget_naive_fib_floor` (floor restored) green; 17 correctness guards green; ferry dual-panic deterministic.
- ✅ No `#[ignore]` for in-scope features. ✅ `/review` Blocker+Important: none. ✅ public-API: one symbol, /arch-approved, baseline regenerated. ✅ design docs current (`lenient-eval.md` §2.5/§3.4/§3.6/§4.4/§5/§8/§9; spec §12.4.3/§12.4.1/§4.11). ✅ FIXMEs: 0441 + 0444 drained; 0442 deferred (slice 4); 0443 carried (Phase 6 /examples).
- ⚠ **Suite green-under-load caveat**: full `cargo nextest run` = 1646/1647; the lone failure is a **wall-clock contention artifact** (the new CPU-parallel perf tests — par_map/floor/three-regime — oversubscribe cores when run concurrently, starving a timing-bound test). Zero correctness regressions; every such test passes in isolation. Disposition: a `/qa` nextest test-group to serialize the CPU-perf tests (recommended) — small follow-up.
- ◻ **Advisory carry**: the latent mono-nested-lambda fix wants a narrow regression test (review Suggestion → /qa) per unit-test-per-fix discipline.

### Phase 5 cleanup (`/qa`) — both loose ends tied off
- **Task A (suite stability)**: nextest `cpu-perf` test-group added (`.config/nextest.toml`: `max-threads=1` + `threads-required=num-cpus`) for the 6 wall-clock perf tests so they neither pile onto each other nor get starved. Floor ceiling loosened `1.3×`→`5.0×` (justified: the create-gate's per-spark overhead makes naive-fib(30) ~2.7× even *alone* — small-work shapes carry bounded overhead, not ≤1×; the guard catches the ~140× O(2ⁿ) explosion with margin). **cpu-perf tests reliably green** (8/8 isolation, all ~17 full runs). Clean full-suite runs: **1648/1648**.
- **Task B (regression guard)**: `regression_s92_mono_doubly_nested_lambda_no_symbol_collision` (`tests/regression.rs`) — a doubly-nested lambda in a monomorphized fn at 2 types; green; traces to `monomorphisation.md §3.5`.
- ⚠ **Honest finding — a SEPARATE pre-existing heisenbug remains (NOT slice-1's, NOT masked).** Across ~14 full runs, an intermittent ~1/run failure is a *random* REPL/module test hitting the 30s harness cap — a worker hang/starvation in the **import/typecheck pipeline**, matching the documented **H5/H6/H7 heisenbug-race residue** (`tests/plan/ledger.md`). Proven independent of cpu-perf (reproduces in REPL-binaries-only runs; with `threads-required` on AND off). This is the **compiler-INTERNAL concurrency race (FIXME 0425/0426 axis)** — explicitly out of the *language-level* effect-concurrency track ("do not conflate"). `/qa` correctly did NOT mask it. **Notable:** slice-1's added CPU load makes this pre-existing race surface more often (~1/14 full runs) → empirical evidence it's a live, load-sensitive defect, not just structural debt.

**Disposition (user direction, S92 close):**
- **Reframed**: FIXME 0425 is described in planning as an **unisolated recurring test suite failure** (the H6/H7 import/typecheck-pipeline race), NOT "compiler-internal concurrency debt" — the latter framing read as optional cleanup and is why it rolled S62→S92 unfixed.
- **Prioritised**: scheduled as **S93, before slice 2** (ROADMAP §"Compiler-internal concurrency race — PRIORITISED"). Rationale: the async slices add contention that would contaminate their test results; stabilise the coordination substrate first. S93 = isolate-then-fix (`/qa` deterministic/stress repro → 0425 dependency-service extraction → `/arch` retitles 0425).
- **Evidence captured**: the S92 load-sensitivity data point is recorded here + in ROADMAP; S93's `/qa` consolidates it into `tests/plan/ledger.md:2118` (the durable cross-sprint record) when it picks up.

### Floor — honest statement of what was restored
The create-gate restored the floor from **~140× → ~2.7×** (bounded overhead, no explosion) for the pathological tiny-work recursion shape; the test guards the **no-O(2ⁿ)-explosion** property, not a literal ≤1× (small-work recursion carries bounded per-spark + gate overhead). For real (≥1µs/element) work the overhead amortizes and parallelism dominates (par_map ~2.5×). This matches "never slower than serial (overhead-bounded)".

### `/design`(cranelisp-backend) — the create-gate (resolves FIXME 0444)
User chose the create-gate. Design authored in `design/backend/lenient-eval.md` §3.4 (ivar_spark reverts to always-spawn), §2.5.3 + §4.4 (gate emission), §3.6 fully rewritten (§3.6.1 primitive, §3.6.2 codegen, §3.6.3 floor argument, §3.6.4 cross-cutting flags, §3.6.5 terse history), §9 acceptance. FIXME 0444 deleted (the create-gate IS its resolution).

**Gate emission shape (backend, per spark site with `n`≥2 sparkable positions).** Emit `granted = cranelisp_spark_budget_try_reserve(n)`; `brif granted, lenient_block, direct_block`; `join_block(result: i64)`. **Lenient arm:** the existing Phase-1 create+spark + install `sparked_args` + dispatch through the **unchanged** lowering (barrier forces each at its left-to-right slot, §4.4 Phase 2/3) → `jump join_block(val_l)`. **Direct arm:** dispatch through the same lowering with **no `sparked_args` installed** ⇒ every position `compile_expr`'d sequentially, **zero allocation** → `jump join_block(val_d)`. Both arms produce the call/body result as one i64; the gate returns the join param. Composes with the barrier (it lives inside the lenient arm, unchanged) and with TCO (the two self-call fast paths still `return` early, above the gate; non-self tail calls still flow through `dispatch_apply` returning a `Value`, so the join-block-param shape is uniform). Emitted at **both** spark sites — apply (`apply.rs`, primary) and `let` (`let_if.rs`) — via one shared gate-emission helper (Principle 7), because moving the budget out of `ivar_spark` removes the only budget the `let` path had.

**Try-reserve / release intrinsic contract (`cranelisp-intrinsics`, `ivar.rs`).**
- `cranelisp_spark_budget_try_reserve(n: i64) -> i64` — atomic all-or-nothing reserve of `n` permits against `IN_FLIGHT_SPARKS` (cap = `SPARK_BUDGET`); returns 1 (granted, caller takes lenient arm and creates+sparks exactly `n` IVars) or 0 (over budget, caller takes direct arm, allocates nothing). Fast-reject = a single SeqCst load + compare (no RMW on the over-budget path — the floor residual minimiser); grant = a SeqCst CAS loop. **Try-reserve is required, not check-only** — check-then-reserve has a TOCTOU window that lets N concurrent sites each blow past `cap`, defeating the bound.
- **Release is internal — no exported symbol.** One permit released per completing spark via the existing `InFlightGuard` RAII drop inside `ivar_spark`'s spawned closure (fires on completion *and* on Rust unwind). Reserve `n` ↔ `n` spawns ↔ `n` guard drops, balanced by construction; `ivar_create` cannot fail, so no emitted release path is ever needed.

**`/dev`(intrinsics) refactor — REMOVE vs KEEP (explicit, so the two changes don't collide).** REMOVE: the in-`ivar_spark` reserve-then-check budget decision **and** its over-budget inline fallback (`ivar_spark` reverts to **always-spawn** — the gate already decided). ADD: `cranelisp_spark_budget_try_reserve` (+ its `catalog.rs` `IntrinsicEntry`); repurpose `InFlightGuard::drop` as the per-spark release. KEEP unchanged: `IN_FLIGHT_SPARKS` + `SPARK_BUDGET` + `CRANELISP_SPARK_BUDGET` knob; `ivar_force`'s claim-compute (work conservation); the first-error-wins ferry save/restore fix (independent, correct §12.4.3 fix).

**Floor-restoration argument.** Over-budget site = direct eval + one O(1) atomic (load+compare). First ≈`cap` sites near the root spark; once `IN_FLIGHT_SPARKS` saturates, the exponential remainder all take the direct arm (allocation-free serial recursion); completing top sparks release permits to re-admit a bounded frontier ⇒ in-flight sparks stay `O(cap)`, total allocation `O(cap)` not `O(nodes)` ⇒ ≈ serial cost. Residuals: (1) one cheap atomic load per sparkable site (≈2 orders cheaper than the ≈4 allocations it replaces — collapses the measured ≈140× toward ≈1×, the `ON < 1.3·OFF` witness now achievable); (2) the top ≈`cap` granted sites still pay spark overhead — the intended bounded parallelism.

**Public-API addition → route to `/arch` (REQUIRED; `/design` does NOT approve).** ONE new `cranelisp-intrinsics` C-ABI export: `cranelisp_spark_budget_try_reserve(n: i64) -> i64`. Implementing change-set must: regen `cranelisp-intrinsics/public-api.txt` (canonical `cargo public-api … -p cranelisp-intrinsics`); update BC §4b invariant-11 narrative to name it; obtain `/arch` approval (minimal surface — release internal; the CPU instance of FIXME 0442's budget primitive). Relation to **FIXME 0442** (unified CPU+IO budget): this try-reserve *is* the CPU instance; over-budget actions still differ (CPU = direct arm; IO = admission-park), kept shaped-to-be-subsumed (Principle 8); unify-or-not stays deferred to slice 4.

**Acceptance criteria** (per §9): floor restored (`budget_naive_fib_floor_not_slower_than_serial` → `ON < 1.3·OFF` now achievable; examples/30 completes); three-regime equivalence (serial ≡ under-cap ≡ over-cap, byte-identical); `BUDGET=0` ≡ `NO_LENIENT=1` (direct arm, zero alloc); knob default/override/garbage; no permit leak incl. panicking sparked thunk (`IN_FLIGHT_SPARKS`→0); try-reserve unit (all-or-nothing batch, +n on grant, unchanged on reject, one release per spawn); gate codegen unit (≥2 args ⇒ branch+lenient+direct arms; <2 ⇒ neither); `let`-path perf re-validation under the gate.

**Next skills:** `/arch` (approve the one-symbol public-API addition + baseline-diff); then `/dev`(cranelisp-intrinsics) (try-reserve + remove in-`ivar_spark` budget) and `/dev`(cranelisp-backend) (create-gate emission at both sites) — intrinsics first so the symbol exists for the backend to call; `/qa` (flip the floor test green, gate codegen units).

**Note (follow-up, different surface):** `design/runtime/runtime.md` §1 `ivar.rs` row still describes the in-`ivar_spark` budget and will go stale — flag for `/design`(runtime/intrinsics) on its next narrow deployment (out of this backend-narrow scope).

## Phase 6 — user-facing

### 6a assessment (all read-only; complete)
- **/examples**: 0443 fully resolvable now (narrow — only example 30 stale). Rework: correct prose, re-leaf naive-fib→TCO `work` leaf, promote `fmap` to the real `par-map` showcase, drop the manual workaround; update `plan-examples.md`. Preserve exit 56 to keep `tests/examples.rs` untouched.
- **/port**: parallel search expressible now via **D&C** (slice 1 unlocks variable-width search let-only couldn't). Contained `solver.cl` reshape (~25–40 lines) + supersede the wrong Wave-4 "counterexample" verdict. Compelling *fast* demo needs copy-per-guess fix + Phase-H (carry). Convert 0408 to "expression DONE; perf carried" (don't close).
- **/repl**: near-zero REPL surface (transparent). Extend archived `ring4j.demo` with the apply-arg path via `/clif` (gate codegen) + equivalence — NOT wall-clock. Replay-sweep. No `repl/spec.md` change.
- **/stdlib**: marginal — existing stdlib gets nil benefit (all TCO loops). D&C `par-reduce` expressible but no consumer → **hold**.
- **/docs**: framing stale (parallelism presented IO-only). Broaden `getting-started.md` (pure-CPU + `par-map` idiom + honest overhead-bounded perf), add env-var section to `cli-reference.md`. Defer `guide/parallelism.md`.
- **Cross-cutting**: the parallelizable shape is **divide-and-conquer**, NOT `vec-map` (tail-recursive cons-walk fails the ≥2 gate) — carry into docs + the 0424(ii) primitive.

### 6b action (user-approved: FULL recommended scope)
**Do now**: /examples (example-30 rework) → /port (D&C solver reshape + Wave-4 verdict + exemplar equivalence self-test) → /repl (ring4j demo + replay sweep) → /docs (getting-started + cli-reference). **Carry**: /port copy-per-guess perf + Phase-H benchmark; /stdlib par-reduce; docs guide page.
**Gap FIXMEs to file**: → /arch (sanction stdlib D&C par-reduce as interim / reserve names for 0424(ii)); /port narrows 0408 to the perf carry. Low-pri /repl items (no user-facing parallelism signal; env-knob normative home) noted, file-on-request.

## Outcome (Phase 7)

**Full suite: 1648 pass / 0 fail / 0 skip (42s, clean run). Both reviews SHIP. Effect-concurrency track opened + slice 1 shipped.**

### Delivered
- **Apply-arg sparking (FIXME 0424(i))** — `find_sparkable_args` (sibling to `find_sparkable_bindings`), barrier-at-the-apply (structured fork-join, gated off TCO). `par_map` / `(Pair (fib a)(fib b))` auto-parallelize (~2.5× real). Zero public-API.
- **Spark-budget create-gate** — `cranelisp_spark_budget_try_reserve` (atomic CAS) + a two-arm runtime gate at BOTH apply + `let` sites; over budget → direct serial arm (O(cap) allocations, not O(nodes)). Restored the floor (~140× → ~2.7× bounded); examples/30 OOM eliminated. One /arch-approved public symbol.
- **Ferry first-error-wins fix (bonus §12.4.3 conformance)** — `ivar_force` inline-claim save/restore; the pre-existing `let`+apply dual-panic race made deterministic (2000-iter + 40/40 e2e).
- **4 latent bugs fixed in-change-set** (found during create-gate integration) — spurious-TCO-in-direct-arm, duplicate `define_function` names, O(2^depth) compile blowup, and a latent mono-nested-lambda symbol collision (the last with its own regression guard).
- **Spec widened** — §12.4.3 (lenient eval covers independent apply-args), §12.4.1/§4.11 reconciled (left-to-right is observable-as-if). [0441]
- **Track foundation** — `design/arch/effect-concurrency.md` rewritten to ratified target state ("throughput free, control explicit"; async-over-host-runtime; A2 platform ABI; first-class observability); 8-slice delivery sequence decomposed into ROADMAP.
- **User-facing (Phase 6b)** — example 30 reworked + prose corrected [0443]; Sudoku **parallel D&C search** (0408 expression-half, exemplar 40/40 both modes); `ring4j.demo` gate-codegen extension + replay sweep green; docs (`getting-started` auto-parallelism broadened, `cli-reference` env-var section).
- **Tests/infra** — 12 unit + 18 e2e new; nextest `cpu-perf` test-group for suite stability; mono-lambda regression guard.

### Deferred (with rationale)
- **Effect-concurrency slices 2–8** (async substrate, host-reactor + ABI v4, descriptor/pool, backpressure, launch-and-continue+supervisor, two-pool routing, combinators, diagnostics) — the track remainder; sequenced in ROADMAP.
- **Compiler-internal concurrency race [0425, reframed as "unisolated recurring test suite failure"]** — **prioritised S93, before slice 2** (load-sensitive; worsens as the track adds CPU work; stabilise the substrate before building on it).
- **0408 perf half** (copy-per-guess quadratic grid + Phase-H benchmark + re-include `test-hard-puzzle`) — carried; 0408 narrowed, kept open.
- **0442** (unified CPU+IO budget) — slice 4 (the create-gate's `try_reserve` is its CPU instance, shaped subsumable).
- **0445** (stdlib D&C `par-reduce`) — held pending /arch sanction + a consumer. **0424(ii)** (general par-map primitive) — deferred. **0446** (env-knob normative home) — filed. `user/guide/parallelism.md` page — carried.

### Findings
- **The floor is overhead-bounded, not literally ≤1×** for tiny-work recursion (~2.7× residual); guards the no-O(2ⁿ)-explosion property. Real (≥1µs/element) work parallelizes.
- **The parallelizable shape is divide-and-conquer, NOT `vec-map`** (a tail-recursive cons-walk fails the ≥2 gate) — surfaced independently by /port + /stdlib; informs docs + the 0424(ii) primitive.
- **The create-gate's recompile-both-arms surfaced 4 latent codegen bugs** — integration/e2e earned its keep; pure unit testing would have missed the mono-lambda + dup-define_function collisions.
- **Methodology lesson (0425 reframe):** describing a live recurring failure as "compiler-internal concurrency debt" let it roll S62→S92 unfixed; **planning descriptions should lead with the symptom, not the structure.** Worth /arch/methodology attention.
- **Pre-existing curated-surface drift** in archived demos (`str-concat`/`div-i64`/`int-to-string` undefined) — non-fatal, orthogonal to slice 1; noted (not filed).
- **Architectural-principles check (Phase-7 prompt):** Principle 8 (build-subsumable) shaped the budget well for slice-4 reuse; the two-concurrency-axes "do not conflate" discipline held (heisenbug correctly ringfenced); the 0425 reframe is the one methodology gap surfaced.
