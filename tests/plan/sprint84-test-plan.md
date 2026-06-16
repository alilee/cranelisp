# Sprint 84 Test Plan — Full Monomorphisation + Auto-IO Parallelisation

**Author:** `/qa` (Phase 3 Design). **Status:** Wave-0 AUTHORED (`.rs` committed; states verified).
**Scope source:** `sprints/SPRINT.md` §Scope (Clusters A + B) + §Architecture review (Phase 2) PO-0367.1/.2/.3.
**FIXMEs:** `0374` (typecheck Tier-2), `0375` (backend guard retire), `0373`+`0373-spec` (spec rank-1 HM / ambiguity / §12.1), `0367` (int re-wire), `0353` (platform/qa close).

This doc is subordinate to `tests/plan/ledger.md` (failure ledger) and `tests/plan/PLAN.md` (spec→test bridge). Phase-5 Stage-1 authoring derives the `.rs` files from the rows below. **No `.rs` authored in Phase 3.**

---

## 0. Conventions for these rows

- **Tier**: `e2e` (subprocess, `tests/`, /qa-owned, release gate) or `unit` (`crates/*/src/`, /dev-owned — NAMED here for plan completeness only; /qa does not author them).
- **W0-state**: failing-first state at Wave-0 commit (RED / GREEN / does-not-compile).
- **Green-on-landing**: the condition under which the row flips/stays green.
- **★ = mandatory failing-first Wave-0 guard** (must exist RED before the owning /dev wave begins).

The Tier-2 mono repros reuse the established 0373 repro shape (`tests/regression.rs::fixme_0373_*`): a plain polymorphic chain returning `neg(5) = -5 = 0xFFFF…FFFB` (≥1024 unsigned → SIGSEGV on the unsound `<1024` RC guard), asserted to exit **251** (`-5 & 0xFF`) on a clean run. SIGSEGV manifests as `status.code() == None` (`.assert_exit(251)` FAILS). That is the SIGSEGV-class signal; no signal-number assertion needed.

---

## Cluster A — Full Monomorphisation

### A.1 — 0374 Tier-2 concreteness: SIGSEGV-class e2e repros (the instance-shape gap)

The existing two 0373 guards (`fixme_0373_polymorphic_result_fn_value_two_hops_no_crash`, `fixme_0373_residual_polymorphic_result_cross_module_hops_no_crash`) cover the **result-hop** subset — a chain whose intervening hop's *result type* is a bare `Type::Var`. **Tier-1/1.5 deliberately does NOT collect** instances whose call-site result is concrete, and never enumerates polymorphic *values flowing as fn-arguments through HOFs* nor *nested-generic* instances reached only from a non-collected parent (machinery confirmed: `collect_local_parametric_calls` result-var gate `program.rs:2516-2520`; HOF case explicitly named non-covered at `infer.rs:691`; `collect_apply_var_calls` reaches inner hops only when the parent was top-level-collected). **These are the Tier-2 remainder and the coverage gap this sprint must witness.**

Each repro below is RED at Wave-0 (SIGSEGV or `Type::Var`-at-codegen panic), GREEN when 0374 makes every reachable instance concrete. All run through `--run`, `--link`, and REPL (use `run_through_all_modes` where the shape permits; the `:(IO Int)` `main` shape runs cleanly in all three). `// spec: spec/12-runtime.md §12.1` (representation) + cross-ref `spec/03-types.md` rank-1 HM once 0373(i) lands.

> **WAVE-0 AUTHORING CORRECTION (2026-06-16, /qa).** The "RED (SIGSEGV)" predictions for A.1.a/b/c (bare-Int HOF / nested-generic / arg-position) were STALE against HEAD — those shapes already monomorphise correctly (each exits 251/249 cleanly today). They are committed as GREEN-STAY *regression guards* instead. The GENUINE surviving residual gap, witnessed RED 5/5 at HEAD, is NARROWER: a polymorphic fn-value passed THROUGH A HOF whose result is a GENERIC ADT carrying a `Type::Var` FIELD (the field type survives as the residual `Type::Var` at the RC boundary). Committed as `mono_tier2_generic_adt_field_through_hof_no_crash` (the actual failing-first guard) + `mono_tier2_all_modes_concreteness_equivalence` (mode-uniformity on that shape). The mode-equivalence rollup does NOT use `run_through_all_modes::assert_all_equivalent` — that helper false-diverges on negative-Int results (REPL parses `-5`, --run/--link observe exit `251`); it drives --run/--link/REPL legs explicitly instead. The A.2 ambiguity rows landed as authored (RED — REPL echoes `:(user/Option a)`; `--run` `(defn ambig [] None)` compiles silently). See `tests/plan/ledger.md` Sprint-84-Wave-0 entry for the full disposition + the flag to /design(typecheck) that 0374's scope is the ADT-field instance.

| # | Test name | Tier | Instance-shape (the gap) | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| A.1.a ★ | `mono_tier2_hof_polymorphic_fn_arg_no_crash` | e2e | **Polymorphic value through a HOF.** `(defn apply2 [g x] (g x))` applied with a polymorphic fn-value (`neg`) whose result flows back ≥1024-unsigned. The fn-value is an *argument*, not a direct-name callee → never collected by Tier-1/1.5 (`infer.rs:691` names this uncovered). | RED (SIGSEGV) | 0374 enumerates the HOF instance at `g = (Fn [Int] Int)` |
| A.1.b ★ | `mono_tier2_nested_generic_concrete_parent_no_crash` | e2e | **Nested-generic via a concrete-result parent.** Outer hop's call-site result is CONCRETE (`:Int`) so Tier-1's result-var gate skips it (`program.rs:2516-2520`); the inner generic hop it calls is therefore never reached → inner result stays `Type::Var`. | RED (SIGSEGV) | 0374 roots-forward enumeration reaches the inner instance regardless of the parent's concrete result |
| A.1.c ★ | `mono_tier2_polymorphic_in_arg_position_no_crash` | e2e | **Polymorphic ARGUMENT (not result).** A generic fn whose *parameter* type stays `Type::Var` at a reachable instantiation (value built then consumed via a hop), exercising arg-position classify, not just result-position. | RED (SIGSEGV) | 0374 pins the parameter type at every reachable instantiation |
| A.1.d | `mono_tier2_same_def_two_instantiations_no_crash` | e2e | **One def, two reachable concrete instances** (`id` used at `Int` AND `String`, each through a hop). Witnesses definition-driven enumeration (per-`(Def, type-args)`), not call-site-only. The `String` instance is `AlwaysHeap`, the `Int` is `NeverHeap` — a mis-shared single template would mis-RC one of them. | RED (SIGSEGV on the Int/≥1024 path; or `Type::Var` panic) | 0374 emits a distinct `MonoDefn` per `(Def, type-args)` |
| A.1.e | `mono_tier2_cross_module_hof_arg_no_crash` | e2e | **HOF + cross-module** composite: the polymorphic-fn-value-as-arg case (A.1.a) where the HOF lives in an imported module — the union of the two gaps Tier-1.5 split. | RED (SIGSEGV) | 0374 enumerates cross-module HOF instances |
| A.1.f | `mono_tier2_all_modes_concreteness_equivalence` | e2e | **Mode-equivalence rollup.** The A.1.a–c shapes run through `run_through_all_modes` — `--run` / `--link` / REPL must agree (clean exit 251 in all three). Guards against a mode that mono's differently (e.g. REPL incremental path skipping an enumeration). | RED (one+ mode SIGSEGVs / diverges) | 0374 mono is mode-uniform |

**Coverage-gap statement (the deliverable /sprint asked me to surface):** Tier-1/1.5 covers exactly the *polymorphic-result-hop* set (same-module + cross-module + 0355-constrained), enumerated **backward from result-var detection**. The Tier-2 remainder is everything reachable **forward from the roots** that the backward result-var gate skips: **(1)** polymorphic fn-values passed as HOF arguments (`infer.rs:691`, A.1.a/A.1.e); **(2)** generic instances reached only through a concrete-result parent that the result-var gate excludes (`program.rs:2516-2520`, A.1.b); **(3)** polymorphic ARGUMENT positions (vs result, A.1.c); **(4)** the same def at multiple reachable concrete instantiations needing distinct `MonoDefn`s (A.1.d). The single risk to flag: **0344's fold-accumulator preservation** — Tier-1's result-var gate exists *specifically* to avoid pinning a deliberately-kept polymorphic accumulator (`program.rs:2503-2515`); Tier-2's roots-forward enumeration MUST NOT re-collapse it. **A.1.b is the canary** — if Tier-2 over-monomorphises, the 0344 fold guard (`tests/spec_*::*fold*`/`reduce`) regresses. Note this for /design(typecheck): the enumeration must distinguish "instance reachable at a concrete type" (monomorphise) from "scheme deliberately generalised-and-kept" (leave generic). I add **A.1.g** below as the explicit negative.

| # | Test name | Tier | Concern | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| A.1.g | `mono_tier2_fold_accumulator_not_over_monomorphised` | e2e | **NEGATIVE / regression canary.** A `reduce`/fold whose accumulator scheme is generalised-and-kept (0344). Tier-2 MUST still compile and run it correctly (no over-mono, no scheme re-collapse). Confirms Tier-2 grew coverage without regressing the 0344 preservation. | GREEN at W0 (already works), MUST STAY GREEN | stays green through 0374 |

### A.2 — 0373(ii) ambiguity rule (NEGATIVE)

An unconstrained top-level type var remaining after inference is a **type error** ("ambiguous type"), NOT compiled, NOT defaulted. Enforced in typecheck at the post-inference generalisation/finalisation boundary (per Phase-2 point 1 — the `CheckError` complement to 0375's codegen assert). The exact `CheckError` variant + wording is /design(typecheck)'s seam — **coordinate before authoring the assertion**; this row uses substring matching (`error:` + `ambiguous`) per the error-test convention, NOT exact text.

| # | Test name | Tier | Concern | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| A.2.a ★ | `mono_ambiguous_unconstrained_top_level_var_rejected_neg` | e2e | A top-level form whose finalised type retains an unconstrained `Type::Var` that no reachable instantiation pins → must produce an "ambiguous type" `CheckError` on stdout, exit non-zero, NO crash, NO silent compile. | RED (currently either compiles silently or behaves undefined — verify the W0 behaviour during authoring) | 0373(ii) + the /typecheck check rejects with the ambiguity error |
| A.2.b | `mono_ambiguous_neg_does_not_reach_codegen` | e2e | Negative companion: the ambiguous form must NOT reach codegen (no `Type::Var`-at-codegen panic, no SIGSEGV) — it is caught at typecheck. Asserts the error is a *clean* typecheck rejection, not a downstream crash. | RED | 0373(ii) catches it pre-codegen |

> **Seam coordination (file if blocked):** if /design(typecheck) has not pinned the `CheckError` variant + diagnostic substring by Wave-0 authoring time, /qa asserts on the generic `error:` + `ambiguous` substrings and files `target: /design` only if the wording is genuinely undecidable. Phase-2 point 1 already specifies the variant exists; this is a wording sync, not a design gap.

### A.3 — 0375 guard retirement (backend-seam observability)

0375 makes `classify(Type::Var)` an assert and retires `emit_rc_inc_guarded` from the `Type::Var` path, KEEPING it for nullary-tag discrimination within a known `Mixed` ADT. The **kept path** and the **retired path** are both observable.

- **Kept path (Mixed ADT nullary-tag discrimination):** the canonical seam test is a **/dev backend UNIT test** (`crates/cranelisp-backend/src/heap.rs` `#[cfg(test)]`) per 0375 — `/qa` does NOT author it. Named here for plan completeness: `mixed_adt_nullary_tag_still_discriminates` + `classify_type_var_now_panics`.
- **e2e need assessment:** The retired-path soundness ("no UAF on the dec path for a polymorphic-positioned scalar") is **already witnessed e2e by A.1.a–f** — those ARE the SIGSEGV/UAF repros that the `<1024` guard caused. **No additional 0375-specific e2e is warranted** beyond A.1. The kept path (nullary-tag ADT discrimination) needs a positive e2e that a `Mixed` ADT with nullary + heap-carrying constructors still round-trips correctly after the guard is scoped down — this DOES warrant one e2e (a known `Mixed` ADT could be mis-classified if the guard-scoping edit is too aggressive):

| # | Test name | Tier | Concern | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| A.3.a | `mixed_adt_nullary_and_heap_ctor_roundtrip_after_guard_scope` | e2e | A `Mixed` ADT (≥1 nullary ctor + ≥1 heap-carrying ctor) constructed, matched, and RC-managed correctly — the KEPT-guard path must still discriminate a nullary tag (`< 1024`) from a heap pointer. Build, match both arms, drop, no crash, correct values. | GREEN at W0 (works today), MUST STAY GREEN | stays green through 0375 (regression guard against over-scoping the guard removal) |
| A.3.b | `mixed_adt_nullary_tag_still_discriminates` (unit) | unit | /dev-authored, named for completeness | n/a | /dev lands with 0375 |
| A.3.c | `classify_type_var_now_panics` (unit) | unit | /dev-authored, named for completeness | n/a | /dev lands with 0375 |

> **0375 e2e verdict (the assessment /sprint asked for):** the SIGSEGV-class repros A.1.a–f are the retired-path UAF witnesses (they fail BECAUSE of the unsound guard today and pass once the guard is gone + concreteness is total). The only NEW e2e 0375 warrants is the KEPT-path guard A.3.a — ensuring guard-scoping does not break legitimate `Mixed`-ADT nullary discrimination. This is the negative-coverage complement: "the guard removal removes the bug WITHOUT removing the legitimate behaviour."

---

## Cluster B — Auto-IO Parallelisation (PO-0367 checklist)

### B.1 — PO-0367.1 deterministic AST-property tests (unit-tier, NO concurrency)

These pin the **Par-emission contract** at the bind-chain-analysis seam. Per Phase-2 ruling + `tests/CLAUDE.md` two-tier model, these are **/dev unit tests** in the int binary crate (`src/bind_chain_analysis.rs` / `src/session_setup.rs` `#[cfg(test)]`) authored alongside the wiring — **NOT /qa-authored**. They are NAMED here because PO-0367.1 names them as **mandatory failing-first Wave-0 guards** and /qa owns the plan that asserts they exist. **/qa's Wave-0 obligation:** confirm these unit rows exist RED before the wiring lands; if /dev cannot author them in Wave-0 (they're same-wave as the wiring per the unit-test-per-fix discipline), the e2e equivalents B.2.* carry the failing-first signal. **Resolution (flag to /sprint):** PO-0367.1 says "MUST exist failing-first before wiring" but unit tests land in the same change-set as the wiring (`memory/feedback_unit_test_per_fix.md`). The reconciliation: /qa authors **e2e proxies** for the .1 contract in Wave-0 (B.1-proxy rows below, which ARE /qa-ownable and CAN be RED in Wave-0), and /dev adds the in-crate unit tests in the wiring change-set. The e2e proxies are the Wave-0 failing-first guards; the units are the per-fix seam pins.

**MUST-emit (positive):**

| # | Test name | Tier | Concern | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| B.1.a | `bind_chain_independent_diff_token_emits_par` (unit) | unit | data-independent + different-token (or token-0/Commutative) pair → emits `ParBind`/`Par` | n/a (/dev, wiring change-set) | wiring lands |

**MUST-NOT-emit (negatives — the soundness guards):**

| # | Test name | Tier | Concern | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| B.1.b | `bind_chain_data_dependent_emits_no_par_neg` (unit) | unit | later binding references an earlier-bound name → MUST NOT Par-group | n/a (/dev) | wiring lands |
| B.1.c | `bind_chain_same_nonzero_token_not_independent_neg` (unit) | unit | same non-zero resource token → MUST NOT hoist to independent branches (may be serial group, never independent) | n/a (/dev) | wiring lands |
| B.1.d | `bind_chain_sequential_class_emits_no_par_neg` (unit) | unit | `Sequential`-class pair (e.g. `read-line`/`print`) → MUST NOT Par-group | n/a (/dev) | wiring lands |

**/qa e2e proxies for PO-0367.1 (these ARE the Wave-0 failing-first guards /qa owns):**

| # | Test name | Tier | Concern | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| B.1.proxy-pos ★ | `auto_io_independent_diff_token_parallelizes_e2e` | e2e | data-independent diff-token pair observably parallelises end-to-end. (Subsumed by / same shape as `resource_serial_diff_token_parallelizes` — see B.3; listed for traceability.) | RED | 0367 wiring |
| B.1.proxy-neg-dep ★ | `auto_io_data_dependent_stays_serial_e2e` | e2e | a *data-dependent* diff-token chain (second call's token/arg derives from the first's result) MUST stay serial (wall-clock ≥ 1.5× single) even after wiring — proves the independence analysis is real, not "parallelise all diff-token pairs". | GREEN at W0 (serial today), MUST STAY GREEN after wiring | stays green (negative guard) |
| B.1.proxy-neg-seq ★ | `auto_io_sequential_class_stays_serial_e2e` | e2e | a `Sequential`-class pair (ordering-sensitive IO) MUST NOT be parallelised after wiring — stays serial/ordered. | GREEN at W0, MUST STAY GREEN | stays green (negative guard) |

> **Why the negative e2e proxies stay green both before AND after wiring:** before wiring, NOTHING parallelises (all serial → negatives trivially hold). After wiring, the negatives are the *real* soundness assertion — they catch a wiring that over-parallelises (parallelising a data-dependent or Sequential pair would be a correctness/ordering bug). They are the cheapest guard against the wiring going too far, exactly as Phase-2 §Refinement-to-Wave-0 directs.

### B.2 — PO-0367.2 mode-uniformity (e2e)

Same source → same Par-grouping decision in `--run`, `--link`, REPL. No mode silently skips the pass (the current dormant state IS a mode-uniformity hole — the REPL-eval path note in `bind_chain_analysis.rs` "does not invoke auto-scheduling" is the specific gap).

| # | Test name | Tier | Concern | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| B.2.a ★ | `auto_io_par_grouping_uniform_across_modes` | e2e | a data-independent diff-token program parallelises (diff-token wall-clock < 1.5× single) in `--run` AND `--link` AND REPL — no mode skips. Asserts the grouping *decision* is identical across modes (via the timing witness in each mode). | RED in ALL modes at W0 (pass dormant everywhere) | 0367 wires mode-uniform (incl. REPL-eval seam) |
| B.2.b | `auto_io_repl_eval_path_parallelizes` | e2e | REPL-specific: the eval-expression path (the named gap) emits the Par decision — a bind chain entered at the REPL parallelises. Closes the `bind_chain_analysis.rs` REPL-eval note. | RED at W0 (REPL eval path does not invoke auto-scheduling) | 0367 wires the REPL-eval seam |

### B.3 — PO-0367.3 structured-fork-join timing witnesses (EXISTING guards)

The ONLY genuinely-concurrent obligation, narrow (structured fork-join over pure IO thunks, deterministic join point). **/qa verified these exist** in `tests/spec_10_io.rs`:

| # | Test name | Tier | Current state (verified this phase) | Green-on-landing |
|---|---|---|---|---|
| B.3.a ★ | `resource_serial_diff_token_parallelizes` | e2e | **EXISTS, RED today** (confirmed `tests/spec_10_io.rs:1010`). Asserts diff-token wall-clock < 1.5×single (300ms midpoint, 200ms sleeps) in `--run` AND `--link`. Failing-not-ignored defect guard for 0367. | **MUST FLIP GREEN** when 0367 lands |
| B.3.b ★ | `resource_serial_same_token_serializes` | e2e | **EXISTS, GREEN today** (confirmed `tests/spec_10_io.rs:974`). Same-token wall-clock > 1.5×single in `--run` AND `--link` — serialised regardless of independence. | **MUST STAY GREEN** (regression guard against wrongly parallelising same-token branches) |

These two together witness the token-serialisation decision AND the join semantics. `// spec: spec/10-io.md §10.12.4` (verified anchor present). **No new B.3 tests needed — the pair already exists; the obligation is state-transition (B.3.a RED→GREEN, B.3.b GREEN→GREEN).**

> **Fork-join error-ferry note (out of S84 scope, flag for awareness):** `design/arch/CLAUDE.md` records an OWED-IMPLEMENTATION fork-join error-slot ferry obligation (worker panic silently swallowed on the joining thread, spec §12.4.3 observational-equivalence). 0367 wiring turns Par on across all modes — if a branch faults, the un-ferried slot becomes observable. This is a PRE-EXISTING defect, NOT introduced by 0367, and NOT in S84 scope. If a B.* witness surfaces it (a parallelised branch panicking and being swallowed), /qa files a fresh FIXME `target: /dev` (per the OWED-IMPLEMENTATION note) — do not block 0367 on it unless a B.* test directly trips it.

### B.4 — 0353 closure

0353 closes EXACTLY when `resource_serial_diff_token_parallelizes` (B.3.a) goes green. **/qa verified:**

- The S83 fixture `resource-serial-sleep-ms` **is present** at `platforms/test-capture/src/lib.rs:92` (`resource_serial_sleep_ms`, `cl_name: "resource-serial-sleep-ms"`, ResourceSerial, token + ms), wired into the test-capture GOT/manifest (`:127`/`:141`). The companion `commutative-sleep-ms` is also present (`:70`). Confirmed.
- The fixture lives in `platforms/test-capture/` (NOT `crates/cranelisp-platform/`; the SPRINT brief's "verify it's present in `crates/cranelisp-platform/`" resolves to: the *SchedulingClass round-trip + token-placement* unit tests are in `crates/cranelisp-platform/src/lib.rs:2465+`, the DLL *fixture function* is in `platforms/test-capture/`). Both halves present.

| # | Item | Tier | State | Closure condition |
|---|---|---|---|---|
| B.4.a | 0353 closure | — | open | closes when B.3.a (`resource_serial_diff_token_parallelizes`) green. NO new test — B.3.a IS the closure witness. |

> **Platform `public-api.txt` watch-item (per Phase-2 point 4):** the 0353 fixture already landed (S83), so no *new* fixture lands in S84 → **no new `crates/cranelisp-platform/public-api.txt` move expected from 0353 this sprint.** The watch-item is theoretical (it would apply only if /dev(platform) adds a *new* test-capture fn). The test-capture fns are C-ABI DLL exports (`pub extern "C"`), not Rust `pub` library items, so even a new one likely does not move the Rust baseline — but if `crates/cranelisp-platform/public-api.txt` moves, two-update discipline applies. **For S84: no action expected; confirm at close.**

---

## Wave-0 mandatory failing-first guard list (★)

These MUST exist RED (or compile-failing) at Wave-0 commit, before the owning /dev wave begins. This is the list /sprint confirms for "Wave 0 has enough to draft failing tests":

**Cluster A:**
1. `mono_tier2_hof_polymorphic_fn_arg_no_crash` (e2e) — HOF gap
2. `mono_tier2_nested_generic_concrete_parent_no_crash` (e2e) — nested-generic-via-concrete-parent gap
3. `mono_tier2_polymorphic_in_arg_position_no_crash` (e2e) — arg-position gap
4. `mono_ambiguous_unconstrained_top_level_var_rejected_neg` (e2e) — 0373(ii) ambiguity NEGATIVE

**Cluster B:**
5. `auto_io_independent_diff_token_parallelizes_e2e` (e2e, B.1.proxy-pos) — independence-analysis positive
6. `auto_io_data_dependent_stays_serial_e2e` (e2e, B.1.proxy-neg-dep) — MUST-NOT-Par data-dependent (green-stay)
7. `auto_io_sequential_class_stays_serial_e2e` (e2e, B.1.proxy-neg-seq) — MUST-NOT-Par Sequential-class (green-stay)
8. `auto_io_par_grouping_uniform_across_modes` (e2e, B.2.a) — mode-uniformity
9. `resource_serial_diff_token_parallelizes` (e2e, B.3.a) — **already exists RED** (the canonical 0367/0353 witness)
10. `resource_serial_same_token_serializes` (e2e, B.3.b) — **already exists GREEN**, must stay green

Plus the /dev-authored unit guards (B.1.a–d, A.3.b–c) which land in their wiring/fix change-sets per the unit-test-per-fix discipline; /qa confirms their existence at wave gate, does not author them.

---

## Existing-guard states verified this phase

| Guard | File:line | State at W0 | Note |
|---|---|---|---|
| `resource_serial_diff_token_parallelizes` | `tests/spec_10_io.rs:1010` | **RED** | flips green on 0367; 0353 closure witness |
| `resource_serial_same_token_serializes` | `tests/spec_10_io.rs:974` | **GREEN** | must stay green (same-token serialise guard) |
| `fixme_0373_polymorphic_result_fn_value_two_hops_no_crash` | `tests/regression.rs:3307` | **GREEN** (Tier-1, since `5634dd3`) | result-hop subset already covered; Tier-2 extends |
| `fixme_0373_residual_polymorphic_result_cross_module_hops_no_crash` | `tests/regression.rs:3386` | **GREEN** (Tier-1.5, since `9e57330`) | cross-module result-hop subset covered; Tier-2 extends |
| `resource-serial-sleep-ms` fixture | `platforms/test-capture/src/lib.rs:92` | **present** | 0353 fixture landed S83 |
| SchedulingClass round-trip + token-placement units | `crates/cranelisp-platform/src/lib.rs:2465+` | present | platform-side already covered |

---

## Risks / open coordination

1. **Tier-2 over-monomorphisation vs 0344 fold preservation** (PRIMARY Cluster-A risk). The Tier-1 result-var gate exists to NOT pin a generalised-and-kept accumulator (`program.rs:2503-2515`). Tier-2's roots-forward enumeration must distinguish "reachable concrete instance" (monomorphise) from "scheme deliberately kept" (leave generic). **A.1.g is the canary** + the existing 0344 fold guards must stay green. Flagged to /design(typecheck).
2. **0373(ii) `CheckError` wording sync** (Cluster-A). A.2.a/.b assert on substring (`error:` + `ambiguous`), exact variant TBD by /design(typecheck). Coordinate before Phase-5 authoring; file `target: /design` only if genuinely undecidable.
3. **PO-0367.1 failing-first vs unit-test-per-fix** (Cluster-B). The .1 unit negatives land in the wiring change-set (same-wave), so /qa's Wave-0 failing-first signal is carried by the e2e proxies B.1.proxy-* + B.2.* + B.3.a. Resolution recorded in §B.1. No FIXME needed.
4. **Mode-uniformity REPL-eval seam** (Cluster-B). B.2.b targets the named `bind_chain_analysis.rs` REPL-eval gap specifically — the most likely place a wiring lands non-uniform. Keep it distinct from B.2.a so a REPL-only miss is visible.
5. **Fork-join error-ferry** (out of scope, awareness only). Turning Par on may make the pre-existing un-ferried-panic defect observable. Not an S84 blocker; file fresh FIXME if a B.* test trips it.

No `cranelisp-types` / BC / interfaces edit is implied by any row (confirmed against Phase-2 points 1 + 4). No new platform baseline move expected (0353 fixture already landed S83).
