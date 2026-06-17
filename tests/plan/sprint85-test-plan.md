# Sprint 85 Test Plan — Concurrency: Auto-IO Wiring + RC-inc Atomicity + Fork-Join Error-Ferry Remainder

**Author:** `/qa`. **Status:** PHASE 5 STAGE 1 — the two NEW 0398 `.rs` guards authored (`tests/spec_10_io.rs`); empirical W0-states recorded below.
**Scope source:** `sprints/SPRINT.md` §Scope items 1–4 + §Architecture review (Phase 2) (a)–(d).
**FIXMEs:** `0367` (int — auto-IO wiring, CORE), `0397` (arch RULED → /dev intrinsics/primitives — RC-inc atomicity), `0398` (qa — Par-boundary panic e2e guard, gated on 0367), `0353` (platform/qa — closes automatically on 0367's diff-token guard).

This doc is subordinate to `tests/plan/ledger.md` (failure ledger) and `tests/plan/PLAN.md` (spec→test bridge). Phase-5 Stage-1 authoring derives the `.rs` rows below.

Definition of done (the sprint's measurable exit, per SPRINT.md §Scope item 4): `cargo nextest run --workspace` is **fully green (0 fail)**. The baseline is **3 reds, all auto-IO** (`resource_serial_diff_token_parallelizes`, `auto_io_independent_diff_token_parallelizes_e2e`, `auto_io_par_grouping_uniform_across_modes`). Every red flips on the 0367 wiring.

**Phase-5 Stage-1 EMPIRICAL CORRECTION (2026-06-17, /qa).** The two NEW 0398 Par-boundary guards were authored and their pre-wiring state determined empirically. The Phase-3 expectation that 0398.4.a would be **RED-on-author** is **WRONG**: pre-0367-wiring the bind chain runs sequentially, so a div-by-zero in a branch argument surfaces trivially on the own thread (`--run` exit≠0 + "division by zero"; REPL slot cleared so the next expression is clean). **Both 0398 guards are GREEN-on-author** → they are **MUST-STAY-GREEN regression guards** (analogous to `resource_serial_same_token_serializes`), NOT reds-that-flip. They prove the already-landed S76 ferry keeps surfacing the first error once 0367 wires Par grouping; a regression to a swallowed panic flips them RED — that is the 0398 defect signal. The S85 red baseline is therefore the **3 existing auto-IO reds only**; the 0398 guards do not change the red count. (Verified: targeted run `10 tests run: 7 passed, 3 failed` — the 3 known reds unchanged, both 0398 guards PASS.)

---

## 0. Conventions for these rows

- **Tier**: `e2e` (subprocess, `tests/`, /qa-owned, release gate) or `unit` (`crates/*/src/`, /dev-owned — NAMED here for plan completeness only; /qa does not author them).
- **W0-state**: failing-first state at Phase-5 Stage-1 commit (RED / GREEN / NEW-RED).
- **Green-on-landing**: the condition under which the row flips/stays green.
- **★ = mandatory failing-first guard** (must be RED before the owning /dev wave begins).

**Layering principle applied throughout (per `tests/CLAUDE.md` two-tier model + 0367 brief).** A grouping/independence *decision* is an **AST-shape** property → it belongs in a **/dev unit test** in the int binary crate (`src/bind_chain_analysis.rs` `#[cfg(test)]`). A *runtime-observable* consequence (parallel wall-clock; serial ordering; a worker panic surfacing on the joining thread) is **only** witnessable **e2e** → /qa-owned. The two answer different questions; both are required. Where the same behaviour has both an AST-shape and a runtime face, the row names BOTH layers and marks which is /dev vs /qa.

---

## Item 1 — 0367 Auto-IO wiring (CORE)

The Par-insertion pass (`auto_schedule_defn` / `apply_bind_chain_analysis`) is `#[allow(dead_code)]` with zero live callers. Wiring it onto `process_cluster_once` → `finalize_cluster` (the mode-uniform seam, per Phase-2 (a)) makes the existing dormant guards observe parallelism. **The algorithm and backend are complete and unit-tested** — this item is wiring + verification, not new behaviour.

### 1.1 — Positive guards that MUST FLIP RED → GREEN (already exist)

| # | Test name | File:line | Tier | What it asserts | W0-state | Green-on-landing | Closes |
|---|---|---|---|---|---|---|---|
| 1.1.a ★ | `resource_serial_diff_token_parallelizes` | `tests/spec_10_io.rs:1010` | e2e | Two data-independent ResourceSerial calls with DIFFERENT tokens run concurrently: diff-token wall-clock `< 1.5×D` (300ms midpoint, 200ms sleeps) in `--run` AND `--link`. The canonical 0367/0353 witness. | **RED** | flips when ParBind-insertion is reactivated | 0367, 0353 |
| 1.1.b ★ | `auto_io_independent_diff_token_parallelizes_e2e` | `tests/spec_10_io.rs:1193` | e2e | The Commutative independence path: a data-independent `commutative-sleep-ms` ×2 `bind` chain parallelises (`< 1.5×D`) in `--run` AND `--link`. Proves the defect is the missing wiring, not ResourceSerial-specific. | **RED** | flips on wiring | 0367 |
| 1.1.c ★ | `auto_io_par_grouping_uniform_across_modes` | `tests/spec_10_io.rs:1319` | e2e | Mode-uniformity (PO-0367.2): the SAME source parallelises (`< 1.5×D`) in `--run` AND `--link` — the grouping *decision* is identical across modes; no mode silently skips the pass. | **RED in all modes** | flips when wiring is mode-uniform (worker + REPL both funnel through `process_cluster_once`) | 0367 |

> These three ARE the entire S85 red baseline. When all three are green and the one new 0398 guard (item 4) is green, the workspace is fully green and the sprint's definition-of-done is met.

### 1.2 — Negative guards that MUST STAY GREEN (the soundness guards — already exist)

These are GREEN today (nothing parallelises → all serial/ordered) AND must STAY green after wiring. After wiring they become the *real* soundness assertion: they catch a wiring that over-parallelises (a correctness/ordering bug).

| # | Test name | File:line | Tier | What it asserts | W0-state | Green-on-landing | Layer note |
|---|---|---|---|---|---|---|---|
| 1.2.a ★ | `resource_serial_same_token_serializes` | `tests/spec_10_io.rs:974` | e2e | Two data-independent ResourceSerial calls with the SAME non-zero token are SERIALISED regardless of independence: wall-clock `> 1.5×D` in `--run` AND `--link`. | **GREEN** | stays green | runtime-observable → e2e is the right layer (token-grouping is a trampoline runtime decision, not an AST-shape) |
| 1.2.b ★ | `auto_io_data_dependent_stays_serial_e2e` | `tests/spec_10_io.rs:1226` | e2e | A DATA-DEPENDENT diff-token chain (second effect's token derives from the first's result → `a` free in second) MUST stay serial (`> 1.5×D`) even after wiring. Proves the independence analysis is real, not "parallelise all diff-token pairs". | **GREEN** | stays green | the **runtime face** of 1.4.b; AST-shape face is the /dev unit 1.4.b |
| 1.2.c ★ | `auto_io_sequential_class_stays_serial_e2e` | `tests/spec_10_io.rs:1256` | e2e | A `Sequential`-class pair (`print`/`print`) MUST stay ordered ("first" before "second") in `--run` AND `--link` after wiring. | **GREEN** | stays green | the **runtime face** of 1.4.c; AST-shape face is the /dev unit 1.4.c |

> **Why these stay green both before and after.** Before wiring, nothing parallelises → negatives trivially hold. After wiring, they are the cheapest guard against the wiring going *too far* (parallelising a data-dependent or Sequential pair). Per the 0367 brief: "verify the data-dependency and Sequential-class negatives still hold." These three are exactly that verification.

### 1.3 — REPL-eval-path mode coverage (assessment)

The `bind_chain_analysis.rs` note ("REPL eval-expression path currently does not invoke auto-scheduling") names the highest-risk place for a non-uniform wiring. Phase-2 (a) confirms the REPL funnels through `process_cluster_once` too, so the seam is mode-uniform **by construction** — but that must be witnessed, not assumed.

| # | Test name | Tier | Concern | W0-state | Green-on-landing |
|---|---|---|---|---|---|
| 1.3.a | `auto_io_repl_eval_path_parallelizes` | e2e | REPL-specific: a data-independent diff-token `bind` chain entered at the REPL parallelises (timing witness via REPL capture). Closes the `bind_chain_analysis.rs` REPL-eval note; keeps a REPL-only miss visible distinct from 1.1.c. | **NEW-RED** (REPL eval path dormant today) | flips when 0367 wires the REPL-eval seam through `process_cluster_once` |

> **Assessment / coordination note.** 1.1.c (`auto_io_par_grouping_uniform_across_modes`) currently folds the REPL leg into its `--run`/`--link` assertions (its comment says the REPL-specific proxy is "deferred to /dev's wiring change-set"). 1.3.a is the explicit REPL-eval witness. If REPL timing capture proves flaky (REPL output is line-buffered, not a clean wall-clock window), the fallback is a `/clif`-based REPL introspection check that a `Par` node is emitted for a REPL-entered bind chain — an emission witness, not a timing witness. Decide the REPL witness mechanism with /int(/dev) before authoring; if the timing window is unreliable, file `target: /int` for a REPL `Par`-emission introspection hook rather than relaxing to a flaky timing assertion. This is the one row whose mechanism is not yet pinned.

### 1.4 — Par-emission AST-property contract (/dev unit tests — NAMED, not /qa-authored)

These pin the grouping *decision* at the bind-chain-analysis seam. They are **AST-shape** properties → **/dev unit tests** in `src/bind_chain_analysis.rs` `#[cfg(test)]`, authored alongside the wiring per the unit-test-per-fix discipline (the existing `src/bind_chain_analysis.rs::tests` module is the home — `/sprint` brief confirms the negatives already partly live there). NAMED here because /qa owns the plan asserting they exist; /qa does NOT author them. /qa's wave-gate obligation: confirm these unit rows exist (RED-first or same-change-set per unit-test-per-fix) before the wiring lands; the e2e proxies above carry the failing-first signal /qa owns.

| # | Test name (unit) | Concern | Owner |
|---|---|---|---|
| 1.4.a | `bind_chain_independent_diff_token_emits_par` | data-independent + different-token (or token-0/Commutative) pair → emits `ParBind`/`Par` | /dev (int crate) |
| 1.4.b | `bind_chain_data_dependent_emits_no_par_neg` | later binding references an earlier-bound name → MUST NOT Par-group (AST-shape face of e2e 1.2.b) | /dev (int crate) |
| 1.4.c | `bind_chain_sequential_class_emits_no_par_neg` | `Sequential`-class pair (`read-line`/`print`) → MUST NOT Par-group (AST-shape face of e2e 1.2.c) | /dev (int crate) |
| 1.4.d | `bind_chain_same_nonzero_token_not_independent_neg` | same non-zero resource token → MUST NOT hoist to independent branches (may be a serial group, never independent — AST-shape face of e2e 1.2.a) | /dev (int crate) |

> **Layer assignment (the explicit /sprint ask).** The 0367-brief negatives split cleanly:
> - **AST-shape** (independence/grouping *decision*, no thread pool needed) → unit, in `src/bind_chain_analysis.rs::tests`: 1.4.a–d. The dependent-binding and Sequential-class "MUST NOT Par-group" checks are *fundamentally* AST-shape — you can decide them by inspecting the rewritten chain without running it.
> - **runtime-observable** (does it actually run concurrently / in order on the live trampoline) → e2e, in `tests/spec_10_io.rs`: 1.1.a–c (positive), 1.2.a–c (negative). These need the thread pool + wall-clock.
>
> Both layers are required. The unit answers "did the pass make the right grouping decision"; the e2e answers "did the runtime honour it". A green unit + red e2e would mean the pass decides correctly but the wiring/dispatch is broken (or vice versa) — the two-layer split makes that distinguishable.

---

## Item 2 — 0397 RC-inc atomicity (soundness precondition; /dev-authored unit, NAMED here)

Phase-2 (b) RULED: ordering = `fetch_add(1, Ordering::Release)` (NFR C.4.1 floor, `spec/appendix-c-nfr.md:144`); blessed `pub fn rc_inc(ptr: i64)` in `cranelisp_intrinsics::rc`, mirroring `consume_shallow` (nullary-tag-skip via `HeapHeader::RC_OFFSET`, `rc_trace("inc", …)`). `/dev` then routes `marshal.rs::shallow_rc_inc` + `string.rs::string_identity` through it, deleting the open-coded pointer arithmetic.

Per the unit-test-per-fix discipline (mandatory unit test per fix, `tests/CLAUDE.md` §"Unit-test-per-fix"), **`rc_inc` lands with /dev-authored unit tests in `crates/cranelisp-intrinsics/src/rc.rs` `#[cfg(test)]`** — /qa does NOT author these. NAMED here so the plan records the obligation and /qa confirms their existence at wave gate.

| # | Test name (unit) | Concern | W0-state | Owner |
|---|---|---|---|---|
| 2.a | `rc_inc_increments_refcount` | `rc_inc(ptr)` on a heap value bumps the RC by exactly 1 (read RC at `HeapHeader::RC_OFFSET` before/after). | n/a (/dev, lands with the fn) | /dev (cranelisp-intrinsics) |
| 2.b | `rc_inc_skips_nullary_tag` | `rc_inc` on a nullary-tag ("immediate", `< 1024`) value is a no-op — no write, no fault. Mirrors `consume_shallow`'s nullary-tag skip. | n/a (/dev) | /dev (cranelisp-intrinsics) |
| 2.c | `rc_inc_uses_release_ordering` | (best-effort / documentary) the inc uses `fetch_add(1, Release)` — pin the RULED ordering at the seam so a future weakening to `Relaxed` is caught. May be a source-level assertion or a Loom/concurrent-inc check if the crate carries that infra; otherwise a comment-pinned single-thread inc test + the rustdoc-on-fn is the floor. | n/a (/dev) | /dev (cranelisp-intrinsics) |
| 2.d | `shallow_rc_inc_routes_through_rc_inc` / `string_identity_routes_through_rc_inc` | After re-route: `cranelisp-primitives` `shallow_rc_inc` + `string_identity` produce identical RC effects as before (no behavioural change), with the open-coded arithmetic gone. | n/a (/dev) | /dev (cranelisp-primitives) |

> **Atomicity / concurrent-inc guard — assessment (the /sprint ask).** A *true* concurrent-inc race guard (two threads inc the same value, assert no lost update) would require Loom or a stress harness. Phase-2 (b) RULED the ordering by argument (NFR floor + consistency with the SeqCst inline path), NOT by empirical race-detection — so a heavyweight concurrent-inc test is **not required for soundness closure**. The worth-having guard is the lightweight 2.c (pin the ordering at the seam) so the RULED ordering does not silently regress. **No e2e is warranted for 0397**: the RC-inc atomicity is invisible from the binary's outside surface (it manifests only as the *absence* of a heisenbug under the now-live spark forks); the live-spark paths it protects are exercised e2e by item 1's parallelisation guards (which fork user work) and item 4's panic guard. If a parallelisation guard from item 1 ever flakes with an RC-related crash after wiring, THAT is the signal a concurrent-inc race exists — file `target: /dev` then. For S85, the unit tests + the RULED ordering are closure.
>
> **Public-API watch:** `rc_inc` is a new `pub fn` → bumps `crates/cranelisp-intrinsics/public-api.txt` (regen + review in the same change-set per the baseline-diff discipline). Not a test row, but /qa confirms the baseline moved at wave gate.

---

## Item 3 — 0353 closure (no new test)

0353 closes EXACTLY when 1.1.a (`resource_serial_diff_token_parallelizes`) goes green. The S83 fixture `resource-serial-sleep-ms` is present (`platforms/test-capture/src/lib.rs:92`), wired into the test-capture GOT/manifest. No new /platform work, no new test.

| # | Item | State | Closure condition |
|---|---|---|---|
| 3.a | 0353 closure | open | closes when 1.1.a green. **No new test** — 1.1.a IS the closure witness. |

---

## Item 4 — 0398 Par-boundary fork-join error ferry (NEW e2e guard, /qa-authored, gated on 0367)

Phase-2 (c) CONFIRMED: the ferry **mechanism is already landed and unit-tested at both boundaries** (IVar `ivar.rs:204–222`, Par `io.rs:527–564` `ItemResult{positioned,error}`; `set_runtime_error` `panic.rs:108`; spec §12.4.3 pinned `spec/12-runtime.md:157`; invariant 13 closed). No mechanism work, no /spec work. The IVar/lenient equivalent (`lenient_binding_panic_not_swallowed_neg`, `tests/spec_12_runtime.rs:626`) already passes.

**The only S85 remainder is the Par-boundary e2e guard** — the Par/IO variant of `lenient_binding_panic_not_swallowed_neg`, recorded as deferred in `tests/plan/PLAN.md` L2 ("Par/IO variant deferred — needs IO infra"). It is **gated on 0367's wiring**: a Par-branch panic can only be witnessed end-to-end once user source actually emits `Par` nodes. NEW, RED-on-author, flips green when 0367 lands.

| # | Test name | Tier | What it asserts | W0-state (EMPIRICAL) | Green-on-landing | Closes |
|---|---|---|---|---|---|---|
| 4.a | `auto_io_par_branch_panic_surfaces_on_join_neg` (`tests/spec_10_io.rs`) | e2e | A runtime panic inside ONE branch of an auto-scheduled `Par` group MUST surface on the joining thread — MUST NOT be silently swallowed. `--run`: exit≠0 AND "division by zero" surfaces. `--link`: exit≠0 (non-swallow only — see LINK-MODE NOTE). `// spec: spec/12-runtime.md §12.4.3`. | **GREEN-STAY** (NOT red-on-author — pre-0367 the chain is sequential so the panic surfaces trivially on the own thread; verified PASS) | **STAYS green** once 0367 Par-groups the chain — the already-landed S76 ferry re-raises the first error on join. Regression to a swallowed panic → flips RED (the 0398 signal). | 0398 |
| 4.b | `auto_io_par_branch_panic_no_slot_pollution_neg` (`tests/spec_10_io.rs`) | e2e | After a Par-branch panic surfaces, the runtime-error slot is NOT left polluted: a REPL session does the panicking bind chain, then a clean independent expression in the SAME process which MUST evaluate to `:primitives/Int 42` (does not spuriously inherit the prior error). Witnesses the first-error-wins + slot-clear half of the ferry. | **GREEN-STAY** (pre-0367 sequential — slot cleared on read; verified PASS) | **STAYS green** on 0367 wiring; the ferry's slot management is already landed. Slot left polluted across the Par fork → flips RED. | 0398 (companion) |

> **Construction (as authored — mechanism 1, no new fixture).** A data-independent two-effect `bind` chain over `commutative-sleep-ms` where the FIRST branch's argument is `(div-i64 200 0)`. The div-by-zero panic fires inside that branch's argument-computation extent; pre-0367 sequential (panic on own thread), post-0367 the same chain is Par-grouped and the panic fires inside a spark → the ferry must re-raise on join. Mechanism 2 (a panicking `/platform` fixture) was NOT needed — the div-by-zero in the branch argument does not hoist out of the branch. **LINK-MODE NOTE:** a div-by-zero panic in a `--link` produced binary currently terminates by SIGSEGV (exit 139), not a clean "division by zero" message — a PRE-EXISTING `--link` panic-surfacing gap independent of Par/0367 (reproduces with a plain non-bind div-by-zero `--run`/`--link` program). The 4.a `--link` leg therefore asserts only the spec-load-bearing non-swallow property (exit≠0), not the message, to avoid entangling 0398 with that separate gap. The `--run` leg asserts full message surfacing.

> **Construction note (coordinate with /int(/dev) before authoring).** Witnessing a panic *inside a Par branch* requires a data-independent two-effect `bind` chain (so the pass Par-groups it) where ONE branch raises a runtime panic. The test-capture platform has NO panicking fixture today (only `commutative-sleep-ms` / `resource-serial-sleep-ms` / `print` / `read-line` / noops). Three candidate mechanisms, in preference order:
> 1. **Runtime panic in the effect's argument computation** — e.g. one branch is `(commutative-sleep-ms (div-i64 1 0))`: the `div-i64` div-by-zero panic fires while computing the branch. This needs NO new fixture and reuses the established div-by-zero panic shape from `lenient_binding_panic_not_swallowed_neg`. **Preferred** — confirm during authoring that the panic fires inside the Par-branch dynamic extent (not hoisted before the fork).
> 2. If (1) hoists the panic out of the branch (constant-folded / evaluated before the spark), fall back to a panicking test-capture fixture — file `target: /platform` for a `panic-effect` fixture function (a ResourceSerial/Commutative fn that panics). This is the same fixture-extension pattern 0353 used; it would extend `tests/scripts/build-link-prereqs.sh`-covered test-capture.
> 3. Last resort: a Par branch over an effect whose *value* triggers a downstream RC/marshal fault. Avoid — non-deterministic, hard to attribute.
>
> Decide mechanism (1) vs (2) at authoring time; if (2), file the `/platform` fixture FIXME as part of Phase-5 Stage-1 so the fixture lands before the guard can flip. The guard is RED-on-author regardless (no Par emitted yet) — the mechanism choice only affects HOW it observes the panic once Par is live.
>
> **Why this is failing-first-correct as RED-on-author.** Per `tests/CLAUDE.md` §Failing-not-ignored: an in-scope guard whose feature isn't wired yet is RED (not `#[ignore]`). 0398's guard is in-scope this sprint and gated on 0367 (same sprint) → it ships RED in Phase-5 Stage-1 and flips with the wiring, exactly like 1.1.a–c.

---

## Mandatory failing-first guard list (★) — what must be RED before the /dev wiring wave

These MUST be RED (or NEW-RED-on-author) before the 0367 wiring wave begins. This is the list /sprint confirms for "Phase 5 Stage 1 has enough failing tests to scope the wiring":

1. `resource_serial_diff_token_parallelizes` (e2e, 1.1.a) — **exists RED** — canonical 0367/0353 witness
2. `auto_io_independent_diff_token_parallelizes_e2e` (e2e, 1.1.b) — **exists RED** — Commutative independence
3. `auto_io_par_grouping_uniform_across_modes` (e2e, 1.1.c) — **exists RED** — mode-uniformity

> 4.a (`auto_io_par_branch_panic_surfaces_on_join_neg`) was forecast NEW-RED in Phase 3 but is **GREEN-on-author** (empirical — pre-0367 sequential panics surface trivially); it moves to the GREEN-STAY list below. The S85 failing-first baseline is the **3 auto-IO reds above**, unchanged by the 0398 authoring.

GREEN-STAY soundness guards that MUST NOT regress (verified at wave gate, not in the failing-first list):

4. `resource_serial_same_token_serializes` (e2e, 1.2.a) — same-token serialises
5. `auto_io_data_dependent_stays_serial_e2e` (e2e, 1.2.b) — data-dependent stays serial
6. `auto_io_sequential_class_stays_serial_e2e` (e2e, 1.2.c) — Sequential-class stays ordered
7. `lenient_binding_panic_not_swallowed_neg` (e2e, item 4 reference) — IVar/lenient ferry already passes
8. `auto_io_par_branch_panic_surfaces_on_join_neg` (e2e, 4.a) — **GREEN-STAY** — 0398 Par-boundary ferry; stays green when 0367 wires Par grouping
9. `auto_io_par_branch_panic_no_slot_pollution_neg` (e2e, 4.b) — **GREEN-STAY** — 0398 slot-clear companion

Plus the /dev-authored units (1.4.a–d, 2.a–d) which land in their wiring/fix change-sets per unit-test-per-fix; /qa confirms their existence at wave gate, does not author them.

---

## Existing-guard states verified this phase

| Guard | File:line | State (verified) | Note |
|---|---|---|---|
| `resource_serial_diff_token_parallelizes` | `tests/spec_10_io.rs:1010` | **RED** | flips on 0367; 0353 closure witness |
| `auto_io_independent_diff_token_parallelizes_e2e` | `tests/spec_10_io.rs:1193` | **RED** | flips on 0367 (Commutative path) |
| `auto_io_par_grouping_uniform_across_modes` | `tests/spec_10_io.rs:1319` | **RED in all modes** | flips on 0367 (mode-uniform) |
| `resource_serial_same_token_serializes` | `tests/spec_10_io.rs:974` | **GREEN** | must stay green (same-token serialise) |
| `auto_io_data_dependent_stays_serial_e2e` | `tests/spec_10_io.rs:1226` | **GREEN** | must stay green (data-dependent serial) |
| `auto_io_sequential_class_stays_serial_e2e` | `tests/spec_10_io.rs:1256` | **GREEN** | must stay green (Sequential ordered) |
| `lenient_binding_panic_not_swallowed_neg` | `tests/spec_12_runtime.rs:626` | **GREEN** | IVar/lenient ferry already passes (0398's already-landed half) |
| `resource-serial-sleep-ms` fixture | `platforms/test-capture/src/lib.rs:92` | **present** | 0353 fixture landed S83 |
| `commutative-sleep-ms` fixture | `platforms/test-capture/src/lib.rs:70` | **present** | independence-path fixture |
| Par ferry mechanism | `crates/cranelisp-intrinsics/src/io.rs:527–564` | **present + unit-tested** | 0398's mechanism (already landed S76 W4) |
| `dead_code` pass | `src/bind_chain_analysis.rs:41`, `src/session_setup.rs:329` | **dormant** | 0367 re-wires |

---

## Risks / open coordination

1. **REPL-eval timing witness mechanism (1.3.a)** — the only row whose mechanism is unpinned. REPL output is line-buffered, so a wall-clock timing window may be unreliable. Coordinate with /int(/dev) on whether a timing witness or a `Par`-emission introspection witness (`/clif`) is the right REPL check; file `target: /int` for an introspection hook only if timing proves genuinely flaky. Do NOT land a flaky timing assertion. (1.1.c already covers `--run`/`--link` mode-uniformity, so a REPL-witness deferral does not block the core wiring.)
2. **0398 panic-in-branch construction (4.a/4.b)** — RESOLVED at authoring: mechanism 1 (div-by-zero in the branch argument, no new fixture) works — the panic does NOT hoist out of the branch, so no `/platform` panicking-fixture FIXME was needed. Both guards are GREEN-on-author (not RED — pre-0367 sequential). NEW finding logged: the `--link` produced binary SIGSEGVs on a div-by-zero panic (exit 139, no message) — a PRE-EXISTING `--link` panic-surfacing gap independent of Par/0367; the 4.a `--link` leg asserts only non-swallow (exit≠0) to avoid entangling that separate gap. If a future sprint wants full "division by zero"-message surfacing in `--link`, that is a distinct `/dev` (backend/int) concern, not 0398.
3. **Over-parallelisation soundness** — the wiring must honour the negatives 1.2.a–c. The PRIMARY risk is a wiring that parallelises a data-dependent or Sequential pair. These three GREEN-STAY e2e + the /dev AST-shape units 1.4.b–d are the guard; both layers must hold.
4. **RC-inc concurrent-race (0397)** — Phase-2 RULED the ordering by argument, not empirically. No heavyweight Loom/stress test required for closure (per item-2 assessment). The live-spark exercise IS item 1's parallelisation guards. If an item-1 guard flakes with an RC crash after wiring, file `target: /dev` — that is the empirical signal a race survived the ruling.
5. **Public-API baseline (0397)** — `rc_inc` is a new `pub fn` → `crates/cranelisp-intrinsics/public-api.txt` must move in the same change-set (two-update discipline). /qa confirms at wave gate; not a test row.

No `cranelisp-types` / BC / interfaces edit is implied by any row (confirmed against Phase-2 (d): "`cranelisp-types`: NONE"). No new platform baseline move expected unless 0398 needs a panicking fixture (mechanism 2).

---

## Flake-hardening record — §12.4.3 lenient-eval CPU-bound timing witnesses (2026-06-17, /qa)

The two §12.4.3 lenient-eval wall-clock witnesses in `tests/spec_12_runtime.rs`
(`lenient_vec_map_reduce_parallelizes` + its negative control
`lenient_vec_map_reduce_prior_binding_stays_serial`) were **timing-flaky** under
`cargo nextest run --workspace`. Unlike the auto-IO timing tests above, which are
**SLEEP-based** (wall-clock parallelism is immune to CPU contention), these are
**CPU-bound** (recursive `fib`). Under a saturated parallel harness every core is
busy with sibling test processes, so a single lenient-ON run can be starved of
spare cores and show ~no speedup — a false failure (observed once at ON=246ms vs
a 240ms threshold). A CPU-bound wall-clock parallelism assertion measured ONCE
under a saturated harness is fundamentally noisy.

**Mechanism chosen: best-of-N (positive) / majority-of-N (negative).** N=4 attempts
(`PMR_ATTEMPTS`). Rationale: it is the simplest mechanism that genuinely fixes the
flake without weakening the parallelism proof, and it does not require nextest
test-group config (no `.config/nextest.toml` test-group exists for these; not a
clean fit for two tests).

- **Positive** (`lenient_vec_map_reduce_parallelizes`): the speedup
  `ON < 0.7*OFF` must appear in **at least one** of N attempts; early-exits on the
  first qualifying attempt. A purely SEQUENTIAL impl never qualifies in ANY attempt
  (ON ~= OFF regardless of contention), so one qualifying attempt still genuinely
  proves the two same-block bindings were sparked and ran in parallel — the test
  still fails loudly if lenient eval stops parallelising.
- **Negative control** (`..._prior_binding_stays_serial`): the inverse —
  **majority** of N attempts (strict `>N/2` = 3 of 4) must show NO speedup
  (`ON >= 0.7*OFF`); early-exits once the majority is locked in. Tolerates one
  contention blip (an OFF-slow reading that spuriously looks like a speedup) while
  still failing if the prior-binding case were wrongly sparked (which would show
  the speedup in all/most attempts).
- **Semantic transparency (ON exit == OFF exit) is asserted on EVERY attempt** and
  is never relaxed — it is contention-immune and is the most valuable invariant.

**Margin unchanged:** `PMR_SPEEDUP_NUM/DEN = 7/10` (ON < 0.7*OFF, a >=1.43x
speedup). Leaf cost unchanged (`fib(35)`, Vec of 8). The robustness comes from
best-of-N, not from loosening the per-attempt margin.

**Observed numbers (10-core box, direct).** Positive: ON ~105–134ms, OFF ~287–297ms,
ratio **~2.2–2.7x** (clears the 0.7 threshold by a wide margin). Negative control:
ON ~296–304ms, OFF ~294–300ms, ratio **~0.98–0.99x** (ON stays well above the
~206ms threshold — no speedup). Same exit code (73) ON and OFF in both — semantic
transparency holds.

**Verification.** Targeted loop (5× isolated): 5/5 green. Full `cargo nextest run
--workspace` ×6 (the contention condition that produced the original flake): all
green, **2745 passed / 0 failed**, runtimes 24.4–28.1s (under the 30s budget; the
negative-control majority early-exit keeps the worst case ~6 subprocess runs, not
8). Both PMR tests confirmed PASS under full parallel load (positive ~0.47–0.51s
via early-exit; negative ~2.0s). The flake is resolved.
