# Sprint 98: Concurrency-track drain + the trampoline boundary defect — clear the slate before the parallelism axis

**Status**: PHASE 7 CLOSE — **PROPOSED CLOSE, awaiting user approval to archive.** All phases complete: bands A–E landed, bug #2 closed, `/review` clean bill + hardening, Phase 6 delivered (exemplar v9 replay + docs split + repl assessment + the user-directed 0499 root-cause fix), all 22 FIXMEs filed/carried this sprint resolved. Suite **1798 pass / 1 skip / 0 fail**. See Outcome below.

**Goal**: Drain the entire S97-carried defect/FIXME backlog — headlined by the `/int↔/backend` trampoline arg-lifetime boundary (`0486`) and the bug-#2 launched-effect UAF it names — so the parallelism/memory-contention axis (S99) tunes the spark gate against a fully-settled substrate, with zero known-defect REDs and zero open concurrency-track FIXMEs behind it.

## Why this sprint, why now

The roadmap's next-scheduled increment is the parallelism/memory-contention knot (`0459` contention-aware spark gate + `0408` Sudoku perf). But that is a **clean-substrate** play — it tunes the create-gate against a *settled* concurrency model. S97 shipped the v9 ctx-vtable handle model and drained most of the concurrency track, but **closed deliberately with carry**: one boundary defect (`0486` + the bug-#2 UAF guard `launch_grid_corrupt`, RED; `exemplar_web` quarantined), 4 more RED test-side guards (`0487`/`0489`×2/`0490`), and a spread of design/spec/doc rulings filed during close (`0483`–`0493`). Tuning the contention gate on top of an open UAF and 5 REDs is tuning against a moving target.

**User direction (2026-07-01): resolve the defects and FIXMEs first, then move to the parallelism/memory-contention sprint.** S98 is the drain; parallelism (`0459`/`0408`) becomes **S99**.

## Scope (PHASE 1 SCOPE DRAFT)

### A. The spine — the trampoline arg-lifetime boundary + the bug-#2 fix (`0486`)

The headline. A launched per-connection handler whose terminal `send-conn` is reactor-polled **after** the launched frame is torn down; the frame's scope-cleanup frees the baked `Response` buffer before the deferred send reads it → heap-metadata overrun → SIGABRT. Deterministic guard committed RED (`tests/launch_grid_corrupt.rs`); `exemplar_web` quarantined.

`0486` is filed `target: /arch` because the fix exposed an unwritten boundary: **there is no owned contract for "a launched/reactor-deferred effect's baked arguments stay alive until the reactor resolves it."** S97 landed the low-risk doc half (reactor.md relocated `design/int/`→`design/intrinsics/`; BC §4a/§4b/§6 affirm intrinsics as backend-emitted runtime + `/int` as host-client). **What remains for S98:**

1. **`/arch` rules the boundary + pins the contract** (`0486` **Level-1** — locked): write the deferred/launched-effect arg-lifetime-across-suspension contract as an explicit `/backend`↔runtime interface, naming which side owns keep-alive. `reactor.md:150` already *names* this contract but never specifies it. Manifests at `bounded-contexts.md §3/§4b/§6` + `io-trampoline.md`/`reactor.md`.
2. **The owning skill lands the fix** — flip `launch_grid_corrupt` guard green + un-quarantine `exemplar_web`. Owner determined by `/arch`'s keep-alive ruling (backend-emitted vs runtime-owned).

**QA-first Stage-1 refinement (2026-07-01, `/qa`): the `redA` "pure-String UAF" hypothesis is REFUTED (measured, 8 trials each).** Churned-`Response.body` String does NOT reproduce (0/8); a single live vec does NOT (0/8). The load-bearing floor is a **borrowed-Var `(Vec …)` with TWO vecs both live** across the launched `send-conn` (8/8). New smaller deterministic guard committed: `tests/launch_vec_send_corrupt.rs::launched_strand_two_live_vecs_send_does_not_corrupt_heap_neg` (RED) — drops the `Cell`/`Grid` ADT wrappers.

**⚠️ Band A SPLIT — the invariant-15 keep-alive LANDED but is necessary-not-sufficient (2026-07-01, `/dev` on `cranelisp-intrinsics`, `75f286d`; FIXME `0494`).** The runtime keep-alive is implemented + correct + unit-tested (net-zero-inc variant; `EffectPoll`/`StateClosure` RAII, exactly-once two-path release) — **kept; invariant 15 stands.** But an A/B of both variants proves it does **not** flip the guards, and the arch-preferred **move-out-sentinel is a FALSE-GREEN** (eager-frees the `accept` listener closure → server hangs → crash never triggers → guard reads "no signal"). The residual bug-#2 UAF is a **`/backend` codegen borrowed-Var two-live-vec RC miscount on the launched strand** (`ring2-rc.md §5.5` path) — a double-dec that frees the vec early; the state-closure RC is balanced (consistent with S97's "UAF not a miscount" — different object). **The Level-1 "no backend change" premise is contradicted by evidence.**
- **`0486` runtime half: DONE** (kept). `0486` stays OPEN carrying the residual.
- **`0494` (→ /backend on `cranelisp-backend`): the ACTUAL bug-#2 fix + guard-flip** — new critical path. Handoff repro = the two committed guards; the smaller `launch_vec_send_corrupt` is the reduction floor. Disciplined next step (root CLAUDE.md §cross-skill handoff): shrink toward a **non-server CLIF-inspectable** repro confirming the borrowed-Var vec double-dec, timeboxed, BEFORE the fix (avoid the S97 wasted-fix trap).
- Guards stay RED; `exemplar_web` re-`#[ignore]`'d (un-ignoring injects a flaky RED); **`0492` now blocked on `0494`, not `0486`.**

**Level-1 is locked (user, 2026-07-01) on the strength of a read-only technical scout** (grounded in the runtime code, the reverted S97 attempt, and the repro). Findings that decided the fork:
- **HIGH confidence, contained-not-whack-a-mole.** Every reactor-deferred effect (launch/`race`/`select`/`timeout`/`Par`/top-level poll) funnels through **one registration chokepoint** — `await_poll_node` → `EffectPoll::new` (`crates/cranelisp-intrinsics/src/{io.rs,reactor.rs}`). Non-suspending effects need no keep-alive (they force synchronously, args live naturally).
- **Release-timing — normally the hard part — is already solved.** The reactor's exactly-once **two-path release** (`Poll::Ready` at `reactor.rs:946-951` + cancel via `ReactorInterest::drop` at `reactor.rs:751-770`), keyed on the per-leaf `reg: RegId`, is the *working, tested* permit-release discipline; the baked-arg keep-alive rides the identical key/paths. **No backend change required** — the state-closure's backend-generated drop glue already decs the args correctly; the fix only holds the closure alive across the `await` and consumes it at resolve.
- **Why S97 stalled: wrong seam, not a wall.** The reverted attempt put the registry in `alloc.rs` (the allocator has no signal for reactor-resolution) → wedged non-compiling. Trivial at the `reg`-keyed `EffectPoll` two-path; hard at the allocator. Exactly what "the boundary was never written down" predicts.
- **Remaining variable is small + internal:** net-zero-inc vs. move-out-with-sentinel (to avoid double-free against the sub-tree's own `consume_io_tree` tag-4 reclamation, `drop.rs:304-306`) — decided by an RC trace of the reduced `redA` repro. "Which of the two, not whether it works." Both are small/localized.

**Level-2 DEFERRED to the recurrence trigger** (`0486`'s own gate; not defaulted). The scout confirmed it is sprawling — ~1200-line interpreter replaced, a new backend async-codegen capability, ABI/node-layout reopened, `effect-concurrency.md §6` re-ratified — **and it still leaves the reactor as a runtime library** (does not fully collapse the boundary). One occurrence does not meet the recurrence bar; Phase H is the more natural home if it does recur.

This is the gate that unblocks `0492` (exemplar v9 adoption, blocked on bug #2).

### B. Spec/design rulings filed at S97 close (small, mostly doc-tier)

- **`0483`** (/arch) — add the "make actors + the functions between them explicit BEFORE synthesising a mechanism" principle (author + delete). The pivot's root lesson.
- **`0484`** (/design) — re-word `Connection` opacity: opaque to the **trampoline**, not the user (`poll-support.md §3.5.1`).
- **`0485`** (/spec) — bare-name module resolution: early (submodule-first) vs late (root-first) precedence inversion (`spec/08-modules.md §8.11.2`). Ties to the S97 bare-submodule-reexport fix.
- **`0487`** (/spec) — is `(select [])` "recoverable" achievable? empty-select raises at run-time but `catch-runtime-error` brackets construction (relates to the `4.2` RED).
- **`0488`** (/design) — S97 /review-flagged doc staleness, 2 spots (`ring2-rc.md §3.3`, `reactor.md §8.2`).

### C. Test-side + defect-completion drains (clear the REDs)

- **`0489`** (/qa) — two v9 test-side residuals: `2.1` reframe (invalid guard — user CAN destructure) + `5.1B` timing margin. Clears 2 REDs.
- **`0490`** (/platform) — bounded `poll-produce`/`poll-consume` fixture leaves for the v9 RC-leak guard (`2.4`). Clears 1 RED.
- **`0475`** (/int) — S97 landed the empty-`select` mechanism but the FIXME stayed open (guard owed / not deleted). Finish + `/qa` guard + close. (Coordinates with `0487`'s catchability ruling.)
- **`0479`** (/int) — S97 landed the reactor-watchdog armed-ness detector + `drive_mode` knobs but the FIXME stayed open. Verify the idle-server accept loop survives + close.
- **`0493`** (/dev, repo-wide) — retire stale `cranelisp-runtime` references (D43-split debt): CLAUDE.md skills table, `src/CLAUDE.md` dep graph, io-trampoline.md, several crate source comments, audits. Doc/comment sweep, no behaviour change.

### E. Platform-boundary consolidation (user-directed, 2026-07-01)

The shipped v9 model has exactly two functions across the platform boundary — **poll-in** (`PollFn` → `Ready`/`Pending`) and **wake-out** (the platform signals the waker). A cranelisp closure never crosses it; a continuation is the trampoline's own suspended state. User ruling: **poll-in/wake-out is the *complete* platform-effect boundary — there is no closure-callback-into-cranelisp capability, by design.** The un-invertible-C-dispatcher case (`qsort` comparator, un-invertible GUI `run()` loop) is handled one layer lower — the callback is written in the platform's own language (Rust), exposing only a poll-shaped effect; the residual "cranelisp-authored synchronous C callback" sliver is economically void (a cranelisp comparator forfeits the C library's speed).

- **`0407`** (/arch) — **DELETE.** Author the closure-boundary ruling (poll-in/wake-out complete; no closure-callback capability, *why*: keeps platforms thin, prevents the Roc platform-owned-loop degeneration) at its manifestation home (`platform-interface.md` / `effect-concurrency.md §2`), then delete the FIXME. This retires the "escape hatch, build on demand" residual — the reactor + Rust-side platform wrapping cover every real case.
- **`0419`** (/dev, cross-crate) — **DRAIN.** With `0407` deleted, `0419` collapses to a pure Principle-7 dedup: `HostCallbacks` is hand-constructed at two mirrored sites (`src/platform.rs:253` + `crates/cranelisp-exe-bundle/src/lib.rs:131`) — the DEF-6 heap-corruption window. Introduce ONE shared consumer-side builder (`/arch` decides its home + ABI surface — likely a host-side `fn host_callbacks() -> HostCallbacks` in the lowest crate that can name both intrinsic pointers); both production sites + the test mirror (`src/platform.rs:932`) call it. Makes the contract divergence-proof-by-construction. `/arch` sets the home (Phase 3); `/dev` implements.

### D. User-facing — Phase 6 (carried from S97)

- **`0491`** (/docs) — split the concurrency docs: a **user concurrency guide** (inferred half + `race`/`select`/`timeout`/`sleep` + structured cancellation, **no descriptors/tokens**) and a new **platform-writer's guide** (poll-shape leaves, produce/consume role, manifest, v9 ctx-vtable leaf-return model).
- **`0492`** (/port) — exemplar adopts the v9 ctx-vtable handle model + marquee replay. **Blocked on A (`0486`/bug-#2)** — sequences after the fix lands.
- Routine Phase-6 user-proxy assessment: `/repl`, `/stdlib`, `/examples` against what S97+S98 actually delivered; gap FIXMEs feed S99.

### Out of scope

- **Parallelism / memory-contention knot → S99**: `0459` (contention-aware spark gate — static allocation/RC-density axis) + `0408` (Sudoku perf half). Deferred deliberately per user direction — it tunes the spark gate against the substrate this sprint settles.
- **`0486` level 2** (interpreter-vs-state-machine split) — deferred unless the bug class recurs (Principle 8; named-not-defaulted).
- **Parked (Phase H / off-track):** `0050`/`0052`/`0365` (Phase-H polish), `0416` (bitwise intrinsics — feature-gated, S99 parallelism/bitmask domains), `0430` (design docstring regen — off-track). _(`0407`/`0419` moved INTO scope as band E per user direction 2026-07-01.)_
- **Opportunistic only (drain if slack):** `0460` (/qa set-doc honest-failure e2e).

## FIXME debt

| FIXME | Target skill | Status | Disposition this sprint |
|---|---|---|---|
| 0486 | /arch ✅ → runtime half **DONE** | open (residual) | **A** — invariant-15 keep-alive landed+kept (`75f286d`, net-zero-inc, unit-tested). Necessary-not-sufficient for bug #2; stays open carrying the residual → `0494`. `/design` cite-back owed (`reactor.md`/`io-trampoline.md` + "necessary-not-sufficient"). |
| 0494 | /backend ✅ **CLOSED** | **RESOLVED + deleted** (`5ca6ef2`) | **A — BUG #2 CLOSED.** Root cause was an AST-traversal gap: `find_var_type_in_expr` (`rc_emission.rs`) had no `MonoExpr::LaunchContinue` arm → `conn` (used only in the launched sub-tree) had no recorded type → the *existing* `compile_consuming_arg_list` inc (which only inc's **typed** heap Vars) skipped it, while `build_poll_state_drop_glue` dec'd unconditionally → double-free. **Fix: descend into `LaunchContinue`+`ConstrADT` in `find_var_type_in_expr`** — restores the type visibility the existing consuming-inc needs (no new mechanism, no bake-site hack; owned temporaries unchanged). Oracle silent; both guards GREEN; `exemplar_web` un-ignored+GREEN; unit test at the seam. 6 passes, 5 wasted fixes prevented by the reduce-first gate. |
| 0483 | /arch | **RESOLVED + deleted** | B — **Principle 21** authored (`principles/21-actors-and-functions-before-mechanism.md`) |
| 0484 | /design | open | B — Connection opacity wording |
| 0485 | /spec | open | B — submodule root-precedence ruling (**before** any `/int` reexport follow-up) |
| 0487 | /spec | open | B/C — empty-select catchability (→ 4.2 RED). `/arch` steer: resolution **(a) fatal-runtime-error** keeps band C code-free; (b) construction-time raise adds a `/backend compile_select` task. **Gates 0475.** |
| 0488 | /design | open | B — doc staleness, 2 spots |
| 0489 | /qa | open | C — 2.1 reframe + 5.1B timing (2 REDs) |
| 0490 | /platform | open | C — bounded poll fixture (2.4 RED) |
| 0475 | ~~/int~~ → **/backend** | open | C — finish empty-`select` raise in `io.rs` (intrinsics = backend-emitted runtime, per 0486); `/qa` guard. **Gated behind 0487.** |
| 0479 | /int | open | C — verify idle-server survival + close |
| 0493 | /dev | open | C — retire stale `cranelisp-runtime` refs (repo-wide; comment-only, `/arch`-preapproved, no baseline churn) |
| 0491 | /docs | open | D — concurrency docs split (Phase 6) |
| 0492 | /port | open | D — exemplar v9 adoption (**blocked on 0486**) |
| 0407 | /arch | open | **E** — DELETE via closure-boundary ruling (poll-in/wake-out is the complete platform-effect boundary; no closure-callback capability by design) |
| 0419 | /arch (home) → **/dev** | open | **E** — DRAIN the shared `HostCallbacks` builder dedup (2 mirrored sites → 1); 0407-prerequisite role gone, now standalone Principle-7 dedup |
| 0459 | /backend | **DEFER → S99** | parallelism axis (contention gate) |
| 0408 | /port | **DEFER → S99** | parallelism axis (Sudoku perf) |
| 0460 | /qa | opportunistic | drain if slack |
| 0430 | /design | parked | off-track (docstring regen) |
| 0416 | /arch | parked | bitwise intrinsics (feature-gated; S99 bitmask domains) |
| 0050/0052/0365 | /int·/repl·/spec | parked (Phase H) | display protocol / `/learn` / `Type.member` |

## Known RED baseline + green-flip map (QA-first Stage-1 confirmed, `/qa` `3b94a2e`)

Suite: **1795 run, 1789 passed, 6 failed, 2 skipped** (~53s, stable ×2). The 6 failures = 5 tracked S97 REDs + 1 new smaller band-A guard; 2 skips = `exemplar_web` (bug #2) + unrelated `concurrency_spark` perf bench. **Zero genuine regressions.**

| RED | Exact test | Resolved by | Flip / retire |
|---|---|---|---|
| `2.1` | `concurrency_v9_abi::connection_opaque_field_present_but_not_user_destructurable_neg` | C / `0489` (/qa) | **retire/invert** — invalid guard confirmed (destructure typechecks → exit 0) |
| `2.4` | `concurrency_v9_abi::produce_consume_descriptor_no_rc_leak` | C / `0490` (/platform) | flip once bounded `poll-produce/consume` fixture lands (`poll-pool` DLL) |
| `4.2` | `concurrency_v9_select::empty_select_caught_by_catch_runtime_error` | B / `0487` (/spec) | **(b)** → flip via `/backend compile_select`; **(a)** → **retire the row** (not a flip) |
| `5.1B` | `concurrency_fanout_web::idle_armed_server_survives_then_serves` | C / `0489`+`0479` | flip via `drive_mode`/backstop knob (detector already green) |
| `launch_grid_corrupt` | `launch_grid_corrupt::launched_strand_grid_get_assoc_does_not_corrupt_heap_neg` | A / `0486` (/backend) | flip via keep-alive fix |
| `launch_vec_send` *(new)* | `launch_vec_send_corrupt::launched_strand_two_live_vecs_send_does_not_corrupt_heap_neg` | A / `0486` (/backend) | flip via keep-alive fix (smaller repro) |
| `exemplar_web` | `exemplar_web::exemplar_web_server_serves_form_solution_and_not_found_over_http` (`#[ignore]`) | A / `0486` (/backend) | **un-ignore** + green |

**Exit definition of done:** all rows flipped **or** retired (2.1, and 4.2 under ruling (a)). `0475`/`0479` **mechanisms already GREEN** post-S97 — only `4.2` catchability (gated on `0487`) and `5.1B` knob remain of them; the FIXME table's C-band scope is narrower than it reads.

**✅ ALL RESOLVED (S98 close-of-drain).** Full suite: **1795 passed, 1 skipped (`concurrency_spark` perf bench), 0 failed.** `2.1` inverted-green, `2.4` fixture-green, `4.2` retired, `5.1B` knob-green, both bug-#2 guards (`launch_grid_corrupt` + `launch_vec_send_corrupt`) GREEN, **`exemplar_web` un-ignored + GREEN.** Zero known-defect REDs remain. Bug #2 (the 6-pass headline) closed via `0486` keep-alive + `0494` traversal fix together.

**Phase-6 finding + fix (`0499`, user-directed root-cause investigation, 2026-07-01): REPL/`--run` empty-`select` divergence — RESOLVED, `e77b71b`.** `/repl`'s assessment found `(select [])` correctly fatal under `--run` but returning unsound-null `Int 0` in the REPL (§10.12.8 violation). User asked whether this meant a regrown dual pipeline (the sketch's original sin). **Investigated + confirmed: NO — single IO driver** (`cranelisp_run_io`) **shared by both modes; the actual bug was a dual host WRAPPER** — `src/pipeline.rs::execute_compiled_expr` (REPL) hand-rolled a partial mirror of the shared C-ABI driver (`cranelisp_run_program`, FIXME 0366) that only checked the runtime-error slot BEFORE the IO drive, never after. **Fix: deleted the hand-rolled mirror; REPL now calls `cranelisp_run_program` directly** — structurally unifies error observation for ALL fatal IO errors (not just empty-select), not just this one symptom. New parity e2e (`concurrency_v9_select::empty_select_repl_run_parity_no_unsound_null`) + 5 unit tests. **Suite now 1798 pass / 1 skip / 0 fail.**

## Phase-1 decisions (resolved, user 2026-07-01)

1. **Appetite** — ✅ **full A–D drain** (everything but the parallelism axis + Phase-H/off-track parked).
2. **`0486` depth** — ✅ **Level-1 locked** (pin the contract + land the bug-#2 fix); Level-2 deferred to the recurrence trigger. Decided on the scout evidence recorded in band A.

## Architecture review (Phase 2) — SIGN-OFF (`/arch`, 2026-07-01)

- **`0486` ruling: keep-alive is RUNTIME-OWNED** at the intrinsics `EffectPoll`/`reg` seam — NOT backend-emitted (backend-emitted keep-alive would require modelling suspension points = Level-2, deferred). Grounded in `effect-concurrency.md §6` (lifetime-across-suspension is a runtime discipline) + Principles 7/18. **Contract written down** as `bounded-contexts.md §4b` **invariant 15** (+ a §3 backend-obligation-unchanged note): baked heap args of a reactor-deferred effect are live from establish (`await_poll_node`→`EffectPoll`) until resolve (Ready or cancel-drop), released exactly-once on the `reg`-keyed two-path. **No `cranelisp-types`/ABI/node-layout/`public-api.txt` change for Level-1.** **Phase-5 owner: `/backend`** (on `cranelisp-intrinsics`); move-out-with-sentinel is the arch-coherent variant (net-zero-inc alt; RC-trace-decided on `redA`). FIXME **kept open** — fix + guard-flip owed.
- **`0483`: Principle 21** ("model the actors and the functions between them before synthesising a mechanism") authored + imported across all four blocks; FIXME deleted.
- **Coherence flags** (for wave org): (1) **`0487` gates `0475`** — "recoverable" is unachievable for a runtime-empty `select` via IO-wrapping (raises at effect-run time, outside `catch-runtime-error`'s construction bracket); `/arch` steers `/spec` toward resolution **(a)** (honest fatal-runtime-error, band C stays code-free) — if **(b)** taken, add a `/backend compile_select` task. (2) **`0475`'s raise lives in `io.rs`** = backend-emitted runtime → route to `/backend`(intrinsics), not `/int` (same mis-ownership 0486 diagnoses). (3) **`0485` precedes** any `/int` bare-reexport follow-up. (4) **`0492` strictly blocked on band A.** (5) **`0493` pre-approved**, comment-only, no baseline churn. (6) `0484`/`0488`/`0489`/`0490`/`0479` clean, fully parallelizable.
- **Whole-sprint public-API/interface pre-approval: NONE required.**

## Waves (Phase 4) — provisional (finalized after Phase 3)

- **Wave 1 (critical path) — band A:** `/backend`(intrinsics) lands the `0486` Level-1 fix against invariant 15 → flips `launch_grid_corrupt`, un-quarantines `exemplar_web`; `/design`(backend) cascades the `reactor.md`/`io-trampoline.md` cite-back in the same change-set. Gates `0492`.
- **Wave 1 (parallel) — bands B/C/E spec+doc+test+dedup drains** (independent of A, serial only on shared source): `/spec` (`0485`, then `0487`→ its ruling gates `0475`), `/design` (`0484`, `0488`), `/qa` (`0489`), `/platform` (`0490`), `/dev` (`0493`), `/int` (`0479`), `/arch` (band E — `0407` closure-boundary ruling + delete; sets `0419` builder home), `/dev` (band E — `0419` shared `HostCallbacks` builder, cross-crate `src/`+`cranelisp-exe-bundle`, after `/arch` sets its home).
- **Wave 2 — 0487-gated:** `/backend`(intrinsics) `0475` raise + `/qa` guard (after `0487` resolves).
- **Wave 3 — band D Phase 6** (after Wave 1 band A is green): `/docs` (`0491` docs split), `/port` (`0492` exemplar v9 adoption + marquee replay), routine `/repl`·`/stdlib`·`/examples` assessment.

_Note: worktree isolation is broken here — only one agent edits source at a time (CLAUDE.md §Testing). "Parallel" above means logically independent; source-touching invocations serialize._

## Skill plans (Phase 3)

_Superseded by execution — this was a drain sprint; per-band skill plans lived directly in the FIXMEs + the Phase-2 `0486` ruling, not a separate Phase-3 pass. See Outcome for what each skill actually delivered._

## Waves (Phase 4)

_As executed (serial — worktree isolation broken, one source-touching agent at a time): Wave 1 band A (`/backend` intrinsics keep-alive) parallel-in-principle with bands B/C/E (`/spec`, `/design`, `/qa`, `/platform`, `/dev`, `/arch`) — all landed serially in practice. Band A's `0494` codegen investigation ran after B/C/E per user direction (de-risk the sure wins first), through 6 passes to a confirmed fix. Phase 6 (`/port`, `/docs`, `/repl`) sequenced after band A closed. See Outcome._

## Outcome (Phase 7) — PROPOSED CLOSE (awaiting user approval to archive)

**Headline:** S98 delivered the full concurrency-track + host-callback drain scoped at Phase 1, closed the sprint's namesake defect (bug #2 — a 6-pass, cross-model investigation), and completed a user-directed root-cause fix for a REPL/`--run` divergence surfaced in Phase 6. Every FIXME filed or carried into this sprint is resolved. Zero known-defect REDs remain.

### Delivered (committed + clean tree)

- **Band A — the `0486` boundary + bug #2 (the sprint's spine).** `/arch` ruled the arg-lifetime-across-suspension contract (`bounded-contexts.md §4b` invariant 15: keep-alive is runtime-owned at the `EffectPoll`/`reg` seam). `/dev`(intrinsics) landed the keep-alive (`75f286d`, net-zero-inc `StateClosure` RAII) — correct and `/review`-confirmed exactly-once, but proven (via disciplined A/B) necessary-not-sufficient. **Bug #2's actual cause**, found after 6 investigation passes each blocked by a refuted hypothesis (RC double-dec → refuted; ASAN-clean vec-COW-JIT-store → refuted by CLIF; CLIF-confirmed-correct vec codegen → led to the real site): a `/backend` AST-traversal gap (`find_var_type_in_expr`, no `LaunchContinue`/`ConstrADT` arm) starved the *existing* consuming-inc discipline of a borrowed Var's (`conn`) type, so the poll-effect drop-glue decremented it once too often — a double-free on launched-strand teardown. Fixed at the root (`5ca6ef2`); hardened by `/review`'s P8 mirror-hunt finding (`0497`: the traversal's wildcard arm converted to exhaustive, so the next `MonoExpr` variant is a compile error, not a silent UAF). `0486` closed with the Level-2 deferral (state-machine transform) recorded permanently at `effect-concurrency.md §6`, reinforced rather than triggered by this sprint's finding.
- **Band B — spec/design rulings.** `/spec`: submodule bare-name precedence (submodule-first, `0485`); empty-`select` catchability (fatal/non-catchable, generalizing to all run-time effect errors, `0487`). `/design`: `Connection` opacity re-worded (tramp-opaque, user-readable, `0484`); doc staleness fixed (`0488`); the `0486` keep-alive cite-back; later doc-tidy `0495`/`0496`.
- **Band C — RED-clearing drains.** `/dev`(intrinsics): idle-server watchdog knob (flips `5.1B`, root-caused a supervisor-exemption bug + a SIGABRT-vs-clean-exit(70) timing issue, `0479`); empty-select mechanism confirmed (`0475`). `/qa`: inverted `2.1` (Connection is user-readable), retired `4.2` (wrong premise under the `0487` ruling), confirmed `5.1B`. `/platform`: bounded `poll-produce`/`poll-consume` fixture flips `2.4` (`0490`). `/dev`: repo-wide stale-`cranelisp-runtime`-reference sweep (`0493`).
- **Band E — platform-boundary consolidation (user-directed).** `/arch` ruled poll-in/wake-out is the *complete* platform-effect boundary — no closure-callback-into-cranelisp capability, by design (manifested `effect-concurrency.md §12.1` + `platform-interface.md §3a`; deleted `0407`; caught and reconciled a stale Decision-0031 contradiction en route). `/dev` drained the resulting standalone dedup: one shared `host_callbacks()` builder in `cranelisp-intrinsics` replacing 3 hand-mirrored `HostCallbacks` construction sites (`0419`).
- **Quality gate.** Consolidated `/review` of every RC/lifetime-critical change: clean bill (no Blocker/Important), both crux items (the `0494` traversal fix, the `0486` keep-alive) confirmed sound; one P8 hardening finding actioned (`0497`).
- **Phase 6 — user-facing.** `/port`: exemplar already on v9 (from the S97 cutover); reconciled one stale comment, replayed the marquee green — the real-showcase end-to-end proof the bug-#2 fix holds (`0492`). `/docs`: split concurrency docs into a user guide (combinators only, zero descriptors/tokens) + a new platform-writer's guide (poll-in/wake-out, roles, manifest) (`0491`). `/repl`: confirmed the settled concurrency surface behaves per spec — **and surfaced a genuine defect**, `0499`: `(select [])` was fatal under `--run` but returned an unsound-null `Int 0` in the REPL (§10.12.8 violation).
- **`0499` — user-directed root-cause investigation + fix (not deferred).** User asked whether this indicated a regrown dual pipeline (the sketch's original sin). Investigated and confirmed: **no** — REPL and `--run`/`--link` share one IO driver (`cranelisp_run_io`); the bug was a narrower dual host *wrapper* — the REPL hand-rolled a partial mirror of the shared C-ABI driver (`cranelisp_run_program`) that only checked the runtime-error slot before the IO drive, never after. Fixed by deleting the hand-rolled mirror and routing the REPL through the same shared driver (`e77b71b`) — structurally unifies error observation for *all* fatal IO errors, not just this symptom. New parity e2e + 5 unit tests.
- **Doc hygiene closed out**: `0495` (reactor backstop/supervisor prose), `0496` (stale `cranelisp-runtime` refs in `/design`-owned docs), `0498` (stale exemplar_web quarantine header).

### FIXMEs resolved this sprint (19)

`0407 0419 0475 0479 0483 0484 0485 0486 0487 0488 0489 0490 0493 0494 0495 0496 0497 0498 0499` — 6 carried from S97 close (`0407 0419 0475 0479 0489 0490`; `0483 0484 0485 0487 0488` were also S97-close carries) plus `0486` (S97 carry, closed via the band-A investigation) and 6 filed + resolved within S98 itself (`0494 0495 0496 0497 0498 0499`). Net: **zero FIXMEs remain that were opened or carried by this sprint.**

### Deferred (with rationale — unchanged from Phase-1 scope)

- **Parallelism/memory-contention axis → S99**: `0459` (contention-aware spark gate) + `0408` (Sudoku perf half). Deliberately out of scope — this sprint's entire point was producing the settled substrate S99 tunes against.
- **`0486` Level-2** (interpreter-vs-state-machine split of `effect-concurrency.md §6`) — deferred to its recurrence trigger, **reinforced not triggered**: bug #2 turned out to be a plain codegen traversal gap, not a lifetime-model failure, so the reified-IO-as-data model stands.
- **Parked (Phase H / off-track, unchanged):** `0050`/`0052`/`0365`, `0416`, `0430`.
- **Opportunistic, undrawn:** `0460`.

### Known state at close

**Suite: 1798 passed, 1 skipped (`concurrency_spark` perf benchmark, feature-gated), 0 failed.** Zero known-defect REDs. `exemplar_web` un-ignored and green (both tests). Working tree clean (only pre-existing unrelated untracked cruft: `scratch_other.diff`, `test1/` — not part of this sprint).

### Findings (durable lessons)

- **The reduce-first/confirm-first gate paid for itself many times over.** Bug #2 took 6 investigation passes; the gate prevented at least 3 wasted fixes (vec-RC hypothesis, ASAN-implied vec-COW-JIT-store hypothesis, and would have prevented shipping the false-green move-out-sentinel variant that hangs the server instead of crashing it). The final fix was a genuine root cause, not a symptom patch.
- **Cross-model divergence is informative even when one line is wrong.** The analytical (read-only) cross-check on bug #2 diverged from the empirical instrumentation pass — it wrongly named the untracked vec buffer instead of the tracked `conn` ADT — but it correctly identified the mechanism CLASS (a stray write/dec into freed memory) and its "why 5 passes failed" reasoning (heavyweight sanitizers perturb layout-sensitive bugs away) was exactly right and reusable.
- **P8 mirror-hunting on a fix, not just the diff, catches the root enabler.** `/review`'s finding on `0494` (`0497`) wasn't a new bug — it was noticing the wildcard-match pattern that let the ORIGINAL bug ship silently, and closing that structurally (compile error, not runtime UAF) for the next variant.
- **User-directed root-cause investigation over methodology-default deferral.** `0499` would have defaulted to an S99 carry per Phase-6 convention; the user's insistence on understanding "is this a regrown dual pipeline" before accepting any fix path caught the correct, narrower framing (dual wrapper, not dual driver) and produced a structural fix in the same sprint rather than a symptom patch scheduled for later.
- **Agent-liveness judgment from transcript files is unreliable.** Twice this sprint a transcript's byte-count/idle-time was read as a stall signal; the first time genuinely working. The transcript file appears to buffer until completion. Live-process activity (build/test processes, listening sockets) and the completion notification are the trustworthy signals — this is a durable operational lesson for future sprints. [See memory candidate below.]

### Close plan

1. ✅ All FIXMEs resolved; suite green; tree clean.
2. **On user approval:** `git mv sprints/SPRINT.md sprints/archive/sprint-98.md`; update `sprints/ROADMAP.md` (S98 closed → **S99 = parallelism/memory-contention axis** next); commit.
3. **Arch-principles check (Phase 7 prompt):** Principle 21 (actors-first, authored this sprint) served the band-E closure-boundary ruling well. No new principle proposed from this sprint's findings — the reduce-first-gate discipline and the transcript-liveness lesson are operational/memory items, not architectural principles.
