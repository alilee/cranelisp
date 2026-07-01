# Sprint 98: Concurrency-track drain + the trampoline boundary defect — clear the slate before the parallelism axis

**Status**: PHASE 5 LANGUAGE (ACTIVE) — **Stage 1 QA-first** (sprint-wide RED baseline). Scope user-approved (full A–E drain; `0486` **Level-1 locked**). Phase-2 `/arch`: **SIGN-OFF**, no public-API impact. **Phase 3/4 compressed** (drain sprint — per-band design lives in the FIXMEs + the Phase-2 `0486` ruling; waves finalized as drafted below). `/qa` issued for the failing-not-ignored baseline.

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

**QA-first Stage-1 refinement (2026-07-01, `/qa`): the `redA` "pure-String UAF" hypothesis is REFUTED (measured, 8 trials each).** Churned-`Response.body` String does NOT reproduce (0/8); a single live vec does NOT (0/8). The load-bearing floor is a **borrowed-Var `(Vec …)` with TWO vecs both live** across the launched `send-conn` (8/8). New smaller deterministic guard committed: `tests/launch_vec_send_corrupt.rs::launched_strand_two_live_vecs_send_does_not_corrupt_heap_neg` (RED) — drops the `Cell`/`Grid` ADT wrappers. **This retargets `/backend`'s fix from a pure-String path toward the borrowed-Var vec RC path on the launched strand** — the keep-alive contract (invariant 15) is unchanged, but the reduction says the failing hold is the borrowed vec, not the marshaled `Response`.

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
| 0486 | /arch ✅ → **/backend** | open (fix owed) | **A (spine)** — Phase-2 ruling landed: keep-alive **runtime-owned** at `EffectPoll`/`reg` seam, contract = BC §4b **invariant 15**, no interface/ABI/public-API change. Phase-5 `/backend` (on `cranelisp-intrinsics`) lands the fix (`io.rs`/`reactor.rs`/`drop.rs`; move-out-sentinel vs net-zero-inc = RC-trace on `redA`), flips `launch_grid_corrupt`, un-quarantines `exemplar_web`; `/design` cascades `reactor.md`/`io-trampoline.md` cite-back **with** the fix. |
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

_Pending Phase 2._

## Waves (Phase 4)

_Pending Phase 3. Provisional shape: `0486` /arch ruling gates band A's fix + `0492`; bands B/C are largely independent doc/spec/test drains that parallelize (serial only where they touch shared source); band D Phase-6 sequences last._
