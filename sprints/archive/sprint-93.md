# Sprint 93: Reactor Gate — Race Stabilisation + Slice-2 Async Substrate Begins

**Status**: COMPLETE

**Goal**: Stabilise the compiler-internal H6/H7 race into a deterministic repro and structurally fix it (the reactor's clean noise floor), then begin Slice-2 of the effect-concurrency track — the async trampoline over a host-owned reactor — on top of it.

## Scope

S93 enters the **effect-concurrency track's Slice 2** (the async tramp/reactor) behind a hard gate. The slice-2 reactor implementation does not begin until the compiler-internal race repro is green — settle the substrate, then build on it (the same logic that puts the whole track before Phase H). User direction (S93 planning): **gate + begin reactor impl, same sprint.**

**1. Race stabilisation — the reactor gate (FIXME 0425 item 1 + 0426).** Reframed per roadmap §"Compiler-internal concurrency race": 0425 is NOT optional cleanup — it is an **unisolated recurring test-suite failure**, the H6/H7 import/typecheck-pipeline race (`'helper-val' not found in module 'helper'`), firing ~5–10% under contention and **worsening as the track adds CPU-parallel work** (S92 slice-1 load surfaced it ~1/14 full runs). Shape (isolate-then-fix):
   - (a) `/qa` isolates the race into a deterministic / stress repro (loom / structured-interleaving — `design/int/heisenbug-race-closure.md` §7.10/§8.3, `tests/repl_persist_race.rs`, `tests/plan/ledger.md:2118`). Turns "unisolated" into a pinned failing test.
   - (b) **Structural fix — the signature/body pre-pass** (register all module signatures before any body typechecks; subsumes 0426's mutual-import deadlock) OR the equivalent dependency-service subsystem extraction. Make the publish/readiness/block/resume invariant **structural, not convention**. **(arch R1) The tactical `eval_in_flight` convention-flag (heisenbug §8.2) MUST NOT be landed as the gate** — Principle 8 (no interim structure). **(arch R2) Gate scope = 0425 item 1 ONLY**; items 2–4 (`SharedState` field-ownership sweep, `cached_modules` dual-store, priority/nice worker unify) are non-gating, drain-if-time. **(arch R3) 0426 is evaluated in the SAME design pass**, not bolted on later — its resolution mandates this.
   - (c) Race fix is **internal to the `src/` int surface** — no cross-crate interface impact; `/dev` (int) proceeds in parallel with the arch-led ABI design.
   - **Gate (behavioural)**: the isolated repro is deterministically green and stays green under contention, **achieved via the structural fix** — before slice-2 reactor implementation begins.

**2. Slice-2 async substrate begins (effect-concurrency track, slice 2) — strict internal order (arch R4).** Within "begin slice 2," the ordering is non-negotiable: **(i) design ABI-v4 + HostCtx C-ABI → (ii) land the interface types in `cranelisp-types`/`cranelisp-platform` → (iii) THEN reactor impl.** The host-reactor C-ABI (`HostCtx` vtable + C-ABI waker) is the one genuinely new designed artifact — writing reactor code before it lands is interim code against an unsettled boundary (Principle 8). Steps (i)+(ii) **are** the load-bearing "begin slice 2" deliverable. Step (iii) — minimal host-reactor + one async-leaf effect + observability (strand-correlated event stream) — is **feature-gated (byte-identical-when-off) and cleanly spillable to S94**. Acceptance target if reached: **two slow reads overlap on the reactor, no thread-per-read; strand trace visible.**

**3. Slice-2 design groundwork (cascade prerequisites for slices ≥ 2).** Flagged in `effect-concurrency.md`, actioned by `/arch` in Phase 3:
   - `platform-interface.md` ABI cascade — **(arch R5) numeric `ABI_VERSION` 6→7** (NOT the doc-label "v3→v4"): poll-shape GOT effect fns, descriptor in manifest, host-reactor C-ABI.
   - **ConcurrencyDescriptor `#[repr(C)]` layout reserved in FULL this sprint, incl. the inert budget field (arch R5/§6)** — semantically inert until slice 4, but present now to avoid a second ABI bump (7→8). 0442 (budget *abstraction*) stays a slice-4 decision.
   - spec §10.12 / §12 — `/arch` **files a FIXME `target:/spec`**; does not author spec.
   - `bounded-contexts.md` §3/§5/§6 — manifest only what slice-2 delivers.
   - a `sequences/` concurrency-scheduler diagram (+ reconcile `concurrency-dependency-service.mmd` to the as-built pre-pass).
   - **(arch R6) The candidate principle "confine mutable-state concurrency to the interpreter" is added at Phase 7 (close), NOT Phase 3** — principles change only at sprint close.

**4. FIXME drain — near-term actionables** (your "clear unless future-phase"): 0410, 0423, 0430, 0433, 0434, 0440, 0446; decide 0424(ii)/0445 (par-map primitive vs. reserve names). See FIXME debt table.

### Out of scope (deferred — future phase = Phase H)

- **0050** (List/Seq pretty-printer / display protocol) — Phase H opener.
- **0052** (`/learn` in-REPL tutorial) — Phase H opener.
- **0365** (`Type.member` accessor qualification) — Phase H opener.
- **0408** (Sudoku parallel-search perf showcase) — needs the `--release` backend (Phase H); expr-half already shipped S92.
- **0416** (bitwise intrinsics) — feature-gated, deferred.
- **0407 / 0419** (platform closure-callback Model B + shared HostCallbacks builder) — reframed as an escape hatch, explicitly NOT on the concurrency path; deferred capability.
- **0442** (unified CPU+IO budget abstraction) — a slice-4 backpressure design decision; not slice-2.

## FIXME debt

| FIXME | Target skill | Disposition | Notes |
|---|---|---|---|
| 0425 | /arch | **RESOLVE (gate)** | item 1 = signature/body pre-pass (race); design done; /dev Phase 5 |
| 0426 | /arch | **RESOLVE (gate)** | D0030 → cycle-error (coarse reading, user ruling); subsumed by pre-pass |
| 0449 | /arch | **RESOLVE (Phase-5 setup)** | `--features concurrency` test lane so ABI-v7 guards run (filed Phase 3) |
| 0410 | /repl | drain | Cranelisp.toml scaffold on project root |
| 0423 | /int (src/) | ✅ RESOLVED on HEAD (W1) | regen path + `:Type` spacing already landed; QA repros pass — close FIXME |
| 0430 | /design | drain | Docstring-into-source regen increment |
| 0434 | /qa | ✅ RESOLVED on HEAD (W1) | 4-position sweep passes; +Neg guards added — close FIXME |
| 0440 | /design | drain | int listing surface — unify 3 category-bucketing sites into one classifier |
| 0446 | /repl | drain | Env knobs (`CRANELISP_SPARK_BUDGET`, `CRANELISP_NO_LENIENT`) normative CLI home |
| 0424 | /arch+/stdlib | TRACK (not S93) | par-map/par-reduce are STDLIB fns (user ruling); gated on 0424(i) sparking generalization |
| 0433 | /spec | ✅ RESOLVED (Phase 3) | literal patterns NOT a feature; §6.6.2 pinned; /qa owes rejection test |
| 0445 | /arch | ✅ RESOLVED (Phase 3) | folded into 0424 — stdlib provides par-* (user ruling) |
| 0448 | /arch | ✅ RESOLVED (Phase 3) | mutual imports = cycle-error; fine reading rejected |
| 0450 | /design | ✅ RESOLVED (Phase 3) | doc reconcile of the 0448 ruling |
| 0447 | /spec | DEFER (slice-surface) | async-leaf/reactor user semantics — spec at the slice they surface |
| 0050 | /int | DEFER (Phase H) | Display protocol |
| 0052 | /repl | DEFER (Phase H) | `/learn` tutorial |
| 0365 | /spec | DEFER (Phase H) | `Type.member` accessor qualification |
| 0407 | /arch | DEFER | Host-callback Model B — escape hatch, off track |
| 0408 | /port | DEFER (Phase H) | Sudoku perf — needs `--release` |
| 0416 | /arch | DEFER | Bitwise intrinsics — feature-gated |
| 0419 | /arch | DEFER | Shared HostCallbacks builder — tied to 0407 |
| 0442 | /arch | DEFER (slice 4) | Unified CPU+IO budget — backpressure design |

## Architecture review (Phase 2)

**Verdict: SIGN-OFF WITH REVISIONS** (`/arch`, 2026-06-27). Gate-then-build sequencing affirmed; the 0425 reframe (debt → unisolated recurring failure) is correct. Six required revisions folded into Scope above (tagged arch R1–R6). Race fix is internal to `src/` (no cross-crate impact); the ABI-v4 design is the load-bearing slice-2 work.

### New / changed cross-crate interfaces (ABI v4 = numeric `ABI_VERSION` 6→7)

| Interface | Home | Disposition |
|---|---|---|
| **ConcurrencyDescriptor** (token/cardinality/global-budget/blocking; generalizes `SchedulingClass`) | `cranelisp-types` | land this sprint — **FULL `#[repr(C)]` layout incl. inert budget field**; not `#[non_exhaustive]` |
| **Poll-ABI primitives** (`Poll` repr; `poll(state, *HostCtx, *Waker) -> Poll`) | `cranelisp-types` | land this sprint |
| **HostCtx vtable + C-ABI waker** (`register_readable`/`writable`/`timer` + waker) | `cranelisp-platform` (alongside `HostCallbacks`) | design this sprint; land layout; host impl follows — *the new load-bearing artifact* |
| **PlatformFn manifest** — add descriptor field, effect-fn→poll-shape, retire `jit_name` | `cranelisp-platform` (`#[repr(C)]`) | design + layout this sprint; `ABI_VERSION` 6→7 |
| **Strand-id correlation newtype** | `cranelisp-intrinsics` (with `IoObserver`) | land the newtype this sprint (expensive to retrofit; §11) |
| **Observability event enum** | `cranelisp-intrinsics` | stage — accrue kinds per slice |
| Race-fix coordination (pre-pass / `ModuleState`) | `src/` (int) | internal — no cross-crate impact, no arch interface-gating |

### Ranked deliverables + spill line (arch §5)

1. **Race repro deterministically green** (gate — non-negotiable).
2. **ABI-v4 + HostCtx C-ABI design + interface types landed** (the real "begin slice 2").
3. *(stretch, feature-gated, spillable to S94)* minimal host-reactor + one async-leaf effect demo.
4. FIXME drain (independent surface work; first to shed if the race runs long).

### Risk flags
- **Interim (P8):** tactical race-flag as gate; reactor code before HostCtx lands — both mitigated by R1 + R4.
- **Scope (P6):** full pre-pass + ABI-v4 + types + reactor impl is over-budget — mitigated by the rank+spill line and the gate narrowed to 0425 item 1.
- **ABI churn:** omitting the inert budget field forces a second bump (7→8) at slice 4 — reserve the slot now.

## Skill plans (Phase 3)

Phase-3 design is complete. The implementable plans:

### /qa (Phase-5 Stage 1 — sprint-wide failing tests)
- **Task**: write all failing-not-ignored tests per `tests/plan/sprint-93.md` — the race gate (deterministic `src/scheduler.rs` interleaving pin via `P_publish`/`P_read`, loom variant, the `repl_persist_race.rs` contention guard, the D0030 cycle-error e2e), the 6 ABI-v7 dormant-contract guards, the literal-pattern rejection test (0433 owed), and the 0423 + 0434 repros.
- **Design refs**: `tests/plan/sprint-93.md`, `design/int/signature-body-prepass.md` §6.
- **Acceptance**: all in-scope tests present + RED (race repro RED pre-fix); 0434 sweep verify-on-HEAD.

### /design + /dev (src/ int) — the gate
- **Task**: implement the signature/body pre-pass (Invariants PP+SW) per `design/int/signature-body-prepass.md` §7 (7 ordered steps, each with its unit-test seam). Net-neutral/subtractive (retire the per-symbol wait/notify + `eval_owned`/`eval_in_flight` family). 0425 item 1 + 0426 only; items 2–4 non-gating.
- **Acceptance** (the GATE): the deterministic race repro is green + green under contention; D0030 yields a cycle-error not a hang; full suite no RED beyond known guards.

### /arch — Phase-5 setup + reactor design
- **Task**: resolve FIXME 0449 (`--features concurrency` test lane). Stand ready for the reactor stretch's residual design Q (host-runtime feature topology).

### /dev (reactor stretch — feature-gated, SPILLABLE to S94)
- **Task**: minimal host-reactor + one async-leaf effect + trampoline `async fn` + strand-event hooks, behind the off-by-default `concurrency` feature (byte-identical-when-off). Per `platform-interface.md` §6.8 wiring list.
- **Acceptance**: two slow reads overlap on the reactor, no thread-per-read; strand trace visible. **First to spill if the gate runs long.**

### FIXME drain (independent surfaces)
- 0423 (/int src/), 0410 + 0446 (/repl), 0430 + 0440 (/design), 0434 (/qa, in Stage 1).

## Waves (Phase 4)

Source-touching work runs **serially** (worktree isolation broken — one editor at a time). Waves express dependency order; the gate is the hard barrier before the reactor.

### Wave 0 — Phase-5 setup
| Skill | Surface | Task | Status |
|---|---|---|---|
| /arch | crates/tests | Resolve 0449 — `--features concurrency` test lane | ✅ done — `cargo nt-concurrency` alias; 0449 deleted; 1648+325 green |

### Wave 1 — QA-first (Stage 1): all failing tests sprint-wide
| Skill | Surface | Task | Status |
|---|---|---|---|
| /qa | tests/ | Race gate repros + ABI-v7 guards + literal-pattern + 0423/0434 | ✅ done — 1 RED gate pin (mutual-import cycle-error, no-hang); 5 ABI-v7 guards GREEN (lane 330/330); 8 coverage e2e GREEN. **0423 + 0434 already resolved on HEAD** (drained). Scheduler-internal unit pins deferred to /dev Wave 2 (seam doesn't exist yet) |

### Wave 2 — THE GATE (src/ int) · blocks Wave 3
| Skill | Surface | Task | Status |
|---|---|---|---|
| /dev | src/ | Implement pre-pass (§7 steps 1–7) | ⚠️ **PARTIAL** — substrate (dependency_closure+cycle-error, signatures_ready, register/await barrier, single-writer claim) + deterministic P_publish/P_read pin LANDED & tested; D0030 **live** (mutual-import RED→GREEN). **Steps 4–5 DEFERRED → FIXME 0450 (/arch):** live body-barrier wiring + `eval_owned` retirement need an arch worker-pool decision (parking vs S78 free-back-to-pool). Suite 1671/1671, lane 330/330. |
| /dev (2b) | src/ | Live body-barrier requeue gate + `eval_owned` retirement (§7 steps 4–5) | ✅ done — 0450 ruling B (requeue gate); `eval_owned` retired structurally (Invariant SW); live body gated on barrier (PP). Suite 1675/1675, lane 330/330, contention guard **10/10 deterministic**, deadlock-free @1/2/4 workers |
| /review | src/ | Review the gate change-set (P6/P7/P8) | ✅ done — core sound (cycle gate, eval barrier, B1 closure, pin all correct). **1 BLOCKER:** worker-path requeue gate `gate_body_on_signature_barrier` (dependency.rs:288–294) is check-then-act across 2 locks → latent lost-wakeup deadlock. 3 Important: `signatures_ready` live-redundant (= the missed 0452 subtraction); per-retry closure re-parse; BC §6 says TypecheckWorking but as-built = TypecheckDone. → /dev Wave-2c |
| /dev (2c) | src/ | Fix the BLOCKER (atomic find-and-block) + closure caching + 0452 subtraction per /arch | ✅ done — atomic `block_on_first_unready_closure_member` (Blocker fixed; 256-iter interleaving pin); `signatures_ready` machinery removed (net −14); closure memoised per cluster. Suite 1676/1676, lane 330/330, contention ×5 + deadlock-free @1/2/4 |
| **gate** | — | **Race repro deterministically green + green-under-contention → reactor may begin** | ✅ **FULLY ACCEPTED (W2a+b+c) — live H6/H7 race structurally closed; worker path deadlock-free BY CONSTRUCTION (atomic check-and-block, Blocker fixed); D0030 = cycle-error; `eval_owned` retired (Invariant SW); barrier reads pool-terminal state. /review Blocker + Importants all resolved; 0452 ruled (net-additive accepted, subtraction taken). Reactor (W3) UNBLOCKED.** |

### Wave 3 — reactor stretch (feature-gated, spillable to S94) · after gate
| Skill | Surface | Task | Status |
|---|---|---|---|
| /arch | crates + src/ | Reactor scoping decision | ✅ done — substrate **mio+futures** (not tokio; HostCtx is mio-shaped); reactor lives in **cranelisp-intrinsics** (not src/ — must link into `--link`); 2 features (`concurrency` + `concurrency-runtime`); 1 await boundary; `async-read` demo leaf via fixture poll-fn. Plan in effect-concurrency.md Appendix B. 0425/0426 deleted; filed /design 0454 |
| /dev | cranelisp-intrinsics | Minimal host-reactor (mio HostCtx) + async trampoline twin + `async-read` demo leaf + strand hooks, behind `concurrency-runtime` | in-progress |
| /dev | cranelisp-intrinsics | Minimal host-reactor + async trampoline twin + `async-read` demo leaf + strand hooks, behind `concurrency-runtime` | ✅ done — mio HostCtx reactor + C-ABI waker + block_on executor + EffectPoll await + strand sink; **2 async-reads overlap ≈max(100,200)ms on ONE thread**, strand trace interleaved; default 1676/1676 byte-identical-off, `--link` links no executor. New lane `cargo nt-concurrency-runtime` (3 green) |
| /review | cranelisp-intrinsics | Review reactor change-set | ✅ done — accept-with-1-Blocker; waker projection + executor verified SOUND, byte-identical-off + overlap proof genuine. **B1 (Blocker):** host handle derived from `&Reactor` → Stacked-Borrows UB (1-line provenance fix). 3 Important: lost-wakeup latch, missing SAFETY notes, P7 bookend mirror. → /dev 3b |
| /dev (3b) | cranelisp-intrinsics | Fix B1 + I1 + I2 + I3 + M1/M3 | ✅ done — B1 host-provenance UB fixed (raw `*mut`, SAFETY invariants); I2 lost-wakeup fixed (re-register every Pending + double-Pending guard test); I1/I3/M1/M3 done. nt 1676/1676, nt-concurrency 330/330, nt-concurrency-runtime 171/171 |
| **reactor** | — | **Slice-2 spine ACCEPTED — 2 reads overlap on 1 reactor thread, strand trace visible, byte-identical-off, sound (B1 closed), lost-wakeup-free (I2 closed)** | ✅ |

### Wave 4 — FIXME drain (parallel surfaces, serialized execution) · independent of gate
| Skill | Surface | Task | Status |
|---|---|---|---|
| /dev | src/ | 0423 — source-regen path + annotation spacing | ✅ resolved on HEAD (W1) |
| /repl | repl/ | 0410 (Cranelisp.toml scaffold) + 0446 (env-knob CLI home) | ✅ done — 0410 already shipped S91 (deleted); 0446 → `repl/spec.md §0.7` + /docs 0456 |
| /dev | src/ | 0440 (listing classifier) + 0430 (docstring-into-source) | ✅ 0440 resolved (4 sites unified, 1677 green); 0430 deferred→S94 (design fork) |
| /docs | user/ | 0456 (cli-reference env-knobs) | ✅ done — cross-linked §0.7, caveat dropped; no other user-doc affected |
| /platform | cranelisp-platform | Phase-6 v7 protocol assessment | ✅ done — authoring unchanged (v7 dormant); rustdoc note added |
| /arch+/qa | — | bookkeeping 0455 (App-B caveat), 0434 (delete) | ✅ done — both deleted; final suite GREEN (1677/330/171) |

## Notes

- 2026-06-27 — Phase 1 scope draft. User direction: clear FIXMEs unless future-phase; get into the concurrent tramp/reactor; gate + begin reactor impl in the same sprint.
- 2026-06-27 — Phase 3 design spine landed (ABI-v7 dormant contracts, race-fix pre-pass design, QA test plan, spec hooks). FIXMEs resolved/deleted: 0433 (literal patterns not a feature), 0445 (superseded by ruling below). Deferred: 0447 (spec, slice-surface). Filed: 0447, 0448, 0449.
- 2026-06-27 — **User rulings (Phase-3 review):**
  - **(R-a) `par-map`/`par-reduce` are STDLIB functions, not a language primitive.** Keeps /arch's "no primitive" half; REVERSES the "/stdlib holds" half — /stdlib provides them (over the inferred apply-arg sparking substrate). /arch to adjust effect-concurrency.md §7 verdict + the 0424 annotation; /stdlib owns the implementation (scope TBD — likely a near-term /stdlib item gated on 0424(i)'s full-independence generalization, not necessarily S93).
  - **(R-b) Mutual imports are an ERROR.** Resolves FIXME 0448 — the COARSE reading: deadlock → clean cycle-error, src/-only. The fine reading (compile mutual imports, cross-crate typecheck Pass-1 entry) is REJECTED, not deferred. /arch to close 0448 + update signature-body-prepass.md §4 / BC §6 / the .mmd Note to state mutual-import = cycle-error definitively.
  - **(R-c) SVG regen:** RESOLVED — both `concurrency-{dependency-service,scheduler}.svg` rendered (root cause was a mermaid syntax error: `;` is a statement separator, `()` breaks titles; /arch sanitized + regenerated). Render recipe saved to memory. Disk was 100% full (target/=14 GB) — user freed it; Phase 5 builds unblocked.
- 2026-06-27 — **Phase 4 (wave org) complete.** par-map TRACKED (not S93) per user. Waves written; gate (Wave 2) is the hard barrier before the reactor (Wave 3, spillable). Status → PHASE 5 LANGUAGE (ACTIVE).
- 2026-06-27 — **Phase 5 SUBSTANCE COMPLETE.** Gate fully closed (race structurally gone, deadlock-free, all /review findings resolved). ABI-v7 contracts dormant + lane. Reactor slice-2 spine ACCEPTED (overlap demo, sound, lost-wakeup-free, all /review findings fixed). Doc currency done (0453/0454; reactor.md authored). FIXMEs cleared this sprint: 0423, 0425, 0426, 0433, 0434(HEAD), 0445, 0448, 0450, 0451, 0452, 0453, 0454. **Remaining near-term drains (not future-phase):** 0410, 0430, 0440, 0446 + bookkeeping 0455 (/arch App-B caveat), 0434 (/qa delete). Deferred future-phase: 0050, 0052, 0365, 0407, 0408, 0416, 0419, 0424, 0442, 0447.

## Outcome (Phase 7)

**Pre-close gate GREEN:** default `cargo nextest run` **1677/1677** · `cargo nt-concurrency` **330/330** · `cargo nt-concurrency-runtime` **171/171**. Zero RED, zero `#[ignore]` on S93 in-scope features. The former 14 S81 intentional failing-repro guards are all resolved.

### Delivered
- **The race gate (FIXME 0425 item 1 + 0426) — the headline.** The H6/H7 import/typecheck race is **structurally closed** in the live compiler via the signature/body pre-pass barrier (Invariant PP) + single-writer exclusive claim (Invariant SW, retiring `eval_owned`). Deadlock-free **by construction** (free-back-to-pool requeue gate, not thread-park; atomic single-lock check-and-block). D0030 mutual-imports now give a clean compile-time cycle-error. The long H4→H7 tactical lineage is addressed at the root (convention → structure). Pinned by a deterministic P_publish/P_read interleaving test + a 256-iteration atomic-block guard + the contention guard deterministic under load. Two `/review` rounds; all Blocker+Important findings resolved.
- **Effect-concurrency Slice 2 — the reactor spine.** ABI-v7 layout contracts landed dormant (`ConcurrencyDescriptor`/`Poll`/`PollFn`, `HostCtx`/`Waker`/`ConcurrentPlatformFn`, `StrandId`/`StrandEvent`; `ABI_VERSION` 6→7), behind off-by-default `concurrency`. A minimal **mio host-reactor + C-ABI waker + async trampoline twin + `EffectPoll` await + strand sink** (behind `concurrency-runtime`): **two slow reads overlap on one reactor thread** (≈max not sum, no thread-per-read), strand trace visible. Unsafe-soundness reviewed — provenance-UB Blocker + lost-wakeup both fixed. Byte-identical-when-off; `--link` links no executor. New test lanes `cargo nt-concurrency` + `cargo nt-concurrency-runtime`.
- **FIXME drain (the sprint's other goal — "clear unless future-phase").** Resolved: **0423, 0425, 0426, 0433, 0434, 0440, 0445, 0448, 0450, 0451, 0452, 0453, 0454, 0455, 0456** + 0410/0446 (repl). par-map ruled stdlib-not-primitive (0424/0445); mutual-imports ruled cycle-error (0448). **Zero open-actionable FIXMEs remain.**
- **User-facing assessment (Phase 6).** `/platform`: authoring unchanged (v7 dormant; 6→7 invisible — all platforms are workspace members) + rustdoc note. `/docs`: env-knobs cross-linked in `cli-reference`; no other `user/` doc affected (reactor has no user surface, per spec ruling). `/repl`: env-knobs normative home (`repl/spec.md §0.7`) + `Cranelisp.toml` scaffold confirmed shipped. Spec kept free of new user surface (§10.12.6 informative only; 0447 deferred).
- **Design currency.** `bounded-contexts.md` §3/§5/§6, `platform-interface.md` §6.8, `effect-concurrency.md` §7/§13/App-B, new `design/int/reactor.md` + `signature-body-prepass.md`, `concurrency-scheduler.mmd` (new) + `concurrency-dependency-service.mmd` (reconciled), both SVGs regenerated.

### Deferred (with rationale)
- **Reactor wiring through `cranelisp_run_io` for real effect nodes** — the async twin currently delegates the node walk to the sync stepper; the `EffectPoll` await is exercised only by the fixture demo leaf. Real poll-shape effect nodes need backend poll-emission (`declare_platform!` + GOT dispatch arm) — a later slice. As-built caveat recorded (App-B + `reactor.md §4`). This was the explicit spillable scope; the spine landed, the spill item is the real-node wiring.
- **0430** (docstring-into-source regen) → **S94** — genuine design fork (renderer-contract change; depends on the `set-doc` surface descoped S89). Deferred with recommended candidate 1 + open `/design` question.
- **0424** (par-map stdlib functions) → **S94** — ruled stdlib (not primitive); depends on 0424(i) sparking generalization; tracked, not pulled into this gate+reactor sprint.
- **Future-phase (Phase H / later slices), correctly parked:** 0050, 0052, 0365 (Phase H); 0407, 0416, 0419 (host-callback/feature-gated); 0442 (slice-4 budget); 0447 (spec async-leaf, surfaces with its slice).

### Findings (methodology / observations)
- **`/review` earns its keep on concurrency work.** Two genuine defects caught only by reading the lock/provenance discipline (a latent gate deadlock; a Stacked-Borrows provenance UB) — both invisible to a green suite, both in the exact class the code claimed to eliminate "by construction." Adversarial review, not test-passing, was the safety net.
- **Design *projections* can be wrong even when the design is right.** The "net-neutral LOC" mandate (signature-body-prepass §5) was an incorrect projection — the requeue kernel is reused and structural enforcement (P18) costs more than a convention flag. `/arch` accepted net-additive as the correct floor; the one real subtraction (`signatures_ready`) was found by `/review`, not the design.
- **Honest spill > forced completion.** The reactor's real-node wiring and 0430 were deferred with rationale rather than half-shipped; the gate's live-integration was *not* deferred (Path A) precisely because a partial gate defeats its noise-floor purpose. Knowing which to push and which to spill was the judgment call.
- **Environment friction:** SVG render toolchain (aarch64 + snap-chromium + mermaid `;`/`()` syntax) and a 100%-full disk surfaced mid-sprint; both resolved, render recipe saved to memory.
