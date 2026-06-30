# Sprint 96: Effect-concurrency — platform-model completion + the server demo

**Status**: ✅ **S96 CLOSED (2026-06-30).** All deliverables shipped + validated + documented; Phase 6 (5-skill) + Phase 7 complete. Suite **1766 run / 1763 passed / 3 known-defect-RED guards / 1 skip — ZERO regressions** (the 3 reds: 0476 constructor-as-value→/backend, race+inline-bind-lambda→/backend, bare-submodule-reexport→/int — all failing-not-ignored, each with a `// FIXME(/owner)` resolver). Committed to main (not pushed). Carried-forward FIXMEs (forward cross-skill, none blocking): 0469/0471/0474/0475/0478/0479 (S96) + older.
- 2026-06-30 — **Phase 6 /examples: added `examples/32-concurrency-combinators.cl`** (the explicit-control peer to 28/30's inferred half) — free-standing (no stdlib; `timeout` written inline as `race work (sleep-sentinel)`), teaches sleep/race/select + the timeout pattern, 6 sub-tests → exit 6, deterministic 5×, ~0.32s. Plan doc + `tests/examples.rs` runner updated (suite stays green). **NEW DEFECT found (S96-relevant, → consolidated /qa repro, resolver /backend):** `race` with an INLINE `bind`-lambda argument miscompiles under default lenient eval — `codegen error … lambda __lambda_main__… signature {2 params} incompatible with previous {1 param}` (apply-argument-sparking vs combinator-argument lambda-name collision); `CRANELISP_NO_LENIENT=1` compiles+runs clean (exit 111); **`select` UNAFFECTED — `race`-specific**; named-helper branches sidestep it (the example uses named helpers, transparently noted — not a silent workaround). Minimal repro: `(race (bind (Pure 0) (fn [_] (Pure 111))) (Pure 222))`. Workaround exists so not S96-blocking, but it's a real limitation of the shipped `race` combinator. Full suite **1763 passed / 1 skip / 1 expected fail (0476)**.
- 2026-06-30 — **Phase 6 /docs: concurrency model documented — PHASE 6 COMPLETE.** New `user/guide/concurrency.md` (the two-halves thesis: inferred "concurrency written by nobody" via launch-and-continue + the direct-leaf discipline, with the server-with-no-`spawn` exemplar excerpt; explicit `sleep`/`race`/`select`/`timeout` with a signature table; structured cancellation as a consequence + the 3 reference patterns). Edited `user/getting-started.md` (capacity-scoped the concurrency bullet + cross-links) + `user/CLAUDE.md` (doc-set row). **Every snippet RUN-validated** before inclusion (race→111, select→7, inline-timeout→99, sleep→42, stdlib timeout→None/Some, cancellation→"EARLY" only LATE-absent); all use named-helper branches + no bare-constructor-as-value (sidestep 0476/0475/race-inline-bind). **Honest-scope documented:** timeout=stdlib-not-primitive; idle-server ~30s limit (0479); per-resource capacity N (0462); the 3 rough edges named. **FIXME 0462 RESOLVED+deleted** (all 3 asks met). No new defects. **PHASE 6 COMPLETE: /port ✓ /stdlib ✓ /repl ✓ /examples ✓ /docs ✓.**
- 2026-06-30 — **Consolidated /qa repro pass DONE + Phase 7 close triage.** Two Phase-6 defects guarded failing-not-ignored: (1) **`regression::race_with_inline_bind_lambda_branch_compiles_under_lenient`** (→/backend) — `(race (bind (Pure 0) (fn [_] (Pure 111))) (Pure 222))` codegen-errors (lambda-name collision `{2 params} vs {1}` under lenient apply-arg sparking); FAILS (got 1); `select` unaffected; `// spec: §10.12.8`. (2) **`spec_08_modules::bare_relative_submodule_reexport_resolves`** (→/int) — ISOLATED to a self-contained 3-file fixture (NOT stdlib/lib-path-specific): a bare current-module-relative submodule name in `export`/`import` skips spec **§8.11.2 step 1** (`handle_export`→`resolve_module_file`, `process_form/dependency.rs:735`); FQ path works; FAILS ("module 'child' not found"); `// spec: §8.11.2`. **Suite: 1766 run / 1763 passed / 3 known-defect REDs (0476 + these 2) / 1 skip — ZERO regressions.** Fixed a /qa-caught malformed citation on the 0476 guard (`spec/06-adt.md §6` → the real `spec/05-definitions.md §5.2.7` "Data constructors are functions… `(let [f Some] (f 42))` works" — the exact contract 0476 violates); spec-link linter clean for regression.rs (the 2 residual MIS-CITED are pre-existing Decision-0044/ClusterContext, unrelated). **FIXME wave-gate triage:** 8 S96-filed (0469/0471/0474/0475/0477/0478/0479/0480) all forward cross-skill requests to /spec·/int·/backend·/design — none block S96 deliverables; 0478 (no trigger), 0474 (needs /qa heap repro; pre-existing in Par), 0479 (needs reactor design) defer-legit; 0475/0477/0480 are quick /spec concurrency-wording/rulings (drain candidates).
- 2026-06-30 — **/spec drained 3 concurrency-spec FIXMEs (user-ruled at close).** 0477 RATIFIED (sleep/timeout duration = milliseconds, `sleep: Int→IO Int`; `spec/10-io.md §10.12.8` + `spec/12-runtime.md §12.4.4`; deleted). 0480 FIXED (`select : Vec (IO a)` not `List`, both §10.12.8 + §12.4.4, swept clean; deleted). 0475 RULED (`(select [])` MUST raise a recoverable runtime error §12.7.2 — chosen over unsound-`0`/hang; pinned §10.12.8 "Empty select" + §12.4.4; **re-targeted to /int** with impl site `io.rs:496-500` "select over empty collection" + /qa failing-test owed — NOT deleted). Linters: reconcile exit 0 (589 live cites); spec_link_check byte-identical to baseline (no new issues).
- 2026-06-30 — **✅ S96 CLOSE.** Final verify: `cargo nextest run --no-fail-fast` = **1766 run / 1763 passed / 3 failed / 1 skip**, the 3 fails being EXACTLY the intentional known-defect guards (0476, race+inline-bind, bare-submodule-reexport) — zero regressions. **Delivered:** single ABI v8 + single async trampoline (full cutover); launch-and-continue + supervisor + backpressure; cancellation foundations (2 reviews) + race/select/timeout/sleep; **the marquee "server with no spawn" genuinely fans out** (fixture + exemplar, 105ms vs 417ms); **2 S93-class scheduler lost-wakeups closed** (SIGUSR1 dump in-tree) retiring the intermittent suite hang; 3 waves + marquee reviewed; full 5-skill user-proxy validation; new `user/guide/concurrency.md`. Committed to main (not pushed — push is the user's call).
- 2026-06-30 — **Phase 6 /repl: self-documenting principle HOLDS for all S96 forms** (sleep/race/select/timeout — bare-lookup, /info, /type, /doc, evaluation, REPL↔`--run` parity all PASS with correct `:Type value` + qualified names + docstrings; clean type errors on bad input, no panics/opaque errors; known defects 0475 empty-select + 0476 constructor don't crash the REPL). **One conformance gap FIXED in-session (FIXME 0481 resolved+deleted):** `race`/`select`/`sleep` (+`bind`) classified `; defn` instead of `; primitive` — root cause `src/repl.rs:2227` matched only `DefKind::Primitive`, missing the slot-less `DefKind::PrimitiveExtern`. Fix: `| DefKind::PrimitiveExtern` (one line, repl/spec.md §1.1). Guard `tests/repl_introspection.rs::extern_primitive_classifies_as_primitive_not_defn` (RED pre-fix `; defn`, GREEN post). **Two pre-existing non-S96 observations noted for /sprint-triage (not filed):** `/sig <imported-name>` punts (no sig for any imported symbol, not opaque — /type/info/doc/bare all work); `repl/spec.md §1.2` IO-display wording stale (REPL unwraps IO via `unwrap_io_inline` per Decision 24/FIXME 0457 — predates S96, needs deliberate spec-grooming).
- 2026-06-30 — **Phase 6 /stdlib: concurrency surface VALIDATED correct+complete+idiomatic — no changes (Principle 6).** Exercised as a real consumer via `CRANELISP_LIB=stdlib --run` scratch programs (stdlib-separation honored): `(timeout 1000 (Pure 42))`→Some 42; `(timeout 10 (sleep 1000))`→None; race/select/sleep compose; **ex4 load-bearing: `(timeout 10 (sleep 1000 >> print "LATE"))` under stdio prints "EARLY" only — "LATE" ABSENT** ⇒ the timed-out loser is genuinely CANCELLED not run-to-completion (spec §10.12.8 item 4 + §10.12.9). `timeout` (`stdlib/core/io.cl:47`) is the sole correct derivation; race/select/sleep correctly raw `primitives` builtins (consumers already import from primitives — no re-export gap; a wrapper layer would only duplicate docstrings + add indirection). Naming aligns with `core.async` (timeout/select≈alts!/sleep≈Thread/sleep). **Findings:** (a) **FIXME 0480 (→/spec)** — `select` typed `List (IO a)` in §10.12.8 but impl is `Vec (IO a)` + examples use `[..]` Vec literals; spec→Vec (no impl change); sibling of 0477. (b) **Pre-existing module-resolution defect (→/qa repro, NOT concurrency, NOT S96-blocking):** `(import [core [timeout]])` (the `core` shell submodule re-export) fails under `CRANELISP_LIB=stdlib` with "module 'syntax' not found (re-exported by 'core')" — general to the `core.cl:7` `(export [syntax …])` re-export from a lib path (reproduces with `[core [map-io]]` too); the working idiom `(import [core.io [timeout]])` is unaffected. Queued for the consolidated Phase-6 /qa repro pass.
- 2026-06-30 — **Phase 6 /port: exemplar ADOPTS the concurrent fan-out — DONE.** Reshaped `exemplar/main.cl` serve-loop to mirror the proven fixture's direct-leaf discipline: removed the `handle-conn` user-fn wrapper (the IO-in-effect-position TRAP), inlined `(bind (read-conn…) (fn [req] (bind (sleep (slow-ms req)) (fn [_] (send-conn… (safe-handle req))))))` as the discarded sub-tree + `(serve-loop listener)` continuation; pure helpers `slow-ms: Request→Int` + `safe-handle: Request→Response` compute leaf ARGS only (no user-fn-returning-IO in any effect position). New e2e `tests/exemplar_web.rs::exemplar_web_server_fans_out_concurrent_requests_overlap`: **K=4 /slow = 105ms vs serial ≈417ms** (single 104ms), 5/5 deterministic, all 200 OK. Preserved: serves (form/solve/404 over HTTP), 500-on-fault (`safe-handle`+`catch-runtime-error`), keeps-living. Harness: both exemplar_web tests now use `free_port()`+`CRANELISP_PORT` (retired fixed-8080). exemplar/CLAUDE.md updated. Full suite **1762 passed / 1 skip / 1 expected fail (0476 guard)** — no other regression. **Honest-scope finding filed FIXME 0479** (→/int): the reactor `block_on_reactor` 30s watchdog aborts a legitimately-idle server `accept` loop (pre-existing; the marquee server can't yet idle unattended > 30s; needs a no-progress watchdog / server-mode opt-out — does not affect any e2e which all drive traffic < 30s). Chunk A+B COMPLETE; C1 + C-fanout COMPLETE; **FIXME 0472 RESOLVED+deleted** (the marquee launched-web-handler reset — `define_launch_cont_body` failed to seed capture *types* into the inner compiler → skipped consuming-call `rc_inc` on `listener` → double-dec use-after-free; fix mirrors the S60 lambda.rs capture-type seeding + fails-on-revert unit test; served/500 e2e GREEN). FIXME 0470 lighter-path RULED IN-SPRINT by /arch (E1-E3 predicate). Sequence: C2 reactor cancellation foundations (ACTIVE) → C3 combinator node+runtime → C4 timeout/cancel/shutdown+verify.

**Goal**: Make the v7 concurrent-platform model real on real platforms (`web` + `stdio`) and stand up a production-shaped "server with no `spawn`" — completing the IO-transition substrate (poll-shape live capacity + `poll_support` ergonomics) and landing the full control layer on top: launch-and-continue + supervisor (slice 5), backpressure/admission budget (slice 4), and cancellation + combinators (slice 7).

## Scope

The IO transition (S95, slices 3+6) proved the async substrate feature-on ≥ feature-off, but the **concurrent-platform model is still proven only on the synthetic `async-demo` socketpair/timer leaf**. S96 makes it real on two production platforms and lands the first user-facing control capability (launch-and-continue + supervisor) on top — the "server with no `spawn`" reference demo (§10/§16 reference workload).

**In scope — the keystone (one coherent increment around the server demo):**

1. **`web` + `stdio` v7 model-platform rewrites.** Rewrite the exemplar **`web` platform** (`exemplar/platforms/web/`: `listen`/`accept`/`send` + internal `read_request` → poll-shape `accept`/`read` leaves over a connection token) and **`stdio`** (`print` stays blocking; `read_line` the poll candidate — the "simple platform ports cleanly" ergonomics check). v6 blocking leaves coexist; this is *adoption* of the first real poll-shape effects, not a breaking cutover.

2. **`poll_support` ergonomics suite — evidence-first.** Rewrite the platforms by hand against a minimal env accessor, let the idiom pain surface, then extract the `concurrency`-gated `poll_support` module from real evidence: typed env accessor (codifies the R1 env-layout convention in one place), fd-readiness/timer poll scaffold over the host/waker vtable, first-poll/re-poll phase scaffold (`PollState`, which lost its S95 consumer to the blocking-carrier decision), and a **converged macro skeleton** retiring the /review-S94-flagged ~105-line `declare_concurrent_platform!` mirror. The descriptor (trust assertion) + syscall (platform domain) + result interpretation stay hand-written.

3. **Poll-shape live capacity supply + acquire-around-poll** (deferred from S95). S95 reserved the poll-node `(token, capacity)` slots at sentinel and proved the token-capacity pool on the blocking carrier; S96 lights up the **reactor connection pool** — the real capacity-on-poll consumer — with the permit wrapping the full `EffectPoll` establish→ready arc (the acquire-around-poll lifecycle, the deferred complexity).

4. **Slice 5 — launch-and-continue + supervisor.** Fire-and-forget effect launch + a supervisor that turns a panicking handler into a 500 while the server lives. Co-landed with the web rewrite (user direction S95) so the "server with no `spawn`" demo exercises real poll `accept`/`read` leaves in-sprint.

5. **Slice 4 — backpressure / admission budget.** Bounded admission (saturate-not-oversaturate; bounded in-flight + memory). FIXME 0442 resolves the cross-cutting interface question — one unified CPU+IO budget abstraction vs two mechanisms sharing a shape (the over-budget actions differ: CPU spark folds inline, I/O effect admission-parks). The program-chosen `degree` throttle composes as `min(capacity, degree)` over the S95 per-token capacity.

6. **Slice 7 — cancellation + combinator layer.** The user-facing control combinators `race`/`select`/`timeout` — per-request timeout, cancel-on-disconnect, graceful shutdown. Has spec surface (FIXME 0447 combinator half).

**Opportunistic drains (land in-wave if slack; else carry):**
- **0461** (/design platform-doc capacity-carrier + ABI-v7 drift) — small reconciliation, owner already in scope.
- **0462** (/docs IO-concurrency per-resource-bound honest scope) — has its worked example *only once* the web rewrite lands; natural S96 home.

**SCOPE PIVOT (user direction, 2026-06-29) — single-ABI cutover, ditch backward compat.** "Jump to the latest ABI and ditch backward compatibility — there are no users." This **retires the Phase-2 additive-coexistence envelope** (no-ABI-bump / no-`cranelisp-types` / no-`public-api.txt` constraints were predicated on backward compat). New foundation: **ONE platform ABI** (the latest, v7-shape) — one manifest, one macro, one GOT export per platform; each effect independently blocking or poll-shape via its descriptor. **Dissolves FIXME 0464 entirely** (no mixed-DLL problem — stdio = `print`-blocking + `read_line`-poll in one manifest; web = one platform), and **un-blocks A4 steps 1/3/5** (the /arch "resolve-by-scoping" workaround — pure-v7 web + stdio-stays-v6 — is superseded). Deletes: `declare_platform!` v6 macro, the v6 `cranelisp_platform_manifest_<name>` export, the either/or loader probe, the `from_scheduling_class` compat bridge. Migrates: ALL existing platforms/leaves to the single ABI; the default non-reactor host loads the unified manifest + calls blocking effects synchronously. `/arch` is designing the cutover + migration plan (Phase-2-level re-architecture mid-Phase-5); the plan returns to the user before the heavy /dev migration.

**SCOPE PIVOT EXTENDED (user direction, 2026-06-29) — collapse to ONE trampoline too (full streamline, one jump).** User: "are we still carrying two tramps or variations? would it make sense to cutover to the streamlined state in one jump? simple platform, simplest tramp?" Yes — the single-ABI plan above still kept TWO `#[cfg]`-selected trampolines (sync off-build + async on-build; the plan even adds a poll-error arm to the off-build). Landing A4c on the dual-trampoline state would be a Principle-8 interim (migrate platforms now, re-migrate when the trampoline collapses later). So A4c targets the **genuine end-state**: **one ABI + one (async) trampoline + NO `concurrency-runtime` feature**. Delete the synchronous trampoline; the reactor IS the runtime. Enabler = **lazy reactor init** (executor drives on the calling thread; mio `Poll`/reactor thread constructed only when the first poll-shape leaf or `Par` is scheduled) — a pure-blocking program drains synchronously through the one trampoline and pays ~nothing, so lean-default becomes a RUNTIME property, not a `#[cfg]` split. Retires the "reactor-free-off"/"byte-identical-off" invariant entirely (no off-state to police → the feature-on-vs-off divergence bug class is gone). /arch is feasibility-checking the lazy executor (main-thread-drive for pure-blocking; `--link`/exe-bundle with an always-present-but-lazy reactor) and redesigning A4c as the full streamline; the revised plan returns to the user before /dev.

**Out of scope:**
- **Parallelism/memory-contention knot** (FIXME 0459 + atomic-RC crux, §3.1) → **S97** (Parallelism axis, orthogonal to the IO axis).
- **`/strand` dev surface** → slice 8 (diagnostics). The strand sink emits + is test-verified; only the REPL surface is deferred.
- **Phase-H openers** (0050/0052/0365), **0407/0416/0419** (host-callback escape hatch / bitwise / shared `HostCallbacks` builder), **0408 perf half** — parked.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0447 | /spec | deferred → **trigger MET — ACTION** | async-leaf/combinator/supervisor spec. Both halves land this sprint: supervisor/launch-and-continue (slice 5) + the `race`/`select`/`timeout` combinators (slice 7) → /spec actions the §10.12/§12 control-layer surface this sprint. |
| 0442 | /arch | **RESOLVED (Phase 2, deleted)** | unified CPU+IO budget vs two → ruled **TWO substrate-bound mechanisms, one shared concept** (over-budget actions + threading models diverge irreducibly; CPU counter stays subsumable, I/O *degree* parameterizes the §8.1 pool + a global reactor-thread gate). Manifested at `effect-concurrency.md` §5; slice-4 /design elaborates against it. |
| 0463 | /design | **RESOLVED (A4 design pass, deleted)** | poll-shape operand injection lives in the backend `MonoExpr` pass (point) vs `poll_support` (value source) — reconciled in `poll-support.md §3.4.1` |
| 0465 | /design (+/port +/platform) | open → **Chunk B** (user decision) | web capacity-on-poll needs a cranelisp connection-handle interface (`web/Connection` ADT + token-carrying `read`/`send` + serve-loop reshape) — co-designs with the slice-5 server demo that exercises it; the deferred web e2e rows (§3A/§3C-web) + Gap G4 ride with it |
| 0464 | /arch | **SUPERSEDED-BY-PIVOT → deleted** | The single-ABI cutover dissolves the within-DLL-mixing problem entirely (one manifest carries both shapes). Resolve-by-scoping ruling retired; merge mechanism never built; FIXME file deleted. See "## Single-ABI cutover" below. |
| 0461 | /design | **RESOLVED (Phase-3 platform pass, deleted)** | platform design-doc capacity-carrier + ABI-v7 drift — reconciled `platform.md`/`platform-dlls.md` |
| 0462 | /docs | open → **action** (web rewrite supplies the worked example) | IO-concurrency honest per-resource scope |
| 0419 | /arch | open (off critical path) | shared `HostCallbacks` builder — `--link` concurrency may re-surface it here |
| 0459 | /backend | DEFER (S97) | contention-aware spark gate — Parallelism axis |
| 0460 | /qa | open (opportunistic) | set-doc honest-failure e2e — pure drain, not on critical path |
| 0430 | /design | deferred | docstring-into-source regen — agent Document-mode, off-track |
| 0407 | /arch | DEFER (parked) | host-callback escape hatch |
| 0416 | /arch | DEFER (parked) | bitwise intrinsics — feature-gated |
| 0408 | /port | DEFER (perf half wants `--release`) | Sudoku raw-speed numbers |
| 0050 | /int | DEFER (Phase H) | display protocol |
| 0052 | /repl | DEFER (Phase H) | `/learn` tutorial |
| 0365 | /spec | DEFER (Phase H) | `Type.member` accessor qualification |

## Architecture review (Phase 2)

**Verdict: SIGN-OFF WITH REVISIONS** (`/arch`, 2026-06-28). The scope is technically
coherent, correctly sequenced, and — decisively — carries **no Principle-8 interim risk**:
every item is *additive adoption* or the *lighting-up of an already-reserved gated carrier*,
not a throwaway interim. The "revisions" are sharpened seams + two co-landing constraints,
not blockers. **No `cranelisp-types` edit is needed this sprint** (the standout edge result —
see public-API below). FIXME 0442 is **RESOLVED by this review** (recorded at its
manifestation site `effect-concurrency.md` §5; the FIXME file is deleted). The blast radius
is real, so the work is partitioned into **three dependency-ordered chunks** (below) for
chunk-by-chunk Phase-3/5 gating.

**Why no interim risk (the Principle-8 spine).** (1) web/stdio + poll_support are
*evidence-first* extraction (rewrite by hand, extract the suite from real pain — explicitly
NOT speculative abstraction; it is a net subtraction, retiring the ~105-line mirror).
(2) acquire-around-poll reuses §8.1 (the pool carrier) + the permanent §7 wakeable bridge. (3) supervisor
reuses the S95 worker-side capture. (4) backpressure *parameterizes* the existing §8.1 pool
(degree) + reuses its permit machinery (global gate) — and the slice-1 CPU counter stays
subsumable-not-orphaned (0442 ruling). (5) combinators are the permanent in-language control
layer; cancellation lights up the already-reserved `drop_state`. Each chunk's deliverable
*survives* — e.g. Chunk A ships a poll-shape web platform under the existing serial serve
loop (a permanent baseline), and Chunk B *accretes* fan-out on top; nothing is built to be
discarded.

### Gate rulings (a)–(d) + public-API

**(a) acquire-around-poll lifecycle — NO pool deadlock from park-while-holding-permit; TWO
structural requirements.** A permit is a **counter on the single reactor thread, not a
thread**. A poll-shape effect that parks (registers fd/timer interest, returns `Pending`)
holds only a *permit slot* while **freeing the reactor thread** to drive other futures — so
N parked same-token polls each wait on their **own independent** external readiness; none
depends on another *releasing* a permit, and the (N+1)th parking is correct backpressure,
not deadlock. The two genuine hazards, both prevented structurally:
1. **Cancellation must release the permit (the load-bearing cross-link to slice 7).** The
   `Permit` MUST be an **RAII drop-guard owned by the `EffectPoll` future**, released on
   `Poll::Ready` **and on future-drop**. A race-lost / timed-out / disconnected poll that
   leaks its permit is exactly how a capacity-N pool bleeds to deadlock. So acquire-around-
   poll (Chunk A) **builds** the drop-release path; cancellation (Chunk C) **exercises** it.
   This is a named A→C contract — co-review the two for the Permit-on-drop path.
2. **Acquire is non-re-entrant on its own token.** The acquire is the trampoline's single
   admission gate wrapping the whole establish→ready arc; the **platform poll-fn cannot
   re-enter admission**, so a poll-fn cannot self-deadlock by dispatching another effect on
   its own exhausted token. (The web case is sound by construction: `accept` mints a *fresh*
   connection token; `read`/`send` ride that token — no re-entry on the listener/pool token.)
   Admission stays reactor-thread single-threaded (the reactor.md §2.8 lock-free-permit-map invariant
   holds verbatim for the poll carrier).

**(b) slice-5 launch-and-continue lifetime + supervisor — reuse the CAPTURE, replace the
re-raise; new supervisor machinery required; co-land with backpressure.** The S95 fork-join
ferry (worker-side `take_runtime_error()` → join-side `set_runtime_error()` re-raise) is a
**structured** mechanism: every branch joins inside the dynamic extent. Launch-and-continue
is **detached** — a fire-and-forget strand with **no join point**, so the ferry's *join-side
re-raise has nowhere to land*. Ruling: the **worker-side capture is reused verbatim**; the
join-side re-raise is **NOT** what detached strands need. New machinery = a **supervisor
handle** (a `JoinSet`-equivalent on the reactor) that **owns** each detached strand future,
catches its outcome, and applies the §10 per-effect-kind policy (**500 + log + drop-the-
request**, via the strand sink + strand-id already plumbed) — never re-raising into a
nonexistent parent, never aborting the server. Lifetime = **detached-but-supervised**:
outlives the spawning expression (the accept loop continues), owned by the supervisor, never
joined by pure code. This is **co-requisite with launch-and-continue** (a detached strand
with no supervisor silently swallows panics — §10) AND **gated on backpressure** (§14 step 4:
unbounded accept-loop fan-out is a memory-exhaustion hazard; the global admission budget is
what makes the fan-out safe). Therefore slices **4 + 5 co-land** (Chunk B), and Chunk B
depends on Chunk A (the demo fans out real poll `accept`/`read` leaves). The §10 honest
caveat (no "first error" ordering for detached strands — each supervisor action is
independent) stands.

**(c) poll_support macro convergence — APPROVED; the `_neg` frozen-edge guard is the
enforcement, and it MUST stay green.** The converged skeleton retires the
`declare_concurrent_platform!` mirror via a **field-shape-parameterized** shared inner
helper: v6 `declare_platform!` and the gated v7 path are **separate `macro_rules!` arms** that
delegate to a common `@emit-*` helper taking only **shape-neutral tokens** (manifest-entry
construction, GOT export, fn-name handles). v7 type names (`ConcurrentPlatformFn`,
`ConcurrencyDescriptor`, `drop_state`, …) appear **only in the v7 arm** (itself gated) — never
in the shared helper, and never inside a single arm that the v6 caller would still tokenize.
(The hazard to avoid: one arm with a `#[cfg]`-stripped v7-type reference — the v6 expansion
may still need the type in scope. Separate non-matching arms don't expand, so the two-arm +
shared-helper shape is safe.) Enforcement is the **existing `_neg` guard** (v6 expansion
free of v7 names) — it is this chunk's review gate; `/review` (platform) walks it on the
change-set. **No platform `public-api.txt` touch** (all helpers name already-gated types).

**(d) FIXME 0442 — TWO substrate-bound mechanisms, ONE shared *concept*, NOT one unified
abstraction. RESOLVED.** Full ruling at `effect-concurrency.md` §5 (manifestation site;
FIXME deleted). Summary: the over-budget actions diverge irreducibly (CPU spark **folds
inline** on the caller — a backend create-gate fallback; I/O effect **admission-parks** — an
async suspension), and the two substrates **forbid a shared data structure** (CPU counter is
necessarily a cross-thread `AtomicIsize` on rayon; I/O admission is the *deliberately
lock-free* reactor.md §2.8 single-reactor-thread permit map). A unified abstraction would be a name over
two disjoint bodies (Principle 6) and would regress the reactor.md §2.8 lock-free ruling. Neither is
orphaned (Principle 8): the slice-1 CPU counter is unchanged, its *signal* refined later by
the contention-aware gate (0459, S97/Parallelism-axis — not slice 4's); the slice-4 I/O
*degree* is **not new machinery** — it is `effective permits = min(capacity, degree)` on the
existing §8.1 token-permit map **plus** one **global** reactor-thread admission `Semaphore`
(the launch-and-continue fan-out memory bound) reusing the same `AcquirePermit`/`TokenSlot`.
This is the descriptor→runtime-primitive mapping slice-4 /design elaborates against.

**Public-API / interface impact — ZERO new edges, NO ABI bump, v7 stays UNFROZEN.** The
strongest possible result, and it confirms the additive-no-cutover framing holds:
- **`cranelisp-types`: NO edge touch.** degree/global-budget ride the **already-landed,
  `concurrency`-gated** `ConcurrencyDescriptor.global_budget` (lit up → stays gated, off the
  default `public-api.txt` baseline) + a reactor-construction knob (int-internal). The
  `_neg`/frozen-edge guard stays green.
- **`cranelisp-platform`: NO `public-api.txt` touch.** poll_support is `concurrency`-gated;
  the macro convergence names only already-gated types (gate (c)). Poll-shape live capacity
  rides the **node `(token, capacity)` slots reserved at sentinel in S95** (in-process
  backend↔intrinsics convention) — no new public constructor on the default edge.
- **Slice 7 combinators / cancellation: NO ABI bump.** `race`/`select` are new **IO node
  tags** (in-process backend↔intrinsics convention, `concurrency`-gated, the
  `IO_TAG_EFFECT_POLL` precedent — pinned const, off the default edge); `timeout` is derived
  `.cl` stdlib. Cancellation lights up the **already-reserved gated `ConcurrentPlatformFn.
  drop_state`** (landed S94, no bump).
- **v7 is NOT frozen by S96.** web/stdio are **in-tree** (exemplar/bundled, rebuilt with the
  compiler), not out-of-tree prebuilt cdylibs — so the "reserve-now-no-`ABI_VERSION`-bump"
  latitude **persists**. The freeze trigger is the first **out-of-tree** v7 cdylib release (a
  future milestone, not S96). S96 is *adoption of the first real poll-shape effects*, not a
  cutover; v6 blocking leaves coexist permanently via the slice-6 rayon route.
- **0419 (shared `HostCallbacks` builder): confirmed OFF the S96 critical path.** `--link`
  concurrency stays a later slice (production default keeps `concurrency-runtime` OFF; the
  exe-bundle path never enables it — structural). No slice this sprint lights up `--link`
  concurrency, so the two hand-mirrored host-construction sites are not re-surfaced. Reactor/
  `HostCtx` construction remains single-sited in intrinsics (divergence-proof), explicitly
  out of 0419's scope. Stays parked.
- **0407 (host-callback escape hatch): confirmed PARKED.** The reactor structurally obviates
  Model B; the residual (synchronous C-reentrancy) is reactor-orthogonal, build-on-demand.
  Untouched by S96.
- **0447 trigger MET (confirmed):** both halves land — supervisor/launch-and-continue
  (Chunk B) + `race`/`select`/`timeout` (Chunk C) → /spec actions the §10.12/§12 control-
  layer surface this sprint (split across the chunks, per the partition).

### FIXME 0464 ruling (/arch) — within-DLL v6+v7 mixing (2026-06-29) — SUPERSEDED by the single-ABI cutover (see "## Single-ABI cutover" below)

> **SUPERSEDED 2026-06-29 (same day) by the user's single-ABI scope pivot.** The
> resolve-by-scoping ruling (pure-v7 web + stdio-stays-v6 + deferred dual-manifest
> merge) was correct *within the v6/v7 coexistence envelope* — which the pivot
> RETIRES. Under one ABI there is no within-DLL mixing problem at all: a single
> manifest carries blocking and poll-shape entries natively. stdio becomes
> `print`-blocking + `read_line`-poll in ONE manifest (A4 step 1 UN-descoped); web
> is one platform with poll effects. FIXME 0464 is resolved-by-superseding-pivot
> and **deleted**. The merge mechanism (option a) is never built. The text below is
> retained only as the record of the coexistence-era reasoning.

**Verdict: RESOLVE-BY-SCOPING. Pure-v7 web + stdio-stays-v6 delivers the S96 demo
with NO merge mechanism. The dual-manifest merge (option a) is the named future
path, DEFERRED to the first genuine within-DLL mixed-platform need (unmet trigger).
A4 step 3 (web) PROCEEDS, reshaped to pure-v7; A4 step 1 (stdio `read_line` poll) is
DESCOPED this sprint; A4 step 5 (macro convergence) stays optional/deferred. 0464 no
longer blocks the headline.**

**1. Scoping verdict — pure-v7 web is VIABLE (grep evidence).** Within-DLL mixing is
NOT required for the S96 server demo. The server demo (Chunk B, slice 5) runs under
the `concurrency-runtime` host (it needs the reactor); the web platform is only ever
a concurrency-host artifact going forward. Evidence:
- **The exemplar's committed showcase is stdio, not web.** `user.cl`/`solver.cl` use
  `(platform stdio)` (`exemplar/CLAUDE.md`; web is the "designed-but-unbuilt future
  stretch"). The exemplar's default `--run`/`--link` showcase path is web-free.
- **The ONLY consumer of the real `(platform web)` is `tests/exemplar_web.rs`** — a
  non-ignored e2e that spawns `--run exemplar/main.cl` against the DEFAULT-host binary
  (`target/debug/cranelisp`, built without `concurrency`), exercising the **v6 serial
  serve loop** (the exact "permanent serial baseline" Chunk A ships). `tests/exemplar.rs`
  uses its OWN inline `main.cl` fixtures (`.file("main.cl", …)`), NOT `exemplar/main.cl`
  — it does not load web. No other default test loads web.
- **No concurrency-host test currently loads web** (`concurrency_reactor.rs` =
  `io_main.cl (Pure 7)`; `concurrency_capacity.rs` = async-demo/test-capture/pool-demo).

  Therefore: make the exemplar **web** platform **pure-v7** — ALL leaves poll-shape
  (`accept`/`read` are genuine reactor polls; `listen`/`send` are poll-shape even where
  the syscall is nominally blocking, via a trivially-ready `Poll::Ready` poll — §6.8
  point 1: "sync effects return `Poll::Ready` immediately, so blocking- and poll-style
  coexist"). It invokes `declare_concurrent_platform!` ONLY ⇒ ONE GOT export ⇒ **block 1
  (GOT collision) never arises**; the existing v7-probe-first **either/or loader suffices**
  ⇒ **block 2 dissolves**. NO merge mechanism. The §3.2 web design (poll `accept` mints a
  fresh connection token; `read`/`send` ride it) is unchanged — it was always poll-shape;
  pure-v7 only PINS `listen`/`send` to poll-shape (drops their "(or v6 blocking)" alternative,
  a /platform-domain choice).

**2. Required migrations (named, not /arch-owned — file/action per owner).**
- **`/qa`: migrate `tests/exemplar_web.rs` to the `concurrency-runtime` lane.** A pure-v7
  web platform loads ONLY under the concurrency host, so the test must be
  `#[cfg(feature = "concurrency-runtime")]`-gated and spawn the concurrency-runtime binary
  (the `nt-reactor-e2e` lane: `cargo nextest run -p cranelisp --features concurrency-runtime`),
  exactly as `concurrency_reactor.rs` rows are. This is NOT a regression — the v7 web server
  IS a reactor-host artifact (it always was, per the S96 plan); the migration co-lands with
  the A4/A5 web rewrite. The §3A/§3C-web rows + Gap-G4 port-parametrized fixture land in
  this same gated lane.
- **`/port` + `/docs`: `exemplar/main.cl` becomes a concurrency-runtime-only entry.** Under
  pure-v7 web, `--run exemplar/main.cl` on the DEFAULT binary will fail to load web
  (`cranelisp_platform_manifest_web` absent) — acceptable, because the committed stdio
  showcase (`user.cl`/`solver.cl`) is untouched and web was always the reactor-host stretch.
  `/port` notes the web entry now requires the `concurrency-runtime` build; if `read` becomes
  a first-class effect (§3.2 — was internal `read_request`), `main.cl`'s
  `(import [platform.web …])` adds it. (`exemplar/CLAUDE.md` is /port-owned — I do not edit
  it; this is the change request.)

**3. stdio stays FULLY v6 this sprint — drop `read_line`-as-poll (A4 step 1 DESCOPED).**
`print` is loaded by the default host EVERYWHERE (exemplar stdio CLI, examples, dozens of
default tests), so stdio MUST retain a v6 manifest and CANNOT go pure-v7. A mixed v6+v7
stdio is the ONLY thing that needs the merge mechanism — and the stdio poll rewrite is, by
the design's own framing (`poll-support.md §3.1`), the **"simple platform ports cleanly"
ergonomics check — the least load-bearing A4 goal**. The "real poll platform" proof is
carried entirely WITHOUT stdio: **web** (pure-v7, real `accept`/`read` reactor leaves — the
§10/§16 reference workload), the landed **`poll-pool`** test leaf (live `(token, capacity)`
carrier end-to-end), and **`async-demo`** (two real poll leaves overlap on the reactor).
stdio's ergonomics check defers cleanly with the merge mechanism; it has no S96 consumer.

**4. Mechanism ruling — IF/WHEN within-DLL mixing is genuinely needed: option (a)
dual-manifest merge. Option (b) REJECTED.** When a single platform must be BOTH
default-host-loadable (a v6 blocking effect) AND carry a poll effect, build **option (a)**:
one DLL exports BOTH `cranelisp_platform_manifest_<name>` (blocking subset) and
`cranelisp_concurrent_manifest` (poll subset) over ONE shared GOT (disjoint slot ranges);
the `concurrency` host reads + merges both, the default host reads only the v6 subset (poll
effects simply absent for it). Size: (i) de-dup the `__CRANELISP_PLATFORM_GOT` static so one
DLL invoking both emitters exports it once — the **natural home is the deferred A4-step-5
macro convergence's shared `@spine`/`@emit` helper** (already planned); (ii) a `src/platform.rs`
loader change to read both manifests from one handle and merge over the shared GOT slab.
**Stays within the Phase-2 envelope: NO `cranelisp-types` touch, NO `ABI_VERSION` bump, NO
`public-api.txt` touch** — both manifest exports already exist; the change is macro-internal
(GOT de-dup) + int-internal (loader merge); the v7 manifest read is already
`#[cfg(feature="concurrency")]`, so the default host's byte-identical-off (§6.8) is preserved.
**Option (b) (unified v7 manifest with a blocking carrier + a v6 *view*/shim for the default
host) is REJECTED**: larger, couples the default-host load path to v7 types, and re-opens the
"v7 unfrozen / no ABI bump" posture §6.8 worked to protect — it buys nothing (a) doesn't, at
higher blast radius. The merge's durable architectural home is recorded at
`platform-interface.md §6.8` (within-DLL-mixing disposition).

**5. Macro convergence (A4 step 5) — OPTIONAL this sprint, not a blocker.** The two-arm +
shared-`@spine` convergence (gate (c), retiring the ~105-line `declare_concurrent_platform!`
mirror) has independent quality value (Principle 6/7) and is the precondition for option (a)'s
GOT de-dup, but it is NOT required by pure-v7 web (which uses `declare_concurrent_platform!`
as-is). `/platform` MAY land it this sprint as a pure refactor (the `_neg` frozen-edge guard
is the gate); given its high blast radius across all platforms and the absence of a
load-bearing S96 consumer, deferring it WITH the merge mechanism is equally acceptable —
/platform's call against remaining Chunk-A budget. Either way it does not gate the demo.

**Public-API / interface envelope: CONFIRMED ZERO (Phase-2 result holds).** Pure-v7 web
uses only the already-shipped `declare_concurrent_platform!` + either/or loader — no
`cranelisp-types` edge, no ABI bump, no `public-api.txt` touch. The deferred merge mechanism
(option a) ALSO stays in-envelope when built. v7 remains UNFROZEN (web/stdio are in-tree,
rebuilt with the compiler).

**Disposition of 0464:** status → **deferred** (S96-blocking question RESOLVED by ruling;
residual = the merge mechanism, unmet trigger). Ruling recorded here + at
`platform-interface.md §6.8`. A4 row + FIXME-debt row updated.

## Single-ABI cutover (S96 SCOPE PIVOT) — /arch cutover + migration plan (2026-06-29)

**Returns to the user before the heavy /dev migration.** Durable architectural home:
`design/arch/platform-interface.md` §6.8.0. This re-architects the platform ABI to a
single shape, dissolving FIXME 0464 and superseding the resolve-by-scoping ruling and
the A4 "steps 1/3/5 walled" disposition.

**The unified ABI (v8).** ONE manifest type, ONE macro, ONE GOT export, ONE loader
path. Each effect is independently **blocking or poll-shape via its
`ConcurrencyDescriptor`** (`blocking == 1` ⇒ blocking `CLIO` fn; `blocking == 0` ⇒
poll-shape `PollFn`). The v6/v7 split — two macros, two manifest types, two GOT export
paths, the either/or loader probe — is **deleted**.

- **Unified `PlatformFn`** absorbs `ConcurrentPlatformFn`: one type-erased `ptr`
  (GOT-indirect dispatch is shape-agnostic; the backend reads `poll_shape` off
  `DefKind` to pick the node), `+ drop_state: Option<…>`, `+ concurrency:
  ConcurrencyDescriptor` **replacing** `scheduling_class: u32`. `ConcurrentPlatformManifest`
  merges into `PlatformManifest`; `concurrent_manifest_to_descriptors` merges into
  `manifest_to_descriptors`.
- **ABI types go CORE (ungated).** `ConcurrencyDescriptor`/`Poll`/`PollFn` (types) +
  `HostCtx`/`Waker`/`WakerVTable`/`PollFn` (platform) leave the dormant
  `#[cfg(feature="concurrency")]` edge. The **`concurrency` (layout-only) feature is
  RETIRED**; the host **reactor** stays optional behind `concurrency-runtime`
  (mio/futures). **`/arch` has LANDED the `cranelisp-types` half** (ungated the three
  types; re-documented `from_scheduling_class` as the blocking-effect descriptor
  sugar; `cargo check -p cranelisp-types` clean, the 3 ungated guards pass under the
  default lane).
- **ONE macro `declare_platform!`**; `declare_concurrent_platform!` deleted. Per-fn:
  `scheduling: SchedulingClass` (blocking sugar → `from_scheduling_class`, minimal
  churn) OR `descriptor: ConcurrencyDescriptor` + optional `drop_state:` (poll). A
  per-fn key choice in one macro — simpler than the rejected two-macro `@spine`
  convergence (A4 step 5 is thus SUPERSEDED, not merely deferred).
- **Loader single path** (`src/platform.rs`): delete the `#[cfg]` either/or probe +
  the `cranelisp_concurrent_manifest` symbol; dlsym `cranelisp_platform_manifest_<name>`,
  lift via the lone `manifest_to_descriptors`, compute `poll_shape =
  desc.concurrency.blocking == 0` and `scheduling_class =
  desc.concurrency.nearest_scheduling_class()` with NO cfg.

**Default (non-reactor) host + poll effects — the key question, answered: CALL-TIME
error, not load-time.** The default build reads the unified manifest fully, registers
blocking effects (work) and poll-shape effects (registered, undispatchable). A mixed
platform (stdio `print`+`read_line`) LOADS — `print` works, the wall 0464 hit is gone.
The backend is build-invariant (always emits the poll node). The earliest build-aware
point is the **trampoline**: the `#[cfg(not(feature="concurrency-runtime"))]` build
gains a new `IO_TAG_EFFECT_POLL` arm returning a **clean runtime error** ("poll-shape
effect invoked without a concurrency runtime — rebuild with `--features
concurrency-runtime`"), never a SIGSEGV / missing-arm panic. Load-time whole-platform
refusal is REJECTED (it would break `print` because the same DLL carries a poll
`read_line`). `concurrency-runtime` **stays optional** (lean default; `--link`
links no executor — structural).

**"byte-identical-off" → "reactor-free-off".** The ABI types are now core, so the
default build is not byte-identical to a pre-cutover default. The new, narrower
invariant: the `concurrency-runtime`-off build carries no reactor, drives only blocking
effects, and errors cleanly on poll invocation. The `_neg`/frozen-edge guards that
asserted "v7 types ABSENT from the default edge" are **inverted** (those types are now
present by design) → REPLACED by positive unified-`PlatformFn` field-order +
`ConcurrencyDescriptor`-presence guards (/qa rewrite).

**Public-API impact.**
- `cranelisp-types/public-api.txt`: ADD `ConcurrencyDescriptor`, `Poll`, `PollFn`
  (promoted to the default edge). `nearest_scheduling_class`/`from_scheduling_class`
  now on the default edge. `DefKind::PlatformEffect.poll_shape` already present. (/dev
  regenerates with the cutover change-set.)
- `cranelisp-platform/public-api.txt`: DELETE `declare_concurrent_platform!`,
  `ConcurrentPlatformFn`, `ConcurrentPlatformManifest`, `concurrent_manifest_to_descriptors`.
  PROMOTE (ungate) `ConcurrencyDescriptor`/`Poll`/`PollFn`/`HostCtx`/`Waker`/`WakerVTable`
  + the `poll_support` module. CHANGE `PlatformFn` fields (`scheduling_class` removed;
  `ptr`/`drop_state`/`concurrency` shape). `OwnedPlatformFnDescriptor.concurrency`
  ungated + always populated.
- ABI bump **7 → 8** (`cranelisp-platform::ABI_VERSION`; layout-affecting per Principle
  14). `shapes-badabi`'s hard-coded wrong version re-pinned wrong-relative-to-8.

**Platform migration list (the /dev work-list — 9 platforms + 1 negative fixture).**
All migrate to the unified `declare_platform!` in the SAME change-set (they must, or
they won't build against v8):
| Platform | Current macro | Migrated shape |
|---|---|---|
| `platforms/stdio` | `declare_platform!` (v6) | `print` **blocking** (`scheduling: Sequential`); `read_line` **poll-shape** (`descriptor: blocking=0`) — A4 step 1 UN-descoped |
| `platforms/boom` | `declare_platform!` | blocking (panic-test fixture) |
| `platforms/pool-demo` | `declare_platform!` | blocking (S95 blocking carrier) |
| `platforms/shapes` | `declare_platform!` + schema | blocking; keep `schema:` arm |
| `platforms/test-capture` | `declare_platform!` | blocking |
| `exemplar/platforms/web` | `declare_platform!` (currently blocking stub) | **poll-shape** `accept`/`read`/`send` over a fresh connection token; `listen` poll-shape-trivially-ready (`Poll::Ready`); requires reactor host |
| `platforms/async-demo` | `declare_concurrent_platform!` (v7) | unified, poll (`descriptor: blocking=0`); drop `features=["concurrency"]` |
| `platforms/poll-pool` | `declare_concurrent_platform!` (v7) | unified, poll + capacity; drop `features=["concurrency"]` |
| `platforms/shapes-badabi` | hand-rolled bad-ABI manifest | re-pin wrong-version-relative-to-8 (negative AbiVersionMismatch fixture; /qa) |
Plus: `build-link-prereqs.sh` (drops `--features concurrency` on the platform builds);
`tests/exemplar_web.rs` migrates to the `concurrency-runtime` lane (web effects are
poll → reactor host); `cranelisp-exe-bundle` recompiles against the unified
`PlatformManifest` (shape unchanged).

### Revised Chunk-A wave plan (folds into the Waves table)

A2/A2b/A3 (backend bake + intrinsics acquire-around-poll) are LANDED and unaffected —
the cutover changes the platform-authoring + loader surface, not the poll-node runtime
seam. The PARTIAL A4 is re-sequenced; A4 steps 0/2/4 stay landed.

| Wave | Surface | Task |
|---|---|---|
| **A4c — single-ABI cutover (NEW, the foundation)** | cranelisp-platform, cranelisp-types (done), src/, intrinsics, exe-bundle, ALL 9 platforms | Unify `PlatformFn`/manifest/macro/loader; ABI 7→8; ungate the ABI types; delete `declare_concurrent_platform!`/`ConcurrentPlatform*`/`concurrent_manifest_to_descriptors`/the either/or probe; add the trampoline `#[cfg(not(concurrency-runtime))]` poll-error arm; migrate all 9 platforms + `build-link-prereqs.sh`; regen both `public-api.txt`. /review (the largest wave; gate on the loader single-path unit + the unified field-order guard). |
| **A4d — web/stdio poll rewrite + poll_support** | cranelisp-platform, exemplar, stdio | On the unified ABI: stdio `read_line` poll (step 1, now trivial) + web `accept`/`read`/`send` poll (step 3); extract the `concurrency`-gated→now-core `poll_support` suite; /qa migrates `tests/exemplar_web.rs` to the reactor lane + co-lands the web e2e rows. |
| **A5 — wire + verify** | src/ | (unchanged) confirm `concurrency-runtime` wiring; flip Chunk-A RED→GREEN; verify reactor-free-off (poll-error arm) + `--link`-no-executor. |

**Knock-on to Chunks B/C: NONE semantically** — the reactor + poll-leaf substrate is
identical; B (launch-and-continue + supervisor + backpressure) and C (cancellation +
combinators) build on it unchanged, now over a single cleaner ABI. A4 step 5 (macro
convergence) is **superseded** (one macro, no convergence). FIXME 0419 (shared
HostCallbacks builder) stays parked.

### Single-ABI cutover — sizing + risk (honest verdict)

**Net-subtraction architecture, but a large mechanical blast radius.** After the
cutover there is *less* (one macro/manifest/loader-path/feature, not two) — it
*simplifies*. The cost is breadth, not depth: `cranelisp-types` (done, small),
`cranelisp-platform` (medium — merge 2 macros→1, 2 manifests→1, 2 lifters→1, ungate
~6 types, the macro_rules per-fn two-key arm), `src/platform.rs` loader (small),
intrinsics poll-error arm (small), exe-bundle (trivial recompile), **9 platforms ×
rebuild** (mechanical but where mechanical errors hide), and BOTH `public-api.txt`
baselines churn at the frozen edge + the `_neg` meaning-inversion (easy to get subtly
wrong). Worktree isolation is broken ⇒ this is one big serial /dev push.

**Landability:** **Landable in S96 as the Chunk-A foundation IF taken as the first
wave (A4c, before the web/stdio rewrites) and gated carefully.** It is the single
largest wave of the sprint. Recommended discipline: land the loader-single-path unit
+ unified-`PlatformFn` field-order guard RED first, then the migration flips them
green; review the public-api diff + the `_neg` rewrite explicitly. Honest risk
register: (1) the 9-platform rebuild + macro hygiene; (2) public-api baseline churn at
the frozen edge; (3) the trampoline poll-error arm must be genuinely loud (no
silent/SIGSEGV path) — the load-bearing default-host guarantee. None is deep, but the
breadth makes "the suite still passes" insufficient — each platform needs its own
load + dispatch confirmation.

### A4c revised — full streamline (single trampoline) — /arch design pass (2026-06-29)

**Returns to the user before the heavy /dev migration.** Durable architectural home:
`design/arch/platform-interface.md` §6.8.0a (extends §6.8.0 in the SAME A4c jump) +
`effect-concurrency.md` §6 (substrate gating updated). Folds the trampoline collapse
into the single-ABI cutover so A4c lands the FULL end-state — **one ABI + one (async)
trampoline + NO `concurrency`/`concurrency-runtime` feature** — in one wave, avoiding a
Principle-8 dual-trampoline interim.

**FEASIBILITY VERDICT: YES, with caveats** (verified against `cranelisp-intrinsics/src/{io.rs,reactor.rs}`):
- `block_on` already drives on the **calling thread** — there is **no dedicated reactor
  thread** (only rayon's own lazily-spun pool). A pure-blocking tree (Pure/Bind/blocking-
  Effect) **never returns `Pending`** (blocking effects force synchronously via
  `force_effect_node`), so the first `future.poll()` returns `Ready` and `turn()` is
  never reached ⇒ the mio `Poll` is never needed.
- **Lazy mio `Poll`** (a `OnceCell`/`RefCell<Option>` field inside `Reactor`, NOT a
  process-global) forced at `register_fd`/`register_timer` and **before** the
  `rayon::spawn` in `run_blocking_branch` is **sound by single-thread happens-before**:
  a poll-fn can only park by first calling `HostCtx::register_*` (forces the `Poll` on
  the calling thread before `Pending`), and the cross-thread `Par` wake races only after
  the spawn we front-load the `Poll`+bridge-waker ahead of — no wake ever targets a
  not-yet-built eventfd. The `HostCtx` *struct* stays eager+cheap; a trivially-ready
  poll leaf (web `listen`/`send` → `Poll::Ready`) pays nothing.
- Blocking path works without the `Poll` for the sequential case (inline force); only a
  blocking `Par` branch spawns rayon (forcing the lazy `Poll` first). The **sync
  `run_io_trampoline` is RETAINED** as the rayon-worker per-branch driver — only the
  `drive_io` `#[cfg]` split is deleted.
- `--link`/exe-bundle: the startup stub calls `cranelisp_run_io` → `block_on_reactor`
  unconditionally; mio/futures/rayon always linked (rayon already is); a `(print …)`
  binary builds no `Poll` at runtime. **No exe-bundle/`HostCallbacks` change; 0419 stays
  parked** (reactor `HostCtx` is single-sited in `block_on_reactor`).
- **Closest-feasible fallback if the lazy refactor over-runs A4c:** "always-construct-
  but-cheap" — keep `Reactor::new()` eager (2 syscalls/drive), still collapse to one
  trampoline + delete the features. A perf refinement, NOT a correctness interim
  (eager-cheap is permanently valid). Recommend landing the collapse green first, then
  lazy-`Poll` as the LAST step of A4c (both in A4c).

**What dies (the `#[cfg]` topology):**
- The `drive_io` `#[cfg(not(feature = "concurrency-runtime"))]` sync arm + the
  `#[cfg(feature = "concurrency-runtime")]` async arm → ONE async body.
- The §6.8.0-point-5 trampoline poll-error arm is **deleted before it is built** —
  poll effects ALWAYS work (no non-reactor build to error from).
- **BOTH** the `concurrency` AND `concurrency-runtime` features (§6.8.0 retired only
  `concurrency`). `reactor`/`strand` (intrinsics) + the gated platform/types ABI items
  go unconditional; mio/futures → plain deps.
- **Blast radius — feature sites removed: ~56 `#[cfg(... concurrency ...)]` source
  attribute sites** (io.rs 14, io/tests.rs 3, intrinsics lib.rs 2, strand.rs 5,
  platform lib.rs 8, platform tests.rs 4, platform concurrency.rs 1, types module.rs 1 +
  scheduling.rs 2, src/platform.rs 4, and the test files concurrency_{capacity,
  poll_capacity,reactor,stdio_v7}.rs 12) **+ 5 feature declarations** (root Cargo.toml,
  intrinsics/platform/types Cargo.toml, async-demo + poll-pool platform Cargo.toml) **+ 3
  nextest aliases** (`nt-concurrency`, `nt-concurrency-runtime`, `nt-reactor-e2e` collapse
  into the default lane).

**Lazy-init owner.** A reactor-thread-local lazy singleton on the `Reactor` struct
(`OnceCell`/`RefCell<Option<(mio::Poll, Arc<mio::Waker>)>>`), forced at the register
callbacks + before the `Par` rayon spawn. **Implementation detail is `/design` int's
(`design/int/reactor.md`)** — specified here, not authored by /arch.

**New regression guard (replaces "reactor-free-off"/"byte-identical-off").** A RUNTIME
assertion — *a pure-blocking program builds no mio `Poll` (no epoll_create/eventfd) and
drains synchronously through the one trampoline* — plus lazy-init correctness:
(i) a lazy-init unit/e2e driving a `(print …)`-shaped tree asserting the reactor's
`Poll` was never constructed (a test-visible construction counter on `Reactor`);
(ii) the existing reactor/`Par`-overlap e2e rows now exercise the lazy build-on-first-
`Pending` path (proving no lost-wake). The whole `#[cfg(not(...))]` feature-off test
lane + the 3 gated cargo aliases collapse into the single default `nt` lane (a /qa
rewrite, larger than §6.8.0's `_neg` inversion).

**Public-API impact (beyond §6.8.0).** Retiring `concurrency-runtime` ungates
intrinsics' `reactor`(+`strand`) module ⇒ its `pub` items (`Reactor`,
`make_cabi_waker`, `monotonic_nanos`, `join_io_leaves`, the `AsyncRead*`/`TimerWrite*`
fixtures) now hit the **default** `crates/cranelisp-intrinsics/public-api.txt` baseline.
/dev regenerates it in the cutover change-set; several fixtures likely warrant a
`pub(crate)` downgrade during the ungate (facade cleanup, flagged not blocking). The
§6.8.0 `cranelisp-types`/`cranelisp-platform` deltas + ABI bump 7→8 are unchanged.

**Revised waves (supersede the §"Revised Chunk-A wave plan" rows above):**
| Wave | Surface | Task |
|---|---|---|
| **A4c — single-ABI + single-trampoline cutover (NEW, the foundation)** | cranelisp-platform, cranelisp-types (done), src/, **cranelisp-intrinsics**, exe-bundle, ALL 9 platforms | §6.8.0 unification (PlatformFn/manifest/macro/loader; ABI 7→8; delete `declare_concurrent_platform!`/`ConcurrentPlatform*`/`concurrent_manifest_to_descriptors`/either-or probe; migrate 9 platforms + `build-link-prereqs.sh`) **PLUS** the streamline: collapse `drive_io` to one async body, delete the §6.8.0 poll-error arm, **retire BOTH features**, make reactor/strand + mio/futures unconditional, lazy-`Poll` reactor (last step). Regen BOTH `public-api.txt` + intrinsics' baseline. /review (the largest wave). **← /dev DONE (2026-06-29), Stage 1 full + Stage 2 eager-cheap fallback. Suite 1716/1716/1skip; contract crates 362/362; `--link` smoke green. 9 platforms migrated+confirmed; 3 public-api baselines regen'd; ABI v8; ~30 cfg sites+5 feature decls+3 nextest aliases removed; lanes collapsed. Stage-2 lazy-`Poll` DEFERRED to A5/S97 (real lost-wake hazard on the capacity-park-release path when the releaser is a sync-ready leaf — eager-cheap `Reactor::new` per drive is the blessed permanent state, ~2 syscalls/drive). /qa-flag: dev neutralized a forbidden `ensure_platform_cdylibs_built()` band-aid in `tests/examples.rs`+`tests/platform_errors.rs` (was breaking concurrent `--link`). **/review ACCEPT-WITH-FIXES (no Blockers; A4d may proceed). 2 Importants folded into A4d. Eager-cheap fallback adjudicated SOUND+PERMANENT; lazy-Poll = perf-only follow-up.** |
| **A4d — web/stdio poll rewrite + poll_support** | cranelisp-platform, exemplar, stdio | stdio `read_line` poll + web `accept`/`read`/`send` poll on the unified ABI (one manifest each — no mixed-DLL problem); use/refine `poll_support` (now-core) as the shared idiom; co-land the deferred web e2e rows (§3A/§3C-web) + the port-parametrized fixture (Gap G4); single trampoline ⇒ no lane migration needed (reactor always present). **PLUS the 2 A4c Importants (do FIRST): (i) `pub(crate)`-downgrade the 4 intrinsics demo-leaf fixtures + regen intrinsics baseline; (ii) doc-staleness sweep.** /review. **/dev DONE (2026-06-29) — step 0 (both Importants, +corrected an under-regenerated A4c intrinsics baseline) + step 1 (stdio `print`-blocking + `read_line`-poll in ONE v8 manifest — the mixed-platform proof; RC-verified). Suite 1716/1716/1skip. STEP 2 (web) → moved to Chunk B (user decision 2026-06-29): the connection-token model needs a cranelisp connection-handle interface (FIXME 0465) that co-designs with the slice-5 server demo. **/review ACCEPT-WITH-FIXES (no Blockers): mixed manifest genuine; stdio poll leaf correct (RC/partial-read/EOF/fd-rearm verified); `poll_support` serves it (no dup); A4c baseline-under-regen confirmed+fixed. 1 Important = Chunk-B precondition: read-line token-0 no-admission vs its process-global stdin buffer — fix before concurrent reachability (§3.1 serial-discipline claim or a capacity-1 serial-stdin token).** |
| **A5 — wire + verify** | src/ | confirm single-trampoline wiring; flip Chunk-A RED→GREEN; verify `--link`-runs-with-always-linked reactor. **DONE (2026-06-29): no feature wiring left (the `concurrency-runtime` feature is deleted — single trampoline always-on); Chunk-A RED set resolved (poll-pool rows GREEN; web rows moved to Chunk B); `--link` smoke green (A4c). Full suite `cargo nextest run` = 1716/1716 passed / 1 skipped. The lazy-init `no-Poll` guard does NOT apply (eager-cheap fallback shipped; lazy-`Poll` → S97). Chunk A COMPLETE.** |

### Chunk A — COMPLETE (2026-06-29). Gate met: suite 1716/1716/1skip; all Chunk-A `/review`s ACCEPT/ACCEPT-WITH-FIXES (no Blockers).
**Delivered:** the poll-shape live-capacity substrate (A2 backend bake + A3 acquire-around-poll + RAII Permit drop-guard, unit-proven incl. the A→C drop-release); the **single-ABI v8 + single-trampoline cutover** (A4c — the user-directed streamline: one manifest/macro/loader/trampoline, both features retired, ~30 cfg sites + 3 nextest lanes collapsed, all 9 platforms migrated, eager-cheap reactor); **stdio as a real mixed v8 platform** (`print` blocking + `read_line` poll in one manifest — the "simple platform ports cleanly" proof); capacity-N parking proven via the `poll-pool` fixture. FIXMEs resolved+deleted: 0461, 0463, 0464.
**Carried to Chunk B:** the web poll rewrite + **FIXME 0465** (web connection-handle cranelisp interface — co-designs with the slice-5 server demo) + the deferred web e2e rows (§3A/§3C-web) + Gap G4 (port-param fixture); the read-line-concurrency precondition (token-0 vs process-global stdin buffer).
**Carried to Chunk C:** the 2 A3-review prerequisites (active fd-interest deregistration on `EffectPoll` drop; `Drop for AcquirePermit` / pop-until-live release — both bite under cancellation volume).
**Carried to S97:** lazy-`Poll` reactor init (perf-only; eager-cheap is the sound permanent state).
**Process notes:** A4c `/review` inspected diffs but didn't run the `public_api_relocations` guard against the working tree → missed an under-regenerated intrinsics baseline (A4d caught+fixed) — *reviews must run the guard tests, not just read diffs*. /qa-flag (timing-window recalibration in `concurrency_poll_capacity.rs`) + the `ensure_platform_cdylibs_built()` neutralization await /qa ratification.

**S96-LANDABILITY VERDICT (honest).** **Still landable in S96 as the Chunk-A
foundation, but A4c is now the single largest wave of the sprint** — it adds the
executor/feature-gate topology (the `drive_io` collapse, the lazy-`Poll` refactor, the
two-feature retirement across ~56 cfg sites, the whole-test-suite lane collapse, +
intrinsics' public-api churn) on TOP of the §6.8.0 platform-ABI blast radius (9
platforms, 2→1 macro/manifest/loader, ABI 7→8). The added risk from collapsing the
trampoline is real and named: the dual-path was **load-bearing for the lean default
AND for the entire feature-off test lane** — deleting it means (1) every default-lane
test now drives the lazy reactor (a behaviour change to ~the whole suite, mitigated by
lazy init being result-equivalent for blocking trees — the async stepper forces them
synchronously), and (2) the lazy-`Poll` soundness (no lost-wake) is now on the default
path, not a gated lane. Net architecture is a **subtraction** (one trampoline, no
features, less `#[cfg]`), which is why it is worth doing in one jump — but the
mechanical breadth is the cost. **Discipline (reinforced):** land the loader-single-
path + unified-`PlatformFn` field-order + **lazy-init runtime guard** RED first; land
the collapse green BEFORE the lazy-`Poll` step; review the public-api diffs (both
platform + intrinsics) + the test-lane collapse explicitly. If A4c's budget strains,
the lazy-`Poll` step takes the "always-construct-but-cheap" fallback (still in-sprint,
no interim) and the perf-refinement lazy-`Poll` carries to A5/S97 — the feature
deletion + trampoline collapse themselves do NOT spill.

### Chunk partition (3 chunks, dependency-ordered A → B → C)

Each chunk is independently witnessable and gates separately at Phases 3/5. Source-touching
work still runs **serially** (worktree isolation broken) — the partition is the *review +
acceptance* unit, not a parallelism license.

**Chunk A — Platform v7 model + poll-shape live capacity (the substrate-adoption keystone).**
- **Items:** 1 (web + stdio v7 rewrites), 2 (poll_support suite), 3 (poll-shape live capacity
  + acquire-around-poll).
- **Crates/specs:** `cranelisp-platform` (gated poll_support module; macro convergence),
  `exemplar/platforms/web`, the `stdio` platform, `cranelisp-intrinsics` (§8.1 acquire-
  around-poll + the **RAII `Permit` drop-guard**), `cranelisp-backend` (poll-node live
  `(token, capacity)` bake), `design/int/reactor.md`, `design/platform/*` (0461 drains here),
  `design/backend/io-trampoline.md`. **Spec: none new** (substrate is language-invisible per
  0447's S94 re-affirmation). **Docs: 0462** worked example lands once the web rewrite exists.
- **Depends on:** S95 as-built only. No dependency on B or C.
- **Gates:** **(a)** and **(c)** are this chunk's review focus (acquire-around-poll deadlock-
  freedom + RAII Permit; macro `_neg` guard green).
- **Witnessable:** poll `accept`/`read` leaves suspend/resume on the reactor; web serves a
  roundtrip under the existing **serial** serve loop; poll-shape capacity-N — N overlap, the
  (N+1)th parks (the poll analogue of S95's blocking-carrier test); `_neg` green; no public-
  api/ABI change. (The full "server-with-no-`spawn`" is NOT complete here — that is B.)

**Chunk B — Launch-and-continue + supervisor + backpressure (the fan-out / control-flow
chunk; the reference-workload headline).**
- **Items:** 5 (launch-and-continue + supervisor), 4 (backpressure / 0442) — **co-landed**
  (gate (b): supervisor is co-requisite with launch-and-continue, and fan-out must be bounded
  by admission, §14 step 4).
- **Crates/specs:** `cranelisp-intrinsics` (detached-strand spawn + supervisor `JoinSet` +
  global admission `Semaphore` + `min(capacity, degree)` on §8.1), `src/` int (reactor-
  construction params: degree knob + supervisor-policy config + feature-gating),
  `design/int/reactor.md`, `effect-concurrency.md` §5/§10. **Spec: 0447 first half** — §10.12
  / §12.5 launch-and-continue (un-joined strand, TCO + observational-equivalence interaction)
  + the §12 supervisor-policy note.
- **Depends on:** **Chunk A** (the demo fans out real poll `accept`/`read` leaves; the
  supervisor wraps real handler strands; bounded fan-out needs A's acquire-around-poll).
- **Gates:** **(b)** (supervisor capture-reuse / detached lifetime) + **(d)/0442** (degree +
  global budget mechanism).
- **Witnessable:** the **"server with no `spawn`"** — accept loop fans out, many concurrent
  handlers bounded by the admission budget (saturate-not-oversaturate); a **panicking handler
  → 500 + log + drop, server lives**. THE reference-workload acceptance.

**Chunk C — Cancellation + combinator layer (the explicit control surface; most separable).**
- **Items:** 6 (slice 7 — `race`/`select`/`timeout` + structured cancellation).
- **Crates/specs:** `cranelisp-intrinsics` (new gated `race`/`select` IO node tags;
  cancellation = future-drop ⇒ Permit release; `drop_state` light-up), `cranelisp-backend`
  (combinator node codegen), `stdlib` (`timeout = race io (sleep d)` + the `.cl` combinator
  surface), `effect-concurrency.md` §9. **Spec: 0447 second half** — §12 typing + semantics
  of the in-language combinators + structured cancellation.
- **Depends on:** **Chunk A** (cancellation drops a poll future ⇒ must release its permit —
  the A→C RAII contract from gate (a)) and lightly on **Chunk B** (§9: combinators depend
  only on launch-and-continue being present). Last per §14 (fewest predecessors, not optional).
- **Gates:** the A→C **Permit-release-on-drop** contract is verified here.
- **Witnessable:** per-request **timeout** fires and cancels the loser (releasing its
  permit); `race`/`select` pick the winner; **cancel-on-disconnect** + **graceful shutdown**
  (cancel outstanding strands). No public-api/ABI change.

## Skill plans (Phase 3)

### Chunk A — design complete (2026-06-28)

All four invocations landed; design docs mutually consistent on the cross-crate offsets.

- **`/design` platform** — new `design/platform/poll-support.md` (the `concurrency`-gated `poll_support` suite: `PollEnv` typed env accessor, `Reactor` fd/timer scaffold, `PollState`/`drive` phase scaffold — extraction-target framed, evidence-first per Principle 8). web `accept` mints a FRESH connection token (`read`/`send` ride it → the gate-(a) non-re-entry property, stated normatively); stdio `print` stays v6 blocking, `read_line` the first poll candidate. **Macro convergence honors gate (c)**: two `macro_rules!` arms (v6 `declare_platform!` + gated v7) delegating to a shared `@spine` helper taking only shape-neutral tokens (~85 mirrored lines retired); v7 type names confined to the gated arm; `_neg` guard named as the review gate. **FIXME 0461 drained + deleted** (`platform.md`/`platform-dlls.md` reconciled to ABI v7 + the capacity carrier).
- **`/design` backend** — `design/backend/io-trampoline.md §14`: the poll-node live `(token, capacity)` bake replaces the S95 sentinel `iconst` stores with live operand Values at the reserved offsets (token @ `field_offset(1)`=abs 32, capacity @ `field_offset(2)`=abs 40). Construction-time bake (not first-poll narrowing) because acquire-around-poll needs the values on the node before establish. Both fields `NeverHeap` scalars (no RC), no alloc change, no new node field, no `cranelisp-types` touch, no ABI bump, byte-identical-off.
- **`/design` int (reactor)** — `design/int/reactor.md §2.9`: acquire-around-poll lifecycle + **RAII `Permit` drop-guard**. The `Permit` moves into the `EffectPoll` as `permit: Option<Permit>`; eager `take()`-release on `Poll::Ready`, auto drop-glue release on future-drop (cancel/timeout/race-lost) — two mutually-exclusive paths, no double-release, "released exactly once" made *representable* via the `Option` (Principle 20). The A→C contract: Chunk A builds the drop-release path, Chunk C exercises it. The S95 branch-level no-op acquire is removed; the single admission gate moves down to leaf establishment (the structural owner the drop contract requires). §2.8 lock-free single-reactor-thread permit-map holds verbatim for the poll carrier.
- **`/qa`** — `tests/plan/sprint-96.md` (~28 RED-first Chunk-A rows): poll-shape live capacity (poll analogues of S95's blocking rows — capacity-N park, capacity-1 serial+ordered, distinct/shared token, first-writer-wins + `TokenCapacityMismatch`); the load-bearing A→C drop-release row (`dropping_inflight_poll_releases_permit_next_waiter_proceeds`); web serial roundtrip via poll `accept`/`read`; stdio `read_line` + `print`-stays-blocking; `poll_support` suite; the macro `_neg` gate (existing + a new direct macro-expansion `_neg`); regression guards. **Fixture note (G1):** Chunk A needs a poll-shape `poll-pool` test leaf (S95's `pool-demo` was blocking) — authored WITH the Phase-5 /dev wave (it uses the live poll-node carrier), not in the QA-first wave.

### Phase-3 exit-gate seam → /arch arbitration — RESOLVED (`/arch`, 2026-06-28)

**Ruling: the uniform leading-pair operand convention is CONFIRMED.** It is the correct
seam *and* the only one consistent with the Phase-2 no-`cranelisp-types`-touch ruling. The
rejected per-leaf `resource_arity` field on `DefKind::PlatformEffect` is denied — it requires
a forbidden `cranelisp-types` edge touch and would re-introduce a second node discriminator
where `poll_shape: bool` suffices.

**1. Operand order at the poll-leaf call boundary (the in-process convention).** The
poll-shape lowering supplies, in order:

```
arg_vals = [ token, capacity, resource_handle (= leaf_0), leaf_1, leaf_2, ... ]
             arg_vals[0]  arg_vals[1]  └──────────── arg_vals[2..] = leaf args ────────────┘
```

- `arg_vals[0]` = **token** → baked to node `field_offset(1)` (abs 32).
- `arg_vals[1]` = **capacity** → baked to node `field_offset(2)` (abs 40), **node-only**
  (admission metadata; the poll-fn does not see it).
- `arg_vals[2..]` = **leaf args** → marshaled into the state-closure env at `capture(1+i)`;
  the **result slot stays at `capture(0)` (`state+0`)**, undisturbed.
- The **resource handle IS re-passed as `leaf_0`** (`arg_vals[2]` → `capture(1)`), so the
  poll-fn still finds its fd in the env at **`state+8`** (`PollEnv::arg(0)`,
  poll-support.md §2.1) — env layout unchanged from S94/S95; the leading-pair peel does not
  shift any arg the poll-fn relies on. CONFIRMED.

**2. `poll_shape: bool` stays the SOLE discriminator; tokenless leaves pass `(0, 1)`
constants.** The backend always peels `arg_vals[0]`/`arg_vals[1]` and bakes by one uniform
path — no "tokened vs tokenless" branch, no per-leaf arity field. A tokenless poll leaf (bare
timer, no resource) supplies the leading pair as the explicit constants `(0, 1)` → `token = 0`
(no-acquire / unrestricted) and `capacity = 1` (serial): the **S95 sentinel behaviour
preserved by value, not by special-case**. CONFIRMED.

**3. ZERO public-API / ABI surface — Phase-3 interface set is now COMPLETE for Chunk A.**
This is an in-process **backend (bake) ↔ intrinsics/int (reactor read) ↔ platform (poll-leaf
lowering)** convention only — the node offsets (32/40) frozen at the S95 reservation, the
operand positions agreed here. **No `cranelisp-types` touch** (no `resource_arity`/`cardinality`
field; `poll_shape: bool` is the discriminator; `(token, capacity)` are ordinary i64 operands);
**no `cranelisp-platform` `public-api.txt` touch** (the lowering is `concurrency`-gated, off the
default edge); **no `ABI_VERSION` bump** (the poll-node layout is unchanged from S95 — same
48-byte 3-field shape; only the *values stored* change). The `_neg`/frozen-edge guard stays
green. CONFIRMED. **The Phase-3 cross-crate interface set for Chunk A is closed — /dev may
implement against the three /design docs as written** (io-trampoline.md §14, reactor.md §2.9,
poll-support.md §2.1/§3.3); they are mutually consistent on offsets, operand order, and the
re-passed-handle env contract.

> No `design/arch/**` manifestation site is warranted: with ZERO public-API/ABI surface the
> convention sits below the facade/BC layer (an in-process codegen↔reactor convention, not a
> cross-crate type or contract). Its durable home is the three /design docs; this SPRINT.md
> ruling is the authority they cite. (Convention ruling only — no code, no build.)

## Waves (Phase 4)

### Chunk A — waves (source-touching work runs SERIALLY; waves express dependency order, not a parallelism license)

Dependency order: the backend bake provides live `(token, capacity)` on the poll node → intrinsics reads them for acquire-around-poll → the platform poll-leaf lowering rides the leading-pair operand convention (backend) → wire + verify. The poll-pool test-leaf fixture lands WITH the platform wave (it uses the live carrier). Each implementing wave = `/dev` (design is fresh from Phase 3 — `/design` refine folded in only if /dev hits a problem) → `/review` (change-set against design intent).

| Wave | Surface | Task | Status |
|---|---|---|---|
| **A1 — QA-first** | tests/ | `/qa` writes the ~28 Chunk-A rows (`tests/plan/sprint-96.md`) as failing-not-ignored. e2e rows referencing the poll-pool fixture compile + run RED until the carrier + fixture land (A4). | done |
| **A2 — Backend bake** | cranelisp-backend | `/dev`: `compile_poll_effect` stores live `arg_vals[0]`/`arg_vals[1]` (token @ `field_offset(1)`=32, capacity @ `field_offset(2)`=40) replacing the S95 `iconst` sentinels; marshal `arg_vals[2..]` as leaf captures per the leading-pair convention. Byte-identical-off. `/review`. | **done** (A2 review folded into A2b/A3) |
| **A2b — async-demo leaf leading-pair migration** | cranelisp-backend (injection is a compile-time MonoExpr pass, not platform-Rust) | `/dev`: ✅ added `inject_poll_leading_pair` production-only `MonoExpr` pass in `compile_to_module_impl` — prepends `(0,1)` sentinel ahead of natural leaf args for poll-shape `Apply`s. 5 reactor rows GREEN; 4 poll-pool rows RED (A4-blocked); default `nt` 1702/0/1; backend `-p` 281/0 (+2 units). Filed **FIXME 0463** (/design — reconcile poll-support.md ownership wording; A4 must REPLACE this pass with live derivation). `/review` (A2+A2b operand convention end-to-end) **ACCEPT** — no blockers; predicate single-sourced (no mirror drift), missing-injection fails loud, seam-level units present. | **done** |
| **A3 — Intrinsics acquire-around-poll** | cranelisp-intrinsics | `/dev`: add `permit: Option<Permit>` to `EffectPoll`; move the live-`(token,capacity)` acquire into `await_poll_node` (single admission gate at establish); eager `take()`-release on `Poll::Ready` + auto drop-glue release on future-drop (the A→C contract); delete the S95 branch-level no-op acquire. Author A3 co-landing units (§1A, §1E, §2A, §2B drop-release, §2C). `/review`. | **done** — 10 units green; `nt-concurrency-runtime` 190/0; default `nt` 1702/0/1; 4 poll-pool rows RED as expected. `/review` **ACCEPT** (no Chunk-A blockers; "released exactly once" proven all paths; §2B airtight; §2B `_neg` reframing Chunk-A-acceptable). **Surfaced 2 Chunk-C prerequisites** (see below). |
| **A4 — Platform poll_support + web/stdio rewrite + fixture** | cranelisp-platform, exemplar | `/dev`: hand-rewrite stdio `read_line` (first poll leaf; `print` stays v6) → web `accept`/`read`/`send` over a fresh connection token → extract the `concurrency`-gated `poll_support` suite from the evidence → macro convergence (two-arm + `@spine` helper, `_neg` green). Author the **poll-pool test leaf** (Gap G1; add to `build-link-prereqs.sh`) — flips the 4 A1 poll-capacity rows green. (The `async-demo` leaf migration moved to A2b.) **Co-land the deferred web e2e rows** (§3A/§3C-web — needs a **port-parametrized** poll-shape web fixture, Gap G4: the exemplar hard-codes 8080 which collides in shared lanes). Author the A4 co-landing units. | **PARTIAL — 3 of 6 steps landed; steps 1/3/5 WALLED on FIXME 0464 (→/arch).** Landed: step 0 (backend `scheduling_class`-keyed injection, subsumes A2b; +fixed a latent drop-glue offset bug in `compile_poll_effect` for ResourceSerial leaves), step 2 (`poll-pool` G1 test leaf → 4 `concurrency_poll_capacity.rs` rows GREEN), step 4 (`poll_support` extraction `PollEnv`/`Reactor`/`PollState` + `poll-pool` refactored onto it + §4A/§4B units). **0464 RULED (/arch, 2026-06-29 — see "FIXME 0464 ruling" above):** step 3 (web) is **UNWALLED — proceeds as PURE-v7** (concurrency-host-only, `declare_concurrent_platform!` only ⇒ no GOT collision, either/or loader suffices; `/qa` migrates `tests/exemplar_web.rs` to the `concurrency-runtime` lane); step 1 (stdio `read_line` poll) is **DESCOPED** (stdio stays v6 — least-load-bearing ergonomics check; the real poll-platform proof rides web + `poll-pool` + `async-demo`); step 5 (macro convergence) stays optional/deferred (natural co-resolution of the deferred merge mechanism = option (a)). Counts: 4 poll-pool GREEN, 5 reactor GREEN, default `nt` 1702/0/1, `nt-concurrency` 340/0, `nt-concurrency-runtime` 190/0, `_neg` green. **/qa flag:** /dev edited `tests/concurrency_poll_capacity.rs` timing windows (D_MS 60→150, exit 180→194) for the poll carrier's ~30ms reactor overhead — needs /qa ratification. |
| **A5 — Wire + verify** | src/ | `/dev`: confirm `concurrency-runtime` feature wiring; run the suite; flip Chunk-A RED→GREEN; verify byte-identical-off + `--link`-no-executor. `/review` (Chunk-A gate). | pending |

**Spill order (if long):** A5's optional checks first; the A2→A3→A4 substrate path + the A1 RED set is the non-spillable Chunk-A core.

### Chunk-C design prerequisites (surfaced by the A3 adversarial review — fold into Chunk C's /design pass, NOT standalone FIXMEs per the reviewer; crates mid-flight)

Both are latent in the S95 pool machinery A3 deliberately left unchanged — memory-safe and benign for one-shot `--run`/REPL, but they bite under Chunk C's deliberate, high-volume cancellation in a long-running server loop:
1. **(/design)** `EffectPoll`-owned reactor-registration handle whose `Drop` actively removes the `fd_waiters` entry + mio-deregisters (the literal active-deregistration the A3 §2B plan row named). Without it, a dropped-mid-flight poll that armed real fd interest leaks its waiter entry until the fd readies — bounded for one-shot, unbounded under server-loop cancellation. NOT a deadlock (the executor loop returns on the top future, not `has_waiters()`).
2. **(/design)** `Drop for AcquirePermit` (or pop-until-live on release): a future cancelled *while parked awaiting a permit* leaves a stale waker in the FIFO; a later release pops+wakes the dead waiter (no-op) while the next live waiter is never woken → lost-wakeup / unclaimable free permit.

Minor (fold into A4/A5 or Chunk C): downgrade `pub struct EffectPoll` → `pub(crate)` (its only ctor is already `pub(crate)`); the A3 `_neg` test name still says `deregisters_reactor_interest` though it now asserts released-exactly-once (/qa rename).

## Chunk A reviews

### A2+A2b review (cranelisp-backend) — 2026-06-29, `/review`

**Verdict: ACCEPT.** The poll-shape leading-pair operand convention is implemented correctly and coherently against `io-trampoline.md §14` and the /arch RESOLVED ruling. No Blockers. No source-targeting Important findings. Two Suggestions + one e2e-coverage observation (below). A3 may build on the baked node.

**Scope confirmed:** change-set touches `cranelisp-backend` only (`apply.rs`, `lib.rs`, `poll_codegen_tests.rs`). No `cranelisp-types` touch, no `public-api.txt` (so no ABI/baseline obligation), no `#[cfg]`. `inject_poll_leading_pair` is a private `fn` (crate-root, visible to the descendant test module via `crate::` — no `pub` leak). Concern #6 (no types touch / no ABI bump) CONFIRMED.

**1. Production-vs-unit path divergence (the load-bearing concern) — ADEQUATELY GUARDED.** The prompt's worry ("fix guarded only by e2e is incomplete") does **not** hold here: the dev added a *direct seam-level unit test on the producer pass* — `inject_poll_leading_pair_prepends_tokenless_sentinel_for_poll_effect` (positive: `[55]`→`[0,1,55]`) and `inject_poll_leading_pair_leaves_blocking_effect_untouched_neg` (negative: `poll_shape:false` ⇒ identity). The pass IS unit-pinned at its own seam (satisfies `feedback_unit_test_per_fix`), keyed on the same `resolve_poll_effect_target`/`poll_shape:bool` discriminator the peel uses. Two further reasons the divergence is safe: (a) a **missing** injection is a *loud* failure, not a silent miscompile — `compile_poll_effect`'s strict peel hits its `_ =>` arm and returns `CodegenError` ("must carry the leading (token, capacity) operand pair"), never SIGSEGVs or mis-marshals; (b) because both injection and peel call the *identical* `resolve_poll_effect_target`, if injection fires the peel arm fires too (and vice-versa) — they are structurally symmetric and cannot drift (concern #4 mirror hazard CLOSED — this is a single-source-of-truth predicate, not two parallel deciders). The S59 prelude-parity class of bug needs a *silent* divergence; this divergence is fail-loud. **Residual gap (Suggestion, not Blocker):** the *wiring* — that the `for body in &mut bodies` loop in `compile_to_module_impl` actually runs the pass over the production `codegen_view` bodies that reach `compile_poll_effect` — is exercised only by the `nt-reactor-e2e` rows, not by a backend unit/integration test. Given the fail-loud property + the green e2e rows, this is acceptable for the change-set; a future thin integration test driving a poll-effect defn through the production path (not `compile_defn`) would close it. Recorded as Suggestion; no FIXME filed.

**2. Peel correctness + robustness — CORRECT.** `[token, cap, rest @ ..]` slice match; the malformed (<2 operand) arm returns `CodegenError` (NOT panic) — confirmed `apply.rs` ~960. No `.unwrap()`/`panic!` introduced in the production path (audit: panics-in-non-test-code clean). `capture(1+i)` leaf marshalling is off-by-one-correct against result-slot `capture(0)` and is pinned by `poll_env_layout_under_leading_pair_peel` (result@+32, leaf_0@+40=state+8, leaf_1@+48; peeled token/cap proven ABSENT from env). Tokenless `(0,1)` sentinel-by-value flows the same store path — pinned by `tokenless_poll_leaf_bakes_sentinel_by_value`. Live token/cap bakes pinned by `poll_node_bakes_live_token_at_field_offset_1` (777@+32, sentinel-0 NEGATED) and `...capacity...field_offset_2` (333@+40, sentinel-1 NEGATED). The `node_store_region`/`closure_store_region` split (rfind last `call `) correctly disambiguates node+32 from closure+32.

**3. Byte-identical-when-off — STRUCTURALLY SOUND.** `poll_shape:false` ⇒ `resolve_poll_effect_target` returns `None` ⇒ pass is a no-op (proven by the `_neg` unit) AND `compile_poll_effect` is unreachable (blocking arm). No `#[cfg]` — data-field selection per Principle 11. The default `nt` 1702/0/1 claim is sound: feature-off builds register no `poll_shape:true` effect, so output is identity. Note (Suggestion): the `for body in &mut bodies` walk runs on *every* production compile even feature-off (cheap O(AST) structural recursion, identity transform); negligible, no action.

**4. Root-cause / mirror / duplication (P7/P8) — CLEAN.** As above, the injection predicate and the peel predicate are the *same function* (`resolve_poll_effect_target`), not duplicated logic — the strongest possible guard against the "two sites decide poll-ness differently" hazard. No recurring-defect-class signal.

**5. Forward-compat / Principle 8 — SATISFIED.** A2b is a forward-compatible minimal step: the injection POINT (`compile_to_module_impl` MonoExpr pass) and the leading-pair convention are the stable seam; only the value SOURCE generalises in A4 (live `token`=resource handle, `capacity`=pool ceiling). FIXME 0463 captures the A4-must-SUBSUME-not-add constraint explicitly and correctly ("A4's `poll_support` lowering SUBSUMES the `(0,1)` constants... would otherwise inject `(0,1)` and clobber a real `(token,capacity)`"), targeting `/design` to reconcile `poll-support.md`'s "platform owns the injection" wording with the codegen reality. This is the right disposition — not a throwaway A4 rips out.

**Suggestions (no obligation):** (S1) add a thin production-path integration guard on the `compile_to_module_impl` injection wiring (see #1 residual); (S2) the CLIF-string assertions (`stores_const_at` matching trailing `; vN = <const>`) are brittle to a future Cranelift print-format change — acceptable as-is, noted for the next reader. Neither blocks A3.

### A3 review (cranelisp-intrinsics) — 2026-06-29, `/review`

**Verdict: ACCEPT.** The acquire-around-poll lifecycle + RAII `Permit` drop-guard is implemented correctly and coherently against `design/int/reactor.md §2.9`. The core invariant (**released exactly once**) holds on all paths — Ready, drop-before-Ready, Ready-then-drop. **No Chunk-A Blockers.** The §2B `_neg` reframing is **acceptable for Chunk A**, but it exposes **two forward-looking Important findings that are load-bearing for Chunk C** (cancellation at volume) — flagged below for `/design` + Chunk C planning, NOT fixes to A3. `cargo check -p cranelisp-intrinsics --features concurrency-runtime --tests` clean.

**Scope confirmed:** change-set touches `cranelisp-intrinsics` only (`reactor.rs`, `io.rs`, + their `tests.rs`). No `cranelisp-types`, no public-api baseline. Feature-gating verified: `pub mod reactor` is entirely under `#[cfg(feature = "concurrency-runtime")]` (lib.rs:215) ⇒ feature-off byte-identical (no `EffectPoll`/`Permit`/`TokenPool` compiled). Concern #5 CONFIRMED.

**1. No double-release / released exactly once (the core invariant) — PROVEN on every path.**
- (a) **Ready** — `drop(this.permit.take())` (reactor.rs:579) leaves the field `None`; the subsequent auto drop-glue is a no-op. No `?`, no early-return, no panic point between `take()` and `TaskPoll::Ready(value)` (the value is an already-completed i64 read at line 568). Single release.
- (b) **Drop-before-Ready** — field is `Some` ⇒ the `Option<Permit>` field's auto drop glue runs `Drop for Permit` exactly once.
- (c) **Ready-then-drop** — `take()` ⇒ `None` ⇒ field-drop no-op. Pinned by `poll_ready_then_drop_no_double_release` (capacity-1: second acquirer parks, proving exactly one credit). Solid.
- **Panic window** — if `poll_fn` panics (reactor.rs:558) the permit field is still `Some`, so unwind drops it once (no double, no leak). The only side effect is a leaked C-ABI waker on the panic path (`drop_cabi_waker` skipped) — pre-existing, panic-path only, not permit-related.
- **Re-poll after Ready** — harmless: a second poll runs `take()` on `None` ⇒ no-op. `Drop for Permit` is additionally idempotent-safe (`slots.get_mut` → `None` early-return; `token==0` inert). The `Option` is the primary guarantee (Principle 20 — released-exactly-once made representable, no boolean flag). CLEAN.

**2. The A→C drop-release contract — the §2B test is AIRTIGHT.** `dropping_inflight_poll_releases_permit_next_waiter_proceeds`: capacity-1 token genuinely exhausted (`acquire_now` takes the only permit ⇒ permits=0), waiter asserted Pending immediately *before* the drop, and the pool has exactly one slot — the ONLY credit that can flip the waiter Ready is the leaf's field-drop. No spurious-pass path (no capacity miscount, the waiter genuinely parks). The companion `dropping_inflight_poll_deregisters_reactor_interest_neg` correctly **binds** w1's permit (`_w1_permit`) so an unbound `Ready(_)` cannot mask a double-release by immediately re-crediting — exactly one waiter proceeds, w2 stays parked. This is the right test design for the no-double-release face.

**3. The §2B `_neg` reframing — ADJUDICATION: acceptable for Chunk A; Chunk C MUST add active deregistration.** The dev reframed the plan's "drop deregisters reactor interest" → "permit released exactly once; stale wake harmless," arguing the design (§2.9, lines 489–495) deliberately has **no `Drop for EffectPoll`** and the future owns no registration handle. I verified this adversarially against the reactor internals:
- **Memory-safety claim CONFIRMED.** The waker the reactor stores (`fd_waiters: HashMap<usize,(RawFd,OwnedCWaker)>`, reactor.rs:238; `timer_waiters` likewise) is the **executor task waker** (`ExecutorWaker` → `Arc<mio::Waker>`), NOT a pointer into the `EffectPoll`. A stale `turn()` fire after the future is dropped does `OwnedCWaker::wake` → `mio.wake()` → an eventfd signal that just re-polls the top future. No dangling pointer, no double-free, no UAF. Waiters are genuinely **one-shot** (`turn()` reactor.rs:360-364 `remove` + mio `deregister` + wake). The reframing is correct AND aligns the test to the as-designed §2.9 (which only requires permit-release-on-drop). **Chunk-A-correct: the test name says "deregisters reactor interest" but the future has no interest-handle to deregister by design, so "permit released exactly once" is the right invariant to assert here.**
- **BUT the literal active-deregistration the plan named is NOT vestigial — Chunk C needs it.** Trace a dropped-mid-flight `EffectPoll` that HAD armed fd interest (the real reactor path, not the noop-host unit fixtures): its `fd_waiters` entry + live `mio` registration + `OwnedCWaker` clone **persist until that fd next becomes readable** (or for the whole drive, if it never does — a timer entry self-clears at its deadline; an fd that never readies does not). It is memory-safe but it is a **within-drive resource leak** (`fd_waiters` entries + mio registrations grow unboundedly). For a one-shot `--run`/REPL drive this is bounded by drive end and benign; for **Chunk C's volume cancellation inside a long-running reactor** (the server-loop spine this sprint is building — `select`/`timeout`/`race` dropping in-flight poll futures per request, drive never ending) it accumulates without bound. *(It does NOT hang `block_on_reactor` — the loop returns on the TOP future's completion, reactor.rs:926-928, not on `has_waiters()` — so the liveness risk is leak, not deadlock.)* **Finding for `/design` (Important):** Chunk C requires an `EffectPoll`-owned reactor-registration handle whose drop actively removes the `fd_waiters`/`timer_waiters` entry + `mio` deregisters — the literal active-deregistration the plan named. The A3 reframing should be recorded in §2.9 as "Chunk A: permit-only release; active reactor-interest deregistration deferred to Chunk C (needed for volume cancellation in a long-running reactor)."

**4. Lost-wakeup / FIFO on release — sound for Chunk A; a SECOND Chunk-C cancellation hazard.** The non-cancelled release path is correct: `Drop for Permit` increments + pops the FIFO front waiter and wakes it **outside** the `slots` borrow (reactor.rs:749-765, the S2 hardening) — no re-entrant-borrow panic, no lost wake. All permit ops run on the one reactor thread (§2.8 invariant holds verbatim — `AcquirePermit::poll`, `EffectPoll::poll`'s eager take, and the field-drop are all reactor-thread events; the noop-host unit tests drive them synchronously on the test thread, which is sound for the permit-map-only assertions they make). **BUT** (adversarial, the S95-class concern): there is **no `Drop for AcquirePermit`** (confirmed — only `Drop for OwnedCWaker` and `Drop for Permit` exist). If an `AcquirePermit` is dropped **while parked** (Chunk C cancels a future that is waiting *for* a permit, before it acquires), its waker remains in `slot.waiters`. A later `Drop for Permit` does `pop_front()` (reactor.rs:761) and wakes that **stale** waker (no-op — the future is gone), while the freed permit goes unclaimed and the **next live** waiter behind it is never woken ⇒ **lost wakeup / a free permit nobody can take**. Unreachable in Chunk A (no cancellation; `await_poll_node` always runs the acquire to completion), but **Chunk C will hit it.** **Finding for `/design` (Important):** Chunk C needs either `Drop for AcquirePermit` (remove own waker from the FIFO on cancel) or pop-until-live release semantics (skip dropped/`will_wake`-stale wakers). Note both Chunk-C findings (#3 and #4) live in the **pool/acquire machinery A3 deliberately left unchanged** (§2.9 "leaves the pool machinery unchanged") — they are latent in S95 and made *live* by Chunk C cancellation, so they belong in Chunk C's design, not as an A3 rework.

**5. Feature-off + private-in-public — CLEAN.** `EffectPoll::new` correctly downgraded `pub`→`pub(crate)` (justified in-comment); the `pub(crate) Permit` appears only there and in the private `permit` field — **no private-in-public**, confirmed by clean `cargo check --tests`. (Suggestion: the `EffectPoll` *struct* is still `pub` while its only constructor is `pub(crate)`, so it is externally unconstructable dead surface — could be `pub(crate)`; facade question, no obligation, no FIXME.)

**6. Offset agreement (no drift) — CONFIRMED single-source.** int reads token @ abs 32 (`read_resource_token`/`FIELD_1_OFFSET`) and capacity @ abs 40 (`read_capacity`/`POLL_CAPACITY_ABS_OFFSET` = `FIELD_1_OFFSET+8`); the A2 backend bake writes `field_offset(1)`=32 and `field_offset(2)`=40 (apply.rs diff lines 110-135, explicitly "abs 32/40, unchanged"). Pinned cross-crate by `io-trampoline.md §13/§14` + `reactor.md §2.9` "Offsets read" table — three statements, one set of offsets, no third hardcoded site. `poll_node_token_capacity_read_live_not_sentinel` guards live-vs-sentinel on the SAME read path. No mirror/duplication (P7/P8) introduced by A3.

**Suggestions (no obligation, no FIXME):** (S1) downgrade `pub struct EffectPoll` → `pub(crate)` (see #5); (S2) the `_neg` test name `..._deregisters_reactor_interest_neg` no longer matches what it asserts (released-exactly-once, not deregistration) — a future `grep deregister` will mislead; rename or the §2.9 record (finding #3) suffices.

**Findings to file (for `/sprint` disposition):** two **Important** findings target `/design` (int reactor) for Chunk C — (#3) `EffectPoll`-owned active reactor-interest deregistration on drop; (#4) `AcquirePermit` cancellation stale-waker lost-wakeup. Both are **Chunk-C-prerequisites, not A3 reworks** — A3 is ACCEPT as a Chunk-A deliverable. Recommend folding both into Chunk C's design pass rather than filing standalone FIXMEs now (the sprint is mid-flight on these crates); recorded here as the durable trigger.

### A4c review (single-ABI cutover) — 2026-06-29, `/review`

**Verdict: ACCEPT-WITH-FIXES.** The single-ABI + single-trampoline cutover is functionally correct and well-guarded across every load-bearing seam the gate named — the public-api diffs are intentional, ABI v8 is consistent, the unified `PlatformFn` field order is single-sourced, the loader is a genuine single path, the trampoline collapse leaves one top-level dispatch, and the lazy-`Poll` deferral is justified with a sound + permanent eager-cheap fallback. **No Blockers; A4d may build on this foundation.** Two **Important** findings (facade hygiene on the now-frozen intrinsics edge; pervasive in-source doc staleness vs the deleted v7 surface) and three Suggestions, all below — fixes, not gates. `cargo check --workspace --all-targets` clean (all 9 platforms + exe-bundle compile against v8, no warnings).

**1. The 3 `public-api.txt` diffs — line-by-line, all intentional.** `cranelisp-types`: +`Poll`, +`ConcurrencyDescriptor`, +`PollFn` — the three promoted-to-core types, exactly the plan's ADD list. `cranelisp-platform`: DELETE `declare_concurrent_platform!` ✓; PROMOTE `ConcurrencyDescriptor`/`Poll`/`PollFn`/`HostCtx`/`Waker`/`WakerVTable` + the `poll_support` module ✓; `PlatformFn` loses `scheduling_class`, gains `drop_state` + `concurrency` ✓; `OwnedPlatformFnDescriptor.concurrency` now present + non-`Option` ✓; +`IO_TAG_EFFECT_POLL` ✓. No accidental leak in types/platform — every delta maps to the §6.8.0 plan, and the `unified_abi_contracts_present_dual_channel_deleted` guard (replacing the inverted `_neg`) positively pins presence of the core types AND absence of `ConcurrentPlatform*`/`concurrent_manifest_to_descriptors`/`declare_concurrent_platform`/`scheduling_class`. **The intrinsics ~100-line churn is the one real concern → finding #2.**

**2. (Important → /arch facade + /dev) Test/demo fixtures now on the PERMANENT public edge.** Ungating intrinsics' `reactor` (+`strand`) modules promoted their entire `pub` surface onto the default `crates/cranelisp-intrinsics/public-api.txt` baseline. I verified consumption adversarially: **NOTHING outside `cranelisp-intrinsics` consumes any `reactor::`/`strand::` item** — not `src/`, not the other crates, not the platforms, and `tests/` reference them only in prose comments (the async-demo `async_read_pollfn` match is the platform's *own* fn, not an import). So the whole promoted surface — and in particular the **demo-leaf fixtures `AsyncReadState`, `TimerWriteState`, `async_read_pollfn`, `timer_write_pollfn`** (reactor.rs §"Fixture demo leaves — hand-written poll-shape effects, NO `declare_platform!`") plus `EffectPoll`/`Reactor`/`join_io_leaves`/`make_cabi_waker`/`monotonic_nanos` and the `strand::*` recording surface — sits on the frozen public edge with zero external callers. A test/demo fixture on the permanent public API is debt (my skill §Public-surface drift: unjustified `pub` ⇒ Important). This is exactly the cleanup `/arch` pre-flagged ("several fixtures likely warrant a `pub(crate)` downgrade during the ungate — flagged not blocking", SPRINT §6.8.0a public-API impact). **Disposition: Important, NOT a Blocker** (consistent with /arch's own call + the green baseline being internally consistent). Recommend `/dev` downgrade the four demo-leaf fixtures (and as many of `EffectPoll`/`Reactor`/`join_io_leaves`/`make_cabi_waker`/`monotonic_nanos`/`strand::*` as have no test consumer) to `pub(crate)` and regen the baseline, before A4d ossifies them as "the way it's always been."

**3. ABI v8 + unified `PlatformFn` field order — single-sourced, consistent, guarded.** `ABI_VERSION = 8` at lib.rs:278; every functional reference is `ABI_VERSION`/`$crate::ABI_VERSION` (macro emit, manifest, loader gate, tests). The only literal `8`s are intentional pins (`tests.rs:306`, `baseline.rs` source-string check, `platform_errors` e2e expects "8"); `shapes-badabi` correctly re-pinned `STALE_ABI_VERSION = 2` (≠ 8 ⇒ `AbiVersionMismatch{expected:8, found:2}`). **No stale 7 anywhere functional.** The v8 byte layout has exactly ONE source of truth — the `#[repr(C)] struct PlatformFn` declaration: the field-order guard `platform_fn_repr_c_field_order_v8` *reads* it via `offset_of!` (derives, not mirrors), and BOTH constructors (the `declare_platform!` macro Phase-2 and the hand-rolled `shapes-badabi`) use **named-field** init (order-independent). So macro-emit / loader-read / hand-roll / guard cannot drift on field order — the P7/P8 mirror hazard the gate worried about is structurally absent.

**4. Loader single-path — correct for both shapes.** `src/platform.rs::load_platform_dll` deletes the `#[cfg]` either/or `cranelisp_concurrent_manifest` probe; the one path dlsyms `cranelisp_platform_manifest_<name>`, validates ABI, lifts via the lone `manifest_to_descriptors`. `register_platform_in_tc` derives `poll_shape = desc.concurrency.blocking == 0` with NO cfg — and since `from_scheduling_class` sets `blocking: 1` for all three blocking classes (verified scheduling.rs:155-182) while poll leaves declare `blocking: 0`, every blocking platform derives `poll_shape:false` and every poll leaf `true`. A mixed manifest (stdio `print`+`read_line`) lifts both in one pass — the 0464 wall is genuinely dissolved. `scheduling_class` derives via `nearest_scheduling_class()` (pinned by `manifest_to_descriptors_lifts_poll_shape_descriptor`).

**5. Trampoline collapse — one top-level dispatch, no hidden dual-path.** `drive_io` is now a single async body `block_on_reactor`-ing the executor; the `#[cfg]` sync/async split is gone. I traced every host entry: `src/pipeline.rs` + `src/repl.rs` → `cranelisp_run_io` → `drive_io`; `src/session_v4/lifecycle.rs` + `src/exe.rs` (`--link`) → `cranelisp_run_program` (panic.rs) → `drive_io`. The retained **sync** `run_io_trampoline` is reached ONLY from `run_blocking_branch` (the rayon worker, io.rs:406) and from nested in-tree force points (io.rs:951/961) — genuinely the worker/nested driver, **not** a second top-level trampoline. Blocking programs are behavior-preserved (a pure-blocking tree never returns `Pending`, so the first `poll` is `Ready` and `turn()` is never reached). *(Suggestion S1: the `pub use io::run_io_trampoline` re-export comment cites `src/{session_v4,pipeline}.rs`, but those now call `cranelisp_run_io` — verify the re-export still has an external consumer or drop it.)*

**6. Lazy-`Poll` deferral + eager-cheap fallback — ADJUDICATED: hazard real, deferral justified, eager-cheap SOUND + PERMANENT (not interim).** The hazard is real: with a truly-lazy mio `Poll` (built only at `register_fd`/`register_timer`), a parked `AcquirePermit` (capacity exhausted) whose releaser is a **sync-ready** leaf — one that returns `Poll::Ready` without ever registering fd interest, then drops its `Permit`, waking the parked acquire via `ExecutorWaker::wake → mio.wake()` — would target an eventfd that was never constructed ⇒ lost wake ⇒ hang. The deferral is therefore an engineering judgement, not an excuse. The shipped **eager-cheap** state genuinely avoids it: `block_on_reactor_capped` calls `Reactor::new()` unconditionally at the top of every drive (reactor.rs:889), and `Reactor::new` (reactor.rs:268-272) builds `mio::Poll::new()` + the eventfd-backed `bridge_waker` *before* the `task_waker` is even constructed — so the eventfd always exists before any park, and `mio.wake()` can never miss. Cost is ~2 syscalls (`epoll_create` + eventfd) **per program drive** (one drive per `--run`/`--link` execution, one per REPL eval) — negligible. Per Principle 8 this is a **permanently valid behaviour**, not a correctness interim: lazy-`Poll` is a pure perf refinement correctly carried to A5/S97. ACCEPT the deferral.

**7. Feature retirement — complete.** Zero remaining `#[cfg(... concurrency ...)]` *attributes* anywhere (grep of all `#[cfg` lines in crates/src/platforms/exemplar = empty for concurrency); `reactor`/`strand` are unconditional `pub mod`; mio/futures are plain deps; both feature declarations are gone from all 5 Cargo.tomls; the 3 nextest aliases collapsed into `nt`. No orphaned dead-code (the `--all-targets` check is warning-free). The formerly feature-gated tests (`io/tests.rs`, `reactor/tests.rs`, scheduling.rs `_neg`s) now run in the **default** lane — a coverage *gain*, no hole. *(This feeds finding #8.)*

**8. (Important → /dev) Pervasive in-source doc staleness vs the deleted v7 surface.** Many comments still describe shipped code as it no longer is — misleading the next reader and referencing **deleted types**: `scheduling.rs:104` ("crosses the C-ABI as raw bytes in the v7 manifest entry (`cranelisp_platform::ConcurrentPlatformFn`)" — that type is DELETED) and its "(ABI v7)"/"ABI-v7" headers on `ConcurrencyDescriptor`/`Poll`/`PollFn`; the gated-lane test comments at `scheduling.rs:276-340` ("compile out under the canonical feature-off `cargo nt`", "RUN only under `cargo nt-concurrency`") — those tests now run unconditionally and the alias is deleted; `strand.rs:149-224` still describes the module as `#[cfg(feature="concurrency")]`/"byte-identical-when-off"; `reactor.rs:44` "Gated `concurrency-runtime`: byte-identical-when-off"; the **`PlatformFn` struct doc lib.rs:440-446** still describes the removed `scheduling_class: u32` discriminant field; `shapes-badabi` lib.rs:95 "(= 6, DEF-5)". Code is correct; the comments are stale (my skill: doc-staleness against shipped code ⇒ Important). Recommend a `/dev` comment-sweep over the retired-feature + v7-type references in `cranelisp-intrinsics` + `cranelisp-types` + `cranelisp-platform`.

**9. The mid-wave /qa-file change — CORRECT, no coverage lost.** Neutralizing `ensure_platform_cdylibs_built()` to a no-op in `tests/examples.rs`+`tests/platform_errors.rs` removes a forbidden `cargo build` shell-out (tests/CLAUDE.md: "A test MUST NOT shell out to `cargo build`"). The rationale holds: the per-test build resolved `cranelisp-platform` over a different dep-subgraph than the setup script → mismatched crate disambiguator → `undefined reference` under concurrent `--link`. The artifact set is genuinely covered: `build-link-prereqs.sh` (the nextest setup-script, single owner) now builds **all 9 platforms in ONE invocation** (stdio + test-capture included) — the cutover dissolved the reason the separate `async-demo`/`concurrency`-variant invocation existed, so folding it in is a real simplification, not a paper-over. No coverage hole.

**10. Root-cause / mirror / duplication (P7/P8) — CLEAN.** No drift-prone mirror introduced: v8 field order is single-sourced (#3); `ABI_VERSION` single-sourced (#3); `poll_shape` derived at one site from the descriptor (#4). The new `poll_support` module (listed under A4d in the plan) landed here because the newly-migrated `platforms/poll-pool` consumes its `PollEnv`/`Reactor` — it is wired + used, not premature dead code; acceptable scope pull-forward. *(Suggestion S2: there are now two types named `Reactor` — `cranelisp_intrinsics::reactor::Reactor` (host event loop) vs `cranelisp_platform::poll_support::Reactor` (platform-author wake-registration wrapper); distinct crates/responsibilities, but the name overload may mislead — consider renaming the platform-side one e.g. `WakeCtx`/`PollReactor`.)*

**Findings to file (for `/sprint` disposition):** two **Important** — (#2) intrinsics demo-leaf fixtures + unused reactor/strand surface on the frozen public edge → `pub(crate)` downgrade (`/dev`, baseline regen; route facade question to `/arch`); (#8) in-source doc-staleness comment-sweep vs deleted v7 surface (`/dev`). Both are **fixes within the cutover's own crates, not gates on A4d** — A4c is ACCEPT-WITH-FIXES; A4d (web/stdio poll rewrite) may proceed on the unified ABI. Recommend `/dev` actions #2 and #8 land this sprint while the cutover is fresh (downgrading fixtures is far cheaper now than after A4d adds real `poll_support` consumers). Three Suggestions (S1 stale `run_io_trampoline` re-export comment; S2 `Reactor` name overload; no FIXME) carry no obligation.

### A4d review (stdio mixed platform + cleanups) — 2026-06-29, `/review`

**Verdict: ACCEPT-WITH-FIXES.** The headline cutover proof — a genuine MIXED v8 manifest (`print` blocking + `read-line` poll in ONE `declare_platform!`, ONE GOT export, ONE loader path) — lands correct, and the first hand-written production poll leaf consumes `poll_support` cleanly rather than hand-rolling around it. **No Blockers.** One **Important** (latent, Chunk-B precondition: the tokenless `read-line` descriptor does not structurally enforce the serial-stdin discipline its process-global buffer assumes) and three Suggestions, all below. The A4c baseline-under-regeneration claim is **REAL and verified** (see #3). Suite effectively green (see #6).

**1. The mixed manifest — GENUINE, the cutover headline proof holds.** `platforms/stdio/src/lib.rs:198-218` declares ONE `declare_platform!` carrying two effects with the per-fn EITHER/OR concurrency key (declare.rs:295-301): `print_string` uses `scheduling: SchedulingClass::Sequential` → `from_scheduling_class` → `{token:1, cardinality:1, blocking:1}` ⇒ blocking node, `nearest_scheduling_class` ⇒ Sequential (scheduling.rs:155-182, verified). `read_line_pollfn` uses `descriptor: COMMUTATIVE` = `{token:0, cardinality:0, blocking:0}` ⇒ poll node, `nearest_scheduling_class` ⇒ Commutative (scheduling.rs:201-209). Both descriptors are correct; the loader lifts both in ONE `manifest_to_descriptors` pass deriving `poll_shape = concurrency.blocking == 0` per effect (lib.rs:1587). This is genuinely one mixed manifest, not two — the byte-identical-off witness (a v6-shape blocking effect coexisting with a poll leaf) is real.

**2. The `read_line` poll leaf — correctness CONFIRMED across every axis the gate named.** (a) **Cross-poll line buffer** (`STDIN_BUF: Mutex<Vec<u8>>`, lib.rs:65) is sound for the single-reader case: a line straddling several poll wakeups accumulates across them, bytes past the first newline stay buffered for the next call, the `Mutex` guards interior mutability of the `static` (not contention). (b) **Partial-read / multi-poll** — `poll_read_line` (lib.rs:121-153) loops drain-buffered → non-blocking-read → re-check, accumulating until a `\n`; on `EWOULDBLOCK`/`EAGAIN` it `wake_on_readable(0)` + `Park`; on resume it re-drains then reads more. A split line is correct. (c) **EOF** (`n==0`) drains the remaining bytes as the final unterminated line (mirrors v6); **hard error** surfaces an empty line rather than wedging the strand. (d) **CLString result** at RC=1 base pointer via `to_raw()`, threaded carrier-agnostically (the consuming `(IO String)` continuation adopts it exactly as the v6 blocking carrier did) — dev's `CRANELISP_RC_TRACE` verification is consistent with the code shape; empty/EOF strings still allocate a non-null base so they never collide with the result-slot sentinel. (e) **fd-readiness re-armed on EVERY park** (correct per the v7 re-arm contract — a one-shot deregister would lose the wake otherwise); `Reactor` registers, never blocks, leaks no interest. The **result-slot-as-phase-sentinel** (`READ_LINE_ARMED = -1`, lib.rs:70) never collides with the `0` unstarted sentinel nor a real `CLString` base. `PollState::drive` with identical setup/resume closures is idiomatic (read attempt is idempotent) — slightly ceremonial here but correct and the prescribed pattern.

**3. (CONFIRMED) The A4c baseline-under-regeneration claim is REAL.** `crates/cranelisp-intrinsics/public-api.txt` gains +75 lines (276→351), and they are **exactly** the `reactor` (`EffectPoll`, `Reactor`, `join_io_leaves`, `make_cabi_waker`, `monotonic_nanos`) + `strand` (`StrandEvent`, `StrandId`) surface graduating from `concurrency`-gated to ungated under the cutover. The HEAD baseline (a23fed0) reflected the gated state; the cutover ungating landed in the working tree at A4a-c but the baseline was NOT regenerated, so `tests/public_api_relocations.rs` was RED in the working tree until A4d regenerated it (now green — full suite passed it). **This means the A4c review gate did not run `public_api_relocations` against the working tree** — worth a process note: the A4c finding #2 (fixtures on the frozen edge) was identified, but the stale baseline that the ungate produced was not caught as a RED test. Recommend the chunk-review checklist add "run the affected `public-api`/relocations guard" so a stale baseline surfaces at the gate, not the next wave.

**4. Fixture downgrade — CLEAN, off the public edge, zero non-test consumers.** `AsyncReadState`/`TimerWriteState`/`async_read_pollfn`/`timer_write_pollfn` are now `#[cfg(test)] pub(crate)` (reactor.rs). Adversarial consumer check: the only references outside the reactor.rs defs are `crates/cranelisp-intrinsics/src/reactor/tests.rs` (test consumers — fine) and `platforms/async-demo/src/lib.rs` (its OWN independent `pub` copy of `async_read_pollfn`, NOT an import of the reactor symbol). So zero non-test consumers; the downgrade resolves A4c finding #2 for the four demo-leaf fixtures. `EffectPoll::new` is also correctly `pub(crate)` now (keeps the `pub(crate) Permit` out of a `pub` signature — no private-in-public). Suite builds warning-free (no dead-code). NOTE: A4c finding #2 also flagged `EffectPoll`/`Reactor`/`join_io_leaves`/`make_cabi_waker`/`monotonic_nanos`/`strand::*` as candidates — these remain on the public edge (still +75 in the baseline). They are the live reactor surface (consumed in-crate by the trampoline) so the call is defensible, but if they have no cross-crate consumer the A4c #2 recommendation to downgrade them too is still open — `/sprint` to dispose.

**5. `token == 0` ⇒ no-acquire — CONFIRMED.** `read-line` is Commutative `token 0`; the backend injects the `(0,1)` leading pair (Commutative branch of `inject_poll_leading_pair`); `token == 0` ⇒ `io::await_poll_node` hands `EffectPoll` an inert permit whose drop is a no-op (reactor.rs EffectPoll doc, §2.9). The stdio leaf is permit-agnostic (never sees one). No spurious permit interaction.

**6. Suite green except one flaky e2e timeout (NOT a regression).** The single full `cargo nextest run` hit `repl_negative::repl_exits_clean_after_errors` FAIL = "child did not exit within 30s" under the heavy parallel run. Re-run in isolation it PASSES in 0.022s. It is a pipe-stdin REPL e2e that does not touch the stdio platform's `read-line` at all — a timing/resource-contention flake under full-suite load, not a regression from A4d. The dev's "1716/1716/1skip" claim is credible.

**7. Root-cause / mirror / duplication (P7/P8) — CLEAN.** stdio genuinely CONSUMES `poll_support` (`PollEnv`/`Reactor`/`PollState`/`PollStep`); the only hand-written parts (`set_stdin_nonblocking`, the `STDIN_BUF` line buffer, `take_buffered_line`/`drain_buffered_all`, the read loop) are exactly the irreducible per-platform pieces §2.4 says `poll_support` deliberately does NOT own (syscall + result meaning + buffering). As the 2nd poll-leaf consumer, `poll_support` serves it without hand-rolled offset math or vtable indirection — the evidence-first extraction is validated. No copy-paste warranting further extraction. The doc-only "sweep" framing of lib.rs/concurrency.rs is inaccurate for the cumulative working-tree diff (it contains the v8 ABI changes + `ConcurrentPlatformFn`/`Manifest` deletion from earlier A4 chunks — already covered by the A4c review #1/#3); the A4d-attributed comment edits introduce no accidental code change.

**Findings (for `/sprint` disposition):** one **Important** — (I1) `read-line`'s `Commutative token 0` descriptor takes the no-admission path, so nothing structurally enforces the "at most one in-flight `read-line`" invariant its process-global `STDIN_BUF` + globally-`O_NONBLOCK`'d fd 0 assume. Correct under Chunk A's serial serve loop (single in-flight), but at Chunk B fan-out two concurrently-admitted `read-line` strands would race on the shared buffer (line-stealing/interleaving — the `Mutex` prevents UB, not the logical race). The code comment + `poll-support.md §3.1` claim "stdin's serial discipline is a host concern" — but token 0 means the host imposes NO admission. Before `read-line` becomes concurrently reachable (Chunk B), either correct the §3.1 claim (`/design`) or give `read-line` a capacity-1 serial-stdin token (`{token:!=0, cardinality:1}`) so admission enforces it (`/dev`). **Not an A4d gate** — consistent with the ratified token-0 choice and only bites at fan-out. Three **Suggestions** (no obligation): (S1) `set_stdin_nonblocking` permanently flips inherited fd 0 to `O_NONBLOCK` process-globally and never restores it — benign for `--run`/`--link` (read-line is the sole stdin consumer, process exits) but an unrestored global fd mutation; (S2) the A4c-flagged `Reactor` name overload now has a concrete second consumer (stdio uses `poll_support::Reactor`) — the rename suggestion gains weight; (S3) add "run the affected public-api/relocations guard" to the chunk-review checklist so a stale baseline surfaces at the gate (per #3). No FIXME filed (the Important is a Chunk-B precondition for `/sprint` to schedule, not a present defect with an observable repro).

## Notes

- 2026-06-28 — **Phase 1 scope draft.** Next sprint after S95 (IO transition complete). Presented the roadmapped S96 cluster (poll-capacity + web/stdio rewrites + poll_support + slices 4/5/7, ~2 sprints of content) with a recommended split vs whole-sprint decision. **User decision: take it whole** — S96 = the full cluster (items 1–6), the production-shaped "server with no `spawn`" landing with backpressure + per-request timeouts + graceful shutdown in-sprint. Larger blast radius accepted; the server demo is the coherent spine all six items serve. Scope updated to whole; awaiting user approval to advance to Phase 2 (/arch review).
- 2026-06-28 — **Scope APPROVED (whole), advancing to Phase 2.** User: "approved, but we may need to review in chunks." Given the blast radius, /arch is asked to (1) give an overall coherence/interim-architecture/public-API verdict AND (2) partition the work into reviewable chunks with a dependency order, so Phases 3/5 gate chunk-by-chunk. Status → PHASE 2 ARCH REVIEW.
- 2026-06-28 — **Phase 2 complete: /arch SIGN-OFF WITH REVISIONS.** No Principle-8 interim risk; ZERO new public-API edges, no ABI bump, no `cranelisp-types` touch; FIXME 0442 RESOLVED + deleted (two substrate-bound mechanisms, one concept; recorded `effect-concurrency.md §5`). Four gate rulings (a)–(d) folded in; A→C RAII-Permit contract named. Work partitioned into 3 dependency-ordered chunks (A substrate → B fan-out/control → C combinators). **User: "go ahead with chunk A."** Cadence confirmed: drive sprint chunk-by-chunk (design → build+review → chunk gate), starting Chunk A. Status → PHASE 3 DESIGN (Chunk A).
- 2026-06-28 — **Chunk A Phase 5 progress.** A1 (QA-first) ✅ — 4 poll-capacity e2e rows RED on `nt-reactor-e2e`, default `nt` 1702/1/0; web rows deferred to A4 (port-hardcoded-8080 + no-true-RED-on-v6); stdio rows landed as GREEN verify-pins (poll/block indistinguishable on instant I/O). A2 (backend bake) ✅ — live `(token,capacity)` at abs 32/40, `-p` 279/0, byte-identical-off, leading-pair operand peel. **A2 surfaced a sequencing consequence:** the strict peel turned 5 `nt-reactor-e2e` rows RED (the S94 `async-demo` leaf still lowers with natural args — consumer ahead of producer). /dev correctly refused a transitional fallback (Principle 8 + §14.2, no reliable discriminator). **Decision:** inserted a small producer-side **Wave A2b** (migrate the `async-demo` leaf to the leading-pair `(0,1)`) to restore the 5 green before A3 — keeps each wave's regression signal crisp (the chunked-review payoff). Expected RED carried into A3 = just the 4 A4-fixture-blocked poll-pool rows + the 1 known cold-start intermittent.
- 2026-06-28 — **Phase 3 (Chunk A) launched.** Chunk A is language-invisible (no /spec, no public-API/types touch per Phase-2 (a)/(c) + public-API rulings). Four parallel design invocations (distinct docs, no git/build — parallel-safe): /design platform (poll_support + macro convergence + web/stdio v7 adoption; drain 0461), /design backend (poll-node live (token,capacity) bake, io-trampoline.md §13), /design int (acquire-around-poll + RAII Permit drop-guard, reactor.md), /qa (Chunk A test plan).

- 2026-06-28 — **Phase-3 exit-gate seam RESOLVED (/arch).** Poll-leaf operand-injection convention CONFIRMED as the uniform leading-pair `arg_vals = [token, capacity, resource_handle(=leaf_0), …leaf_args]`: token→field_offset(1)/abs 32, capacity→field_offset(2)/abs 40 (node-only), leaf args→env capture(1+i), result@capture(0), re-passed handle@capture(1)=poll-fn fd at state+8. `poll_shape: bool` stays sole discriminator; tokenless leaves pass `(0,1)` constants (S95 sentinel-by-value). ZERO public-API/ABI surface (no `cranelisp-types`, no platform `public-api.txt`, no `ABI_VERSION` bump). The per-leaf `resource_arity` alternative rejected (forbidden types edge). **Chunk A Phase-3 interface set CLOSED — /dev may implement.** Recorded under Skill plans; no `design/arch/**` site warranted (below the facade/BC layer).

- 2026-06-29 — **Chunk A COMPLETE + scope decision: CONTINUE to Chunk B in S96.** Suite 1716/1716/1skip. User chose to continue the control layer in-sprint (vs close-at-A or push-all-B+C). Chunk B = slice 5 (launch-and-continue + supervisor) + slice 4 (backpressure/admission budget) + the web poll rewrite + FIXME 0465 (web connection-handle interface) + the "server with no `spawn`" demo. Status → PHASE 3 DESIGN (Chunk B). Chunk C (cancellation + combinators) reassessed after B.
- 2026-06-29 — **Phase 3 (Chunk B) launched.** 4 parallel design invocations (distinct docs — parallel-safe): (1) /design platform + /port — resolve **FIXME 0465** (web `Connection` cranelisp interface: ADT shape + `accept`→connection→`read`/`send` token threading + serve-loop reshape; the keystone the server demo + slice-5 fan-out depend on); (2) /design intrinsics — slice 5 supervisor (`JoinSet` handle, detached-but-supervised, 500+log+drop, per Phase-2 gate (b)) + slice 4 backpressure (global admission `Semaphore` + `min(capacity,degree)` on the §8.1 pool, per gate (d)/0442) — verify the gates hold post-cutover; (3) /spec — FIXME 0447 first half (§10.12/§12 launch-and-continue + supervisor + degree-budget user-facing surface); (4) /qa — Chunk B test plan (server-with-no-`spawn`, panic→500-server-lives, bounded fan-out, web roundtrip + the deferred §3A/§3C-web rows + the read-line-concurrency precondition).

- 2026-06-29 — **Phase 3 (Chunk B) — 4 designs landed + consistent.** (1) **FIXME 0465 RESOLVED+deleted** (`poll-support.md §3.5`): `web/Listener [fd pool]` + `web/Connection [token capacity fd]` (token==fd ⇒ distinct connections concurrent; capacity==1 per connection; the N count-ceiling lives on the Listener, enforced by slice-4 global budget — corrected the loose §3.4.5 "capacity-N per connection" wording to arch §16-faithful); accept-conn/read-conn/send-conn poll leaves; serve-loop reshape threads the Connection; `(token,capacity)`→poll node lights up A3 acquire-around-poll; poll_support sufficient (web = 3rd consumer); ordered /port+/platform impl list. (2) **Supervisor+backpressure** (`reactor.md §2.11-2.14`): supervisor = single-thread `FuturesUnordered` owning each detached strand, `catch_unwind`+reused-S95-capture, catch+`StrandFailed`+drop, never re-raise; backpressure = `min(capacity,degree)` slot-sizing + global admission `Semaphore` on a reserved `GLOBAL_BUDGET_TOKEN`; `IO_TAG_LAUNCH` detached node; **gates (b)/(d) confirmed HOLD post-cutover**; supervisor = first volume consumer of the A3 RAII drop-path (permits free on drop). (3) **/spec 0447 first half** (§10.12.7 launch-and-continue, §10.12.4.2 admission degree, §12.7.9 supervised strands; combinator half stays open→Chunk C). (4) **/qa plan** (26 rows; server-no-spawn, panic→500-server-lives, backpressure-park, no-ferry, web rows+G4; 12 e2e/6 unit/1 conditional).
  - **Coordination gaps to close before Phase 5:** (a) **/design backend `IO_TAG_LAUNCH`** node (const+bake+independence-detection+RC sub-tree ownership transfer — the one genuinely-new codegen construct; Phase-3 pass dispatched). (b) **A3-finding-#3 pull-forward?** — supervisor panic path drops strands with armed fd interest → `fd_waiters` leak under volume; assess pull-into-Chunk-B vs defer-Chunk-C (folded into the backend design brief). (c) read-line G7 + src/ knobs (degree/SupervisorPolicy/web-500-mapping) → Phase-5 design-refine. (d) finding-#4 (`AcquirePermit` stale-waker) does NOT bite in Chunk B — strictly Chunk C.

- 2026-06-29 — **FIXME 0466 RESOLVED (/arch) — launch-and-continue AST marker landed.** Ruled + added the **dedicated** `Expr::LaunchContinue { launched: Box<Expr>, continuation: Box<Expr>, span, inferred_type }` + the codegen twin `MonoExpr::LaunchContinue { launched: Box<MonoExpr>, continuation: Box<MonoExpr>, span, ty }` to `cranelisp-types/ast.rs` + `mono_expr.rs`, mirroring the `Expr::ParBind`/`MonoExpr::ParBind` pair exactly (span+inferred_type carriage, `span()`/`inferred_type()`/`set_inferred_type()`/`ty()`/`from_expr()` arms, `free_vars_expr` arm = union over both sub-trees). **Dedicated variant over a `ParBind { detached }` discriminator** — Principle 20: structured-join (`ParBind`) and detached (`LaunchContinue`) stay representationally distinct, so the backend's marker match selects the runtime node by the variant itself and a join site can never be mis-lowered as detached (or vice versa) by construction. Field set is exactly what `io-trampoline.md §15.4/§15.3` consumes: the launched sub-tree `MonoExpr` (lowered to the `IO_TAG_LAUNCH` detached strand) + the continuation `MonoExpr` (runs without awaiting; supplies the node's `ty`). **public-API: purely additive — confirmed.** `crates/cranelisp-types/public-api.txt` regenerated (canonical `--omit blanket-impls,auto-derived-impls`): +10 `LaunchContinue` lines (5 `Expr` + 5 `MonoExpr`), zero removals. (The regen also folded in the already-uncommitted S96 single-ABI cutover — `Poll`/`ConcurrencyDescriptor`/`PollFn` now CORE per the retired `concurrency` feature; those were stale-out-of-baseline, not introduced here.) `cargo check -p cranelisp-types` clean. Ruling narrative manifested at `design/arch/interfaces.md` (the cranelisp-types companion) + the `ast.rs`/`mono_expr.rs` rustdoc; no BC/facade change (the variant is below the facade layer, an additive `Expr`/`MonoExpr` arm). Closes coordination-gap (a)'s arch half.
  - **Phase-5 producer-side direction (the marker is now consumable; emit it):**
    - **`/int` (analysis producer)** — extend the bind-chain independence analysis to **emit `Expr::LaunchContinue`** at the §10.12.7 launch shape: a non-final `do`/`bind!` statement whose **result is discarded** AND whose **resource tokens are disjoint** from the continuation's effects. **REUSE the `Par` token-disjointness core — do NOT fork it** (Principle 7); add only the discriminator "result discarded + single launched arm + continuation does not await". `launched` = the discarded effect sub-tree; `continuation` = the remaining chain. Conservative default: when not provably eligible (result used / tokens not disjoint), lower as an ordinary `Bind` (the sound fallthrough, `io-trampoline.md §15.7`). Mono pass already threads it through (`MonoExpr::from_expr` arm landed).
    - **`/design` int (`design/int/bind-chain-analysis.md`)** — design **WHEN** to emit the marker: state the eligibility predicate (the two §10.12.7 criteria), show it as the same disjointness computation that feeds `ParBind` with the added discriminator, and pin the conservative-`Bind` fallthrough. Cross-ref `io-trampoline.md §15.3` (consumer) + `reactor.md §2.11` (the detached-strand runtime) + `spec/10-io.md §10.12.7` (eligibility). Producer of the WHEN; backend `§15` is the WHAT-on-consume.
  - Backend half (`io-trampoline.md §15`: const + `compile_launch` + RC sub-tree ownership-transfer + null-guarded drop glue) is now **fully un-blocked** — the marker-match dispatch arm has its variant.

- 2026-06-29 — **Phase 3 (Chunk B) COMPLETE; Phase 5 wave plan set.** All interfaces resolved (0465 web interface, 0466 launch marker), all designs landed + consistent, /qa plan drafted. Finding #3 → Chunk C; finding #4 → Chunk C; read-line G7 → Phase-5 wave gate. **Chunk B Phase-5 waves** (source-serial; D-refine→/dev→/review per wave; the launch vertical marker→producer→node→runtime-arm + supervisor/backpressure + web rewrite + wiring → the "server with no `spawn`" demo):
  - **B1 — QA-first** (tests/): e2e rows RED-first (server-no-`spawn` fan-out; supervisor panic→500-server-lives + no-kill `_neg`; backpressure degree-park; launch no-ferry `_neg`; web roundtrip §3A/§3C-web + Gap-G4 port-param fixture). Units + fixtures (fault-injecting/saturating handler, port-param web) co-land with their /dev wave.
  - **B2 — Launch lowering** (/int analysis + cranelisp-backend): /design-int refine `bind-chain-analysis.md` (when to emit `LaunchContinue`); /dev /int emit the marker (REUSE Par disjointness); /dev backend `compile_launch` (`IO_TAG_LAUNCH` + move-out RC + null-guarded drop glue + dispatch arm + the `IO_TAG_LAUNCH=5` const).
  - **B3 — Supervisor + backpressure** (cranelisp-intrinsics): the `IO_TAG_LAUNCH` trampoline arm; supervisor (`FuturesUnordered` + `catch_unwind` + reused-capture + catch+`StrandFailed`+drop, never re-raise); backpressure (`min(capacity,degree)` + global `Semaphore` on `GLOBAL_BUDGET_TOKEN`); strand events.
  - **B4 — Web rewrite** (exemplar /port + exemplar/platforms/web /platform): `web/Listener`+`web/Connection` ADTs + `.cl` wrappers + serve-loop reshape; the v8 poll leaves (`bind-listener` blocking + `accept-conn`/`read-conn`/`send-conn` poll over `poll_support`; fd-keyed maps replace `Mutex<ServerState>`); schema regen.
  - **B5 — Wire + server demo + verify** (src/ int): degree/`SupervisorPolicy`/web-500-mapping knobs; the `(do (handle-conn) (serve))` launch site; resolve read-line G7; flip Chunk-B RED→GREEN incl. the **server-with-no-`spawn`** headline; full-suite verify.
  - **Also fold in (A4c/A4d carried Importants, while crates fresh):** the intrinsics `pub(crate)` downgrade of the remaining unused reactor/strand surface (A4c #2) + the doc-staleness sweep (A4c #8) → land in B3; the /qa ratifications (timing-window recalib; `ensure_platform_cdylibs_built` neutralization) → B1.

- 2026-06-29 — **Chunk B Phase 5 progress (B1–B3).** **B1 (QA-first)** ✅ — `tests/concurrency_fanout.rs`: 1 GREEN no-`spawn` verify-pin + 3 RED-first (detached-fault-no-abort, degree-park, launch-concurrency); ratified the A4d timing recalib + the `ensure_platform_cdylibs_built` neutralization; build-blocker found (expected — the 0466 marker left non-exhaustive matches) → B2. **B2 (launch lowering)** ✅ — restored build (11 `LaunchContinue` arms across typecheck/backend); /int analysis emits the marker (reuses Par disjointness + result-discarded witness; `bind-chain-analysis.md §3.7`); backend `compile_launch` + `IO_TAG_LAUNCH=5` const + move-out RC + null-guarded drop glue (`drop.rs`). `launch_and_continue` e2e reaches the trampoline (fails at `unknown IO tag 5` = B3). **B3 (supervisor + backpressure)** ✅ — the `IO_TAG_LAUNCH` trampoline arm (detached strand + global permit) + supervisor (`FuturesUnordered`, `catch_unwind`+reused-capture, catch+`StrandFailed`+drop, never re-raise, drive-drains-before-exit) + backpressure (`min(capacity,degree)` + global `Semaphore` on `GLOBAL_BUDGET_TOKEN`) + strand events; folded in A4c #2 (`reactor`/`strand`→`pub(crate)`, intrinsics baseline 351→276) + #8 (doc sweep). **`launch_and_continue` e2e flipped GREEN.** Suite 1723 passed / 2 failed / 1 skipped. The 2 RED = test-infra gaps (not impl — supervisor+degree+gate unit-proven): **FIXME 0467** (/qa — `degree_n_bounds` exercises a `Par` not a launch; re-author as a launch loop) + **FIXME 0468** (/platform — `poll-pool` needs a `poll-fault` leaf for the supervisor e2e). [Both /dev-filed as 0463/0464 — collided with resolved Chunk-A numbers; /sprint renumbered to 0467/0468 per the wave-gate collision rule.] Pre-existing DEF-6 `link_repeated_platform_adt_marshal` known-RED guard confirmed (ledger S86), not a regression.

- 2026-06-29 — **B4 (web rewrite)** ✅ — `web/Listener`+`web/Connection` ADTs (`web.cl`) + destructuring wrappers (`serve.cl` — split from `web.cl` to avoid a platform-load cycle; **FIXME 0469** → /design reconciles `poll-support.md §3.5.3`); the v8 web platform (one manifest: `bind-listener` blocking + `accept-conn`/`read-conn`/`send-conn` poll over `poll_support`; fd-keyed maps replace `Mutex<ServerState>`; schema regen'd); serial serve-loop reshape (TCO, fan-out-ready). **FIXME 0468 resolved** (poll-fault leaf — corrected: a `PollFn` can't `panic!` across the C-ABI → it signals via the `runtime/panic` slot). §3A web roundtrip **GREEN** + DEF-4 link repro fixed; `exemplar_web` full matrix stays GREEN (§3C-web serve-equivalence). Suite 1726 run / 1724 passing / 1 skip / 2 RED. **The 2 RED, for B5:** (1) `degree_n_bounds` (FIXME 0467 — re-author as a launch loop); (2) **`detached_faulting…` — the one real impl gap:** the supervisor catches the strand (unit-proven) but does NOT isolate the runtime-error SLOT → the detached fault bleeds into the launcher's `cranelisp_run_program` completion check (the fork-join ferry for the *detached* case = capture+clear+`StrandFailed`, NOT re-raise). The load-bearing panic→500-server-lives correctness property; e2e caught what units couldn't. → **B5 headline fix.**

- 2026-06-29 — **B5 (integration + verify)** ✅ + **revised headline diagnosis.** B4's "supervisor slot-isolation bleed" was a MISDIAGNOSIS — the B3 supervised wrapper's per-strand `take_runtime_error()` already captures+clears the slot (the launcher's slot stays clean; unit-proven). The two RED rows had two real causes, both rooted in FIXME 0467: (1) **test shape** — a flat result-discarded distinct-token bind chain lowers to `IO_TAG_PAR` (joins+ferries), not `IO_TAG_LAUNCH`; only a SINGLE discarded step per group becomes a launch (re-authored both as recursive launch loops); (2) **a real backpressure gate gap** — the executor "would hang" guard misfired when a degree-parked launcher is woken by an in-flight strand freeing the global permit *during* `supervisor.drive()`. **Fixed** (`reactor.rs`: a `woken: AtomicBool` on `ExecutorWaker`; the guard now requires `!woken` → the degree-parked launcher re-polls — the slice-4 backpressure completion) + a unit. **Both RED rows GREEN.** FIXME 0467 resolved+deleted. `degree` wired (`CRANELISP_DEGREE`, default no-throttle); `SupervisorPolicy::LogAndDrop` default (no src/-side reactor construction — it's intrinsics-owned). read-line G7 → doc-correction (FIXME 0471 /design; descriptor unchanged — a tokenless leaf can't cheaply take a serial-stdin token).
  - **THE GAP — concurrent server fan-out WALLED → FIXME 0470 (/design):** `handle-conn` is a USER FN; `classify_expr` always treats user-fn calls as `Sequential`, so `(do (handle-conn conn) (serve-loop listener))` lowers to a serial `Bind` — **the per-connection fan-out cannot trigger without interprocedural token-disjointness analysis** (knowing `handle-conn`'s effects are disjoint from the accept loop's — a real design decision). The launch+supervisor+backpressure SUBSTRATE is fully proven via direct platform effects (the synthetic launch-loop tests); the web server serves real HTTP form/solve/404; but it serves **SERIALLY** — the "concurrent requests overlap + panicking handler → 500 + server lives" half is unproven and **no acceptance row gates it**. `exemplar/main.cl` stays serial (the permanent Chunk-A baseline). /dev STOPPED at the wall (didn't improvise the interprocedural-analysis interface).

- 2026-06-29 — **CHUNK B GATE: suite GREEN — `cargo nextest run --no-fail-fast` = 1726/1726 passed / 1 skipped / 0 failed** (the 1 skip = the intentional on-demand CPU-contention benchmark; the pre-existing DEF-6 `link_repeated_platform_adt_marshal` guard now PASSES). All Chunk-B acceptance rows green (server-no-`spawn`-primitive, detached-fault-no-abort, degree-park, launch-concurrency, web HTTP roundtrip) + the Chunk-A baseline. **Chunk B delivered: the full control-layer substrate (launch-and-continue + supervisor + backpressure, proven) + the v8 web platform (real HTTP) — EXCEPT the concurrent per-connection fan-out (walled on FIXME 0470, interprocedural launch analysis).** Carried to /design: 0469 (web wrapper location), 0470 (interprocedural launch — the fan-out), 0471 (read-line §3.1 doc). Carried to Chunk C: combinator/cancellation half of 0447 + A3 findings #3/#4.

- 2026-06-29 — **Phase 3 (Chunk C) COMPLETE** (4 parallel designs + 1 reconciliation). (1) **/spec — FIXME 0447 FULLY RESOLVED + deleted** (§10.12.8 combinators `race`/`select`/`timeout`; §10.12.9 structured cancellation — resource release + no-completion-side-effect + not-a-fault; §10.12.10 reference patterns; §12.4.4 typing + the §12.4.3 cancellation carve-out; **no `cancel` primitive** — cancellation is the consequence of losing/timeout/scope-exit). (2) **/design backend (`io-trampoline.md §16`)** — **ONE** `IO_TAG_SELECT=6` list-carrier node (`race`=binary select, `timeout` derived; dynamic arity ⇒ list not inline array; no move-out/null-guard — select never detaches); **NO `cranelisp-types` AST marker** (combinators are user-written explicit calls name-matched at the builtin apply arm, the `bind` precedent — NOT inferred like Par/Launch); no public-API/ABI. (3) **/design int (`reactor.md §2.15-2.19`)** — cancellation = future-drop; race/select run branch futures on the reactor thread, winner wins, losers dropped+`StrandCancelled`; **the A3 prerequisites DESIGNED:** finding #3 = `EffectPoll` `ReactorInterest` RAII field whose Drop deregisters fd/timer interest (§2.16, discharges the §2.9 deferral); finding #4 = `Drop for AcquirePermit` (FIFO `retain`-by-id, §2.17); + `TrampolineFrame` RAII drop-guard for branch-subtree RC (§2.15.1); `sleep` tokenless timer leaf; `timeout`=`race (map Some io) (map (const None) (sleep d))`; cancel-on-disconnect=`race handler (until-disconnect conn)`; graceful shutdown via drain-to-empty vs `clear()`. (4) **/qa** — 22 rows (race/select/timeout + the load-bearing findings #3/#4 cancellation rows + cancel-on-disconnect/shutdown web rows DEFERRED-with-0470). **RECONCILIATION (/sprint):** int proposed two tags (`RACE=6`/`SELECT=7`) but delegated const values to backend → **backend's ONE `IO_TAG_SELECT=6` stands** (race=binary select); int's runtime collapses to one arm (identical semantics). No /arch needed. **Phase-3 exit gate met:** zero new public-API (in-process tag + name-matched builtins + reserved `drop_state`/RAII; no AST marker), /qa plan drafted, design docs current.

## Waves (Phase 5) — Chunk C (source-serial; D-refine→/dev→/review per wave)

| Wave | Surface | Task |
|---|---|---|
| **C1 — QA-first** | tests/ | e2e rows RED-first (race winner/loser-cancelled, select index+value, timeout fires+cancels, the findings #3/#4 cancellation rows, synthetic graceful-shutdown); units co-land with /dev; the web cancel-on-disconnect/shutdown rows DEFER with FIXME 0470. New `poll-block` never-readying cancellable leaf + fd-leak observability (Gap G10) co-land with /dev. |
| **C2 — Reactor cancellation foundations** | cranelisp-intrinsics | /dev: finding #4 `Drop for AcquirePermit` (FIFO retain-by-id) → finding #3 `ReactorInterest` RAII dereg → `StrandCancelled` event → `sleep` timer leaf → `TrampolineFrame` RAII drop-guard. (The A→C contract completion; per `reactor.md §2.16/§2.17` order.) |
| **C3 — Combinator node + runtime** | cranelisp-backend + cranelisp-intrinsics + /int+/typecheck | /dev backend: `IO_TAG_SELECT=6` const + `compile_select` + name-match `select`/`race` at the builtin apply arm (`bind` precedent) + drop glue; /dev intrinsics: the ONE `IO_TAG_SELECT` trampoline arm (race branch futures, winner wins, losers drop=cancel via C2's release paths); /int+/typecheck seed `race`/`select`/`timeout` as inline builtins (the `bind` path, existing `DefKind`). |
| **C4 — timeout/cancel/shutdown + verify** | stdlib + exemplar/platforms + src/ | /stdlib: `timeout`/`race` `.cl` derivations; /platform: the `until-disconnect` disconnect-watch poll leaf; src/: the graceful-shutdown policy knob; flip Chunk-C RED→GREEN (the non-0470-deferred rows); full-suite verify → Chunk C gate. |

**Carried to FIXME 0470 (forward or in-sprint — user deciding):** the concurrent server fan-out + the web cancel-on-disconnect/shutdown e2e rows (they need the fan-out).

### FIXME 0470 lighter-path ruling (/arch) — 2026-06-29

**Verdict: the lighter path (option 2 — inline-handler + local discarded-disjoint bind
**sub-tree** launch) is SOUND and IN-SPRINT-SIZED. Adopt it; the heavy interprocedural
option 1 STAYS DEFERRED (never needed once the handler is inlined to platform leaves).**
Full ruling at the manifestation site `design/arch/effect-concurrency.md` §4.1 + recorded
on FIXME 0470. No `cranelisp-types`/ABI/public-api touch; no /spec change (§10.12.7 already
landed Chunk B).

- **Eligibility predicate (§4.1):** E1 result-discarded (free-vars; sufficient for "no one
  awaits"); E2 value-locality (effects act only on tokens carried by values bound within
  the sub-tree, no free var shared with the continuation — derives token disjointness from
  value provenance, since runtime tokens are dynamic and the analysis sees only classes;
  also discharges cross-iteration/sibling aliasing — fresh `conn` per accept); E3 token-0
  / shared-singleton **REFUSE** (no `Commutative` token-0 nor global `Sequential` token-1;
  per-token semaphore gives exclusion-not-order across the detach boundary, so a
  shared-token sub-tree reorders observably). Opaque user-fn in an effect position ⇒ refuse
  (this is why the handler must be inlined to platform leaves). E1–E3 also tighten the
  existing single-step `LaunchContinue` arm (its `class!=Sequential && discarded` test omits
  E2/E3) — fold in as a co-landing correctness fix.
- **Par-vs-launch:** result-discarded is the first discriminator — discarded+disjoint ⇒
  `LaunchContinue` (detached, excluded from `Par`); result-used+independent+non-Sequential ⇒
  `Par` (joined); else ⇒ `Bind`. The inlined server sub-tree classifies `Sequential` (head
  is `bind`), so it is decided wholly in the `Sequential` arm — no Par-loop change needed.
- **Sizing:** no hidden depth — inlining is exactly what keeps the footprint LOCAL (effects
  become direct platform calls in the serve loop's own chain; cores `collect_bind_chain` /
  `classify_expr` / `free_vars_expr` reused). Blast radius: /int `bind_chain_analysis.rs`
  sub-tree-launch extension (~60–100 LOC + units) + /port inline `exemplar/main.cl` serve
  loop + /qa failing-first concurrent-fan-out e2e + 500-mapping row + the E1/E2/E3 unit
  matrix (incl. negatives: token-0/shared-token/value-shared/opaque-user-fn refusals).
- **Recommended fan-out wave (fold into Chunk C, source-serial D-refine→/dev→/review):**
  C-fanout — /int sub-tree launch extension (+ existing-arm E2/E3 tightening) → /port
  inline-handler serve-loop rewrite → /qa concurrent-fan-out e2e + web 500-mapping +
  cancel-on-disconnect/shutdown rows (now un-deferred) + /int unit matrix → RED→GREEN →
  full-suite verify.

- 2026-06-29 — **Chunk C Phase 5 progress.** **C1 (QA-first)** ✅ — 15 RED-first e2e (`concurrency_cancellation.rs` 11: race/select/timeout/findings-#3/#4/shutdown-core; `concurrency_fanout_web.rs` 4: concurrent-overlap, web-500, cancel-on-disconnect, graceful-shutdown — port-parametrized harness, Gap-G4 retired) + 2 new GREEN (E3 token-0 ordering pin; chunk_c no-new-edge guard); `select` re-pointed to the as-landed value-only shape; spec anchors G8 closed. Suite 1728 passed / 15 expected-RED / 1 skip; no regression. Co-landing units assigned: C2 (findings #3/#4 + `poll-block` leaf), C3 (race-node loser-drop), C-fanout (E1/E2/E3 matrix + the web fixture). **C-fanout (/int sub-tree launch + /port inline) IN PROGRESS** — the marquee.

- 2026-06-29 — **C-fanout** ✅ (inference) / ⚠ (e2e blocked on 0472). **The "server with no `spawn`" fan-out is now INFERRED** — /int §4.1 E1/E2/E3 sub-tree-launch extension (+ E2/E3 tightening of the single-step arm), 37/37 bind-chain tests; inlining the handler observably detaches the serve loop. /port inlined the handler in the fixture (`tests/fixtures/web_fanout/main.cl`; `exemplar/main.cl` kept SERIAL — no regression). The 500-mapping landed application-layer (`safe-handle` = router wrapped in `catch-runtime-error` → in-band 500, the §2.12 "handler's own catch"; the generic supervisor→web-500 bridge stays deferred, not improvised). `CRANELISP_PORT` override added to web `bind-listener` (the Gap-G4 ephemeral-port fix). graceful-shutdown web row flipped GREEN. **BLOCKER: FIXME 0472 (/backend)** — a LAUNCHED web handler whose tail leaf takes a runtime-constructed heap `Response` ADT on a real connection fd RESETS the connection (a generic launched poll-pool literal-arg sub-tree runs clean → fingerprints an `IO_TAG_LAUNCH` move-out/drop-glue RC bug: the `Response` freed before the detached `send-conn` reads it). Clean `ConnectionReset` repros: `tests/concurrency_fanout_web.rs::{web_server_fans_out…, web_handler_fault_yields_500…}`. Suite 1738 passed / 14 RED (11 cancellation C3/C4 + 3 web 0472) / 1 skip; no regression. (Overlap wall-clock witness also needs a `sleep`/timer leaf → C2/C4.) **→ /backend 0472 fix next (marquee blocker), then C2→C3→C4.**
- 2026-06-29 — **FIXME 0472 RESOLVED+deleted (marquee blocker cleared).** Root cause: `define_launch_cont_body` (`control_flow/launch.rs`) loaded the continuation's captures but — unlike `compile_lambda_body` (the documented S60 fix, lambda.rs:428-434) — **never seeded each capture's TYPE into the inner compiler's `variable_types`**. So inside the launch continuation the captured `listener` read as non-heap, `compile_consuming_arg_list` **skipped the caller-side `rc_inc`** on the recursive `serve-loop` call, the callee dec'd at scope-exit AND the closure drop-glue dec'd again → `listener` freed after iteration 1, its address reused for iteration 2's `IO_TAG_LAUNCH` node, and the recursive `(match conn …)` read a dangling tag-5 node → `runtime_panic`/`Aborted`. Deterministic with **2 sequential `/` requests**. Fix: seed capture types into `inner.variable_types` (mirror lambda.rs). Unit guard `cranelisp-backend/src/tests.rs::launch_continuation_consuming_call_on_capture_keeps_it_live` (builds `Bind(Launch,cont)`, invokes the cont closure + drop glue directly, asserts capture survives — **confirmed fails-on-revert**). E2e: `web_handler_fault_yields_500…` GREEN+stable; `web_server_fans_out…` **served assertions GREEN** (fails only the sub-ms wall-clock timing-ratio at line 230 — flaky without a real parking delay = the **C4 `sleep` follow-on**, `/qa`-owned, not the reset). Suite: 1740/1752 (11 = unimplemented C3/C4 cancellation rows; 1 = the overlap timing flake). **→ C2 next.**
- 2026-06-29 — **C2 (Reactor cancellation foundations) COMPLETE** (intrinsics-only; the A→C contract discharged). All 5 items in `cranelisp-intrinsics`, each co-landing unit test verified RED-on-revert: (1) **finding #4 `Drop for AcquirePermit`** — `TokenSlot.waiters: VecDeque<(u64,Waker)>` waiter-identity + `parked_id` + `retain`-by-id on cancel (also closed a latent push-on-every-`Pending` duplication); units `dropping_parked_acquire_removes_stale_waker_next_live_waiter_woken` + global co-cover. (2) **finding #3 `ReactorInterest` RAII** — `RegId`-tagged `fd_waiters`/`timer_waiters` + `Reactor::deregister` (mio-deregisters/tombstones) + `EffectPoll._interest: ReactorInterest` whose Drop deregisters (no hand-written `Drop for EffectPoll`); discharges the §2.9 deferral; unit `dropping_inflight_poll_deregisters_reactor_interest`. (3) **`StrandCancelled`** event + `CancelReason{RaceLost,Shutdown}` (`#[non_exhaustive]`; emitters are C3/C4). (4) **`sleep` tokenless timer leaf** (`sleep_pollfn`, intrinsics not platform export; backend lowering is C3) — unblocks the marquee overlap witness once C3 lowers it; unit parks ≈40ms. (5) **`TrampolineFrame` RAII drop-guard** — frees the **fresh** (continuation-produced) in-flight sub-tree on drop-before-finish; **scope: fresh-only deliberately** (avoids double-free vs `supervised`'s explicit `consume_io_tree`; the non-fresh moved-out branch-root RC balance is the backend-coordinated seam already in `reactor.md §2.15.1` + the C3 row — wired in C3, no new FIXME). `cargo nextest -p cranelisp-intrinsics` 207/207 (+6). Full suite **1740/12/1skip — no regression** (12 = 11 C3/C4 combinator rows still RED + 1 load-flake). No public-API/ABI change. **→ C2 /review, then C3.**
- 2026-06-29 — **C2 /review: ACCEPT-WITH-FIXES (no Blockers); fixes APPLIED.** Adversarial review confirmed both A3 hazards GENUINELY closed (not merely approached): finding #4 `parked_id` lifecycle correct on every path (cleared on acquire so no reused-id retain; replace-in-place no-dup; `retain` removes only own stale waker → `Drop for Permit` front-pop reaches a guaranteed-live waiter; witness asserts the NEGATIVE — stale flag must NOT fire); finding #3 `RegId`+`current_registrant`+`deregister` sound, null-host reg-0 inert verified (no fixture passes a non-null-non-Reactor host), `turn()` tolerates tombstones; `sleep` idempotency latch correct; `TrampolineFrame` fresh-only scope legitimate not a hidden leak. Guards: intrinsics 207/207, public-api.txt unchanged+consistent, **only new clippy = `identity_op` in a WEBDBG block (now removed)**. **Fixes applied by /sprint in-session** (mechanical debug-cruft removal, all leftover from the 0472 marquee investigation): removed WEBDBG `eprintln!`/early-return scaffolding from `panic.rs` (3 — incl. the runtime_panic block that CHANGED semantics under the env var), `io.rs` (3), and reverted the `match_codegen.rs` `emit_match_panic(scrut_val)` hack to the original no-arg `&[msg_ptr, msg_len]` call (`rc.rs:44` left — it's the legit `rc_trace` facility, not cruft; review mis-attributed). Post-fix: `cargo clippy -p cranelisp-intrinsics -p cranelisp-backend --tests` **zero warnings in either crate's src** (remaining are transitive `cranelisp-types` pre-existing); `cargo nextest -p cranelisp-intrinsics -p cranelisp-backend` **492/492** (match-failure tests green under reverted runtime_panic). **Two items folded into C3** (A3 precedent, not C2 defects): (i) **Important** — woken-then-cancelled `AcquirePermit` does not FORWARD its freed permit (Drop-for-Permit pops+wakes X, X dropped before re-poll → its `retain` is a no-op, next parked sibling not re-pinged; harmless under `join_all` which re-polls all pending, but under the supervisor `FuturesUnordered` a token-contended parked strand can strand → C3 must either confirm every combinator polling path re-polls all pending branches OR have woken-then-cancelled `AcquirePermit` forward the permit); (ii) **Low** — `current_registrant` bracket not panic-safe (stale `Some(reg)` if a poll-fn panics; harmless today, a scope-guard would harden). **→ C3 now.**
- 2026-06-29 — **C3 (Combinator node + runtime) COMPLETE.** ONE `IO_TAG_SELECT=6` Vec-carrier node (race=binary select; NO `IO_TAG_RACE`, NO move-out, NO AST marker — the `bind` name-match precedent). **Backend:** const `cranelisp-platform/src/lib.rs:349`; `compile_select`/`compile_race`/`compile_select_node` new `control_flow/select.rs` (`race a b` reuses `compile_vec_lit` → same node; race IS a backend primitive — free-standing tests import it from `primitives`); name-match `apply.rs:284/289`; drop glue `drop.rs:349` (`consume_vec_with(consume_io_tree)`, every branch freed once). **Intrinsics:** `IO_TAG_SELECT` arm `io.rs:298`→`run_select_node` (`io.rs:489`) — reads branches by raw ptr (no RC/move-out), child strand + future per branch, `futures::select_all` (re-polls ALL pending each turn), losers dropped after `StrandCancelled{RaceLost}`, winner returned. **/int+/typecheck:** `race`/`select` seeded slot-less `DefKind::PrimitiveExtern` in `primitives` (`src/bootstrap.rs:916`); schemes `race: IO a→IO a→IO a`, `select: Vec (IO a)→IO a`; existing `resolve_primitive_jit_name` maps PrimitiveExtern→BuiltinFn (no typecheck change). **Two C2-forward items DONE:** (i) permit-forwarding fixed **substrate-wide** — `Drop for AcquirePermit` (`reactor.rs:~1130`) now FORWARDS a freed permit (pop+wake next front) when its own FIFO entry was already popped, curing the `FuturesUnordered` lost-wakeup; unit `woken_then_cancelled_acquire_forwards_permit_to_next_waiter` RED-on-revert; (ii) `RegistrantGuard` RAII (`reactor.rs:574`, used `:754`) clears `current_registrant` on return AND unwind; unit `registrant_guard_clears_current_registrant_on_drop`. **Units:** `select_codegen_tests.rs` (race/select build tag-6, +neg), `consume_io_select_frees_branch_vec_and_all_branches` (RED-on-revert), the 2 reactor forward-tests, `mounts_race_select_combinators`. **Cancellation rows: 10/11 GREEN.** **1 RED = FIXME 0473** (`volume_cancellation_does_not_leak_fd_waiters_bounded`): TEST-PROGRAM token collision (`poll-read` deadline token 99 ∈ `poll-block` range 1..200; at n==99 both branches contend the same cap-1 token → never-readying `poll-block` deadlocks). Bisected: bound 98 = 0.31s, bound 100 = hang — **finding-#3 active-dereg PROVEN at volume by the bound-98 run**. Added a never-readying READABLE-fd `poll-block` leaf `platforms/poll-pool/src/lib.rs:277`. Routed **FIXME 0473 → /qa** (one-token fix: deadline token → 9999). **`timeout` + `sleep` backend lowering DEFERRED to C4** (deliberate, Principle 6: zero C3 consumers, tests use inline `(race io (poll-read…))`; `sleep` needs new non-GOT runtime-symbol resolution for the poll-node `code_ptr`; co-land with `timeout`; the C2 `sleep_pollfn` leaf+timer stay). **public-api:** `cranelisp-platform/public-api.txt` regenerated via guard (only diff = `IO_TAG_SELECT` line); baseline.rs green; no ABI bump. **Design:** `reactor.md §2.15` as-built note — landed model is io-trampoline.md §16 (no move-out), so the C2 fresh-only `TrampolineFrame` guard is correct verbatim + the "non-fresh branch-root RC" item is moot. **Full suite (excl. the 0473 hang): 1752 passed / 0 failed / 2 skipped** — 11/12 baseline failures resolved (web overlap timing flake passed this run, incidental not sleep). **→ C3 /review, then C4 (+ resolve 0473).**
- 2026-06-29 — **C3 /review: ACCEPT-WITH-FIXES (no Blockers); all follow-ups actioned.** Adversarial review rendered the three named verdicts clean: (a) select-node free-exactly-once CORRECT on the program-tree path (no-move-out list-carrier; winner Pure no-op, losers `drop(remaining)` free fresh-only via `TrampolineFrame`, whole tree freed once by the `consume_vec_with(consume_io_tree)` drop-glue arm; unit RED-on-revert); (b) permit-forward SAFE — forward fires only when `parked_id` Some AND retain found nothing, never touches `permits` (no over-increment), wakes a DIFFERENT waiter than `Drop for Permit` (no double-wake), empty-FIFO safe, mutually-exclusive with retain; witness proves the negative; `RegistrantGuard` correct; (c) FIXME 0473 CORRECTLY a test-program token collision not a masked leak (bound-98=0.31s AFFIRMS finding-#3 dereg at volume; bound-100 hang = pure n==99 deadlock). Guards: 960 unit pass, **baseline guard RUN** (the A4c lesson) = 1 pass/ABI intact, no new clippy. **Review item 1 ("no green test exercises run_select_node, sole e2e is the hanging 0473") was FACTUALLY WRONG** — the reviewer ran only the unit crates, not `tests/`; /sprint verified the e2e crate: **10 green cancellation rows incl. `select_only_winner_value_returned_losers_side_effects_absent_neg`, `select_returns_first_completed_value`, race winner/loser/permit** → `run_select_node` (winner-return AND loser-drop) is well-covered e2e; no action. **FIXME 0473 RESOLVED+deleted** by /sprint (one-token fix, fully diagnosed+review-confirmed): `volume_cancellation_does_not_leak_fd_waiters_bounded` deadline token 99→9999 (outside `1..=VOLUME_N`); the now-unblocked row passes **3.5s at full VOLUME_N=200** — finding-#3 active-deregistration proven at volume. **All 11 cancellation rows GREEN.** **Two genuinely-forward review items filed (A3 precedent, low/pre-existing, not C3 defects):** **FIXME 0474** (→/backend) fresh-continuation-produced `IO_TAG_SELECT`/`IO_TAG_PAR` node leaks its branch Vec (shallow-dec doesn't walk fields; inherited from Par, untested for both; needs /qa heap-balance repro); **FIXME 0475** (→/spec) `(select [])` returns Unit `0` = unsound null for heap-typed `a` where §10.12.8 says "never completes" (+ minor List/Vec wording). **→ C4 now.**
- 2026-06-29 — **C4 COMPLETE (sleep keystone + timeout + stdlib) — but the MARQUEE FAN-OUT GAP surfaced.** Landed: (1) **`sleep` backend lowering** — the genuinely-new non-GOT runtime-symbol `code_ptr` path: `compile_sleep` (`apply.rs`) resolves `runtime/sleep_pollfn` via `declare_function(Linkage::Import)`+`func_addr` (vs the GOT-slot path), builds tag-4 poll node, ms→ns; catalog entry 31; seed `sleep: Int→IO Int` in bootstrap; reuses C2 `sleep_pollfn`+timer. Units incl. `sleep_bakes_runtime_symbol_code_ptr_via_func_addr` (RED-on-revert) + e2e `concurrency_sleep.rs` (parks ≥200ms). (2) **`timeout` stdlib** (`stdlib/core/io.cl`: `race (map Some io) (map (const None) (sleep d))`) validated `--run` both outcomes; fixed a latent bare-`bind` import bug. (3) deterministic overlap witness — fixture `/slow` now `(sleep 100)`. (4) public-api no drift. Suite (overlap ignored): 1754/0/2skip. **THE FINDING:** the now-deterministic `web_server_fans_out_concurrent_requests_overlap` **FAILS — K=4 /slow = 441ms ≈ serial 4×110ms**: the web serve loop processes each connection to completion before accepting the next; **the launch fan-out does NOT fire/overlap for the web shape**, though the synthetic `launch_and_continue_runs_concurrently…` is GREEN (mechanism works in isolation) and the fixture handler is INLINED (so the original "interprocedural 0470" framing may be wrong). C4 agent `#[ignore]`'d the row + deferred `until-disconnect`/graceful-shutdown to 0470 + filed **FIXME 0476** (→/qa: pre-existing constructor-as-fn-value SIGSEGV surfaced by timeout, worked around — NEEDS a failing-not-ignored repro per policy) + **FIXME 0477** (→/spec: ratify sleep/timeout duration unit = ms). **USER RULING: diagnose & fix 0470 NOW** (deliver the true concurrent marquee). **Candidate causes:** (a) inference doesn't fire — `slow-delay`/`safe-handle` calls hide value-locality (genuine interprocedural 0470); (b) fires but doesn't overlap — serve-loop/web-accept runtime serialisation (a NEW defect, not 0470); (c) C4's `slow-delay` insertion broke a working inference. **Process owed:** un-ignore the overlap witness (failing-not-ignored 0470 guard); 0476 needs a failing test. **→ 0470 diagnosis-first dig (ACTIVE).**
- 2026-06-29 — **MARQUEE DELIVERED — 0470 RESOLVED+deleted. The web server genuinely fans out.** **Diagnosis = cause (c):** NOT an interprocedural wall — C4's own `slow-delay` insertion (a user fn returning IO placed in an EFFECT POSITION) broke an inference that was ALREADY FIRING for the pre-C4 handler. Ruled out (b) runtime (synthetic `concurrency_fanout` overlap green; `degree` defaults `u32::MAX` no throttle) and confirmed via a unit mirroring the serve-loop shape that `LaunchContinue` was not emitted (`is_launchable_leaf` refuses an opaque user-fn footprint per §4.1 E3). **Fix (two coordinated parts):** (A) `src/bind_chain_analysis.rs` — `is_sleep_timer_leaf`/`resolves_to_sleep_extern` admit the resource-free `sleep` timer as a sub-tree effect MEMBER (token-free + no observable side-effect ⇒ detaching reorders nothing; the right §4.1-local level, no interprocedural walk), but NOT in the single-step arm (a lone `(sleep d)` never self-detaches); (B) `tests/fixtures/web_fanout/main.cl` — `slow-delay`(returned IO)→pure `slow-ms: Fn[Request] Int` + direct `(sleep (slow-ms req))`, so every handler effect position is a direct leaf (`read-conn`/`send-conn` ResourceSerial poll + `sleep` timer) ⇒ whole `read→sleep→send` launches as ONE supervised strand, K connections fan out. **Proof:** `web_server_fans_out_concurrent_requests_overlap` UN-IGNORED + GREEN, deterministic ~110ms (1·D) not ~440ms (K·D), web suite run 3×; unit guards `test_launch_subtree_with_inlined_sleep_timer_step` (+) / `test_no_single_step_launch_for_lone_sleep_step` (−) RED-on-revert; 36 bind_chain tests pass. **The cancel-on-disconnect + graceful-shutdown web rows now GENUINELY exercise the fan-out** (real outstanding detached handler strands), not liveness-only. **Suite 1757 passed / 1 skip / 0 failed** (+1 un-ignored overlap, +2 unit guards; the 1 skip = on-demand CPU benchmark). public-api no drift (edits are binary-crate-private + tests + fixture + design). FIXME 0470 deleted; timer refinement documented in `effect-concurrency.md §4.1`. **Forward caveat filed FIXME 0478** (→/int, low/latent, no trigger): the single-step launch arm skips the E2 value-locality check (relies on §B4 per-call dynamic token); a §4.1 hardening note, not a blocker. **→ C4+0470 /review; author 0476 failing repro; then Phase 6.**
- 2026-06-29 — **C4+0470 /review: BLOCK (1 real `--link` blocker) → RESOLVED in-session; +1 doc fix.** Review verdicts: (b) timer-as-launchable-member SOUND (reorder-safe; single-step exclusion correct+pinned), (c) FIXME 0478 genuinely deferrable (not reachable by marquee/near-shape), (d) marquee witness an HONEST proof (assertion `<3.5·one`, overlap ≈1·one wide margin, 3× green) — all clean. **BLOCKER (a):** `sleep` worked `--run` (JIT catalog pointer) but FAILED `--link` — `sleep_pollfn` lacked `#[export_name]`, so `ld` saw `undefined reference to runtime/sleep_pollfn`; since stdlib `timeout` builds on `sleep`, any `--link` binary using `timeout` would break (the release-gate mode). **FIX (in-session):** added `#[unsafe(export_name = "runtime/sleep_pollfn")]` to `sleep_pollfn` (`reactor.rs`, mirroring `runtime/vec_new`/`runtime/alloc`); verified empirically — the reviewer's minimal `(bind (sleep 50) (fn [_] (Pure 7)))` now `--link`s + runs (exit 7, 54ms park). **Closed the test gap that let it through:** added `concurrency_sleep.rs::sleep_links_and_runs_through_link_mode` (`link_then_run` — links AND execs ⇒ undefined-ref-at-link OR park-fail-at-run both fail it); the e2e was `--run`-only. **Doc fix:** rewrote the stale `web_server_fans_out…` doc block (it still described the pre-fix SERIALISES/IGNORED state; now describes 0470-resolved + the green overlap guard). Sleep suite 3/3 (incl. --link). **Gate verify: full suite 1757 passed / 1 skip (CPU benchmark) / 1 FLAKE** — `repl_introspection::bare_trace_special_form_carries_type_prefix` timed out at 30.022s under full-parallel load, **passes 0.023s in isolation**. **RECURRING SYMPTOM (3× this session, different repl_introspection rows each time — C3/C4 agents + now): repl_introspection subprocess tests intermittently HANG (30s) under parallel nextest load, instant alone.** Hypothesis: possibly the single-trampoline cutover made the host reactor UNCONDITIONAL (epoll_create+eventfd per drive) → contention/lost-wake under many parallel REPL subprocesses. Flagged for decision — NOT carried as debt.
- 2026-06-29 — **Recurring hang DIAGNOSED (user ruled: diagnose now). Reactor hypothesis REFUTED — root cause is a PRE-EXISTING scheduler lost-wakeup, in THIS sprint's track.** Reproduced on demand (full-suite first-run hit a 4th distinct introspection row `syntax_topic_returns_content`@30.026s; a 48-child concurrent-spawn stress harness hit ~1 hung child per 13–88 rounds → live PID). `/proc/<tid>` wchan of the hung child: main(eval)+priority-worker+nice-worker-0 ALL parked on **futexes (scheduler condvars)**; the only `ep_poll` is the idle inotify watcher — **NO reactor thread, nothing in epoll_wait**. Pure-introspection commands never produce IO so the reactor is never reached (`repl.rs:2147`/`pipeline.rs:188` gate on `is_io()`); the S96 unconditional-reactor cutover is NOT the cause. fd-exhaustion ruled out (ulimit 524288, child held ~4 fds). The 30s = the harness `e2e.rs:145` timeout, not nextest/reactor. **Precise cause:** the per-import FQ-dependency discovery path has a two-lock window — `process_form/dependency.rs:379-380` does `register_module(dep)` (lock#1, notify_all) then `block_dep`→`block_for_typecheck` (lock#2); a priority worker can pop+typecheck+`notify_typecheck_done(dep)` BETWEEN the locks (no waiter for `module` yet), then `block_for_typecheck` (`scheduler.rs:766`) **unconditionally** registers `module` as a waiter on the now-TERMINAL `dep` and never re-checks readiness → `module` stranded in `TypecheckBlocked` forever, eval thread parks on its completion forever, both workers idle. This is the **documented S93 Invariant-PP lost-wakeup class** (`src/CLAUDE.md` §Signature-barrier; `.config/nextest.toml` NOTE: this worker-hang race "belongs to the **effect-concurrency track**" = S96): S93 closed the window for the body-boundary barrier (`block_on_first_unready_closure_member`, `scheduler.rs:1432`, atomic single-lock) but the discovery path was NOT converted. Pre-existing; surfaced (not caused) by S96. **Turnkey fix (owner /int):** make `block_for_typecheck` atomic check-and-act — under its single lock, before registering the waiter, re-check `signatures_ready_locked` (the S93 predicate); if `dep` already terminal, requeue `module` immediately (the `try_unblock_locked`/`unblock_module` path) instead of a dead waiter; production callers use the `"*"` whole-module waiter so the whole-module check suffices. **Deterministic guard (RED-on-revert):** `src/scheduler/tests.rs` unit — register `dep`, drive to `TypecheckDone`, THEN `block_for_typecheck(module, dep, "*")`, assert `module` is requeued NOT left `TypecheckBlocked`. No timeout-self-heal (would mask the repro). Stress harness retained at scratchpad `stress.py`. **→ dispatch the fix NOW (in-track, root-caused, deterministically guardable).**
- 2026-06-29 — **Scheduler lost-wakeup FIX landed (window #1 closed+guarded) — but a SECOND window remains.** `block_for_typecheck` (`src/scheduler.rs:766`) now does atomic check-and-act under ONE lock: re-checks `signatures_ready_locked(needed_module)` (the S93 predicate) for the `"*"` whole-module waiter (the sole production form) BEFORE registering; if `needed_module` already terminal → requeue `module` via `try_unblock_locked`+`notify_all` (the inlined `unblock_module` path) instead of a dead waiter; else register as before. Mirrors `block_on_first_unready_closure_member` (`:1432`). Closes the `dependency.rs` two-lock window (register_module(dep)…block_dep). **Deterministic guard:** `src/scheduler/tests.rs::block_for_typecheck_on_already_terminal_dep_requeues_not_strands` — drive `dep` to `TypecheckDone` first, then `block_for_typecheck`, assert requeued not `TypecheckBlocked`; **RED-on-revert VERIFIED** (pre-fix: stranded TypecheckBlocked; post-fix: TypecheckFirst/Next + re-drivable). Scheduler 48/48, lib 430/430, full suite **1759/1skip on clean runs (3×)**; entry-path soak `stress.py 48 120` = 5760 spawns NO hang (was ~1/13-88 rounds). public-api unchanged (binary-crate-internal). **SECOND WINDOW (reported, not patched):** full suite STILL intermittently hangs under extreme cross-binary CPU oversubscription (~2 hangs / 5 full runs). Hung REPL child wchan: eval `futex` + **a SINGLE priority-worker** `futex` + nice-worker `futex` + watcher idle `ep_poll` = a module stranded `TypecheckBlocked`, requeue trigger lost. **Distinct mechanism** — the fixed race needs ≥2 concurrent priority workers; this reproduces in the eval+ONE-worker topology, so it's a separate lost-wakeup (eval-thread drive vs the single worker, or a transitive-dep transition the `"*"`-terminal check misses). Could not pin by inspection (no gdb/lldb; ptrace_scope=1; no sudo). The S93/Invariant-PP heisenbug class is LAYERED (per `.config/nextest.toml` NOTE — effect-concurrency-track residue). **Recommended:** add SIGUSR1 scheduler-state dump (pool + per-module `blocked_on` + waiters) to the REPL binary, reproduce under full-suite monitor, pin the stranded module's dead edge, fix+guard the same way. Window #1 is durable progress; window #2 is a separate, narrower continuation. **→ DECISION: keep digging window #2 (instrument+pin) vs bank window #1 + proceed to S96 close with #2 tracked.**
- 2026-06-29 — **Window #2 PINNED+FIXED+GUARDED (user ruled: keep digging). The S93-class scheduler heisenbug is CLOSED (2 windows).** **SIGUSR1 instrumentation (durable, in-tree):** new `src/sched_dump.rs` + `CompileScheduler::dump_state_to_string()`, armed via `sched_dump::arm_if_enabled` in `session_v4/lifecycle.rs::new`, gated on `CRANELISP_SCHED_DUMP_ON_SIGUSR1` (zero cost unset — no handler/thread; suite unaffected). Async-signal-safe: handler does only an atomic store; a `sched-dump-watchdog` thread takes the lock + dumps every module's pool/`blocked_on`/inmem+object flags/waiters/queues + a LOST-WAKEUP-SUSPECT flag. **The PIN (soak round 181 / ~11.6k spawns, 64-way):** stranded module = `user` (entry), `TypecheckDone`, `inmem_done=true` but `object_done=false`/`object_working=false`, sitting in `typecheck_done` queue; nice-worker parked. **Lost transition:** `notify_typecheck_done(user)` (`scheduler.rs:866`) pushes to `typecheck_done` + fires `object_work_available.notify_all()` (`:933`) under the state lock, but it lands in the GAP between the nice-worker loop's TWO separate lock acquisitions (`nice_worker.rs:82` `try_take_object_codegen`→None, then `:114` `park_nice_worker`) — the S91 index-interleave; no waiter parked yet → notify lost → nice worker waits forever → `user.object_done` never set → eval/main hangs in `wait_object_complete()` (`main.rs:456`, REPL `.o` cache-persist). **Distinct from window #1:** different condvar (`object_work_available` vs `priority_work_available`), different worker class (nice/object-codegen vs priority/typecheck), single-worker topology. **Fix:** `park_nice_worker` re-checks `has_pending_object_work_locked(&state)` (new shared predicate = the exact `try_take_object_codegen` scan, Principle 7) UNDER THE SAME LOCK before `wait` — scan-sees-work OR notify-after-wait, no gap. Mirrors window #1 / `block_on_first_unready_closure_member`. No timeout self-heal. **Guard:** `src/scheduler/tests.rs::park_nice_worker_does_not_strand_pending_object_codegen` (drive to TypecheckDone+notify-fired, assert park returns promptly via spawned-thread+recv_timeout so a revert fails cleanly not hangs); **RED-on-revert VERIFIED both directions** (revert→"STRANDED…lost wakeup (window #2)"@2s; restore→PASS 0.003s). **Verify:** scheduler 49/49, binary lib + public_api_relocations green, no clippy; **full suite 5/5 CLEAN (1760 passed/1 skip, ~47s, no slowdown)**; **soak 500 rounds × 64 = 32,000 spawns CLEAN** (past the round-181 repro); residual hang rate 0. **No THIRD window observed** (can't prove zero for an intermittent class, but the SIGUSR1 dump pins any future one in one shot). public-api unchanged (binary-crate-internal). **→ S96 close-out: 0476 repro → Phase 6 → Phase 7.**
- 2026-06-29 — **FIXME 0476 RESOLVED → failing-not-ignored guard (the test replaces the FIXME, per `feedback_no_fixme_with_failing_test`).** Confirmed the defect: `(apply-it Some 7)` (a bare ADT constructor escaping as a fn-VALUE, applied indirectly) **SIGSEGVs (exit 139)**; the lambda-wrapped control `(apply-it (fn [y] (Some y)) 7)` exits 7. Pre-existing codegen defect (the `fn_as_value` constructor-wrapper / auto-curry arm for a `DefKind::Constructor` reaching codegen as a value), surfaced not caused by C4's `timeout`. Authored 2 guards in `tests/regression.rs`: `constructor_as_fn_value_applied_indirectly_does_not_segfault` (asserts the CORRECT exit 7 → currently FAILS "expected 7 got None" [SIGSEGV by signal] = failing-not-ignored known-defect guard, flips green when /backend fixes; `// spec: spec/06-adt.md §6` + `FIXME(/backend)` naming the resolver) + `constructor_wrapped_in_lambda_applied_indirectly_works` (positive companion, PASSES — pins the defect is specifically the bare-constructor-as-value path). FIXME 0476 file deleted. **This adds 1 intentional known-defect RED to the suite** (consistent with the project's existing failing-not-ignored guards) — a /backend resolver target, not a regression.

## Outcome (Phase 7)

{Pending close.}
