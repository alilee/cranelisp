//! Sprint 96 — effect-concurrency Chunk B: launch-and-continue + supervisor +
//! backpressure (the fan-out / control-flow chunk) — the QA-first (Phase-5
//! Chunk-B Stage-1, Wave-B1) e2e acceptance rows.
//!
//! Plan: `tests/plan/sprint-96.md` (CHUNK B) §B1 / §B2-syn / §B3-syn / §B4.
//! Contract of record: `design/arch/effect-concurrency.md` §4 (launch-and-
//! continue is *inferable* — a result-discarded, token-disjoint effect may be
//! launched and not joined; the accept loop fans out automatically, TCO'd) / §5
//! (the *degree* program-throttle, `effective permits = min(capacity, degree)`) /
//! §10 (supervisor semantics — 500 + log + drop, never a whole-server abort) /
//! §16 (the worked pure-side server sketch). `design/int/reactor.md` §5 (the
//! backpressure / supervisor forward-looking seams). Spec of record:
//!   - `spec/10-io.md` §10.12.7  (Launch-and-Continue / Detached Effects)
//!   - `spec/10-io.md` §10.12.4.2 (Admission Degree — Program-Chosen Throttle)
//!   - `spec/12-runtime.md` §12.7.9 (Supervised Detached Strands)
//!
//! ## Lane (post-cutover)
//!
//! The single-ABI / single-trampoline cutover (S96, `Cargo.toml` §6.8.0a) RETIRED
//! the `concurrency` / `concurrency-runtime` features: the host reactor is now
//! UNCONDITIONAL (lazy-init — a pure-blocking program constructs no `mio` Poll at
//! runtime). So there is ONE collapsed test lane — `cargo nextest run` — and this
//! file is **un-gated** (no `#![cfg(feature = …)]`); it runs in the default lane.
//!
//! ## Posture (Wave-B1 = QA-first, the synthetic RED-first acceptance rows)
//!
//! These are **failing-not-ignored** acceptance guards
//! (`memory/feedback_failing_not_ignored`). Per the Chunk-A precedent, Wave-B1
//! authors ONLY the black-box e2e rows that compile as Rust and run RED today
//! because the *capability* (launch-and-continue lowering / supervisor / admission
//! degree) or a *fixture leaf* is not wired yet. They flip GREEN as the Chunk-B
//! /dev waves land. The unit rows (supervisor `JoinSet`, `min(capacity, degree)`
//! composition, the no-ferry semantics) + the web rows (the FIXME-0465 connection-
//! handle interface + the Gap-G4 port-parametrized fixture) **co-land** with their
//! /dev crate waves — writing them now would reference types/programs absent on
//! HEAD and break the workspace build (`tests/plan/sprint-96.md` §B9).
//!
//! ## The extended `poll-pool` fixture (Gap G6 — Chunk-B /dev deliverable)
//!
//! Chunk A landed `platforms/poll-pool/` (`poll-read` / `poll-write` / `poll-log`,
//! poll-shape capacity leaves). Chunk B's §B2-syn needs ONE more leaf — a
//! `poll-fault` poll-shape leaf that deliberately FAULTS (panics / returns a
//! runtime error) so the supervisor's "catch + drop, loop lives" policy is
//! witnessable without any web/HTTP machinery. It does NOT exist on HEAD, so the
//! §B2-syn row references it via the const below; an absent effect is a clean
//! runtime-RED (the binary errors at load), NOT a compile break (e2e shell out to
//! the `cranelisp` binary). It is authored WITH the /dev supervisor wave + added
//! to `tests/scripts/build-link-prereqs.sh`. §B3-syn / §B4 reuse the EXISTING
//! `poll-read` / `poll-log` leaves — their RED-now is the missing *capability*
//! (admission degree / launch-and-continue lowering), not a missing leaf.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, CrOutput};

// =============================================================================
// Tuning — matches the poll-carrier calibration in `concurrency_poll_capacity.rs`
// (the S96 A4 recalibration: D=150 absorbs the poll carrier's ~30 ms fixed
// reactor overhead while keeping the regimes a generous 150 ms apart).
// =============================================================================

/// Per-effect delay (ms). Matches `concurrency_poll_capacity.rs::D_MS`.
const D_MS: u64 = 150;

/// Best-of-N minimum for a wall-clock witness — contention can only make a
/// measurement SLOWER, never faster, so the minimum filters scheduler noise and
/// reflects the genuine overlap / parking / serialisation behaviour.
const BEST_OF_N: usize = 3;

// === The `poll-pool` fixture leaves ==========================================

const POLL_PLATFORM: &str = "poll-pool";
const POLL_READ: &str = "poll-read"; // EXISTS (Chunk A) — armed-timer poll leaf.
/// `poll-fault` — the Gap-G6 extended `poll-pool` leaf (Chunk-B /dev deliverable):
/// a poll-shape effect that deliberately FAULTS. Absent on HEAD ⇒ clean runtime-RED.
const POLL_FAULT: &str = "poll-fault";

/// The provisional **admission-degree** configuration surface (Gap G6). Per
/// `spec/10-io.md` §10.12.4.2 the degree is **implementation-defined config, not a
/// language form** ("The means by which a program selects a degree … is
/// implementation-defined"), so an env var is the natural carrier. The concrete
/// name/shape is the /dev backpressure-wave deliverable; reconcile this const when
/// that wave lands. On HEAD the var is ignored (no admission throttle exists) ⇒ the
/// §B3-syn row runs RED.
const DEGREE_ENV: &str = "CRANELISP_DEGREE";

// === Helpers =================================================================

/// `--run` the program with the workspace platforms on the search path.
fn run_prog(prog: &str) -> CrOutput {
    Cranelisp::new()
        .use_workspace_platforms()
        .run("user.cl")
        .user(prog)
        .output()
}

/// `--run` the program with an extra env overlay (e.g. the degree config).
fn run_prog_env(prog: &str, env: &[(&str, &str)]) -> CrOutput {
    let mut cr = Cranelisp::new().use_workspace_platforms().run("user.cl").user(prog);
    for (k, v) in env {
        cr = cr.env(k, v);
    }
    cr.output()
}

/// Best-of-`BEST_OF_N` minimum wall-clock (ms) over repeated `--run`s.
fn best_elapsed_ms(prog: &str, env: &[(&str, &str)]) -> u128 {
    (0..BEST_OF_N)
        .map(|_| run_prog_env(prog, env).elapsed.as_millis())
        .min()
        .expect("BEST_OF_N >= 1")
}

// =============================================================================
// §B1 — "server with no `spawn`": the language exposes NO concurrency primitive.
// The fan-out is purely INFERRED from dataflow (arch §1/§4); concurrency is
// "written by nobody". This is the negative face — a verify pin that is
// GREEN today (failing-not-ignored-faithful: a genuinely-passing pin is not a
// hidden failure, and it is NOT `#[ignore]`'d). It becomes a stays-green guard
// the moment the fan-out server fixture lands.
// =============================================================================

// spec: spec/10-io.md §10.12.7 — launch-and-continue is "the mechanism by which a
// server fans out request handlers with **no `spawn`** in the source". No
// `spawn`/`go`/`async`/`thread` primitive exists: each probe at a bare REPL
// reports the name unbound, never a bound function signature.
#[test]
fn web_server_no_user_spawn_primitive_neg() {
    for name in ["spawn", "go", "async", "thread"] {
        let out = Cranelisp::repl_capture(&format!("{name}\n"));
        let lc = out.stdout.to_lowercase();
        // The probe is unbound: the REPL says "undefined" (or "error") and names
        // the symbol — it does NOT echo a `:(Fn …)` / `:primitives/…` value, which
        // would mean a concurrency primitive secretly exists.
        assert!(
            lc.contains("undefined") || lc.contains("error"),
            "concurrency primitive `{name}` must be UNBOUND (fan-out is inferred, \
             not spawned — spec/10-io.md §10.12.7); got stdout:\n{}",
            out.stdout
        );
        assert!(
            !out.stdout.contains(&format!("primitives/{name}")),
            "concurrency primitive `{name}` must NOT resolve to a primitive; \
             got stdout:\n{}",
            out.stdout
        );
    }
}

// =============================================================================
// §B2-syn — Supervisor: a detached fault does not abort the launch loop.
// The synthetic core of "panic → drop, server lives" (spec/12-runtime.md §12.7.9
// item 1 — the supervising context survives), with NO web/HTTP machinery: a loop
// that LAUNCHES a faulting poll effect each iteration (result discarded, distinct
// tokens ⇒ launch-and-continue per arch §4) still completes all iterations and
// exits cleanly. A NON-supervised detached fault would abort the program (signal /
// non-zero exit) — the abort this guards.
// =============================================================================

// spec: spec/12-runtime.md §12.7.9 — a launched (detached) faulting effect is
// contained by the supervisor (catch + drop), so the launching strand survives and
// the loop runs to completion. A tail-recursive launch LOOP (the §B4 model)
// launches one faulting effect per dynamic frame (result discarded ⇒ the
// `IO_TAG_LAUNCH` shape, NOT a joined `Par`; FIXME 0467); the continuation reaches
// `(Pure 42)` ⇒ exit 42. A detached fault is captured by the supervisor, the slot
// is CLEARED, `StrandFailed` is emitted, the strand dropped — so the launcher's
// slot is clean at `cranelisp_run_program`'s completion check.
#[test]
fn detached_faulting_effect_does_not_abort_the_launch_loop() {
    // A tail-recursive launch LOOP (the §B4 model): each iteration LAUNCHES one
    // `poll-fault` on a DISTINCT token `n` (its result discarded — the unused bind
    // binder, exactly what the `do` sequencing macro desugars to; tests are
    // free-standing so we cannot use the prelude `do` macro) and recurses. The
    // `(let [m (sub-i64 n 1)] …)` decouple hoists the loop control value OUT of the
    // token operand so io free {n} and cont free {m} are disjoint — the unified
    // single-step launch-arm E2 (FIXME 0478: same literal free-var disjointness the
    // sub-tree arm uses) then permits the launch. A single
    // result-discarded, token-disjoint bind step per dynamic frame lowers to
    // `IO_TAG_LAUNCH` (the launch shape `/int`'s independence analysis recognises —
    // a flat sibling chain would instead group into a joined `Par`, bypassing the
    // supervisor; FIXME 0467). Each launched strand faults; under the supervisor
    // each fault is caught + the slot CLEARED + `StrandFailed` emitted + the strand
    // dropped, and the launching loop survives to reach `(Pure 42)` ⇒ exit 42.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{fault}]])\n\
         (import [primitives [bind Pure sub-i64 eq-i64]])\n\
         (defn fault-loop [n]\n\
           (if (eq-i64 n 0)\n\
               (Pure 42)\n\
               (let [m (sub-i64 n 1)]\n\
                 (bind ({fault} n 1 {d}) (fn [r]\n\
                   (fault-loop m))))))\n\
         (defn main [] (fault-loop 3))\n",
        plat = POLL_PLATFORM,
        fault = POLL_FAULT,
        d = D_MS,
    );
    // Positive: the loop completed (exit 42). Negative: the run did NOT abort /
    // signal (an unsupervised detached fault would crash the process before 42) and
    // did NOT report the detached fault as the program error (exit 1 — the slot
    // bleed). `assert_exit(42)` is all three — a clean coded exit excludes both
    // signal termination and the runtime-error exit.
    run_prog(&prog).assert_exit(42);
}

// =============================================================================
// §B3-syn — Backpressure / admission degree: degree=N bounds in-flight launched
// effects; the (N+1)th admission-PARKS (spec/10-io.md §10.12.4.2 item 1 — the
// same observable park as the (N+1)th-parks of §10.12.4.1, wall-clock latency,
// not an error). A loop launches M independent slow poll effects on DISTINCT
// tokens (so per-resource capacity does not bound them) under a configured global
// degree N < M: at most N overlap, the rest park ⇒ ≈⌈M/N⌉ waves.
// =============================================================================

// spec: spec/10-io.md §10.12.4.2 — a launch LOOP of M=4 detached poll-reads under
// CRANELISP_DEGREE=2: the global admission budget bounds in-flight DETACHED STRANDS
// (§10.12.4.2 item 3) to 2, so the 3rd/4th launch admission-PARKS ⇒ wall-clock ≈ 2
// waves ≈ 2·D, distinguishable from unbounded (≈1·D — degree NOT enforced) AND from
// serial (≈4·D). FIXME 0467: this is a launch loop (results DISCARDED ⇒
// `IO_TAG_LAUNCH`, which acquires the global-budget permit) — NOT a flat
// result-using bind chain (which `/int` lowers to a distinct-token `Par` the
// launch-scoped global degree cannot bound). RED-first on HEAD before the
// backpressure wave: the `CRANELISP_DEGREE` knob is ignored, so the 4 launches run
// unthrottled ⇒ the two-sided window is violated. Saturate-not-oversaturate is the
// load-bearing assertion.
#[test]
fn degree_n_bounds_inflight_launched_effects_nplus1_parks() {
    // A tail-recursive launch LOOP (the §B4 model): each iteration LAUNCHES one
    // D-ms `poll-read` on a DISTINCT token `n` (capacity 1 each, so the per-resource
    // pool never bounds them — only the global degree does) with its result
    // DISCARDED (the unused bind binder), then recurses. The `(let [m (sub-i64 n 1)]
    // …)` decouple keeps the token operand `n` disjoint from the continuation (io
    // free {n}, cont free {m}) so the unified single-step launch-arm E2 (FIXME 0478)
    // permits the launch. The discarded, token-
    // disjoint single bind step lowers to `IO_TAG_LAUNCH`, whose `launch_continue`
    // arm acquires the GLOBAL-budget permit (sized to the degree) — so degree=2
    // admits 2 strands and PARKS the 3rd/4th launch. Returns `(Pure 0)` ⇒ exit 0
    // (results are discarded, so there is no sum to witness — the wall-clock IS the
    // witness, exactly as the §B4 launch row).
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [bind Pure sub-i64 eq-i64]])\n\
         (defn launch-loop [n]\n\
           (if (eq-i64 n 0)\n\
               (Pure 0)\n\
               (let [m (sub-i64 n 1)]\n\
                 (bind ({read} n 1 {d}) (fn [r]\n\
                   (launch-loop m))))))\n\
         (defn main [] (launch-loop 4))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        d = D_MS,
    );
    let env = [(DEGREE_ENV, "2")];
    run_prog_env(&prog, &env).assert_exit(0);

    let ms = best_elapsed_ms(&prog, &env);
    // Lower bound (> 1.5·D ≈ 225): the (N+1)th admission PARKED — the 4 reads did
    // not all overlap freely (which would be ≈ 1·D ≈ 180). This is the load-bearing
    // "do not oversaturate" half.
    assert!(
        ms > (D_MS as u128 * 3) / 2,
        "degree=2 must BOUND in-flight launched effects (the 3rd/4th admission-PARK, \
         wall-clock > {}ms ≈ 1.5·D); measured {ms}ms — looks unthrottled (all 4 \
         overlapped; admission degree not enforced)",
        (D_MS * 3) / 2,
    );
    // Upper bound (< 3·D ≈ 450): at most-N-in-flight still OVERLAPS within each wave
    // (≈ 2 waves ≈ 2·D ≈ 300), distinguishable from serial (≈ 4·D ≈ 600). This is
    // the "do saturate" half.
    assert!(
        ms < D_MS as u128 * 3,
        "degree=2 must still SATURATE to N in flight per wave (≈2 waves ≈ 2·D, \
         wall-clock < {}ms ≈ 3·D); measured {ms}ms — looks fully serial (degree \
         throttled below N, or no overlap at all)",
        D_MS * 3,
    );
}

// =============================================================================
// §B4 — Launch-and-continue: a launched effect runs CONCURRENTLY while the
// launcher continues WITHOUT awaiting it (arch §4; spec/10-io.md §10.12.7 item 1).
// The witness is the canonical accept-loop shape `(do (handle) (recur))`: a
// tail-recursive loop that LAUNCHES a slow effect each iteration and recurses
// immediately. Across recursion iterations the structured fork-join cannot group
// siblings (each iteration is a fresh dynamic call), so WITHOUT launch-and-continue
// the loop is serial (≈ K·D); WITH it the launcher fans out and the K slow effects
// overlap (≈ D, drained at exit). This is why a recursive loop — not a flat
// `(do slow fast)` — is the robust observable: a flat sibling chain would overlap
// under structured auto-IO-parallel too, and could not distinguish the two.
// =============================================================================

// spec: spec/10-io.md §10.12.7 — the accept loop launches K=5 slow poll effects
// (results discarded — unused bind binder, the `do`-desugaring; distinct tokens)
// and the launcher continues
// (recurses) without awaiting each ⇒ the 5 overlap (≈ D, not serial 5·D) AND the
// detached effects still RUN (drained before exit — the wall-clock lower bound
// proves they were not skipped). RED-first on HEAD: no launch-and-continue
// lowering exists, so each `bind` awaits its slow effect and the loop is serial
// (≈ 5·D ≈ 750ms ≫ the overlap window).
#[test]
fn launch_and_continue_runs_concurrently_launcher_does_not_await() {
    // A tail-recursive accept-loop: launch a slow D-ms poll-read on token `n`
    // (result discarded — unused bind binder), then recurse. Distinct tokens per
    // iteration, so capacity never bounds them. The `(let [m (sub-i64 n 1)] …)`
    // decouple hoists the loop control value out of the token operand (io free {n},
    // cont free {m} ⇒ disjoint), which the unified single-step launch-arm E2 (FIXME
    // 0478) requires to permit the launch. Returns `(Pure 0)` at n=0 ⇒ exit 0.
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{read}]])\n\
         (import [primitives [bind Pure sub-i64 eq-i64]])\n\
         (defn fanout-loop [n]\n\
           (if (eq-i64 n 0)\n\
               (Pure 0)\n\
               (let [m (sub-i64 n 1)]\n\
                 (bind ({read} n 1 {d}) (fn [r]\n\
                   (fanout-loop m))))))\n\
         (defn main [] (fanout-loop 5))\n",
        plat = POLL_PLATFORM,
        read = POLL_READ,
        d = D_MS,
    );
    run_prog(&prog).assert_exit(0);

    let ms = best_elapsed_ms(&prog, &[]);
    // Lower bound (> 0.5·D ≈ 75): the launched slow effects still RAN — they were
    // drained before exit (had they been skipped, the run would finish ≈ 0ms).
    assert!(
        ms > D_MS as u128 / 2,
        "launched effects must still RUN (drained before exit; wall-clock > {}ms ≈ \
         0.5·D); measured {ms}ms — looks like the detached effects were skipped",
        D_MS / 2,
    );
    // Upper bound (< 3·D ≈ 450): the launcher did NOT await each effect — the 5
    // overlap (≈ D), NOT serial (≈ 5·D ≈ 750). This is the load-bearing
    // "launcher does not await" assertion.
    assert!(
        ms < D_MS as u128 * 3,
        "the launcher must CONTINUE without awaiting each launched effect (the 5 \
         overlap ≈ D, wall-clock < {}ms ≈ 3·D); measured {ms}ms — looks serial \
         (≈5·D ≈ 750ms; each `bind` awaited its slow effect — no launch-and-continue)",
        D_MS * 3,
    );
}

// =============================================================================
// Sprint 97 — 0474: fresh continuation-produced SELECT / PAR node branch-Vec leak.
//
// A fresh `IO_TAG_SELECT` / `IO_TAG_PAR` node built INSIDE a bind continuation is
// released by the shallow `dec_shallow_io` path, which never walks field 0 → the
// branch container Vec + the branch sub-trees LEAK (`design/backend/ring2-rc.md
// §3.5.10`). The fix (option (a), shared across both tags) makes `dec_shallow_io`
// shape-aware for `IO_TAG_PAR` / `IO_TAG_SELECT` and deep-frees the branch container.
// `/qa` owns the heap-balance e2e guard; `/dev` (intrinsics) owns the unit mirror.
//
// Both rows are **failing-not-ignored** RC-balance guards: under `CRANELISP_RC_TRACE=1`
// a leaked branch Vec shows `alloc > free`. They are RED on HEAD (the leak) and flip
// GREEN when the 0474 deep-free lands. Process-isolated (each `--run` is its own
// subprocess; the RC counter reads only that child's stderr), so no `serial`
// coordination is needed.
// =============================================================================

/// Count `[RC] alloc` / `[RC]  free` events in a `CRANELISP_RC_TRACE=1` stderr.
/// Mirrors `concurrency_spark.rs::rc_alloc_free_counts` / `spec_12_runtime.rs`.
fn rc_alloc_free_counts(stderr: &str) -> (usize, usize) {
    let allocs = stderr
        .lines()
        .filter(|l| l.contains("[RC]") && l.contains(" alloc "))
        .count();
    let frees = stderr
        .lines()
        .filter(|l| l.contains("[RC]") && l.contains(" free "))
        .count();
    (allocs, frees)
}

// spec: spec/10-io.md §10.12.8 — a continuation-produced FRESH `select` with N≥2 heap
// branches: `(bind (Pure 0) (fn [_] (select [(Pure 7) (Pure 8)])))`. The first branch
// wins ⇒ exit 7 (a clean run), but the freshly-built `IO_TAG_SELECT` node is released
// shallow, leaking the branch container + the N branch roots. `[RC] alloc` MUST equal
// `[RC] free`. RED on HEAD (leaks); GREEN post-0474 deep-free.
#[test]
fn fresh_select_in_continuation_rc_balanced() {
    let src = "(import [primitives [bind select Pure]])\n\
               (defn main [] (bind (Pure 0) (fn [_] (select [(Pure 7) (Pure 8)]))))\n";
    let out = Cranelisp::new()
        .env("CRANELISP_RC_TRACE", "1")
        .file("user.cl", src)
        .run("user.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(7),
        "the continuation-produced select must run cleanly (first branch wins ⇒ exit 7)\n\
         stdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert!(allocs > 0, "expected the RC trace to record allocations; got 0");
    assert_eq!(
        allocs, frees,
        "a FRESH continuation-produced select node must be alloc/free balanced — the \
         branch container Vec + N branch roots must deep-free (0474, ring2-rc.md §3.5.10); \
         got {allocs} allocs / {frees} frees (alloc > free ⇒ the shallow-dec leaked the \
         branch Vec).\nstderr:\n{}",
        out.stderr
    );
}

// spec: spec/10-io.md §10.12.7 — the `par` analogue. There is NO surface `par` form
// (`spec/10-io.md §10.12.5`: concurrent IO is AUTOMATIC — the compiler inserts a `Par`
// node for data-independent effect pairs in a bind chain). A continuation whose body
// is TWO INDEPENDENT poll effects (`b` does not reference `a`) builds a fresh
// `IO_TAG_PAR` node INSIDE the continuation (gap G-B resolved: auto-IO-Par over the
// independent pair, no surface combinator needed). The fresh par node leaks its branch
// container exactly as the select node does. CONTROL: the DEPENDENT variant (b uses a ⇒
// NO Par node) is alloc/free BALANCED on HEAD (verified: 12/12 vs the independent
// 12/8), isolating this imbalance to the par branch-Vec leak (not poll-machinery
// noise). RED on HEAD (leaks); GREEN post-0474.
#[test]
fn fresh_par_in_continuation_rc_balanced() {
    // Two 30 ms `poll-read`s on DISTINCT tokens, results combined; the second does NOT
    // depend on the first ⇒ the independence analysis inserts a fresh `IO_TAG_PAR` node
    // in the continuation. 30 + 30 ⇒ exit 60 (a clean run).
    let src = "(platform poll-pool)\n\
               (import [platform.poll-pool [poll-read]])\n\
               (import [primitives [bind Pure add-i64]])\n\
               (defn main []\n\
                 (bind (Pure 0) (fn [_]\n\
                   (bind (poll-read 1 1 30) (fn [a]\n\
                     (bind (poll-read 2 1 30) (fn [b]\n\
                       (Pure (add-i64 a b)))))))))\n";
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .env("CRANELISP_RC_TRACE", "1")
        .file("user.cl", src)
        .run("user.cl")
        .output();
    assert_eq!(
        out.status.code(),
        Some(60),
        "the continuation-produced par (two independent poll-reads) must run cleanly \
         (30+30 ⇒ exit 60)\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let (allocs, frees) = rc_alloc_free_counts(&out.stderr);
    assert!(allocs > 0, "expected the RC trace to record allocations; got 0");
    assert_eq!(
        allocs, frees,
        "a FRESH continuation-produced par node must be alloc/free balanced — the branch \
         container Vec must deep-free (0474, shared with the select tag; ring2-rc.md \
         §3.5.10); got {allocs} allocs / {frees} frees. (The DEPENDENT control — b uses a, \
         no Par — balances on HEAD, isolating this to the par branch-Vec leak.)\nstderr:\n{}",
        out.stderr
    );
}
