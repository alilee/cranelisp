//! Sprint 94 — effect-concurrency Slice-2 completion: real effect-node await.
//!
//! QA-first (Phase 5 Stage 1) e2e guards for the ratified backend↔intrinsics
//! poll-shape Effect-node seam (`design/arch/effect-concurrency.md` Appendix B
//! §"the ratified … seam" (a)–(d); `design/int/reactor.md` §2.5/§2.7/§4). Plan:
//! `tests/plan/sprint-94.md` §1A/§1B/§1C/§1D.
//!
//! Two lanes share this file:
//!   - DEFAULT `nt` (feature OFF): the ungated structural replays (a)/(d) — the
//!     byte-identical-when-off + executor-free-link guarantees. GREEN today.
//!   - `nt-reactor-e2e` (`cargo nextest run -p cranelisp --features
//!     concurrency-runtime`): the gated headline rows (b)/(c) drive a real
//!     in-tree async leaf through `cranelisp_run_io`. RED-first — the
//!     `declare_platform!`-emitted in-tree async leaf (R2/R6) lands in the
//!     reactor wave (Wave 2). The gated rows compile OUT of the default lane so
//!     they raise no collateral RED there.
//!
//! Observability note (the e2e vs unit split). The strand sink
//! (`cranelisp-intrinsics::strand`) is an in-memory buffer drained only by the
//! gated intrinsics unit tests; the dev-facing `/strand` dump is DEFERRED
//! (`design/int/reactor.md` §3). So the `EffectDispatched → EffectSuspended →
//! EffectResumed` strand-stream assertions are NOT subprocess-observable and
//! live in the intrinsics-unit regression-replay rows (`/dev`-authored,
//! `reactor/tests.rs`). These e2e rows assert the OBSERVABLE proxy of
//! suspend/resume + overlap: the leaf's i64 result reads back correctly, and two
//! leaves in a `Par` overlap in wall-clock (≈max not sum).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// =============================================================================
// §1A (a) — feature-off byte-identical: the v6 blocking path is unchanged.
// =============================================================================

// spec: design/arch/effect-concurrency.md §"The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" (a) — the
// backend's poll arm is reached only by `concurrency`-gated poll effects, so a
// DEFAULT (feature-off) build constructs only `IO_TAG_EFFECT` for the blocking
// effects that are every real platform today; a real-IO program's observable
// output is byte-identical to the v6 path. This is the thin e2e edge over the
// standing `spec_10_io` coverage named for the App-B(a) claim. GREEN today
// (regression-replay).
#[test]
fn real_io_program_default_build_output_unchanged() {
    let probe = "reactor-byte-identical-probe";
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .use_workspace_platforms()
        .run("user.cl")
        .user(&format!(
            "(platform stdio)\n\
             (import [platform.stdio [print]])\n\
             (defn main [] (print \"{probe}\"))\n"
        ))
        .output();
    out.assert_stdout_contains(probe);
}

// =============================================================================
// §1D (d) — `--link` links no executor: the linked binary runs with no
// reactor/executor present (`mio`/`futures` never compiled into the exe-bundle
// path — the `dep:`-gated guarantee, `reactor.md` §1).
// =============================================================================

// spec: design/arch/effect-concurrency.md §"The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" (d) — a small
// IO program `--link`ed then RUN succeeds and computes correctly, witnessing that
// the executor-free linked binary works. Named for the no-executor edge over the
// standing `link.rs` coverage. GREEN today (regression-replay).
#[test]
fn link_io_program_runs_without_executor() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::TestStandard)
        .link_then_run("io_main.cl")
        .file("io_main.cl", "(defn main [] (Pure 7))")
        .output();
    // The produced standalone binary RAN (not just linked): exit code carries the
    // computed value (§10.6.1). No executor is linked, yet the IO trampoline drives.
    out.assert_exit(7);
}

// =============================================================================
// §1B/§1C (b)/(c) — feature-on real-node await through `cranelisp_run_io`.
// RED-first; runs in the `nt-reactor-e2e` lane only (gated).
// =============================================================================

// The intended Wave-2 in-tree async leaf surface (R2/R6): a real
// `declare_platform!`-emitted async-capable `DefKind::PlatformEffect`
// (`design/int/reactor.md` §2.7 — "Demo leaf — `async-read`"). The exact
// platform/effect NAME and arg signature are the `/platform` + `/dev` Wave-2
// deliverable; reconcile these two consts when the leaf lands. Until then these
// programs reference a platform that does not exist, so the binary errors at
// load — a meaningful runtime-RED against the intended shape (failing-not-ignored;
// preferred over a compile-fail per the task's QA-first guidance).
#[cfg(feature = "concurrency-runtime")]
const ASYNC_LEAF_PLATFORM: &str = "async-demo";
#[cfg(feature = "concurrency-runtime")]
const ASYNC_LEAF_EFFECT: &str = "async-read";

// spec: design/arch/effect-concurrency.md §"The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" (b) single-leaf
// — a compiled-from-source program using ONE real in-tree async leaf, run via the
// `concurrency-runtime` binary, drives `cranelisp_run_io` so the leaf suspends
// (EWOULDBLOCK ⇒ `register_readable` + Pending) and resumes (waker ⇒ Ready). The
// strand stream (`Dispatched → Suspended → Resumed`) is the intrinsics-unit guard;
// here the observable proxy is that the program completes with the leaf's result.
// RED-first: the in-tree leaf does not exist on HEAD (Wave 2).
#[cfg(feature = "concurrency-runtime")]
#[test]
fn real_leaf_suspends_and_resumes_through_run_io() {
    // The leaf reads after a 50ms-armed timer; its i64 result is the value we
    // observe. Suspend/resume is required to produce it (the write side is fed
    // after a delay via the host reactor's timer — no per-read thread).
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{eff}]])\n\
         (import [primitives [bind Pure]])\n\
         (defn main [] (bind ({eff} 55) (fn [r] (Pure r))))\n",
        plat = ASYNC_LEAF_PLATFORM,
        eff = ASYNC_LEAF_EFFECT,
    );
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .run("user.cl")
        .user(&prog)
        .output();
    // The leaf suspended and resumed on the reactor and produced 55 (exit byte).
    out.assert_exit(55);
}

// spec: design/arch/effect-concurrency.md §"The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" (b) two-leaf —
// TWO real in-tree async leaves in independent `bind`s overlap on ONE reactor
// thread (`join_io_leaves` / auto-IO-parallel): wall-clock ≈ MAX(delay) not SUM,
// no thread-per-read. Observable proxy for the interleaved two-strand stream.
// RED-first: the in-tree leaf does not exist on HEAD (Wave 2).
#[cfg(feature = "concurrency-runtime")]
#[test]
fn two_real_leaves_in_par_overlap_max_not_sum_one_thread() {
    // Two data-independent 60ms async reads (`a` not free in the second, `b` not
    // free in the first) so the independence analysis can Par-group them. Summed
    // result = 120 (exit byte) proves both ran; the wall-clock proves overlap.
    let delay_ms: u64 = 60;
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{eff}]])\n\
         (import [primitives [bind Pure add-i64]])\n\
         (defn main []\n\
           (bind ({eff} {d}) (fn [a]\n\
             (bind ({eff} {d}) (fn [b]\n\
               (Pure (add-i64 a b)))))))\n",
        plat = ASYNC_LEAF_PLATFORM,
        eff = ASYNC_LEAF_EFFECT,
        d = delay_ms,
    );
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .run("user.cl")
        .user(&prog)
        .output();
    // Both leaves ran: 60 + 60 = 120 (exit byte).
    let elapsed_ms = out.elapsed.as_millis();
    out.assert_exit(120);
    // Overlap, not serialization: ≈ max(60) not sum(120). Generous midpoint
    // (1.5×delay = 90ms) so the structural inequality is robust to jitter (timing
    // flakiness is banned as a disposition — the margin is wide, not tight).
    assert!(
        elapsed_ms < (delay_ms as u128 * 3) / 2,
        "two async leaves must OVERLAP on one reactor thread (≈max {delay_ms}ms, \
         not sum {}ms); measured {elapsed_ms}ms >= 90ms midpoint",
        delay_ms * 2,
    );
}

// spec: design/arch/effect-concurrency.md §"The ratified backend↔intrinsics poll-shape Effect-node seam (S94, R1 — the /dev contract)" (c) — result
// extraction via the generic env-offset read: a real leaf's i64 result (scalar or
// heap base pointer) is observable in the program's value after `cranelisp_run_io`
// returns. The S93 per-effect `ResultReader` fn-pointer collapses to a host-known
// offset read (seam decision 3). RED-first: the in-tree leaf does not exist on
// HEAD (Wave 2).
#[cfg(feature = "concurrency-runtime")]
#[test]
fn real_leaf_i64_result_reads_back_correctly() {
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{eff}]])\n\
         (import [primitives [bind Pure]])\n\
         (defn main [] (bind ({eff} 42) (fn [r] (Pure r))))\n",
        plat = ASYNC_LEAF_PLATFORM,
        eff = ASYNC_LEAF_EFFECT,
    );
    let out = Cranelisp::new()
        .use_workspace_platforms()
        .run("user.cl")
        .user(&prog)
        .output();
    // The leaf's i64 result (42) reads back through the env result slot.
    out.assert_exit(42);
}
