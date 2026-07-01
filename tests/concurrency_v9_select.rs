//! Sprint 97 — concurrency-track drains: 0475 (empty `(select [])` recoverable
//! runtime error) + 0479 (unarmed one-shot suspend trips the deadlock detector
//! promptly). QA-first (Phase 5 Wave 1) failing-not-ignored e2e acceptance rows.
//!
//! Plan: `tests/plan/sprint-97.md` §"Item 4" (0475) + §"Item 5" row 5.2 (0479).
//! Contracts of record: `design/int/reactor.md §9` (0475 — count-zero guard in
//! `run_select_node`, `io.rs:496-500`) + `§8` (0479 — armed-ness deadlock detector
//! + `drive_mode` knob). Spec of record: `spec/10-io.md §10.12.8` ("Empty
//! `select`") / `spec/12-runtime.md §12.7.2` (Runtime Panics — recoverable via
//! `catch-runtime-error`) / `§12.4.4` (combinators + cancellation; the "never
//! completes is also non-conforming" clause).
//!
//! ## Posture — failing-not-ignored, RED-until the Wave-3 /dev drains
//!
//! All rows are RED on HEAD (`memory/feedback_failing_not_ignored.md`):
//!   - 0475: an empty `(select [])` at a HEAP-typed `a` is today an unsound null —
//!     it SIGSEGVs (signal termination) when the synthesised `0` is dereferenced.
//!     The fix routes a "select over empty collection" runtime error through the
//!     standard recoverable slot. The rows assert the POST-FIX behaviour.
//!   - 0479 (5.2): an unarmed one-shot suspend must trip the deadlock detector
//!     PROMPTLY. This needs a `/dev` fixture leaf that returns `Pending` with nothing
//!     armed (design §8.3 describes it as a fixture-future) — absent on HEAD ⇒ clean
//!     runtime-RED. See the gap-G-D FIXME on 5.2.
//!
//! Free-standing per `tests/CLAUDE.md`: primitives + special forms only; 5.2 uses
//! the workspace `poll-pool` fixture platform. ZERO `stdlib/` dependency.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, CrError};
use std::time::Duration;

/// The empty-select message of record (`reactor.md §9` / `spec/10-io.md §10.12.8`).
const EMPTY_SELECT_MSG: &str = "select over empty collection";

/// An empty `(select [])` instantiated at a HEAP-typed `a` (`String`), bound to a
/// use that dereferences the resulting string. At a heap-typed `a` the as-built
/// synthesised `0` is an unsound null pointer; `use-str` dereferencing it is the
/// SIGSEGV the 0475 fix removes. The explicit `:(Vec (IO String))` annotation pins
/// `a := String` (a heap type) so the empty literal is not ambiguous.
const EMPTY_SELECT_HEAP_UNCAUGHT: &str = "\
(import [primitives [select Pure bind String]])\n\
(defn use-str [:primitives/String s] (Pure 0))\n\
(defn main []\n\
  (bind (select :(primitives/Vec (primitives/IO primitives/String)) [])\n\
    (fn [s] (use-str s))))\n";

// =============================================================================
// Item 4 — 0475: `(select [])` recoverable runtime error.
// =============================================================================

// spec: spec/10-io.md §10.12.8 — an UNcaught empty `(select [])` at a heap-typed `a`
// under `--run` MUST surface the recoverable runtime error "select over empty
// collection" (non-zero exit + the message), NOT an unsound-null SIGSEGV and NOT a
// hang. RED on HEAD: today the heap-typed empty select dereferences a synthesised
// null ⇒ SIGSEGV (signal termination, no message). The `.timeout` bounds the no-hang
// requirement.
#[test]
fn empty_select_heap_typed_fatal_runtime_error() {
    let out = Cranelisp::new()
        .file("user.cl", EMPTY_SELECT_HEAP_UNCAUGHT)
        .run("user.cl")
        .timeout(Duration::from_secs(5))
        .output();
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert_ne!(
        out.status.code(),
        Some(0),
        "an uncaught empty (select []) MUST be a runtime error (non-zero exit), not a \
         value\ncombined:\n{combined}"
    );
    assert!(
        combined.contains(EMPTY_SELECT_MSG),
        "an uncaught empty (select []) MUST surface '{EMPTY_SELECT_MSG}' (spec/10-io.md \
         §10.12.8); RED on HEAD (today: unsound-null SIGSEGV, no message). Flips GREEN when \
         the 0475 count-zero guard lands (reactor.md §9).\ncombined:\n{combined}"
    );
}

// spec: spec/12-runtime.md §12.7.2 — the empty `(select [])` runtime error is
// RECOVERABLE at a `catch-runtime-error` boundary: the bracket returns
// `(Err "select over empty collection…")` and the program recovers (exits with the
// recovered branch). Ok ⇒ exit 0; Err ⇒ exit 42 (the discriminator). RED on HEAD:
// today the empty select is never raised through the recoverable slot.
//
// FIXME(/spec 0487) — GATED, catchability RULING PENDING (S98 band B). The exit-42
// assertion below PRESUMES resolution (b) "construction-time-catchable". This is
// NOT yet decided: FIXME 0487 (`design/arch/fixmes/0487-spec-empty-select-catchability
// -semantics.md`) is the /spec ruling that finalizes the shape, and /arch's S98 Phase-2
// steer is toward resolution **(a) honest fatal-runtime-error** — under which this row
// is UNACHIEVABLE (the empty select raises at effect-RUN time, outside `catch-runtime-
// error`'s pure-construction bracket, spec/appendix-a §A.3) and MUST be RETIRED, not
// green-flipped. So this row is HELD RED pending 0487:
//   - if /spec rules (b) construction-time-catchable → /backend `compile_select` raise
//     makes exit 42 GREEN (this row is the acceptance);
//   - if /spec rules (a) fatal-runtime-error → RETIRE this row; the "does raise, not
//     unsound-null" invariant is already covered GREEN by the three sibling rows
//     (`empty_select_heap_typed_fatal_runtime_error`, `_not_unit_zero_neg`,
//     `_does_not_hang`). /qa re-points after the ruling. Do NOT green-flip by
//     presuming either shape before 0487 resolves.
#[test]
fn empty_select_caught_by_catch_runtime_error() {
    let src = "\
(import [primitives [select Pure bind catch-runtime-error Result Ok Err String]])\n\
(defn empty-sel []\n\
  (bind (select :(primitives/Vec (primitives/IO primitives/String)) []) (fn [s] (Pure s))))\n\
(defn main []\n\
  (match (catch-runtime-error (fn [] (empty-sel)))\n\
    [(Ok v)  (Pure 0)\n\
     (Err m) (Pure 42)]))\n";
    let out = Cranelisp::new()
        .file("user.cl", src)
        .run("user.cl")
        .timeout(Duration::from_secs(5))
        .output();
    out.assert_exit(42);
}

// spec: spec/10-io.md §10.12.8 — negative: the empty-select result MUST NOT be a
// synthesised `0`/Unit/garbage flowing downstream (the unsound-null path is gone).
// Distinct from 4.1's message assertion: this asserts the run is NOT signal-
// terminated. RED on HEAD: the heap-typed empty select SIGSEGVs (signal termination,
// `status.code() == None`); post-fix it is a clean recoverable runtime error
// (`status.code()` is `Some` non-zero — a fault slot, not a hardware signal, not 0).
#[test]
fn empty_select_heap_typed_not_unit_zero_neg() {
    let out = Cranelisp::new()
        .file("user.cl", EMPTY_SELECT_HEAP_UNCAUGHT)
        .run("user.cl")
        .timeout(Duration::from_secs(5))
        .output();
    assert!(
        out.status.code().is_some(),
        "the heap-typed empty select MUST raise a clean recoverable runtime error, NOT \
         dereference a synthesised null (a hardware SIGSEGV ⇒ signal termination, no exit \
         code). RED on HEAD (today: SIGSEGV); flips GREEN when 0475 routes it through the \
         runtime-error slot.\nstatus={:?}\nstdout:\n{}\nstderr:\n{}",
        out.status,
        out.stdout,
        out.stderr
    );
    assert_ne!(
        out.status.code(),
        Some(0),
        "the empty select MUST NOT exit 0 with a synthesised value — the unsound-null \
         placeholder path is non-conforming (spec/10-io.md §10.12.8)\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
}

// spec: spec/12-runtime.md §12.4.4 — the empty select returns PROMPTLY (a clean
// fault), not a deadlock-hang ("a guaranteed deadlock is worse than a clean fault";
// "never completes is also non-conforming"). The `.timeout(5s)` is the no-hang
// witness; surfacing the error message is what keeps it RED on HEAD (today: SIGSEGV,
// no message — fast but non-conforming). Flips GREEN when 0475 lands the prompt,
// message-bearing runtime error.
#[test]
fn empty_select_does_not_hang() {
    let res = Cranelisp::new()
        .file("user.cl", EMPTY_SELECT_HEAP_UNCAUGHT)
        .run("user.cl")
        .timeout(Duration::from_secs(5))
        .try_output();
    let out = match res {
        Ok(o) => o,
        Err(CrError::Timeout(d)) => panic!(
            "empty (select []) must return PROMPTLY (a clean runtime error), not deadlock-\
             hang (spec/12-runtime.md §12.4.4); the run did not complete within {d:?}"
        ),
        Err(e) => panic!("empty_select_does_not_hang: harness error: {e}"),
    };
    let combined = format!("{}{}", out.stdout, out.stderr);
    assert!(
        combined.contains(EMPTY_SELECT_MSG),
        "empty (select []) must complete promptly WITH the '{EMPTY_SELECT_MSG}' runtime \
         error (not hang, not a silent SIGSEGV); RED on HEAD until 0475.\ncombined:\n{combined}"
    );
}

// =============================================================================
// Item 5 row 5.2 — 0479: an unarmed one-shot suspend trips the deadlock detector
// PROMPTLY (the negative face of the idle-armed-server survives row 5.1).
// =============================================================================

/// The `poll-pool` fixture platform (Chunk-A; `concurrency_fanout.rs`).
const POLL_PLATFORM: &str = "poll-pool";
/// `poll-no-interest` — the §8.3 unarmed-suspend fixture leaf (a poll-shape effect
/// that returns `Pending` with NOTHING armed: no fd in `fd_waiters`, no timer, no
/// bridge, no supervisor, no parked permit). It does NOT exist on HEAD ⇒ a clean
/// runtime-RED (the binary errors at load — an absent effect, NOT a compile break,
/// since e2e shells out to the binary; mirrors `POLL_FAULT` in `concurrency_fanout.rs`
/// §B2-syn). Named WITHOUT an "armed"/"deadlock" substring so the absent-leaf load
/// error cannot false-match the deadlock-diagnostic assertion below.
const POLL_UNARMED: &str = "poll-no-interest";

// spec: design/int/reactor.md §8 — a one-shot `--run` program that suspends `Pending`
// with NOTHING armed MUST abort PROMPTLY (well under the old 30s `MAX_TOTAL_BLOCK`
// cap) with the deadlock diagnostic — the armed-ness detector trips the instant the
// stuck state is structurally present, not 30s later. The `.timeout(5s)` proves
// "promptly" (a 30s-cap abort would exceed it; a true hang would Timeout).
//
// FIXME(/sprint S97 W3) — gap G-D (5.2 is gap-contingent): an unarmed-`Pending`
// program is NOT expressible from ordinary user source (no user leaf returns Pending
// without arming a readiness source). Design §8.3 describes the unarmed future as a
// `/dev` FIXTURE FUTURE. This e2e therefore references a `/dev`-owed `poll-pool`
// fixture leaf `poll-unarmed` (the §8.3 immediate-trip fixture surfaced as a poll-
// shape leaf) — /dev (int) Wave 3 must ADD `poll-unarmed` to `platforms/poll-pool/`
// + `tests/scripts/build-link-prereqs.sh`. If that leaf is not provided, 5.2 reduces
// to the §8.3 `/dev` intrinsics immediate-trip UNIT and /qa keeps only the positive
// 5.1 (`concurrency_fanout_web::idle_armed_server_survives_then_serves`). On HEAD the
// leaf is absent ⇒ this is RED (load error, no deadlock diagnostic).
#[test]
fn unarmed_oneshot_suspend_trips_promptly_neg() {
    let prog = format!(
        "(platform {plat})\n\
         (import [platform.{plat} [{unarmed}]])\n\
         (import [primitives [bind Pure]])\n\
         (defn main [] (bind ({unarmed} 0 1 0) (fn [_] (Pure 7))))\n",
        plat = POLL_PLATFORM,
        unarmed = POLL_UNARMED,
    );
    let res = Cranelisp::new()
        .use_workspace_platforms()
        .file("user.cl", &prog)
        .run("user.cl")
        .timeout(Duration::from_secs(5))
        .try_output();
    let out = match res {
        Ok(o) => o,
        Err(CrError::Timeout(d)) => panic!(
            "an unarmed one-shot suspend must trip the deadlock detector PROMPTLY \
             (reactor.md §8), not hang; the run did not complete within {d:?} — looks like \
             the armed-ness detector is not tripping (or the fixture leaf parks armed)"
        ),
        Err(e) => panic!("unarmed_oneshot_suspend_trips_promptly_neg: harness error: {e}"),
    };
    assert_ne!(
        out.status.code(),
        Some(0),
        "an unarmed suspend must ABORT (non-zero exit), not complete\nstdout:\n{}\nstderr:\n{}",
        out.stdout,
        out.stderr
    );
    let lc = format!("{}{}", out.stdout, out.stderr).to_lowercase();
    assert!(
        lc.contains("deadlock") || lc.contains("no armed interest") || lc.contains("suspended"),
        "an unarmed suspend must abort with the DEADLOCK diagnostic ('reactor suspended \
         with no armed interest …', reactor.md §8.2); RED on HEAD (the `poll-no-interest` \
         fixture leaf is absent — see the gap-G-D FIXME above).\ncombined:\n{lc}"
    );
}
