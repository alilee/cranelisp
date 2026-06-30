//! Sprint 96 — effect-concurrency Chunk C4: the `sleep` runtime timer poll leaf
//! (`design/int/reactor.md §2.18`, spec `spec/10-io.md §10.12.8`).
//!
//! `(sleep d)` (`sleep : Int -> IO Int`) arms the reactor's timer and resumes
//! (with `0`) after `d` MILLISECONDS, reusing the entire `IO_TAG_EFFECT_POLL` /
//! `EffectPoll` / acquire-around-poll / timer-`turn()` machinery — it is just
//! another poll node, but its `code_ptr` is the RUNTIME symbol
//! `runtime/sleep_pollfn` (`func_addr`-baked by the backend's `compile_sleep` — the
//! non-GOT runtime-symbol path, the keystone C4 machinery), NOT a `declare_platform!`
//! GOT slot. `sleep` is the leaf the derived stdlib `timeout` builds on.
//!
//! ## Lane (post-cutover)
//!
//! The single-ABI / single-trampoline cutover (S96) retired the `concurrency` /
//! `concurrency-runtime` features: the host reactor is UNCONDITIONAL (lazy-init), so
//! there is ONE collapsed test lane (`cargo nextest run`) and this file is un-gated.
//! `sleep` is a `primitives` builtin (no platform DLL needed).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, CrOutput};

/// A park duration (ms) large enough that "parked then resumed" is unambiguously
/// distinguishable from "returned immediately" by wall-clock, even allowing for the
/// poll carrier's ~30 ms fixed reactor overhead + process startup.
const SLEEP_MS: u64 = 300;
/// A conservative lower-bound floor (ms): the program MUST take at least this long
/// (it parked). Set well below `SLEEP_MS` to absorb monotonic-clock granularity but
/// far above "no park at all" (~tens of ms of startup).
const FLOOR_MS: u128 = 200;

fn run_prog(prog: &str) -> CrOutput {
    Cranelisp::new().run("user.cl").user(prog).output()
}

/// Best-of-N minimum wall-clock (ms). For a PARK lower-bound the minimum is the
/// right filter: scheduler noise can only make a run SLOWER, so the minimum is the
/// closest-to-true parking floor — if even the fastest run exceeds `FLOOR_MS`, the
/// leaf genuinely parked.
fn best_elapsed_ms(prog: &str) -> u128 {
    (0..3)
        .map(|_| run_prog(prog).elapsed.as_millis())
        .min()
        .expect("N >= 1")
}

// spec: spec/10-io.md §10.12.8 / reactor.md §2.18 — `(sleep d)` parks for ≈d ms then
// resumes with `0`. `main` is `(bind (sleep d) (fn [_] (Pure 7)))`, so the program
// exits 7 (proving the bind continuation ran AFTER the timer resumed) and takes at
// least ≈d ms wall-clock (proving the leaf genuinely parked on the reactor timer).
#[test]
fn sleep_parks_for_duration_then_resumes_and_continues() {
    let prog = format!(
        "(import [primitives [bind sleep Pure]])\n\
         (defn main [] (bind (sleep {SLEEP_MS}) (fn [_] (Pure 7))))\n",
    );
    // The continuation ran AFTER the timer resumed ⇒ exit 7.
    run_prog(&prog).assert_exit(7);

    // It genuinely parked ≈SLEEP_MS (not returned immediately).
    let ms = best_elapsed_ms(&prog);
    assert!(
        ms >= FLOOR_MS,
        "(sleep {SLEEP_MS}) must PARK for ≈{SLEEP_MS}ms before resuming; measured \
         {ms}ms (< {FLOOR_MS}ms floor) — looks like the timer leaf did not park \
         (sleep lowering / runtime-symbol code_ptr broken)",
    );
}

// spec: spec/10-io.md §10.12.8 / reactor.md §2.18 — `sleep` must resolve + run in
// `--link` mode too, NOT just `--run` (JIT). The JIT in-memory linker resolves
// `runtime/sleep_pollfn` from the catalog POINTER table, but the system linker (`ld`)
// needs a real exported symbol of that exact slash-name. This is the `--run`/`--link`
// divergence guard: `sleep_pollfn` carries `#[export_name = "runtime/sleep_pollfn"]`
// (mirroring `runtime/vec_new`) so the standalone binary links. `link_then_run`
// links AND execs ⇒ an undefined-reference at link OR a park failure at runtime both
// fail this test. (The `--run` park-floor timing is covered above; here exit 7 — the
// continuation ran after the timer resumed in the linked binary — is the discriminator.)
#[test]
fn sleep_links_and_runs_through_link_mode() {
    let prog = format!(
        "(import [primitives [bind sleep Pure]])\n\
         (defn main [] (bind (sleep {SLEEP_MS}) (fn [_] (Pure 7))))\n",
    );
    Cranelisp::new()
        .link_then_run("user.cl")
        .user(&prog)
        .output()
        .assert_exit(7);
}

// spec: reactor.md §2.18 — the discriminating control: an identical program WITHOUT
// the sleep returns promptly (well under the park floor). This pins that the
// `sleep`-program's wall-clock above comes from the timer park, not from fixed
// process/startup overhead.
#[test]
fn no_sleep_returns_promptly_neg() {
    let prog = "(import [primitives [Pure]])\n\
                (defn main [] (Pure 7))\n";
    run_prog(prog).assert_exit(7);
    let ms = best_elapsed_ms(prog);
    assert!(
        ms < FLOOR_MS,
        "a program with no `sleep` must return promptly (< {FLOOR_MS}ms); measured \
         {ms}ms — the park floor would not discriminate a real sleep",
    );
}
