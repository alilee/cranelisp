//! Sprint 61 Slice 0 — IO trampoline event log integration tests.
//!
//! Derived in Phase 3a (`tests/plan/ring4.md §Sprint 61 → Slice 0 → S0-B`).
//! Validates `design/backend/io-trampoline-trace.md`:
//!   * §2 env-var gating, parse-once, zero overhead when unset
//!   * §3 event taxonomy (TrampolineEnter/Exit, Pure/Bind, PlatformEffect,
//!     ContPush/Pop, Par*)
//!   * §4 event struct shape — `IoTraceEvent: Send + Sync`, bounded size,
//!     no `Serialize`
//!   * §5 crate placement — events MUST NOT appear in any serialised
//!     artefact
//!   * §6 dump format — merge-sorted by `(timestamp_ns, thread_ord_id)`
//!   * §7 off-path regression budget
//!   * §9 acceptance criteria
//!
//! Tests derive from the DESIGN, not the implementation. If an assertion
//! fails because the implementation diverges from the design, the test
//! stays failing.
//!
//! ## Layering
//!
//! Subprocess tests invoke `cranelisp --run examples/21-hello-io.cl`.
//! This path:
//!   * exercises the instrumented `io.rs` sites (§3 taxonomy),
//!   * requires the `stdio` platform DLL to be present (see test guard
//!     `stdio_dll_available`),
//!   * prints directly to the subprocess stderr (per §6 mode A, which is
//!     the default — per-thread ring buffers flushed at process exit).

use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

use cranelisp_runtime::io_trace::{
    IO_TRACE_BUFFER_CAPACITY, IoTraceEvent, IoTracePayload, IoTraceTag,
    dump_thread_buffer, record_event,
};

// -----------------------------------------------------------------------------
// Subprocess harness
// -----------------------------------------------------------------------------

static TEST_COUNTER: AtomicUsize = AtomicUsize::new(0);

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn binary_path() -> PathBuf {
    project_root().join("target").join("debug").join("cranelisp")
}

fn examples_dir() -> PathBuf {
    project_root().join("examples")
}

fn hello_io_path() -> PathBuf {
    examples_dir().join("21-hello-io.cl")
}

/// Is the `stdio` platform DLL built and available? Required for
/// `examples/21-hello-io.cl` to execute end-to-end. When absent, the
/// subprocess tests are un-runnable — we surface that as a single
/// diagnostic assertion rather than hiding behind `#[ignore]`.
fn stdio_dll_available() -> bool {
    let platforms = examples_dir().join("platforms");
    // macOS symlink → libcranelisp_stdio.dylib; Linux → .so; Windows → .dll.
    for name in ["stdio.dylib", "stdio.so", "stdio.dll"] {
        if platforms.join(name).exists() {
            return true;
        }
    }
    false
}

/// Run `cranelisp --run examples/21-hello-io.cl` in a fresh TempDir with
/// the supplied env vars. cwd is the TempDir — `examples/Cranelisp.toml`
/// is therefore NOT discovered; the binary falls back to default config.
/// This is intentional: we do not want this test's subprocess to populate
/// `examples/.cranelisp-cache/`.
fn run_hello_io_with_env(label: &str, env: &[(&str, &str)]) -> (Output, tempfile::TempDir) {
    let binary = binary_path();
    assert!(
        binary.exists(),
        "cranelisp binary not found at {binary:?} — run `cargo build` first"
    );
    let n = TEST_COUNTER.fetch_add(1, Ordering::SeqCst);
    let tmp = tempfile::Builder::new()
        .prefix(&format!("sprint61_io_{n}_{label}_"))
        .tempdir()
        .expect("TempDir creation");
    // Run from the examples directory so the stdio platform DLL is
    // resolved via `examples/platforms/stdio.<ext>`. The examples dir
    // is the natural home for the example's relative platform path.
    //
    // We still isolate the cache via `CRANELISP_CACHE_DIR` pointing to
    // the TempDir — each subprocess gets a fresh cache so cache-contents
    // are deterministic for the negative test T-S0B-7.
    let mut cmd = Command::new(&binary);
    cmd.args(["--run", hello_io_path().to_str().unwrap()])
        .current_dir(examples_dir())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    cmd.env_remove("CRANELISP_IO_TRACE");
    // Override cache dir so it lands inside the TempDir.
    cmd.env("CRANELISP_CACHE_DIR", tmp.path());
    for (k, v) in env {
        cmd.env(k, v);
    }
    let out = cmd.output().expect("failed to run cranelisp");
    (out, tmp)
}

fn stderr_of(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).to_string()
}

/// Exit code guard: spec §12.6 says main's Int return is the exit code.
/// `examples/21-hello-io.cl` returns a sum-of-passes per the examples
/// convention. The Sprint 60 Defect #2 signature is exit 201. Other
/// runtime crashes (signal-terminated, unknown-IO-tag panic) manifest
/// as 101 / 133 and are ALSO part of the same open-defect family —
/// fail loudly so the failure message points at the root cause rather
/// than reporting a confusing "no events observed" later.
fn assert_example_ran_cleanly(out: &Output) {
    let code = out.status.code();
    if code == Some(201) {
        panic!(
            "21-hello-io.cl exited 201 (Sprint 60 Defect #2 signature); \
             stderr=\n{}",
            stderr_of(out)
        );
    }
    // 101 (Rust panic), 133 (signal 5) are the other observed crash
    // modes during Sprint 61 Wave 1 /qa run. These are tracked under
    // Slice 4 and trigger an explicit failure so the observability
    // tests don't report a misleading "events absent" diagnostic.
    if matches!(code, Some(101) | Some(133)) {
        panic!(
            "21-hello-io.cl crashed (exit {:?}) — Slice 4 open defect. \
             stderr=\n{}",
            code,
            stderr_of(out)
        );
    }
    // Any other exit code is accepted — examples return a sum of
    // passes and non-zero IS often "success".
}

// -----------------------------------------------------------------------------
// S0-B tests (IO trampoline event log)
// -----------------------------------------------------------------------------

// spec: design/backend/io-trampoline-trace.md §9 AC 1 — trampoline event
// sequence contains TrampolineEnter ... TrampolineExit, plus at least
// one PlatformEffect for the stdio print. Equivalent to T-S0B-1.
#[test]
fn io_trace_hello_io_emits_full_trampoline_sequence() {
    if !stdio_dll_available() {
        // The example cannot run without the stdio DLL. Flag as a
        // precondition the implementation must satisfy — do NOT softly
        // pass. This mirrors `examples_run.rs`'s approach.
        panic!(
            "stdio platform DLL missing under examples/platforms — build with \
             `cargo build -p cranelisp-stdio` and symlink into \
             examples/platforms/. Test cannot proceed."
        );
    }
    let (out, _tmp) =
        run_hello_io_with_env("full_seq", &[("CRANELISP_IO_TRACE", "1")]);
    assert_example_ran_cleanly(&out);
    let stderr = stderr_of(&out);

    // Event-shaped lines (prefix `[IO] ts=…`, per io_trace::format_event_line).
    let event_lines: Vec<&str> = stderr
        .lines()
        .filter(|l| l.contains("[IO] ts=") && l.contains(" thr="))
        .collect();
    assert!(
        !event_lines.is_empty(),
        "expected at least one [IO] event line under CRANELISP_IO_TRACE=1; \
         stderr was:\n{stderr}"
    );

    let joined = event_lines.join("\n");
    assert!(
        joined.contains("TrampolineEnter"),
        "expected TrampolineEnter event; lines were:\n{joined}"
    );
    assert!(
        joined.contains("TrampolineExit"),
        "expected TrampolineExit event; lines were:\n{joined}"
    );
    assert!(
        joined.contains("PlatformEffect"),
        "expected at least one PlatformEffect (stdio print) event; \
         lines were:\n{joined}"
    );
}

// spec: design/backend/io-trampoline-trace.md §3 — every documented
// event type SHOULD be observable under realistic workloads. For
// `21-hello-io.cl` specifically, we expect: TrampolineEnter, PureStep,
// BindEnter/Exit, ContPush/Pop, PlatformEffect, TrampolineExit.
// ParSpark/ParJoin/ParSerialGroupEnter may not fire for a sequential
// hello-io program — those are asserted weakly. Equivalent to a
// taxonomy-coverage check.
#[test]
fn io_trace_hello_io_observes_core_sequential_event_types() {
    if !stdio_dll_available() {
        panic!("stdio platform DLL missing — see io_trace_hello_io_emits_full_trampoline_sequence");
    }
    let (out, _tmp) =
        run_hello_io_with_env("taxonomy", &[("CRANELISP_IO_TRACE", "1")]);
    assert_example_ran_cleanly(&out);
    let stderr = stderr_of(&out);

    // Core sequential event types — these MUST appear for a well-formed
    // hello-io run. Bind/Cont pairs shape the trampoline's main loop.
    for required in [
        "TrampolineEnter",
        "TrampolineExit",
        "PlatformEffect",
        "BindEnter",
        "ContPush",
        "ContPop",
    ] {
        assert!(
            stderr.contains(required),
            "expected event `{required}` in IO trace dump; stderr was:\n{stderr}"
        );
    }
}

// spec: design/backend/io-trampoline-trace.md §3 PlatformEffect payload —
// `scheduling_class: u8`. Equivalent to T-S0B-6.
#[test]
fn io_trace_platformeffect_carries_scheduling_class_byte() {
    if !stdio_dll_available() {
        panic!("stdio platform DLL missing — see io_trace_hello_io_emits_full_trampoline_sequence");
    }
    let (out, _tmp) =
        run_hello_io_with_env("sched_class", &[("CRANELISP_IO_TRACE", "1")]);
    assert_example_ran_cleanly(&out);
    let stderr = stderr_of(&out);

    // At least one PlatformEffect line. Shape (per io_trace::format_event_line):
    // `[IO] ts=N thr=…/O PlatformEffect\tthunk=0x… token=N sched_class=N`.
    let effect_lines: Vec<&str> = stderr
        .lines()
        .filter(|l| l.contains("PlatformEffect"))
        .collect();
    assert!(
        !effect_lines.is_empty(),
        "expected at least one PlatformEffect event; stderr was:\n{stderr}"
    );
    // The `sched_class=` fragment must appear on every such line —
    // the payload field is present even if its value is `0` (per the
    // post-implementation note in the design doc).
    for line in &effect_lines {
        assert!(
            line.contains("sched_class="),
            "PlatformEffect line missing `sched_class=` field: {line}"
        );
    }
}

// spec: design/backend/io-trampoline-trace.md §2 — unset = zero output.
// Equivalent to T-S0B-5 (negative).
#[test]
fn io_trace_unset_means_no_event_output_to_stderr() {
    if !stdio_dll_available() {
        panic!("stdio platform DLL missing — see io_trace_hello_io_emits_full_trampoline_sequence");
    }
    let (out, _tmp) = run_hello_io_with_env("unset", &[]);
    assert_example_ran_cleanly(&out);
    let stderr = stderr_of(&out);
    // `[IO] ts=` is the line prefix; absence means no IO event was
    // emitted. The test is resilient to other stderr traces (RC,
    // scheduler) that may be active in CI.
    assert!(
        !stderr.contains("[IO] ts="),
        "IO-trace event lines leaked when env var unset; stderr was:\n{stderr}"
    );
    // Tag names alone aren't a negative signature (they might appear
    // in unrelated error messages), but the framed event line is.
}

// spec: design/backend/io-trampoline-trace.md §5 + §9 AC 3 — events MUST
// NOT appear in any serialised artefact. We check the cache directory
// (the most likely place for stray serialisation to land). Equivalent
// to T-S0B-7 (negative).
#[test]
fn io_trace_event_types_absent_from_cache_meta_json() {
    if !stdio_dll_available() {
        panic!("stdio platform DLL missing — see io_trace_hello_io_emits_full_trampoline_sequence");
    }
    let (out, tmp) =
        run_hello_io_with_env("meta_json", &[("CRANELISP_IO_TRACE", "1")]);
    assert_example_ran_cleanly(&out);

    // Walk the cache directory for any `*.meta.json` (and `*.json` for
    // insurance against future cache format drift).
    let cache_root = tmp.path();
    let mut checked = 0usize;
    let mut leaks: Vec<String> = Vec::new();
    visit_json_files(cache_root, &mut |path, body| {
        checked += 1;
        for needle in [
            "IoTraceEvent",
            "IoTracePayload",
            "IoTraceTag",
            "TrampolineEnter",
            "TrampolineExit",
            "io_trace",
        ] {
            if body.contains(needle) {
                leaks.push(format!(
                    "{}: contains `{}`",
                    path.display(),
                    needle
                ));
            }
        }
    });
    assert!(
        leaks.is_empty(),
        "IO-trace types leaked into serialised cache artefacts: {leaks:?}"
    );
    // `checked` can be zero (cache may not have been populated for a
    // single --run). Record that as informational via a trace line —
    // the negative assertion above is sufficient.
    eprintln!("io_trace_event_types_absent_from_cache_meta_json: checked {checked} json files under {}", cache_root.display());
}

fn visit_json_files(dir: &std::path::Path, f: &mut impl FnMut(&std::path::Path, &str)) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let p = entry.path();
        if p.is_dir() {
            visit_json_files(&p, f);
            continue;
        }
        let name = p
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or_default();
        if (name.ends_with(".json") || name.ends_with(".meta.json"))
            && let Ok(body) = std::fs::read_to_string(&p)
        {
            f(&p, &body);
        }
    }
}

// spec: design/backend/io-trampoline-trace.md §6 — ring buffer
// discipline: oldest events are dropped at capacity (FIFO). The
// implementation's capacity is exported; assert the contract (bounded
// + reasonable), and exercise the ring-wrap behaviour directly where
// possible.
#[test]
fn io_trace_ring_buffer_bounded_by_capacity() {
    // Design: "bounded-capacity drop counter" (§7 acceptance + unit
    // tests), "older events are dropped". Exported capacity is the
    // public contract.
    //
    // Clippy flags these as constant-value asserts — that is
    // intentional: the test locks in the exported-symbol contract and
    // its bounds.
    const _: () = assert!(
        IO_TRACE_BUFFER_CAPACITY >= 4096,
        "IO trace capacity unreasonably small"
    );
    const _: () = assert!(
        IO_TRACE_BUFFER_CAPACITY <= 1_048_576,
        "IO trace capacity unreasonably large"
    );

    // Seed overflow. `record_event` short-circuits when filter=None
    // (typical in `cargo nextest` with env unset); in that branch the
    // body is a no-op and the implementation-owned unit test
    // `ring_buffer_wraps_at_capacity` is the exhaustive check. The
    // contract this integration test guards is that the constant
    // exists, is bounded, and the hot-path is `record_event(tag, payload)`.
    let _ = dump_thread_buffer();
    for i in 0..(IO_TRACE_BUFFER_CAPACITY + 3) {
        record_event(
            IoTraceTag::PureStep,
            IoTracePayload::PureStep { value: i as i64, is_fresh: false },
        );
    }
    let dumped: Vec<IoTraceEvent> = dump_thread_buffer();
    if dumped.is_empty() {
        return;
    }
    assert!(
        dumped.len() <= IO_TRACE_BUFFER_CAPACITY,
        "IO trace grew beyond capacity: {} > {}",
        dumped.len(),
        IO_TRACE_BUFFER_CAPACITY,
    );
}

// spec: design/backend/io-trampoline-trace.md §9 AC 2 — off-path
// performance regression `< 1%`. Integration-test scale cannot
// reliably distinguish 1% — wall-clock noise on `cargo run -- --run`
// is dominated by cache-state effects (cold vs warm compile) that
// swamp any trace-related delta by 2-3 orders of magnitude. The <1%
// acceptance gate is appropriate for a micro-benchmark, not a
// subprocess integration test.
//
// This test therefore asserts a much weaker structural property:
// running the same program twice with `CRANELISP_IO_TRACE` unset
// completes within a generous ceiling — proving the "unset" path
// isn't catastrophically slow. The true <1% gate is enforced at the
// micro-benchmark level (Slice 5 or later).
//
// FIXME(/qa S61 Wave 5): author a proper criterion-style
// microbenchmark alongside `cargo nextest run --ignored` that
// compares `record_event` filter-off cost against a no-op baseline
// at nanosecond resolution, yielding the <1% bound per
// design/backend/io-trampoline-trace.md §9 AC 2. Integration-test
// ceilings cannot substitute for microbenchmark-level measurement.
#[test]
fn io_trace_off_path_subprocess_completes_within_generous_ceiling() {
    if !stdio_dll_available() {
        panic!("stdio platform DLL missing — see io_trace_hello_io_emits_full_trampoline_sequence");
    }
    // Single run with env unset. 5 s is a generous upper bound — far
    // larger than any plausible trace-off overhead, small enough that
    // an accidental infinite loop is caught.
    let t0 = std::time::Instant::now();
    let (base, _tb) = run_hello_io_with_env("perf_base", &[]);
    let elapsed_ms = t0.elapsed().as_millis();
    assert_example_ran_cleanly(&base);
    assert!(
        elapsed_ms < 5_000,
        "off-path subprocess run {elapsed_ms}ms exceeds 5s generous ceiling \
         — either the example is stuck OR tracing-when-off overhead is \
         catastrophic. Tighten to <1% per FIXME(/qa S61 Wave 5) when \
         microbenchmark harness lands."
    );
}
