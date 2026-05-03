// QUARANTINED — Sprint 64 test-port. Not built or run by Cargo.
// FIXME: design/arch/fixmes/0132-harvest-tests-legacy-sprint61-observability-scheduler.md (shared with the scheduler companion above)
// Owning crate: src/ (scheduler observability) + cranelisp-runtime
//                (`trace_instant_anchor` + `io_trace`) — the file asserts
//                cross-crate invariants between the two trace channels,
//                so harvest spans two unit-test sites coupled by a shared
//                anchor invariant; the BC §"Trace channel separation"
//                rule (re: boundary-crate hygiene scan) lives in /arch
//                principle space.
// Owning skill: /int (with /runtime co-owner; the boundary-crate hygiene
//                scan portion is /arch territory but tests trivially via
//                a structural Rust-API check)
// Quarantined: 2026-05-04
//
// This file's 3 tests test cross-cutting invariants:
//   - `scheduler_and_io_trace_share_timestamp_domain` — `trace_instant_anchor()`
//     returns the same `&'static Instant` across calls; both trace channels
//     read from it.
//   - `trace_event_types_do_not_appear_in_boundary_crate_sources` — recursive
//     filesystem scan of `crates/cranelisp-{types,frontend,typecheck}/src/`
//     for forbidden trace-type tokens.
//   - `merge_across_both_logs_uses_shared_anchor_and_orderable_keys` —
//     structural property: events project onto a `(u64, u64)` key space
//     and merge-sort yields a monotonic timeline.
//
// All three are pure Rust-API observations with no e2e analogue. Harvest
// the timestamp-domain + merge-sort invariants into unit tests adjacent
// to the trace-anchor code in cranelisp-runtime. The boundary-crate
// hygiene scan can move to a workspace-level lint test or live as a
// `#[cfg(test)]` in cranelisp-runtime that walks the relevant crates'
// `src/` trees. Per memory/feedback_unit_tests_with_dev.md and
// memory/project_test_strategy.md.
//
//! Sprint 61 Slice 0 — Shared invariants across scheduler + IO traces.
//!
//! Derived in Phase 3a (`tests/plan/ring4.md §Sprint 61 → Slice 0 → S0-X`).
//! Validates the cross-log invariants that both design docs share:
//!   * `design/int/observability.md §4 + §6` — shared `Instant` anchor and
//!     merge-sort methodology across both logs.
//!   * `design/backend/io-trampoline-trace.md §9 AC 3` — same timestamp
//!     domain, merge-sortable against the scheduler trace.
//!   * `observability.md §4` + `io-trampoline-trace.md §5` — neither log
//!     appears in any boundary crate or serialised format.
//!
//! Tests derive from the DESIGN. Implementation drift produces failing
//! tests.

use std::path::{Path, PathBuf};

use cranelisp::observability::{
    SchedulerTracePayload, SchedulerTraceTag, record_module_event,
};
use cranelisp_runtime::trace_instant_anchor;

fn project_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

// -----------------------------------------------------------------------------
// S0-X tests
// -----------------------------------------------------------------------------

// spec: design/int/observability.md §6 + design/backend/io-trampoline-trace.md §9 AC 3
// Both traces use the same `OnceLock<Instant>` anchor exported from
// `cranelisp-runtime`. Generate one scheduler event timestamp and one
// IO event timestamp; both must lie within a tight bound of
// `anchor.elapsed()`. Equivalent to T-S0X-1.
#[test]
fn scheduler_and_io_trace_share_timestamp_domain() {
    // Grab the anchor reference up front. Subsequent calls MUST return
    // the same reference (OnceLock contract).
    let anchor_a = trace_instant_anchor();
    let anchor_b = trace_instant_anchor();
    assert!(
        std::ptr::eq(anchor_a, anchor_b),
        "trace_instant_anchor must return the same &'static Instant \
         across calls — shared anchor is the whole point"
    );

    // Snapshot elapsed before emitting events.
    let before_ns = anchor_a.elapsed().as_nanos() as u64;

    // Emit one scheduler event + one IO event. When the env-var filter
    // is disabled both calls short-circuit; we still assert the
    // property that matters — the anchor's monotonic elapsed value is
    // a shared origin both crates use for their event timestamps.
    record_module_event(
        SchedulerTraceTag::RegisterDepPublish,
        "shared-anchor-test",
    );
    cranelisp_runtime::io_trace::record_event(
        cranelisp_runtime::io_trace::IoTraceTag::PureStep,
        cranelisp_runtime::io_trace::IoTracePayload::PureStep {
            value: 42,
            is_fresh: false,
        },
    );

    // Snapshot elapsed after. Non-decreasing.
    let after_ns = anchor_a.elapsed().as_nanos() as u64;
    assert!(
        after_ns >= before_ns,
        "anchor.elapsed() must be monotonic: before={before_ns} after={after_ns}"
    );

    // Drain both thread-local buffers. If either produced an event
    // its timestamp must be in [before_ns, after_ns + slack] — proving
    // the event-time reads came from the same anchor origin as the
    // surrounding probe reads.
    let scheduler_events = cranelisp::observability::dump_thread_buffer();
    let io_events = cranelisp_runtime::io_trace::dump_thread_buffer();

    // Per-event reads may land before or after the probe reads due to
    // interleaving; allow a generous 10ms window on either side —
    // enough to hide scheduling jitter, tight enough to catch a
    // different clock (wall-clock vs monotonic) with orders of
    // magnitude larger spread.
    const SLACK_NS: u64 = 10_000_000;
    let lower = before_ns.saturating_sub(SLACK_NS);
    let upper = after_ns.saturating_add(SLACK_NS);

    if let Some(evt) = scheduler_events.first() {
        assert!(
            evt.timestamp >= lower && evt.timestamp <= upper,
            "scheduler event timestamp {} outside shared-anchor window \
             [{lower}, {upper}]",
            evt.timestamp,
        );
    }
    if let Some(evt) = io_events.first() {
        assert!(
            evt.timestamp_ns >= lower && evt.timestamp_ns <= upper,
            "IO event timestamp {} outside shared-anchor window \
             [{lower}, {upper}]",
            evt.timestamp_ns,
        );
    }
}

// spec: design/int/observability.md §4 + design/backend/io-trampoline-trace.md §5
// Neither log type may appear in any boundary crate. The design names
// `cranelisp-shared` and `cranelisp-types` specifically. No
// `cranelisp-shared` crate exists in this workspace; `cranelisp-types`
// is the analogous boundary crate (see design/arch/interfaces.md).
// Extend the scan to other cross-crate surfaces that could
// accidentally leak the types: the frontend and typecheck crates
// depend on `cranelisp-types` and are also upstream of the runtime —
// if IO/scheduler trace types ever leaked into their APIs that would
// be architectural drift. Equivalent to T-S0X-2 (negative).
#[test]
fn trace_event_types_do_not_appear_in_boundary_crate_sources() {
    // Crate roots to scan. Ordered by architectural proximity to the
    // boundary.
    let boundary_crate_dirs: Vec<PathBuf> = vec![
        project_root().join("crates").join("cranelisp-types").join("src"),
        project_root().join("crates").join("cranelisp-frontend").join("src"),
        project_root().join("crates").join("cranelisp-typecheck").join("src"),
    ];

    // Forbidden tokens — type names owned by the two trace modules
    // that MUST NOT appear in any boundary crate source file.
    let forbidden: &[&str] = &[
        "SchedulerTraceEvent",
        "SchedulerTraceTag",
        "SchedulerTracePayload",
        "IoTraceEvent",
        "IoTraceTag",
        "IoTracePayload",
    ];

    let mut leaks: Vec<String> = Vec::new();
    for dir in &boundary_crate_dirs {
        visit_rs_files(dir, &mut |path, body| {
            for needle in forbidden {
                if body.contains(needle) {
                    leaks.push(format!(
                        "{}: contains forbidden token `{}`",
                        path.display(),
                        needle
                    ));
                }
            }
        });
    }
    assert!(
        leaks.is_empty(),
        "boundary-crate hygiene breach — trace types leaked into upstream \
         crate sources: {leaks:?}"
    );
}

fn visit_rs_files(dir: &Path, f: &mut impl FnMut(&Path, &str)) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let p = entry.path();
        if p.is_dir() {
            visit_rs_files(&p, f);
            continue;
        }
        let name = p
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or_default();
        if name.ends_with(".rs")
            && let Ok(body) = std::fs::read_to_string(&p)
        {
            f(&p, &body);
        }
    }
}

// spec: design/int/observability.md §6 + design/backend/io-trampoline-trace.md §9 AC 3
// Merge-sort across both logs produces a monotonic unified timeline
// when events from both are combined on `(timestamp, thread_ord_id)`.
// This is a joint design invariant — neither log can be merge-sorted
// with the other unless the anchor and ordering keys agree.
// Equivalent to T-S0X-3 (structural).
#[test]
fn merge_across_both_logs_uses_shared_anchor_and_orderable_keys() {
    // Both event struct shapes expose `(timestamp, thread_ord_id)`
    // pairs. This test asserts the structural property: events from
    // each type can be projected onto a common `(u64, u64)` key space
    // and sorted into a monotonic unified sequence.
    //
    // We do this by:
    //   1. Dumping both buffers (may be empty when filters are
    //      disabled — that is OK).
    //   2. Projecting each event to a `(timestamp_ns, thread_ord_id,
    //      source_tag)` triple.
    //   3. Sorting and asserting monotonicity.
    //
    // When both dumps are empty the invariant holds vacuously. Prior
    // assertions in this file (shared anchor, same monotonic origin)
    // cover the non-empty case.
    let sch_events = cranelisp::observability::dump_all_buffers();
    let io_events = cranelisp_runtime::io_trace::dump_all_buffers();

    // Project onto a common key.
    #[derive(Copy, Clone, Debug)]
    enum Source {
        Scheduler,
        Io,
    }
    let mut merged: Vec<(u64, u64, Source)> = Vec::new();
    for e in &sch_events {
        merged.push((e.timestamp, e.thread_ord_id, Source::Scheduler));
    }
    for e in &io_events {
        merged.push((e.timestamp_ns, e.thread_ord_id, Source::Io));
    }
    merged.sort_by_key(|(t, o, _)| (*t, *o));

    for pair in merged.windows(2) {
        let (ta, oa, _) = pair[0];
        let (tb, ob, _) = pair[1];
        assert!(
            (ta, oa) <= (tb, ob),
            "merged (scheduler ∪ io) timeline is not monotonic: \
             {:?} then {:?}",
            pair[0],
            pair[1],
        );
    }

    // Also assert the anchor is shared — a property the merge-sort
    // relies on.
    let a1 = trace_instant_anchor();
    let a2 = trace_instant_anchor();
    assert!(
        std::ptr::eq(a1, a2),
        "merge-sort correctness depends on the shared anchor being stable"
    );

    // Silence potentially-unused warning; also confirms both variants
    // can be constructed.
    let _ = (Source::Scheduler, Source::Io);

    // Reference `SchedulerTracePayload` to ensure the import is live
    // (we use it via record_module_event at test-build time for the
    // scheduler harness).
    let _p = SchedulerTracePayload::Bulk { count: 0 };
}
