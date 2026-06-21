use super::*;
use std::sync::atomic::{AtomicUsize, Ordering as StdOrdering};

// Process-global observer state means these tests cannot run truly
// concurrently; nextest runs each test in its own process so this is
// safe under the project's `cargo nt` invocation. Within a single
// process the tests serialise via the OBSERVER_SLOT mutation +
// unregister-at-end discipline.

static TEST_OBSERVER_CALLS: AtomicUsize = AtomicUsize::new(0);
static LAST_TAG_BITS: AtomicUsize = AtomicUsize::new(usize::MAX);

fn record_observer(tag: IoEventTag, _event: &IoEvent) {
    TEST_OBSERVER_CALLS.fetch_add(1, StdOrdering::Relaxed);
    LAST_TAG_BITS.store(tag as usize, StdOrdering::Relaxed);
}

fn reset_counters() {
    TEST_OBSERVER_CALLS.store(0, StdOrdering::Relaxed);
    LAST_TAG_BITS.store(usize::MAX, StdOrdering::Relaxed);
}

#[test]
fn anchor_is_stable_across_calls() {
    let a = trace_anchor();
    let b = trace_anchor();
    assert!(std::ptr::eq(a, b), "trace_anchor must return the same Instant ref");
}

#[test]
fn unregistered_emit_is_no_op() {
    // Defensively make sure no observer is left from another test.
    register_io_observer(None);
    reset_counters();
    emit(
        IoEventTag::TrampolineEnter,
        &IoEvent::TrampolineEnter { io_ptr: 0x1234 },
    );
    assert_eq!(
        TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed),
        0,
        "unregistered emit must not invoke any observer",
    );
}

#[test]
fn register_then_emit_delivers_event() {
    reset_counters();
    register_io_observer(Some(record_observer));
    emit(
        IoEventTag::PlatformEffect,
        &IoEvent::PlatformEffect {
            thunk_ptr: 0xDEAD,
            resource_token: 1,
            scheduling_class: 0,
        },
    );
    // Cleanup BEFORE asserting — keep the OBSERVER_SLOT clean for siblings.
    register_io_observer(None);

    assert_eq!(
        TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed),
        1,
        "observer must be invoked once per emit when registered",
    );
    assert_eq!(
        LAST_TAG_BITS.load(StdOrdering::Relaxed),
        IoEventTag::PlatformEffect as usize,
        "observer must receive the correct tag",
    );
}

#[test]
fn unregister_after_register_disables_emit() {
    reset_counters();
    register_io_observer(Some(record_observer));
    emit(
        IoEventTag::TrampolineEnter,
        &IoEvent::TrampolineEnter { io_ptr: 1 },
    );
    register_io_observer(None);
    let count_before = TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed);
    emit(
        IoEventTag::TrampolineExit,
        &IoEvent::TrampolineExit { result: 0 },
    );
    let count_after = TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed);
    assert_eq!(
        count_before, count_after,
        "post-unregister emit must not invoke the observer",
    );
}

#[test]
fn last_observer_wins() {
    static FIRST_CALLS: AtomicUsize = AtomicUsize::new(0);
    static SECOND_CALLS: AtomicUsize = AtomicUsize::new(0);
    fn first(_t: IoEventTag, _e: &IoEvent) {
        FIRST_CALLS.fetch_add(1, StdOrdering::Relaxed);
    }
    fn second(_t: IoEventTag, _e: &IoEvent) {
        SECOND_CALLS.fetch_add(1, StdOrdering::Relaxed);
    }
    FIRST_CALLS.store(0, StdOrdering::Relaxed);
    SECOND_CALLS.store(0, StdOrdering::Relaxed);

    register_io_observer(Some(first));
    register_io_observer(Some(second));
    emit(IoEventTag::PureStep, &IoEvent::PureStep { value: 7, is_fresh: false });
    register_io_observer(None);

    assert_eq!(FIRST_CALLS.load(StdOrdering::Relaxed), 0, "old observer must not fire");
    assert_eq!(SECOND_CALLS.load(StdOrdering::Relaxed), 1, "new observer must fire");
}
