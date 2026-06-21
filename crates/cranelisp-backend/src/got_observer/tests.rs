use super::*;
use std::sync::atomic::{AtomicUsize, Ordering as StdOrdering};

// Process-global observer state means these tests cannot run truly
// concurrently; nextest runs each test in its own process so this is
// safe under the project's `cargo nt` invocation. Within a single
// process the tests serialise via the OBSERVER_SLOT mutation +
// unregister-at-end discipline.

static TEST_OBSERVER_CALLS: AtomicUsize = AtomicUsize::new(0);
static LAST_TAG_BITS: AtomicUsize = AtomicUsize::new(usize::MAX);

fn record_observer(tag: GotEventTag, _event: &GotEvent) {
    TEST_OBSERVER_CALLS.fetch_add(1, StdOrdering::Relaxed);
    LAST_TAG_BITS.store(tag as usize, StdOrdering::Relaxed);
}

fn reset_counters() {
    TEST_OBSERVER_CALLS.store(0, StdOrdering::Relaxed);
    LAST_TAG_BITS.store(usize::MAX, StdOrdering::Relaxed);
}

fn fake_event() -> GotEvent {
    GotEvent {
        module: ModuleFullPath::from("user"),
        symbol: Symbol::from("foo"),
        slot: 0,
        ptr: 0xDEAD_BEEF as *const u8,
        provenance: GotProvenance::Jit { jit_addr: 0xABCD },
    }
}

#[test]
fn unregistered_emit_is_no_op() {
    // Defensively make sure no observer is left from another test.
    register_got_observer(None);
    reset_counters();
    emit(GotEventTag::JitWrite, &fake_event());
    assert_eq!(
        TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed),
        0,
        "unregistered emit must not invoke any observer",
    );
}

#[test]
fn register_then_emit_delivers_event() {
    reset_counters();
    register_got_observer(Some(record_observer));
    emit(GotEventTag::LinkerWrite, &fake_event());
    // Cleanup BEFORE asserting — keep the OBSERVER_SLOT clean for siblings.
    register_got_observer(None);

    assert_eq!(
        TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed),
        1,
        "observer must be invoked once per emit when registered",
    );
    assert_eq!(
        LAST_TAG_BITS.load(StdOrdering::Relaxed),
        GotEventTag::LinkerWrite as usize,
        "observer must receive the correct tag",
    );
}

#[test]
fn unregister_after_register_disables_emit() {
    reset_counters();
    register_got_observer(Some(record_observer));
    emit(GotEventTag::JitWrite, &fake_event());
    register_got_observer(None);
    let count_before = TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed);
    emit(GotEventTag::Redefinition, &fake_event());
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
    fn first(_t: GotEventTag, _e: &GotEvent) {
        FIRST_CALLS.fetch_add(1, StdOrdering::Relaxed);
    }
    fn second(_t: GotEventTag, _e: &GotEvent) {
        SECOND_CALLS.fetch_add(1, StdOrdering::Relaxed);
    }
    FIRST_CALLS.store(0, StdOrdering::Relaxed);
    SECOND_CALLS.store(0, StdOrdering::Relaxed);

    register_got_observer(Some(first));
    register_got_observer(Some(second));
    emit(GotEventTag::JitWrite, &fake_event());
    register_got_observer(None);

    assert_eq!(
        FIRST_CALLS.load(StdOrdering::Relaxed),
        0,
        "old observer must not fire after replacement"
    );
    assert_eq!(
        SECOND_CALLS.load(StdOrdering::Relaxed),
        1,
        "new observer must fire"
    );
}

#[test]
fn all_three_tags_round_trip_through_observer() {
    // Sanity: every published tag variant flows through emit to the
    // observer correctly. Catches the "added a tag but forgot the
    // dispatch path" regression.
    reset_counters();
    register_got_observer(Some(record_observer));
    for tag in [
        GotEventTag::JitWrite,
        GotEventTag::LinkerWrite,
        GotEventTag::Redefinition,
    ] {
        emit(tag, &fake_event());
    }
    register_got_observer(None);
    assert_eq!(
        TEST_OBSERVER_CALLS.load(StdOrdering::Relaxed),
        3,
        "each emit must invoke the observer exactly once"
    );
}
