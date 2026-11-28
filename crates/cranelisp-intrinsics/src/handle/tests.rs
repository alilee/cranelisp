use super::*;
use crate::source_census::{expected, production_sources, token_sites};
use std::path::Path;

// spec: design/runtime/s119-typed-consume-funnel.md §5 — dropping an armed
// owner without discharging it is a located debug failure.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "LEAKED Owned heap handle")]
fn leaked_owner_trips_the_debug_drop_bomb() {
    let raw = crate::heap_string::alloc_string(b"leaked") as i64;
    let _owner = unsafe { Owned::from_abi(raw) };
}

// spec: design/runtime/s119-typed-consume-funnel.md §5 — consuming the same
// fixture disarms the owner and balances its allocation without a false alarm.
#[cfg(debug_assertions)]
#[test]
fn consumed_owner_is_silent_and_balanced() {
    let allocs_before = crate::alloc::alloc_count();
    let deallocs_before = crate::alloc::dealloc_count();
    let raw = crate::heap_string::alloc_string(b"consumed") as i64;
    let owner = unsafe { Owned::from_abi(raw) };

    crate::rc::consume_shallow(owner);

    assert_eq!(
        crate::alloc::alloc_count() - allocs_before,
        crate::alloc::dealloc_count() - deallocs_before,
        "the consumed handle fixture must balance"
    );
}

// spec: design/runtime/s119-typed-consume-funnel.md §5 — an unrelated unwind
// remains survivable while an owner is in scope.
#[cfg(debug_assertions)]
#[test]
#[should_panic(expected = "unrelated handle test panic")]
fn owner_drop_during_unrelated_unwind_does_not_double_panic() {
    let raw = crate::heap_string::alloc_string(b"unwind") as i64;
    let _owner = unsafe { Owned::from_abi(raw) };
    panic!("unrelated handle test panic");
}

// spec: design/runtime/s119-typed-consume-funnel.md §3 — the unsafe adoption
// and disarm vocabulary remains confined to the approved intrinsics seams.
#[test]
fn typed_handle_trusted_base_matches_the_approved_intrinsics_allow_list() {
    let sources = production_sources();

    assert_eq!(
        token_sites(&sources, "Owned::from_abi"),
        expected(&[
            ("drop.rs::consume_vec_with", 1),
            ("drop.rs::owned_field", 1),
            ("handle.rs::Borrowed::to_owned", 1),
            ("handle.rs::test_owned", 1),
            ("io.rs::ProducedValue::drop", 1),
            ("io.rs::TrampolineFrame::drop", 2),
            ("io.rs::call_continuation", 1),
            ("io.rs::cranelisp_run_io", 1),
            ("io.rs::feed_continuation", 2),
            ("io.rs::read_bind_transition", 1),
            ("panic.rs::cranelisp_run_program", 1),
            ("reactor.rs::StateClosure::consume", 1),
            ("reactor.rs::supervised", 1),
            ("trace.rs::consume_slist_of_string", 2),
            ("trace.rs::consume_slist_of_trace", 2),
            ("trace.rs::consume_trace_call", 4),
            ("trace.rs::cranelisp_trace_children", 1),
            ("trace.rs::cranelisp_trace_name", 1),
            ("trace.rs::cranelisp_trace_nanos", 1),
            ("trace.rs::cranelisp_trace_params", 1),
            ("trace.rs::cranelisp_trace_result", 1),
            ("vec_runtime.rs::UnpublishedVecStrings::drop", 1),
        ])
    );
    assert_eq!(
        token_sites(&sources, "Borrowed::from_abi"),
        expected(&[("io.rs::borrowed_io_field", 1)])
    );
    assert_eq!(
        token_sites(&sources, "borrowed_io_field("),
        expected(&[("io.rs::read_bind_transition", 2)])
    );
    assert_eq!(
        token_sites(&sources, ".to_owned()"),
        expected(&[("io.rs::read_bind_transition", 2)])
    );

    assert_eq!(
        token_sites(&sources, "mem::forget"),
        expected(&[
            ("handle.rs::Owned::into_raw", 1),
            ("reactor.rs::OwnedCWaker::wake", 1),
        ])
    );

    let handle = &sources[Path::new("handle.rs")];
    let owned_decl = handle.find("pub struct Owned").unwrap();
    let owned_attributes = &handle[owned_decl.saturating_sub(300)..owned_decl];
    assert!(!owned_attributes.contains("derive(Clone"));
    assert!(!owned_attributes.contains("derive(Copy"));
    assert!(!handle.contains("impl Clone for Owned"));
    assert!(!handle.contains("impl Copy for Owned"));
    assert!(!sources[Path::new("drop.rs")].contains("pub type ElemConsumeFn"));
}
