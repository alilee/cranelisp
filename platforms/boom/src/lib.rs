//! `boom` platform for cranelisp -- the dispatch-fault test-DLL fixture.
//!
//! Sprint 81 Wave G (the fault-guarded FFI-dispatch funnel, step 4/4 — FIXME
//! 0327 close-out + FIXME 0289 item 5). The minimal platform whose single fn
//! returns an `IO Int` Effect whose **forced thunk deliberately faults** (a
//! Rust `panic!`), so the intrinsics IO trampoline's fault guard
//! (`force_effect_thunk_protected`) captures it and int composes a structured
//! `PlatformError::DispatchError { fn_name }` naming the offending fn.
//!
//! ## Why this fixture exists
//!
//! The real `stdio`/`test-capture`/`shapes` platforms never fault at dispatch
//! time, so no e2e against them can exercise the `DispatchError` carrier. This
//! fixture is the smallest thing that triggers a dispatch-time fault with a
//! KNOWN cranelisp fn-name: the backend bakes the FQ name `platform.boom/crash`
//! into the returned Effect node's field-3, and after the fault the surfaced
//! error names exactly that fn.
//!
//! ## Minimal by design
//!
//! Scalar-only (mirrors `stdio`, NOT the ADT-typed `shapes`): `crash` takes no
//! arguments and returns `IO Int`, so there is no ADT marshaling, no schema
//! artifact, and no `__cranelisp_layout_hash`. It exists ONLY to fault. The
//! ADT-typed `shapes` round-trip + drift e2e (FIXME 0289 items 1-4) is separate
//! scope and stays open.
//!
//! ## The fault
//!
//! A Rust `panic!` is the cleanest, most portable fault — `catch_unwind` in the
//! guard recovers it on every OS without depending on a signal trap. (A SIGSEGV
//! null-deref would exercise the `sigsetjmp` signal path instead; the funnel
//! handles both, but the panic path is sufficient and portable.) All platform
//! fns MUST return `IO _` (FIXME 0318) — the fault is raised when the Effect is
//! FORCED by the trampoline, not when `crash` is called, which is exactly the
//! dispatch-time site the funnel guards.

use cranelisp_platform::*;

static HOST: HostContext = HostContext::new();

/// A platform fn whose forced IO Effect thunk deliberately panics.
///
/// Returns a deferred `IO Int` Effect (all platform fns MUST return `IO _` —
/// FIXME 0318). The `crash` call itself returns the Effect node cleanly; the
/// `panic!` fires only when the trampoline FORCES the thunk — the dispatch-time
/// fault site the funnel guard (`force_effect_thunk_protected`) wraps. The
/// guard's `catch_unwind` captures the panic, pairs it with the backend-baked
/// fn-name from the Effect node's field-3, and int composes
/// `PlatformError::DispatchError { fn_name: "platform.boom/crash", .. }`.
pub extern "C" fn crash() -> CLIO<CLInt> {
    CLIO::effect(move || {
        panic!("boom: deliberate dispatch-time fault in platform fn `crash`");
        #[allow(unreachable_code)]
        CLInt::from(0i64)
    })
}

declare_platform! {
    name: "boom",
    version: "0.1.0",
    host: HOST,
    functions: [
        crash {
            cl_name: "crash",
            sig: "(Fn [] (primitives/IO primitives/Int))",
            doc: "Deliberately fault when its IO Effect is forced (dispatch-fault test fixture)",
            params: [],
            scheduling: SchedulingClass::Sequential,
        },
    ]
}
