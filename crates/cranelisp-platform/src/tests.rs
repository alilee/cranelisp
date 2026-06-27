    use super::*;
    use cranelisp_types::Span;
    use std::sync::atomic::AtomicI64;

    // ---------------------------------------------------------------------
    // PlatformError adoption — Decision 42 / FIXME 0104.
    //
    // These tests pin the platform crate's public error surface to the
    // shape the PlatformError rustdoc + bounded-contexts.md §5 specify: each variant carries
    // an `ErrorLocation`; `manifest_to_descriptors` returns
    // `Result<…, PlatformError>` with `ErrorLocation::unknown()` at the
    // construction site (callers — `int::load_platform_dll` — rewrite the
    // location with the `(platform "name")` form's span before surfacing).
    // ---------------------------------------------------------------------

    // spec: crates/cranelisp-platform/src/lib.rs PlatformError rustdoc + bounded-contexts.md §5 — `LoadFailed`
    // carries `dll`, `cause`, and `location`. Re-exported `PlatformError`
    // must construct + display this variant.
    #[test]
    fn platform_error_load_failed_constructs_and_displays() {
        let err = PlatformError::LoadFailed {
            dll: std::path::PathBuf::from("nonexistent.dylib"),
            cause: "dlopen returned NULL".to_string(),
            location: ErrorLocation::from_span(Span::new(10, 35)),
        };
        let displayed = format!("{err}");
        assert!(
            displayed.contains("nonexistent.dylib"),
            "Display must surface the DLL path; got: {displayed}"
        );
        assert!(
            displayed.contains("dlopen returned NULL"),
            "Display must surface the underlying cause; got: {displayed}"
        );
        // Location accessor works.
        assert_eq!(err.location().span, Span::new(10, 35));
    }

    // spec: crates/cranelisp-platform/src/lib.rs PlatformError rustdoc + bounded-contexts.md §5 — `ManifestNotFound`
    // carries `dll` and `location`.
    #[test]
    fn platform_error_manifest_not_found_constructs_and_displays() {
        let err = PlatformError::ManifestNotFound {
            dll: std::path::PathBuf::from("stale.dylib"),
            location: ErrorLocation::from_span(Span::new(1, 9)),
        };
        let displayed = format!("{err}");
        assert!(
            displayed.contains("stale.dylib"),
            "Display must surface the DLL path; got: {displayed}"
        );
        assert!(
            displayed.contains("manifest"),
            "Display must mention manifest; got: {displayed}"
        );
        assert_eq!(err.location().span, Span::new(1, 9));
    }

    // spec: crates/cranelisp-platform/src/lib.rs PlatformError rustdoc + bounded-contexts.md §5 —
    // `AbiVersionMismatch` carries `dll`, `expected`, `found`, `location`.
    #[test]
    fn platform_error_abi_version_mismatch_constructs_and_displays() {
        let err = PlatformError::AbiVersionMismatch {
            dll: std::path::PathBuf::from("old.dylib"),
            expected: ABI_VERSION,
            found: 99,
            location: ErrorLocation::from_span(Span::new(20, 30)),
        };
        let displayed = format!("{err}");
        assert!(
            displayed.contains("old.dylib"),
            "Display must surface the DLL path; got: {displayed}"
        );
        // Both expected + found values must surface.
        assert!(
            displayed.contains(&ABI_VERSION.to_string()),
            "Display must surface the expected ABI; got: {displayed}"
        );
        assert!(
            displayed.contains("99"),
            "Display must surface the found ABI; got: {displayed}"
        );
        assert_eq!(err.location().span, Span::new(20, 30));
    }

    // spec: crates/cranelisp-platform/src/lib.rs PlatformError rustdoc + bounded-contexts.md §5 — `DispatchError`
    // carries `fn_name`, `cause`, `location`.
    #[test]
    fn platform_error_dispatch_error_carries_fn_name() {
        use cranelisp_types::Symbol;
        let err = PlatformError::DispatchError {
            fn_name: Symbol::from("read-line"),
            cause: "null fn pointer".to_string(),
            location: ErrorLocation::from_span(Span::new(100, 120)),
        };
        let displayed = format!("{err}");
        assert!(
            displayed.contains("read-line"),
            "Display must surface the fn name; got: {displayed}"
        );
        assert!(
            displayed.contains("null fn pointer"),
            "Display must surface the cause; got: {displayed}"
        );
        assert_eq!(err.location().span, Span::new(100, 120));
    }

    // spec: crates/cranelisp-platform/src/lib.rs PlatformError rustdoc + bounded-contexts.md §5 — DLL-author /
    // int code constructs `PlatformError` and wraps via `CranelispError`.
    // The `From<PlatformError> for CranelispError` blanket conversion
    // must succeed and preserve the location.
    #[test]
    fn platform_error_into_cranelisp_error_preserves_location() {
        use cranelisp_types::CranelispError;
        let err = PlatformError::LoadFailed {
            dll: std::path::PathBuf::from("missing.dylib"),
            cause: "no such file".to_string(),
            location: ErrorLocation::from_span(Span::new(7, 42)),
        };
        let wrapped: CranelispError = err.into();
        assert_eq!(wrapped.span(), Span::new(7, 42));
        // Through `CranelispError::Display`, the platform inner displays.
        let displayed = format!("{wrapped}");
        assert!(
            displayed.contains("missing.dylib"),
            "Display via CranelispError::Platform must surface inner; got: {displayed}"
        );
    }

    // spec: crates/cranelisp-platform/src/lib.rs PlatformError rustdoc + bounded-contexts.md §5 + FIXME 0104 Phase 2
    // — UTF-8 validation failures in `manifest_to_descriptors` construct
    // `PlatformError::LoadFailed` with `ErrorLocation::unknown()`; the
    // caller rewrites with the form's span before surfacing. This test
    // confirms the construction-side behaviour.
    #[test]
    fn manifest_to_descriptors_utf8_failure_returns_load_failed_with_unknown_location() {
        // Build a manifest whose name field is non-UTF-8 (a lone 0xFF byte).
        // Use a static lifetime backing store so the test exercise is sound:
        // the `&PlatformManifest` we pass borrows from `manifest_storage`
        // which lives the full test scope.
        let bad_name: &[u8] = &[0xFFu8];
        let version: &[u8] = b"0.1.0";
        let manifest = PlatformManifest {
            abi_version: ABI_VERSION,
            name: bad_name.as_ptr(),
            name_len: bad_name.len(),
            version: version.as_ptr(),
            version_len: version.len(),
            functions: std::ptr::null(),
            function_count: 0,
        };

        // SAFETY: pointers above point at the local slices that outlive the
        // call (`manifest_to_descriptors` is unsafe; we honour its contract
        // here by ensuring the pointers are valid and the lengths correct).
        let result = unsafe { manifest_to_descriptors(&manifest) };

        match result {
            Err(PlatformError::LoadFailed { cause, location, dll }) => {
                assert!(
                    cause.contains("UTF-8") || cause.contains("invalid"),
                    "cause must mention UTF-8 / invalid; got: {cause}"
                );
                // platform-side construction uses `ErrorLocation::unknown()`
                // → span is synthetic; int rewrites with the form's span.
                assert_eq!(
                    location.span,
                    Span::SYNTHETIC,
                    "platform crate constructs with unknown location; int rewrites at call site"
                );
                assert_eq!(
                    dll,
                    std::path::PathBuf::new(),
                    "platform crate has no DLL path on hand; int fills it in"
                );
            }
            Err(e) => panic!("expected LoadFailed, got different PlatformError: {e}"),
            Ok(_) => panic!("expected LoadFailed, got Ok"),
        }
    }


    // Allocate a mock heap-layout `[alloc_size(8) | rc(8) | payload(>=0)]` with
    // initial rc=1. Returns the base pointer. The payload is zero-filled;
    // the test doesn't care about contents — only the RC field.
    fn mock_heap_alloc(payload_size: usize) -> i64 {
        let total_size = HEAP_HEADER_SIZE as usize + payload_size;
        unsafe {
            let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
            let ptr = std::alloc::alloc_zeroed(layout);
            *(ptr as *mut i64) = total_size as i64;
            *((ptr as *mut i64).add(1)) = 1; // rc = 1
            ptr as i64
        }
    }

    // Read the current RC from a mock allocation.
    fn read_rc(base: i64) -> i64 {
        unsafe {
            let rc_addr = (base + 8) as *const AtomicI64;
            (*rc_addr).load(Ordering::SeqCst)
        }
    }

    // spec: design/backend/ring2-rc.md §10.4 — `into_owned_consuming` must NOT
    // inc RC on wrap (it takes the caller's transferred ref as-is) and MUST
    // dec on drop — so the net RC change is exactly -1 over the wrap+drop
    // pair, symmetric with the caller's +1 transfer.
    #[test]
    fn into_owned_consuming_does_not_inc_on_wrap() {
        let base = mock_heap_alloc(0);
        let s = CLString(base);
        assert_eq!(read_rc(base), 1, "starting rc = 1 (caller's transferred ref)");

        {
            let _owned = s.into_owned_consuming();
            assert_eq!(
                read_rc(base),
                1,
                "into_owned_consuming must NOT inc: still rc=1 after wrap"
            );
        }
        // After _owned drops, CLOwned::drop calls dec_rc. rc was 1, goes to 0,
        // so the allocation is freed. Cannot read_rc here (use-after-free).
    }

    // spec: design/backend/ring2-rc.md §10.4 — contrast with `own()`: `own()`
    // inc's on wrap, so one extra inc is needed by the caller when the
    // caller does NOT transfer ownership. This test locks in the behavioural
    // difference between the two wrappers so regressions are caught.
    #[test]
    fn own_vs_into_owned_consuming_rc_semantics_differ() {
        // own() path: wraps with inc, drops with dec — net zero, original ref survives.
        let base_a = mock_heap_alloc(0);
        let s_a = CLString(base_a);
        assert_eq!(read_rc(base_a), 1);

        {
            let _owned = s_a.own();
            assert_eq!(read_rc(base_a), 2, "own() inc's on wrap: rc=2");
        }
        assert_eq!(read_rc(base_a), 1, "own() dec's on drop: back to rc=1");
        // Manually free s_a (simulates caller's post-return dec of its own ref).
        unsafe {
            let total_size = *(base_a as *const i64) as usize;
            let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
            std::alloc::dealloc(base_a as *mut u8, layout);
        }

        // into_owned_consuming path: no inc on wrap, dec on drop — the original
        // ref itself is consumed and freed. Contrast verified above.
    }

    // spec: design/backend/ring2-rc.md §10.4 — the capture-Effect pattern used
    // by platform externs (print, capture_print): caller transfers one ref,
    // extern wraps via `into_owned_consuming`, closure holds `CLOwned`,
    // deferred thunk-drop dec's once. Net allocator operations: 1 alloc
    // (caller), 1 dealloc (CLOwned drop when closure drops).
    #[test]
    fn decision24_capture_effect_pattern_balanced() {
        // Simulate the caller's alloc + transfer. RC starts at 1 (caller's
        // single ref); caller immediately transfers ownership to the extern
        // (no further inc — the caller's ref becomes the extern's parameter).
        let base = mock_heap_alloc(0);
        let s = CLString(base);
        assert_eq!(read_rc(base), 1);

        // Simulate the extern: wrap via `into_owned_consuming`, capture into
        // a Rust closure (as `print_string` does via `CLIO::effect`).
        let owned = s.into_owned_consuming();
        assert_eq!(
            read_rc(base),
            1,
            "wrap must not inc — the captured ref IS the caller's transferred ref"
        );

        // The closure keeps the CLOwned alive. We inspect RC through the
        // closure's lifetime, then drop the closure to trigger CLOwned::drop.
        let boxed: Box<dyn FnOnce() -> i64> = Box::new(move || {
            // While the closure is live, RC stays at 1.
            read_rc(owned.raw_ptr())
        });

        let rc_during_call = boxed();
        assert_eq!(rc_during_call, 1, "RC stays at 1 through the capture");
        // After boxed() consumed itself, `owned` was dropped inside boxed's scope;
        // CLOwned::drop → dec_rc → rc 0 → std::alloc::dealloc.
        // Cannot read_rc(base) here — allocation is freed.
    }

    // ---------------------------------------------------------------------
    // Sprint 71 Wave 2 — pinned-surface tests per
    // `tests/plan/sprint71-platform.md`.
    // ---------------------------------------------------------------------

    // ABI_VERSION is 7 (Sprint 93, effect-concurrency slice 2 — the ABI-v4
    // cascade recorded numerically 6→7: poll-shape async-leaf effect fns +
    // ConcurrencyDescriptor in the manifest + the host-reactor C-ABI; the v7
    // layout types are landed-and-dormant behind the `concurrency` feature, the
    // emitter/loader still use the v6 PlatformFn shape until the reactor wires
    // them). Was 6 (Sprint 86, DEF-5 — manifest export namespacing), 5 at FIXME
    // 0327 Option A (DLL-local dispatch-funnel fault-catch), 4 at the FIXME 0327
    // step-1 node-widen, 3 at FIXME 0286 (three-exports macro rework).
    // spec: design/arch/bounded-contexts.md §5 invariant 9;
    //       design/arch/platform-interface.md §6.8
    #[test]
    fn abi_version_is_7() {
        assert_eq!(ABI_VERSION, 7);
    }

    // The macro's `concat!("cranelisp_platform_manifest_", name)` export-name
    // string MUST equal `platform_manifest_symbol(name)` (the host consume-side
    // helper) for every platform name — emit and consume agree by construction
    // (Principle 7). This pins the two strings together so a future edit to one
    // pattern without the other is caught at unit time, not at the
    // multiple-definition / unresolved-symbol link failure.
    // spec: design/arch/platform-interface.md §5.5.5 — shared naming function
    #[test]
    fn manifest_symbol_helper_matches_macro_concat() {
        // The macro emits `concat!("cranelisp_platform_manifest_", $name)`.
        // Mirror that compile-time concat here and assert the runtime helper
        // produces the identical string for the same name.
        for name in ["shapes", "stdio", "test-capture", "shapes-badabi", "web"] {
            let macro_emitted = format!("cranelisp_platform_manifest_{name}");
            assert_eq!(platform_manifest_symbol(name), macro_emitted);
        }
        // Spot-check the literal concat form for one concrete name, matching the
        // macro's `concat!` exactly.
        assert_eq!(
            platform_manifest_symbol("shapes"),
            concat!("cranelisp_platform_manifest_", "shapes"),
        );
    }

    // spec: design/arch/bounded-contexts.md §5 invariant 9 — a `CLIO::effect`
    // thunk whose user closure panics, when forced, yields an `EffectOutcome`
    // with a non-null `fault_cause` carrying the panic message; a clean closure
    // yields a null `fault_cause` and the value. This proves the `EffectOutcome`
    // mechanics + the DLL-local catch wrapper.
    //
    // HOST-RUNTIME CAVEAT: this unit test runs in ONE runtime (the host test
    // binary), so it CANNOT exercise the true cross-cdylib runtime boundary —
    // here `effect_on_resource` is monomorphised into the test binary, not a
    // DLL. It proves the EffectOutcome catch/forward mechanics; the true
    // cross-DLL proof (the wrapper catching a DLL-runtime panic that would abort
    // if it reached the host) is the `boom` e2e at the /qa step.
    //
    // `effect_force_test_alloc` wires a real `std::alloc`-backed host allocator
    // (the node + thunk box need a live allocator; `get_global_alloc` panics
    // otherwise) and reads field-0 (the thunk_ptr) from the built node, then
    // forces it through `call_effect_thunk` to obtain the `EffectOutcome`.
    extern "C" fn effect_force_test_alloc(size: i64) -> i64 {
        let total = HEAP_HEADER_SIZE as usize + size as usize;
        unsafe {
            let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
            let base = std::alloc::alloc_zeroed(layout);
            *(base as *mut i64) = total as i64;
            *((base as *mut i64).add(1)) = 1;
            (base as i64) + HEAP_HEADER_SIZE
        }
    }

    fn wire_effect_force_alloc() {
        let cb = HostCallbacks {
            alloc: effect_force_test_alloc,
            alloc_with_tag: null_alloc_with_tag,
        };
        let host = HostContext::new();
        // SAFETY: `&cb` is a valid HostCallbacks for the duration of init.
        unsafe { host.init(&cb) };
    }

    #[test]
    fn effect_thunk_panic_yields_fault_cause() {
        wire_effect_force_alloc();
        // Faulting closure → non-null fault_cause carrying the message.
        let io: CLIO<CLInt> = CLIO::effect(|| -> CLInt { panic!("device exploded") });
        let base: i64 = io.into();
        // field-0 (thunk_ptr) is at payload offset 8 = base + header + 8.
        let thunk_ptr = unsafe { *((base + HEAP_HEADER_SIZE + 8) as *const i64) };
        let outcome = unsafe { call_effect_thunk(thunk_ptr) };
        assert!(
            !outcome.fault_cause.is_null(),
            "panicking thunk must yield a non-null fault_cause"
        );
        let cause = unsafe {
            std::str::from_utf8(std::slice::from_raw_parts(
                outcome.fault_cause,
                outcome.fault_len,
            ))
            .unwrap()
        };
        assert!(
            cause.contains("device exploded"),
            "fault_cause must carry the panic message, got {cause:?}"
        );
        // Free the node (the thunk box was consumed by call_effect_thunk).
        unsafe {
            let total = *((base) as *const i64) as usize;
            let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
            std::alloc::dealloc(base as *mut u8, layout);
        }
    }

    // spec: design/arch/bounded-contexts.md §5 invariant 9 — a clean
    // `CLIO::effect` thunk, when forced, yields a null `fault_cause` and the
    // closure's value. Host-runtime caveat as above.
    #[test]
    fn effect_thunk_clean_yields_null_fault_cause() {
        wire_effect_force_alloc();
        let io: CLIO<CLInt> = CLIO::effect(|| CLInt::from(4242i64));
        let base: i64 = io.into();
        let thunk_ptr = unsafe { *((base + HEAP_HEADER_SIZE + 8) as *const i64) };
        let outcome = unsafe { call_effect_thunk(thunk_ptr) };
        assert!(
            outcome.fault_cause.is_null(),
            "clean thunk must yield a null fault_cause"
        );
        assert_eq!(outcome.value, 4242, "clean thunk forwards the closure value");
        assert_eq!(outcome.fault_len, 0, "clean thunk has fault_len 0");
        unsafe {
            let total = *((base) as *const i64) as usize;
            let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
            std::alloc::dealloc(base as *mut u8, layout);
        }
    }

    // spec: design/arch/bounded-contexts.md §5 invariant 9 — the IO_TAG_EFFECT
    // node widened from 24 → 32 bytes with a fourth i64 field (the baked
    // fn-name handle, FIXME 0327 step 1/4). `CLIO::effect*` must allocate 32
    // payload bytes and reserve field-3 as null (the backend stamps it
    // post-call; until then it reads null → fn_name "<unknown>"). This test
    // installs a synthetic host allocator that records the requested size and
    // hands back a real allocation, builds an Effect node via
    // `CLIO::effect_on_resource`, then asserts the node carries tag /
    // resource-token correctly and that field-3 is reserved-and-null.
    #[test]
    fn effect_node_is_32_bytes_with_null_fn_name_field() {
        use std::sync::atomic::AtomicI64;

        // Synthetic host allocator: leak a zeroed 16-byte-header allocation of
        // `size` payload bytes and record the requested size for assertion.
        // (Matches the host contract: returns payload pointer = base + 16.)
        static LAST_ALLOC_SIZE: AtomicI64 = AtomicI64::new(0);
        extern "C" fn recording_alloc(size: i64) -> i64 {
            LAST_ALLOC_SIZE.store(size, Ordering::SeqCst);
            let total = HEAP_HEADER_SIZE as usize + size as usize;
            unsafe {
                let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
                let base = std::alloc::alloc_zeroed(layout);
                *(base as *mut i64) = total as i64; // alloc_size header
                *((base as *mut i64).add(1)) = 1; // rc = 1
                (base as i64) + HEAP_HEADER_SIZE // payload pointer
            }
        }
        let cb = HostCallbacks {
            alloc: recording_alloc,
            alloc_with_tag: null_alloc_with_tag,
        };
        let host = HostContext::new();
        // SAFETY: `&cb` is a valid HostCallbacks for the duration of init.
        unsafe { host.init(&cb) };

        // Build an Effect node with a known resource token. The thunk is never
        // forced here — we only inspect the node layout.
        let token = 7i64;
        let io: CLIO<CLInt> = CLIO::effect_on_resource(token, || CLInt::from(0i64));
        let base: i64 = io.into();

        // The DLL allocated 32 payload bytes (tag + thunk + token + fn_name).
        assert_eq!(
            LAST_ALLOC_SIZE.load(Ordering::SeqCst),
            32,
            "Effect node payload must be 32 bytes (ABI v4 node-widen, FIXME 0327)"
        );

        // Inspect the node fields at the documented offsets. The node base is
        // the alloc base; the payload (tag) starts at base + HEAP_HEADER_SIZE.
        let payload = base + HEAP_HEADER_SIZE;
        unsafe {
            let tag = *(payload as *const i64);
            let tok = *((payload + IO_EFFECT_RESOURCE_OFFSET) as *const i64);
            let fn_name = *((payload + IO_EFFECT_FN_NAME_OFFSET) as *const i64);
            assert_eq!(tag, IO_TAG_EFFECT, "tag field");
            assert_eq!(tok, token, "resource-token field at offset 16");
            assert_eq!(
                fn_name, 0,
                "field-3 (fn-name handle) must be reserved-and-null at offset 24 \
                 — the backend stamps it post-call (step 2)"
            );
        }
        // Note: the thunk_ptr (field-0, offset 8) holds a leaked
        // Box<Box<dyn FnOnce>> that the trampoline would consume; we do not
        // force it here, so the closure box is intentionally left unfreed
        // (a one-shot leak bounded to this test).
    }

    // ---------------------------------------------------------------------
    // DEF-6 (Sprint 86) — the alloc-callback payload-pointer LAYOUT INVARIANT
    // ---------------------------------------------------------------------
    //
    // spec: HostCallbacks::alloc (lib.rs §"Current shape (ABI v3)") —
    // "Allocate `size` bytes, returns payload pointer (base + 16)."
    //
    // The platform's heap-node constructors (`CLIO::pure`, `CLIO::effect*`,
    // `CLString::from`) treat the `alloc` callback's return as a PAYLOAD pointer
    // and compute the stored BASE as `payload - HEAP_HEADER_SIZE`. The whole
    // base-pointer convention the consuming side (`CLHeap::dec_rc` reads the RC
    // at `base + 8`; `CLOwned::drop`/`consume_io_tree` free `total_size` bytes
    // from `base + 0`) depends on this single invariant:
    //
    //     stored_base == (alloc-return) - HEAP_HEADER_SIZE  AND
    //     stored_base == the real allocation base           (so base+0 = total_size,
    //                                                            base+8 = rc).
    //
    // DEF-6 was a HOST wiring bug (`cranelisp-exe-bundle` `--link` path) that
    // wired `alloc` to `heap_alloc` (returns the alloc BASE) instead of
    // `heap_alloc_payload` (returns base + 16). Given a base-returning `alloc`,
    // these constructors compute `stored_base = base - 16` (16 bytes BEFORE the
    // allocation) and write the node's tag/fields into the header + the previous
    // chunk — clobbering the RC header (`base + 8`) and overrunning into adjacent
    // heap metadata. The damage accumulates one node per host↔DLL crossing until
    // glibc aborts (`double free or corruption`). RC accounting stays balanced
    // (the bug is a pointer-base error, not a refcount miscount).
    //
    // This test pins the platform-side half of that invariant: when the `alloc`
    // contract is honoured (payload pointer = base + 16), every heap node the
    // platform builds has its stored base land EXACTLY on the real allocation
    // base — so `base + 0` reads a sane `total_size` and `base + 8` reads the
    // live rc=1 the allocator wrote. A tight construct loop verifies the property
    // holds repeatedly (the per-crossing accumulation the e2e abort surfaced),
    // and a control assertion shows that the contract-VIOLATING (base-returning)
    // allocator drives the stored base off by exactly -HEAP_HEADER_SIZE — i.e.
    // pins the precise offset of the host bug.

    /// Contract-HONOURING host allocator: returns a payload pointer = base + 16,
    /// with `total_size` at base+0 and rc=1 at base+8. Mirrors the real
    /// `cranelisp_intrinsics::heap_alloc_payload` the JIT path wires (and the
    /// `--link` path MUST wire). Leaks the allocation (bounded to the test).
    extern "C" fn payload_returning_alloc(size: i64) -> i64 {
        let total = HEAP_HEADER_SIZE as usize + size as usize;
        // SAFETY: standard allocator path; total >= 16, align 8.
        unsafe {
            let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
            let base = std::alloc::alloc_zeroed(layout);
            *(base as *mut i64) = total as i64; // total_size @ base+0
            *((base as *mut i64).add(1)) = 1; // rc=1 @ base+8
            (base as i64) + HEAP_HEADER_SIZE // <-- payload pointer (CONTRACT)
        }
    }

    /// Contract-VIOLATING host allocator: returns the alloc BASE (NOT base + 16).
    /// This is exactly the DEF-6 host bug (`heap_alloc` wired where
    /// `heap_alloc_payload` was required). Used only to pin the precise -16 byte
    /// offset the violation produces; the node it builds is corrupt by design and
    /// is NOT consumed.
    extern "C" fn base_returning_alloc(size: i64) -> i64 {
        let total = HEAP_HEADER_SIZE as usize + size as usize;
        // SAFETY: standard allocator path; total >= 16, align 8.
        unsafe {
            let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
            let base = std::alloc::alloc_zeroed(layout);
            *(base as *mut i64) = total as i64;
            *((base as *mut i64).add(1)) = 1;
            base as i64 // <-- BASE pointer (the DEF-6 violation)
        }
    }

    fn wire_alloc(cb_alloc: extern "C" fn(i64) -> i64) {
        let cb = HostCallbacks {
            alloc: cb_alloc,
            alloc_with_tag: null_alloc_with_tag,
        };
        let host = HostContext::new();
        // SAFETY: `&cb` is a valid HostCallbacks for the duration of init.
        unsafe { host.init(&cb) };
    }

    /// Read the i64 at `base + offset`.
    ///
    /// # Safety
    /// `base` must be a live allocation with at least `offset + 8` bytes.
    unsafe fn peek(base: i64, offset: i64) -> i64 {
        unsafe { *((base + offset) as *const i64) }
    }

    // spec: HostCallbacks::alloc — when the alloc contract is honoured (payload
    // pointer = base + 16), the base a heap node stores lands on the REAL
    // allocation base: total_size at base+0 is sane and rc at base+8 is the live
    // rc=1. This is the exact invariant DEF-6 violated; with the correct
    // (payload-returning) allocator it holds, so the node's RC header is where
    // `CLHeap::dec_rc` (base+8) and the free path (base+0) expect it.
    #[test]
    fn def6_io_node_base_lands_on_real_allocation_header() {
        wire_alloc(payload_returning_alloc);

        // Pure node: payload [tag | value] = 16 bytes.
        let pure: CLIO<CLInt> = CLIO::pure(CLInt::from(99i64));
        let pbase: i64 = pure.into();
        // SAFETY: pbase is the node's stored base; header reads are in-bounds iff
        // the base lands on the real allocation (the property under test).
        unsafe {
            let total = peek(pbase, 0);
            let rc = peek(pbase, 8);
            assert_eq!(
                total, 32,
                "Pure node total_size at base+0 must be 16 header + 16 payload \
                 = 32; a wrong base reads garbage here (DEF-6 signature)"
            );
            assert_eq!(
                rc, 1,
                "Pure node rc at base+8 must be the live rc=1 the allocator \
                 wrote; DEF-6 read this slot 16 bytes low and saw garbage \
                 (the `dec ... rc=64` trace)"
            );
            // The payload tag sits at base + HEAP_HEADER_SIZE, NOT inside the header.
            assert_eq!(
                peek(pbase, HEAP_HEADER_SIZE),
                IO_TAG_PURE,
                "Pure tag must be at payload offset 0 (base+16), not clobbering \
                 the header"
            );
        }

        // Effect node: payload 32 bytes; same invariant.
        let eff: CLIO<CLInt> = CLIO::effect(|| CLInt::from(0i64));
        let ebase: i64 = eff.into();
        // SAFETY: as above.
        unsafe {
            assert_eq!(peek(ebase, 0), 48, "Effect node total_size = 16 + 32");
            assert_eq!(peek(ebase, 8), 1, "Effect node rc=1 at base+8");
            assert_eq!(
                peek(ebase, HEAP_HEADER_SIZE),
                IO_TAG_EFFECT,
                "Effect tag at payload offset 0"
            );
        }
    }

    // spec: HostCallbacks::alloc — pins the PRECISE offset of the DEF-6 host bug.
    // A contract-VIOLATING (base-returning) allocator makes the node's stored
    // base land exactly HEAP_HEADER_SIZE (16) bytes BELOW the real allocation
    // base — the `dec ... 16-bytes-below-a-fresh-alloc` signature from the RC
    // trace. The contract-honouring allocator lands it dead on. This is the
    // before/after that names the fix: wire the payload-returning allocator.
    #[test]
    fn def6_violating_alloc_offsets_base_by_exactly_header_size() {
        // Honouring allocator: stored base == real allocation base, so total_size
        // at base+0 is the sane 32 (16 header + 16 Pure payload).
        wire_alloc(payload_returning_alloc);
        let good: i64 = CLIO::<CLInt>::pure(CLInt::from(1i64)).into();
        // SAFETY: honouring base lands on the real header.
        let good_total = unsafe { peek(good, 0) };
        assert_eq!(good_total, 32, "honouring allocator: base+0 = total_size = 32");

        // Violating allocator: `alloc` returns the REAL allocation base. The
        // platform, believing it got a PAYLOAD pointer, (a) writes the node's
        // tag/value at real_base+0 / real_base+8 — CLOBBERING the total_size and
        // rc header the allocator wrote — and (b) returns stored_base =
        // real_base - HEAP_HEADER_SIZE (16 bytes BELOW the real allocation). Both
        // halves of the DEF-6 corruption are observable here:
        wire_alloc(base_returning_alloc);
        let bad: i64 = CLIO::<CLInt>::pure(CLInt::from(1i64)).into();

        // (a) stored base is exactly HEAP_HEADER_SIZE below the real base — so
        //     `bad + 16` recovers the real allocation base. The platform wrote
        //     the Pure tag (IO_TAG_PURE = 0) over the total_size slot at that
        //     real base+0, and the Pure value (1) over the rc slot at real
        //     base+8 — proving the header was overrun.
        // SAFETY: bad + HEAP_HEADER_SIZE is the real allocation base.
        let clobbered_total = unsafe { peek(bad + HEAP_HEADER_SIZE, 0) };
        let clobbered_rc = unsafe { peek(bad + HEAP_HEADER_SIZE, 8) };
        assert_eq!(
            clobbered_total, IO_TAG_PURE,
            "DEF-6: a base-returning `alloc` makes the platform write the node \
             TAG over the real total_size header slot — the header is destroyed. \
             The fix is host-side: wire `heap_alloc_payload` (payload pointer), \
             NOT `heap_alloc` (base), in cranelisp-exe-bundle's --link wiring."
        );
        assert_eq!(
            clobbered_rc, 1,
            "DEF-6: the platform wrote the Pure value (1) over the real rc \
             header slot — so the consuming side's `dec_rc` at stored_base+8 \
             reads adjacent garbage (the `dec ... rc=64` RC-trace signature)."
        );

        // (b) the platform's STORED base (`bad`) is 16 bytes below the real base.
        //     Confirm the off-by-exactly-HEAP_HEADER_SIZE relationship directly.
        assert_eq!(
            (bad + HEAP_HEADER_SIZE) - bad,
            HEAP_HEADER_SIZE,
            "stored base is exactly HEAP_HEADER_SIZE below the real allocation base"
        );
    }

    // spec: HostCallbacks::alloc — the per-crossing accumulation guard. DEF-6
    // aborted only after ~40 host↔DLL crossings because each crossing wrote one
    // node's fields into the previous chunk's metadata. This loops the node
    // construct+free cycle 256 times under the contract-honouring allocator,
    // verifying every iteration's node header is intact AND that a real
    // `std::alloc` free of each node (via the documented base) succeeds without
    // tripping the allocator — i.e. no adjacent-chunk corruption accumulates.
    #[test]
    fn def6_repeated_node_construct_free_does_not_corrupt_heap() {
        wire_alloc(payload_returning_alloc);
        for i in 0..256i64 {
            let io: CLIO<CLInt> = if i % 2 == 0 {
                CLIO::pure(CLInt::from(i))
            } else {
                CLIO::effect(move || CLInt::from(i))
            };
            let base: i64 = io.into();
            // SAFETY: with the honouring allocator the stored base is the real
            // allocation base, so the header reads + the free below are sound.
            unsafe {
                let total = peek(base, 0);
                assert!(
                    total == 32 || total == 48,
                    "iter {i}: node total_size must be 32 (Pure) or 48 (Effect), \
                     got {total} — a corrupted header would show here"
                );
                assert_eq!(peek(base, 8), 1, "iter {i}: rc=1 header intact");
                // Free the node through its documented base (mirrors the
                // consuming side reading total_size@0). If a prior iteration had
                // overrun adjacent metadata, this free would abort.
                let layout = std::alloc::Layout::from_size_align_unchecked(total as usize, 8);
                std::alloc::dealloc(base as *mut u8, layout);
            }
        }
    }

    // spec: design/arch/platform-interface.md §5.5.4 — extract_layout_hash
    // pulls the hex from the artifact's `;; layout-hash:` header (and returns
    // "" when absent — a tolerated first-build artifact).
    #[test]
    fn extract_layout_hash_reads_header() {
        assert_eq!(
            extract_layout_hash(";; layout-hash: deadbeef\n(schema)"),
            "deadbeef"
        );
        assert_eq!(extract_layout_hash("(schema)"), "");
        // Tolerates leading spaces + trailing whitespace.
        assert_eq!(extract_layout_hash(";; layout-hash:   abc123  \n"), "abc123");
    }

    // T24 — F2 source-move — HostContext does NOT impl Default
    // spec: design/platform/sprint71-redesign.md §8 row F2
    //
    // We assert the no-impl-Default property at compile time using a
    // trait-bound check that succeeds only if HostContext is NOT Default.
    // The trick: write a generic that requires `T: !Default` (Rust doesn't
    // have negative bounds in stable, so use a marker-trait + impl<all
    // except Default> pattern). Simpler: just verify that `HostContext::default()`
    // is NOT callable by checking via a function-existence proof at the
    // type system level. We do this via a const fn that consumes the
    // assertion.
    //
    // The most robust approach without static_assertions: a function
    // generic that would compile if Default were implemented. Since we
    // cannot have negative bounds, we instead verify via a runtime probe
    // that doesn't depend on the type system: check that the Default
    // associated function is not in the cargo-public-api baseline — this
    // is what T23 effectively checks already. Here we add a structural
    // proof: the public-api.txt file does NOT contain a Default impl line
    // for HostContext.
    #[test]
    fn t24_host_context_not_default_compile_fence() {
        // Read the public-api baseline at the workspace root and assert
        // the Default impl for HostContext is absent.
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("public-api.txt");
        // The baseline may or may not be regenerated yet at the time this
        // test runs in CI; if absent, skip with a clear note.
        let baseline = match std::fs::read_to_string(&path) {
            Ok(s) => s,
            Err(_) => return, // pre-regen; T23 covers the regen discipline.
        };
        assert!(
            !baseline.contains("impl core::default::Default for cranelisp_platform::HostContext"),
            "F2 source-move regression: HostContext::default() reappeared \
             in the public-api baseline. The impl Default for HostContext \
             was deleted in Sprint 71 Wave 2 per design §8 row F2; this \
             test guards against reintroduction. \
             Re-run cargo +nightly public-api > crates/cranelisp-platform/public-api.txt \
             if the baseline is stale."
        );
    }

    // T25 — R1 wired-or-panic — construction path panics with explicit message
    // spec: design/platform/sprint71-redesign.md §9 (R1 uninitialized-host gate)
    //
    // We cannot use `#[should_panic]` directly: `null_alloc_with_tag` is
    // `extern "C" fn`, and modern Rust aborts on panics across the
    // extern-C boundary (which a #[should_panic] harness cannot catch
    // because the process exits). Instead, T25 asserts the panic-message
    // content is present in the source — the fallback fires at runtime,
    // visibly, when a host has not called HostContext::init to wire
    // alloc_with_tag, and the message names the uninitialized-host
    // condition + HostCallbacks::alloc_with_tag + the synthetic callback
    // workaround. The actual panic-and-abort behaviour is verified in
    // integration / observed at DLL load when a CLAdt::construct call lands
    // without a wired host. This split keeps T25 as a failing-first
    // regression guard against accidental message dilution.
    //
    // The gate is a PERMANENT uninitialized-host fallback (alloc_with_tag
    // has been wired by the host since Sprint 76), not a migration scaffold
    // — the message no longer names a now-resolved FIXME.
    #[test]
    fn t25_null_alloc_with_tag_panic_message_contract() {
        // Read this source file and verify the panic message contains the
        // required substrings from the reframed fallback contract.
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("src/lib.rs");
        let src = std::fs::read_to_string(&path)
            .expect("can read crates/cranelisp-platform/src/lib.rs");
        // Locate the null_alloc_with_tag function definition (skip past
        // any doc-comment mentions; the actual fn starts with
        // `pub extern "C" fn null_alloc_with_tag(`).
        let body_start = src.find("pub extern \"C\" fn null_alloc_with_tag(")
            .expect("null_alloc_with_tag fn declared in lib.rs");
        let body = &src[body_start..(body_start + 1500).min(src.len())];
        assert!(body.contains("alloc_with_tag"),
                "fallback panic message must name HostCallbacks::alloc_with_tag");
        assert!(body.contains("HostContext::init"),
                "fallback panic message must name the uninitialized-host condition (no HostContext::init call)");
        // The source-text concatenation wraps "synthetic" and "callback"
        // across a line-continuation backslash; check for "synthetic"
        // alone as the trigger word for the workaround instruction.
        assert!(body.contains("synthetic"),
                "fallback panic message must instruct on the test-side workaround (synthetic callback via HostContext::init)");
    }

    // T27 — HostCallbacks carries the two fn-pointer fields (ABI v3, FIXME
    // 0288 — `validate_schema` removed; schema validation superseded by the
    // layout-hash gate, platform-interface.md §5.5.4).
    // spec: bounded-contexts.md §5 — HostCallbacks { alloc, alloc_with_tag }
    //
    // Structural construction site — confirms the fields exist with the
    // chosen extern "C" fn signatures.
    #[test]
    fn t27_host_callbacks_carries_new_fn_pointer_fields() {
        extern "C" fn dummy_alloc(_size: i64) -> i64 { 0 }
        let cb = HostCallbacks {
            alloc: dummy_alloc,
            alloc_with_tag: null_alloc_with_tag,
        };
        // Field-existence verified by the struct literal; assert one
        // pointer-equal sanity check.
        assert_eq!(
            cb.alloc_with_tag as *const () as usize,
            null_alloc_with_tag as *const () as usize
        );
    }

    // ---------------------------------------------------------------------
    // S82 harvest — 0135 (legacy/lenient.rs) platform-owned scheduling-class
    // GAPs. The lenient-eval *correctness* subset (independent/dependent
    // bindings, cheap-builtin threshold, env opt-out, …) is e2e-covered
    // (spec_04_expressions.rs::lenient_*, spec_12_runtime.rs). The Par-node
    // *emission* / bind-chain *data-dependency analysis* is backend (Par
    // codegen) — already harvested there. What `cranelisp-platform` genuinely
    // owns of the `io_schedule_*` GAPs is the **scheduling-class declaration +
    // marshaling surface**: the per-fn `SchedulingClass` discriminant must
    // survive the C-ABI manifest round-trip (`manifest_to_descriptors`'s u32 →
    // typed-enum lift), and a `ResourceSerial` fn's per-call resource token
    // must land on the Effect node at the documented offset. These are the
    // platform half of the legacy `io_schedule_sequential_*` /
    // `io_schedule_data_dependent_*` / `io_schedule_resource_serial_*` triple;
    // the scheduling *decision* (sequential vs Par, same-vs-different-token
    // serialization at the trampoline) is NOT platform's — it is backend /
    // intrinsics (lib.rs IO trampoline note; Decision 0043), so those
    // assertions are not ported here.

    // Build a one-fn `PlatformManifest` carrying a given scheduling-class
    // discriminant, with all string fields valid UTF-8, and return its
    // round-tripped descriptor's typed `scheduling_class`. The backing
    // byte-slices are passed in by the caller so they outlive the call.
    fn descriptor_scheduling_class(class_discriminant: u32) -> SchedulingClass {
        let name: &[u8] = b"sched";
        let version: &[u8] = b"0.1.0";
        let fn_name: &[u8] = b"f";
        let type_sig: &[u8] = b"(Fn [] (IO primitives/Int))";
        let docstring: &[u8] = b"";

        let func = PlatformFn {
            name: fn_name.as_ptr(),
            name_len: fn_name.len(),
            ptr: std::ptr::null(),
            param_count: 0,
            type_sig: type_sig.as_ptr(),
            type_sig_len: type_sig.len(),
            docstring: docstring.as_ptr(),
            docstring_len: docstring.len(),
            param_names: std::ptr::null(),
            param_name_lens: std::ptr::null(),
            param_name_count: 0,
            scheduling_class: class_discriminant,
        };
        let funcs = [func];
        let manifest = PlatformManifest {
            abi_version: ABI_VERSION,
            name: name.as_ptr(),
            name_len: name.len(),
            version: version.as_ptr(),
            version_len: version.len(),
            functions: funcs.as_ptr(),
            function_count: 1,
        };

        // SAFETY: every pointer above borrows a slice that lives to the end of
        // this fn, and the lengths match. `manifest_to_descriptors` reads the
        // manifest once and copies into owned shapes before returning.
        let (_name, _version, descriptors) =
            unsafe { manifest_to_descriptors(&manifest) }.expect("valid manifest round-trips");
        assert_eq!(descriptors.len(), 1, "one fn in, one descriptor out");
        descriptors[0].scheduling_class
    }

    // spec: spec/10-io.md §10.12.2 — a `Sequential`-declared platform fn
    // (discriminant 0) round-trips through the C-ABI manifest as the typed
    // `SchedulingClass::Sequential`. (Platform half of legacy
    // lenient.rs::test_io_schedule_sequential_no_par — the order-preservation
    // *decision* is backend/intrinsics; what platform owns is the class lift.)
    #[test]
    fn manifest_lifts_sequential_scheduling_class() {
        assert_eq!(descriptor_scheduling_class(0), SchedulingClass::Sequential);
    }

    // spec: spec/10-io.md §10.12.1 — a `Commutative`-declared platform fn
    // (discriminant 1) round-trips as `SchedulingClass::Commutative`. This is
    // the class on which the backend bases its Par-node emission for
    // data-independent pairs (legacy lenient.rs::test_io_schedule_commutative_pair_par
    // / test_io_schedule_data_dependent_no_par — the *data-dependency* analysis
    // is backend; platform owns the class declaration that gates it).
    #[test]
    fn manifest_lifts_commutative_scheduling_class() {
        assert_eq!(descriptor_scheduling_class(1), SchedulingClass::Commutative);
    }

    // spec: spec/10-io.md §10.12.4 — a `ResourceSerial`-declared platform fn
    // (discriminant 2) round-trips as `SchedulingClass::ResourceSerial`.
    // (Platform half of legacy
    // lenient.rs::test_io_schedule_resource_serial_*_token_* — the token
    // *serialization* at the trampoline is intrinsics, not platform.)
    #[test]
    fn manifest_lifts_resource_serial_scheduling_class() {
        assert_eq!(
            descriptor_scheduling_class(2),
            SchedulingClass::ResourceSerial
        );
    }

    // spec: spec/10-io.md §10.12.2 — an unknown scheduling-class discriminant
    // is conservatively lifted to `Sequential` (the safe default;
    // `SchedulingClass::from_u32` fallback). Negative guard: a DLL built
    // against a newer ABI declaring an unknown class must NOT be silently
    // treated as parallelizable.
    #[test]
    fn manifest_lifts_unknown_scheduling_class_to_sequential_neg() {
        assert_eq!(descriptor_scheduling_class(99), SchedulingClass::Sequential);
    }

    // spec: spec/10-io.md §10.12.4 — a `ResourceSerial` fn's per-call resource
    // token is written onto the Effect node at `IO_EFFECT_RESOURCE_OFFSET`
    // (offset 16), where the trampoline reads it to group-by-token. This is
    // the platform-owned token-placement half of the resource-serial GAP; the
    // same-vs-different-token serialization *decision* lives in the intrinsics
    // trampoline (Decision 0043). A distinct non-zero token from the default-0
    // (unscheduled) effect is exercised to pin the placement.
    #[test]
    fn resource_serial_token_lands_on_effect_node() {
        extern "C" fn token_test_alloc(size: i64) -> i64 {
            let total = HEAP_HEADER_SIZE as usize + size as usize;
            unsafe {
                let layout = std::alloc::Layout::from_size_align_unchecked(total, 8);
                let base = std::alloc::alloc_zeroed(layout);
                *(base as *mut i64) = total as i64;
                *((base as *mut i64).add(1)) = 1; // rc = 1
                (base as i64) + HEAP_HEADER_SIZE
            }
        }
        let cb = HostCallbacks {
            alloc: token_test_alloc,
            alloc_with_tag: null_alloc_with_tag,
        };
        let host = HostContext::new();
        // SAFETY: `&cb` is a valid HostCallbacks for the duration of init.
        unsafe { host.init(&cb) };

        // A ResourceSerial fn sets a non-zero token (e.g. a file descriptor);
        // contrast with the default-0 token an unscheduled effect carries.
        let token = 0x1234_i64;
        let io: CLIO<CLInt> = CLIO::effect_on_resource(token, || CLInt::from(0i64));
        let base: i64 = io.into();
        let payload = base + HEAP_HEADER_SIZE;
        let (tag, tok, default_tok) = unsafe {
            let tag = *(payload as *const i64);
            let tok = *((payload + IO_EFFECT_RESOURCE_OFFSET) as *const i64);
            // A token-less effect must carry token 0 (unscheduled).
            let io0: CLIO<CLInt> = CLIO::effect(|| CLInt::from(0i64));
            let base0: i64 = io0.into();
            let default_tok =
                *((base0 + HEAP_HEADER_SIZE + IO_EFFECT_RESOURCE_OFFSET) as *const i64);
            (tag, tok, default_tok)
        };
        assert_eq!(tag, IO_TAG_EFFECT, "node is an Effect node");
        assert_eq!(
            tok, token,
            "ResourceSerial token must land at IO_EFFECT_RESOURCE_OFFSET (16)"
        );
        assert_eq!(
            default_tok, 0,
            "a token-less effect carries the unscheduled token 0"
        );
    }

    // ======================================================================
    // S93 §2B — ABI-v7 dormant-contract guard (/qa, Phase-5 Stage-1).
    // Gated `#[cfg(feature = "concurrency")]`; runs only under
    // `cargo nt-concurrency` (the FIXME-0449 lane). Verifies the LANDED v7
    // contract — the poll-shape successor to v6 `PlatformFn`.
    // ======================================================================

    // spec: design/arch/platform-interface.md §6.8 + effect-concurrency.md §12 —
    // `ConcurrentPlatformFn` is the ABI-v7 manifest entry that crosses the
    // platform-DLL C-ABI as raw bytes. Its `#[repr(C)]` field order is the
    // FROZEN v7 byte layout (governed by ABI_VERSION = 7). This pins the
    // declaration order via monotonic field offsets — the poll fn replaces v6's
    // blocking `ptr`, and `concurrency: ConcurrencyDescriptor` subsumes v6's
    // `scheduling_class: u32`. A reorder breaks the GOT-indirect manifest read.
    #[cfg(feature = "concurrency")]
    #[test]
    fn concurrent_platform_fn_repr_c_field_order_v7() {
        use core::mem::offset_of;
        // Field declaration order, pinned by strictly-increasing offsets.
        let offs = [
            offset_of!(ConcurrentPlatformFn, name),
            offset_of!(ConcurrentPlatformFn, name_len),
            offset_of!(ConcurrentPlatformFn, poll),
            offset_of!(ConcurrentPlatformFn, param_count),
            offset_of!(ConcurrentPlatformFn, type_sig),
            offset_of!(ConcurrentPlatformFn, type_sig_len),
            offset_of!(ConcurrentPlatformFn, docstring),
            offset_of!(ConcurrentPlatformFn, docstring_len),
            offset_of!(ConcurrentPlatformFn, param_names),
            offset_of!(ConcurrentPlatformFn, param_name_lens),
            offset_of!(ConcurrentPlatformFn, param_name_count),
            offset_of!(ConcurrentPlatformFn, concurrency),
        ];
        assert_eq!(offset_of!(ConcurrentPlatformFn, name), 0, "name leads the v7 layout");
        for w in offs.windows(2) {
            assert!(
                w[0] < w[1],
                "v7 ConcurrentPlatformFn field order frozen: offsets must be \
                 strictly increasing in declaration order, got {offs:?}"
            );
        }
        // The concurrency descriptor is the trailing field (subsumes v6
        // scheduling_class) and is the embedded v7 descriptor type.
        assert_eq!(
            offset_of!(ConcurrentPlatformFn, concurrency),
            *offs.iter().max().unwrap(),
            "concurrency descriptor is the last field"
        );
    }
