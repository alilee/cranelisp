//! The `declare_platform!` three-exports emitter — the DLL-author entry point.
//!
//! This module co-locates the three-exports macro pair with the
//! compile-time helper they depend on:
//!
//! - [`extract_layout_hash`] — pulls the `;; layout-hash: <hex>` header out of a
//!   generated schema artifact at compile time so the `schema:` arm can export it
//!   as `__cranelisp_layout_hash_<name>`.
//! - [`declare_platform!`] — the public macro every platform DLL invokes once
//!   (two arms: with / without the `schema:` embed).
//! - [`__declare_platform_body!`] — the shared body emitter (`#[doc(hidden)]`).
//!
//! Both macros are `#[macro_export]`, so they resolve at the crate root
//! (`cranelisp_platform::declare_platform!`) regardless of this module — the
//! split is a placement change only, behaviour is identical. Every path inside
//! the macros is `$crate::`-qualified, so they reference the crate facade
//! (`HostCallbacks`, `PlatformFn`, `PlatformManifest`, `Schema`,
//! `set_global_schema`, `MacroAtomicPtr`, `GOT_TABLE_SIZE`, `ABI_VERSION`) the
//! same way from here as from `lib.rs`.

// -- declare_platform! macro --

/// Extract the `<hex>` from a generated schema artifact's `;; layout-hash:
/// <hex>` header line, at compile time, so the [`declare_platform!`] `schema:`
/// embed arm can export it as `__cranelisp_layout_hash_<name>`
/// (platform-interface.md §5.5.4).
///
/// `const fn` so the macro can use the result to initialise a `&'static str`
/// data symbol with no runtime work. Scans for the `;; layout-hash:` marker and
/// returns the trimmed remainder of that line; returns `""` if absent (a
/// first-build artifact may carry no header — the absence is tolerated, the
/// layout-hash gate simply compares against an empty hash and the REPL warns).
pub const fn extract_layout_hash(artifact: &str) -> &str {
    const MARKER: &[u8] = b";; layout-hash:";
    let bytes = artifact.as_bytes();
    let n = bytes.len();
    let m = MARKER.len();
    let mut i = 0;
    while i + m <= n {
        // Match MARKER at position i.
        let mut k = 0;
        while k < m && bytes[i + k] == MARKER[k] {
            k += 1;
        }
        if k == m {
            // Skip leading spaces after the marker.
            let mut start = i + m;
            while start < n && (bytes[start] == b' ' || bytes[start] == b'\t') {
                start += 1;
            }
            // Find end of line.
            let mut end = start;
            while end < n && bytes[end] != b'\n' && bytes[end] != b'\r' {
                end += 1;
            }
            // Trim trailing spaces.
            while end > start && (bytes[end - 1] == b' ' || bytes[end - 1] == b'\t') {
                end -= 1;
            }
            // SAFETY: start/end fall on ASCII boundaries (the hash is hex; the
            // marker + spaces are ASCII), so the slice is valid UTF-8.
            let slice = unsafe {
                std::str::from_utf8_unchecked(
                    std::slice::from_raw_parts(bytes.as_ptr().add(start), end - start),
                )
            };
            return slice;
        }
        i += 1;
    }
    ""
}

/// Declare a platform DLL with metadata and function registrations —
/// the DLL-author entry point.
///
/// Every platform DLL invokes `declare_platform!` exactly once. The macro
/// implements the **three-exports model** (`design/arch/platform-interface.md`
/// §1/§6.1, user-ratified 2026-06-07; FIXME 0286) — a platform exports its GOT,
/// its manifest, and (optionally) its embedded generated schema + layout hash:
///
/// 1. **The exported GOT** — `__cranelisp_got_platform_<name>`, a
///    `[AtomicPtr<u8>; GOT_TABLE_SIZE]` static (the `__cranelisp_got_primitives`
///    precedent, FIXME 0280). Slot *i* holds the fn pointer of `functions[i]`
///    — **manifest order IS GOT slot order** (§5.1). The macro populates the
///    used slots inside `cranelisp_platform_manifest` at DLL load; the host
///    wraps the GOT in place (`GotTable::with_static_backing`) and dispatches
///    GOT-indirect at `got_slot = manifest index`.
/// 2. **The manifest** — the `cranelisp_platform_manifest` extern fn returning
///    a [`PlatformManifest`] of [`PlatformFn`] descriptors (name, FQ type_sig,
///    scheduling class, docstring, param-names). The host builds its
///    `SymbolTable` from this.
/// 3. **The embedded schema + layout hash** (optional `schema:` arm) — the
///    `/platform-schema`-generated artifact text, embedded via `include_str!`,
///    parsed once into the per-DLL [`Schema`] (`CLAdt::read_field` reads it by
///    name); the artifact's `;; layout-hash:` header is exported as the data
///    symbol `__cranelisp_layout_hash_<name>` (§5.5.4). The arm is optional —
///    an absent schema is tolerated for first builds (the layout-hash gate then
///    compares against an empty hash; the REPL warns).
///
/// Platform functions are normal `extern "C"` Rust functions over the `CL*`
/// wrapper family — defined outside the macro. **Platforms no longer declare
/// ADTs:** a platform's data types are ordinary `.cl` modules; the macro's
/// signatures reference them by fully-qualified name
/// (`(Fn [shapes/Rectangle] primitives/Int)`). The Sprint 71 schema
/// *declaration* dialect (the `LazyLock<Schema>`-as-DSL static, the marker-type
/// auto-emission, `GetSchema`, `schema_types:`) is **retired** (§6.6).
///
/// # Macro keys
///
/// | Key | Required | Shape | Purpose |
/// |---|---|---|---|
/// | `name:` | yes | `&'static str` literal | Platform name; the GOT/hash export suffix |
/// | `version:` | yes | `&'static str` literal | Platform version |
/// | `host:` | yes | identifier of a `static HOST: HostContext` | Where the macro calls `init(callbacks)` |
/// | `schema:` | optional | `&'static str` (the embedded `/platform-schema` artifact, typically `include_str!(...)`) | Embedded generated schema; absent ⇒ no ADT marshaling |
/// | `functions:` | yes | `[ fn { ... }, ... ]` array | Per-fn descriptors |
///
/// Each per-fn block has five required fields — `cl_name:` (kebab-case
/// user-visible name), `sig:` (FQ type-signature S-expression), `doc:`
/// (docstring), `params:` (named-parameter ident list), `scheduling:`
/// ([`SchedulingClass`] expression).
///
/// # ABI v7 — authoring is unchanged (Sprint 93)
///
/// [`crate::ABI_VERSION`] is now **7**: the effect-concurrency track landed the
/// v7 host-reactor C-ABI layout contracts (`ConcurrentPlatformFn`,
/// `HostCtx` / `Waker` / `WakerVTable`, the poll-shape `PollFn`). **Those
/// contracts are landed-but-dormant behind the off-by-default `concurrency`
/// feature** — they are out of the default build and the `public-api.txt`
/// frozen edge. For a platform author, **nothing about `declare_platform!`
/// changed**: this macro still emits the v6 [`crate::PlatformFn`] shape, effect
/// fns are still **blocking** `extern "C"` functions returning [`crate::CLIO`],
/// and each fn still declares a `scheduling:` [`crate::SchedulingClass`]. The
/// poll-shape async-leaf
/// model — where blocking effect fns become `PollFn`s the host reactor drives,
/// and `scheduling:` is subsumed by `ConcurrencyDescriptor` — wires in a later
/// slice; until then write platforms exactly as the examples below.
///
/// The 6→7 bump matters only for the load-time ABI gate: a DLL built from this
/// crate now stamps `abi_version: 7` in its manifest, and the host rejects a
/// mismatched stamp with [`crate::PlatformError`]`::AbiVersionMismatch`. In-workspace
/// host + platform DLLs rebuild together, so the stamp stays consistent; an
/// externally pre-built v6 DLL would need a rebuild against this crate to load
/// against a v7 host (there are no such external DLLs today — every platform is
/// a workspace member).
///
/// # Example — no schema (scalar-only platform)
///
/// ```ignore
/// use cranelisp_platform::*;
///
/// static HOST: HostContext = HostContext::new();
///
/// pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
///     let owned = s.into_owned_consuming();
///     CLIO::effect(move || { println!("{}", owned.as_str()); CLInt::from(0i64) })
/// }
///
/// declare_platform! {
///     name: "stdio",
///     version: "0.1.0",
///     host: HOST,
///     functions: [
///         print_string {
///             cl_name: "print",
///             sig: "(Fn [primitives/String] (IO primitives/Int))",
///             doc: "Print a string followed by a newline",
///             params: [s],
///             scheduling: SchedulingClass::Sequential,
///         },
///     ]
/// }
/// ```
///
/// # Example — with the `schema:` embed arm
///
/// ```ignore
/// declare_platform! {
///     name: "shapes",
///     version: "0.1.0",
///     host: HOST,
///     schema: include_str!("shapes.platform-schema"), // GENERATED — never hand-edited
///     functions: [
///         rectangle_area {
///             cl_name: "rectangle-area",
///             sig: "(Fn [shapes/Rectangle] primitives/Int)", // fully qualified
///             doc: "Compute the area of a rectangle",
///             params: [r],
///             scheduling: SchedulingClass::Commutative,
///         },
///     ]
/// }
/// ```
#[macro_export]
macro_rules! declare_platform {
    // Arm 1: with the `schema:` EMBED arm (the generated artifact text — the
    // schema *declaration* dialect is retired, §6.6). Installs the parsed
    // schema for name-based field access and exports the layout-hash.
    (
        name: $platform_name:literal,
        version: $platform_version:literal,
        host: $host:ident,
        schema: $schema_text:expr,
        functions: [
            $(
                $fn_ident:ident {
                    cl_name: $cl_name:literal,
                    sig: $sig:literal,
                    doc: $doc:literal,
                    params: [$($param:ident),* $(,)?],
                    scheduling: $scheduling:expr,
                }
            ),* $(,)?
        ]
    ) => {
        // The embedded generated schema artifact text (typically
        // `include_str!("<name>.platform-schema")`).
        const __CRANELISP_PLATFORM_SCHEMA_TEXT: &str = $schema_text;

        // Export the layout hash (extracted from the artifact's
        // `;; layout-hash:` header at compile time) as a data symbol the host
        // compares against its live-tables regeneration (§5.5.4). Carried as a
        // `&'static str` — a `(ptr, len)` fat reference into the schema rodata.
        // BOTH run-mode readers dereference this fat reference and use its `len`,
        // so neither depends on a NUL terminator (the D2 fix lives in the reader,
        // `cranelisp-intrinsics::layout` — see its doc):
        //   - `--run` reads `library.get::<*const &str>` → `**sym` (`src/platform.rs`).
        //   - `--link`'s startup stub passes THIS symbol's address to
        //     `cranelisp_check_layout_hash`, which reads it as `*const &str` —
        //     the same (ptr, len) view, so the two modes read identically.
        // Platform-agnostic: an ordinary Rust static, correct on Mach-O / ELF / PE.
        #[unsafe(export_name = concat!("__cranelisp_layout_hash_", $platform_name))]
        pub static __CRANELISP_LAYOUT_HASH: &str =
            $crate::extract_layout_hash(__CRANELISP_PLATFORM_SCHEMA_TEXT);

        $crate::__declare_platform_body!(
            name: $platform_name,
            version: $platform_version,
            host: $host,
            schema_text: ::core::option::Option::Some(__CRANELISP_PLATFORM_SCHEMA_TEXT),
            functions: [
                $(
                    $fn_ident {
                        cl_name: $cl_name,
                        sig: $sig,
                        doc: $doc,
                        params: [$($param),*],
                        scheduling: $scheduling,
                    }
                ),*
            ]
        );
    };

    // Arm 2: no schema — a scalar-only platform that marshals no ADTs.
    (
        name: $platform_name:literal,
        version: $platform_version:literal,
        host: $host:ident,
        functions: [
            $(
                $fn_ident:ident {
                    cl_name: $cl_name:literal,
                    sig: $sig:literal,
                    doc: $doc:literal,
                    params: [$($param:ident),* $(,)?],
                    scheduling: $scheduling:expr,
                }
            ),* $(,)?
        ]
    ) => {
        $crate::__declare_platform_body!(
            name: $platform_name,
            version: $platform_version,
            host: $host,
            schema_text: ::core::option::Option::<&str>::None,
            functions: [
                $(
                    $fn_ident {
                        cl_name: $cl_name,
                        sig: $sig,
                        doc: $doc,
                        params: [$($param),*],
                        scheduling: $scheduling,
                    }
                ),*
            ]
        );
    };
}

/// Shared body of `declare_platform!` — emits the `cranelisp_platform_manifest`
/// extern fn. Internal; do not invoke directly.
#[doc(hidden)]
#[macro_export]
macro_rules! __declare_platform_body {
    (
        name: $platform_name:literal,
        version: $platform_version:literal,
        host: $host:ident,
        schema_text: $schema_text:expr,
        functions: [
            $(
                $fn_ident:ident {
                    cl_name: $cl_name:literal,
                    sig: $sig:literal,
                    doc: $doc:literal,
                    params: [$($param:ident),* $(,)?],
                    scheduling: $scheduling:expr,
                }
            ),* $(,)?
        ]
    ) => {
        // The exported platform GOT (§5.1) — modelled on
        // `cranelisp-primitives::PRIMITIVES_GOT_SLAB` (FIXME 0280). Slot i holds
        // the fn pointer of the i-th declared function (manifest order IS GOT
        // slot order); the rest stay null. Lives in writable `__DATA` so the
        // `(trace …)` GOT copy-swap can reach platform slots. The host wraps
        // this in place via `GotTable::with_static_backing` — no copy.
        #[unsafe(export_name = concat!("__cranelisp_got_platform_", $platform_name))]
        pub static __CRANELISP_PLATFORM_GOT:
            [$crate::MacroAtomicPtr<u8>; $crate::GOT_TABLE_SIZE] =
            [const { $crate::MacroAtomicPtr::new(::std::ptr::null_mut()) };
                $crate::GOT_TABLE_SIZE];

        // NAMESPACED per platform-interface.md §5.5.5 (DEF-5, ABI v4 step) —
        // the manifest export carries a `_<name>` suffix like the GOT and
        // layout-hash exports, so two force-loaded platform rlibs no longer
        // collide on a bare `cranelisp_platform_manifest`. The pattern string
        // here MUST match `$crate::platform_manifest_symbol` exactly (the host
        // consume side calls that helper); a unit test pins the two together.
        // The macro cannot call a runtime fn in `export_name`, so it emits the
        // suffix with the same `concat!(…, $platform_name)` form the GOT and
        // layout-hash exports already use.
        #[unsafe(export_name = concat!("cranelisp_platform_manifest_", $platform_name))]
        pub unsafe extern "C" fn cranelisp_platform_manifest(
            callbacks: *const $crate::HostCallbacks,
        ) -> $crate::PlatformManifest {
            // Initialize the host context (stores callbacks, sets global alloc).
            unsafe { $host.init(callbacks); }

            // Install the embedded generated schema (if this platform marshals
            // ADTs) so `CLAdt::read_field` resolves field offsets by name
            // (§5.5). A parse failure is a generator/parser grammar drift — a
            // `/dev` bug — and aborts loudly.
            if let ::core::option::Option::Some(schema_text) = $schema_text {
                let schema = $crate::Schema::parse(schema_text).expect(
                    "embedded platform schema artifact failed to parse — \
                     regenerate it with /platform-schema and rebuild",
                );
                $crate::set_global_schema(schema);
            }

            // Populate the exported GOT: slot i ← fn pointer of functions[i].
            // Manifest order IS GOT slot order (§5.1, answer 1). Done here at
            // DLL load so a session/`--link` finds the slots resolved; the host
            // never populates the platform GOT.
            {
                let mut __got_slot: usize = 0;
                $(
                    __CRANELISP_PLATFORM_GOT[__got_slot].store(
                        $fn_ident as *const u8 as *mut u8,
                        ::std::sync::atomic::Ordering::Release,
                    );
                    __got_slot += 1;
                )*
                let _ = __got_slot;
            }

            // Build function descriptors.
            // Phase 1: Capture each function pointer, param info, and scheduling class
            // before shadowing the identifier.
            $(
                #[allow(unused)]
                let $fn_ident = {
                    let fn_ptr = $fn_ident as *const u8;
                    let param_names_vec: Vec<&'static [u8]> = vec![
                        $( stringify!($param).as_bytes(), )*
                    ];
                    let param_count = param_names_vec.len();
                    let (name_ptrs_ptr, name_lens_ptr) = if param_count > 0 {
                        let name_ptrs: Vec<*const u8> =
                            param_names_vec.iter().map(|b| b.as_ptr()).collect();
                        let name_lens: Vec<usize> =
                            param_names_vec.iter().map(|b| b.len()).collect();
                        let ptrs = Box::leak(name_ptrs.into_boxed_slice());
                        let lens = Box::leak(name_lens.into_boxed_slice());
                        (ptrs.as_ptr(), lens.as_ptr())
                    } else {
                        (std::ptr::null::<*const u8>(), std::ptr::null::<usize>())
                    };
                    let scheduling_class = ($scheduling) as u32;
                    (fn_ptr, name_ptrs_ptr, name_lens_ptr, param_count, scheduling_class)
                };
            )*

            // Phase 2: Build PlatformFn descriptors array. Platform fns carry no
            // exported linker name (the former jit_name mangled-name dispatch
            // retired, FIXME 0288) — dispatch is GOT-indirect at the manifest
            // index. The fn pointer in `ptr` is the only address coordinate; the
            // exported GOT (populated above) carries it for code dispatch.
            let functions: &'static [$crate::PlatformFn] = Box::leak(vec![
                $(
                    $crate::PlatformFn {
                        name: $cl_name.as_ptr(),
                        name_len: $cl_name.len(),
                        ptr: ($fn_ident).0,
                        param_count: ($fn_ident).3 as u32,
                        type_sig: $sig.as_ptr(),
                        type_sig_len: $sig.len(),
                        docstring: $doc.as_ptr(),
                        docstring_len: $doc.len(),
                        param_names: ($fn_ident).1,
                        param_name_lens: ($fn_ident).2,
                        param_name_count: ($fn_ident).3,
                        scheduling_class: ($fn_ident).4,
                    },
                )*
            ].into_boxed_slice());

            $crate::PlatformManifest {
                abi_version: $crate::ABI_VERSION,
                name: $platform_name.as_ptr(),
                name_len: $platform_name.len(),
                version: $platform_version.as_ptr(),
                version_len: $platform_version.len(),
                functions: functions.as_ptr(),
                function_count: functions.len(),
            }
        }
    };
}

/// Declare a **poll-shape (concurrent) platform** — the ABI-v7 sibling of
/// [`declare_platform!`] for platforms whose effects are host-reactor poll
/// leaves (`blocking == 0`), not v6 blocking `CLIO` thunks (FIXME 0457,
/// `platform-interface.md` §6.8).
///
/// Each function is a [`crate::PollFn`] (`unsafe extern "C" fn(state, *HostCtx,
/// *Waker) -> Poll`) — NOT a `CLIO`-returning blocking fn — and carries a
/// [`crate::ConcurrencyDescriptor`] (the `descriptor:` key) instead of a
/// `SchedulingClass`. The macro emits TWO exports, deliberately on the **v7
/// channel only** (it does NOT emit the v6 `cranelisp_platform_manifest_<name>`
/// — these functions are not blocking effects, so they have no v6 shape):
///
/// 1. `__cranelisp_got_platform_<name>` — the exported GOT (poll-fn pointers,
///    manifest order = slot order), identical in shape + symbol to the v6 GOT so
///    the host's existing dlsym + `GotTable::with_static_backing` wiring works
///    unchanged.
/// 2. `cranelisp_concurrent_manifest` — a fn taking `HostCallbacks`, returning a
///    [`crate::ConcurrentPlatformManifest`]; it inits the host context, populates
///    the GOT, and builds the [`crate::ConcurrentPlatformFn`] array. The
///    concurrency-built host dlsym-probes this symbol FIRST (`src/platform.rs`).
///
/// Gated usage: the platform crate must enable `cranelisp-platform/concurrency`
/// (so the v7 types resolve). `drop_state` is `None` for S94 (the reserved-inert
/// hook; the in-tree demo's state is host-known — `effect-concurrency.md` §13
/// decision 4).
#[macro_export]
macro_rules! declare_concurrent_platform {
    (
        name: $platform_name:literal,
        version: $platform_version:literal,
        host: $host:ident,
        functions: [
            $(
                $fn_ident:ident {
                    cl_name: $cl_name:literal,
                    sig: $sig:literal,
                    doc: $doc:literal,
                    params: [$($param:ident),* $(,)?],
                    descriptor: $descriptor:expr,
                }
            ),* $(,)?
        ]
    ) => {
        // The exported platform GOT (§5.1) — slot i holds poll-fn i's pointer.
        // Same symbol + shape as the v6 GOT (the host dlsyms it by name).
        #[unsafe(export_name = concat!("__cranelisp_got_platform_", $platform_name))]
        pub static __CRANELISP_PLATFORM_GOT:
            [$crate::MacroAtomicPtr<u8>; $crate::GOT_TABLE_SIZE] =
            [const { $crate::MacroAtomicPtr::new(::std::ptr::null_mut()) };
                $crate::GOT_TABLE_SIZE];

        // The v7 concurrent manifest export. NOT namespaced by platform name: a
        // concurrent platform is dlopened as its own library and the host
        // dlsyms this symbol in that specific handle (FIXME 0457).
        #[unsafe(export_name = "cranelisp_concurrent_manifest")]
        pub unsafe extern "C" fn cranelisp_concurrent_manifest(
            callbacks: *const $crate::HostCallbacks,
        ) -> $crate::ConcurrentPlatformManifest {
            // Initialize the host context (stores callbacks, sets global alloc).
            unsafe { $host.init(callbacks); }

            // Populate the exported GOT: slot i ← poll-fn i (manifest order IS
            // GOT slot order, §5.1).
            {
                let mut __got_slot: usize = 0;
                $(
                    __CRANELISP_PLATFORM_GOT[__got_slot].store(
                        $fn_ident as *const u8 as *mut u8,
                        ::std::sync::atomic::Ordering::Release,
                    );
                    __got_slot += 1;
                )*
                let _ = __got_slot;
            }

            // Phase 1: capture each poll-fn pointer + param info before shadowing.
            $(
                #[allow(unused)]
                let $fn_ident = {
                    let poll: $crate::PollFn = $fn_ident;
                    let param_names_vec: Vec<&'static [u8]> = vec![
                        $( stringify!($param).as_bytes(), )*
                    ];
                    let param_count = param_names_vec.len();
                    let (name_ptrs_ptr, name_lens_ptr) = if param_count > 0 {
                        let name_ptrs: Vec<*const u8> =
                            param_names_vec.iter().map(|b| b.as_ptr()).collect();
                        let name_lens: Vec<usize> =
                            param_names_vec.iter().map(|b| b.len()).collect();
                        let ptrs = Box::leak(name_ptrs.into_boxed_slice());
                        let lens = Box::leak(name_lens.into_boxed_slice());
                        (ptrs.as_ptr(), lens.as_ptr())
                    } else {
                        (std::ptr::null::<*const u8>(), std::ptr::null::<usize>())
                    };
                    let descriptor: $crate::ConcurrencyDescriptor = $descriptor;
                    (poll, name_ptrs_ptr, name_lens_ptr, param_count, descriptor)
                };
            )*

            // Phase 2: build the ConcurrentPlatformFn array.
            let functions: &'static [$crate::ConcurrentPlatformFn] = Box::leak(vec![
                $(
                    $crate::ConcurrentPlatformFn {
                        name: $cl_name.as_ptr(),
                        name_len: $cl_name.len(),
                        poll: ($fn_ident).0,
                        // RESERVED-but-inert (S94): host-known state, no leaf hook.
                        drop_state: ::core::option::Option::None,
                        param_count: ($fn_ident).3 as u32,
                        type_sig: $sig.as_ptr(),
                        type_sig_len: $sig.len(),
                        docstring: $doc.as_ptr(),
                        docstring_len: $doc.len(),
                        param_names: ($fn_ident).1,
                        param_name_lens: ($fn_ident).2,
                        param_name_count: ($fn_ident).3,
                        concurrency: ($fn_ident).4,
                    },
                )*
            ].into_boxed_slice());

            $crate::ConcurrentPlatformManifest {
                abi_version: $crate::ABI_VERSION,
                name: $platform_name.as_ptr(),
                name_len: $platform_name.len(),
                version: $platform_version.as_ptr(),
                version_len: $platform_version.len(),
                functions: functions.as_ptr(),
                function_count: functions.len(),
            }
        }
    };
}
