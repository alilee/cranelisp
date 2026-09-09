//! The `declare_platform!` three-exports emitter — the DLL-author entry point.
//!
//! This module co-locates the three-exports macro pair with the
//! compile-time helper they depend on:
//!
//! - [`extract_layout_hash`] — pulls the `;; layout-hash: <hex>` header out of a
//!   generated schema artifact at compile time so the `schema:` arm can export it
//!   as `__cranelisp_layout_hash_<name>`.
//! - [`schema_declares_type`] — checks at compile time that an `adts:` marker's
//!   bare FQ key is an entry in that same artifact.
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
/// <hex>` header line, at compile time, so the
/// [`macro@crate::declare_platform`] `schema:`
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
                std::str::from_utf8_unchecked(std::slice::from_raw_parts(
                    bytes.as_ptr().add(start),
                    end - start,
                ))
            };
            return slice;
        }
        i += 1;
    }
    ""
}

/// Whether a generated schema artifact declares the bare fully-qualified
/// `type_key` supplied by a [`macro@crate::declare_platform`] `adts:` marker.
///
/// This is a second, const-evaluable reader of the generated artifact grammar;
/// the runtime parser and grammar authority remain [`crate::Schema::parse`] and
/// `crate::schema`'s module documentation. Any grammar change must update both
/// readers. The scan tracks parenthesis depth and skips `;;` comments, so a key
/// mentioned only as a field type or in commentary is not a declaration.
///
/// Only bare keys such as `shapes/Rectangle` are accepted. Empty keys, applied
/// forms and keys containing ASCII whitespace or parentheses return `false`;
/// applied marker keys remain expressible through a hand-written
/// [`crate::CLAdtType`] implementation.
pub const fn schema_declares_type(artifact: &str, type_key: &str) -> bool {
    let key = type_key.as_bytes();
    if key.is_empty() {
        return false;
    }
    let mut k = 0;
    while k < key.len() {
        if key[k] == b'('
            || key[k] == b')'
            || key[k] == b' '
            || key[k] == b'\t'
            || key[k] == b'\r'
            || key[k] == b'\n'
        {
            return false;
        }
        k += 1;
    }

    let bytes = artifact.as_bytes();
    let mut depth = 0usize;
    let mut i = 0usize;
    while i < bytes.len() {
        if bytes[i] == b';' && i + 1 < bytes.len() && bytes[i + 1] == b';' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' && bytes[i] != b'\r' {
                i += 1;
            }
            continue;
        }
        if bytes[i] == b'(' {
            depth += 1;
            i += 1;
            if depth == 2 {
                while i < bytes.len()
                    && (bytes[i] == b' '
                        || bytes[i] == b'\t'
                        || bytes[i] == b'\r'
                        || bytes[i] == b'\n')
                {
                    i += 1;
                }
                let start = i;
                while i < bytes.len()
                    && bytes[i] != b' '
                    && bytes[i] != b'\t'
                    && bytes[i] != b'\r'
                    && bytes[i] != b'\n'
                    && bytes[i] != b'('
                    && bytes[i] != b')'
                {
                    i += 1;
                }
                if i - start == key.len() {
                    let mut same = true;
                    let mut n = 0;
                    while n < key.len() {
                        if bytes[start + n] != key[n] {
                            same = false;
                            break;
                        }
                        n += 1;
                    }
                    if same {
                        return true;
                    }
                }
                continue;
            }
            continue;
        }
        if bytes[i] == b')' {
            depth = depth.saturating_sub(1);
        }
        i += 1;
    }
    false
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
///    a [`crate::PlatformManifest`] of [`crate::PlatformFn`] descriptors (name, FQ type_sig,
///    scheduling class, docstring, param-names). The host builds its
///    `SymbolTable` from this.
/// 3. **The embedded schema + layout hash** (optional `schema:` arm) — the
///    `/platform-schema`-generated artifact text, embedded via `include_str!`,
///    parsed once into the per-DLL [`crate::Schema`] (`CLAdt::read_field` reads it by
///    name); the artifact's `;; layout-hash:` header is exported as the data
///    symbol `__cranelisp_layout_hash_<name>` (§5.5.4). The arm is optional —
///    an absent schema is tolerated for first builds (the layout-hash gate then
///    compares against an empty hash; the REPL warns).
///
/// Platform functions are normal `extern "C"` Rust functions over the `CL*`
/// wrapper family — defined outside the macro. **Platforms do not declare ADT
/// layouts:** a platform's data types are ordinary `.cl` modules; the macro's
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
/// | `adts:` | optional, with `schema:` only | `[ Marker => "module/Type", ... ]` | Emit [`crate::CLAdtType`] markers and assert each bare FQ key is declared by the embedded artifact |
/// | `functions:` | yes | `[ fn { ... }, ... ]` array | Per-fn descriptors |
///
/// Each per-fn block has four required fields — `cl_name:` (kebab-case
/// user-visible name), `sig:` (fully-qualified, fully concrete type-signature
/// S-expression; a bare lowercase leaf is a refused type variable), `doc:`
/// (docstring), `params:` (named-parameter ident list) — plus a **concurrency
/// key** that is EITHER `scheduling:` ([`crate::SchedulingClass`] expression — the
/// blocking-effect sugar, lowered via
/// [`crate::ConcurrencyDescriptor::from_scheduling_class`]) OR `descriptor:`
/// ([`crate::ConcurrencyDescriptor`] expression — a poll-shape leaf, `blocking =
/// 0`), and an OPTIONAL `drop_state:` (an
/// `unsafe extern "C" fn(*mut c_void)` poll-leaf teardown hook).
///
/// # ABI v10 — the single ABI
///
/// [`crate::ABI_VERSION`] is now **10**. The v6/v7 dual-channel split was
/// collapsed into one ABI (`design/arch/platform-interface.md` §6.8.0): one macro
/// (`declare_concurrent_platform!` is **deleted**), one manifest type, one GOT
/// export, ONE loader path. A platform may freely mix blocking effects
/// (`scheduling:` / `descriptor` with `blocking = 1`) and poll-shape leaves
/// (`descriptor` with `blocking = 0`) in ONE manifest; the host reads
/// `concurrency.blocking` per effect to pick the dispatch node. A blocking effect
/// is an `extern "C"` fn returning [`crate::CLIO`]; a poll-shape leaf is a
/// [`crate::PollFn`] (`unsafe extern "C" fn(state, *HostCtx, *Waker) -> Poll`).
///
/// The current stamp matters at the load-time ABI gate: a DLL built from this
/// crate stamps `abi_version: ABI_VERSION`, and the host rejects a mismatch with
/// [`crate::PlatformError`]`::AbiVersionMismatch`. In-workspace host + platform
/// DLLs rebuild together, so the stamp stays consistent.
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
    // Arm 1a: schema embed plus compile-time-bound ADT marker types. This
    // delegates the three exports to arm 1 after emitting the markers and
    // checking their keys against the exact bytes arm 1 embeds.
    (
        name: $platform_name:literal,
        version: $platform_version:literal,
        host: $host:ident,
        schema: $schema_text:expr,
        adts: [
            $(
                $(#[$attr:meta])*
                $marker:ident => $key:literal
            ),* $(,)?
        ],
        functions: [
            $(
                $fn_ident:ident {
                    cl_name: $cl_name:literal,
                    sig: $sig:literal,
                    doc: $doc:literal,
                    params: [$($param:ident),* $(,)?],
                    $conc_key:ident: $conc_val:expr,
                    $(drop_state: $drop_state:expr,)?
                }
            ),* $(,)?
        ]
    ) => {
        $(
            $(#[$attr])*
            pub struct $marker;

            impl $crate::CLAdtType for $marker {
                const TYPE_NAME: &'static str = $key;
            }

            const _: () = assert!(
                $crate::schema_declares_type($schema_text, $key),
                concat!(
                    "declare_platform!: ADT marker `", stringify!($marker), "` names \"", $key,
                    "\", which is no bare fully-qualified entry in this platform's embedded ",
                    "schema. The adts: key accepts module/Type names only; check the spelling, ",
                    "or regenerate the artifact with /platform-schema if the type changed."
                ),
            );
        )*

        $crate::declare_platform! {
            name: $platform_name,
            version: $platform_version,
            host: $host,
            schema: $schema_text,
            functions: [
                $(
                    $fn_ident {
                        cl_name: $cl_name,
                        sig: $sig,
                        doc: $doc,
                        params: [$($param),*],
                        $conc_key: $conc_val,
                        $(drop_state: $drop_state,)?
                    }
                ),*
            ]
        }
    };

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
                    $conc_key:ident: $conc_val:expr,
                    $(drop_state: $drop_state:expr,)?
                }
            ),* $(,)?
        ]
    ) => {
        // The embedded generated schema artifact text (typically
        // `include_str!("<name>.platform-schema")`).
        const __CRANELISP_PLATFORM_SCHEMA_TEXT: &str = $schema_text;

        // Export the layout hash (extracted from the artifact's
        // `;; layout-hash:` header at compile time) as a data symbol the host
        // compares against its live-tables regeneration (§5.5.4).
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
                        $conc_key: $conc_val,
                        $(drop_state: $drop_state,)?
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
                    $conc_key:ident: $conc_val:expr,
                    $(drop_state: $drop_state:expr,)?
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
                        $conc_key: $conc_val,
                        $(drop_state: $drop_state,)?
                    }
                ),*
            ]
        );
    };
}

/// Lower a per-fn concurrency key to a [`crate::ConcurrencyDescriptor`].
///
/// `scheduling: <SchedulingClass>` is the blocking-effect sugar (→
/// [`crate::ConcurrencyDescriptor::from_scheduling_class`], `blocking = 1`);
/// `descriptor: <ConcurrencyDescriptor>` is the full form (poll-shape leaves set
/// `blocking = 0`). Internal to [`declare_platform!`]; do not invoke directly.
#[doc(hidden)]
#[macro_export]
macro_rules! __platform_concurrency {
    (scheduling $e:expr) => {
        $crate::ConcurrencyDescriptor::from_scheduling_class($e)
    };
    (descriptor $e:expr) => {
        $e
    };
}

/// Lower the OPTIONAL per-fn `drop_state:` key to an `Option<fn>`. Absent ⇒
/// `None`. Internal to [`declare_platform!`]; do not invoke directly.
#[doc(hidden)]
#[macro_export]
macro_rules! __platform_drop_state {
    () => {
        ::core::option::Option::None
    };
    ($e:expr) => {
        ::core::option::Option::Some($e)
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
                    $conc_key:ident: $conc_val:expr,
                    $(drop_state: $drop_state:expr,)?
                }
            ),* $(,)?
        ]
    ) => {
        // The exported platform GOT (§5.1). Slot i holds the fn pointer of the
        // i-th declared function (manifest order IS GOT slot order); the rest stay
        // null. Lives in writable `__DATA`. The host wraps this in place via
        // `GotTable::with_static_backing` — no copy.
        #[unsafe(export_name = concat!("__cranelisp_got_platform_", $platform_name))]
        pub static __CRANELISP_PLATFORM_GOT:
            [$crate::MacroAtomicPtr<u8>; $crate::GOT_TABLE_SIZE] =
            [const { $crate::MacroAtomicPtr::new(::std::ptr::null_mut()) };
                $crate::GOT_TABLE_SIZE];

        // NAMESPACED per platform-interface.md §5.5.5 — the manifest export
        // carries a `_<name>` suffix like the GOT and layout-hash exports. The
        // pattern string MUST match `$crate::platform_manifest_symbol` exactly.
        #[unsafe(export_name = concat!("cranelisp_platform_manifest_", $platform_name))]
        pub unsafe extern "C" fn cranelisp_platform_manifest(
            callbacks: *const $crate::HostCallbacks,
        ) -> $crate::PlatformManifest {
            // Initialize the host context (stores callbacks, sets global alloc).
            unsafe { $host.init(callbacks); }

            // Install the embedded generated schema (if this platform marshals
            // ADTs) so `CLAdt::read_field` resolves field offsets by name (§5.5).
            if let ::core::option::Option::Some(schema_text) = $schema_text {
                let schema = $crate::Schema::parse(schema_text).expect(
                    "embedded platform schema artifact failed to parse — \
                     regenerate it with /platform-schema and rebuild",
                );
                $crate::set_global_schema(schema);
            }

            // Populate the exported GOT: slot i ← fn pointer of functions[i].
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

            // Phase 1: capture each fn pointer, param info, the unified
            // concurrency descriptor, and the optional drop_state hook before
            // shadowing the identifier.
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
                    let concurrency: $crate::ConcurrencyDescriptor =
                        $crate::__platform_concurrency!($conc_key $conc_val);
                    let drop_state: ::core::option::Option<
                        unsafe extern "C" fn(state: *mut ::core::ffi::c_void),
                    > = $crate::__platform_drop_state!($($drop_state)?);
                    (fn_ptr, name_ptrs_ptr, name_lens_ptr, param_count, concurrency, drop_state)
                };
            )*

            // Phase 2: Build the unified PlatformFn descriptor array.
            let functions: &'static [$crate::PlatformFn] = Box::leak(vec![
                $(
                    $crate::PlatformFn {
                        name: $cl_name.as_ptr(),
                        name_len: $cl_name.len(),
                        ptr: ($fn_ident).0,
                        drop_state: ($fn_ident).5,
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

// ---------------------------------------------------------------------------
// Platform-declaration tier (FIXME 0501/0502)
//
// declare.rs is the surface every platform DLL's correctness flows through and
// had ZERO inline coverage. Two strategy scenario spaces per METHOD §2.2:
//
//  * `extract_layout_hash` — a pure `const fn` scanner. The crate-root
//    `tests.rs::extract_layout_hash_reads_header` covers three basic cases;
//    this DEEPENS to the boundary/negative cells it omits (mid-file marker,
//    CRLF, EOF-without-newline, tab indent, empty input, near-miss markers).
//  * `declare_platform!` — the three-exports emitter. The load-bearing invariant
//    is **manifest order IS GOT slot order** (§5.1); we invoke the macro and
//    pin it end-to-end (order, FQ-sig fidelity, count, abi_version, unused slots
//    null) — untested anywhere (tests.rs builds manifests by hand, never via
//    the macro).
// spec: design/arch/platform-interface.md §5.5.4 / §5.1 / §6.1.
// ---------------------------------------------------------------------------
#[cfg(test)]
mod tests {
    // -- extract_layout_hash: boundary + negative cells --

    use super::extract_layout_hash as elh;
    use super::schema_declares_type as sdt;

    #[test]
    fn extract_layout_hash_finds_marker_not_on_first_line() {
        assert_eq!(
            elh("(schema stuff)\n;; layout-hash: cafef00d\n"),
            "cafef00d"
        );
    }

    #[test]
    fn extract_layout_hash_handles_crlf_line_ending() {
        // The end-of-line scan stops at \r, so the trailing CR is not captured.
        assert_eq!(elh(";; layout-hash: abc123\r\n(schema)"), "abc123");
    }

    #[test]
    fn extract_layout_hash_handles_eof_without_newline() {
        assert_eq!(elh(";; layout-hash: 0f0f0f"), "0f0f0f");
    }

    #[test]
    fn extract_layout_hash_trims_tab_indent_and_trailing_tabs() {
        assert_eq!(elh(";; layout-hash:\t\tbeef\t\t\n"), "beef");
    }

    #[test]
    fn extract_layout_hash_returns_first_of_multiple_markers() {
        assert_eq!(
            elh(";; layout-hash: first\n;; layout-hash: second\n"),
            "first",
        );
    }

    // negatives: what must NOT be matched.
    #[test]
    fn extract_layout_hash_empty_input_is_empty() {
        assert_eq!(elh(""), "");
    }

    #[test]
    fn extract_layout_hash_near_miss_marker_does_not_match() {
        // Missing the space after ";;" — not the exact marker.
        assert_eq!(elh(";;layout-hash: nope\n"), "");
        // Missing the trailing colon — not the exact marker.
        assert_eq!(elh(";; layout-hash nope\n"), "");
    }

    #[test]
    fn extract_layout_hash_marker_with_empty_value_is_empty() {
        assert_eq!(elh(";; layout-hash:\n(schema)"), "");
        assert_eq!(elh(";; layout-hash:   \n"), "");
    }

    const SCHEMA_WITH_NESTED_REFERENCE: &str = "\
;; layout-hash: marker-tests
(schema
  (shapes/Outer
    (Outer 0 ((inner shapes/Inner))))
  (shapes/Other
    (Other 0 ())))";

    #[test]
    fn schema_declares_type_finds_a_declared_entry() {
        assert!(sdt(SCHEMA_WITH_NESTED_REFERENCE, "shapes/Outer"));
        assert!(sdt(SCHEMA_WITH_NESTED_REFERENCE, "shapes/Other"));
    }

    #[test]
    fn schema_declares_type_rejects_an_absent_entry() {
        assert!(!sdt(SCHEMA_WITH_NESTED_REFERENCE, "shapes/Missing"));
    }

    #[test]
    fn schema_declares_type_does_not_treat_a_field_type_as_a_declaration() {
        assert!(!sdt(SCHEMA_WITH_NESTED_REFERENCE, "shapes/Inner"));
    }

    #[test]
    fn schema_declares_type_skips_comment_occurrences() {
        assert!(!sdt(
            ";; (shapes/Commented (Commented 0 ()))\n(schema)",
            "shapes/Commented",
        ));
    }

    #[test]
    fn schema_declares_type_rejects_empty_artifacts_and_keys() {
        assert!(!sdt("", "shapes/Outer"));
        assert!(!sdt(SCHEMA_WITH_NESTED_REFERENCE, ""));
    }

    #[test]
    fn schema_declares_type_rejects_applied_or_non_bare_keys() {
        assert!(!sdt(
            "(schema ((shapes/Box primitives/Int) (Box 0 ())))",
            "(shapes/Box primitives/Int)",
        ));
        assert!(!sdt(SCHEMA_WITH_NESTED_REFERENCE, "shapes /Outer"));
    }

    // -- declare_platform!: manifest order IS GOT slot order --

    extern "C" fn eff_a() -> i64 {
        1
    }
    extern "C" fn eff_b() -> i64 {
        2
    }
    extern "C" fn eff_c() -> i64 {
        3
    }

    static HOST: crate::HostContext = crate::HostContext::new();

    crate::declare_platform! {
        name: "declaretest",
        version: "0.1.0",
        host: HOST,
        functions: [
            eff_a {
                cl_name: "eff-a",
                sig: "(Fn [primitives/Int] (primitives/IO primitives/Int))",
                doc: "first",
                params: [n],
                scheduling: crate::SchedulingClass::Sequential,
            },
            eff_b {
                cl_name: "eff-b",
                sig: "(Fn [primitives/Int] (primitives/IO primitives/Int))",
                doc: "second",
                params: [n],
                scheduling: crate::SchedulingClass::Commutative,
            },
            eff_c {
                cl_name: "eff-c",
                sig: "(Fn [primitives/Int] (primitives/IO primitives/Int))",
                doc: "third",
                params: [n],
                scheduling: crate::SchedulingClass::ResourceSerial,
            },
        ]
    }

    fn cl_name(f: &crate::PlatformFn) -> &str {
        unsafe { std::str::from_utf8(std::slice::from_raw_parts(f.name, f.name_len)).unwrap() }
    }

    fn type_sig(f: &crate::PlatformFn) -> &str {
        unsafe {
            std::str::from_utf8(std::slice::from_raw_parts(f.type_sig, f.type_sig_len)).unwrap()
        }
    }

    #[test]
    fn declare_platform_manifest_order_is_got_slot_order() {
        use std::sync::atomic::Ordering;

        extern "C" fn t_alloc(_: i64) -> i64 {
            0
        }
        let cb = crate::HostCallbacks {
            alloc: t_alloc,
            alloc_with_tag: crate::null_alloc_with_tag,
        };
        // SAFETY: `cb` is a valid HostCallbacks; the macro reads it via init.
        let manifest = unsafe { cranelisp_platform_manifest(&cb) };

        assert_eq!(
            manifest.abi_version,
            crate::ABI_VERSION,
            "stamps the crate ABI"
        );
        assert_eq!(manifest.function_count, 3, "three declared functions");

        // SAFETY: the macro leaks a &'static [PlatformFn] of function_count entries.
        let funcs =
            unsafe { std::slice::from_raw_parts(manifest.functions, manifest.function_count) };

        // The load-bearing invariant: GOT slot i holds functions[i].ptr, in
        // declaration order (manifest order IS GOT slot order, §5.1).
        for (i, f) in funcs.iter().enumerate() {
            let slot = __CRANELISP_PLATFORM_GOT[i].load(Ordering::Acquire) as *const u8;
            assert_eq!(slot, f.ptr, "GOT slot {i} must hold functions[{i}].ptr");
            assert!(!f.ptr.is_null(), "declared slot {i} is populated");
        }

        // Declaration order is preserved through the manifest.
        assert_eq!(cl_name(&funcs[0]), "eff-a");
        assert_eq!(cl_name(&funcs[1]), "eff-b");
        assert_eq!(cl_name(&funcs[2]), "eff-c");
        // The three GOT slots hold three DISTINCT fn pointers (no aliasing).
        assert_ne!(funcs[0].ptr, funcs[1].ptr);
        assert_ne!(funcs[1].ptr, funcs[2].ptr);

        // FQ signature carried verbatim (FQ-sig rendering).
        assert_eq!(
            type_sig(&funcs[0]),
            "(Fn [primitives/Int] (primitives/IO primitives/Int))",
        );

        // Unused GOT slots (beyond the declared count) stay null.
        assert!(
            __CRANELISP_PLATFORM_GOT[3]
                .load(Ordering::Acquire)
                .is_null(),
            "slot past the declared functions must stay null",
        );
        assert!(
            __CRANELISP_PLATFORM_GOT[crate::GOT_TABLE_SIZE - 1]
                .load(Ordering::Acquire)
                .is_null(),
            "the last GOT slot stays null for a 3-fn platform",
        );
    }
}
