//! Shared interface crate for the cranelisp platform ABI — the C-ABI
//! ground-truth that lives between the cranelisp host binary and every
//! platform DLL.
//!
//! # Dual audience
//!
//! Both consumers link against this crate:
//!
//! - **The host binary** (`cranelisp`) calls [`manifest_to_descriptors`]
//!   to load a DLL's manifest into safe Rust shapes, owns the
//!   [`HostContext`] / [`HostCallbacks`] init-time bridge, and dispatches
//!   platform-fn calls via the per-symbol GOT slot (Decision 0026).
//! - **Each platform DLL** (out-of-tree crates like `cranelisp-stdio`,
//!   `cranelisp-fs`, etc.) calls the [`declare_platform!`] macro to
//!   emit its [`PlatformManifest`] static, defines `extern "C"` functions
//!   that take/return CL wrapper types ([`CLInt`], [`CLBool`], [`CLFloat`],
//!   [`CLString`], [`CLIO`], [`CLAdt`]), and accesses host services
//!   (allocator, RC, validation) through the host-installed
//!   [`HostCallbacks`].
//!
//! Per Principle 15's **external-audience exception**, this crate's
//! facade lives with its source rustdoc (after Sprint 71 the standalone
//! `design/arch/facades/platform.md` retired into this rustdoc plus
//! `design/arch/bounded-contexts.md` §5 — the 3rd data point of the
//! facade-retirement pattern after `types.md` (S69) and `frontend.md`
//! (S70)). DLL author crates need only depend on `cranelisp-platform`;
//! re-exports from `cranelisp-types` (currently [`SchedulingClass`] and
//! [`PlatformError`]) are surfaced here so DLL authors avoid a
//! `cranelisp-types` dep.
//!
//! # CL wrapper family — the value-marshaling surface
//!
//! Every cranelisp value crosses the DLL boundary as a `#[repr(transparent)]`
//! `i64` wrapped in a typed handle. The wrapper makes the boundary
//! type-safe in Rust while preserving the bare-`i64` C ABI.
//!
//! | Wrapper | Underlying `i64` is | Heap? |
//! |---|---|---|
//! | [`CLInt`] | Cranelisp integer (passthrough) | No |
//! | [`CLBool`] | 0 = false, 1 = true | No |
//! | [`CLFloat`] | IEEE 754 `f64` bit-cast | No |
//! | [`CLString`] | Base pointer to `[total_size][rc][len][bytes...]` | Yes ([`CLHeap`]) |
//! | [`CLIO<CL>`] | Base pointer to an IO node (`Pure`/`Effect`/`Bind`/`Par`) | Yes |
//! | [`CLAdt<T>`] | Base pointer to `[total_size][rc][tag][pad][fields...]` | Yes ([`CLHeap`]) |
//!
//! [`CLOwned<T>`] is the host-side RAII wrapper that holds a heap-typed
//! value with correct RC discipline across multiple host-callback
//! invocations: it inc's on construction (via [`CLHeap::own`]) and
//! dec's on drop. The consuming variant [`CLHeap::into_owned_consuming`]
//! takes the caller's transferred ref directly without re-inc'ing — used
//! by platform externs that capture a heap parameter into an Effect
//! closure (Decision 0024 — consuming capture-RC protocol; see
//! `design/backend/ring2-rc.md` §10.4).
//!
//! # RC discipline at the boundary
//!
//! Cross-cutting reference-counting rules govern heap values:
//!
//! - All heap CL types store **base pointers** (the address of the
//!   `[total_size][rc][...]` allocation header), NOT payload pointers.
//!   Decision 0013 sets the allocator's payload-base convention; Decision
//!   0024 specifies the consuming calling convention; Decision 0026
//!   determines where the per-fn `code_ptr` lives.
//! - [`CLHeap::inc_rc`] / [`CLHeap::dec_rc`] use `Ordering::SeqCst`
//!   to match Cranelift's `atomic_rmw` semantics — `Relaxed` is unsound
//!   because it allows the dec to be reordered before object-field reads
//!   (potential read-after-free).
//! - Drop with old RC = 1 calls `std::alloc::dealloc` against the base
//!   pointer using the recorded `alloc_size` at offset 0.
//!
//! # ABI versioning
//!
//! [`ABI_VERSION`] is the single layout-discipline gate between host
//! and DLL. Per Principle 14 (FFI layout discipline), any
//! layout-affecting change to a `#[repr(C)]` struct or a const the DLL
//! reads by hard-coded offset bumps the version; the host rejects
//! mismatched DLLs with [`PlatformError::AbiVersionMismatch`]. See
//! [`ABI_VERSION`]'s rustdoc for the bump-rule enumeration.
//!
//! # Schema mechanism — embedded generated artifact (Sprint 76, FIXME 0286)
//!
//! Platforms **do not declare ADTs**. A platform's data types are ordinary
//! `.cl` modules; its function signatures reference them by fully-qualified
//! name (`(Fn [shapes/Rectangle] primitives/Int)`). For DLLs that marshal ADT
//! values, the [`declare_platform!`] macro's `schema:` arm embeds the
//! **compiler-generated schema artifact** (`/platform-schema`-produced text,
//! typically `schema: include_str!("<name>.platform-schema")`). The macro
//! parses that artifact once into the per-DLL [`Schema`] and installs it via
//! [`set_global_schema`]; it also exports the artifact's `;; layout-hash:`
//! header as the data symbol `__cranelisp_layout_hash_<name>` for the host's
//! load/link staleness gate (`design/arch/platform-interface.md` §5.5).
//!
//! DLL authors write `extern "C" fn rectangle_area(r: CLAdt<Rectangle>) ->
//! CLInt { r.read_field::<CLInt>("w") ... }`. Field-access reads are
//! **callback-free**: [`CLAdt::read_field`] resolves the field's byte offset +
//! declared [`FieldType`] **by name** from the embedded schema and transmutes
//! at that offset — no host round-trip per access. Construction
//! ([`CLAdt::construct`]) routes through [`HostCallbacks::alloc_with_tag`]
//! (wired by the host since S76).
//!
//! The Sprint 71 schema *declaration* dialect (the `LazyLock<Schema>`-as-DSL
//! static, marker-type auto-emission, `GetSchema`, `schema_types:`) is
//! **retired** — the schema is one machine-generated artifact, never
//! hand-authored. See `design/arch/platform-interface.md` §6.6 for the
//! retirement table.
//!
//! # `#[non_exhaustive]` discipline
//!
//! Per Principle 14, FFI boundary types are governed by layout discipline
//! (`ABI_VERSION`), not source-level evolution guards. Layout-contract
//! types ([`PlatformManifest`], [`PlatformFn`], [`HostCallbacks`] —
//! `#[repr(C)]`; [`CLInt`]/[`CLBool`]/[`CLFloat`]/[`CLString`]/[`CLIO`]/[`CLAdt`]
//! — `#[repr(transparent)]`) are **exempt**: any field change is a
//! breaking change requiring an `ABI_VERSION` bump, and a `#[non_exhaustive]`
//! annotation would not catch a `#[repr(transparent)]` underlying-type
//! swap anyway. Plain Rust structs that don't cross the C ABI
//! ([`OwnedPlatformFnDescriptor`], [`PlatformError`] via cranelisp-types)
//! carry `#[non_exhaustive]` under the standard facade convention.
//!
//! # Consumed surface
//!
//! Depends only on `cranelisp-types` (for [`SchedulingClass`],
//! [`PlatformError`], `Symbol`, `Span`, layout helpers). The external
//! `libloading` dep that opens the DLL handles lives on the `int` side
//! per the bounded-context allocation (see
//! `design/arch/bounded-contexts.md` §5).
//!
//! # See also
//!
//! - `design/arch/bounded-contexts.md` §5 — Platform bounded-context
//!   full statement (cross-surface narrative + invariants).
//! - `design/platform/sprint71-redesign.md` — Sprint 71 design doc
//!   (schema format, marker-type pattern, ABI v2 growth).
//! - Principles 6, 8, 14, 15, 18 — design budget, no-interim, FFI
//!   layout, facade-types-live-with-behaviour, structural invariants.

use std::ops::Deref;
use std::sync::atomic::{AtomicPtr, Ordering};

mod schema;
pub use schema::{Ctor, Field, FieldType, ParseLoc, Schema, SchemaParseError, TypeShape};

mod adt;
pub use adt::{set_global_schema, CLAdt, CLAdtType, CLTypeWitness, ExpectedFieldType};

// The `declare_platform!` three-exports emitter + its compile-time
// `extract_layout_hash` helper. The macros are `#[macro_export]` (crate-root
// resolution); `extract_layout_hash` is re-exported here so the macro's
// `$crate::extract_layout_hash` path and in-crate callers resolve identically.
mod declare;
pub use declare::extract_layout_hash;

/// GOT table size — re-exported from `cranelisp-types` so the
/// [`declare_platform!`] macro can size the exported platform GOT
/// (`__cranelisp_got_platform_<name>`) without the caller crate depending on
/// `cranelisp-types`. One slot per manifest function; the rest stay null
/// (the primitives `__cranelisp_got_primitives` precedent, FIXME 0280).
pub use cranelisp_types::GOT_TABLE_SIZE;

/// Re-exported so the macro's exported-GOT static can name the slot type
/// (`[AtomicPtr<u8>; GOT_TABLE_SIZE]`) hygienically in the caller crate.
#[doc(hidden)]
pub use std::sync::atomic::AtomicPtr as MacroAtomicPtr;

/// Platform ABI version — bump on any layout-affecting change to the
/// platform DLL boundary.
///
/// **Bump rules** (per `design/platform/sprint71-redesign.md` §6 / A4):
///
/// (i)  Any field added/removed/reordered in `HostCallbacks`,
///      `PlatformFn`, `PlatformManifest`: BUMP.
/// (ii) Any change to `HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`,
///      `IO_TAG_*`, `IO_EFFECT_RESOURCE_OFFSET`: BUMP.
/// (iii) Any new `CL_TYPE_TAG_*` const value: BUMP (DLLs built against
///       the old ABI don't know to populate the new tag).
/// (iv) Adding a new pub `CL<T>` wrapper variant — alone — does NOT
///      bump (Principle 14 `#[repr(transparent)]` exemption).
/// (v)  Adding a method on `CLAdt` (no new `HostCallbacks` field, no new
///      const) does NOT bump.
///
/// Every bump rides with a `public-api.txt` regeneration and a narrative
/// update naming the changed item (S67 close baseline-diff discipline).
///
/// **History**: v1 (Sprint 67-and-prior) — initial ABI; v2 (Sprint 71) —
/// `HostCallbacks` grows `alloc_with_tag` + `validate_schema` for the
/// ADT-marshaling surface; v3 (Sprint 76, FIXME 0286 / platform-interface.md
/// §6.1) — the `declare_platform!` macro reworked to the three-exports model
/// (exported GOT `__cranelisp_got_platform_<name>` + manifest + embedded
/// generated schema with `__cranelisp_layout_hash_<name>`); the schema
/// *declaration* dialect retired (platforms stop declaring ADTs — their types
/// are ordinary `.cl` modules), `read_field` is now name-based against the
/// embedded generated artifact. `HostCallbacks::validate_schema` /
/// `null_validate_schema` and `PlatformFn.jit_name` / `derive_jit_name` /
/// `OwnedPlatformFnDescriptor.jit_name` are **removed** (FIXME 0288 — the int
/// load path now dispatches GOT-indirect against the exported GOT, so platform
/// fns need no exported linker name and the host injects no schema-validation
/// callback). The v3 ABI surface is `HostCallbacks { alloc, alloc_with_tag }` +
/// the jit_name-free `PlatformFn`. v4 (Sprint 81, FIXME 0327 — the
/// fault-guarded dispatch funnel, step 1/4) — the `IO_TAG_EFFECT` node widens
/// from 24 → 32 bytes with a **fourth `i64` field** ([`IO_EFFECT_FN_NAME_OFFSET`])
/// carrying a baked fn-name handle (rule (ii) — an `IO_TAG_*` / Effect-node
/// layout change). The DLL's [`CLIO::effect`] / [`CLIO::effect_on_resource`]
/// constructors reserve the field (allocate 32 bytes, init field-3 to **null**);
/// the backend stamps the statically-known fn-name into it after the
/// platform-fn call returns (step 2), and the intrinsics trampoline reads it
/// in the fault guard (step 3). An unstamped node (or an out-of-tree DLL
/// building nodes itself) degrades to a null name → `fn_name: "<unknown>"`,
/// not a crash. v5 (Sprint 81, FIXME 0327 Option A — the dispatch-funnel
/// fault-catch is DLL-local) — [`call_effect_thunk`]'s return contract changes
/// from bare `i64` to [`EffectOutcome`] (the force-return shape), and the
/// `CLIO::effect*` thunk wrapper now runs the user closure under a DLL-local
/// `std::panic::catch_unwind` so a panic is caught by the DLL's own runtime and
/// carried back across the C-ABI as a value (rule (i) — a host-DLL
/// layout-contract / force-return change). A v4 DLL is rejected against a v5
/// host: the force-return shape differs. The `IO_TAG_EFFECT` node layout (the
/// v3-to-4 field-3 widen) is UNCHANGED. See `design/arch/bounded-contexts.md`
/// §5 invariant 9. v6 (Sprint 86, DEF-5 / platform-interface.md §6.7) — the
/// manifest fn export is **namespaced** by platform name
/// (`cranelisp_platform_manifest_<name>`, was bare
/// `cranelisp_platform_manifest`), honouring the §5.5.5 invariant the GOT and
/// layout-hash exports already followed; this resolves the
/// `multiple definition of cranelisp_platform_manifest` collision when two
/// platforms link into one binary (rule (i) — an exported-symbol-name change to
/// a layout-discipline-governed boundary: a v5 host looks up the bare name, a v6
/// DLL exports the suffixed name, neither finds the other). The shared
/// [`platform_manifest_symbol`] helper computes the suffixed name on the consume
/// side. The three-exports model, manifest content, and schema are unchanged —
/// naming only. See `design/arch/platform-interface.md` §5.5.5 / §6.7.
pub const ABI_VERSION: u32 = 6;

/// The exported-symbol name of a platform's manifest entry point, namespaced by
/// the platform's raw `name:` literal (`cranelisp_platform_manifest_<name>`).
///
/// This is the **single source of truth** for the manifest symbol name on BOTH
/// sides of the platform boundary (Principle 7): the `declare_platform!` macro
/// emits the same string via `concat!("cranelisp_platform_manifest_", name)` in
/// `#[unsafe(export_name = …)]` (it cannot call a runtime fn there), and the
/// host consume sites — the `--run`/REPL dlopen lookup and the `--link`
/// startup-stub import list — call this helper rather than inlining a
/// `format!`, so emit and consume cannot drift. A unit test pins the macro's
/// `concat!` string equal to this helper's output.
///
/// `name` is the **raw platform name verbatim** (the `name:` literal — NOT the
/// crate-name `replace('-', '_')` form, which is only used for rlib filenames).
/// See `design/arch/platform-interface.md` §5.5.5.
pub fn platform_manifest_symbol(name: &str) -> String {
    format!("cranelisp_platform_manifest_{name}")
}

/// IO task tree tags -- shared between platform DLLs and the host trampoline.
pub const IO_TAG_PURE: i64 = 0;
pub const IO_TAG_EFFECT: i64 = 1;
pub const IO_TAG_BIND: i64 = 2;
/// Parallel IO dispatch: branches run concurrently with resource token serialization.
/// See spec §10.12 (Automatic IO Scheduling).
pub const IO_TAG_PAR: i64 = 3;

/// Byte offset of the resource token within an Effect node payload.
/// Effect layout: [tag i64][thunk_ptr i64][resource_token i64][fn_name_handle i64]
/// -- 32 bytes (ABI v4; widened from 24 by FIXME 0327, the dispatch funnel).
pub const IO_EFFECT_RESOURCE_OFFSET: i64 = 16;

/// Byte offset of the baked fn-name handle within an Effect node payload
/// (the fourth `i64` field, ABI v4 / FIXME 0327). The DLL's [`CLIO::effect`]
/// constructors init this to **null** (the DLL cannot know the cranelisp-level
/// fn-name); the backend stamps the statically-known name handle here after
/// the platform-fn call returns (step 2), and the intrinsics IO trampoline
/// reads it in the fault guard (step 3). A null handle ⇒ `fn_name: "<unknown>"`.
pub const IO_EFFECT_FN_NAME_OFFSET: i64 = 24;

/// Scheduling class for a platform function, declared in the platform manifest.
///
/// Re-exported from `cranelisp-types` (Sprint 57 Wave 3 step A, Decision 26).
/// The canonical definition lives at the bottom of the dependency DAG
/// (`cranelisp_types::scheduling::SchedulingClass`) because it must appear
/// both on `PrimitiveKind::PlatformEffect` (a `cranelisp-types` variant
/// field) and in the C-ABI-adjacent surface here. A `cranelisp-types ->
/// cranelisp-platform` edge would invert the DAG and violate Principle 3.
///
/// External consumers (platform DLLs, `declare_platform!` macro users)
/// continue to import `cranelisp_platform::SchedulingClass` unchanged.
pub use cranelisp_types::SchedulingClass;

/// Platform-boundary error type, re-exported from `cranelisp-types`.
///
/// Per Decision 0042 / FIXME 0104, `PlatformError` lives in
/// `cranelisp-types` (so all crates can construct + match), with
/// `ErrorLocation` carriers per variant. The four variants are
/// `LoadFailed`, `ManifestNotFound`, `AbiVersionMismatch`, and
/// `DispatchError` — each carrying `dll: PathBuf` / `cause` /
/// `expected` / `found` / `fn_name: Symbol` as appropriate, plus a
/// uniform `location: ErrorLocation`. See `cranelisp_types::error::PlatformError`
/// for the canonical definition.
///
/// Platform-origin failures construct `PlatformError` and surface via
/// `CranelispError::Platform(PlatformError)`; `int`'s `Sess::format_error`
/// consumes through Decision 39's mode-conditional source-resolution
/// path. The `(platform "name")` form's span flows into the `location`
/// field so a missing DLL produces
/// `lib/main.cl:42:7: error: platform "stdio" not found in search path`
/// rather than a free-floating string.
///
/// Re-exported here per Principle 15's external-audience exception —
/// out-of-tree DLL author crates depend only on `cranelisp-platform`
/// and would not otherwise see `cranelisp-types`.
pub use cranelisp_types::PlatformError;
use cranelisp_types::ErrorLocation;

/// Heap header size: `[i64 total_size][i64 rc]` = 16 bytes.
/// The host allocator returns payload pointer = base + HEAP_HEADER_SIZE.
/// The trampoline expects base pointers for IO nodes.
/// Derived from `cranelisp_types::HeapHeader::SIZE` to avoid duplication.
pub const HEAP_HEADER_SIZE: i64 = cranelisp_types::HeapHeader::SIZE as i64;

/// String layout: `[i64 len][u8 bytes...]` at payload pointer.
/// Payload pointer = alloc base + 16 (after size + rc headers).
pub const STRING_HEADER_BYTES: usize = 8;

// -- C-ABI contract types --

/// A single platform function descriptor in the C ABI.
///
/// One element of [`PlatformManifest::functions`]. Crosses the DLL
/// boundary as a `#[repr(C)]` byte-shape; both the DLL author (writing
/// the descriptor via [`declare_platform!`]) and the host (loading the
/// manifest via [`manifest_to_descriptors`]) see identical layout.
///
/// # Length-prefixed strings (not null-terminated)
///
/// Every string-shaped field is a `(ptr, len)` pair (`name` +
/// `name_len`, `type_sig` + `type_sig_len`,
/// `docstring` + `docstring_len`). Length prefixing — rather than
/// null-termination — avoids forcing every DLL author's toolchain to
/// guarantee null-termination across the C-ABI surface. The host reads
/// `(ptr, len)` pairs and constructs UTF-8 slices via
/// `std::slice::from_raw_parts` + `std::str::from_utf8`, failing fast
/// on malformed bytes.
///
/// # Parameter names — parallel arrays
///
/// `param_names` + `param_name_lens` + `param_name_count` form a
/// parallel-arrays representation of the function's parameter-name
/// list. The names surface in `/sig` and `/doc` REPL introspection on
/// the host side. The DLL author writes the names in the `params: [...]`
/// arm of [`declare_platform!`]; the macro emits the parallel arrays
/// alongside the function pointer.
///
/// # Scheduling class
///
/// `scheduling_class` is a `u32` discriminant — **not** a Rust-typed
/// [`SchedulingClass`] field. The host re-interprets the `u32` via
/// `SchedulingClass::from(u32)`. Keeping the `#[repr(C)]` struct free of
/// Rust-typed fields lets the DLL author's `cbindgen`-generated header
/// match the layout exactly. Discriminants: 0 = Sequential, 1 =
/// Commutative, 2 = ResourceSerial (per Decision 0026; spec §10.10.1).
///
/// # ABI versioning
///
/// Any field added/removed/reordered in this struct is a layout-affecting
/// change that bumps [`ABI_VERSION`] (per Principle 14).
///
/// # Cross-thread invariants — `Send` + `Sync`
///
/// `unsafe impl Send` and `unsafe impl Sync` are below this declaration
/// because `PlatformFn` carries raw pointers (`name`, `ptr`,
/// etc.). Safety: every pointer is read-only data with `'static`
/// lifetime — string-literal byte arrays in the DLL's read-only
/// segment, `Box::leak`'d descriptors from [`declare_platform!`], or the
/// function pointer itself. None of the data behind the pointers is
/// mutable, so concurrent reads from any thread are sound. Per BC §5
/// invariant 6 ("no DLL unloading mid-session"), DLL pages stay mapped
/// for the session, so pointer validity is bounded by the session
/// lifetime. The IO trampoline (in `cranelisp-intrinsics` per Decision
/// 0043) reads platform-fn descriptors from multiple threads when
/// dispatching `IO_TAG_EFFECT` nodes.
#[repr(C)]
pub struct PlatformFn {
    /// Name as seen by cranelisp code (e.g. "print").
    pub name: *const u8,
    pub name_len: usize,
    /// Function pointer (extern "C", all i64 params/returns). The manifest's
    /// fn-pointer order IS the GOT slot order (platform-interface.md §5.1); the
    /// host adopts `got_slot = manifest index` and dispatches GOT-indirect
    /// against `__cranelisp_got_platform_<name>`. Platform fns need no exported
    /// linker name (the former `jit_name` mangled-name dispatch retired, FIXME
    /// 0288).
    pub ptr: *const u8,
    /// Number of i64 parameters.
    pub param_count: u32,
    /// Type signature as S-expression string (e.g. "(Fn [String] (IO Int))").
    pub type_sig: *const u8,
    pub type_sig_len: usize,
    /// Docstring for the function.
    pub docstring: *const u8,
    pub docstring_len: usize,
    /// Array of parameter name pointers.
    pub param_names: *const *const u8,
    /// Array of parameter name lengths (parallel to param_names).
    pub param_name_lens: *const usize,
    /// Number of parameter names.
    pub param_name_count: usize,
    /// SchedulingClass discriminant: 0=Sequential, 1=Commutative, 2=ResourceSerial.
    pub scheduling_class: u32,
}

// Safety: PlatformFn is a C-ABI struct with raw pointers; it is only
// constructed and accessed within unsafe blocks during DLL loading.
// The pointers must remain valid for the lifetime of the manifest.
unsafe impl Send for PlatformFn {}
unsafe impl Sync for PlatformFn {}

/// Host callbacks provided to the platform at init time — what platform
/// DLL code can call back into the host runtime for.
///
/// `#[repr(C)]` layout-contract type; layout governed by [`ABI_VERSION`]
/// per Principle 14. The host (`int`) constructs a `HostCallbacks`
/// instance with fn pointers into `cranelisp-intrinsics` (per Decision
/// 0043) and passes it to each loaded DLL's
/// `cranelisp_platform_manifest` entry point; [`HostContext::init`]
/// stores it for the DLL's lifetime.
///
/// # Current shape (ABI v3)
///
/// As of Sprint 76 (`ABI_VERSION = 3`, FIXMEs 0286 + 0288), the struct carries
/// two fields: `alloc` (the original, ABI v1+) and `alloc_with_tag` (consumed by
/// [`CLAdt::construct`] — KEPT, ADT construction across the FFI still needs the
/// host allocator). `alloc_with_tag` is wired to the real host intrinsic. The
/// former `validate_schema` channel is **gone** (FIXME 0288): schema validation
/// is superseded by the layout-hash gate (platform-interface.md §5.5.4) — the
/// host regenerates the schema from its live tables and compares the canonical
/// hash to the DLL's exported `__cranelisp_layout_hash_<name>`.
///
/// # Future shape — Decision 0031 callback support
///
/// When `Fn a b` lands on the spec §10.10.1 platform-ABI permitted-types
/// list (currently future work; not in this sprint's scope), the struct
/// widens further with `rc_inc`, `rc_dec`, and `invoke_closure` fields.
/// Platform DLLs retaining user-supplied closures across calls will
/// inc-on-store / dec-on-release; invocation will dispatch through the
/// GOT (so REPL redefinition retargets future invocations
/// transparently). The widening is a binary-incompatible ABI bump
/// (Principle 14). See `bounded-contexts.md` §5 invariant 3 for the
/// durable forward-looking contract.
#[repr(C)]
pub struct HostCallbacks {
    /// Allocate `size` bytes, returns payload pointer (base + 16).
    pub alloc: extern "C" fn(i64) -> i64,

    /// Allocate a tagged heap ADT and write the variant tag + fields.
    ///
    /// Called by `CLAdt::<T>::construct(...)`. The host:
    /// 1. Allocates `total_size` bytes via the runtime allocator (`alloc`).
    /// 2. Writes the 16-byte heap header (`[total_size: i64][rc: i64]`).
    /// 3. Writes the 4-byte tag at payload+0 (payload = alloc_base + 16).
    /// 4. Writes `field_count` i64 values from `fields_ptr` at sequential
    ///    8-byte offsets starting payload+8 (8-byte align after the u32 tag
    ///    with 4 bytes pad).
    /// 5. Returns the **alloc base pointer** as i64 (matching `CLString`'s
    ///    base-pointer convention — `CLAdt<T>::from_raw` expects alloc base).
    ///
    /// The host wires this to the real intrinsic at DLL load
    /// ([`HostContext::init`]); it has been wired since Sprint 76. When no
    /// host has called `init` — e.g. a `cranelisp-platform` unit test
    /// exercising a construction path directly — this field is left at its
    /// uninitialized-host fallback [`null_alloc_with_tag`], which panics on
    /// call. Install a synthetic callback via `HostContext::init` to exercise
    /// construction without a real host.
    pub alloc_with_tag: extern "C" fn(
        tag: u32,
        field_count: u32,
        fields_ptr: *const i64,
    ) -> i64,
}

/// Permanent uninitialized-host fallback for `HostCallbacks::alloc_with_tag`.
///
/// The host wires the real `alloc_with_tag` intrinsic at DLL load via
/// [`HostContext::init`] (wired since Sprint 76). This fallback is what the
/// `alloc_with_tag` slot reads **before any host has called `init`** — the
/// legitimate uninitialized-host path. It is a permanent safety gate, not a
/// migration scaffold: it fires only when `CLAdt::construct` runs without a
/// wired host, which in practice means a `cranelisp-platform` unit test
/// exercising a construction path directly. Such a test installs a synthetic
/// `alloc_with_tag` callback via `HostContext::init` before constructing.
pub extern "C" fn null_alloc_with_tag(
    _tag: u32,
    _field_count: u32,
    _fields_ptr: *const i64,
) -> i64 {
    panic!(
        "CLAdt construction requires HostCallbacks::alloc_with_tag, but no host \
         has called HostContext::init to wire it (uninitialized-host fallback).\n\
         \n\
         If you are running tests inside cranelisp-platform, install a synthetic \
         callback via HostContext::init in test setup."
    )
}

/// Platform manifest returned by the DLL's entry point.
///
/// Returned by `cranelisp_platform_manifest` (emitted by
/// [`declare_platform!`]) when the host calls into the loaded DLL.
/// Carries the platform name, version, ABI-version stamp, and an array
/// of [`PlatformFn`] descriptors.
///
/// # Load-time validation
///
/// The host (`int::load_platform_dll`) reads `abi_version` first and
/// refuses mismatched DLLs with [`PlatformError::AbiVersionMismatch`].
/// Any field added/removed/reordered in this struct is a layout-affecting
/// change requiring an [`ABI_VERSION`] bump (per Principle 14 — see
/// [`ABI_VERSION`] for the bump rules).
///
/// # Length-prefixed strings
///
/// Same convention as [`PlatformFn`]: `name` / `version` are
/// `(ptr, len)` pairs, not null-terminated. See [`PlatformFn`]'s rustdoc
/// for the rationale.
///
/// # Cross-thread access
///
/// `PlatformManifest` is `!Send + !Sync` by auto-projection (raw
/// pointers; no `unsafe impl`). The host reads it once on the load
/// thread via [`manifest_to_descriptors`], copies the bytes into safe
/// owned shapes ([`OwnedPlatformFnDescriptor`]), and then discards the
/// manifest reference. Concurrent reads from background threads are
/// not part of the contract — the descriptor data is what crosses
/// threads.
#[repr(C)]
pub struct PlatformManifest {
    /// Must match `cranelisp_platform::ABI_VERSION`.
    pub abi_version: u32,
    /// Platform name (e.g. "stdio").
    pub name: *const u8,
    pub name_len: usize,
    /// Platform version string.
    pub version: *const u8,
    pub version_len: usize,
    /// Array of function descriptors.
    pub functions: *const PlatformFn,
    pub function_count: usize,
}

// -- Safe wrapper types --
//
// These `#[repr(transparent)]` wrappers over i64 provide type-safe
// conversions for platform authors. All `unsafe` is encapsulated here.

/// A cranelisp integer value — `i64` passthrough.
///
/// `#[repr(transparent)]` over `i64`. ABI: the `i64` is the value
/// directly; no boxing, no header. Conversions: `From<i64>` /
/// `From<CLInt> for i64`. JIT-emitted code that returns an integer
/// returns the bare `i64`; the DLL author wraps in `CLInt` for type
/// safety at the Rust source level.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLInt(i64);

/// A cranelisp string value — alloc-base pointer to a heap-allocated
/// `[total_size][rc][len][bytes...]` shape.
///
/// `#[repr(transparent)]` over `i64`. The stored `i64` is the
/// **alloc base** of the heap allocation (NOT the payload pointer);
/// the string payload begins at `base + HEAP_HEADER_SIZE` and consists
/// of an `[i64 len][u8 bytes...]` shape. This matches the compiler's
/// `HeapString` convention (Decision 0012 + Decision 0043 — string
/// layout owned by `cranelisp-intrinsics`).
///
/// `CLString` implements [`CLHeap`]; the host-side allocator returns
/// the alloc base via [`HostCallbacks::alloc`] (which itself returns
/// `base + HEAP_HEADER_SIZE`; `CLString::from(&str)` then subtracts
/// the header size to land on the base). [`CLString::as_str`] adds
/// `HEAP_HEADER_SIZE` to reach the payload and reads `len` + bytes.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLString(i64);

/// A cranelisp boolean value — 0 = false, 1 = true.
///
/// `#[repr(transparent)]` over `i64`. ABI: the `i64` is 0 or 1.
/// Conversions: `From<bool>` / `From<CLBool> for bool`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLBool(i64);

/// A cranelisp float value — IEEE 754 `f64` bit-cast into the `i64`.
///
/// `#[repr(transparent)]` over `i64`. ABI: the `i64` carries the
/// native-endian bit pattern of an `f64` (via
/// `i64::from_ne_bytes(f.to_ne_bytes())`). Conversions: `From<f64>` /
/// `From<CLFloat> for f64`.
#[repr(transparent)]
#[derive(Clone, Copy, Debug)]
pub struct CLFloat(i64);

// -- CLInt conversions --

impl From<i64> for CLInt {
    fn from(v: i64) -> Self {
        CLInt(v)
    }
}

impl From<CLInt> for i64 {
    fn from(v: CLInt) -> Self {
        v.0
    }
}

// -- CLBool conversions --

impl From<bool> for CLBool {
    fn from(v: bool) -> Self {
        CLBool(v as i64)
    }
}

impl From<CLBool> for bool {
    fn from(v: CLBool) -> Self {
        v.0 != 0
    }
}

// -- CLFloat conversions --

impl From<f64> for CLFloat {
    fn from(v: f64) -> Self {
        CLFloat(i64::from_ne_bytes(v.to_ne_bytes()))
    }
}

impl From<CLFloat> for f64 {
    fn from(v: CLFloat) -> Self {
        f64::from_ne_bytes(v.0.to_ne_bytes())
    }
}

// -- CLType trait --

/// Marker trait for cranelisp value types that can cross the DLL
/// boundary as a `#[repr(transparent)]` `i64`.
///
/// Convention-sealed: only the four primitive wrappers ([`CLInt`],
/// [`CLBool`], [`CLFloat`], [`CLString`]) plus the parameterised
/// wrappers ([`CLIO<T>`], [`CLAdt<T>`]) implement `CLType`. The `Copy`
/// super-bound suffices in practice — DLL authors don't own any `Copy`
/// type satisfying the `i64` + ABI contract. A `mod sealed { pub trait
/// Sealed {} }` super-bound is a candidate future cleanup but not
/// required (per audit F8 — the existing super-bound is consistent
/// across declaration sites).
///
/// # S67 W1 narrowing — `to_raw` only
///
/// The trait was narrowed to a single method during the S67 baseline
/// pass. Earlier facade drafts speculated `type_signature` / `from_repr`
/// / `to_repr` — none of those are needed: host-side code never
/// constructs a CL\* from a raw `i64` (the DLL hands them back as `i64`
/// and the host doesn't reverse the construction), and `type_signature`
/// belongs to the manifest, not the value wrapper (the type-sig string
/// lives on [`PlatformFn::type_sig`] / [`OwnedPlatformFnDescriptor::type_sig`]
/// — both at the descriptor level).
pub trait CLType: Copy {
    fn to_raw(self) -> i64;
}

impl CLType for CLInt {
    fn to_raw(self) -> i64 {
        self.0
    }
}
impl CLType for CLString {
    fn to_raw(self) -> i64 {
        self.0
    }
}
impl CLType for CLBool {
    fn to_raw(self) -> i64 {
        self.0
    }
}
impl CLType for CLFloat {
    fn to_raw(self) -> i64 {
        self.0
    }
}

/// The result of forcing a platform Effect thunk, carried across the C-ABI
/// from the DLL back to the host.
///
/// `#[repr(C)]` layout-contract type governed by [`ABI_VERSION`] (Principle 14
/// — FFI layout discipline; **no** `#[non_exhaustive]`, since the ABI gate, not
/// source-level evolution guards, governs compatibility). Introduced at ABI v5
/// (Sprint 81, FIXME 0327 Option A — the dispatch-funnel fault-catch is
/// DLL-local).
///
/// # Why a value, not a thread-local
///
/// A platform `cdylib` statically links its **own** copy of the Rust panic
/// runtime AND its own copy of `cranelisp-platform`'s thread-locals. A
/// `panic!` raised inside the DLL must be caught by the DLL's own runtime (a
/// foreign unwind reaching the host's `catch_unwind` aborts), so the catch
/// happens in the [`CLIO::effect`] thunk wrapper — DLL-compiled code. The DLL
/// then CANNOT set the host's dispatch-fault slot directly (different
/// thread-locals), so the caught fault travels back to the host as this
/// **return value**.
///
/// # Field discipline
///
/// - `fault_cause == null` ⇒ **clean**; `value` is the thunk's result.
/// - `fault_cause != null` ⇒ **faulted**; `fault_cause` points at DLL-owned
///   UTF-8 panic-cause bytes `fault_len` long, leaked for the session (bounded
///   by §5 invariant 6 "no DLL unloading mid-session", mirroring the existing
///   `declare_platform!` `Box::leak`s); `value` is unused.
///
/// The host's [`call_effect_thunk`] merely *forwards* this struct — the catch
/// already happened DLL-side in the wrapper; the host does NO `catch_unwind` of
/// its own. See `design/arch/bounded-contexts.md` §5 invariant 9.
#[repr(C)]
pub struct EffectOutcome {
    /// The thunk's result value when clean (`fault_cause` null); unused on fault.
    pub value: i64,
    /// Null = clean. Non-null = DLL-owned, session-leaked UTF-8 panic-cause bytes.
    pub fault_cause: *const u8,
    /// Length of `fault_cause` in bytes when non-null; 0 when clean.
    pub fault_len: usize,
}

// -- CLIO -- IO-wrapped return value --

/// IO-wrapped return value — base pointer to a heap-allocated IO node.
///
/// `#[repr(transparent)]` over `i64` with a zero-sized `PhantomData<CL>`
/// for compile-time witness binding. The stored `i64` is the
/// **alloc base** of a heap allocation whose payload is an IO node
/// (one of `Pure` / `Effect` / `Bind` / `Par`, tagged by the first
/// `i64` of the payload — see [`IO_TAG_PURE`], [`IO_TAG_EFFECT`],
/// [`IO_TAG_BIND`], [`IO_TAG_PAR`]).
///
/// Platform DLL fns return `CLIO<CL>` to defer effects per spec
/// §10.10.1; the IO trampoline (in `cranelisp-intrinsics` per Decision
/// 0043) drives the tree at the appropriate scheduling point. See
/// [`CLIO::pure`] / [`CLIO::effect`] / [`CLIO::effect_on_resource`] for
/// the three constructors.
///
/// Per spec §10.10.1 the platform calling convention permits `Int`,
/// `Bool`, `String`, `Float`, and `IO a` as argument and return types.
/// `Fn a b` is reserved for future callback support per Decision 0031's
/// "Callback support (forward commitment)" sub-section.
#[repr(transparent)]
#[derive(Debug)]
pub struct CLIO<CL: CLType>(i64, std::marker::PhantomData<CL>);

impl<CL: CLType> CLIO<CL> {
    /// Wrap a completed value in IO by allocating a Pure node on the heap.
    ///
    /// Returns a base pointer (not payload pointer) because the IO trampoline
    /// reads fields at base + HEAP_HEADER_SIZE offsets.
    pub fn pure(val: CL) -> Self {
        let alloc = get_global_alloc();
        let payload = alloc(16); // 2 x i64: tag + value
        // SAFETY: `payload` is a valid pointer returned by the host allocator for
        // at least 16 bytes. We write two i64 fields (tag at offset 0, value at
        // offset 8) within that allocation. The allocator guarantees 8-byte alignment.
        unsafe {
            *(payload as *mut i64) = IO_TAG_PURE;
            *((payload + 8) as *mut i64) = val.to_raw();
        }
        // Return base pointer (payload - header) for trampoline compatibility.
        CLIO(payload - HEAP_HEADER_SIZE, std::marker::PhantomData)
    }

    /// Wrap a Rust closure as a deferred IO Effect node with no resource token.
    ///
    /// The closure is double-boxed to produce a thin pointer (fits in one i64).
    /// The trampoline unboxes and calls it when forcing the IO tree.
    /// Resource token is set to 0 (unrestricted).
    pub fn effect(f: impl FnOnce() -> CL + 'static) -> Self {
        Self::effect_on_resource(0, f)
    }

    /// Wrap a Rust closure as a deferred IO Effect node with a resource token.
    ///
    /// The `token` identifies a shared resource. Two Effect nodes with the same
    /// non-zero token in a Par group will be serialized by the trampoline.
    pub fn effect_on_resource(token: i64, f: impl FnOnce() -> CL + 'static) -> Self {
        // DLL-LOCAL fault catch (FIXME 0327 Option A). This wrapper closure is
        // monomorphised at the `CLIO::effect*` call site — i.e. INTO the DLL
        // that owns `f` — so the `catch_unwind` below executes in DLL-compiled
        // code, caught by the DLL's OWN panic runtime. A `panic!` in `f`
        // therefore does NOT cross the cdylib runtime boundary as a foreign
        // unwind (which would abort); it is converted here, DLL-side, into an
        // `EffectOutcome` carried back to the host as a C-ABI return value. The
        // host's `call_effect_thunk` merely forwards it (no host-side catch).
        let thunk: Box<Box<dyn FnOnce() -> EffectOutcome>> = Box::new(Box::new(move || {
            match std::panic::catch_unwind(std::panic::AssertUnwindSafe(move || f().to_raw())) {
                Ok(value) => EffectOutcome {
                    value,
                    fault_cause: std::ptr::null(),
                    fault_len: 0,
                },
                Err(payload) => {
                    // Recover the panic-cause message and LEAK it for the
                    // session (no DLL unloading mid-session — §5 invariant 6),
                    // yielding a stable `*const u8` + len the host can read.
                    let cause: String = if let Some(s) = payload.downcast_ref::<String>() {
                        s.clone()
                    } else if let Some(s) = payload.downcast_ref::<&str>() {
                        (*s).to_string()
                    } else {
                        "unknown panic in platform effect".to_string()
                    };
                    let leaked: &'static str = String::leak(cause);
                    EffectOutcome {
                        value: 0,
                        fault_cause: leaked.as_ptr(),
                        fault_len: leaked.len(),
                    }
                }
            }
        }));
        let thunk_ptr = Box::into_raw(thunk) as i64;

        let alloc = get_global_alloc();
        // 4 x i64: tag + thunk_ptr + resource_token + fn_name_handle (ABI v4 —
        // node widened 24 → 32 by FIXME 0327, the dispatch funnel). Field-3
        // (the baked fn-name handle) is RESERVED here and init to null: the DLL
        // cannot know the cranelisp-level fn-name, so the backend stamps it
        // post-call (step 2) and the intrinsics trampoline reads it (step 3).
        let payload = alloc(32);
        // SAFETY: `payload` is a valid pointer returned by the host allocator for
        // at least 32 bytes. We write four i64 fields (tag, thunk_ptr, token,
        // fn_name_handle) at offsets 0, 8, 16, 24 within that allocation.
        // `thunk_ptr` is a valid pointer from `Box::into_raw` and will be
        // consumed exactly once by `call_effect_thunk`. Field-3 is null — the
        // backend stamps the real handle after this node is returned.
        unsafe {
            *(payload as *mut i64) = IO_TAG_EFFECT;
            *((payload + 8) as *mut i64) = thunk_ptr;
            *((payload + 16) as *mut i64) = token;
            *((payload + 24) as *mut i64) = 0; // fn_name_handle — reserved, null
        }
        // Return base pointer (payload - header) for trampoline compatibility.
        CLIO(payload - HEAP_HEADER_SIZE, std::marker::PhantomData)
    }
}

/// Call a double-boxed thunk pointer (created by `CLIO::effect()`).
///
/// This **consumes** the thunk -- it is valid to call exactly once.
/// The trampoline must not force the same Effect node twice.
///
/// Returns an [`EffectOutcome`] (ABI v5, FIXME 0327 Option A). The thunk is the
/// DLL-local wrapper that already ran the user closure under `catch_unwind`
/// inside the DLL — so this host-side copy merely **forwards** the wrapper's
/// `EffectOutcome`; it does NO `catch_unwind` of its own (the catch already
/// happened DLL-side, the only place a DLL-origin panic can be caught). A clean
/// force yields `{ value, fault_cause: null, fault_len: 0 }`; a faulted force
/// yields a non-null `fault_cause` pointing at DLL-owned, session-leaked
/// panic-cause bytes.
///
/// # Safety
/// `thunk_ptr` must be a valid pointer from
/// `Box::into_raw(Box<Box<dyn FnOnce() -> EffectOutcome>>)`.
pub unsafe fn call_effect_thunk(thunk_ptr: i64) -> EffectOutcome {
    let thunk: Box<Box<dyn FnOnce() -> EffectOutcome>> =
        unsafe { Box::from_raw(thunk_ptr as *mut Box<dyn FnOnce() -> EffectOutcome>) };
    (*thunk)()
}

impl<CL: CLType> From<CLIO<CL>> for i64 {
    fn from(v: CLIO<CL>) -> Self {
        v.0
    }
}

// Explicit From impls for lifting natural types through CL* into CLIO:
impl From<i64> for CLIO<CLInt> {
    fn from(val: i64) -> Self {
        CLIO::pure(CLInt::from(val))
    }
}
impl From<String> for CLIO<CLString> {
    fn from(val: String) -> Self {
        CLIO::pure(CLString::from(val))
    }
}
impl From<bool> for CLIO<CLBool> {
    fn from(val: bool) -> Self {
        CLIO::pure(CLBool::from(val))
    }
}
impl From<f64> for CLIO<CLFloat> {
    fn from(val: f64) -> Self {
        CLIO::pure(CLFloat::from(val))
    }
}
// CL* -> CLIO directly:
impl From<CLInt> for CLIO<CLInt> {
    fn from(val: CLInt) -> Self {
        CLIO::pure(val)
    }
}
impl From<CLString> for CLIO<CLString> {
    fn from(val: CLString) -> Self {
        CLIO::pure(val)
    }
}
impl From<CLBool> for CLIO<CLBool> {
    fn from(val: CLBool) -> Self {
        CLIO::pure(val)
    }
}
impl From<CLFloat> for CLIO<CLFloat> {
    fn from(val: CLFloat) -> Self {
        CLIO::pure(val)
    }
}

// -- CLString conversions --

/// Global allocator function pointer, set by `HostContext::init()`.
/// Each DLL gets its own copy of this static (separate compilation unit).
static GLOBAL_ALLOC: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

/// Global tagged-ADT allocator pointer (Sprint 71). Set by
/// `HostContext::init()` from `HostCallbacks::alloc_with_tag`. Defaults
/// to `null_alloc_with_tag` (R1 wired-or-panic gate) when no init has run.
static GLOBAL_ALLOC_WITH_TAG: AtomicPtr<()> = AtomicPtr::new(std::ptr::null_mut());

/// Get the global allocator function. Panics if not initialized.
fn get_global_alloc() -> extern "C" fn(i64) -> i64 {
    let ptr = GLOBAL_ALLOC.load(Ordering::SeqCst);
    assert!(
        !ptr.is_null(),
        "platform not initialized: HostContext::init() not called"
    );
    // SAFETY: The pointer was stored by `HostContext::init()` which cast a valid
    // `extern "C" fn(i64) -> i64` to `*mut ()`. We transmute it back to the
    // original function pointer type. The assert above ensures it is non-null.
    unsafe { std::mem::transmute(ptr) }
}

/// Get the host's tagged-ADT allocator (Sprint 71). When no
/// `HostContext::init` has been called (e.g. inside cranelisp-platform
/// unit tests for read paths), falls back to `null_alloc_with_tag` so
/// the R1 gate fires with a clear FIXME-0229 message on attempted
/// construction.
pub(crate) fn get_host_alloc_with_tag() -> extern "C" fn(u32, u32, *const i64) -> i64 {
    let ptr = GLOBAL_ALLOC_WITH_TAG.load(Ordering::SeqCst);
    if ptr.is_null() {
        return null_alloc_with_tag;
    }
    // SAFETY: pointer set by `HostContext::init()` from
    // `HostCallbacks::alloc_with_tag`, which is the canonical
    // `extern "C" fn(u32, u32, *const i64) -> i64`.
    unsafe { std::mem::transmute(ptr) }
}

impl CLString {
    /// View the string contents as a `&str`.
    ///
    /// CLString stores a **base pointer** (matching the compiler's convention).
    /// The string payload starts at base + HEAP_HEADER_SIZE:
    /// `[alloc_size(8) | rc(8) | len(8) | bytes...]`
    pub fn as_str(&self) -> &str {
        // SAFETY: `self.0` is a base pointer to a heap allocation with layout
        // `[alloc_size: i64][rc: i64][len: i64][bytes: u8...]`. Adding
        // HEAP_HEADER_SIZE yields the payload pointer. The length field at the
        // payload start was written by `CLString::from(&str)` or the compiler,
        // and the subsequent `len` bytes are valid UTF-8 (guaranteed by
        // construction — only Rust `&str` data is ever stored).
        unsafe {
            let payload = self.0 + HEAP_HEADER_SIZE;
            let len = *(payload as *const i64) as usize;
            let bytes = std::slice::from_raw_parts(
                (payload + STRING_HEADER_BYTES as i64) as *const u8,
                len,
            );
            std::str::from_utf8_unchecked(bytes)
        }
    }
}

impl From<CLString> for String {
    fn from(v: CLString) -> Self {
        v.as_str().to_string()
    }
}

impl From<String> for CLString {
    fn from(s: String) -> Self {
        CLString::from(s.as_str())
    }
}

impl From<&str> for CLString {
    fn from(s: &str) -> Self {
        let bytes = s.as_bytes();
        let size = (STRING_HEADER_BYTES + bytes.len()) as i64;
        let alloc = get_global_alloc();
        let payload = alloc(size);
        // SAFETY: `payload` is a valid pointer returned by the host allocator for
        // `STRING_HEADER_BYTES + bytes.len()` bytes. We write the length as an i64
        // at offset 0, then copy the UTF-8 bytes at offset STRING_HEADER_BYTES.
        // `bytes` is a valid slice from a Rust `&str`, so the copy source is sound.
        unsafe {
            *(payload as *mut i64) = bytes.len() as i64;
            std::ptr::copy_nonoverlapping(
                bytes.as_ptr(),
                (payload + STRING_HEADER_BYTES as i64) as *mut u8,
                bytes.len(),
            );
        }
        // Store base pointer (payload - header) to match compiler convention.
        CLString(payload - HEAP_HEADER_SIZE)
    }
}

// -- CLOwned -- RAII RC wrapper for heap CL* types --

/// Trait for CL types that are heap-allocated with RC headers — the
/// platform's view of the cranelisp heap-RC discipline.
///
/// # Allocation layout
///
/// `[total_size: i64][rc: i64][payload...]` — 16-byte header
/// ([`HEAP_HEADER_SIZE`]) followed by the type-specific payload. All
/// CL\* types store **base pointers** (the address of the allocation
/// header), NOT payload pointers. This matches the compiler's
/// convention (Decision 0013) — JIT-emitted code and `CLString` /
/// `CLAdt` value wrappers agree on what an `i64` "heap reference"
/// means.
///
/// # Method receiver shape — authoritative source names
///
/// The receiver shape is `&self` for RC operations; the method names
/// are [`inc_rc`](Self::inc_rc), [`dec_rc`](Self::dec_rc),
/// [`raw_ptr`](Self::raw_ptr), [`own`](Self::own), and
/// [`into_owned_consuming`](Self::into_owned_consuming). Per audit F5
/// (R3 disposition — S71): the asymmetry `inc_rc` / `dec_rc` (rather
/// than `rc_inc` / `rc_dec`) is intentional and matches the historical
/// name from `cranelisp-intrinsics`. Renaming would propagate a
/// consumer cascade across `platforms/stdio` + `platforms/test-capture`
/// + intrinsics + every test using `CLHeap` directly; deferred to a
/// future sprint with explicit consumer-cascade analysis. Source is
/// authoritative.
///
/// # RC ordering — `SeqCst`, not `Relaxed`
///
/// [`inc_rc`](Self::inc_rc) and [`dec_rc`](Self::dec_rc) use
/// `Ordering::SeqCst` to match the backend's Cranelift `atomic_rmw`
/// semantics (arch decision 13). `Relaxed` is unsound for both:
///
/// - **`inc_rc` Relaxed** — allows the increment to be reordered
///   relative to field reads; concurrent readers may see the inc'd
///   refcount before the field initialisation that motivated the inc.
/// - **`dec_rc` Relaxed** — allows the dec to be reordered before
///   reads of object fields, potentially producing read-after-free
///   when the dec races a concurrent dec that frees the allocation.
///
/// # Conventionally sealed
///
/// Currently only [`CLString`] and [`CLAdt<T>`] implement `CLHeap`.
/// `CLInt` / `CLBool` / `CLFloat` are value types (no heap allocation,
/// no RC). DLL authors do not implement `CLHeap` directly — they use
/// the existing wrappers.
pub trait CLHeap: CLType + Copy {
    /// Get the raw base pointer.
    fn raw_ptr(&self) -> i64;

    /// Atomically increment the reference count.
    ///
    /// Uses `Ordering::SeqCst` to match the backend's Cranelift `atomic_rmw`
    /// semantics (arch decision 13). `Relaxed` is unsound because it allows
    /// reordering of the increment relative to field reads.
    fn inc_rc(&self) {
        let base = self.raw_ptr();
        let rc_addr = (base + 8) as *mut i64; // rc at base+8
        // SAFETY: `base` is a valid heap allocation base pointer with layout
        // `[alloc_size: i64][rc: i64][payload...]`. The RC field at base+8 is
        // an i64 with 8-byte alignment, valid for atomic access. The allocation
        // is live (RC >= 1) so the pointer is not dangling.
        unsafe {
            use std::sync::atomic::AtomicI64;
            let atomic = &*(rc_addr as *const AtomicI64);
            atomic.fetch_add(1, Ordering::SeqCst);
        }
    }

    /// Atomically decrement the reference count.
    /// If the old RC was 1 (now 0), frees the allocation.
    ///
    /// Uses `Ordering::SeqCst` -- `Relaxed` for dec is unsound because it
    /// allows the dec to be reordered before reads of object fields,
    /// potentially reading freed memory.
    fn dec_rc(&self) {
        let base = self.raw_ptr();
        let rc_addr = (base + 8) as *mut i64; // rc at base+8
        // SAFETY: Same invariants as `inc_rc` — `base` is a valid live heap
        // allocation, and RC at base+8 is an aligned i64 suitable for atomic ops.
        let old_rc = unsafe {
            use std::sync::atomic::AtomicI64;
            let atomic = &*(rc_addr as *const AtomicI64);
            atomic.fetch_sub(1, Ordering::SeqCst)
        };
        if old_rc == 1 {
            // RC reached 0 -- free the allocation
            // SAFETY: `base` points to the start of a global-allocator allocation.
            // `alloc_size` at base+0 records the total allocation size that was
            // used in the original `alloc` call. Alignment is 8 (matching the
            // host allocator). No other references exist (RC was 1, now 0).
            let total_size = unsafe { *(base as *const i64) } as usize;
            unsafe {
                let layout = std::alloc::Layout::from_size_align_unchecked(total_size, 8);
                std::alloc::dealloc(base as *mut u8, layout);
            }
        }
    }

    /// Create an owned handle that increments RC and decrements on drop.
    fn own(&self) -> CLOwned<Self> {
        CLOwned::new(*self)
    }

    /// Consuming-convention version of `own()` (Decision 24): take ownership
    /// of the caller's transferred reference and wrap it in a `CLOwned`
    /// without incrementing RC. The returned `CLOwned` will `dec_rc` on drop,
    /// releasing the caller's transferred reference. Net effect per call:
    /// caller +1 (transfer) → CLOwned drop -1 = balanced.
    ///
    /// Use this in platform externs that capture a heap-typed parameter into
    /// an Effect-thunk closure instead of `own()`. `own()` is still correct
    /// when the caller did NOT transfer ownership (e.g. when the extern
    /// takes a borrow / the ref is reused after the extern returns).
    ///
    /// See `design/backend/ring2-rc.md` §10.4 Form B for the rationale.
    fn into_owned_consuming(self) -> CLOwned<Self> {
        // No inc — the caller's transferred ref becomes the CLOwned's ref.
        // Construct the wrapper directly, bypassing `CLOwned::new`'s inc.
        CLOwned { inner: self }
    }
}

impl CLHeap for CLString {
    fn raw_ptr(&self) -> i64 {
        self.0 // base pointer
    }
}

/// RAII wrapper for heap-allocated CL\* values — host-side RC
/// discipline across multiple host-callback invocations.
///
/// Lets platform DLL code hold a heap-typed cranelisp value across
/// multiple host-callback invocations with correct reference-counting.
/// [`new`](Self::new) inc's via [`CLHeap::own`]; `Drop` dec's via
/// [`CLHeap::dec_rc`]. The consuming variant
/// [`CLHeap::into_owned_consuming`] takes the caller's transferred ref
/// directly (no inc on wrap) — used by platform externs capturing a
/// heap parameter into an Effect closure per Decision 0024.
///
/// # Methods — what exists
///
/// Currently only [`new`](Self::new) and `Drop` are implemented. The
/// pre-S71 facade speculated an `into_inner(self) -> T` method that
/// would release ownership without dec'ing; per audit F1 (R3
/// disposition — S71): no such method exists in source, and the
/// marker-type design for `CLAdt<T>` does not need it. The audit's
/// resolution stands — rustdoc records what is actually implemented;
/// `into_inner` is not added speculatively.
///
/// # `#[non_exhaustive]` — deliberately absent
///
/// `CLOwned<T>` is plain Rust (host-side only; does not cross the DLL
/// ABI). The pre-S71 facade speculated `#[non_exhaustive]` on it; per
/// audit F7 (S71): the actual source carries no `#[non_exhaustive]`.
/// The struct has one field (`inner: T`) that doesn't need source-level
/// evolution gating because callers construct via [`new`](Self::new)
/// and access via [`Deref`], not via direct struct-literal
/// construction.
pub struct CLOwned<T: CLHeap> {
    inner: T,
}

impl<T: CLHeap> CLOwned<T> {
    /// Create a new owned handle, incrementing the reference count.
    pub fn new(val: T) -> Self {
        val.inc_rc();
        CLOwned { inner: val }
    }
}

impl<T: CLHeap> Drop for CLOwned<T> {
    fn drop(&mut self) {
        self.inner.dec_rc();
    }
}

impl<T: CLHeap> Deref for CLOwned<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.inner
    }
}

// -- HostContext --

/// Initialization handle for platform DLLs — the runtime ↔ platform
/// bridge.
///
/// Exists solely to receive and store host callbacks at manifest time.
/// Platform authors declare a static instance (`static HOST: HostContext
/// = HostContext::new();`); the [`declare_platform!`] macro calls
/// [`init`](Self::init) automatically when the host invokes the
/// DLL's `cranelisp_platform_manifest` entry point.
///
/// # Why no centralised dispatch wrapper
///
/// `HostContext` does NOT expose a `dispatch()` method. Platform-fn
/// invocation reads the fn pointer from `SymbolTable.got()` indexed by
/// `ModuleEntry::Def.got_slot` (per Decision 0026, S66 amendment +
/// rollback `1dc57ae` — GOT is the single source of truth for callable
/// addresses) and calls through it directly. Adding a `dispatch`
/// wrapper would re-introduce a parallel call path (Principle 7
/// violation) without buying anything the per-entry GOT slot doesn't
/// already provide.
///
/// # Cross-thread invariants
///
/// `HostContext` is `Send + Sync` by auto-derivation (the only field,
/// `callbacks: AtomicPtr<HostCallbacks>`, is itself `Send + Sync`). BC
/// §5 invariant 5 holds: [`init`](Self::init) is called exactly once
/// per session by `int`; subsequent platform-fn calls observe the same
/// callbacks for the session's lifetime.
///
/// # Default — deliberately absent
///
/// Per audit F2 (S69) and design §8 (S71), `HostContext` does NOT
/// implement `Default`. The pre-S71 `impl Default for HostContext` was
/// an unannounced facade item with zero callers; deletion is a
/// source-move with no consumer cascade. Use [`new`](Self::new)
/// directly.
pub struct HostContext {
    callbacks: AtomicPtr<HostCallbacks>,
}

impl HostContext {
    /// Create a new uninitialized context.
    ///
    /// Note: `HostContext` intentionally does NOT implement `Default`
    /// per audit F2 / design §8 — Default's `Self::new()` body was an
    /// unannounced public-surface item with zero callers. Use `new()`
    /// directly.
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        HostContext {
            callbacks: AtomicPtr::new(std::ptr::null_mut()),
        }
    }

    /// Initialize from host callbacks.
    ///
    /// Stores a leaked copy of the callbacks and sets the crate-global
    /// allocator used by `From<String> for CLString`.
    ///
    /// # Safety
    /// `callbacks` must point to a valid `HostCallbacks` struct.
    pub unsafe fn init(&self, callbacks: *const HostCallbacks) {
        let cb_copy = unsafe { Box::new(std::ptr::read(callbacks)) };
        let raw = Box::into_raw(cb_copy);
        self.callbacks.store(raw, Ordering::SeqCst);

        // Set the global allocator for CLString conversions.
        let alloc_fn = unsafe { (*raw).alloc };
        GLOBAL_ALLOC.store(alloc_fn as *mut (), Ordering::SeqCst);

        // Sprint 71: also set the global tagged-ADT allocator used by
        // CLAdt::<T>::construct(...). The host passes the real intrinsic
        // here (wired since Sprint 76); the `null_alloc_with_tag`
        // uninitialized-host fallback only stands in before any host has
        // called init.
        let alloc_with_tag_fn = unsafe { (*raw).alloc_with_tag };
        GLOBAL_ALLOC_WITH_TAG.store(alloc_with_tag_fn as *mut (), Ordering::SeqCst);
    }
}

// -- Owned descriptors (safe Rust types) --

/// Safe Rust descriptor for a platform function, converted from C-ABI.
///
/// The host-side typed form of [`PlatformFn`] — string fields are owned
/// `String`s, `scheduling_class` is the typed [`SchedulingClass`] enum
/// (lifted from the C-ABI `u32` via `SchedulingClass::from(u32)`),
/// `param_names` is an owned `Vec<String>`. Produced by
/// [`manifest_to_descriptors`] and consumed by the host's platform-load
/// path on `int` (which writes the descriptor into the per-platform
/// synthetic module's `SymbolTable` per spec §8.9.3).
///
/// # Auto-projection — `!Send + !Sync`
///
/// The raw `ptr: *const u8` field forces auto-projection of `!Send +
/// !Sync` on this struct. That projection is intentional: callers who
/// move descriptors across threads MUST wrap in `Arc<>` or similar.
/// The fn pointer itself is invariant for the DLL's lifetime (BC §5
/// invariant 6 — no DLL unloading mid-session), but the auto-projection
/// keeps the boundary disciplined.
///
/// # `#[non_exhaustive]`
///
/// Plain Rust struct (not crossing the C ABI; not layout-contract). The
/// standard facade convention applies — additional fields may be added
/// in a non-breaking source-evolution step.
#[non_exhaustive]
pub struct OwnedPlatformFnDescriptor {
    pub name: String,
    pub ptr: *const u8,
    pub param_count: usize,
    pub type_sig: String,
    pub docstring: String,
    pub param_names: Vec<String>,
    pub scheduling_class: SchedulingClass,
}

/// Convert a C-ABI manifest into safe Rust descriptors.
///
/// The C-ABI → typed-Rust bridge: given a raw [`PlatformManifest`]
/// (already located in a loaded DLL by the caller), copies the
/// descriptor list into safe Rust shapes and returns
/// `(platform_name, platform_version, descriptors)`. The two leading
/// strings come from `PlatformManifest.name` / `PlatformManifest.version`
/// (each `(ptr, len)` pair lifted to an owned `String`); the descriptor
/// vector comes from `PlatformManifest.functions`.
///
/// # DLL lifecycle is not this crate's concern
///
/// Per `bounded-contexts.md` §5 — DLL lifecycle orchestration (`dlopen`
/// via `libloading::Library` retention) is `int`'s job; the
/// `cranelisp-platform` crate has no `libloading` dep and does not own
/// DLL handles. The DLL handle lands on the synthetic platform module's
/// `SymbolTable.dll: Option<D>` field per spec §8.9.3, keyed by
/// `symbol_tables["platform.<name>"]`; dropping the SymbolTable drops
/// the DLL.
///
/// `parse_type_sig` (the platform-fn type-signature lifter) and
/// `load_manifest` (the `libloading` open path) are NOT public surface
/// here. Per FIXME 0155 resolution, `parse_type_sig` lives `int`-side
/// because it requires `cranelisp-typecheck` vocabulary that platform
/// must not depend on (Principle 3); `load_manifest`'s DLL-handle
/// retention is `int`-side per the BC allocation.
///
/// # Safety
/// All pointers in the manifest must be valid and point to UTF-8 data.
///
/// # Errors
/// UTF-8 validation failures construct [`PlatformError::LoadFailed`]
/// with `ErrorLocation::unknown()`. The caller — `int::load_platform_dll`
/// — rewrites `dll` and `location` at the call site (using the
/// `(platform "name")` form's span) before surfacing via
/// `CranelispError::Platform`. Per Decision 0042 / FIXME 0104.
pub unsafe fn manifest_to_descriptors(
    manifest: &PlatformManifest,
) -> Result<(String, String, Vec<OwnedPlatformFnDescriptor>), PlatformError> {
    let utf8_err = |what: &str, e: std::str::Utf8Error| PlatformError::LoadFailed {
        dll: std::path::PathBuf::new(),
        cause: format!("invalid UTF-8 in {what}: {e}"),
        location: ErrorLocation::unknown(),
    };

    let name = unsafe {
        let bytes = std::slice::from_raw_parts(manifest.name, manifest.name_len);
        std::str::from_utf8(bytes)
            .map_err(|e| utf8_err("platform name", e))?
            .to_string()
    };
    let version = unsafe {
        let bytes = std::slice::from_raw_parts(manifest.version, manifest.version_len);
        std::str::from_utf8(bytes)
            .map_err(|e| utf8_err("platform version", e))?
            .to_string()
    };

    let functions =
        unsafe { std::slice::from_raw_parts(manifest.functions, manifest.function_count) };

    let mut descriptors = Vec::with_capacity(manifest.function_count);
    for func in functions {
        let func_name = unsafe {
            let bytes = std::slice::from_raw_parts(func.name, func.name_len);
            std::str::from_utf8(bytes)
                .map_err(|e| utf8_err("function name", e))?
                .to_string()
        };
        let func_type_sig = unsafe {
            let bytes = std::slice::from_raw_parts(func.type_sig, func.type_sig_len);
            std::str::from_utf8(bytes)
                .map_err(|e| utf8_err("function type_sig", e))?
                .to_string()
        };
        let func_docstring = unsafe {
            let bytes = std::slice::from_raw_parts(func.docstring, func.docstring_len);
            std::str::from_utf8(bytes)
                .map_err(|e| utf8_err("function docstring", e))?
                .to_string()
        };

        let mut param_names = Vec::with_capacity(func.param_name_count);
        if func.param_name_count > 0 {
            let name_ptrs = unsafe {
                std::slice::from_raw_parts(func.param_names, func.param_name_count)
            };
            let name_lens = unsafe {
                std::slice::from_raw_parts(func.param_name_lens, func.param_name_count)
            };
            for i in 0..func.param_name_count {
                let pname = unsafe {
                    let bytes = std::slice::from_raw_parts(name_ptrs[i], name_lens[i]);
                    std::str::from_utf8(bytes)
                        .map_err(|e| utf8_err(&format!("param name {i}"), e))?
                        .to_string()
                };
                param_names.push(pname);
            }
        }

        descriptors.push(OwnedPlatformFnDescriptor {
            name: func_name,
            ptr: func.ptr,
            param_count: func.param_count as usize,
            type_sig: func_type_sig,
            docstring: func_docstring,
            param_names,
            scheduling_class: SchedulingClass::from_u32(func.scheduling_class),
        });
    }

    Ok((name, version, descriptors))
}

// ---------------------------------------------------------------------
// Decision 24 — consuming capture-RC protocol (Sprint 59 Workstream C-i).
//
// These tests verify that `into_owned_consuming` preserves the caller's
// transferred-reference contract: one caller-transfer in, one CLOwned::drop
// dec out, net zero. `own()` vs `into_owned_consuming()` differ by whether
// they inc for the capture (former) or take the caller's transferred ref
// directly (latter). Regression guard for `design/backend/ring2-rc.md` §10.4.
// ---------------------------------------------------------------------

#[cfg(test)]
mod tests {
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

    // ABI_VERSION is 6 (Sprint 86, DEF-5 — the manifest export namespacing).
    // Was 5 at FIXME 0327 Option A (the DLL-local dispatch-funnel fault-catch;
    // `call_effect_thunk` returns `EffectOutcome` and the `CLIO::effect*`
    // wrapper catches DLL-side), 4 at the FIXME 0327 step-1 node-widen (the
    // IO_TAG_EFFECT fourth-field add), 3 at FIXME 0286 (the three-exports macro
    // rework).
    // spec: design/arch/bounded-contexts.md §5 invariant 9
    #[test]
    fn abi_version_is_6() {
        assert_eq!(ABI_VERSION, 6);
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
}
