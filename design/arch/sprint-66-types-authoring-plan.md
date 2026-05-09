# Sprint 66 — `cranelisp-types` Wave 0 authoring plan

**Status:** authored 2026-05-07 by `/arch` (Phase 3 design); expanded 2026-05-08 (/arch Wave B — Phase 3 FIXME resolutions per `sprints/SPRINT.md` §"Phase 3 FIXME resolutions"); revised 2026-05-09 (/arch — fn_ptr unification: the Wave B `primitive_fn_ptr` add was replaced by a unified `fn_ptr` field that ALSO replaced `platform_fn_ptr`; `Code` variants slim to lifecycle owner only); **rolled back 2026-05-09 later same day (Wave 0 amendment, commit `1dc57ae`)** — the unified `fn_ptr` field introduced by `b09ec76` was redundant with the per-module `GotTable` already populated at registration; it has been **removed** from `ModuleEntry::Def`. The `Code` variant slim still holds (variants are tuple-shaped `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)`); the post-rollback canonical statement is **GOT is the single source of truth for callable addresses** (see §1.7-revised below). Wave B's `ParsedEntry`, `DefmacroInfo`, `LinkerError` additions are unaffected.
**Companion docs:** `sprints/SPRINT.md` §"Architecture review (Phase 2)" — Wave 0 task; `sprints/SPRINT.md` §"Phase 3 FIXME resolutions" — Wave B resolutions; `design/arch/facades/types.md` — target-stating public surface.
**Scope:** design-only. Source authoring (`crates/cranelisp-types/src/`) lands in Phase 5 by `/dev` (types). This plan is the brief that `/dev` (types) executes.

This plan is the **Wave 0 authoring brief** for the types crate. After Wave B's FIXME resolutions, Wave 0 lands more new types in `cranelisp-types` than originally scoped. Wave 0 must complete before Wave 2 consumer slices begin per the wave-ordering constraint at §5.

---

## 1. Types to add (Wave 0 authoring — `/arch`-direct)

### 1.1 `ErrorLocation` + `LineCol` + `LineColRange` — Decision 39 partial-landing

**Status discovered during Phase 3 authoring.** The Phase 2 review listed `ErrorLocation` as "verify — final per Decision 39 / S64 substance" and the slices (typecheck row 13, backend row 5, platform rows 1–2, int rows 27–28) all assume `ErrorLocation` already exists in `cranelisp-types`. **Source check confirms it does not.** `crates/cranelisp-types/src/error.rs` carries the pre-Decision-39 shape: each `CranelispError` variant has `span: Span` directly; no `ErrorLocation`, no `LineCol`, no `LineColRange`. Decision 39's `ErrorLocation` is a contract the source has not caught up with — the same gap pattern Decision 42 was filed against.

**Implication:** `PlatformError`'s four variants in §1.3 below carry `location: ErrorLocation`. Authoring `PlatformError` without `ErrorLocation` is structurally impossible. **`ErrorLocation` becomes the first authoring item of Wave 0.** This is in scope per the Phase 2 verdict's revision #2 ("/arch authors `ResolutionGap` + `PlatformError` + `CranelispError::Platform` variant before Wave 2 consumer slices begin") read against the actual source state — the verdict's "verify" disposition for `ErrorLocation` was based on the slice authors' belief that S64 had landed it; it had not.

This is flagged as a **Wave 0 scope-expansion finding** at §6 below. Net effect: +3 types added to Wave 0, not the +3 (`ResolutionGap` + `PlatformError` + variant) the verdict estimated. The reshape is `ErrorLocation` + `LineCol` + `LineColRange` plus a per-variant reshape of `CranelispError`.

**Shape to author** (per `design/arch/facades/types.md` lines 488–533):

```rust
// crates/cranelisp-types/src/error.rs

use std::path::PathBuf;
use serde::{Deserialize, Serialize};
use crate::{FQSymbol, Span};

/// 1-based line + column, derived from byte offsets when source is in hand.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineCol {
    pub line: u32,
    pub col: u32,
}

/// Range across `LineCol` coordinates — start inclusive, end exclusive (matches `Span`).
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct LineColRange {
    pub start: LineCol,
    pub end: LineCol,
}

/// Permissive error-location carrier per Decision 39.
///
/// Producers populate the fields they have on hand at error-construction
/// time; the integration-layer formatter (`Sess::format_error`) selects
/// display strategy based on what's present.
///
/// - `span` is always populated — even synthetic forms use `SYNTHETIC`.
/// - `file` set when the error originates in a file-based module.
/// - `fq` set for post-parse errors (lets formatter resolve via
///   `shared.introspection[fq].source` for inline snippets).
/// - `line_col` set when source was in hand at error-construction time.
/// - `context` set when producer captures inline source snippet (parse
///   errors always; typecheck/codegen typically defer to introspection).
///
/// See `design/arch/legacy/decisions/0039-per-defn-source-on-introspection.md`
/// for the operative rationale and `facades/types.md` §"Errors and warnings"
/// for the producer-side population matrix.
#[non_exhaustive]
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ErrorLocation {
    pub span: Span,
    pub file: Option<PathBuf>,
    pub fq: Option<FQSymbol>,
    pub line_col: Option<LineColRange>,
    pub context: Option<String>,
}

impl ErrorLocation {
    /// Synthetic location — used by callers that don't have any concrete
    /// coordinates yet (e.g., `cranelisp-platform::manifest_to_descriptors`
    /// constructs `LoadFailed` with `ErrorLocation::unknown()`; the caller
    /// rewrites at the call site). Span is `SYNTHETIC`.
    pub fn unknown() -> Self;

    /// Construct from a span only — common for typecheck/codegen sites that
    /// have a span but defer file/fq/line_col resolution to the formatter.
    pub fn from_span(span: Span) -> Self;
}
```

**Derived traits:** `Debug, Clone, Serialize, Deserialize` (cache participation per types-crate convention). `LineCol` and `LineColRange` additionally derive `PartialEq, Eq` (cheap; useful for tests). `ErrorLocation` does NOT derive `PartialEq` because `context: Option<String>` would force string comparison on equality — tests that need to compare locations should match on individual fields.

**`#[non_exhaustive]`:** all three structs (per the policy at `facades/types.md` §"`#[non_exhaustive]` policy").

**Reshape of `CranelispError`** — paired with `ErrorLocation` landing. Each variant that today carries `span: Span` directly is reshaped to carry `location: ErrorLocation`:

```rust
#[non_exhaustive]
pub enum CranelispError {
    ParseError    { message: String, location: ErrorLocation },
    TypeError     { message: String, location: ErrorLocation },
    CodegenError  { message: String, location: ErrorLocation },
    ModuleError   { message: String, location: ErrorLocation },   // `file: Option<PathBuf>` migrates into ErrorLocation.file
    MacroError    { message: String, location: ErrorLocation },
    Platform(PlatformError),                                       // §1.3 below
    // future: LinkError, CacheError, RuntimeError per facade lines 541–545
}

impl CranelispError {
    pub fn span(&self) -> Span;                                    // delegates to location.span where applicable
    pub fn message(&self) -> &str;
    pub fn location(&self) -> Option<&ErrorLocation>;              // facade line 551 — single accessor
}
```

**Cost:** ~80 LOC of authoring (3 new structs + helper impls + `CranelispError` variant reshape + `Display` impl path-through). The `Display` impl in `error.rs` lines 54–82 is reshaped to format from `location` rather than from bare `span` + `file`; the existing message + span/file path reduces cleanly.

### 1.2 `ResolutionGap` enum

**Source:** `design/arch/facades/types.md` §"Errors and warnings" lines 579–593; FIXME 0098 Phase 1.

```rust
// crates/cranelisp-types/src/error.rs (or a new resolution.rs sibling — /dev's call)

use crate::{FQSymbol, FQTypeName};

/// Cross-cutting "this dependency isn't ready yet" signal.
///
/// Carried by both `cranelisp_frontend::ExpansionError::Gap` and
/// `cranelisp_typecheck::CheckError::Gap`. The integration layer's
/// `process_form` pattern-matches on the variant to decide what to wait
/// on — typecheck for symbol typing, JIT for in-mem macro code, typecheck
/// for an opaque type ref. Per FIXMEs 0092 / 0093 / 0098.
///
/// `ResolutionGap` is the sole multi-consumer exception that justifies
/// staying in `cranelisp-types` per Principle 15 — both frontend and
/// typecheck originate it, and `int` consumes from both. `CheckError`
/// and `ExpansionError` move to their originating crates per FIXME 0100.
#[non_exhaustive]
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResolutionGap {
    /// Symbol's typecheck not yet complete — wait for
    /// `notify_symbol_typechecked(fq)`. Produced by
    /// `cranelisp_typecheck::check_form` for value references.
    SymbolTypechecked(FQSymbol),

    /// Macro target needs in-mem JIT — typecheck first, then
    /// `priority_boost_jit(fq)` + `wait_for_inmem(fq)`. Produced
    /// exclusively by `cranelisp_frontend::expand`; never raised
    /// from typecheck.
    MacroInMem(FQSymbol),

    /// Type reference needs typecheck — wait for
    /// `notify_type_resolved(fq)`. Produced by
    /// `cranelisp_typecheck::check_form` for FQ type references.
    Type(FQTypeName),
}
```

**Variant set** is the disambiguated facade form per master-design §11 question 1 (typecheck slice row 5). Per-variant rustdoc names which producer raises which variant — typecheck slice's row 5 is the contract this fulfils.

**Derived traits:** `Debug, Clone, PartialEq, Eq`. NOT `Serialize/Deserialize` — `ResolutionGap` is a transient runtime signal, never persisted to cache. (Contrast `FQSymbol`/`FQTypeName` which DO derive serde because they're persisted in `ModuleEntry` fields.)

**Placement:** `crates/cranelisp-types/src/error.rs` is the natural sibling location alongside `CheckError`'s carrier (FIXME 0100 Phase 1 moves `CheckError` to typecheck; `ResolutionGap` stays). `/dev` may alternatively place in a new `crates/cranelisp-types/src/resolution.rs` if module-cohesion arguments prefer that — both are facade-conformant.

**`#[non_exhaustive]`:** required per policy.

### 1.3 `PlatformError` enum

**Source:** Decision 42 (`design/arch/decisions/0042-platform-error-adopts-error-location.md`); FIXME 0104 Phase 1; `facades/types.md` §"Errors and warnings" lines 607–621.

```rust
// crates/cranelisp-types/src/error.rs

use std::path::PathBuf;
use crate::{ErrorLocation, Symbol};

/// Platform-origin failures — DLL load, manifest parse, ABI mismatch,
/// dispatch. Per Decision 42 — coordinates as data; `int`'s
/// `Sess::format_error` consumes via `CranelispError::Platform(PlatformError)`
/// and selects display strategy via Decision 39's mode-conditional source
/// resolution.
///
/// `cranelisp-platform`'s `manifest_to_descriptors` constructs the
/// `LoadFailed` variant with `ErrorLocation::unknown()`; the integration
/// layer (`int::load_platform_dll`) rewrites the `dll` path and
/// `location` fields at the call site so the user sees
/// `lib/main.cl:42:7: error: platform "stdio" not found in search path`
/// rather than a free-floating string.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum PlatformError {
    /// DLL could not be loaded from the search path.
    LoadFailed {
        dll: PathBuf,
        cause: String,
        location: ErrorLocation,
    },
    /// DLL was found but its manifest is missing or unreadable.
    ManifestNotFound {
        dll: PathBuf,
        location: ErrorLocation,
    },
    /// DLL's declared ABI version does not match the runtime's expected version.
    AbiVersionMismatch {
        dll: PathBuf,
        expected: u32,
        found: u32,
        location: ErrorLocation,
    },
    /// A platform-fn dispatch failed at runtime (e.g., null fn ptr,
    /// panic in callee).
    DispatchError {
        fn_name: Symbol,
        cause: String,
        location: ErrorLocation,
    },
}

impl PlatformError {
    /// Single accessor — every variant carries an `ErrorLocation`.
    pub fn location(&self) -> &ErrorLocation;
}
```

**Variant set:** the four variants Decision 42 §"Shape" pins. `#[non_exhaustive]` admits future failure modes (the platform slice's open question 1 about `TypeSigParseError` is downstream of this — adding a fifth variant in S67+ does not break the enum).

**Derived traits:** `Debug, Clone`. Not `Serialize/Deserialize` — platform errors are transient (constructed at load time, formatted at error display, dropped). Not `PartialEq/Eq` — `ErrorLocation` doesn't derive them (see §1.1).

**`Display` impl:** per Decision 42 §"Consequences" — `Display` matches the `Sess::format_error` mode-conditional path. The actual mode-conditional source-resolution lives in `int::format_error` (per Decision 39 — formatting is `int`'s); `PlatformError`'s `Display` is the **fallback** that produces a one-liner from the variant's data when no formatter is available (e.g., `Debug` outputs in tests, `eprintln!("{:?}", err)` paths).

```rust
impl std::fmt::Display for PlatformError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::LoadFailed { dll, cause, .. } =>
                write!(f, "failed to load DLL {}: {}", dll.display(), cause),
            Self::ManifestNotFound { dll, .. } =>
                write!(f, "DLL {} has no `cranelisp_platform_manifest` symbol", dll.display()),
            Self::AbiVersionMismatch { dll, expected, found, .. } =>
                write!(f, "DLL {} ABI version {} does not match expected {}", dll.display(), found, expected),
            Self::DispatchError { fn_name, cause, .. } =>
                write!(f, "platform fn `{}` dispatch failed: {}", &**fn_name, cause),
        }
    }
}
```

`std::error::Error` impl is also authored (mechanical — no source field given the upstream cause is `String`, not `&dyn Error`).

### 1.4 `CranelispError::Platform(PlatformError)` variant

**Source:** Decision 42 §"Shape"; `facades/types.md` line 544; FIXME 0104 Phase 1 step 2.

Single new variant on `CranelispError`. Placement in the existing enum: append after `MacroError` (the current last variant), before any future `LinkError`/`CacheError`/`RuntimeError` per facade lines 541–545. Keeps the enum order matching the facade text:

```rust
#[non_exhaustive]
pub enum CranelispError {
    ParseError    { message: String, location: ErrorLocation },
    TypeError     { message: String, location: ErrorLocation },
    CodegenError  { message: String, location: ErrorLocation },
    ModuleError   { message: String, location: ErrorLocation },
    MacroError    { message: String, location: ErrorLocation },
    Platform(PlatformError),   // ← new (FIXME 0104 Phase 1)
}
```

`CranelispError::location()` (the facade-line-551 accessor authored in §1.1) gains a `Self::Platform(p) => Some(p.location())` arm. `Display` impl gains a `Self::Platform(p) => write!(f, "{}", p)` arm.

### 1.5 `ParsedEntry` enum + `DefmacroInfo` move (per FIXME 0156 resolution, Wave B)

**Source:** `design/arch/facades/types.md` §"`ParsedEntry`"; `design/arch/facades/frontend.md` §"Free functions" — `build_form` returns `Vec<ParsedEntry>`.

`ParsedEntry` is the parse-time-only transient produced by `cranelisp_frontend::build_form` and consumed by `cranelisp_typecheck::check_form`. It NEVER lands in `SymbolTable`. Lifecycle: `parse → ParsedEntry → check_form → Vec<(Symbol, ModuleEntry)> → SymbolTable.insert`.

```rust
// crates/cranelisp-types/src/parsed.rs (new file — /dev's call where to place; sibling to ast.rs)

use crate::{
    ConstructorDef, DefnVariant, FieldDef, MacroClauseInfo, Span, Symbol, TraitDecl, TraitImpl,
    TypeName, Visibility,
};

/// Parse-time-only transient. Carries only what the parser knows; resolved-stage
/// fields (type, scheme, callees, code, got_slot) are populated by `check_form`
/// downstream and end up on `ModuleEntry`. NEVER lands in `SymbolTable`.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum ParsedEntry {
    /// Parsed `(defn name (params) body)` form. Pre-typecheck — types are `TypeExpr`, no `Scheme`.
    Def {
        name: Symbol,
        variants: Vec<DefnVariant>,
        visibility: Visibility,
        docstring: Option<String>,
        span: Span,
    },
    /// Parsed `(deftype Name … | (Variant fields...))` form.
    /// Yields the type itself plus per-constructor entries downstream.
    TypeDef {
        name: TypeName,
        type_params: Vec<TypeName>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        docstring: Option<String>,
        span: Span,
    },
    /// Parsed `(deftrait Name … (method sig)*)` form.
    TraitDecl {
        decl: TraitDecl,
    },
    /// Parsed `(impl Trait Type method-defns…)` form.
    TraitImpl {
        impl_: TraitImpl,
    },
    /// Parsed `(defmacro name clauses…)` form. Each clause downstream becomes
    /// a `ModuleEntry::Macro` clause via `synthesize_macro_clause_defn`.
    Macro {
        info: DefmacroInfo,
    },
    /// Synthetic per-constructor entry — emitted by `build_form` for each
    /// constructor of a `TypeDef`. Pre-typecheck shape; `check_form` lifts to
    /// a `ModuleEntry::Def` with primitive-kind constructor metadata.
    Constructor {
        name: Symbol,
        of_type: TypeName,
        fields: Vec<FieldDef>,
        span: Span,
    },
}

/// Per-clause macro structure derived from a `defmacro` Sexp.
/// Moved from `cranelisp-frontend` to `cranelisp-types` per FIXME 0156 resolution
/// — `int`'s post-`build_form` consumption path needs to name the type uniformly,
/// and `MacroClauseInfo` / `MacroParam` already live here.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub struct DefmacroInfo {
    pub name: Symbol,
    pub clauses: Vec<MacroClauseInfo>,
    pub visibility: Visibility,
    pub docstring: Option<String>,
    pub span: Span,
}
```

**Derived traits:** `Debug, Clone`. NOT `Serialize/Deserialize` — `ParsedEntry` is transient (never persisted to cache); `DefmacroInfo` similarly is not persisted directly (the resolved `ModuleEntry::Macro.clauses` is what serializes).

**`#[non_exhaustive]`:** required per policy.

**Move-out coordination:** `cranelisp-frontend/src/defmacro.rs` currently hosts `DefmacroInfo`. The type definition moves to `cranelisp-types`; the frontend's `parse_defmacro` becomes `pub(crate)` inside the `build_form` dispatcher. The frontend slice's row for `parse_defmacro` reshape coordinates this move-out — Wave 0 lands the new home; the frontend slice's row deletes from the old home in Wave 2.

**Cost:** ~120 LOC of authoring (`ParsedEntry` enum + variants + `DefmacroInfo` struct + module wiring in `lib.rs`).

### 1.6 `LinkerError` shape — confirm 2-variant baseline (per FIXME 0154 resolution)

**Source:** `design/arch/facades/types.md` §"Errors and warnings" — `LinkerError`; `design/arch/facades/backend.md` §"Errors" — backend-side reference.

`LinkerError` is the typed result of `Linker::get_symbol`. Per FIXME 0154 resolution (Wave B, 2026-05-08), accept the 2-variant baseline as the minimum surface acceptable at S66 close. The type is hosted in `cranelisp-types` (multi-consumer per Principle 15 — backend constructs, `int` matches at cache-hit failure); backend's facade re-references the same shape.

```rust
// crates/cranelisp-types/src/error.rs

use crate::LinkerSymbol;

#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum LinkerError {
    /// The cache `Linker`'s symbol table does not contain the requested name.
    SymbolNotFound { name: LinkerSymbol },
    /// Object relocation pass produced an error during `load_object` or
    /// per-symbol resolution.
    RelocationFailed { name: LinkerSymbol, cause: String },
}
```

**Derived traits:** `Debug, Clone`. Not `Serialize/Deserialize` — transient runtime signal.

**`#[non_exhaustive]`:** required; admits future variants (e.g., `MmapFailed`, `MachOParseError`, `AbiMismatch`) when evidence accrues. Re-shape may be triggered during /review of a future FIXME if the variant set proves insufficient.

**Cost:** ~15 LOC of authoring; this is a small enum with two variants.

### 1.7-revised GOT-as-single-source-of-truth (post-rollback) — supersedes both Wave B's `primitive_fn_ptr` add and the briefly-landed unified `fn_ptr` field

**Source:** `design/arch/facades/types.md` §"Symbol table — the single store" — `ModuleEntry::Def`; `design/arch/facades/primitives.md` §"Public surface" — `PRIMITIVES_TABLE`; `design/arch/facades/backend.md` §"Code — the per-symbol lifecycle owner"; `design/arch/facades/platform.md` §"Bounded-context invariants" #1; `crates/cranelisp-types/src/got.rs` (`GotTable`).

**Status (2026-05-09).** This section's authoring history has two superseded chapters:

1. **Wave B (FIXME 0159 resolution)** — proposed adding `primitive_fn_ptr: Option<*const u8>` to `ModuleEntry::Def` parallel to the existing `platform_fn_ptr`. Solved a real cycle but perpetuated per-origin field proliferation. **Superseded** mid-sprint by the fn_ptr unification (below).
2. **fn_ptr unification (commit `b09ec76`, Wave 0)** — proposed a single unified `fn_ptr: Option<*const u8>` covering all four origins, removing `platform_fn_ptr`. Landed briefly. **Superseded same day by `1dc57ae`** (the rollback) when /arch identified that the unified field duplicated state already maintained by the per-module `GotTable`: every callable entry already has a `got_slot`, and JIT-emitted code reads addresses from `got_base + slot * 8`. Stashing the same address on a sibling field was duplicate state — a Principle 7 violation.

**Canonical statement (post-rollback):**

> **GOT is the single source of truth for callable addresses.** `ModuleEntry::Def.got_slot: Option<usize>` indexes into the module's `GotTable`; the runtime address lives at `symbol_table.got().load_slot(slot)`. There is no separate `fn_ptr` / `platform_fn_ptr` / `primitive_fn_ptr` field — those workarounds are deleted. Origin (JIT-compiled / linker-loaded / platform DLL / primitive) is encoded by `kind: DefKind`, not by which optional field carries the ptr. `got_slot: None` indicates non-callable, non-addressable entries (special forms, `Overloaded` base entries, `TypeDef`/`TraitDecl`/`Macro`, constrained-fn templates).

**Authoring (post-rollback):**

- **No `fn_ptr` field on `ModuleEntry::Def`.** The b09ec76 add has been reverted by `1dc57ae`. `ModuleEntry::Def`'s post-rollback callable-address shape is `got_slot: Option<usize>` only.
- **No `platform_fn_ptr` field.** Removed by `b09ec76`; not reinstated by the rollback. Platform fn registration writes to a GOT slot, not to a per-entry field.
- **No `primitive_fn_ptr` field.** Wave B add never landed.
- **GOT shape unchanged** (`crates/cranelisp-types/src/got.rs`). `GotTable` carries `[AtomicPtr<u8>; GOT_TABLE_SIZE]`; `store_slot(slot, ptr)` (Release) / `load_slot(slot)` (Acquire). One `GotTable` per `SymbolTable`.

**Read pattern (post-rollback):**

```rust
// At read sites — collect_jit_setup, linker setup, IO trampoline, etc.
if let ModuleEntry::Def { got_slot: Some(slot), .. } = entry {
    let ptr = st.got().load_slot(*slot);
    if !ptr.is_null() {
        // use ptr — register with linker, push to jit_symbols, dispatch effect, etc.
    }
}
```

**Write pattern (post-rollback):**

```rust
// Backend: compile_to_module per defined symbol —
let slot = table.allocate_got_slot_for(&sym); // existing
let ptr = jit.get_finalized_function(func_id);
table.got().store_slot(slot, ptr);
// (No paired fn_ptr write. The entry already carries got_slot: Some(slot).)

// Platform: handle_platform per descriptor —
let slot = entry.got_slot.unwrap_or_else(|| table.allocate_got_slot());
table.got().store_slot(slot, desc.ptr);
// entry.got_slot updated to Some(slot) if newly allocated.

// Primitives: PRIMITIVES_TABLE static init —
// every primitive entry registers with a got_slot; the static populates
// the GOT slot to the function constant. C = () (Decision 32 default);
// no Code variant is named.
```

**Cycle stays avoided.** `cranelisp-primitives` and `cranelisp-platform` use `SymbolTable<C = ()>` (Decision 32 default — `()` never names `Code`). Both write to GOT slots via the `cranelisp-types`-hosted `GotTable` API. Neither names `cranelisp-backend`. Dep DAG `cranelisp-primitives → cranelisp-types` and `cranelisp-platform → cranelisp-types` stay acyclic.

**Decision 31 Scenario 2 preserved.** Lifecycle ownership stays inside `Code::Jit(Arc<Jit>)`. When a user redefines a fn, the old `ModuleEntry::Def` drops, its `Code::Jit(Arc<Jit>)` drops, refcount → 0 if last reference, custom `Drop` on `Jit` fires, `JITModule::free_memory()` runs. The GOT slot is atomically updated to the new code address before the old `Arc<Jit>` clone can drop (per-symbol JIT cardinality + GOT swap order — see Decision 41 + concurrency-symbol-table-entry.mmd for the atomic ordering). The GOT slot's pointer becomes invalid the instant `JITModule::free_memory()` runs — same lifecycle semantics as the briefly-considered sibling-field placement, but now the callable address has a single home.

**Cost (post-rollback):** zero net authoring in this Wave 0 brief. The `b09ec76` field add and `1dc57ae` field remove are paired in source; `cranelisp-types` is back at the pre-fn_ptr-unification shape (modulo the rewritten `got_slot` doc comment which now states the single-source-of-truth invariant). The `Code` variant slim (§1.8) still holds — that aspect of the unification work survived the rollback.

### 1.8 `Code` enum slim — `/dev (backend)` Wave 3 (preserved through rollback)

The `Code` enum's variants slim from `Code::Jit { jit: Arc<Jit>, ptr: *const u8 }` / `Code::Linker { linker: Arc<Linker>, ptr: *const u8 }` to `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` — lifecycle owner only. The variant-uniform `Code::ptr()` accessor is removed; consumers read the address from the GOT (the post-rollback single source of truth — see §1.7-revised) via the entry's `got_slot`, not from the `Code` variant.

This aspect of the S66 unification survived the `1dc57ae` rollback. The rollback removed only the redundant per-entry `fn_ptr` field; `Code` variants stay slim because the GOT (not a sibling field) is now where the address lives.

This is `/dev (backend)` work (Wave 3), not /arch authoring — `Code` lives in `crates/cranelisp-backend/src/code.rs` per Decision 41. The /arch deliverables that drive the work:

- `facades/backend.md` §"Code — the per-symbol lifecycle owner" — target shape (slim variants, no ptr accessor)
- `facades/types.md` §"Symbol table — the single store" — `ModuleEntry::Def.got_slot: Option<usize>` (the single source of truth for callable addresses; doc-comment in `crates/cranelisp-types/src/module.rs:430–460`)
- `facades/primitives.md`, `facades/platform.md`, `facades/intrinsics.md` — GOT-slot reference at the facade level

**Cross-wave dep:** the `Code` slim depends on consumers being able to read addresses without a `Code::ptr()` accessor. Post-rollback that requirement is met by the GOT — every callable entry has `got_slot: Some(_)` and the address is read via `symbol_table.got().load_slot(slot)`. Backend's `compile_to_module` writes to the GOT slot (not to a per-entry field) immediately after `jit.get_finalized_function`; the `Code::Jit(Arc<Jit>)` lifecycle owner is written separately via `SymbolTable::write_code`.

---

## 2. Verification — `ErrorLocation`, `CodeStore`, `LinkerStore`

Per the Phase 2 verdict's "verify" classification for these items, spot-checked against current source.

### 2.1 `CodeStore` and `LinkerStore` — VERIFIED PRESENT

Source: `crates/cranelisp-types/src/module.rs:36-37` (`CodeStore`) and `:54-55` (`LinkerStore`). Shape matches Decision 32 exactly:

```rust
pub trait CodeStore: Clone + Send + Sync + 'static {}
impl<T: Clone + Send + Sync + 'static> CodeStore for T {}

pub trait LinkerStore: Clone + Send + Sync + 'static {}
impl<T: Clone + Send + Sync + 'static> LinkerStore for T {}
```

`SymbolTable<C: CodeStore = (), L: LinkerStore = ()>` parameterisation present at `:101`. Tests at `:1590-1683` confirm the blanket impl works with `()` defaults and concrete `C = i64`. **No Wave 0 action required.** `/dev` (types) confirms during the slice landing that the surface is unchanged.

### 2.2 `ErrorLocation` — NOT PRESENT (corrected from "verify" to "author")

See §1.1 above. The Phase 2 verdict's classification was based on the slice authors' assumption that S64 had landed `ErrorLocation`; it had not. **This becomes Wave 0 authoring**, not Wave 0 verification.

The substance partial-landing inventory at S65 close (`design/arch/sprint-65-reshape-phase-2-review.md`) noted Decision 39's per-defn source on Introspection landed but the error-shape reshape did not. `ErrorLocation`'s absence from source is the surviving Decision-39 gap — closing it here aligns with the Phase 2 verdict's "Wave 0 types-crate authoring" wave revision.

### 2.3 `Span`, `FQSymbol`, `FQTypeName`, `FQTraitName` — VERIFIED PRESENT

Spot-check: `crates/cranelisp-types/src/lib.rs:29` (`Span`), `:64-67` (FQ-types). All match facade. **No Wave 0 action required.**

---

## 3. Removals to coordinate (`/dev`-owned; not /arch authoring)

These are **migrate-out** work owned by `/dev` (typecheck) and `/dev` (backend) per FIXME 0100 Phases 1+2. `/arch`'s role here is verification of the relocation order so dangling re-exports do not appear.

### 3.1 FIXME 0100 Phase 1 — relocate to `cranelisp-typecheck` (`/dev`-typecheck-owned)

Source: `crates/cranelisp-types/src/check.rs` (133 lines total). The whole file's contents move out, **except** items that other consumers continue to need from `cranelisp-types` (none — see analysis below).

| Type | Current home (lines) | Target crate | Notes |
|---|---|---|---|
| `MethodResolutions` (type alias) | `check.rs:9` | `cranelisp-typecheck` | Re-exported via `cranelisp-types` lib.rs:38 ; consumed by typecheck `infer.rs` and backend `compile_apply` |
| `ResolvedCall` enum | `check.rs:13-40` | `cranelisp-typecheck` | Consumed by backend codegen — backend's import path becomes `cranelisp_typecheck::ResolvedCall` |
| `MonoDefn` | `check.rs:43-50` | `cranelisp-typecheck` | Consumed by backend monomorphisation |
| `DisplayInfo` | `check.rs:55-60` | `cranelisp-typecheck` | Consumed only by `int` |
| `CheckResult` | `check.rs:74-80` | `cranelisp-typecheck` | Re-exported via lib.rs:38 ; consumed by `int` |
| `TypeDefInfo` | `check.rs:84-89` | `cranelisp-typecheck` | Consumed by `int` (introspection) and backend (ADT layout) |
| `ConstructorInfo` | `check.rs:93-102` | `cranelisp-typecheck` | Consumed by backend |
| `FieldInfo` | `check.rs:106-109` | `cranelisp-typecheck` | Consumed by backend |
| `ReplSnapshot` | `check.rs:121-132` | `cranelisp-typecheck` | Re-exported via lib.rs:38 ; consumed by `int` |

**Coordination check (dangling re-exports):**

- `cranelisp-types/src/lib.rs:37-40` re-exports `CheckResult, ConstructorInfo, DisplayInfo, FieldInfo, MethodResolutions, MonoDefn, ReplSnapshot, ResolvedCall, TypeDefInfo`. **All nine** must be deleted from this re-export block when the file moves out, in the same change set as the source-side deletion. `/dev` (typecheck) handles this in their slice (typecheck slice row 20).
- `cranelisp-typecheck/src/lib.rs:38-40` currently `pub use cranelisp_types::{CheckResult, CranelispError, ReplSnapshot, TopLevel}`. Per typecheck slice row 20: drop the four-item block; add new `pub use` for the relocated types from internal modules; `CranelispError` and `TopLevel` callers import from `cranelisp-types` directly.
- Backend's `compile_apply` and other consumers re-import as `use cranelisp_typecheck::{ResolvedCall, …}` — backend slice rows enumerate this.
- Int's `worker.rs`, `session_v4.rs`, etc. re-import — int slice rows 6/9 cover this.

**Order-of-landing constraint:** the `cranelisp-types` deletions and the `cranelisp-typecheck` migrate-ins must land in the **same commit** (not just the same wave). Splitting risks an intermediate state where a consumer crate sees the type from neither crate or both. `/sprint` Wave 2 sub-batching enforces this.

**`CheckError`, `ResolutionGap`** are not in this list because they don't yet exist in source — they are new types authored here at §1.2 and (for `CheckError`) authored in `cranelisp-typecheck` per typecheck slice row 3. The migrate-out list above is the existing types only.

**`FormCheckResult`, `CheckPass`, `ModuleCheckAccumulator`, `CheckState`, `TypeCheckEnv`** are listed in FIXME 0100 Phase 1 but **already live in `cranelisp-typecheck`** per typecheck slice rows 7–8 (verified at `cranelisp-typecheck/src/program.rs:231` for `CheckPass` and `:checker.rs:52,134` for `CheckState`/`TypeCheckEnv`). Their entries in FIXME 0100 are verify-only — they were never in `cranelisp-types` to begin with.

### 3.2 FIXME 0100 Phase 2 — relocate to `cranelisp-backend` (`/dev`-backend-owned)

`CompilationError` is **not currently in `cranelisp-types`** — there is no `CompilationError` type in the types crate today. Backend slice row 5 authors it as a NEW type **in `cranelisp-backend`**. So Phase 2's "relocate `CompilationError` out of `cranelisp-types`" is a misstatement of FIXME 0100; the actual work is "author `CompilationError` in `cranelisp-backend`". No `cranelisp-types` deletion is required.

`GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver` are similarly not in `cranelisp-types` — they're new authoring in `cranelisp-backend` per FIXME 0099 (backend slice rows). No `cranelisp-types` deletion required.

**Coordination check:** Phase 2's "verify" disposition is correct — `/dev` (backend) confirms during their slice that none of the four GOT-observer types or `CompilationError` accidentally land in `cranelisp-types` during S66.

### 3.3 Net removal count

Per §3.1: **9 types removed from `cranelisp-types::check` (the entire `check` module)** — the `pub mod check` declaration at `lib.rs:10` and the nine `pub use check::*` re-exports at `:37-40` all disappear when the file is moved.

The Phase 2 verdict's estimate of "−13 types" was based on an assumption that included Phase 2 backend-side types as removals; correcting for §3.2's finding (those are NEW authoring in backend, not removals from types), the actual removal count is **−9 types** from `cranelisp-types`.

---

## 4. Public-API delta — before / after stub

### Before S66 (current state of `cranelisp-types/src/lib.rs:29-67`)

```rust
pub use span::Span;
pub use error::{CranelispError, Warning, WarningKind};
pub use sexp::Sexp;
pub use ast::{ConstructorDef, Defn, DefnVariant, Expr, FieldDef, MatchArm, Pattern, Program,
              TopLevel, TraitDecl, TraitImpl, TraitMethodSig, TypeExpr, Visibility, free_vars_expr};
pub use types::{Scheme, Subst, Type, TypeId, apply, free_vars, max_type_var_id,
                format_type_display, format_type_with_vars, type_var_names};
pub use check::{CheckResult, ConstructorInfo, DisplayInfo, FieldInfo, MethodResolutions,
                MonoDefn, ReplSnapshot, ResolvedCall, TypeDefInfo};                              // ← 9 items removed by §3.1
pub use scheduling::SchedulingClass;
pub use module::{CodeStore, ConstrainedFn, DefKind, ExportSpec, ImplSexp, ImportNames,
                 ImportSpec, LinkerStore, MacroClauseInfo, MacroParam, ModDecl, ModuleEntry,
                 OverloadVariant, PlatformSpec, PrimitiveKind, SymbolTable};
pub use got::GotTable;
pub use heap::{HeapCategory, HeapHeader};
pub use pipeline::{CallEdge, CallGraph, CallInfo, CodegenBehaviour, CompileContext,
                   CompileResult, GOT_TABLE_SIZE, ModuleStrategy, NULLARY_TAG_THRESHOLD};
pub use operator::{ring0_primitives, ring1_primitives, ring3_primitives, PrimitiveDef};
pub use marshal::{TAG_SNIL, TAG_SCONS, TAG_SEXP_INT, TAG_SEXP_FLOAT, TAG_SEXP_BOOL,
                  TAG_SEXP_STR, TAG_SEXP_SYM, TAG_SEXP_LIST, TAG_SEXP_BRACKET};
pub use newtype::{FQSymbol, FQTraitName, FQTypeName, JitSymbol, ModuleFullPath, ModuleName,
                  Symbol, TraitName, TypeName};
```

### After S66 close (target shape — including Wave B additions)

```rust
pub use span::Span;
pub use error::{
    CranelispError,
    ErrorLocation, LineCol, LineColRange,                                                      // ← +3 (§1.1)
    LinkerError,                                                                               // ← +1 (§1.6, FIXME 0154)
    PlatformError,                                                                             // ← +1 (§1.3)
    ResolutionGap,                                                                             // ← +1 (§1.2)
    Warning, WarningKind,
};
pub use sexp::Sexp;
pub use ast::{ConstructorDef, Defn, DefnVariant, Expr, FieldDef, MatchArm, Pattern, Program,
              TopLevel, TraitDecl, TraitImpl, TraitMethodSig, TypeExpr, Visibility, free_vars_expr};
pub use parsed::{DefmacroInfo, ParsedEntry};                                                   // ← +2 (§1.5, FIXME 0156)
pub use types::{Scheme, Subst, Type, TypeId, apply, free_vars, max_type_var_id,
                format_type_display, format_type_with_vars, type_var_names};
// pub use check::{...}                                                                         ← removed (§3.1, 9 items)
pub use scheduling::SchedulingClass;
pub use module::{CodeStore, ConstrainedFn, DefKind, ExportSpec, ImplSexp, ImportNames,
                 ImportSpec, LinkerStore, MacroClauseInfo, MacroParam, ModDecl, ModuleEntry,
                 OverloadVariant, PlatformSpec, PrimitiveKind, SymbolTable};
pub use got::GotTable;
pub use heap::{HeapCategory, HeapHeader};
pub use pipeline::{CallEdge, CallGraph, CallInfo, CodegenBehaviour, CompileContext,
                   CompileResult, GOT_TABLE_SIZE, ModuleStrategy, NULLARY_TAG_THRESHOLD};
pub use operator::{ring0_primitives, ring1_primitives, ring3_primitives, PrimitiveDef};
pub use marshal::{TAG_SNIL, TAG_SCONS, TAG_SEXP_INT, TAG_SEXP_FLOAT, TAG_SEXP_BOOL,
                  TAG_SEXP_STR, TAG_SEXP_SYM, TAG_SEXP_LIST, TAG_SEXP_BRACKET};
pub use newtype::{FQSymbol, FQTraitName, FQTypeName, JitSymbol, ModuleFullPath, ModuleName,
                  Symbol, TraitName, TypeName};
```

### Net delta (post-Wave-B)

| Direction | Count | Items |
|---|---|---|
| **Added** | +8 | `ErrorLocation`, `LineCol`, `LineColRange`, `PlatformError`, `ResolutionGap`, `LinkerError`, `ParsedEntry`, `DefmacroInfo` |
| **Removed** | −9 | `CheckResult`, `ConstructorInfo`, `DisplayInfo`, `FieldInfo`, `MethodResolutions`, `MonoDefn`, `ReplSnapshot`, `ResolvedCall`, `TypeDefInfo` |
| **Reshaped** | +1 enum (variants reshaped) | `CranelispError` (variants migrate `span`/`file` → `location: ErrorLocation`; new `Platform` variant) |
| **Reshaped** | +1 struct (field shape) | `ModuleEntry::Def` `got_slot: Option<usize>` doc-comment rewritten — GOT is the **single source of truth** for callable addresses (§1.7-revised post-rollback). `platform_fn_ptr` removed by `b09ec76`; the briefly-landed unified `fn_ptr` field also removed by `1dc57ae` (the rollback). No per-entry sibling ptr field. |
| **Reshaped** | +1 enum (variants slim) | `Code` (in `cranelisp-backend`) variants slim from `{ jit, ptr }` / `{ linker, ptr }` to `(Arc<Jit>)` / `(Arc<Linker>)` — lifecycle owner only; the per-entry call address now lives in `SymbolTable.got()` (a `GotTable` per Decision 7), indexed by `ModuleEntry::Def.got_slot`. (NOT `cranelisp-types` work; `/dev (backend)` Wave 3 — see §1.8.) |

**Net: −1 public type** in `cranelisp-types` (was −4 pre-Wave-B; +3 Wave-B additions narrow the shrinkage). The direction is still mild shrinkage per Principle 15 — the types crate is concentrating on multi-consumer boundary types. The two new transient types (`ParsedEntry`, `DefmacroInfo`) are additions because the parse-time → check-time handoff was previously implicit (frontend internal types); making it explicit is the cost of the form-vocabulary widening (FIXME 0156 resolution).

The corrected `cargo public-api` baseline target for `cranelisp-types` post-S66 should drop by approximately 9 line-entries (the removed types) plus add approximately 12–15 line-entries (3 new structs with named fields × ~3 entries each = ~9, plus 1 new enum × 4 variants = 4, plus reshaped `CranelispError` variants = ~5 line deltas, minus the existing variants' lost lines). `/qa` slice §1.1 row 7 (cranelisp-types baseline) should expect roughly net-zero line count change in `public-api.txt`, with substantial churn distributed across error.rs and check.rs (the latter going to zero). This is a tractable diff for `/review` to audit in one PR.

---

## 5. Ordering constraint for `/sprint`

Wave 0 (`/arch` authoring) must complete before each Wave 2 consumer slice begins. Per the Phase 2 verdict, Wave 2 is the type-relocation foundation; Wave 3 is the per-crate consumer adoption.

### 5.1 Hard ordering — Wave 0 → Wave 2 prerequisites

The 5 new types from §1 unblock specific items across the 8 implementation slices:

| Wave 0 type | Unblocks (slice : row) | Constraint |
|---|---|---|
| `ErrorLocation` (+ `LineCol`, `LineColRange`) | typecheck slice row 13, 24 ; backend slice row 5, 15 ; platform slice rows 1–2 ; int slice rows 27–28, 51 ; **also** any reshape of typecheck/frontend/backend error sites that today carry bare `Span` | **Hard prerequisite** for any error-reshape work. `PlatformError` cannot land without it. |
| `ResolutionGap` | frontend slice row 10 ; typecheck slice rows 1, 3, 4, 5 ; int slice row 3 | **Hard prerequisite** for the `process_form` shape-pivot triad (frontend row 7 + typecheck row 1 + int row 3 — the load-bearing critical path per Phase 2 recommendation #1). |
| `PlatformError` | platform slice rows 1, 2 ; int slice rows 27, 28 | **Hard prerequisite.** Platform slice cannot land without it. |
| `CranelispError::Platform` variant | int slice row 27 (`format_error` Platform arm) | Same as `PlatformError`. |
| `LinkerError` (Wave B — FIXME 0154) | backend slice row 12 (`Linker::get_symbol` typed-result reshape) | **Hard prerequisite** for backend row 12; small surface so low risk. |
| `ParsedEntry` + `DefmacroInfo` (Wave B — FIXME 0156) | frontend slice rows 5–6 (`build_form` shape-pivot, `parse_defmacro` reshape) ; typecheck slice row 1 (`check_form` consumes `ParsedEntry`) ; int slice (`process_form` parse → check → insert pipeline) | **Hard prerequisite** for the form-vocabulary widening. Coordinated with frontend's `defmacro.rs` move-out. |
| GOT-slot canonicalisation on `ModuleEntry::Def` (Wave B revised — FIXME 0159 + S66 fn_ptr unification + post-rollback per `1dc57ae`) | primitives slice row 10 (`PRIMITIVES_TABLE` static authoring writes to GOT slot) ; backend slice (`compile_to_module` writes ptr to `got().store_slot(slot, ptr)`) ; platform slice (`platform_fn_ptr` callsite migration → GOT-slot read/write) | **Hard prerequisite** for all three. Removal of `platform_fn_ptr` (b09ec76) and removal of the briefly-added `fn_ptr` (1dc57ae) must precede static authoring AND backend `Code` slim AND platform callsite migration. Post-rollback the GOT is the single source of truth for callable addresses. |

### 5.2 Wave 2 consumer slices that DEPEND on Wave 0

In Wave-order priority:

1. **typecheck slice** — depends on `ResolutionGap` + `ErrorLocation` + `ParsedEntry` (rows 1, 3, 13, 24; row 1 reshape now consumes `ParsedEntry` per FIXME 0156).
2. **frontend slice** — depends on `ResolutionGap` + `ParsedEntry` + `DefmacroInfo` (row 10 re-export; rows 5–6 `build_form` shape-pivot per FIXME 0156).
3. **platform slice** — depends on `PlatformError` (rows 1, 2).
4. **int slice** — depends on `ResolutionGap` (row 3), `PlatformError` (rows 27, 28), `ErrorLocation` (rows 27, 28, 51), `ParsedEntry` (parse → check → insert pipeline shape).
5. **backend slice** — depends on `ErrorLocation` (rows 5, 15) for `CompilationError::CodegenFailed.location` field; depends on `LinkerError` (row 12) per FIXME 0154.
6. **primitives slice** — depends on the GOT-slot canonicalisation on `ModuleEntry::Def` (row 10) per FIXME 0159 + S66 fn_ptr unification + post-rollback per `1dc57ae`; the static allocates a `got_slot` per primitive and populates the slot via `got().store_slot(slot, ptr)`, leaving `code: None`.

### 5.3 Wave 0 internal ordering

Within Wave 0 (single `/dev` (types) author working alone):

1. **`ErrorLocation` + `LineCol` + `LineColRange` first.** Both `PlatformError` and `CranelispError`'s reshaped variants depend on it. `ResolutionGap` is independent — can land in parallel.
2. **`CranelispError` variant reshape (existing variants `span`/`file` → `location: ErrorLocation`)** lands paired with #1. This is mechanical but touches every callsite of `CranelispError::*` construction across the workspace — the reshape is `cranelisp-types`-internal in terms of the type definition, but the construction sites scatter across all consumer crates. **`/dev` (types) executes the type-side reshape; consumer crates' construction-site updates land in their own slices' Wave 2/3 work.** This means S66 will have a transient compilation-broken window between Wave 0 landing and the first Wave 2 consumer landing. `/sprint` must sequence consumer slices to close this window quickly.
3. **`ResolutionGap`** independent — can land in parallel with #1+#2.
4. **`PlatformError` + `CranelispError::Platform` variant** — depends on #1 (needs `ErrorLocation`). Lands after #1 but in same wave.
5. **`LinkerError`** (§1.6, Wave B) — independent of all of the above; tiny enum. Can land at any point.
6. **`ParsedEntry` + `DefmacroInfo`** (§1.5, Wave B) — depends on existing types (`Span`, `Symbol`, `MacroClauseInfo`, `TraitDecl`, `TraitImpl`, `ConstructorDef`, `FieldDef`). Independent of error types. Pair with the move-out of `DefmacroInfo` from `cranelisp-frontend` (frontend slice coordinates the deletion in Wave 2).
7. **GOT-slot canonicalisation on `ModuleEntry::Def`** (§1.7-revised, Wave B revised — fn_ptr unification then post-rollback per `1dc57ae`) — `platform_fn_ptr` removed (b09ec76); briefly-landed unified `fn_ptr` removed (1dc57ae); `got_slot: Option<usize>` doc-comment rewritten in `crates/cranelisp-types/src/module.rs:430–460` to state the GOT-as-single-source-of-truth invariant. Coordinated with primitives slice's row 10 (writes ptr to GOT slot from the static), backend slice (writes ptr to `got().store_slot(slot, ptr)` in `compile_to_module` / `load_object`; slims `Code` variants per §1.8), and platform slice (migrates `platform_fn_ptr` callsites to GOT-slot reads/writes). Neither `primitive_fn_ptr` (Wave B) nor `fn_ptr` (b09ec76 unification) lives in source.

Wave 0 is sized as **~2.5 days of `/dev` (types) work** (revised up from 1.5d after Wave B additions) — most of it is the `CranelispError` reshape and the construction-site sweep across consumer crates that must follow. The pure type authoring breakdown:

| Item | Sizing |
|---|---|
| `ErrorLocation` + `LineCol` + `LineColRange` | ~3 hours |
| `CranelispError` reshape + workspace sweep | ~0.5 day |
| `ResolutionGap` | ~30 minutes |
| `PlatformError` + `CranelispError::Platform` | ~2 hours |
| `LinkerError` (Wave B) | ~30 minutes |
| `ParsedEntry` + `DefmacroInfo` move (Wave B) | ~1 day (variants + module wiring + frontend `defmacro.rs` move-out coordination) |
| GOT-slot canonicalisation + `platform_fn_ptr` remove (Wave B revised, post-rollback `1dc57ae`) | ~30 minutes (already landed; doc-comment-only at this point) |

**Total: ~2.5 days.** The bulk of the expansion is `ParsedEntry` (the form-vocabulary widening adds the most authoring work). `LinkerError` and the GOT-slot canonicalisation (per §1.7-revised — post-rollback) are minutes-grade additions that don't materially shift the timeline.

### 5.4 Wave 2 begins when Wave 0 closes

`/sprint` should treat Wave 0 as a **single-author sub-wave** with no parallelism — the cross-crate reshape sweep means parallelising Wave 0 across multiple `/dev` authors creates merge conflicts on every consumer crate's error-construction sites. Wave 0 closes when:

1. `cranelisp-types` builds clean.
2. `cargo public-api` baseline regenerated for `cranelisp-types` (per `/qa` slice §1.1 — `/dev` runs the tool, `/review` approves the diff).
3. Every consumer crate compiles green against the new types (the `CranelispError` reshape sweep is complete).

Wave 2 then begins with the typecheck + frontend + platform slices in parallel; backend + int follow once those land per the Phase 2 verdict's wave plan (line 206 of `sprints/SPRINT.md`).

---

## 6. Findings flagged for `/sprint`

### 6.1 Wave 0 scope expansion — `ErrorLocation` requires authoring, not verification

**Phase 2 verdict said:** `ErrorLocation` is "verify — final per Decision 39 / S64 substance".
**Source check confirms:** `ErrorLocation` does not exist in `crates/cranelisp-types/src/`. Decision 39's error-shape reshape is a surviving partial-landing.
**Implication:** Wave 0 net-types-added expands from +3 to +5 (`ErrorLocation` + `LineCol` + `LineColRange` added), and `CranelispError`'s variants reshape (per-variant `span`/`file` → `location: ErrorLocation`). This adds approximately +0.5 days to Wave 0 sizing and triggers a workspace-wide construction-site sweep that bridges Wave 0 and Wave 2.

`/sprint` should: (a) update SPRINT.md's "Wave 0" row to acknowledge `ErrorLocation` authoring; (b) accept that the `CranelispError` reshape construction-site sweep crosses into consumer slices; (c) sequence Wave 2 consumer slices to close the transient compilation-broken window quickly.

This finding does NOT block Wave 0 from beginning — `/dev` (types) can begin authoring immediately. The finding is a sizing correction, not a structural blocker.

### 6.2 FIXME 0100 Phase 2 misstates the work

FIXME 0100 Phase 2 says "Move from `crates/cranelisp-types/src/` to `crates/cranelisp-backend/src/`: `CompilationError`, `GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver`". **None of those types are in `cranelisp-types` today.** Per §3.2 above, the actual work in those rows is **new authoring in `cranelisp-backend`**, not a relocation. The FIXME's framing is misleading.

This is editorial only — `/dev` (backend) authors the types in their own crate, and `/dev` (types) verifies they don't accidentally land in `cranelisp-types`. No source change to `cranelisp-types` is needed from FIXME 0100 Phase 2. `/sprint` may close FIXME 0100 with a note that Phase 2's wording was loose; backend slice rows 5 + 12+ implement the substance.

### 6.3 Removal count corrected: −9, not −13

The Phase 2 verdict estimated −13 types removed from `cranelisp-types`. Per §3.3, the corrected count is −9 — the four GOT-observer types + `CompilationError` are not currently in `cranelisp-types` (so not removed), and the typecheck-side relocations are 9 distinct types per the `pub use check::*` re-export block. Net types-crate delta is **−4 public types** (not the verdict's estimated −10).

This shifts `/qa` slice §1.1 row 7's expected `public-api.txt` diff for `cranelisp-types` from "substantial shrinkage" to "near-net-zero with substantial internal churn" — `/qa` should retune the baseline expectation accordingly, but the bound remains within the 26-test margin and the per-crate diff is still tractable for `/review`.

---

## 7. Cross-references

- `sprints/SPRINT.md` §"Architecture review (Phase 2)" — Wave 0 task, Phase 2 verdict, "Public-API impact + cranelisp-types deltas" §
- `design/arch/facades/types.md` — target-stating public surface for `cranelisp-types`
- `design/arch/decisions/0042-platform-error-adopts-error-location.md` — Decision 42 (`PlatformError` shape, `ErrorLocation` per variant)
- `design/arch/legacy/decisions/0039-per-defn-source-on-introspection.md` — Decision 39 (`ErrorLocation` + `LineCol`)
- `design/arch/legacy/decisions/0032-codestore-and-linkerstore-empty-marker.md` — Decision 32 (verified)
- `design/arch/fixmes/0098-dev-frontend-typecheck-int-resolutiongap-checkerror-expansionerror-migration.md` — FIXME 0098 (Phase 1 = `ResolutionGap` here)
- `design/arch/fixmes/0100-dev-relocate-single-consumer-types-to-originating-crates.md` — FIXME 0100 (Phase 1 = §3.1 typecheck migrate-out; Phase 2 = §3.2 / §6.2 misstatement)
- `design/arch/fixmes/0104-dev-types-platform-int-platformerror-adoption.md` — FIXME 0104 (Phase 1 = `PlatformError` + `CranelispError::Platform` here)
- `design/typecheck/implementation-slice-s66.md` — typecheck slice (Wave 2 consumer of `ResolutionGap`, `ErrorLocation`)
- `design/frontend/implementation-slice-s66.md` — frontend slice (Wave 2 consumer of `ResolutionGap`)
- `design/platform/implementation-slice-s66.md` — platform slice (Wave 2 consumer of `PlatformError`)
- `design/int/implementation-slice-s66.md` — int slice (Wave 2 consumer of `ResolutionGap`, `PlatformError`, `ErrorLocation`)
- `design/backend/implementation-slice-s66.md` — backend slice (Wave 2 consumer of `ErrorLocation`)
- `crates/cranelisp-types/src/lib.rs:29-67` — current public surface
- `crates/cranelisp-types/src/error.rs` — current `CranelispError` shape (target of §1 reshape)
- `crates/cranelisp-types/src/check.rs` — target of §3.1 migrate-out

---

## 8. Next skills

- **`/sprint`** — collates this plan into SPRINT.md Phase 3 / Phase 4 (Wave 0 sizing, Wave-2 ordering, finding §6.1 reshape acknowledgement)
- **`/dev` (types)** — Phase 5 executes §1 authoring + §3.1 migrate-out coordination. Reads this plan as the brief.
- **`/qa`** — Phase 5 regenerates `cranelisp-types/public-api.txt` baseline post-Wave-0 landing per `/qa` slice §1.1; expected diff per §6.3 (corrected from verdict estimate)
- **`/review`** — Phase 5 audits the Wave-0 PR against this plan + facade
