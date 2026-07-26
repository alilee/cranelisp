//! The ONE program-result owner (`design/int/result-owner.md`, FIXME 0745 /
//! arch ruling 9).
//!
//! Every successful execution result — REPL turn, `--run` entry `main`, and
//! (in CLIF form) the linked startup stub — crosses from generated typed code
//! into exactly one owner here. That owner carries the pair `(value, Type)`
//! from the driver through the result's **final observation**, and only then
//! releases it exactly once through backend's canonical per-concrete drop
//! glue.
//!
//! The binding protocol (§1):
//!
//! 1. the driver has already transferred the `Pure` payload and unwrapped
//!    `IO a` → `a`; this module refuses an `IO a` type outright so no caller
//!    can select `IO a` glue;
//! 2. the type is narrowed once with [`ConcreteType::from_type`] and then
//!    classified with backend's **public** [`HeapCategory::classify`] — the
//!    same predicate `request_if_owning` uses to decide whether an artifact row
//!    exists at all (§1.1). Int owns no second heap-type list;
//! 3. `NeverHeap | Value` ⇒ the inert arm; **no keyed lookup is attempted**,
//!    so a keyed miss on the owning arm is unambiguously a hard error;
//! 4. the owner is observed (REPL formats it, run/link converts it to the
//!    process exit code) while the word is live;
//! 5. finalization consumes the owner and invokes the resolved
//!    `extern "C" fn(i64)` glue exactly once.
//!
//! A resolved release target is **never** a bare address: it always travels
//! with the [`Code`](crate::code::Code) retention owner of the code that
//! produced the result (Principle 22 — published pointers have retention
//! owners). Recompilation replaces a `fresh_jit_drop_glues` row together with
//! its owner, and an armed owner holds its own clone, so a replacement can
//! never invalidate an armed target.

use dashmap::DashMap;

use cranelisp_backend::heap::HeapCategory;
use cranelisp_types::{
    CodeStore, ConcreteType, CranelispError, ErrorLocation, LinkerStore, LinkerSymbol,
    ModuleFullPath, Span, SymbolTable, Type,
};

/// A resolved release target: the canonical glue address **and** the `Code`
/// that keeps it mapped.
///
/// The `owner` field is never read — holding it *is* its job (Principle 22).
/// Constructing one of these without the guard is the shape `/review` rejects.
pub struct GlueTarget {
    /// The module-qualified canonical glue symbol
    /// (`cranelisp_types::drop_glue_symbol_name`). Kept so diagnostics and
    /// unit tests can assert the exact spelling, not merely "some pointer".
    symbol: LinkerSymbol,
    /// The finalized `extern "C" fn(i64)` address.
    address: usize,
    /// Retention guard for `address`. Never READ — holding it *is* its job
    /// (Principle 22: a raw function address without its `Arc<Jit>` /
    /// `Arc<Linker>` guard is not a valid release target). It is dropped only
    /// after the glue call returns.
    #[allow(dead_code)]
    owner: crate::code::Code,
}

impl GlueTarget {
    /// Pair a resolved address with the retention owner of the code that
    /// produced the result. The ONLY constructor.
    pub(crate) fn new(symbol: LinkerSymbol, address: usize, owner: crate::code::Code) -> Self {
        Self {
            symbol,
            address,
            owner,
        }
    }

    /// The canonical glue symbol this target calls. Production reads it
    /// through the `Debug` impl (diagnostics); the unit matrix asserts on it
    /// directly (§6: assert the exact module-qualified `LinkerSymbol`, not
    /// merely that some function pointer was called).
    #[cfg(test)]
    pub(crate) fn symbol(&self) -> &LinkerSymbol {
        &self.symbol
    }
}

impl std::fmt::Debug for GlueTarget {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("GlueTarget")
            .field("symbol", &self.symbol)
            .field("address", &format_args!("{:#x}", self.address))
            .finish_non_exhaustive()
    }
}

/// Resolve canonical per-concrete drop glue for an owning result.
///
/// Three code-housing situations need three adapters (§3): fresh JIT
/// ([`FreshJitGlueResolver`]), cache-hit relocation
/// ([`LinkerGlueResolver`]), and the linked startup stub (which resolves at
/// link time in CLIF, not through this trait). The *protocol* — observe, then
/// release exactly once — does not vary.
pub(crate) trait ResultGlueResolver {
    /// Resolve the release target for `ty`, produced by code homed in
    /// `module`. Absence is a hard error: classification already established
    /// that this result owns heap.
    fn resolve(
        &self,
        module: &ModuleFullPath,
        ty: &ConcreteType,
    ) -> Result<GlueTarget, CranelispError>;
}

/// A successful program result, owned end-to-end.
///
/// Construction consumes the clean driver outcome and its (already
/// IO-unwrapped) static type; observation borrows the value; finalization
/// consumes the owner. There is exactly one finalization chokepoint
/// ([`OwnedProgramResult::finalize`]), shared by the explicit release and the
/// defensive `Drop` backstop, so the glue can never run twice.
pub struct OwnedProgramResult {
    value: i64,
    ty: Type,
    /// `Some` ⇒ armed (an owning result with a resolved target).
    /// `None` ⇒ inert: either a scalar/value-layout result that needs no
    /// release, or an already-finalized owner.
    target: Option<GlueTarget>,
}

impl OwnedProgramResult {
    /// Construct the owner for a clean result.
    ///
    /// `ty` is the **transferred payload type** — the driver boundary
    /// (`pipeline::program_outcome_to_result`, `CompilerSession::trampoline`'s
    /// clean arm) performs the single `IO a` → `a` unwrap before this point.
    /// An `IO a` reaching here is an int invariant failure, not a licence to
    /// select `IO a` glue.
    ///
    /// `module` is the **emitting** module — the module whose
    /// `compile_to_module` produced the glue, i.e. the module that owns `main`
    /// / `__expr`. Never a source expression's module and never the most
    /// recently compiled function's.
    pub(crate) fn new<C, L>(
        value: i64,
        ty: Type,
        codegen_result_ty: Option<ConcreteType>,
        module: &ModuleFullPath,
        symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        resolver: &dyn ResultGlueResolver,
    ) -> Result<Self, CranelispError>
    where
        C: CodeStore,
        L: LinkerStore,
    {
        if ty.is_io() {
            return Err(Self::invariant(format!(
                "program result reached the result owner still wrapped in `{ty}` — the driver \
                 boundary must transfer the `Pure` payload and unwrap `IO a` exactly once; \
                 result glue is selected for the INNER type, never for `IO a`"
            )));
        }
        // (1) the release key.
        let concrete = release_key(codegen_result_ty, &ty, module)?;
        // (2) classify with the SAME predicate backend's `request_if_owning`
        // uses (§1.1). Absence from the artifact projection is ambiguous on its
        // face, so int must ask this question BEFORE it demands a key.
        let target = match HeapCategory::classify(&concrete, Some(symbol_tables)) {
            // (3) inert arm — zero map reads.
            HeapCategory::NeverHeap | HeapCategory::Value => None,
            // (4) owning arm — `Mixed` included: glue exists for it and its
            // body's `guard_nullary` handles the bare-tag case. Int does NOT
            // replicate that guard.
            HeapCategory::AlwaysHeap | HeapCategory::Mixed => {
                Some(resolver.resolve(module, &concrete)?)
            }
        };
        Ok(Self { value, ty, target })
    }

    /// An INERT owner over a plain word — no release target, so finalization
    /// is a typed no-op. Test-only: production owners are always built through
    /// [`Self::new`], which classifies before it decides.
    #[cfg(test)]
    pub(crate) fn inert(value: i64, ty: Type) -> Self {
        Self {
            value,
            ty,
            target: None,
        }
    }

    /// Borrow the owned word for observation.
    ///
    /// This is a **read**, not a transfer: the caller may format it, convert
    /// it, or hand it to a display routine, but must not release it, store it
    /// past the owner's lifetime, or pass it to a second owner.
    pub fn observed_value(&self) -> i64 {
        self.value
    }

    /// The result's static (IO-unwrapped) type.
    pub fn ty(&self) -> &Type {
        &self.ty
    }

    /// Whether this result carries a release target (owning) or is inert.
    #[cfg(test)]
    pub(crate) fn is_armed(&self) -> bool {
        self.target.is_some()
    }

    /// The resolved target, for diagnostics and unit assertions.
    #[cfg(test)]
    pub(crate) fn target(&self) -> Option<&GlueTarget> {
        self.target.as_ref()
    }

    /// Observe the result as a process exit code (§1 step 3): an `Int` result
    /// narrows to `i32`; **every other type yields 0**. `--run` and the linked
    /// startup stub apply the identical rule — a divergence here is a
    /// `mode-divergence` defect.
    pub fn exit_code(&self) -> i32 {
        if result_is_exit_code(&self.ty) {
            self.value as i32
        } else {
            0
        }
    }

    /// The finalization chokepoint: release the word exactly once, then
    /// disarm. Shared by [`Self::release`], [`Self::release_in_place`], and
    /// the `Drop` backstop, so no path can double-release.
    fn finalize(&mut self) {
        let Some(target) = self.target.take() else {
            return;
        };
        // SAFETY: `target.address` is a finalized `extern "C" fn(i64)` — either
        // the `jit_address` backend projected for this exact concrete type in
        // this exact module, or the symbol the entry's own `Linker` resolved
        // under the same canonical spelling. `target.owner` is the retention
        // guard for the code housing it and is alive for the whole call (it is
        // dropped at the end of this scope, after the call returns). The word
        // is the program result, whose ownership transferred to this owner at
        // construction and is transferred to the callee here.
        unsafe {
            let glue: extern "C" fn(i64) =
                std::mem::transmute::<usize, extern "C" fn(i64)>(target.address);
            glue(self.value);
        }
        drop(target);
    }

    /// Release the result and consume the owner. The normal finalization path.
    pub fn release(mut self) {
        self.finalize();
    }

    /// Release the result in place, leaving the owner disarmed.
    ///
    /// For the carriers that must keep the `(value, ty)` pair reachable for
    /// bookkeeping after the observation completes (the REPL's `EvalResult`).
    /// After this returns the word is dead — no caller may read it again.
    pub fn release_in_place(&mut self) {
        self.finalize();
    }

    fn invariant(message: String) -> CranelispError {
        CranelispError::CodegenError {
            message,
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    }
}

impl Drop for OwnedProgramResult {
    /// Defensive backstop (§2): an owner that unwinds — or that a future
    /// caller forgets to finalize — still releases exactly once, through the
    /// same chokepoint and the same disarm state. It is **not** a second
    /// normal release path: every seam finalizes explicitly, and the ordering
    /// contract (observe, THEN release) is the explicit call's job.
    fn drop(&mut self) {
        self.finalize();
    }
}

impl std::fmt::Debug for OwnedProgramResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OwnedProgramResult")
            .field("value", &self.value)
            .field("ty", &self.ty)
            .field("target", &self.target)
            .finish()
    }
}

/// The **release key** for a program result — the `ConcreteType` int demands
/// glue under.
///
/// It comes, in order of authority:
///
/// 1. from the result-producing entry's own `codegen_view` body type — the
///    SAME `ConcreteType` backend computed its result roots from
///    (`compile_to_module`'s `result_roots`, which strips the `IO` head of an
///    `IO a` body exactly as this does). Taking the key from the same read
///    that produced the code pointer is the §4.3 rule, and it makes int's
///    classification agree with backend's `request_if_owning` **by
///    construction** instead of by a second derivation (§4.1 — never re-derive
///    backend's type encoding);
/// 2. failing that, by narrowing the observed static `Type`. A narrowing
///    failure here is the §5 hard invariant error: never a shallow release,
///    never a silent leak.
///
/// **Why (1) is not merely an optimisation** (S118 W4, `/dev`): the design's
/// §1.1/§5 assumed every clean typed-exit result type is concrete. It is not —
/// `repl/spec.md` §1.5's empty-`Vec` display (`[]` ⇒ `(Vec t1)`) and a bare
/// polymorphic nullary constructor (`None` ⇒ `(Option t2)`) are spec-required
/// REPL displays whose observed `Type` carries a residual var. Backend already
/// resolves those through `MonoExpr::lenient_from_expr`, and int must reach the
/// same verdict backend reached, not a second one. FIXME 0892 carries this
/// back to `/design`.
fn release_key(
    codegen_result_ty: Option<ConcreteType>,
    ty: &Type,
    module: &ModuleFullPath,
) -> Result<ConcreteType, CranelispError> {
    if let Some(codegen_ty) = codegen_result_ty {
        return Ok(strip_io_head(codegen_ty));
    }
    ConcreteType::from_type(ty).map_err(|why| {
        OwnedProgramResult::invariant(format!(
            "program result type `{ty}` is not concrete at the typed exit of module \
             `{module}` ({why:?}), and the result-producing entry published no codegen \
             view to key on; the result cannot be released type-directedly"
        ))
    })
}

/// Whether the result word IS the process exit code (§1 step 3): an `Int`
/// result narrows to `i32`; **every other type yields 0**. The single
/// statement of that rule — `--run` reads it through
/// [`OwnedProgramResult::exit_code`], the linked startup stub bakes it through
/// [`startup_result_exit`]. A divergence between the two is a
/// `mode-divergence` defect, so there is one predicate.
pub(crate) fn result_is_exit_code(ty: &Type) -> bool {
    *ty == Type::Int
}

/// What the linked startup stub must do with `main`'s result (§3.3).
///
/// The stub resolves its release target at LINK time, through an ordinary
/// relocation, so it needs no `Code` guard: executable text lifetime keeps both
/// caller and relocated glue live until `exit`. Everything else — the
/// classification, the canonical symbol spelling, and the exit-code rule — is
/// shared with the two runtime adapters.
#[derive(Debug)]
pub(crate) struct StartupResultExit {
    /// `true` ⇒ the stub narrows the result word to the process exit code;
    /// `false` ⇒ it exits 0 (see [`result_is_exit_code`]).
    pub(crate) result_is_exit_code: bool,
    /// The canonical glue symbol to import, relocate, and call exactly once —
    /// after the exit-code conversion, before `exit`. `None` for a
    /// scalar/value-layout result, in which case the stub is byte-identical to
    /// the pre-0745 one.
    pub(crate) release_symbol: Option<LinkerSymbol>,
}

/// Classify `main`'s **inner** result type for the linked startup stub.
///
/// `inner_ty` is the `a` of `main : (Fn [] (IO a))` — `validate_main` has
/// already guaranteed that shape. `codegen_result_ty` is `main`'s
/// `codegen_view` body type when the entry published one (see
/// [`release_key`]); a non-concrete inner type with no codegen view is a
/// **located link-time error naming the module and the type**, never a silent
/// skip (§3.3 step 4).
pub(crate) fn startup_result_exit<C, L>(
    inner_ty: &Type,
    codegen_result_ty: Option<ConcreteType>,
    module: &ModuleFullPath,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Result<StartupResultExit, CranelispError>
where
    C: CodeStore,
    L: LinkerStore,
{
    let key = release_key(codegen_result_ty, inner_ty, module)?;
    let release_symbol = match HeapCategory::classify(&key, Some(symbol_tables)) {
        HeapCategory::NeverHeap | HeapCategory::Value => None,
        HeapCategory::AlwaysHeap | HeapCategory::Mixed => {
            Some(cranelisp_types::drop_glue_symbol_name(module, &key))
        }
    };
    Ok(StartupResultExit {
        result_is_exit_code: result_is_exit_code(inner_ty),
        release_symbol,
    })
}

/// `IO a` ⇒ `a`; anything else unchanged. The single int-side statement of the
/// result-root rule backend applies at `compile_to_module` when it pre-requests
/// glue for every concrete owning result root "including the inner `a` of
/// `IO a`" (§3.1). Run, REPL and the linked stub all key through here.
fn strip_io_head(ty: ConcreteType) -> ConcreteType {
    match ty {
        ConcreteType::ADT(ref name, ref args)
            if name.module.as_ref() == "primitives"
                && name.name.as_ref() == "IO"
                && !args.is_empty() =>
        {
            args[0].clone()
        }
        other => other,
    }
}

// ---------------------------------------------------------------------------
// The three target-resolution adapters (§3)
// ---------------------------------------------------------------------------

/// The session's release-target resolver, selected by **the `Code` that owns
/// the code which produced the result** (§3.2 step 3 — the unifying rule
/// across the fresh-JIT and cache-hit adapters).
///
/// Selection is infallible so the inert arm pays nothing: a result that needs
/// no release never asks, and [`Self::NoCodeOwner`] only surfaces as an error
/// when an owning result actually demands a target.
pub(crate) enum SessionGlueResolver<'a> {
    /// Fresh JIT (`--run`, REPL, post-cache-miss): read the row S117's publish
    /// gate installed, `{artifact, owner}` as one value.
    FreshJit {
        glues: &'a DashMap<(ModuleFullPath, ConcreteType), crate::worker::FreshJitDropGlue>,
    },
    /// Cache hit: the exported glue body is already in the loaded object.
    /// Derive the canonical symbol and resolve it once through the
    /// result-producing entry's own `Linker`.
    Cached {
        linker: std::sync::Arc<cranelisp_backend::cache::linker::Linker>,
    },
    /// No resolvable retention owner on the result-producing entry — it
    /// carries no `Code`, or a `Code` variant this adapter set does not know
    /// (`Code` is `#[non_exhaustive]`; a new housing needs a new adapter, not
    /// a silent no-release fallback).
    NoCodeOwner { reason: String },
}

impl<'a> SessionGlueResolver<'a> {
    /// Select the adapter from the result-producing entry's `Code`.
    ///
    /// A `Code::Linker` result NEVER consults a `Code::Jit` row and vice
    /// versa: the release target's retention owner is the same `Code` that
    /// owns the code which produced the result.
    pub(crate) fn for_result_code(
        code: Option<&crate::code::Code>,
        glues: &'a DashMap<(ModuleFullPath, ConcreteType), crate::worker::FreshJitDropGlue>,
    ) -> Self {
        match code {
            Some(crate::code::Code::Jit(_)) => SessionGlueResolver::FreshJit { glues },
            Some(crate::code::Code::Linker(linker)) => SessionGlueResolver::Cached {
                linker: std::sync::Arc::clone(linker),
            },
            None => SessionGlueResolver::NoCodeOwner {
                reason: "the result-producing entry carries no `Code`".to_string(),
            },
            Some(other) => SessionGlueResolver::NoCodeOwner {
                reason: format!(
                    "the result-producing entry's code housing `{other:?}` has no \
                     release-target adapter"
                ),
            },
        }
    }
}

impl ResultGlueResolver for SessionGlueResolver<'_> {
    fn resolve(
        &self,
        module: &ModuleFullPath,
        ty: &ConcreteType,
    ) -> Result<GlueTarget, CranelispError> {
        match self {
            SessionGlueResolver::FreshJit { glues } => resolve_fresh_jit(glues, module, ty),
            SessionGlueResolver::Cached { linker } => resolve_cached(linker, module, ty),
            SessionGlueResolver::NoCodeOwner { reason } => {
                Err(OwnedProgramResult::invariant(format!(
                    "owning program result of type `{ty:?}` in module `{module}` has no code \
                     lifetime owner ({reason}) — the release target's retention owner is the \
                     same `Code` that owns the code which produced the result"
                )))
            }
        }
    }
}

/// §3.1 — the fresh-JIT adapter. **One** keyed read; the row is cloned WHOLE
/// (artifact *and* owner); the raw `jit_address` is never stored without its
/// guard. There is no symbol scan and no compile-after-the-fact fallback.
fn resolve_fresh_jit(
    glues: &DashMap<(ModuleFullPath, ConcreteType), crate::worker::FreshJitDropGlue>,
    module: &ModuleFullPath,
    ty: &ConcreteType,
) -> Result<GlueTarget, CranelispError> {
    // ONE keyed read, and the row is cloned WHOLE before the guard drops — the
    // artifact and its owner never separate.
    let row = glues
        .get(&(module.clone(), ty.clone()))
        .map(|row| row.clone())
        .map(|row| (row.artifact.symbol, row.artifact.jit_address, row.owner));
    fresh_jit_target(row, module, ty)
}

/// The fresh-JIT adapter's decision core: the four polarities of a published
/// `{artifact, owner}` pair. Split from the keyed read so every polarity is
/// unit-testable without a live JIT batch (`DropGlueArtifact` is
/// `#[non_exhaustive]` and cannot be synthesised outside backend).
fn fresh_jit_target(
    row: Option<(LinkerSymbol, Option<usize>, crate::code::Code)>,
    module: &ModuleFullPath,
    ty: &ConcreteType,
) -> Result<GlueTarget, CranelispError> {
    let expected = cranelisp_types::drop_glue_symbol_name(module, ty);
    let Some((symbol, jit_address, owner)) = row else {
        return Err(OwnedProgramResult::invariant(format!(
            "no fresh-JIT drop glue published for owning result type `{ty:?}` in module \
             `{module}` (expected symbol `{expected}`); classification says this result owns \
             heap, so an absent artifact row is an integration failure, not a no-op"
        )));
    };
    if symbol != expected {
        return Err(OwnedProgramResult::invariant(format!(
            "fresh-JIT drop-glue symbol disagrees with the canonical spelling for module \
             `{module}` type `{ty:?}`: artifact says `{symbol}`, \
             `drop_glue_symbol_name` says `{expected}`"
        )));
    }
    let Some(address) = jit_address else {
        return Err(OwnedProgramResult::invariant(format!(
            "fresh-JIT drop glue `{expected}` for module `{module}` carries no finalized \
             address (object-mode polarity leaking into a JIT result path)"
        )));
    };
    Ok(GlueTarget::new(symbol, address, owner))
}

/// §3.2 — the cache-hit adapter. The object already contains the exported glue
/// body (`Linkage::Export` through the same `compile_to_module` the object path
/// uses), so int derives the canonical symbol and resolves it once. A miss is a
/// cache-LOAD failure; private glue is never synthesised to repair it.
fn resolve_cached(
    linker: &std::sync::Arc<cranelisp_backend::cache::linker::Linker>,
    module: &ModuleFullPath,
    ty: &ConcreteType,
) -> Result<GlueTarget, CranelispError> {
    let symbol = cranelisp_types::drop_glue_symbol_name(module, ty);
    let address = linker.get_symbol(symbol.as_ref()).map_err(|e| {
        OwnedProgramResult::invariant(format!(
            "cache-hit drop glue `{symbol}` for owning result type `{ty:?}` in module \
             `{module}` is missing from the loaded object ({e}); this is a cache-load \
             failure, not a cache miss to repair with private glue"
        ))
    })?;
    if address.is_null() {
        return Err(OwnedProgramResult::invariant(format!(
            "cache-hit drop glue `{symbol}` for module `{module}` resolved to a null address"
        )));
    }
    Ok(GlueTarget::new(
        symbol,
        address as usize,
        crate::code::Code::linker(std::sync::Arc::clone(linker)),
    ))
}

// ---------------------------------------------------------------------------
// Unit tests — §6 rows 1–3 (owner constructor + classification, fresh-JIT
// target resolution, cache-hit resolution)
// ---------------------------------------------------------------------------

#[cfg(test)]
pub(crate) mod test_support {
    use super::*;
    use std::sync::{Arc, Mutex, OnceLock};

    /// Events recorded by the test glue, in call order.
    pub(crate) fn events() -> &'static Mutex<Vec<String>> {
        static EVENTS: OnceLock<Mutex<Vec<String>>> = OnceLock::new();
        EVENTS.get_or_init(|| Mutex::new(Vec::new()))
    }

    pub(crate) fn record(event: impl Into<String>) {
        events()
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(event.into());
    }

    pub(crate) fn take_events() -> Vec<String> {
        std::mem::take(&mut *events().lock().unwrap_or_else(|e| e.into_inner()))
    }

    /// A real `extern "C" fn(i64)` standing in for canonical glue, so the
    /// owner's transmute-and-call path is exercised for real.
    pub(crate) extern "C" fn recording_glue(value: i64) {
        record(format!("glue({value})"));
    }

    /// A `Code` retention guard for tests. Real `Arc<Jit>` — the owner must
    /// never hold a bare address, so tests must not either.
    // `Arc<Jit>` is not auto-`Sync` (JITModule's interior mutability); `Code`
    // asserts `Send`/`Sync` manually for the read-only post-finalize state it
    // holds. Same shape as `src/code.rs`'s own fixture.
    #[allow(clippy::arc_with_non_send_sync)]
    pub(crate) fn test_code() -> crate::code::Code {
        let empty: cranelisp_types::SymbolTables<crate::code::Code, ()> = DashMap::new();
        crate::code::Code::jit(Arc::new(
            cranelisp_backend::jit::Jit::new(&empty).expect("Jit::new must succeed"),
        ))
    }

    pub(crate) fn test_target(symbol: &str) -> GlueTarget {
        GlueTarget::new(
            LinkerSymbol::from(symbol),
            recording_glue as extern "C" fn(i64) as usize,
            test_code(),
        )
    }

    /// A resolver that records the key it was asked for and answers with the
    /// recording glue.
    pub(crate) struct RecordingResolver {
        pub(crate) keys: Mutex<Vec<(ModuleFullPath, ConcreteType)>>,
    }

    impl RecordingResolver {
        pub(crate) fn new() -> Self {
            Self {
                keys: Mutex::new(Vec::new()),
            }
        }
    }

    impl ResultGlueResolver for RecordingResolver {
        fn resolve(
            &self,
            module: &ModuleFullPath,
            ty: &ConcreteType,
        ) -> Result<GlueTarget, CranelispError> {
            self.keys
                .lock()
                .unwrap_or_else(|e| e.into_inner())
                .push((module.clone(), ty.clone()));
            Ok(test_target(
                cranelisp_types::drop_glue_symbol_name(module, ty).as_ref(),
            ))
        }
    }

    /// A resolver that must never be called (the inert arm's negative).
    pub(crate) struct PoisonResolver;

    impl ResultGlueResolver for PoisonResolver {
        fn resolve(
            &self,
            module: &ModuleFullPath,
            ty: &ConcreteType,
        ) -> Result<GlueTarget, CranelispError> {
            panic!("scalar/value arm must attempt NO keyed lookup (asked {module}/{ty:?})");
        }
    }

    /// Symbol tables carrying a sum-shaped `deftype` under the production
    /// ctor-as-Def shape (S79 Option 3a): a `TypeDef` entry naming the
    /// constructors, plus one `Def { kind: Constructor { field_count } }` per
    /// constructor — the exact shape `HeapCategory::classify_adt` walks.
    /// `ctors` is `(name, field_count)`.
    pub(crate) fn tables_with_adt(
        module: &ModuleFullPath,
        type_name: &str,
        ctors: &[(&str, usize)],
    ) -> cranelisp_types::SymbolTables<crate::code::Code, ()> {
        use cranelisp_types::{
            DefKind, FQTypeName, ModuleEntry, Scheme, Symbol, TypeDefInfo, TypeName, Visibility,
        };
        let fqtn = FQTypeName::new(module.clone(), TypeName::from(type_name));
        let tables: cranelisp_types::SymbolTables<crate::code::Code, ()> = DashMap::new();
        let mut table = SymbolTable::<crate::code::Code, ()>::new_with_params(module.clone());
        table.insert(
            Symbol::from(type_name),
            ModuleEntry::TypeDef {
                info: TypeDefInfo {
                    name: fqtn.clone(),
                    type_params: Vec::new(),
                    constructors: ctors.iter().map(|(name, _)| Symbol::from(*name)).collect(),
                },
                visibility: Visibility::Public,
                docstring: None,
            },
        );
        for (tag, (name, field_count)) in ctors.iter().enumerate() {
            table.insert(
                Symbol::from(*name),
                ModuleEntry::Def {
                    scheme: Scheme {
                        type_vars: Vec::new(),
                        constraints: std::collections::HashMap::new(),
                        ty: Type::ADT(fqtn.clone(), Vec::new()),
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: (0..*field_count)
                        .map(|i| Symbol::from(format!("f{i}")))
                        .collect(),
                    kind: Box::new(DefKind::Constructor {
                        got_slot: 0,
                        type_name: fqtn.clone(),
                        tag,
                        field_count: *field_count,
                        internal: false,
                        type_def: None,
                        mode_summary: None,
                    }),
                    callees: Vec::new(),
                    trait_origin: None,
                    seq: 0,
                    ast: None,
                    codegen_view: None,
                    code: None,
                    value_use: false,
                },
            );
        }
        tables.insert(module.clone(), table);
        tables
    }
}

#[cfg(test)]
mod tests {
    use super::test_support::*;
    use super::*;
    use cranelisp_types::{FQTypeName, TypeName};

    fn user() -> ModuleFullPath {
        ModuleFullPath::from("user")
    }

    fn empty_tables() -> cranelisp_types::SymbolTables<crate::code::Code, ()> {
        DashMap::new()
    }

    fn io_of(inner: Type) -> Type {
        Type::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO")),
            vec![inner],
        )
    }

    // spec: design/int/result-owner.md §1.1 — a scalar result takes the inert
    // arm and performs ZERO keyed lookups (the `PoisonResolver` panics if a
    // lookup is attempted).
    #[test]
    fn scalar_int_result_is_inert_and_reads_no_map() {
        let owner = OwnedProgramResult::new(
            7,
            Type::Int,
            None,
            &user(),
            &empty_tables(),
            &PoisonResolver,
        )
        .expect("Int narrows and classifies NeverHeap");
        assert!(!owner.is_armed(), "Int needs no release target");
        assert_eq!(owner.exit_code(), 7, "Int narrows to the process exit code");
        let _ = take_events();
        owner.release();
        assert!(
            take_events().is_empty(),
            "the inert arm must invoke no glue at all"
        );
    }

    // spec: design/int/result-owner.md §1 step 3 — every non-`Int` result
    // yields exit code 0, whether owning or not.
    #[test]
    fn non_int_results_convert_to_exit_code_zero() {
        for ty in [Type::Bool, Type::Float] {
            let owner = OwnedProgramResult::new(
                1,
                ty.clone(),
                None,
                &user(),
                &empty_tables(),
                &PoisonResolver,
            )
            .expect("scalar narrows");
            assert_eq!(owner.exit_code(), 0, "{ty} must convert to exit code 0");
        }
        let _ = take_events();
        let resolver = RecordingResolver::new();
        let owner =
            OwnedProgramResult::new(99, Type::String, None, &user(), &empty_tables(), &resolver)
                .expect("String narrows");
        assert_eq!(owner.exit_code(), 0, "a String result exits 0");
        owner.release();
        assert_eq!(take_events(), vec!["glue(99)".to_string()]);
    }

    // spec: design/int/result-owner.md §1.1 — `String` is `AlwaysHeap`, so the
    // owning arm resolves ONE target keyed by (emitting module, ConcreteType)
    // and the release calls it exactly once with the owned word.
    #[test]
    fn string_result_releases_once_through_the_keyed_target() {
        let _ = take_events();
        let resolver = RecordingResolver::new();
        let owner = OwnedProgramResult::new(
            0xbeef,
            Type::String,
            None,
            &user(),
            &empty_tables(),
            &resolver,
        )
        .expect("String narrows and classifies AlwaysHeap");
        assert!(owner.is_armed());
        assert_eq!(
            owner.target().expect("armed").symbol().as_ref(),
            cranelisp_types::drop_glue_symbol_name(&user(), &ConcreteType::String).as_ref(),
            "the target must carry the module-qualified canonical spelling"
        );
        assert_eq!(
            &*resolver.keys.lock().unwrap(),
            &[(user(), ConcreteType::String)],
            "exactly one keyed lookup, on the emitting module"
        );
        assert!(take_events().is_empty(), "no glue call before observation");
        owner.release();
        assert_eq!(
            take_events(),
            vec!["glue(48879)".to_string()],
            "release invokes the target exactly once with the owned word"
        );
    }

    // spec: design/int/result-owner.md §6 — the recorded event sequence pins
    // observe-before-release ordering AND exact-once release.
    #[test]
    fn observation_completes_before_the_single_glue_call() {
        let _ = take_events();
        let resolver = RecordingResolver::new();
        let mut owner =
            OwnedProgramResult::new(5, Type::String, None, &user(), &empty_tables(), &resolver)
                .expect("String narrows");
        record("observe-start");
        record(format!("observe-read({})", owner.observed_value()));
        record(format!("observe-done(exit={})", owner.exit_code()));
        owner.release_in_place();
        record("guard-drop");
        drop(owner);
        assert_eq!(
            take_events(),
            vec![
                "observe-start".to_string(),
                "observe-read(5)".to_string(),
                "observe-done(exit=0)".to_string(),
                "glue(5)".to_string(),
                "guard-drop".to_string(),
            ],
            "observation must complete before the release, and the release must \
             happen exactly once even though the owner is later dropped"
        );
    }

    // spec: design/int/result-owner.md §2/§5 — the `Drop` backstop releases an
    // owner that was never explicitly finalized, through the SAME chokepoint,
    // so a forgotten seam leaks nothing and a finalized one never doubles.
    #[test]
    fn drop_backstop_releases_once_and_never_doubles() {
        let _ = take_events();
        let resolver = RecordingResolver::new();
        {
            let _owner = OwnedProgramResult::new(
                11,
                Type::String,
                None,
                &user(),
                &empty_tables(),
                &resolver,
            )
            .expect("String narrows");
        }
        assert_eq!(
            take_events(),
            vec!["glue(11)".to_string()],
            "the backstop releases an un-finalized owner"
        );
        {
            let owner = OwnedProgramResult::new(
                12,
                Type::String,
                None,
                &user(),
                &empty_tables(),
                &resolver,
            )
            .expect("String narrows");
            owner.release();
        }
        assert_eq!(
            take_events(),
            vec!["glue(12)".to_string()],
            "an explicitly released owner must not be released again on drop"
        );
    }

    // spec: design/int/result-owner.md §1.1 — value `0` is a legitimate owned
    // word (an empty String / null-shaped payload is the glue's problem, not
    // int's) and must still be released.
    #[test]
    fn value_zero_is_a_valid_owned_word() {
        let _ = take_events();
        let resolver = RecordingResolver::new();
        let owner =
            OwnedProgramResult::new(0, Type::String, None, &user(), &empty_tables(), &resolver)
                .expect("String narrows");
        owner.release();
        assert_eq!(take_events(), vec!["glue(0)".to_string()]);
    }

    // spec: design/int/result-owner.md §1.1 — `HeapCategory::Mixed` (an ADT
    // with both nullary and data constructors) is an OWNING result: glue
    // exists for it and its `guard_nullary` handles the bare-tag case. Int
    // must not fork that guard by treating Mixed as inert.
    #[test]
    fn mixed_category_adt_is_owning_not_inert() {
        let _ = take_events();
        let tables = tables_with_adt(&user(), "Shape", &[("Nil", 0), ("Box", 1)]);
        let ty = Type::ADT(FQTypeName::new(user(), TypeName::from("Shape")), Vec::new());
        let concrete = ConcreteType::from_type(&ty).expect("concrete");
        assert_eq!(
            HeapCategory::classify(&concrete, Some(&tables)),
            HeapCategory::Mixed,
            "fixture must actually be Mixed"
        );
        let resolver = RecordingResolver::new();
        let owner =
            OwnedProgramResult::new(3, ty, None, &user(), &tables, &resolver).expect("ADT narrows");
        assert!(owner.is_armed(), "Mixed is an owning result");
        owner.release();
        assert_eq!(take_events(), vec!["glue(3)".to_string()]);
    }

    // spec: design/int/result-owner.md §1.1 — an all-nullary ADT classifies
    // `NeverHeap` (bare tags) and takes the inert arm with no keyed lookup.
    #[test]
    fn all_nullary_adt_is_inert() {
        let tables = tables_with_adt(&user(), "Flag", &[("On", 0), ("Off", 0)]);
        let ty = Type::ADT(FQTypeName::new(user(), TypeName::from("Flag")), Vec::new());
        let owner = OwnedProgramResult::new(1, ty, None, &user(), &tables, &PoisonResolver)
            .expect("nullary ADT narrows");
        assert!(!owner.is_armed());
    }

    // spec: design/int/result-owner.md §4.4 — the owner selects glue for the
    // INNER type `a`, never for `IO a`. The driver boundary owns the single
    // unwrap; an `IO a` arriving here is an invariant failure, not a licence.
    #[test]
    fn io_type_is_rejected_and_never_selects_io_glue() {
        let resolver = RecordingResolver::new();
        let err = OwnedProgramResult::new(
            1,
            io_of(Type::String),
            None,
            &user(),
            &empty_tables(),
            &resolver,
        )
        .expect_err("an un-transferred IO result is an invariant failure");
        assert!(
            err.to_string().contains("never for `IO a`"),
            "the diagnostic must name the rule: {err}"
        );
        assert!(
            resolver.keys.lock().unwrap().is_empty(),
            "no glue may be keyed for `IO a`"
        );
    }

    // spec: design/int/result-owner.md §4.3 — when the result-producing entry
    // published a codegen view, THAT `ConcreteType` is the release key. It is
    // the same key backend computed its result root from, so int's
    // classification agrees with `request_if_owning` by construction rather
    // than by a second derivation of backend's type encoding.
    #[test]
    fn codegen_view_type_is_the_release_key_not_the_observed_type() {
        let _ = take_events();
        let resolver = RecordingResolver::new();
        // The observed type is non-concrete (`repl/spec.md` §1.5's empty-Vec
        // display), but the entry's codegen view keyed on `Int` — backend
        // therefore emitted NO glue for it, and int must reach that same
        // verdict instead of hard-erroring on the display type.
        let owner = OwnedProgramResult::new(
            0,
            Type::TyConApp(1, vec![Type::Var(2)]),
            Some(ConcreteType::Int),
            &user(),
            &empty_tables(),
            &PoisonResolver,
        )
        .expect("the codegen key decides; the display type does not");
        assert!(!owner.is_armed(), "backend emitted no glue for this root");
        assert!(resolver.keys.lock().unwrap().is_empty());
        assert!(take_events().is_empty());
    }

    // spec: design/int/result-owner.md §3.1 — the release key strips the `IO`
    // head exactly as backend's `result_roots` pre-pass does, so `IO String`
    // selects `String` glue and never `IO String` glue.
    #[test]
    fn codegen_view_io_head_is_stripped_to_the_inner_type() {
        let _ = take_events();
        let resolver = RecordingResolver::new();
        let io_string = ConcreteType::ADT(
            FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO")),
            vec![ConcreteType::String],
        );
        let owner = OwnedProgramResult::new(
            3,
            Type::String,
            Some(io_string),
            &user(),
            &empty_tables(),
            &resolver,
        )
        .expect("IO String keys on String");
        assert_eq!(
            &*resolver.keys.lock().unwrap(),
            &[(user(), ConcreteType::String)],
            "the INNER type is the key — never `IO a`"
        );
        owner.release();
        assert_eq!(take_events(), vec!["glue(3)".to_string()]);
    }

    // spec: design/int/result-owner.md §5 — a non-concrete type at the typed
    // exit is a hard invariant error naming the module and the type; it is
    // never a shallow release and never a silent leak.
    #[test]
    fn non_concrete_type_is_a_hard_error_naming_module_and_type() {
        let resolver = RecordingResolver::new();
        let err =
            OwnedProgramResult::new(1, Type::Var(7), None, &user(), &empty_tables(), &resolver)
                .expect_err("a residual type var cannot be released type-directedly");
        let text = err.to_string();
        assert!(text.contains("user"), "must name the module: {text}");
        assert!(text.contains("not concrete"), "must name the fault: {text}");
        assert!(resolver.keys.lock().unwrap().is_empty());
    }

    // spec: design/int/result-owner.md §5 — a resolver failure propagates as a
    // hard error with the owner never armed; nothing is released.
    #[test]
    fn resolver_failure_propagates_and_releases_nothing() {
        struct Failing;
        impl ResultGlueResolver for Failing {
            fn resolve(
                &self,
                _module: &ModuleFullPath,
                _ty: &ConcreteType,
            ) -> Result<GlueTarget, CranelispError> {
                Err(CranelispError::CodegenError {
                    message: "no glue row".into(),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })
            }
        }
        let _ = take_events();
        let err =
            OwnedProgramResult::new(1, Type::String, None, &user(), &empty_tables(), &Failing)
                .expect_err("an unresolvable owning result is a hard error");
        assert!(err.to_string().contains("no glue row"));
        assert!(take_events().is_empty(), "nothing may be released");
    }

    // spec: design/int/result-owner.md §1.1 — a closure result (`Fn`)
    // classifies `AlwaysHeap` and is released through its own concrete glue.
    #[test]
    fn closure_result_is_owning() {
        let _ = take_events();
        let resolver = RecordingResolver::new();
        let ty = Type::Fn(vec![Type::Int], Box::new(Type::Int));
        let owner = OwnedProgramResult::new(0x1234, ty, None, &user(), &empty_tables(), &resolver)
            .expect("Fn narrows");
        assert!(owner.is_armed(), "closures are heap-allocated");
        owner.release();
        assert_eq!(take_events(), vec!["glue(4660)".to_string()]);
    }

    // -----------------------------------------------------------------------
    // §6 row 2 — fresh-JIT target resolution
    // -----------------------------------------------------------------------

    fn nested_ty() -> ConcreteType {
        ConcreteType::ADT(
            FQTypeName::new(user(), TypeName::from("Branch")),
            vec![ConcreteType::ADT(
                FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Vec")),
                vec![ConcreteType::String],
            )],
        )
    }

    // spec: design/int/result-owner.md §3.1 — a published `{artifact, owner}`
    // row resolves to a target carrying the canonical module-qualified symbol,
    // the finalized address, AND the batch's `Code` retention owner. Nested
    // concrete types key exactly like scalar ones.
    #[test]
    fn fresh_jit_row_resolves_symbol_address_and_owner() {
        for ty in [ConcreteType::String, nested_ty()] {
            let symbol = cranelisp_types::drop_glue_symbol_name(&user(), &ty);
            let target = fresh_jit_target(
                Some((symbol.clone(), Some(0xdead_beef), test_code())),
                &user(),
                &ty,
            )
            .expect("a well-formed row resolves");
            assert_eq!(
                target.symbol(),
                &symbol,
                "module-qualified canonical symbol"
            );
            assert!(
                format!("{target:?}").contains("deadbeef"),
                "the finalized address must be carried: {target:?}"
            );
        }
    }

    // spec: design/int/result-owner.md §3.1 step 4 / §5 — an ABSENT row for a
    // type classification already called owning is a hard integration error.
    // There is no ambient symbol scan and no compile-after-the-fact fallback.
    #[test]
    fn fresh_jit_absent_key_is_a_hard_error_naming_the_expected_symbol() {
        let err = fresh_jit_target(None, &user(), &ConcreteType::String)
            .expect_err("an absent row must not be silently tolerated");
        let text = err.to_string();
        assert!(
            text.contains(
                cranelisp_types::drop_glue_symbol_name(&user(), &ConcreteType::String).as_ref()
            ),
            "must name the expected symbol: {text}"
        );
        assert!(text.contains("integration failure"), "{text}");
    }

    // spec: design/int/result-owner.md §5 — `jit_address: None` on a fresh-JIT
    // owning result is object-mode polarity leaking into a JIT path.
    #[test]
    fn fresh_jit_missing_address_is_a_hard_error() {
        let symbol = cranelisp_types::drop_glue_symbol_name(&user(), &ConcreteType::String);
        let err = fresh_jit_target(
            Some((symbol, None, test_code())),
            &user(),
            &ConcreteType::String,
        )
        .expect_err("a row without a finalized address must not resolve");
        assert!(
            err.to_string().contains("no finalized"),
            "{}",
            err.to_string()
        );
    }

    // spec: design/int/result-owner.md §5 — a symbol/key disagreement names
    // BOTH spellings. Int never re-derives backend's type encoding, so this
    // guard is what catches a divergence between the two grammars.
    #[test]
    fn fresh_jit_symbol_key_mismatch_names_both_spellings() {
        let err = fresh_jit_target(
            Some((
                LinkerSymbol::from("__cranelisp_drop_bogus"),
                Some(8),
                test_code(),
            )),
            &user(),
            &ConcreteType::String,
        )
        .expect_err("a mis-keyed artifact must not resolve");
        let text = err.to_string();
        assert!(text.contains("__cranelisp_drop_bogus"), "{text}");
        assert!(
            text.contains(
                cranelisp_types::drop_glue_symbol_name(&user(), &ConcreteType::String).as_ref()
            ),
            "{text}"
        );
    }

    // spec: design/int/result-owner.md §3.1.1 / §4.1 — an ARMED owner holds a
    // clone of the `Code` it captured, so replacing the map row (pair-atomically)
    // does not invalidate it: the target still calls, exactly once.
    #[test]
    fn armed_owner_survives_a_pair_atomic_row_replacement() {
        let _ = take_events();
        let glues: DashMap<(ModuleFullPath, ConcreteType), crate::worker::FreshJitDropGlue> =
            DashMap::new();
        // The armed owner is built from a target clone, exactly as
        // `resolve_fresh_jit` produces it.
        let symbol = cranelisp_types::drop_glue_symbol_name(&user(), &ConcreteType::String);
        let target = fresh_jit_target(
            Some((
                symbol,
                Some(recording_glue as extern "C" fn(i64) as usize),
                test_code(),
            )),
            &user(),
            &ConcreteType::String,
        )
        .expect("resolves");
        // Recompilation replaces the row wholesale (here: clears it).
        glues.clear();
        struct Fixed(std::cell::RefCell<Option<GlueTarget>>);
        impl ResultGlueResolver for Fixed {
            fn resolve(
                &self,
                _module: &ModuleFullPath,
                _ty: &ConcreteType,
            ) -> Result<GlueTarget, CranelispError> {
                Ok(self.0.borrow_mut().take().expect("one resolution"))
            }
        }
        let owner = OwnedProgramResult::new(
            21,
            Type::String,
            None,
            &user(),
            &empty_tables(),
            &Fixed(std::cell::RefCell::new(Some(target))),
        )
        .expect("armed");
        owner.release();
        assert_eq!(
            take_events(),
            vec!["glue(21)".to_string()],
            "the armed owner's captured target stays callable across replacement"
        );
    }

    // spec: design/int/result-owner.md §3.2 step 3 — the adapter is chosen by
    // the result-producing entry's OWN `Code`: a `Code::Jit` result reads the
    // fresh-JIT map; a `Code::Linker` result resolves through its `Linker` and
    // consults NO `Code::Jit` row; no code owner at all is a hard error.
    #[test]
    fn adapter_selection_follows_the_result_producing_entrys_code() {
        let glues: DashMap<(ModuleFullPath, ConcreteType), crate::worker::FreshJitDropGlue> =
            DashMap::new();
        assert!(matches!(
            SessionGlueResolver::for_result_code(Some(&test_code()), &glues),
            SessionGlueResolver::FreshJit { .. }
        ));
        let linker = std::sync::Arc::new(
            cranelisp_backend::cache::linker::Linker::new().expect("Linker::new"),
        );
        let cached =
            SessionGlueResolver::for_result_code(Some(&crate::code::Code::linker(linker)), &glues);
        assert!(matches!(cached, SessionGlueResolver::Cached { .. }));
        // A Linker result must not fall back to the (here empty) JIT map: the
        // error it raises is the CACHE-load one, naming the canonical symbol.
        let err = cached
            .resolve(&user(), &ConcreteType::String)
            .expect_err("empty linker cannot resolve the glue");
        let text = err.to_string();
        assert!(text.contains("cache-hit drop glue"), "{text}");
        assert!(
            text.contains(
                cranelisp_types::drop_glue_symbol_name(&user(), &ConcreteType::String).as_ref()
            ),
            "the cache adapter derives the SAME canonical symbol: {text}"
        );
        assert!(
            text.contains("cache-load failure"),
            "a missing symbol is a cache-LOAD failure, never a cache miss repaired \
             with private glue: {text}"
        );
        let none = SessionGlueResolver::for_result_code(None, &glues);
        assert!(matches!(none, SessionGlueResolver::NoCodeOwner { .. }));
        assert!(
            none.resolve(&user(), &ConcreteType::String)
                .expect_err("no owner is an error")
                .to_string()
                .contains("no code lifetime owner")
        );
    }

    // -----------------------------------------------------------------------
    // §6 row 6 (classification half) — linked startup disposition
    // -----------------------------------------------------------------------

    // spec: design/int/result-owner.md §3.3 steps 1–3 — the linked stub's
    // disposition comes from the SAME classification the runtime arms use: a
    // scalar `Int` inner result narrows to the exit code and imports nothing;
    // an owning inner result exits 0 and imports the canonical
    // module-qualified glue symbol.
    #[test]
    fn startup_disposition_matches_the_shared_classification() {
        let scalar =
            startup_result_exit(&Type::Int, None, &user(), &empty_tables()).expect("Int narrows");
        assert!(scalar.result_is_exit_code, "an Int result IS the exit code");
        assert!(
            scalar.release_symbol.is_none(),
            "a scalar inner result imports no glue — the stub stays byte-identical"
        );

        let owning = startup_result_exit(&Type::String, None, &user(), &empty_tables())
            .expect("String narrows");
        assert!(
            !owning.result_is_exit_code,
            "every non-Int result exits 0, exactly as `--run` does"
        );
        assert_eq!(
            owning.release_symbol.as_ref(),
            Some(&cranelisp_types::drop_glue_symbol_name(
                &user(),
                &ConcreteType::String
            )),
            "the canonical module-qualified spelling, from the ONE grammar"
        );
    }

    // spec: design/int/result-owner.md §3.3 — an all-nullary ADT inner result
    // is `NeverHeap`: no import, and (being non-Int) exit code 0.
    #[test]
    fn startup_nullary_adt_inner_result_imports_nothing() {
        let tables = tables_with_adt(&user(), "Flag", &[("On", 0), ("Off", 0)]);
        let ty = Type::ADT(FQTypeName::new(user(), TypeName::from("Flag")), Vec::new());
        let exit = startup_result_exit(&ty, None, &user(), &tables).expect("nullary ADT narrows");
        assert!(!exit.result_is_exit_code);
        assert!(exit.release_symbol.is_none());
    }

    // spec: design/int/result-owner.md §3.3 step 4 — a non-concrete inner
    // result type with no codegen view to key on is a LOCATED link-time error
    // naming the module and the type, never a silent skip.
    #[test]
    fn startup_non_concrete_inner_type_is_a_located_link_error() {
        let err = startup_result_exit(&Type::Var(4), None, &user(), &empty_tables())
            .expect_err("a residual var cannot be released type-directedly");
        let text = err.to_string();
        assert!(text.contains("user"), "must name the module: {text}");
        assert!(text.contains("not concrete"), "must name the fault: {text}");
    }

    // -----------------------------------------------------------------------
    // §6 row 3 — cache-hit resolution
    // -----------------------------------------------------------------------

    // spec: design/int/result-owner.md §3.2 — the cache adapter derives the
    // canonical symbol with `drop_glue_symbol_name` (never a second grammar)
    // and two module-qualified copies of the SAME concrete type get distinct
    // symbols, so a cross-module collision is impossible.
    #[test]
    fn cache_hit_symbols_are_module_qualified_and_distinct() {
        let other = ModuleFullPath::from("lib.util");
        let linker = std::sync::Arc::new(
            cranelisp_backend::cache::linker::Linker::new().expect("Linker::new"),
        );
        let a = resolve_cached(&linker, &user(), &ConcreteType::String).unwrap_err();
        let b = resolve_cached(&linker, &other, &ConcreteType::String).unwrap_err();
        let sym_a = cranelisp_types::drop_glue_symbol_name(&user(), &ConcreteType::String);
        let sym_b = cranelisp_types::drop_glue_symbol_name(&other, &ConcreteType::String);
        assert_ne!(sym_a, sym_b, "module qualification must distinguish them");
        assert!(a.to_string().contains(sym_a.as_ref()));
        assert!(b.to_string().contains(sym_b.as_ref()));
    }
}
