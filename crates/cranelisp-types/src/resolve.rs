//! Symbol-table resolution primitive — the one query that turns a name into
//! a resolved symbol-table entry, following imports/reexports, module-path
//! aliases, visibility, and Principle-17 chain-following.
//!
//! ## Why this lives in `cranelisp-types` (the S76 W-Macro fold-in)
//!
//! Resolving a name — "in this table set, what does `name` mean when looked
//! up from `current_module`, after following import/reexport chains, applying
//! §8.6.6 module-path aliases, and honouring visibility?" — is a **query over
//! the symbol-table data structure**. It performs no inference, no
//! unification, no substitution; it reads `symbol_tables` + `module_aliases`
//! (both types-owned) and returns an entry. By Principle 15 (behaviour lives
//! with the type it operates on) and Principle 7 (single source of truth) it
//! belongs here, extending the precedent set by [`crate::ensure_module_exists`],
//! [`crate::got_data_symbol_name`], and the chain-follow family
//! ([`crate::resolve_terminal_entry_and_home`] et al.).
//!
//! This consolidates two formerly-scattered copies onto one primitive:
//!
//! - **int's `SymbolTableMacroResolver`** (`src/worker.rs`) — the macro-head
//!   chain-walker that probed the symbol tables to recognise a macro before
//!   executing it.
//! - **typecheck's `resolve_*` family** (`resolve_trait` / `resolve_type` /
//!   `resolve_constructor` / `resolve_qualified` in
//!   `crates/cranelisp-typecheck/src/checker.rs`) — the inference-side name
//!   resolvers.
//!
//! Both now call this one primitive; the typed `ResolveError` that grounded
//! the `resolve_*` family moves here with it (it was typecheck-local only
//! because the resolver was; once the resolver is types-owned, its error is
//! a types boundary type by the multi-consumer rule).
//!
//! ## The primitive-vs-view split (the load-bearing line)
//!
//! The **search primitive is types-owned**: pure over `symbol_tables` +
//! `module_aliases`, generic over `<C, L>`, carrying **no `CheckState`**, no
//! substitution, no inference state. Compatible with "types is data-only" —
//! it is a query, not execution logic.
//!
//! The **choice of which view to search stays with the caller**, supplied as
//! the first-hop [`View`] over the *current* module:
//!
//! - **int's Pass-1 macro recognition** searches the **committed** tables —
//!   it constructs the first-hop view with [`View::single`] over the live
//!   `symbol_tables[current_module]` entry. No staging exists during Pass 1
//!   (the expand phase precedes `check_forms`).
//! - **typecheck's Pass-2/3 body resolution** searches the **staging ∪ live**
//!   union — its `SymbolTableAccess` hands a [`View::union`] over the
//!   orchestrator-owned staging table and live (staging-first).
//!
//! Same primitive, different first-hop view supplied by the caller. The
//! *cross-module* hops (chain-following `Import` edges to a dependency
//! module, and the alias-resolved FQ target module) always land in **other,
//! already-committed** modules — staging only ever holds the *current*
//! cluster's module (Principle 17 + Decision 44), so beyond the first hop the
//! search reads `symbol_tables` directly. This is why the view parameterises
//! only the entry point, not the whole walk.
//!
//! See `design/arch/bounded-contexts.md` §7 (types — the resolution-primitive
//! responsibility), §2 (typecheck — `resolve_*` becomes a caller), §6 (int —
//! Pass-1 recognition via this primitive), and `design/arch/interfaces.md`
//! §"Resolution primitive".

use crate::ast::Visibility;
use crate::error::{CranelispError, ErrorLocation};
use crate::module::{
    CHAIN_FOLLOW_DEPTH_LIMIT, CodeStore, LinkerStore, ModuleAliases, ModuleEntry, SymbolTables,
    resolve_terminal_entry_home_and_key,
};
use crate::newtype::{FQSymbol, ModuleFullPath, Symbol, TraitName, TypeName};
use crate::span::Span;
use crate::view::View;

/// The reference-resolution scope — a name lookup with the implicit-prelude
/// **fallback intrinsic to the scope**, decided ONCE at construction, never at
/// a call site (S108 Wave-G convergence, `design/arch/prelude-import-convergence.md`
/// §3). Per Principles 18/20 the forgettable per-call fallback flag is made
/// unrepresentable: there is no public resolution entry that takes a per-call
/// fallback bool and no public fallback-less entry point at all. A caller that
/// genuinely must not fall back constructs a scope with `prelude: None` — an
/// explicit, single, reviewable decision at construction.
///
/// The scope carries the caller-supplied first-hop [`View`] over the *current*
/// module (`View::single(live)` for committed search, `View::union(staging,
/// live)` for staging-aware search) plus the two types-owned collections
/// (`symbol_tables`, `module_aliases`), the calling module, and the prelude
/// path to fall back to (`Some` iff the module's fallback bit is ON **and**
/// `current_module != prelude`). Consumed by typecheck (the `TypeCheckEnv`
/// scope constructor) and int (macro recognition, the defmacro gate) with zero
/// cross-crate dependency, exactly like the resolution walk it wraps.
pub struct ResolutionScope<'a, C: CodeStore = (), L: LinkerStore = ()> {
    symbol_tables: &'a SymbolTables<C, L>,
    module_aliases: &'a ModuleAliases,
    first_hop: &'a View<'a, C, L>,
    current_module: &'a ModuleFullPath,
    prelude: Option<&'a ModuleFullPath>,
}

impl<'a, C: CodeStore, L: LinkerStore> ResolutionScope<'a, C, L> {
    /// Construct a resolution scope. `prelude` is `Some(prelude_path)` iff the
    /// module's fallback bit is ON **and** `current_module != prelude` (the
    /// caller-side role datum, resolved ONCE here); `None` ⇒ no fallback for
    /// this scope (a suppressed-prelude module, the prelude itself, platform
    /// sig checks). A `prelude == current_module` is defensively collapsed to
    /// `None` — a module never falls back onto itself.
    pub fn new(
        symbol_tables: &'a SymbolTables<C, L>,
        module_aliases: &'a ModuleAliases,
        first_hop: &'a View<'a, C, L>,
        current_module: &'a ModuleFullPath,
        prelude: Option<&'a ModuleFullPath>,
    ) -> Self {
        let prelude = match prelude {
            Some(p) if p == current_module => None,
            other => other,
        };
        ResolutionScope {
            symbol_tables,
            module_aliases,
            first_hop,
            current_module,
            prelude,
        }
    }

    /// THE reference lookup. Inner (first-hop view) walk; on a
    /// not-found-class miss of an UNQUALIFIED name, prelude retry (public-only
    /// I-1 terminal filter); chain-follow; §8.7.3 visibility; §8.6.6 alias
    /// substitution for qualified names. A qualified `mod/sym` NEVER takes the
    /// prelude retry (it names its module — made explicit inside the walk).
    pub fn resolve(&self, name: &str, span: Span) -> Result<Resolved<C>, ResolveError> {
        resolve_with_prelude(
            self.symbol_tables,
            self.module_aliases,
            self.first_hop,
            self.current_module,
            name,
            self.prelude,
            span,
        )
    }

    /// Typed projection retained on the scope (macro-head recognition). Resolve
    /// `name`, succeed with `Some(fq)` only if the canonical entry is a macro
    /// (`DefKind::Macro`); a resolved non-macro entry or a not-found-class miss
    /// yields `Ok(None)` (a bare forward reference is not yet known to be a
    /// macro); a hard failure (private, unknown qualified module) surfaces as
    /// `Err`. The prelude fallback is intrinsic (same as [`Self::resolve`]),
    /// replacing int's hand-rolled `recognize_macro_head` retry.
    pub fn resolve_macro_head(
        &self,
        name: &str,
        span: Span,
    ) -> Result<Option<FQSymbol>, ResolveError> {
        match self.resolve(name, span) {
            Ok(resolved) => match &resolved.entry {
                ModuleEntry::Def { kind, .. }
                    if matches!(kind.as_ref(), crate::DefKind::Macro { .. }) =>
                {
                    Ok(Some(resolved.fq))
                }
                _ => Ok(None),
            },
            Err(ResolveError::TraitNotFound { .. })
            | Err(ResolveError::TypeNotFound { .. })
            | Err(ResolveError::ConstructorNotFound { .. }) => Ok(None),
            Err(e @ ResolveError::PrivateInaccessible { .. })
            | Err(e @ ResolveError::QualifiedModuleUnknown { .. }) => Err(e),
        }
    }

    /// The inner-table (first-hop) head for `name`, WITHOUT chain-follow or the
    /// prelude fallback — the raw entry as it sits in the current module's view.
    /// Used by [`reject_def_over_binding`] to classify provenance (an inner
    /// `Import` head is an explicit import/export; its absence with a resolving
    /// terminal means the binding came from the prelude fallback).
    fn first_hop_head(&self, name: &str) -> Option<ModuleEntry<C>> {
        self.first_hop.lookup(&Symbol::from(name)).cloned()
    }
}

/// The §8.6.4 definition seam — "may this bare `name` be defined in this
/// scope?" — derived from the SAME [`ResolutionScope::resolve`] walk as
/// reference resolution (S108 Wave-G convergence §4.1). Every definition form
/// (`defn`/`deftype` on the typecheck side, `deftrait` name + method names,
/// `defmacro` in int) routes through this ONE seam, which consults the prelude
/// — to **REJECT**, per §8.6.4 (a name provided by the prelude is in scope on
/// identical terms to an explicit import; a definition over it is a conflict,
/// never a shadow).
///
/// Grounds: the rule already has ONE predicate ([`check_binding_addition`],
/// FIXME 0516); what was still per-surface was the resolve+classify glue, now
/// single-sourced here so int's defmacro path calls the identical seam without
/// a typecheck dependency (the same multi-consumer argument that placed the
/// resolution primitive in this crate).
///
/// Decision, read off the resolved terminal's `home`:
/// - resolve MISS ⇒ not in scope ⇒ **free to define** (§8.8.3 "not-loading");
/// - `home == current_module` ⇒ the module's OWN prior definition ⇒ ordinary
///   **redefinition, ALLOWED** (the REPL redefine path);
/// - `home != current_module` ⇒ the in-scope binding is an explicit
///   `import`/`export` inner head, or (inner head absent) a prelude PUBLIC
///   terminal ⇒ classify provenance and delegate to [`check_binding_addition`].
///
/// Synthetic / mangled names (`$`-containing or `__`-prefixed) are never
/// user-facing bare definitions contesting an in-scope binding; they skip the
/// seam so it only ever fires on an authored bare name.
pub fn reject_def_over_binding<C: CodeStore, L: LinkerStore>(
    scope: &ResolutionScope<'_, C, L>,
    name: &Symbol,
    span: Span,
) -> Result<(), CranelispError> {
    let n = name.as_ref();
    if n.contains('$') || n.starts_with("__") {
        return Ok(());
    }
    let resolved = match scope.resolve(n, span) {
        Ok(r) => r,
        Err(_) => return Ok(()), // not in scope — free to define (§8.8.3)
    };
    let existing = if &resolved.home == scope.current_module {
        // The module's OWN prior def/typedef — ordinary redefinition.
        BindingProvenance::Definition
    } else {
        // Name the source kind from the inner (first-hop) head, no chain-follow,
        // no fallback: an inner `Import` head is an explicit import (Private) or
        // export (Public); absence means the binding came from the implicit
        // prelude outer scope.
        match scope.first_hop_head(n) {
            Some(e) if matches!(e, ModuleEntry::Import { .. }) && e.is_public() => {
                BindingProvenance::Export
            }
            Some(ModuleEntry::Import { .. }) => BindingProvenance::Import,
            _ => BindingProvenance::Prelude,
        }
    };
    check_binding_addition(
        name,
        BindingProvenance::Definition,
        existing,
        &resolved.fq,
        span,
    )
}

/// Error returned by the resolution primitive and its typed wrappers.
///
/// Each variant carries enough context to produce a user-facing message
/// without further lookups: the name being resolved, the calling module (so
/// messages can say "from `<module>`"), and the source span. Grounded in
/// Principle 17 (module locality — resolution failures are scoped to the
/// calling module's import frontier) and Principle 2 (narrow interfaces —
/// one Result-shaped surface per resolution kind).
///
/// **Relocated to `cranelisp-types` at S76 (the W-Macro fold-in).** It was
/// previously `cranelisp-typecheck`-local (one producer, one consumer). Now
/// that the resolution primitive it grounds is types-owned and called by both
/// int (Pass-1 macro recognition) and typecheck (`resolve_*`), the error is a
/// multi-consumer boundary type and lives here per Principle 15's placement
/// heuristic.
///
/// **Error-projection placement.** `ResolveError` projects to the types-owned
/// [`CranelispError`] here (the neutral session error). The
/// `From<ResolveError> for CheckError` projection that the `resolve_*` family
/// previously used stays in `cranelisp-typecheck` — `CheckError` is
/// typecheck-owned (single-consumer per Principle 15), so the projection into
/// it lives with the crate that owns the target. Both projections produce the
/// same message + location; the typecheck-side one is a thin re-projection of
/// this [`CranelispError`] form.
#[non_exhaustive]
#[derive(Debug, Clone)]
pub enum ResolveError {
    /// Trait name is not reachable from the calling module's import scope,
    /// nor anywhere on its chain-follow path.
    TraitNotFound {
        // FQTypeName exception 1 (display: echoes the as-written bare name for the diagnostic; lookup failed so no FQ exists)
        name: TraitName,
        from_module: ModuleFullPath,
        span: Span,
    },
    /// Type name is not reachable from the calling module's import scope.
    /// Includes the intrinsic short-names (`Int`/`Bool`/`Float`/`String`) —
    /// there is no hardcoded fallback; intrinsics are reached through the
    /// `primitives` module's import bindings like any other name.
    TypeNotFound {
        // FQTypeName exception 1 (display: echoes the as-written bare name for the diagnostic; lookup failed so no FQ exists)
        name: TypeName,
        from_module: ModuleFullPath,
        span: Span,
    },
    /// Constructor name is not reachable, OR is reachable but is not a
    /// constructor entry (e.g., a regular `Def` of the same name shadows it).
    ConstructorNotFound {
        name: Symbol,
        from_module: ModuleFullPath,
        span: Span,
    },
    /// FQ reference like `module/name` where `module` doesn't exist or
    /// isn't loaded. Distinct from `*NotFound` because the failure is at
    /// module-resolution, not name-resolution — the orchestrator promotes
    /// this to a `ResolutionGap` and loads the named module.
    QualifiedModuleUnknown {
        module: ModuleFullPath,
        name: Symbol,
        span: Span,
    },
    /// Name exists in `defining_module` but its visibility forbids access
    /// from `from_module`. Lets the user-facing message say "X is private
    /// to module Y" instead of "X not found".
    PrivateInaccessible {
        name: Symbol,
        defining_module: ModuleFullPath,
        from_module: ModuleFullPath,
        visibility_found: Visibility,
        span: Span,
    },
}

impl std::fmt::Display for ResolveError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message())
    }
}

impl std::error::Error for ResolveError {}

impl ResolveError {
    /// The source span the failure is attributed to.
    pub fn span(&self) -> Span {
        match self {
            ResolveError::TraitNotFound { span, .. }
            | ResolveError::TypeNotFound { span, .. }
            | ResolveError::ConstructorNotFound { span, .. }
            | ResolveError::QualifiedModuleUnknown { span, .. }
            | ResolveError::PrivateInaccessible { span, .. } => *span,
        }
    }

    /// The user-facing message. Shared by `Display` and the `CranelispError`
    /// projection so the two never drift.
    pub fn message(&self) -> String {
        match self {
            ResolveError::TraitNotFound {
                name, from_module, ..
            } => {
                format!("unknown trait `{name}` (from module `{from_module}`)")
            }
            ResolveError::TypeNotFound {
                name, from_module, ..
            } => {
                format!("unknown type `{name}` (from module `{from_module}`)")
            }
            ResolveError::ConstructorNotFound {
                name, from_module, ..
            } => {
                format!("unknown constructor `{name}` (from module `{from_module}`)")
            }
            ResolveError::QualifiedModuleUnknown { module, name, .. } => {
                format!("module `{module}` referenced by `{module}/{name}` is not loaded")
            }
            ResolveError::PrivateInaccessible {
                name,
                defining_module,
                from_module,
                ..
            } => {
                format!(
                    "`{name}` is private to module `{defining_module}`; not accessible from `{from_module}`"
                )
            }
        }
    }
}

/// Projection to the types-owned neutral session error. The typecheck-side
/// `From<ResolveError> for CheckError` is a thin re-projection of this form
/// (it lives in `cranelisp-typecheck` because `CheckError` is owned there).
impl From<ResolveError> for CranelispError {
    fn from(e: ResolveError) -> CranelispError {
        CranelispError::TypeError {
            message: e.message(),
            location: ErrorLocation::from_span(e.span()),
        }
    }
}

/// A successfully resolved name: the canonical entry, its defining (home)
/// module, and TWO identities — the **reference identity** (`fq`) and the
/// **storage identity** (`storage_key` / [`Resolved::storage_fq`]).
///
/// The home module is the chain-follow terminus (the module that owns the
/// canonical, non-`Import` entry).
///
/// **The two identities (FIXME 0620,
/// `design/arch/backend-keyed-consumer.md` §1.1):**
///
/// - `fq` = `home` + `canonical_symbol(written name)` — the *reference*
///   identity: how the caller spelled the name, homed at the terminus. This
///   is the display/attribution/`callees` identity (macro-head dispatch,
///   error messages, §8.6.4 remedies). It does **NOT** in general address the
///   entry in `home`'s table: across a member alias (`v` → `Box.v`,
///   `Pure` → `IO.Pure`) or a renamed import/export (`[(foo bar)]`) the
///   written spelling is an `Import`-edge alias, not the table key.
/// - `storage_key` — the *storage* identity: the exact symbol-table key the
///   chain-follow terminated at (the last followed edge's `source.symbol`,
///   or the written name when no edge renamed). `symbol_tables[home]
///   [storage_key]` IS the terminal entry, always. This is the identity a
///   keyed consumer (the backend `entry_at` read, the `VarRef::Global` /
///   `ApplyRef::Dispatch` carrier values) must record — captured here, at the ONE place it is knowable,
///   because a `ModuleEntry` does not carry its own key (Principle 24
///   "Resolve once": the walk that found the entry reports where it found
///   it; no consumer ever reconstructs the key from a written spelling).
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Resolved<C: CodeStore = ()> {
    /// The canonical (non-`Import`/non-`Reexport`) entry the name resolves to.
    pub entry: ModuleEntry<C>,
    /// The module that defines the canonical entry (chain-follow terminus).
    pub home: ModuleFullPath,
    /// The reference identity: `home` + the canonical written spelling. For
    /// storage addressing use [`Resolved::storage_fq`] — see the type-level
    /// rustdoc for the distinction.
    pub fq: FQSymbol,
    /// The terminal storage key: the exact key the entry sits under in
    /// `home`'s table ("whichever storage key HIT"). Equals the written
    /// spelling iff no followed `Import`/`Reexport` edge renamed.
    pub storage_key: Symbol,
}

impl<C: CodeStore> Resolved<C> {
    /// The storage identity as an [`FQSymbol`] — `home` + [`Self::storage_key`].
    /// The key a direct two-level table read (`symbol_tables[module][symbol]`)
    /// fetches this exact terminal entry with; the `VarRef::Global` /
    /// `ApplyRef::Dispatch` carrier value
    /// (`design/arch/backend-keyed-consumer.md` §1.1).
    pub fn storage_fq(&self) -> FQSymbol {
        FQSymbol {
            module: self.home.clone(),
            symbol: self.storage_key.clone(),
        }
    }
}

/// The single general resolution primitive: resolve `name` from
/// `current_module` against the table set, following imports/reexports,
/// applying §8.6.6 module-path aliases for qualified references, honouring
/// visibility, and chain-following per Principle 17.
///
/// **The view-vs-primitive split.** `first_hop` is the caller-supplied
/// [`View`] over the *current* module — `View::single(live)` for committed
/// search (int Pass-1 recognition), `View::union(staging, live)` for the
/// staging-aware search (typecheck Pass-2/3). The primitive consults
/// `first_hop` only for the entry-point lookup; once a hop crosses into a
/// different module (an `Import` edge's `source.module`, or an alias-resolved
/// FQ target), it reads `symbol_tables` directly — those modules are
/// dependencies, always already-committed (Principle 17 + Decision 44), so no
/// staging view applies to them.
///
/// **Inputs are types-owned only.** `symbol_tables` and `module_aliases` are
/// both `cranelisp-types` collections; there is no `CheckState`, no
/// substitution, no inference. This is what keeps the primitive in the
/// data-only crate.
///
/// **Resolution algorithm** (per spec §8.6.6 + Principle 17 shapes 1–2):
///
/// 1. If `name` contains a `/` it is a **qualified** reference `mod/sym`:
///    apply longest-prefix alias substitution to `mod` (via `module_aliases`),
///    then look the symbol up directly in the alias-resolved module. A missing
///    target module yields [`ResolveError::QualifiedModuleUnknown`] (the
///    orchestrator promotes this to a load-and-retry gap).
/// 2. Otherwise it is an **unqualified short name**: look it up in `first_hop`
///    (current-module view). If absent → not found. If present and it is an
///    `Import`/`Reexport`, chain-follow `source.module` one edge at a time
///    against `symbol_tables` to the canonical entry.
/// 3. Apply the **visibility filter**: a non-public canonical entry is
///    accessible only from within the defining module's subtree; otherwise
///    [`ResolveError::PrivateInaccessible`].
///
/// Returns the [`Resolved`] triple on success. The typed projections on
/// [`ResolutionScope`] ([`ResolutionScope::resolve_macro_head`], the checker's
/// `resolve_trait`-shaped kind projections, etc.) layer kind-specific
/// success/error projection on top of this one walk (Principle 6 — one
/// general primitive + thin typed wrappers, not many bespoke walkers).
///
/// `span` is carried only for error attribution; it does not affect the walk.
///
/// **Private (S108 Wave-G).** The former `pub fn resolve` walk; the sole public
/// entry point is now [`ResolutionScope::resolve`] (fallback intrinsic) — there
/// is no bare fallback-less resolve on the public surface.
fn resolve_one<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    name: &str,
    span: Span,
) -> Result<Resolved<C>, ResolveError>
where
    C: CodeStore,
    L: LinkerStore,
{
    if let Some((module_part, symbol_part)) = split_qualified(name) {
        return resolve_qualified(
            symbol_tables,
            module_aliases,
            first_hop,
            current_module,
            &module_part,
            &symbol_part,
            span,
        );
    }

    // Unqualified short-name: resolve through the caller-chosen view.
    resolve_current_via_view(symbol_tables, first_hop, current_module, name, span)
}

/// Current-module view resolution: first hop through the caller-chosen VIEW
/// (staging ∪ live), chain-follow with the AN-5 same-module staging arm
/// ([`chain_follow_committed`]), visibility filter. The ONE body behind BOTH
/// spellings of a current-module reference (Principle 7):
///
/// - the bare short name ([`resolve_one`]'s unqualified leg), and
/// - the current-module-qualified `cur/sym` ([`resolve_qualified`]'s own-module
///   arm — S113 0655, user ruling (a)): per TB-25 resolved identity, `cur/sym`
///   written inside `cur` is another SPELLING of the local name, so it must see
///   exactly what the bare spelling sees (staging, the in-flight cluster), and
///   a member absent from the view is the bare **not-found** class — never
///   [`ResolveError::QualifiedModuleUnknown`], which the orchestrator promotes
///   to a load-and-retry gap (a current-module gap is the 0655 false
///   self-dependency mint: "circular dependency detected: m -> m").
fn resolve_current_via_view<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    name: &str,
    span: Span,
) -> Result<Resolved<C>, ResolveError>
where
    C: CodeStore,
    L: LinkerStore,
{
    // First hop is the caller-chosen view; subsequent hops read committed
    // tables (dependencies are always committed), with the AN-5 same-module
    // staging arm inside the chain-follow.
    let sym = Symbol::from(name);
    let head = first_hop
        .lookup(&sym)
        .cloned()
        .ok_or_else(|| not_found(name, current_module, span))?;

    let (entry, home, storage_key) = chain_follow_committed(
        symbol_tables,
        first_hop,
        current_module,
        head,
        current_module.clone(),
        sym,
    )
    .ok_or_else(|| not_found(name, current_module, span))?;

    visibility_check(&entry, &home, current_module, name, span)?;

    Ok(Resolved {
        fq: FQSymbol {
            module: home.clone(),
            symbol: canonical_symbol(name),
        },
        entry,
        home,
        storage_key,
    })
}

/// The shared reference-lookup body with the prelude fallback intrinsic to the
/// `prelude: Option` scope datum — the single realisation behind
/// [`ResolutionScope::resolve`] (the sole public reference-resolution entry
/// point since the CS2 removal of the free fallback shim,
/// `prelude-import-convergence.md` §6). (1) resolve in the current-module first hop; (2) on a not-found miss
/// of an unqualified name with `prelude = Some`, retry rooted at the prelude;
/// (3) **public-only I-1 filter on the prelude HEAD binding** — spec §8.8.1
/// provides the prelude's *public names*, so the visibility that gates the
/// retry is the binding in the prelude's own table, not the chain-followed
/// terminal's (FIXME 0567: a private `(import …)` edge inside the prelude
/// chaining to a public terminal elsewhere must NOT leak as a bare name) —
/// plus the terminal-side public check as defence in depth. A filtered hit
/// reads as the ORIGINAL current-module not-found.
fn resolve_with_prelude<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    name: &str,
    prelude: Option<&ModuleFullPath>,
    span: Span,
) -> Result<Resolved<C>, ResolveError>
where
    C: CodeStore,
    L: LinkerStore,
{
    // Step 1: resolve in the caller-chosen current-module view.
    let first = resolve_one(
        symbol_tables,
        module_aliases,
        first_hop,
        current_module,
        name,
        span,
    );

    // No fallback for this scope (suppressed prelude, the prelude itself, or a
    // never-self-fallback collapse) ⇒ a bare first-hop resolve.
    let prelude_path = match prelude {
        Some(p) if p != current_module => p,
        _ => return first,
    };

    // §8.6.4: the prelude fallback applies to BARE names only — a qualified
    // reference names its module directly. This guard is load-bearing since
    // the 0655 own-module view arm: a CURRENT-module-qualified miss now
    // returns the bare not-found class (deliberately — it must never mint a
    // load-and-retry gap), and without this guard that miss would consult the
    // prelude (`user/ghost` resolving to the prelude's `ghost` would be a
    // wrong-accept against the written spelling; MC-X3b).
    if split_qualified(name).is_some() {
        return first;
    }

    match first {
        Ok(resolved) => Ok(resolved),
        // Only an inner-scope MISS triggers the prelude retry. Hard failures
        // (private, unknown qualified module) are returned as-is — they are
        // not "the name is absent here", so the outer scope does not apply.
        // (Qualified names never reach the retry — the guard above.)
        Err(ResolveError::TraitNotFound { .. })
        | Err(ResolveError::TypeNotFound { .. })
        | Err(ResolveError::ConstructorNotFound { .. }) => {
            // Step 2: retry rooted at the prelude module. The prelude's own
            // committed table is the first hop for this retry.
            let inner_miss = || not_found(name, current_module, span);
            let prelude_view = match symbol_tables.get(prelude_path) {
                Some(t) => t,
                // Prelude not loaded → the inner miss stands.
                None => return Err(inner_miss()),
            };
            // Step 2a (FIXME 0567): the §8.8.1 HEAD-visibility filter. The
            // prelude provides its PUBLIC names — the binding that must be
            // public is the prelude HEAD (the entry in the prelude's own
            // table), not the chain-followed terminal. A private `(import …)`
            // edge inside the prelude whose chain terminates at a public
            // `Def` elsewhere must NOT leak as a bare name; it reads as the
            // original current-module not-found. (Only unqualified names
            // reach this retry — the qualified branch never returns the
            // retried not-found class — so a bare `Symbol` probe of the
            // prelude table is exact.) Head-side precedents: typecheck's
            // `find_trait_method_decl` `public_only`, int's
            // `prelude_implicit_names`, the §3.5.2 display-gate fix.
            let prelude_first_hop = View::single(&prelude_view);
            match prelude_first_hop.lookup(&Symbol::from(name)) {
                Some(head) if head.is_public() => {}
                _ => return Err(inner_miss()),
            }
            let retry = resolve_one(
                symbol_tables,
                module_aliases,
                &prelude_first_hop,
                prelude_path,
                name,
                span,
            );
            match retry {
                // Step 3: public-only filter on the prelude TERMINAL as well
                // (defence in depth beside `resolve_one`'s own visibility
                // check — a public prelude head must not expose a private
                // terminal either).
                Ok(resolved) if resolved.entry.is_public() => Ok(resolved),
                Ok(_) => Err(inner_miss()),
                // A prelude-side miss reports the original current-module miss
                // (the user wrote the name in `current_module`, not prelude).
                Err(_) => Err(inner_miss()),
            }
        }
        Err(e) => Err(e),
    }
}

/// The provenance of a name binding, for the §8.6.4 / §8.4.0 name-collision
/// rule ([`check_binding_addition`]). A binding of a bare name arises from one
/// of four sources; the collision rule is a pure function of the (incoming,
/// existing) provenance pair.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BindingProvenance {
    /// A module-local definition (`defn` / `def` / `deftype`).
    Definition,
    /// A name brought into scope by an explicit `(import …)` (spec §8.3 — a
    /// `Private` inner `Import` edge).
    Import,
    /// A name brought into scope by an `(export …)` re-export (spec §8.4.0 — a
    /// `Public` inner `Import` edge; it enters the exporting module's own bare
    /// scope).
    Export,
    /// A name reachable only through the implicit-prelude OUTER SCOPE
    /// (spec §8.8.1).
    Prelude,
}

/// The §8.6.4 / §8.4.0 name-binding collision rule — the SINGLE shared
/// predicate, called at BOTH binding events (definition-register on the
/// typecheck side, import/export-install on the int side). Single-sources the
/// symmetric rule AND its FQ-remedy diagnostic so the two events can never
/// drift (the FIXME-0516 unification — before it, each event carried its own
/// copy of the rule and the import-event silently skipped the local-def case,
/// the #8 mode-divergence hole).
///
/// `name` is the contested bare name; `incoming` is the provenance of the
/// binding being added; `existing` is the provenance of the binding already in
/// scope for that name; `remedy` is the fully-qualified identity of the OTHER
/// symbol (the one the user should reference qualified to resolve the clash).
///
/// **Symmetric rule** (spec §8.6.4, all modes, no exceptions):
///
/// - incoming `Definition` vs existing `Import`/`Export`/`Prelude` ⇒ **error**
///   (a definition may not shadow a name brought into scope);
/// - incoming `Import`/`Export` vs existing `Definition` ⇒ **error** (the
///   symmetric companion — an import/export may not shadow a local definition;
///   this is the arm the import-event was missing);
/// - incoming `Definition` vs existing `Definition` ⇒ **ok** (the module's own
///   prior definition of the same name — ordinary REPL redefinition);
/// - any other pairing ⇒ **ok** (import-over-import dedup/ambiguity is the
///   §8.6.5 distinct-terminal rule, handled at the install seam, not here).
///
/// Both binding events install imports/exports (Pass-0) before registering
/// definitions (Pass-1), so def-over-import AND import-over-def both reduce to
/// this one probe, identically in every mode (the mode-parity MUST).
pub fn check_binding_addition(
    name: &Symbol,
    incoming: BindingProvenance,
    existing: BindingProvenance,
    remedy: &FQSymbol,
    span: Span,
) -> Result<(), CranelispError> {
    use BindingProvenance::{Definition, Export, Import, Prelude};
    let collides = matches!(
        (incoming, existing),
        (Definition, Import | Export | Prelude) | (Import | Export, Definition)
    );
    if !collides {
        // Def-over-def is ordinary redefinition; import-over-import is the
        // §8.6.5 distinct-terminal rule (not this predicate's concern).
        return Ok(());
    }
    let incoming_desc = match incoming {
        Definition => "definition",
        Import => "import",
        Export => "export",
        Prelude => "implicit-prelude binding",
    };
    let existing_desc = match existing {
        Definition => "a local definition",
        Import => "an explicit import",
        Export => "an export",
        Prelude => "the implicit prelude",
    };
    let message = format!(
        "error: {incoming_desc} of '{name}' conflicts with '{name}' already in \
         scope via {existing_desc} (spec/08-modules.md §8.6.4): a name may not be \
         bound by both a definition and an import, export, or the implicit \
         prelude. Rename or remove one binding (§8.3.5 / §8.8.3), or reference \
         the other symbol fully-qualified as '{}/{}'",
        remedy.module, remedy.symbol,
    );
    Err(CranelispError::TypeError {
        message,
        location: ErrorLocation::from_span(span),
    })
}

/// Qualified `mod/sym` resolution (Principle 17 shape 2). Applies §8.6.6
/// longest-prefix alias substitution to `module_part`; a reference whose
/// alias-resolved module is the CURRENT module delegates to
/// [`resolve_current_via_view`] (S113 0655 — the qualified spelling of a local
/// name resolves identically to the bare spelling, staging included); any
/// other module resolves via the committed tables (dependencies are always
/// committed), chain-following within the named module (a qualified name may
/// land on a re-export that points further on).
fn resolve_qualified<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    module_part: &ModuleFullPath,
    symbol_part: &str,
    span: Span,
) -> Result<Resolved<C>, ResolveError>
where
    C: CodeStore,
    L: LinkerStore,
{
    let resolved_module = substitute_module_alias(module_aliases, module_part);
    // S113 0655 (user ruling (a); TB-25 resolved identity): a reference
    // qualified with the CURRENT module — after §8.6.6 alias substitution —
    // is another spelling of the local name. Resolve it through the caller's
    // first-hop VIEW exactly like the bare spelling: the committed-only
    // primitive below cannot see the caller's staging mid-cluster (the AN-5
    // asymmetry this arm removes), and its `QualifiedModuleUnknown` for a
    // mid-compile current module is what minted the 0655 false
    // self-dependency gap.
    if resolved_module == *current_module {
        return resolve_current_via_view(
            symbol_tables,
            first_hop,
            current_module,
            symbol_part,
            span,
        );
    }
    // Chain-follow the symbol within the named module too (a qualified name
    // may land on a re-export that points further on).
    let (entry, home, storage_key) =
        resolve_terminal_entry_home_and_key(symbol_tables, &resolved_module, symbol_part)
            .ok_or_else(|| {
                if symbol_tables.get(&resolved_module).is_none() {
                    ResolveError::QualifiedModuleUnknown {
                        module: resolved_module.clone(),
                        name: Symbol::from(symbol_part),
                        span,
                    }
                } else {
                    not_found(symbol_part, &resolved_module, span)
                }
            })?;
    visibility_check(&entry, &home, current_module, symbol_part, span)?;
    Ok(Resolved {
        fq: FQSymbol {
            module: home.clone(),
            symbol: canonical_symbol(symbol_part),
        },
        entry,
        home,
        storage_key,
    })
}

// --- Internal helpers ---

/// A qualified name carries exactly one `/` separating a non-empty module
/// path from a non-empty symbol (trait-method symbols like `Display.show` use
/// `.`, never `/`). A name whose module part OR symbol part is empty — a bare
/// punctuation operator like `/` or `//`, or a leading/trailing `foo/` / `/bar`
/// — is NOT qualified; it is a literal bare name (Principle 16 — punctuation
/// symbols are not special). Returning `None` for those routes them to the
/// unqualified short-name path, matching pre-S81 chokepoint behaviour.
fn split_qualified(name: &str) -> Option<(ModuleFullPath, String)> {
    name.split_once('/')
        .filter(|(m, s)| !m.is_empty() && !s.is_empty())
        .map(|(m, s)| (ModuleFullPath::from(m), s.to_string()))
}

/// Chain-follow `head` to its canonical home. The first hop already came from
/// the caller's view; this walks the rest.
///
/// **Same-module alias hop through the caller's VIEW (S109, W1 commit 1;
/// `design/arch/dotted-ctor-canonical-keys.md` §3.5/§6).** The S76 premise that
/// "beyond the first hop the walk always lands in other, already-committed
/// modules" is FALSE for a SAME-MODULE member alias: a bare constructor /
/// field-accessor name is an `Import` edge onto its canonical `Type.member`
/// `Def` in the SAME module, and within one typecheck cluster that canonical
/// `Def` lives in the caller's STAGING, not the committed live table. When an
/// `Import` edge's `source.module == current_module`, take the hop through the
/// caller's first-hop VIEW (staging∪live) rather than the live-only committed
/// primitive — otherwise a same-cluster bare→canonical alias misses (the
/// `undefined variable: v` field-accessor same-cluster `--run` defect, AN-5,
/// and the S109 ctor alias). Cross-module hops stay on the committed primitive
/// (dependencies are always committed).
fn chain_follow_committed<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    head: ModuleEntry<C>,
    home: ModuleFullPath,
    key: Symbol,
) -> Option<(ModuleEntry<C>, ModuleFullPath, Symbol)>
where
    C: CodeStore,
    L: LinkerStore,
{
    chain_follow_committed_depth(symbol_tables, first_hop, current_module, head, home, key, 0)
}

/// [`chain_follow_committed`]'s recursive body with the same-module-arm depth
/// counter. A degenerate same-module alias CYCLE (self-alias, or a→b→a — only
/// constructible by a registration bug, but a stack overflow is the wrong
/// failure for it) bottoms out at [`CHAIN_FOLLOW_DEPTH_LIMIT`] and reads as a
/// not-found miss, mirroring the committed primitive's own depth cap
/// (`resolve_terminal_entry_and_home`).
fn chain_follow_committed_depth<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    head: ModuleEntry<C>,
    home: ModuleFullPath,
    key: Symbol,
    depth: usize,
) -> Option<(ModuleEntry<C>, ModuleFullPath, Symbol)>
where
    C: CodeStore,
    L: LinkerStore,
{
    if depth > CHAIN_FOLLOW_DEPTH_LIMIT {
        return None;
    }
    match &head {
        ModuleEntry::Import { source, .. } if source.module == *current_module => {
            // Same-module member alias — follow through the caller's view so a
            // same-cluster staged canonical `Def` is visible. The alias and its
            // canonical target are both in `current_module`, so `home` is unchanged;
            // the followed edge's `source.symbol` becomes the candidate storage key.
            let next_key = source.symbol.clone();
            let next = first_hop.lookup(&next_key)?.clone();
            chain_follow_committed_depth(
                symbol_tables,
                first_hop,
                current_module,
                next,
                home,
                next_key,
                depth + 1,
            )
        }
        ModuleEntry::Import { source, .. } => {
            // Delegate the cross-module remainder to the existing committed
            // chain-follow primitive — single source of truth for the walk
            // (it carries its own depth cap and threads the storage key).
            resolve_terminal_entry_home_and_key(
                symbol_tables,
                &source.module,
                source.symbol.as_ref(),
            )
        }
        _ => Some((head, home, key)),
    }
}

/// §8.6.6 step 5 longest-prefix module-alias substitution. Find the longest
/// alias-table key that is a dot-segment prefix of `module_path`, substitute
/// its `target`, and carry any remaining dot-segments through. No match →
/// unchanged.
///
/// **Public surface (Principle 7 — single source of truth).** The int
/// FQ-autoload boundary (`SymbolTableMacroResolver::recognize`,
/// `src/process_form.rs`) computes the dependency module to load from a raw
/// `mod/sym` reference *before* typecheck runs, so it must apply the same
/// §8.6.6 alias resolution typecheck would (otherwise a bare submodule
/// reference like `util/...` after `(mod util)` would try to load a module
/// literally named `util`). It calls this primitive directly rather than
/// re-implementing the longest-prefix walk — the former int-side
/// `resolve_module_alias` re-implementation (a byte-identical copy that aged
/// independently) is retired. This is also the same walk
/// [`resolve_qualified`] applies internally, so all three qualified-reference
/// resolution sites share one implementation.
pub fn substitute_module_alias(
    module_aliases: &ModuleAliases,
    module_path: &ModuleFullPath,
) -> ModuleFullPath {
    let queried: &str = module_path.as_ref();
    let mut best: Option<(usize, ModuleFullPath)> = None;
    for entry in module_aliases.iter() {
        let key: &str = entry.key().as_ref();
        let is_prefix = queried == key
            || (queried.len() > key.len()
                && queried.as_bytes()[key.len()] == b'.'
                && queried.starts_with(key));
        if is_prefix {
            let take = best
                .as_ref()
                .map(|(len, _)| key.len() > *len)
                .unwrap_or(true);
            if take {
                best = Some((key.len(), entry.value().target.clone()));
            }
        }
    }
    match best {
        None => module_path.clone(),
        Some((matched_len, target)) => {
            let remainder = &queried[matched_len..];
            if remainder.is_empty() {
                target
            } else {
                ModuleFullPath::from(format!("{target}{remainder}"))
            }
        }
    }
}

/// Visibility filter (spec §8.7.3): a non-public canonical entry is accessible
/// only from within the defining module's subtree.
fn visibility_check<C: CodeStore>(
    entry: &ModuleEntry<C>,
    home: &ModuleFullPath,
    from_module: &ModuleFullPath,
    name: &str,
    span: Span,
) -> Result<(), ResolveError> {
    if entry.is_public() || in_subtree(from_module, home) {
        Ok(())
    } else {
        Err(ResolveError::PrivateInaccessible {
            name: Symbol::from(name),
            defining_module: home.clone(),
            from_module: from_module.clone(),
            visibility_found: Visibility::Private,
            span,
        })
    }
}

/// A module is in its own subtree; a child (`foo.bar`) is in the subtree of
/// its parent (`foo`).
fn in_subtree(accessor: &ModuleFullPath, definer: &ModuleFullPath) -> bool {
    let a: &str = accessor.as_ref();
    let d: &str = definer.as_ref();
    a == d || a.starts_with(&format!("{d}."))
}

/// Mint the canonical `Type.member` symbol-table key for a type-owned member.
///
/// The inverted member model (spec §8.5.2, `bounded-contexts.md` §7) stores a
/// type's members as real `Def` entries under a **dotted canonical key** in
/// the type's home module — `Box.v` for the field accessor, and (S109
/// dotted-ctor capability) `Maybe.Some` for a constructor — with the bare
/// member name as a convenience ALIAS that §8.6.5 poisons to
/// `ModuleEntry::Ambiguous` on distinct-terminal collision. This function is
/// the ONE mint point for that key shape (Principle 7): registration
/// (`cranelisp-typecheck::adt`), the checker's canonical-key probes, and the
/// dotted-reference resolver all call it instead of hand-rolling
/// `format!("{}.{}", …)`, so the key grammar cannot drift per site.
///
/// The `.` separator is deliberate and distinct from the `/` module
/// separator: `mod/Type.member` splits at `/` into (module, `Type.member`)
/// via [`split_qualified`], and the dotted remainder is then a member key in
/// the home module's table. `member` is accepted as `&str` so both `Symbol`
/// and `TypeName` (a ctor name) deref in.
pub fn member_key(type_name: &TypeName, member: &str) -> Symbol {
    Symbol::from(format!("{}.{}", type_name, member).as_str())
}

/// Mint the synthetic `impl$FQType$FQTrait` storage key under which a trait
/// impl's **discovery shell** (`ModuleEntry::TraitImpl`) is stored in the
/// trait's home module (Decision 45).
///
/// The ONE mint point for the `impl$` key grammar (the [`member_key`]
/// pattern, hoisted S119 per `design/arch/trait-impl-cache-carrier.md` §4):
/// fresh registration (`cranelisp-typecheck::traits::impl_check`), dispatch's
/// home probe (`traits::dispatch`), and cache-restore enrolment
/// (`crate::enrol_written_trait_impl`) all route here — the two formerly
/// hand-rolled `format!("impl${}${}", …)` sites re-point in the S119/S120
/// wash. Injective by construction over canonical FQ inputs (both halves
/// render with their module qualifier and `$` never occurs inside an FQ
/// rendering), which discharges the safety-register R4 census obligation for
/// the `impl$` family.
pub fn trait_impl_key(impl_type: &crate::FQTypeName, trait_name: &crate::FQTraitName) -> Symbol {
    Symbol::from(format!("impl${impl_type}${trait_name}").as_str())
}

/// The projection **inverse of [`member_key`]** — the bare member name of a
/// (possibly `/`-qualified, possibly `.`-dotted) constructor / member
/// reference or storage key: `Maybe.Some` → `Some`, `macros/SCons` → `SCons`,
/// `m/Maybe.Some` → `Some`, bare `Some` → `Some`.
///
/// The ONE home for the terminal-segment grammar (Principle 7) shared by
/// every site that compares a *written form or storage key* against a *bare
/// display name* — typecheck's exhaustiveness covered-set normaliser
/// (`adt.rs`, the S109 BR-1 `.`-strip) and backend sparkability's
/// ctor-exclusion comparison (`sparkability.rs` vs
/// `collect_module_constructors`'s storage keys, the S109 I-1 finding). A
/// per-site `rsplit` copy is how the two sides of that comparison drift.
///
/// Mirrors `split_qualified`/`canonical_symbol`'s Principle-16 guards: a
/// segment is stripped only when BOTH sides of its separator are non-empty,
/// so bare punctuation operators (`/`, `//`, `.`, `->`) and empty-part shapes
/// (`foo.`, `.foo`) stay literal.
pub fn bare_member_name(name: &str) -> &str {
    let after_slash = name
        .rsplit_once('/')
        .filter(|(m, s)| !m.is_empty() && !s.is_empty())
        .map(|(_, s)| s)
        .unwrap_or(name);
    after_slash
        .rsplit_once('.')
        .filter(|(t, m)| !t.is_empty() && !m.is_empty())
        .map(|(_, m)| m)
        .unwrap_or(after_slash)
}

/// The canonical local symbol for a (possibly qualified) name — the part
/// after the last `/`, which is the symbol within its home module. A bare
/// punctuation operator like `/` (or `//`) whose post-`/` remainder would be
/// empty is NOT split — it is its own canonical symbol (Principle 16; mirrors
/// `split_qualified`'s non-empty-part guard).
fn canonical_symbol(name: &str) -> Symbol {
    Symbol::from(
        name.rsplit_once('/')
            .filter(|(_, s)| !s.is_empty())
            .map(|(_, s)| s)
            .unwrap_or(name),
    )
}

/// Generic not-found projection used before the kind is known. The typed
/// wrappers re-project to the kind-specific variant where they have the
/// expected kind in hand; the bare primitive uses `TypeNotFound`-shaped
/// messaging only as the neutral fallback (callers that care about the kind
/// use a wrapper).
fn not_found(name: &str, from_module: &ModuleFullPath, span: Span) -> ResolveError {
    ResolveError::TypeNotFound {
        name: TypeName::from(name),
        from_module: from_module.clone(),
        span,
    }
}

#[cfg(test)]
mod tests;
