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

use crate::error::{CranelispError, ErrorLocation};
use crate::module::{
    CodeStore, LinkerStore, ModuleAliases, ModuleEntry, SymbolTables,
    resolve_terminal_entry_and_home,
};
use crate::newtype::{FQSymbol, ModuleFullPath, Symbol, TraitName, TypeName};
use crate::span::Span;
use crate::view::View;
use crate::ast::Visibility;

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
            ResolveError::TraitNotFound { name, from_module, .. } => {
                format!("unknown trait `{name}` (from module `{from_module}`)")
            }
            ResolveError::TypeNotFound { name, from_module, .. } => {
                format!("unknown type `{name}` (from module `{from_module}`)")
            }
            ResolveError::ConstructorNotFound { name, from_module, .. } => {
                format!("unknown constructor `{name}` (from module `{from_module}`)")
            }
            ResolveError::QualifiedModuleUnknown { module, name, .. } => {
                format!("module `{module}` referenced by `{module}/{name}` is not loaded")
            }
            ResolveError::PrivateInaccessible { name, defining_module, from_module, .. } => {
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
/// module, and the fully-qualified identity that addresses it.
///
/// The home module is the chain-follow terminus (the module that owns the
/// canonical, non-`Import` entry). `fq` composes `home` + the canonical local
/// symbol, so callers needing an identity (macro-head dispatch, GOT
/// addressing, error attribution) read it directly without recomposing.
#[derive(Debug, Clone)]
pub struct Resolved<C: CodeStore = ()> {
    /// The canonical (non-`Import`/non-`Reexport`) entry the name resolves to.
    pub entry: ModuleEntry<C>,
    /// The module that defines the canonical entry (chain-follow terminus).
    pub home: ModuleFullPath,
    /// The fully-qualified identity addressing the canonical entry.
    pub fq: FQSymbol,
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
/// Returns the [`Resolved`] triple on success. The typed wrappers below
/// ([`resolve_macro_head`], `resolve_trait`-shaped, etc.) layer kind-specific
/// success/error projection on top of this one walk (Principle 6 — one
/// general primitive + thin typed wrappers, not many bespoke walkers).
///
/// `span` is carried only for error attribution; it does not affect the walk.
pub fn resolve<C, L>(
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
            symbol_tables, module_aliases, current_module, &module_part, &symbol_part, span,
        );
    }

    // Unqualified short-name: first hop is the caller-chosen view; subsequent
    // hops read committed tables (dependencies are always committed).
    let sym = Symbol::from(name);
    let head = first_hop
        .lookup(&sym)
        .cloned()
        .ok_or_else(|| not_found(name, current_module, span))?;

    let (entry, home) = chain_follow_committed(symbol_tables, head, current_module.clone())
        .ok_or_else(|| not_found(name, current_module, span))?;

    visibility_check(&entry, &home, current_module, name, span)?;

    Ok(Resolved {
        fq: FQSymbol { module: home.clone(), symbol: canonical_symbol(name) },
        entry,
        home,
    })
}

/// Resolve `name` from `current_module`, falling back to the implicit-prelude
/// **outer scope** on an inner-scope miss when `fallback_on` is true (S78 §2.7.5).
///
/// This is the one general realisation of the 3-step shape duplicated 5× across
/// the codebase (S78 fragmentation, the proximate cause of the recurring
/// "fallback wired for path X not Y" defect): (1) [`resolve`] rooted at the
/// current module; (2) on a not-found miss with `fallback_on`, retry [`resolve`]
/// rooted at `prelude_path`; (3) **public-only filter** on the prelude-retry
/// terminal (the I-1 leak fix — reachability is judged from the original user
/// `current_module`, never in prelude's subtree, so only a PUBLIC prelude
/// terminal is reachable as a bare name; a private one is treated as not-found
/// and does NOT shadow).
///
/// **Data-only by construction (no reverse dependency on typecheck).** The
/// caller does its own `prelude_fallback.get(module)` lookup and passes the
/// resulting `bool` (`fallback_on`) plus the prelude `ModuleFullPath`
/// (`prelude_path`, a types-owned type). The crate never names typecheck's
/// `PreludeFallback` companion-map — it receives the already-resolved decision.
/// This keeps `cranelisp-types` data-only (Principle 7) and is the same
/// general-primitive-plus-thin-wrapper pattern [`resolve`] already follows.
///
/// `fallback_on == false`, or `current_module == prelude_path` (never
/// self-fallback), reduces to a bare [`resolve`] against the first hop.
///
/// **Filter applies to the prelude retry only.** The first-hop (current-module)
/// result is returned unfiltered — a module's own bindings are always reachable
/// from itself. The public-only post-filter reads the prelude terminal's
/// [`ModuleEntry::is_public`]; the I-1 rule reduces to `is_public()` because the
/// original `current_module` is never in prelude's subtree (the `in_subtree`
/// visibility leg never fires for a prelude hit). A private prelude terminal is
/// reported as the original current-module not-found, not as `PrivateInaccessible`.
///
/// See `design/arch/interfaces.md` §"`resolve_with_fallback`" and the typecheck
/// chokepoint family in `crates/cranelisp-typecheck/CLAUDE.md`.
pub fn resolve_with_fallback<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    name: &str,
    fallback_on: bool,
    prelude_path: &ModuleFullPath,
    span: Span,
) -> Result<Resolved<C>, ResolveError>
where
    C: CodeStore,
    L: LinkerStore,
{
    // Step 1: resolve in the caller-chosen current-module view.
    let first = resolve(symbol_tables, module_aliases, first_hop, current_module, name, span);

    // Self-fallback is never taken: a module does not fall back onto itself.
    if !fallback_on || current_module == prelude_path {
        return first;
    }

    match first {
        Ok(resolved) => Ok(resolved),
        // Only an inner-scope MISS triggers the prelude retry. Hard failures
        // (private, unknown qualified module) are returned as-is — they are
        // not "the name is absent here", so the outer scope does not apply.
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
            let retry = resolve(
                symbol_tables,
                module_aliases,
                &View::single(&prelude_view),
                prelude_path,
                name,
                span,
            );
            match retry {
                // Step 3: public-only filter on the prelude terminal. A
                // non-public prelude binding does NOT leak as a bare name; it
                // reads as the original current-module not-found.
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
/// longest-prefix alias substitution to `module_part`, then looks `symbol_part`
/// up directly in the alias-resolved module. No chain-follow on the symbol —
/// a qualified reference names its module directly.
fn resolve_qualified<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
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
    // Chain-follow the symbol within the named module too (a qualified name
    // may land on a re-export that points further on).
    let (entry, home) =
        resolve_terminal_entry_and_home(symbol_tables, &resolved_module, symbol_part).ok_or_else(
            || {
                if symbol_tables.get(&resolved_module).is_none() {
                    ResolveError::QualifiedModuleUnknown {
                        module: resolved_module.clone(),
                        name: Symbol::from(symbol_part),
                        span,
                    }
                } else {
                    not_found(symbol_part, &resolved_module, span)
                }
            },
        )?;
    visibility_check(&entry, &home, current_module, symbol_part, span)?;
    Ok(Resolved {
        fq: FQSymbol { module: home.clone(), symbol: canonical_symbol(symbol_part) },
        entry,
        home,
    })
}

// --- Typed wrappers (Principle 6 — thin projections over the one primitive) ---

/// Resolve a **macro head**: resolve `name`, succeed only if the canonical
/// entry is a macro (`DefKind::Macro`), and return its `FQSymbol` identity for
/// the orchestrator's expand loop to dispatch on.
///
/// Returns `Ok(None)` when the name resolves to a non-macro entry — the caller
/// (int's Pass-1 walk) treats the head as an ordinary call in that case, not
/// an error. `Err` is reserved for genuine resolution failures (private,
/// unknown qualified module). A name absent from the view also yields
/// `Ok(None)` (a bare forward reference is not yet known to be a macro — it
/// flows to the AST builder as an ordinary reference per the locked
/// defmacro-before-use rule, §0.2 of `macro-availability-model.md`).
///
/// This replaces int's `SymbolTableMacroResolver::resolve_macro` chain-walk
/// (`src/worker.rs`) — int constructs the committed first-hop view
/// (`View::single` over the live current module) and calls this; recognition
/// is thereby a `cranelisp-types` query with **zero int→typecheck dependency**.
pub fn resolve_macro_head<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    module_aliases: &ModuleAliases,
    first_hop: &View<'_, C, L>,
    current_module: &ModuleFullPath,
    name: &str,
    span: Span,
) -> Result<Option<FQSymbol>, ResolveError>
where
    C: CodeStore,
    L: LinkerStore,
{
    match resolve(symbol_tables, module_aliases, first_hop, current_module, name, span) {
        Ok(resolved) => match &resolved.entry {
            ModuleEntry::Def { kind, .. } if matches!(kind.as_ref(), crate::DefKind::Macro { .. }) => {
                Ok(Some(resolved.fq))
            }
            _ => Ok(None),
        },
        // A name not reachable from the current view is not a macro head —
        // it is a forward / ordinary reference. Only hard failures (private,
        // unknown qualified module) surface as `Err`.
        Err(ResolveError::TraitNotFound { .. })
        | Err(ResolveError::TypeNotFound { .. })
        | Err(ResolveError::ConstructorNotFound { .. }) => Ok(None),
        Err(e @ ResolveError::PrivateInaccessible { .. })
        | Err(e @ ResolveError::QualifiedModuleUnknown { .. }) => Err(e),
    }
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

/// Chain-follow `head` to its canonical home reading committed tables. The
/// first hop already came from the caller's view; this walks the rest.
fn chain_follow_committed<C, L>(
    symbol_tables: &SymbolTables<C, L>,
    head: ModuleEntry<C>,
    home: ModuleFullPath,
) -> Option<(ModuleEntry<C>, ModuleFullPath)>
where
    C: CodeStore,
    L: LinkerStore,
{
    match &head {
        ModuleEntry::Import { source, .. } => {
            // Delegate the cross-module remainder to the existing committed
            // chain-follow primitive — single source of truth for the walk.
            resolve_terminal_entry_and_home(symbol_tables, &source.module, source.symbol.as_ref())
        }
        _ => Some((head, home)),
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
            let take = best.as_ref().map(|(len, _)| key.len() > *len).unwrap_or(true);
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
