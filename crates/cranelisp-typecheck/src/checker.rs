//! TypeCheckEnv: borrowed references to shared state for type inference.
//!
//! Scope operations, fresh variable generation, and expr_type recording.
//! Other modules extend TypeCheckEnv via `impl TypeCheckEnv<'_>` blocks.
//!
//! ## State model (Sprint 51)
//!
//! State is split between:
//! - **`TypeCheckEnv<'a>`** — borrowed references to session-owned shared state
//!   (module symbol tables, TypeId counter). Trivially constructible, `Send + Sync`.
//! - **`CheckState`** — per-check transient state created/consumed by each
//!   `check()` invocation (substitution, scope stack, resolutions, warnings).
//!   The caller owns this and passes `&mut CheckState` to methods that need it.
//!
//! All type definitions, trait declarations, trait implementations, and
//! constructor mappings are stored on per-module `SymbolTable` entries
//! (within the `modules` DashMap). The old `TypeDefRegistry`, `TraitRegistry`,
//! and `ImplRegistry` global caches have been eliminated — all lookups go
//! through the module system.
//!
//! `next_id: &AtomicU32` enables lock-free TypeId allocation for concurrent
//! `check()` calls. Module compilation locks are a scheduling concern owned
//! by the caller, not by the typechecker.

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU32, Ordering};

use dashmap::DashMap;

use cranelisp_types::{ErrorLocation,
    CranelispError, FQSymbol, FQTraitName, MethodResolutions, ModuleAliases,
    ModuleEntry, ModuleFullPath, ResolutionGap, ResolutionScope, ResolveError, ResolvedCall, Scheme,
    Span, Subst, Symbol, SymbolTable, TraitName, Type, TypeDefInfo, TypeId, TypeName,
    Warning, apply,
};

// Per single-pair invariant (`facades/typecheck.md` §"Single-pair invariant"):
// `SymbolTableRead` / `SymbolTableMut` are defined ONCE in `cluster.rs` and
// reused at the `TypeCheckEnv` interior accessor surface. No parallel
// `pub(crate)` pair lives in this file.
pub(crate) use crate::cluster::{SymbolTableMut, SymbolTableRead};

use crate::scope::ScopeStack;
use crate::scheme;
use crate::traits::ActiveConstraints;

/// Maximum depth for following Import/Reexport chains (spec §8.6.2).
const IMPORT_CHAIN_DEPTH_LIMIT: usize = 10;

/// Session-level per-module prelude-fallback flags (S78 §2.7; S108 Wave G).
///
/// `module_path → true` ⇒ a bare-name inner-miss in that module falls back to
/// the `prelude` module's own table. The prelude is **just an implicit
/// `(import [prelude [*]])`** — a prelude-provided name is in scope on
/// identical terms to an explicit import (spec §8.6.4 / §8.8.1); the fallback
/// is a resolution-mechanism detail, NOT an "outer scope" as a language
/// concept. Absent OR `false` ⇒ no fallback (the module refuses or explicitly
/// references prelude, or is a synthetic / the `prelude` module itself). `int`
/// populates this map in `inject_prelude_if_needed`; typecheck reads it
/// **read-only** at the two scope constructors.
///
/// This is the session-side companion to [`cranelisp_types::ModuleAliases`] —
/// identical key space (`ModuleFullPath`), identical threading channel
/// (`TypeCheckEnv` + `check_forms`'s parameter list). It is **session-side and
/// unserialized** (recomputed per session from source via `sexps_reference_prelude`),
/// so it carries no data on the cached `SymbolTable` shape. Per the S78 §2.7.2
/// realization fork the alias lives **here** in `cranelisp-typecheck` (option b),
/// leaving `cranelisp-types` untouched.
pub type PreludeFallback = dashmap::DashMap<ModuleFullPath, bool>;

/// The canonical name of the implicit-prelude fallback module.
///
/// A module whose [`PreludeFallback`] bit is ON resolves bare-name inner-misses
/// against this module's own table (chain-following its `(export [primitives [*]])`
/// re-export edges to canonical primitive entries, Decision 0048).
pub(crate) const PRELUDE_MODULE: &str = "prelude";

/// The **type-def view** of a resolved `ModuleEntry` — the single reader that
/// replaces the retired `ModuleEntry::TypeDef.constructor_scheme` smuggling
/// field (S79 Option 3a, FIXME 0319).
///
/// A type name resolves to one of two shapes:
/// - a `ModuleEntry::TypeDef` — the **sum/enum** case, type name distinct from
///   every ctor name; or
/// - a `ModuleEntry::Def { kind: DefKind::Constructor { type_def: Some(td), .. } }`
///   — the **single-ctor product** case, where the got-slotted ctor `Def` IS
///   its own type and carries the type facet (type-name == ctor-name).
///
/// This accessor yields `Some(&TypeDefInfo)` for either shape, so every site
/// that needs an entry *as a type* (resolution, arity validation, exhaustiveness,
/// introspection) reads it uniformly without caring which facet survived under
/// the `"Rectangle"` key.
pub(crate) fn type_def_view_of<C: cranelisp_types::CodeStore>(
    entry: &ModuleEntry<C>,
) -> Option<&TypeDefInfo> {
    match entry {
        ModuleEntry::TypeDef { info, .. } => Some(info),
        ModuleEntry::Def { kind, .. } => match kind.as_ref() {
            cranelisp_types::DefKind::Constructor {
                type_def: Some(td),
                ..
            } => Some(&**td),
            _ => None,
        },
        _ => None,
    }
}

/// Per-check transient state for type inference.
///
/// Created or reused by each `check()` call. Contains all state that is
/// accumulated during checking and either drained into `CheckResult` or
/// carried forward for the next REPL evaluation.
///
/// In the future parallel model, each concurrent `check()` will have its own
/// `CheckState` on the stack, enabling `&self` on `TypeChecker`.
pub struct CheckState {
    /// Global substitution (unification bindings).
    pub(crate) subst: Subst,
    /// Lexical scope stack.
    pub(crate) env: ScopeStack,
    /// Type of every expression, keyed by span.
    pub(crate) expr_types: HashMap<Span, Type>,
    /// How each call site was resolved (builtin operators in Ring 0).
    pub(crate) method_resolutions: MethodResolutions,
    /// Statically-resolved user-fn references discovered during body
    /// inference (FIXME 0470 + 0472, S101). Span-keyed — like
    /// `method_resolutions.resolved_calls` — so snapshot-delta extraction via
    /// the ONE shared `program::harvest_callee_edges` helper attributes each
    /// reference to the body under check at EVERY body-check seam: the Pass-2
    /// per-form seams (`check_form_body_*`) and the Pass-1 impl-method
    /// writeback (`finalize_impl_method_writeback` — impl/default/HKT method
    /// bodies). Covers BOTH call-position and value-position `Var` references
    /// that resolve (chain-follow, current-module-rooted,
    /// prelude-fallback-aware) to a module-resident `DefKind::UserFn` entry.
    /// Flows through the `write_callees_to_module_entries` sink, making
    /// `Def.callees` the COMPLETE static user-fn reference set required by
    /// the S101 dependent-recompilation transaction's reverse index
    /// (`design/int/session-transaction.md` §3.2; sole residue: mono-instance
    /// bodies, covered via their template — see `harvest_callee_edges`).
    /// Value and call edges are recorded uniformly — indistinguishable to
    /// consumers.
    pub(crate) user_fn_refs: HashMap<Span, FQSymbol>,
    /// Non-fatal warnings accumulated during checking.
    pub(crate) warnings: Vec<Warning>,
    /// Active type variable constraints during body checking (Ring 2).
    pub(crate) active_constraints: ActiveConstraints,
    /// Pending cross-module resolution gap, recorded by the `&mut`-holding
    /// resolution caller (`infer_var` / `infer_pattern_constructor`) when a
    /// qualified-name `lookup` fails AND reported a gap in-band (an
    /// alias-resolved target module absent from the session symbol tables).
    /// `check_forms` reads this after the per-form dispatcher returns an
    /// error and lifts the resulting `TypeError` to `CheckError::Gap`.
    ///
    /// The gap rides the `lookup` return value (`(Option<Scheme>,
    /// Option<ResolutionGap>)`) rather than a `&CheckState` side-channel, so
    /// this is a plain owned field written only from `&mut CheckState`
    /// contexts — no interior mutability, keeping `CheckState: Sync + Freeze`.
    /// Carries the alias-resolved target module (not the bare alias prefix).
    pub(crate) pending_gap: Option<ResolutionGap>,
    /// Transient flag: set true during `infer_apply` when inferring the callee.
    /// Used to suppress the "constrained fn as value" error for direct calls.
    pub(crate) in_call_position: bool,
    /// Pending auto-curry resolutions for single-arity functions.
    /// (call_span, function_name, applied_arg_count, total_param_count,
    /// callee_type, target_resolution, callee_var_span).
    ///
    /// `callee_var_span` (S110 W0.1b, §1.1.1) is the span of the callee `Var`,
    /// used at drain time to transport the callee's already-recorded
    /// `resolved_targets` storage carrier for a PLAIN-fn curry (resolve-once,
    /// shadow-correct — `infer_var` recorded the target's terminal storage FQ,
    /// or nothing for a local binding). `None` when the callee is not a `Var`
    /// (auto-curry requires a `Var` callee, so this is always `Some` in
    /// practice).
    pub(crate) pending_auto_curry:
        Vec<(Span, Symbol, usize, usize, Type, Option<ResolvedCall>, Option<Span>)>,
    /// Multi-sig overload table: base name → [(internal_name, arity)].
    /// Populated during pass 1 when a `Defn` has multiple variants.
    pub(crate) overloads: HashMap<Symbol, Vec<(Symbol, usize)>>,
    /// Resolved overloads: base name → [(param_types, ret_type, mangled_name)].
    /// Built during overload resolution after pass 2.
    pub(crate) resolved_overloads: HashMap<Symbol, Vec<(Vec<Type>, Type, Symbol)>>,
    /// Pending overload dispatch resolutions from call sites.
    /// (call_span, base_name, arg_types, ret_type_var)
    pub(crate) pending_overload_resolutions: Vec<(Span, Symbol, Vec<Type>, Type)>,
    /// Field-accessor synthesis collisions with a NON-accessor binding
    /// (a user `defn`, a ctor, …) — `(accessor_name, owning_type_name)`.
    /// Surfaced as a non-fatal `ShadowedName` warning at finalize: the accessor
    /// is suppressed (the existing binding wins) and the clash is reported so it
    /// is never silent (FIXME 0351(a), spec §5.2.6 safe disposition).
    pub(crate) deferred_accessor_collisions: Vec<(Symbol, String)>,
    /// Names this check synthesised as field accessors (FIXME 0351(a)). Used to
    /// classify a later accessor collision: a clash with a name in this set is
    /// a cross-type duplicate field name (POISON the bare name as ambiguous per
    /// §5.2.6 + §8.6.5 — no overload, no winner); a clash with any OTHER
    /// binding is refused. Populated per-check; a user `defn`/ctor under the
    /// same name is never in this set.
    pub(crate) synthesised_accessor_names: std::collections::HashSet<Symbol>,
    /// Per field-accessor name → the owning product types whose accessor
    /// generation registered (or poisoned) that name. A single entry means a
    /// normal first-class accessor; two-or-more means the bare name is poisoned
    /// (§5.2.6) and these are the qualified alternatives (`Box.v`, `Cup.v`)
    /// listed in the ambiguity error when bare `v` is used.
    pub(crate) accessor_owning_types:
        HashMap<Symbol, Vec<cranelisp_types::FQTypeName>>,
    /// The currently active module path for this check.
    pub(crate) current_module: ModuleFullPath,
    /// **RIGID written type variables active for the definition body currently
    /// being checked** (spec §3.3 [S109]). A written free lowercase type
    /// variable (`:a`, or one nested in `:(Box a)`) is a *fixed-but-unknown*
    /// skolem within its definition — the body may not choose what it is. These
    /// `TypeId`s are consulted by [`unify`](TypeCheckEnv::unify) (via
    /// `unify::unify_with_rigid`): a rigid var MUST NOT unify with a concrete
    /// type nor with a *distinct* rigid var (skolem-escape), while a flexible
    /// inference var MAY acquire a rigid one.
    ///
    /// **Scoped to the owning body, NOT global.** Installed by `check_defn_body`
    /// from the definition's ASSERTED-constraint param vars (`:C x`), and torn
    /// down when the body check completes. Under W6.3 (spec §3.3.1–§3.3.2) ONLY a
    /// constraint at a parameter position is rigid (held abstract over `C`); a
    /// bare written var is an ordinary flexible inference var (co-reference only,
    /// via `written_var_scope`). Outside its own body the set is empty so a
    /// forward-referencing caller instantiates every var flexibly.
    pub(crate) rigid_vars: HashSet<TypeId>,
    /// The current definition's **written-var lexical scope** — name → the one
    /// `TypeId` that name resolves to across the whole definition body,
    /// **including nested `fn` closures** (spec §3.3.1 lexical co-reference).
    /// Threaded from Pass-1 signature registration through Pass-2 body checking;
    /// `infer_annotate`/`infer_lambda` resolve written vars against it (never a
    /// fresh per-occurrence map — the 0588 seam). `None` outside a definition
    /// body; a top-level value annotation gets a transient per-annotation scope.
    /// This is ALL a bare written var carries — a name for relating occurrences,
    /// never rigidity (W6.3 backs out the W6.2 rigid-bare model).
    pub(crate) written_var_scope: Option<HashMap<Symbol, TypeId>>,
    /// The name of the definition whose body is CURRENTLY being checked, when
    /// that body was entered through `check_defn_body` (the ordinary
    /// concrete/generic Pass-2 body). Installed + torn down there; `None`
    /// otherwise (top level, and deliberately during the `check_defn_body_with_
    /// types` mono/impl-method recheck, whose self-dispatch is recorded by the
    /// monomorphise-seam SigDispatch writers instead — S110 0583 leg 2).
    ///
    /// Sole consumer: the self-recursion carve-out in
    /// [`TypeCheckEnv::record_reference_target`] — a self-call resolves the
    /// recursion LOCAL (env-shadowed), yet the backend keys it through the
    /// fn's own storage slot, so its `resolved_targets` carrier is the
    /// enclosing defn's own FQ. Compared by name only (`as_deref`).
    pub(crate) current_defn: Option<Symbol>,
}

impl CheckState {
    /// Create a new empty CheckState for the given module.
    pub fn new(module: ModuleFullPath) -> Self {
        CheckState {
            subst: Subst::new(),
            env: ScopeStack::new(),
            expr_types: HashMap::new(),
            method_resolutions: MethodResolutions::new(),
            user_fn_refs: HashMap::new(),
            warnings: Vec::new(),
            active_constraints: ActiveConstraints::default(),
            pending_gap: None,
            in_call_position: false,
            pending_auto_curry: Vec::new(),
            overloads: HashMap::new(),
            resolved_overloads: HashMap::new(),
            pending_overload_resolutions: Vec::new(),
            deferred_accessor_collisions: Vec::new(),
            synthesised_accessor_names: std::collections::HashSet::new(),
            current_defn: None,
            accessor_owning_types: HashMap::new(),
            current_module: module,
            rigid_vars: HashSet::new(),
            written_var_scope: None,
        }
    }

    /// Currently active module path for this check state.
    ///
    /// Exposed for callers that carry a `CheckState` across module
    /// boundaries (e.g., the REPL's `repl_check_state` mutex) and need to
    /// decide whether a preserved state is valid for the module about to
    /// be checked.
    pub fn current_module(&self) -> &ModuleFullPath {
        &self.current_module
    }
}

/// Borrowed references to session-owned shared state for type inference.
///
/// No owned mutable state — all mutation goes through `CheckState`
/// (passed as `&mut CheckState` to methods) or DashMap / AtomicU32
/// interior mutability.
///
/// Fields are pub(crate) so that `impl TypeCheckEnv<'_>` blocks in other
/// modules can access them directly (borrow-splitting pattern).
///
/// Multiple workers can hold `TypeCheckEnv` references concurrently
/// (it is `Send + Sync`). Each worker has its own `CheckState` on the stack.
// Sprint 58 Wave 3b (Decision 35 / 32): generic over `C: CodeStore` and
// `L: LinkerStore`. Defaults to `<(), ()>` so existing call sites within
// typecheck need no change; the integration layer instantiates with
// `<Code, ()>` (its `SessionSymbolTable` flavour). Typecheck's own code
// never reads or writes the `code` field — the parameters propagate as
// opaque type variables.
pub struct TypeCheckEnv<'a, C = (), L = ()>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Monotonic counter for fresh type variable IDs.
    ///
    /// `AtomicU32` enables lock-free allocation from concurrent `check()` calls.
    pub(crate) next_id: &'a AtomicU32,
    /// Per-module symbol tables, keyed by module full path.
    ///
    /// Behind `DashMap` for concurrent access from multiple worker threads.
    /// Each worker typechecks a different module — DashMap's per-shard locking
    /// allows concurrent reads/writes to different modules without contention.
    pub(crate) modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
    /// Optional cluster-mode staging table for the current cluster's writes.
    ///
    /// When `Some(staging)` and a write targets `staging.module`, the write
    /// is redirected to the orchestrator-handed staging table via the
    /// `RefCell` interior mutability. When `None` (or when the write targets
    /// a different module), writes flow to the per-module live table via
    /// `DashMap`. Per Decision 44 amendments: this is the Wave 3a-α
    /// write-redirection plumbing that makes `SymbolTableAccess::Cluster`
    /// staging effective from within `check_forms`.
    ///
    /// Holding a `RefCell` means a `TypeCheckEnv` carrying staging is
    /// **not `Sync`** — a single cluster is processed by a single thread
    /// (the orchestrator's `check_forms` call frame). Concurrent workers
    /// construct their own non-staging `TypeCheckEnv` instances via the
    /// `new` constructor; the staging variant is constructed only by
    /// `check_forms` for the duration of one cluster.
    ///
    /// The `TypeCheckStaging` carries two lifetimes — `'a` is the env's
    /// borrow lifetime (the outer `&RefCell` borrow), and `'a` also names
    /// the inner `&mut SymbolTable` reborrow held inside the cell, since
    /// the env's lifetime parameter is the call-frame lifetime of
    /// `check_forms` and both the outer borrow and the inner mut originate
    /// in that same frame (the env is constructed with the cell borrowed
    /// out of `SymbolTableAccess`; the cell's inner `&mut` originates from
    /// the orchestrator and lives at least as long as `check_forms`'s
    /// frame). We keep them as distinct lifetime parameters on
    /// `TypeCheckStaging` (the inner mut is invariant) but collapse them
    /// to `'a` here — the env's `'a` is shrunk to the shorter of the two
    /// when this Option is constructed.
    pub(crate) staging: Option<TypeCheckStaging<'a, 'a, C, L>>,
    /// Session-level module-alias table for §8.6.6 qualified-name
    /// resolution (longest-prefix substitution of the queried module path).
    ///
    /// Borrowed from the orchestrator's session state. Carried on the env
    /// (rather than threaded through every `resolve_qualified`/`lookup`
    /// call). The real session table always arrives caller-supplied via
    /// `new` or `new_with_staging` — there is no empty default.
    pub(crate) module_aliases: &'a ModuleAliases,
    /// Session-level per-module prelude-fallback flags (S78 §2.7; S108 Wave G).
    ///
    /// Read-only here: `int` populates the map in `inject_prelude_if_needed`,
    /// typecheck consults it at the single scope-construction seam
    /// (`scope_resolve` / `scope_resolve_in`, S108 Wave-G).
    /// When the bit for `state.current_module` is `true`, a bare-name miss in
    /// the inner (current-module) scope falls back to the `prelude` module's
    /// table. Threaded identically to `module_aliases` — borrowed from the
    /// orchestrator's session state, carried on the env. See [`PreludeFallback`].
    pub(crate) prelude_fallback: &'a PreludeFallback,
}

/// Per-cluster staging override carried on `TypeCheckEnv`.
///
/// `module` identifies which symbol-table the staging redirect applies to;
/// writes targeting any other module fall through to live as usual. `cell`
/// holds a `RefCell` wrapping the orchestrator-handed staging table by
/// mutable reference, providing interior mutability so the `&self`-flavoured
/// `current_symbol_table_mut` accessor can hand out a writable guard.
///
/// Two lifetimes: `'a` is the borrow of the `RefCell` (lives for the env's
/// lifetime); `'b` is the lifetime of the `&mut SymbolTable` inside the cell
/// (the orchestrator's mutable borrow of staging — outlives `'a`).
pub(crate) struct TypeCheckStaging<'a, 'b, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    pub(crate) module: ModuleFullPath,
    pub(crate) cell: &'a RefCell<&'b mut SymbolTable<C, L>>,
}

// SAFETY: `TypeCheckStaging` carries a `&RefCell<&mut SymbolTable>` which
// `RefCell` makes `!Sync` and the inner `&mut` makes `!Send` for the
// reborrow. The staging variant is constructed only by `check_forms` on the
// orchestrator's single thread (the entire `check_forms` call frame is a
// per-cluster, single-threaded ownership of staging). Concurrent workers
// in other parts of the codebase construct their own `TypeCheckEnv`
// instances via `new` without staging — they never share an env carrying
// staging across threads.
//
// We assert `Send + Sync` so that `TypeCheckEnv` preserves its pre-S66
// auto-impl guarantee (concurrent workers continue to construct and use
// independent envs across threads). Sharing a single env across threads
// while it carries staging is a single-cluster correctness violation that
// the public-API contract prohibits — staging mode is internal to
// `check_forms`'s call frame and not exposed to concurrent paths.
unsafe impl<'a, 'b, C, L> Send for TypeCheckStaging<'a, 'b, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
}
unsafe impl<'a, 'b, C, L> Sync for TypeCheckStaging<'a, 'b, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
}

/// A read-only view over a single module's symbol table.
///
/// This is the single home for the per-module scan/probe logic that the
/// kind-specific lookup helpers on [`TypeCheckEnv`] share (type-def
/// enumeration, single-name type-def / trait-decl probes, impl existence).
/// Each helper opens a view via [`TypeCheckEnv::read_view`] and routes through
/// the methods here, so the staging-aware enumeration (`for_each_in_module`)
/// and chain-follow discipline (Principle 17, FIXME 0179) live in one place
/// rather than being re-derived per helper.
pub(crate) struct ModuleReadView<'v, 'a, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    env: &'v TypeCheckEnv<'a, C, L>,
    module_path: &'v ModuleFullPath,
}

impl<'v, 'a, C, L> ModuleReadView<'v, 'a, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Probe this module for a type-def named `name`, chain-following
    /// `Import`/`Reexport` entries to their terminal entry.
    ///
    /// Yields the type-def view via [`type_def_view_of`] so a **single-ctor
    /// product** type (whose surviving `"Rectangle"` entry is the got-slotted
    /// ctor `Def` carrying `type_def: Some(..)`) resolves as a type just as a
    /// sum/enum `TypeDef` does.
    pub(crate) fn lookup_type_def(&self, name: &TypeName) -> Option<TypeDefInfo> {
        let entry = self.env.resolve_entry_in_module(self.module_path, name.as_ref())?;
        type_def_view_of(&entry).cloned()
    }

    /// Probe this module for a `TraitDecl` named `trait_name`, chain-following
    /// `Import`/`Reexport` entries to their terminal `TraitDecl`. Reached via
    /// `lookup_trait_decl_in_module` (test-only post S108 Wave-G).
    #[allow(dead_code)] // delegated to by the test-exercised `lookup_trait_decl_in_module`.
    pub(crate) fn lookup_trait_decl(
        &self,
        trait_name: &TraitName,
    ) -> Option<cranelisp_types::TraitDeclInfo> {
        match self.env.resolve_entry_in_module(self.module_path, trait_name.as_ref())? {
            ModuleEntry::TraitDecl { info, .. } => Some(info),
            _ => None,
        }
    }

    /// Check whether a trait impl exists for `(trait_name, impl_type)` reachable
    /// from this module (Decision 45 Pattern B): chain-follow the trait
    /// reference to its defining module H, then scan H's symbol table for a
    /// matching `TraitImpl`. No universe scan; only H is touched.
    pub(crate) fn has_impl(&self, trait_name: &TraitName, impl_type: &TypeName) -> bool {
        // Chain-follow trait reference to its defining module.
        let (terminal, trait_home) = match self
            .env
            .resolve_terminal_entry_and_home(self.module_path, trait_name.as_ref())
        {
            Some(t) => t,
            None => return false,
        };
        // Terminal must be a TraitDecl for this to be a valid trait reference.
        if !matches!(terminal, ModuleEntry::TraitDecl { .. }) {
            return false;
        }
        // Scan the trait's home only (Principle 17 shape 3). Staging-aware.
        let mut found = false;
        self.env.for_each_in_module(&trait_home, |_key, entry| {
            if found {
                return;
            }
            if let ModuleEntry::TraitImpl { trait_name: tn, impl_type: it, .. } = entry
                && &tn.name == trait_name
                && &it.name == impl_type
            {
                found = true;
            }
        });
        found
    }
}

impl<'a, C, L> TypeCheckEnv<'a, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Create a new TypeCheckEnv from borrowed shared state.
    ///
    /// The caller owns the `DashMap` and `AtomicU32`; this struct just
    /// borrows them. The caller is responsible for seeding the modules map
    /// (primitives + synthetic modules) before constructing the env; typecheck
    /// no longer assembles those (FIXME 0242 — mounted by `int` at session
    /// init).
    pub fn new(
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        next_id: &'a AtomicU32,
        module_aliases: &'a ModuleAliases,
        prelude_fallback: &'a PreludeFallback,
    ) -> Self {
        TypeCheckEnv {
            modules,
            next_id,
            staging: None,
            module_aliases,
            prelude_fallback,
        }
    }

    /// Create a `TypeCheckEnv` whose writes targeting `staging_module` flow
    /// to the orchestrator-handed staging `SymbolTable` instead of to the
    /// per-module live table.
    ///
    /// Used by `check_forms` when invoked with
    /// `SymbolTableAccess::Cluster { staging, current_module, .. }`. The caller
    /// constructs a `RefCell` wrapping the cluster's `&mut SymbolTable`
    /// staging reference and passes it here; writes targeting
    /// `staging_module` route through `RefCell::borrow_mut`. Writes to other
    /// modules (the rare cross-module impl write per Decision 0045) fall
    /// through to live unchanged — `symbol_table_mut_in` is unaffected by
    /// staging.
    ///
    /// The returned env is **not `Sync`** — it carries a `RefCell` reference.
    /// Cluster mode is single-threaded by construction (the orchestrator's
    /// `check_forms` call frame); concurrent workers use `new` without
    /// staging instead.
    pub(crate) fn new_with_staging(
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        next_id: &'a AtomicU32,
        staging_module: ModuleFullPath,
        staging_cell: &'a RefCell<&'a mut SymbolTable<C, L>>,
        module_aliases: &'a ModuleAliases,
        prelude_fallback: &'a PreludeFallback,
    ) -> Self {
        TypeCheckEnv {
            modules,
            next_id,
            staging: Some(TypeCheckStaging {
                module: staging_module,
                cell: staging_cell,
            }),
            module_aliases,
            prelude_fallback,
        }
    }

    // --- Module-scoped symbol table accessors ---

    /// Get a read wrapper for the current module's symbol table.
    ///
    /// Returns a [`SymbolTableRead`] that exposes a `view()` method producing
    /// a `View<'_, C, L>` over the held references:
    /// - In `Live` mode (no staging or staging targets another module): the
    ///   wrapper holds a DashMap `Ref` for the per-module live table; `view()`
    ///   returns `View::single(live)`.
    /// - In `Cluster` mode (staging targets the current module): the wrapper
    ///   holds the staging `RefCell::borrow()` guard plus the DashMap `Ref`;
    ///   `view()` returns `View::union(staging, live)` — staging-first.
    ///
    /// Per FIXME 0179 / Decision 44: cluster-mode reads must see in-cluster
    /// writes that landed in staging. The 9 read sites in
    /// `program.rs`/`adt.rs`/`infer.rs`/`traits.rs`/`checker.rs` go through
    /// this accessor and dispatch lookups via `view().lookup(...)` or
    /// `view().iter()`.
    ///
    /// The wrapper holds a per-shard read lock (Live mode) or a `RefCell`
    /// runtime borrow (Cluster mode) — drop it before acquiring another guard
    /// to avoid deadlocks (see design/typecheck/dashmap-migration.md §4.10) or
    /// `RefCell` borrow-check panics.
    pub fn current_symbol_table<'b>(
        &'b self,
        state: &CheckState,
    ) -> SymbolTableRead<'b, 'a, C, L> {
        let live = self.modules
            .get(&state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in modules map"));
        match &self.staging {
            Some(staging) if staging.module == state.current_module => {
                SymbolTableRead::Cluster {
                    staging: staging.cell.borrow(),
                    live,
                }
            }
            _ => SymbolTableRead::Live(live),
        }
    }

    /// Get a write guard for the current module's symbol table.
    ///
    /// Returns a `SymbolTableMut<'_, C, L>` wrapper that derefs mutably to
    /// `SymbolTable<C, L>`. In cluster mode (when `self.staging` is `Some`
    /// for the current module), the guard wraps the orchestrator-handed
    /// staging table via `RefCell::borrow_mut`. Otherwise it wraps the
    /// per-module live `DashMap` `RefMut`. Drop the guard before acquiring
    /// another one (DashMap deadlock; `RefCell` runtime borrow check).
    ///
    /// The 91 register-call sites in `program.rs` and the in-checker write
    /// sites continue to use this accessor uniformly — staging-vs-live is
    /// absorbed in the wrapper's `Deref`/`DerefMut` impls.
    pub fn current_symbol_table_mut<'b>(
        &'b self,
        state: &CheckState,
    ) -> SymbolTableMut<'b, 'a, C, L> {
        if let Some(staging) = &self.staging
            && staging.module == state.current_module
        {
            return SymbolTableMut::Staging(staging.cell.borrow_mut());
        }
        SymbolTableMut::Live(
            self.modules
                .get_mut(&state.current_module)
                .unwrap_or_else(|| {
                    unreachable!("invariant: current_module always exists in modules map")
                }),
        )
    }

    /// Get a write guard for an explicitly named module's symbol table.
    ///
    /// Used by Pattern B impl-write retargeting (Decision 45 / α15): the
    /// orchestrator selects the trait's defining module as the write target,
    /// not the writer's lexical module. Caller must ensure the module exists
    /// (typecheck invariant: `ensure_module_exists` precedes any write).
    pub(crate) fn symbol_table_mut_in(
        &self,
        module_path: &ModuleFullPath,
    ) -> dashmap::mapref::one::RefMut<'_, ModuleFullPath, SymbolTable<C, L>> {
        self.modules
            .get_mut(module_path)
            .unwrap_or_else(|| unreachable!(
                "invariant: target module '{}' must exist before write",
                module_path
            ))
    }

    /// Ensure a module's symbol table exists, creating it if needed.
    ///
    /// Uses DashMap interior mutation — safe with `&self`. Creates an empty
    /// `SymbolTable` if the module does not exist. Does NOT seed special
    /// forms (per Principle 17 + FIXME 0193 amendment — special-form
    /// metadata lives once at root `""`; other modules start empty).
    /// Does NOT set `self.state.current_module` — callers set the module
    /// on their own `CheckState`.
    ///
    /// **Sprint 67 hack-back (FIXME 0192 + 0193)**: thin shim for backwards
    /// compatibility — atomic create-if-absent via
    /// `cranelisp-types::ensure_module_exists`. Per Principle 17 amendment
    /// (FIXME 0193), regular modules start empty; special-form metadata
    /// lives once at root `""` and is NOT seeded into other modules.
    /// Internal typecheck callers continue to use this shim; cross-crate
    /// callers should call the cranelisp-types free fn directly.
    pub(crate) fn ensure_module_exists(&self, path: &ModuleFullPath) {
        let outcome = cranelisp_types::ensure_module_exists(self.modules, path);
        let trace_outcome = match outcome {
            cranelisp_types::EnsureOutcome::AlreadyPresent => {
                crate::trace::SymbolTableEnsureOutcome::AlreadyPresent
            }
            cranelisp_types::EnsureOutcome::Created => {
                crate::trace::SymbolTableEnsureOutcome::Created
            }
        };
        crate::trace::emit_symbol_table_ensure(path, trace_outcome);
    }

    /// Module-rooted lookup of a `TypeDefInfo` by bare `TypeName`.
    ///
    /// Probes `module_path`'s symbol table for `name`; if absent or if the
    /// entry is an `Import`/`Reexport`, chain-follows per Principle 17. No
    /// other modules are consulted.
    pub(crate) fn lookup_type_def_in_module(
        &self,
        module_path: &ModuleFullPath,
        name: &TypeName,
    ) -> Option<TypeDefInfo> {
        self.read_view(module_path).lookup_type_def(name)
    }


    /// Resolve a name in `module_path` to its terminal `ModuleEntry`, following
    /// `Import`/`Reexport` chains by `source.module` references (Principle 17).
    /// Returns an owned clone of the terminal entry.
    ///
    /// Staging-aware (FIXME 0179): consults staging first when
    /// `module_path == staging.module`.
    pub(crate) fn resolve_entry_in_module(
        &self,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Option<ModuleEntry<C>> {
        self.resolve_terminal_entry_and_home(module_path, name).map(|(e, _home)| e)
    }

    /// Look up the parent type name for a constructor, rooted in
    /// `module_path`.
    ///
    /// Per Principle 17 — current-module-only short-name lookup, with
    /// per-symbol chain-follow on `Import`/`Reexport` entries. Returns the bare
    /// TypeName of the parent type. A **single-ctor product** type resolves
    /// through the `Def { kind: Constructor }` arm exactly like a sum ctor (S79
    /// Option 3a): the product ctor's surviving entry under the `"Rectangle"`
    /// key is the got-slotted ctor `Def`, whose `DefKind::Constructor.type_name`
    /// names the parent type. There is no longer a separate
    /// `TypeDef`-via-`constructor_scheme` path to consult.
    ///
    /// The former no-arg `lookup_constructor_type` sibling that defaulted its
    /// root to `"user"` was deleted (S87-4, Principle 17/19 — no module is
    /// privileged by name); the `#[cfg(test)]` convenience wrapper in
    /// `test_support.rs` roots explicitly at `state.current_module`.
    pub(crate) fn lookup_constructor_type_in_module(
        &self,
        module_path: &ModuleFullPath,
        ctor_name: &str,
    ) -> Option<TypeName> {
        let entry = self.resolve_entry_in_module(module_path, ctor_name)?;
        match entry {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                cranelisp_types::DefKind::Constructor { type_name, .. } => {
                    Some(type_name.name.clone())
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// State-rooted constructor→parent-type resolve (S108 Wave-G §3.3 collapse
    /// — a thin `DefKind::Constructor` projection over [`Self::scope_resolve`]).
    /// The prelude fallback (a primitives ADT ctor re-exported via the prelude
    /// resolving as a bare ctor) and the I-1 public-only filter are intrinsic to
    /// the scope resolve; a private prelude ctor does not leak.
    ///
    /// The production caller (the `infer.rs` pattern-ctor `exists` gate) was
    /// retired when the product-fallback leg was deleted (S79 Option 3a — product
    /// ctors now resolve through their own `Def` like sum ctors); the
    /// prelude-fallback behaviour remains exercised by the `#[cfg(test)]`
    /// chokepoint regressions in `checker/tests.rs`.
    #[allow(dead_code)] // prelude-fallback chokepoint; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn lookup_constructor_type_with_state(
        &self,
        state: &CheckState,
        ctor_name: &str,
    ) -> Option<TypeName> {
        let resolved = self.scope_resolve(state, ctor_name, Span::default()).ok()?;
        match &resolved.entry {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                cranelisp_types::DefKind::Constructor { type_name, .. } => {
                    Some(type_name.name.clone())
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Check whether a constructor is marked as internal (not user-constructable).
    ///
    /// Per Principle 17 — routes through the principled lookups above.
    /// Module-rooted: pass the access root explicitly. The production gate
    /// roots at `state.current_module` via [`Self::is_internal_constructor`];
    /// tests root at the constructor's home module directly.
    pub(crate) fn is_internal_constructor_check_in_module(
        &self,
        module_path: &ModuleFullPath,
        ctor_name: &str,
    ) -> bool {
        let type_name = match self.lookup_constructor_type_in_module(module_path, ctor_name) {
            Some(tn) => tn,
            None => return false,
        };
        if let Some(info) = self.lookup_type_def_in_module(module_path, &type_name) {
            // Per S70: per-ctor `internal` lives on `DefKind::Constructor.internal`;
            // `TypeDefInfo.constructors` is `Vec<Symbol>`. Probe the named ctor's
            // Def to read its kind discriminator.
            for c_sym in &info.constructors {
                if c_sym.as_ref() == ctor_name {
                    // Chain-follow Import/Reexport entries to the constructor's
                    // home Def (e.g. `Bind` imported into `user` resolves to the
                    // `primitives` Constructor Def). A direct probe would return
                    // the Import entry, not the Constructor, and miss the
                    // `internal` discriminator.
                    if let Some(entry) = self.resolve_entry_in_module(module_path, c_sym.as_ref())
                        && let ModuleEntry::Def { kind, .. } = entry
                        && let cranelisp_types::DefKind::Constructor { internal, .. } = kind.as_ref()
                    {
                        return *internal;
                    }
                    return false;
                }
            }
        }
        false
    }

    /// State-rooted variant of [`Self::is_internal_constructor_check_in_module`].
    ///
    /// Bare-name current-module gate with the implicit-prelude **fallback**
    /// (S78 §2.7.5 — Chokepoint 1; FIXME 0317). Under §2 a re-exported
    /// internal ctor (`Bind`/`Pure`/`Effect`) is no longer an `Import` entry in
    /// the user table, so the `current_module`-rooted gate alone misses it and
    /// the value/pattern resolution (which DOES fall back) would let the
    /// internal ctor through. We mirror the value/pattern fallback: resolve the
    /// ctor's terminal entry via [`Self::resolve_entry_scoped`] (which
    /// already consults the prelude fallback under the ON bit and applies the
    /// I-1 public-only filter), then read the canonical `internal` discriminator
    /// off the terminal `DefKind::Constructor`. `Bind`/`Pure`/`Effect` are
    /// registered `Visibility::Public` in `primitives`, so the I-1 filter does
    /// NOT hide them — what rejects them is their `internal: true` discriminator,
    /// reached through the fallback.
    pub(crate) fn is_internal_constructor_check_with_state(
        &self,
        state: &CheckState,
        ctor_name: &str,
    ) -> bool {
        // Current-module-only gate first (covers in-module and locally-imported
        // ctors, plus product-type single-ctor cases routed through the
        // chain-follow in `is_internal_constructor_check_in_module`).
        if self.is_internal_constructor_check_in_module(&state.current_module, ctor_name) {
            return true;
        }
        // The current-module gate returns `false` for both "found, not internal"
        // and "not found". Under §2 the re-exported internal ctor is absent from
        // the user table, so re-resolve through the prelude-aware terminal-entry
        // path and read the `internal` discriminator off the canonical
        // Constructor Def. `resolve_entry_scoped` already applies the
        // prelude fallback (bit-gated, self-guarded) and the I-1 public
        // filter, so a private prelude ctor never reaches here.
        if let Some(ModuleEntry::Def { kind, .. }) =
            self.resolve_entry_scoped(state, ctor_name)
            && let cranelisp_types::DefKind::Constructor { internal, .. } = kind.as_ref()
        {
            return *internal;
        }
        false
    }

    /// Open a single-module read view rooted at `module_path`.
    ///
    /// The read view ([`ModuleReadView`]) is the single home for the
    /// per-module symbol-table probe logic that the kind-specific lookup
    /// helpers (`lookup_type_def_in_module`, `lookup_trait_decl_in_module`,
    /// `has_impl_in_module`) share. Each helper routes through this view so the
    /// staging-aware chain-follow discipline (Principle 17, FIXME 0179) lives in
    /// one place.
    pub(crate) fn read_view<'v>(
        &'v self,
        module_path: &'v ModuleFullPath,
    ) -> ModuleReadView<'v, 'a, C, L> {
        ModuleReadView { env: self, module_path }
    }

    /// Access the per-module symbol tables (for display, introspection).
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn modules(&self) -> &DashMap<ModuleFullPath, SymbolTable<C, L>> {
        self.modules
    }

    /// Look up a specific module's symbol table by path.
    /// Returns a DashMap read guard that derefs to `SymbolTable`.
    ///
    /// Sprint 67 hack-back (FIXME 0187 partial close — /dev (int)): narrowed
    /// to `pub(crate)`. No external consumers: REPL introspection paths in
    /// `src/session_v4.rs` read `self.shared.symbol_tables.get(path)`
    /// directly via the `CompilerSession::module_table` accessor, which is
    /// the facade-aligned shape per `design/arch/facades/int.md` §"introspection
    /// accessors".
    ///
    /// Kept for potential internal use by future typecheck code paths;
    /// `#[allow(dead_code)]` while no callers exist.
    #[allow(dead_code)]
    pub(crate) fn module_table(&self, path: &ModuleFullPath) -> Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable<C, L>>> {
        self.modules.get(path)
    }

    /// Look up a specific module's symbol table by path, returning an owned clone.
    /// Used by callers that need to own the symbol table (e.g., serialization).
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn module_table_cloned(&self, path: &ModuleFullPath) -> Option<SymbolTable<C, L>> {
        self.modules.get(path).map(|guard| guard.clone())
    }

    /// Look up a symbol's GOT slot in a specific module's symbol table.
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn get_got_slot(&self, module: &ModuleFullPath, name: &Symbol) -> Option<usize> {
        let guard = self.modules.get(module)?;
        // S83 (Principle 20): the GOT slot rides on the callable `DefKind`
        // variant, read through the single `callable_got_slot()` accessor.
        guard.get(name.as_ref())?.callable_got_slot()
    }

    /// Get a reference to the underlying modules DashMap.
    /// Used by the integration layer to construct a `CompilationEnv` that
    /// resolves GOT slots by reading symbol tables directly.
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn modules_ref(&self) -> &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>> {
        self.modules
    }

    /// The prelude module to consult as the **fallback** when a bare-name
    /// lookup misses in `current_module`, or `None` when no fallback should fire
    /// (S78 §2.7 — the one per-module ON/OFF condition, single source of truth
    /// for every bare-name resolution chokepoint). The prelude is an implicit
    /// `(import [prelude [*]])`, not an "outer scope" (spec §8.6.4 / §8.8.1).
    ///
    /// Returns `Some(prelude_path)` iff the [`PreludeFallback`] bit is ON for
    /// `current_module` **and** `current_module` is not the prelude module
    /// itself (a module never falls back onto itself). Absent/`false` ⇒ `None`
    /// (§2.7.1 absence-is-OFF). Post-S108-Wave-G this is consulted only at the
    /// two scope constructors [`Self::scope_resolve`] / [`Self::scope_resolve_in`]
    /// (the single bit-consult per surface; the I-1 public-only filter and the
    /// prelude retry are now intrinsic to `ResolutionScope::resolve`), plus the
    /// bulk trait-method-declaring scan `find_trait_method_decl` (an
    /// enumeration reader, not the resolve walk).
    pub(crate) fn prelude_fallback_target(
        &self,
        current_module: &ModuleFullPath,
    ) -> Option<ModuleFullPath> {
        if current_module.as_ref() != PRELUDE_MODULE
            && self.prelude_fallback.get(current_module).map(|b| *b).unwrap_or(false)
        {
            Some(ModuleFullPath::from(PRELUDE_MODULE))
        } else {
            None
        }
    }

    /// Single-source the scope-construction glue shared by the three resolution
    /// seams — [`Self::scope_resolve`], [`Self::scope_resolve_in`], and the
    /// [`Self::reject_def_over_binding`] adapter (S108 Wave-G §3.2; the
    /// 0564/0565 divergent-duplication category applied to this crate's own new
    /// code). Each seam differs only in which module's (staging-aware) first-hop
    /// table it resolves against; the `view()` + prelude-bit consult +
    /// `ResolutionScope::new` construction is otherwise identical, and the
    /// prelude fallback is decided ONCE here, at scope construction. The scope is
    /// passed INTO `f` rather than returned: its `first_hop` borrows the `View`
    /// guard, which must outlive the scope — a `ResolutionScope` cannot escape
    /// the borrow of the table it views.
    fn with_scope<R>(
        &self,
        read: &SymbolTableRead<'_, '_, C, L>,
        module: &ModuleFullPath,
        f: impl FnOnce(&ResolutionScope<'_, C, L>) -> R,
    ) -> R {
        let view = read.view();
        let prelude = self.prelude_fallback_target(module);
        let scope = ResolutionScope::new(
            self.modules,
            self.module_aliases,
            &view,
            module,
            prelude.as_ref(),
        );
        f(&scope)
    }

    /// THE typecheck reference lookup for a bare (unqualified) `name` against
    /// the current module (S108 Wave-G convergence §3.2 — the ONE scope
    /// constructor for the current module). Every bare-name resolution that
    /// used the retired per-site prelude-fallback resolver family (the six
    /// bare-name chokepoints of the S78 census) now routes through this one
    /// seam (`resolve_type`, `resolve_trait`, the `resolve_constructor` family,
    /// `resolve_type_expr_in_module`).
    ///
    /// The prelude fallback is **intrinsic to the scope**: it is decided ONCE
    /// at scope construction ([`Self::with_scope`] reads the prelude-fallback
    /// bit via [`Self::prelude_fallback_target`] and hands the prelude root to
    /// `ResolutionScope::new`), never at a call site — there is no caller-side
    /// retry and no per-call fallback flag. On a bare-name inner miss under an
    /// ON bit, `ResolutionScope::resolve` chain-follows prelude's
    /// `(export [primitives [*]])` re-export edges to the canonical entry, so
    /// primitives-via-prelude resolve through the fallback (not a name-key).
    /// The prelude is **just an implicit `(import [prelude [*]])`** — a
    /// prelude-provided name is in scope on identical terms to an explicit
    /// import (spec §8.6.4 / §8.8.1), NOT an "outer scope" as a language
    /// concept.
    ///
    /// The I-1 public-only filter (a private prelude entry must not leak or
    /// shadow) and the qualified-name-never-retries guard (a `mod/sym`
    /// reference names its module directly) are likewise intrinsic to
    /// `ResolutionScope::resolve`; `cranelisp-types` owns them (see
    /// `crates/cranelisp-types/src/resolve/mod.rs`). The staging∪live first-hop
    /// view selection also lives here (`current_symbol_table(state).view()`).
    ///
    /// The scope (and its borrowed guard/view) cannot be returned as a value —
    /// the `View` borrows a per-shard DashMap guard that must outlive it — so
    /// the construct-and-resolve is a single method (via [`Self::with_scope`])
    /// rather than a returned `ResolutionScope`; it is nonetheless the single
    /// scope-construction seam.
    pub(crate) fn scope_resolve(
        &self,
        state: &CheckState,
        name: &str,
        span: Span,
    ) -> Result<cranelisp_types::Resolved<C>, ResolveError> {
        let read = self.current_symbol_table(state);
        self.with_scope(&read, &state.current_module, |scope| scope.resolve(name, span))
    }

    /// Arbitrary-root scope resolve (S108 Wave-G §3.2 — collapses the former
    /// `resolve_type_expr_in_module` inline leaf-resolver copy). The first hop
    /// is a staging-aware view over `module_path`; the prelude bit is consulted
    /// for `module_path`. A qualified name inside `name` never takes the prelude
    /// retry (intrinsic to `ResolutionScope::resolve`). An absent `module_path`
    /// yields a not-found (mirroring the prior chain-follow's graceful `None`).
    pub(crate) fn scope_resolve_in(
        &self,
        module_path: &ModuleFullPath,
        name: &str,
        span: Span,
    ) -> Result<cranelisp_types::Resolved<C>, ResolveError> {
        let live = match self.modules.get(module_path) {
            Some(g) => g,
            None => {
                return Err(ResolveError::TypeNotFound {
                    name: TypeName::from(name),
                    from_module: module_path.clone(),
                    span,
                });
            }
        };
        let read = match &self.staging {
            Some(staging) if staging.module == *module_path => {
                SymbolTableRead::Cluster { staging: staging.cell.borrow(), live }
            }
            _ => SymbolTableRead::Live(live),
        };
        self.with_scope(&read, module_path, |scope| scope.resolve(name, span))
    }

    /// §8.6.4 definition-over-(import|export|prelude) rejection — the single,
    /// mode-uniform seam (FIXME 0514). A `defn`/`deftype` whose name is already
    /// bound IN SCOPE by anything OTHER than this module's OWN prior definition
    /// is a compile-time error, resolved by the fully-qualified reference.
    ///
    /// The seam glue (synthetic-name guard, resolve-in-scope, provenance
    /// classification off the scope's first-hop head, `check_binding_addition`
    /// delegate) is single-sourced in `cranelisp_types::reject_def_over_binding`
    /// (S108 Wave-G §4.1) so int's defmacro path can call the identical seam
    /// without a typecheck dependency. This method is the 3-line adapter:
    /// construct the current-module `ResolutionScope` (the ONE bit consult) and
    /// hand it to the types-owned seam.
    pub(crate) fn reject_def_over_binding(
        &self,
        state: &CheckState,
        name: &Symbol,
        span: Span,
    ) -> Result<(), CranelispError> {
        let read = self.current_symbol_table(state);
        self.with_scope(&read, &state.current_module, |scope| {
            cranelisp_types::reject_def_over_binding(scope, name, span)
        })
    }


    /// Resolve a bare type name to its `FQTypeName` via symbol-table
    /// chain-follow from `state.current_module`. Phase B Part 5 successor
    /// to the retired `fqtn_for_bare_type_name`: returns
    /// `Result<FQTypeName, ResolveError>` and never silently falls back to
    /// `current_module` or a hard-coded `primitives` map.
    ///
    /// Both `TypeDef` and `IntrinsicType` terminals resolve successfully —
    /// the FQ identity for the latter is `(home, type_name)` where `home`
    /// is the terminal module (typically `primitives`).
    pub(crate) fn resolve_type(
        &self,
        state: &CheckState,
        type_name: &TypeName,
        span: Span,
    ) -> Result<cranelisp_types::FQTypeName, ResolveError> {
        let type_not_found = || ResolveError::TypeNotFound {
            name: type_name.clone(),
            from_module: state.current_module.clone(),
            span,
        };
        let resolved = self
            .scope_resolve(state, type_name.as_ref(), span)
            .map_err(|e| project_not_found(e, type_not_found))?;
        if let Some(info) = type_def_view_of(&resolved.entry) {
            return Ok(info.name.clone());
        }
        match resolved.entry {
            ModuleEntry::IntrinsicType { .. } => {
                Ok(cranelisp_types::FQTypeName::new(resolved.home, type_name.clone()))
            }
            _ => Err(type_not_found()),
        }
    }

    /// Resolve the concrete `Type` for an impl target's bare type name.
    ///
    /// Phase B Part 1.4(3): the impl machinery needs to produce
    /// `Type::Int` (etc.) when the target is an intrinsic scalar, and
    /// `Type::ADT(target_fqtn, type_args)` for ADT-shaped types. Centralises
    /// the dispatch so `check_impl_method` / `check_hkt_impl_method` don't
    /// each replicate the kind-probe.
    ///
    /// `type_args` is the resolved type-arg vector to embed in the ADT case
    /// (empty for HKT pre-unification, populated for concrete parameterised
    /// impls like `(impl Showable (Option Int) …)`).
    pub(crate) fn concrete_type_for_impl_target(
        &self,
        state: &CheckState,
        type_name: &TypeName,
        type_args: Vec<Type>,
        span: Span,
    ) -> Result<Type, ResolveError> {
        let type_not_found = || ResolveError::TypeNotFound {
            name: type_name.clone(),
            from_module: state.current_module.clone(),
            span,
        };
        let resolved = self
            .scope_resolve(state, type_name.as_ref(), span)
            .map_err(|e| project_not_found(e, type_not_found))?;
        if let Some(info) = type_def_view_of(&resolved.entry) {
            return Ok(Type::ADT(info.name.clone(), type_args));
        }
        match resolved.entry {
            ModuleEntry::IntrinsicType { ty, .. } => Ok(ty),
            _ => Err(type_not_found()),
        }
    }

    /// Resolve a trait reference to its defining module via per-symbol
    /// chain-follow from `state.current_module`. Phase B Part 5 successor
    /// to `trait_home_for` — returns `Result<ModuleFullPath, ResolveError>`.
    ///
    /// Per Principle 17 shape 1 + Decision 45 Pattern B. No fallback —
    /// callers no longer need to combine this with a separate existence
    /// probe; the typed error carries the diagnostic context.
    pub(crate) fn resolve_trait(
        &self,
        state: &CheckState,
        trait_name: &str,
        span: Span,
    ) -> Result<ModuleFullPath, ResolveError> {
        let trait_not_found = || ResolveError::TraitNotFound {
            name: TraitName::from(trait_name),
            from_module: state.current_module.clone(),
            span,
        };
        let resolved = self
            .scope_resolve(state, trait_name, span)
            .map_err(|e| project_not_found(e, trait_not_found))?;
        match resolved.entry {
            ModuleEntry::TraitDecl { .. } => Ok(resolved.home),
            _ => Err(trait_not_found()),
        }
    }

    /// Best-effort fully-qualified render of a bare `TypeName` for a diagnostic
    /// message. Resolves `type_name` to its `FQTypeName` (`module/name`) so a
    /// "no impl" message disambiguates two same-named ADTs from different
    /// modules; falls back to the bare name when resolution fails — a
    /// diagnostic must never itself error. Read-only (routes through
    /// `scope_resolve`).
    pub(crate) fn fq_type_name_for_diagnostics(
        &self,
        state: &CheckState,
        type_name: &TypeName,
        span: Span,
    ) -> String {
        self.resolve_type(state, type_name, span)
            .map(|fq| fq.to_string())
            .unwrap_or_else(|_| type_name.to_string())
    }

    /// Best-effort fully-qualified render of a bare `TraitName` for a
    /// diagnostic message — sibling of [`Self::fq_type_name_for_diagnostics`].
    /// Chain-follows the trait reference to its defining module and renders
    /// `module/Trait`; falls back to the bare name on resolution failure.
    pub(crate) fn fq_trait_name_for_diagnostics(
        &self,
        state: &CheckState,
        trait_name: &TraitName,
        span: Span,
    ) -> String {
        self.resolve_trait(state, trait_name.as_ref(), span)
            .map(|home| FQTraitName::new(home, trait_name.clone()).to_string())
            .unwrap_or_else(|_| trait_name.to_string())
    }

    /// Resolve a constructor name to its parent type's `FQTypeName` via
    /// chain-follow from `state.current_module`. Phase B Part 5 successor
    /// to the `lookup_constructor_type[_in_module/_with_state]` triple.
    ///
    /// The old triple is retained while ~7 test fixtures and the
    /// `infer.rs:818/821` production sites still depend on it; the rename
    /// sweep for those sites is deferred per the plan §5.5 "minimum" form.
    #[allow(dead_code)]
    ///
    /// Returns `(parent_fqtn, parent_type_bare_name)`. The bare parent name
    /// is retained because some callers index `TypeDefInfo.constructors`
    /// using it after the resolve. Keeping the deferred `ConstructorIdx`
    /// augmentation for a later sprint per the plan's "minimum" variant.
    pub(crate) fn resolve_constructor(
        &self,
        state: &CheckState,
        ctor_name: &str,
        span: Span,
    ) -> Result<TypeName, ResolveError> {
        let module_path = &state.current_module;
        let ctor_not_found = || ResolveError::ConstructorNotFound {
            name: Symbol::from(ctor_name),
            from_module: module_path.clone(),
            span,
        };
        let resolved = self
            .scope_resolve(state, ctor_name, span)
            .map_err(|e| project_not_found(e, ctor_not_found))?;
        match resolved.entry {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                cranelisp_types::DefKind::Constructor { type_name, .. } => {
                    Ok(type_name.name.clone())
                }
                _ => Err(ctor_not_found()),
            },
            _ => Err(ctor_not_found()),
        }
    }

    // --- Scope operations (delegate to CheckState.env) ---

    /// Push a new scope frame.
    pub(crate) fn push_scope(&self, state: &mut CheckState) {
        state.env.push_scope();
    }

    /// Pop the topmost scope frame.
    pub(crate) fn pop_scope(&self, state: &mut CheckState) {
        state.env.pop_scope();
    }

    /// Bind a name in the current scope with a type scheme.
    pub(crate) fn bind_local(&self, state: &mut CheckState, name: Symbol, scheme: Scheme) {
        state.env.bind(name, scheme);
    }

    /// Look up a name in scope stack, falling back to current module's symbol table.
    ///
    /// Resolution order per spec §8.6.1:
    /// 1. Local environment (let bindings, fn params, match vars)
    /// 2. Module scope (current module's defs + imports, following chains)
    /// 3. Qualified name resolution: `module/name` splits on `/` and resolves
    ///    via `resolve_qualified` (spec §8.6.6)
    /// Returns `(scheme, gap)`: the resolved scheme (or `None`), plus an
    /// optional cross-module resolution gap reported in-band by qualified-name
    /// resolution. On a successful resolution the gap is always `None` (a
    /// winning candidate never carries a stale gap from a non-winning earlier
    /// probe). On failure the gap, if any, is the precise cross-module cause —
    /// the `&mut`-holding caller stores it for `check_forms`/`lift_error` to
    /// promote to `CheckError::Gap`.
    pub(crate) fn lookup(
        &self,
        state: &CheckState,
        name: &str,
    ) -> (Option<Scheme>, Option<ResolutionGap>) {
        // Check local scope stack first
        if let Some(scheme) = state.env.lookup(name) {
            return (Some(scheme.clone()), None);
        }

        // Fall back to current module's symbol table (following import chains)
        if let Some(scheme) = self.lookup_in_current_module(state, name) {
            return (Some(scheme), None);
        }

        // Try the dotted `Type.member` form (FIXME 0365 / spec §8.5.2). `Box.v`
        // resolves the field accessor `v` of `Box`; `Maybe.Some` resolves the
        // constructor `Some` of `Maybe` (S109) — both directly and
        // unconditionally, bypassing the (possibly poisoned) bare-name lookup.
        // The member is an ordinary concrete `Def`; typing it is plain
        // value-position scheme instantiation (the read here returns its
        // `Scheme`; the caller instantiates with fresh vars).
        if let Some(scheme) = self.resolve_dotted_member(state, name) {
            return (Some(scheme), None);
        }

        // Try qualified name resolution: "module/name" -> resolve_qualified
        if let Some(slash_pos) = name.find('/') {
            let module_part = &name[..slash_pos];
            let name_part = &name[slash_pos + 1..];
            if !module_part.is_empty() && !name_part.is_empty() {
                // Try child-of-current-module first: "util" in module "main"
                // resolves to "main.util" (submodule reference).
                let child_path = ModuleFullPath::from(
                    format!("{}.{}", state.current_module, module_part),
                );
                let child = self.resolve_qualified(state, &child_path, name_part);
                if let Ok((Some(scheme), _)) = child {
                    // A winning candidate carries no gap, even if it probed a
                    // missing child path first.
                    return (Some(scheme), None);
                }

                // Fall back to absolute module path. Alias substitution is
                // handled inside `resolve_qualified` (§8.6.6 longest-prefix).
                // The absolute path is the module the user actually named, so
                // its gap (if any) supersedes the child probe's — last-writer-
                // wins, matching the prior side-slot semantics.
                let abs_path = ModuleFullPath::from(module_part);
                let abs = self.resolve_qualified(state, &abs_path, name_part);
                if let Ok((Some(scheme), _)) = abs {
                    return (Some(scheme), None);
                }

                // Neither candidate resolved a scheme. Choose which cause to
                // surface (FIXME 0513, spec §8.6.4 order-independence):
                let gap = match abs {
                    // The absolute probe carried its own gap. Post-0571 this is
                    // the member-absent case too: `resolve_qualified` yields the
                    // abs `module/name` gap UNCONDITIONALLY when the module is
                    // present but the member is absent (as well as when the module
                    // itself is unknown). Surfacing it here MUST win over the
                    // child probe's phantom `<current>.<qualifier>` gap so the
                    // resolution is order-independent (a loaded absolute module
                    // always beats an unloaded child probe — FIXME 0513, spec
                    // §8.6.4); INT authors the honest "module X has no member Y"
                    // from this gap's live state (`module_has_no_member_error`).
                    Ok((_, Some(g))) => Some(g),
                    // Abs probe resolved cleanly with NEITHER scheme nor gap. This
                    // is NOT the member-absent case (that yields a gap above,
                    // post-0571); it is reachable only via `resolve_qualified`'s
                    // conservative fall-through for a future non-exhaustive
                    // `ResolveError` variant (treated as recoverable not-found, no
                    // gap). Return no gap — the phantom child gap stays suppressed.
                    Ok((_, None)) => None,
                    // A hard error from the absolute probe (e.g. a visibility
                    // violation) is not a member-absent verdict — preserve the
                    // prior last-writer-wins fall-through to the child probe's gap.
                    Err(_) => match child {
                        Ok((_, gap)) => gap,
                        Err(_) => None,
                    },
                };
                return (None, gap);
            }
        }

        (None, None)
    }

    /// Record a bare/qualified reference's storage identity into the two
    /// reference-recording feeds, resolving the name EXACTLY ONCE (Principle 24
    /// — the "Resolve once" consolidation folded in by the W0.1 top-up, 0616).
    /// Called from `infer_var` for every successfully-typed non-dotted
    /// `Expr::Var`.
    ///
    /// - **`resolved_targets`** — the backend keyed-consumer carrier (S110
    ///   0583, `design/arch/backend-keyed-consumer.md` §1.1/§1.1.2). Keyed at
    ///   the referencing `Var` span, the value is `resolved.storage_fq()` — the
    ///   TERMINAL STORAGE key the walk surfaced, "whichever storage key HIT" —
    ///   for EVERY table-resolved kind (user fn, primitive, constructor,
    ///   platform effect, host-promised extern, mangled/mono variants a
    ///   chain-follow lands on — any terminal `ModuleEntry::Def`). This is NOT
    ///   `resolved.fq`: for a member-canonical-keyed symbol (sum ctor, field
    ///   accessor) or a renamed import/re-export, `fq` composes the WRITTEN
    ///   alias spelling while `storage_fq()` carries the terminal table key the
    ///   backend's `entry_at` reads directly (FIXME 0620, W1.1). Rides UNREAD
    ///   in W0/W0.1 (behaviour-invariant); W1 keys the backend's ONE fetch on
    ///   it.
    /// - **`user_fn_refs`** — the `Def.callees` edge feed (FIXME 0470, S101).
    ///   Records `resolved.fq` (NOT `storage_fq()`) — `callees` is a persisted
    ///   `.meta.json` value pinned this schema window; its own alias residual
    ///   is FIXME 0621. Kept only when the terminal is a `DefKind::UserFn`
    ///   `Def` (a `UserFn`-filtered PROJECTION of the single resolution).
    ///   `BuiltinFn` is always available (no codegen dependency); non-`UserFn`
    ///   redefinition falls back to module-grain reload
    ///   (session-transaction §10 trigger T1).
    ///
    /// This single resolution replaces the former THREE probes of one name
    /// (`lookup` + `resolve_user_fn_ref_fq` + `resolved_target_fq`) — the F1
    /// chokepoint the S101 `record_user_fn_ref` established, now widened + made
    /// resolve-once.
    ///
    /// Gates: a LOCAL binding (fn param, `let`, `match`, lambda param) shadows
    /// module scope — a shadowed name records NEITHER feed — with ONE
    /// carve-out: the enclosing defn's own recursion binding records the
    /// `resolved_targets` carrier (see below). Self-edges stay OUT of `callees`
    /// (the documented cheap disposition — `save.rs::dependency_sort` filters
    /// them). Dotted `Type.member` references are recorded by the dedicated
    /// [`Self::resolve_dotted_member_fq`] leg in `infer_var` (they never
    /// resolve through `scope_resolve`) and, per the S101 residue, feed only
    /// `resolved_targets`, never `callees`.
    pub(crate) fn record_reference_target(
        &self,
        state: &mut CheckState,
        name: &str,
        span: Span,
    ) {
        // Local scope shadows module scope (spec §8.6.1 resolution order).
        if state.env.lookup(name).is_some() {
            // Self-recursion carve-out (S110 0583 leg 2, FIXME 0616):
            // `check_defn_body` binds the enclosing defn's OWN name as a
            // recursion LOCAL, so the env-shadow gate fires — but the backend
            // compiles a non-tail self-call through `resolve_got_target` on the
            // fn's own name (the recursion local is NOT a backend local). So
            // record the enclosing defn's own storage FQ as the carrier,
            // EXPLICITLY diverging from the `callees` self-edge skip: the two
            // feeds' gates are semantically different — a self-edge is unwanted
            // in the call graph, yet the self-call IS a table reference the
            // backend keys. `resolved_targets` only; never `callees`.
            if state.current_defn.as_deref() == Some(name) {
                let fq = FQSymbol {
                    module: state.current_module.clone(),
                    symbol: Symbol::from(name),
                };
                state.method_resolutions.resolved_targets.insert(span, fq);
            }
            return;
        }
        // Ordinary bare/qualified reference: resolve ONCE, record both feeds
        // (any-`Def` for the carrier; `UserFn`-filtered projection for callees).
        if let Some(resolved) = self.resolve_ref_target(state, name, span) {
            state
                .method_resolutions
                .resolved_targets
                .insert(span, resolved.storage_fq());
            if let ModuleEntry::Def { kind, .. } = &resolved.entry
                && matches!(kind.as_ref(), cranelisp_types::DefKind::UserFn { .. })
            {
                state.user_fn_refs.insert(span, resolved.fq);
            }
        }
    }

    /// Resolve `name` to its terminal storage `Resolved` for the
    /// reference-recording feeds, mirroring [`Self::lookup`]'s qualified
    /// candidate order (child-of-current-module before absolute path) so the
    /// recorded identity agrees with the scheme the reference type-checked
    /// against. Resolves ONCE (Principle 24); the caller projects the kind
    /// filter each feed needs. Returns `None` for a non-`Def` terminal (a
    /// local, a type, a special form, an unresolved name).
    fn resolve_ref_target(
        &self,
        state: &CheckState,
        name: &str,
        span: Span,
    ) -> Option<cranelisp_types::Resolved<C>> {
        if let Some(slash_pos) = name.find('/') {
            let module_part = &name[..slash_pos];
            let name_part = &name[slash_pos + 1..];
            if !module_part.is_empty() && !name_part.is_empty() {
                let child = format!(
                    "{}.{}/{}",
                    state.current_module, module_part, name_part,
                );
                if let Some(r) = self.def_resolved(state, &child, span) {
                    return Some(r);
                }
            }
        }
        self.def_resolved(state, name, span)
    }

    /// One chain-follow + prelude-fallback resolution of a single candidate
    /// spelling, kept only when it terminates at a `ModuleEntry::Def` of ANY
    /// kind (S110 0583 — the backend discriminates the kind off the fetched
    /// entry; Principle 24). Does NOT filter on `DefKind`; the caller applies
    /// any projection.
    pub(crate) fn def_resolved(
        &self,
        state: &CheckState,
        name: &str,
        span: Span,
    ) -> Option<cranelisp_types::Resolved<C>> {
        let resolved = self.scope_resolve(state, name, span).ok()?;
        matches!(&resolved.entry, ModuleEntry::Def { .. }).then_some(resolved)
    }

    /// Resolve a dotted `Type.member` field-accessor reference to its accessor
    /// `Scheme` (FIXME 0365 Item 1 / spec §8.5.2, INVERTED model §1.6).
    ///
    /// `Box.v` is the **canonical** field accessor of type `Box` — a real,
    /// uniformly-Public `Def` keyed `Type.field` in `Box`'s home module. It
    /// resolves directly and unconditionally (no ambiguity ever): `Box.v` always
    /// names exactly the `Box`-`v` accessor, even when the bare alias `v` is
    /// contested (the bare `v` is the convenience alias whose ambiguity is the
    /// resolution concern, never the canonical dotted form). The split is on the
    /// FIRST `.`: the head (`Box`) is a type name in bare scope, the tail (`v`)
    /// the field.
    ///
    /// The read is the canonical accessor `Def.scheme` (Principle 7 — the
    /// `Def.scheme` is the single source of the accessor's type;
    /// `committed_accessor_kind` is the single "is this an accessor of this
    /// type" judgment). The caller (`lookup`) instantiates the returned scheme
    /// with fresh vars, so the dotted form is an ordinary first-class callable
    /// typed `(Fn [Type] FieldType)` — no special value-position handling. (The
    /// bare alias `v` resolves via the ordinary `Import`-chain-follow path in
    /// `lookup_in_current_module`, not here.)
    ///
    /// Returns `None` when `name` is not a `Type.member` form, the head does not
    /// name a type in scope, or `member` is not a field accessor of that type
    /// (the caller then proceeds to the `/`-split / undefined-variable path).
    fn resolve_dotted_member(
        &self,
        state: &CheckState,
        name: &str,
    ) -> Option<Scheme> {
        let entry = self.resolve_dotted_member_entry(state, name)?;
        self.extract_scheme_from_entry_owned(&entry, 0)
    }

    /// Resolve a dotted `Type.member` reference to the terminal `ModuleEntry` of
    /// the member it names — a field accessor (`Box.v`) OR a constructor
    /// (`Maybe.Some`, S109). This is the ONE member-resolution core both value
    /// position (`resolve_dotted_member` → scheme, via `lookup`) and pattern
    /// position (`resolve_constructor_entry`'s dotted arm) consume, so the two
    /// agree by construction (spec §6.2.1 "mirrors value position exactly";
    /// `design/typecheck/dotted-ctor-registration.md` §3.1).
    ///
    /// The head (`Type`) resolves to its `FQTypeName` in bare scope, and the
    /// member is probed under the canonical `member_key(Type, member)` in the
    /// type's HOME module — rooting the probe there (not the current module) is
    /// what makes the dotted form work cross-module. Accepted only when the
    /// terminal is a member OWNED BY THAT EXACT type (accessor of `fqtn` or ctor
    /// of `fqtn`), so a degenerate product form (`Point.Point`, no such key) and
    /// a non-member head both yield `None`.
    pub(crate) fn resolve_dotted_member_entry(
        &self,
        state: &CheckState,
        name: &str,
    ) -> Option<ModuleEntry<C>> {
        self.dotted_member_identity(state, name).map(|(_, entry)| entry)
    }

    /// The STORAGE FQ of a dotted `Type.member` reference (S110 0583 leg 3,
    /// FIXME 0616) — the canonical `(fqtn.module, member_key(Type, member))`
    /// key `resolve_dotted_member_entry` probes, recorded into
    /// `resolved_targets`. The reference resolves via the dotted core, NOT
    /// `scope_resolve`, so the W0 bare-name re-probe missed it whenever only a
    /// type-only import was present (`(import [m [Maybe]])` then
    /// `(Maybe.Some 3)` — the always-works dotted spelling, S109). `None` when
    /// `name` is not a dotted member of a type in scope. Feeds only
    /// `resolved_targets` (dotted member refs are `callees` residue).
    pub(crate) fn resolve_dotted_member_fq(
        &self,
        state: &CheckState,
        name: &str,
    ) -> Option<FQSymbol> {
        self.dotted_member_identity(state, name).map(|(fq, _)| fq)
    }

    /// Shared core of [`Self::resolve_dotted_member_entry`] /
    /// [`Self::resolve_dotted_member_fq`] (single source of truth, Principle 7):
    /// resolve a dotted `Type.member` form to `(storage FQ, terminal entry)`.
    /// The identity is `(fqtn.module, member_key(Type, member))` — exactly what
    /// the entry probe hits.
    fn dotted_member_identity(
        &self,
        state: &CheckState,
        name: &str,
    ) -> Option<(FQSymbol, ModuleEntry<C>)> {
        // A `Type.member` form: exactly one `.`, both sides non-empty. A
        // module-qualified `m/Type` head carries a `/`, which the `/`-split
        // path owns — restrict the dotted member to a bare type head here.
        let dot = name.find('.')?;
        let type_part = &name[..dot];
        let member_part = &name[dot + 1..];
        if type_part.is_empty() || member_part.is_empty() || member_part.contains('.')
            || type_part.contains('/') || member_part.contains('/')
        {
            return None;
        }

        // Resolve the head to its `FQTypeName` (current-module-or-prelude). A
        // non-type head (a value `Var`, an unknown name) yields `None` — not a
        // member reference.
        let resolved = self
            .scope_resolve(state, type_part, Span::default())
            .ok()?;
        let fqtn = type_def_view_of(&resolved.entry)?.name.clone();

        // Probe the CANONICAL key `Type.member` directly (the real Public member
        // `Def`, inverted model) in the type's home module, union-view (staging
        // then live). Accept it only when it is a member owned by this exact type.
        let key = cranelisp_types::member_key(&fqtn.name, member_part);
        let entry = self.probe_module_entry_owned(&fqtn.module, key.as_ref())?;
        match crate::adt::committed_member_owner(&entry) {
            Some(owner) if owner == fqtn => Some((
                FQSymbol { module: fqtn.module, symbol: key },
                entry,
            )),
            _ => None,
        }
    }

    /// Look up a name in the current module's symbol table, following
    /// Import/Reexport chains to their source definitions.
    ///
    /// Clone-and-drop discipline: clone the entry from the guard, drop the
    /// guard, then follow import chains (which may access other modules).
    ///
    /// In cluster mode (FIXME 0179): consults staging first via
    /// [`Self::probe_module_entry_owned`], so in-cluster writes are visible
    /// to downstream resolution.
    fn lookup_in_current_module(&self, state: &CheckState, name: &str) -> Option<Scheme> {
        // The scope resolve returns the chain-followed terminal entry;
        // `extract_scheme_from_entry_owned`'s own re-follow of a terminal `Def`
        // is idempotent, so projecting `.entry` is behaviour-identical to
        // returning the head and following downstream.
        let entry = self.scope_resolve(state, name, Span::default()).ok()?.entry;
        self.extract_scheme_from_entry_owned(&entry, 0)
    }

    /// Probe a name in `module_path`'s symbol table, returning an owned
    /// clone of the `ModuleEntry`. Staging-aware: in cluster mode, when
    /// `module_path == staging.module`, staging entries shadow live.
    ///
    /// Clone-and-drop discipline: clones the entry while the guard is
    /// held, then drops the guard before returning. The orchestrator's
    /// staging is borrowed via `RefCell::borrow()` for the duration of
    /// the probe.
    pub(crate) fn probe_module_entry_owned(
        &self,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Option<ModuleEntry<C>> {
        // Staging-first when applicable. The borrow is short-lived (clone
        // and drop).
        if let Some(staging) = &self.staging
            && staging.module == *module_path
        {
            let borrow = staging.cell.borrow();
            if let Some(entry) = borrow.get(name) {
                return Some(entry.clone());
            }
        }
        let guard = self.modules.get(module_path)?;
        guard.get(name).cloned()
    }

    /// Iterate over the union of staging + live for `module_path`,
    /// invoking `f` for each (name, entry) pair. Staging entries shadow
    /// live entries with the same key.
    ///
    /// Staging-aware (FIXME 0179): in cluster mode, when
    /// `module_path == staging.module`, the iteration covers staging
    /// first then live entries not shadowed by staging keys. The closure
    /// receives owned clones of the names/entries to avoid borrow
    /// entanglement between staging (RefCell::borrow) and live (DashMap
    /// Ref).
    pub(crate) fn for_each_in_module<F>(
        &self,
        module_path: &ModuleFullPath,
        mut f: F,
    )
    where
        F: FnMut(&Symbol, &ModuleEntry<C>),
    {
        // Snapshot staging entries first (if applicable). Drop the
        // staging borrow before acquiring the DashMap read guard to
        // avoid simultaneous-guard pitfalls.
        let mut staging_keys: HashSet<Symbol> = HashSet::new();
        if let Some(staging) = &self.staging
            && staging.module == *module_path
        {
            let borrow = staging.cell.borrow();
            for (k, v) in borrow.all_symbols() {
                staging_keys.insert(k.clone());
                f(k, v);
            }
        }
        if let Some(guard) = self.modules.get(module_path) {
            for (k, v) in guard.all_symbols() {
                if !staging_keys.contains(k) {
                    f(k, v);
                }
            }
        }
    }

    /// Extract a Scheme from a ModuleEntry, following Import/Reexport chains.
    ///
    /// `depth` tracks recursion to enforce the chain depth limit (spec §8.6.2).
    /// Named `_owned` to emphasise the caller should clone the entry before calling,
    /// ensuring no DashMap guard is held during chain following.
    fn extract_scheme_from_entry_owned(
        &self,
        entry: &ModuleEntry<C>,
        depth: usize,
    ) -> Option<Scheme> {
        if depth > IMPORT_CHAIN_DEPTH_LIMIT {
            return None; // Pathological chain — give up
        }

        match entry {
            // A single-ctor product type's scheme lives canonically on its
            // got-slotted ctor `Def` (S79 Option 3a) — the `TypeDef`-via-
            // `constructor_scheme` smuggling arm is retired.
            ModuleEntry::Def { scheme, .. } => Some(scheme.clone()),
            ModuleEntry::Import { source, .. } => {
                self.resolve_fq_symbol(source, depth + 1)
            }
            _ => None,
        }
    }

    /// Resolve a fully-qualified symbol reference by looking up the source
    /// module's symbol table.
    ///
    /// Clone-and-drop discipline: clone entry from guard, drop guard,
    /// then follow chain. Staging-aware (FIXME 0179): when
    /// `fq.module == staging.module`, staging shadows live.
    fn resolve_fq_symbol(&self, fq: &FQSymbol, depth: usize) -> Option<Scheme> {
        let entry = self.probe_module_entry_owned(&fq.module, fq.symbol.as_ref())?;
        self.extract_scheme_from_entry_owned(&entry, depth)
    }

    /// Resolve a bare `name` in the current-module SCOPE to its terminal
    /// `ModuleEntry`, following Import/Reexport chains. Returns an owned clone.
    ///
    /// `_scoped`, not `_in_current_module`: the resolve is a projection over
    /// [`Self::scope_resolve`], so the implicit-prelude **fallback** is intrinsic
    /// (an inner miss under an ON [`PreludeFallback`] bit resolves against the
    /// prelude's table; the prelude is an implicit `(import [prelude [*]])`, spec
    /// §8.6.4 / §8.8.1) — the lookup is NOT current-module-only. The I-1
    /// public-only filter is likewise intrinsic. Sibling of the `_scoped` family
    /// ([`Self::resolve_terminal_entry_scoped`] / [`Self::resolve_terminal_fq_scoped`]).
    ///
    /// Staging-aware (FIXME 0179): consults staging first via
    /// [`Self::probe_module_entry_owned`].
    pub(crate) fn resolve_entry_scoped(&self, state: &CheckState, name: &str) -> Option<ModuleEntry<C>> {
        // Terminal-entry projection over the single scope resolve (S108 Wave-G).
        // The same-cluster same-module member-alias hop (bare ctor/field-accessor
        // → canonical `Type.member`) is handled at the resolution PRIMITIVE
        // (`cranelisp_types::resolve::chain_follow_committed`, staging-view hop,
        // W1 commit 1 / `dotted-ctor-canonical-keys.md` §3.5), not here.
        self.scope_resolve(state, name, Span::default()).ok().map(|resolved| resolved.entry)
    }

    /// Resolve a **constructor reference** in a pattern to its terminal
    /// `ModuleEntry`, dispatching on whether the name is bare or
    /// module-qualified.
    ///
    /// - **Bare** (`SCons`): rooted at `state.current_module` with the
    ///   implicit-prelude fallback (Principle 17 + S78 §2) — exactly
    ///   [`Self::resolve_entry_scoped`].
    /// - **Qualified** (`macros/SCons`): an FQ reference that bypasses import
    ///   scope (spec §8.6.6) and roots directly in the named module via
    ///   [`Self::resolve_entry_in_module`]. Quasiquote macros lower their
    ///   templates into qualified `macros/SCons`/`macros/SNil` patterns, so this
    ///   arm is load-bearing for every macro. The prior `lookup_constructor_scheme`
    ///   product-fallback leg (which performed this `/`-split before reading the
    ///   scheme) was retired with S79 Option 3a; the split lives here now so a
    ///   qualified SUM ctor still resolves through its `Def { Constructor }`
    ///   entry. No product special-case — a single-ctor product type's ctor
    ///   `Def` carries `type_name`/`tag` identically.
    pub(crate) fn resolve_constructor_entry(
        &self,
        state: &CheckState,
        name: &str,
    ) -> Option<ModuleEntry<C>> {
        // **Dotted `Type.Ctor` (S109, design §3.3).** A dotted head (`.` and no
        // `/`) is a canonical constructor reference — resolve it through the SAME
        // member core the value seam uses, so value and pattern agree by
        // construction. `(Maybe.Some x)` and dotted nullary `Maybe.Nil` resolve
        // to the canonical ctor `Def` for both same-module and imported types
        // (the current-module literal-key hit worked only same-module). The caller
        // filters the returned entry to `DefKind::Constructor`.
        if name.contains('.') && !name.contains('/') {
            return self.resolve_dotted_member_entry(state, name);
        }
        if let Some(slash_pos) = name.find('/') {
            let module_str = &name[..slash_pos];
            let bare_name = &name[slash_pos + 1..];
            let module_path = ModuleFullPath::from(module_str);
            self.resolve_entry_in_module(&module_path, bare_name)
        } else {
            self.resolve_entry_scoped(state, name)
        }
    }

    /// Resolve a bare name to its terminal `(entry, home)` against the current
    /// module, with the implicit-prelude **fallback** on an inner
    /// miss when the module's [`PreludeFallback`] bit is ON (S78 §2.7.5 —
    /// Chokepoint 1, trait-method/impl-discovery extension for FIXME 0315).
    /// The prelude is an implicit `(import [prelude [*]])`, not an "outer
    /// scope" as a language concept (spec §8.6.4 / §8.8.1).
    ///
    /// This is the `(entry, home)`-returning sibling of
    /// [`Self::resolve_entry_scoped`]. The trait-method dispatch
    /// path (`method_to_trait_with_state`) and the impl-discovery path
    /// (`has_impl_with_state` via [`ModuleReadView::has_impl`]) both root the
    /// trait/method reference at `state.current_module` and chain-follow per
    /// Decision 45 Pattern B; when the trait + impl live in the prelude (the
    /// current module misses, bit ON), the chain-follow head must be sought in
    /// the prelude's own table first. Routing those sites through this helper
    /// mirrors the value/type/constructor fallback the other chokepoints
    /// already perform — a bare operator (`+`, `==`, …) backed by a prelude
    /// `deftrait`/`impl` resolves through the fallback, not a name-key.
    ///
    /// The recorded `home` is the module that hosts the **terminal** entry, so
    /// downstream impl scans (`for_each_in_module(home, …)`) land on the trait's
    /// true defining module regardless of which scope (current or prelude)
    /// supplied the head reference.
    pub(crate) fn resolve_terminal_entry_scoped(
        &self,
        state: &CheckState,
        name: &str,
    ) -> Option<(ModuleEntry<C>, ModuleFullPath)> {
        // Project the fq-carrying resolver's `Resolved` to (terminal entry, home).
        self.resolve_terminal_fq_scoped(state, name)
            .map(|resolved| (resolved.entry, resolved.home))
    }

    /// Like [`Self::resolve_terminal_entry_scoped`] but returns the full
    /// [`Resolved`] triple so the caller can read the canonical **terminal**
    /// symbol (`resolved.fq.symbol`) — the bare local name in the home module,
    /// with any `module/symbol` qualifier and module alias already resolved away.
    ///
    /// FIXME 0488 (sig a/b): the pass-4 monomorphisation collectors record the
    /// callee's *reference* name and re-use it downstream as a symbol-table key
    /// (`get_constrained_fn`'s home-probe, the mangled-name builder). For an FQ
    /// reference (`gen/iden2`, `user/iden`) that reference name is the raw
    /// qualified string, which is never a table key — so no mono is minted.
    /// Canonicalising at collection to the terminal symbol + home makes the FQ
    /// reference mint/dispatch under the same bare-mangled name as the bare call.
    ///
    /// [`Resolved`]: cranelisp_types::Resolved
    pub(crate) fn resolve_terminal_fq_scoped(
        &self,
        state: &CheckState,
        name: &str,
    ) -> Option<cranelisp_types::Resolved<C>> {
        // The full `Resolved` triple over the single scope resolve (S108 Wave-G).
        self.scope_resolve(state, name, Span::default()).ok()
    }

    /// Chain-follow a name starting from `module_path` to its canonical home,
    /// returning `(terminal_entry, terminal_module)`. Per Principle 17 and
    /// Decision 45 — used by Pattern B impl resolution.
    ///
    /// Walks per-symbol `ModuleEntry::Import` / `ModuleEntry::Reexport`
    /// bindings one edge at a time along `source.module` references until a
    /// canonical (non-Import/non-Reexport) entry is reached. Returns the
    /// terminal entry plus the module that hosts it (the defining module).
    /// Returns `None` if no entry exists for `name` in `module_path`, the
    /// chain is malformed, or the chain depth limit is exceeded.
    ///
    /// Staging-aware (FIXME 0179): consults staging first via
    /// [`Self::probe_module_entry_owned`].
    pub(crate) fn resolve_terminal_entry_and_home(
        &self,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Option<(ModuleEntry<C>, ModuleFullPath)> {
        let entry = self.probe_module_entry_owned(module_path, name)?;
        self.chain_follow_to_home(entry, module_path.clone(), 0)
    }

    /// Recursive helper for [`Self::resolve_terminal_entry_and_home`].
    fn chain_follow_to_home(
        &self,
        entry: ModuleEntry<C>,
        home: ModuleFullPath,
        depth: usize,
    ) -> Option<(ModuleEntry<C>, ModuleFullPath)> {
        if depth > IMPORT_CHAIN_DEPTH_LIMIT {
            return None;
        }
        match &entry {
            ModuleEntry::Import { source, .. } => {
                let next_home = source.module.clone();
                let next_entry = self.probe_module_entry_owned(&source.module, source.symbol.as_ref())?;
                self.chain_follow_to_home(next_entry, next_home, depth + 1)
            }
            _ => Some((entry, home)),
        }
    }

    /// Resolve a qualified name `module_path/name` (spec §8.6.6).
    ///
    /// Bypasses local scope. Checks visibility — private names are inaccessible
    /// from outside the defining module's subtree (spec §8.7.3).
    ///
    /// Returns `(scheme, gap)`: `scheme` is the resolved type scheme (or
    /// `None` if not found). `gap` is `Some(..)` when the alias-resolved
    /// target module is absent from the session symbol tables — a cross-module
    /// resolution gap. The gap is reported in-band (not via a `&CheckState`
    /// side-slot) so the `lookup` fallback chain can still satisfy the name
    /// via another candidate; only the `&mut`-holding caller promotes a
    /// surviving gap to `CheckError::Gap` once the chain is exhausted.
    pub(crate) fn resolve_qualified(
        &self,
        state: &CheckState,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Result<(Option<Scheme>, Option<ResolutionGap>), CranelispError> {
        // Compose the qualified `module/symbol` form the scope resolve consumes;
        // it applies §8.6.6 longest-prefix alias substitution to the module part,
        // chain-follows the symbol within the resolved module, and runs the
        // §8.7.3 visibility filter. A qualified name names its module directly
        // and never takes the prelude retry (intrinsic to the scope resolve), so
        // routing it through `scope_resolve` is behaviour-identical to the former
        // bare `cranelisp_types::resolve` call.
        let qualified = format!("{module_path}/{name}");
        match self.scope_resolve(state, &qualified, Span::SYNTHETIC) {
            Ok(resolved) => Ok((self.extract_scheme_from_entry_owned(&resolved.entry, 0), None)),
            // Module present, symbol absent (S109 0571 B4/B5). Yield the gap
            // UNCONDITIONALLY (supersedes FIXME 0513's gap-less arm): typecheck
            // reports "the qualified reference `module/name` did not resolve"
            // and stays scheduler-free; INT decides from the module's live state
            // (Principle 3/17) — module present-but-non-terminal ⇒ park (a genuine
            // FQ cycle then converts to the honest circular-dependency error via
            // `block_for_typecheck`'s acyclicity check), terminal ⇒ the honest
            // "module X has no member Y" diagnostic. The gap carries the referenced
            // `module/name` so INT need not re-probe. The `lookup` gap-selection
            // (abs probe wins over the phantom child) keeps the 0513
            // order-independence: the abs member-absent gap is preferred, so the
            // phantom `<current>.<qualifier>` child gap never surfaces.
            Err(ResolveError::TypeNotFound { .. })
            | Err(ResolveError::TraitNotFound { .. })
            | Err(ResolveError::ConstructorNotFound { .. }) => Ok((
                None,
                Some(ResolutionGap::SymbolTypechecked(FQSymbol {
                    module: module_path.clone(),
                    symbol: Symbol::from(name),
                })),
            )),
            // Alias-resolved target module absent from the session tables: the
            // precise cross-module resolution gap. Reported in-band so the
            // fallback chain is not short-circuited; the `&mut`-holding caller
            // promotes a surviving gap to `CheckError::Gap`.
            Err(ResolveError::QualifiedModuleUnknown { module, name: sym, .. }) => Ok((
                None,
                Some(ResolutionGap::SymbolTypechecked(FQSymbol { module, symbol: sym })),
            )),
            // Visibility violation: a hard error (the symbol exists but is
            // private to a module outside the accessor's subtree).
            Err(e @ ResolveError::PrivateInaccessible { .. }) => Err(CranelispError::from(e)),
            // `ResolveError` is `#[non_exhaustive]`: a future variant is
            // treated as a non-recoverable not-found (no gap), matching the
            // conservative "the fallback chain may still satisfy it" default.
            Err(_) => Ok((None, None)),
        }
    }

    // --- Fresh variable generation ---

    /// Allocate the next fresh `TypeId`, advancing the monotonic atomic counter.
    ///
    /// Per `design/arch/facades/typecheck.md` §"Cluster check scaffolding" —
    /// one of the two facade-prescribed `TypeCheckEnv` public methods (the
    /// other being `new`). External callers use this when threading the
    /// shared `next_id` atomic into their own driver state.
    ///
    /// Uses `fetch_add` on the atomic counter — safe for `&self`. The
    /// `&mut self` receiver in the facade text is the as-designed
    /// signature; the implementation uses interior mutability for the
    /// atomic so the receiver discipline doesn't actually require
    /// exclusive borrow. Kept `&mut self` for consistency with the facade
    /// API ledger.
    pub fn next_type_id(&mut self) -> TypeId {
        self.next_id.fetch_add(1, Ordering::Relaxed)
    }

    /// Generate a fresh type variable.
    ///
    /// Uses `fetch_add` on the atomic counter — safe for `&self`.
    pub(crate) fn fresh_var(&self) -> Type {
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        Type::Var(id)
    }

    /// Generate a fresh type variable and return both the type and ID.
    /// Used by ADT registration to allocate type parameter variables.
    ///
    /// Uses `fetch_add` on the atomic counter — safe for `&self`.
    pub(crate) fn fresh_var_id(&self) -> (Type, TypeId) {
        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        (Type::Var(id), id)
    }

    /// Create a temporary mutable counter for functions that need `&mut TypeId`.
    ///
    /// Takes a snapshot of the atomic counter, returns a mutable local copy.
    /// The caller must call `commit_next_id` after using it to advance the
    /// atomic past any IDs allocated through the local counter.
    ///
    /// SAFETY: Only safe when the scheduler guarantees no concurrent allocation
    /// (e.g., during module registration, which is serialized per module).
    pub(crate) fn next_id_snapshot(&self) -> TypeId {
        self.next_id.load(Ordering::Relaxed)
    }

    /// Advance the atomic counter to at least `new_val`.
    /// Called after using a local counter from `next_id_snapshot`.
    pub(crate) fn commit_next_id(&self, new_val: TypeId) {
        self.next_id.fetch_max(new_val, Ordering::Relaxed);
    }

    // --- Unification (delegate to unify module, borrow-splitting) ---

    /// Unify two types. Wraps the free function with state's subst.
    /// `span` is used for error context.
    pub(crate) fn unify(
        &self,
        state: &mut CheckState,
        t1: &Type,
        t2: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        crate::unify::unify_with_rigid(&mut state.subst, &state.rigid_vars, t1, t2).map_err(|e| {
            // Re-wrap with the caller's span if the error has SYNTHETIC span
            if e.span() == Span::SYNTHETIC {
                CranelispError::TypeError {
                    message: e.message().to_string(),
                    location: ErrorLocation::from_span(span),
                }
            } else {
                e
            }
        })
    }

    // --- Scheme operations ---

    /// Instantiate a scheme with fresh variables.
    ///
    /// If the scheme has constraints, they are tracked on the fresh variables
    /// in `self.active_constraints` for later propagation during generalize.
    pub(crate) fn instantiate(&self, state: &mut CheckState, s: &Scheme) -> Type {
        if s.constraints.is_empty() {
            self.instantiate_scheme(s)
        } else {
            self.instantiate_constrained(state, s)
        }
    }

    /// Build a collision-free instantiation substitution mapping each
    /// quantified variable in `quantified` to a genuinely fresh variable.
    ///
    /// Each fresh var is guaranteed NOT to equal any var in `quantified`.
    /// This is the soundness contract of HM instantiation: instantiating a
    /// scheme must rename its bound variables apart from any live variable,
    /// in particular apart from the scheme's own bound variables.
    ///
    /// A collision arises across module boundaries when the per-session
    /// `next_id` counter has not been advanced past an imported scheme's
    /// quantified TypeIds (e.g. a polymorphic identity `(Fn [a] a)` with
    /// `type_vars: [1]` instantiated while `next_id` is still ≤ 1). Without
    /// this guard `fresh_var()` returns `Var(1)`, the substitution becomes the
    /// identity self-map `{1 -> Var(1)}`, and `apply` chases `1 -> Var(1) ->
    /// Var(1) -> …` forever (FIXME 0279/0295 — the compiler stack overflow).
    /// Re-rolling fresh ids on collision makes instantiation correct
    /// regardless of the counter's state.
    fn fresh_instantiation_subst(&self, quantified: &[TypeId]) -> Subst {
        let bound: std::collections::HashSet<TypeId> = quantified.iter().copied().collect();
        let mut inst_subst = Subst::new();
        for &var_id in quantified {
            // Allocate a fresh var that does not collide with any of the
            // scheme's own quantified vars — re-roll if the counter has not
            // been advanced past them.
            let fresh = loop {
                let (fresh_ty, fresh_id) = self.fresh_var_id();
                if !bound.contains(&fresh_id) {
                    break fresh_ty;
                }
            };
            inst_subst.insert(var_id, fresh);
        }
        inst_subst
    }

    /// Instantiate a scheme by replacing each quantified variable with a fresh variable.
    /// Uses atomic `fresh_var()` — safe for `&self`.
    pub(crate) fn instantiate_scheme(&self, scheme: &Scheme) -> Type {
        if scheme.type_vars.is_empty() {
            return scheme.ty.clone();
        }
        let inst_subst = self.fresh_instantiation_subst(&scheme.type_vars);
        apply(&inst_subst, &scheme.ty)
    }

    /// Generalize a type relative to the current environment,
    /// propagating any active constraints on the quantified variables.
    ///
    /// Constraints are resolved through the substitution: if a constraint
    /// was recorded on var X, and X is unified with var Y (the scheme var),
    /// the constraint attaches to Y. This handles the case where
    /// `instantiate_constrained` records a constraint on a fresh var that
    /// gets unified with a different var during type checking.
    pub(crate) fn generalize(&self, state: &CheckState, ty: &Type) -> Scheme {
        let env_fv = state.env.free_vars_in_env();
        let mut scheme = scheme::generalize(&state.subst, ty, &env_fv);

        // Build a set of scheme vars for fast lookup
        let scheme_var_set: std::collections::HashSet<TypeId> =
            scheme.type_vars.iter().copied().collect();

        // Propagate constraints from active_constraints to the scheme,
        // resolving through the substitution.
        let mut constraints: std::collections::HashMap<TypeId, Vec<_>> =
            std::collections::HashMap::new();

        for (constrained_var, traits) in state.active_constraints.all() {
            // Resolve the constrained var through the substitution
            let resolved = apply(&state.subst, &Type::Var(*constrained_var));
            if let Type::Var(resolved_id) = resolved
                && scheme_var_set.contains(&resolved_id)
            {
                // Multiple `constrained_var`s can `apply`-resolve onto the SAME
                // scheme var; a plain `.extend(...)` then concatenates without
                // dedup, yielding garbled runs like `[Eq, Display, Display]`
                // (FIXME 0354 Bug A). Dedup the extend so a stacked-bound binder
                // gets a clean witness layout (`[Eq, Display]`).
                let bucket = constraints.entry(resolved_id).or_default();
                for t in traits {
                    if !bucket.contains(t) {
                        bucket.push(t.clone());
                    }
                }
            }
        }

        if !constraints.is_empty() {
            scheme.constraints = constraints;
        }

        scheme
    }

    // --- Expression type recording ---

    /// Record the inferred type for an expression (keyed by span).
    pub(crate) fn record_expr_type(&self, state: &mut CheckState, span: Span, ty: Type) {
        state.expr_types.insert(span, ty);
    }

    /// Clear transient inference state (expr_types, method_resolutions,
    /// active_constraints) accumulated during type-checking.
    ///
    /// Called after inline trait registration (e.g., from test setup) to
    /// prevent stale entries from leaking into subsequent program checking.
    /// Does NOT clear `subst` because unification results from registration
    /// are harmless (all concrete).
    #[cfg(test)]
    pub(crate) fn clear_transient_state(state: &mut CheckState) {
        state.expr_types.clear();
        state.method_resolutions.resolved_calls.clear();
        state.user_fn_refs.clear();
        state.active_constraints = ActiveConstraints::default();
    }

    /// Apply the current substitution to a type.
    pub(crate) fn apply_subst(&self, state: &CheckState, ty: &Type) -> Type {
        apply(&state.subst, ty)
    }

    // --- REPL query methods for output formatting ---

    /// Look up the FQTypeName for a bare type name via SymbolTables.
    /// Used for display formatting and diagnostics.
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn fqtn_for_type(&self, type_name: &TypeName) -> Option<cranelisp_types::FQTypeName> {
        let user_path = ModuleFullPath::from("user");
        self.lookup_type_def_in_module(&user_path, type_name)
            .map(|info| info.name)
    }

    /// Module-rooted variant of trait-impl enumeration.
    pub(crate) fn get_impls_for_type_in_module(
        &self,
        module_path: &ModuleFullPath,
        type_name: &TypeName,
    ) -> Vec<TraitName> {
        let mut traits: Vec<TraitName> = Vec::new();
        // Collect candidate trait names from the current module (shape 4 —
        // bulk current-module-only introspection). Each candidate is then
        // chain-followed (shape 3) per Decision 45.
        // Staging-aware (FIXME 0179): iterate the union of staging + live
        // for `module_path`.
        let candidates: Vec<TraitName> = {
            let mut acc = Vec::new();
            self.for_each_in_module(module_path, |name, entry| {
                match entry {
                    ModuleEntry::TraitDecl { .. }
                    | ModuleEntry::Import { .. } => {
                        acc.push(TraitName::from(name.as_ref()));
                    }
                    _ => {}
                }
            });
            acc
        };
        // Track visited trait homes so we don't double-scan.
        let mut visited_homes: std::collections::HashSet<ModuleFullPath> =
            std::collections::HashSet::new();
        for candidate in candidates {
            let trait_home = match self.resolve_terminal_entry_and_home(
                module_path,
                candidate.as_ref(),
            ) {
                Some((ModuleEntry::TraitDecl { .. }, home)) => home,
                _ => continue,
            };
            if !visited_homes.insert(trait_home.clone()) {
                continue;
            }
            // Staging-aware (FIXME 0179): trait_home may equal
            // staging.module when the trait + impl are both in-cluster.
            self.for_each_in_module(&trait_home, |_key, entry| {
                if let ModuleEntry::TraitImpl { trait_name, impl_type, .. } = entry
                    && &impl_type.name == type_name
                    && !traits.contains(&trait_name.name)
                {
                    traits.push(trait_name.name.clone());
                }
            });
        }
        traits.sort();
        traits
    }

    /// State-rooted variant of [`Self::get_impls_for_type`]. Reserved for
    /// future internal callers (`/repl` and session-layer REPL formatters
    /// currently use the public default-rooted variant).
    #[allow(dead_code)]
    pub(crate) fn get_impls_for_type_with_state(
        &self,
        state: &CheckState,
        type_name: &TypeName,
    ) -> Vec<TraitName> {
        self.get_impls_for_type_in_module(&state.current_module, type_name)
    }

    /// Module-rooted lookup of a `TraitDecl` by bare `TraitName`.
    ///
    /// The state-rooted `lookup_trait_decl_with_state` caller was retired at the
    /// S108 Wave-G convergence (the `deftrait` duplicate check became a raw
    /// same-module `probe_module_entry_owned` probe); this module-rooted variant
    /// (and the `ModuleReadView::lookup_trait_decl` it delegates to) now serves
    /// the unit suite (`builtins.rs`, `test_support.rs`, `registry/tests.rs`).
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn lookup_trait_decl_in_module(
        &self,
        module_path: &ModuleFullPath,
        trait_name: &TraitName,
    ) -> Option<cranelisp_types::TraitDeclInfo> {
        self.read_view(module_path).lookup_trait_decl(trait_name)
    }

    /// Resolve a trait reference to its `TraitDeclInfo` — a thin `TraitDecl`
    /// kind-projection over [`Self::resolve_terminal_entry_scoped`], the single
    /// scope resolve (S108 Wave-G §3.3; the fallback is intrinsic, not
    /// advertised in the name). Used by the `(impl <trait> <type> …)` form's
    /// `trait_name` so a prelude-globbed trait (reachable at `user` only via
    /// the implicit prelude glob, no `Import` edge) resolves exactly as a bare
    /// `Display` resolves in a lookup position; a genuinely-unknown name yields
    /// `None` (the impl site still raises `unknown trait`).
    pub(crate) fn resolve_trait_decl(
        &self,
        state: &CheckState,
        trait_name: &TraitName,
    ) -> Option<cranelisp_types::TraitDeclInfo> {
        let (terminal, _home) =
            self.resolve_terminal_entry_scoped(state, trait_name.as_ref())?;
        match terminal {
            ModuleEntry::TraitDecl { info, .. } => Some(info),
            _ => None,
        }
    }

    /// Look up which trait a method name belongs to.
    ///
    /// Per Principle 17 — current-module-only short-name lookup with
    /// per-symbol chain-follow on `Import`/`Reexport` entries. Probes the
    /// (default `user`) module for `method_name`; if it resolves to a
    /// canonical `ModuleEntry::Def` carrying `trait_origin`, returns the
    /// bare trait name. No universe scan.
    pub(crate) fn method_to_trait(&self, method_name: &Symbol) -> Option<TraitName> {
        let user_path = ModuleFullPath::from("user");
        self.method_to_trait_in_module(&user_path, method_name)
    }

    /// Module-rooted variant of [`Self::method_to_trait`].
    pub(crate) fn method_to_trait_in_module(
        &self,
        module_path: &ModuleFullPath,
        method_name: &Symbol,
    ) -> Option<TraitName> {
        let entry = self.resolve_entry_in_module(module_path, method_name.as_ref())?;
        match entry {
            ModuleEntry::Def { trait_origin: Some(fqtn), .. } => Some(fqtn.name.clone()),
            _ => None,
        }
    }

    /// State-rooted variant of [`Self::method_to_trait`].
    ///
    /// Roots the method-name probe at `state.current_module` and, on an inner
    /// miss, consults the implicit-prelude fallback when the module's
    /// fallback bit is ON (S78 §2.7.5 / FIXME 0315) — so a bare operator backed
    /// by a prelude `deftrait` (e.g. `(+ a b)` against a prelude `Num`) is
    /// recognised as a trait method.
    pub(crate) fn method_to_trait_with_state(
        &self,
        state: &CheckState,
        method_name: &Symbol,
    ) -> Option<TraitName> {
        let (entry, _home) =
            self.resolve_terminal_entry_scoped(state, method_name.as_ref())?;
        match entry {
            ModuleEntry::Def { trait_origin: Some(fqtn), .. } => Some(fqtn.name.clone()),
            _ => None,
        }
    }

    /// Check if a method belongs to a specific trait, via trait_origin on ModuleEntry::Def.
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn method_belongs_to_trait(&self, method: &Symbol, trait_name: &TraitName) -> bool {
        self.method_to_trait(method).as_ref() == Some(trait_name)
    }

    /// Check if a trait impl exists for the given (trait_name, impl_type) pair.
    ///
    /// Per Decision 45 (Pattern B) — chain-follow the trait reference from
    /// the (default `user`) module to its defining module, then probe that
    /// one module's symbol table for the synthetic key
    /// `impl$<FQTypeName>$<FQTraitName>`. No universe scan.
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn has_impl(&self, trait_name: &TraitName, impl_type: &TypeName) -> bool {
        let user_path = ModuleFullPath::from("user");
        self.has_impl_in_module(&user_path, trait_name, impl_type)
    }

    /// Module-rooted variant of [`Self::has_impl`].
    pub(crate) fn has_impl_in_module(
        &self,
        module_path: &ModuleFullPath,
        trait_name: &TraitName,
        impl_type: &TypeName,
    ) -> bool {
        self.read_view(module_path).has_impl(trait_name, impl_type)
    }

    /// State-rooted variant of [`Self::has_impl`].
    ///
    /// Chain-follows the trait reference from `state.current_module`, with the
    /// implicit-prelude fallback on an inner miss when the
    /// module's fallback bit is ON (S78 §2.7.5 / FIXME 0315). Once the trait's
    /// defining module is located (whether the head reference came from the
    /// current module or the prelude), the `TraitImpl` scan runs over that home
    /// only (Decision 45 Pattern B) — so a prelude `impl Num Int` is discovered
    /// for a bare `(+ …)` in a user module that misses the trait locally.
    pub(crate) fn has_impl_with_state(
        &self,
        state: &CheckState,
        trait_name: &TraitName,
        impl_type: &TypeName,
    ) -> bool {
        // Chain-follow the trait reference to its defining module, with the
        // prelude fallback for bare prelude-backed traits.
        let (terminal, trait_home) =
            match self.resolve_terminal_entry_scoped(state, trait_name.as_ref()) {
                Some(t) => t,
                None => return false,
            };
        if !matches!(terminal, ModuleEntry::TraitDecl { .. }) {
            return false;
        }
        self.has_impl_in_home(&trait_home, trait_name, impl_type)
    }

    /// Does the trait's ALREADY-RESOLVED home module carry an impl of
    /// `trait_name` for `impl_type`? The home-rooted core of
    /// [`Self::has_impl_with_state`]: a caller that already holds the trait's
    /// defining module — e.g. `infer_annotate`'s value-position satisfaction
    /// check, which resolves a QUALIFIED constraint's module directly (mirroring
    /// `resolve_bound_param`) — checks the impl here without a second bare-name
    /// resolution. Impls are written to the trait's defining module (Decision
    /// 45), so scanning the home only is complete (Principle 17 shape 3).
    /// Staging-aware.
    pub(crate) fn has_impl_in_home(
        &self,
        trait_home: &ModuleFullPath,
        trait_name: &TraitName,
        impl_type: &TypeName,
    ) -> bool {
        let mut found = false;
        self.for_each_in_module(trait_home, |_key, entry| {
            if found {
                return;
            }
            if let ModuleEntry::TraitImpl { trait_name: tn, impl_type: it, .. } = entry
                && &tn.name == trait_name
                && &it.name == impl_type
            {
                found = true;
            }
        });
        found
    }

    /// Read the `impl_module` (storage of the mangled method `Def`s — the
    /// impl-WRITER's module) off the `ModuleEntry::TraitImpl` shell in the
    /// trait's ALREADY-RESOLVED home (S110 W0.1b,
    /// `design/arch/backend-keyed-consumer.md` §1.1.1). Probes the exact
    /// canonical shell key first (a direct staging-aware keyed get), then falls
    /// back to a bare-name match (mirroring [`Self::has_impl_in_home`]) for an
    /// intrinsic-receiver head skew between the dispatch-site `fq_for_mangle`
    /// and the definition-site `fq_impl_type`. Returns `None` only if no shell
    /// exists — the caller (which has already proven the impl exists via
    /// `has_impl_with_state`) degrades to `current_module`.
    pub(crate) fn impl_module_in_home(
        &self,
        trait_home: &ModuleFullPath,
        impl_key: &str,
        trait_name: &TraitName,
        impl_type: &TypeName,
    ) -> Option<ModuleFullPath> {
        // Exact canonical-key probe (staging-aware).
        if let Some(ModuleEntry::TraitImpl { impl_module, .. }) =
            self.probe_module_entry_owned(trait_home, impl_key)
        {
            return Some(impl_module);
        }
        // Bare-name fallback for a head skew (intrinsic receiver), mirroring
        // `has_impl_in_home`.
        let mut found = None;
        self.for_each_in_module(trait_home, |_key, entry| {
            if found.is_some() {
                return;
            }
            if let ModuleEntry::TraitImpl {
                trait_name: tn,
                impl_type: it,
                impl_module,
                ..
            } = entry
                && &tn.name == trait_name
                && &it.name == impl_type
            {
                found = Some(impl_module.clone());
            }
        });
        found
    }

    /// Module-rooted variant of trait-impl-type enumeration (Decision 45 Pattern B).
    pub(crate) fn get_implementing_types_in_module(
        &self,
        module_path: &ModuleFullPath,
        trait_name: &TraitName,
    ) -> Vec<TypeName> {
        let mut types: Vec<TypeName> = Vec::new();
        // Chain-follow trait reference to its defining module.
        let trait_home = match self.resolve_terminal_entry_and_home(
            module_path,
            trait_name.as_ref(),
        ) {
            Some((ModuleEntry::TraitDecl { .. }, home)) => home,
            _ => return types, // trait not reachable from this module
        };
        // Enumerate impls in the trait's home only. Staging-aware (FIXME 0179).
        self.for_each_in_module(&trait_home, |_name, entry| {
            if let ModuleEntry::TraitImpl { trait_name: tn, impl_type, .. } = entry
                && &tn.name == trait_name && !types.contains(&impl_type.name)
            {
                types.push(impl_type.name.clone());
            }
        });
        types.sort();
        types
    }

    /// State-rooted variant of [`Self::get_implementing_types`]. Reserved
    /// for future internal callers.
    #[allow(dead_code)]
    pub(crate) fn get_implementing_types_with_state(
        &self,
        state: &CheckState,
        trait_name: &TraitName,
    ) -> Vec<TypeName> {
        self.get_implementing_types_in_module(&state.current_module, trait_name)
    }

    // --- Module state management ---

    /// Unregister a trait.
    ///
    /// The trait declaration and methods are on the module's SymbolTable,
    /// which is removed by `remove_module`. TraitImpl entries are also on
    /// module SymbolTables, so removing the module removes them too.
    /// This method is now a no-op but kept for API compatibility.
    ///
    /// Used during module hot-reload (repl/spec.md §14.2).
    #[allow(dead_code)] // no-op kept for symmetry with remove_module; exercised via TestFixture.
    pub(crate) fn unregister_trait(&self, _trait_name: &TraitName) {
        // TraitImpl entries live on module SymbolTables — removing the module
        // (done by remove_module before this is called) removes them.
    }

    /// Remove a module's symbol table and unregister its types and traits.
    ///
    /// Removes the CompiledModule from the modules map and cleans up:
    /// - Trait declarations (from trait_registry)
    ///
    /// Type definitions and constructor-to-type mappings are stored on the
    /// module's SymbolTable, so removing the module implicitly removes them.
    ///
    /// Returns the removed symbol table, or None if the module was not found.
    /// Used during module hot-reload (repl/spec.md §14.2).
    #[allow(dead_code)] // reserved for REPL `/reload` cache invalidation path.
    pub(crate) fn remove_module(&self, module_path: &ModuleFullPath) -> Option<SymbolTable<C, L>> {
        let (_, table) = self.modules.remove(module_path)?;

        // Unregister traits defined by this module.
        let traits_to_remove: Vec<TraitName> = table
            .all_symbols()
            .filter_map(|(_, entry)| {
                if let ModuleEntry::TraitDecl { info, .. } = entry {
                    Some(info.name.clone())
                } else {
                    None
                }
            })
            .collect();
        for trait_name in &traits_to_remove {
            self.unregister_trait(trait_name);
        }

        // Type definitions and constructor mappings are on the SymbolTable,
        // so removing the module from self.modules is sufficient.

        Some(table)
    }

    /// Insert a fresh (empty) module symbol table.
    ///
    /// Used after `remove_module` to re-establish the module path before
    /// recompilation populates it with fresh definitions.
    #[allow(dead_code)] // reserved for REPL `/reload` cache invalidation path.
    pub(crate) fn insert_module(&self, table: SymbolTable<C, L>) {
        self.modules.insert(table.path.clone(), table);
    }

    // --- Cache restoration ---
    //
    // Sprint 67 hack-back (FIXME 0192 method 11 split): `restore_cached_module`
    // and `restore_cached_impls` are deleted. Callers (currently
    // `CompilerSession::introduce_module`'s cache-hit branch in
    // `src/session_v4.rs`) compose primitives directly:
    //   1. `cranelisp_typecheck::advance_next_id_past_table(next_id, &table)`
    //      to preserve the TypeId-consistency invariant.
    //   2. `cranelisp_types::install_module(modules, path, table)` to atomically
    //      install the decoded `SymbolTable`.
    // `restore_cached_impls` was a no-op (trait impls live on the cached
    // `SymbolTable` and arrive with it) — deleted with no replacement.

    // --- Type-expression resolution (for source annotations) ---

    /// Resolve a source `TypeExpr` against `module_path`'s import scope.
    ///
    /// Replaces the deleted `known_type_names*` snapshot builders + the
    /// `resolve.rs` free-function-over-map convention. Resolution matches
    /// directly on the terminal [`ModuleEntry`] reached by per-name
    /// chain-follow (`resolve_terminal_entry_and_home`) — no intermediate map
    /// is materialised. Bare references resolve in `module_path`; qualified
    /// `module/Name` references (`TypeRef.module = Some(m)`) resolve in `m`.
    ///
    /// Per Principle 17 — resolution is import-scoped to the calling module's
    /// own symbol table + chain-follow; no other modules are consulted for a
    /// bare name.
    pub(crate) fn resolve_type_expr_in_module(
        &self,
        texpr: &cranelisp_types::TypeExpr,
        var_map: &std::collections::HashMap<Symbol, TypeId>,
        module_path: &ModuleFullPath,
        span: Span,
    ) -> Result<Type, ResolveError> {
        // Type-definition context (`deftype` field, platform sig): a `TypeVar`
        // that is not a declared parameter is an unbound reference and a miss is
        // an error (`mint_free_var: None`). (Trait-method signatures do NOT route
        // through here — they resolve via `traits/type_resolve.rs`, which mints
        // their own type-var map; see FIXME 0590.) The caller's `var_map` is
        // read-only here, so clone into a scratch map — no minting means the
        // clone is never mutated.
        let mut scratch = var_map.clone();
        self.resolve_type_expr_impl(texpr, &mut scratch, module_path, None, span)
    }

    /// Resolve an **annotation** type expression (`defn`/`fn` parameter, a value
    /// annotation `:a form`, or a type var nested in an applied annotation
    /// `:(Box a)`) to its [`Type`], **minting a fresh type variable** for each
    /// free lowercase type-var name the source author writes (spec §3.3 [S109]).
    ///
    /// The minted var is bound in `var_map`, so repeated names within one
    /// resolution — and across the whole definition when the caller threads ONE
    /// shared scope (the `written_var_scope`) — co-refer (`[:a x :a y]` shares
    /// `a`; a body `:a` co-refers to a param `:a`). A name already in `var_map`
    /// is REUSED (not re-minted).
    ///
    /// **A minted bare var is FLEXIBLE — it carries only a display name (spec
    /// §3.3.1 [S109 W6.3]).** Rigidity is NOT a property of the written var; it
    /// lives on the CONSTRAINT path (`check_defn_body` seeds
    /// `CheckState::rigid_vars` from asserted-constraint param vars only). A
    /// `defn`/`fn` parameter, a body/value annotation, and a nested-`fn`
    /// parameter all mint flexible ids — the body MAY pin one to a concrete type
    /// (never an error, §3.3.1 MUST (a)), and a nested `fn` that leaves a written
    /// var polymorphic is a legitimate rank-1 poly value (W6.3 ruling — no eager
    /// escape check; the genuine restrictions are enforced by the value
    /// restriction + unification + the §3.11 gate).
    pub(crate) fn resolve_annotation_type_expr_in_module(
        &self,
        texpr: &cranelisp_types::TypeExpr,
        var_map: &mut std::collections::HashMap<Symbol, TypeId>,
        module_path: &ModuleFullPath,
        span: Span,
    ) -> Result<Type, ResolveError> {
        let mint = || self.fresh_var_id().1;
        self.resolve_type_expr_impl(texpr, var_map, module_path, Some(&mint), span)
    }

    /// Shared resolution core for both the type-definition path
    /// ([`resolve_type_expr_in_module`], `mint_free_var: None`) and the
    /// annotation path ([`resolve_annotation_type_expr_in_module`],
    /// `mint_free_var: Some(..)`).
    fn resolve_type_expr_impl(
        &self,
        texpr: &cranelisp_types::TypeExpr,
        var_map: &mut std::collections::HashMap<Symbol, TypeId>,
        module_path: &ModuleFullPath,
        mint_free_var: Option<&dyn Fn() -> TypeId>,
        span: Span,
    ) -> Result<Type, ResolveError> {
        // Leaf-name resolution routes through the arbitrary-root scope resolve
        // (S108 Wave-G §3.3 — this inline leaf-resolver copy collapses onto
        // `scope_resolve_in`). The prelude fallback for a bare `TypeRef`, the
        // I-1 public-only filter, the qualified-name-never-retries guard, and
        // the staging-aware first hop are ALL intrinsic to the scope resolve.
        // The structural `TypeExpr` recursion (arity validation, type-var
        // allocation) stays in `crate::resolve::resolve_type_expr`.
        let resolve_terminal = |tref: &cranelisp_types::TypeRef| -> Option<ModuleEntry<C>> {
            // A self-qualified ref (`:t/Box` from inside module `t`) names the
            // requester's OWN module by FQ name. It must resolve against the
            // in-progress cluster staging exactly as a bare `:Box` does — the
            // qualified path reads only COMMITTED tables, so during
            // cluster-atomic typecheck the in-cluster `Box` (still in staging,
            // not yet committed) is invisible to it (FIXME 0362). Collapse
            // `module == current_module` to the bare path: the composed `name`
            // becomes just the leaf, and the staging-aware first-hop view in
            // `scope_resolve_in` carries the in-progress definition. A genuinely
            // cross-module qualified ref keeps the `module/name` form and
            // resolves against the committed home (Principle 17 — only the SELF
            // case changes).
            let is_self_qualified = tref.module.as_ref() == Some(module_path);
            let name: String = match &tref.module {
                Some(m) if !is_self_qualified => format!("{m}/{}", tref.name),
                _ => tref.name.to_string(),
            };
            self.scope_resolve_in(module_path, &name, span).ok().map(|resolved| resolved.entry)
        };
        crate::resolve::resolve_type_expr(texpr, var_map, &resolve_terminal, mint_free_var, span)
    }

    /// Resolve a **qualified** `TypeRef` (`module: Some(..)`) appearing in a
    /// trait-method signature to its `Type`, via the canonical
    /// `resolve_type_expr_in_module` path (the same resolution `defn`/`deftype`
    /// type refs use). Returns `None` if the qualified name does not resolve to
    /// a type — the caller (`resolve_trait_type_expr`) then raises the
    /// "unknown type" diagnostic. FIXME 0436 / spec §8.5: a qualified type ref
    /// is the canonical form of the bare type, resolved against the named
    /// module.
    pub(crate) fn resolve_qualified_method_sig_type(
        &self,
        state: &CheckState,
        tref: &cranelisp_types::TypeRef,
        span: Span,
    ) -> Option<Type> {
        let texpr = cranelisp_types::TypeExpr::Named(tref.clone());
        let empty_var_map = std::collections::HashMap::new();
        self.resolve_type_expr_in_module(&texpr, &empty_var_map, &state.current_module, span)
            .ok()
    }

    /// Check whether a constructor name refers to an internal constructor.
    ///
    /// Internal constructors (e.g. `Bind` for the IO type) cannot be
    /// constructed or pattern-matched by user code.
    pub(crate) fn is_internal_constructor(&self, state: &CheckState, name: &Symbol) -> bool {
        // Strip module prefix for qualified names like "primitives/Bind"
        let bare_name: &str = if let Some(slash_pos) = name.as_ref().find('/') {
            &name.as_ref()[slash_pos + 1..]
        } else {
            name.as_ref()
        };
        self.is_internal_constructor_check_with_state(state, bare_name)
    }

}

/// Re-project a `ResolveError` from the general primitive into a kind-specific
/// not-found, preserving the richer failures.
///
/// The primitive uses `TypeNotFound`-shaped messaging as its neutral
/// fallback for an unreachable bare name (it does not know the caller's kind).
/// The kind-specific `resolve_*` wrappers re-label that neutral not-found with
/// the kind they expected (so a missing trait reads "unknown trait", a missing
/// constructor reads "unknown constructor", etc.). The discriminating failures
/// — `PrivateInaccessible` and `QualifiedModuleUnknown` — carry diagnostic
/// context the wrapper cannot improve on, so they pass through unchanged
/// (`QualifiedModuleUnknown` in particular is the gap signal `resolve_qualified`
/// promotes to a load-and-retry).
fn project_not_found(
    err: ResolveError,
    kind_specific: impl FnOnce() -> ResolveError,
) -> ResolveError {
    match err {
        ResolveError::PrivateInaccessible { .. }
        | ResolveError::QualifiedModuleUnknown { .. } => err,
        // Every not-found-shaped variant (and any future `#[non_exhaustive]`
        // addition) re-labels with the caller's kind-specific not-found.
        _ => kind_specific(),
    }
}

/// Advance `next_id` past the maximum TypeId found in `table`'s schemes.
///
/// Sprint 67 hack-back (FIXME 0192 method 11 split): the cache-hit branch
/// of `CompilerSession::introduce_module` calls this free fn against the
/// shared `next_id` atomic before `cranelisp_types::install_module` is
/// invoked. The TypeId-consistency invariant is typecheck-internal (it
/// prevents fresh vars from colliding with cached vars during
/// `apply_subst`), so the work stays in this crate; the orchestration is
/// hoisted to `int` per the FIXME 0192 disposition.
pub fn advance_next_id_past_table<C, L>(
    next_id: &AtomicU32,
    table: &SymbolTable<C, L>,
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut max_id: Option<TypeId> = None;
    for (_name, entry) in table.all_symbols() {
        let scheme = match entry {
            ModuleEntry::Def { scheme, .. } => Some(scheme),
            _ => None,
        };
        if let Some(s) = scheme {
            if let Some(id) = cranelisp_types::max_type_var_id(&s.ty) {
                max_id = Some(max_id.map_or(id, |m: TypeId| m.max(id)));
            }
            for &v in &s.type_vars {
                max_id = Some(max_id.map_or(v, |m| m.max(v)));
            }
            for &v in s.constraints.keys() {
                max_id = Some(max_id.map_or(v, |m| m.max(v)));
            }
        }
    }
    if let Some(id) = max_id {
        next_id.fetch_max(id + 1, Ordering::Relaxed);
    }
}

// ---------------------------------------------------------------------------
// Test fixture + test module (extracted to sibling submodule files)
// ---------------------------------------------------------------------------

#[cfg(test)]
pub(crate) mod test_support;
#[cfg(test)]
pub(crate) use test_support::TestFixture;

#[cfg(test)]
mod tests;
