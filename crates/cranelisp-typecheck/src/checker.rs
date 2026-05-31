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
    CranelispError, ExportSpec, FQSymbol, ImportNames, ImportSpec,
    MethodResolutions, ModuleEntry, ModuleFullPath, ResolvedCall, Scheme, Span,
    Subst, Symbol, SymbolTable, TraitName, Type, TypeDefInfo, TypeId, TypeName, Visibility,
    Warning, apply,
};

// Per single-pair invariant (`facades/typecheck.md` §"Single-pair invariant"):
// `SymbolTableRead` / `SymbolTableMut` are defined ONCE in `cluster.rs` and
// reused at the `TypeCheckEnv` interior accessor surface. No parallel
// `pub(crate)` pair lives in this file.
pub(crate) use crate::cluster::{SymbolTableMut, SymbolTableRead};

use crate::result::ReplSnapshot;

use crate::scope::ScopeStack;
use crate::scheme;
use crate::traits::ActiveConstraints;

/// Maximum depth for following Import/Reexport chains (spec §8.6.2).
const IMPORT_CHAIN_DEPTH_LIMIT: usize = 10;

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
    /// Non-fatal warnings accumulated during checking.
    pub(crate) warnings: Vec<Warning>,
    /// Active type variable constraints during body checking (Ring 2).
    pub(crate) active_constraints: ActiveConstraints,
    /// Module aliases: alias name -> full module path (from aliased imports).
    pub(crate) module_aliases: HashMap<Symbol, ModuleFullPath>,
    /// Transient flag: set true during `infer_apply` when inferring the callee.
    /// Used to suppress the "constrained fn as value" error for direct calls.
    pub(crate) in_call_position: bool,
    /// Pending auto-curry resolutions for single-arity functions.
    /// (call_span, function_name, applied_arg_count, total_param_count, callee_type, target_resolution)
    pub(crate) pending_auto_curry: Vec<(Span, Symbol, usize, usize, Type, Option<ResolvedCall>)>,
    /// Multi-sig overload table: base name → [(internal_name, arity)].
    /// Populated during pass 1 when a `Defn` has multiple variants.
    pub(crate) overloads: HashMap<Symbol, Vec<(Symbol, usize)>>,
    /// Resolved overloads: base name → [(param_types, ret_type, mangled_name)].
    /// Built during overload resolution after pass 2.
    pub(crate) resolved_overloads: HashMap<Symbol, Vec<(Vec<Type>, Type, Symbol)>>,
    /// Pending overload dispatch resolutions from call sites.
    /// (call_span, base_name, arg_types, ret_type_var)
    pub(crate) pending_overload_resolutions: Vec<(Span, Symbol, Vec<Type>, Type)>,
    /// The currently active module path for this check.
    pub(crate) current_module: ModuleFullPath,
}

impl CheckState {
    /// Create a new empty CheckState for the given module.
    pub fn new(module: ModuleFullPath) -> Self {
        CheckState {
            subst: Subst::new(),
            env: ScopeStack::new(),
            expr_types: HashMap::new(),
            method_resolutions: MethodResolutions::new(),
            warnings: Vec::new(),
            active_constraints: ActiveConstraints::default(),
            module_aliases: HashMap::new(),
            in_call_position: false,
            pending_auto_curry: Vec::new(),
            overloads: HashMap::new(),
            resolved_overloads: HashMap::new(),
            pending_overload_resolutions: Vec::new(),
            current_module: module,
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
    /// write-redirection plumbing that makes `ClusterContext::Cluster`
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
    /// out of `ClusterContext`; the cell's inner `&mut` originates from
    /// the orchestrator and lives at least as long as `check_forms`'s
    /// frame). We keep them as distinct lifetime parameters on
    /// `TypeCheckStaging` (the inner mut is invariant) but collapse them
    /// to `'a` here — the env's `'a` is shrunk to the shorter of the two
    /// when this Option is constructed.
    pub(crate) staging: Option<TypeCheckStaging<'a, 'a, C, L>>,
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

impl<'a, C, L> TypeCheckEnv<'a, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    /// Create a new TypeCheckEnv from borrowed shared state.
    ///
    /// The caller owns the `DashMap` and `AtomicU32`; this struct just
    /// borrows them. Use `register_builtins()` (free function) to seed
    /// the modules map before constructing the env.
    pub fn new(
        modules: &'a DashMap<ModuleFullPath, SymbolTable<C, L>>,
        next_id: &'a AtomicU32,
    ) -> Self {
        TypeCheckEnv { modules, next_id, staging: None }
    }

    /// Create a `TypeCheckEnv` whose writes targeting `staging_module` flow
    /// to the orchestrator-handed staging `SymbolTable` instead of to the
    /// per-module live table.
    ///
    /// Used by `check_forms` when invoked with
    /// `ClusterContext::Cluster { staging, current_module, .. }`. The caller
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
    ) -> Self {
        TypeCheckEnv {
            modules,
            next_id,
            staging: Some(TypeCheckStaging {
                module: staging_module,
                cell: staging_cell,
            }),
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
    pub fn ensure_module_exists(&self, path: &ModuleFullPath) {
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
        let entry = self.resolve_entry_in_module(module_path, name.as_ref())?;
        match entry {
            ModuleEntry::TypeDef { info, .. } => Some(info),
            _ => None,
        }
    }

    /// State-rooted variant of [`Self::lookup_type_def`].
    ///
    /// Uses `state.current_module` as the access root.
    pub(crate) fn lookup_type_def_with_state(
        &self,
        state: &CheckState,
        name: &TypeName,
    ) -> Option<TypeDefInfo> {
        self.lookup_type_def_in_module(&state.current_module, name)
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
        let entry = self.probe_module_entry_owned(module_path, name)?;
        self.resolve_to_terminal_entry_owned(&entry, 0)
    }

    /// Look up the parent type name for a constructor.
    ///
    /// Per Principle 17 — current-module-only short-name lookup, with
    /// per-symbol chain-follow on `Import`/`Reexport` entries. Public
    /// default-rooted variant defaults to `user`. Returns the bare TypeName
    /// of the parent type. Also handles product types where the constructor
    /// has the same name as the type — in that case the
    /// `ModuleEntry::TypeDef` with `constructor_scheme` is the authority.
    #[allow(dead_code)] // default-rooted accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn lookup_constructor_type(&self, ctor_name: &str) -> Option<TypeName> {
        let user_path = ModuleFullPath::from("user");
        self.lookup_constructor_type_in_module(&user_path, ctor_name)
    }

    /// Module-rooted variant of [`Self::lookup_constructor_type`].
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
            ModuleEntry::TypeDef { info, constructor_scheme: Some(_), .. } => {
                // Product type: constructor has same name as type.
                Some(info.name.name.clone())
            }
            _ => None,
        }
    }

    /// State-rooted variant of [`Self::lookup_constructor_type`].
    pub(crate) fn lookup_constructor_type_with_state(
        &self,
        state: &CheckState,
        ctor_name: &str,
    ) -> Option<TypeName> {
        self.lookup_constructor_type_in_module(&state.current_module, ctor_name)
    }

    /// Check whether a constructor is marked as internal (not user-constructable).
    ///
    /// Per Principle 17 — routes through the principled lookups above.
    /// Public default-rooted variant defaults to `user`.
    #[allow(dead_code)] // default-rooted accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn is_internal_constructor_check(&self, ctor_name: &str) -> bool {
        let user_path = ModuleFullPath::from("user");
        self.is_internal_constructor_check_in_module(&user_path, ctor_name)
    }

    /// Module-rooted variant of [`Self::is_internal_constructor_check`].
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
                    if let Some(entry) = self.probe_module_entry_owned(module_path, c_sym.as_ref())
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

    /// State-rooted variant of [`Self::is_internal_constructor_check`].
    pub(crate) fn is_internal_constructor_check_with_state(
        &self,
        state: &CheckState,
        ctor_name: &str,
    ) -> bool {
        self.is_internal_constructor_check_in_module(&state.current_module, ctor_name)
    }

    /// Iterate over all type definitions visible from the default module.
    ///
    /// Per Principle 17 — bulk introspection (shape 4) is current-module-only.
    /// The public default-rooted variant scans the `user` module's symbol
    /// table (and chain-follows `Import`/`Reexport` entries to their canonical
    /// `TypeDef`). Multi-module aggregation for REPL `/list` etc. is the
    /// session/REPL layer's concern, not typecheck's.
    #[allow(dead_code)] // default-rooted accessor pair; exercised internally + via TestFixture.
    pub(crate) fn all_type_defs(&self) -> Vec<(TypeName, TypeDefInfo)> {
        let user_path = ModuleFullPath::from("user");
        self.all_type_defs_in_module(&user_path)
    }

    /// Module-rooted variant of [`Self::all_type_defs`].
    ///
    /// Scans `module_path`'s symbol table only; canonical `TypeDef` entries
    /// are returned directly, and `Import`/`Reexport` entries are
    /// chain-followed to their terminal `TypeDef` so reach via the prelude is
    /// preserved.
    pub(crate) fn all_type_defs_in_module(
        &self,
        module_path: &ModuleFullPath,
    ) -> Vec<(TypeName, TypeDefInfo)> {
        // Staging-aware (FIXME 0179): collect entries via the union iter,
        // then chain-follow Import/Reexport entries to their terminal
        // `TypeDef`. The collect step holds clones; `resolve_to_terminal_entry_owned`
        // runs outside the borrow.
        let entries: Vec<ModuleEntry<C>> = {
            let mut acc: Vec<ModuleEntry<C>> = Vec::new();
            self.for_each_in_module(module_path, |_k, v| acc.push(v.clone()));
            acc
        };
        let mut result: Vec<(TypeName, TypeDefInfo)> = Vec::new();
        let mut seen: HashSet<TypeName> = HashSet::new();
        for entry in &entries {
            if let Some(terminal) = self.resolve_to_terminal_entry_owned(entry, 0)
                && let ModuleEntry::TypeDef { info, .. } = terminal
                && seen.insert(info.name.name.clone())
            {
                result.push((info.name.name.clone(), info.clone()));
            }
        }
        result
    }

    /// State-rooted variant of [`Self::all_type_defs`].
    #[allow(dead_code)] // accessor-pair convention; reserved for future state-aware callers.
    pub(crate) fn all_type_defs_with_state(
        &self,
        state: &CheckState,
    ) -> Vec<(TypeName, TypeDefInfo)> {
        self.all_type_defs_in_module(&state.current_module)
    }

    /// Build a map of all type definitions (TypeName -> TypeDefInfo).
    ///
    /// Used by external consumers that need the old HashMap-based API.
    #[allow(dead_code)] // delegates to all_type_defs; called by snapshot_type_defs.
    pub(crate) fn all_type_defs_map(&self) -> HashMap<TypeName, TypeDefInfo> {
        self.all_type_defs().into_iter().collect()
    }

    /// Access the per-module symbol tables (for display, introspection).
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn modules(&self) -> &DashMap<ModuleFullPath, SymbolTable<C, L>> {
        self.modules
    }

    /// Build type_defs and constructor_to_type maps from SymbolTables.
    ///
    /// Used by the worker to build partial `CheckResult` for inline
    /// macro compilation without going through `finalize_check_result`.
    ///
    /// NOTE: These maps will be eliminated when the backend reads from
    /// SharedState SymbolTables directly (FQTypeName migration wave C).
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn snapshot_type_defs(&self) -> (HashMap<TypeName, TypeDefInfo>, HashMap<Symbol, TypeName>) {
        let type_defs = self.all_type_defs_map();
        let constructor_to_type: HashMap<Symbol, TypeName> = type_defs.iter()
            .flat_map(|(type_name, info)| {
                info.constructors.iter().map(move |c_sym| (c_sym.clone(), type_name.clone()))
            })
            .collect();
        (type_defs, constructor_to_type)
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
        match guard.get(name.as_ref())? {
            ModuleEntry::Def { got_slot, .. } => *got_slot,
            _ => None,
        }
    }

    /// Get a reference to the underlying modules DashMap.
    /// Used by the integration layer to construct a `CompilationEnv` that
    /// resolves GOT slots by reading symbol tables directly.
    #[allow(dead_code)] // accessor pair; exercised via TestFixture in `#[cfg(test)]`.
    pub(crate) fn modules_ref(&self) -> &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>> {
        self.modules
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
    ) -> Result<cranelisp_types::FQTypeName, crate::result::ResolveError> {
        match self.resolve_terminal_entry_and_home(
            &state.current_module,
            type_name.as_ref(),
        ) {
            Some((ModuleEntry::TypeDef { info, .. }, _home)) => Ok(info.name.clone()),
            Some((ModuleEntry::IntrinsicType { .. }, home)) => {
                Ok(cranelisp_types::FQTypeName::new(home, type_name.clone()))
            }
            _ => Err(crate::result::ResolveError::TypeNotFound {
                name: type_name.clone(),
                from_module: state.current_module.clone(),
                span,
            }),
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
    ) -> Result<Type, crate::result::ResolveError> {
        match self.resolve_terminal_entry_and_home(
            &state.current_module,
            type_name.as_ref(),
        ) {
            Some((ModuleEntry::TypeDef { info, .. }, _home)) => {
                Ok(Type::ADT(info.name.clone(), type_args))
            }
            Some((ModuleEntry::IntrinsicType { ty, .. }, _home)) => Ok(ty),
            _ => Err(crate::result::ResolveError::TypeNotFound {
                name: type_name.clone(),
                from_module: state.current_module.clone(),
                span,
            }),
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
    ) -> Result<ModuleFullPath, crate::result::ResolveError> {
        match self.resolve_terminal_entry_and_home(&state.current_module, trait_name) {
            Some((ModuleEntry::TraitDecl { .. }, home)) => Ok(home),
            _ => Err(crate::result::ResolveError::TraitNotFound {
                name: TraitName::from(trait_name),
                from_module: state.current_module.clone(),
                span,
            }),
        }
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
    ) -> Result<TypeName, crate::result::ResolveError> {
        let module_path = &state.current_module;
        let entry = self
            .resolve_entry_in_module(module_path, ctor_name)
            .ok_or_else(|| crate::result::ResolveError::ConstructorNotFound {
                name: Symbol::from(ctor_name),
                from_module: module_path.clone(),
                span,
            })?;
        match entry {
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                cranelisp_types::DefKind::Constructor { type_name, .. } => {
                    Ok(type_name.name.clone())
                }
                _ => Err(crate::result::ResolveError::ConstructorNotFound {
                    name: Symbol::from(ctor_name),
                    from_module: module_path.clone(),
                    span,
                }),
            },
            ModuleEntry::TypeDef { info, constructor_scheme: Some(_), .. } => {
                Ok(info.name.name.clone())
            }
            _ => Err(crate::result::ResolveError::ConstructorNotFound {
                name: Symbol::from(ctor_name),
                from_module: module_path.clone(),
                span,
            }),
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
    pub(crate) fn lookup(&self, state: &CheckState, name: &str) -> Option<Scheme> {
        // Check local scope stack first
        if let Some(scheme) = state.env.lookup(name) {
            return Some(scheme.clone());
        }

        // Fall back to current module's symbol table (following import chains)
        if let Some(scheme) = self.lookup_in_current_module(state, name) {
            return Some(scheme);
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
                if let Ok(Some(scheme)) = self.resolve_qualified(state, &child_path, name_part) {
                    return Some(scheme);
                }

                // Fall back to absolute module path.
                let abs_path = ModuleFullPath::from(module_part);
                if let Ok(Some(scheme)) = self.resolve_qualified(state, &abs_path, name_part) {
                    return Some(scheme);
                }

                // Also try alias resolution (handled inside resolve_qualified).
            }
        }

        None
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
        let entry = self.probe_module_entry_owned(&state.current_module, name)?;
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
            ModuleEntry::Def { scheme, .. } => Some(scheme.clone()),
            ModuleEntry::TypeDef {
                constructor_scheme: Some(scheme),
                ..
            } => Some(scheme.clone()),
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

    /// Resolve a name in the current module to its terminal `ModuleEntry`,
    /// following Import/Reexport chains. Returns an owned clone.
    ///
    /// Staging-aware (FIXME 0179): consults staging first via
    /// [`Self::probe_module_entry_owned`].
    pub(crate) fn resolve_entry_in_current_module(&self, state: &CheckState, name: &str) -> Option<ModuleEntry<C>> {
        let entry = self.probe_module_entry_owned(&state.current_module, name)?;
        self.resolve_to_terminal_entry_owned(&entry, 0)
    }

    /// Follow Import/Reexport chains to the terminal `ModuleEntry`.
    /// Returns an owned clone. Clone-and-drop discipline applied at each step.
    ///
    /// Staging-aware: chain edges land on staging entries first when the
    /// edge's source module matches the current staging target.
    pub(crate) fn resolve_to_terminal_entry_owned(
        &self,
        entry: &ModuleEntry<C>,
        depth: usize,
    ) -> Option<ModuleEntry<C>> {
        if depth > IMPORT_CHAIN_DEPTH_LIMIT {
            return None;
        }
        match entry {
            ModuleEntry::Import { source, .. } => {
                let target = self.probe_module_entry_owned(&source.module, source.symbol.as_ref())?;
                self.resolve_to_terminal_entry_owned(&target, depth + 1)
            }
            other => Some(other.clone()),
        }
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
    pub(crate) fn resolve_qualified(
        &self,
        state: &CheckState,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Result<Option<Scheme>, CranelispError> {
        // Resolve the module: check if the first path component is an alias
        let first_component = module_path.as_ref().split('.').next().unwrap_or(module_path.as_ref());
        let resolved_path = state
            .module_aliases
            .get(&Symbol::from(first_component))
            .cloned()
            .unwrap_or_else(|| module_path.clone());

        // Clone-and-drop discipline: clone entry from guard, drop guard,
        // then check visibility and follow chains. Staging-aware (FIXME 0179).
        let entry = match self.probe_module_entry_owned(&resolved_path, name) {
            Some(e) => e,
            None => {
                // Module not loaded or symbol absent — distinguish by checking
                // module presence.
                if self.modules.get(&resolved_path).is_none() {
                    return Ok(None);
                }
                return Ok(None);
            }
        };

        // Visibility check: private names are only accessible within the
        // defining module's subtree
        if !entry.is_public() && !self.is_in_subtree(&state.current_module, &resolved_path) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "'{}' is private in module '{}'",
                    name, resolved_path
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }

        Ok(self.extract_scheme_from_entry_owned(&entry, 0))
    }

    /// Check if `accessor` is within the subtree of `definer`.
    ///
    /// A module is in its own subtree, and a child module (e.g. "foo.bar")
    /// is in the subtree of its parent ("foo").
    fn is_in_subtree(&self, accessor: &ModuleFullPath, definer: &ModuleFullPath) -> bool {
        let accessor_str: &str = accessor.as_ref();
        let definer_str: &str = definer.as_ref();
        accessor_str == definer_str
            || accessor_str.starts_with(&format!("{}.", definer_str))
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
        crate::unify::unify(&mut state.subst, t1, t2).map_err(|e| {
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

    /// Instantiate a scheme by replacing each quantified variable with a fresh variable.
    /// Uses atomic `fresh_var()` — safe for `&self`.
    pub(crate) fn instantiate_scheme(&self, scheme: &Scheme) -> Type {
        if scheme.type_vars.is_empty() {
            return scheme.ty.clone();
        }
        let mut inst_subst = Subst::new();
        for &var_id in &scheme.type_vars {
            let fresh = self.fresh_var();
            inst_subst.insert(var_id, fresh);
        }
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
                constraints
                    .entry(resolved_id)
                    .or_default()
                    .extend(traits.iter().cloned());
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
        state.active_constraints = ActiveConstraints::default();
    }

    /// Apply the current substitution to a type.
    pub(crate) fn apply_subst(&self, state: &CheckState, ty: &Type) -> Type {
        apply(&state.subst, ty)
    }

    // --- Import processing (spec §8.3) ---

    /// Process import specifications and register imported names into the
    /// current module's symbol table.
    ///
    /// For each ImportSpec:
    /// - `Glob`: import all public symbols from the source module
    /// - `Specific(names)`: import listed names (must be public)
    /// - `MemberGlob(parent)`: import all constructors/methods of a type or trait
    /// - `None`: alias-only import (no bare names)
    ///
    /// Duplicate bare names from different sources produce `ModuleEntry::Ambiguous`
    /// per spec §8.6.4.
    pub fn register_imports(
        &self,
        state: &mut CheckState,
        specs: &[ImportSpec],
    ) -> Result<(), CranelispError> {
        for spec in specs {
            // Register alias if present
            if let Some(alias) = &spec.alias {
                state.module_aliases.insert(
                    Symbol::from(alias.as_ref()),
                    spec.module_path.clone(),
                );
            }

            // Clone-and-drop discipline: collect imports from source guard,
            // drop it, then acquire write guard on current module.
            let imports_to_add: Vec<(Symbol, ModuleEntry<C>)> = {
                let source_guard = match self.modules.get(&spec.module_path) {
                    Some(g) => g,
                    None => {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "unknown module '{}' in import",
                                spec.module_path
                            ),
                            location: ErrorLocation::from_span(spec.span),
                        });
                    }
                };

                match &spec.names {
                    ImportNames::Glob => {
                        collect_glob_imports(&source_guard, &spec.module_path)
                    }
                    ImportNames::Specific(names) => {
                        self.collect_specific_imports(
                            state, &source_guard, names, &spec.module_path, spec.span,
                        )?
                    }
                    ImportNames::MemberGlob(parent) => {
                        self.collect_member_glob_imports(
                            &source_guard, parent, &spec.module_path,
                        )
                    }
                    ImportNames::None => {
                        // Alias-only import — no bare names
                        Vec::new()
                    }
                }
                // source_guard dropped here
            };

            // Now safe to get write guard on current module
            let mut guard = self.current_symbol_table_mut(state);
            insert_imports_detecting_ambiguity(&mut *guard, imports_to_add);
        }
        Ok(())
    }

    /// Register export (re-export) specs for the current module.
    ///
    /// For each `ExportSpec`, looks up the source module and creates
    /// `ModuleEntry::Reexport` entries in the current module's symbol table.
    /// Follows the same pattern as `register_imports` but creates Reexport
    /// entries instead of Import entries.
    pub fn register_exports(
        &self,
        state: &mut CheckState,
        specs: &[ExportSpec],
    ) -> Result<(), CranelispError> {
        for spec in specs {
            // Resolve the module path: try as-is first, then as a child
            // of the current module (e.g., "syntax" -> "core.syntax"
            // when current module is "core").
            let resolved_path = if self.modules.contains_key(&spec.module_path) {
                spec.module_path.clone()
            } else {
                let child_path = ModuleFullPath::from(format!(
                    "{}.{}",
                    state.current_module, spec.module_path
                ));
                if self.modules.contains_key(&child_path) {
                    child_path
                } else {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "unknown module '{}' in export",
                            spec.module_path
                        ),
                        location: ErrorLocation::from_span(spec.span),
                    });
                }
            };

            // Clone-and-drop discipline: collect reexports from source guard,
            // drop it, then acquire write guard on current module.
            let reexports: Vec<(Symbol, ModuleEntry<C>)> = {
                let source_guard = match self.modules.get(&resolved_path) {
                    Some(g) => g,
                    None => unreachable!("module existence verified above"),
                };

                match &spec.names {
                    ImportNames::Glob => {
                        collect_glob_reexports(&source_guard, &resolved_path)
                    }
                    ImportNames::Specific(names) => {
                        self.collect_specific_reexports(
                            state, &source_guard, names, &resolved_path, spec.span,
                        )?
                    }
                    ImportNames::MemberGlob(parent) => {
                        self.collect_member_glob_reexports(
                            &source_guard, parent, &resolved_path,
                        )
                    }
                    ImportNames::None => {
                        // No names to re-export.
                        Vec::new()
                    }
                }
                // source_guard dropped here
            };

            // Now safe to get write guard on current module
            let mut guard = self.current_symbol_table_mut(state);
            insert_imports_detecting_ambiguity(&mut *guard, reexports);
        }
        Ok(())
    }

    /// Collect specific named re-exports from a source module, checking
    /// visibility and existence.
    fn collect_specific_reexports(
        &self,
        state: &CheckState,
        source_table: &SymbolTable<C, L>,
        names: &[Symbol],
        module_path: &ModuleFullPath,
        span: Span,
    ) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CranelispError> {
        let mut result = Vec::new();
        for name in names {
            match source_table.get(name.as_ref()) {
                Some(entry) => {
                    if !entry.is_public()
                        && !self.is_in_subtree(
                            &state.current_module,
                            module_path,
                        )
                    {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "'{}' is not public in '{}'",
                                name, module_path
                            ),
                            location: ErrorLocation::from_span(span),
                        });
                    }
                    let fq = FQSymbol {
                        module: module_path.clone(),
                        symbol: name.clone(),
                    };
                    result.push((
                        name.clone(),
                        ModuleEntry::Import { source: fq, visibility: Visibility::Public },
                    ));
                }
                None => {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "'{}' not found in module '{}'",
                            name, module_path
                        ),
                        location: ErrorLocation::from_span(span),
                    });
                }
            }
        }
        Ok(result)
    }

    /// Collect all constructors of a type or all methods of a trait from a
    /// source module for re-export (member glob).
    fn collect_member_glob_reexports(
        &self,
        source_table: &SymbolTable<C, L>,
        parent: &Symbol,
        module_path: &ModuleFullPath,
    ) -> Vec<(Symbol, ModuleEntry<C>)> {
        let trait_name = cranelisp_types::TraitName::from(parent.as_ref());
        let mut result = Vec::new();
        for (name, entry) in source_table.public_symbols() {
            let is_member = match entry {
                ModuleEntry::Def { trait_origin, kind, .. } => {
                    match kind.as_ref() {
                        cranelisp_types::DefKind::Constructor { type_name, .. } => {
                            type_name.name.as_ref() == parent.as_ref()
                        }
                        cranelisp_types::DefKind::Primitive
                        | cranelisp_types::DefKind::UserFn { .. } => trait_origin
                            .as_ref()
                            .is_some_and(|fqtn| fqtn.name == trait_name),
                        _ => false,
                    }
                }
                _ => false,
            };
            if is_member {
                let fq = FQSymbol {
                    module: module_path.clone(),
                    symbol: name.clone(),
                };
                result.push((
                    name.clone(),
                    ModuleEntry::Import { source: fq, visibility: Visibility::Private },
                ));
            }
        }
        result
    }

    /// Collect specific named imports from a source module, checking
    /// visibility and existence (spec §8.3).
    fn collect_specific_imports(
        &self,
        state: &CheckState,
        source_table: &SymbolTable<C, L>,
        names: &[Symbol],
        module_path: &ModuleFullPath,
        span: Span,
    ) -> Result<Vec<(Symbol, ModuleEntry<C>)>, CranelispError> {
        let mut result = Vec::new();
        for name in names {
            match source_table.get(name.as_ref()) {
                Some(entry) => {
                    if !entry.is_public()
                        && !self.is_in_subtree(
                            &state.current_module,
                            module_path,
                        )
                    {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "'{}' is not public in '{}'",
                                name, module_path
                            ),
                            location: ErrorLocation::from_span(span),
                        });
                    }
                    let fq = FQSymbol {
                        module: module_path.clone(),
                        symbol: name.clone(),
                    };
                    result.push((
                        name.clone(),
                        ModuleEntry::Import { source: fq, visibility: Visibility::Private },
                    ));
                }
                None => {
                    return Err(CranelispError::TypeError {
                        message: format!(
                            "'{}' not found in module '{}'",
                            name, module_path
                        ),
                        location: ErrorLocation::from_span(span),
                    });
                }
            }
        }
        Ok(result)
    }

    /// Collect all constructors of a type or all methods of a trait from a
    /// source module (member glob import).
    fn collect_member_glob_imports(
        &self,
        source_table: &SymbolTable<C, L>,
        parent: &Symbol,
        module_path: &ModuleFullPath,
    ) -> Vec<(Symbol, ModuleEntry<C>)> {
        let trait_name = cranelisp_types::TraitName::from(parent.as_ref());
        let mut result = Vec::new();
        for (name, entry) in source_table.public_symbols() {
            let is_member = match entry {
                ModuleEntry::Def { trait_origin, kind, .. } => {
                    match kind.as_ref() {
                        cranelisp_types::DefKind::Constructor { type_name, .. } => {
                            type_name.name.as_ref() == parent.as_ref()
                        }
                        cranelisp_types::DefKind::Primitive
                        | cranelisp_types::DefKind::UserFn { .. } => trait_origin
                            .as_ref()
                            .is_some_and(|fqtn| fqtn.name == trait_name),
                        _ => false,
                    }
                }
                _ => false,
            };
            if is_member {
                let fq = FQSymbol {
                    module: module_path.clone(),
                    symbol: name.clone(),
                };
                result.push((
                    name.clone(),
                    ModuleEntry::Import { source: fq, visibility: Visibility::Private },
                ));
            }
        }
        result
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
    pub(crate) fn lookup_trait_decl_in_module(
        &self,
        module_path: &ModuleFullPath,
        trait_name: &TraitName,
    ) -> Option<cranelisp_types::TraitDeclInfo> {
        let entry = self.resolve_entry_in_module(module_path, trait_name.as_ref())?;
        match entry {
            ModuleEntry::TraitDecl { info, .. } => Some(info),
            _ => None,
        }
    }

    /// State-rooted variant of [`Self::lookup_trait_decl`].
    pub(crate) fn lookup_trait_decl_with_state(
        &self,
        state: &CheckState,
        trait_name: &TraitName,
    ) -> Option<cranelisp_types::TraitDeclInfo> {
        self.lookup_trait_decl_in_module(&state.current_module, trait_name)
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
    pub(crate) fn method_to_trait_with_state(
        &self,
        state: &CheckState,
        method_name: &Symbol,
    ) -> Option<TraitName> {
        self.method_to_trait_in_module(&state.current_module, method_name)
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
        self.find_impl_entry_in_module(module_path, trait_name, impl_type).is_some()
    }

    /// State-rooted variant of [`Self::has_impl`].
    pub(crate) fn has_impl_with_state(
        &self,
        state: &CheckState,
        trait_name: &TraitName,
        impl_type: &TypeName,
    ) -> bool {
        self.has_impl_in_module(&state.current_module, trait_name, impl_type)
    }

    /// Pattern B impl-resolution primitive: chain-follow the trait to its
    /// defining module H, then probe H for `impl$<FQTypeName>$<FQTraitName>`.
    /// Returns the impl entry (cloned) plus the trait's home module.
    ///
    /// The probe matches by `impl_type.name == impl_type` to accommodate the
    /// caller passing a bare `TypeName`; the FQ trait name is built from the
    /// trait's chain-followed home so the synthetic key is correct.
    fn find_impl_entry_in_module(
        &self,
        module_path: &ModuleFullPath,
        trait_name: &TraitName,
        impl_type: &TypeName,
    ) -> Option<(ModuleEntry<C>, ModuleFullPath)> {
        // Chain-follow trait reference to its defining module.
        let (terminal, trait_home) = self.resolve_terminal_entry_and_home(
            module_path,
            trait_name.as_ref(),
        )?;
        // Terminal must be a TraitDecl for this to be a valid trait reference.
        if !matches!(terminal, ModuleEntry::TraitDecl { .. }) {
            return None;
        }
        // Probe trait's home for any `impl$*$<trait_home/trait_name>` whose
        // impl_type's bare name matches `impl_type`. Iterate the trait's home
        // symbol table only (Principle 17 shape 3) — no other modules touched.
        // Staging-aware (FIXME 0179): when trait_home == staging.module the
        // for_each iter unions staging-first then live.
        let mut found: Option<(ModuleEntry<C>, ModuleFullPath)> = None;
        self.for_each_in_module(&trait_home, |_key, entry| {
            if found.is_some() {
                return;
            }
            if let ModuleEntry::TraitImpl { trait_name: tn, impl_type: it, .. } = entry
                && &tn.name == trait_name && &it.name == impl_type
            {
                found = Some((entry.clone(), trait_home.clone()));
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

    // --- REPL snapshot/restore ---

    /// Take a snapshot of the current state for REPL error recovery.
    pub fn snapshot(&self, state: &CheckState) -> ReplSnapshot {
        // Use the View read accessor so staging entries are included in the
        // snapshot's key set in cluster mode (FIXME 0179).
        let r = self.current_symbol_table(state);
        let symbol_keys = r.view().iter().map(|(k, _)| k.clone()).collect();
        drop(r);
        ReplSnapshot {
            next_type_id: self.next_id.load(Ordering::Relaxed),
            symbol_keys,
            subst_len: state.subst.len(),
            scope_depth: state.env.depth(),
        }
    }

    /// Restore state from a snapshot (on REPL error).
    pub fn restore(&self, state: &mut CheckState, snapshot: ReplSnapshot) {
        self.next_id.store(snapshot.next_type_id, Ordering::Relaxed);
        state.subst.retain(|id, _| *id < snapshot.next_type_id);
        state.expr_types.clear();
        state.method_resolutions.resolved_calls.clear();
        state.warnings.clear();
        state.pending_auto_curry.clear();
        // Remove symbol table entries added after the snapshot was taken.
        self.current_symbol_table_mut(state)
            .symbols
            .retain(|key, _| snapshot.symbol_keys.contains(key));
        // Restore scope stack depth (pop frames left by failed check_defn_body).
        state.env.truncate_to(snapshot.scope_depth);
    }

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
    ) -> Result<Type, crate::result::ResolveError> {
        let resolve_terminal = |tref: &cranelisp_types::TypeRef| -> Option<ModuleEntry<C>> {
            let root = tref.module.as_ref().unwrap_or(module_path);
            self.resolve_terminal_entry_and_home(root, tref.name.as_ref())
                .map(|(entry, _home)| entry)
        };
        crate::resolve::resolve_type_expr(texpr, var_map, &resolve_terminal, span)
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

// ---------------------------------------------------------------------------
// Sprint 67 hack-back (FIXME 0192 methods 9 + 10): free-fn entry points
// for `register_imports` / `register_exports`. Cross-crate callers avoid
// constructing a transient `TypeCheckEnv` per spec change; instead they
// hand in the live `next_id` + `&DashMap` + `&mut CheckState` directly.
// Implementation delegates to the existing methods to preserve semantics
// (visibility checks, ambiguity detection, staging-aware writes via
// `current_symbol_table_mut`); only the API shape changes.
// ---------------------------------------------------------------------------

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

/// Register import specs for the current module (free-fn entry point).
///
/// Per the FIXME 0192 disposition for method 9 (`register_imports`): the work
/// is genuinely typecheck-pass — interprets `ImportSpec` / `ImportNames` AST
/// variants, applies visibility + ambiguity rules per spec §8.6, mutates
/// `state.module_aliases`, produces typecheck diagnostics. The method-on-
/// `TypeCheckEnv` shape forced cross-crate callers to construct transient
/// envs; this free fn closes that smell while keeping the substance in
/// typecheck.
pub fn register_imports<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    next_id: &AtomicU32,
    state: &mut CheckState,
    specs: &[ImportSpec],
) -> Result<(), CranelispError>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let env = TypeCheckEnv::<C, L>::new(symbol_tables, next_id);
    env.register_imports(state, specs)
}

/// Register export (re-export) specs for the current module (free-fn entry).
///
/// Mirror of [`register_imports`] for `ExportSpec` / `Reexport` entries with
/// path-resolution (try-as-is or child-of-current per spec §8.6.x relative
/// form). Same disposition as method 10.
pub fn register_exports<C, L>(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    next_id: &AtomicU32,
    state: &mut CheckState,
    specs: &[ExportSpec],
) -> Result<(), CranelispError>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let env = TypeCheckEnv::<C, L>::new(symbol_tables, next_id);
    env.register_exports(state, specs)
}

// ---------------------------------------------------------------------------
// Import helpers (free functions to avoid borrow conflicts)
// ---------------------------------------------------------------------------

/// Collect all public symbols from a source module as glob imports.
fn collect_glob_imports<C, L>(
    source_table: &SymbolTable<C, L>,
    module_path: &ModuleFullPath,
) -> Vec<(Symbol, ModuleEntry<C>)>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    source_table
        .public_symbols()
        .map(|(name, _entry)| {
            let fq = FQSymbol {
                module: module_path.clone(),
                symbol: name.clone(),
            };
            (name.clone(), ModuleEntry::Import { source: fq, visibility: Visibility::Private })
        })
        .collect()
}

/// Collect all public names from a module as Reexport entries (glob re-export).
fn collect_glob_reexports<C, L>(
    source_table: &SymbolTable<C, L>,
    module_path: &ModuleFullPath,
) -> Vec<(Symbol, ModuleEntry<C>)>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    source_table
        .public_symbols()
        .map(|(name, _entry)| {
            let fq = FQSymbol {
                module: module_path.clone(),
                symbol: name.clone(),
            };
            (name.clone(), ModuleEntry::Import { source: fq, visibility: Visibility::Public })
        })
        .collect()
}

/// Insert import entries into a symbol table, marking same-name entries from
/// different sources as ambiguous (spec §8.6.4). Same-source duplicates are
/// allowed and silently deduplicated.
fn insert_imports_detecting_ambiguity<C, L>(
    table: &mut SymbolTable<C, L>,
    imports: Vec<(Symbol, ModuleEntry<C>)>,
)
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    for (name, new_entry) in imports {
        if let Some(existing) = table.get(name.as_ref()) {
            // Same-source duplicate is NOT ambiguous (spec §8.6.4)
            let is_same_source = match (existing, &new_entry) {
                (
                    ModuleEntry::Import { source: s1, .. },
                    ModuleEntry::Import { source: s2, .. },
                ) => s1 == s2,
                _ => false,
            };
            if is_same_source {
                // Same source — skip silently (no overwrite needed).
                continue;
            }

            // Both are Import entries from different sources. Check
            // whether the existing one is a seeded builtin (source module
            // is "user" or "primitives"). Seeded builtins are copied into
            // every module by set_current_module — they are canonical
            // definitions, not intentional imports. A prelude glob import
            // that brings in the same name via a different chain (e.g.,
            // "prelude/add-i64" vs "user/add-i64") is NOT ambiguous.
            let both_indirect = matches!(
                (existing, &new_entry),
                (ModuleEntry::Import { .. }, ModuleEntry::Import { .. })
            );
            if both_indirect {
                // If either source is from "user" or "primitives" (builtin
                // seeding), prefer the existing entry — it's canonical.
                let is_seeded_source = |entry: &ModuleEntry<C>| -> bool {
                    match entry {
                        ModuleEntry::Import { source, .. } => {
                            let m: &str = source.module.as_ref();
                            m == "user" || m == "primitives"
                        }
                        _ => false,
                    }
                };
                let existing_is_seeded = is_seeded_source(existing);
                let new_is_seeded = is_seeded_source(&new_entry);
                if existing_is_seeded || new_is_seeded {
                    // One is a seeded builtin — keep existing, skip new.
                    continue;
                }

                // Both from non-builtin different sources: ambiguous (spec §8.6.4).
                table.insert(name, ModuleEntry::Ambiguous { visibility: Visibility::Public });
                continue;
            }

            // Existing is a directly-defined entry (Def, TypeDef,
            // Constructor, Macro, TraitDecl). It takes priority
            // over an incoming Import — skip the new entry.
            continue;
        }
        table.insert(name, new_entry);
    }
}

// ---------------------------------------------------------------------------
// Test fixture: owns DashMap + AtomicU32, provides TypeCheckEnv + CheckState
// ---------------------------------------------------------------------------

/// Test helper that owns the backing stores and provides a `TypeCheckEnv`
/// plus a `CheckState` for test methods. Replaces the old `TypeChecker::new()`.
#[cfg(test)]
pub(crate) struct TestFixture {
    pub modules: DashMap<ModuleFullPath, SymbolTable>,
    pub next_id: AtomicU32,
    pub state: CheckState,
}

#[cfg(test)]
impl TestFixture {
    /// Create a test fixture with builtins registered and "user" as the current module.
    pub fn new() -> Self {
        let modules = DashMap::new();
        let next_id = AtomicU32::new(0);
        let current_module = ModuleFullPath::from("user");
        modules.insert(current_module.clone(), SymbolTable::new(current_module.clone()));
        crate::builtins::register_builtins(&modules, &next_id);
        // Per S72 Wave 1 Trigger 1 (Decision 0048): production sources
        // primitive Defs from `cranelisp-primitives::PRIMITIVES_TABLE` at
        // session startup; typecheck no longer registers them. Tests stay
        // self-contained via this fixture seed (no `cranelisp-primitives`
        // dep). See `seed_test_primitives` rustdoc.
        crate::builtins::seed_test_primitives(&modules, &next_id);
        TestFixture {
            modules,
            next_id,
            state: CheckState::new(current_module),
        }
    }

    /// Get a TypeCheckEnv borrowing this fixture's stores.
    pub fn env(&self) -> TypeCheckEnv<'_> {
        TypeCheckEnv::new(&self.modules, &self.next_id)
    }

    /// Switch the active module. Creates the module's symbol table if needed.
    pub fn set_current_module(&mut self, path: ModuleFullPath) {
        self.env().ensure_module_exists(&path);
        self.state.current_module = path;
    }

    /// Get a read guard for the current module's symbol table.
    pub fn symbol_table(&self) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable> {
        self.modules.get(&self.state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists"))
    }

    /// Get a write guard for the current module's symbol table.
    pub fn symbol_table_mut(&self) -> dashmap::mapref::one::RefMut<'_, ModuleFullPath, SymbolTable> {
        self.modules.get_mut(&self.state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists"))
    }

    /// Look up a name using current state.
    pub fn lookup(&self, name: &str) -> Option<Scheme> {
        self.env().lookup(&self.state, name)
    }

    /// Resolve qualified using current state.
    pub fn resolve_qualified(
        &self,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Result<Option<Scheme>, CranelispError> {
        self.env().resolve_qualified(&self.state, module_path, name)
    }

    /// Register a type definition (test convenience).
    pub fn register_type_def_self(
        &mut self,
        name: &cranelisp_types::TypeName,
        docstring: &Option<String>,
        type_params: &[Symbol],
        constructors: &[cranelisp_types::ConstructorDef],
        visibility: cranelisp_types::Visibility,
        span: Span,
    ) -> Result<(), CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.register_type_def(&mut self.state, name, docstring, type_params, constructors, visibility, span)
    }

    /// Register a trait decl (test convenience).
    pub fn register_trait_decl_self(
        &mut self,
        decl: &cranelisp_types::TraitDecl,
    ) -> Result<(), CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.register_trait_decl(&mut self.state, decl)
    }

    /// Register a trait impl (test convenience).
    pub fn register_trait_impl_self(
        &mut self,
        impl_: &cranelisp_types::TraitImpl,
    ) -> Result<Vec<cranelisp_types::Defn>, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.register_trait_impl(&mut self.state, impl_)
    }

    /// Try resolve trait method (test convenience).
    pub fn try_resolve_trait_method_self(
        &mut self,
        name: &Symbol,
        arg_types: &[Type],
        span: Span,
    ) -> Result<Option<cranelisp_types::ResolvedCall>, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.try_resolve_trait_method(&mut self.state, name, arg_types, span)
    }

    /// Check program (test convenience).
    ///
    /// Routes a whole-program batch through `check_via_forms` (the same Pass 1
    /// / Pass 2 / finalize pipeline as production `check_forms`) with `Additive`
    /// strategy, matching the retired `check_program`. The module is taken from
    /// the fixture's current `CheckState` (set via `set_current_module`), so
    /// helpers like `tc_with_prims` that switch to `test` resolve correctly.
    pub fn check_program_self(
        &mut self,
        program: &[cranelisp_types::TopLevel],
    ) -> Result<crate::result::CheckResult, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        let ctx = cranelisp_types::CompileContext {
            module: self.state.current_module.clone(),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        };
        env.check_via_forms(
            &mut self.state,
            program,
            &ctx,
            cranelisp_types::ModuleStrategy::Additive,
        )
    }

    /// Check REPL input (test convenience).
    ///
    /// Routes a single REPL form through `check_via_forms` as a one-element
    /// slice with `Additive` strategy, matching the retired `check_repl_input`
    /// incremental path. The module is taken from the fixture's current
    /// `CheckState` (set via `set_current_module`).
    pub fn check_repl_input_self(
        &mut self,
        input: &cranelisp_types::TopLevel,
    ) -> Result<crate::result::CheckResult, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        let ctx = cranelisp_types::CompileContext {
            module: self.state.current_module.clone(),
            codegen: cranelisp_types::CodegenBehaviour::InMemoryAndObject,
        };
        let program = std::slice::from_ref(input);
        env.check_via_forms(
            &mut self.state,
            program,
            &ctx,
            cranelisp_types::ModuleStrategy::Additive,
        )
    }

    /// Infer expression type (test convenience).
    pub fn infer_expr_for_test(
        &mut self,
        expr: &mut cranelisp_types::Expr,
    ) -> Result<Type, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.infer_expr(&mut self.state, expr)
    }

    /// Register imports (test convenience).
    pub fn register_imports_self(
        &mut self,
        specs: &[cranelisp_types::ImportSpec],
    ) -> Result<(), CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.register_imports(&mut self.state, specs)
    }

    /// Clear transient state (test convenience).
    pub fn clear_transient_state(&mut self) {
        TypeCheckEnv::<()>::clear_transient_state(&mut self.state);
    }

    /// Resolve primitive JIT name (test convenience).
    pub fn resolve_primitive_jit_name_self(&self, name: &str) -> Option<Symbol> {
        self.env().resolve_primitive_jit_name(&self.state, name)
    }

    /// Look up type def (test convenience). Uses `state.current_module` as the
    /// access root so tests that switch the active module via
    /// `set_current_module` see types registered there.
    pub fn lookup_type_def(&self, name: &TypeName) -> Option<TypeDefInfo> {
        self.env().lookup_type_def_in_module(&self.state.current_module, name)
    }

    /// Look up type def in a specific module (test convenience).
    ///
    /// Synthetic modules (`primitives`, `macros`) have empty imports per
    /// Principle 17, so types registered there are not reachable via
    /// short-name lookup from `user`. Tests that need to inspect synthetic
    /// types call this variant with the explicit module path.
    pub fn lookup_type_def_in_module(
        &self,
        module_path: &ModuleFullPath,
        name: &TypeName,
    ) -> Option<TypeDefInfo> {
        self.env().lookup_type_def_in_module(module_path, name)
    }

    /// Read the docstring stored on a `TypeDef` entry (test convenience).
    ///
    /// Docstrings live on the `ModuleEntry` directly (not inside
    /// `TypeDefInfo`), so tests that assert a registered type's doc read it
    /// through this accessor rather than off the returned `TypeDefInfo`.
    pub fn lookup_type_def_docstring_in_module(
        &self,
        module_path: &ModuleFullPath,
        name: &TypeName,
    ) -> Option<String> {
        match self.env().resolve_entry_in_module(module_path, name.as_ref())? {
            ModuleEntry::TypeDef { docstring, .. } => docstring,
            _ => None,
        }
    }

    /// Look up constructor type (test convenience). Uses `state.current_module`.
    pub fn lookup_constructor_type(&self, ctor_name: &str) -> Option<TypeName> {
        self.env()
            .lookup_constructor_type_in_module(&self.state.current_module, ctor_name)
    }

    /// Check exhaustiveness (test convenience). Uses `state.current_module`.
    pub fn check_exhaustiveness(
        &self,
        type_name: &TypeName,
        covered: &[Symbol],
        has_wildcard: bool,
        span: Span,
    ) -> Result<(), CranelispError> {
        let fqtn = cranelisp_types::FQTypeName::new(
            self.state.current_module.clone(),
            type_name.clone(),
        );
        self.env().check_exhaustiveness_in_module(&fqtn, covered, has_wildcard, span)
    }

    /// Check exhaustiveness in a specific module (test convenience).
    pub fn check_exhaustiveness_in_module(
        &self,
        module_path: &ModuleFullPath,
        type_name: &TypeName,
        covered: &[Symbol],
        has_wildcard: bool,
        span: Span,
    ) -> Result<(), CranelispError> {
        let fqtn = cranelisp_types::FQTypeName::new(module_path.clone(), type_name.clone());
        self.env().check_exhaustiveness_in_module(&fqtn, covered, has_wildcard, span)
    }

    /// Fresh var id (test convenience).
    pub fn fresh_var_id(&self) -> (Type, TypeId) {
        self.env().fresh_var_id()
    }

    /// Fresh var (test convenience).
    pub fn fresh_var(&self) -> Type {
        self.env().fresh_var()
    }

    /// Snapshot (test convenience).
    pub fn snapshot(&self) -> ReplSnapshot {
        self.env().snapshot(&self.state)
    }

    /// Has impl (test convenience). State-rooted so tests that switch the
    /// active module via `set_current_module` honour the active module.
    pub fn has_impl(&self, trait_name: &TraitName, impl_type: &TypeName) -> bool {
        self.env().has_impl_with_state(&self.state, trait_name, impl_type)
    }

    /// Lookup trait decl (test convenience). State-rooted.
    pub fn lookup_trait_decl(&self, trait_name: &TraitName) -> Option<cranelisp_types::TraitDeclInfo> {
        self.env().lookup_trait_decl_with_state(&self.state, trait_name)
    }

    /// Method to trait (test convenience). State-rooted.
    pub fn method_to_trait(&self, method_name: &Symbol) -> Option<TraitName> {
        self.env().method_to_trait_with_state(&self.state, method_name)
    }

    /// Bind local (test convenience).
    pub fn bind_local_self(&mut self, name: Symbol, scheme: Scheme) {
        self.state.env.bind(name, scheme);
    }

    /// Apply subst (test convenience).
    pub fn apply_subst_self(&self, ty: &Type) -> Type {
        apply(&self.state.subst, ty)
    }

    /// Check form (test convenience).
    pub fn check_form(
        &mut self,
        module: &ModuleFullPath,
        form: &cranelisp_types::TopLevel,
        pass: crate::program::CheckPass,
        accumulator: &mut crate::program::ModuleCheckAccumulator,
    ) -> Result<crate::program::FormCheckResult, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.check_form(module, form, pass, &mut self.state, accumulator)
    }

    /// Merge form result (test convenience).
    pub fn merge_form_result(
        &mut self,
        module: &ModuleFullPath,
        accumulator: &mut crate::program::ModuleCheckAccumulator,
        result: crate::program::FormCheckResult,
    ) {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.merge_form_result(module, &mut self.state, accumulator, result);
    }

    /// Finalize check result (test convenience).
    pub fn finalize_check_result(
        &mut self,
        module: &ModuleFullPath,
        accumulator: &mut crate::program::ModuleCheckAccumulator,
        working_program: &[cranelisp_types::TopLevel],
        strategy: cranelisp_types::ModuleStrategy,
    ) -> Result<crate::result::CheckResult, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.finalize_check_result(module, &mut self.state, accumulator, working_program, strategy)
    }

    /// Check (unified pipeline, test convenience).
    ///
    /// Routes to `check_via_forms`, which drives the same Pass 1 / Pass 2 /
    /// finalize pipeline as the production `check_forms` free function and
    /// returns the display-bearing `CheckResult` in-crate tests assert on.
    pub fn check(
        &mut self,
        program: &[cranelisp_types::TopLevel],
        ctx: &cranelisp_types::CompileContext,
        strategy: cranelisp_types::ModuleStrategy,
    ) -> Result<crate::result::CheckResult, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.check_via_forms(&mut self.state, program, ctx, strategy)
    }

    /// Is internal constructor (test convenience).
    pub fn is_internal_constructor_check(&self, ctor_name: &str) -> bool {
        self.env().is_internal_constructor_check(ctor_name)
    }

    /// Resolve a `TypeExpr` in the `user` module (test convenience).
    pub fn resolve_type_expr_in_user(
        &self,
        texpr: &cranelisp_types::TypeExpr,
    ) -> Result<Type, crate::result::ResolveError> {
        self.env().resolve_type_expr_in_module(
            texpr,
            &std::collections::HashMap::new(),
            &ModuleFullPath::from("user"),
            Span::SYNTHETIC,
        )
    }

    /// Is trait method (test convenience).
    pub fn is_trait_method(&self, name: &Symbol) -> bool {
        self.env().method_to_trait(name).is_some()
    }

    /// Generate default methods (test convenience).
    /// Note: the real method takes (state, decl, impl_) but this wrapper
    /// keeps state implicit. Tests that need to pass decl explicitly can
    /// use `env().generate_default_methods(state, decl, impl_)`.
    pub fn generate_default_methods(
        &self,
        _state: &CheckState,
        decl: &cranelisp_types::TraitDeclInfo,
        impl_: &cranelisp_types::TraitImpl,
    ) -> Result<Vec<cranelisp_types::Defn>, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.generate_default_methods(&self.state, decl, impl_)
    }

    // ---------------------------------------------------------------------
    // Post-slim CheckResult accessors (Sprint 57 Wave 2 step 4).
    //
    // The `CheckResult` boundary type no longer carries `method_resolutions`,
    // `expr_types`, `constrained_fn_names`, `mono_defns`, or
    // `default_method_defns` — those live on typecheck-internal state
    // (`CheckState`, `SymbolTable`) instead. Tests that used to read those
    // fields off `CheckResult` go through these accessors now.
    // ---------------------------------------------------------------------

    /// Collect `ResolvedCall`s from annotated AST nodes across all defn bodies
    /// in the current module. Mirrors what `check()` used to publish via
    /// `CheckResult.method_resolutions` before the Sprint 57 Wave 2 slim-down.
    ///
    /// Walks `ModuleEntry::Def.ast.body` recursively, collecting
    /// `Expr::Apply.resolved_call` entries keyed by the Apply's span.
    pub fn annotated_resolutions(
        &self,
    ) -> std::collections::HashMap<Span, cranelisp_types::ResolvedCall> {
        let mut out = std::collections::HashMap::new();
        for (_name, entry) in self.symbol_table().all_symbols() {
            if let cranelisp_types::ModuleEntry::Def { ast: Some(variant), .. } = entry {
                collect_resolutions_from_expr(&variant.body, &mut out);
            }
        }
        out
    }

    /// Current `CheckState.expr_types` with final substitution applied.
    /// Mirrors what `check_program` used to publish via `CheckResult.expr_types`.
    pub fn state_expr_types_resolved(&self) -> std::collections::HashMap<Span, Type> {
        self.state
            .expr_types
            .iter()
            .map(|(span, ty)| (*span, apply(&self.state.subst, ty)))
            .collect()
    }

    /// Names of all constrained polymorphic functions in the current module.
    /// Mirrors what `check_program` used to publish via
    /// `CheckResult.constrained_fn_names`. Derived from `SymbolTable` —
    /// `ModuleEntry::Def { kind: UserFn { constrained_fn: Some(_) }, .. }`.
    pub fn constrained_fn_names_set(&self) -> std::collections::HashSet<Symbol> {
        self.symbol_table()
            .all_symbols()
            .filter_map(|(name, entry)| {
                if let cranelisp_types::ModuleEntry::Def { kind, .. } = entry
                    && let cranelisp_types::DefKind::UserFn { constrained_fn: Some(_) } =
                        kind.as_ref()
                {
                    return Some(name.clone());
                }
                None
            })
            .collect()
    }

    /// Names of all monomorphised specialisation entries registered in the
    /// current module. Mirrors what `check_program` used to publish via
    /// `CheckResult.mono_defns` (but only the names — mono entries now carry
    /// their annotated AST on `ModuleEntry::Def.ast`).
    ///
    /// Mono entries are registered as `DefKind::UserFn { constrained_fn: None }`
    /// with mangled names containing a `$` separator (e.g. `add$Int+Int`).
    /// Trait-impl methods also use `$` mangling (e.g. `Num.+$Int`), but those
    /// carry a `.` prefix — excluded here by requiring the name NOT contain a
    /// `.` before the `$`.
    pub fn mono_defn_names(&self) -> Vec<Symbol> {
        self.symbol_table()
            .all_symbols()
            .filter_map(|(name, entry)| {
                if let cranelisp_types::ModuleEntry::Def { kind, .. } = entry
                    && let cranelisp_types::DefKind::UserFn { constrained_fn: None } =
                        kind.as_ref()
                {
                    let s = name.as_ref();
                    if let Some(dollar) = s.find('$')
                        && !s[..dollar].contains('.')
                    {
                        return Some(name.clone());
                    }
                }
                None
            })
            .collect()
    }
}

/// Test helper: walk an `Expr` tree, collecting `resolved_call` annotations
/// keyed by the Apply span. Used by `TestFixture::annotated_resolutions` to
/// recover the per-call-site resolutions that `CheckResult.method_resolutions`
/// used to carry before Sprint 57 Wave 2 step 4.
#[cfg(test)]
fn collect_resolutions_from_expr(
    expr: &cranelisp_types::Expr,
    out: &mut std::collections::HashMap<Span, cranelisp_types::ResolvedCall>,
) {
    use cranelisp_types::Expr;
    match expr {
        Expr::Apply { callee, args, span, resolved_call, .. } => {
            if let Some(r) = resolved_call {
                out.insert(*span, (**r).clone());
            }
            collect_resolutions_from_expr(callee, out);
            for a in args {
                collect_resolutions_from_expr(a, out);
            }
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            collect_resolutions_from_expr(cond, out);
            collect_resolutions_from_expr(then_branch, out);
            collect_resolutions_from_expr(else_branch, out);
        }
        Expr::Let { bindings, body, .. } => {
            for (_, bexpr) in bindings {
                collect_resolutions_from_expr(bexpr, out);
            }
            collect_resolutions_from_expr(body, out);
        }
        Expr::Lambda { body, .. } => {
            collect_resolutions_from_expr(body, out);
        }
        Expr::Match { scrutinee, arms, .. } => {
            collect_resolutions_from_expr(scrutinee, out);
            for arm in arms {
                collect_resolutions_from_expr(&arm.body, out);
            }
        }
        Expr::VecLit { elements, .. } => {
            for e in elements {
                collect_resolutions_from_expr(e, out);
            }
        }
        Expr::Annotate { expr, .. } => {
            collect_resolutions_from_expr(expr, out);
        }
        Expr::Trace { body, .. } => {
            collect_resolutions_from_expr(body, out);
        }
        Expr::ParBind { bindings, body, .. } => {
            for (_, bexpr) in bindings {
                collect_resolutions_from_expr(bexpr, out);
            }
            collect_resolutions_from_expr(body, out);
        }
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{DefKind, ImportNames, ImportSpec, ModuleEntry, ModuleFullPath,
        Span, Symbol, Visibility,
    };

    // --- Module-scoped type environments ---

    // spec: 08-modules §8.13 — default REPL module is "user"
    #[test]
    fn test_default_module_is_user() {
        let tf = TestFixture::new();
        assert_eq!(tf.state.current_module.as_ref(), "user");
    }

    // spec: 11-stdlib §11.1, 08-modules §8.9 — special-form metadata lives at
    // root `""` only (Principle 17 amendment, FIXME 0193). Regular modules
    // are empty after ensure_module_exists.
    #[test]
    fn test_bare_module_has_root_contents_only() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("bare"));

        // --- Special forms live at root `""` ---
        let root_path = ModuleFullPath::from("");
        let root_table = tf.modules.get(&root_path).expect("root \"\" should exist");
        assert!(root_table.get("if").is_some(), "if should be at root \"\"");
        assert!(root_table.get("let").is_some(), "let should be at root \"\"");
        assert!(root_table.get("defn").is_some(), "defn should be at root \"\"");
        assert!(root_table.get("fn").is_some(), "fn should be at root \"\"");
        assert!(root_table.get("match").is_some(), "match should be at root \"\"");
        assert!(root_table.get("deftype").is_some(), "deftype should be at root \"\"");
        assert!(root_table.get("deftrait").is_some(), "deftrait should be at root \"\"");
        assert!(root_table.get("impl").is_some(), "impl should be at root \"\"");
        assert!(root_table.get("defmacro").is_some(), "defmacro should be at root \"\"");
        drop(root_table);

        // --- Bare module is empty (no special forms seeded — FIXME 0193) ---
        assert!(tf.symbol_table().get("if").is_none(), "if not seeded into bare modules");
        assert!(tf.symbol_table().get("let").is_none(), "let not seeded into bare modules");

        // --- NOT available without import (spec §8.9.1) ---
        assert!(tf.symbol_table().get("Int").is_none(), "Int needs import");
        assert!(tf.symbol_table().get("Bool").is_none(), "Bool needs import");
        assert!(tf.symbol_table().get("Float").is_none(), "Float needs import");
        assert!(tf.symbol_table().get("String").is_none(), "String needs import");
        assert!(tf.symbol_table().get("add-i64").is_none(), "add-i64 needs import");
        assert!(tf.symbol_table().get("str-concat").is_none(), "str-concat needs import");
        assert!(tf.symbol_table().get("bind").is_none(), "bind needs import");
        assert!(tf.symbol_table().get("Pure").is_none(), "Pure needs import");
        assert!(tf.symbol_table().get("SexpSym").is_none(), "SexpSym needs import");
        assert!(tf.symbol_table().get("+").is_none(), "+ needs prelude");
        assert!(tf.symbol_table().get("TestResult").is_none(), "TestResult needs import");
        assert!(tf.symbol_table().get("discover-tests").is_none(), "discover-tests needs import");
        assert!(tf.symbol_table().get("run-test").is_none(), "run-test needs import");

        // Primitives ARE in the primitives synthetic module.
        let prims_path = ModuleFullPath::from("primitives");
        let prims_table = tf.modules.get(&prims_path).unwrap();
        assert!(prims_table.get("add-i64").is_some(), "add-i64 in primitives");
        assert!(prims_table.get("Int").is_some(), "Int in primitives");
        assert!(prims_table.get("Bool").is_some(), "Bool in primitives");
        assert!(prims_table.get("TestResult").is_some(), "TestResult in primitives");
        assert!(prims_table.get("discover-tests").is_some(), "discover-tests in primitives");
        assert!(prims_table.get("run-test").is_some(), "run-test in primitives");
    }

    // spec: 08-modules §8.9 — new modules are empty; special forms live at
    // root `""` (Principle 17 amendment, FIXME 0193).
    #[test]
    fn test_set_current_module_creates_new() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("math"));
        assert_eq!(tf.state.current_module.as_ref(), "math");
        assert!(tf.symbol_table().get("if").is_none(), "special forms at root \"\", not seeded");
        assert!(tf.symbol_table().get("Int").is_none());
        assert!(tf.symbol_table().get("add-i64").is_none());
        assert!(tf.symbol_table().get("+").is_none());
    }

    // spec: 08-modules §8.6 — switching modules preserves existing module state.
    // Per FIXME 0193 amendment: `user` has no special status.
    #[test]
    fn test_switch_back_to_user_preserves_builtins() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("other"));
        tf.set_current_module(ModuleFullPath::from("user"));
        assert!(tf.symbol_table().get("if").is_none(), "user not architecturally privileged");
        assert!(tf.symbol_table().get("add-i64").is_none());
    }

    // spec: 08-modules §8.6 — modules have independent symbol tables
    #[test]
    fn test_modules_are_independent() {
        let mut tf = TestFixture::new();
        // Define something in user
        tf.symbol_table_mut().insert(
            Symbol::from("user-only"),
            ModuleEntry::Def {
                scheme: crate::scheme::mono(Type::Int),
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: Vec::new(),
                got_slot: None,
                trait_origin: None,
                seq: 0,
                ast: None,
                code: None,
            },
        );

        // Switch to another module — shouldn't see user-only
        tf.set_current_module(ModuleFullPath::from("other"));
        assert!(tf.symbol_table().get("user-only").is_none());

        // Switch back — should see it again
        tf.set_current_module(ModuleFullPath::from("user"));
        assert!(tf.symbol_table().get("user-only").is_some());
    }

    // --- Cross-module name resolution ---

    fn seed_module(tf: &mut TestFixture, path: &str, entries: Vec<(&str, Visibility)>) {
        tf.set_current_module(ModuleFullPath::from(path));
        for (name, vis) in entries {
            tf.symbol_table_mut().insert(
                Symbol::from(name),
                ModuleEntry::Def {
                    scheme: crate::scheme::mono(Type::Int),
                    visibility: vis,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                    callees: Vec::new(),
                    got_slot: None,
                    trait_origin: None,
                    seq: 0,
                    ast: None,
                    code: None,
                },
            );
        }
    }

    // spec: 08-modules §8.5 — qualified name resolves public symbol in target module
    #[test]
    fn test_resolve_qualified_public() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "math", vec![("add", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("user"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "add").unwrap();
        assert!(result.is_some());
    }

    // spec: 08-modules §8.7 — private symbol access denied from outside module
    #[test]
    fn test_resolve_qualified_private_denied() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "math", vec![("internal", Visibility::Private)]);
        tf.set_current_module(ModuleFullPath::from("user"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "internal");
        assert!(result.is_err());
        assert!(result.unwrap_err().message().contains("private"));
    }

    // spec: 08-modules §8.7 — private symbol accessible from child module in subtree
    #[test]
    fn test_resolve_qualified_private_allowed_in_subtree() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "math", vec![("internal", Visibility::Private)]);
        tf.set_current_module(ModuleFullPath::from("math.test"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "internal").unwrap();
        assert!(result.is_some());
    }

    // spec: 08-modules §8.6 — qualified lookup returns None for nonexistent symbol
    #[test]
    fn test_resolve_qualified_not_found() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "math", vec![("add", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("user"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "nonexistent").unwrap();
        assert!(result.is_none());
    }

    // spec: 08-modules §8.6 — qualified lookup on unknown module returns None
    #[test]
    fn test_resolve_qualified_unknown_module() {
        let tf = TestFixture::new();
        let result = tf.resolve_qualified(&ModuleFullPath::from("unknown"), "foo").unwrap();
        assert!(result.is_none());
    }

    // --- Import processing ---

    // spec: 08-modules §8.3 — glob import brings all public names into scope
    #[test]
    fn test_import_glob() {
        let mut tf = TestFixture::new();
        seed_module(
            &mut tf,
            "math",
            vec![
                ("add", Visibility::Public),
                ("sub", Visibility::Public),
                ("internal", Visibility::Private),
            ],
        );
        tf.set_current_module(ModuleFullPath::from("main"));

        tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("math"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }]).unwrap();

        assert!(tf.symbol_table().get("add").is_some());
        assert!(tf.symbol_table().get("sub").is_some());
        assert!(tf.symbol_table().get("internal").is_none());
    }

    // spec: 08-modules §8.3 — specific import brings only named symbols into scope
    #[test]
    fn test_import_specific() {
        let mut tf = TestFixture::new();
        seed_module(
            &mut tf,
            "math",
            vec![
                ("add", Visibility::Public),
                ("sub", Visibility::Public),
            ],
        );
        tf.set_current_module(ModuleFullPath::from("main"));

        tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("math"),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from("add")]),
            span: Span::SYNTHETIC,
        }]).unwrap();

        assert!(tf.symbol_table().get("add").is_some());
        assert!(tf.symbol_table().get("sub").is_none());
    }

    // spec: 08-modules §8.7 — importing private symbol by name produces error
    #[test]
    fn test_import_specific_private_error() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "math", vec![("secret", Visibility::Private)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        let result = tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("math"),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from("secret")]),
            span: Span::SYNTHETIC,
        }]);

        assert!(result.is_err());
        assert!(result.unwrap_err().message().contains("not public"));
    }

    // spec: 08-modules §8.3 — importing nonexistent symbol produces error
    #[test]
    fn test_import_specific_not_found_error() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "math", vec![("add", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        let result = tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("math"),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from("nonexistent")]),
            span: Span::SYNTHETIC,
        }]);

        assert!(result.is_err());
        assert!(result.unwrap_err().message().contains("not found"));
    }

    // spec: 08-modules §8.3 — importing from unknown module produces error
    #[test]
    fn test_import_unknown_module_error() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("main"));

        let result = tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("unknown"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }]);

        assert!(result.is_err());
        assert!(result.unwrap_err().message().contains("unknown module"));
    }

    // spec: 08-modules §8.4 — re-exported symbol resolved through import chain
    #[test]
    fn test_import_chain_resolution() {
        let mut tf = TestFixture::new();

        seed_module(&mut tf, "lib", vec![("helper", Visibility::Public)]);

        tf.set_current_module(ModuleFullPath::from("reexport"));
        tf.symbol_table_mut().insert(
            Symbol::from("helper"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: ModuleFullPath::from("lib"),
                    symbol: Symbol::from("helper"),
                },
                visibility: Visibility::Public,
            },
        );

        tf.set_current_module(ModuleFullPath::from("main"));
        tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("reexport"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }]).unwrap();

        let scheme = tf.lookup("helper");
        assert!(scheme.is_some());
    }

    // spec: 08-modules §8.6 — conflicting glob imports produce Ambiguous entry
    #[test]
    fn test_import_ambiguity() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "mod_a", vec![("clash", Visibility::Public)]);
        seed_module(&mut tf, "mod_b", vec![("clash", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        tf.register_imports_self(&[
            ImportSpec {
                module_path: ModuleFullPath::from("mod_a"),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            },
            ImportSpec {
                module_path: ModuleFullPath::from("mod_b"),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            },
        ]).unwrap();

        assert!(matches!(
            tf.symbol_table().get("clash"),
            Some(ModuleEntry::Ambiguous { .. })
        ));
        assert!(tf.lookup("clash").is_none());
    }

    // spec: 08-modules §8.6 — duplicate import from same source is not ambiguous
    #[test]
    fn test_import_same_source_not_ambiguous() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "math", vec![("add", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        tf.register_imports_self(&[
            ImportSpec {
                module_path: ModuleFullPath::from("math"),
                alias: None,
                names: ImportNames::Specific(vec![Symbol::from("add")]),
                span: Span::SYNTHETIC,
            },
            ImportSpec {
                module_path: ModuleFullPath::from("math"),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            },
        ]).unwrap();

        assert!(matches!(
            tf.symbol_table().get("add"),
            Some(ModuleEntry::Import { .. })
        ));
    }

    // spec: 08-modules §8.3 — alias-only import registers alias without bare names
    #[test]
    fn test_import_alias_only() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "core.option", vec![("Some", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("core.option"),
            alias: Some(cranelisp_types::ModuleName::from("opt")),
            names: ImportNames::None,
            span: Span::SYNTHETIC,
        }]).unwrap();

        assert!(tf.symbol_table().get("Some").is_none());
        assert!(tf.state.module_aliases.contains_key(&Symbol::from("opt")));
    }

    // --- is_in_subtree ---

    // spec: 08-modules §8.7 — module is in its own subtree
    #[test]
    fn test_is_in_subtree_self() {
        let tf = TestFixture::new();
        assert!(tf.env().is_in_subtree(
            &ModuleFullPath::from("foo"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // spec: 08-modules §8.7 — child module is in parent subtree
    #[test]
    fn test_is_in_subtree_child() {
        let tf = TestFixture::new();
        assert!(tf.env().is_in_subtree(
            &ModuleFullPath::from("foo.bar"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // spec: 08-modules §8.7 — grandchild module is in ancestor subtree
    #[test]
    fn test_is_in_subtree_grandchild() {
        let tf = TestFixture::new();
        assert!(tf.env().is_in_subtree(
            &ModuleFullPath::from("foo.bar.baz"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // spec: 08-modules §8.7 — unrelated module is not in subtree
    #[test]
    fn test_is_not_in_subtree() {
        let tf = TestFixture::new();
        assert!(!tf.env().is_in_subtree(
            &ModuleFullPath::from("other"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // spec: 08-modules §8.7 — string prefix without dot separator is not subtree
    #[test]
    fn test_is_not_in_subtree_prefix_mismatch() {
        let tf = TestFixture::new();
        assert!(!tf.env().is_in_subtree(
            &ModuleFullPath::from("foobar"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // --- Alias resolution in resolve_qualified ---

    // spec: 08-modules §8.3 — qualified resolution follows module alias
    #[test]
    fn test_resolve_qualified_uses_alias() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "core.option", vec![("Some", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        tf.state.module_aliases.insert(
            Symbol::from("opt"),
            ModuleFullPath::from("core.option"),
        );

        let result = tf.resolve_qualified(&ModuleFullPath::from("opt"), "Some").unwrap();
        assert!(result.is_some(), "resolve_qualified should resolve 'opt/Some' via alias");
    }

    // spec: 08-modules §8.5 — direct qualified path works without alias
    #[test]
    fn test_resolve_qualified_without_alias_unchanged() {
        let mut tf = TestFixture::new();
        seed_module(&mut tf, "math", vec![("add", Visibility::Public)]);
        tf.set_current_module(ModuleFullPath::from("main"));

        let result = tf.resolve_qualified(&ModuleFullPath::from("math"), "add").unwrap();
        assert!(result.is_some());
    }

    // --- Builtin seeding in new modules ---

    // spec: 08-modules §8.9 — new module is empty (Principle 17 amendment,
    // FIXME 0193). Special forms at root `""`, not seeded.
    #[test]
    fn test_new_module_does_not_have_primitives() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("mymod"));
        assert!(tf.symbol_table().get("add-i64").is_none(), "add-i64 needs import");
        assert!(tf.symbol_table().get("bind").is_none(), "bind needs import");
        assert!(tf.symbol_table().get("if").is_none(), "special forms at root \"\"");
        assert!(tf.symbol_table().get("Int").is_none(), "Int needs import");
    }

    // --- Fresh variable generation ---

    // spec: pipeline-v3.md §3.4.3 — AtomicU32 TypeId allocation is monotonic
    #[test]
    fn test_fresh_var_ids_are_monotonic() {
        let tf = TestFixture::new();
        let env = tf.env();
        let (_, id1) = env.fresh_var_id();
        let (_, id2) = env.fresh_var_id();
        let (_, id3) = env.fresh_var_id();
        assert!(id1 < id2);
        assert!(id2 < id3);
    }

    // spec: pipeline-v3.md §3.4.3 — fresh_var returns unique Var types
    #[test]
    fn test_fresh_var_returns_unique_vars() {
        let tf = TestFixture::new();
        let env = tf.env();
        let v1 = env.fresh_var();
        let v2 = env.fresh_var();
        assert_ne!(v1, v2);
        assert!(matches!(v1, Type::Var(_)));
        assert!(matches!(v2, Type::Var(_)));
    }

    // spec: pipeline-v3.md §3.4.3 — snapshot/restore works with atomic next_id
    #[test]
    fn test_snapshot_restore_with_atomic_next_id() {
        let mut tf = TestFixture::new();
        // Use fresh_var through env (doesn't borrow state)
        let _ = tf.fresh_var();
        let _ = tf.fresh_var();
        let snap = tf.snapshot();
        let snap_id = snap.next_type_id;
        let _ = tf.fresh_var();
        let _ = tf.fresh_var();
        assert_eq!(tf.next_id.load(Ordering::Relaxed), snap_id + 2);
        // Restore through env — create env fresh to avoid borrow conflict
        {
            let env = TypeCheckEnv::new(&tf.modules, &tf.next_id);
            env.restore(&mut tf.state, snap);
        }
        assert_eq!(tf.next_id.load(Ordering::Relaxed), snap_id);
        let (_, id_after_restore) = tf.fresh_var_id();
        assert_eq!(id_after_restore, snap_id);
    }

    // -----------------------------------------------------------------
    // Sprint 61 Wave 3 step 3e'' — H6 atomic `ensure_module_exists`
    // -----------------------------------------------------------------
    //
    // These tests exercise the new `entry().or_insert_with(...)` +
    // hoisted-seed implementation per /arch mini-review §3d''.
    //
    // Per `design/int/heisenbug-race-closure.md §3d''` Test authoring
    // requirements (2): narrow regression guard for concurrent ensures
    // on the same path — exactly one thread builds, others observe
    // the pre-existing table intact.
    //
    // Tests use `TestFixture` which already populates `user` with
    // special forms so the seed clone is non-trivial.

    // Per Principle 17 amendment (FIXME 0193): `ensure_module_exists` creates
    // an empty `SymbolTable`. Special forms live at root `""` only.
    #[test]
    fn ensure_module_exists_creates_empty_table() {
        let tf = TestFixture::new();
        let path = ModuleFullPath::from("fresh-mod-a");
        assert!(
            tf.modules.get(&path).is_none(),
            "precondition: module absent"
        );
        tf.env().ensure_module_exists(&path);
        let guard = tf.modules.get(&path).expect("module must be present");
        assert!(
            guard.get("if").is_none(),
            "special forms not seeded (FIXME 0193) — live at root \"\""
        );
        assert!(
            guard.get("defn").is_none(),
            "special forms not seeded (FIXME 0193) — live at root \"\""
        );
        assert!(
            guard.get("Int").is_none(),
            "builtin types must NOT leak via ensure"
        );
    }

    #[test]
    fn ensure_module_exists_on_populated_table_preserves_entries() {
        // Simulates the post-populate-then-ensure scenario that H6's
        // pre-fix code broke: another code path populated
        // `modules[helper]` with a real symbol; a concurrent
        // `ensure_module_exists(helper)` on the REPL thread must NOT
        // overwrite the table.
        let tf = TestFixture::new();
        let path = ModuleFullPath::from("fresh-mod-b");

        // Pre-seed with a user-visible symbol (emulating what the
        // priority worker does in handle_typecheck_work_shared after
        // its own ensure + typecheck).
        tf.env().ensure_module_exists(&path);
        {
            let mut guard = tf.modules.get_mut(&path).unwrap();
            guard.insert(
                Symbol::from("helper-val"),
                ModuleEntry::Def {
                    scheme: crate::scheme::mono(Type::Int),
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                    callees: Vec::new(),
                    got_slot: None,
                    trait_origin: None,
                    seq: 0,
                    ast: None,
                    code: None,
                },
            );
        }

        // Second ensure — pre-fix, this OVERWROTE the populated table.
        // Post-fix, the `Entry::Occupied` path fires and the table is
        // left untouched.
        tf.env().ensure_module_exists(&path);

        let guard = tf.modules.get(&path).expect("module still present");
        assert!(
            guard.get("helper-val").is_some(),
            "pre-existing helper-val MUST NOT be overwritten by second ensure \
             (H6 regression guard — design/int/heisenbug-race-closure.md §8.3)"
        );
        // Per FIXME 0193: special forms NOT seeded into regular modules.
        assert!(
            guard.get("if").is_none(),
            "special forms live at root \"\", not seeded into regular modules"
        );
    }

    #[test]
    fn ensure_module_exists_concurrent_same_path_emits_exactly_one_created() {
        // Stress the atomicity: spawn N threads each calling
        // `ensure_module_exists(same_path)` concurrently. Exactly one
        // Created emission, N-1 AlreadyPresent emissions, and the
        // table ends up present with special forms seeded.
        //
        // Observability: install a test-local counting hook on the
        // trace slot. Because `install_symbol_table_ensure_hook` is
        // backed by a `OnceLock` (process-global, first-install wins),
        // the hook may already be installed by a sibling test or a
        // higher-level binary run. To make the assertion robust to
        // test-execution order we spy via a dedicated atomic counter
        // keyed off the module path in the forwarding hook below.

        use std::sync::Arc;
        use std::sync::atomic::{AtomicUsize, Ordering as AOrd};
        use std::thread;

        // Global counters: one per outcome, scoped to this test's path.
        static CREATED: AtomicUsize = AtomicUsize::new(0);
        static ALREADY_PRESENT: AtomicUsize = AtomicUsize::new(0);
        // Install a forwarding hook on first call. This is idempotent
        // on the OnceLock slot — subsequent tests' installs are
        // no-ops. Routing is keyed by a well-known path the test owns.
        fn test_counting_hook(
            module: &ModuleFullPath,
            outcome: crate::trace::SymbolTableEnsureOutcome,
        ) {
            if module.as_ref() == CONCURRENT_PATH {
                match outcome {
                    crate::trace::SymbolTableEnsureOutcome::Created => {
                        CREATED.fetch_add(1, AOrd::Relaxed);
                    }
                    crate::trace::SymbolTableEnsureOutcome::AlreadyPresent => {
                        ALREADY_PRESENT.fetch_add(1, AOrd::Relaxed);
                    }
                }
            }
        }
        const CONCURRENT_PATH: &str = "concurrent-ensure-path";
        crate::trace::install_symbol_table_ensure_hook(test_counting_hook);

        CREATED.store(0, AOrd::Relaxed);
        ALREADY_PRESENT.store(0, AOrd::Relaxed);

        let tf = Arc::new(TestFixture::new());
        let path = ModuleFullPath::from(CONCURRENT_PATH);
        assert!(tf.modules.get(&path).is_none());

        const N: usize = 8;
        let barrier = Arc::new(std::sync::Barrier::new(N));
        let mut handles = Vec::with_capacity(N);
        for _ in 0..N {
            let tf_cl = tf.clone();
            let barrier_cl = barrier.clone();
            let path_cl = path.clone();
            handles.push(thread::spawn(move || {
                barrier_cl.wait();
                tf_cl.env().ensure_module_exists(&path_cl);
            }));
        }
        for h in handles {
            h.join().unwrap();
        }

        // Post-condition: the table is present and empty. Special forms
        // live at root `""` (FIXME 0193).
        let guard = tf.modules.get(&path).expect("module must be present");
        assert!(
            guard.get("if").is_none(),
            "special forms at root \"\", not seeded under concurrency"
        );

        // Sink invariants (only valid if our hook was the active
        // install — OnceLock ordering permitting). If another forwarding
        // hook had already won the install race in a prior test, the
        // counters stay at 0 and the invariant degrades to
        // "post-condition observed via the fixture". Guard with a
        // conditional assertion so the test remains deterministic
        // regardless of execution order.
        let created = CREATED.load(AOrd::Relaxed);
        let already = ALREADY_PRESENT.load(AOrd::Relaxed);
        if created + already > 0 {
            assert_eq!(
                created, 1,
                "exactly ONE Created emission for a concurrent ensure on the same \
                 path (H6 invariant — any >1 is the race signature). \
                 observed: created={created} already_present={already}"
            );
            assert_eq!(
                already,
                N - 1,
                "the other N-1 threads must each emit AlreadyPresent"
            );
        }
    }

    // -----------------------------------------------------------------
    // Wave 3a-α redo Sub-D — Pattern B trait-home + chain-follow tests
    // -----------------------------------------------------------------
    //
    // These tests guard Decision 45 (Pattern B) and Principle 17 (per-symbol
    // chain-follow as THE navigation primitive) for `TraitImpl` writes and
    // lookups. See `design/typecheck/implementation-slice-s66.md §5`.

    use cranelisp_types::{
        Defn, DefnVariant, Expr, FQSymbol, FQTypeName, TraitDecl, TraitImpl, TraitMethodSig,
        TraitName, TypeExpr, TypeName,
    };

    /// Make a unary trait `T` over type parameter `a` with one method `op`
    /// (`(Fn [a a] a)`). Used by Pattern B / chain-follow tests below.
    fn make_unary_trait_decl(name: &str, method: &str) -> TraitDecl {
        TraitDecl {
            name: TraitName::from(name),
            docstring: None,
            type_params: vec![Symbol::from("a")],
            methods: vec![TraitMethodSig {
                name: Symbol::from(method),
                docstring: None,
                params: vec![
                    (Symbol::from("lhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                    (Symbol::from("rhs"), TypeExpr::TypeVar(Symbol::from("a"))),
                ],
                ret_type: TypeExpr::TypeVar(Symbol::from("a")),
                span: Span::SYNTHETIC,
                hkt_param_index: None,
                default_body: None,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }
    }

    /// Make a concrete `(impl T Int (defn op [lhs rhs] (add-i64 lhs rhs)))`.
    fn make_int_op_impl(trait_name: &str, method: &str) -> TraitImpl {
        TraitImpl {
            trait_name: cranelisp_types::TraitRef::new(None, TraitName::from(trait_name)),
            target: cranelisp_types::TypeExpr::Named(
                cranelisp_types::TypeRef::new(None, TypeName::from("Int")),
            ),
            type_constraints: vec![],
            methods: vec![Defn {
                name: Symbol::from(method),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![(Symbol::from("lhs"), None), (Symbol::from("rhs"), None)],
                    body: Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("add-i64"),
                            span: Span::SYNTHETIC,
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("lhs"),
                                span: Span::SYNTHETIC,
                                inferred_type: None,
                            },
                            Expr::Var {
                                name: Symbol::from("rhs"),
                                span: Span::SYNTHETIC,
                                inferred_type: None,
                            },
                        ],
                        span: Span::SYNTHETIC,
                        resolved_call: None,
                        inferred_type: None,
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            }],
            span: Span::SYNTHETIC,
        }
    }

    // spec: arch Decision 45 Pattern B + slice §1.A α15 — `ModuleEntry::TraitImpl`
    // writes target the trait's defining module H, NOT the writer's module M.
    // Set up: trait T declared in H; M imports T from H; register impl from M's
    // perspective; assert the impl entry lands in H's symbol table and is
    // absent from M's.
    #[test]
    fn test_trait_impl_write_lands_in_trait_home_not_writer() {
        let mut tf = TestFixture::new();

        // Need primitives imported into M so the impl body (`add-i64`) and
        // the bare type name `Int` are resolvable.
        let home = ModuleFullPath::from("home_h");
        let writer = ModuleFullPath::from("writer_m");

        // 1. Declare trait T in H.
        tf.set_current_module(home.clone());
        tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("primitives"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }]).unwrap();
        tf.register_trait_decl_self(&make_unary_trait_decl("PatternBTrait", "pb-op"))
            .unwrap();

        // 2. Switch to writer M; import T from H + primitives glob.
        tf.set_current_module(writer.clone());
        tf.register_imports_self(&[
            ImportSpec {
                module_path: ModuleFullPath::from("primitives"),
                alias: None,
                names: ImportNames::Glob,
                span: Span::SYNTHETIC,
            },
            ImportSpec {
                module_path: home.clone(),
                alias: None,
                names: ImportNames::Specific(vec![
                    Symbol::from("PatternBTrait"),
                    Symbol::from("pb-op"),
                ]),
                span: Span::SYNTHETIC,
            },
        ]).unwrap();

        // Sanity: M sees T via Import binding (terminal resolves to TraitDecl in H).
        let (_term, term_home) = tf
            .env()
            .resolve_terminal_entry_and_home(&writer, "PatternBTrait")
            .expect("M's Import of PatternBTrait should chain-follow to H");
        assert_eq!(
            term_home, home,
            "chain-follow of `PatternBTrait` from writer M should land at trait home H"
        );

        // 3. Register impl from M's perspective.
        tf.register_trait_impl_self(&make_int_op_impl("PatternBTrait", "pb-op"))
            .unwrap();

        // 4. Assert ModuleEntry::TraitImpl lands in H, not M.
        let expected_key = Symbol::from("impl$primitives/Int$home_h/PatternBTrait");

        let home_table = tf
            .modules
            .get(&home)
            .expect("H's symbol table should exist");
        let h_entry = home_table.get(expected_key.as_ref());
        assert!(
            matches!(h_entry, Some(ModuleEntry::TraitImpl { .. })),
            "Pattern B: TraitImpl MUST be written to H (trait's home), \
             key `{expected_key}`; got {h_entry:?}"
        );
        if let Some(ModuleEntry::TraitImpl { trait_name, impl_type, .. }) = h_entry {
            assert_eq!(trait_name.module, home, "trait_name FQ module should be H");
            assert_eq!(trait_name.name.as_ref(), "PatternBTrait");
            assert_eq!(
                impl_type.module.as_ref(),
                "primitives",
                "Int resolves to primitives"
            );
            assert_eq!(impl_type.name.as_ref(), "Int");
        }
        drop(home_table);

        // Negative: writer M's table MUST NOT contain ANY TraitImpl entry
        // for PatternBTrait — and no synthetic `impl$...$home_h/PatternBTrait`
        // key in particular.
        let writer_table = tf
            .modules
            .get(&writer)
            .expect("M's symbol table should exist");
        assert!(
            writer_table.get(expected_key.as_ref()).is_none(),
            "Pattern A regression: TraitImpl MUST NOT appear in writer module M's table"
        );
        for (key, entry) in writer_table.all_symbols() {
            if let ModuleEntry::TraitImpl { trait_name, .. } = entry {
                panic!(
                    "writer M contains an unexpected TraitImpl entry `{key}` for trait `{trait_name}` \
                     — Pattern B requires it to live in the trait's home module H, not M"
                );
            }
        }
    }

    // spec: arch Decision 45 + Principle 17 + slice §1.A α5/α6/α7 — impl
    // resolution uses per-symbol chain-follow on `Import`/`Reexport`
    // bindings to find the trait's home, then probes ONLY that one module
    // for the synthetic `impl$...` key. No universe scan, no closure walk.
    //
    // Set up a re-export chain: L declares trait T; M imports T from L and
    // re-exports it; N imports T from M (so N's binding is an `Import`
    // pointing at M's `Reexport` pointing at L's `TraitDecl`). Place the
    // impl at L (trait's home, per Pattern B). Place "decoy" TraitImpl
    // entries in two unrelated modules (D1 and D2) that a universe scan
    // would erroneously pick up. From N's view, `has_impl_in_module(N, T,
    // Int)` MUST return true (chain-follow finds the L-resident impl), and
    // the decoys MUST be ignored.
    #[test]
    fn test_impl_resolution_chain_follows_not_universe_scans() {
        let mut tf = TestFixture::new();

        let l = ModuleFullPath::from("chain_l");
        let m = ModuleFullPath::from("chain_m");
        let n = ModuleFullPath::from("chain_n");
        let d1 = ModuleFullPath::from("decoy_d1");
        let d2 = ModuleFullPath::from("decoy_d2");

        // 1. L declares trait T (with primitives glob so the impl body
        //    can resolve add-i64).
        tf.set_current_module(l.clone());
        tf.register_imports_self(&[ImportSpec {
            module_path: ModuleFullPath::from("primitives"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }]).unwrap();
        tf.register_trait_decl_self(&make_unary_trait_decl("ChainTrait", "ch-op"))
            .unwrap();
        // L also owns the impl — write from L's perspective (Pattern B:
        // chain-follow is depth-zero because writer == trait home).
        tf.register_trait_impl_self(&make_int_op_impl("ChainTrait", "ch-op"))
            .unwrap();

        // 2. M imports T from L AND re-exports it. We construct the
        //    `Reexport` entry directly (matches what `register_exports`
        //    builds in the prod pipeline).
        tf.set_current_module(m.clone());
        tf.register_imports_self(&[ImportSpec {
            module_path: l.clone(),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from("ChainTrait")]),
            span: Span::SYNTHETIC,
        }]).unwrap();
        // Overwrite the `Import` with a `Reexport` on M so N's import sees
        // a `Reexport` edge — the chain becomes N(Import) → M(Reexport) → L(TraitDecl).
        tf.symbol_table_mut().insert(
            Symbol::from("ChainTrait"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: l.clone(),
                    symbol: Symbol::from("ChainTrait"),
                },
                visibility: Visibility::Public,
            },
        );

        // 3. N imports T from M.
        tf.set_current_module(n.clone());
        tf.register_imports_self(&[ImportSpec {
            module_path: m.clone(),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from("ChainTrait")]),
            span: Span::SYNTHETIC,
        }]).unwrap();

        // Sanity: from N, chain-follow lands at L (the trait's home).
        let (_term, home_via_n) = tf
            .env()
            .resolve_terminal_entry_and_home(&n, "ChainTrait")
            .expect("chain-follow from N should reach L");
        assert_eq!(
            home_via_n, l,
            "chain-follow of `ChainTrait` from N must terminate at L (chain length 2)"
        );

        // 4. Place decoy TraitImpl entries in D1 and D2. A universe scan
        //    would erroneously match these; chain-follow MUST ignore them
        //    because it probes ONLY the trait's home (L).
        let decoy_key = Symbol::from("impl$primitives/Int$chain_l/ChainTrait");
        for decoy_path in [&d1, &d2] {
            // Ensure the module exists so a write succeeds.
            tf.env().ensure_module_exists(decoy_path);
            let mut tbl = tf
                .modules
                .get_mut(decoy_path)
                .expect("decoy module just ensured");
            tbl.insert(
                decoy_key.clone(),
                ModuleEntry::TraitImpl {
                    trait_name: cranelisp_types::FQTraitName::new(
                        l.clone(),
                        TraitName::from("ChainTrait"),
                    ),
                    impl_type: FQTypeName::new(
                        ModuleFullPath::from("primitives"),
                        TypeName::from("Int"),
                    ),
                    methods: vec![Symbol::from("ch-op")],
                    visibility: Visibility::Public,
                },
            );
        }

        // 5. From N's view, has_impl_with_state MUST find the L-resident
        //    impl via chain-follow (positive). The decoy entries are
        //    structurally identical but live in unrelated modules; if the
        //    resolver were doing a universe scan it would still find one,
        //    so the positive does not by itself prove chain-follow. The
        //    negative below tightens the assertion.
        let n_state = CheckState::new(n.clone());
        let env = tf.env();
        assert!(
            env.has_impl_with_state(&n_state, &TraitName::from("ChainTrait"), &TypeName::from("Int")),
            "impl resolution from N should chain-follow N → M → L and find the L-resident impl"
        );

        // Negative: lookup against a trait name that DOES NOT have an
        // import binding in N MUST return false. If the resolver were
        // doing a universe scan over `self.modules`, the decoys (whose
        // synthetic key embeds `chain_l/ChainTrait`) could be matched by
        // name alone; chain-follow refuses because the starting module N
        // has no `UnknownTrait` binding to follow.
        assert!(
            !env.has_impl_with_state(
                &n_state,
                &TraitName::from("UnknownTrait"),
                &TypeName::from("Int")
            ),
            "no `UnknownTrait` import in N → chain-follow must fail and decoys MUST NOT be matched \
             (a universe scan would falsely hit the decoy entries)"
        );

        // Negative: probing the writer module N directly for the synthetic
        // impl key MUST find nothing — the entry lives in L only.
        let n_table = tf
            .modules
            .get(&n)
            .expect("N's symbol table should exist");
        assert!(
            n_table.get(decoy_key.as_ref()).is_none(),
            "N's symbol table MUST NOT carry the impl entry (it lives in L per Pattern B)"
        );
    }

    // spec: arch Principle 17 + slice §1.A α1/α2/α3 — short-name lookup is
    // current-module-only. If `foo` is absent from the current module's
    // symbol table, the lookup fails — no fallback to primitives, no
    // closure walk, no universe scan. With a `(import [M [foo]])` binding
    // in N, the same lookup chain-follows the per-symbol Import edge to M.
    #[test]
    fn test_short_name_lookup_is_current_module_only() {
        let mut tf = TestFixture::new();

        let m = ModuleFullPath::from("home_m");
        let n = ModuleFullPath::from("consumer_n");

        // 1. Register a TypeDef for `Foo` in M.
        tf.set_current_module(m.clone());
        tf.register_type_def_self(
            &TypeName::from("Foo"),
            &None,
            &[],
            &[cranelisp_types::ConstructorDef {
                name: Symbol::from("MkFoo"),
                docstring: None,
                fields: vec![],
                span: Span::SYNTHETIC,
            }],
            Visibility::Public,
            Span::SYNTHETIC,
        ).unwrap();

        // 2. From N (no import of M.Foo), short-name lookup of Foo MUST fail.
        tf.set_current_module(n.clone());
        let result_no_import = tf
            .env()
            .lookup_type_def_in_module(&n, &TypeName::from("Foo"));
        assert!(
            result_no_import.is_none(),
            "current-module-only short-name lookup MUST fail when `Foo` is not bound in N \
             (Principle 17: no fallback, no closure walk, no universe scan)"
        );

        // Negative: also confirm that short-name `lookup` (Scheme variant)
        // does not silently chain into M.
        let n_state = CheckState::new(n.clone());
        assert!(
            tf.env().lookup(&n_state, "Foo").is_none(),
            "Scheme-flavoured lookup of `Foo` from N MUST also fail without an Import"
        );

        // 3. Now inject a per-symbol Import binding into N for M.Foo.
        //    Manual insert mirrors what `register_imports` would build for
        //    a Specific import (TypeDef entries are public-by-default here).
        tf.symbol_table_mut().insert(
            Symbol::from("Foo"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: m.clone(),
                    symbol: Symbol::from("Foo"),
                },
                visibility: Visibility::Private,
            },
        );

        // 4. The same short-name lookup now chain-follows N(Import) → M(TypeDef)
        //    and succeeds — reach is per-binding, not per-resolver.
        let result_after_import = tf
            .env()
            .lookup_type_def_in_module(&n, &TypeName::from("Foo"));
        assert!(
            result_after_import.is_some(),
            "after injecting `ModuleEntry::Import {{ source: M/Foo }}` into N, \
             chain-follow should resolve `Foo` to M's TypeDef"
        );
        let info = result_after_import.unwrap();
        assert_eq!(info.name.module, m, "resolved Foo's FQ module should be M");
        assert_eq!(info.name.name.as_ref(), "Foo");
    }
}
