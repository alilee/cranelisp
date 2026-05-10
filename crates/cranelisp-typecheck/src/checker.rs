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

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};

use dashmap::DashMap;

use cranelisp_types::{ErrorLocation,
    ConstructorInfo, CranelispError, ExportSpec, FQSymbol, ImportNames, ImportSpec,
    MethodResolutions, ModuleEntry, ModuleFullPath, ResolvedCall, Scheme, Span,
    Subst, Symbol, SymbolTable, TraitName, Type, TypeDefInfo, TypeId, TypeName, Warning,
    apply,
};

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
            method_resolutions: HashMap::new(),
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
        TypeCheckEnv { modules, next_id }
    }

    // --- Module-scoped symbol table accessors ---

    /// Get a read guard for the current module's symbol table.
    ///
    /// Returns a DashMap `Ref` guard that derefs to `SymbolTable`.
    /// The guard holds a per-shard read lock — drop it before acquiring
    /// another guard to avoid deadlocks (see design/typecheck/dashmap-migration.md §4.10).
    pub(crate) fn current_symbol_table(
        &self,
        state: &CheckState,
    ) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable<C, L>> {
        self.modules
            .get(&state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in modules map"))
    }

    /// Get a write guard for the current module's symbol table.
    ///
    /// Returns a DashMap `RefMut` guard that derefs mutably to `SymbolTable`.
    /// Drop before acquiring another guard.
    pub(crate) fn current_symbol_table_mut(
        &self,
        state: &CheckState,
    ) -> dashmap::mapref::one::RefMut<'_, ModuleFullPath, SymbolTable<C, L>> {
        self.modules
            .get_mut(&state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in modules map"))
    }

    /// Ensure a module's symbol table exists, creating it if needed.
    ///
    /// Uses DashMap interior mutation — safe with `&self`. Seeds new modules
    /// with imports from `primitives` and seedable entries from `user`.
    /// Does NOT set `self.state.current_module` — callers set the module
    /// on their own `CheckState`.
    ///
    // FIXME(/typecheck) — cross-skill hybrid ownership per
    // `design/int/heisenbug-race-closure.md §3d''` (/arch mini-review,
    // Sprint 61 Wave 3, 2026-04-22). /int authored this rewrite under an
    // explicit /arch cross-skill grant to close the H6 non-atomic
    // compare-then-set race. /typecheck reviews the diff before commit.
    // Ownership boundary unchanged: the public signature of
    // `ensure_module_exists` is untouched; this precedent is NARROW and
    // does NOT authorise further /int → crates/ edits without /arch
    // arbitration.
    //
    // Mechanism (option d per §8.3.1 + /arch §3d'' mandatory variant):
    //   1. Hoist the `user`-seed clone OUTSIDE `entry()` so the
    //      `or_insert_with` closure performs NO nested DashMap access.
    //      DashMap v6's `entry` guard holds a shard write-lock across
    //      the closure; a nested `get` on the same shard would deadlock.
    //      Pre-computing the seed is zero-cost (the same Vec<(Symbol,
    //      ModuleEntry)> was allocated before; it is simply materialised
    //      one statement earlier).
    //   2. `entry(path).or_insert_with(|| {...})` performs the
    //      check-then-insert atomically under the shard write-lock, so
    //      no concurrent thread can insert between the check and the
    //      store. Replaces the prior unconditional `self.modules.insert`
    //      at old line 237 that overwrote populated tables built by the
    //      priority worker's concurrent ensure.
    //   3. Emit `SymbolTableEnsure { module, outcome }` so post-fix
    //      traces make the atomicity observable. `Created` fires inside
    //      the closure (we built and inserted); `AlreadyPresent` fires
    //      on the fall-through (another caller won the race).
    pub fn ensure_module_exists(&self, path: &ModuleFullPath) {
        // (1) Hoist seed clone OUTSIDE the `entry()` critical section.
        // Read `user` under its own shard read-lock; clone; drop the
        // guard BEFORE we take the `entry()` write-lock on `path`. This
        // avoids any risk of shard-collision deadlock between
        // `modules[path]` and `modules[user]`, and keeps the closure
        // below free of nested DashMap access.
        let user_path = ModuleFullPath::from("user");
        let seed_entries: Vec<(Symbol, ModuleEntry<C>)> = self.modules.get(&user_path)
            .map(|guard| {
                // Special forms only: language keywords universally
                // available per spec §11.1. Everything else requires
                // explicit import or qualified access (spec §8.9.1,
                // §8.9.4).
                guard.all_symbols()
                    .filter(|(_name, entry)| {
                        matches!(entry, ModuleEntry::Def { kind, .. }
                            if matches!(kind.as_ref(),
                                cranelisp_types::DefKind::SpecialForm { .. }
                            )
                        )
                    })
                    .map(|(name, entry)| (name.clone(), entry.clone()))
                    .collect()
            })
            .unwrap_or_default();

        // (2) Atomic check-then-insert. `entry(...).or_insert_with(...)`
        // holds the shard write-lock on `path`'s shard across the
        // closure; a concurrent ensure on the same path is serialised
        // behind it and observes the entry as Occupied.
        //
        // Outcome determination: DashMap v6 does not surface
        // "was-inserted" from `or_insert_with` directly, so we use
        // the pattern `match entry {}` — Occupied means the key was
        // already present (AlreadyPresent); Vacant means we're about
        // to build and insert (Created).
        //
        // Use the generic `new_with_params` constructor so the table
        // matches the parameterised flavour `<C, L>` of `self.modules`.
        use dashmap::mapref::entry::Entry;
        let outcome = match self.modules.entry(path.clone()) {
            Entry::Occupied(_) => {
                crate::trace::SymbolTableEnsureOutcome::AlreadyPresent
            }
            Entry::Vacant(slot) => {
                let mut table = SymbolTable::<C, L>::new_with_params(path.clone());
                for (name, entry) in seed_entries {
                    table.insert(name, entry);
                }
                slot.insert(table);
                crate::trace::SymbolTableEnsureOutcome::Created
            }
        };
        // (3) Emit observability event. Fires AFTER the shard
        // write-lock has been released (both Occupied guard and the
        // Vacant-insert's guard are dropped by the match arm's end).
        // Hot-path cost when no sink is installed: single relaxed
        // OnceLock load + null check.
        crate::trace::emit_symbol_table_ensure(path, outcome);
    }

    /// Check whether a module has been registered.
    pub fn has_module(&self, path: &ModuleFullPath) -> bool {
        self.modules.contains_key(path)
    }

    /// Look up a TypeDefInfo by bare TypeName, scanning all loaded module SymbolTables.
    ///
    /// Returns the first matching TypeDefInfo found across all modules.
    /// Used where the old `TypeDefRegistry.get()` was called.
    pub fn lookup_type_def(&self, name: &TypeName) -> Option<TypeDefInfo> {
        let sym = Symbol::from(name.as_ref());
        let primitives_path = ModuleFullPath::from("primitives");
        let mut primitives_fallback: Option<TypeDefInfo> = None;
        for guard in self.modules.iter() {
            if let Some(ModuleEntry::TypeDef { info, .. }) = guard.get(sym.as_ref()) {
                if *guard.key() == primitives_path {
                    // Defer primitives — prefer user-defined types.
                    primitives_fallback = Some(info.clone());
                } else {
                    return Some(info.clone());
                }
            }
        }
        primitives_fallback
    }

    /// Look up the parent type name for a constructor by scanning all modules.
    ///
    /// Returns the bare TypeName of the parent type.
    /// Also handles product types where the constructor has the same name as the
    /// type — in that case, the `ModuleEntry::TypeDef` with `constructor_scheme`
    /// is the authority (the Constructor entry was overwritten by the TypeDef entry).
    pub fn lookup_constructor_type(&self, ctor_name: &str) -> Option<TypeName> {
        for guard in self.modules.iter() {
            match guard.get(ctor_name) {
                Some(ModuleEntry::Constructor { type_name, .. }) => {
                    return Some(type_name.name.clone());
                }
                Some(ModuleEntry::TypeDef { info, constructor_scheme: Some(_), .. }) => {
                    // Product type: constructor has same name as type.
                    return Some(info.name.name.clone());
                }
                _ => {}
            }
        }
        None
    }

    /// Check whether a constructor is marked as internal (not user-constructable).
    ///
    /// Scans all modules for the constructor, then checks the parent type's
    /// TypeDefInfo for the internal flag.
    pub fn is_internal_constructor_check(&self, ctor_name: &str) -> bool {
        // Find which type owns this constructor
        let type_name = match self.lookup_constructor_type(ctor_name) {
            Some(tn) => tn,
            None => return false,
        };
        // Look up the TypeDefInfo
        if let Some(info) = self.lookup_type_def(&type_name) {
            return info.constructors.iter().any(|c| c.name.as_ref() == ctor_name && c.internal);
        }
        false
    }

    /// Iterate over all type definitions across all loaded modules.
    ///
    /// Returns (TypeName, TypeDefInfo) pairs. Used by REPL to sync type defs for display.
    pub fn all_type_defs(&self) -> Vec<(TypeName, TypeDefInfo)> {
        let mut result = Vec::new();
        for guard in self.modules.iter() {
            for (_name, entry) in guard.all_symbols() {
                if let ModuleEntry::TypeDef { info, .. } = entry {
                    result.push((info.name.name.clone(), info.clone()));
                }
            }
        }
        result
    }

    /// Build a map of all type definitions (TypeName -> TypeDefInfo).
    ///
    /// Used by external consumers that need the old HashMap-based API.
    pub fn all_type_defs_map(&self) -> HashMap<TypeName, TypeDefInfo> {
        self.all_type_defs().into_iter().collect()
    }

    /// Access the per-module symbol tables (for display, introspection).
    pub fn modules(&self) -> &DashMap<ModuleFullPath, SymbolTable<C, L>> {
        self.modules
    }

    /// Build type_defs and constructor_to_type maps from SymbolTables.
    ///
    /// Used by the worker to build partial `CheckResult` for inline
    /// macro compilation without going through `finalize_check_result`.
    ///
    /// NOTE: These maps will be eliminated when the backend reads from
    /// SharedState SymbolTables directly (FQTypeName migration wave C).
    pub fn snapshot_type_defs(&self) -> (HashMap<TypeName, TypeDefInfo>, HashMap<Symbol, TypeName>) {
        let type_defs = self.all_type_defs_map();
        let constructor_to_type: HashMap<Symbol, TypeName> = type_defs.iter()
            .flat_map(|(type_name, info)| {
                info.constructors.iter().map(move |c| (c.name.clone(), type_name.clone()))
            })
            .collect();
        (type_defs, constructor_to_type)
    }

    /// Look up a specific module's symbol table by path.
    /// Returns a DashMap read guard that derefs to `SymbolTable`.
    /// Used by `/imports` to resolve type signatures of imported symbols.
    pub fn module_table(&self, path: &ModuleFullPath) -> Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable<C, L>>> {
        self.modules.get(path)
    }

    /// Look up a specific module's symbol table by path, returning an owned clone.
    /// Used by callers that need to own the symbol table (e.g., serialization).
    pub fn module_table_cloned(&self, path: &ModuleFullPath) -> Option<SymbolTable<C, L>> {
        self.modules.get(path).map(|guard| guard.clone())
    }

    /// Look up a symbol's GOT slot in a specific module's symbol table.
    pub fn get_got_slot(&self, module: &ModuleFullPath, name: &Symbol) -> Option<usize> {
        let guard = self.modules.get(module)?;
        match guard.get(name.as_ref())? {
            ModuleEntry::Def { got_slot, .. } => *got_slot,
            _ => None,
        }
    }

    /// Get a reference to the underlying modules DashMap.
    /// Used by the integration layer to construct a `CompilationEnv` that
    /// resolves GOT slots by reading symbol tables directly.
    pub fn modules_ref(&self) -> &dashmap::DashMap<ModuleFullPath, SymbolTable<C, L>> {
        self.modules
    }

    /// Build an FQTypeName for a bare TypeName by looking up SymbolTables.
    /// Falls back to the current module if the type is not found.
    pub(crate) fn fqtn_for_bare_type_name(&self, state: &CheckState, type_name: &TypeName) -> cranelisp_types::FQTypeName {
        if let Some(info) = self.lookup_type_def(type_name) {
            return info.name.clone();
        }
        // Primitive types
        let module = match type_name.as_ref() {
            "Int" | "Bool" | "Float" | "String" | "Vec" | "IO" | "Trace" | "TestResult" =>
                ModuleFullPath::from("primitives"),
            _ => state.current_module.clone(),
        };
        cranelisp_types::FQTypeName::new(module, type_name.clone())
    }

    /// Look up the defining module for a symbol. Checks the `primitives` module
    /// first (for core traits and builtins), then falls back to the current module.
    pub fn defining_module_for(&self, state: &CheckState, name: &str) -> ModuleFullPath {
        let primitives_path = ModuleFullPath::from("primitives");
        let found = self.modules.get(&primitives_path)
            .map(|guard| guard.get(name).is_some())
            .unwrap_or(false);
        if found {
            return primitives_path;
        }
        state.current_module.clone()
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
    fn lookup_in_current_module(&self, state: &CheckState, name: &str) -> Option<Scheme> {
        let entry = {
            let guard = self.modules.get(&state.current_module)?;
            guard.get(name)?.clone()
        };
        self.extract_scheme_from_entry_owned(&entry, 0)
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
            ModuleEntry::Constructor { scheme, .. } => Some(scheme.clone()),
            ModuleEntry::TypeDef {
                constructor_scheme: Some(scheme),
                ..
            } => Some(scheme.clone()),
            ModuleEntry::Import { source } => {
                self.resolve_fq_symbol(source, depth + 1)
            }
            ModuleEntry::Reexport { source } => {
                self.resolve_fq_symbol(source, depth + 1)
            }
            _ => None,
        }
    }

    /// Resolve a fully-qualified symbol reference by looking up the source
    /// module's symbol table.
    ///
    /// Clone-and-drop discipline: clone entry from guard, drop guard,
    /// then follow chain.
    fn resolve_fq_symbol(&self, fq: &FQSymbol, depth: usize) -> Option<Scheme> {
        let entry = {
            let guard = self.modules.get(&fq.module)?;
            guard.get(fq.symbol.as_ref())?.clone()
        };
        self.extract_scheme_from_entry_owned(&entry, depth)
    }

    /// Resolve a name in the current module to its terminal `ModuleEntry`,
    /// following Import/Reexport chains. Returns an owned clone.
    pub(crate) fn resolve_entry_in_current_module(&self, state: &CheckState, name: &str) -> Option<ModuleEntry<C>> {
        let entry = {
            let guard = self.modules.get(&state.current_module)?;
            guard.get(name)?.clone()
        };
        self.resolve_to_terminal_entry_owned(&entry, 0)
    }

    /// Follow Import/Reexport chains to the terminal `ModuleEntry`.
    /// Returns an owned clone. Clone-and-drop discipline applied at each step.
    pub(crate) fn resolve_to_terminal_entry_owned(
        &self,
        entry: &ModuleEntry<C>,
        depth: usize,
    ) -> Option<ModuleEntry<C>> {
        if depth > IMPORT_CHAIN_DEPTH_LIMIT {
            return None;
        }
        match entry {
            ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                let target = {
                    let guard = self.modules.get(&source.module)?;
                    guard.get(source.symbol.as_ref())?.clone()
                };
                self.resolve_to_terminal_entry_owned(&target, depth + 1)
            }
            other => Some(other.clone()),
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
        // then check visibility and follow chains.
        let entry = {
            let guard = match self.modules.get(&resolved_path) {
                Some(g) => g,
                None => return Ok(None), // Module not loaded
            };
            match guard.get(name) {
                Some(e) => e.clone(),
                None => return Ok(None),
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
        if scheme.vars.is_empty() {
            return scheme.ty.clone();
        }
        let mut inst_subst = Subst::new();
        for &var_id in &scheme.vars {
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
            scheme.vars.iter().copied().collect();

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
        state.method_resolutions.clear();
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
            insert_imports_detecting_ambiguity(
                &mut self.current_symbol_table_mut(state),
                imports_to_add,
            );
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
            insert_imports_detecting_ambiguity(
                &mut self.current_symbol_table_mut(state),
                reexports,
            );
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
                        ModuleEntry::Reexport { source: fq },
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
                ModuleEntry::Constructor { type_name, .. } => {
                    type_name.name.as_ref() == parent.as_ref()
                }
                ModuleEntry::Def { trait_origin, kind, .. } => {
                    matches!(
                        kind.as_ref(),
                        cranelisp_types::DefKind::Primitive { .. }
                            | cranelisp_types::DefKind::UserFn { .. }
                    ) && trait_origin.as_ref().is_some_and(|fqtn| fqtn.name == trait_name)
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
                    ModuleEntry::Reexport { source: fq },
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
                        ModuleEntry::Import { source: fq },
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
                ModuleEntry::Constructor { type_name, .. } => {
                    type_name.name.as_ref() == parent.as_ref()
                }
                ModuleEntry::Def { trait_origin, kind, .. } => {
                    matches!(
                        kind.as_ref(),
                        cranelisp_types::DefKind::Primitive { .. }
                            | cranelisp_types::DefKind::UserFn { .. }
                    ) && trait_origin.as_ref().is_some_and(|fqtn| fqtn.name == trait_name)
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
                    ModuleEntry::Import { source: fq },
                ));
            }
        }
        result
    }

    // --- REPL query methods for output formatting ---

    /// Look up a type definition and return its constructors.
    pub fn get_type_constructors(&self, type_name: &TypeName) -> Option<Vec<ConstructorInfo>> {
        self.lookup_type_def(type_name)
            .map(|info| info.constructors)
    }

    /// Look up the FQTypeName for a bare type name via SymbolTables.
    /// Used for display formatting and diagnostics.
    pub fn fqtn_for_type(&self, type_name: &TypeName) -> Option<cranelisp_types::FQTypeName> {
        self.lookup_type_def(type_name)
            .map(|info| info.name)
    }

    /// Return all trait names that have an impl registered for `type_name`.
    /// Results are sorted alphabetically.
    ///
    /// Scans all loaded module SymbolTables for `ModuleEntry::TraitImpl` entries
    /// whose `impl_type.name` matches the given type name.
    pub fn get_impls_for_type(&self, type_name: &TypeName) -> Vec<TraitName> {
        let mut traits: Vec<TraitName> = Vec::new();
        for guard in self.modules.iter() {
            for (_name, entry) in guard.all_symbols() {
                if let ModuleEntry::TraitImpl { trait_name, impl_type, .. } = entry
                    && &impl_type.name == type_name && !traits.contains(&trait_name.name)
                {
                    traits.push(trait_name.name.clone());
                }
            }
        }
        traits.sort();
        traits
    }

    /// Return the method names declared in a trait.
    pub fn get_trait_methods(&self, trait_name: &TraitName) -> Option<Vec<Symbol>> {
        self.lookup_trait_decl(trait_name)
            .map(|decl| decl.methods.iter().map(|m| m.name.clone()).collect())
    }

    /// Look up a TraitDecl by bare TraitName, scanning all loaded module SymbolTables.
    pub fn lookup_trait_decl(&self, trait_name: &TraitName) -> Option<cranelisp_types::TraitDecl> {
        let sym = Symbol::from(trait_name.as_ref());
        for guard in self.modules.iter() {
            if let Some(ModuleEntry::TraitDecl { decl, .. }) = guard.get(sym.as_ref()) {
                return Some(decl.clone());
            }
        }
        None
    }

    /// Look up which trait a method name belongs to, via trait_origin on ModuleEntry::Def.
    ///
    /// Scans all loaded modules for a Def entry with the given name that has
    /// a `trait_origin` set.
    pub fn method_to_trait(&self, method_name: &Symbol) -> Option<TraitName> {
        for guard in self.modules.iter() {
            if let Some(ModuleEntry::Def { trait_origin: Some(fqtn), .. }) = guard.get(method_name.as_ref()) {
                return Some(fqtn.name.clone());
            }
        }
        None
    }

    /// Check if a method belongs to a specific trait, via trait_origin on ModuleEntry::Def.
    pub fn method_belongs_to_trait(&self, method: &Symbol, trait_name: &TraitName) -> bool {
        self.method_to_trait(method).as_ref() == Some(trait_name)
    }

    /// Check if a trait impl exists for the given (trait_name, impl_type) pair.
    ///
    /// Scans all loaded module SymbolTables for a `ModuleEntry::TraitImpl` entry
    /// matching both the trait name and the implementation type name.
    pub fn has_impl(&self, trait_name: &TraitName, impl_type: &TypeName) -> bool {
        for guard in self.modules.iter() {
            for (_name, entry) in guard.all_symbols() {
                if let ModuleEntry::TraitImpl { trait_name: tn, impl_type: it, .. } = entry
                    && &tn.name == trait_name && &it.name == impl_type
                {
                    return true;
                }
            }
        }
        false
    }

    /// Return all type names that implement a given trait.
    /// Results are sorted alphabetically.
    ///
    /// Scans all loaded module SymbolTables for `ModuleEntry::TraitImpl` entries
    /// whose `trait_name.name` matches the given trait name.
    pub fn get_implementing_types(&self, trait_name: &TraitName) -> Vec<TypeName> {
        let mut types: Vec<TypeName> = Vec::new();
        for guard in self.modules.iter() {
            for (_name, entry) in guard.all_symbols() {
                if let ModuleEntry::TraitImpl { trait_name: tn, impl_type, .. } = entry
                    && &tn.name == trait_name && !types.contains(&impl_type.name)
                {
                    types.push(impl_type.name.clone());
                }
            }
        }
        types.sort();
        types
    }

    /// Resolve a module name: try as child of current module first, then as
    /// root module. Returns `None` if not found.
    pub fn resolve_module_by_name(&self, state: &CheckState, name: &str) -> Option<ModuleFullPath> {
        let child_path =
            ModuleFullPath::from(format!("{}.{}", state.current_module, name));
        if self.has_module(&child_path) {
            return Some(child_path);
        }
        // Try as root module
        let root_path = ModuleFullPath::from(name);
        if self.has_module(&root_path) {
            return Some(root_path);
        }
        None
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
    pub fn unregister_trait(&self, _trait_name: &TraitName) {
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
    pub fn remove_module(&self, module_path: &ModuleFullPath) -> Option<SymbolTable<C, L>> {
        let (_, table) = self.modules.remove(module_path)?;

        // Unregister traits defined by this module.
        let traits_to_remove: Vec<TraitName> = table
            .all_symbols()
            .filter_map(|(_, entry)| {
                if let ModuleEntry::TraitDecl { decl, .. } = entry {
                    Some(decl.name.clone())
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
    pub fn insert_module(&self, table: SymbolTable<C, L>) {
        self.modules.insert(table.path.clone(), table);
    }

    // --- Cache restoration ---

    /// Restore a module's symbol table from cached metadata.
    ///
    /// Installs the given symbol table into the modules map.
    /// All definitions (types, traits, constructors) are stored directly
    /// on the SymbolTable, so no separate registry reconstruction is needed.
    /// Trait method resolution uses `trait_origin` on `ModuleEntry::Def` entries.
    ///
    /// Used by the pipeline's cache-hit path (src/pipeline.rs).
    pub fn restore_cached_module(&self, table: SymbolTable<C, L>) {
        let path = table.path.clone();

        // Advance next_id past any type variable IDs used in the cached
        // module's schemes. Without this, instantiate_constrained may create
        // fresh vars with IDs that collide with vars already in cached schemes,
        // causing infinite recursion in apply_subst.
        self.advance_next_id_past_table(&table);

        self.modules.insert(path, table);
    }

    /// Advance `next_id` past the maximum type variable ID found in a symbol table.
    ///
    /// Scans all schemes (including constraint vars) in the table and ensures
    /// `next_id` is strictly greater than any ID found. This prevents ID
    /// collisions between cached schemes and freshly created type variables.
    fn advance_next_id_past_table(&self, table: &SymbolTable<C, L>) {
        let mut max_id: Option<TypeId> = None;

        for (_name, entry) in table.all_symbols() {
            let scheme = match entry {
                ModuleEntry::Def { scheme, .. } => Some(scheme),
                ModuleEntry::Constructor { scheme, .. } => Some(scheme),
                _ => None,
            };
            if let Some(s) = scheme {
                // Check vars in the scheme's type.
                if let Some(id) = cranelisp_types::max_type_var_id(&s.ty) {
                    max_id = Some(max_id.map_or(id, |m: TypeId| m.max(id)));
                }
                // Check quantified vars (they may not appear in the type
                // after substitution, but we reserved those IDs).
                for &v in &s.vars {
                    max_id = Some(max_id.map_or(v, |m| m.max(v)));
                }
                // Check constraint keys.
                for &v in s.constraints.keys() {
                    max_id = Some(max_id.map_or(v, |m| m.max(v)));
                }
            }
        }

        if let Some(id) = max_id {
            self.next_id.fetch_max(id + 1, Ordering::Relaxed);
        }
    }

    /// Restore trait implementation registrations from cached data.
    ///
    /// After registry elimination, `ModuleEntry::TraitImpl` entries are stored
    /// directly on the module's SymbolTable and restored with it via
    /// `restore_cached_module`. This method is now a no-op but kept for API
    /// compatibility with the caller in `src/worker.rs`.
    pub fn restore_cached_impls(&self, _mangled_names: &[String]) {
        // TraitImpl entries are on the SymbolTable — no separate reconstruction needed.
    }

    // --- REPL snapshot/restore ---

    /// Take a snapshot of the current state for REPL error recovery.
    pub fn snapshot(&self, state: &CheckState) -> ReplSnapshot {
        let symbol_keys = self.current_symbol_table(state).symbols.keys().cloned().collect();
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
        state.method_resolutions.clear();
        state.warnings.clear();
        state.pending_auto_curry.clear();
        // Remove symbol table entries added after the snapshot was taken.
        self.current_symbol_table_mut(state)
            .symbols
            .retain(|key, _| snapshot.symbol_keys.contains(key));
        // Restore scope stack depth (pop frames left by failed check_defn_body).
        state.env.truncate_to(snapshot.scope_depth);
    }

    // --- Known types lookup (for resolve_type_expr) ---

    /// Build a map of known type names for type expression resolution.
    ///
    /// Scans all loaded module SymbolTables for TypeDef entries and builds
    /// a map of (TypeName -> (FQTypeName, arity)).
    pub(crate) fn known_type_names(&self) -> crate::resolve::KnownTypes {
        let mut result = crate::resolve::KnownTypes::new();
        let primitives_path = ModuleFullPath::from("primitives");
        // Process primitives module first so user-defined types shadow builtins.
        // HashMap last-insert-wins ensures local definitions take precedence.
        if let Some(guard) = self.modules.get(&primitives_path) {
            for (_name, entry) in guard.all_symbols() {
                if let ModuleEntry::TypeDef { info, .. } = entry {
                    result.insert(
                        info.name.name.clone(),
                        (info.name.clone(), info.type_params.len()),
                    );
                }
            }
        }
        for guard in self.modules.iter() {
            if *guard.key() == primitives_path {
                continue; // Already processed above.
            }
            for (_name, entry) in guard.all_symbols() {
                if let ModuleEntry::TypeDef { info, .. } = entry {
                    result.insert(
                        info.name.name.clone(),
                        (info.name.clone(), info.type_params.len()),
                    );
                }
            }
        }
        result
    }

    /// Check whether a constructor name refers to an internal constructor.
    ///
    /// Internal constructors (e.g. `Bind` for the IO type) cannot be
    /// constructed or pattern-matched by user code.
    pub(crate) fn is_internal_constructor(&self, name: &Symbol) -> bool {
        // Strip module prefix for qualified names like "primitives/Bind"
        let bare_name: &str = if let Some(slash_pos) = name.as_ref().find('/') {
            &name.as_ref()[slash_pos + 1..]
        } else {
            name.as_ref()
        };
        self.is_internal_constructor_check(bare_name)
    }

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
            (name.clone(), ModuleEntry::Import { source: fq })
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
            (name.clone(), ModuleEntry::Reexport { source: fq })
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
                    ModuleEntry::Import { source: s1 },
                    ModuleEntry::Import { source: s2 },
                )
                | (
                    ModuleEntry::Reexport { source: s1 },
                    ModuleEntry::Reexport { source: s2 },
                )
                | (
                    ModuleEntry::Import { source: s1 },
                    ModuleEntry::Reexport { source: s2 },
                )
                | (
                    ModuleEntry::Reexport { source: s1 },
                    ModuleEntry::Import { source: s2 },
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
                (ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. },
                 ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. })
            );
            if both_indirect {
                // If either source is from "user" or "primitives" (builtin
                // seeding), prefer the existing entry — it's canonical.
                let is_seeded_source = |entry: &ModuleEntry<C>| -> bool {
                    match entry {
                        ModuleEntry::Import { source }
                        | ModuleEntry::Reexport { source } => {
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
                table.insert(name, ModuleEntry::Ambiguous);
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
    pub fn check_program_self(
        &mut self,
        program: &[cranelisp_types::TopLevel],
    ) -> Result<crate::result::CheckResult, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        #[allow(deprecated)]
        env.check_program(&mut self.state, program)
    }

    /// Check REPL input (test convenience).
    pub fn check_repl_input_self(
        &mut self,
        input: &cranelisp_types::TopLevel,
    ) -> Result<crate::result::CheckResult, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        #[allow(deprecated)]
        env.check_repl_input(&mut self.state, input)
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

    /// Look up type def (test convenience).
    pub fn lookup_type_def(&self, name: &TypeName) -> Option<TypeDefInfo> {
        self.env().lookup_type_def(name)
    }

    /// Look up constructor type (test convenience).
    pub fn lookup_constructor_type(&self, ctor_name: &str) -> Option<TypeName> {
        self.env().lookup_constructor_type(ctor_name)
    }

    /// Check exhaustiveness (test convenience).
    pub fn check_exhaustiveness(
        &self,
        type_name: &TypeName,
        covered: &[Symbol],
        has_wildcard: bool,
        span: Span,
    ) -> Result<(), CranelispError> {
        self.env().check_exhaustiveness(type_name, covered, has_wildcard, span)
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

    /// Has impl (test convenience).
    pub fn has_impl(&self, trait_name: &TraitName, impl_type: &TypeName) -> bool {
        self.env().has_impl(trait_name, impl_type)
    }

    /// Lookup trait decl (test convenience).
    pub fn lookup_trait_decl(&self, trait_name: &TraitName) -> Option<cranelisp_types::TraitDecl> {
        self.env().lookup_trait_decl(trait_name)
    }

    /// Method to trait (test convenience).
    pub fn method_to_trait(&self, method_name: &Symbol) -> Option<TraitName> {
        self.env().method_to_trait(method_name)
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
    pub fn check(
        &mut self,
        program: &[cranelisp_types::TopLevel],
        ctx: &cranelisp_types::CompileContext,
        strategy: cranelisp_types::ModuleStrategy,
    ) -> Result<crate::result::CheckResult, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id);
        env.check(&mut self.state, program, ctx, strategy)
    }

    /// Is internal constructor (test convenience).
    pub fn is_internal_constructor_check(&self, ctor_name: &str) -> bool {
        self.env().is_internal_constructor_check(ctor_name)
    }

    /// Known type names (test convenience).
    pub fn known_type_names(&self) -> crate::resolve::KnownTypes {
        self.env().known_type_names()
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
        decl: &cranelisp_types::TraitDecl,
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

    /// Current `CheckState.method_resolutions` snapshot.
    ///
    /// Populated on the `check_program_self` path (single-shot batch); drained
    /// into annotated ASTs on the `check` path — tests that used
    /// `tc.check(..)` should use `annotated_resolutions()` instead.
    pub fn state_method_resolutions(
        &self,
    ) -> &std::collections::HashMap<Span, cranelisp_types::ResolvedCall> {
        &self.state.method_resolutions
    }

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
            if let cranelisp_types::ModuleEntry::Def { ast: Some(defn), .. } = entry {
                for variant in &defn.variants {
                    collect_resolutions_from_expr(&variant.body, &mut out);
                }
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

    // spec: 11-stdlib §11.1, 08-modules §8.9 — bare module has root module contents only
    #[test]
    fn test_bare_module_has_root_contents_only() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("bare"));

        // --- Root module: special forms ---
        assert!(tf.symbol_table().get("if").is_some(), "if should be available");
        assert!(tf.symbol_table().get("let").is_some(), "let should be available");
        assert!(tf.symbol_table().get("defn").is_some(), "defn should be available");
        assert!(tf.symbol_table().get("fn").is_some(), "fn should be available");
        assert!(tf.symbol_table().get("match").is_some(), "match should be available");
        assert!(tf.symbol_table().get("deftype").is_some(), "deftype should be available");
        assert!(tf.symbol_table().get("deftrait").is_some(), "deftrait should be available");
        assert!(tf.symbol_table().get("impl").is_some(), "impl should be available");
        assert!(tf.symbol_table().get("defmacro").is_some(), "defmacro should be available");

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

    // spec: 08-modules §8.9 — new modules get root contents, nothing else
    #[test]
    fn test_set_current_module_creates_new() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("math"));
        assert_eq!(tf.state.current_module.as_ref(), "math");
        assert!(tf.symbol_table().get("if").is_some());
        assert!(tf.symbol_table().get("Int").is_none());
        assert!(tf.symbol_table().get("add-i64").is_none());
        assert!(tf.symbol_table().get("+").is_none());
    }

    // spec: 08-modules §8.6 — switching modules preserves existing module state
    #[test]
    fn test_switch_back_to_user_preserves_builtins() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("other"));
        tf.set_current_module(ModuleFullPath::from("user"));
        assert!(tf.symbol_table().get("if").is_some());
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
            ModuleEntry::Reexport {
                source: FQSymbol {
                    module: ModuleFullPath::from("lib"),
                    symbol: Symbol::from("helper"),
                },
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
            Some(ModuleEntry::Ambiguous)
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

    // spec: 08-modules §8.9 — new module seeded with builtin imports as Import entries
    #[test]
    fn test_new_module_does_not_have_primitives() {
        let mut tf = TestFixture::new();
        tf.set_current_module(ModuleFullPath::from("mymod"));
        assert!(tf.symbol_table().get("add-i64").is_none(), "add-i64 needs import");
        assert!(tf.symbol_table().get("bind").is_none(), "bind needs import");
        assert!(tf.symbol_table().get("if").is_some(), "if should be available");
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

    #[test]
    fn ensure_module_exists_seeds_special_forms_on_first_call() {
        let tf = TestFixture::new();
        let path = ModuleFullPath::from("fresh-mod-a");
        assert!(
            tf.modules.get(&path).is_none(),
            "precondition: module absent"
        );
        tf.env().ensure_module_exists(&path);
        let guard = tf.modules.get(&path).expect("module must be present");
        assert!(
            guard.get("if").is_some(),
            "special forms must be seeded"
        );
        assert!(
            guard.get("defn").is_some(),
            "special forms must be seeded"
        );
        // And NOT builtin types (those require explicit import).
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
        assert!(
            guard.get("if").is_some(),
            "seeded special forms still present"
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

        // Post-condition: the table is present AND seeded.
        let guard = tf.modules.get(&path).expect("module must be present");
        assert!(
            guard.get("if").is_some(),
            "special forms must be seeded even under concurrency"
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
}
