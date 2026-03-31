//! TypeChecker struct: the central state for type inference.
//!
//! Scope operations, fresh variable generation, and expr_type recording.
//! Other modules extend TypeChecker via `impl TypeChecker` blocks.
//!
//! ## Concurrency preparation (Sprint 40)
//!
//! State is split between:
//! - **`TypeChecker`** — persistent state that survives across `check()` calls
//!   (module tables, type/trait registries, TypeId counter).
//! - **`CheckState`** — per-check transient state created/consumed by each
//!   `check()` invocation (substitution, scope stack, resolutions, warnings).
//!
//! **Phase 1** (Wave 1): extracted `CheckState` from `TypeChecker`.
//!
//! **Phase 2** (Wave 2): added concurrency primitives to persistent state:
//! - `next_id: AtomicU32` — lock-free TypeId allocation via `fetch_add`.
//! - `module_locks: HashMap<ModuleFullPath, Arc<AtomicBool>>` — per-module
//!   compilation exclusion via `try_lock_module()` / `ModuleGuard` RAII guard.
//!
//! **Phase 3** (Wave 3): shared registries behind `RwLock`:
//! - `type_defs: RwLock<TypeDefRegistry>` — read during constructor lookups,
//!   written during type definition registration.
//! - `trait_registry: RwLock<TraitRegistry>` — read during method resolution,
//!   written during trait declaration registration.
//! - `impl_registry: RwLock<ImplRegistry>` — read during impl lookup,
//!   written during impl registration.
//!
//! Methods with `&mut self` use `get_mut().unwrap()` for zero-overhead access
//! (no actual locking — `&mut` guarantees exclusivity). Methods with `&self`
//! acquire `read().unwrap()` or `write().unwrap()` as needed.
//!
//! **`check()` remains `&mut self`** because `CheckState` is stored on
//! `TypeChecker` (field `self.state`) for REPL additive mode, where state
//! persists across evaluations. Converting `check()` to `&self` requires
//! either: (a) making `state` an `Option` that is temporarily taken and
//! restored, or (b) passing `CheckState` as a separate parameter to all
//! ~30 internal helper methods. Both are invasive changes deferred until
//! the parallel pipeline actually calls `check()` concurrently.
//! The `RwLock` wrapping is the primary Phase 3 deliverable — it ensures
//! the registries are safe for concurrent access when that conversion happens.

use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::{Arc, Mutex, RwLock, RwLockReadGuard};

use dashmap::DashMap;

use cranelisp_types::{
    ConstructorInfo, CranelispError, ExportSpec, FQSymbol, ImportNames, ImportSpec,
    MethodResolutions, ModuleEntry, ModuleFullPath, ResolvedCall, ReplSnapshot, Scheme, Span,
    Subst, Symbol, SymbolTable, TraitName, Type, TypeDefInfo, TypeId, TypeName, Warning,
    apply,
};

use crate::adt::TypeDefRegistry;
use crate::scope::ScopeStack;
use crate::scheme;
use crate::traits::{ActiveConstraints, ImplRegistry, TraitRegistry};

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
    pub(crate) fn new(module: ModuleFullPath) -> Self {
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
}

/// RAII guard that releases a module's compilation lock on drop.
///
/// Returned by `TypeChecker::try_lock_module()`. Holding this guard
/// guarantees exclusive compilation rights for the named module.
/// The lock is released automatically when the guard goes out of scope.
#[derive(Debug)]
pub struct ModuleGuard {
    /// The locked flag — shared with the TypeChecker's `module_locks` map.
    flag: Arc<AtomicBool>,
    /// The module path, retained for diagnostics / logging.
    #[allow(dead_code)]
    module: ModuleFullPath,
}

impl Drop for ModuleGuard {
    fn drop(&mut self) {
        self.flag.store(false, Ordering::Release);
    }
}

/// Central persistent state for Hindley-Milner type inference.
///
/// Fields are pub(crate) so that `impl TypeChecker` blocks in other modules
/// can access them directly (borrow-splitting pattern).
///
/// Persistent state survives across `check()` calls. Per-check transient
/// state lives in `CheckState` (stored in `self.state`).
pub struct TypeChecker {
    /// Monotonic counter for fresh type variable IDs.
    ///
    /// `AtomicU32` enables lock-free allocation from concurrent `check()` calls
    /// in Phase 3. In the current serial model, `&mut self` methods can use
    /// `get_mut()` for zero-overhead access.
    pub(crate) next_id: AtomicU32,
    /// Per-module symbol tables, keyed by module full path.
    ///
    /// Behind `DashMap` for concurrent access from multiple worker threads.
    /// Each worker typechecks a different module — DashMap's per-shard locking
    /// allows concurrent reads/writes to different modules without contention.
    pub(crate) modules: DashMap<ModuleFullPath, SymbolTable>,
    /// Registered type definitions (ADTs).
    ///
    /// Behind `RwLock` for Phase 3 parallel `check()`. Methods with `&mut self`
    /// use `get_mut()` (zero overhead); `&self` methods acquire read/write locks.
    pub(crate) type_defs: RwLock<TypeDefRegistry>,
    /// Registered trait declarations (Ring 2).
    ///
    /// Behind `RwLock` for Phase 3 parallel `check()`. Same access pattern as `type_defs`.
    pub(crate) trait_registry: RwLock<TraitRegistry>,
    /// Registered trait implementations (Ring 2).
    ///
    /// Behind `RwLock` for Phase 3 parallel `check()`. Same access pattern as `type_defs`.
    pub(crate) impl_registry: RwLock<ImplRegistry>,
    /// Per-module compilation locks. Each entry is `true` when a `compile_unit`
    /// is actively building that module, `false` otherwise. `try_lock_module()`
    /// uses compare-and-swap to claim exclusive access; the RAII `ModuleGuard`
    /// releases the flag on drop.
    ///
    /// Entries are `Arc<AtomicBool>` so the guard can outlive the borrow of the
    /// HashMap (the guard holds an Arc clone, not a reference into the map).
    /// Wrapped in `Mutex` so `try_lock_module` works with `&self`.
    module_locks: Mutex<HashMap<ModuleFullPath, Arc<AtomicBool>>>,
    /// Per-check transient state. Stored here for serial REPL reuse;
    /// parallel `check()` will use stack-local `CheckState` once `check()`
    /// is converted to `&self` (see module-level doc for blockers).
    pub(crate) state: CheckState,
}

impl TypeChecker {
    /// Create a new TypeChecker with Ring 0 builtins registered.
    ///
    /// Seeds the default "user" module as the active module.
    pub fn new() -> Self {
        let current_module = ModuleFullPath::from("user");
        let modules = DashMap::new();
        modules.insert(
            current_module.clone(),
            SymbolTable::new(current_module.clone()),
        );
        let mut tc = TypeChecker {
            next_id: AtomicU32::new(0),
            modules,
            type_defs: RwLock::new(TypeDefRegistry::new()),
            trait_registry: RwLock::new(TraitRegistry::default()),
            impl_registry: RwLock::new(ImplRegistry::default()),
            module_locks: Mutex::new(HashMap::new()),
            state: CheckState::new(current_module),
        };
        tc.register_builtins();
        tc
    }

    // --- Module-scoped symbol table accessors ---

    /// Get a read guard for the current module's symbol table.
    ///
    /// Returns a DashMap `Ref` guard that derefs to `SymbolTable`.
    /// The guard holds a per-shard read lock — drop it before acquiring
    /// another guard to avoid deadlocks (see design/typecheck/dashmap-migration.md §4.10).
    pub(crate) fn current_symbol_table_with_state(
        &self,
        state: &CheckState,
    ) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable> {
        self.modules
            .get(&state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in modules map"))
    }

    /// Get a write guard for the current module's symbol table.
    ///
    /// Returns a DashMap `RefMut` guard that derefs mutably to `SymbolTable`.
    /// Drop before acquiring another guard.
    pub(crate) fn current_symbol_table_mut_with_state(
        &self,
        state: &CheckState,
    ) -> dashmap::mapref::one::RefMut<'_, ModuleFullPath, SymbolTable> {
        self.modules
            .get_mut(&state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in modules map"))
    }

    /// Get a read guard for the current module's symbol table (using self.state).
    pub(crate) fn current_symbol_table(
        &self,
    ) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable> {
        self.modules
            .get(&self.state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in modules map"))
    }

    /// Get a write guard for the current module's symbol table (using self.state).
    pub(crate) fn current_symbol_table_mut(
        &self,
    ) -> dashmap::mapref::one::RefMut<'_, ModuleFullPath, SymbolTable> {
        self.modules
            .get_mut(&self.state.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in modules map"))
    }

    /// Switch the active module. Creates the module's symbol table if it
    /// doesn't already exist.
    pub fn set_current_module(&mut self, path: ModuleFullPath) {
        if !self.modules.contains_key(&path) {
            let mut table = SymbolTable::new(path.clone());

            // Seed new modules with imports from `primitives` module so that
            // named primitives (add-i64, str-concat, quote-sexp, etc.) and
            // constructors (Pure, Effect) are accessible everywhere.
            // Note: the `user` module is NOT seeded — it requires explicit
            // imports per spec §8.9.1.
            //
            // Clone-and-drop discipline: collect entries, drop guard, then insert.
            let primitives_path = ModuleFullPath::from("primitives");
            let prim_entries: Vec<Symbol> = self.modules.get(&primitives_path)
                .map(|guard| guard.all_symbols().map(|(n, _)| n.clone()).collect())
                .unwrap_or_default();
            for name in prim_entries {
                table.insert(
                    name.clone(),
                    ModuleEntry::Import {
                        source: FQSymbol {
                            module: primitives_path.clone(),
                            symbol: name,
                        },
                    },
                );
            }

            // Seed from `user` module: special forms, trait decls,
            // constrained defs, constructors, and type defs.
            //
            // Clone-and-drop discipline: collect seedable names, drop guard, then insert.
            let user_path = ModuleFullPath::from("user");
            let user_entries: Vec<Symbol> = self.modules.get(&user_path)
                .map(|guard| {
                    guard.all_symbols()
                        .filter_map(|(name, entry)| {
                            let is_seedable = matches!(entry, ModuleEntry::Def { kind, .. }
                                if matches!(kind.as_ref(),
                                    cranelisp_types::DefKind::SpecialForm { .. }
                                )
                            ) || matches!(entry, ModuleEntry::Def { scheme, .. }
                                if !scheme.constraints.is_empty()
                            ) || matches!(entry, ModuleEntry::Constructor { .. })
                              || matches!(entry, ModuleEntry::TypeDef { .. })
                              || matches!(entry, ModuleEntry::TraitDecl { .. });
                            if is_seedable { Some(name.clone()) } else { None }
                        })
                        .collect()
                })
                .unwrap_or_default();
            for name in user_entries {
                table.insert(
                    name.clone(),
                    ModuleEntry::Import {
                        source: FQSymbol {
                            module: user_path.clone(),
                            symbol: name,
                        },
                    },
                );
            }

            self.modules.insert(path.clone(), table);
        }
        self.state.current_module = path;
    }

    /// Get the current module path.
    pub fn current_module_path(&self) -> &ModuleFullPath {
        &self.state.current_module
    }

    /// Ensure a module's symbol table exists, creating it if needed.
    ///
    /// Uses DashMap interior mutation — safe with `&self`. Seeds new modules
    /// with imports from `primitives` and seedable entries from `user`.
    /// Does NOT set `self.state.current_module` — callers set the module
    /// on their own `CheckState`.
    pub fn ensure_module_exists(&self, path: &ModuleFullPath) {
        if self.modules.contains_key(path) {
            return;
        }
        let mut table = SymbolTable::new(path.clone());

        // Seed from primitives (clone-and-drop discipline)
        let primitives_path = ModuleFullPath::from("primitives");
        let prim_entries: Vec<Symbol> = self.modules.get(&primitives_path)
            .map(|guard| guard.all_symbols().map(|(n, _)| n.clone()).collect())
            .unwrap_or_default();
        for name in prim_entries {
            table.insert(
                name.clone(),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: primitives_path.clone(),
                        symbol: name,
                    },
                },
            );
        }

        // Seed from user (clone-and-drop discipline)
        let user_path = ModuleFullPath::from("user");
        let user_entries: Vec<Symbol> = self.modules.get(&user_path)
            .map(|guard| {
                guard.all_symbols()
                    .filter_map(|(name, entry)| {
                        let is_seedable = matches!(entry, ModuleEntry::Def { kind, .. }
                            if matches!(kind.as_ref(),
                                cranelisp_types::DefKind::SpecialForm { .. }
                            )
                        ) || matches!(entry, ModuleEntry::Def { scheme, .. }
                            if !scheme.constraints.is_empty()
                        ) || matches!(entry, ModuleEntry::Constructor { .. })
                          || matches!(entry, ModuleEntry::TypeDef { .. })
                          || matches!(entry, ModuleEntry::TraitDecl { .. });
                        if is_seedable { Some(name.clone()) } else { None }
                    })
                    .collect()
            })
            .unwrap_or_default();
        for name in user_entries {
            table.insert(
                name.clone(),
                ModuleEntry::Import {
                    source: FQSymbol {
                        module: user_path.clone(),
                        symbol: name,
                    },
                },
            );
        }

        self.modules.insert(path.clone(), table);
    }

    /// Check whether a module has been registered.
    pub fn has_module(&self, path: &ModuleFullPath) -> bool {
        self.modules.contains_key(path)
    }

    // --- Module compilation locks ---

    /// Attempt to acquire exclusive compilation rights for a module.
    ///
    /// Returns a RAII `ModuleGuard` that releases the lock on drop.
    /// If the module is already being compiled (lock held), returns an
    /// error immediately — non-blocking, deadlock-free.
    ///
    /// Used by the pipeline to prevent concurrent compilation of the same
    /// module. Callers acquire the lock before stages 1-5 and let the guard
    /// drop on return.
    pub fn try_lock_module(
        &self,
        module: &ModuleFullPath,
    ) -> Result<ModuleGuard, CranelispError> {
        let flag = {
            let mut locks = self.module_locks.lock().unwrap();
            Arc::clone(locks
                .entry(module.clone())
                .or_insert_with(|| Arc::new(AtomicBool::new(false))))
        };

        // Attempt to flip false → true atomically.
        let was_locked = flag.compare_exchange(
            false,
            true,
            Ordering::Acquire,
            Ordering::Relaxed,
        );

        match was_locked {
            Ok(_) => Ok(ModuleGuard {
                flag,
                module: module.clone(),
            }),
            Err(_) => Err(CranelispError::TypeError {
                message: format!(
                    "module '{}' is already being compiled",
                    module
                ),
                span: Span::SYNTHETIC,
            }),
        }
    }

    /// Check whether a module is currently locked for compilation.
    ///
    /// Returns `true` if a `ModuleGuard` is held for this module.
    /// Useful for diagnostics and testing.
    pub fn is_module_locked(&self, module: &ModuleFullPath) -> bool {
        self.module_locks.lock().unwrap()
            .get(module)
            .map(|flag| flag.load(Ordering::Acquire))
            .unwrap_or(false)
    }

    /// Convenience accessor for the current module's symbol table (public).
    /// Used by tests and external code that needs to inspect symbols.
    pub fn symbol_table(&self) -> dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable> {
        self.current_symbol_table()
    }

    /// Mutable accessor for the current module's symbol table (public).
    /// Used by the pipeline orchestrator to register macro entries.
    pub fn symbol_table_mut(&self) -> dashmap::mapref::one::RefMut<'_, ModuleFullPath, SymbolTable> {
        self.current_symbol_table_mut()
    }

    /// Public accessor for the type definition registry.
    /// Used by prelude loading to copy type defs into the REPL session.
    ///
    /// Returns a `RwLockReadGuard` that derefs to `TypeDefRegistry`.
    /// Callers use `.iter()`, `.get()` etc. transparently via `Deref`.
    pub fn type_def_registry(&self) -> RwLockReadGuard<'_, TypeDefRegistry> {
        self.type_defs.read().unwrap()
    }

    /// Build type_defs and constructor_to_type maps from the registry.
    ///
    /// Used by the worker to build partial `CheckResult` for inline
    /// macro compilation without going through `finalize_check_result`.
    pub fn snapshot_type_defs(&self) -> (HashMap<TypeName, TypeDefInfo>, HashMap<Symbol, TypeName>) {
        let registry = self.type_defs.read().unwrap();
        let type_defs: HashMap<TypeName, TypeDefInfo> = registry.iter()
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
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
    pub fn module_table(&self, path: &ModuleFullPath) -> Option<dashmap::mapref::one::Ref<'_, ModuleFullPath, SymbolTable>> {
        self.modules.get(path)
    }

    /// Look up a specific module's symbol table by path, returning an owned clone.
    /// Used by callers that need to own the symbol table (e.g., serialization).
    pub fn module_table_cloned(&self, path: &ModuleFullPath) -> Option<SymbolTable> {
        self.modules.get(path).map(|guard| guard.clone())
    }

    /// Look up the defining module for a symbol. Checks the `primitives` module
    /// first (for core traits and builtins), then falls back to the current module.
    pub fn defining_module_for(&self, name: &str) -> ModuleFullPath {
        let primitives_path = ModuleFullPath::from("primitives");
        let found = self.modules.get(&primitives_path)
            .map(|guard| guard.get(name).is_some())
            .unwrap_or(false);
        if found {
            return primitives_path;
        }
        self.state.current_module.clone()
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
        entry: &ModuleEntry,
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
    pub(crate) fn resolve_entry_in_current_module(&self, state: &CheckState, name: &str) -> Option<ModuleEntry> {
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
        entry: &ModuleEntry,
        depth: usize,
    ) -> Option<ModuleEntry> {
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
                span: Span::SYNTHETIC,
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
                    span,
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
    pub(crate) fn clear_transient_state(&mut self) {
        self.state.expr_types.clear();
        self.state.method_resolutions.clear();
        self.state.active_constraints = ActiveConstraints::default();
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
        &mut self,
        specs: &[ImportSpec],
    ) -> Result<(), CranelispError> {
        let mut state = std::mem::replace(&mut self.state, CheckState::new(ModuleFullPath::from("")));
        let result = self.register_imports_with_state(&mut state, specs);
        self.state = state;
        result
    }

    pub(crate) fn register_imports_with_state(
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
            let imports_to_add: Vec<(Symbol, ModuleEntry)> = {
                let source_guard = match self.modules.get(&spec.module_path) {
                    Some(g) => g,
                    None => {
                        return Err(CranelispError::TypeError {
                            message: format!(
                                "unknown module '{}' in import",
                                spec.module_path
                            ),
                            span: spec.span,
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
                &mut self.current_symbol_table_mut_with_state(state),
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
        &mut self,
        specs: &[ExportSpec],
    ) -> Result<(), CranelispError> {
        let mut state = std::mem::replace(&mut self.state, CheckState::new(ModuleFullPath::from("")));
        let result = self.register_exports_with_state(&mut state, specs);
        self.state = state;
        result
    }

    pub(crate) fn register_exports_with_state(
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
                        span: spec.span,
                    });
                }
            };

            // Clone-and-drop discipline: collect reexports from source guard,
            // drop it, then acquire write guard on current module.
            let reexports: Vec<(Symbol, ModuleEntry)> = {
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
                &mut self.current_symbol_table_mut_with_state(state),
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
        source_table: &SymbolTable,
        names: &[Symbol],
        module_path: &ModuleFullPath,
        span: Span,
    ) -> Result<Vec<(Symbol, ModuleEntry)>, CranelispError> {
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
                            span,
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
                        span,
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
        source_table: &SymbolTable,
        parent: &Symbol,
        module_path: &ModuleFullPath,
    ) -> Vec<(Symbol, ModuleEntry)> {
        let trait_name = cranelisp_types::TraitName::from(parent.as_ref());
        let trait_reg = self.trait_registry.read().unwrap();
        let mut result = Vec::new();
        for (name, entry) in source_table.public_symbols() {
            let is_member = match entry {
                ModuleEntry::Constructor { type_name, .. } => {
                    type_name.as_ref() == parent.as_ref()
                }
                ModuleEntry::Def { kind, .. } => {
                    matches!(
                        kind.as_ref(),
                        cranelisp_types::DefKind::Primitive { .. }
                            | cranelisp_types::DefKind::UserFn { .. }
                    ) && trait_reg
                        .method_belongs_to_trait(name, &trait_name)
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
        source_table: &SymbolTable,
        names: &[Symbol],
        module_path: &ModuleFullPath,
        span: Span,
    ) -> Result<Vec<(Symbol, ModuleEntry)>, CranelispError> {
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
                            span,
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
                        span,
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
        source_table: &SymbolTable,
        parent: &Symbol,
        module_path: &ModuleFullPath,
    ) -> Vec<(Symbol, ModuleEntry)> {
        let trait_name = cranelisp_types::TraitName::from(parent.as_ref());
        let trait_reg = self.trait_registry.read().unwrap();
        let mut result = Vec::new();
        for (name, entry) in source_table.public_symbols() {
            let is_member = match entry {
                ModuleEntry::Constructor { type_name, .. } => {
                    type_name.as_ref() == parent.as_ref()
                }
                ModuleEntry::Def { kind, .. } => {
                    matches!(
                        kind.as_ref(),
                        cranelisp_types::DefKind::Primitive { .. }
                            | cranelisp_types::DefKind::UserFn { .. }
                    ) && trait_reg
                        .method_belongs_to_trait(name, &trait_name)
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
        self.type_defs.read().unwrap()
            .get(type_name)
            .map(|info| info.constructors.clone())
    }

    /// Return all trait names that have an impl registered for `type_name`.
    /// Results are sorted alphabetically.
    pub fn get_impls_for_type(&self, type_name: &TypeName) -> Vec<TraitName> {
        let impl_reg = self.impl_registry.read().unwrap();
        let mut traits: Vec<TraitName> = impl_reg
            .impls
            .iter()
            .filter(|(_, type_map)| type_map.contains_key(type_name))
            .map(|(trait_name, _)| trait_name.clone())
            .collect();
        traits.sort();
        traits
    }

    /// Return the method names declared in a trait.
    pub fn get_trait_methods(&self, trait_name: &TraitName) -> Option<Vec<Symbol>> {
        self.trait_registry.read().unwrap()
            .decls
            .get(trait_name)
            .map(|decl| decl.methods.iter().map(|m| m.name.clone()).collect())
    }

    /// Return all type names that implement a given trait.
    /// Results are sorted alphabetically.
    pub fn get_implementing_types(&self, trait_name: &TraitName) -> Vec<TypeName> {
        let impl_reg = self.impl_registry.read().unwrap();
        let mut types: Vec<TypeName> = impl_reg
            .impls
            .get(trait_name)
            .map(|type_map| type_map.keys().cloned().collect())
            .unwrap_or_default();
        types.sort();
        types
    }

    /// Resolve a module name: try as child of current module first, then as
    /// root module. Returns `None` if not found.
    pub fn resolve_module_by_name(&self, name: &str) -> Option<ModuleFullPath> {
        // Note: reads self.state.current_module which is only valid in
        // single-threaded (REPL) context. Worker code passes module path explicitly.
        let child_path =
            ModuleFullPath::from(format!("{}.{}", self.state.current_module, name));
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

    /// Unregister a trait declaration from the trait registry.
    ///
    /// Removes the trait from the decls map and all its method-to-trait
    /// reverse lookups. Used during module hot-reload to clear old state
    /// before recompilation (repl/spec.md §14.2).
    pub fn unregister_trait(&mut self, trait_name: &TraitName) {
        let trait_reg = self.trait_registry.get_mut().unwrap();
        if let Some(decl) = trait_reg.decls.remove(trait_name) {
            for method in &decl.methods {
                trait_reg.method_to_trait.remove(&method.name);
            }
            // Also remove impls for this trait to allow re-registration.
            self.impl_registry.get_mut().unwrap().impls.remove(trait_name);
        }
    }

    /// Remove a module's symbol table and unregister its types and traits.
    ///
    /// Removes the CompiledModule from the modules map and cleans up:
    /// - Trait declarations (from trait_registry)
    /// - Type definitions (from type_defs)
    /// - Constructor-to-type mappings
    ///
    /// Returns the removed symbol table, or None if the module was not found.
    /// Used during module hot-reload (repl/spec.md §14.2).
    pub fn remove_module(&mut self, module_path: &ModuleFullPath) -> Option<SymbolTable> {
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

        // Unregister type definitions defined by this module.
        let td = self.type_defs.get_mut().unwrap();
        for (_, entry) in table.all_symbols() {
            if let ModuleEntry::TypeDef { info, .. } = entry {
                td.type_defs.remove(&info.name);
                for ctor in &info.constructors {
                    td.constructor_to_type.remove(&ctor.name);
                }
            }
        }

        Some(table)
    }

    /// Insert a fresh (empty) module symbol table.
    ///
    /// Used after `remove_module` to re-establish the module path before
    /// recompilation populates it with fresh definitions.
    pub fn insert_module(&mut self, table: SymbolTable) {
        self.modules.insert(table.path.clone(), table);
    }

    // --- Cache restoration ---

    /// Restore a module's symbol table from cached metadata.
    ///
    /// Installs the given symbol table into the modules map and
    /// reconstructs type_defs and constructor_to_type entries from
    /// the table's TypeDef and Constructor entries. This enables
    /// downstream modules to import from and typecheck against
    /// the cached module without recompiling it.
    ///
    /// Used by the pipeline's cache-hit path (src/pipeline.rs).
    pub fn restore_cached_module(&mut self, table: SymbolTable) {
        let path = table.path.clone();

        // Reconstruct type_defs, constructor_to_type, and trait registries
        // from symbol table entries.
        let td = self.type_defs.get_mut().unwrap();
        let tr = self.trait_registry.get_mut().unwrap();
        for (_name, entry) in table.all_symbols() {
            match entry {
                ModuleEntry::TypeDef { info, .. } => {
                    // Register each constructor in constructor_to_type.
                    for ctor in &info.constructors {
                        td.constructor_to_type.insert(
                            ctor.name.clone(),
                            info.name.clone(),
                        );
                    }
                    td.type_defs.insert(
                        info.name.clone(),
                        info.clone(),
                    );
                }
                ModuleEntry::Constructor { type_name, .. } => {
                    // Ensure constructor_to_type has this entry too
                    // (may duplicate the TypeDef loop, but HashMap insert is idempotent).
                    td.constructor_to_type.insert(
                        _name.clone(),
                        TypeName::from(type_name.as_ref()),
                    );
                }
                ModuleEntry::TraitDecl { decl, .. }
                    // Reconstruct trait_registry from cached TraitDecl entries.
                    // This populates decls and method_to_trait so trait method
                    // resolution works after loading from cache.
                    if !tr.decls.contains_key(&decl.name) => {
                        for method in &decl.methods {
                            tr.method_to_trait
                                .insert(method.name.clone(), decl.name.clone());
                        }
                        tr.decls
                            .insert(decl.name.clone(), decl.clone());
                }
                _ => {}
            }
        }

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
    fn advance_next_id_past_table(&mut self, table: &SymbolTable) {
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

        if let Some(id) = max_id
            && *self.next_id.get_mut() <= id
        {
            *self.next_id.get_mut() = id + 1;
        }
    }

    /// Restore trait implementation registrations from cached mangled method names.
    ///
    /// During fresh compilation, `register_trait_impl` populates `impl_registry`
    /// with (trait_name, impl_type) pairs. When loading from cache, the impl
    /// information is reconstructed from the mangled method names in the codegen
    /// state (e.g., `"Num.+$Int"` → trait=Num, impl_type=Int).
    ///
    /// Must be called after `restore_cached_module` so that `trait_registry`
    /// is already populated.
    pub fn restore_cached_impls(&mut self, mangled_names: &[String]) {
        use crate::traits::RegisteredImpl;

        let impl_reg = self.impl_registry.get_mut().unwrap();
        for name in mangled_names {
            // Parse "Trait.method$Type" pattern.
            let Some(dot_pos) = name.find('.') else { continue };
            let Some(dollar_pos) = name.find('$') else { continue };
            if dollar_pos <= dot_pos { continue; }

            let trait_str = &name[..dot_pos];
            let method_str = &name[dot_pos + 1..dollar_pos];
            let impl_type_str = &name[dollar_pos + 1..];

            let trait_name = TraitName::from(trait_str);
            let impl_type = TypeName::from(impl_type_str);
            let method_name = Symbol::from(method_str);

            // Skip if this impl is already registered.
            if impl_reg.has_impl(&trait_name, &impl_type) {
                continue;
            }

            let mut method_primitives = HashMap::new();
            method_primitives.insert(method_name.clone(), method_name);

            impl_reg.impls
                .entry(trait_name.clone())
                .or_default()
                .insert(
                    impl_type.clone(),
                    RegisteredImpl {
                        trait_name,
                        impl_type,
                        method_primitives,
                    },
                );
        }
    }

    // --- REPL snapshot/restore ---

    /// Take a snapshot of the current state for REPL error recovery.
    pub fn snapshot(&self) -> ReplSnapshot {
        let symbol_keys = self.current_symbol_table().symbols.keys().cloned().collect();
        ReplSnapshot {
            next_type_id: self.next_id.load(Ordering::Relaxed),
            symbol_keys,
            subst_len: self.state.subst.len(),
            scope_depth: self.state.env.depth(),
        }
    }

    /// Restore state from a snapshot (on REPL error).
    pub fn restore(&mut self, snapshot: ReplSnapshot) {
        *self.next_id.get_mut() = snapshot.next_type_id;
        self.state.subst.retain(|id, _| *id < snapshot.next_type_id);
        self.state.expr_types.clear();
        self.state.method_resolutions.clear();
        self.state.warnings.clear();
        self.state.pending_auto_curry.clear();
        // Remove symbol table entries added after the snapshot was taken.
        self.current_symbol_table_mut()
            .symbols
            .retain(|key, _| snapshot.symbol_keys.contains(key));
        // Restore scope stack depth (pop frames left by failed check_defn_body).
        self.state.env.truncate_to(snapshot.scope_depth);
    }

    // --- Known types lookup (for resolve_type_expr) ---

    /// Build a map of known type names for type expression resolution.
    pub(crate) fn known_type_names(&self) -> crate::resolve::KnownTypes {
        self.type_defs.read().unwrap().known_types()
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
        self.type_defs.read().unwrap().is_internal_constructor(bare_name)
    }

    // --- Test convenience methods (take-and-restore pattern) ---

    /// Lookup using self.state (test convenience).
    #[cfg(test)]
    pub(crate) fn lookup_self(&self, name: &str) -> Option<Scheme> {
        self.lookup(&self.state, name)
    }

    /// Resolve qualified using self.state (test convenience).
    #[cfg(test)]
    pub(crate) fn resolve_qualified_self(
        &self,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Result<Option<Scheme>, CranelispError> {
        self.resolve_qualified(&self.state, module_path, name)
    }

    /// Bind local using self.state (test convenience).
    #[cfg(test)]
    pub(crate) fn bind_local_self(&mut self, name: Symbol, scheme: Scheme) {
        self.state.env.bind(name, scheme);
    }

    /// Apply subst using self.state (test convenience).
    #[cfg(test)]
    pub(crate) fn apply_subst_self(&self, ty: &Type) -> Type {
        apply(&self.state.subst, ty)
    }


    /// Register trait decl using self.state (test/external convenience).
    pub(crate) fn register_trait_decl_self(
        &mut self,
        decl: &cranelisp_types::TraitDecl,
    ) -> Result<(), CranelispError> {
        let mut state = std::mem::replace(&mut self.state, CheckState::new(ModuleFullPath::from("")));
        let result = self.register_trait_decl(&mut state, decl);
        self.state = state;
        result
    }

    /// Register trait impl using self.state (test convenience).
    pub(crate) fn register_trait_impl_self(
        &mut self,
        impl_: &cranelisp_types::TraitImpl,
    ) -> Result<Vec<cranelisp_types::Defn>, CranelispError> {
        let mut state = std::mem::replace(&mut self.state, CheckState::new(ModuleFullPath::from("")));
        let result = self.register_trait_impl(&mut state, impl_);
        self.state = state;
        result
    }

    /// Try resolve trait method using self.state (test convenience).
    pub(crate) fn try_resolve_trait_method_self(
        &mut self,
        name: &Symbol,
        arg_types: &[Type],
        span: Span,
    ) -> Result<Option<cranelisp_types::ResolvedCall>, CranelispError> {
        let mut state = std::mem::replace(&mut self.state, CheckState::new(ModuleFullPath::from("")));
        let result = self.try_resolve_trait_method(&mut state, name, arg_types, span);
        self.state = state;
        result
    }

    /// Check program using self.state (test convenience, deprecated).
    pub(crate) fn check_program_self(
        &mut self,
        program: &[cranelisp_types::TopLevel],
    ) -> Result<cranelisp_types::CheckResult, CranelispError> {
        #[allow(deprecated)]
        self.check_program(program)
    }

    /// Check REPL input using self.state (test convenience, deprecated).
    pub(crate) fn check_repl_input_self(
        &mut self,
        input: &cranelisp_types::TopLevel,
    ) -> Result<cranelisp_types::CheckResult, CranelispError> {
        #[allow(deprecated)]
        self.check_repl_input(input)
    }


    /// Register type def using self.state (test/external convenience).
    pub(crate) fn register_type_def_self(
        &mut self,
        name: &cranelisp_types::TypeName,
        docstring: &Option<String>,
        type_params: &[Symbol],
        constructors: &[cranelisp_types::ConstructorDef],
        visibility: cranelisp_types::Visibility,
        span: Span,
    ) -> Result<(), CranelispError> {
        let mut state = std::mem::replace(&mut self.state, CheckState::new(ModuleFullPath::from("")));
        let result = self.register_type_def(&mut state, name, docstring, type_params, constructors, visibility, span);
        self.state = state;
        result
    }

    /// Resolve primitive JIT name using self.state (test convenience).
    pub(crate) fn resolve_primitive_jit_name_self(&self, name: &str) -> Option<Symbol> {
        self.resolve_primitive_jit_name(&self.state, name)
    }

}

// ---------------------------------------------------------------------------
// Import helpers (free functions to avoid borrow conflicts)
// ---------------------------------------------------------------------------

/// Collect all public symbols from a source module as glob imports.
fn collect_glob_imports(
    source_table: &SymbolTable,
    module_path: &ModuleFullPath,
) -> Vec<(Symbol, ModuleEntry)> {
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
fn collect_glob_reexports(
    source_table: &SymbolTable,
    module_path: &ModuleFullPath,
) -> Vec<(Symbol, ModuleEntry)> {
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
fn insert_imports_detecting_ambiguity(
    table: &mut SymbolTable,
    imports: Vec<(Symbol, ModuleEntry)>,
) {
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
                let is_seeded_source = |entry: &ModuleEntry| -> bool {
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

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        DefKind, ImportNames, ImportSpec, ModuleEntry, ModuleFullPath,
        Span, Symbol, Visibility,
    };

    // --- Module-scoped type environments ---

    // spec: 08-modules §8.13 — default REPL module is "user"
    #[test]
    fn test_default_module_is_user() {
        let tc = TypeChecker::new();
        assert_eq!(tc.current_module_path().as_ref(), "user");
    }

    // spec: 08-modules §8.9.1 — named primitives NOT in user module; special forms ARE
    #[test]
    fn test_builtins_in_user_module() {
        let tc = TypeChecker::new();
        // Per spec §8.9.1, named primitives are NOT bare in user module
        assert!(tc.symbol_table().get("add-i64").is_none());
        assert!(tc.symbol_table().get("quote-sexp").is_none());
        // Special forms ARE in user module
        assert!(tc.symbol_table().get("if").is_some());
        // Operators (+, =, etc.) are NOT registered at startup — they come from prelude
        assert!(tc.symbol_table().get("+").is_none());
        // Named primitives ARE in the primitives synthetic module
        let prims_path = ModuleFullPath::from("primitives");
        let prims_table = tc.modules.get(&prims_path).unwrap();
        assert!(prims_table.get("add-i64").is_some());
        assert!(prims_table.get("quote-sexp").is_some());
    }

    // spec: 08-modules §8.9 — new modules are seeded with builtin imports
    #[test]
    fn test_set_current_module_creates_new() {
        let mut tc = TypeChecker::new();
        tc.set_current_module(ModuleFullPath::from("math"));
        assert_eq!(tc.current_module_path().as_ref(), "math");
        // New modules are seeded with primitive imports from `primitives`
        assert!(tc.symbol_table().get("add-i64").is_some());
        // Special forms from `user`
        assert!(tc.symbol_table().get("if").is_some());
        // Operators come from prelude, NOT compiler builtins
        assert!(tc.symbol_table().get("+").is_none());
        // User-defined names are NOT copied
        assert!(tc.symbol_table().get("user-only").is_none());
    }

    // spec: 08-modules §8.6 — switching modules preserves existing module state
    #[test]
    fn test_switch_back_to_user_preserves_builtins() {
        let mut tc = TypeChecker::new();
        tc.set_current_module(ModuleFullPath::from("other"));
        tc.set_current_module(ModuleFullPath::from("user"));
        // Special forms preserved in user
        assert!(tc.symbol_table().get("if").is_some());
        // Named primitives NOT in user (spec §8.9.1)
        assert!(tc.symbol_table().get("add-i64").is_none());
    }

    // spec: 08-modules §8.6 — modules have independent symbol tables
    #[test]
    fn test_modules_are_independent() {
        let mut tc = TypeChecker::new();
        // Define something in user
        tc.current_symbol_table_mut().insert(
            Symbol::from("user-only"),
            ModuleEntry::Def {
                scheme: crate::scheme::mono(Type::Int),
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: Vec::new(),
            },
        );

        // Switch to another module — shouldn't see user-only
        tc.set_current_module(ModuleFullPath::from("other"));
        assert!(tc.symbol_table().get("user-only").is_none());

        // Switch back — should see it again
        tc.set_current_module(ModuleFullPath::from("user"));
        assert!(tc.symbol_table().get("user-only").is_some());
    }

    // --- Cross-module name resolution ---

    fn seed_module(tc: &mut TypeChecker, path: &str, entries: Vec<(&str, Visibility)>) {
        tc.set_current_module(ModuleFullPath::from(path));
        for (name, vis) in entries {
            tc.current_symbol_table_mut().insert(
                Symbol::from(name),
                ModuleEntry::Def {
                    scheme: crate::scheme::mono(Type::Int),
                    visibility: vis,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                    callees: Vec::new(),
                },
            );
        }
    }

    // spec: 08-modules §8.5 — qualified name resolves public symbol in target module
    #[test]
    fn test_resolve_qualified_public() {
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "math", vec![("add", Visibility::Public)]);
        tc.set_current_module(ModuleFullPath::from("user"));

        let result = tc
            .resolve_qualified_self(&ModuleFullPath::from("math"), "add")
            .unwrap();
        assert!(result.is_some());
    }

    // spec: 08-modules §8.7 — private symbol access denied from outside module
    #[test]
    fn test_resolve_qualified_private_denied() {
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "math", vec![("internal", Visibility::Private)]);
        tc.set_current_module(ModuleFullPath::from("user"));

        let result = tc.resolve_qualified_self(
            &ModuleFullPath::from("math"),
            "internal",
        );
        assert!(result.is_err());
        assert!(result.unwrap_err().message().contains("private"));
    }

    // spec: 08-modules §8.7 — private symbol accessible from child module in subtree
    #[test]
    fn test_resolve_qualified_private_allowed_in_subtree() {
        let mut tc = TypeChecker::new();
        seed_module(
            &mut tc,
            "math",
            vec![("internal", Visibility::Private)],
        );
        // A child module of math should be able to access private names
        tc.set_current_module(ModuleFullPath::from("math.test"));

        let result = tc
            .resolve_qualified_self(&ModuleFullPath::from("math"), "internal")
            .unwrap();
        assert!(result.is_some());
    }

    // spec: 08-modules §8.6 — qualified lookup returns None for nonexistent symbol
    #[test]
    fn test_resolve_qualified_not_found() {
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "math", vec![("add", Visibility::Public)]);
        tc.set_current_module(ModuleFullPath::from("user"));

        let result = tc
            .resolve_qualified_self(&ModuleFullPath::from("math"), "nonexistent")
            .unwrap();
        assert!(result.is_none());
    }

    // spec: 08-modules §8.6 — qualified lookup on unknown module returns None
    #[test]
    fn test_resolve_qualified_unknown_module() {
        let tc = TypeChecker::new();
        let result = tc
            .resolve_qualified_self(&ModuleFullPath::from("unknown"), "foo")
            .unwrap();
        assert!(result.is_none());
    }

    // --- Import processing ---

    // spec: 08-modules §8.3 — glob import brings all public names into scope
    #[test]
    fn test_import_glob() {
        let mut tc = TypeChecker::new();
        seed_module(
            &mut tc,
            "math",
            vec![
                ("add", Visibility::Public),
                ("sub", Visibility::Public),
                ("internal", Visibility::Private),
            ],
        );
        tc.set_current_module(ModuleFullPath::from("main"));

        tc.register_imports(&[ImportSpec {
            module_path: ModuleFullPath::from("math"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }])
        .unwrap();

        // Public names imported
        assert!(tc.symbol_table().get("add").is_some());
        assert!(tc.symbol_table().get("sub").is_some());
        // Private names NOT imported
        assert!(tc.symbol_table().get("internal").is_none());
    }

    // spec: 08-modules §8.3 — specific import brings only named symbols into scope
    #[test]
    fn test_import_specific() {
        let mut tc = TypeChecker::new();
        seed_module(
            &mut tc,
            "math",
            vec![
                ("add", Visibility::Public),
                ("sub", Visibility::Public),
            ],
        );
        tc.set_current_module(ModuleFullPath::from("main"));

        tc.register_imports(&[ImportSpec {
            module_path: ModuleFullPath::from("math"),
            alias: None,
            names: ImportNames::Specific(vec![Symbol::from("add")]),
            span: Span::SYNTHETIC,
        }])
        .unwrap();

        assert!(tc.symbol_table().get("add").is_some());
        assert!(tc.symbol_table().get("sub").is_none());
    }

    // spec: 08-modules §8.7 — importing private symbol by name produces error
    #[test]
    fn test_import_specific_private_error() {
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "math", vec![("secret", Visibility::Private)]);
        tc.set_current_module(ModuleFullPath::from("main"));

        let result = tc.register_imports(&[ImportSpec {
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
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "math", vec![("add", Visibility::Public)]);
        tc.set_current_module(ModuleFullPath::from("main"));

        let result = tc.register_imports(&[ImportSpec {
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
        let mut tc = TypeChecker::new();
        tc.set_current_module(ModuleFullPath::from("main"));

        let result = tc.register_imports(&[ImportSpec {
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
        let mut tc = TypeChecker::new();

        // Create "lib" module with a definition
        seed_module(&mut tc, "lib", vec![("helper", Visibility::Public)]);

        // Create "reexport" module that re-exports from "lib"
        tc.set_current_module(ModuleFullPath::from("reexport"));
        tc.current_symbol_table_mut().insert(
            Symbol::from("helper"),
            ModuleEntry::Reexport {
                source: FQSymbol {
                    module: ModuleFullPath::from("lib"),
                    symbol: Symbol::from("helper"),
                },
            },
        );

        // Import from "reexport" into "main"
        tc.set_current_module(ModuleFullPath::from("main"));
        tc.register_imports(&[ImportSpec {
            module_path: ModuleFullPath::from("reexport"),
            alias: None,
            names: ImportNames::Glob,
            span: Span::SYNTHETIC,
        }])
        .unwrap();

        // Should be able to look up "helper" in main — follows the chain
        let scheme = tc.lookup_self("helper");
        assert!(scheme.is_some());
    }

    // spec: 08-modules §8.6 — conflicting glob imports produce Ambiguous entry
    #[test]
    fn test_import_ambiguity() {
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "mod_a", vec![("clash", Visibility::Public)]);
        seed_module(&mut tc, "mod_b", vec![("clash", Visibility::Public)]);
        tc.set_current_module(ModuleFullPath::from("main"));

        tc.register_imports(&[
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
        ])
        .unwrap();

        // The name should be marked Ambiguous
        assert!(matches!(
            tc.symbol_table().get("clash"),
            Some(ModuleEntry::Ambiguous)
        ));
        // Lookup should return None for ambiguous names
        assert!(tc.lookup_self("clash").is_none());
    }

    // spec: 08-modules §8.6 — duplicate import from same source is not ambiguous
    #[test]
    fn test_import_same_source_not_ambiguous() {
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "math", vec![("add", Visibility::Public)]);
        tc.set_current_module(ModuleFullPath::from("main"));

        // Import the same name twice from the same source
        tc.register_imports(&[
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
        ])
        .unwrap();

        // Should NOT be ambiguous (same source)
        assert!(matches!(
            tc.symbol_table().get("add"),
            Some(ModuleEntry::Import { .. })
        ));
    }

    // spec: 08-modules §8.3 — alias-only import registers alias without bare names
    #[test]
    fn test_import_alias_only() {
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "core.option", vec![("Some", Visibility::Public)]);
        tc.set_current_module(ModuleFullPath::from("main"));

        tc.register_imports(&[ImportSpec {
            module_path: ModuleFullPath::from("core.option"),
            alias: Some(cranelisp_types::ModuleName::from("opt")),
            names: ImportNames::None,
            span: Span::SYNTHETIC,
        }])
        .unwrap();

        // No bare names imported
        assert!(tc.symbol_table().get("Some").is_none());
        // Alias registered
        assert!(tc.state.module_aliases.contains_key(&Symbol::from("opt")));
    }

    // --- is_in_subtree ---

    // spec: 08-modules §8.7 — module is in its own subtree
    #[test]
    fn test_is_in_subtree_self() {
        let tc = TypeChecker::new();
        assert!(tc.is_in_subtree(
            &ModuleFullPath::from("foo"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // spec: 08-modules §8.7 — child module is in parent subtree
    #[test]
    fn test_is_in_subtree_child() {
        let tc = TypeChecker::new();
        assert!(tc.is_in_subtree(
            &ModuleFullPath::from("foo.bar"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // spec: 08-modules §8.7 — grandchild module is in ancestor subtree
    #[test]
    fn test_is_in_subtree_grandchild() {
        let tc = TypeChecker::new();
        assert!(tc.is_in_subtree(
            &ModuleFullPath::from("foo.bar.baz"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // spec: 08-modules §8.7 — unrelated module is not in subtree
    #[test]
    fn test_is_not_in_subtree() {
        let tc = TypeChecker::new();
        assert!(!tc.is_in_subtree(
            &ModuleFullPath::from("other"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // spec: 08-modules §8.7 — string prefix without dot separator is not subtree
    #[test]
    fn test_is_not_in_subtree_prefix_mismatch() {
        let tc = TypeChecker::new();
        // "foobar" starts with "foo" but is NOT a subtree of "foo"
        assert!(!tc.is_in_subtree(
            &ModuleFullPath::from("foobar"),
            &ModuleFullPath::from("foo"),
        ));
    }

    // --- Alias resolution in resolve_qualified ---

    // spec: 08-modules §8.3 — qualified resolution follows module alias
    #[test]
    fn test_resolve_qualified_uses_alias() {
        let mut tc = TypeChecker::new();
        seed_module(
            &mut tc,
            "core.option",
            vec![("Some", Visibility::Public)],
        );
        tc.set_current_module(ModuleFullPath::from("main"));

        // Register alias: "opt" -> "core.option"
        tc.state.module_aliases.insert(
            Symbol::from("opt"),
            ModuleFullPath::from("core.option"),
        );

        // resolve_qualified with alias module path should find the symbol
        let result = tc
            .resolve_qualified_self(&ModuleFullPath::from("opt"), "Some")
            .unwrap();
        assert!(
            result.is_some(),
            "resolve_qualified should resolve 'opt/Some' via alias to core.option"
        );
    }

    // spec: 08-modules §8.5 — direct qualified path works without alias
    #[test]
    fn test_resolve_qualified_without_alias_unchanged() {
        let mut tc = TypeChecker::new();
        seed_module(
            &mut tc,
            "math",
            vec![("add", Visibility::Public)],
        );
        tc.set_current_module(ModuleFullPath::from("main"));

        // No alias — direct path should still work
        let result = tc
            .resolve_qualified_self(&ModuleFullPath::from("math"), "add")
            .unwrap();
        assert!(result.is_some());
    }

    // --- Builtin seeding in new modules ---

    // spec: 08-modules §8.9 — new module seeded with builtin imports as Import entries
    #[test]
    fn test_new_module_has_builtin_imports() {
        let mut tc = TypeChecker::new();
        tc.set_current_module(ModuleFullPath::from("mymod"));
        // Builtins should be accessible as imports
        let table_guard = tc.symbol_table();
        let entry = table_guard.get("add-i64");
        assert!(entry.is_some(), "new module should have add-i64 from builtins");
        assert!(
            matches!(entry.unwrap(), ModuleEntry::Import { .. }),
            "builtin in new module should be an Import entry"
        );
    }

    // --- Concurrency primitives (Phase 2) ---

    // spec: pipeline-v3.md §3.4.3 — AtomicU32 TypeId allocation is monotonic
    #[test]
    fn test_fresh_var_ids_are_monotonic() {
        let mut tc = TypeChecker::new();
        let (_, id1) = tc.fresh_var_id();
        let (_, id2) = tc.fresh_var_id();
        let (_, id3) = tc.fresh_var_id();
        assert!(id1 < id2);
        assert!(id2 < id3);
    }

    // spec: pipeline-v3.md §3.4.3 — fresh_var returns unique Var types
    #[test]
    fn test_fresh_var_returns_unique_vars() {
        let mut tc = TypeChecker::new();
        let v1 = tc.fresh_var();
        let v2 = tc.fresh_var();
        assert_ne!(v1, v2);
        assert!(matches!(v1, Type::Var(_)));
        assert!(matches!(v2, Type::Var(_)));
    }

    // spec: pipeline-v3.md §3.4.3 — try_lock_module succeeds on unlocked module
    #[test]
    fn test_try_lock_module_succeeds() {
        let mut tc = TypeChecker::new();
        let module = ModuleFullPath::from("test.mod");
        assert!(!tc.is_module_locked(&module));
        let guard = tc.try_lock_module(&module);
        assert!(guard.is_ok());
        assert!(tc.is_module_locked(&module));
        drop(guard);
        assert!(!tc.is_module_locked(&module));
    }

    // spec: pipeline-v3.md §3.4.3 — try_lock_module fails on already-locked module
    #[test]
    fn test_try_lock_module_fails_when_locked() {
        let mut tc = TypeChecker::new();
        let module = ModuleFullPath::from("test.mod");
        let _guard = tc.try_lock_module(&module).unwrap();
        // Second lock attempt must fail immediately
        let result = tc.try_lock_module(&module);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            err.message().contains("already being compiled"),
            "expected 'already being compiled' error, got: {}",
            err.message()
        );
    }

    // spec: pipeline-v3.md §3.4.3 — ModuleGuard releases lock on drop (RAII)
    #[test]
    fn test_module_guard_releases_on_drop() {
        let mut tc = TypeChecker::new();
        let module = ModuleFullPath::from("test.mod");
        {
            let _guard = tc.try_lock_module(&module).unwrap();
            assert!(tc.is_module_locked(&module));
        }
        // Guard dropped — lock must be released
        assert!(!tc.is_module_locked(&module));
        // Can re-acquire
        let guard2 = tc.try_lock_module(&module);
        assert!(guard2.is_ok());
    }

    // spec: pipeline-v3.md §3.4.3 — independent modules can be locked simultaneously
    #[test]
    fn test_independent_modules_lock_simultaneously() {
        let mut tc = TypeChecker::new();
        let mod_a = ModuleFullPath::from("mod.a");
        let mod_b = ModuleFullPath::from("mod.b");
        let _guard_a = tc.try_lock_module(&mod_a).unwrap();
        let guard_b = tc.try_lock_module(&mod_b);
        assert!(guard_b.is_ok(), "independent modules should lock independently");
        assert!(tc.is_module_locked(&mod_a));
        assert!(tc.is_module_locked(&mod_b));
    }

    // spec: pipeline-v3.md §3.4.3 — snapshot/restore works with atomic next_id
    #[test]
    fn test_snapshot_restore_with_atomic_next_id() {
        let mut tc = TypeChecker::new();
        // Generate some type vars
        let _ = tc.fresh_var();
        let _ = tc.fresh_var();
        let snap = tc.snapshot();
        let snap_id = snap.next_type_id;
        // Generate more after snapshot
        let _ = tc.fresh_var();
        let _ = tc.fresh_var();
        // Counter should have advanced past snapshot
        assert_eq!(*tc.next_id.get_mut(), snap_id + 2);
        // Restore should reset the counter
        tc.restore(snap);
        assert_eq!(*tc.next_id.get_mut(), snap_id);
        // Next fresh var should use the snapshot's next_id
        let (_, id_after_restore) = tc.fresh_var_id();
        assert_eq!(id_after_restore, snap_id);
    }
}
