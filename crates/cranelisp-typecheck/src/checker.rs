//! TypeChecker struct: the central state for type inference.
//!
//! Scope operations, fresh variable generation, and expr_type recording.
//! Other modules extend TypeChecker via `impl TypeChecker` blocks.

use std::collections::HashMap;

use cranelisp_types::{
    ConstructorInfo, CranelispError, ExportSpec, FQSymbol, ImportNames, ImportSpec,
    MethodResolutions, ModuleEntry, ModuleFullPath, ResolvedCall, ReplSnapshot, Scheme, Span,
    Subst, Symbol, SymbolTable, TraitName, Type, TypeId, TypeName, Warning,
    apply,
};

use crate::adt::TypeDefRegistry;
use crate::scope::ScopeStack;
use crate::scheme;
use crate::traits::{ActiveConstraints, ImplRegistry, TraitRegistry};

/// Maximum depth for following Import/Reexport chains (spec §8.6.2).
const IMPORT_CHAIN_DEPTH_LIMIT: usize = 10;

/// Central state for Hindley-Milner type inference.
///
/// Fields are pub(crate) so that `impl TypeChecker` blocks in other modules
/// can access them directly (borrow-splitting pattern).
pub struct TypeChecker {
    /// Monotonic counter for fresh type variable IDs.
    pub(crate) next_id: TypeId,
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
    /// Per-module symbol tables, keyed by module full path.
    pub(crate) modules: HashMap<ModuleFullPath, SymbolTable>,
    /// The currently active module path.
    pub(crate) current_module: ModuleFullPath,
    /// Registered type definitions (ADTs).
    pub(crate) type_defs: TypeDefRegistry,
    /// Registered trait declarations (Ring 2).
    pub(crate) trait_registry: TraitRegistry,
    /// Registered trait implementations (Ring 2).
    pub(crate) impl_registry: ImplRegistry,
    /// Active type variable constraints during body checking (Ring 2).
    pub(crate) active_constraints: ActiveConstraints,
    /// Module aliases: alias name -> full module path (from aliased imports).
    pub(crate) module_aliases: HashMap<Symbol, ModuleFullPath>,
    /// Transient flag: set true during `infer_apply` when inferring the callee.
    /// Used to suppress the "constrained fn as value" error for direct calls.
    pub(crate) in_call_position: bool,
    /// Pending auto-curry resolutions for single-arity functions.
    /// (call_span, function_name, applied_arg_count, total_param_count, callee_type, target_resolution)
    /// The callee_type stores the callee's type at inference time (may contain vars).
    /// The optional ResolvedCall is populated when the auto-curried callee is a
    /// trait method or builtin, so the wrapper can call the concrete implementation.
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
}

impl TypeChecker {
    /// Create a new TypeChecker with Ring 0 builtins registered.
    ///
    /// Seeds the default "user" module as the active module.
    pub fn new() -> Self {
        let current_module = ModuleFullPath::from("user");
        let mut modules = HashMap::new();
        modules.insert(
            current_module.clone(),
            SymbolTable::new(current_module.clone()),
        );
        let mut tc = TypeChecker {
            next_id: 0,
            subst: Subst::new(),
            env: ScopeStack::new(),
            expr_types: HashMap::new(),
            method_resolutions: HashMap::new(),
            warnings: Vec::new(),
            modules,
            current_module,
            type_defs: TypeDefRegistry::new(),
            trait_registry: TraitRegistry::default(),
            impl_registry: ImplRegistry::default(),
            active_constraints: ActiveConstraints::default(),
            module_aliases: HashMap::new(),
            in_call_position: false,
            pending_auto_curry: Vec::new(),
            overloads: HashMap::new(),
            resolved_overloads: HashMap::new(),
            pending_overload_resolutions: Vec::new(),
        };
        tc.register_builtins();
        tc
    }

    // --- Module-scoped symbol table accessors ---

    /// Get a reference to the current module's symbol table.
    pub(crate) fn current_symbol_table(&self) -> &SymbolTable {
        self.modules
            .get(&self.current_module)
            .unwrap_or_else(|| unreachable!("invariant: current_module always exists in modules map"))
    }

    /// Get a mutable reference to the current module's symbol table.
    pub(crate) fn current_symbol_table_mut(&mut self) -> &mut SymbolTable {
        self.modules
            .get_mut(&self.current_module)
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
            let primitives_path = ModuleFullPath::from("primitives");
            if let Some(prims_table) = self.modules.get(&primitives_path) {
                for (name, _entry) in prims_table.all_symbols() {
                    table.insert(
                        name.clone(),
                        ModuleEntry::Import {
                            source: FQSymbol {
                                module: primitives_path.clone(),
                                symbol: name.clone(),
                            },
                        },
                    );
                }
            }

            // Seed from `user` module: special forms, trait decls,
            // constrained defs, constructors, and type defs.
            let user_path = ModuleFullPath::from("user");
            if let Some(user_table) = self.modules.get(&user_path) {
                for (name, entry) in user_table.all_symbols() {
                    let is_seedable = matches!(entry, ModuleEntry::Def { kind, .. }
                        if matches!(kind.as_ref(),
                            cranelisp_types::DefKind::SpecialForm { .. }
                        )
                    ) || matches!(entry, ModuleEntry::Def { scheme, .. }
                        if !scheme.constraints.is_empty()
                    ) || matches!(entry, ModuleEntry::Constructor { .. })
                      || matches!(entry, ModuleEntry::TypeDef { .. })
                      || matches!(entry, ModuleEntry::TraitDecl { .. });
                    if is_seedable {
                        table.insert(
                            name.clone(),
                            ModuleEntry::Import {
                                source: FQSymbol {
                                    module: user_path.clone(),
                                    symbol: name.clone(),
                                },
                            },
                        );
                    }
                }
            }

            self.modules.insert(path.clone(), table);
        }
        self.current_module = path;
    }

    /// Get the current module path.
    pub fn current_module_path(&self) -> &ModuleFullPath {
        &self.current_module
    }

    /// Check whether a module has been registered.
    pub fn has_module(&self, path: &ModuleFullPath) -> bool {
        self.modules.contains_key(path)
    }

    /// Convenience accessor for the current module's symbol table (public).
    /// Used by tests and external code that needs to inspect symbols.
    pub fn symbol_table(&self) -> &SymbolTable {
        self.current_symbol_table()
    }

    /// Mutable accessor for the current module's symbol table (public).
    /// Used by the pipeline orchestrator to register macro entries.
    pub fn symbol_table_mut(&mut self) -> &mut SymbolTable {
        self.current_symbol_table_mut()
    }

    /// Public accessor for the type definition registry.
    /// Used by prelude loading to copy type defs into the REPL session.
    pub fn type_def_registry(&self) -> &TypeDefRegistry {
        &self.type_defs
    }

    /// Look up a specific module's symbol table by path.
    /// Used by `/imports` to resolve type signatures of imported symbols.
    pub fn module_table(&self, path: &ModuleFullPath) -> Option<&SymbolTable> {
        self.modules.get(path)
    }

    /// Look up the defining module for a symbol. Checks the `primitives` module
    /// first (for core traits and builtins), then falls back to the current module.
    pub fn defining_module_for(&self, name: &str) -> ModuleFullPath {
        let primitives_path = ModuleFullPath::from("primitives");
        if let Some(table) = self.modules.get(&primitives_path)
            && table.get(name).is_some()
        {
            return primitives_path;
        }
        self.current_module.clone()
    }

    // --- Scope operations (delegate to ScopeStack) ---

    /// Push a new scope frame.
    pub(crate) fn push_scope(&mut self) {
        self.env.push_scope();
    }

    /// Pop the topmost scope frame.
    pub(crate) fn pop_scope(&mut self) {
        self.env.pop_scope();
    }

    /// Bind a name in the current scope with a type scheme.
    pub(crate) fn bind_local(&mut self, name: Symbol, scheme: Scheme) {
        self.env.bind(name, scheme);
    }

    /// Look up a name in scope stack, falling back to current module's symbol table.
    ///
    /// Resolution order per spec §8.6.1:
    /// 1. Local environment (let bindings, fn params, match vars)
    /// 2. Module scope (current module's defs + imports, following chains)
    /// 3. Qualified name resolution: `module/name` splits on `/` and resolves
    ///    via `resolve_qualified` (spec §8.6.6)
    pub(crate) fn lookup(&self, name: &str) -> Option<Scheme> {
        // Check local scope stack first
        if let Some(scheme) = self.env.lookup(name) {
            return Some(scheme.clone());
        }

        // Fall back to current module's symbol table (following import chains)
        if let Some(scheme) = self.lookup_in_current_module(name) {
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
                    format!("{}.{}", self.current_module, module_part),
                );
                if let Ok(Some(scheme)) = self.resolve_qualified(&child_path, name_part) {
                    return Some(scheme);
                }

                // Fall back to absolute module path.
                let abs_path = ModuleFullPath::from(module_part);
                if let Ok(Some(scheme)) = self.resolve_qualified(&abs_path, name_part) {
                    return Some(scheme);
                }

                // Also try alias resolution (handled inside resolve_qualified).
            }
        }

        None
    }

    /// Look up a name in the current module's symbol table, following
    /// Import/Reexport chains to their source definitions.
    fn lookup_in_current_module(&self, name: &str) -> Option<Scheme> {
        let entry = self.current_symbol_table().get(name)?;
        self.extract_scheme_from_entry(entry, 0)
    }

    /// Extract a Scheme from a ModuleEntry, following Import/Reexport chains.
    ///
    /// `depth` tracks recursion to enforce the chain depth limit (spec §8.6.2).
    fn extract_scheme_from_entry(
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
    fn resolve_fq_symbol(&self, fq: &FQSymbol, depth: usize) -> Option<Scheme> {
        let source_table = self.modules.get(&fq.module)?;
        let entry = source_table.get(fq.symbol.as_ref())?;
        self.extract_scheme_from_entry(entry, depth)
    }

    /// Resolve a name in the current module to its terminal `ModuleEntry`,
    /// following Import/Reexport chains.
    pub(crate) fn resolve_entry_in_current_module(&self, name: &str) -> Option<&ModuleEntry> {
        let entry = self.current_symbol_table().get(name)?;
        self.resolve_to_terminal_entry(entry, 0)
    }

    /// Follow Import/Reexport chains to the terminal `ModuleEntry`.
    pub(crate) fn resolve_to_terminal_entry<'a>(
        &'a self,
        entry: &'a ModuleEntry,
        depth: usize,
    ) -> Option<&'a ModuleEntry> {
        if depth > IMPORT_CHAIN_DEPTH_LIMIT {
            return None;
        }
        match entry {
            ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                let source_table = self.modules.get(&source.module)?;
                let target = source_table.get(source.symbol.as_ref())?;
                self.resolve_to_terminal_entry(target, depth + 1)
            }
            other => Some(other),
        }
    }

    /// Resolve a qualified name `module_path/name` (spec §8.6.6).
    ///
    /// Bypasses local scope. Checks visibility — private names are inaccessible
    /// from outside the defining module's subtree (spec §8.7.3).
    pub fn resolve_qualified(
        &self,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Result<Option<Scheme>, CranelispError> {
        // Resolve the module: check if the first path component is an alias
        let first_component = module_path.as_ref().split('.').next().unwrap_or(module_path.as_ref());
        let resolved_path = self
            .module_aliases
            .get(&Symbol::from(first_component))
            .cloned()
            .unwrap_or_else(|| module_path.clone());

        let table = match self.modules.get(&resolved_path) {
            Some(t) => t,
            None => return Ok(None), // Module not loaded
        };

        let entry = match table.get(name) {
            Some(e) => e,
            None => return Ok(None),
        };

        // Visibility check: private names are only accessible within the
        // defining module's subtree
        if !entry.is_public() && !self.is_in_subtree(&self.current_module, &resolved_path) {
            return Err(CranelispError::TypeError {
                message: format!(
                    "'{}' is private in module '{}'",
                    name, resolved_path
                ),
                span: Span::SYNTHETIC,
            });
        }

        Ok(self.extract_scheme_from_entry(entry, 0))
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
    pub(crate) fn fresh_var(&mut self) -> Type {
        crate::unify::fresh_var(&mut self.next_id)
    }

    /// Generate a fresh type variable and return both the type and ID.
    /// Used by ADT registration to allocate type parameter variables.
    pub(crate) fn fresh_var_id(&mut self) -> (Type, TypeId) {
        crate::unify::fresh_var_id(&mut self.next_id)
    }

    // --- Unification (delegate to unify module, borrow-splitting) ---

    /// Unify two types. Wraps the free function with self's subst.
    /// `span` is used for error context.
    pub(crate) fn unify(
        &mut self,
        t1: &Type,
        t2: &Type,
        span: Span,
    ) -> Result<(), CranelispError> {
        crate::unify::unify(&mut self.subst, t1, t2).map_err(|e| {
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
    pub(crate) fn instantiate(&mut self, s: &Scheme) -> Type {
        if s.constraints.is_empty() {
            scheme::instantiate(s, &mut self.next_id)
        } else {
            self.instantiate_constrained(s)
        }
    }

    /// Generalize a type relative to the current environment,
    /// propagating any active constraints on the quantified variables.
    ///
    /// Constraints are resolved through the substitution: if a constraint
    /// was recorded on var X, and X is unified with var Y (the scheme var),
    /// the constraint attaches to Y. This handles the case where
    /// `instantiate_constrained` records a constraint on a fresh var that
    /// gets unified with a different var during type checking.
    pub(crate) fn generalize(&self, ty: &Type) -> Scheme {
        let env_fv = self.env.free_vars_in_env();
        let mut scheme = scheme::generalize(&self.subst, ty, &env_fv);

        // Build a set of scheme vars for fast lookup
        let scheme_var_set: std::collections::HashSet<TypeId> =
            scheme.vars.iter().copied().collect();

        // Propagate constraints from active_constraints to the scheme,
        // resolving through the substitution.
        let mut constraints: std::collections::HashMap<TypeId, Vec<_>> =
            std::collections::HashMap::new();

        for (constrained_var, traits) in self.active_constraints.all() {
            // Resolve the constrained var through the substitution
            let resolved = apply(&self.subst, &Type::Var(*constrained_var));
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
    pub(crate) fn record_expr_type(&mut self, span: Span, ty: Type) {
        self.expr_types.insert(span, ty);
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
        self.expr_types.clear();
        self.method_resolutions.clear();
        self.active_constraints = ActiveConstraints::default();
    }

    /// Apply the current substitution to a type.
    pub(crate) fn apply_subst(&self, ty: &Type) -> Type {
        apply(&self.subst, ty)
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
        for spec in specs {
            // Register alias if present
            if let Some(alias) = &spec.alias {
                self.module_aliases.insert(
                    Symbol::from(alias.as_ref()),
                    spec.module_path.clone(),
                );
            }

            let source_table = match self.modules.get(&spec.module_path) {
                Some(t) => t,
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

            // Collect names to import (collect first to avoid borrowing
            // self.modules while mutating current symbol table)
            let imports_to_add: Vec<(Symbol, ModuleEntry)> = match &spec.names {
                ImportNames::Glob => {
                    collect_glob_imports(source_table, &spec.module_path)
                }
                ImportNames::Specific(names) => {
                    self.collect_specific_imports(
                        source_table, names, &spec.module_path, spec.span,
                    )?
                }
                ImportNames::MemberGlob(parent) => {
                    self.collect_member_glob_imports(
                        source_table, parent, &spec.module_path,
                    )
                }
                ImportNames::None => {
                    // Alias-only import — no bare names
                    Vec::new()
                }
            };

            // Insert into current symbol table, detecting ambiguities
            insert_imports_detecting_ambiguity(
                self.current_symbol_table_mut(),
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
        for spec in specs {
            // Resolve the module path: try as-is first, then as a child
            // of the current module (e.g., "syntax" -> "core.syntax"
            // when current module is "core").
            let resolved_path = if self.modules.contains_key(&spec.module_path) {
                spec.module_path.clone()
            } else {
                let child_path = ModuleFullPath::from(format!(
                    "{}.{}",
                    self.current_module, spec.module_path
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

            let source_table = match self.modules.get(&resolved_path) {
                Some(t) => t,
                None => unreachable!("module existence verified above"),
            };

            // Collect names to re-export (collect first to avoid borrowing
            // self.modules while mutating current symbol table).
            let reexports: Vec<(Symbol, ModuleEntry)> = match &spec.names {
                ImportNames::Glob => {
                    collect_glob_reexports(source_table, &resolved_path)
                }
                ImportNames::Specific(names) => {
                    self.collect_specific_reexports(
                        source_table, names, &resolved_path, spec.span,
                    )?
                }
                ImportNames::MemberGlob(parent) => {
                    self.collect_member_glob_reexports(
                        source_table, parent, &resolved_path,
                    )
                }
                ImportNames::None => {
                    // No names to re-export.
                    Vec::new()
                }
            };

            // Insert into current symbol table, detecting ambiguities.
            insert_imports_detecting_ambiguity(
                self.current_symbol_table_mut(),
                reexports,
            );
        }
        Ok(())
    }

    /// Collect specific named re-exports from a source module, checking
    /// visibility and existence.
    fn collect_specific_reexports(
        &self,
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
                            &self.current_module,
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
                    ) && self
                        .trait_registry
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
                            &self.current_module,
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
                    ) && self
                        .trait_registry
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
        self.type_defs
            .get(type_name)
            .map(|info| info.constructors.clone())
    }

    /// Return all trait names that have an impl registered for `type_name`.
    /// Results are sorted alphabetically.
    pub fn get_impls_for_type(&self, type_name: &TypeName) -> Vec<TraitName> {
        let mut traits: Vec<TraitName> = self
            .impl_registry
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
        self.trait_registry
            .decls
            .get(trait_name)
            .map(|decl| decl.methods.iter().map(|m| m.name.clone()).collect())
    }

    /// Return all type names that implement a given trait.
    /// Results are sorted alphabetically.
    pub fn get_implementing_types(&self, trait_name: &TraitName) -> Vec<TypeName> {
        let mut types: Vec<TypeName> = self
            .impl_registry
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
        // Try as child of current module (e.g., "user.foo" when current is "user")
        let child_path =
            ModuleFullPath::from(format!("{}.{}", self.current_module, name));
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
        if let Some(decl) = self.trait_registry.decls.remove(trait_name) {
            for method in &decl.methods {
                self.trait_registry.method_to_trait.remove(&method.name);
            }
            // Also remove impls for this trait to allow re-registration.
            self.impl_registry.impls.remove(trait_name);
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
        let table = self.modules.remove(module_path)?;

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
        for (_, entry) in table.all_symbols() {
            if let ModuleEntry::TypeDef { info, .. } = entry {
                self.type_defs.type_defs.remove(&info.name);
                for ctor in &info.constructors {
                    self.type_defs.constructor_to_type.remove(&ctor.name);
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
        for (_name, entry) in table.all_symbols() {
            match entry {
                ModuleEntry::TypeDef { info, .. } => {
                    // Register each constructor in constructor_to_type.
                    for ctor in &info.constructors {
                        self.type_defs.constructor_to_type.insert(
                            ctor.name.clone(),
                            info.name.clone(),
                        );
                    }
                    self.type_defs.type_defs.insert(
                        info.name.clone(),
                        info.clone(),
                    );
                }
                ModuleEntry::Constructor { type_name, .. } => {
                    // Ensure constructor_to_type has this entry too
                    // (may duplicate the TypeDef loop, but HashMap insert is idempotent).
                    self.type_defs.constructor_to_type.insert(
                        _name.clone(),
                        TypeName::from(type_name.as_ref()),
                    );
                }
                ModuleEntry::TraitDecl { decl, .. }
                    // Reconstruct trait_registry from cached TraitDecl entries.
                    // This populates decls and method_to_trait so trait method
                    // resolution works after loading from cache.
                    if !self.trait_registry.decls.contains_key(&decl.name) => {
                        for method in &decl.methods {
                            self.trait_registry
                                .method_to_trait
                                .insert(method.name.clone(), decl.name.clone());
                        }
                        self.trait_registry
                            .decls
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
            && self.next_id <= id
        {
            self.next_id = id + 1;
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
            if self.impl_registry.has_impl(&trait_name, &impl_type) {
                continue;
            }

            let mut method_primitives = HashMap::new();
            method_primitives.insert(method_name.clone(), method_name);

            self.impl_registry.impls
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
        ReplSnapshot {
            next_type_id: self.next_id,
            symbol_keys: self.current_symbol_table().symbols.keys().cloned().collect(),
            subst_len: self.subst.len(),
            scope_depth: self.env.depth(),
        }
    }

    /// Restore state from a snapshot (on REPL error).
    pub fn restore(&mut self, snapshot: ReplSnapshot) {
        self.next_id = snapshot.next_type_id;
        self.subst.retain(|id, _| *id < snapshot.next_type_id);
        self.expr_types.clear();
        self.method_resolutions.clear();
        self.warnings.clear();
        self.pending_auto_curry.clear();
        // Remove symbol table entries added after the snapshot was taken.
        self.current_symbol_table_mut()
            .symbols
            .retain(|key, _| snapshot.symbol_keys.contains(key));
        // Restore scope stack depth (pop frames left by failed check_defn_body).
        self.env.truncate_to(snapshot.scope_depth);
    }

    // --- Known types lookup (for resolve_type_expr) ---

    /// Build a map of known type names for type expression resolution.
    pub(crate) fn known_type_names(&self) -> crate::resolve::KnownTypes {
        self.type_defs.known_types()
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
        self.type_defs.is_internal_constructor(bare_name)
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
            .resolve_qualified(&ModuleFullPath::from("math"), "add")
            .unwrap();
        assert!(result.is_some());
    }

    // spec: 08-modules §8.7 — private symbol access denied from outside module
    #[test]
    fn test_resolve_qualified_private_denied() {
        let mut tc = TypeChecker::new();
        seed_module(&mut tc, "math", vec![("internal", Visibility::Private)]);
        tc.set_current_module(ModuleFullPath::from("user"));

        let result = tc.resolve_qualified(
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
            .resolve_qualified(&ModuleFullPath::from("math"), "internal")
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
            .resolve_qualified(&ModuleFullPath::from("math"), "nonexistent")
            .unwrap();
        assert!(result.is_none());
    }

    // spec: 08-modules §8.6 — qualified lookup on unknown module returns None
    #[test]
    fn test_resolve_qualified_unknown_module() {
        let tc = TypeChecker::new();
        let result = tc
            .resolve_qualified(&ModuleFullPath::from("unknown"), "foo")
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
        let scheme = tc.lookup("helper");
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
        assert!(tc.lookup("clash").is_none());
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
        assert!(tc.module_aliases.contains_key(&Symbol::from("opt")));
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
        tc.module_aliases.insert(
            Symbol::from("opt"),
            ModuleFullPath::from("core.option"),
        );

        // resolve_qualified with alias module path should find the symbol
        let result = tc
            .resolve_qualified(&ModuleFullPath::from("opt"), "Some")
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
            .resolve_qualified(&ModuleFullPath::from("math"), "add")
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
        let entry = tc.symbol_table().get("add-i64");
        assert!(entry.is_some(), "new module should have add-i64 from builtins");
        assert!(
            matches!(entry.unwrap(), ModuleEntry::Import { .. }),
            "builtin in new module should be an Import entry"
        );
    }
}
