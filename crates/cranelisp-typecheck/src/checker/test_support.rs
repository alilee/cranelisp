//! Test-only fixture support extracted from `checker.rs`.
//!
//! Gated by the `#[cfg(test)] pub(crate) mod test_support;` declaration in the
//! parent module, so per-item `#[cfg(test)]` attributes are unnecessary here.

use std::sync::atomic::AtomicU32;

use dashmap::DashMap;

use super::*;

/// Test helper that owns the backing stores and provides a `TypeCheckEnv`
/// plus a `CheckState` for test methods. Replaces the old `TypeChecker::new()`.
pub(crate) struct TestFixture {
    pub modules: DashMap<ModuleFullPath, SymbolTable>,
    pub next_id: AtomicU32,
    pub state: CheckState,
    /// Session-level module-alias table (§8.6.6). Tests that exercise
    /// alias-resolution seed this directly; most leave it empty.
    pub module_aliases: cranelisp_types::ModuleAliases,
}

impl TestFixture {
    /// Create a test fixture with the FULL synthetic world registered and
    /// "user" as the current module.
    ///
    /// Production session-init no longer assembles primitives or synthetic
    /// modules in typecheck (facade §"Builtin registration — removed from
    /// typecheck"; FIXME 0242 reconstructs the mount in `int`). This composes
    /// every Tier-3 content preset (special forms + builtin type names + macros
    /// Sexp/SList + IO ADT + Ring 0/1/3 primitives) via
    /// `FixtureBuilder::full()`, which builds only on `cranelisp-types` (no
    /// `cranelisp-primitives` dep). Tests that need a narrower starting
    /// position can compose presets directly via [`TestFixture::with_content`].
    pub fn new() -> Self {
        Self::with_content(crate::builtins::FixtureBuilder::full())
    }

    /// Create a test fixture seeding exactly the composed content presets,
    /// with "user" as the current module. Use this to declare the minimal
    /// starting position a test needs, e.g.
    /// `TestFixture::with_content(FixtureBuilder::new().with_special_forms())`.
    pub fn with_content(builder: crate::builtins::FixtureBuilder) -> Self {
        let modules = DashMap::new();
        let next_id = AtomicU32::new(0);
        let current_module = ModuleFullPath::from("user");
        modules.insert(current_module.clone(), SymbolTable::new(current_module.clone()));
        builder.seed(&modules, &next_id);
        TestFixture {
            modules,
            next_id,
            state: CheckState::new(current_module),
            module_aliases: cranelisp_types::ModuleAliases::new(),
        }
    }

    /// Get a TypeCheckEnv borrowing this fixture's stores, including the
    /// fixture's module-alias table so alias-resolution tests see seeded
    /// aliases.
    pub fn env(&self) -> TypeCheckEnv<'_> {
        TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases)
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
        self.env().lookup(&self.state, name).0
    }

    /// Resolve qualified using current state.
    pub fn resolve_qualified(
        &self,
        module_path: &ModuleFullPath,
        name: &str,
    ) -> Result<Option<Scheme>, CranelispError> {
        self.env()
            .resolve_qualified(&self.state, module_path, name)
            .map(|(scheme, _gap)| scheme)
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
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
        env.register_type_def(&mut self.state, name, docstring, type_params, constructors, visibility, span)
    }

    /// Register a trait decl (test convenience).
    pub fn register_trait_decl_self(
        &mut self,
        decl: &cranelisp_types::TraitDecl,
    ) -> Result<(), CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
        env.register_trait_decl(&mut self.state, decl)
    }

    /// Register a trait impl (test convenience).
    pub fn register_trait_impl_self(
        &mut self,
        impl_: &cranelisp_types::TraitImpl,
    ) -> Result<Vec<cranelisp_types::Defn>, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
        env.register_trait_impl(&mut self.state, impl_)
    }

    /// Try resolve trait method (test convenience).
    pub fn try_resolve_trait_method_self(
        &mut self,
        name: &Symbol,
        arg_types: &[Type],
        span: Span,
    ) -> Result<Option<cranelisp_types::ResolvedCall>, CranelispError> {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
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
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
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
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
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
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
        env.infer_expr(&mut self.state, expr)
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

    /// Fresh var (test convenience).
    pub fn fresh_var(&self) -> Type {
        self.env().fresh_var()
    }

    /// Instantiate a scheme (test convenience) — exercises the collision-free
    /// `fresh_instantiation_subst` path.
    pub fn instantiate_scheme(&self, scheme: &Scheme) -> Type {
        self.env().instantiate_scheme(scheme)
    }

    /// Force the shared `next_id` counter to a chosen value (test convenience).
    /// Used to reproduce the cross-module instantiation collision where the
    /// counter has not been advanced past an imported scheme's bound vars.
    pub fn set_next_id(&self, value: TypeId) {
        self.next_id.store(value, std::sync::atomic::Ordering::Relaxed);
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
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
        env.check_form(module, form, pass, &mut self.state, accumulator)
    }

    /// Merge form result (test convenience).
    pub fn merge_form_result(
        &mut self,
        module: &ModuleFullPath,
        accumulator: &mut crate::program::ModuleCheckAccumulator,
        result: crate::program::FormCheckResult,
    ) {
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
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
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
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
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
        env.check_via_forms(&mut self.state, program, ctx, strategy)
    }

    /// Resolve a `TypeExpr` in the `user` module (test convenience).
    pub fn resolve_type_expr_in_user(
        &self,
        texpr: &cranelisp_types::TypeExpr,
    ) -> Result<Type, cranelisp_types::ResolveError> {
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
        let env = TypeCheckEnv::new(&self.modules, &self.next_id, &self.module_aliases);
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
