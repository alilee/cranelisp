//! `#[cfg(test)]` in-crate pipeline driver (`check_via_forms`) — retains
//! the display-bearing `CheckResult` for in-crate test assertions; the
//! production path routes through `check_forms` in `form.rs`.

use cranelisp_types::{CompileContext, DisplayInfo};
use super::*;

impl<C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore> TypeCheckEnv<'_, C, L> {
    /// Drive the cluster pipeline over a `TopLevel` slice and return the
    /// display-bearing `CheckResult`.
    ///
    /// Mirrors `check_forms`'s internal Pass 1 / Pass 2 / finalize ordering.
    /// `Expr` variants are wrapped in a synthetic zero-arg `Defn` named
    /// `__expr` so they flow through the same passes as regular definitions.
    /// Used by in-crate test fixtures only — the production path is the
    /// `check_forms` free function in `form.rs`.
    #[cfg(test)]
    #[must_use = "check result contains display info needed by REPL-display tests"]
    pub(crate) fn check_via_forms(
        &self,
        state: &mut CheckState,
        program: &[TopLevel],
        ctx: &CompileContext,
        strategy: ModuleStrategy,
    ) -> Result<CheckResult, CranelispError> {
        // Ensure the module's symbol table exists (DashMap interior mutation).
        self.ensure_module_exists(&ctx.module);

        // Set the module on the caller-owned state.
        state.current_module = ctx.module.clone();

        // Build a working copy of the program with Expr variants wrapped
        // as synthetic zero-arg Defns.
        let working_program = Self::wrap_exprs_as_defns(program);

        // Create per-module accumulator
        let mut accumulator = ModuleCheckAccumulator::new();

        // Pass 1: Register all forms in source order
        for form in &working_program {
            let result = self.check_form_register(state, form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }

        // Register default method defns generated during Pass 1 TraitImpl processing.
        // These need Pass 1 signature registration too.
        let defaults: Vec<Defn> = std::mem::take(&mut accumulator.default_method_defns);
        for defn in &defaults {
            let form = TopLevel::Defn(defn.clone());
            let result = self.check_form_register(state, &form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }
        // Put defaults back so finalize knows about them
        accumulator.default_method_defns = defaults;

        // Pass 2: Check bodies for all forms.
        // FIXME 0354 Bug A: mirror `check_forms`' production path — restore the
        // post-Pass-1 bound-param constraints before each form's body check so a
        // prior form's body-instantiation residue (e.g. a `Display`-only var
        // from `show`) does not bleed into this form's generalize.
        let pass1_constraints = state.active_constraints.clone();
        for form in &working_program {
            state.active_constraints = pass1_constraints.clone();
            let result = self.check_form_body(state, form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }

        // Check bodies of default method defns too.
        let defaults_for_body: Vec<Defn> = accumulator.default_method_defns.clone();
        for defn in &defaults_for_body {
            state.active_constraints = pass1_constraints.clone();
            let form = TopLevel::Defn(defn.clone());
            let result = self.check_form_body(state, &form, &mut accumulator)?;
            self.merge_form_result_inner(state, &mut accumulator, result);
        }

        // Finalize: run post-passes (generalization, overload resolution, monomorphisation,
        // auto-curry) and build CheckResult.
        let mut result = self.finalize_check_result_inner(
            state, &mut accumulator, &working_program, strategy,
        )?;

        // Populate display info
        result.display = self.compute_display_info(state, program, &accumulator.defn_type_vars);

        Ok(result)
    }


    /// Wrap `Expr` variants as synthetic zero-arg `Defn` named `__expr`.
    /// Used only by the `check_via_forms` test driver.
    #[cfg(test)]
    pub(super) fn wrap_exprs_as_defns(program: &[TopLevel]) -> Vec<TopLevel> {
        let mut working_program = Vec::with_capacity(program.len());
        for top in program {
            match top {
                TopLevel::Expr(expr) => {
                    let span = expr.span();
                    let wrapper_span = Span::new(
                        span.start.saturating_sub(1),
                        span.end.saturating_add(1),
                    );
                    let synthetic_defn = Defn {
                        name: Symbol::from("__expr"),
                        docstring: None,
                        variants: vec![DefnVariant {
                            params: vec![],
                            body: expr.clone(),
                            span,
                        }],
                        visibility: Visibility::Public,
                        span: wrapper_span,
                    };
                    working_program.push(TopLevel::Defn(synthetic_defn));
                }
                other => {
                    working_program.push(other.clone());
                }
            }
        }
        working_program
    }


    /// Compute DisplayInfo from the last form in the program.
    ///
    /// Populated when the input has 1-2 elements (REPL-like input).
    /// For batch programs (many forms), returns None.
    /// Used only by the `check_via_forms` test driver.
    #[cfg(test)]
    pub(super) fn compute_display_info(
        &self,
        state: &CheckState,
        original_program: &[TopLevel],
        defn_type_vars: &HashMap<Symbol, (Vec<Type>, Type)>,
    ) -> Option<DisplayInfo> {
        if original_program.len() > 2 {
            return None;
        }

        let last = original_program.last()?;
        match last {
            TopLevel::Expr(_expr) => {
                // The synthetic __expr defn was registered — look up its type.
                if let Some((_param_tys, ret_ty)) = defn_type_vars.get(&Symbol::from("__expr")) {
                    let resolved = self.apply_subst(state, ret_ty);
                    Some(DisplayInfo {
                        ty: resolved,
                        scheme: None,
                    })
                } else {
                    None
                }
            }
            TopLevel::Defn(defn) => {
                // Look up the defn's generalized scheme from the symbol table.
                let r = self.current_symbol_table(state);
                if let Some(ModuleEntry::Def { scheme, .. }) = r.view().lookup(&defn.name) {
                    Some(DisplayInfo {
                        ty: scheme.ty.clone(),
                        scheme: Some(scheme.clone()),
                    })
                } else {
                    None
                }
            }
            TopLevel::TypeDef { name, .. } => {
                let fqtn = cranelisp_types::FQTypeName::new(
                    state.current_module.clone(), name.clone(),
                );
                let ty = Type::ADT(fqtn, vec![]);
                Some(DisplayInfo { ty, scheme: None })
            }
            TopLevel::TraitDecl(_) => {
                Some(DisplayInfo { ty: Type::Bool, scheme: None })
            }
            TopLevel::TraitImpl(_) => {
                Some(DisplayInfo { ty: Type::Bool, scheme: None })
            }
        }
    }

}
