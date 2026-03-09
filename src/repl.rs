// REPL session: interactive read-eval-print loop with persistent state.
//
// The TypeChecker and ModuleCodegenState persist across inputs so that
// function definitions and type definitions accumulate. Each input is
// parsed, type-checked, compiled, and executed independently.
//
// Error recovery: on any error, the TypeChecker is restored to its
// pre-input snapshot so the session remains usable.
//
// No `unwrap()` in this module -- all errors use `?`.
//
// FIXME(/int): Universal output format (repl/spec.md §1.1, S14) — major rework needed:
//
// 1. special_form_feedback(): Add classification comment suffix to ALL outputs:
//    - Functions: `:Type module/name ; defn - docstring`
//    - Constructors: `:Type module/Type.Ctor ; deftype`
//    - Types: `:module/Type ; deftype` + related symbols (match: ctors, impl: traits)
//    - Traits: `:module/Trait ; deftrait` + related symbols (defn: methods, impl: types)
//    - Special forms: `:Type name ; special form - description`
//    - Macros: `:module/name ; defmacro` + clause signatures (`; [params] -> Sexp`)
//    - Primitives: currently skipped (DefKind::Primitive returns None) — MUST show as defn
//    - Trait methods: use `Trait.method` dot notation (e.g. `core.num/Num.+`)
//    - Builtin types (Int, Bool, Float, String): `:primitives/Type ; type` + impl: section
//
// 2. handle_list(): Align with spec §3.3:
//    - Remove special_forms category (belongs on /imports)
//    - Remove imports category (belongs on /imports)
//    - Include constructors in Types category
//    - Print `(no definitions)` for empty module
//    - Change filter from substring to prefix match (case-insensitive)
//    - Category order: Modules, Macros, Traits, Types, Fns
//
// 3. handle_imports(): Align with spec §3.4:
//    - ADD special forms category (always present)
//    - Include Reexport entries (not just Import)
//    - Per-source-module filter: `/imports modulename` → `From module:` groups
//    - Unfiltered: organize by category (Macros, Traits, Types, Fns)
//
// 4. /exports: New command (spec §3.5) — resolve module, list public symbols by category
//
// 5. Macro display: Replace `name :: macro` format with universal format:
//    `:module/name ; defmacro` + `; [params] -> Sexp` clause lines
//    Affects: defmacro definition response, /info, /sig, /doc, bare symbol lookup
//

use std::collections::HashMap;
use std::io::{self, BufRead, Write};
use std::time::{Duration, Instant};

use cranelisp_backend::got::ModuleCodegenState;
use cranelisp_backend::heap::{HeapAdt, HeapVec};
use cranelisp_backend::jit::Jit;
use cranelisp_typecheck::TypeChecker;
use cranelisp_types::{
    CompileMode, CranelispError, DefKind, MacroClauseInfo, MacroParam,
    ModuleEntry, ModuleFullPath, ReplCheckResult, ReplInput, Sexp, Symbol, Type,
    TypeDefInfo, TypeName, Visibility, Warning, NULLARY_TAG_THRESHOLD,
};

use crate::expander::CraneliftExpander;

/// Result of evaluating one REPL input.
pub struct ReplResult {
    /// The i64 result value (raw bits; interpret per type).
    pub value: i64,
    /// The inferred type of the input.
    pub ty: Type,
    /// Whether this was a definition (defn/deftype) rather than an expression.
    pub is_definition: bool,
    /// Non-fatal warnings.
    pub warnings: Vec<Warning>,
    /// Override display string for definitions (deftrait, impl, constrained fn).
    /// When present, `format_repl_display` uses this instead of `format_result_value`.
    pub definition_display: Option<String>,
    /// Time spent executing the compiled function pointer (excludes compilation).
    /// The caller can compute compile time as `total_elapsed - eval_duration`.
    pub eval_duration: Duration,
}

/// Persistent REPL session state.
pub struct ReplSession {
    /// Type checker state (persists across inputs).
    pub tc: TypeChecker,
    /// Backend GOT state (persists across inputs for function redefinition).
    pub got_state: ModuleCodegenState,
    /// Macro expander (persists across inputs — macros accumulate).
    expander: CraneliftExpander,
    /// JIT instances that must stay alive (their code is referenced via GOT).
    /// Each defn compilation creates a new JIT; we keep them alive here.
    jit_modules: Vec<Jit>,
    /// Accumulated type definitions from all inputs (for ADT value display).
    type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Maps type names to the module they were defined in (for qualified display).
    type_modules: HashMap<TypeName, ModuleFullPath>,
}

impl ReplSession {
    /// Create a new REPL session without prelude loading.
    pub fn new() -> Self {
        ReplSession {
            tc: TypeChecker::new(),
            got_state: ModuleCodegenState::new(),
            expander: CraneliftExpander::new(),
            jit_modules: Vec::new(),
            type_defs: HashMap::new(),
            type_modules: HashMap::new(),
        }
    }

    /// Create a new REPL session with prelude loading.
    ///
    /// Resolves the prelude module from `project_root` or `lib_dirs`, compiles
    /// it through the normal module graph pipeline, and injects an implicit
    /// `(import [prelude [*]])`. If no prelude is found, the session works
    /// normally without it.
    pub fn new_with_prelude(
        project_root: &std::path::Path,
        lib_dirs: &[std::path::PathBuf],
    ) -> Result<Self, CranelispError> {
        let mut session = Self::new();

        // We need a temporary JIT for prelude compilation.
        let mut jit = Jit::new()?;
        jit.declare_intrinsics()?;
        let mut all_func_sigs: Vec<(Symbol, usize)> = Vec::new();

        let prelude_jits = crate::pipeline::load_prelude(
            project_root,
            lib_dirs,
            &mut session.tc,
            &mut session.expander,
            &mut jit,
            &mut all_func_sigs,
        )?;

        // Store prelude JIT modules to keep code alive.
        session.jit_modules.extend(prelude_jits);
        // The main JIT for prelude code also needs to stay alive.
        session.jit_modules.push(jit);

        // Switch back to user module for REPL input.
        session.tc.set_current_module(ModuleFullPath::from("user"));

        Ok(session)
    }

    /// Get the accumulated type definitions for value display.
    pub fn type_defs(&self) -> &HashMap<TypeName, TypeDefInfo> {
        &self.type_defs
    }

    /// Get the type-to-module mapping for qualified display.
    pub fn type_modules(&self) -> &HashMap<TypeName, ModuleFullPath> {
        &self.type_modules
    }

    /// Evaluate a single source input, returning the result.
    ///
    /// Pipeline:
    /// 1. Parse source -> sexps
    /// 2. Check for defmacro -> compile + register, return display
    /// 3. Expand through CraneliftExpander
    /// 4. Flatten (begin ...) results, process sub-forms
    /// 5. Build REPL input -> typecheck -> compile -> execute
    ///
    /// On error, restores the TypeChecker to its pre-input state.
    pub fn eval(&mut self, source: &str) -> Result<ReplResult, CranelispError> {
        // Skip blank and comment-only input before it reaches the parser.
        let trimmed = source.trim();
        if trimmed.is_empty() || is_comment_only(trimmed) {
            return Ok(ReplResult {
                value: 0,
                ty: Type::Int,
                is_definition: true,
                warnings: Vec::new(),
                definition_display: None,
                eval_duration: Duration::ZERO,
            });
        }

        // Parse the source into sexps.
        let mut sexps = cranelisp_frontend::parse(source)?;

        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty input".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            });
        }

        // Take the first sexp for evaluation.
        let first_sexp = sexps.swap_remove(0);

        // Snapshot for error recovery (covers macro compilation too).
        let snapshot = self.tc.snapshot();

        match self.eval_sexp(first_sexp) {
            Ok(result) => Ok(result),
            Err(e) => {
                self.tc.restore(snapshot);
                Err(e)
            }
        }
    }

    /// Evaluate a single Sexp with defmacro interception and macro expansion.
    ///
    /// This is the core of the REPL eval loop, separated to allow recursive
    /// processing of begin-flattened sub-forms.
    fn eval_sexp(&mut self, sexp: Sexp) -> Result<ReplResult, CranelispError> {
        // Step 1: Check for defmacro — compile and register the macro.
        if cranelisp_frontend::is_defmacro(&sexp) {
            return self.eval_defmacro(&sexp);
        }

        // Step 1b: Check for import — intercept before AST building.
        // Import forms must be handled here because the AST builder does not
        // accept (import ...) — it expects module declarations to be extracted
        // before AST construction. In the REPL, imports are entered interactively.
        if is_import_form(&sexp) {
            return self.eval_import(sexp);
        }

        // Step 1c: Check for bare symbols that need introspection display.
        // Non-zero-arg macro names show their signature (instead of failing
        // with "no matching clause"). Special forms show their description
        // (instead of erroring in the typechecker).
        if let Some(result) = self.check_bare_symbol_introspection(&sexp) {
            return Ok(result);
        }

        // Step 2: Expand macros in the sexp.
        let expanded = self.expander.expand_sexp(sexp)?;

        // Step 3: Flatten (begin ...) results and process sub-forms.
        let forms = cranelisp_frontend::flatten_begin(expanded);
        self.eval_flattened_forms(forms)
    }

    /// Process a sequence of flattened forms, returning the result of the last.
    ///
    /// Each form may itself be a defmacro (defmacro-in-results from macro
    /// expansion). Non-macro, non-type forms are accumulated and compiled
    /// as a batch.
    fn eval_flattened_forms(
        &mut self,
        forms: Vec<Sexp>,
    ) -> Result<ReplResult, CranelispError> {
        let mut last_result = None;

        for form in forms {
            if cranelisp_frontend::is_defmacro(&form) {
                last_result = Some(self.eval_defmacro(&form)?);
                continue;
            }
            if is_import_form(&form) {
                last_result = Some(self.eval_import(form)?);
                continue;
            }

            // Build and process a normal REPL input.
            let input = cranelisp_frontend::build_repl_input(&form, &mut self.expander)?;
            let check_result = self.tc.check_repl_input(&input)?;
            last_result = Some(self.compile_and_execute(&input, &check_result)?);
        }

        last_result.ok_or_else(|| CranelispError::ParseError {
            message: "empty input after expansion".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        })
    }

    /// Compile a defmacro form and register it in the expander and symbol table.
    ///
    /// Creates a fresh JIT for the macro clause compilation, keeps it alive
    /// so the compiled function pointer remains valid. Registers the macro
    /// in the TC's symbol table as `ModuleEntry::Macro` for introspection.
    fn eval_defmacro(&mut self, sexp: &Sexp) -> Result<ReplResult, CranelispError> {
        let info = cranelisp_frontend::parse_defmacro(sexp)?;

        let mut jit = Jit::new()?;
        jit.declare_intrinsics()?;

        self.expander.compile_macro(&info, &mut self.tc, &mut jit)?;

        // Keep JIT alive so macro function pointers remain valid.
        self.jit_modules.push(jit);

        // Register macro in the symbol table for introspection (spec §11.2).
        let clause_infos: Vec<MacroClauseInfo> = info
            .clauses
            .iter()
            .map(|c| MacroClauseInfo {
                params: c.fixed_params.clone(),
                rest_param: c.rest_param.clone(),
                source: None,
            })
            .collect();
        let visibility = if info.is_private {
            Visibility::Private
        } else {
            Visibility::Public
        };
        self.tc.symbol_table_mut().insert(
            info.name.clone(),
            ModuleEntry::Macro {
                name: info.name.clone(),
                clauses: clause_infos,
                docstring: info.docstring.clone(),
                visibility,
                sexp: Some(sexp.clone()),
                source: None,
            },
        );

        // Display format per spec §11.3: "name :: macro" or "name :: macro (N clauses)"
        let display = format_defmacro_display(&info.name, info.clauses.len());

        Ok(ReplResult {
            value: 0,
            ty: Type::Int,
            is_definition: true,
            warnings: Vec::new(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Check if a sexp is a bare symbol that should show introspection info
    /// instead of being evaluated.
    ///
    /// Intercepts:
    /// - Non-zero-arg macros: show signature (zero-arg macros expand normally)
    /// - Special forms: show description (they have no value semantics)
    ///
    /// Does NOT intercept:
    /// - Constructors, functions, imports: these have value semantics
    /// - Zero-arg macros: the expander handles these
    fn check_bare_symbol_introspection(&self, sexp: &Sexp) -> Option<ReplResult> {
        let name = match sexp {
            Sexp::Symbol(name, _) => name,
            _ => return None,
        };

        // Look up the symbol in the current module's symbol table.
        let entry = self.tc.symbol_table().get(name.as_str())?;
        match entry {
            ModuleEntry::Macro { clauses, .. } => {
                // Check if any clause accepts zero args — if so, let the
                // expander handle it (it's a valid zero-arg macro call).
                let has_zero_arg_clause = clauses.iter().any(|c| {
                    c.params.is_empty() && c.rest_param.is_none()
                });
                if has_zero_arg_clause {
                    return None; // Let expander handle zero-arg expansion.
                }
                // Non-zero-arg macro: show signature info.
                let display = format_macro_signature(name, clauses);
                Some(ReplResult {
                    value: 0,
                    ty: Type::Int,
                    is_definition: true,
                    warnings: Vec::new(),
                    definition_display: Some(display),
                    eval_duration: Duration::ZERO,
                })
            }
            ModuleEntry::Def { kind, .. } => {
                // Special forms have no value semantics — show description.
                if let DefKind::SpecialForm { description } = kind.as_ref() {
                    let display = format_special_form_display(name, description);
                    Some(ReplResult {
                        value: 0,
                        ty: Type::Int,
                        is_definition: true,
                        warnings: Vec::new(),
                        definition_display: Some(display),
                        eval_duration: Duration::ZERO,
                    })
                } else {
                    None // Regular function — let it evaluate normally.
                }
            }
            _ => None,
        }
    }

    /// Process an import form in the REPL.
    ///
    /// Parses the import sexp using `extract_module_declarations` and registers
    /// the resulting import specs in the typechecker's symbol table.
    fn eval_import(&mut self, sexp: Sexp) -> Result<ReplResult, CranelispError> {
        let module = self.tc.current_module_path().clone();
        let (structure, _remaining) =
            cranelisp_frontend::extract_module_declarations(module, None, vec![sexp])?;

        if !structure.import_specs.is_empty() {
            self.tc.register_imports(&structure.import_specs)?;
        }

        // Build display: "imported N names from module1, module2, ..."
        let mod_names: Vec<String> = structure
            .import_specs
            .iter()
            .map(|s| s.module_path.to_string())
            .collect();
        let display = if mod_names.is_empty() {
            "import: no names".to_string()
        } else {
            format!("imported from {}", mod_names.join(", "))
        };

        Ok(ReplResult {
            value: 0,
            ty: Type::Int,
            is_definition: true,
            warnings: Vec::new(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Compile and execute a checked REPL input.
    fn compile_and_execute(
        &mut self,
        input: &ReplInput,
        check_result: &ReplCheckResult,
    ) -> Result<ReplResult, CranelispError> {
        match input {
            ReplInput::Expr(expr) => self.execute_expr(expr, check_result),
            ReplInput::Defn(defn) => self.execute_defn(defn, check_result),
            ReplInput::TypeDef { .. } => self.execute_typedef(check_result),
            ReplInput::DefnMulti { span, .. } => Err(CranelispError::TypeError {
                message: "multi-signature functions not supported in Ring 0".into(),
                span: *span,
            }),
            ReplInput::TraitDecl(decl) => self.execute_trait_decl(decl, check_result),
            ReplInput::TraitImpl(impl_) => self.execute_trait_impl(impl_, check_result),
        }
    }

    /// Compile and execute an expression input.
    fn execute_expr(
        &mut self,
        expr: &cranelisp_types::Expr,
        check_result: &ReplCheckResult,
    ) -> Result<ReplResult, CranelispError> {
        let check = self.build_check_for_backend(check_result);

        // Compile any monomorphised specializations before executing
        // the expression (Gap 4: REPL constrained-poly path).
        self.compile_mono_defns(check_result)?;

        let compiled = cranelisp_backend::compile_expr_with_got(
            expr,
            &check,
            CompileMode::Interactive,
            Some(&mut self.got_state),
        )?;

        // Time the actual evaluation (function call) separately from compilation.
        let eval_start = Instant::now();
        let value = compiled.execute();
        let eval_duration = eval_start.elapsed();

        Ok(ReplResult {
            value,
            ty: check_result.ty.clone(),
            is_definition: false,
            warnings: check_result.warnings.clone(),
            definition_display: None,
            eval_duration,
        })
    }

    /// Compile and execute a function definition input.
    fn execute_defn(
        &mut self,
        defn: &cranelisp_types::Defn,
        check_result: &ReplCheckResult,
    ) -> Result<ReplResult, CranelispError> {
        // Skip compiling constrained fn base definitions — they are
        // templates that get monomorphised at call sites.
        let is_constrained = check_result
            .scheme
            .as_ref()
            .is_some_and(|s| !s.constraints.is_empty());

        if !is_constrained {
            let check = self.build_check_for_backend(check_result);
            self.compile_and_register_defn(defn, &check)?;
        }

        // For defn, execute if it's zero-arg, otherwise return 0.
        // Time the execution separately from compilation.
        let (value, eval_duration) = if defn.params.is_empty() && !is_constrained {
            let entry = self.got_state.def_codegen.get(defn.name.as_ref());
            let code_ptr = entry
                .and_then(|e| e.code_ptr)
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("no code pointer after compiling defn '{}'", defn.name),
                    span: cranelisp_types::Span::SYNTHETIC,
                })?;
            let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
            let eval_start = Instant::now();
            let result = func();
            (result, eval_start.elapsed())
        } else {
            (0, Duration::ZERO)
        };

        // Build definition display with qualified name (spec §1.3).
        let module = self.tc.current_module_path().clone();
        let definition_display = if is_constrained {
            check_result.scheme.as_ref().map(|s| {
                format_scheme_display(&defn.name, s, &module, &self.type_modules)
            })
        } else if !defn.params.is_empty() {
            let type_str = format_type_qualified(&check_result.ty, &self.type_modules);
            Some(format!(":{type_str} {module}/{}", defn.name))
        } else {
            None
        };

        Ok(ReplResult {
            value,
            ty: check_result.ty.clone(),
            is_definition: true,
            warnings: check_result.warnings.clone(),
            definition_display,
            eval_duration,
        })
    }

    /// Execute a type definition input.
    fn execute_typedef(
        &mut self,
        check_result: &ReplCheckResult,
    ) -> Result<ReplResult, CranelispError> {
        let module = self.tc.current_module_path().clone();

        // Accumulate type definitions for ADT value display.
        for (name, info) in &check_result.type_defs {
            self.type_defs.insert(name.clone(), info.clone());
            self.type_modules.insert(name.clone(), module.clone());
        }

        // Build qualified display: `:module/TypeName`
        let type_name = match &check_result.ty {
            Type::ADT(name, _) => name.to_string(),
            _ => "?".to_string(),
        };
        let display = format!(":{module}/{type_name}");

        Ok(ReplResult {
            value: 0,
            ty: check_result.ty.clone(),
            is_definition: true,
            warnings: check_result.warnings.clone(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Execute a trait declaration input.
    fn execute_trait_decl(
        &mut self,
        decl: &cranelisp_types::TraitDecl,
        check_result: &ReplCheckResult,
    ) -> Result<ReplResult, CranelispError> {
        // Trait registration is already done by check_repl_input.
        // Compile any default method bodies generated by the typechecker.
        if !check_result.default_method_defns.is_empty() {
            let check = self.build_check_for_backend(check_result);
            for defn in &check_result.default_method_defns {
                self.compile_and_register_defn(defn, &check)?;
            }
        }

        let module = self.tc.current_module_path();
        let display = format!(":{module}/{}", decl.name);

        Ok(ReplResult {
            value: 0,
            ty: check_result.ty.clone(),
            is_definition: true,
            warnings: check_result.warnings.clone(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Execute a trait implementation input.
    fn execute_trait_impl(
        &mut self,
        impl_: &cranelisp_types::TraitImpl,
        check_result: &ReplCheckResult,
    ) -> Result<ReplResult, CranelispError> {
        let check = self.build_check_for_backend(check_result);

        // Compile the impl methods.
        for defn in &impl_.methods {
            self.compile_and_register_defn(defn, &check)?;
        }

        // Compile any default method bodies generated by the typechecker.
        for defn in &check_result.default_method_defns {
            self.compile_and_register_defn(defn, &check)?;
        }

        // Compile any monomorphised definitions generated during checking.
        self.compile_mono_defns(check_result)?;

        let module = self.tc.current_module_path();
        let display = format!(
            "impl {module}/{} for {module}/{}",
            impl_.trait_name, impl_.target_type
        );

        Ok(ReplResult {
            value: 0,
            ty: check_result.ty.clone(),
            is_definition: true,
            warnings: check_result.warnings.clone(),
            definition_display: Some(display),
            eval_duration: Duration::ZERO,
        })
    }

    /// Compile monomorphised specializations from a check result.
    ///
    /// Used by both expression and trait impl execution paths.
    fn compile_mono_defns(
        &mut self,
        check_result: &ReplCheckResult,
    ) -> Result<(), CranelispError> {
        for mono in &check_result.mono_defns {
            let mut mono_check = self.build_check_for_backend(check_result);
            mono_check.method_resolutions.extend(mono.resolutions.clone());
            if !mono.expr_types.is_empty() {
                mono_check.expr_types = mono.expr_types.clone();
            }
            self.compile_and_register_defn(&mono.defn, &mono_check)?;
        }
        Ok(())
    }

    /// Compile a single function definition and register it in the GOT.
    ///
    /// Used by Defn, TraitDecl (default methods), and TraitImpl (impl methods).
    fn compile_and_register_defn(
        &mut self,
        defn: &cranelisp_types::Defn,
        check: &cranelisp_types::CheckResult,
    ) -> Result<(), CranelispError> {
        let mut jit = Jit::new()?;

        // Declare runtime intrinsics (Ring 1 heap infrastructure).
        jit.declare_intrinsics()?;

        // Declare just this function.
        let func_ids = jit.declare_functions(&[defn])?;

        // Ensure a GOT slot exists for this function.
        let slot = self.got_state.ensure_slot_for(&defn.name)?;

        // Build GOT slot map from existing state + this new function.
        let mut got_slots: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &self.got_state.def_codegen {
            if let Some(s) = dc.got_slot {
                got_slots.insert(name.clone(), s);
            }
        }
        got_slots.insert(defn.name.clone(), slot);

        let got_base = self.got_state.got_base_ptr() as i64;

        // Build function arity map from existing GOT state + this defn.
        let mut func_arities: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &self.got_state.def_codegen {
            if let Some(pc) = dc.param_count {
                func_arities.insert(name.clone(), pc);
            }
        }
        func_arities.insert(defn.name.clone(), defn.params.len());

        // Compile the function with awareness of existing GOT.
        let compile_ctx = jit.build_compile_context(
            check,
            CompileMode::Interactive,
            &func_ids,
            &func_arities,
            Some(&got_slots),
            Some(got_base),
            None, // No cross-module GOT in single-module REPL yet.
        );
        let _clif_ir = jit.compile_defn(defn, compile_ctx)?;

        // Finalize and get the code pointer.
        let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params.len())?;

        // Update the GOT slot with the new code pointer.
        self.got_state.update_slot(slot, code_ptr);

        // Record codegen info.
        let entry = self.got_state.def_codegen.entry(defn.name.clone()).or_default();
        entry.code_ptr = Some(code_ptr);
        entry.got_slot = Some(slot);
        entry.param_count = Some(defn.params.len());

        // Keep JIT alive so code pointer remains valid.
        self.jit_modules.push(jit);

        Ok(())
    }

    /// Build a CheckResult suitable for the backend from a ReplCheckResult.
    fn build_check_for_backend(
        &self,
        repl_check: &ReplCheckResult,
    ) -> cranelisp_types::CheckResult {
        cranelisp_types::CheckResult {
            method_resolutions: repl_check.method_resolutions.clone(),
            constrained_fn_names: repl_check.constrained_fn_names.clone(),
            mono_defns: Vec::new(), // MonoDefn is not Clone; backend handles mono
            expr_types: repl_check.expr_types.clone(),
            default_method_defns: repl_check.default_method_defns.clone(),
            warnings: repl_check.warnings.clone(),
            type_defs: repl_check.type_defs.clone(),
            constructor_to_type: repl_check.constructor_to_type.clone(),
        }
    }
}

impl Default for ReplSession {
    fn default() -> Self {
        Self::new()
    }
}

/// Qualify a type name with its module path for REPL display (spec §1.4).
///
/// Primitives get `primitives/` prefix. User-defined types look up their
/// defining module in `type_modules`. `Fn` and type variables stay bare.
fn qualify_type_name(name: &str, type_modules: &HashMap<TypeName, ModuleFullPath>) -> String {
    if let Some(module) = type_modules.get(name) {
        format!("{module}/{name}")
    } else {
        // Not in type_modules — unqualified (e.g., type vars, unknown types).
        name.to_string()
    }
}

/// Format a type with fully-qualified names for REPL display (spec §1.4).
///
/// Primitive types get `primitives/` prefix, ADT types get their module prefix,
/// `Fn` keyword and type variables stay unqualified.
fn format_type_qualified(ty: &Type, type_modules: &HashMap<TypeName, ModuleFullPath>) -> String {
    // Compute var names from the full type, then use them in the recursive helper.
    let var_names = cranelisp_types::type_var_names(ty);
    format_type_qualified_inner(ty, type_modules, &var_names)
}

/// Recursive helper for `format_type_qualified` with pre-computed var names.
fn format_type_qualified_inner(
    ty: &Type,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
    var_names: &HashMap<cranelisp_types::TypeId, String>,
) -> String {
    match ty {
        Type::Int => "primitives/Int".to_string(),
        Type::Bool => "primitives/Bool".to_string(),
        Type::String => "primitives/String".to_string(),
        Type::Float => "primitives/Float".to_string(),
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| format_type_qualified_inner(p, type_modules, var_names))
                .collect();
            let ret_s = format_type_qualified_inner(ret, type_modules, var_names);
            format!("(Fn [{}] {ret_s})", parts.join(" "))
        }
        Type::ADT(name, args) => {
            let qname = qualify_type_name(name, type_modules);
            if args.is_empty() {
                qname
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_qualified_inner(a, type_modules, var_names))
                    .collect();
                format!("({qname} {})", arg_strs.join(" "))
            }
        }
        Type::Var(id) => {
            var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"))
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if args.is_empty() {
                name
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| format_type_qualified_inner(a, type_modules, var_names))
                    .collect();
                format!("({name} {})", arg_strs.join(" "))
            }
        }
    }
}

/// Format a result value for REPL display (simple version, no ADT introspection).
///
/// Format: `:Type value`
/// - Bool: `true` / `false`
/// - Float: reinterpret i64 bits as f64
/// - Int: decimal integer
/// - String: reads heap string content, displays as `:String "contents"`
/// - Fn: displays as `:(Fn [...] ...) <closure>`
/// - ADT without type_defs: `:TypeName tag` (fallback, no constructor name lookup)
///
/// For richer ADT display with constructor names and field values,
/// use `format_result_value` which accepts `type_defs`.
pub fn format_result(value: i64, ty: &Type) -> String {
    format_result_value(value, ty, &HashMap::new(), &HashMap::new())
}

/// Format a constrained function's scheme for REPL display (spec §1.3).
///
/// Produces inline-constraint notation:
///   `:(Fn [:Num a :a] a) user/double`
///
/// On first occurrence of a constrained type variable, the constraint trait
/// is shown as `:TraitName var`. Subsequent occurrences use `:var`.
/// Unconstrained variables appear bare.
fn format_scheme_display(
    name: &str,
    scheme: &cranelisp_types::Scheme,
    module: &cranelisp_types::ModuleFullPath,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    let var_names = cranelisp_types::type_var_names(&scheme.ty);

    // Build a map from TypeId to the constraint traits for quick lookup.
    // Use sorted trait names for deterministic output.
    let mut constraint_map: HashMap<cranelisp_types::TypeId, Vec<&str>> = HashMap::new();
    for (type_id, traits) in &scheme.constraints {
        let mut trait_strs: Vec<&str> = traits.iter().map(|t| t.as_ref()).collect();
        trait_strs.sort();
        constraint_map.insert(*type_id, trait_strs);
    }

    // Track which constrained vars have been "introduced" (first occurrence shown).
    let mut introduced: std::collections::HashSet<cranelisp_types::TypeId> =
        std::collections::HashSet::new();

    let type_str = format_type_with_inline_constraints(
        &scheme.ty,
        &var_names,
        &constraint_map,
        &mut introduced,
        false,
        type_modules,
    );

    format!(":{type_str} {module}/{name}")
}

/// Format a type with inline constraint annotations (spec §1.3, §1.4).
///
/// Type names are fully qualified. Inside function param lists (`in_params = true`):
///   first occurrence of constrained var: `:TraitName var`
///   subsequent occurrences: `:var`
/// Outside param lists (return type, ADT args): vars are always bare.
fn format_type_with_inline_constraints(
    ty: &Type,
    var_names: &HashMap<cranelisp_types::TypeId, String>,
    constraints: &HashMap<cranelisp_types::TypeId, Vec<&str>>,
    introduced: &mut std::collections::HashSet<cranelisp_types::TypeId>,
    in_params: bool,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    match ty {
        Type::Int => "primitives/Int".to_string(),
        Type::Bool => "primitives/Bool".to_string(),
        Type::String => "primitives/String".to_string(),
        Type::Float => "primitives/Float".to_string(),
        Type::Fn(params, ret) => {
            let parts: Vec<String> = params
                .iter()
                .map(|p| {
                    format_type_with_inline_constraints(
                        p, var_names, constraints, introduced, true, type_modules,
                    )
                })
                .collect();
            let ret_s = format_type_with_inline_constraints(
                ret, var_names, constraints, introduced, false, type_modules,
            );
            format!("(Fn [{}] {ret_s})", parts.join(" "))
        }
        Type::ADT(name, args) => {
            let qname = qualify_type_name(name, type_modules);
            if args.is_empty() {
                qname
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| {
                        format_type_with_inline_constraints(
                            a, var_names, constraints, introduced, false, type_modules,
                        )
                    })
                    .collect();
                format!("({qname} {})", arg_strs.join(" "))
            }
        }
        Type::Var(id) => {
            let var_name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if in_params {
                if let Some(traits) = constraints.get(id) {
                    if !introduced.contains(id) {
                        // First occurrence in params: show `:TraitName var`
                        introduced.insert(*id);
                        let trait_prefix = traits.join(" ");
                        format!(":{trait_prefix} {var_name}")
                    } else {
                        // Subsequent occurrence in params: show `:var`
                        format!(":{var_name}")
                    }
                } else {
                    // Unconstrained var in params: bare name
                    var_name
                }
            } else {
                // Outside params (return type, etc.): always bare
                var_name
            }
        }
        Type::TyConApp(id, args) => {
            let name = var_names
                .get(id)
                .cloned()
                .unwrap_or_else(|| format!("t{id}"));
            if args.is_empty() {
                name
            } else {
                let arg_strs: Vec<String> = args
                    .iter()
                    .map(|a| {
                        format_type_with_inline_constraints(
                            a, var_names, constraints, introduced, false, type_modules,
                        )
                    })
                    .collect();
                format!("({name} {})", arg_strs.join(" "))
            }
        }
    }
}

/// Format a result value for REPL display with full type definition context.
///
/// When `type_defs` is provided, ADT values are displayed with constructor
/// names and field values: `:(user/Option primitives/Int) (Option.Some 42)`.
///
/// Types are fully qualified per spec §1.4. Constructor values use
/// `Type.Constructor` dot notation per spec §1.5.
///
/// Strings are read from heap memory via `cranelisp_runtime::read_string_as_str`.
/// Closures display as `:(Fn [...] ...) <closure>`.
pub fn format_result_value(
    value: i64,
    ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    match ty {
        Type::Bool => {
            let display_val = if value != 0 { "true" } else { "false" };
            format!(":primitives/Bool {display_val}")
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            let s = format!("{f}");
            if s.contains('.') {
                format!(":primitives/Float {s}")
            } else {
                format!(":primitives/Float {s}.0")
            }
        }
        Type::Int => format!(":primitives/Int {value}"),
        Type::String => format_string_value(value),
        Type::Fn(_, _) => {
            let type_str = format_type_qualified(ty, type_modules);
            format!(":{type_str} <closure>")
        }
        Type::ADT(type_name, type_args) => {
            format_adt_value(value, type_name, type_args, type_defs, type_modules)
        }
        other => {
            let type_str = format_type_qualified(other, type_modules);
            format!(":{type_str} {value}")
        }
    }
}

/// Format a String heap value as `:primitives/String "contents"`.
fn format_string_value(value: i64) -> String {
    if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
        // Null or small value -- not a valid heap pointer.
        return format!(":primitives/String <invalid:{value}>");
    }
    // SAFETY: value is a heap pointer to a valid HeapString (produced by JIT code).
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    format!(":primitives/String \"{s}\"")
}

/// Check whether a type has exactly one constructor whose name matches the type name.
///
/// Single-constructor product types like `(deftype Point [:Int x :Int y])` have
/// a redundant `Type.Constructor` display (`Point.Point`). For these types we
/// suppress the `Type.` prefix and show just the constructor name.
fn is_single_matching_constructor(type_name: &TypeName, type_info: &TypeDefInfo) -> bool {
    type_info.constructors.len() == 1 && type_info.constructors[0].name.0 == type_name.0
}

/// Format the constructor display name for an ADT value.
///
/// For single-constructor types where the constructor name matches the type name,
/// returns just the constructor name (e.g., `Point`). For multi-constructor types,
/// returns `Type.Constructor` (e.g., `Color.Red`, `Option.Some`).
fn format_ctor_display(type_name: &TypeName, ctor_name: &str, type_info: &TypeDefInfo) -> String {
    if is_single_matching_constructor(type_name, type_info) {
        ctor_name.to_string()
    } else {
        format!("{type_name}.{ctor_name}")
    }
}

/// Format an ADT value with constructor name lookup and dot notation (spec §1.5).
///
/// Nullary constructors display as `Type.Ctor` (e.g., `Color.Red`).
/// Data constructors display as `(Type.Ctor field1 field2)` (e.g., `(Option.Some 42)`).
/// Single-constructor product types where the constructor name matches the type name
/// suppress the `Type.` prefix (e.g., `(Point 3 4)` not `(Point.Point 3 4)`).
/// Type names in the `:Type` prefix are fully qualified.
fn format_adt_value(
    value: i64,
    type_name: &TypeName,
    type_args: &[Type],
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    let type_display = format_adt_type_qualified(type_name, type_args, type_modules);

    // Vec is a built-in type, not in type_defs -- handle it specially.
    if type_name == "Vec" {
        let elem_type = type_args.first();
        let elems = format_vec_elements(value, elem_type, type_defs, type_modules);
        return format!(":{type_display} {elems}");
    }

    let Some(type_info) = type_defs.get(type_name) else {
        // No type def available -- fallback to bare value display.
        return format!(":{type_display} {value}");
    };

    // Determine if this is a nullary tag or a heap pointer.
    if (value as usize) < NULLARY_TAG_THRESHOLD {
        // Nullary constructor: value is the tag directly.
        let tag = value as usize;
        let ctor_name = find_constructor_by_tag(type_info, tag);
        let ctor_display = format_ctor_display(type_name, &ctor_name, type_info);
        format!(":{type_display} {ctor_display}")
    } else {
        // Data constructor: read tag and fields from heap.
        format_adt_heap_value(value, &type_display, type_name, type_info, type_args, type_defs, type_modules)
    }
}

/// Format the type portion of an ADT display with qualification (spec §1.4).
/// Simple types: `user/Color`. Parameterized: `(user/Option primitives/Int)`.
fn format_adt_type_qualified(
    type_name: &TypeName,
    type_args: &[Type],
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    let qname = qualify_type_name(type_name, type_modules);
    if type_args.is_empty() {
        qname
    } else {
        let arg_strs: Vec<String> = type_args
            .iter()
            .map(|a| format_type_qualified(a, type_modules))
            .collect();
        format!("({qname} {})", arg_strs.join(" "))
    }
}

/// Find a constructor name by tag, or return a fallback string.
fn find_constructor_by_tag(type_info: &TypeDefInfo, tag: usize) -> String {
    type_info
        .constructors
        .iter()
        .find(|c| c.tag == tag)
        .map(|c| format!("{}", c.name))
        .unwrap_or_else(|| format!("<tag:{tag}>"))
}

/// Format a heap-allocated ADT value (data constructor with fields).
///
/// Reads tag from HeapAdt::TAG_OFFSET (16), fields from HeapAdt::field_offset(i).
/// Recursively formats field values using their declared types.
/// Uses `Type.Constructor` dot notation per spec §1.5, suppressing the `Type.`
/// prefix for single-constructor product types where the constructor name matches
/// the type name.
///
/// For polymorphic ADTs (e.g., `(Option Int)`), substitutes the concrete type_args
/// into field types before formatting. Without this, fields with type variables
/// would display as raw values instead of properly formatted values.
fn format_adt_heap_value(
    value: i64,
    type_display: &str,
    type_name: &TypeName,
    type_info: &TypeDefInfo,
    type_args: &[Type],
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    // SAFETY: value is a heap pointer to a valid HeapAdt (produced by JIT code).
    let base = value as *const u8;
    let tag = unsafe { *(base.add(HeapAdt::TAG_OFFSET as usize) as *const i64) } as usize;
    let ctor = type_info.constructors.iter().find(|c| c.tag == tag);

    let Some(ctor) = ctor else {
        return format!(":{type_display} <unknown-tag:{tag}>");
    };

    if ctor.fields.is_empty() {
        // Nullary constructor stored on heap (shouldn't happen, but handle gracefully).
        let ctor_display = format_ctor_display(type_name, &ctor.name, type_info);
        return format!(":{type_display} {ctor_display}");
    }

    // Build substitution from type_params to type_args for polymorphic ADTs.
    let subst = build_adt_subst(type_info, type_args);

    // Read and format each field.
    let mut field_strs = Vec::new();
    for (i, field_info) in ctor.fields.iter().enumerate() {
        let field_offset = HeapAdt::field_offset(i) as usize;
        let field_val = unsafe { *(base.add(field_offset) as *const i64) };
        // Substitute type args into field type before formatting.
        let field_ty = substitute_field_type(&field_info.ty, &subst);
        let field_str = format_field_value(field_val, &field_ty, type_defs, type_modules);
        field_strs.push(field_str);
    }

    let fields_display = field_strs.join(" ");
    let ctor_display = format_ctor_display(type_name, &ctor.name, type_info);
    format!(":{type_display} ({ctor_display} {fields_display})")
}

/// Build a type substitution from a TypeDefInfo's type_params and concrete type_args.
///
/// The type_params are Symbol names (e.g., "a", "b") but the field types use
/// Type::Var(TypeId). We need to map from the Var ids used in field types
/// to the concrete types in type_args.
fn build_adt_subst(
    type_info: &TypeDefInfo,
    type_args: &[Type],
) -> HashMap<cranelisp_types::TypeId, Type> {
    let mut subst = HashMap::new();
    // Collect all Var ids used in constructor fields, in order.
    let mut var_ids = Vec::new();
    for ctor in &type_info.constructors {
        for field in &ctor.fields {
            collect_var_ids(&field.ty, &mut var_ids);
        }
    }
    // Map each unique Var id to the corresponding type arg.
    for (i, &id) in var_ids.iter().enumerate() {
        if i < type_args.len() {
            subst.insert(id, type_args[i].clone());
        }
    }
    subst
}

/// Collect unique Var ids from a type in order of first occurrence.
fn collect_var_ids(ty: &Type, ids: &mut Vec<cranelisp_types::TypeId>) {
    match ty {
        Type::Var(id) => {
            if !ids.contains(id) {
                ids.push(*id);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_var_ids(p, ids);
            }
            collect_var_ids(ret, ids);
        }
        Type::ADT(_, args) | Type::TyConApp(_, args) => {
            for a in args {
                collect_var_ids(a, ids);
            }
        }
        Type::Int | Type::Bool | Type::String | Type::Float => {}
    }
}

/// Substitute type variables in a field type using the given substitution.
fn substitute_field_type(
    ty: &Type,
    subst: &HashMap<cranelisp_types::TypeId, Type>,
) -> Type {
    cranelisp_types::apply(subst, ty)
}

/// Format Vec elements by reading the heap layout.
///
/// HeapVec layout: `[alloc_size(+0) | rc(+8) | len(+16) | cap(+24) | data_ptr(+32)]`
/// Elements are stored in the data buffer at `data_ptr`, each 8 bytes (i64).
fn format_vec_elements(
    value: i64,
    elem_type: Option<&Type>,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
        return "[]".to_string();
    }

    let base = value as *const u8;
    // SAFETY: value is a heap pointer to a valid HeapVec (produced by JIT code).
    let len = unsafe { *(base.add(HeapVec::LEN_OFFSET as usize) as *const i64) } as usize;
    if len == 0 {
        return "[]".to_string();
    }

    let data_ptr = unsafe { *(base.add(HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64) };
    if data_ptr.is_null() {
        return "[]".to_string();
    }

    let mut elems = Vec::with_capacity(len);
    for i in 0..len {
        let elem_val = unsafe { *data_ptr.add(i) };
        let formatted = match elem_type {
            Some(ty) => format_field_value(elem_val, ty, type_defs, type_modules),
            None => format!("{elem_val}"),
        };
        elems.push(formatted);
    }

    format!("[{}]", elems.join(" "))
}

/// Format a single field value based on its type.
///
/// Field values use `Type.Constructor` dot notation for ADT constructors (spec §1.5).
fn format_field_value(
    value: i64,
    ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    match ty {
        Type::Int => format!("{value}"),
        Type::Bool => {
            if value != 0 { "true".to_string() } else { "false".to_string() }
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            let s = format!("{f}");
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Type::String => {
            if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
                format!("<invalid-string:{value}>")
            } else {
                let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
                format!("\"{s}\"")
            }
        }
        Type::Fn(_, _) => "<closure>".to_string(),
        Type::ADT(name, args) => {
            // Vec is built-in, not in type_defs.
            if name == "Vec" {
                return format_vec_elements(value, args.first(), type_defs, type_modules);
            }
            // Recursive ADT formatting with dot notation.
            let type_display = format_adt_type_qualified(name, args, type_modules);
            if let Some(info) = type_defs.get(name) {
                if (value as usize) < NULLARY_TAG_THRESHOLD {
                    let tag = value as usize;
                    let ctor_name = find_constructor_by_tag(info, tag);
                    format_ctor_display(name, &ctor_name, info)
                } else {
                    // Recursive heap ADT -- format with parens and dot notation.
                    let inner = format_adt_heap_value(
                        value, &type_display, name, info, args, type_defs, type_modules,
                    );
                    // Strip the leading `:Type ` prefix from the recursive call.
                    inner.split_once(' ').map_or_else(
                        || inner.clone(),
                        |(_, rest)| rest.to_string(),
                    )
                }
            } else {
                format!("{value}")
            }
        }
        _ => format!("{value}"),
    }
}

/// Format the REPL display for a defmacro definition (spec §11.3).
///
/// Single clause: `name :: macro`
/// Multi-clause:  `name :: macro (N clauses)`
fn format_defmacro_display(name: &str, clause_count: usize) -> String {
    if clause_count <= 1 {
        format!("{name} :: macro")
    } else {
        format!("{name} :: macro ({clause_count} clauses)")
    }
}

/// Parsed REPL slash command.
enum ReplCommand<'a> {
    Help,
    Quit,
    Sig(&'a str),
    Doc(&'a str),
    Type(&'a str),
    Info(&'a str),
    List(&'a str),
    Time(&'a str),
    Expand(&'a str),
    Imports(&'a str),
    Unknown(&'a str),
}

/// Parse a slash command from trimmed input.
///
/// Returns `None` if the input does not start with `/`.
fn parse_slash_command(input: &str) -> Option<ReplCommand<'_>> {
    if !input.starts_with('/') {
        return None;
    }

    let (cmd, arg) = match input.split_once(char::is_whitespace) {
        Some((c, a)) => (c, a.trim()),
        None => (input, ""),
    };

    Some(match cmd {
        "/help" | "/h" => ReplCommand::Help,
        "/quit" | "/q" => ReplCommand::Quit,
        "/sig" | "/s" => ReplCommand::Sig(arg),
        "/doc" | "/d" => ReplCommand::Doc(arg),
        "/type" | "/t" => ReplCommand::Type(arg),
        "/info" | "/i" => ReplCommand::Info(arg),
        "/list" | "/l" => ReplCommand::List(arg),
        "/time" => ReplCommand::Time(arg),
        "/expand" | "/e" => ReplCommand::Expand(arg),
        "/imports" => ReplCommand::Imports(arg),
        _ => ReplCommand::Unknown(cmd),
    })
}

/// Print the /help command output to stdout.
fn print_help(stdout: &mut impl Write) {
    let _ = writeln!(stdout, "Available commands:");
    let _ = writeln!(stdout, "  /help (/h)          Show this help");
    let _ = writeln!(stdout, "  /quit (/q)          Exit REPL");
    let _ = writeln!(stdout, "  /sig (/s) NAME      Show type signature");
    let _ = writeln!(stdout, "  /doc (/d) NAME      Show docstring");
    let _ = writeln!(stdout, "  /type (/t) EXPR     Show type without evaluating");
    let _ = writeln!(stdout, "  /info (/i) NAME     Show full details");
    let _ = writeln!(stdout, "  /list (/l) [FILTER] List symbols in current module");
    let _ = writeln!(stdout, "  /time EXPR          Evaluate with timing breakdown");
    let _ = writeln!(stdout, "  /expand (/e) FORM   Macro-expand a form");
    let _ = writeln!(stdout, "  /imports [MODULE]   Show imports in current module");
}

/// Format the REPL prompt with timing and module info.
fn format_prompt(compile_ms: u64, eval_ms: u64, module: &str) -> String {
    format!("{compile_ms}+{eval_ms}ms; {module}> ")
}

/// Write the prompt string to stdout and flush.
fn write_prompt(stdout: &mut impl Write, compile_ms: u64, eval_ms: u64, module: &str) {
    let prompt = format_prompt(compile_ms, eval_ms, module);
    let _ = write!(stdout, "{prompt}");
    let _ = stdout.flush();
}

/// Dispatch a parsed slash command, returning true if the REPL should quit.
fn dispatch_slash_command(
    cmd: ReplCommand,
    session: &mut ReplSession,
    stdout: &mut impl Write,
) -> bool {
    match cmd {
        ReplCommand::Help => print_help(stdout),
        ReplCommand::Quit => return true,
        ReplCommand::Sig(name) => handle_sig(session, name, stdout),
        ReplCommand::Doc(name) => handle_doc(session, name, stdout),
        ReplCommand::Type(expr_src) => handle_type(session, expr_src, stdout),
        ReplCommand::Info(name) => handle_info(session, name, stdout),
        ReplCommand::List(filter) => handle_list(session, filter, stdout),
        ReplCommand::Time(expr_src) => {
            match handle_time(session, expr_src) {
                Ok(display) => {
                    let _ = writeln!(stdout, "{display}");
                }
                Err(e) => {
                    let _ = writeln!(stdout, "error: {e}");
                }
            }
        }
        ReplCommand::Expand(form) => handle_expand(session, form, stdout),
        ReplCommand::Imports(filter) => handle_imports(session, filter, stdout),
        ReplCommand::Unknown(cmd) => {
            let _ = writeln!(
                stdout,
                "error: unknown command '{cmd}'. Type /help for available commands."
            );
        }
    }
    false
}

/// Evaluate an input and display the result, returning updated timing.
fn eval_and_display(
    session: &mut ReplSession,
    input: &str,
    stdout: &mut impl Write,
) -> (u64, u64) {
    let total_start = Instant::now();
    match session.eval(input) {
        Ok(result) => {
            let total_elapsed = total_start.elapsed();
            // Compile time = total time minus the eval (function call) time.
            let compile_duration = total_elapsed.saturating_sub(result.eval_duration);
            let compile_ms = compile_duration.as_millis() as u64;
            let eval_ms = result.eval_duration.as_millis() as u64;

            for w in &result.warnings {
                let _ = writeln!(stdout, "warning: {}", w.message);
            }
            let display = if let Some(ref def_display) = result.definition_display {
                def_display.clone()
            } else {
                format_result_value(
                    result.value,
                    &result.ty,
                    session.type_defs(),
                    session.type_modules(),
                )
            };
            let _ = writeln!(stdout, "{display}");
            (compile_ms, eval_ms)
        }
        Err(e) => {
            let total_elapsed = total_start.elapsed();
            let compile_ms = total_elapsed.as_millis() as u64;
            let _ = writeln!(stdout, "error: {e}");
            (compile_ms, 0)
        }
    }
}

/// Create a REPL session, attempting prelude loading from the current directory.
///
/// Library directories are assembled from `CRANELISP_LIB` (if set) or the
/// `stdlib/` directory in the current directory (fallback). If prelude loading
/// fails, falls back to a session without prelude.
fn create_repl_session() -> ReplSession {
    let cwd = std::env::current_dir().ok();

    if let Some(ref project_root) = cwd {
        let lib_dirs = crate::pipeline::assemble_lib_dirs(project_root);

        match ReplSession::new_with_prelude(project_root, &lib_dirs) {
            Ok(session) => return session,
            Err(e) => {
                eprintln!("warning: prelude loading failed: {e}");
            }
        }
    }

    ReplSession::new()
}

/// Run the interactive REPL loop.
///
/// Reads lines from stdin, evaluates them, prints results.
/// Errors are printed without crashing the session.
///
/// Library directories are resolved from `CRANELISP_LIB` (if set) or the
/// `stdlib/` directory in the current directory. If prelude loading fails,
/// starts without it and prints a warning.
pub fn run_repl() {
    let mut session = create_repl_session();
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    // Startup banner.
    let _ = writeln!(stdout, "Cranelisp v0.1.0");
    let _ = writeln!(stdout, "Type /help for commands, /quit to exit.");

    let mut last_compile_ms: u64 = 0;
    let mut last_eval_ms: u64 = 0;
    let module = "user";

    let prompt = format_prompt(last_compile_ms, last_eval_ms, module);
    write_prompt(&mut stdout, last_compile_ms, last_eval_ms, module);

    let mut buffer = String::new();

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        buffer.push_str(&line);

        if !parens_balanced(&buffer) {
            buffer.push('\n');
            let continuation = format!("{:>width$}", "...", width = prompt.len());
            let _ = write!(stdout, "{continuation}");
            let _ = stdout.flush();
            continue;
        }

        let input = buffer.trim();
        if input.is_empty() || is_comment_only(input) {
            buffer.clear();
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, module);
            continue;
        }

        if let Some(cmd) = parse_slash_command(input) {
            let should_quit = dispatch_slash_command(cmd, &mut session, &mut stdout);
            buffer.clear();
            if should_quit {
                break;
            }
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, module);
            continue;
        }

        if let Some(display) = special_form_feedback(input, &session) {
            let _ = writeln!(stdout, "{display}");
            buffer.clear();
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, module);
            continue;
        }

        (last_compile_ms, last_eval_ms) =
            eval_and_display(&mut session, input, &mut stdout);

        buffer.clear();
        write_prompt(&mut stdout, last_compile_ms, last_eval_ms, module);
    }

    let _ = writeln!(stdout);
}

/// Check if a Sexp is an `(import ...)` form.
///
/// Returns true if the sexp is a list whose head is the symbol `import`.
fn is_import_form(sexp: &Sexp) -> bool {
    matches!(sexp, Sexp::List(elems, _)
        if !elems.is_empty() && matches!(&elems[0], Sexp::Symbol(name, _) if name == "import"))
}

/// Check if the input consists only of comments (lines starting with `;`).
///
/// Returns true if every non-empty line in the input starts with `;`
/// (ignoring leading whitespace). This prevents comment-only input
/// from reaching the parser and producing an "empty input" error.
fn is_comment_only(input: &str) -> bool {
    input.lines().all(|line| {
        let trimmed = line.trim();
        trimmed.is_empty() || trimmed.starts_with(';')
    })
}

/// Check if parentheses and brackets are balanced in the input.
///
/// Ignores content in string literals and after `;` comment markers.
/// Tracks both `()` and `[]` depth so multi-line Vec literals are
/// not submitted prematurely.
fn parens_balanced(input: &str) -> bool {
    let mut paren_depth: i32 = 0;
    let mut bracket_depth: i32 = 0;
    let mut in_string = false;
    let mut in_comment = false;
    let mut prev_char = '\0';

    for ch in input.chars() {
        if in_comment {
            if ch == '\n' {
                in_comment = false;
            }
            prev_char = ch;
            continue;
        }

        match ch {
            ';' if !in_string => {
                in_comment = true;
            }
            '"' if prev_char != '\\' => in_string = !in_string,
            '(' if !in_string => paren_depth += 1,
            ')' if !in_string => paren_depth -= 1,
            '[' if !in_string => bracket_depth += 1,
            ']' if !in_string => bracket_depth -= 1,
            _ => {}
        }
        prev_char = ch;
    }

    paren_depth <= 0 && bracket_depth <= 0
}

// ---------------------------------------------------------------------------
// Slash command handlers
// ---------------------------------------------------------------------------

/// Handle `/sig <name>` — show type signature of a symbol.
fn handle_sig(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /sig <name>");
        return;
    }
    let module = session.tc.current_module_path().clone();
    match session.tc.symbol_table().get(name) {
        Some(entry) => {
            let display = format_entry_signature(entry, name, &module, &session.type_modules, &session.tc);
            let _ = writeln!(stdout, "{display}");
        }
        None => {
            let _ = writeln!(stdout, "error: unknown symbol '{name}'");
        }
    }
}

/// Handle `/doc <name>` — show docstring of a symbol (spec §11.2.4).
fn handle_doc(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /doc <name>");
        return;
    }
    match session.tc.symbol_table().get(name) {
        Some(ModuleEntry::Macro { docstring, .. }) => {
            if let Some(doc) = docstring {
                let _ = writeln!(stdout, "{name}: \"{doc}\"");
            } else {
                let _ = writeln!(stdout, "{name}: no docstring");
            }
        }
        Some(ModuleEntry::Def { docstring, .. }) => {
            if let Some(doc) = docstring {
                let _ = writeln!(stdout, "{name}: \"{doc}\"");
            } else {
                let _ = writeln!(stdout, "{name}: no docstring");
            }
        }
        Some(ModuleEntry::TraitDecl { decl, .. }) => {
            if let Some(doc) = &decl.docstring {
                let _ = writeln!(stdout, "{name}: \"{doc}\"");
            } else {
                let _ = writeln!(stdout, "{name}: no docstring");
            }
        }
        Some(_) => {
            let _ = writeln!(stdout, "{name}: no docstring");
        }
        None => {
            let _ = writeln!(stdout, "error: unknown symbol '{name}'");
        }
    }
}

/// Handle `/type <expr>` — show type of expression without evaluating.
fn handle_type(session: &mut ReplSession, expr_src: &str, stdout: &mut impl Write) {
    if expr_src.is_empty() {
        let _ = writeln!(stdout, "usage: /type <expr>");
        return;
    }
    // Parse, build AST, typecheck — but do NOT compile or execute.
    let snapshot = session.tc.snapshot();
    let result = typecheck_only(session, expr_src);
    // Always restore — we don't want /type to have side effects.
    session.tc.restore(snapshot);
    match result {
        Ok(ty) => {
            let display = format_type_qualified(&ty, &session.type_modules);
            let _ = writeln!(stdout, ":{display}");
        }
        Err(e) => {
            let _ = writeln!(stdout, "error: {e}");
        }
    }
}

/// Parse, expand, and typecheck an expression without compiling or executing.
fn typecheck_only(session: &mut ReplSession, expr_src: &str) -> Result<Type, CranelispError> {
    let sexps = cranelisp_frontend::parse(expr_src)?;
    if sexps.is_empty() {
        return Err(CranelispError::ParseError {
            message: "empty expression".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        });
    }
    let input = cranelisp_frontend::build_repl_input(&sexps[0], &mut session.expander)?;
    let check_result = session.tc.check_repl_input(&input)?;
    Ok(check_result.ty)
}

/// Handle `/info <name>` — show full details about a symbol (spec §3.5, §11.2.2).
fn handle_info(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /info <name>");
        return;
    }
    let module = session.tc.current_module_path().clone();
    match session.tc.symbol_table().get(name) {
        Some(entry) => {
            // Line 1: type signature (same as /sig).
            let sig = format_entry_signature(entry, name, &module, &session.type_modules, &session.tc);
            let _ = writeln!(stdout, "{sig}");
            // Line 2: for macros, show docstring; for functions, show code info.
            match entry {
                ModuleEntry::Macro { docstring, .. } => {
                    if let Some(doc) = docstring {
                        let _ = writeln!(stdout, "  \"{doc}\"");
                    }
                }
                _ => {
                    if let Some(dc) = session.got_state.def_codegen.get(name) {
                        let size_str = dc
                            .code_size
                            .map(|s| format!("{s} bytes"))
                            .unwrap_or_else(|| "? bytes".to_string());
                        let time_str = dc
                            .compile_duration
                            .map(|d| format!("{}ms", d.as_millis()))
                            .unwrap_or_else(|| "?ms".to_string());
                        let _ = writeln!(stdout, "  {size_str}, {time_str}");
                    }
                }
            }
        }
        None => {
            let _ = writeln!(stdout, "error: unknown symbol '{name}'");
        }
    }
}

/// Handle `/list [filter]` — list symbols in the current module by category.
///
/// Categories (spec §3.3): Types, Traits, Special forms, Macros, Functions, Imports.
/// Only shows names defined in the current module. Imported names appear
/// in the Imports category as a summary count per source module.
fn handle_list(session: &ReplSession, filter: &str, stdout: &mut impl Write) {
    let categories = classify_symbols(session, filter);
    print_categories(&categories, stdout);
}

/// Classified symbols for `/list` display.
struct ListCategories {
    types: Vec<String>,
    traits: Vec<String>,
    special_forms: Vec<String>,
    macros: Vec<String>,
    functions: Vec<String>,
    imports: HashMap<String, Vec<String>>,
}

/// Classify all symbols in the current module into `/list` categories.
fn classify_symbols(session: &ReplSession, filter: &str) -> ListCategories {
    let module = session.tc.current_module_path().clone();
    let table = session.tc.symbol_table();

    let mut cats = ListCategories {
        types: Vec::new(),
        traits: Vec::new(),
        special_forms: Vec::new(),
        macros: Vec::new(),
        functions: Vec::new(),
        imports: HashMap::new(),
    };

    for (sym, entry) in table.all_symbols() {
        if matches!(entry, ModuleEntry::Constructor { .. }) {
            continue;
        }

        let name = sym.to_string();
        if !filter.is_empty() && !name.to_lowercase().contains(&filter.to_lowercase()) {
            continue;
        }

        match entry {
            ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                cats.imports
                    .entry(source.module.to_string())
                    .or_default()
                    .push(name);
            }
            ModuleEntry::TypeDef { .. } => {
                cats.types.push(format!("{module}/{name}"));
            }
            ModuleEntry::TraitDecl { .. } => {
                let defining = session.tc.defining_module_for(&name);
                cats.traits.push(format!("{defining}/{name}"));
            }
            ModuleEntry::Macro { .. } => {
                cats.macros.push(name);
            }
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::SpecialForm { .. } => {
                    cats.special_forms.push(name);
                }
                DefKind::Primitive { .. } => {} // skip — belongs in primitives module
                _ => {
                    // Skip internal macro implementation functions (e.g. __macro_twice_clause_0)
                    if !name.starts_with("__macro_") {
                        cats.functions.push(format!("{module}/{name}"));
                    }
                }
            },
            _ => {}
        }
    }

    cats.types.sort();
    cats.traits.sort();
    cats.special_forms.sort();
    cats.macros.sort();
    cats.functions.sort();
    cats
}

/// Print classified symbols to stdout in `/list` format.
fn print_categories(cats: &ListCategories, stdout: &mut impl Write) {
    let print_section = |name: &str, items: &[String], out: &mut dyn Write| {
        if !items.is_empty() {
            let _ = writeln!(out, "{name}:");
            for item in items {
                let _ = writeln!(out, "  {item}");
            }
        }
    };

    print_section("Types", &cats.types, stdout);
    print_section("Traits", &cats.traits, stdout);
    print_section("Special forms", &cats.special_forms, stdout);
    print_section("Macros", &cats.macros, stdout);
    print_section("Functions", &cats.functions, stdout);

    if !cats.imports.is_empty() {
        let _ = writeln!(stdout, "Imports:");
        let mut sorted_modules: Vec<_> = cats.imports.keys().cloned().collect();
        sorted_modules.sort();
        for mod_name in &sorted_modules {
            let names = cats.imports.get(mod_name).map(|v| v.as_slice()).unwrap_or(&[]);
            let count = names.len();
            if count <= 5 {
                let mut sorted_names: Vec<_> = names.to_vec();
                sorted_names.sort();
                let _ = writeln!(
                    stdout,
                    "  {mod_name} ({count} names: {})",
                    sorted_names.join(", ")
                );
            } else {
                let _ = writeln!(stdout, "  {mod_name} ({count} names)");
            }
        }
    }
}

/// Handle `/time <expr>` — evaluate with timing breakdown.
fn handle_time(
    session: &mut ReplSession,
    expr_src: &str,
) -> Result<String, CranelispError> {
    if expr_src.is_empty() {
        return Ok("usage: /time <expr>".to_string());
    }
    let total_start = Instant::now();
    let result = session.eval(expr_src)?;
    let total_elapsed = total_start.elapsed();

    // Compile time = total minus eval (function call) time.
    let compile_duration = total_elapsed.saturating_sub(result.eval_duration);
    let compile_ms = compile_duration.as_millis();
    let eval_ms = result.eval_duration.as_millis();

    // Format the result value.
    let display = if let Some(ref def_display) = result.definition_display {
        def_display.clone()
    } else {
        format_result_value(
            result.value,
            &result.ty,
            session.type_defs(),
            session.type_modules(),
        )
    };
    Ok(format!("{display} (compile: {compile_ms}ms, eval: {eval_ms}ms)"))
}

/// Handle `/expand <form>` — macro-expand a form without evaluating (spec §11.1).
fn handle_expand(session: &mut ReplSession, form_src: &str, stdout: &mut impl Write) {
    if form_src.is_empty() {
        let _ = writeln!(stdout, "usage: /expand <form>");
        return;
    }
    match expand_form(session, form_src) {
        Ok(expanded) => {
            let _ = writeln!(stdout, "{expanded}");
        }
        Err(e) => {
            let _ = writeln!(stdout, "error: {e}");
        }
    }
}

/// Parse and expand a form through the session's macro expander.
///
/// Does not evaluate the result. Returns the expanded Sexp as a formatted string.
fn expand_form(session: &mut ReplSession, form_src: &str) -> Result<String, CranelispError> {
    let sexps = cranelisp_frontend::parse(form_src)?;
    if sexps.is_empty() {
        return Err(CranelispError::ParseError {
            message: "empty form".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        });
    }
    let expanded = session.expander.expand_sexp(sexps.into_iter().next().ok_or_else(|| {
        CranelispError::ParseError {
            message: "empty form".into(),
            span: cranelisp_types::Span::SYNTHETIC,
        }
    })?)?;
    Ok(format_sexp(&expanded))
}

/// Format an S-expression as a readable string.
///
/// Produces valid S-expression syntax: symbols, integers, floats, booleans,
/// strings (quoted), lists (parenthesized), and brackets (square).
fn format_sexp(sexp: &Sexp) -> String {
    match sexp {
        Sexp::Symbol(name, _) => name.clone(),
        Sexp::Int(n, _) => format!("{n}"),
        Sexp::Float(v, _) => {
            let s = format!("{v}");
            if s.contains('.') { s } else { format!("{s}.0") }
        }
        Sexp::Bool(b, _) => format!("{b}"),
        Sexp::Str(s, _) => format!("\"{s}\""),
        Sexp::List(children, _) => {
            let parts: Vec<String> = children.iter().map(format_sexp).collect();
            format!("({})", parts.join(" "))
        }
        Sexp::Bracket(children, _) => {
            let parts: Vec<String> = children.iter().map(format_sexp).collect();
            format!("[{}]", parts.join(" "))
        }
    }
}

/// Handle `/imports [module]` — show imports in current module (spec §3.4).
///
/// Groups imported names by source module. Optional filter narrows to one
/// source module (exact match). Empty output for no imports or unknown module.
fn handle_imports(session: &ReplSession, filter: &str, stdout: &mut impl Write) {
    let table = session.tc.symbol_table();

    // Collect imports grouped by source module.
    let mut imports: HashMap<String, Vec<(String, String)>> = HashMap::new();
    for (sym, entry) in table.all_symbols() {
        if let ModuleEntry::Import { source } = entry {
            let source_mod = source.module.to_string();
            // Apply module filter if provided.
            if !filter.is_empty() && source_mod != filter {
                continue;
            }
            // Look up the type signature of the imported symbol in the source module.
            let type_sig = lookup_import_type(session, source);
            imports
                .entry(source_mod)
                .or_default()
                .push((sym.to_string(), type_sig));
        }
    }

    // Display grouped by source module, sorted.
    let mut sorted_modules: Vec<_> = imports.keys().cloned().collect();
    sorted_modules.sort();
    for mod_name in &sorted_modules {
        let _ = writeln!(stdout, "From {mod_name}:");
        if let Some(names) = imports.get(mod_name) {
            let mut sorted = names.clone();
            sorted.sort_by(|a, b| a.0.cmp(&b.0));
            for (name, sig) in &sorted {
                let _ = writeln!(stdout, "  {name} :: {sig}");
            }
        }
    }
}

/// Look up the type signature for an imported symbol.
fn lookup_import_type(
    session: &ReplSession,
    source: &cranelisp_types::FQSymbol,
) -> String {
    // Try to find the entry in the source module's symbol table.
    if let Some(table) = session.tc.module_table(&source.module) {
        if let Some(entry) = table.get(source.symbol.as_ref()) {
            return format_import_type_sig(entry, &session.type_modules);
        }
    }
    // Fallback: unknown type.
    "?".to_string()
}

/// Format the type signature of an imported module entry.
fn format_import_type_sig(
    entry: &ModuleEntry,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
) -> String {
    match entry {
        ModuleEntry::Def { scheme, .. } => {
            format_type_qualified(&scheme.ty, type_modules)
        }
        ModuleEntry::Constructor { scheme, .. } => {
            format_type_qualified(&scheme.ty, type_modules)
        }
        ModuleEntry::TypeDef { info, .. } => {
            qualify_type_name(&info.name, type_modules)
        }
        ModuleEntry::TraitDecl { decl, .. } => {
            format!("trait {}", decl.name)
        }
        ModuleEntry::Macro { name, clauses, .. } => {
            if clauses.len() <= 1 {
                format!("{name} :: macro")
            } else {
                format!("{name} :: macro ({} clauses)", clauses.len())
            }
        }
        _ => "?".to_string(),
    }
}

/// Format a module entry's type signature for /sig and /info display.
///
/// Handles functions, constructors, types, traits, and macros (spec §11.2.3).
fn format_entry_signature(
    entry: &ModuleEntry,
    name: &str,
    module: &ModuleFullPath,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
    tc: &cranelisp_typecheck::TypeChecker,
) -> String {
    match entry {
        ModuleEntry::Def {
            scheme,
            kind,
            ..
        } => {
            if let DefKind::SpecialForm { description } = kind.as_ref() {
                return format_special_form_display(name, description);
            }
            if !scheme.constraints.is_empty() {
                format_scheme_display(name, scheme, module, type_modules)
            } else {
                let type_str = format_type_qualified(&scheme.ty, type_modules);
                format!(":{type_str} {module}/{name}")
            }
        }
        ModuleEntry::Constructor {
            type_name, scheme, ..
        } => {
            let type_str = format_type_qualified(&scheme.ty, type_modules);
            let tn = TypeName::from(type_name.0.as_str());
            let ctor_display = if let Some(info) = tc.type_def_registry().get(&tn) {
                format_ctor_display(&tn, name, info)
            } else {
                format!("{type_name}.{name}")
            };
            format!(":{type_str} {module}/{ctor_display}")
        }
        ModuleEntry::TypeDef { info, .. } => {
            let qname = qualify_type_name(&info.name, type_modules);
            format!(":{qname}")
        }
        ModuleEntry::TraitDecl { decl, .. } => {
            let defining = tc.defining_module_for(decl.name.as_ref());
            format!("trait {defining}/{}", decl.name)
        }
        ModuleEntry::Macro { clauses, .. } => {
            format_macro_signature(name, clauses)
        }
        _ => format!("{module}/{name}"),
    }
}

/// Format a macro's signature for /sig and bare symbol display (spec §11.2.3).
///
/// Single clause: `name :: macro [param1 param2]`
/// Multi-clause:  `name :: macro (N clauses)\n  [param1 param2]\n  [param1 & rest]`
fn format_macro_signature(name: &str, clauses: &[MacroClauseInfo]) -> String {
    if clauses.len() == 1 {
        let params = format_macro_clause_params(&clauses[0]);
        format!("{name} :: macro {params}")
    } else {
        let mut lines = vec![format!(
            "{name} :: macro ({} clauses)",
            clauses.len()
        )];
        for clause in clauses {
            let params = format_macro_clause_params(clause);
            lines.push(format!("  {params}"));
        }
        lines.join("\n")
    }
}

/// Format a single macro clause's parameter list.
///
/// Uses `& rest` syntax for variadic and bracket notation for destructuring.
fn format_macro_clause_params(clause: &MacroClauseInfo) -> String {
    let mut parts = Vec::new();
    for param in &clause.params {
        match param {
            MacroParam::Name(name) => {
                parts.push(name.to_string());
            }
            MacroParam::Bracket { fixed, rest } => {
                let mut inner = Vec::new();
                for f in fixed {
                    inner.push(f.to_string());
                }
                if let Some(r) = rest {
                    inner.push(format!("& {r}"));
                }
                parts.push(format!("[{}]", inner.join(" ")));
            }
        }
    }
    if let Some(rest) = &clause.rest_param {
        parts.push(format!("& {rest}"));
    }
    format!("[{}]", parts.join(" "))
}

/// Format a special form for display (spec §4.2).
///
/// Produces a function-like signature that teaches the user the form's shape.
fn format_special_form_display(name: &str, description: &str) -> String {
    match name {
        "if" => ":(Fn [primitives/Bool a a] a) if".to_string(),
        "let" => ":(Fn [bindings body] a) let".to_string(),
        "fn" => ":(Fn [params body] function) fn".to_string(),
        "defn" => ":(Fn [name params body] function) defn".to_string(),
        "deftype" => ":(Fn [name ctors...] type) deftype".to_string(),
        "match" => ":(Fn [expr [pat body]...] a) match".to_string(),
        "defmacro" => ":(Fn [name params body] macro) defmacro".to_string(),
        _ => format!("{name} — {description}"),
    }
}

/// Check if the trimmed input is a bare symbol name and return its display.
///
/// Handles special forms, primitive types, functions, constructors, traits,
/// and macros (spec §4.1, §11.4). Returns `Some(display_string)` if the
/// input matches a known symbol, `None` otherwise.
///
/// When a symbol has a docstring, the first line is appended as a comment
/// (spec §4.1): `:(Fn [Int] Int) user/double ; Multiply by 2`
fn special_form_feedback(input: &str, session: &ReplSession) -> Option<String> {
    let trimmed = input.trim();
    // Must be a single bare identifier (no parens, no spaces, no brackets).
    if trimmed.contains(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']') {
        return None;
    }
    if trimmed.is_empty() {
        return None;
    }
    // Check primitive type names: Int, Bool, Float, String (spec §4.1).
    // These live in the `primitives` synthetic module but are not bare names
    // in the user module's symbol table, so we check before the lookup.
    if Type::from_name(trimmed).is_some() {
        return Some(format!(":primitives/{trimmed}"));
    }

    // Look up in the symbol table (spec §4.1 — bare symbol lookup).
    let module = session.tc.current_module_path();
    let entry = session.tc.symbol_table().get(trimmed)?;
    match entry {
        ModuleEntry::Def { kind, scheme, docstring, .. } => {
            if let DefKind::SpecialForm { description } = kind.as_ref() {
                Some(format_special_form_display(trimmed, description))
            } else {
                // Regular function/primitive: show `:TypeScheme module/name`
                let type_str = format_type_qualified(&scheme.ty, &session.type_modules);
                let base = format!(":{type_str} {module}/{trimmed}");
                Some(append_docstring_comment(base, docstring.as_deref()))
            }
        }
        ModuleEntry::TypeDef { .. } => {
            // Bare type name: show `:module/TypeName`
            Some(format!(":{module}/{trimmed}"))
        }
        ModuleEntry::TraitDecl { .. } => {
            // Bare trait name: show `:defining_module/TraitName`
            let defining_module = session.tc.defining_module_for(trimmed);
            Some(format!(":{defining_module}/{trimmed}"))
        }
        ModuleEntry::Constructor { type_name, scheme, .. } => {
            // Bare constructor: show `:QualifiedType module/Type.Ctor`
            // For single-constructor types where ctor name matches type name,
            // suppress the `Type.` prefix: `module/Ctor` instead of `module/Type.Ctor`.
            let type_str = format_type_qualified(&scheme.ty, &session.type_modules);
            let tn = TypeName::from(type_name.0.as_str());
            let ctor_display = if let Some(info) = session.type_defs().get(&tn) {
                format_ctor_display(&tn, trimmed, info)
            } else {
                format!("{type_name}.{trimmed}")
            };
            Some(format!(":{type_str} {module}/{ctor_display}"))
        }
        ModuleEntry::Macro { clauses, docstring, .. } => {
            // Bare macro name: show clause signatures (spec §11.4).
            // Zero-arg macros expand immediately via bare-symbol expansion,
            // so they won't reach here (the expander handles them first).
            let base = format_macro_signature(trimmed, clauses);
            Some(append_docstring_comment(base, docstring.as_deref()))
        }
        _ => None,
    }
}

/// Append the first line of a docstring as a ` ; comment` suffix.
///
/// Used by bare symbol display (spec §4.1) to show a brief description
/// after the type/name display.
fn append_docstring_comment(base: String, docstring: Option<&str>) -> String {
    match docstring {
        Some(doc) if !doc.is_empty() => {
            let first_line = doc.lines().next().unwrap_or("");
            if first_line.is_empty() {
                base
            } else {
                format!("{base} ; {first_line}")
            }
        }
        _ => base,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_result_int() {
        assert_eq!(format_result(42, &Type::Int), ":primitives/Int 42");
    }

    #[test]
    fn test_format_result_bool_true() {
        assert_eq!(format_result(1, &Type::Bool), ":primitives/Bool true");
    }

    #[test]
    fn test_format_result_bool_false() {
        assert_eq!(format_result(0, &Type::Bool), ":primitives/Bool false");
    }

    #[test]
    fn test_format_result_float() {
        let bits = 1.234_f64.to_bits() as i64;
        let result = format_result(bits, &Type::Float);
        assert!(result.starts_with(":primitives/Float 1.234"));

        // Whole-number floats must display with `.0` suffix (spec §1.2).
        let whole_bits = 5.0_f64.to_bits() as i64;
        assert_eq!(
            format_result(whole_bits, &Type::Float),
            ":primitives/Float 5.0"
        );

        let zero_bits = 0.0_f64.to_bits() as i64;
        assert_eq!(
            format_result(zero_bits, &Type::Float),
            ":primitives/Float 0.0"
        );
    }

    #[test]
    fn test_parens_balanced_simple() {
        assert!(parens_balanced("(+ 1 2)"));
        assert!(!parens_balanced("(+ 1 2"));
        assert!(parens_balanced("42"));
    }

    #[test]
    fn test_parens_balanced_nested() {
        assert!(parens_balanced("(defn main [] (+ 1 2))"));
        assert!(!parens_balanced("(defn main [] (+ 1 2)"));
    }

    #[test]
    fn test_parens_balanced_string() {
        assert!(parens_balanced("\"hello (world\""));
    }

    #[test]
    fn test_brackets_balanced() {
        assert!(parens_balanced("[1 2 3]"));
        assert!(!parens_balanced("[1 2"));
        assert!(parens_balanced("(vec-get [1 2 3] 0)"));
        assert!(!parens_balanced("(vec-get [1 2 3"));
        // Multi-line Vec literal
        assert!(!parens_balanced("[1 2\n"));
        assert!(parens_balanced("[1 2\n 3]"));
    }

    #[test]
    fn test_is_comment_only() {
        assert!(is_comment_only("; a comment"));
        assert!(is_comment_only("  ; indented comment"));
        assert!(is_comment_only("; line one\n; line two"));
        assert!(is_comment_only(""));
        assert!(is_comment_only("   "));
        assert!(!is_comment_only("42"));
        assert!(!is_comment_only("(+ 1 2) ; trailing comment"));
        assert!(!is_comment_only("; comment\n42"));
    }

    #[test]
    fn test_session_eval_empty_input() {
        let mut session = ReplSession::new();
        let result = session.eval("").unwrap();
        assert_eq!(result.value, 0);
    }

    #[test]
    fn test_session_eval_comment_only() {
        let mut session = ReplSession::new();
        let result = session.eval("; just a comment").unwrap();
        assert_eq!(result.value, 0);
        // Session still works.
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
    }

    #[test]
    fn test_session_eval_int() {
        let mut session = ReplSession::new();
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    #[test]
    fn test_session_error_recovery() {
        let mut session = ReplSession::new();
        // This should error (parse error).
        let err = session.eval("(+ 1");
        assert!(err.is_err());
        // Session should still work after error.
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
    }

    // --- Ring 1 format tests ---

    #[test]
    fn test_format_result_string() {
        let s = cranelisp_runtime::alloc_string(b"hello") as i64;
        let result = format_result(s, &Type::String);
        assert_eq!(result, ":primitives/String \"hello\"");
        cranelisp_runtime::heap_dealloc(s);
    }

    #[test]
    fn test_format_result_empty_string() {
        let s = cranelisp_runtime::alloc_string(b"") as i64;
        let result = format_result(s, &Type::String);
        assert_eq!(result, ":primitives/String \"\"");
        cranelisp_runtime::heap_dealloc(s);
    }

    #[test]
    fn test_format_result_fn_type() {
        let fn_ty = Type::Fn(vec![Type::Int, Type::Bool], Box::new(Type::String));
        let result = format_result(0, &fn_ty);
        assert_eq!(result, ":(Fn [primitives/Int primitives/Bool] primitives/String) <closure>");
    }

    #[test]
    fn test_format_result_adt_nullary_with_type_defs() {
        use cranelisp_types::{ConstructorInfo, TypeDefInfo};

        let type_name = TypeName::from("Color");
        let mut type_defs = HashMap::new();
        type_defs.insert(
            type_name.clone(),
            TypeDefInfo {
                name: type_name.clone(),
                type_params: vec![],
                constructors: vec![
                    ConstructorInfo {
                        name: Symbol::from("Red"),
                        tag: 0,
                        fields: vec![],
                        docstring: None,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Green"),
                        tag: 1,
                        fields: vec![],
                        docstring: None,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Blue"),
                        tag: 2,
                        fields: vec![],
                        docstring: None,
                    },
                ],
                docstring: None,
            },
        );

        let adt = Type::ADT(type_name, vec![]);
        let tm = HashMap::new();
        assert_eq!(
            format_result_value(0, &adt, &type_defs, &tm),
            ":Color Color.Red"
        );
        assert_eq!(
            format_result_value(1, &adt, &type_defs, &tm),
            ":Color Color.Green"
        );
        assert_eq!(
            format_result_value(2, &adt, &type_defs, &tm),
            ":Color Color.Blue"
        );
    }

    #[test]
    fn test_format_result_adt_data_constructor() {
        use cranelisp_types::{ConstructorInfo, FieldInfo, TypeDefInfo};

        let type_name = TypeName::from("Option");
        let mut type_defs = HashMap::new();
        type_defs.insert(
            type_name.clone(),
            TypeDefInfo {
                name: type_name.clone(),
                type_params: vec![],
                constructors: vec![
                    ConstructorInfo {
                        name: Symbol::from("None"),
                        tag: 0,
                        fields: vec![],
                        docstring: None,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Some"),
                        tag: 1,
                        fields: vec![FieldInfo {
                            name: Symbol::from("val"),
                            ty: Type::Int,
                        }],
                        docstring: None,
                    },
                ],
                docstring: None,
            },
        );

        let adt = Type::ADT(type_name.clone(), vec![Type::Int]);
        let tm = HashMap::new();

        // Nullary: None (tag 0) — dot notation.
        assert_eq!(
            format_result_value(0, &adt, &type_defs, &tm),
            ":(Option primitives/Int) Option.None"
        );

        // Data constructor: allocate Some(42) on heap.
        // Payload = tag (8 bytes) + 1 field (8 bytes) = 16 bytes.
        let ptr = cranelisp_runtime::alloc_with_rc(16);
        unsafe {
            *(ptr.add(16) as *mut i64) = 1; // tag = 1 (Some)
            *(ptr.add(24) as *mut i64) = 42; // field val = 42
        }

        // Data constructor — dot notation: (Option.Some 42).
        assert_eq!(
            format_result_value(ptr as i64, &adt, &type_defs, &tm),
            ":(Option primitives/Int) (Option.Some 42)"
        );

        cranelisp_runtime::heap_dealloc(ptr as i64);
    }

    #[test]
    fn test_format_result_adt_no_type_defs() {
        // Without type_defs, falls back to bare value display.
        let adt = Type::ADT(TypeName::from("Color"), vec![]);
        assert_eq!(format_result(0, &adt), ":Color 0");
    }

    #[test]
    fn test_format_type_display_fn() {
        use cranelisp_types::format_type_display;
        let fn1 = Type::Fn(vec![Type::Int], Box::new(Type::Bool));
        assert_eq!(format_type_display(&fn1), "(Fn [Int] Bool)");

        let fn2 = Type::Fn(vec![Type::Int, Type::String], Box::new(Type::Float));
        assert_eq!(format_type_display(&fn2), "(Fn [Int String] Float)");

        let fn3 = Type::Fn(vec![], Box::new(Type::Int));
        assert_eq!(format_type_display(&fn3), "(Fn [] Int)");
    }

    #[test]
    fn test_format_adt_type_qualified() {
        let tm = HashMap::new();
        assert_eq!(
            format_adt_type_qualified(&TypeName::from("Color"), &[], &tm),
            "Color"
        );
        assert_eq!(
            format_adt_type_qualified(&TypeName::from("Option"), &[Type::Int], &tm),
            "(Option primitives/Int)"
        );
        // With type_modules, ADT name gets qualified too.
        let mut tm2 = HashMap::new();
        tm2.insert(
            TypeName::from("Color"),
            ModuleFullPath::from("user"),
        );
        assert_eq!(
            format_adt_type_qualified(&TypeName::from("Color"), &[], &tm2),
            "user/Color"
        );
    }

    // --- Macro integration tests ---

    // spec: 09-macros.md §9.2 — defmacro in REPL
    #[test]
    fn test_repl_defmacro_and_use() {
        let mut session = ReplSession::new();

        // Define a macro.
        let result = session.eval("(defmacro id [x] x)").unwrap();
        assert!(result.is_definition);
        assert!(result.definition_display.is_some());

        // Use the macro.
        let result = session.eval("(id 42)").unwrap();
        assert_eq!(result.value, 42);
        assert_eq!(result.ty, Type::Int);
    }

    // spec: 09-macros.md §9.4.2 — quasiquote macro in REPL
    #[test]
    fn test_repl_defmacro_quasiquote() {
        let mut session = ReplSession::new();

        session.eval("(defmacro inc1 [x] `(add-i64 1 ~x))").unwrap();

        let result = session.eval("(inc1 41)").unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 09-macros.md §9.2 — macro accumulates across evals
    #[test]
    fn test_repl_macro_persists() {
        let mut session = ReplSession::new();

        session.eval("(defmacro id [x] x)").unwrap();

        // First use.
        let r1 = session.eval("(id 10)").unwrap();
        assert_eq!(r1.value, 10);

        // Second use — macro is still registered.
        let r2 = session.eval("(id 20)").unwrap();
        assert_eq!(r2.value, 20);
    }

    // spec: 09-macros.md §9.2 — error recovery does not corrupt expander
    #[test]
    fn test_repl_macro_error_recovery() {
        let mut session = ReplSession::new();

        // Define a macro.
        session.eval("(defmacro id [x] x)").unwrap();

        // Cause an error (type error after macro expansion).
        let err = session.eval("(id (add-i64 true 2))");
        assert!(err.is_err());

        // Macro should still work after error.
        let result = session.eval("(id 42)").unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 09-macros.md — session without macros still works
    #[test]
    fn test_repl_no_macros_unchanged() {
        let mut session = ReplSession::new();
        let result = session.eval("(add-i64 1 2)").unwrap();
        assert_eq!(result.value, 3);
    }

    // spec: 09-macros.md §9.2 — macro in defn body
    #[test]
    fn test_repl_macro_in_defn_body() {
        let mut session = ReplSession::new();

        session.eval("(defmacro id [x] x)").unwrap();

        // Define a function that uses the macro.
        session.eval("(defn f [] (id 77))").unwrap();

        // Call the function.
        let result = session.eval("(f)").unwrap();
        assert_eq!(result.value, 77);
    }

    // spec: 08-modules.md — REPL prelude loading
    #[test]
    fn test_repl_with_prelude() {
        let dir = tempfile::tempdir().unwrap();
        let lib_dir = dir.path().join("lib");
        std::fs::create_dir_all(&lib_dir).unwrap();
        std::fs::write(
            lib_dir.join("prelude.cl"),
            "(defmacro id [x] x)",
        )
        .unwrap();

        let session = ReplSession::new_with_prelude(
            dir.path(),
            &[lib_dir.clone()],
        )
        .unwrap();

        // Verify the macro from the prelude is available.
        let mut session = session;
        let result = session.eval("(id 42)").unwrap();
        assert_eq!(result.value, 42);
    }

    // spec: 08-modules.md — REPL without prelude still works
    #[test]
    fn test_repl_without_prelude() {
        let dir = tempfile::tempdir().unwrap();

        // No prelude.cl anywhere — should succeed with empty prelude.
        let session = ReplSession::new_with_prelude(
            dir.path(),
            &[],
        )
        .unwrap();

        let mut session = session;
        let result = session.eval("42").unwrap();
        assert_eq!(result.value, 42);
    }
}
