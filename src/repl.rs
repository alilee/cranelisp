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

use std::collections::HashMap;
use std::io::{self, BufRead, Write};

use cranelisp_backend::got::ModuleCodegenState;
use cranelisp_backend::heap::{HeapAdt, HeapVec};
use cranelisp_backend::jit::Jit;
use cranelisp_typecheck::TypeChecker;
use cranelisp_types::{
    CompileMode, CranelispError, DefKind, ModuleEntry, ModuleFullPath, NoOpExpander,
    ReplCheckResult, ReplInput, Symbol, Type, TypeDefInfo, TypeName, Warning,
    NULLARY_TAG_THRESHOLD,
};

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
}

/// Persistent REPL session state.
pub struct ReplSession {
    /// Type checker state (persists across inputs).
    pub tc: TypeChecker,
    /// Backend GOT state (persists across inputs for function redefinition).
    pub got_state: ModuleCodegenState,
    /// JIT instances that must stay alive (their code is referenced via GOT).
    /// Each defn compilation creates a new JIT; we keep them alive here.
    jit_modules: Vec<Jit>,
    /// Accumulated type definitions from all inputs (for ADT value display).
    type_defs: HashMap<TypeName, TypeDefInfo>,
    /// Maps type names to the module they were defined in (for qualified display).
    type_modules: HashMap<TypeName, ModuleFullPath>,
}

impl ReplSession {
    /// Create a new REPL session.
    pub fn new() -> Self {
        ReplSession {
            tc: TypeChecker::new(),
            got_state: ModuleCodegenState::new(),
            jit_modules: Vec::new(),
            type_defs: HashMap::new(),
            type_modules: HashMap::new(),
        }
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
            });
        }

        // Parse the source into sexps.
        let sexps = cranelisp_frontend::parse(source)?;

        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty input".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            });
        }

        // Build REPL input from the first sexp.
        let mut expander = NoOpExpander;
        let input = cranelisp_frontend::build_repl_input(&sexps[0], &mut expander)?;

        // Snapshot for error recovery.
        let snapshot = self.tc.snapshot();

        // Type check the input.
        let check_result = match self.tc.check_repl_input(&input) {
            Ok(r) => r,
            Err(e) => {
                self.tc.restore(snapshot);
                return Err(e);
            }
        };

        // Compile and execute.
        match self.compile_and_execute(&input, &check_result) {
            Ok(result) => Ok(result),
            Err(e) => {
                self.tc.restore(snapshot);
                Err(e)
            }
        }
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

        let value = cranelisp_backend::compile_and_run_expr_with_got(
            expr,
            &check,
            CompileMode::Interactive,
            Some(&mut self.got_state),
        )?;
        Ok(ReplResult {
            value,
            ty: check_result.ty.clone(),
            is_definition: false,
            warnings: check_result.warnings.clone(),
            definition_display: None,
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
        let value = if defn.params.is_empty() && !is_constrained {
            let entry = self.got_state.def_codegen.get(defn.name.as_ref());
            let code_ptr = entry
                .and_then(|e| e.code_ptr)
                .ok_or_else(|| CranelispError::CodegenError {
                    message: format!("no code pointer after compiling defn '{}'", defn.name),
                    span: cranelisp_types::Span::SYNTHETIC,
                })?;
            let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
            func()
        } else {
            0
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

/// Format an ADT value with constructor name lookup and dot notation (spec §1.5).
///
/// Nullary constructors display as `Type.Ctor` (e.g., `Color.Red`).
/// Data constructors display as `(Type.Ctor field1 field2)` (e.g., `(Option.Some 42)`).
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
        // Dot notation: Type.Constructor (spec §1.5).
        format!(":{type_display} {type_name}.{ctor_name}")
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
/// Uses `Type.Constructor` dot notation per spec §1.5.
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
        // Dot notation: Type.Constructor (spec §1.5).
        return format!(":{type_display} {type_name}.{}", ctor.name);
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
    // Dot notation: (Type.Constructor fields...) (spec §1.5).
    format!(":{type_display} ({type_name}.{} {fields_display})", ctor.name)
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
                    // Dot notation: Type.Constructor (spec §1.5).
                    format!("{name}.{ctor_name}")
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

/// Parsed REPL slash command.
enum ReplCommand<'a> {
    Help,
    Quit,
    Sig(&'a str),
    Type(&'a str),
    Info(&'a str),
    List(&'a str),
    Time(&'a str),
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
        "/type" | "/t" => ReplCommand::Type(arg),
        "/info" | "/i" => ReplCommand::Info(arg),
        "/list" | "/l" => ReplCommand::List(arg),
        "/time" => ReplCommand::Time(arg),
        _ => ReplCommand::Unknown(cmd),
    })
}

/// Print the /help command output to stdout.
fn print_help(stdout: &mut impl Write) {
    let _ = writeln!(stdout, "Available commands:");
    let _ = writeln!(stdout, "  /help (/h)          Show this help");
    let _ = writeln!(stdout, "  /quit (/q)          Exit REPL");
    let _ = writeln!(stdout, "  /sig (/s) NAME      Show type signature");
    let _ = writeln!(stdout, "  /type (/t) EXPR     Show type without evaluating");
    let _ = writeln!(stdout, "  /info (/i) NAME     Show full details");
    let _ = writeln!(stdout, "  /list (/l) [FILTER] List symbols in current module");
    let _ = writeln!(stdout, "  /time EXPR          Evaluate with timing breakdown");
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
    let compile_start = std::time::Instant::now();
    match session.eval(input) {
        Ok(result) => {
            let compile_elapsed = compile_start.elapsed();
            let compile_ms = compile_elapsed.as_millis() as u64;

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
            (compile_ms, 0)
        }
        Err(e) => {
            let compile_elapsed = compile_start.elapsed();
            let compile_ms = compile_elapsed.as_millis() as u64;
            let _ = writeln!(stdout, "error: {e}");
            (compile_ms, 0)
        }
    }
}

/// Run the interactive REPL loop.
///
/// Reads lines from stdin, evaluates them, prints results.
/// Errors are printed without crashing the session.
pub fn run_repl() {
    let mut session = ReplSession::new();
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

/// Handle `/type <expr>` — show type of expression without evaluating.
fn handle_type(session: &mut ReplSession, expr_src: &str, stdout: &mut impl Write) {
    if expr_src.is_empty() {
        let _ = writeln!(stdout, "usage: /type <expr>");
        return;
    }
    // Parse, build AST, typecheck — but do NOT compile or execute.
    let snapshot = session.tc.snapshot();
    let result = (|| -> Result<Type, CranelispError> {
        let sexps = cranelisp_frontend::parse(expr_src)?;
        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty expression".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            });
        }
        let mut expander = NoOpExpander;
        let input = cranelisp_frontend::build_repl_input(&sexps[0], &mut expander)?;
        let check_result = session.tc.check_repl_input(&input)?;
        Ok(check_result.ty)
    })();
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

/// Handle `/info <name>` — show full details about a symbol.
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
            // Line 2: code size and compile time (if available).
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
        None => {
            let _ = writeln!(stdout, "error: unknown symbol '{name}'");
        }
    }
}

/// Handle `/list [filter]` — list symbols in the current module by category.
fn handle_list(session: &ReplSession, filter: &str, stdout: &mut impl Write) {
    let module = session.tc.current_module_path().clone();
    let table = session.tc.symbol_table();

    let mut types: Vec<String> = Vec::new();
    let mut traits: Vec<String> = Vec::new();
    let mut special_forms: Vec<String> = Vec::new();
    let mut functions: Vec<String> = Vec::new();

    for (sym, entry) in table.all_symbols() {
        // Skip constructors — they are listed under their type.
        if matches!(entry, ModuleEntry::Constructor { .. }) {
            continue;
        }
        // Skip imports and reexports for now (they clutter the listing).
        if matches!(entry, ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. }) {
            continue;
        }

        let name = sym.to_string();
        // Apply filter if provided.
        if !filter.is_empty() && !name.contains(filter) {
            continue;
        }

        match entry {
            ModuleEntry::TypeDef { .. } => {
                types.push(format!("{module}/{name}"));
            }
            ModuleEntry::TraitDecl { .. } => {
                let defining = session.tc.defining_module_for(&name);
                traits.push(format!("{defining}/{name}"));
            }
            ModuleEntry::Def { kind, .. } => match kind.as_ref() {
                DefKind::SpecialForm { .. } => {
                    special_forms.push(name);
                }
                _ => {
                    functions.push(format!("{module}/{name}"));
                }
            },
            _ => {}
        }
    }

    // Sort each category for deterministic output.
    types.sort();
    traits.sort();
    special_forms.sort();
    functions.sort();

    if !types.is_empty() {
        let _ = writeln!(stdout, "Types:");
        for t in &types {
            let _ = writeln!(stdout, "  {t}");
        }
    }
    if !traits.is_empty() {
        let _ = writeln!(stdout, "Traits:");
        for t in &traits {
            let _ = writeln!(stdout, "  {t}");
        }
    }
    if !special_forms.is_empty() {
        let _ = writeln!(stdout, "Special forms:");
        for sf in &special_forms {
            let _ = writeln!(stdout, "  {sf}");
        }
    }
    if !functions.is_empty() {
        let _ = writeln!(stdout, "Functions:");
        for f in &functions {
            let _ = writeln!(stdout, "  {f}");
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
    let compile_start = std::time::Instant::now();
    let result = session.eval(expr_src)?;
    let compile_elapsed = compile_start.elapsed();
    let compile_ms = compile_elapsed.as_millis();

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
    Ok(format!("{display} (compile: {compile_ms}ms, eval: 0ms)"))
}

/// Format a module entry's type signature for /sig and /info display.
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
            format!(":{type_str} {module}/{type_name}.{name}")
        }
        ModuleEntry::TypeDef { info, .. } => {
            let qname = qualify_type_name(&info.name, type_modules);
            format!(":{qname}")
        }
        ModuleEntry::TraitDecl { decl, .. } => {
            let defining = tc.defining_module_for(decl.name.as_ref());
            format!("trait {defining}/{}", decl.name)
        }
        _ => format!("{module}/{name}"),
    }
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
        _ => format!("{name} — {description}"),
    }
}

/// Check if the trimmed input is a bare special form name and return its display.
///
/// Returns `Some(display_string)` if the input matches a special form,
/// `None` otherwise.
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
        ModuleEntry::Def { kind, scheme, .. } => {
            if let DefKind::SpecialForm { description } = kind.as_ref() {
                Some(format_special_form_display(trimmed, description))
            } else {
                // Regular function/primitive: show `:TypeScheme module/name`
                let type_str = format_type_qualified(&scheme.ty, &session.type_modules);
                Some(format!(":{type_str} {module}/{trimmed}"))
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
            let type_str = format_type_qualified(&scheme.ty, &session.type_modules);
            Some(format!(":{type_str} {module}/{type_name}.{trimmed}"))
        }
        _ => None,
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
}
