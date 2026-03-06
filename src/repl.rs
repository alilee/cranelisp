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
    CompileMode, CranelispError, NoOpExpander, ReplCheckResult, ReplInput, Symbol, Type,
    TypeDefInfo, TypeName, Warning, NULLARY_TAG_THRESHOLD,
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
}

impl ReplSession {
    /// Create a new REPL session.
    pub fn new() -> Self {
        ReplSession {
            tc: TypeChecker::new(),
            got_state: ModuleCodegenState::new(),
            jit_modules: Vec::new(),
            type_defs: HashMap::new(),
        }
    }

    /// Get the accumulated type definitions for value display.
    pub fn type_defs(&self) -> &HashMap<TypeName, TypeDefInfo> {
        &self.type_defs
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
        let warnings: Vec<Warning> = check_result.warnings.clone();

        match input {
            ReplInput::Expr(expr) => {
                // Build a CheckResult for the backend.
                let check = self.build_check_for_backend(check_result);

                // Compile any monomorphised specializations before executing
                // the expression (Gap 4: REPL constrained-poly path).
                for mono in &check_result.mono_defns {
                    // Build per-mono CheckResult with merged resolutions.
                    let mut mono_check = self.build_check_for_backend(check_result);
                    mono_check.method_resolutions.extend(mono.resolutions.clone());
                    if !mono.expr_types.is_empty() {
                        mono_check.expr_types = mono.expr_types.clone();
                    }
                    self.compile_and_register_defn(&mono.defn, &mono_check)?;
                }

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
                    warnings,
                    definition_display: None,
                })
            }

            ReplInput::Defn(defn) => {
                // Skip compiling constrained fn base definitions — they are
                // templates that get monomorphised at call sites.
                let is_constrained = check_result
                    .scheme
                    .as_ref()
                    .map_or(false, |s| !s.constraints.is_empty());

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
                            message: format!(
                                "no code pointer after compiling defn '{}'",
                                defn.name
                            ),
                            span: cranelisp_types::Span::SYNTHETIC,
                        })?;
                    let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(code_ptr) };
                    func()
                } else {
                    0
                };

                // Build definition display with constraint info for constrained fns.
                let definition_display = if is_constrained {
                    check_result.scheme.as_ref().map(|s| {
                        format_scheme_display(&defn.name, s)
                    })
                } else {
                    None
                };

                Ok(ReplResult {
                    value,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                    definition_display,
                })
            }

            ReplInput::TypeDef { .. } => {
                // Accumulate type definitions for ADT value display.
                for (name, info) in &check_result.type_defs {
                    self.type_defs.insert(name.clone(), info.clone());
                }

                // Type definitions don't produce a runtime value.
                Ok(ReplResult {
                    value: 0,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                    definition_display: None,
                })
            }

            // Not supported in Ring 0.
            ReplInput::DefnMulti { span, .. } => Err(CranelispError::TypeError {
                message: "multi-signature functions not supported in Ring 0".into(),
                span: *span,
            }),
            ReplInput::TraitDecl(decl) => {
                // Trait registration is already done by check_repl_input.
                // Compile any default method bodies generated by the typechecker.
                if !check_result.default_method_defns.is_empty() {
                    let check = self.build_check_for_backend(check_result);
                    for defn in &check_result.default_method_defns {
                        self.compile_and_register_defn(defn, &check)?;
                    }
                }

                let display = format!("deftrait {}", decl.name);

                Ok(ReplResult {
                    value: 0,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                    definition_display: Some(display),
                })
            }
            ReplInput::TraitImpl(impl_) => {
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
                for mono in &check_result.mono_defns {
                    // Build per-mono CheckResult with merged resolutions.
                    let mut mono_check = self.build_check_for_backend(check_result);
                    mono_check.method_resolutions.extend(mono.resolutions.clone());
                    if !mono.expr_types.is_empty() {
                        mono_check.expr_types = mono.expr_types.clone();
                    }
                    self.compile_and_register_defn(&mono.defn, &mono_check)?;
                }

                let display = format!(
                    "impl {} {}",
                    impl_.trait_name, impl_.target_type
                );

                Ok(ReplResult {
                    value: 0,
                    ty: check_result.ty.clone(),
                    is_definition: true,
                    warnings,
                    definition_display: Some(display),
                })
            }
        }
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
    format_result_value(value, ty, &HashMap::new())
}

/// Format a constrained function's scheme for REPL display.
///
/// Shows the function name, type signature, and trait constraints.
/// Example: `defn double :: (Fn [:Num a] a) where a: Num`
fn format_scheme_display(name: &str, scheme: &cranelisp_types::Scheme) -> String {
    let var_names = cranelisp_types::type_var_names(&scheme.ty);
    let type_str = cranelisp_types::format_type_with_vars(&scheme.ty, &var_names);

    // Build constraint display
    let mut constraint_parts = Vec::new();
    for (type_id, traits) in &scheme.constraints {
        if let Some(var_name) = var_names.get(type_id) {
            for trait_name in traits {
                constraint_parts.push(format!("{var_name}: {trait_name}"));
            }
        }
    }

    if constraint_parts.is_empty() {
        format!("defn {name} :: {type_str}")
    } else {
        constraint_parts.sort();
        let constraints = constraint_parts.join(", ");
        format!("defn {name} :: {type_str} where {constraints}")
    }
}

/// Format a result value for REPL display with full type definition context.
///
/// When `type_defs` is provided, ADT values are displayed with constructor
/// names and field values: `:(Option Int) (Some 42)`.
///
/// Strings are read from heap memory via `cranelisp_runtime::read_string_as_str`.
/// Closures display as `:(Fn [...] ...) <closure>`.
pub fn format_result_value(
    value: i64,
    ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
) -> String {
    match ty {
        Type::Bool => {
            let display_val = if value != 0 { "true" } else { "false" };
            format!(":Bool {display_val}")
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            format!(":Float {f}")
        }
        Type::Int => format!(":Int {value}"),
        Type::String => format_string_value(value),
        Type::Fn(_, _) => {
            let type_str = cranelisp_types::format_type_display(ty);
            format!(":{type_str} <closure>")
        }
        Type::ADT(type_name, type_args) => {
            format_adt_value(value, type_name, type_args, type_defs)
        }
        other => {
            let type_str = cranelisp_types::format_type_display(other);
            format!(":{type_str} {value}")
        }
    }
}

/// Format a String heap value as `:String "contents"`.
fn format_string_value(value: i64) -> String {
    if value == 0 || (value as usize) < NULLARY_TAG_THRESHOLD {
        // Null or small value -- not a valid heap pointer.
        return format!(":String <invalid:{value}>");
    }
    // SAFETY: value is a heap pointer to a valid HeapString (produced by JIT code).
    let s = unsafe { cranelisp_runtime::read_string_as_str(value) };
    format!(":String \"{s}\"")
}

/// Format an ADT value with constructor name lookup.
///
/// Nullary constructors (bare i64 tags) look up the constructor name from type_defs.
/// Data constructors (heap pointers) read tag + fields from the heap.
fn format_adt_value(
    value: i64,
    type_name: &TypeName,
    type_args: &[Type],
    type_defs: &HashMap<TypeName, TypeDefInfo>,
) -> String {
    let type_display = format_adt_type(type_name, type_args);

    // Vec is a built-in type, not in type_defs -- handle it specially.
    if type_name == "Vec" {
        let elem_type = type_args.first();
        let elems = format_vec_elements(value, elem_type, type_defs);
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
        format!(":{type_display} {ctor_name}")
    } else {
        // Data constructor: read tag and fields from heap.
        format_adt_heap_value(value, &type_display, type_info, type_args, type_defs)
    }
}

/// Format the type portion of an ADT display.
/// Simple types: `Color`. Parameterized: `(Option Int)`.
fn format_adt_type(type_name: &TypeName, type_args: &[Type]) -> String {
    if type_args.is_empty() {
        format!("{type_name}")
    } else {
        let arg_strs: Vec<String> = type_args.iter().map(|a| format!("{a}")).collect();
        format!("({type_name} {})", arg_strs.join(" "))
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
///
/// For polymorphic ADTs (e.g., `(Option Int)`), substitutes the concrete type_args
/// into field types before formatting. Without this, fields with type variables
/// would display as raw values instead of properly formatted values.
fn format_adt_heap_value(
    value: i64,
    type_display: &str,
    type_info: &TypeDefInfo,
    type_args: &[Type],
    type_defs: &HashMap<TypeName, TypeDefInfo>,
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
        return format!(":{type_display} {}", ctor.name);
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
        let field_str = format_field_value(field_val, &field_ty, type_defs);
        field_strs.push(field_str);
    }

    let fields_display = field_strs.join(" ");
    format!(":{type_display} ({} {fields_display})", ctor.name)
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
            Some(ty) => format_field_value(elem_val, ty, type_defs),
            None => format!("{elem_val}"),
        };
        elems.push(formatted);
    }

    format!("[{}]", elems.join(", "))
}

/// Format a single field value based on its type.
fn format_field_value(
    value: i64,
    ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
) -> String {
    match ty {
        Type::Int => format!("{value}"),
        Type::Bool => {
            if value != 0 { "true".to_string() } else { "false".to_string() }
        }
        Type::Float => {
            let f = f64::from_bits(value as u64);
            format!("{f}")
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
                return format_vec_elements(value, args.first(), type_defs);
            }
            // Recursive ADT formatting.
            let type_display = format_adt_type(name, args);
            if let Some(info) = type_defs.get(name) {
                if (value as usize) < NULLARY_TAG_THRESHOLD {
                    let tag = value as usize;
                    find_constructor_by_tag(info, tag)
                } else {
                    // Recursive heap ADT -- format with parens.
                    let inner = format_adt_heap_value(value, &type_display, info, args, type_defs);
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

/// Run the interactive REPL loop.
///
/// Reads lines from stdin, evaluates them, prints results.
/// Errors are printed without crashing the session.
pub fn run_repl() {
    let mut session = ReplSession::new();
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut stdout = stdout.lock();

    let _ = write!(stdout, "> ");
    let _ = stdout.flush();

    let mut buffer = String::new();

    for line in stdin.lock().lines() {
        let line = match line {
            Ok(l) => l,
            Err(_) => break,
        };

        buffer.push_str(&line);

        // Check for balanced parentheses for multi-line input.
        if !parens_balanced(&buffer) {
            buffer.push('\n');
            let _ = write!(stdout, "  ");
            let _ = stdout.flush();
            continue;
        }

        let input = buffer.trim();
        if input.is_empty() || is_comment_only(input) {
            buffer.clear();
            let _ = write!(stdout, "> ");
            let _ = stdout.flush();
            continue;
        }

        match session.eval(input) {
            Ok(result) => {
                // Print warnings first.
                for w in &result.warnings {
                    let _ = writeln!(stdout, "warning: {}", w.message);
                }
                // Print the result, using definition_display when available.
                let display = if let Some(ref def_display) = result.definition_display {
                    def_display.clone()
                } else {
                    format_result_value(
                        result.value,
                        &result.ty,
                        session.type_defs(),
                    )
                };
                let _ = writeln!(stdout, "{display}");
            }
            Err(e) => {
                let _ = writeln!(stdout, "error: {e}");
            }
        }

        buffer.clear();
        let _ = write!(stdout, "> ");
        let _ = stdout.flush();
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_format_result_int() {
        assert_eq!(format_result(42, &Type::Int), ":Int 42");
    }

    #[test]
    fn test_format_result_bool_true() {
        assert_eq!(format_result(1, &Type::Bool), ":Bool true");
    }

    #[test]
    fn test_format_result_bool_false() {
        assert_eq!(format_result(0, &Type::Bool), ":Bool false");
    }

    #[test]
    fn test_format_result_float() {
        let bits = 1.234_f64.to_bits() as i64;
        let result = format_result(bits, &Type::Float);
        assert!(result.starts_with(":Float 1.234"));
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
        assert_eq!(result, ":String \"hello\"");
        cranelisp_runtime::heap_dealloc(s);
    }

    #[test]
    fn test_format_result_empty_string() {
        let s = cranelisp_runtime::alloc_string(b"") as i64;
        let result = format_result(s, &Type::String);
        assert_eq!(result, ":String \"\"");
        cranelisp_runtime::heap_dealloc(s);
    }

    #[test]
    fn test_format_result_fn_type() {
        let fn_ty = Type::Fn(vec![Type::Int, Type::Bool], Box::new(Type::String));
        let result = format_result(0, &fn_ty);
        assert_eq!(result, ":(Fn [Int Bool] String) <closure>");
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
        assert_eq!(
            format_result_value(0, &adt, &type_defs),
            ":Color Red"
        );
        assert_eq!(
            format_result_value(1, &adt, &type_defs),
            ":Color Green"
        );
        assert_eq!(
            format_result_value(2, &adt, &type_defs),
            ":Color Blue"
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

        // Nullary: None (tag 0).
        assert_eq!(
            format_result_value(0, &adt, &type_defs),
            ":(Option Int) None"
        );

        // Data constructor: allocate Some(42) on heap.
        // Payload = tag (8 bytes) + 1 field (8 bytes) = 16 bytes.
        let ptr = cranelisp_runtime::alloc_with_rc(16);
        unsafe {
            *(ptr.add(16) as *mut i64) = 1; // tag = 1 (Some)
            *(ptr.add(24) as *mut i64) = 42; // field val = 42
        }

        assert_eq!(
            format_result_value(ptr as i64, &adt, &type_defs),
            ":(Option Int) (Some 42)"
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
    fn test_format_adt_type() {
        assert_eq!(
            format_adt_type(&TypeName::from("Color"), &[]),
            "Color"
        );
        assert_eq!(
            format_adt_type(&TypeName::from("Option"), &[Type::Int]),
            "(Option Int)"
        );
    }
}
