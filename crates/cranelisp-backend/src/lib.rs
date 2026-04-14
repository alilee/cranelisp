// cranelisp-backend: Cranelift IR codegen, JIT, RC emission, caching, linking.
//
// Public API:
// - compile_program: batch compilation of a full program
// - compile_expr_with_got_and_symbols: compile a single expression with env (REPL)
// - compile_and_run_expr: compile and execute a single expression (convenience)
// - Jit: JIT module management
// - build_isa: ISA construction for JIT and ObjectModule (re-exported from cache::object)

pub mod cache;

// Re-export build_isa at the crate root for convenient access.
// This is the single ISA construction point (architecture decision 7).
pub use cache::object::build_isa;
use cranelisp_types::ModuleEntry;
// Re-export TargetIsa for shared ISA in N-core codegen (pipeline-v3.md §6).
pub use cranelift::codegen::isa::TargetIsa;
// Re-export Cranelift module types for callers of compile_to_module.
pub use cranelift_module;
pub use cranelift_object;
pub mod codegen_types;
pub mod exe;
pub mod compiler;
pub mod display;
pub mod got;
pub mod heap;
pub mod jit;
pub mod operators;

use std::collections::HashMap;

use cranelift_module::FuncId;

use dashmap::DashMap;

use cranelisp_types::{
    CheckResult, CranelispError, Defn, Expr, FQTypeName,
    ModuleFullPath, Program, Span, Symbol, SymbolTable,
    TopLevel, Type, TypeName, Warning,
};

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::compiler::{CompilationEnv, CompileContext, FnCompiler};
use crate::jit::{Jit, IntrinsicFuncIds, declare_intrinsics_generic};

/// Result of compiling a program's functions into a module.
///
/// Module-type-agnostic: the caller extracts what it needs.
/// For JIT: uses `entry_func_id` to get the entry point after finalization.
/// For ObjectModule: ignores `entry_func_id` (no entry needed for .o files).
pub struct CompilationResult {
    /// FuncIds for all compiled functions (name -> FuncId).
    pub func_ids: HashMap<Symbol, FuncId>,
    /// FuncId of the entry function (last zero-arg defn), if any.
    pub entry_func_id: Option<FuncId>,
    /// Function arities for all compiled functions.
    pub func_arities: HashMap<Symbol, usize>,
    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

/// Compile a program's functions into a Cranelift module.
///
/// This is the ONLY compilation entry point in the backend crate.
/// See design/backend/compile-to-module.md §2 (PRESCRIPTIVE).
///
/// Five parameters. Everything else derived internally:
/// - Intrinsics: declared on the module internally
/// - GOT slots: read from symbol_tables
/// - GOT bases: JIT → runtime pointers; Object → symbolic relocations (internal fork)
/// - Cross-module refs: resolved from symbol_tables Import chains
/// - CompilationEnv: built internally
/// - JIT name prefix: derived from module_path
pub fn compile_to_module<M: Module>(
    module_path: ModuleFullPath,
    program: &Program,
    typecheck: &CheckResult,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError> {
    // TODO(/backend): Derive all of these internally instead of
    // delegating to the legacy inner function. See §2.3 of the design doc.
    let intrinsic_ids = declare_intrinsics_generic(module)?;
    let env_impl = crate::cache::object::ObjectCompilationEnv {
        symbol_tables,
        current_module: module_path.clone(),
    };
    let cross_refs = resolve_cross_module_refs(symbol_tables, &module_path);
    let jit_prefix_owned: Option<String> = if module_path.as_ref() != "user" && module_path.as_ref() != "main" {
        Some(module_path.as_ref().to_string())
    } else {
        None
    };
    _compile_to_module_inner(
        program, typecheck, symbol_tables, module, module_path,
        &intrinsic_ids, Some(&env_impl as &dyn CompilationEnv),
        &cross_refs, jit_prefix_owned.as_deref(),
    )
}

/// Resolve cross-module function references from symbol table Import chains.
fn resolve_cross_module_refs(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module_path: &ModuleFullPath,
) -> Vec<(Symbol, usize)> {
    let mut refs = Vec::new();
    let Some(table) = symbol_tables.get(module_path) else { return refs };
    for (name, entry) in table.all_symbols() {
        if let ModuleEntry::Import { source } = entry {
            if let Some(source_table) = symbol_tables.get(&source.module) {
                if let Some(source_entry) = source_table.get(source.symbol.as_ref()) {
                    let param_count = match source_entry {
                        ModuleEntry::Def { scheme, .. } | ModuleEntry::Constructor { scheme, .. } => {
                            match &scheme.ty {
                                Type::Fn(params, _) => params.len(),
                                _ => continue,
                            }
                        }
                        _ => continue,
                    };
                    let qualified = Symbol::from(format!("{}/{}", source.module.as_ref(), source.symbol.as_ref()));
                    refs.push((qualified, param_count));
                    refs.push((name.clone(), param_count));
                }
            }
        }
    }
    refs
}

/// Legacy inner implementation — to be eliminated by /backend.
/// All parameters should be derived internally by compile_to_module.
#[allow(clippy::too_many_arguments)]
fn _compile_to_module_inner<M: Module>(
    program: &Program,
    check: &CheckResult,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
    current_module: ModuleFullPath,
    intrinsic_ids: &IntrinsicFuncIds,
    env: Option<&dyn CompilationEnv>,
    prior_funcs: &[(Symbol, usize)],
    jit_prefix: Option<&str>,
) -> Result<CompilationResult, CranelispError> {
    // Step 1: Collect defns from the program.
    let mut regular_defns: Vec<&Defn> = Vec::new();
    let mut multi_sig_defns: Vec<Defn> = Vec::new();

    for tl in program {
        if let TopLevel::Defn(defn) = tl {
            if check.constrained_fn_names.contains(&defn.name) {
                continue; // Template only — mono specializations compiled below
            }
            if defn.is_multi_sig() {
                let expanded = expand_multi_sig_defn(defn, &check.expr_types)?;
                multi_sig_defns.extend(expanded);
            } else {
                regular_defns.push(defn);
            }
        }
    }

    // Step 2: Collect extra defns from CheckResult.
    let extra_defns: Vec<&Defn> = check.default_method_defns.iter().collect();
    let mono_defns: Vec<&Defn> = check.mono_defns.iter().map(|m| &m.defn).collect();

    // Step 3: Build the full defn list for declaration.
    let mut all_declare: Vec<&Defn> = regular_defns.clone();
    all_declare.extend(extra_defns.iter().copied());
    all_declare.extend(multi_sig_defns.iter());
    all_declare.extend(mono_defns.iter().copied());

    if all_declare.is_empty() {
        return Err(CranelispError::CodegenError {
            message: "no function definitions in program".into(),
            span: Span::SYNTHETIC,
        });
    }

    // Step 4: Declare all functions in the module (Pass 1).
    // Start with intrinsic FuncIds.
    let mut func_ids: HashMap<Symbol, FuncId> = intrinsic_ids.by_name.clone();

    // When a prefix is provided, JIT symbol names are module-qualified.
    let mut jit_names: HashMap<Symbol, Symbol> = HashMap::new();

    for defn in &all_declare {
        let qualified_name = if let Some(prefix) = jit_prefix {
            let qn = format!("{prefix}/{}", defn.name);
            jit_names.insert(defn.name.clone(), Symbol::from(qn.as_str()));
            qn
        } else {
            defn.name.to_string()
        };

        let mut sig = module.make_signature();
        for _ in defn.params() {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = module
            .declare_function(&qualified_name, cranelift_module::Linkage::Export, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare function '{}': {e}", defn.name),
                span: defn.span,
            })?;
        func_ids.insert(defn.name.clone(), func_id);
    }

    // Declare prior (cross-module) functions as imports.
    for (name, param_count) in prior_funcs {
        if func_ids.contains_key(name) {
            continue;
        }

        // Check if a bare-name alias already exists.
        if let Some(slash_pos) = name.as_ref().rfind('/') {
            let bare_name = Symbol::from(&name.as_ref()[slash_pos + 1..]);
            if let Some(&existing_func_id) = func_ids.get(&bare_name) {
                func_ids.insert(name.clone(), existing_func_id);
                continue;
            }
        }

        let mut sig = module.make_signature();
        for _ in 0..*param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = module
            .declare_function(name, cranelift_module::Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare imported function '{}': {e}", name),
                span: Span::SYNTHETIC,
            })?;
        func_ids.insert(name.clone(), func_id);

        // Also register the bare name.
        if let Some(slash_pos) = name.as_ref().rfind('/') {
            let bare_name = Symbol::from(&name.as_ref()[slash_pos + 1..]);
            if !func_ids.contains_key(&bare_name) {
                func_ids.insert(bare_name, func_id);
            }
        }
    }

    // Build function arity map.
    let mut func_arities: HashMap<Symbol, usize> = all_declare
        .iter()
        .map(|d| (d.name.clone(), d.params().len()))
        .collect();
    for (name, count) in prior_funcs {
        func_arities.insert(name.clone(), *count);
        if let Some(slash_pos) = name.as_ref().rfind('/') {
            let bare_name = Symbol::from(&name.as_ref()[slash_pos + 1..]);
            func_arities.entry(bare_name).or_insert(*count);
        }
    }

    // Step 5: Compile each function body (Pass 2).
    let mut func_ctx = FunctionBuilderContext::new();

    // Compile regular defns + extra defns + multi-sig variants.
    let non_mono_defns: Vec<&Defn> = regular_defns.iter().copied()
        .chain(extra_defns.iter().copied())
        .chain(multi_sig_defns.iter())
        .collect();

    for defn in &non_mono_defns {
        let compile_ctx = CompileContext {
            method_resolutions: &check.method_resolutions,
            expr_types: &check.expr_types,
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables,
            current_module: current_module.clone(),
            env,
            traced_fns: None,
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids.dealloc,
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic_func_id: intrinsic_ids.panic,
            vec_new_func_id: intrinsic_ids.vec_new,
            vec_drop_func_id: intrinsic_ids.vec_drop,
        };
        compile_defn_in_module(defn, module, &mut func_ctx, &func_ids, compile_ctx)?;
    }

    // Compile mono specializations with per-specialization resolutions.
    for mono in &check.mono_defns {
        let mut merged = check.method_resolutions.clone();
        merged.extend(mono.resolutions.clone());

        let expr_types = if mono.expr_types.is_empty() {
            &check.expr_types
        } else {
            &mono.expr_types
        };

        let compile_ctx = CompileContext {
            method_resolutions: &merged,
            expr_types,
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables,
            current_module: current_module.clone(),
            env,
            traced_fns: None,
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids.dealloc,
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic_func_id: intrinsic_ids.panic,
            vec_new_func_id: intrinsic_ids.vec_new,
            vec_drop_func_id: intrinsic_ids.vec_drop,
        };
        compile_defn_in_module(&mono.defn, module, &mut func_ctx, &func_ids, compile_ctx)?;
    }

    // Find entry function (last zero-arg defn).
    let entry_func_id = regular_defns
        .iter()
        .rev()
        .find(|d| d.params().is_empty())
        .and_then(|d| func_ids.get(&d.name).copied());

    // Collect func_signatures for downstream modules (JIT-visible names).
    let result_func_ids: HashMap<Symbol, FuncId> = all_declare.iter()
        .filter_map(|d| {
            let jit_name = jit_names.get(&d.name)
                .cloned()
                .unwrap_or_else(|| d.name.clone());
            func_ids.get(&d.name).map(|&fid| (jit_name, fid))
        })
        .collect();

    Ok(CompilationResult {
        func_ids: result_func_ids,
        entry_func_id,
        func_arities,
        warnings: Vec::new(),
    })
}

/// Compile a single defn into a module using FnCompiler.
fn compile_defn_in_module<M: Module>(
    defn: &Defn,
    module: &mut M,
    func_ctx: &mut FunctionBuilderContext,
    func_ids: &HashMap<Symbol, FuncId>,
    compile_ctx: CompileContext<'_>,
) -> Result<(), CranelispError> {
    let mut sig = module.make_signature();
    for _ in defn.params() {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));

    let func_id = *func_ids.get(&defn.name).ok_or_else(|| {
        CranelispError::CodegenError {
            message: format!("function '{}' not declared", defn.name),
            span: defn.span,
        }
    })?;

    let mut func = cranelift::codegen::ir::Function::with_name_signature(
        cranelift::codegen::ir::UserFuncName::testcase(defn.name.as_bytes()),
        sig,
    );

    FnCompiler::compile_body(defn, &mut func, func_ctx, module, compile_ctx)?;

    let mut ctx = cranelift::codegen::Context::for_function(func);
    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define function '{}': {e}", defn.name),
            span: defn.span,
        })?;

    Ok(())
}

/// Result of compiling a batch program. Holds the JIT and entry point
/// so the caller can execute and then drop the JIT.
pub struct _DeprecatedCompiledProgram {
    // Kept alive so JIT-compiled code pointers remain valid.
    #[allow(dead_code)]
    jit: Jit,
    entry_ptr: *const u8,
    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

impl _DeprecatedCompiledProgram {
    /// Execute the compiled program.
    ///
    /// # Safety
    ///
    /// The entry_ptr must point to valid JIT-compiled code with the signature
    /// `extern "C" fn() -> i64`. This is guaranteed when CompiledProgram was
    /// produced by `compile_program`.
    pub unsafe fn execute(&self) -> Result<i64, CranelispError> {
        // Clear any stale runtime error before execution.
        let _ = cranelisp_runtime::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(self.entry_ptr) };
        let value = func();
        // Check for runtime panics (e.g., division by zero, match failure).
        if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", msg),
                span: Span::SYNTHETIC,
            });
        }
        Ok(value)
    }
}

/// Result of compiling a single REPL expression. Holds the JIT alive so
/// the caller can execute the compiled function pointer at its leisure.
/// This enables the caller to separately time compilation and evaluation.
pub struct _DeprecatedCompiledExpr {
    // Kept alive so the compiled function pointer remains valid.
    #[allow(dead_code)]
    jit: Jit,
    func_ptr: *const u8,
}

impl _DeprecatedCompiledExpr {
    /// Execute the compiled expression and return the i64 result.
    ///
    /// Checks for runtime panics (division by zero, match failure, etc.)
    /// after execution and returns an error if one occurred.
    ///
    /// # Safety
    ///
    /// The func_ptr must point to valid JIT-compiled code with the signature
    /// `extern "C" fn() -> i64`. This is guaranteed when CompiledExpr was
    /// produced by `compile_expr_with_got`.
    pub unsafe fn execute(&self) -> Result<i64, CranelispError> {
        // Clear any stale runtime error before execution.
        let _ = cranelisp_runtime::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(self.func_ptr) };
        let value = func();
        // Check for runtime panics (e.g., division by zero, match failure).
        if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", msg),
                span: Span::SYNTHETIC,
            });
        }
        Ok(value)
    }
}


/// Compile a batch program: declare all functions, compile them, finalize.
///
/// The last zero-arg function in the program is the entry point.
/// Returns a CompiledProgram that can be executed.
///
/// Thin wrapper around `compile_to_module<JITModule>`.
pub fn _deprecated_compile_program(
    _program: &Program,
    _check: &CheckResult,
    _use_got: bool,
    _symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
) -> Result<_DeprecatedCompiledProgram, CranelispError> {
    unimplemented!("superseded by compile_to_module")
}

/// Extract the concrete type name from a resolved type, for mangled name construction.
///
/// Mirrors `concrete_type_name` in the typecheck crate. Returns `None` for
/// unresolved type variables — those cannot appear in multi-sig dispatch
/// (all variants must have concrete parameter types).
fn concrete_type_name(ty: &Type) -> Option<FQTypeName> {
    match ty {
        Type::Int => Some(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Int"))),
        Type::Float => Some(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Float"))),
        Type::Bool => Some(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("Bool"))),
        Type::String => Some(FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("String"))),
        Type::ADT(fqtn, _) => Some(fqtn.clone()),
        _ => None,
    }
}

/// Build a mangled function name from a base name and concrete parameter types.
///
/// Follows the convention `name$Type1+Type2` (spec §5.1.2). Mirrors
/// `build_mangled_name` in the typecheck crate to ensure the backend and
/// typechecker agree on mangled names.
fn build_mangled_name(fn_name: &Symbol, param_types: &[Type]) -> String {
    let type_names: Vec<String> = param_types
        .iter()
        .filter_map(|t| concrete_type_name(t).map(|fqtn| fqtn.name.to_string()))
        .collect();
    format!("{}${}", fn_name, type_names.join("+"))
}

/// Expand a multi-sig defn into individual single-variant defns with mangled names.
///
/// For each variant, looks up its function type in `expr_types` (keyed by the
/// variant's span) to determine the concrete parameter types, then builds a
/// mangled name using `build_mangled_name`.
///
/// Returns the expanded defns. The base multi-sig defn should not be compiled
/// directly — callers use `ResolvedCall::SigDispatch` to call specific variants.
fn expand_multi_sig_defn(
    defn: &Defn,
    expr_types: &HashMap<Span, Type>,
) -> Result<Vec<Defn>, CranelispError> {
    let mut expanded = Vec::new();

    for variant in &defn.variants {
        // Look up the function type for this variant's span.
        let param_types = match expr_types.get(&variant.span) {
            Some(Type::Fn(params, _)) => params.clone(),
            _ => {
                // Fall back: try the defn-level span (some typecheckers register there).
                match expr_types.get(&defn.span) {
                    Some(Type::Fn(params, _)) if params.len() == variant.params.len() => {
                        params.clone()
                    }
                    _ => {
                        return Err(CranelispError::CodegenError {
                            message: format!(
                                "multi-sig variant of '{}' missing type info at span {:?}",
                                defn.name, variant.span
                            ),
                            span: variant.span,
                        });
                    }
                }
            }
        };

        let mangled_name = build_mangled_name(&defn.name, &param_types);

        expanded.push(Defn {
            name: Symbol::from(mangled_name),
            docstring: defn.docstring.clone(),
            variants: vec![variant.clone()],
            visibility: defn.visibility,
            span: variant.span,
        });
    }

    Ok(expanded)
}





/// Result of compiling a module's program into a shared JIT.
///
/// Holds function name/arity pairs for symbols that downstream
/// modules may need to reference.
pub struct _DeprecatedCompiledModuleInfo {
    /// Function names and their param counts (for downstream import declarations).
    pub func_signatures: Vec<(Symbol, usize)>,
    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

/// Compile a module's program into an existing shared JIT (no finalize).
///
/// Thin wrapper around `compile_to_module` with JIT prefix and prior funcs.
pub fn _deprecated_compile_module_program(
    _program: &Program,
    _check: &CheckResult,
    _jit: &mut Jit,
    _prior_funcs: &[(Symbol, usize)],
    _module_prefix: &str,
    _symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
) -> Result<_DeprecatedCompiledModuleInfo, CranelispError> {
    unimplemented!("superseded by compile_to_module")
}

/// Compile a single expression into a `CompiledExpr` without executing it.
///
/// Thin wrapper around `compile_to_module<JITModule>`. Wraps the expression
/// in a synthetic zero-arg function and compiles it.
pub fn _deprecated_compile_expr_with_got_and_symbols(
    _expr: &Expr,
    _check: &CheckResult,
    _extra_symbols: &[(&str, *const u8)],
    _got_data_defs: &[(String, *const u8)],
    _env: Option<&dyn crate::compiler::CompilationEnv>,
    _symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    _current_module: ModuleFullPath,
) -> Result<_DeprecatedCompiledExpr, CranelispError> {
    unimplemented!("superseded by compile_to_module")
}

/// Compile and execute a single expression (convenience wrapper).
///
/// Delegates to `compile_expr_with_got_and_symbols` then executes.
pub fn _deprecated_compile_and_run_expr(
    _expr: &Expr,
    _check: &CheckResult,
    _symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
) -> Result<i64, CranelispError> {
    unimplemented!("superseded by compile_to_module")
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{
        CheckResult, Defn, DefnVariant, Expr, Span, Symbol, TopLevel, Visibility,
    };
    use std::collections::{HashMap, HashSet};

    fn empty_check() -> CheckResult {
        CheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        }
    }

    fn empty_tables() -> DashMap<ModuleFullPath, SymbolTable> {
        DashMap::new()
    }

    /// Test helper: wrap an expression in a synthetic zero-arg defn, compile via
    /// `compile_to_module`, finalize JIT, execute, and return the i64 result.
    fn test_compile_and_run(
        expr: &Expr,
        check: &CheckResult,
        tables: &DashMap<ModuleFullPath, SymbolTable>,
    ) -> Result<i64, CranelispError> {
        let defn = Defn {
            name: Symbol::from("__expr__"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: expr.clone(),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        let program: Program = vec![TopLevel::Defn(defn)];
        let mut jit = Jit::new()?;
        let result = compile_to_module(
            ModuleFullPath::from("user"),
            &program,
            check,
            tables,
            jit.jit_module(),
        )?;
        jit.finalize()?;
        let entry_id = result.entry_func_id.ok_or_else(|| CranelispError::CodegenError {
            message: "no entry function".into(),
            span: Span::SYNTHETIC,
        })?;
        let ptr = jit.get_finalized_ptr(entry_id);
        let _ = cranelisp_runtime::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let value = func();
        if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", msg),
                span: Span::SYNTHETIC,
            });
        }
        Ok(value)
    }

    /// Test helper: compile a program via `compile_to_module`, finalize JIT,
    /// execute entry function, and return the i64 result.
    fn test_compile_program_and_run(
        program: &Program,
        check: &CheckResult,
        tables: &DashMap<ModuleFullPath, SymbolTable>,
    ) -> Result<i64, CranelispError> {
        let mut jit = Jit::new()?;
        let result = compile_to_module(
            ModuleFullPath::from("user"),
            program,
            check,
            tables,
            jit.jit_module(),
        )?;
        jit.finalize()?;
        let entry_id = result.entry_func_id.ok_or_else(|| CranelispError::CodegenError {
            message: "no entry function".into(),
            span: Span::SYNTHETIC,
        })?;
        let ptr = jit.get_finalized_ptr(entry_id);
        let _ = cranelisp_runtime::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let value = func();
        if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", msg),
                span: Span::SYNTHETIC,
            });
        }
        Ok(value)
    }

    /// Build symbol tables with an Option type for ADT tests.
    fn option_type_tables() -> DashMap<ModuleFullPath, SymbolTable> {
        use cranelisp_types::{
            ConstructorInfo, FQTypeName, FieldInfo, ModuleEntry, Scheme, Type,
            TypeDefInfo, TypeName, Visibility,
        };

        let module = ModuleFullPath::from("main");
        let type_name = TypeName::from("Option");
        let fqtn = FQTypeName::new(module.clone(), type_name.clone());

        let type_def_info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: vec![],
            constructors: vec![
                ConstructorInfo {
                    name: Symbol::from("None"),
                    tag: 0,
                    fields: vec![],
                    docstring: None,
                    internal: false,
                },
                ConstructorInfo {
                    name: Symbol::from("Some"),
                    tag: 1,
                    fields: vec![FieldInfo {
                        name: Symbol::from("val"),
                        ty: Type::Int,
                    }],
                    docstring: None,
                    internal: false,
                },
            ],
            docstring: None,
        };

        let tables = DashMap::new();
        let mut st = SymbolTable::new(module.clone());

        // Insert type def
        st.insert(
            Symbol::from("Option"),
            ModuleEntry::TypeDef {
                info: type_def_info.clone(),
                visibility: Visibility::Public,
                constructor_scheme: None,
                sexp: None,
            },
        );

        // Insert constructors
        let none_scheme = Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: Type::ADT(fqtn.clone(), vec![]),
        };
        st.insert(
            Symbol::from("None"),
            ModuleEntry::Constructor {
                type_name: fqtn.clone(),
                info: type_def_info.constructors[0].clone(),
                scheme: none_scheme,
                visibility: Visibility::Public,
            },
        );

        let some_scheme = Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::ADT(fqtn.clone(), vec![]))),
        };
        st.insert(
            Symbol::from("Some"),
            ModuleEntry::Constructor {
                type_name: fqtn.clone(),
                info: type_def_info.constructors[1].clone(),
                scheme: some_scheme,
                visibility: Visibility::Public,
            },
        );

        tables.insert(module, st);
        tables
    }

    // spec: 05-definitions §5.1 — single defn compiles and executes via JIT
    #[test]
    fn test_compile_program_simple() {
        let defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 42,
                    span: Span::new(0, 2),
                },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 42);
    }

    // spec: 12-runtime §12.6 — batch mode requires main entry point
    #[test]
    fn test_compile_program_no_defns() {
        let program: Program = vec![];
        let check = empty_check();

        let mut jit = Jit::new().unwrap();
        let result = compile_to_module(
            ModuleFullPath::from("user"),
            &program,
            &check,
            &empty_tables(),
            jit.jit_module(),
        );
        assert!(result.is_err());
    }

    // spec: 04-expressions §4.1.1 — integer literal codegen
    #[test]
    fn test_compile_and_run_expr() {
        let expr = Expr::IntLit {
            value: 99,
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let value = test_compile_and_run(&expr, &check, &empty_tables()).unwrap();
        assert_eq!(value, 99);
    }

    // spec: 05-definitions §5.1 — defn compiles in interactive (REPL) mode
    #[test]
    fn test_compile_program_interactive_mode() {
        let defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                value: 7,
                span: Span::new(0, 1),
                },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 7);
    }

    // spec: 04-expressions §4.1.1 — integer literal codegen with GOT state
    // spec: 05-definitions §5.13.1 — multiple function definitions compile together
    #[test]
    fn test_compile_program_multiple_defns() {
        // Two functions: helper and main. Main returns 100.
        let helper = Defn {
            name: Symbol::from("helper"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![],
                body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(20, 21),
                },
                span: Span::new(10, 30),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(10, 30),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                value: 100,
                span: Span::new(40, 43),
                },
                span: Span::new(35, 50),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(35, 50),
        };

        let program: Program = vec![TopLevel::Defn(helper), TopLevel::Defn(main_defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 100);
    }

    // spec: 04-expressions §4.1.3 — boolean literal codegen
    #[test]
    fn test_compile_and_run_expr_bool() {
        let expr = Expr::BoolLit {
            value: true,
            span: Span::new(0, 4),
        };
        let check = empty_check();

        let value = test_compile_and_run(&expr, &check, &empty_tables()).unwrap();
        assert_eq!(value, 1);
    }

    // --- Ring 1 tests ---

    // spec: 04-expressions §4.1.4 — string literal codegen, heap allocation
    #[test]
    fn test_compile_string_literal() {
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: Span::new(0, 7),
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "string literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Read back the string content via runtime API.
        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "hello");

        // Clean up the allocation.
        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 04-expressions §4.1.4 — empty string literal codegen
    #[test]
    fn test_compile_empty_string_literal() {
        let expr = Expr::StringLit {
            value: String::new(),
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty string should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "");

        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 12-runtime §12.1.4 — data constructor heap layout [tag | fields]
    #[test]
    fn test_compile_adt_data_constructor() {
        // Expression: (Some 42)
        let some_span = Span::new(0, 10);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(1, 5),
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: Span::new(6, 8),
            }],
            span: some_span,
        };

        let check = empty_check();
        let tables = option_type_tables();

        let result = test_compile_and_run(&expr, &check, &tables);
        assert!(result.is_ok(), "ADT constructor should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify the heap layout: [header(16) | tag(1) | field(42)]
        unsafe {
            let base = ptr as *const u8;
            let tag = *(base.add(16) as *const i64);
            assert_eq!(tag, 1, "tag should be 1 for Some");
            let val = *(base.add(24) as *const i64);
            assert_eq!(val, 42, "field should be 42");
        }

        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 04-expressions §4.8 — match expression with constructor patterns and field extraction
    #[test]
    fn test_compile_match_with_fields() {
        use cranelisp_types::{MatchArm, Pattern};

        // (match (Some 99) [(Some x) x (None) 0])
        let some_span = Span::new(10, 20);
        let match_span = Span::new(0, 50);
        let scrutinee = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(11, 15),
            }),
            args: vec![Expr::IntLit {
                value: 99,
                span: Span::new(16, 18),
            }],
            span: some_span,
        };

        let expr = Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Some"),
                        bindings: vec![Symbol::from("x")],
                        span: Span::new(22, 30),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: Span::new(31, 32),
                    },
                    span: Span::new(22, 32),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("None"),
                        bindings: vec![],
                        span: Span::new(34, 40),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: Span::new(41, 42),
                    },
                    span: Span::new(34, 42),
                },
            ],
            span: match_span,
            compiler_generated: false,
        };

        let check = empty_check();
        let tables = option_type_tables();

        let result = test_compile_and_run(&expr, &check, &tables);
        assert!(result.is_ok(), "match with fields should compile: {result:?}");
        assert_eq!(result.unwrap(), 99, "match should extract field value");
    }

    // spec: 04-expressions §4.5 — lambda capture, closure allocation, and indirect call
    #[test]
    fn test_compile_lambda_closure() {
        // (let [n 5] ((fn [x] (+ n x)) 10))
        // This tests: lambda capture of 'n', closure allocation, closure call.
        use cranelisp_types::ResolvedCall;

        let add_span = Span::new(30, 37);
        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("n"),
                Expr::IntLit {
                    value: 5,
                    span: Span::new(5, 6),
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Box::new(Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("+"),
                            span: Span::new(31, 32),
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("n"),
                                span: Span::new(33, 34),
                            },
                            Expr::Var {
                                name: Symbol::from("x"),
                                span: Span::new(35, 36),
                            },
                        ],
                        span: add_span,
                    }),
                    span: Span::new(10, 40),
                }),
                args: vec![Expr::IntLit {
                    value: 10,
                    span: Span::new(42, 44),
                }],
                span: Span::new(10, 45),
            }),
            span: Span::new(0, 46),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "closure should compile: {result:?}");
        assert_eq!(result.unwrap(), 15, "5 + 10 = 15");
    }

    // --- Vec codegen tests ---

    // spec: 04-expressions §4.10 — empty Vec literal codegen
    #[test]
    fn test_compile_empty_vec_literal() {
        let expr = Expr::VecLit {
            elements: vec![],
            span: Span::new(0, 2),
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 0.
        assert_eq!(cranelisp_runtime::vec_len(ptr), 0);

        // Clean up.
        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — Vec literal with integer elements
    #[test]
    fn test_compile_vec_literal_with_ints() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 10, span: Span::new(1, 3) },
                Expr::IntLit { value: 20, span: Span::new(4, 6) },
                Expr::IntLit { value: 30, span: Span::new(7, 9) },
            ],
            span: Span::new(0, 10),
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 3.
        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);

        // Verify element values from data buffer.
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(heap::HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64);
            assert_eq!(*data_ptr, 10);
            assert_eq!(*data_ptr.add(1), 20);
            assert_eq!(*data_ptr.add(2), 30);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — single-element Vec literal
    #[test]
    fn test_compile_vec_literal_single_element() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1, 3) },
            ],
            span: Span::new(0, 4),
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "single-element vec should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(cranelisp_runtime::vec_len(ptr), 1);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 42);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — Vec literal with boolean elements
    #[test]
    fn test_compile_vec_literal_with_bool_elements() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: Span::new(1, 5) },
                Expr::BoolLit { value: false, span: Span::new(6, 11) },
            ],
            span: Span::new(0, 12),
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "bool vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(cranelisp_runtime::vec_len(ptr), 2);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1); // true
            assert_eq!(*data_ptr.add(1), 0); // false
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-len inline primitive codegen
    #[test]
    fn test_compile_vec_len_inline() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [10 20 30])
        let vec_span = Span::new(10, 20);
        let apply_span = Span::new(0, 25);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            apply_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1, 8),
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 10, span: Span::new(11, 13) },
                    Expr::IntLit { value: 20, span: Span::new(14, 16) },
                    Expr::IntLit { value: 30, span: Span::new(17, 19) },
                ],
                span: vec_span,
            }],
            span: apply_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-len should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: appendix-a-builtins §A.3 — vec-get bounds-checked index codegen
    #[test]
    fn test_compile_vec_get_inline() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-get v 1))
        let vec_span = Span::new(8, 18);
        let get_span = Span::new(21, 35);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(9, 11) },
                        Expr::IntLit { value: 20, span: Span::new(12, 14) },
                        Expr::IntLit { value: 30, span: Span::new(15, 17) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(22, 29),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(30, 31),
                    },
                    Expr::IntLit { value: 1, span: Span::new(32, 33) },
                ],
                span: get_span,
            }),
            span: Span::new(0, 36),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get should compile: {result:?}");
        assert_eq!(result.unwrap(), 20);
    }

    // spec: appendix-a-builtins §A.3 — vec-get index 0 boundary
    #[test]
    fn test_compile_vec_get_first_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(100, 110);
        let get_span = Span::new(120, 135);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(101, 104) },
                        Expr::IntLit { value: 200, span: Span::new(105, 108) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(121, 128),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(129, 130),
                    },
                    Expr::IntLit { value: 0, span: Span::new(131, 132) },
                ],
                span: get_span,
            }),
            span: Span::new(99, 136),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get index 0 should work: {result:?}");
        assert_eq!(result.unwrap(), 100);
    }

    // spec: appendix-a-builtins §A.3 — vec-get last index boundary
    #[test]
    fn test_compile_vec_get_last_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(200, 210);
        let get_span = Span::new(220, 235);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(201, 202) },
                        Expr::IntLit { value: 2, span: Span::new(203, 204) },
                        Expr::IntLit { value: 3, span: Span::new(205, 206) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(221, 228),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(229, 230),
                    },
                    Expr::IntLit { value: 2, span: Span::new(231, 232) },
                ],
                span: get_span,
            }),
            span: Span::new(199, 236),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get last index should work: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 12-runtime §12.3.3 — vec-set copy-on-write path codegen
    #[test]
    fn test_compile_vec_set_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-len (vec-set v 1 99)))
        // Since v is used twice (vec-set and vec-len), vec-set takes the copy path.
        let vec_span = Span::new(300, 310);
        let set_span = Span::new(320, 340);
        let len_span = Span::new(315, 345);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(301, 303) },
                        Expr::IntLit { value: 20, span: Span::new(304, 306) },
                        Expr::IntLit { value: 30, span: Span::new(307, 309) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(316, 323),
                }),
                args: vec![Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("vec-set"),
                        span: Span::new(321, 328),
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("v"),
                            span: Span::new(329, 330),
                        },
                        Expr::IntLit { value: 1, span: Span::new(331, 332) },
                        Expr::IntLit { value: 99, span: Span::new(333, 335) },
                    ],
                    span: set_span,
                }],
                span: len_span,
            }),
            span: Span::new(299, 346),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-set should compile: {result:?}");
        // vec-set returns a new Vec with same length.
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 12-runtime §12.3.3 — vec-push copy-on-write path codegen
    #[test]
    fn test_compile_vec_push_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [10 20] 30))
        let vec_span = Span::new(400, 410);
        let push_span = Span::new(415, 435);
        let len_span = Span::new(410, 440);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(411, 418),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(416, 424),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(401, 403) },
                            Expr::IntLit { value: 20, span: Span::new(404, 406) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 30, span: Span::new(425, 427) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-push should compile: {result:?}");
        // [10 20] pushed 30 -> len 3
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.3, §4.10 — Vec literal bound in let, accessed via vec-len
    #[test]
    fn test_compile_vec_literal_in_let() {
        // (let [v [1 2 3]] (vec-len v))
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(500, 510);
        let len_span = Span::new(515, 530);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(501, 502) },
                        Expr::IntLit { value: 2, span: Span::new(503, 504) },
                        Expr::IntLit { value: 3, span: Span::new(505, 506) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(516, 523),
                }),
                args: vec![Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(524, 525),
                }],
                span: len_span,
            }),
            span: Span::new(499, 531),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec in let should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.10, §4.11 — Vec literal with computed elements, left-to-right eval
    #[test]
    fn test_compile_vec_literal_with_computed_elements() {
        use cranelisp_types::ResolvedCall;

        // [1 (+ 2 3) 10]
        let add_span = Span::new(603, 610);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: Span::new(601, 602) },
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: Span::new(604, 605),
                    }),
                    args: vec![
                        Expr::IntLit { value: 2, span: Span::new(606, 607) },
                        Expr::IntLit { value: 3, span: Span::new(608, 609) },
                    ],
                    span: add_span,
                },
                Expr::IntLit { value: 10, span: Span::new(611, 613) },
            ],
            span: Span::new(600, 614),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec with computed elements should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1);
            assert_eq!(*data_ptr.add(1), 5); // 2 + 3
            assert_eq!(*data_ptr.add(2), 10);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 05-definitions §5.1, 04-expressions §4.10 — Vec literal as function return value
    #[test]
    fn test_compile_vec_in_function_defn() {
        // (defn make-vec [] [1 2 3])
        // Returns a Vec literal.
        let defn = Defn {
            name: Symbol::from("make-vec"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::VecLit {
                elements: vec![
                Expr::IntLit { value: 1, span: Span::new(701, 702) },
                Expr::IntLit { value: 2, span: Span::new(703, 704) },
                Expr::IntLit { value: 3, span: Span::new(705, 706) },
                ],
                span: Span::new(700, 707),
                },
                span: Span::new(700, 710),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(700, 710),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let ptr = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");
        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-get returns correct element value
    #[test]
    fn test_compile_vec_get_verify_value() {
        use cranelisp_types::ResolvedCall;

        // (let [v [100 200 300]] (vec-get v 2))
        let vec_span = Span::new(808, 818);
        let get_span = Span::new(821, 840);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(809, 812) },
                        Expr::IntLit { value: 200, span: Span::new(813, 816) },
                        Expr::IntLit { value: 300, span: Span::new(817, 820) },
                    ],
                    span: vec_span,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(822, 829),
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(830, 831),
                    },
                    Expr::IntLit { value: 2, span: Span::new(832, 833) },
                ],
                span: get_span,
            }),
            span: Span::new(807, 841),
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get value should compile: {result:?}");
        assert_eq!(result.unwrap(), 300);
    }

    // spec: 12-runtime §12.3.3 — vec-push on temporary Vec (COW in-place path)
    #[test]
    fn test_compile_vec_push_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [1] 2))
        // vec-push on a temporary VecLit — will take COW path (temp = unique).
        let vec_span = Span::new(900, 905);
        let push_span = Span::new(910, 925);
        let len_span = Span::new(905, 930);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(906, 913),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(911, 919),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 1, span: Span::new(901, 902) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 2, span: Span::new(920, 921) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-push on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 2);
    }

    // spec: 12-runtime §12.3.3 — vec-set on temporary Vec (COW in-place path)
    #[test]
    fn test_compile_vec_set_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-set [10 20 30] 0 99))
        let vec_span = Span::new(1000, 1010);
        let set_span = Span::new(1015, 1035);
        let len_span = Span::new(1010, 1040);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1011, 1018),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-set"),
                    span: Span::new(1016, 1023),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(1001, 1003) },
                            Expr::IntLit { value: 20, span: Span::new(1004, 1006) },
                            Expr::IntLit { value: 30, span: Span::new(1007, 1009) },
                        ],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 0, span: Span::new(1024, 1025) },
                    Expr::IntLit { value: 99, span: Span::new(1026, 1028) },
                ],
                span: set_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-set on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.10 — Vec literal in interactive (REPL) mode
    #[test]
    fn test_compile_vec_literal_interactive_mode() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1101, 1103) },
            ],
            span: Span::new(1100, 1104),
        };
        let check = empty_check();

        let result = test_compile_and_run(
            &expr, &check, &empty_tables(),
        );
        assert!(result.is_ok(), "vec in interactive mode should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024);
        assert_eq!(cranelisp_runtime::vec_len(ptr), 1);

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-len on empty Vec returns 0
    #[test]
    fn test_compile_vec_empty_len() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [])
        let vec_span = Span::new(1200, 1202);
        let len_span = Span::new(1195, 1210);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1196, 1203),
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: vec_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty vec len should compile: {result:?}");
        assert_eq!(result.unwrap(), 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-push on empty Vec
    #[test]
    fn test_compile_vec_push_empty_vec() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [] 42))
        let vec_span = Span::new(1300, 1302);
        let push_span = Span::new(1305, 1320);
        let len_span = Span::new(1300, 1325);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1301, 1308),
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(1306, 1314),
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![],
                        span: vec_span,
                    },
                    Expr::IntLit { value: 42, span: Span::new(1315, 1317) },
                ],
                span: push_span,
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "push to empty vec should compile: {result:?}");
        assert_eq!(result.unwrap(), 1);
    }

    // spec: appendix-a-builtins §A.3 — vec-len on empty Vec (duplicate boundary check)
    #[test]
    fn test_compile_vec_len_empty_vec() {
        use cranelisp_types::ResolvedCall;

        let len_span = Span::new(1400, 1420);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1401, 1408),
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: Span::new(1409, 1411),
            }],
            span: len_span,
        };

        let check = CheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 0);
    }

    // spec: 04-expressions §4.10 — nested Vec literals (Vec of Vecs)
    #[test]
    fn test_compile_nested_vec_literals() {
        // [[1 2] [3 4]] — a Vec of Vecs (nested heap values)
        let expr = Expr::VecLit {
            elements: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(1502, 1503) },
                        Expr::IntLit { value: 2, span: Span::new(1504, 1505) },
                    ],
                    span: Span::new(1501, 1506),
                },
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 3, span: Span::new(1508, 1509) },
                        Expr::IntLit { value: 4, span: Span::new(1510, 1511) },
                    ],
                    span: Span::new(1507, 1512),
                },
            ],
            span: Span::new(1500, 1513),
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "nested vec should compile: {result:?}");
        let outer_ptr = result.unwrap();
        assert!(outer_ptr > 1024);
        assert_eq!(cranelisp_runtime::vec_len(outer_ptr), 2);

        // First inner vec.
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            let inner1 = *data;
            assert!(inner1 > 1024, "inner vec should be heap pointer");
            assert_eq!(cranelisp_runtime::vec_len(inner1), 2);
        }

        // Clean up (inner vecs need manual cleanup since no drop glue yet).
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            cranelisp_runtime::vec_drop(*data, 0);
            cranelisp_runtime::vec_drop(*data.add(1), 0);
        }
        cranelisp_runtime::vec_drop(outer_ptr, 0);
    }

    // spec: 04-expressions §4.10 — large Vec literal (10 elements)
    #[test]
    fn test_compile_vec_large_literal() {
        // [0 1 2 3 4 5 6 7 8 9] — 10 elements
        let elements: Vec<Expr> = (0..10)
            .map(|i| Expr::IntLit {
                value: i,
                span: Span::new(1600 + (i as u32) * 2, 1602 + (i as u32) * 2),
            })
            .collect();

        let expr = Expr::VecLit {
            elements,
            span: Span::new(1600, 1620),
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "large vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(cranelisp_runtime::vec_len(ptr), 10);

        unsafe {
            let base = ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            for i in 0..10 {
                assert_eq!(*data.add(i), i as i64);
            }
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // --- Ring 2A: TraitMethod dispatch tests ---

    // spec: 07-traits §7.7, appendix-a-builtins §A.3 — Num.+ trait dispatch inlines to add-i64
    #[test]
    fn test_trait_method_dispatch_inline_add() {
        // (+ 3 4) resolved as TraitMethod Num.+ on Int → should inline as iadd.
        let apply_span = Span::new(100, 110);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: Span::new(101, 102),
            }),
            args: vec![
                Expr::IntLit { value: 3, span: Span::new(103, 104) },
                Expr::IntLit { value: 4, span: Span::new(105, 106) },
            ],
            span: apply_span,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::FQTraitName::new(ModuleFullPath::from("core.num"), "Num".into()),
                method_name: Symbol::from("+"),
                impl_type: cranelisp_types::FQTypeName::new(ModuleFullPath::from("primitives"), "Int".into()),
                mangled_name: cranelisp_types::JitSymbol::from("Num.+$Int"),
            },
        );

        let value = test_compile_and_run(&expr, &check, &empty_tables())
            .expect("TraitMethod inline add should compile");
        assert_eq!(value, 7);
    }

    // spec: 07-traits §7.7, appendix-a-builtins §A.3 — Eq.= trait dispatch on Bool
    #[test]
    fn test_trait_method_dispatch_eq_bool() {
        // (= true true) resolved as TraitMethod Eq.= on Bool → eq-bool.
        let apply_span = Span::new(200, 210);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("="),
                span: Span::new(201, 202),
            }),
            args: vec![
                Expr::BoolLit { value: true, span: Span::new(203, 207) },
                Expr::BoolLit { value: true, span: Span::new(208, 212) },
            ],
            span: apply_span,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::FQTraitName::new(ModuleFullPath::from("core.eq"), "Eq".into()),
                method_name: Symbol::from("="),
                impl_type: cranelisp_types::FQTypeName::new(ModuleFullPath::from("primitives"), "Bool".into()),
                mangled_name: cranelisp_types::JitSymbol::from("Eq.=$Bool"),
            },
        );

        let value = test_compile_and_run(&expr, &check, &empty_tables())
            .expect("TraitMethod eq-bool should compile");
        assert_eq!(value, 1); // true == true → true (1)
    }

    // spec: 07-traits §7.7 — constrained polymorphic fn skipped at definition, monomorphised at call
    #[test]
    fn test_constrained_fn_skipped_in_compile_program() {
        // A constrained fn should be skipped (not compiled).
        let defn = Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![],
                body: Expr::IntLit { value: 0, span: Span::new(10, 11) },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(30, 32) },
                span: Span::new(25, 40),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(25, 40),
        };

        let program: Program = vec![
            TopLevel::Defn(defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        // Mark "add" as constrained — should be skipped during compilation.
        check.constrained_fn_names.insert(Symbol::from("add"));

        let value = test_compile_program_and_run(&program, &check, &empty_tables())
            .expect("should compile with constrained fn skipped");
        assert_eq!(value, 42);
    }

    // spec: 07-traits §7.7 — no default method defns produces empty extras
    #[test]
    fn test_collect_extra_defns_empty() {
        let check = empty_check();
        // Verify default_method_defns is empty in a fresh CheckResult.
        assert!(check.default_method_defns.is_empty());
    }

    // spec: 07-traits §7.7 — default trait methods compiled as extra defns
    #[test]
    fn test_compile_with_default_method_defns() {
        // A program with only a main function, but check has a default method defn.
        // The default method defn should be compiled alongside main.
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("default-ne"),
                        span: Span::new(10, 20),
                    }),
                    args: vec![
                        Expr::IntLit { value: 1, span: Span::new(21, 22) },
                        Expr::IntLit { value: 2, span: Span::new(23, 24) },
                    ],
                    span: Span::new(9, 25),
                },
                span: Span::new(0, 30),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 30),
        };

        let default_defn = Defn {
            name: Symbol::from("default-ne"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![],
                body: Expr::IntLit { value: 77, span: Span::new(0, 2) },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let program: Program = vec![TopLevel::Defn(main_defn)];
        let mut check = empty_check();
        check.default_method_defns.push(default_defn);

        let value = test_compile_program_and_run(&program, &check, &empty_tables())
            .expect("program with default method defns should compile");
        assert_eq!(value, 77, "should call the default method defn");
    }

    // spec: 12-runtime §12.5, 07-traits §7.7 — TCO for monomorphised self-recursive call
    //
    // When a constrained-poly function like `countdown` is monomorphised to
    // `countdown$Int`, the body contains a self-recursive call `(countdown ...)`
    // that the typechecker resolves to `SigDispatch { mangled_name: "countdown$Int" }`.
    // The backend's TCO check must recognize this as self-recursion.
    //
    // This test compiles a simple recursive function and verifies it completes
    // without stack overflow (1M iterations would blow the stack without TCO).
    #[test]
    fn test_mono_defn_self_recursive_tco() {
        // countdown$Int: (defn countdown$Int [n] (if (= n 0) 0 (countdown$Int (- n 1))))
        // Simplified: use intrinsic primitives instead of trait dispatch.
        let n_span = Span::new(10, 11);
        let zero_span = Span::new(20, 21);
        let eq_span = Span::new(30, 40);
        let sub_span = Span::new(50, 60);
        let recurse_span = Span::new(70, 90);
        let if_span = Span::new(5, 95);
        let result_span = Span::new(92, 93);

        // Build: (if (eq-i64 n 0) 0 (countdown$Int (sub-i64 n 1)))
        let cond = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("eq-i64"),
                span: Span::new(31, 37),
            }),
            args: vec![
                Expr::Var { name: Symbol::from("n"), span: n_span },
                Expr::IntLit { value: 0, span: zero_span },
            ],
            span: eq_span,
        };

        let sub_call = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("sub-i64"),
                span: Span::new(51, 58),
            }),
            args: vec![
                Expr::Var { name: Symbol::from("n"), span: Span::new(55, 56) },
                Expr::IntLit { value: 1, span: Span::new(57, 58) },
            ],
            span: sub_span,
        };

        // The recursive call: callee is "countdown" (original name),
        // but it's resolved to countdown$Int via SigDispatch.
        let recurse = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("countdown"),
                span: Span::new(71, 80),
            }),
            args: vec![sub_call],
            span: recurse_span,
        };

        let body = Expr::If {
            cond: Box::new(cond),
            then_branch: Box::new(Expr::IntLit { value: 0, span: result_span }),
            else_branch: Box::new(recurse),
            span: if_span,
        };

        let countdown_defn = Defn {
            name: Symbol::from("countdown$Int"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("n")],
                param_annotations: vec![],
                body,
                span: Span::new(0, 100),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 100),
        };

        // Set up method resolutions:
        // - eq_span: BuiltinFn("eq-i64") for the equality check
        // - sub_span: BuiltinFn("sub-i64") for the subtraction
        // - recurse_span: SigDispatch("countdown$Int") for the self-recursive call
        let mut check = empty_check();
        check.method_resolutions.insert(
            eq_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("eq-i64"),
            },
        );
        check.method_resolutions.insert(
            sub_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("sub-i64"),
            },
        );
        check.method_resolutions.insert(
            recurse_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("countdown$Int"),
            },
        );

        // Compile with direct calls (no GOT).
        let mut jit = Jit::new().unwrap();
        jit.declare_intrinsics().unwrap();
        let func_ids = jit.declare_functions(&[&countdown_defn]).unwrap();

        let arities: HashMap<Symbol, usize> =
            vec![(Symbol::from("countdown$Int"), 1)].into_iter().collect();

        let tables = empty_tables();
        let ctx = jit.build_compile_context(
            &check, &func_ids, &arities,
            &tables, ModuleFullPath::from("test"),
        );
        jit.compile_defn(&countdown_defn, ctx).unwrap();
        let countdown_ptr = jit.finalize_and_get_ptr(&Symbol::from("countdown$Int"), 1).unwrap();

        // Call with 1_000_000 — without TCO this would stack overflow.
        let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(countdown_ptr) };
        let result = func(1_000_000);
        assert_eq!(result, 0, "TCO should allow 1M recursive calls without stack overflow");
    }

    // --- compile_to_module module tests ---

    // spec: 08-modules §8.3 — two modules with same-named function compiled separately
    // Regression test: verifies module prefixing avoids name collisions.
    // With compile_to_module, each module gets its own JIT — no collision possible.
    #[test]
    fn test_module_prefix_applied() {
        // Module "mod_a" defines "val" returning 100.
        let val_a = Defn {
            name: Symbol::from("val"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 100, span: Span::new(0, 3) },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };
        let program_a: Program = vec![TopLevel::Defn(val_a)];
        let check_a = empty_check();

        let tables = empty_tables();
        let mut jit_a = Jit::new().unwrap();
        let result_a = compile_to_module(
            ModuleFullPath::from("mod_a"),
            &program_a,
            &check_a,
            &tables,
            jit_a.jit_module(),
        ).expect("module A should compile");
        jit_a.finalize().unwrap();

        // The result should have the function with a module-qualified name.
        assert!(
            result_a.func_ids.contains_key(&Symbol::from("mod_a/val")),
            "func_ids should contain module-qualified name: {:?}",
            result_a.func_ids.keys().collect::<Vec<_>>()
        );

        // Execute module A's "val".
        let entry_id = result_a.entry_func_id.expect("should have entry");
        let ptr = jit_a.get_finalized_ptr(entry_id);
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        assert_eq!(func(), 100, "module A's val should return 100");

        // Module B also defines "val" returning 200 — compiles into a separate JIT.
        let val_b = Defn {
            name: Symbol::from("val"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 200, span: Span::new(100, 103) },
                span: Span::new(100, 120),
            }],
            visibility: Visibility::Public,
            span: Span::new(100, 120),
        };
        let program_b: Program = vec![TopLevel::Defn(val_b)];
        let check_b = empty_check();

        let mut jit_b = Jit::new().unwrap();
        let result_b = compile_to_module(
            ModuleFullPath::from("mod_b"),
            &program_b,
            &check_b,
            &tables,
            jit_b.jit_module(),
        ).expect("module B should compile without collision");
        jit_b.finalize().unwrap();

        let entry_b = result_b.entry_func_id.expect("should have entry");
        let ptr_b = jit_b.get_finalized_ptr(entry_b);
        let func_b: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr_b) };
        assert_eq!(func_b(), 200, "module B's val should return 200");
    }

    // --- multi-sig defn tests ---

    // spec: 05-definitions §5.1.2 — mangled name construction
    #[test]
    fn test_build_mangled_name_single_param() {
        let name = Symbol::from("identity");
        let mangled = build_mangled_name(&name, &[Type::Int]);
        assert_eq!(mangled, "identity$Int");
    }

    // spec: 05-definitions §5.1.2 — mangled name with multiple params
    #[test]
    fn test_build_mangled_name_multiple_params() {
        let name = Symbol::from("add");
        let mangled = build_mangled_name(&name, &[Type::Int, Type::Int]);
        assert_eq!(mangled, "add$Int+Int");
    }

    // spec: 05-definitions §5.1.2 — mangled name with mixed types
    #[test]
    fn test_build_mangled_name_mixed_types() {
        let name = Symbol::from("convert");
        let mangled = build_mangled_name(&name, &[Type::Float, Type::Bool]);
        assert_eq!(mangled, "convert$Float+Bool");
    }

    // spec: 05-definitions §5.1.2 — expand multi-sig defn into variant defns
    #[test]
    fn test_expand_multi_sig_defn() {
        let variant1_span = Span::new(10, 30);
        let variant2_span = Span::new(40, 60);

        let defn = Defn {
            name: Symbol::from("f"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16) },
                    span: variant1_span,
                },
                DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![],
                    body: Expr::Var { name: Symbol::from("a"), span: Span::new(45, 46) },
                    span: variant2_span,
                },
            ],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 70),
        };

        // Set up expr_types: variant1 is (Fn [Int] Int), variant2 is (Fn [Bool Bool] Bool)
        let mut expr_types: HashMap<Span, Type> = HashMap::new();
        expr_types.insert(variant1_span, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
        expr_types.insert(variant2_span, Type::Fn(vec![Type::Bool, Type::Bool], Box::new(Type::Bool)));

        let expanded = expand_multi_sig_defn(&defn, &expr_types).unwrap();
        assert_eq!(expanded.len(), 2);
        assert_eq!(expanded[0].name, Symbol::from("f$Int"));
        assert_eq!(expanded[1].name, Symbol::from("f$Bool+Bool"));
        assert_eq!(expanded[0].params().len(), 1);
        assert_eq!(expanded[1].params().len(), 2);
    }

    // spec: 05-definitions §5.1.2 — multi-sig defn compiles and dispatches correctly
    //
    // Defines a multi-sig function `f` with two variants:
    //   (defn f ([x] x) ([a b] a))      — identity on 1 arg, first on 2 args
    // Then defines main that calls the first variant via SigDispatch.
    #[test]
    fn test_compile_multi_sig_defn_end_to_end() {
        let variant1_span = Span::new(10, 30);
        let variant2_span = Span::new(40, 60);

        let multi_defn = Defn {
            name: Symbol::from("f"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16) },
                    span: variant1_span,
                },
                DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![],
                    body: Expr::Var { name: Symbol::from("a"), span: Span::new(45, 46) },
                    span: variant2_span,
                },
            ],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 70),
        };

        // main calls f$Int(42)
        let call_span = Span::new(100, 120);
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("f"),
                        span: Span::new(101, 102),
                    }),
                    args: vec![Expr::IntLit { value: 42, span: Span::new(103, 105) }],
                    span: call_span,
                },
                span: Span::new(95, 125),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(95, 125),
        };

        let program: Program = vec![
            TopLevel::Defn(multi_defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        // Register variant types so expand_multi_sig_defn can compute mangled names.
        check.expr_types.insert(variant1_span, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
        check.expr_types.insert(variant2_span, Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)));
        // Register SigDispatch for the call site.
        check.method_resolutions.insert(
            call_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("f$Int"),
            },
        );

        let result = test_compile_program_and_run(&program, &check, &empty_tables())
            .expect("multi-sig program should compile");
        assert_eq!(result, 42, "should dispatch to f$Int and return 42");
    }

    // spec: 05-definitions §5.1.2 — multi-sig dispatch to second variant
    #[test]
    fn test_compile_multi_sig_second_variant() {
        let variant1_span = Span::new(10, 30);
        let variant2_span = Span::new(40, 60);

        let multi_defn = Defn {
            name: Symbol::from("g"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16) },
                    span: variant1_span,
                },
                DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![],
                    // Return b (second param) to prove we dispatched to the right variant.
                    body: Expr::Var { name: Symbol::from("b"), span: Span::new(45, 46) },
                    span: variant2_span,
                },
            ],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 70),
        };

        // main calls g$Int+Int(10, 99) — should return 99 (the second arg)
        let call_span = Span::new(100, 120);
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("g"),
                        span: Span::new(101, 102),
                    }),
                    args: vec![
                        Expr::IntLit { value: 10, span: Span::new(103, 105) },
                        Expr::IntLit { value: 99, span: Span::new(106, 108) },
                    ],
                    span: call_span,
                },
                span: Span::new(95, 125),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(95, 125),
        };

        let program: Program = vec![
            TopLevel::Defn(multi_defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        check.expr_types.insert(variant1_span, Type::Fn(vec![Type::Int], Box::new(Type::Int)));
        check.expr_types.insert(variant2_span, Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int)));
        check.method_resolutions.insert(
            call_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("g$Int+Int"),
            },
        );

        let result = test_compile_program_and_run(&program, &check, &empty_tables())
            .expect("multi-sig program should compile");
        assert_eq!(result, 99, "should dispatch to g$Int+Int and return second arg (99)");
    }

    // spec: 05-definitions §5.1.2 — multi-sig defn with missing type info errors
    #[test]
    fn test_expand_multi_sig_missing_type_info() {
        let defn = Defn {
            name: Symbol::from("f"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Expr::IntLit { value: 1, span: Span::new(15, 16) },
                    span: Span::new(10, 30),
                },
            ],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 40),
        };

        // No expr_types registered — should error.
        let expr_types: HashMap<Span, Type> = HashMap::new();
        let result = expand_multi_sig_defn(&defn, &expr_types);
        assert!(result.is_err(), "should error when type info is missing");
    }

    // spec: 05-definitions §5.1.2 — concrete_type_name covers all primitive types
    #[test]
    fn test_concrete_type_name_all_primitives() {
        assert_eq!(concrete_type_name(&Type::Int).unwrap().name.as_ref(), "Int");
        assert_eq!(concrete_type_name(&Type::Float).unwrap().name.as_ref(), "Float");
        assert_eq!(concrete_type_name(&Type::Bool).unwrap().name.as_ref(), "Bool");
        assert_eq!(concrete_type_name(&Type::String).unwrap().name.as_ref(), "String");
        assert!(concrete_type_name(&Type::Var(0)).is_none());
    }
}
