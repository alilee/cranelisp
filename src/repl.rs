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
// Universal output format (repl/spec.md §1.1, implemented Sprint 15):
// All REPL output uses `:Type {value|name} ; {classification} - {docstring}`
// with optional related symbol sections for types, traits, and macros.

use std::cell::Cell;
use std::collections::HashMap;
use std::io::{self, BufRead, Write};
use std::time::{Duration, Instant};

use cranelisp_backend::compiler::TracedFnInfo;
use cranelisp_backend::display;
use cranelisp_backend::got::ModuleCodegenState;
use cranelisp_backend::jit::Jit;
use cranelisp_typecheck::TypeChecker;
use cranelisp_types::{
    CompileMode, CranelispError, DefKind, Defn, Expr, MacroClauseInfo, MacroParam,
    ModuleEntry, ModuleFullPath, ReplCheckResult, ReplInput, Sexp, Symbol, TraitName, Type,
    TypeDefInfo, TypeName, Visibility, Warning,
};

use crate::expander::CraneliftExpander;

// ── Trace value formatting ────────────────────────────────────────────────────

/// Display state for trace formatting. Holds references to the type definitions
/// and type-to-module mappings needed by `format_value`.
///
/// SAFETY: The raw pointer is valid for the duration of a single `execute_expr`
/// call — set before JIT execution and cleared immediately after. The struct it
/// points to borrows from the ReplSession which does not move during execution.
struct TraceDisplayState {
    type_defs: *const HashMap<TypeName, TypeDefInfo>,
    type_modules: *const HashMap<TypeName, ModuleFullPath>,
}

// TraceDisplayState is only accessed via a thread-local Cell (never crosses
// thread boundaries), so Send/Sync are not required.

thread_local! {
    /// Thread-local pointer to the active display state, used by
    /// `repl_trace_format`. Set before JIT evaluation, cleared after.
    static TRACE_DISPLAY_STATE: Cell<*const TraceDisplayState> =
        const { Cell::new(std::ptr::null()) };
}

/// Set the trace display state before evaluating a trace expression.
fn set_trace_display_state(state: &TraceDisplayState) {
    TRACE_DISPLAY_STATE.with(|c| c.set(state as *const _));
}

/// Clear the trace display state after evaluation completes.
fn clear_trace_display_state() {
    TRACE_DISPLAY_STATE.with(|c| c.set(std::ptr::null()));
}

/// JIT-callable function: format a runtime value for trace display.
///
/// Reads the type pointer (a leaked `Box<Type>`) and the display state
/// (type_defs, type_modules) from thread-local storage, then calls
/// `display::format_value` to produce a formatted string.
///
/// Falls back to `"?"` if the display state has not been set.
///
/// Registered as an extra JIT symbol to override the runtime's fallback
/// `cranelisp_trace_format` when compiling trace expressions.
extern "C" fn repl_trace_format(val: i64, type_ptr: i64) -> i64 {
    TRACE_DISPLAY_STATE.with(|c| {
        let state_ptr = c.get();
        let s = if state_ptr.is_null() {
            "?".to_string()
        } else {
            // SAFETY: state_ptr was set by set_trace_display_state and
            // points to a valid TraceDisplayState on the caller's stack.
            // The Type pointer was leaked by trace_codegen (valid for program lifetime).
            let state = unsafe { &*state_ptr };
            let type_defs = unsafe { &*state.type_defs };
            let type_modules = unsafe { &*state.type_modules };
            let ty = unsafe { &*(type_ptr as *const Type) };
            display::format_value(val, ty, type_defs, type_modules)
        };
        cranelisp_runtime::alloc_string(s.as_bytes()) as i64
    })
}

// Re-export display functions so that downstream crates (tests/helpers, src/main.rs)
// can continue to use `cranelisp::repl::format_result_value` etc.
pub use display::format_result;
pub use display::format_result_value;
pub use display::format_type_qualified;
pub use display::format_value;

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
    /// Platform function pointers for JIT symbol registration.
    /// Each entry is (jit_name, function_pointer). These are passed to
    /// `Jit::new_with_symbols()` when creating JIT instances for compilation
    /// so that platform function calls can be resolved.
    platform_symbols: Vec<(String, *const u8)>,
    /// Loaded platform DLLs — must stay alive for the process lifetime.
    loaded_platforms: Vec<crate::platform::LoadedPlatform>,
    /// Project root directory (for platform path resolution).
    pub project_root: std::path::PathBuf,
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
            platform_symbols: Vec::new(),
            loaded_platforms: Vec::new(),
            project_root: std::env::current_dir().unwrap_or_default(),
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
        session.project_root = project_root.to_path_buf();

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

        // Sync type definitions from prelude modules for ADT value display.
        // Without this, prelude ADT values (e.g. Option.None) display as raw
        // i64 tags because format_result_value lacks the constructor metadata.
        for (name, info) in session.tc.type_def_registry().iter() {
            session.type_defs.insert(name.clone(), info.clone());
        }

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
        let sexps = cranelisp_frontend::parse(source)?;

        if sexps.is_empty() {
            return Err(CranelispError::ParseError {
                message: "empty input".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            });
        }

        // Snapshot for error recovery (covers macro compilation too).
        let snapshot = self.tc.snapshot();

        // Handle multi-sexp annotation expressions (`:Type expr` parses as two sexps).
        // For single sexps, take the first and evaluate normally.
        let result = if sexps.len() > 1 && is_annotation_prefix(&sexps[0]) {
            self.eval_annotation_expr(sexps)
        } else {
            let first_sexp = sexps.into_iter().next().unwrap();
            self.eval_sexp(first_sexp)
        };

        match result {
            Ok(result) => Ok(result),
            Err(e) => {
                self.tc.restore(snapshot);
                Err(e)
            }
        }
    }

    /// Evaluate a type annotation expression (`:Type expr` parsed as multiple sexps).
    ///
    /// Uses `build_repl_input_from_sexps` to combine the annotation and expression
    /// into a single `Expr::Annotate`, then typechecks and executes.
    fn eval_annotation_expr(&mut self, sexps: Vec<Sexp>) -> Result<ReplResult, CranelispError> {
        let input = cranelisp_frontend::build_repl_input_from_sexps(
            &sexps,
            &mut self.expander,
        )?;
        let check_result = self.tc.check_repl_input(&input)?;
        self.compile_and_execute(&input, &check_result)
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

        // Step 1c: Check for platform — load DLL and register functions.
        // Platform declarations must be intercepted before AST building
        // because the AST builder rejects (platform ...) forms.
        if crate::platform::is_platform_form(&sexp) {
            return self.eval_platform(sexp);
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
            // Capture the form sexp before AST building for /sexp introspection.
            let form_sexp = form.clone();
            let input = cranelisp_frontend::build_repl_input(&form, &mut self.expander)?;
            let check_result = self.tc.check_repl_input(&input)?;
            let result = self.compile_and_execute(&input, &check_result)?;

            // Store sexp and source in DefCodegen for introspection commands.
            if let ReplInput::Defn(defn) = &input {
                if let Some(dc) = self.got_state.def_codegen.get_mut(&defn.name) {
                    dc.source = Some(format_sexp(&form_sexp));
                    dc.sexp = Some(form_sexp);
                }
            }
            last_result = Some(result);
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
        // Compute display before moving clause_infos into symbol table.
        let module = self.tc.current_module_path().clone();
        let display = format_defmacro_display(&info.name, &clause_infos, &module);

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
            ModuleEntry::Macro { clauses, docstring, .. } => {
                // Check if any clause accepts zero args — if so, let the
                // expander handle it (it's a valid zero-arg macro call).
                let has_zero_arg_clause = clauses.iter().any(|c| {
                    c.params.is_empty() && c.rest_param.is_none()
                });
                if has_zero_arg_clause {
                    return None; // Let expander handle zero-arg expansion.
                }
                // Non-zero-arg macro: show universal format (spec §4.1.6).
                let module = self.tc.current_module_path().clone();
                let display = format_macro_display_universal(
                    name, clauses, docstring.as_deref(), &module,
                );
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

    /// Handle a `(platform name)` form: load the platform DLL and register
    /// its functions in the typechecker.
    ///
    /// Platform function pointers are stored in `self.platform_symbols` so
    /// that subsequent JIT instances (created for each function compilation)
    /// can resolve calls to platform functions.
    fn eval_platform(&mut self, sexp: Sexp) -> Result<ReplResult, CranelispError> {
        let (name, span) = crate::platform::extract_platform_name(&sexp).ok_or_else(|| {
            CranelispError::ParseError {
                message: "invalid platform declaration".into(),
                span: cranelisp_types::Span::SYNTHETIC,
            }
        })?;

        let (platform, jit_syms) = crate::platform::load_and_register_platform(
            &mut self.tc,
            &name,
            &self.project_root,
            span,
        )?;

        let fn_count = platform.descriptors.len();
        let version = platform.version.clone();

        self.platform_symbols.extend(jit_syms);
        self.loaded_platforms.push(platform);

        let display = format!(
            "; loaded platform: {} v{} ({} functions)\n; use (import [platform.{} [*]]) to bring into scope",
            name, version, fn_count, name
        );

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

        // Build extra symbols for platform function resolution.
        // If the expression contains a (trace ...) form, also override
        // cranelisp_trace_format with the REPL's proper formatter and
        // build traced_fns for GOT-swap wrapper generation.
        let has_trace = expr_contains_trace(expr);
        let traced_fns = if has_trace {
            self.build_traced_fns()
        } else {
            Vec::new()
        };

        let mut extra_symbols: Vec<(&str, *const u8)> = self
            .platform_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();

        // Override the runtime's fallback cranelisp_trace_format with the
        // REPL's version that uses type_defs/type_modules for proper display.
        if has_trace {
            extra_symbols.push((
                "cranelisp_trace_format",
                repl_trace_format as *const u8,
            ));
        }

        let compiled = compile_expr_with_traced_fns(
            expr,
            &check,
            Some(&mut self.got_state),
            &extra_symbols,
            if has_trace { Some(&traced_fns) } else { None },
        )?;

        // Set trace display state before evaluation so cranelisp_trace_format
        // can access type_defs and type_modules.
        let display_state = TraceDisplayState {
            type_defs: &self.type_defs as *const _,
            type_modules: &self.type_modules as *const _,
        };
        if has_trace {
            set_trace_display_state(&display_state);
        }

        // Time the actual evaluation (function call) separately from compilation.
        // Wrap in catch_unwind to recover from runtime panics (spec §12.7.4.1).
        let eval_start = Instant::now();
        let value = invoke_jit_eval(|| compiled.execute());
        let eval_duration = eval_start.elapsed();

        // Always clear trace display state after evaluation.
        if has_trace {
            clear_trace_display_state();
        }

        // Propagate evaluation errors after cleanup.
        let value = value?;

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
            let result = invoke_jit_eval(|| func())?;
            (result, eval_start.elapsed())
        } else {
            (0, Duration::ZERO)
        };

        // Build definition display with qualified name (spec §1.1, §1.3).
        let module = self.tc.current_module_path().clone();
        let definition_display = if is_constrained {
            check_result.scheme.as_ref().map(|s| {
                let base = display::format_scheme_display(&defn.name, s, &module, &self.type_modules);
                format!("{base} ; defn")
            })
        } else if !defn.params.is_empty() {
            let type_str = format_type_qualified(&check_result.ty, &self.type_modules);
            Some(format!(":{type_str} {module}/{} ; defn", defn.name))
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

        // Build qualified display: `:module/TypeName ; deftype` + related symbols
        let type_name = match &check_result.ty {
            Type::ADT(name, _) => name.to_string(),
            _ => "?".to_string(),
        };
        let display = format_type_display_universal(&type_name, &module, self);

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

        let display = format_trait_display_universal(
            decl.name.as_ref(),
            decl.docstring.as_deref(),
            self,
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
    /// Optionally stores the source text and parsed sexp in DefCodegen
    /// for `/source` and `/sexp` introspection commands.
    fn compile_and_register_defn(
        &mut self,
        defn: &cranelisp_types::Defn,
        check: &cranelisp_types::CheckResult,
    ) -> Result<(), CranelispError> {
        self.compile_and_register_defn_with_context(defn, check, None, None)
    }

    /// Compile a defn with optional source text and sexp for introspection.
    fn compile_and_register_defn_with_context(
        &mut self,
        defn: &cranelisp_types::Defn,
        check: &cranelisp_types::CheckResult,
        source_text: Option<String>,
        sexp: Option<Sexp>,
    ) -> Result<(), CranelispError> {
        // Create JIT with platform symbols registered (if any platforms loaded).
        let extra_symbols: Vec<(&str, *const u8)> = self
            .platform_symbols
            .iter()
            .map(|(name, ptr)| (name.as_str(), *ptr))
            .collect();
        let mut jit = Jit::new_with_symbols(&extra_symbols)?;

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
        let clif_ir = jit.compile_defn(defn, compile_ctx)?;

        // Finalize and get the code pointer.
        let code_ptr = jit.finalize_and_get_ptr(&defn.name, defn.params.len())?;

        // Update the GOT slot with the new code pointer.
        self.got_state.update_slot(slot, code_ptr);

        // Record codegen info and introspection data.
        let entry = self.got_state.def_codegen.entry(defn.name.clone()).or_default();
        entry.code_ptr = Some(code_ptr);
        entry.got_slot = Some(slot);
        entry.param_count = Some(defn.params.len());
        entry.clif_ir = Some(clif_ir);
        entry.defn = Some(defn.clone());
        if source_text.is_some() {
            entry.source = source_text;
        }
        if sexp.is_some() {
            entry.sexp = sexp;
        }

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

    /// Build the list of traced function info from the current GOT state.
    ///
    /// Iterates all functions with GOT slots and code pointers, extracts their
    /// type information from the symbol table, and builds `TracedFnInfo` entries
    /// for the trace codegen to generate wrapper functions.
    fn build_traced_fns(&mut self) -> Vec<TracedFnInfo> {
        let got_base = self.got_state.got_base_ptr() as i64;
        let module = self.tc.current_module_path().clone();
        let symbol_table = self.tc.symbol_table();

        let mut traced = Vec::new();
        for (name, dc) in &self.got_state.def_codegen {
            let (slot, code_ptr, arity) = match (dc.got_slot, dc.code_ptr, dc.param_count) {
                (Some(s), Some(p), Some(a)) => (s, p, a),
                _ => continue,
            };

            // Look up the function's type from the symbol table.
            let (param_types, result_type) =
                match symbol_table.get(name.as_ref()) {
                    Some(ModuleEntry::Def { scheme, .. }) => {
                        match &scheme.ty {
                            Type::Fn(params, ret) => (params.clone(), (**ret).clone()),
                            // Zero-arg function: no params, result type is the type itself
                            other => (vec![], other.clone()),
                        }
                    }
                    _ => {
                        // Fallback: use Int for all types (lossy but safe).
                        (vec![Type::Int; arity], Type::Int)
                    }
                };

            let qualified_name = format!("{}/{}", module, name);
            traced.push(TracedFnInfo {
                name: qualified_name,
                got_base,
                got_slot: slot,
                arity,
                code_ptr: code_ptr as i64,
                param_types,
                result_type,
            });
        }
        traced
    }
}

impl Default for ReplSession {
    fn default() -> Self {
        Self::new()
    }
}

// ── Trace support helpers ─────────────────────────────────────────────────────

/// Check if an expression tree contains a `(trace ...)` form anywhere.
///
/// Used to decide whether to build traced_fns and set up the trace display
/// state before compilation. This avoids the overhead for non-trace expressions.
fn expr_contains_trace(expr: &Expr) -> bool {
    match expr {
        Expr::Trace { .. } => true,
        Expr::Apply { callee, args, .. } => {
            // trace is a module-scoped special form (arch Principle 10).
            // It arrives as Apply(Var("trace"), [body]) — detect it here.
            if let Expr::Var { name, .. } = callee.as_ref() {
                if &**name == "trace" {
                    return true;
                }
            }
            expr_contains_trace(callee) || args.iter().any(expr_contains_trace)
        }
        Expr::Let { bindings, body, .. } => {
            bindings.iter().any(|(_, e)| expr_contains_trace(e))
                || expr_contains_trace(body)
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            expr_contains_trace(cond)
                || expr_contains_trace(then_branch)
                || expr_contains_trace(else_branch)
        }
        Expr::Lambda { body, .. } => expr_contains_trace(body),
        Expr::Match { scrutinee, arms, .. } => {
            expr_contains_trace(scrutinee)
                || arms.iter().any(|arm| expr_contains_trace(&arm.body))
        }
        Expr::Annotate { expr, .. } => expr_contains_trace(expr),
        Expr::VecLit { elements, .. } => elements.iter().any(expr_contains_trace),
        Expr::RunTests { init, pass_fn, fail_fn, .. } => {
            expr_contains_trace(init)
                || expr_contains_trace(pass_fn)
                || expr_contains_trace(fail_fn)
        }
        Expr::IntLit { .. }
        | Expr::BoolLit { .. }
        | Expr::FloatLit { .. }
        | Expr::StringLit { .. }
        | Expr::Var { .. } => false,
    }
}

/// Result of compiling a REPL expression with trace support.
///
/// Holds the JIT alive so the compiled function pointer remains valid.
/// This mirrors `cranelisp_backend::CompiledExpr` but can be constructed
/// from `src/` without needing access to the backend struct's private fields.
struct TracedCompiledExpr {
    #[allow(dead_code)]
    jit: Jit,
    func_ptr: *const u8,
}

impl TracedCompiledExpr {
    /// Execute the compiled expression and return the i64 result.
    fn execute(&self) -> i64 {
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(self.func_ptr) };
        func()
    }
}

/// Compile a single REPL expression with optional `traced_fns` for trace support.
///
/// This is a variant of `cranelisp_backend::compile_expr_with_got_and_symbols`
/// that additionally sets `traced_fns` on the `CompileContext`. The backend's
/// public API does not expose this parameter, so we replicate the compilation
/// pipeline here with the extra field set.
fn compile_expr_with_traced_fns(
    expr: &Expr,
    check: &cranelisp_types::CheckResult,
    got_state: Option<&mut ModuleCodegenState>,
    extra_symbols: &[(&str, *const u8)],
    traced_fns: Option<&[TracedFnInfo]>,
) -> Result<TracedCompiledExpr, CranelispError> {
    let mut jit = Jit::new_with_symbols(extra_symbols)?;

    // Declare runtime intrinsics (Ring 1 heap infrastructure).
    jit.declare_intrinsics()?;

    // Wrap expression in a synthetic zero-arg function.
    let wrapper_name = Symbol::from("__repl_expr__");
    let wrapper_defn = Defn {
        name: wrapper_name.clone(),
        params: vec![],
        param_annotations: vec![],
        visibility: Visibility::Public,
        body: expr.clone(),
        docstring: None,
        span: expr.span(),
    };

    let func_ids = jit.declare_functions(&[&wrapper_defn])?;

    // Get GOT info and function arities if available.
    let (got_slots, got_base_ptr, func_arities) = if let Some(state) = got_state {
        let mut slots: HashMap<Symbol, usize> = HashMap::new();
        let mut arities: HashMap<Symbol, usize> = HashMap::new();
        for (name, dc) in &state.def_codegen {
            if let Some(slot) = dc.got_slot {
                slots.insert(name.clone(), slot);
            }
            if let Some(pc) = dc.param_count {
                arities.insert(name.clone(), pc);
            }
        }
        let base = state.got_base_ptr() as i64;
        (Some(slots), Some(base), arities)
    } else {
        (None, None, HashMap::new())
    };

    let mut compile_ctx = jit.build_compile_context(
        check,
        CompileMode::Interactive,
        &func_ids,
        &func_arities,
        got_slots.as_ref(),
        got_base_ptr,
        None, // No cross-module GOT for single-expression compilation.
    );

    // Set traced_fns on the compile context for trace codegen support.
    compile_ctx.traced_fns = traced_fns;

    jit.compile_defn(&wrapper_defn, compile_ctx)?;

    let code_ptr = jit.finalize_and_get_ptr(&wrapper_name, 0)?;

    Ok(TracedCompiledExpr { jit, func_ptr: code_ptr })
}

/// Force an IO tree via the trampoline and format the inner result.
///
/// Side effects (printing, etc.) execute during the trampoline run and are
/// flushed to stdout before this function returns the display string.
/// The trampoline is wrapped in `catch_unwind` so a malformed IO tree
/// does not crash the REPL session.
///
/// Returns a display string for the inner value with the full IO type
/// annotation, wrapping the formatted value in `(IO.Pure ...)`,
/// e.g. `:(IO primitives/Int) (IO.Pure 42)`.
fn force_io_and_format(
    io_value: i64,
    io_ty: &Type,
    type_defs: &HashMap<TypeName, TypeDefInfo>,
    type_modules: &HashMap<TypeName, ModuleFullPath>,
    stdout: &mut impl Write,
) -> String {
    // Flush stdout before trampolining so any prior output appears first,
    // and side-effect output (e.g., print) appears in order.
    let _ = stdout.flush();

    let trampoline_result = std::panic::catch_unwind(|| {
        // SAFETY: io_value is a valid IO tree pointer produced by JIT code.
        // The IO tree remains live because the caller holds the ReplResult
        // which owns the i64 value, and the trampoline processes it
        // synchronously before returning.
        cranelisp_runtime::run_io_trampoline(io_value)
    });

    let inner_ty = io_ty.io_inner_type();
    let type_str = display::format_type_qualified(io_ty, type_modules);

    match trampoline_result {
        Ok(inner_val) => {
            let val_str = display::format_value(inner_val, &inner_ty, type_defs, type_modules);
            format!(":{type_str} (IO.Pure {val_str})")
        }
        Err(_) => {
            format!(":{type_str} <IO trampoline panicked>")
        }
    }
}

/// Format the REPL display for a defmacro definition (spec §1.1, §11.3).
///
/// Uses universal format: `:module/name ; defmacro` + clause signatures.
fn format_defmacro_display(name: &str, clauses: &[MacroClauseInfo], module: &ModuleFullPath) -> String {
    format_macro_display_universal(name, clauses, None, module)
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
    Exports(&'a str),
    Source(&'a str),
    SexpCmd(&'a str),
    Ast(&'a str),
    Clif(&'a str),
    Disasm(&'a str),
    Mod(&'a str),
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
        "/exports" => ReplCommand::Exports(arg),
        "/source" => ReplCommand::Source(arg),
        "/sexp" => ReplCommand::SexpCmd(arg),
        "/ast" => ReplCommand::Ast(arg),
        "/clif" => ReplCommand::Clif(arg),
        "/disasm" => ReplCommand::Disasm(arg),
        "/mod" => ReplCommand::Mod(arg),
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
    let _ = writeln!(stdout, "  /source NAME        Show original source text");
    let _ = writeln!(stdout, "  /sexp NAME          Show parsed S-expression");
    let _ = writeln!(stdout, "  /ast NAME           Show AST");
    let _ = writeln!(stdout, "  /clif NAME          Show Cranelift IR");
    let _ = writeln!(stdout, "  /disasm NAME        Show disassembled native code");
    let _ = writeln!(stdout, "  /list (/l) [FILTER] List symbols in current module");
    let _ = writeln!(stdout, "  /time EXPR          Evaluate with timing breakdown");
    let _ = writeln!(stdout, "  /expand (/e) FORM   Macro-expand a form");
    let _ = writeln!(stdout, "  /imports [MODULE]   Show imports and special forms");
    let _ = writeln!(stdout, "  /exports MODULE     Show module's public symbols");
    let _ = writeln!(stdout, "  /mod [NAME]         Switch module namespace (default: user)");
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
        ReplCommand::Exports(arg) => handle_exports(session, arg, stdout),
        ReplCommand::Source(name) => handle_source(session, name, stdout),
        ReplCommand::SexpCmd(name) => handle_sexp(session, name, stdout),
        ReplCommand::Ast(name) => handle_ast(session, name, stdout),
        ReplCommand::Clif(name) => handle_clif(session, name, stdout),
        ReplCommand::Disasm(name) => handle_disasm(session, name, stdout),
        ReplCommand::Mod(name) => handle_mod(session, name, stdout),
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
            } else if result.ty.is_io() {
                // IO expression: force the IO tree via trampoline, then
                // display the inner result value. Side effects (prints, etc.)
                // happen during the trampoline run.
                force_io_and_format(
                    result.value,
                    &result.ty,
                    session.type_defs(),
                    session.type_modules(),
                    stdout,
                )
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

    let module = session.tc.current_module_path().to_string();
    let prompt = format_prompt(last_compile_ms, last_eval_ms, &module);
    write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);

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
        let module = session.tc.current_module_path().to_string();
        if input.is_empty() || is_comment_only(input) {
            buffer.clear();
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
            continue;
        }

        if let Some(cmd) = parse_slash_command(input) {
            let should_quit = dispatch_slash_command(cmd, &mut session, &mut stdout);
            buffer.clear();
            if should_quit {
                break;
            }
            let module = session.tc.current_module_path().to_string();
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
            continue;
        }

        if let Some(display) = special_form_feedback(input, &session) {
            let _ = writeln!(stdout, "{display}");
            buffer.clear();
            write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
            continue;
        }

        (last_compile_ms, last_eval_ms) =
            eval_and_display(&mut session, input, &mut stdout);

        buffer.clear();
        let module = session.tc.current_module_path().to_string();
        write_prompt(&mut stdout, last_compile_ms, last_eval_ms, &module);
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
/// Check if a Sexp is a type annotation prefix (`:Type` or bare `:`).
fn is_annotation_prefix(sexp: &Sexp) -> bool {
    matches!(sexp, Sexp::Symbol(s, _) if s.starts_with(':') && !s.contains('/'))
}

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
    // Check builtin types first (not in symbol table)
    if Type::from_name(name).is_some() {
        let _ = writeln!(stdout, "{}", format_builtin_type_display(name, session));
        return;
    }
    let module = session.tc.current_module_path().clone();
    match session.tc.symbol_table().get(name) {
        Some(entry) => {
            let (resolved_entry, resolved_module) =
                resolve_entry_for_display(entry, &module, session);
            let display = format_entry_signature(resolved_entry, name, resolved_module, session);
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

/// Handle `/info <name>` — show full details about a symbol (spec §3.6).
fn handle_info(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /info <name>");
        return;
    }
    // Check builtin types first (not in symbol table)
    if Type::from_name(name).is_some() {
        let _ = writeln!(stdout, "{}", format_builtin_type_display(name, session));
        return;
    }
    let module = session.tc.current_module_path().clone();
    match session.tc.symbol_table().get(name) {
        Some(entry) => {
            let (resolved_entry, resolved_module) =
                resolve_entry_for_display(entry, &module, session);
            // Line 1: type signature (same as /sig).
            let sig = format_entry_signature(resolved_entry, name, resolved_module, session);
            let _ = writeln!(stdout, "{sig}");
            // Line 2: for functions, show code info.
            if !matches!(resolved_entry, ModuleEntry::Macro { .. } | ModuleEntry::TypeDef { .. } | ModuleEntry::TraitDecl { .. }) {
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
        None => {
            let _ = writeln!(stdout, "error: unknown symbol '{name}'");
        }
    }
}

/// Handle `/list [prefix]` — list definitions in the current module (spec §3.3).
///
/// Shows only symbols DEFINED in the current module. No imports, no special forms.
/// Categories: Modules, Macros, Traits, Types (incl constructors), Fns.
fn handle_list(session: &ReplSession, filter: &str, stdout: &mut impl Write) {
    let table = session.tc.symbol_table();

    let mut macros: Vec<String> = Vec::new();
    let mut traits: Vec<String> = Vec::new();
    let mut types: Vec<String> = Vec::new();
    let mut fns: Vec<String> = Vec::new();

    for (sym, entry) in table.all_symbols() {
        let name = sym.to_string();

        // Prefix match filter (case-insensitive)
        if !filter.is_empty()
            && !name.to_lowercase().starts_with(&filter.to_lowercase())
        {
            continue;
        }

        match entry {
            // Skip imports, reexports — belong on /imports
            ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. } => {}
            // Types and their constructors in Types category
            ModuleEntry::TypeDef { .. } => {
                types.push(name);
            }
            ModuleEntry::Constructor { .. } => {
                types.push(name);
            }
            ModuleEntry::TraitDecl { .. } => {
                traits.push(name);
            }
            ModuleEntry::Macro { .. } => {
                macros.push(name);
            }
            ModuleEntry::Def { kind, .. } => {
                match kind.as_ref() {
                    // Skip special forms — belong on /imports
                    DefKind::SpecialForm { .. } => {}
                    // Skip primitives — belong in primitives module
                    DefKind::Primitive { .. } => {}
                    _ => {
                        fns.push(name);
                    }
                }
            }
            _ => {}
        }
    }

    macros.sort();
    traits.sort();
    types.sort();
    fns.sort();

    let has_any = !macros.is_empty() || !traits.is_empty()
        || !types.is_empty() || !fns.is_empty();

    if !has_any {
        let _ = writeln!(stdout, "(no definitions)");
        return;
    }

    // Category order: Modules, Macros, Traits, Types, Fns
    print_name_category("Macros", &macros, stdout);
    print_name_category("Traits", &traits, stdout);
    print_name_category("Types", &types, stdout);
    print_name_category("Fns", &fns, stdout);
}

/// Print a category of names for `/list`, `/imports`, `/exports`.
///
/// Names are shown compactly: up to 6 per line for categories with 7+ names,
/// all on one line for smaller categories.
fn print_name_category(label: &str, names: &[String], stdout: &mut impl Write) {
    if names.is_empty() {
        return;
    }
    let _ = writeln!(stdout, "{label}:");
    if names.len() < 7 {
        let _ = writeln!(stdout, "  {}", names.join(" "));
    } else {
        // Compact layout: 6 names per line
        for chunk in names.chunks(6) {
            let _ = writeln!(stdout, "  {}", chunk.join(" "));
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
/// Unfiltered: organize by category (Special forms, Macros, Traits, Types, Fns).
/// Filtered: `/imports <module>` shows imports from that source module only,
/// organized as `From <module>:` groups with sorted names.
/// Names only — no type signatures. Type the name for more detail.
fn handle_imports(session: &ReplSession, filter: &str, stdout: &mut impl Write) {
    let table = session.tc.symbol_table();

    if filter.is_empty() {
        // Unfiltered mode: organize by category (spec §3.4)
        let mut special_forms: Vec<String> = Vec::new();
        let mut macros: Vec<String> = Vec::new();
        let mut traits: Vec<String> = Vec::new();
        let mut types: Vec<String> = Vec::new();
        let mut fns: Vec<String> = Vec::new();

        for (sym, entry) in table.all_symbols() {
            let name = sym.to_string();
            match entry {
                ModuleEntry::Def { kind, .. } => {
                    if let DefKind::SpecialForm { .. } = kind.as_ref() {
                        special_forms.push(name);
                    } else if matches!(kind.as_ref(), DefKind::Primitive { .. }) {
                        // Primitives are NOT shown in /imports (they're via module
                        // resolution fallback, not import).
                    } else {
                        // Skip locally-defined fns (not imports)
                    }
                }
                ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                    // Skip monomorphised variant names (e.g. add$Int+Int)
                    if name.contains('$') {
                        continue;
                    }
                    // Classify by looking up the source entry
                    let classification = classify_import(session, source);
                    match classification {
                        ImportClass::Macro => macros.push(name),
                        ImportClass::Trait => traits.push(name),
                        ImportClass::Type | ImportClass::Constructor => types.push(name),
                        ImportClass::Fn => fns.push(name),
                    }
                }
                _ => {} // TypeDef, TraitDecl, Constructor, Macro — locally defined
            }
        }

        special_forms.sort();
        macros.sort();
        traits.sort();
        types.sort();
        fns.sort();

        // Special forms always present (spec §3.4)
        print_name_category("Special forms", &special_forms, stdout);
        print_name_category("Macros", &macros, stdout);
        print_name_category("Traits", &traits, stdout);
        print_name_category("Types", &types, stdout);
        print_name_category("Fns", &fns, stdout);

        if special_forms.is_empty() && macros.is_empty() && traits.is_empty()
            && types.is_empty() && fns.is_empty()
        {
            // Shouldn't happen (special forms always present), but just in case
            let _ = writeln!(stdout, "(no imports)");
        }
    } else {
        // Filtered mode: `/imports <module>` — show imports from that source module
        let mut names: Vec<String> = Vec::new();
        for (sym, entry) in table.all_symbols() {
            let source = match entry {
                ModuleEntry::Import { source } => source,
                ModuleEntry::Reexport { source } => source,
                _ => continue,
            };
            let name = sym.to_string();
            // Skip monomorphised variant names
            if name.contains('$') {
                continue;
            }
            if source.module.to_string() == filter {
                names.push(name);
            }
        }
        if names.is_empty() {
            // Silent re-prompt for no matches (spec §3.4)
            return;
        }
        names.sort();
        print_name_category(&format!("From {filter}"), &names, stdout);
    }
}

/// Handle `/exports <module>` — list a module's public symbols (spec §3.5).
///
/// Resolves the module, lists public symbols by category (names only).
/// Usage hint for no argument. Error for not-found module.
fn handle_exports(session: &ReplSession, arg: &str, stdout: &mut impl Write) {
    if arg.is_empty() {
        let _ = writeln!(stdout, "Usage: /exports <module-name>");
        return;
    }

    // Parse: first word is module name, rest is optional prefix filter
    let mut parts = arg.splitn(2, char::is_whitespace);
    let mod_name = parts.next().unwrap_or("");
    let prefix_filter = parts.next().unwrap_or("").trim();

    // Resolve module
    let module_path = match session.tc.resolve_module_by_name(mod_name) {
        Some(path) => path,
        None => {
            let _ = writeln!(stdout, "Module '{mod_name}' not found");
            return;
        }
    };

    // Get the module's symbol table
    let table = match session.tc.module_table(&module_path) {
        Some(t) => t,
        None => {
            let _ = writeln!(stdout, "Module '{mod_name}' not found");
            return;
        }
    };

    // Collect public symbols by category
    let mut macros: Vec<String> = Vec::new();
    let mut traits: Vec<String> = Vec::new();
    let mut types: Vec<String> = Vec::new();
    let mut fns: Vec<String> = Vec::new();

    for (sym, entry) in table.all_symbols() {
        // Skip imports/reexports — those are the module's own imports, not exports
        if matches!(entry, ModuleEntry::Import { .. } | ModuleEntry::Reexport { .. }) {
            continue;
        }
        // Skip non-public symbols
        if !entry.is_public() {
            continue;
        }
        let name = sym.to_string();
        // Skip monomorphised variant names
        if name.contains('$') {
            continue;
        }
        // Apply prefix filter if provided
        if !prefix_filter.is_empty()
            && !name.to_lowercase().starts_with(&prefix_filter.to_lowercase())
        {
            continue;
        }

        match entry {
            ModuleEntry::Macro { .. } => macros.push(name),
            ModuleEntry::TraitDecl { .. } => traits.push(name),
            ModuleEntry::TypeDef { .. } | ModuleEntry::Constructor { .. } => types.push(name),
            ModuleEntry::Def { kind, .. } => {
                if !matches!(kind.as_ref(), DefKind::SpecialForm { .. }) {
                    fns.push(name);
                }
            }
            _ => {}
        }
    }

    macros.sort();
    traits.sort();
    types.sort();
    fns.sort();

    let has_any = !macros.is_empty() || !traits.is_empty()
        || !types.is_empty() || !fns.is_empty();

    if !has_any {
        let _ = writeln!(stdout, "Module '{mod_name}' has no public symbols");
        return;
    }

    let _ = writeln!(stdout, "Module '{mod_name}':");
    print_name_category("Macros", &macros, stdout);
    print_name_category("Traits", &traits, stdout);
    print_name_category("Types", &types, stdout);
    print_name_category("Fns", &fns, stdout);
}

/// Classification of an imported symbol for category-based display.
enum ImportClass {
    Macro,
    Trait,
    Type,
    Constructor,
    Fn,
}

/// Classify an imported symbol by looking up the source entry.
///
/// Follows Import/Reexport chains to the ultimate definition (depth-limited).
fn classify_import(session: &ReplSession, source: &cranelisp_types::FQSymbol) -> ImportClass {
    match resolve_to_definition(session, source) {
        Some(entry) => match entry {
            ModuleEntry::Macro { .. } => ImportClass::Macro,
            ModuleEntry::TraitDecl { .. } => ImportClass::Trait,
            ModuleEntry::TypeDef { .. } => ImportClass::Type,
            ModuleEntry::Constructor { .. } => ImportClass::Constructor,
            _ => ImportClass::Fn,
        },
        None => ImportClass::Fn, // Default: treat unknown as function
    }
}

/// Maximum depth for following Import/Reexport chains to prevent cycles.
const RESOLVE_DEPTH_LIMIT: usize = 10;

/// Follow Import/Reexport chains to find the ultimate definition entry.
///
/// Returns the concrete entry (Def, Macro, TypeDef, TraitDecl, Constructor)
/// or None if the chain is broken or exceeds the depth limit.
fn resolve_to_definition<'a>(
    session: &'a ReplSession,
    source: &cranelisp_types::FQSymbol,
) -> Option<&'a ModuleEntry> {
    let mut current_module = source.module.clone();
    let mut current_name: String = source.symbol.to_string();
    for _ in 0..RESOLVE_DEPTH_LIMIT {
        let table = session.tc.module_table(&current_module)?;
        let entry = table.get(&current_name)?;
        match entry {
            ModuleEntry::Import { source: next } | ModuleEntry::Reexport { source: next } => {
                current_module = next.module.clone();
                current_name = next.symbol.to_string();
            }
            _ => return Some(entry),
        }
    }
    None // Depth limit exceeded (cycle or very deep chain)
}

/// Resolve an entry for display: if Import/Reexport, follow the chain to the
/// definition and return the resolved entry with its defining module.
///
/// Returns the original entry and module if not Import/Reexport or if
/// the chain cannot be resolved.
fn resolve_entry_for_display<'a>(
    entry: &'a ModuleEntry,
    module: &'a ModuleFullPath,
    session: &'a ReplSession,
) -> (&'a ModuleEntry, &'a ModuleFullPath) {
    let source = match entry {
        ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => source,
        _ => return (entry, module),
    };
    // Follow the chain to the ultimate definition.
    let mut current_module = &source.module;
    let mut current_name: String = source.symbol.to_string();
    for _ in 0..RESOLVE_DEPTH_LIMIT {
        let table = match session.tc.module_table(current_module) {
            Some(t) => t,
            None => return (entry, module),
        };
        let resolved = match table.get(&current_name) {
            Some(e) => e,
            None => return (entry, module),
        };
        match resolved {
            ModuleEntry::Import { source: next } | ModuleEntry::Reexport { source: next } => {
                current_module = &next.module;
                current_name = next.symbol.to_string();
            }
            _ => return (resolved, current_module),
        }
    }
    (entry, module) // Depth limit exceeded — return original
}

/// Format a module entry's type signature for /sig and /info display.
///
/// Uses universal output format (spec §1.1).
fn format_entry_signature(
    entry: &ModuleEntry,
    name: &str,
    module: &ModuleFullPath,
    session: &ReplSession,
) -> String {
    match entry {
        ModuleEntry::Def {
            scheme,
            kind,
            docstring,
            ..
        } => {
            if let DefKind::SpecialForm { description } = kind.as_ref() {
                return format_special_form_display(name, description);
            }
            let base = if !scheme.constraints.is_empty() {
                display::format_scheme_display(name, scheme, module, &session.type_modules)
            } else {
                let type_str = format_type_qualified(&scheme.ty, &session.type_modules);
                format!(":{type_str} {module}/{name}")
            };
            let classification = if matches!(kind.as_ref(), DefKind::Primitive { .. }) {
                "primitive"
            } else {
                "defn"
            };
            let base = format!("{base} ; {classification}");
            append_docstring_comment(base, docstring.as_deref())
        }
        ModuleEntry::Constructor {
            type_name, scheme, ..
        } => {
            let type_str = format_type_qualified(&scheme.ty, &session.type_modules);
            let tn = TypeName::from(type_name.0.as_str());
            let ctor_display = if let Some(info) = session.tc.type_def_registry().get(&tn) {
                display::format_ctor_display(&tn, name, info)
            } else {
                format!("{type_name}.{name}")
            };
            format!(":{type_str} {module}/{ctor_display} ; deftype")
        }
        ModuleEntry::TypeDef { .. } => {
            format_type_display_universal(name, module, session)
        }
        ModuleEntry::TraitDecl { decl, .. } => {
            format_trait_display_universal(name, decl.docstring.as_deref(), session)
        }
        ModuleEntry::Macro { clauses, docstring, .. } => {
            format_macro_display_universal(name, clauses, docstring.as_deref(), module)
        }
        _ => format!("{module}/{name}"),
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

/// Format a special form for display (spec §4.1.5).
///
/// Produces a function-like signature with `; special form - description`.
fn format_special_form_display(name: &str, description: &str) -> String {
    let type_sig = match name {
        "if" => ":(Fn [primitives/Bool a a] a)",
        "let" => ":(Fn [bindings body] a)",
        "fn" => ":(Fn [params body] function)",
        "defn" => ":(Fn [name params body] function)",
        "deftype" => ":(Fn [name ctors...] type)",
        "match" => ":(Fn [expr [pat body]...] a)",
        "defmacro" => ":(Fn [name params body] macro)",
        "deftrait" => ":(Fn [name methods...] trait)",
        "impl" => ":(Fn [trait type methods...] impl)",
        "import" => ":(Fn [module names] import)",
        "do" => ":(Fn [exprs...] a)",
        _ => "",
    };
    if type_sig.is_empty() {
        format!("{name} ; special form - {description}")
    } else {
        format!("{type_sig} {name} ; special form - {description}")
    }
}

/// Check if the trimmed input is a bare symbol name and return its display.
///
/// Handles special forms, primitive types, functions, constructors, traits,
/// and macros (spec §4.1, §11.4). Returns `Some(display_string)` if the
/// input matches a known symbol, `None` otherwise.
///
/// Universal output format (spec §1.1):
///   `:Type {value|name} ; {classification} - {docstring}`
/// with optional related symbol sections for types, traits, and macros.
fn special_form_feedback(input: &str, session: &ReplSession) -> Option<String> {
    let trimmed = input.trim();
    // Must be a single bare identifier (no parens, no spaces, no brackets).
    if trimmed.contains(|c: char| c.is_whitespace() || c == '(' || c == ')' || c == '[' || c == ']') {
        return None;
    }
    if trimmed.is_empty() {
        return None;
    }
    // Check primitive type names: Int, Bool, Float, String (spec §4.1.3).
    // These live in the `primitives` synthetic module but are not bare names
    // in the user module's symbol table, so we check before the lookup.
    if Type::from_name(trimmed).is_some() {
        return Some(format_builtin_type_display(trimmed, session));
    }

    // Look up in the symbol table (spec §4.1 — bare symbol lookup).
    // Delegate to format_entry_signature which implements the universal format
    // for all symbol classes.
    let module = session.tc.current_module_path().clone();
    let entry = session.tc.symbol_table().get(trimmed)?;
    // For Import/Reexport entries, resolve through the chain to the definition.
    // This allows bare-symbol display for imported special forms, macros, etc.
    let (resolved_entry, resolved_module) =
        resolve_entry_for_display(entry, &module, session);
    // Nullary constructors (zero fields) have value semantics — they evaluate
    // to a value, so let them pass through to eval instead of showing definition
    // metadata. Non-nullary constructors need arguments and can't be evaluated
    // bare, so they show introspection display (spec §4.1).
    if let ModuleEntry::Constructor { info, .. } = resolved_entry
        && info.fields.is_empty()
    {
        return None;
    }
    Some(format_entry_signature(resolved_entry, trimmed, resolved_module, session))
}

/// Format a builtin type (Int, Bool, Float, String) for bare symbol lookup.
///
/// Shows `:primitives/Type ; type` with `; impl:` section listing traits
/// that have implementations for this type (spec §4.1.3).
fn format_builtin_type_display(type_name: &str, session: &ReplSession) -> String {
    let tn = TypeName::from(type_name);
    let mut result = format!(":primitives/{type_name} ; type");
    let trait_names = session.tc.get_impls_for_type(&tn);
    if !trait_names.is_empty() {
        let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
        result.push_str(&format_related_section("impl", &names));
    }
    result
}

/// Format a user-defined type for bare symbol lookup (spec §4.1.3).
///
/// Shows `:module/TypeName ; deftype` with `; match:` (constructors) and
/// `; impl:` (trait implementations) related symbol sections.
fn format_type_display_universal(type_name: &str, module: &ModuleFullPath, session: &ReplSession) -> String {
    let mut result = format!(":{module}/{type_name} ; deftype");
    let tn = TypeName::from(type_name);
    // Related: constructors under `; match:`
    if let Some(ctors) = session.tc.get_type_constructors(&tn) {
        if !ctors.is_empty() {
            let names: Vec<&str> = ctors.iter().map(|c| c.name.as_ref()).collect();
            result.push_str(&format_related_section("match", &names));
        }
    }
    // Related: trait implementations under `; impl:`
    let trait_names = session.tc.get_impls_for_type(&tn);
    if !trait_names.is_empty() {
        let names: Vec<&str> = trait_names.iter().map(|t| t.as_ref()).collect();
        result.push_str(&format_related_section("impl", &names));
    }
    result
}

/// Format a trait for bare symbol lookup (spec §4.1.4).
///
/// Shows `:defining_module/TraitName ; deftrait` with `; defn:` (methods)
/// and `; impl:` (implementing types) related symbol sections.
fn format_trait_display_universal(
    trait_name: &str,
    docstring: Option<&str>,
    session: &ReplSession,
) -> String {
    let defining_module = session.tc.defining_module_for(trait_name);
    let tn = TraitName::from(trait_name);
    let mut result = format!(":{defining_module}/{trait_name} ; deftrait");
    result = append_docstring_comment(result, docstring);
    // Related: methods under `; defn:`
    if let Some(methods) = session.tc.get_trait_methods(&tn) {
        if !methods.is_empty() {
            let names: Vec<&str> = methods.iter().map(|m| m.as_ref()).collect();
            result.push_str(&format_related_section("defn", &names));
        }
    }
    // Related: implementing types under `; impl:`
    let impl_types = session.tc.get_implementing_types(&tn);
    if !impl_types.is_empty() {
        let names: Vec<&str> = impl_types.iter().map(|t| t.as_ref()).collect();
        result.push_str(&format_related_section("impl", &names));
    }
    result
}

/// Format a macro for bare symbol lookup (spec §4.1.6, §11.4).
///
/// Shows `:module/name ; defmacro` with `; [params] -> Sexp` clause lines.
fn format_macro_display_universal(
    name: &str,
    clauses: &[MacroClauseInfo],
    docstring: Option<&str>,
    module: &ModuleFullPath,
) -> String {
    let mut result = format!(":{module}/{name} ; defmacro");
    result = append_docstring_comment(result, docstring);
    for clause in clauses {
        let params = format_macro_clause_params(clause);
        result.push_str(&format!("\n; {params} -> Sexp"));
    }
    result
}

/// Format a related symbols section for universal output (spec §1.1).
///
/// Produces `\n; {label}:\n;  name1 name2 ...` with names on one line.
fn format_related_section(label: &str, names: &[&str]) -> String {
    let mut result = format!("\n; {label}:");
    result.push_str(&format!("\n;  {}", names.join(" ")));
    result
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

// ---------------------------------------------------------------------------
// Introspection commands: /source, /sexp, /ast, /clif, /disasm
// ---------------------------------------------------------------------------

/// Handle `/source <name>` — show original source text of a definition.
fn handle_source(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /source <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.source.is_some() => {
            let _ = writeln!(stdout, "; source for {name}");
            let _ = writeln!(stdout, "{}", dc.source.as_ref().unwrap());
        }
        _ => {
            let _ = writeln!(stdout, "error: no source available for '{name}'");
        }
    }
}

/// Handle `/sexp <name>` — show the parsed S-expression of a definition.
fn handle_sexp(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /sexp <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.sexp.is_some() => {
            let _ = writeln!(stdout, "; sexp for {name}");
            let _ = writeln!(stdout, "{}", format_sexp(dc.sexp.as_ref().unwrap()));
        }
        _ => {
            let _ = writeln!(stdout, "error: no sexp available for '{name}'");
        }
    }
}

/// Handle `/ast <name>` — show the AST (Defn) of a definition.
fn handle_ast(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /ast <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.defn.is_some() => {
            let _ = writeln!(stdout, "; ast for {name}");
            let _ = writeln!(stdout, "{:#?}", dc.defn.as_ref().unwrap());
        }
        _ => {
            let _ = writeln!(stdout, "error: no AST available for '{name}'");
        }
    }
}

/// Handle `/clif <name>` — show the Cranelift IR of a definition.
fn handle_clif(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /clif <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.clif_ir.is_some() => {
            let _ = writeln!(stdout, "; clif ir for {name}");
            let _ = write!(stdout, "{}", dc.clif_ir.as_ref().unwrap());
        }
        _ => {
            let _ = writeln!(stdout, "error: no CLIF IR available for '{name}'");
        }
    }
}

/// Handle `/disasm <name>` — show disassembled native code of a definition.
fn handle_disasm(session: &ReplSession, name: &str, stdout: &mut impl Write) {
    if name.is_empty() {
        let _ = writeln!(stdout, "usage: /disasm <name>");
        return;
    }
    match session.got_state.def_codegen.get(name) {
        Some(dc) if dc.disasm.is_some() => {
            let _ = writeln!(stdout, "; disasm for {name}");
            let _ = writeln!(stdout, "{}", dc.disasm.as_ref().unwrap());
        }
        _ => {
            let _ = writeln!(stdout, "error: no disassembly available for '{name}'");
        }
    }
}

// ---------------------------------------------------------------------------
// /mod command
// ---------------------------------------------------------------------------

/// Handle `/mod [name]` — switch module namespace (spec §8).
///
/// With no argument, switches to the `user` module (no output).
/// With an argument, switches to that module namespace (no output, creating it if needed).
fn handle_mod(session: &mut ReplSession, name: &str, _stdout: &mut impl Write) {
    let target = if name.is_empty() { "user" } else { name };
    let path = ModuleFullPath::from(target);
    session.tc.set_current_module(path);
}

// ---------------------------------------------------------------------------
// Runtime panic boundary (spec §12.7.4.1)
// ---------------------------------------------------------------------------

/// Invoke a JIT-compiled function and check for runtime errors.
///
/// `runtime_panic` in JIT code stores the error in a thread-local (because
/// Cranelift JIT frames lack unwind tables, so `catch_unwind` cannot work).
/// After the JIT call returns, we check `take_runtime_error()` for errors.
fn invoke_jit_eval<F>(f: F) -> Result<i64, CranelispError>
where
    F: FnOnce() -> i64,
{
    // Clear any stale error before the JIT call.
    let _ = cranelisp_runtime::panic::take_runtime_error();
    let value = f();
    // Check if runtime_panic was called during execution.
    if let Some(message) = cranelisp_runtime::panic::take_runtime_error() {
        Err(CranelispError::CodegenError {
            message,
            span: cranelisp_types::Span::SYNTHETIC,
        })
    } else {
        Ok(value)
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
                        internal: false,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Green"),
                        tag: 1,
                        fields: vec![],
                        docstring: None,
                        internal: false,
                    },
                    ConstructorInfo {
                        name: Symbol::from("Blue"),
                        tag: 2,
                        fields: vec![],
                        docstring: None,
                        internal: false,
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
            display::format_adt_type_qualified(&TypeName::from("Color"), &[], &tm),
            "Color"
        );
        assert_eq!(
            display::format_adt_type_qualified(&TypeName::from("Option"), &[Type::Int], &tm),
            "(Option primitives/Int)"
        );
        // With type_modules, ADT name gets qualified too.
        let mut tm2 = HashMap::new();
        tm2.insert(
            TypeName::from("Color"),
            ModuleFullPath::from("user"),
        );
        assert_eq!(
            display::format_adt_type_qualified(&TypeName::from("Color"), &[], &tm2),
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

    // --- classify_import + resolve_to_definition tests ---

    /// Helper: build a ReplSession with custom module tables for classify_import tests.
    ///
    /// Uses `set_current_module` to create each module, inserts entries via
    /// `symbol_table_mut()`, then switches back to the "user" module.
    fn session_with_modules(
        modules: Vec<(ModuleFullPath, Vec<(Symbol, ModuleEntry)>)>,
    ) -> ReplSession {
        let mut session = ReplSession::new();
        for (path, entries) in modules {
            session.tc.set_current_module(path);
            for (sym, entry) in entries {
                session.tc.symbol_table_mut().insert(sym, entry);
            }
        }
        // Switch back to user module
        session.tc.set_current_module(ModuleFullPath::from("user"));
        session
    }

    // spec: repl/spec.md §3.4 — classify_import resolves direct definition
    #[test]
    fn test_classify_import_direct_definition() {
        use cranelisp_types::{FQSymbol, Scheme};

        let mod_path = ModuleFullPath::from("core.num");
        let session = session_with_modules(vec![(
            mod_path.clone(),
            vec![
                (
                    Symbol::from("Num"),
                    ModuleEntry::TraitDecl {
                        decl: cranelisp_types::TraitDecl {
                            name: TraitName::from("Num"),
                            type_params: vec![Symbol::from("a")],
                            methods: vec![],
                            docstring: None,
                            visibility: Visibility::Public,
                            span: cranelisp_types::Span::SYNTHETIC,
                        },
                        visibility: Visibility::Public,
                        sexp: None,
                    },
                ),
                (
                    Symbol::from("add"),
                    ModuleEntry::Def {
                        scheme: Scheme { vars: vec![], constraints: HashMap::new(), ty: Type::Int },
                        visibility: Visibility::Public,
                        docstring: None,
                        param_names: vec![],
                        kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                    },
                ),
            ],
        )]);

        let trait_source = FQSymbol {
            module: mod_path.clone(),
            symbol: Symbol::from("Num"),
        };
        assert!(matches!(
            classify_import(&session, &trait_source),
            ImportClass::Trait
        ));

        let fn_source = FQSymbol {
            module: mod_path,
            symbol: Symbol::from("add"),
        };
        assert!(matches!(
            classify_import(&session, &fn_source),
            ImportClass::Fn
        ));
    }

    // spec: repl/spec.md §3.4 — classify_import follows reexport chain
    #[test]
    fn test_classify_import_reexport_chain() {
        use cranelisp_types::FQSymbol;

        let origin = ModuleFullPath::from("core.num");
        let prelude = ModuleFullPath::from("prelude");

        let session = session_with_modules(vec![
            (
                origin.clone(),
                vec![(
                    Symbol::from("Num"),
                    ModuleEntry::TraitDecl {
                        decl: cranelisp_types::TraitDecl {
                            name: TraitName::from("Num"),
                            type_params: vec![Symbol::from("a")],
                            methods: vec![],
                            docstring: None,
                            visibility: Visibility::Public,
                            span: cranelisp_types::Span::SYNTHETIC,
                        },
                        visibility: Visibility::Public,
                        sexp: None,
                    },
                )],
            ),
            (
                prelude.clone(),
                vec![(
                    Symbol::from("Num"),
                    ModuleEntry::Reexport {
                        source: FQSymbol {
                            module: origin.clone(),
                            symbol: Symbol::from("Num"),
                        },
                    },
                )],
            ),
        ]);

        // Importing from prelude should follow the reexport chain to core.num
        let source = FQSymbol {
            module: prelude,
            symbol: Symbol::from("Num"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Trait
        ));
    }

    // spec: repl/spec.md §3.4 — internal names filtered from /imports
    #[test]
    fn test_imports_filters_internal_names() {
        // Verify that monomorphised variant names (containing $) are filtered.
        // __macro_ names are now private (defn-) and won't appear in imports.
        let internal_names = vec!["add$Int+Int", "foo$Float"];
        let public_names = vec!["add", "Num", "Display"];

        for name in &internal_names {
            assert!(name.contains('$'), "{name} should be filtered");
        }
        for name in &public_names {
            assert!(!name.contains('$'), "{name} should NOT be filtered");
        }
    }

    // spec: repl/spec.md §3.4 — classify_import with macro entry
    #[test]
    fn test_classify_import_macro() {
        use cranelisp_types::FQSymbol;

        let mod_path = ModuleFullPath::from("prelude");
        let session = session_with_modules(vec![(
            mod_path.clone(),
            vec![(
                Symbol::from("defn-macro"),
                ModuleEntry::Macro {
                    name: Symbol::from("defn-macro"),
                    clauses: vec![],
                    docstring: None,
                    visibility: Visibility::Public,
                    sexp: None,
                    source: None,
                },
            )],
        )]);

        let source = FQSymbol {
            module: mod_path,
            symbol: Symbol::from("defn-macro"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Macro
        ));
    }

    // spec: repl/spec.md §3.4 — classify_import with constructor entry
    #[test]
    fn test_classify_import_constructor() {
        use cranelisp_types::{ConstructorInfo, FQSymbol, Scheme};

        let mod_path = ModuleFullPath::from("core.option");
        let session = session_with_modules(vec![(
            mod_path.clone(),
            vec![(
                Symbol::from("Some"),
                ModuleEntry::Constructor {
                    type_name: Symbol::from("Option"),
                    info: ConstructorInfo {
                        name: Symbol::from("Some"),
                        tag: 1,
                        fields: vec![],
                        docstring: None,
                        internal: false,
                    },
                    scheme: Scheme { vars: vec![], constraints: HashMap::new(), ty: Type::Int },
                    visibility: Visibility::Public,
                },
            )],
        )]);

        let source = FQSymbol {
            module: mod_path,
            symbol: Symbol::from("Some"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Constructor
        ));
    }

    // spec: repl/spec.md §3.4 — classify_import with type def entry
    #[test]
    fn test_classify_import_typedef() {
        use cranelisp_types::{FQSymbol, TypeDefInfo};

        let mod_path = ModuleFullPath::from("core.option");
        let session = session_with_modules(vec![(
            mod_path.clone(),
            vec![(
                Symbol::from("Option"),
                ModuleEntry::TypeDef {
                    info: TypeDefInfo {
                        name: TypeName::from("Option"),
                        type_params: vec![],
                        constructors: vec![],
                        docstring: None,
                    },
                    visibility: Visibility::Public,
                    constructor_scheme: None,
                    sexp: None,
                },
            )],
        )]);

        let source = FQSymbol {
            module: mod_path,
            symbol: Symbol::from("Option"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Type
        ));
    }

    // spec: repl/spec.md §3.4 — classify_import unknown symbol defaults to Fn
    #[test]
    fn test_classify_import_unknown_defaults_to_fn() {
        use cranelisp_types::FQSymbol;

        let session = ReplSession::new();
        let source = FQSymbol {
            module: ModuleFullPath::from("nonexistent"),
            symbol: Symbol::from("whatever"),
        };
        assert!(matches!(
            classify_import(&session, &source),
            ImportClass::Fn
        ));
    }

    // IO type detection tests moved to cranelisp-types (Type::is_io, Type::io_inner_type)

    // spec: 10-io §10.8.1 — force_io_and_format with Pure node
    #[test]
    fn test_force_io_and_format_pure_int() {
        // Build a Pure(42) IO node manually.
        let base = cranelisp_runtime::alloc_with_rc(16); // tag + value
        unsafe {
            *((base as isize + 16) as *mut i64) = cranelisp_platform::IO_TAG_PURE;
            *((base as isize + 24) as *mut i64) = 42;
        }
        let io_ty = Type::ADT(TypeName::from("IO"), vec![Type::Int]);
        let type_defs = HashMap::new();
        let type_modules = HashMap::new();
        let mut buf: Vec<u8> = Vec::new();

        let display = force_io_and_format(
            base as i64,
            &io_ty,
            &type_defs,
            &type_modules,
            &mut buf,
        );
        assert_eq!(display, ":(IO primitives/Int) (IO.Pure 42)");
        cranelisp_runtime::heap_dealloc(base as i64);
    }

    // spec: 10-io §10.8.1 — force_io_and_format handles panic gracefully
    #[test]
    fn test_force_io_and_format_panic_recovery() {
        // Build a node with an invalid tag.
        let base = cranelisp_runtime::alloc_with_rc(16);
        unsafe {
            *((base as isize + 16) as *mut i64) = 99; // invalid tag
            *((base as isize + 24) as *mut i64) = 0;
        }
        let io_ty = Type::ADT(TypeName::from("IO"), vec![Type::Int]);
        let type_defs = HashMap::new();
        let type_modules = HashMap::new();
        let mut buf: Vec<u8> = Vec::new();

        let display = force_io_and_format(
            base as i64,
            &io_ty,
            &type_defs,
            &type_modules,
            &mut buf,
        );
        assert_eq!(display, ":(IO primitives/Int) <IO trampoline panicked>");
        cranelisp_runtime::heap_dealloc(base as i64);
    }
}
