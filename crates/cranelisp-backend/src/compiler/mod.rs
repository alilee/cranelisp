// FnCompiler: per-function compilation context.
//
// Contains the FunctionBuilder and all state needed to compile one function.
// NOT a 21-parameter function -- addresses the prototype's primary structural debt.
//
// One dispatch method per Expr variant: compile_int_lit, compile_let, etc.

pub mod apply;
pub mod control_flow;
pub mod literals;
pub mod match_codegen;
pub mod trace_codegen;
pub mod vec_codegen;

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_module::{FuncId, Module};

use dashmap::DashMap;

use cranelisp_types::{
    ConstructorInfo, CranelispError, Defn, Expr, FQTypeName, HeapCategory,
    ModuleEntry, ModuleFullPath, Span, Symbol, SymbolTable,
    Type, TypeDefInfo,
};

use crate::heap;

// Variable allocation is per-FnCompiler instance via next_var field.

/// Named constant for the user trap code used when match exhaustion occurs.
pub const MATCH_EXHAUSTION_TRAP: u8 = 1;

/// GOT data symbol name for a module. Single source of truth.
/// Used as the Cranelift data symbol name for the module's GOT table in both
/// JIT and object codegen. See session-restructure.md.
///
/// Convention: `__cranelisp_got_<flat_path>` where dots are replaced by
/// underscores. Each `.o` file defines all GOT data symbols it needs
/// (own module + imported modules) as `Export` with a placeholder value;
/// the linker/loader patches them at load time.
pub fn got_data_symbol_name(module_path: &ModuleFullPath) -> String {
    let flat = module_path.as_ref().replace('.', "_");
    format!(
        "__cranelisp_got_{}",
        if flat.is_empty() { "_entry" } else { &flat }
    )
}

/// Resolve a function name to `(defining_module, module_local_slot)` by
/// walking `symbol_tables` starting at `current_module`.
///
/// Uniform replacement for the Sprint-56-retracted `CompilationEnv` trait.
/// Handles:
/// - Bare names: resolved in `current_module`, following Import/Reexport chains.
/// - Qualified `"module/name"`: tries `current_module.module`, then absolute
///   `module` path; the bare name is then resolved in the target module.
/// - Global fallback: walks all modules for names that weren't import-linked
///   (e.g., mangled trait methods written without an explicit import).
///
/// Returns `None` if the symbol is not found, is not a `Def` with a `got_slot`,
/// or if the Import chain exceeds the depth limit (10).
pub fn resolve_got_target(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> Option<(ModuleFullPath, usize)> {
    const MAX_IMPORT_DEPTH: usize = 10;

    fn resolve_in_module(
        tables: &DashMap<ModuleFullPath, SymbolTable>,
        module: &ModuleFullPath,
        bare: &str,
        depth: usize,
    ) -> Option<(ModuleFullPath, usize)> {
        if depth > MAX_IMPORT_DEPTH {
            return None;
        }
        let st = tables.get(module)?;
        let entry = st.get(bare)?;
        match entry {
            ModuleEntry::Def { got_slot: Some(slot), .. } => Some((module.clone(), *slot)),
            ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                resolve_in_module(tables, &source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    // 1. Try current module first.
    if let Some(result) = resolve_in_module(symbol_tables, current_module, name.as_ref(), 0) {
        return Some(result);
    }

    // 2. Qualified "module/name" — try child-of-current, then absolute.
    if let Some(slash) = name.as_ref().find('/') {
        let module_part = &name.as_ref()[..slash];
        let bare_name = &name.as_ref()[slash + 1..];
        if !module_part.is_empty() && !bare_name.is_empty() {
            let child_path =
                ModuleFullPath::from(format!("{}.{}", current_module, module_part));
            if let Some(result) = resolve_in_module(symbol_tables, &child_path, bare_name, 0) {
                return Some(result);
            }
            let abs_path = ModuleFullPath::from(module_part);
            if let Some(result) = resolve_in_module(symbol_tables, &abs_path, bare_name, 0) {
                return Some(result);
            }
        }
    }

    // 3. Global fallback: walk all modules. Handles mangled trait methods
    //    referenced without an explicit import.
    for entry in symbol_tables.iter() {
        if entry.key() == current_module {
            continue;
        }
        if let Some(result) = resolve_in_module(symbol_tables, entry.key(), name.as_ref(), 0) {
            return Some(result);
        }
    }

    None
}

/// Resolve a function's parameter count by walking `symbol_tables` starting at
/// `current_module`. Replacement for the Sprint-56-retracted
/// `CompilationEnv::func_arity`. Used when generating closure wrappers for
/// cross-module function references.
pub fn resolve_func_arity(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> Option<usize> {
    const MAX_IMPORT_DEPTH: usize = 10;

    fn arity_in_module(
        tables: &DashMap<ModuleFullPath, SymbolTable>,
        module: &ModuleFullPath,
        bare: &str,
        depth: usize,
    ) -> Option<usize> {
        if depth > MAX_IMPORT_DEPTH {
            return None;
        }
        let st = tables.get(module)?;
        let entry = st.get(bare)?;
        match entry {
            ModuleEntry::Def { param_names, .. } => Some(param_names.len()),
            ModuleEntry::Import { source } | ModuleEntry::Reexport { source } => {
                let source_module = source.module.clone();
                let source_symbol = source.symbol.clone();
                drop(st);
                arity_in_module(tables, &source_module, source_symbol.as_ref(), depth + 1)
            }
            _ => None,
        }
    }

    // 1. Try current module first.
    if let Some(arity) = arity_in_module(symbol_tables, current_module, name.as_ref(), 0) {
        return Some(arity);
    }

    // 2. Qualified "module/name" — try child-of-current, then absolute.
    if let Some(slash) = name.as_ref().find('/') {
        let module_part = &name.as_ref()[..slash];
        let bare_name = &name.as_ref()[slash + 1..];
        if !module_part.is_empty() && !bare_name.is_empty() {
            let child_path =
                ModuleFullPath::from(format!("{}.{}", current_module, module_part));
            if let Some(arity) = arity_in_module(symbol_tables, &child_path, bare_name, 0) {
                return Some(arity);
            }
            let abs_path = ModuleFullPath::from(module_part);
            if let Some(arity) = arity_in_module(symbol_tables, &abs_path, bare_name, 0) {
                return Some(arity);
            }
        }
    }

    // 3. Global fallback.
    for entry in symbol_tables.iter() {
        if entry.key() == current_module {
            continue;
        }
        if let Some(arity) = arity_in_module(symbol_tables, entry.key(), name.as_ref(), 0) {
            return Some(arity);
        }
    }

    None
}

/// Information about a single function to be traced by `(trace ...)`.
///
/// Populated by the integration layer (src/) from the module symbol tables,
/// then passed into `CompileContext` so the trace codegen can compile wrappers.
#[derive(Debug, Clone)]
pub struct TracedFnInfo {
    /// Fully-qualified function name (e.g., "user/fact").
    pub name: String,
    /// GOT base pointer for the module containing this function.
    pub got_base: i64,
    /// GOT slot index for this function.
    pub got_slot: usize,
    /// Number of parameters.
    pub arity: usize,
    /// Code pointer for the ORIGINAL implementation (not the wrapper).
    /// Embedded as `iconst` in the wrapper so it calls the original, not itself.
    pub code_ptr: i64,
    /// Static parameter types (from function's type scheme).
    pub param_types: Vec<Type>,
    /// Static return type (from function's type scheme).
    pub result_type: Type,
}

/// Shared immutable context for compilation, bundling references that
/// are threaded through from `compile_body` to all expression compilers.
///
/// All fields are references or `Copy`-ish types, so the struct is `Clone`.
/// This avoids verbose field-by-field copies when constructing inner compilers
/// (e.g., for lambda bodies).
#[derive(Clone)]
pub struct CompileContext<'a> {
    /// Function IDs for direct calls (Batch mode).
    pub func_ids: &'a HashMap<Symbol, FuncId>,
    /// Function parameter counts, for generating closure wrappers.
    pub func_arities: &'a HashMap<Symbol, usize>,
    /// Per-module symbol tables (shared, authoritative source for type defs,
    /// constructors, GOT slots, and post-G7 GOT base pointers). The backend
    /// reads GOT slots/bases directly from this map — no env abstraction.
    pub symbol_tables: &'a DashMap<ModuleFullPath, SymbolTable>,
    /// Current module being compiled (for constructor/type lookups).
    pub current_module: ModuleFullPath,


    // --- Ring 4 trace context ---
    /// Functions to instrument when compiling `(trace ...)` expressions.
    /// Populated by the integration layer from module symbol tables.
    /// None means trace codegen falls back to "no-swap" path (empty trace).
    pub traced_fns: Option<&'a [TracedFnInfo]>,

    // --- Ring 1 intrinsic FuncIds ---
    /// FuncId for runtime/alloc. None in Ring 0 (no heap).
    pub alloc_func_id: Option<FuncId>,
    /// FuncId for runtime/dealloc. Non-optional: Decision 24 retires the
    /// Option<...> conditional. Codegen always assumes dealloc is declared
    /// — all compile paths since Ring 1 require heap + RC support.
    pub dealloc_func_id: FuncId,
    /// FuncId for runtime/alloc_string. None in Ring 0 (no strings).
    pub alloc_string_func_id: Option<FuncId>,
    /// FuncId for runtime/panic. None in Ring 0 (uses trap instead).
    pub panic_func_id: Option<FuncId>,
    /// FuncId for runtime/vec_new. None in Ring 0 (no Vecs).
    pub vec_new_func_id: Option<FuncId>,
    /// FuncId for runtime/vec_drop. None in Ring 0 (no Vecs).
    pub vec_drop_func_id: Option<FuncId>,
}

impl<'a> CompileContext<'a> {
    /// Look up a constructor by name from the symbol tables.
    ///
    /// Accepts both bare names (`"SexpStr"`) and qualified names (`"macros/SexpStr"`).
    /// For qualified names, looks up directly in the specified module.
    /// For bare names, searches the current module's symbol table (following imports).
    /// Returns `(FQTypeName, ConstructorInfo)` if found.
    pub fn lookup_constructor(&self, name: &str) -> Option<(FQTypeName, ConstructorInfo)> {
        // Determine which module to search and the bare name within it.
        let (search_module, bare_name) = if let Some(slash_pos) = name.find('/') {
            let module_str = &name[..slash_pos];
            let bare = &name[slash_pos + 1..];
            (ModuleFullPath::from(module_str), bare)
        } else {
            (self.current_module.clone(), name)
        };

        // 1. Direct lookup in the target module.
        if let Some(table) = self.symbol_tables.get(&search_module) {
            if let Some(entry) = table.get(bare_name)
                && let Some(result) = Self::extract_constructor(entry)
            {
                return Some(result);
            }

            // Follow import chain.
            if let Some(ModuleEntry::Import { source }) = table.get(bare_name) {
                let source_mod = source.module.clone();
                let source_name = source.symbol.clone();
                drop(table); // Drop guard before getting another
                if let Some(source_table) = self.symbol_tables.get(&source_mod)
                    && let Some(entry) = source_table.get(source_name.as_ref())
                    && let Some(result) = Self::extract_constructor(entry)
                {
                    return Some(result);
                }
            }
        }

        // 2. Global fallback: search all modules for an unqualified name.
        //    This handles cases where constructors from synthetic modules
        //    (primitives, macros) are used without an explicit import.
        if !name.contains('/') {
            for guard in self.symbol_tables.iter() {
                if *guard.key() == self.current_module {
                    continue; // Already searched above
                }
                if let Some(entry) = guard.get(bare_name)
                    && let Some(result) = Self::extract_constructor(entry)
                {
                    return Some(result);
                }
            }
        }

        None
    }

    /// Extract constructor info from a module entry.
    ///
    /// Handles both `ModuleEntry::Constructor` (normal case) and
    /// `ModuleEntry::TypeDef` with `constructor_scheme` (product types
    /// where the constructor name equals the type name — the TypeDef
    /// entry overwrites the Constructor entry during registration).
    fn extract_constructor(entry: &ModuleEntry) -> Option<(FQTypeName, ConstructorInfo)> {
        match entry {
            ModuleEntry::Constructor { type_name, info, .. } => {
                Some((type_name.clone(), info.clone()))
            }
            ModuleEntry::TypeDef {
                info,
                constructor_scheme: Some(_),
                ..
            } => {
                // Product type: single constructor with same name as type.
                // The ConstructorInfo is in info.constructors[0].
                let ctor = info.constructors.first()?;
                Some((info.name.clone(), ctor.clone()))
            }
            _ => None,
        }
    }

    /// Look up a TypeDefInfo by FQTypeName from the symbol tables.
    pub fn lookup_type_def(&self, fqtn: &FQTypeName) -> Option<TypeDefInfo> {
        let table = self.symbol_tables.get(&fqtn.module)?;
        match table.get(fqtn.name.as_ref()) {
            Some(ModuleEntry::TypeDef { info, .. }) => Some(info.clone()),
            _ => None,
        }
    }
}

/// Match-arm-invariant data bundled to reduce parameter counts in
/// `compile_constructor_pattern`.
pub struct MatchContext {
    /// The compiled scrutinee value.
    pub scrut_val: Value,
    /// The inferred type of the scrutinee expression (for field type resolution).
    pub scrut_type: Option<Type>,
    /// The block to branch to if this arm does not match.
    pub next_block: Block,
    /// The merge block where all arms converge.
    pub merge_block: Block,
    /// The saved tail-position flag from before the match.
    pub saved_tail: bool,
}

/// Per-function compilation context.
///
/// Generic over `M: Module` so the same codegen can target both `JITModule`
/// (for immediate execution) and `ObjectModule` (for `.o` file generation).
/// See design/backend/module-caching.md §13.2 for rationale.
pub struct FnCompiler<'a, M: Module> {
    /// Cranelift function builder.
    pub builder: FunctionBuilder<'a>,
    /// Reference to the compilation module (JITModule or ObjectModule).
    pub module: &'a mut M,
    /// Local variable bindings (name -> Cranelift Variable).
    pub(crate) variables: HashMap<Symbol, Variable>,
    /// Scope stack: each frame is a list of variable names introduced.
    pub(crate) scope_stack: Vec<Vec<Symbol>>,
    /// Shared immutable compilation context.
    pub(crate) ctx: CompileContext<'a>,

    /// Next Cranelift Variable index (per-function counter).
    pub(crate) next_var: u32,

    // --- TCO state ---
    //
    // Tail Call Optimization (TCO): loop-based self-TCO.
    //
    // Self-recursive tail calls are compiled as jumps to a loop header block
    // instead of actual function calls. This converts recursion into iteration
    // with O(1) stack usage.
    //
    // The pattern:
    //   1. compile_body creates a loop_header block with block params for each fn param
    //   2. Entry block jumps to loop_header with initial param values
    //   3. Loop_header is NOT sealed eagerly (back-edges from tail calls added later)
    //   4. Body is compiled with in_tail_position = true
    //   5. Tail self-calls jump back to loop_header with new arg values
    //   6. All blocks sealed at the end
    //
    // CRITICAL: compile_apply must set in_tail_position = false before compiling args.
    // Tail position propagation:
    //   - If body / else body: inherits tail position
    //   - Let body: inherits tail position
    //   - Match arm bodies: inherit tail position
    //   - Args, conditions, bindings: NOT in tail position

    /// Name of the current function being compiled (for self-call detection).
    pub(crate) current_fn_name: Option<Symbol>,
    /// Loop header block for TCO (back-edge target for self-recursive tail calls).
    pub(crate) tail_loop_block: Option<Block>,
    /// Whether the current expression is in tail position.
    pub(crate) in_tail_position: bool,
    /// Number of parameters of the current function.
    pub(crate) fn_param_count: usize,

    // --- Ring 1 heap state (scaffolding for RC emission in Ring 2) ---

    /// Types of local variables, for RC management.
    pub(crate) variable_types: HashMap<Symbol, Type>,
    /// Last-use information: (var_name, span) -> is_last_use.
    pub(crate) last_uses: HashMap<(Symbol, Span), bool>,
    /// Set of variables whose ownership has been transferred (consumed).
    pub(crate) consumed_vars: std::collections::HashSet<Symbol>,
    /// Variables that borrow from a parent (e.g., pattern match field bindings).
    /// Borrowed vars skip both inc (at extraction) and dec (at scope exit).
    /// The owner (scrutinee) handles cleanup via its own RC management.
    pub(crate) borrowed_vars: std::collections::HashSet<Symbol>,
    /// Captured variable names (variables closed over by a lambda).
    /// These are NEVER eligible for last-use transfer.
    pub(crate) captured_vars: std::collections::HashSet<Symbol>,

    /// Drop glue FuncIds for closure variables.
    /// When a closure with heap-typed captures is bound to a variable,
    /// the drop glue function is stored here so that `pop_scope_with_cleanup`
    /// can pass it to `emit_rc_dec` when freeing the closure.
    pub(crate) closure_drop_glue: HashMap<Symbol, FuncId>,

    /// Depth counter for inline drop glue generation.
    /// Prevents infinite IR for recursive types (e.g., List).
    /// Allows limited nesting for non-recursive parametric types (e.g., Option(Option(String))).
    pub(crate) drop_glue_depth: u32,

    /// Pending closure drop glue from the last `compile_lambda` call.
    /// Set by `compile_lambda`, consumed by `compile_let` or `compile_body`
    /// when binding the closure value to a variable name.
    pub(crate) pending_closure_drop_glue: Option<FuncId>,

    /// Whether we are compiling inside a `(trace ...)` body.
    /// When true, sparkability analysis is disabled — trace bodies must
    /// execute sequentially to produce deterministic trace trees.
    pub(crate) in_trace_body: bool,
}

impl<'a, M: Module> FnCompiler<'a, M> {
    /// Create an inner `FnCompiler` for lambda bodies, continuations,
    /// or (future) drop glue. This is the single construction point for
    /// inner compilers (ring1-checklist section 5.9).
    ///
    /// TCO state is disabled for inner functions (no self-call detection,
    /// no tail loop). The scope and variable maps start fresh.
    pub(crate) fn inner(
        builder: FunctionBuilder<'a>,
        module: &'a mut M,
        ctx: CompileContext<'a>,
        fn_param_count: usize,
        last_uses: HashMap<(Symbol, Span), bool>,
    ) -> Self {
        FnCompiler {
            builder,
            module,
            variables: HashMap::new(),
            scope_stack: vec![vec![]],
            ctx,
            next_var: 0,
            current_fn_name: None,
            tail_loop_block: None,
            in_tail_position: false,
            fn_param_count,
            variable_types: HashMap::new(),
            last_uses,
            consumed_vars: std::collections::HashSet::new(),
            borrowed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
            closure_drop_glue: HashMap::new(),
            drop_glue_depth: 0,
            pending_closure_drop_glue: None,
            in_trace_body: false,
        }
    }

    /// Compile a function definition body into Cranelift IR.
    ///
    /// This is the main entry point called by Jit::compile_defn.
    /// Creates the entry block, loop header (for TCO), binds parameters,
    /// compiles the body, and finalizes.
    pub fn compile_body(
        defn: &Defn,
        func: &mut cranelift::codegen::ir::Function,
        func_ctx: &mut FunctionBuilderContext,
        module: &'a mut M,
        ctx: CompileContext<'a>,
    ) -> Result<(), CranelispError> {
        let mut builder = FunctionBuilder::new(func, func_ctx);

        // Entry block: receives function parameters.
        let entry_block = builder.create_block();
        builder.append_block_params_for_function_params(entry_block);
        builder.switch_to_block(entry_block);
        builder.seal_block(entry_block);

        // Create loop header block for TCO: one i64 block param per function param.
        let loop_header = builder.create_block();
        for _ in defn.params() {
            builder.append_block_param(loop_header, types::I64);
        }

        // Jump from entry to loop header with initial parameter values.
        let entry_params: Vec<Value> = builder.block_params(entry_block).to_vec();
        builder.ins().jump(loop_header, &entry_params);

        // Switch to loop header. Do NOT seal it yet -- back-edges from tail calls
        // will be added during body compilation.
        builder.switch_to_block(loop_header);

        // Compute last-use info for the body.
        let last_uses = heap::compute_last_uses(defn.body());

        let mut compiler = FnCompiler {
            builder,
            module,
            variables: HashMap::new(),
            scope_stack: vec![vec![]],
            ctx,
            next_var: 0,
            current_fn_name: Some(defn.name.clone()),
            tail_loop_block: Some(loop_header),
            in_tail_position: true,
            fn_param_count: defn.params().len(),
            variable_types: HashMap::new(),
            last_uses,
            consumed_vars: std::collections::HashSet::new(),
            borrowed_vars: std::collections::HashSet::new(),
            captured_vars: std::collections::HashSet::new(),
            closure_drop_glue: HashMap::new(),
            drop_glue_depth: 0,
            pending_closure_drop_glue: None,
            in_trace_body: false,
        };

        // Look up the defn's inferred type to get authoritative parameter types.
        // This is essential for unused parameters: derive_param_type scans
        // use sites, so unused params (e.g., `_s` in `(defn f [:String _s] 42)`)
        // would have no type recorded and scope cleanup would skip their RC dec.
        //
        // Read from the symbol table's Scheme.ty (authoritative source) rather
        // than from expr_types side map (Step 1c: AST-sourced codegen).
        let defn_param_types: Vec<Option<Type>> = compiler.ctx.symbol_tables
            .get(&compiler.ctx.current_module)
            .and_then(|table| {
                if let Some(ModuleEntry::Def { scheme, .. }) = table.get(defn.name.as_ref()) {
                    if let Type::Fn(ref param_types, _) = scheme.ty {
                        return Some(param_types.iter().map(|t| Some(t.clone())).collect());
                    }
                }
                None
            })
            .unwrap_or_else(|| vec![None; defn.params().len()]);

        // Bind function parameters from loop header block params (not entry block).
        // Also record parameter types in variable_types so scope cleanup
        // can emit rc_dec for heap-typed parameters at function exit.
        for (i, param_name) in defn.params().iter().enumerate() {
            let val = compiler.builder.block_params(loop_header)[i];
            let var = compiler.fresh_variable();
            compiler.builder.declare_var(var, types::I64);
            compiler.builder.def_var(var, val);
            compiler.variables.insert(param_name.clone(), var);
            compiler
                .scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(param_name.clone());

            // Use the defn's inferred param type (from symbol table) first.
            // Fall back to derive_param_type_from_body (use-site inference) if the
            // defn type isn't available.
            if let Some(Some(ty)) = defn_param_types.get(i) {
                compiler.variable_types.insert(param_name.clone(), ty.clone());
            } else if let Some(ty) = Self::derive_param_type_from_body(defn.body(), param_name) {
                compiler.variable_types.insert(param_name.clone(), ty);
            }
        }

        // Compile the function body with scope cleanup for parameters.
        // This implements the consuming calling convention: the callee owns
        // heap-typed parameters and dec's them at exit. The caller inc's
        // variable arguments before the call.
        let skip_var = Self::return_var_in_scope(defn.body(), compiler.scope_stack.last());
        let result = compiler.compile_expr(defn.body())?;
        compiler.protect_return_value(&skip_var, result, defn.body());
        compiler.pop_scope_with_cleanup(skip_var.as_ref());

        // Return the result.
        compiler.builder.ins().return_(&[result]);

        // Seal all blocks (including loop_header which may have back-edges).
        compiler.builder.seal_all_blocks();
        compiler.builder.finalize();

        Ok(())
    }

    // --- Expression dispatch ---

    /// Compile an expression, dispatching to the appropriate handler.
    pub fn compile_expr(&mut self, expr: &Expr) -> Result<Value, CranelispError> {
        match expr {
            Expr::IntLit { value, .. } => self.compile_int_lit(*value),
            Expr::FloatLit { value, .. } => self.compile_float_lit(*value),
            Expr::BoolLit { value, .. } => self.compile_bool_lit(*value),
            Expr::StringLit { value, span, .. } => self.compile_string_lit(value, *span),
            Expr::Var { name, span, .. } => self.compile_var(name, *span),
            Expr::Let {
                bindings,
                body,
                span,
                ..
            } => self.compile_let(bindings, body, *span),
            Expr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => self.compile_if(cond, then_branch, else_branch),
            Expr::Lambda {
                params, body, span, inferred_type, ..
            } => self.compile_lambda(params, body, *span, inferred_type.as_deref()),
            Expr::Apply {
                callee,
                args,
                span,
                resolved_call,
                inferred_type,
                ..
            } => self.compile_apply(callee, args, *span, resolved_call.as_deref(), inferred_type.as_deref()),
            Expr::Match {
                scrutinee,
                arms,
                span,
                ..
            } => self.compile_match(scrutinee, arms, *span),
            Expr::Annotate { expr, .. } => self.compile_expr(expr),
            Expr::VecLit { elements, span, .. } => self.compile_vec_lit(elements, *span),
            Expr::Trace {
                modules,
                body,
                span,
                ..
            } => self.compile_trace(modules, body, *span),
            Expr::ParBind {
                bindings,
                body,
                span,
                ..
            } => self.compile_par_bind(bindings, body, *span),
        }
    }

    // --- Variable allocation ---

    /// Allocate a fresh Cranelift Variable index.
    pub(crate) fn fresh_variable(&mut self) -> Variable {
        let idx = self.next_var;
        self.next_var += 1;
        Variable::new(idx as usize)
    }

    // --- Scope management ---

    pub(crate) fn push_scope(&mut self) {
        self.scope_stack.push(vec![]);
    }

    pub(crate) fn pop_scope(&mut self) {
        if let Some(frame) = self.scope_stack.pop() {
            for name in frame {
                self.variables.remove(&name);
                self.variable_types.remove(&name);
            }
        }
    }

    /// Pop a scope frame and emit `rc_dec` for all heap-typed bindings,
    /// except the variable named by `skip_var` (whose ownership transfers
    /// to the caller as the return value).
    ///
    /// Key invariant: "Scope cleanup emits dec for all heap-typed bindings
    /// EXCEPT the return value, consumed vars, and borrowed vars."
    ///
    /// Borrowed vars (e.g., pattern match field bindings) are skipped entirely —
    /// they share the owner's (scrutinee's) reference and the owner handles cleanup.
    ///
    /// ADT field cleanup happens inside the RC=0 dealloc path (via
    /// `emit_rc_dec_with_inline_drop_glue`), NOT as a separate step before dec.
    /// This prevents double-free when fields are independently referenced.
    pub(crate) fn pop_scope_with_cleanup(
        &mut self,
        skip_var: Option<&Symbol>,
    ) {
        if let Some(frame) = self.scope_stack.last() {
            // Collect bindings that need dec before we mutate state.
            let to_dec: Vec<(Symbol, Type, bool)> = frame
                .iter()
                .filter(|name| {
                    // Skip the return value variable.
                    if let Some(skip) = skip_var
                        && *name == skip {
                            return false;
                        }
                    // Skip consumed variables (ownership transferred to callee).
                    if self.consumed_vars.contains(*name) {
                        return false;
                    }
                    // Skip borrowed variables (owner handles cleanup).
                    if self.borrowed_vars.contains(*name) {
                        return false;
                    }
                    // Check if this binding is heap-typed.
                    if let Some(ty) = self.variable_types.get(*name) {
                        self.is_heap_type(ty)
                    } else {
                        false
                    }
                })
                .map(|name| {
                    let ty = self.variable_types.get(name).cloned()
                        .unwrap_or(Type::Int); // fallback, should not happen
                    let needs_guard = matches!(
                        HeapCategory::classify(&ty, Some(self.ctx.symbol_tables)),
                        HeapCategory::Mixed
                    );
                    (name.clone(), ty, needs_guard)
                })
                .collect();

            // Emit rc_dec for each heap-typed binding.
            let dealloc = self.ctx.dealloc_func_id;
            for (name, ty, needs_guard) in &to_dec {
                if let Some(var) = self.variables.get(name) {
                    let val = self.builder.use_var(*var);

                    // For closures (Type::Fn), use runtime-embedded drop glue.
                    // This handles both locally-created closures AND closures
                    // received as function parameters (where the static
                    // closure_drop_glue map has no entry).
                    if matches!(ty, Type::Fn(_, _)) {
                        self.emit_closure_dec_inline(val, dealloc);
                        continue;
                    }

                    // For ADTs: emit RC dec with inline drop glue in the
                    // dealloc path. Field cleanup ONLY happens when RC
                    // reaches 0 (inside the free branch), not unconditionally.
                    // This prevents double-free when fields are independently
                    // referenced (e.g., extracted via pattern match).
                    self.emit_rc_dec_with_inline_drop_glue(val, ty, dealloc, *needs_guard);
                }
            }
        }

        // Now actually pop the scope (remove variables from maps).
        self.pop_scope();
    }

    /// Emit inline drop glue for an ADT: dec each AlwaysHeap field.
    ///
    /// This is a temporary measure until proper drop glue functions are
    /// generated. It handles the common case of ADTs with String or other
    /// heap-typed fields.
    ///
    /// For Mixed ADTs (with both nullary and data constructors), the field
    /// dec is guarded by a heap-pointer check: if the value is a bare
    /// nullary tag, no fields exist to dec.
    fn emit_inline_drop_glue(
        &mut self,
        adt_val: Value,
        ty: &Type,
        dealloc: FuncId,
        is_mixed: bool,
    ) {
        let fqtn = match ty {
            Type::ADT(fqtn, _) => fqtn,
            _ => return, // Not an ADT; nothing to do.
        };

        let type_def = match self.ctx.lookup_type_def(fqtn) {
            Some(td) => td,
            None => return,
        };

        let subst = build_adt_type_substitution(ty, &type_def);

        // Collect data constructors (those with fields).
        let data_ctors: Vec<_> = type_def.constructors.iter()
            .filter(|c| !c.fields.is_empty())
            .collect();

        if data_ctors.is_empty() {
            return; // No data constructors, nothing to drop.
        }

        // Check if any data constructor has heap-typed fields.
        let has_heap_fields = data_ctors.iter().any(|ctor| {
            ctor.fields.iter().any(|f| {
                let resolved = substitute_type_inline(&f.ty, &subst);
                matches!(
                    HeapCategory::classify(&resolved, Some(self.ctx.symbol_tables)),
                    HeapCategory::AlwaysHeap | HeapCategory::Mixed
                )
            })
        });

        if !has_heap_fields {
            return; // No heap fields to drop.
        }

        // For Mixed ADTs, guard the field dec with a heap-pointer check.
        let cont_block = if is_mixed {
            Some(self.emit_mixed_adt_heap_guard(adt_val))
        } else {
            None
        };

        // Emit field decs for each data constructor.
        self.emit_drop_glue_field_decs(adt_val, &data_ctors, &subst, dealloc);

        // Jump to continuation for Mixed guard.
        if let Some(cont) = cont_block {
            self.builder.ins().jump(cont, &[]);
            self.builder.switch_to_block(cont);
            self.builder.seal_block(cont);
        }
    }

    /// Emit a heap-pointer guard for Mixed ADTs in drop glue.
    ///
    /// Creates a branch that skips field dec if the value is a bare nullary
    /// tag (below the heap threshold). Returns the continuation block that
    /// the caller must jump to when field dec is done.
    fn emit_mixed_adt_heap_guard(&mut self, adt_val: Value) -> Block {
        let cont = self.builder.create_block();
        let glue_block = self.builder.create_block();

        let threshold = self
            .builder
            .ins()
            .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
        let is_heap = self.builder.ins().icmp(
            IntCC::UnsignedGreaterThanOrEqual,
            adt_val,
            threshold,
        );
        self.builder
            .ins()
            .brif(is_heap, glue_block, &[], cont, &[]);

        self.builder.switch_to_block(glue_block);
        self.builder.seal_block(glue_block);
        cont
    }

    /// Emit field decs for data constructors in drop glue.
    ///
    /// For a single data constructor, dec fields directly.
    /// For multiple data constructors, emit tag-based dispatch
    /// (branch chain like match codegen).
    fn emit_drop_glue_field_decs(
        &mut self,
        adt_val: Value,
        data_ctors: &[&ConstructorInfo],
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc: FuncId,
    ) {
        use crate::heap::HeapAdt;

        if data_ctors.len() == 1 {
            let ctor = data_ctors[0];
            self.emit_field_decs(adt_val, ctor, subst, dealloc);
        } else {
            // Multiple data constructors: load the tag and branch to the
            // correct field-dec block for each variant.
            let heap_tag = heap::heap_load(
                &mut self.builder,
                adt_val,
                HeapAdt::TAG_OFFSET,
            );

            let done_block = self.builder.create_block();

            for (idx, ctor) in data_ctors.iter().enumerate() {
                let ctor_block = self.builder.create_block();
                let next_block = if idx + 1 < data_ctors.len() {
                    self.builder.create_block()
                } else {
                    // Last data constructor: fallthrough to done.
                    done_block
                };

                let tag_val = self.builder.ins().iconst(types::I64, ctor.tag as i64);
                let cmp = self.builder.ins().icmp(IntCC::Equal, heap_tag, tag_val);
                self.builder.ins().brif(cmp, ctor_block, &[], next_block, &[]);

                self.builder.switch_to_block(ctor_block);
                self.builder.seal_block(ctor_block);

                self.emit_field_decs(adt_val, ctor, subst, dealloc);
                self.builder.ins().jump(done_block, &[]);

                if idx + 1 < data_ctors.len() {
                    self.builder.switch_to_block(next_block);
                    self.builder.seal_block(next_block);
                }
            }

            self.builder.switch_to_block(done_block);
            self.builder.seal_block(done_block);
        }
    }

    /// Emit rc_dec for each heap-typed field of a single constructor.
    ///
    /// Used by `emit_inline_drop_glue` for both the single-constructor case
    /// and within each branch of the multi-constructor tag dispatch.
    ///
    /// For ADT-typed fields, uses `emit_rc_dec_with_inline_drop_glue` to
    /// recursively handle nested ADT field cleanup when the field's RC
    /// reaches 0. For non-ADT heap types (String, closures), uses plain
    /// `emit_rc_dec` since they have no sub-fields.
    fn emit_field_decs(
        &mut self,
        adt_val: Value,
        ctor: &ConstructorInfo,
        subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
        dealloc: FuncId,
    ) {
        use crate::heap::HeapAdt;

        for (i, field) in ctor.fields.iter().enumerate() {
            let resolved_ty = substitute_type_inline(&field.ty, subst);
            let category = HeapCategory::classify(&resolved_ty, Some(self.ctx.symbol_tables));
            match category {
                HeapCategory::AlwaysHeap => {
                    let field_val = heap::heap_load(
                        &mut self.builder,
                        adt_val,
                        HeapAdt::field_offset(i),
                    );
                    // For ADT-typed fields, recursively handle nested field cleanup.
                    if matches!(resolved_ty, Type::ADT(_, _)) {
                        self.emit_rc_dec_with_inline_drop_glue(
                            field_val, &resolved_ty, dealloc, false,
                        );
                    } else if matches!(resolved_ty, Type::Fn(_, _)) {
                        self.emit_closure_dec_inline(field_val, dealloc);
                    } else {
                        heap::emit_rc_dec(
                            &mut self.builder,
                            self.module,
                            field_val,
                            dealloc,
                            None,
                        );
                    }
                }
                HeapCategory::Mixed => {
                    let field_val = heap::heap_load(
                        &mut self.builder,
                        adt_val,
                        HeapAdt::field_offset(i),
                    );
                    // Mixed fields may be ADTs with nested heap fields.
                    if matches!(resolved_ty, Type::ADT(_, _)) {
                        self.emit_rc_dec_with_inline_drop_glue(
                            field_val, &resolved_ty, dealloc, true,
                        );
                    } else {
                        heap::emit_rc_dec_guarded(
                            &mut self.builder,
                            self.module,
                            field_val,
                            dealloc,
                            None,
                            true,
                        );
                    }
                }
                HeapCategory::NeverHeap => {}
            }
        }
    }

    // --- Return value identification ---

    /// If `body` is a direct variable reference to a name in the current scope
    /// frame, return that name. Used to skip rc_dec for the return value.
    pub(crate) fn return_var_in_scope(
        body: &Expr,
        scope_frame: Option<&Vec<Symbol>>,
    ) -> Option<Symbol> {
        if let Expr::Var { name, .. } = body
            && let Some(frame) = scope_frame
                && frame.contains(name) {
                    return Some(name.clone());
                }
        None
    }

    /// If `skip_var` is None and the return value has a heap type, emit
    /// `rc_inc` on the value so it survives the subsequent scope cleanup.
    /// Scope cleanup will dec all heap bindings, which may include the
    /// value being returned (when the body is a non-trivial expression like
    /// `if` or `match` that resolves to a scope binding). The caller will
    /// dec it later, so the net ownership is correct.
    pub(crate) fn protect_return_value(
        &mut self,
        skip_var: &Option<Symbol>,
        body_val: Value,
        body: &Expr,
    ) {
        if skip_var.is_some() {
            return; // The skip_var mechanism already protects the return value.
        }
        // Fresh allocations (Lambda, StringLit) cannot be the same as any
        // scope binding, so scope cleanup cannot affect them. Skip protect.
        if matches!(body, Expr::Lambda { .. } | Expr::StringLit { .. }) {
            return;
        }
        // Only protect if the current scope has heap-typed bindings that
        // scope cleanup will dec. If no bindings are heap-typed, the return
        // value cannot be affected by scope cleanup regardless of its type.
        let has_heap_bindings = self.scope_stack.last().is_some_and(|frame| {
            frame.iter().any(|name| {
                self.variable_types.get(name).is_some_and(|ty| self.is_heap_type(ty))
            })
        });
        if !has_heap_bindings {
            return;
        }
        if let Some(ty) = body.inferred_type() {
            let category = HeapCategory::classify(ty, Some(self.ctx.symbol_tables));
            match category {
                HeapCategory::AlwaysHeap => {
                    heap::emit_rc_inc(&mut self.builder, body_val);
                }
                HeapCategory::Mixed => {
                    heap::emit_rc_inc_guarded(&mut self.builder, body_val);
                }
                HeapCategory::NeverHeap => {}
            }
        }
    }

    // --- Heap helpers (scaffolding for RC emission in Ring 2) ---

    /// Check if a type is heap-allocated and needs RC management.
    pub(crate) fn is_heap_type(&self, ty: &Type) -> bool {
        matches!(
            HeapCategory::classify(ty, Some(self.ctx.symbol_tables)),
            HeapCategory::AlwaysHeap | HeapCategory::Mixed
        )
    }

    /// Derive a function parameter's type by finding a Var reference with the
    /// given name in the function body and reading its `inferred_type()`.
    ///
    /// Function parameters don't have their own `inferred_type`, but every
    /// Var reference to the parameter in the body does. We walk the body AST
    /// to find the first Var node matching the name.
    pub(crate) fn derive_param_type_from_body(body: &Expr, name: &Symbol) -> Option<Type> {
        find_var_type_in_expr(body, name)
    }

    /// Check if a variable use is the last use (for ownership transfer).
    pub(crate) fn is_last_use(&self, name: &Symbol, span: Span) -> bool {
        if self.captured_vars.contains(name) {
            // Captured variables are NEVER eligible for last-use transfer.
            return false;
        }
        self.last_uses
            .get(&(name.clone(), span))
            .copied()
            .unwrap_or(false)
    }

    /// Emit RC dec for a closure value using its embedded drop glue pointer.
    ///
    /// Unlike `emit_rc_dec` which takes a compile-time `drop_glue_id`,
    /// this loads the drop glue pointer from the closure's embedded
    /// `DROP_GLUE_PTR_OFFSET` field at runtime and calls it if non-zero.
    ///
    /// Used for:
    /// - Closure parameters received from callers (type unknown at compile time)
    /// - Temporary closure expressions used as callees
    /// - Any closure variable where the static drop glue is not available
    pub(crate) fn emit_closure_dec_inline(&mut self, closure_val: Value, dealloc_id: FuncId) {
        use crate::heap::HeapClosure;
        use cranelisp_types::HeapHeader;
        use cranelift_codegen::ir::AtomicRmwOp;

        let cont_block = self.builder.create_block();

        // Decrement RC.
        let rc_addr = self
            .builder
            .ins()
            .iadd_imm(closure_val, i64::from(HeapHeader::RC_OFFSET));
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // Branch: if old_rc == 1, free the closure.
        let cmp = self.builder.ins().icmp(IntCC::Equal, old_rc, one);
        let free_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(cmp, free_block, &[], cont_block, &[]);

        // Free path.
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);
        self.builder.ins().fence();

        // Load drop_glue_ptr from the closure.
        let drop_glue_ptr = heap::heap_load(
            &mut self.builder,
            closure_val,
            HeapClosure::DROP_GLUE_PTR_OFFSET,
        );

        // If drop_glue_ptr != 0, call it.
        let zero = self.builder.ins().iconst(types::I64, 0);
        let has_glue = self
            .builder
            .ins()
            .icmp(IntCC::NotEqual, drop_glue_ptr, zero);
        let glue_block = self.builder.create_block();
        let dealloc_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(has_glue, glue_block, &[], dealloc_block, &[]);

        // Call drop glue: (closure_ptr: i64) -> ()
        self.builder.switch_to_block(glue_block);
        self.builder.seal_block(glue_block);

        let mut glue_sig = self.module.make_signature();
        glue_sig.params.push(AbiParam::new(types::I64));
        let glue_sig_ref = self.builder.import_signature(glue_sig);
        self.builder
            .ins()
            .call_indirect(glue_sig_ref, drop_glue_ptr, &[closure_val]);
        self.builder.ins().jump(dealloc_block, &[]);

        // Dealloc the closure.
        self.builder.switch_to_block(dealloc_block);
        self.builder.seal_block(dealloc_block);
        let dealloc_ref = self
            .module
            .declare_func_in_func(dealloc_id, self.builder.func);
        self.builder.ins().call(dealloc_ref, &[closure_val]);
        self.builder.ins().jump(cont_block, &[]);

        // Continue.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);
    }

    /// Emit RC dec for an ADT value with inline drop glue in the dealloc path.
    ///
    /// Unlike the old `emit_inline_drop_glue` + `emit_rc_dec` pattern (which
    /// dec'd fields unconditionally before dec'ing the ADT), this method
    /// only dec's fields inside the "RC reached 0" branch. This prevents
    /// double-free when fields have independent references (e.g., extracted
    /// via pattern match binding).
    ///
    /// Flow:
    /// ```text
    /// if needs_guard && val < NULLARY_THRESHOLD: skip (bare tag)
    /// old_rc = atomic_sub(val.rc, 1)
    /// if old_rc == 1:
    ///     fence()
    ///     emit_inline_drop_glue(val)   // dec heap-typed fields
    ///     dealloc(val)
    /// ```
    pub(crate) fn emit_rc_dec_with_inline_drop_glue(
        &mut self,
        val: Value,
        ty: &Type,
        dealloc: FuncId,
        needs_guard: bool,
    ) {
        use cranelisp_types::HeapHeader;
        use cranelift_codegen::ir::AtomicRmwOp;

        // Depth limit for inline drop glue: prevents infinite IR for
        // recursive types (e.g., List contains List). Allows several
        // levels of nesting for non-recursive parametric types like
        // Option(Option(String)). Beyond the limit, fall back to plain
        // dec (fields leak — known limitation of inline drop glue,
        // to be replaced by proper drop-glue functions later).
        const MAX_DROP_GLUE_DEPTH: u32 = 4;
        if self.drop_glue_depth >= MAX_DROP_GLUE_DEPTH {
            if needs_guard {
                heap::emit_rc_dec_guarded(
                    &mut self.builder, self.module, val, dealloc, None, true,
                );
            } else {
                heap::emit_rc_dec(
                    &mut self.builder, self.module, val, dealloc, None,
                );
            }
            return;
        }
        self.drop_glue_depth += 1;

        let cont_block = self.builder.create_block();

        // Guard: if value is a bare nullary tag, skip the dec entirely.
        if needs_guard {
            let threshold = self
                .builder
                .ins()
                .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
            let is_tag = self.builder.ins().icmp(
                IntCC::UnsignedLessThan,
                val,
                threshold,
            );
            let dec_block = self.builder.create_block();
            self.builder
                .ins()
                .brif(is_tag, cont_block, &[], dec_block, &[]);
            self.builder.switch_to_block(dec_block);
            self.builder.seal_block(dec_block);
        }

        // Atomic dec RC.
        let rc_addr = self
            .builder
            .ins()
            .iadd_imm(val, i64::from(HeapHeader::RC_OFFSET));
        let one = self.builder.ins().iconst(types::I64, 1);
        let old_rc = self.builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        );

        // Branch: if old_rc == 1 (last reference), free the object.
        let cmp = self.builder.ins().icmp(IntCC::Equal, old_rc, one);
        let free_block = self.builder.create_block();
        self.builder
            .ins()
            .brif(cmp, free_block, &[], cont_block, &[]);

        // Free path: Acquire fence, drop glue for fields, then dealloc.
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);
        self.builder.ins().fence();

        // Emit inline drop glue for ADT fields (only in the dealloc path).
        // This is safe because RC==0 means we are the sole owner.
        self.emit_inline_drop_glue(val, ty, dealloc, false);

        // Call runtime/dealloc.
        let dealloc_ref = self
            .module
            .declare_func_in_func(dealloc, self.builder.func);
        self.builder.ins().call(dealloc_ref, &[val]);
        self.builder.ins().jump(cont_block, &[]);

        // Continue path.
        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);

        // Restore depth counter.
        self.drop_glue_depth -= 1;
    }

    /// Mark a variable as borrowed (skip scope-exit dec — owner handles cleanup).
    pub(crate) fn mark_borrowed(&mut self, name: &Symbol) {
        self.borrowed_vars.insert(name.clone());
    }
}

// --- Free helper functions for type variable resolution ---

/// Build a substitution map from type variable IDs to concrete types
/// for an ADT value. Extracts the concrete type args from the ADT type
/// and maps them positionally to the Var IDs found in the type definition.
pub(crate) fn build_adt_type_substitution(
    ty: &Type,
    type_def: &TypeDefInfo,
) -> std::collections::HashMap<cranelisp_types::TypeId, Type> {
    // Get concrete type args from the variable's type.
    let concrete_args = match ty {
        Type::ADT(_, args) => args.clone(),
        _ => return std::collections::HashMap::new(),
    };

    // Build substitution from Var ids to concrete types.
    let mut unique_var_ids: Vec<cranelisp_types::TypeId> = Vec::new();
    for c in &type_def.constructors {
        for field in &c.fields {
            collect_var_ids_from_type(&field.ty, &mut unique_var_ids);
        }
    }
    unique_var_ids
        .iter()
        .zip(concrete_args.iter())
        .map(|(&id, arg)| (id, arg.clone()))
        .collect()
}

/// Collect all unique Var ids from a type, in order of first appearance.
pub(crate) fn collect_var_ids_from_type(ty: &Type, ids: &mut Vec<cranelisp_types::TypeId>) {
    match ty {
        Type::Var(id)
            if !ids.contains(id) => {
                ids.push(*id);
            }
        Type::ADT(_, args) => {
            for a in args {
                collect_var_ids_from_type(a, ids);
            }
        }
        Type::Fn(params, ret) => {
            for p in params {
                collect_var_ids_from_type(p, ids);
            }
            collect_var_ids_from_type(ret, ids);
        }
        _ => {}
    }
}

/// Substitute type variables in a type using a Var id -> Type mapping.
pub(crate) fn substitute_type_inline(
    ty: &Type,
    subst: &std::collections::HashMap<cranelisp_types::TypeId, Type>,
) -> Type {
    match ty {
        Type::Var(id) => {
            subst.get(id).cloned().unwrap_or_else(|| ty.clone())
        }
        Type::ADT(name, args) => {
            let new_args = args.iter().map(|a| substitute_type_inline(a, subst)).collect();
            Type::ADT(name.clone(), new_args)
        }
        Type::Fn(params, ret) => {
            let new_params = params.iter().map(|p| substitute_type_inline(p, subst)).collect();
            let new_ret = Box::new(substitute_type_inline(ret, subst));
            Type::Fn(new_params, new_ret)
        }
        _ => ty.clone(),
    }
}

/// Find the inferred type of a Var reference with the given name in an expression tree.
///
/// Walks the AST recursively and returns the first Var node's `inferred_type()`
/// that matches the name. Used by `derive_param_type_from_body` to find parameter
/// types from use sites when the defn-level type is not available.
fn find_var_type_in_expr(expr: &Expr, name: &Symbol) -> Option<Type> {
    match expr {
        Expr::Var { name: var_name, inferred_type, .. } if var_name == name => {
            inferred_type.as_deref().cloned()
        }
        Expr::Let { bindings, body, .. } => {
            for (_, val) in bindings {
                if let Some(ty) = find_var_type_in_expr(val, name) {
                    return Some(ty);
                }
            }
            find_var_type_in_expr(body, name)
        }
        Expr::If { cond, then_branch, else_branch, .. } => {
            find_var_type_in_expr(cond, name)
                .or_else(|| find_var_type_in_expr(then_branch, name))
                .or_else(|| find_var_type_in_expr(else_branch, name))
        }
        Expr::Lambda { body, .. } => find_var_type_in_expr(body, name),
        Expr::Apply { callee, args, .. } => {
            find_var_type_in_expr(callee, name)
                .or_else(|| args.iter().find_map(|a| find_var_type_in_expr(a, name)))
        }
        Expr::Match { scrutinee, arms, .. } => {
            find_var_type_in_expr(scrutinee, name)
                .or_else(|| arms.iter().find_map(|arm| find_var_type_in_expr(&arm.body, name)))
        }
        Expr::Annotate { expr, .. } => find_var_type_in_expr(expr, name),
        Expr::VecLit { elements, .. } => {
            elements.iter().find_map(|e| find_var_type_in_expr(e, name))
        }
        Expr::Trace { body, .. } => find_var_type_in_expr(body, name),
        Expr::ParBind { bindings, body, .. } => {
            for (_, val) in bindings {
                if let Some(ty) = find_var_type_in_expr(val, name) {
                    return Some(ty);
                }
            }
            find_var_type_in_expr(body, name)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    // FnCompiler is tested via the public compile_and_run_expr API in lib.rs
    // and through the Jit::compile_defn path. Direct unit testing of FnCompiler
    // requires constructing a full Cranelift context, which is covered by
    // the integration tests.
}
