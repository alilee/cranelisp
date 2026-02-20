use std::collections::{HashMap, HashSet};

use cranelift::codegen::ir::BlockArg;
use cranelift::prelude::*;
use cranelift_module::{FuncId, Linkage, Module};

use crate::ast::*;
use crate::error::{CranelispError, Span};
use crate::names::resolve_bare_name;
use crate::typechecker::{MethodResolutions, TypeDefInfo};
use crate::types::Type;

mod apply;
mod closures;
mod expr;
mod match_compile;
mod primitives;

/// How the GOT base address is referenced in codegen.
#[derive(Clone)]
pub enum GotReference {
    /// JITModule: GOT base is a known address, embedded as iconst.
    Immediate(i64),
    /// ObjectModule: GOT base is a data symbol, resolved via relocation.
    DataSymbol(cranelift_module::DataId),
}

/// Metadata for a user-defined function, used during codegen for indirect calls.
#[derive(Clone)]
pub struct FnSlot {
    /// How to obtain the GOT base address for this function's module.
    pub got_ref: GotReference,
    pub slot: usize,
    pub param_count: usize,
}

impl FnSlot {
    /// Emit the GOT base address into the given function builder.
    pub fn emit_got_base<M: Module>(
        &self,
        builder: &mut FunctionBuilder,
        module: &mut M,
    ) -> Value {
        match &self.got_ref {
            GotReference::Immediate(addr) => builder.ins().iconst(types::I64, *addr),
            GotReference::DataSymbol(data_id) => {
                let gv = module.declare_data_in_func(*data_id, builder.func);
                builder.ins().global_value(types::I64, gv)
            }
        }
    }
}

/// How user-defined function calls are compiled.
pub(crate) enum CallMode<'a> {
    /// Direct calls via FuncId lookup (batch mode).
    Direct { func_ids: HashMap<String, FuncId> },
    /// Indirect calls via function pointer table (REPL/module mode).
    Indirect {
        fn_slots: &'a HashMap<String, FnSlot>,
    },
}

/// Info about a single constructor for codegen.
#[derive(Debug, Clone)]
pub struct ConstructorInfoCg {
    pub name: String,
    pub tag: usize,
    pub fields: Vec<String>,
    pub field_types: Vec<Type>,
}

/// Info about a type definition for codegen.
#[derive(Debug, Clone)]
pub struct TypeDefInfoCg {
    pub name: String,
    pub type_params: Vec<crate::types::TypeId>,
    pub constructors: Vec<ConstructorInfoCg>,
}

/// Info about a field accessor for codegen.
#[derive(Debug, Clone)]
pub struct AccessorInfoCg {
    pub field_index: usize,
    pub tag: usize,
    pub is_product: bool, // true = single constructor (total accessor), false = sum type (partial)
}

/// Convert typechecker type defs to codegen type defs.
pub fn build_type_defs_cg(
    type_defs: &HashMap<String, TypeDefInfo>,
) -> HashMap<String, TypeDefInfoCg> {
    type_defs
        .iter()
        .map(|(name, tdi)| {
            let ctors = tdi
                .constructors
                .iter()
                .map(|ci| ConstructorInfoCg {
                    name: ci.name.clone(),
                    tag: ci.tag,
                    fields: ci.fields.iter().map(|(fname, _)| fname.clone()).collect(),
                    field_types: ci.fields.iter().map(|(_, fty)| fty.clone()).collect(),
                })
                .collect();
            (
                name.clone(),
                TypeDefInfoCg {
                    name: tdi.name.clone(),
                    type_params: tdi.type_params.clone(),
                    constructors: ctors,
                },
            )
        })
        .collect()
}

pub(crate) struct FnCompiler<'a, M: Module> {
    pub(crate) builder: FunctionBuilder<'a>,
    pub(crate) module: &'a mut M,
    pub(crate) variables: HashMap<String, Variable>,
    pub(crate) call_mode: CallMode<'a>,
    pub(crate) alloc_func_id: FuncId,
    /// Set of global names (top-level functions + builtins) for capture analysis.
    pub(crate) globals: HashSet<String>,
    /// Resolved trait method calls (span -> mangled name + builtin flag).
    pub(crate) method_resolutions: &'a MethodResolutions,
    /// Per-function resolutions for monomorphised specializations (overrides method_resolutions).
    pub(crate) fn_specific_resolutions: Option<&'a MethodResolutions>,
    /// Builtin trait method FuncIds (mangled name -> FuncId).
    pub(crate) builtin_methods: &'a HashMap<String, FuncId>,
    /// Per-module symbol tables (for BuiltinFn resolution).
    pub(crate) modules: &'a HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    /// Type definitions for ADT codegen.
    pub(crate) type_defs: Option<&'a HashMap<String, TypeDefInfoCg>>,
    /// Constructor name → type name mapping.
    pub(crate) constructor_to_type: Option<&'a HashMap<String, String>>,
    /// Panic function for match failures.
    pub(crate) panic_func_id: Option<FuncId>,
    /// Expression types from the typechecker, for RC decisions.
    pub(crate) expr_types: &'a HashMap<Span, Type>,
    /// Free function for RC dec-to-zero.
    pub(crate) free_func_id: FuncId,
    /// Type of each named variable, for RC decisions.
    pub(crate) variable_types: HashMap<String, Type>,
    /// Stack of scope frames for RC cleanup. Each frame tracks heap-typed bindings.
    pub(crate) scope_stack: Vec<Vec<(String, Variable, Type)>>,
    /// Cache of generated drop functions (mangled type name -> FuncId).
    pub(crate) drop_fn_cache: HashMap<String, FuncId>,
    /// Name of the current function being compiled (for self-call detection in TCO).
    pub(crate) current_fn_name: Option<String>,
    /// Loop header block for TCO jumps (back-edge target).
    pub(crate) tail_loop_block: Option<Block>,
    /// Whether the current expression is in tail position.
    pub(crate) in_tail_position: bool,
    /// Number of function parameters (for TCO arg count validation).
    pub(crate) fn_param_count: usize,
}

impl<'a, M: Module> FnCompiler<'a, M> {
    pub(crate) fn fresh_var(&mut self, ty: types::Type) -> Variable {
        self.builder.declare_var(ty)
    }

    /// If name is a nullary constructor, return its tag. Otherwise None.
    pub(crate) fn nullary_constructor_tag(&self, name: &str) -> Option<usize> {
        let bare = resolve_bare_name(name);
        let c2t = self.constructor_to_type.as_ref()?;
        let type_name = c2t.get(bare)?;
        let tds = self.type_defs.as_ref()?;
        let td = tds.get(type_name)?;
        td.constructors
            .iter()
            .find(|c| c.name == bare && c.fields.is_empty())
            .map(|c| c.tag)
    }

    /// If name is a data constructor (has fields), return its info. Otherwise None.
    pub(crate) fn data_constructor_info(&self, name: &str) -> Option<&ConstructorInfoCg> {
        let bare = resolve_bare_name(name);
        let c2t = self.constructor_to_type.as_ref()?;
        let type_name = c2t.get(bare)?;
        let tds = self.type_defs.as_ref()?;
        let td = tds.get(type_name)?;
        td.constructors
            .iter()
            .find(|c| c.name == bare && !c.fields.is_empty())
    }

    /// If name is a field accessor, return its codegen info. Otherwise None.
    pub(crate) fn accessor_info(&self, name: &str) -> Option<AccessorInfoCg> {
        let bare = resolve_bare_name(name);
        let tds = self.type_defs.as_ref()?;
        for td in tds.values() {
            for ctor in &td.constructors {
                for (fi, fname) in ctor.fields.iter().enumerate() {
                    if fname == bare {
                        let is_product = td.constructors.len() == 1;
                        return Some(AccessorInfoCg {
                            field_index: fi,
                            tag: ctor.tag,
                            is_product,
                        });
                    }
                }
            }
        }
        None
    }

    /// Check if a name refers to a known top-level function (not shadowed by a local variable).
    pub(crate) fn is_known_function(&self, name: &str) -> bool {
        let bare = resolve_bare_name(name);
        if self.variables.contains_key(bare) {
            return false;
        }
        match &self.call_mode {
            CallMode::Direct { func_ids } => func_ids.contains_key(bare),
            CallMode::Indirect { fn_slots, .. } => fn_slots.contains_key(bare),
        }
    }

    /// Allocate a closure: call cranelisp_alloc(size), returns pointer.
    pub(crate) fn compile_alloc(
        &mut self,
        size: i64,
        _span: crate::error::Span,
    ) -> Result<Value, CranelispError> {
        let alloc_ref = self
            .module
            .declare_func_in_func(self.alloc_func_id, self.builder.func);
        let size_val = self.builder.ins().iconst(types::I64, size);
        let call = self.builder.ins().call(alloc_ref, &[size_val]);
        Ok(self.builder.inst_results(call)[0])
    }

    /// Push a new scope frame onto the stack.
    pub(crate) fn push_scope(&mut self) {
        self.scope_stack.push(Vec::new());
    }

    /// Track a heap-typed binding in the current (top) scope frame.
    pub(crate) fn track_binding(&mut self, name: String, var: Variable, ty: Type) {
        if let Some(frame) = self.scope_stack.last_mut() {
            frame.push((name, var, ty));
        }
    }

    /// Pop the top scope frame, emitting dec for each binding except the result value.
    /// Uses runtime value comparison to skip dec on the value being returned.
    pub(crate) fn pop_scope_for_value(&mut self, result_val: Value) {
        if let Some(frame) = self.scope_stack.pop() {
            for (_, var, ty) in &frame {
                if matches!(self.heap_category(ty), HeapCategory::NeverHeap) {
                    continue;
                }
                let val = self.builder.use_var(*var);
                let is_result = self.builder.ins().icmp(IntCC::Equal, val, result_val);
                let dec_block = self.builder.create_block();
                let skip_block = self.builder.create_block();
                self.builder
                    .ins()
                    .brif(is_result, skip_block, &[], dec_block, &[]);
                self.builder.switch_to_block(dec_block);
                self.builder.seal_block(dec_block);
                self.emit_dec(val, ty);
                self.builder.ins().jump(skip_block, &[]);
                self.builder.switch_to_block(skip_block);
                self.builder.seal_block(skip_block);
            }
        }
    }

    /// Emit RC dec for all heap-typed bindings in all scopes (for TCO jump cleanup).
    /// Function params are NOT on scope_stack, so they're unaffected.
    pub(crate) fn emit_scope_cleanup_for_tco(&mut self) {
        // Collect (var, ty) pairs first to avoid borrow conflict with emit_dec
        let bindings: Vec<(Variable, Type)> = self
            .scope_stack
            .iter()
            .flat_map(|scope| scope.iter())
            .filter(|(_, _, ty)| {
                !matches!(
                    classify_heap_type(ty, self.type_defs),
                    HeapCategory::NeverHeap
                )
            })
            .map(|(_, var, ty)| (*var, ty.clone()))
            .collect();
        for (var, ty) in &bindings {
            let val = self.builder.use_var(*var);
            self.emit_dec(val, ty);
        }
    }

    /// Resolve concrete field types for a constructor, given the scrutinee's ADT type.
    /// Substitutes the type definition's type_params with the scrutinee's concrete type args.
    pub(crate) fn resolve_field_types(&self, ctor_name: &str, scrutinee_type: &Type) -> Vec<Type> {
        let (type_name, type_args) = match scrutinee_type {
            Type::ADT(name, args) => (name.as_str(), args.as_slice()),
            _ => return Vec::new(),
        };
        let tds = match self.type_defs {
            Some(tds) => tds,
            None => return Vec::new(),
        };
        let td = match tds.get(type_name) {
            Some(td) => td,
            None => return Vec::new(),
        };
        let bare_ctor = resolve_bare_name(ctor_name);
        let ctor = match td.constructors.iter().find(|c| c.name == bare_ctor) {
            Some(c) => c,
            None => return Vec::new(),
        };
        // Substitute type_params → type_args in each field type
        ctor.field_types
            .iter()
            .map(|ft| substitute_type_params(ft, &td.type_params, type_args))
            .collect()
    }

    /// Classify whether a type's values are always heap-allocated, never, or mixed.
    fn heap_category(&self, ty: &Type) -> HeapCategory {
        match ty {
            Type::String | Type::Fn(_, _) => HeapCategory::AlwaysHeap,
            Type::ADT(name, _) if name == "Vec" => HeapCategory::AlwaysHeap,
            Type::ADT(name, _) => {
                if let Some(tds) = self.type_defs {
                    if let Some(td) = tds.get(name) {
                        let has_nullary = td.constructors.iter().any(|c| c.fields.is_empty());
                        let has_data = td.constructors.iter().any(|c| !c.fields.is_empty());
                        match (has_nullary, has_data) {
                            (true, true) => HeapCategory::Mixed,
                            (true, false) => HeapCategory::NeverHeap,
                            (false, true) => HeapCategory::AlwaysHeap,
                            (false, false) => HeapCategory::NeverHeap,
                        }
                    } else {
                        HeapCategory::Mixed // conservative
                    }
                } else {
                    HeapCategory::Mixed // conservative
                }
            }
            _ => HeapCategory::NeverHeap,
        }
    }

    /// Emit inline RC increment for a heap-typed value.
    /// For mixed ADTs (nullary + data constructors), adds a runtime guard.
    pub(crate) fn emit_inc(&mut self, val: Value, ty: &Type) {
        match self.heap_category(ty) {
            HeapCategory::NeverHeap => {}
            HeapCategory::AlwaysHeap => {
                self.emit_inc_inline(val);
            }
            HeapCategory::Mixed => {
                // Guard: if val < 1024, it's a nullary tag, skip
                let inc_block = self.builder.create_block();
                let skip_block = self.builder.create_block();

                let threshold = self.builder.ins().iconst(types::I64, 1024);
                let is_nullary = self
                    .builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThan, val, threshold);
                self.builder
                    .ins()
                    .brif(is_nullary, skip_block, &[], inc_block, &[]);

                self.builder.switch_to_block(inc_block);
                self.builder.seal_block(inc_block);
                self.emit_inc_inline(val);
                self.builder.ins().jump(skip_block, &[]);

                self.builder.switch_to_block(skip_block);
                self.builder.seal_block(skip_block);
            }
        }
    }

    fn emit_inc_inline(&mut self, val: Value) {
        let rc = self
            .builder
            .ins()
            .load(types::I64, MemFlags::trusted(), val, -8);
        let one = self.builder.ins().iconst(types::I64, 1);
        let new_rc = self.builder.ins().iadd(rc, one);
        self.builder
            .ins()
            .store(MemFlags::trusted(), new_rc, val, -8);
    }

    /// Emit inline RC decrement for a heap-typed value.
    /// Branches to free when rc reaches zero. For mixed ADTs, adds a runtime guard.
    pub(crate) fn emit_dec(&mut self, val: Value, ty: &Type) {
        match self.heap_category(ty) {
            HeapCategory::NeverHeap => {}
            HeapCategory::AlwaysHeap => {
                // Resolve drop function before emitting IR (avoids borrow conflict)
                let drop_fn = resolve_drop_fn(
                    ty,
                    self.module,
                    self.type_defs,
                    self.free_func_id,
                    &mut self.drop_fn_cache,
                );
                self.emit_dec_inline(val, drop_fn);
            }
            HeapCategory::Mixed => {
                let drop_fn = resolve_drop_fn(
                    ty,
                    self.module,
                    self.type_defs,
                    self.free_func_id,
                    &mut self.drop_fn_cache,
                );

                let dec_block = self.builder.create_block();
                let skip_block = self.builder.create_block();

                let threshold = self.builder.ins().iconst(types::I64, 1024);
                let is_nullary = self
                    .builder
                    .ins()
                    .icmp(IntCC::UnsignedLessThan, val, threshold);
                self.builder
                    .ins()
                    .brif(is_nullary, skip_block, &[], dec_block, &[]);

                self.builder.switch_to_block(dec_block);
                self.builder.seal_block(dec_block);
                self.emit_dec_inline(val, drop_fn);
                self.builder.ins().jump(skip_block, &[]);

                self.builder.switch_to_block(skip_block);
                self.builder.seal_block(skip_block);
            }
        }
    }

    fn emit_dec_inline(&mut self, val: Value, drop_fn: Option<FuncId>) {
        let rc = self
            .builder
            .ins()
            .load(types::I64, MemFlags::trusted(), val, -8);
        let one = self.builder.ins().iconst(types::I64, 1);
        let new_rc = self.builder.ins().isub(rc, one);

        let store_block = self.builder.create_block();
        let free_block = self.builder.create_block();
        let cont_block = self.builder.create_block();

        let is_zero = self.builder.ins().icmp_imm(IntCC::Equal, new_rc, 0);
        self.builder
            .ins()
            .brif(is_zero, free_block, &[], store_block, &[]);

        // store_block: write decremented rc and continue
        self.builder.switch_to_block(store_block);
        self.builder.seal_block(store_block);
        self.builder
            .ins()
            .store(MemFlags::trusted(), new_rc, val, -8);
        self.builder.ins().jump(cont_block, &[]);

        // free_block: call drop function (which decs fields and frees) or just free
        self.builder.switch_to_block(free_block);
        self.builder.seal_block(free_block);
        if let Some(drop_fid) = drop_fn {
            let drop_ref = self
                .module
                .declare_func_in_func(drop_fid, self.builder.func);
            self.builder.ins().call(drop_ref, &[val]);
        } else {
            let free_ref = self
                .module
                .declare_func_in_func(self.free_func_id, self.builder.func);
            self.builder.ins().call(free_ref, &[val]);
        }
        self.builder.ins().jump(cont_block, &[]);

        self.builder.switch_to_block(cont_block);
        self.builder.seal_block(cont_block);
    }
}

/// Whether a type's runtime values are heap pointers, never heap, or mixed.
enum HeapCategory {
    NeverHeap,
    AlwaysHeap,
    Mixed,
}

/// Substitute type variable IDs with concrete type args.
/// `params` and `args` must have the same length.
pub(crate) fn substitute_type_params(
    ty: &Type,
    params: &[crate::types::TypeId],
    args: &[Type],
) -> Type {
    match ty {
        Type::Var(id) => {
            if let Some(pos) = params.iter().position(|p| p == id) {
                if pos < args.len() {
                    return args[pos].clone();
                }
            }
            ty.clone()
        }
        Type::Fn(param_types, ret) => Type::Fn(
            param_types
                .iter()
                .map(|t| substitute_type_params(t, params, args))
                .collect(),
            Box::new(substitute_type_params(ret, params, args)),
        ),
        Type::ADT(name, type_args) => Type::ADT(
            name.clone(),
            type_args
                .iter()
                .map(|t| substitute_type_params(t, params, args))
                .collect(),
        ),
        _ => ty.clone(),
    }
}

/// Mangle a type into a string for drop function naming.
fn mangle_type_for_drop(ty: &Type) -> String {
    match ty {
        Type::Int => "Int".to_string(),
        Type::Bool => "Bool".to_string(),
        Type::Float => "Float".to_string(),
        Type::String => "String".to_string(),
        Type::Fn(_, _) => "Fn".to_string(),
        Type::ADT(name, args) if args.is_empty() => name.clone(),
        Type::ADT(name, args) => {
            let arg_strs: Vec<String> = args.iter().map(mangle_type_for_drop).collect();
            format!("{}${}", name, arg_strs.join("+"))
        }
        _ => "unknown".to_string(),
    }
}

/// Classify heap category for a type without needing FnCompiler.
fn classify_heap_type(
    ty: &Type,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
) -> HeapCategory {
    match ty {
        Type::String | Type::Fn(_, _) => HeapCategory::AlwaysHeap,
        Type::ADT(name, _) if name == "Vec" => HeapCategory::AlwaysHeap,
        Type::ADT(name, _) => {
            if let Some(tds) = type_defs {
                if let Some(td) = tds.get(name) {
                    let has_nullary = td.constructors.iter().any(|c| c.fields.is_empty());
                    let has_data = td.constructors.iter().any(|c| !c.fields.is_empty());
                    match (has_nullary, has_data) {
                        (true, true) => HeapCategory::Mixed,
                        (true, false) => HeapCategory::NeverHeap,
                        (false, true) => HeapCategory::AlwaysHeap,
                        (false, false) => HeapCategory::NeverHeap,
                    }
                } else {
                    HeapCategory::Mixed
                }
            } else {
                HeapCategory::Mixed
            }
        }
        _ => HeapCategory::NeverHeap,
    }
}

/// Resolve or generate a drop function for a type. Returns None if no drop needed.
fn resolve_drop_fn<M: Module>(
    ty: &Type,
    module: &mut M,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    free_func_id: FuncId,
    drop_fn_cache: &mut HashMap<String, FuncId>,
) -> Option<FuncId> {
    let (type_name, type_args) = match ty {
        Type::ADT(n, a) => (n.as_str(), a.as_slice()),
        _ => return None,
    };

    // Special case: Vec drop glue
    if type_name == "Vec" {
        return resolve_vec_drop_fn(
            ty,
            type_args,
            module,
            type_defs,
            free_func_id,
            drop_fn_cache,
        );
    }

    let tds = type_defs?;
    let td = tds.get(type_name)?;

    // Check if any constructor has heap-typed fields
    let has_heap_fields = td.constructors.iter().any(|ctor| {
        !ctor.fields.is_empty()
            && ctor.field_types.iter().any(|ft| {
                let concrete = substitute_type_params(ft, &td.type_params, type_args);
                concrete.is_heap_type()
            })
    });
    if !has_heap_fields {
        return None;
    }

    let mangled = format!("drop${}", mangle_type_for_drop(ty));
    if let Some(&fid) = drop_fn_cache.get(&mangled) {
        return Some(fid);
    }

    // Declare the drop function: (ptr: i64) -> i64
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let func_id = module
        .declare_anonymous_function(&sig)
        .expect("failed to declare drop function");

    // Cache before building body (for recursive types)
    drop_fn_cache.insert(mangled, func_id);

    // Collect constructor info with concrete field types
    let ctor_info: Vec<(usize, Vec<Type>)> = td
        .constructors
        .iter()
        .filter(|c| !c.fields.is_empty())
        .map(|ctor| {
            let concrete_fields: Vec<Type> = ctor
                .field_types
                .iter()
                .map(|ft| substitute_type_params(ft, &td.type_params, type_args))
                .collect();
            (ctor.tag, concrete_fields)
        })
        .collect();

    // Pre-generate drop fns for any ADT field types (recursive step)
    for (_, fields) in &ctor_info {
        for ft in fields {
            if let Type::ADT(..) = ft {
                resolve_drop_fn(ft, module, type_defs, free_func_id, drop_fn_cache);
            }
        }
    }

    // Build the drop function body
    {
        let mut drop_func = cranelift::codegen::ir::Function::with_name_signature(
            cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
            sig,
        );
        let mut drop_func_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut drop_func, &mut drop_func_ctx);

        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let ptr = builder.block_params(entry)[0];

        // For each data constructor: check tag, dec heap fields
        let free_block = builder.create_block();

        if ctor_info.len() == 1 {
            // Single data constructor: no tag check needed, just dec fields and free
            let (_, ref fields) = ctor_info[0];
            for (fi, ft) in fields.iter().enumerate() {
                if !ft.is_heap_type() {
                    continue;
                }
                let offset = ((fi + 1) * 8) as i32;
                let field_val = builder
                    .ins()
                    .load(types::I64, MemFlags::trusted(), ptr, offset);
                emit_dec_in_drop_fn(
                    &mut builder,
                    module,
                    field_val,
                    ft,
                    type_defs,
                    free_func_id,
                    drop_fn_cache,
                );
            }
            builder.ins().jump(free_block, &[]);
        } else {
            // Multiple constructors: load tag and branch
            let tag_val = builder.ins().load(types::I64, MemFlags::trusted(), ptr, 0);

            let mut next_blocks: Vec<cranelift::prelude::Block> = Vec::new();
            for _ in &ctor_info {
                next_blocks.push(builder.create_block());
            }

            // Jump to first check
            if next_blocks.is_empty() {
                builder.ins().jump(free_block, &[]);
            } else {
                builder.ins().jump(next_blocks[0], &[]);
            }

            for (ci, (tag, fields)) in ctor_info.iter().enumerate() {
                builder.switch_to_block(next_blocks[ci]);
                builder.seal_block(next_blocks[ci]);

                let expected_tag = builder.ins().iconst(types::I64, *tag as i64);
                let cmp = builder.ins().icmp(IntCC::Equal, tag_val, expected_tag);
                let body_block = builder.create_block();
                let fallthrough = if ci + 1 < next_blocks.len() {
                    next_blocks[ci + 1]
                } else {
                    free_block
                };
                builder.ins().brif(cmp, body_block, &[], fallthrough, &[]);

                builder.switch_to_block(body_block);
                builder.seal_block(body_block);

                for (fi, ft) in fields.iter().enumerate() {
                    if !ft.is_heap_type() {
                        continue;
                    }
                    let offset = ((fi + 1) * 8) as i32;
                    let field_val =
                        builder
                            .ins()
                            .load(types::I64, MemFlags::trusted(), ptr, offset);
                    emit_dec_in_drop_fn(
                        &mut builder,
                        module,
                        field_val,
                        ft,
                        type_defs,
                        free_func_id,
                        drop_fn_cache,
                    );
                }
                builder.ins().jump(free_block, &[]);
            }
        }

        // Free block: call cranelisp_free
        builder.switch_to_block(free_block);
        builder.seal_block(free_block);
        let free_ref = module.declare_func_in_func(free_func_id, builder.func);
        builder.ins().call(free_ref, &[ptr]);
        let zero = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[zero]);

        builder.seal_all_blocks();
        builder.finalize();

        let mut ctx = cranelift::codegen::Context::for_function(drop_func);
        module
            .define_function(func_id, &mut ctx)
            .expect("failed to define drop function");
    }

    Some(func_id)
}

/// Generate a drop function for Vec that loops over elements, dec'ing each, then frees.
/// Vec layout: [len: i64, cap: i64, data_ptr: i64]
/// Data buffer layout: [elem0, elem1, ...] (separate alloc_with_rc allocation)
fn resolve_vec_drop_fn<M: Module>(
    ty: &Type,
    type_args: &[Type],
    module: &mut M,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    free_func_id: FuncId,
    drop_fn_cache: &mut HashMap<String, FuncId>,
) -> Option<FuncId> {
    let mangled = format!("drop${}", mangle_type_for_drop(ty));
    if let Some(&fid) = drop_fn_cache.get(&mangled) {
        return Some(fid);
    }

    let elem_type = type_args.first()?;
    let elem_needs_dec = !matches!(
        classify_heap_type(elem_type, type_defs),
        HeapCategory::NeverHeap
    );

    // Declare the drop function: (ptr: i64) -> i64
    let mut sig = module.make_signature();
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    let func_id = module
        .declare_anonymous_function(&sig)
        .expect("failed to declare Vec drop function");

    // Cache before building body (for recursive types like Vec of Vec)
    drop_fn_cache.insert(mangled, func_id);

    // Pre-generate drop fn for element type if it's ADT
    if let Type::ADT(..) = elem_type {
        resolve_drop_fn(elem_type, module, type_defs, free_func_id, drop_fn_cache);
    }

    // Build the drop function body
    {
        let mut drop_func = cranelift::codegen::ir::Function::with_name_signature(
            cranelift::codegen::ir::UserFuncName::user(0, func_id.as_u32()),
            sig,
        );
        let mut drop_func_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut drop_func, &mut drop_func_ctx);

        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);

        // Create all blocks up front
        let free_header_block = builder.create_block();
        let free_data_block = builder.create_block();
        let loop_setup = if elem_needs_dec {
            Some(builder.create_block())
        } else {
            None
        };
        let loop_header = if elem_needs_dec {
            let blk = builder.create_block();
            builder.append_block_param(blk, types::I64); // counter
            Some(blk)
        } else {
            None
        };
        let loop_body = if elem_needs_dec {
            Some(builder.create_block())
        } else {
            None
        };

        builder.switch_to_block(entry);
        builder.seal_block(entry);

        let ptr = builder.block_params(entry)[0];

        // Load len and data_ptr
        let len = builder.ins().load(types::I64, MemFlags::trusted(), ptr, 0);
        let data_ptr = builder.ins().load(types::I64, MemFlags::trusted(), ptr, 16);

        // Check if data_ptr is null (empty vec)
        let zero = builder.ins().iconst(types::I64, 0);
        let is_null = builder.ins().icmp(IntCC::Equal, data_ptr, zero);

        let non_null_target = if elem_needs_dec {
            loop_setup.unwrap()
        } else {
            free_data_block
        };
        builder
            .ins()
            .brif(is_null, free_header_block, &[], non_null_target, &[]);

        if elem_needs_dec {
            let loop_setup_blk = loop_setup.unwrap();
            let loop_header_blk = loop_header.unwrap();
            let loop_body_blk = loop_body.unwrap();

            // loop_setup: jump to loop header with counter=0
            builder.switch_to_block(loop_setup_blk);
            builder.seal_block(loop_setup_blk);
            let start_counter = builder.ins().iconst(types::I64, 0);
            builder.ins().jump(
                loop_header_blk,
                &[cranelift::codegen::ir::BlockArg::Value(start_counter)],
            );

            // loop_header: check counter >= len
            builder.switch_to_block(loop_header_blk);
            let counter = builder.block_params(loop_header_blk)[0];
            let done = builder
                .ins()
                .icmp(IntCC::SignedGreaterThanOrEqual, counter, len);
            builder
                .ins()
                .brif(done, free_data_block, &[], loop_body_blk, &[]);

            // loop_body: load element, dec, increment counter
            builder.switch_to_block(loop_body_blk);
            builder.seal_block(loop_body_blk);

            let eight = builder.ins().iconst(types::I64, 8);
            let offset = builder.ins().imul(counter, eight);
            let elem_addr = builder.ins().iadd(data_ptr, offset);
            let elem_val = builder
                .ins()
                .load(types::I64, MemFlags::trusted(), elem_addr, 0);

            emit_dec_in_drop_fn(
                &mut builder,
                module,
                elem_val,
                elem_type,
                type_defs,
                free_func_id,
                drop_fn_cache,
            );

            let one = builder.ins().iconst(types::I64, 1);
            let next_counter = builder.ins().iadd(counter, one);
            builder.ins().jump(
                loop_header_blk,
                &[cranelift::codegen::ir::BlockArg::Value(next_counter)],
            );

            builder.seal_block(loop_header_blk);
        }

        // Free data buffer
        builder.switch_to_block(free_data_block);
        builder.seal_block(free_data_block);
        let free_ref_data = module.declare_func_in_func(free_func_id, builder.func);
        builder.ins().call(free_ref_data, &[data_ptr]);
        builder.ins().jump(free_header_block, &[]);

        // Free header
        builder.switch_to_block(free_header_block);
        builder.seal_block(free_header_block);
        let free_ref_header = module.declare_func_in_func(free_func_id, builder.func);
        builder.ins().call(free_ref_header, &[ptr]);
        let ret_zero = builder.ins().iconst(types::I64, 0);
        builder.ins().return_(&[ret_zero]);

        builder.seal_all_blocks();
        builder.finalize();

        let mut ctx = cranelift::codegen::Context::for_function(drop_func);
        module
            .define_function(func_id, &mut ctx)
            .expect("failed to define Vec drop function");
    }

    Some(func_id)
}

/// Emit dec logic for a field value inside a drop function body.
/// Uses raw FunctionBuilder (not FnCompiler) to avoid borrow conflicts.
fn emit_dec_in_drop_fn<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    val: Value,
    ty: &Type,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    free_func_id: FuncId,
    drop_fn_cache: &HashMap<String, FuncId>,
) {
    let category = classify_heap_type(ty, type_defs);
    match category {
        HeapCategory::NeverHeap => {}
        HeapCategory::AlwaysHeap => {
            emit_dec_inline_in_drop_fn(builder, module, val, ty, free_func_id, drop_fn_cache);
        }
        HeapCategory::Mixed => {
            let dec_block = builder.create_block();
            let skip_block = builder.create_block();
            let threshold = builder.ins().iconst(types::I64, 1024);
            let is_nullary = builder.ins().icmp(IntCC::UnsignedLessThan, val, threshold);
            builder
                .ins()
                .brif(is_nullary, skip_block, &[], dec_block, &[]);
            builder.switch_to_block(dec_block);
            builder.seal_block(dec_block);
            emit_dec_inline_in_drop_fn(builder, module, val, ty, free_func_id, drop_fn_cache);
            builder.ins().jump(skip_block, &[]);
            builder.switch_to_block(skip_block);
            builder.seal_block(skip_block);
        }
    }
}

/// Emit the actual rc dec + branch + free/drop logic inside a drop function.
fn emit_dec_inline_in_drop_fn<M: Module>(
    builder: &mut FunctionBuilder,
    module: &mut M,
    val: Value,
    ty: &Type,
    free_func_id: FuncId,
    drop_fn_cache: &HashMap<String, FuncId>,
) {
    let rc = builder.ins().load(types::I64, MemFlags::trusted(), val, -8);
    let one = builder.ins().iconst(types::I64, 1);
    let new_rc = builder.ins().isub(rc, one);

    let store_block = builder.create_block();
    let zero_block = builder.create_block();
    let cont_block = builder.create_block();

    let is_zero = builder.ins().icmp_imm(IntCC::Equal, new_rc, 0);
    builder
        .ins()
        .brif(is_zero, zero_block, &[], store_block, &[]);

    builder.switch_to_block(store_block);
    builder.seal_block(store_block);
    builder.ins().store(MemFlags::trusted(), new_rc, val, -8);
    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(zero_block);
    builder.seal_block(zero_block);
    // Look up drop function for ADT field types
    let drop_fid = if let Type::ADT(name, args) = ty {
        let mangled = format!(
            "drop${}",
            mangle_type_for_drop(&Type::ADT(name.clone(), args.clone()))
        );
        drop_fn_cache.get(&mangled).copied()
    } else {
        None
    };
    if let Some(dfid) = drop_fid {
        let drop_ref = module.declare_func_in_func(dfid, builder.func);
        builder.ins().call(drop_ref, &[val]);
    } else {
        let free_ref = module.declare_func_in_func(free_func_id, builder.func);
        builder.ins().call(free_ref, &[val]);
    }
    builder.ins().jump(cont_block, &[]);

    builder.switch_to_block(cont_block);
    builder.seal_block(cont_block);
}

/// Compile a single function definition into Cranelift IR (batch mode — direct calls).
#[allow(clippy::too_many_arguments)]
pub fn compile_function<M: Module>(
    defn: &Defn,
    program: &Program,
    extra_defns: &[Defn],
    func: &mut cranelift::codegen::ir::Function,
    func_ctx: &mut FunctionBuilderContext,
    module: &mut M,
    alloc_func_id: FuncId,
    free_func_id: FuncId,
    method_resolutions: &MethodResolutions,
    fn_specific_resolutions: Option<&MethodResolutions>,
    builtin_methods: &HashMap<String, FuncId>,
    modules: &HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    constructor_to_type: Option<&HashMap<String, String>>,
    panic_func_id: Option<FuncId>,
    expr_types: &HashMap<Span, Type>,
) -> Result<(), CranelispError> {
    let program_defns = crate::ast::defns(program);
    let impl_method_defns = crate::ast::impl_method_defns(program);
    let mut all_defns: Vec<&Defn> = program_defns;
    for d in &impl_method_defns {
        all_defns.push(d);
    }
    for d in extra_defns {
        all_defns.push(d);
    }
    let mut func_ids = HashMap::new();
    for def in &all_defns {
        let mut sig = module.make_signature();
        for _ in &def.params {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let fid = module
            .declare_function(&def.name, Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to lookup function '{}': {}", def.name, e),
                span: def.span,
            })?;
        func_ids.insert(def.name.clone(), fid);
    }

    // Build globals set from program function names + builtins + trait methods
    let mut globals: HashSet<String> = func_ids.keys().cloned().collect();
    // Add all names from synthetic modules (primitives, platform.stdio) so they aren't treated as captures
    for cm in modules.values() {
        for (name, entry) in &cm.symbols {
            if matches!(
                entry,
                crate::module::ModuleEntry::Def {
                    kind: crate::module::DefKind::Primitive { .. }
                        | crate::module::DefKind::SpecialForm { .. },
                    ..
                }
            ) {
                globals.insert(name.to_string());
            }
        }
    }
    // Add operator wrapper names from builtin_methods
    globals.extend(builtin_methods.keys().cloned());
    // Add trait method names (e.g., "show", "+", "doubled") so they aren't treated as captures
    for td in crate::ast::trait_decls(program) {
        for method in &td.methods {
            globals.insert(method.name.clone());
        }
    }
    // Add overloaded base names so they aren't treated as captures
    for (name, _, _) in crate::ast::defn_multis(program) {
        globals.insert(name.to_string());
    }
    // Add constructor names so they aren't treated as captures
    if let Some(c2t) = &constructor_to_type {
        globals.extend(c2t.keys().cloned());
    }
    // Add accessor names from type_defs
    if let Some(tds) = &type_defs {
        for td in tds.values() {
            for ctor in &td.constructors {
                for fname in &ctor.fields {
                    globals.insert(fname.clone());
                }
            }
        }
    }

    compile_body(
        defn,
        func,
        func_ctx,
        module,
        alloc_func_id,
        free_func_id,
        globals,
        CallMode::Direct { func_ids },
        method_resolutions,
        fn_specific_resolutions,
        builtin_methods,
        modules,
        type_defs,
        constructor_to_type,
        panic_func_id,
        expr_types,
    )
}

/// Compile a single function definition into Cranelift IR (REPL mode — indirect calls via fn_table).
#[allow(clippy::too_many_arguments)]
pub fn compile_function_indirect<M: Module>(
    defn: &Defn,
    func: &mut cranelift::codegen::ir::Function,
    func_ctx: &mut FunctionBuilderContext,
    module: &mut M,
    alloc_func_id: FuncId,
    free_func_id: FuncId,
    fn_slots: &HashMap<String, FnSlot>,
    method_resolutions: &MethodResolutions,
    fn_specific_resolutions: Option<&MethodResolutions>,
    builtin_methods: &HashMap<String, FuncId>,
    modules: &HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    trait_method_names: &HashSet<String>,
    type_defs: Option<&HashMap<String, TypeDefInfoCg>>,
    constructor_to_type: Option<&HashMap<String, String>>,
    panic_func_id: Option<FuncId>,
    expr_types: &HashMap<Span, Type>,
) -> Result<(), CranelispError> {
    // Build globals set from fn_slots + builtins + trait methods + primitives
    let mut globals: HashSet<String> = fn_slots.keys().cloned().collect();
    // Add all names from synthetic modules (primitives, platform.stdio) so they aren't treated as captures
    for cm in modules.values() {
        for (name, entry) in &cm.symbols {
            if matches!(
                entry,
                crate::module::ModuleEntry::Def {
                    kind: crate::module::DefKind::Primitive { .. }
                        | crate::module::DefKind::SpecialForm { .. },
                    ..
                }
            ) {
                globals.insert(name.to_string());
            }
        }
    }
    // Add operator wrapper names from builtin_methods
    globals.extend(builtin_methods.keys().cloned());
    globals.extend(trait_method_names.iter().cloned());
    // Add constructor names so they aren't treated as captures
    if let Some(c2t) = &constructor_to_type {
        globals.extend(c2t.keys().cloned());
    }
    // Add accessor names from type_defs
    if let Some(tds) = &type_defs {
        for td in tds.values() {
            for ctor in &td.constructors {
                for fname in &ctor.fields {
                    globals.insert(fname.clone());
                }
            }
        }
    }

    compile_body(
        defn,
        func,
        func_ctx,
        module,
        alloc_func_id,
        free_func_id,
        globals,
        CallMode::Indirect { fn_slots },
        method_resolutions,
        fn_specific_resolutions,
        builtin_methods,
        modules,
        type_defs,
        constructor_to_type,
        panic_func_id,
        expr_types,
    )
}

#[allow(clippy::too_many_arguments)]
fn compile_body<'a, M: Module>(
    defn: &Defn,
    func: &mut cranelift::codegen::ir::Function,
    func_ctx: &mut FunctionBuilderContext,
    module: &'a mut M,
    alloc_func_id: FuncId,
    free_func_id: FuncId,
    globals: HashSet<String>,
    call_mode: CallMode<'a>,
    method_resolutions: &'a MethodResolutions,
    fn_specific_resolutions: Option<&'a MethodResolutions>,
    builtin_methods: &'a HashMap<String, FuncId>,
    modules: &'a HashMap<crate::module::ModuleFullPath, crate::module::CompiledModule>,
    type_defs: Option<&'a HashMap<String, TypeDefInfoCg>>,
    constructor_to_type: Option<&'a HashMap<String, String>>,
    panic_func_id: Option<FuncId>,
    expr_types: &'a HashMap<Span, Type>,
) -> Result<(), CranelispError> {
    let mut builder = FunctionBuilder::new(func, func_ctx);
    let entry_block = builder.create_block();
    builder.append_block_params_for_function_params(entry_block);
    builder.switch_to_block(entry_block);
    builder.seal_block(entry_block);

    // Create loop header block for TCO: one i64 block param per function param
    let loop_header = builder.create_block();
    for _ in &defn.params {
        builder.append_block_param(loop_header, types::I64);
    }

    // Jump from entry to loop header with initial param values
    let entry_params: Vec<Value> = builder.block_params(entry_block).to_vec();
    let block_args: Vec<BlockArg> = entry_params.iter().map(|v| BlockArg::Value(*v)).collect();
    builder.ins().jump(loop_header, &block_args);

    // Switch to loop header — do NOT seal it yet (back-edges from tail calls will be added)
    builder.switch_to_block(loop_header);

    let mut compiler = FnCompiler {
        builder,
        module,
        variables: HashMap::new(),
        call_mode,
        alloc_func_id,
        globals,
        method_resolutions,
        fn_specific_resolutions,
        builtin_methods,
        modules,
        type_defs,
        constructor_to_type,
        panic_func_id,
        expr_types,
        free_func_id,
        variable_types: HashMap::new(),
        scope_stack: vec![vec![]],
        drop_fn_cache: HashMap::new(),
        current_fn_name: Some(defn.name.clone()),
        tail_loop_block: Some(loop_header),
        in_tail_position: true,
        fn_param_count: defn.params.len(),
    };

    // Bind function params from loop header block params (not entry block)
    for (i, param_name) in defn.params.iter().enumerate() {
        let val = compiler.builder.block_params(loop_header)[i];
        let var = compiler.fresh_var(types::I64);
        compiler.builder.def_var(var, val);
        compiler.variables.insert(param_name.clone(), var);
    }

    let result = compiler.compile_expr(&defn.body)?;

    // RC cleanup: pop function-level scope, skipping return value
    compiler.pop_scope_for_value(result);

    compiler.builder.ins().return_(&[result]);

    compiler.builder.seal_all_blocks();
    compiler.builder.finalize();

    Ok(())
}
