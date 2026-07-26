//! Compilation-local canonical type-drop-glue registry.

use std::collections::HashMap;

use cranelift::prelude::*;
use cranelift_codegen::ir::AtomicRmwOp;
use cranelift_module::{FuncId, Linkage, Module};
use dashmap::DashMap;

use cranelisp_types::{
    CodeStore, ConcreteType, CranelispError, DefKind, ErrorLocation, FQTypeName, LinkerStore,
    LinkerSymbol, ModuleEntry, ModuleFullPath, Span, SymbolTable, Type, TypeId,
    drop_glue_symbol_name, member_key,
};

use crate::heap::{self, HeapAdt, HeapCategory, HeapClosure};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DefinitionState {
    Declared,
    Defining,
    Defined,
}

#[derive(Debug, Clone)]
struct RegistryEntry {
    symbol: LinkerSymbol,
    func_id: FuncId,
    state: DefinitionState,
}

/// The compilation-local canonical registry — **module-borrow-free state**
/// (S118 slice S0, design §3.4 D1).
///
/// The registry holds no `&mut Module` and no `&DashMap`: both are supplied per
/// call. That is what lets a live [`crate::compiler::FnCompiler`] — which itself
/// holds `module: &'a mut M` — reach the registry through a *disjoint* field
/// borrow (`self.glue.request_if_owning(self.module, self.ctx.symbol_tables,
/// ty)`). Holding the module inside the registry made every consumer
/// unreachable, which is why the S116 foundation had zero of them.
///
/// Mid-body definition is safe: `define` builds each body in a fresh
/// `make_context()`, exactly as `lambda.rs::emit_capture_dec_glue` already does
/// while an enclosing `FunctionBuilder` is live.
pub(crate) struct DropGlueRegistry {
    module_path: ModuleFullPath,
    dealloc_id: FuncId,
    vec_drop_id: Option<FuncId>,
    entries: HashMap<ConcreteType, RegistryEntry>,
}

impl DropGlueRegistry {
    pub(crate) fn new(
        module_path: ModuleFullPath,
        dealloc_id: FuncId,
        vec_drop_id: Option<FuncId>,
    ) -> Self {
        Self {
            module_path,
            dealloc_id,
            vec_drop_id,
            entries: HashMap::new(),
        }
    }

    /// Request canonical glue for `ty`, or `None` when the type owns nothing
    /// heap (`NeverHeap`/`Value`). The single entry point for every release
    /// seam.
    pub(crate) fn request_if_owning<M, C, L>(
        &mut self,
        module: &mut M,
        symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        ty: ConcreteType,
    ) -> Result<Option<FuncId>, CranelispError>
    where
        M: Module,
        C: CodeStore,
        L: LinkerStore,
    {
        if matches!(
            HeapCategory::classify(&ty, Some(symbol_tables)),
            HeapCategory::NeverHeap | HeapCategory::Value
        ) {
            return Ok(None);
        }
        self.request(module, symbol_tables, ty).map(Some)
    }

    fn request<M, C, L>(
        &mut self,
        module: &mut M,
        symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        ty: ConcreteType,
    ) -> Result<FuncId, CranelispError>
    where
        M: Module,
        C: CodeStore,
        L: LinkerStore,
    {
        if let Some(entry) = self.entries.get(&ty) {
            return Ok(entry.func_id);
        }
        let symbol = drop_glue_symbol_name(&self.module_path, &ty);
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        let func_id = module
            .declare_function(symbol.as_ref(), Linkage::Export, &sig)
            .map_err(|e| self.error(format!("failed to declare drop glue '{symbol}': {e}")))?;
        self.entries.insert(
            ty.clone(),
            RegistryEntry {
                symbol,
                func_id,
                state: DefinitionState::Declared,
            },
        );
        self.define(module, symbol_tables, ty)?;
        Ok(func_id)
    }

    fn define<M, C, L>(
        &mut self,
        module: &mut M,
        symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        ty: ConcreteType,
    ) -> Result<(), CranelispError>
    where
        M: Module,
        C: CodeStore,
        L: LinkerStore,
    {
        let state = self.entries.get(&ty).expect("declared entry").state;
        if matches!(state, DefinitionState::Defining | DefinitionState::Defined) {
            return Ok(());
        }
        self.entries.get_mut(&ty).expect("declared entry").state = DefinitionState::Defining;

        // Resolve every child before borrowing a FunctionBuilder. Re-entry for
        // self/mutual recursion observes `Defining` and returns its declaration.
        let shape = self.shape(symbol_tables, &ty)?;
        let mut child_ids = HashMap::new();
        for child in shape.children() {
            if let Some(id) = self.request_if_owning(module, symbol_tables, child.clone())? {
                child_ids.insert(child, id);
            }
        }
        let vec_elem_callback = match &shape {
            GlueShape::Vec(elem) => child_ids
                .get(elem)
                .copied()
                .map(|id| self.define_vec_elem_adapter(module, elem, id))
                .transpose()?,
            _ => None,
        };

        let func_id = self.entries[&ty].func_id;
        let mut ctx = module.make_context();
        ctx.func.signature.params.push(AbiParam::new(types::I64));
        let mut fb_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let value = builder.block_params(entry)[0];

        match shape {
            GlueShape::Vec(_) => {
                let vec_drop = self.vec_drop_id.ok_or_else(|| {
                    self.error("runtime/vec_drop is required for Vec drop glue".into())
                })?;
                let child_ptr = if let Some(id) = vec_elem_callback {
                    let rf = module.declare_func_in_func(id, builder.func);
                    builder.ins().func_addr(types::I64, rf)
                } else {
                    builder.ins().iconst(types::I64, 0)
                };
                let rf = module.declare_func_in_func(vec_drop, builder.func);
                builder.ins().call(rf, &[value, child_ptr]);
            }
            other => self.emit_outer_drop(module, &mut builder, value, &other, &child_ids)?,
        }
        builder.ins().return_(&[]);
        builder.seal_all_blocks();
        builder.finalize();
        module
            .define_function(func_id, &mut ctx)
            .map_err(|e| self.error(format!("failed to define drop glue for '{ty:?}': {e}")))?;
        self.entries.get_mut(&ty).expect("declared entry").state = DefinitionState::Defined;
        Ok(())
    }

    /// Adapt canonical `(i64) -> ()` glue to the established Vec runtime
    /// callback ABI `(i64) -> i64`. The returned word is ignored by Vec; this
    /// adapter contains no release policy and delegates to the canonical body.
    fn define_vec_elem_adapter<M: Module>(
        &mut self,
        module: &mut M,
        elem: &ConcreteType,
        glue_id: FuncId,
    ) -> Result<FuncId, CranelispError> {
        let glue_symbol = drop_glue_symbol_name(&self.module_path, elem);
        let name = format!("{}__vec_elem_adapter", glue_symbol.as_ref());
        if let Some(cranelift_module::FuncOrDataId::Func(id)) = module.get_name(&name) {
            return Ok(id);
        }
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        let id = module
            .declare_function(&name, Linkage::Local, &sig)
            .map_err(|e| self.error(format!("failed to declare Vec glue adapter: {e}")))?;
        let mut ctx = module.make_context();
        ctx.func.signature = sig;
        let mut fb_ctx = FunctionBuilderContext::new();
        let mut builder = FunctionBuilder::new(&mut ctx.func, &mut fb_ctx);
        let entry = builder.create_block();
        builder.append_block_params_for_function_params(entry);
        builder.switch_to_block(entry);
        builder.seal_block(entry);
        let value = builder.block_params(entry)[0];
        let glue_ref = module.declare_func_in_func(glue_id, builder.func);
        builder.ins().call(glue_ref, &[value]);
        builder.ins().return_(&[value]);
        builder.finalize();
        module
            .define_function(id, &mut ctx)
            .map_err(|e| self.error(format!("failed to define Vec glue adapter: {e}")))?;
        Ok(id)
    }

    fn emit_outer_drop<M: Module>(
        &mut self,
        module: &mut M,
        builder: &mut FunctionBuilder,
        value: Value,
        shape: &GlueShape,
        child_ids: &HashMap<ConcreteType, FuncId>,
    ) -> Result<(), CranelispError> {
        let done = builder.create_block();
        if shape.guard_nullary() {
            let threshold = builder
                .ins()
                .iconst(types::I64, heap::NULLARY_THRESHOLD_I64);
            let is_tag = builder
                .ins()
                .icmp(IntCC::UnsignedLessThan, value, threshold);
            let dec = builder.create_block();
            builder.ins().brif(is_tag, done, &[], dec, &[]);
            builder.switch_to_block(dec);
            builder.seal_block(dec);
        }
        heap::emit_rc_dec_check_gated(builder, module, value);
        heap::emit_rc_stat_call_gated(builder, module, "runtime/rc_stat_dec");
        let rc_addr = builder
            .ins()
            .iadd_imm(value, i64::from(cranelisp_types::HeapHeader::RC_OFFSET));
        let one = builder.ins().iconst(types::I64, 1);
        let old = builder.ins().atomic_rmw(
            types::I64,
            MemFlags::trusted(),
            AtomicRmwOp::Sub,
            rc_addr,
            one,
        );
        let final_ref = builder.ins().icmp(IntCC::Equal, old, one);
        let free = builder.create_block();
        builder.ins().brif(final_ref, free, &[], done, &[]);
        builder.switch_to_block(free);
        builder.seal_block(free);
        builder.ins().fence();

        match shape {
            GlueShape::String => {}
            GlueShape::Closure => {
                let ptr = heap::heap_load(builder, value, HeapClosure::DROP_GLUE_PTR_OFFSET);
                let zero = builder.ins().iconst(types::I64, 0);
                let has = builder.ins().icmp(IntCC::NotEqual, ptr, zero);
                let call = builder.create_block();
                let after = builder.create_block();
                builder.ins().brif(has, call, &[], after, &[]);
                builder.switch_to_block(call);
                builder.seal_block(call);
                let mut sig = Signature::new(module.isa().default_call_conv());
                sig.params.push(AbiParam::new(types::I64));
                let sr = builder.import_signature(sig);
                builder.ins().call_indirect(sr, ptr, &[value]);
                builder.ins().jump(after, &[]);
                builder.switch_to_block(after);
                builder.seal_block(after);
            }
            GlueShape::Adt(ctors) => {
                self.emit_adt_fields(module, builder, value, ctors, child_ids)?
            }
            GlueShape::Vec(_) => unreachable!(),
        }
        let dealloc = module.declare_func_in_func(self.dealloc_id, builder.func);
        builder.ins().call(dealloc, &[value]);
        builder.ins().jump(done, &[]);
        builder.switch_to_block(done);
        builder.seal_block(done);
        Ok(())
    }

    fn emit_adt_fields<M: Module>(
        &mut self,
        module: &mut M,
        builder: &mut FunctionBuilder,
        value: Value,
        ctors: &[CtorShape],
        child_ids: &HashMap<ConcreteType, FuncId>,
    ) -> Result<(), CranelispError> {
        let data: Vec<_> = ctors.iter().filter(|c| !c.fields.is_empty()).collect();
        if data.is_empty() {
            return Ok(());
        }
        let done = builder.create_block();
        let tag = heap::heap_load(builder, value, HeapAdt::TAG_OFFSET);
        for (i, ctor) in data.iter().enumerate() {
            let arm = builder.create_block();
            let next = if i + 1 == data.len() {
                done
            } else {
                builder.create_block()
            };
            let expected = builder.ins().iconst(types::I64, ctor.tag as i64);
            let matches = builder.ins().icmp(IntCC::Equal, tag, expected);
            builder.ins().brif(matches, arm, &[], next, &[]);
            builder.switch_to_block(arm);
            builder.seal_block(arm);
            for (field_index, field_ty) in ctor.fields.iter().enumerate() {
                if let Some(id) = child_ids.get(field_ty) {
                    let field = heap::heap_load(builder, value, HeapAdt::field_offset(field_index));
                    let rf = module.declare_func_in_func(*id, builder.func);
                    builder.ins().call(rf, &[field]);
                }
            }
            builder.ins().jump(done, &[]);
            if i + 1 != data.len() {
                builder.switch_to_block(next);
                builder.seal_block(next);
            }
        }
        builder.switch_to_block(done);
        builder.seal_block(done);
        Ok(())
    }

    fn shape<C, L>(
        &self,
        symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        ty: &ConcreteType,
    ) -> Result<GlueShape, CranelispError>
    where
        C: CodeStore,
        L: LinkerStore,
    {
        match ty {
            ConcreteType::String => Ok(GlueShape::String),
            ConcreteType::Fn(..) => Ok(GlueShape::Closure),
            ConcreteType::ADT(name, args) if is_vec(name) => Ok(GlueShape::Vec(
                args.first().cloned().unwrap_or(ConcreteType::Int),
            )),
            ConcreteType::ADT(name, args) => Ok(GlueShape::Adt(self.ctor_shapes(
                symbol_tables,
                name,
                args,
            )?)),
            ConcreteType::Int | ConcreteType::Bool | ConcreteType::Float => Err(self.error(
                format!("non-owning type requested from drop-glue registry: {ty:?}"),
            )),
        }
    }

    fn ctor_shapes<C, L>(
        &self,
        symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
        name: &FQTypeName,
        args: &[ConcreteType],
    ) -> Result<Vec<CtorShape>, CranelispError>
    where
        C: CodeStore,
        L: LinkerStore,
    {
        let table = symbol_tables
            .get(&name.module)
            .ok_or_else(|| self.error(format!("missing module '{}' for drop glue", name.module)))?;
        let info = match table.get(name.name.as_ref()) {
            Some(ModuleEntry::TypeDef { info, .. }) => info.clone(),
            Some(ModuleEntry::Def { kind, .. }) => match &**kind {
                DefKind::Constructor {
                    type_def: Some(info),
                    ..
                } => (**info).clone(),
                _ => {
                    return Err(
                        self.error(format!("missing type definition '{name}' for drop glue"))
                    );
                }
            },
            _ => return Err(self.error(format!("missing type definition '{name}' for drop glue"))),
        };
        if info.type_params.len() != args.len() {
            return Err(self.error(format!(
                "drop glue for '{name}' received {} concrete arguments for {} declared parameters",
                args.len(),
                info.type_params.len()
            )));
        }
        let mut subst: Option<HashMap<TypeId, ConcreteType>> = None;
        let mut raw = Vec::new();
        for ctor_name in &info.constructors {
            let key = member_key(&info.name.name, ctor_name.as_ref());
            let entry = table
                .get(key.as_ref())
                .or_else(|| table.get(ctor_name.as_ref()))
                .ok_or_else(|| {
                    self.error(format!("missing constructor '{ctor_name}' of '{name}'"))
                })?;
            let ModuleEntry::Def { kind, scheme, .. } = entry else {
                return Err(self.error(format!("constructor '{ctor_name}' is not a definition")));
            };
            let DefKind::Constructor {
                tag, field_count, ..
            } = &**kind
            else {
                return Err(self.error(format!("'{ctor_name}' is not a constructor")));
            };
            let (fields, result_ty) = match &scheme.ty {
                Type::Fn(params, result) => {
                    let fields = params.get(..*field_count).ok_or_else(|| {
                        self.error(format!(
                            "constructor '{ctor_name}' declares {field_count} fields but its scheme has {} parameters",
                            params.len()
                        ))
                    })?;
                    (fields.to_vec(), result.as_ref())
                }
                result => (vec![], result),
            };
            let Type::ADT(result_name, declared_args) = result_ty else {
                return Err(self.error(format!(
                    "constructor '{ctor_name}' has non-ADT result type in drop glue"
                )));
            };
            if result_name != name || declared_args.len() != info.type_params.len() {
                return Err(self.error(format!(
                    "constructor '{ctor_name}' result does not preserve declared parameter order for '{name}'"
                )));
            }
            let ctor_subst = declared_args
                .iter()
                .zip(args.iter().cloned())
                .map(|(declared, concrete)| match declared {
                    Type::Var(id) => Ok((*id, concrete)),
                    _ => Err(self.error(format!(
                        "constructor '{ctor_name}' result parameter is not a declared type variable"
                    ))),
                })
                .collect::<Result<HashMap<_, _>, _>>()?;
            if let Some(existing) = &subst {
                if existing != &ctor_subst {
                    return Err(self.error(format!(
                        "constructor '{ctor_name}' disagrees on declared parameter identity for '{name}'"
                    )));
                }
            } else {
                subst = Some(ctor_subst);
            }
            raw.push((*tag, fields));
        }
        let subst = subst.unwrap_or_default();
        raw.into_iter()
            .map(|(tag, fields)| {
                fields
                    .into_iter()
                    .map(|f| substitute(&f, &subst))
                    .collect::<Result<Vec<_>, _>>()
                    .map(|fields| CtorShape { tag, fields })
            })
            .collect()
    }

    pub(crate) fn finish(
        self,
    ) -> Result<HashMap<ConcreteType, (LinkerSymbol, FuncId)>, CranelispError> {
        if let Some((ty, _)) = self
            .entries
            .iter()
            .find(|(_, e)| e.state != DefinitionState::Defined)
        {
            return Err(self.error(format!(
                "drop glue for '{ty:?}' did not reach Defined state"
            )));
        }
        Ok(self
            .entries
            .into_iter()
            .map(|(ty, e)| (ty, (e.symbol, e.func_id)))
            .collect())
    }

    fn error(&self, message: String) -> CranelispError {
        CranelispError::CodegenError {
            message,
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }
    }
}

#[derive(Debug, Clone)]
enum GlueShape {
    String,
    Closure,
    Vec(ConcreteType),
    Adt(Vec<CtorShape>),
}
impl GlueShape {
    fn guard_nullary(&self) -> bool {
        matches!(self, Self::Adt(ctors) if ctors.iter().any(|c| c.fields.is_empty()))
    }
    fn children(&self) -> Vec<ConcreteType> {
        match self {
            Self::Vec(t) => vec![t.clone()],
            Self::Adt(cs) => cs.iter().flat_map(|c| c.fields.clone()).collect(),
            _ => vec![],
        }
    }
}
#[derive(Debug, Clone)]
struct CtorShape {
    tag: usize,
    fields: Vec<ConcreteType>,
}

fn is_vec(name: &FQTypeName) -> bool {
    name.module.as_ref() == "primitives" && name.name.as_ref() == "Vec"
}
fn substitute(
    ty: &Type,
    subst: &HashMap<TypeId, ConcreteType>,
) -> Result<ConcreteType, CranelispError> {
    match ty {
        Type::Var(id) => subst
            .get(id)
            .cloned()
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("unresolved field substitution t{id} in drop glue"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }),
        Type::TyConApp(id, _) => Err(CranelispError::CodegenError {
            message: format!("unresolved type-constructor t{id} in drop glue"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        }),
        Type::Int => Ok(ConcreteType::Int),
        Type::Bool => Ok(ConcreteType::Bool),
        Type::String => Ok(ConcreteType::String),
        Type::Float => Ok(ConcreteType::Float),
        Type::Fn(ps, r) => Ok(ConcreteType::Fn(
            ps.iter()
                .map(|p| substitute(p, subst))
                .collect::<Result<_, _>>()?,
            Box::new(substitute(r, subst)?),
        )),
        Type::ADT(n, as_) => Ok(ConcreteType::ADT(
            n.clone(),
            as_.iter()
                .map(|a| substitute(a, subst))
                .collect::<Result<_, _>>()?,
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CodeFinalizer;
    use cranelift_module::{Module, default_libcall_names};
    use cranelift_object::{ObjectBuilder, ObjectModule};
    use cranelisp_types::{
        FQTypeName, ModuleEntry, Scheme, Symbol, TypeDefInfo, TypeName, Visibility,
    };

    fn adt(module: &str, name: &str, args: Vec<ConcreteType>) -> ConcreteType {
        ConcreteType::ADT(
            FQTypeName::new(ModuleFullPath::from(module), TypeName::from(name)),
            args,
        )
    }

    fn object_module() -> ObjectModule {
        let isa = crate::cache::object::build_isa(true).unwrap();
        ObjectModule::new(
            ObjectBuilder::new(isa, "drop_glue_test", default_libcall_names()).unwrap(),
        )
    }

    fn declare_dealloc(module: &mut ObjectModule) -> FuncId {
        let mut sig = module.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        module
            .declare_function("runtime/dealloc", Linkage::Import, &sig)
            .unwrap()
    }

    fn insert_type(
        table: &mut SymbolTable,
        module: &ModuleFullPath,
        name: &str,
        type_params: &[&str],
        ctors: Vec<(&str, usize, Vec<Type>, Vec<Type>)>,
    ) -> FQTypeName {
        let fq = FQTypeName::new(module.clone(), TypeName::from(name));
        table.insert(
            Symbol::from(name),
            ModuleEntry::TypeDef {
                info: TypeDefInfo {
                    name: fq.clone(),
                    type_params: type_params.iter().map(|p| Symbol::from(*p)).collect(),
                    constructors: ctors.iter().map(|(n, ..)| Symbol::from(*n)).collect(),
                },
                visibility: Visibility::Public,
                docstring: None,
            },
        );
        for (ctor_name, tag, fields, result_args) in ctors {
            let result = Type::ADT(fq.clone(), result_args);
            let scheme_ty = if fields.is_empty() {
                result
            } else {
                Type::Fn(fields.clone(), Box::new(result))
            };
            table.insert(
                Symbol::from(ctor_name),
                ModuleEntry::Def {
                    scheme: Scheme {
                        type_vars: vec![],
                        constraints: HashMap::new(),
                        ty: scheme_ty,
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: (0..fields.len())
                        .map(|i| Symbol::from(format!("f{i}")))
                        .collect(),
                    kind: Box::new(DefKind::Constructor {
                        got_slot: 0,
                        type_name: fq.clone(),
                        tag,
                        field_count: fields.len(),
                        internal: false,
                        type_def: None,
                        mode_summary: None,
                    }),
                    callees: vec![],
                    trait_origin: None,
                    seq: 0,
                    ast: None,
                    codegen_view: None,
                    code: None,
                    value_use: false,
                },
            );
        }
        fq
    }

    // spec: appendix-c-nfr §C.1.4 — per-type drop glue recursively releases
    // heap-typed fields, including recursive type graphs.
    #[test]
    fn registry_defines_self_recursive_mutual_and_unbounded_depth_graph() {
        let module_path = ModuleFullPath::from("user");
        let tables = DashMap::new();
        let mut table = SymbolTable::new(module_path.clone());

        let list_name = FQTypeName::new(module_path.clone(), TypeName::from("List"));
        insert_type(
            &mut table,
            &module_path,
            "List",
            &[],
            vec![
                ("Nil", 0, vec![], vec![]),
                (
                    "Cons",
                    1,
                    vec![Type::String, Type::ADT(list_name.clone(), vec![])],
                    vec![],
                ),
            ],
        );
        let a_name = FQTypeName::new(module_path.clone(), TypeName::from("A"));
        let b_name = FQTypeName::new(module_path.clone(), TypeName::from("B"));
        insert_type(
            &mut table,
            &module_path,
            "A",
            &[],
            vec![("MkA", 0, vec![Type::ADT(b_name.clone(), vec![])], vec![])],
        );
        insert_type(
            &mut table,
            &module_path,
            "B",
            &[],
            vec![("MkB", 0, vec![Type::ADT(a_name.clone(), vec![])], vec![])],
        );

        let mut prior = ConcreteType::String;
        for depth in 1..=6 {
            let name = format!("D{depth}");
            let fq = FQTypeName::new(module_path.clone(), TypeName::from(name.clone()));
            insert_type(
                &mut table,
                &module_path,
                &name,
                &[],
                vec![(
                    Box::leak(format!("MkD{depth}").into_boxed_str()),
                    0,
                    vec![prior.to_type()],
                    vec![],
                )],
            );
            prior = ConcreteType::ADT(fq, vec![]);
        }
        tables.insert(module_path.clone(), table);

        let mut module = object_module();
        let dealloc = declare_dealloc(&mut module);
        let mut registry = DropGlueRegistry::new(module_path.clone(), dealloc, None);
        for root in [
            ConcreteType::ADT(list_name, vec![]),
            ConcreteType::ADT(a_name, vec![]),
            prior.clone(),
        ] {
            registry
                .request_if_owning(&mut module, &tables, root)
                .unwrap();
        }
        let ids = registry.finish().unwrap();
        assert!(ids.contains_key(&prior), "depth >5 root must be defined");
        assert!(
            ids.keys()
                .any(|t| matches!(t, ConcreteType::ADT(n, _) if n.name.as_ref() == "List"))
        );
        assert!(
            ids.keys()
                .any(|t| matches!(t, ConcreteType::ADT(n, _) if n.name.as_ref() == "A"))
        );
        assert!(
            ids.keys()
                .any(|t| matches!(t, ConcreteType::ADT(n, _) if n.name.as_ref() == "B"))
        );
        module.finalize_for_code_read().unwrap();
        let artifacts = crate::project_drop_glues(&module, ids);
        assert!(artifacts.values().all(|a| a.jit_address.is_none()));
        for (ty, artifact) in &artifacts {
            assert_eq!(artifact.symbol, drop_glue_symbol_name(&module_path, ty));
        }
        let bytes = module.finish().emit().unwrap();
        let object = object::File::parse(&*bytes).unwrap();
        use object::{Object, ObjectSymbol};
        for artifact in artifacts.values() {
            assert!(
                object
                    .symbols()
                    .any(|s| s.name().ok() == Some(artifact.symbol.as_ref()))
            );
        }
    }

    // spec: appendix-c-nfr §C.1.4 — drop glue depends on the concrete type's
    // declared field layout.
    #[test]
    fn substitution_uses_declared_result_order_and_preserves_phantom_parameter() {
        let module_path = ModuleFullPath::from("user");
        let tables = DashMap::new();
        let mut table = SymbolTable::new(module_path.clone());
        let fq = insert_type(
            &mut table,
            &module_path,
            "Pair",
            &["a", "b"],
            vec![(
                "PairCtor",
                0,
                vec![Type::Var(9)],
                vec![Type::Var(3), Type::Var(9)],
            )],
        );
        tables.insert(module_path.clone(), table);
        let mut module = object_module();
        let dealloc = declare_dealloc(&mut module);
        let registry = DropGlueRegistry::new(module_path, dealloc, None);
        let shapes = registry
            .ctor_shapes(&tables, &fq, &[ConcreteType::Int, ConcreteType::String])
            .unwrap();
        assert_eq!(shapes[0].fields, vec![ConcreteType::String]);
    }

    // spec: appendix-c-nfr §C.1.4 — generated per-type drop glue is callable
    // at each concrete deallocation site.
    #[test]
    fn jit_projection_contains_finalized_address() {
        let module_path = ModuleFullPath::from("user");
        let tables = DashMap::new();
        tables.insert(module_path.clone(), SymbolTable::new(module_path.clone()));
        let mut jit = crate::jit::Jit::new_with_symbols(&[]).unwrap();
        let module = jit.jit_module();
        let mut dealloc_sig = module.make_signature();
        dealloc_sig.params.push(AbiParam::new(types::I64));
        let dealloc = module
            .declare_function("runtime/dealloc", Linkage::Import, &dealloc_sig)
            .unwrap();
        let mut registry = DropGlueRegistry::new(module_path.clone(), dealloc, None);
        registry
            .request_if_owning(module, &tables, ConcreteType::String)
            .unwrap();
        let ids = registry.finish().unwrap();
        module.finalize_for_code_read().unwrap();
        let artifacts = crate::project_drop_glues(module, ids);
        let artifact = artifacts.get(&ConcreteType::String).unwrap();
        assert!(artifact.jit_address.is_some());
        assert_eq!(
            artifact.symbol,
            drop_glue_symbol_name(&module_path, &ConcreteType::String)
        );
    }

    // spec: appendix-c-nfr §C.1.4 — recursive heap fields are released by
    // per-type recursive glue, not a fixed-depth expansion.
    #[test]
    fn recursive_shape_keeps_a_finite_type_key() {
        let list = adt("user", "List", vec![ConcreteType::String]);
        let shape = GlueShape::Adt(vec![
            CtorShape {
                tag: 0,
                fields: vec![],
            },
            CtorShape {
                tag: 1,
                fields: vec![ConcreteType::String, list.clone()],
            },
        ]);
        assert_eq!(
            shape.children(),
            vec![ConcreteType::String, list],
            "a recursive edge is one registry request, not compiler-depth expansion"
        );
    }

    // spec: appendix-c-nfr §C.1.4 — one concrete field type identifies one
    // per-type drop-glue dependency even when repeated.
    #[test]
    fn repeated_field_type_has_one_registry_identity() {
        let child = adt("user", "Child", vec![]);
        let shape = GlueShape::Adt(vec![CtorShape {
            tag: 0,
            fields: vec![child.clone(), child.clone()],
        }]);
        let unique: std::collections::HashSet<_> = shape.children().into_iter().collect();
        assert_eq!(unique, std::collections::HashSet::from([child]));
    }

    // spec: appendix-c-nfr §C.1.4 — per-type glue requires a concrete field
    // layout; unresolved field parameters cannot be emitted.
    #[test]
    fn substitution_rejects_an_unbound_recursive_parameter() {
        let err = substitute(&Type::Var(7), &HashMap::new()).unwrap_err();
        assert!(err.to_string().contains("unresolved field substitution t7"));
    }

    // spec: appendix-c-nfr §C.1.4 — one named drop function per concrete owning
    // type: a repeated request returns the SAME declaration, and two distinct
    // callers requesting the same type share one body (design §3.4 D5 — request
    // eagerness makes emission ORDER input-dependent, so identity must be the
    // type and nothing else).
    #[test]
    fn repeated_request_is_idempotent_and_two_callers_share_one_body() {
        let module_path = ModuleFullPath::from("user");
        let tables = DashMap::new();
        let mut table = SymbolTable::new(module_path.clone());
        let boxed = insert_type(
            &mut table,
            &module_path,
            "Boxed",
            &[],
            vec![("MkBoxed", 0, vec![Type::String], vec![])],
        );
        tables.insert(module_path.clone(), table);

        let mut module = object_module();
        let dealloc = declare_dealloc(&mut module);
        let mut registry = DropGlueRegistry::new(module_path.clone(), dealloc, None);
        let ty = ConcreteType::ADT(boxed, vec![]);

        let first = registry
            .request_if_owning(&mut module, &tables, ty.clone())
            .unwrap()
            .expect("owning type must get glue");
        // A second, independent request — the "second caller" — must NOT declare
        // or define a second body.
        let second = registry
            .request_if_owning(&mut module, &tables, ty.clone())
            .unwrap()
            .expect("owning type must get glue");
        assert_eq!(first, second, "one concrete type ⇒ one glue FuncId");
        // The child (`String`) was requested transitively exactly once too.
        let third = registry
            .request_if_owning(&mut module, &tables, ConcreteType::String)
            .unwrap()
            .expect("String is owning");
        let ids = registry.finish().unwrap();
        assert_eq!(
            ids.len(),
            2,
            "exactly Boxed + String, no duplicates: {ids:?}"
        );
        assert_eq!(ids[&ConcreteType::String].1, third);
        assert_eq!(ids[&ty].1, first);
    }

    // spec: appendix-c-nfr §C.1.4 — glue behaviour is ORDER-INDEPENDENT (design
    // §3.4 D5). After migration the first request for a type happens mid-body of
    // whichever function reaches it first, so permuting the request order must
    // produce the same key set and the same symbols.
    #[test]
    fn permuted_request_order_yields_the_same_keys_and_symbols() {
        fn run(order: &[usize]) -> Vec<(ConcreteType, LinkerSymbol)> {
            let module_path = ModuleFullPath::from("user");
            let tables = DashMap::new();
            let mut table = SymbolTable::new(module_path.clone());
            let boxed = insert_type(
                &mut table,
                &module_path,
                "Boxed",
                &[],
                vec![("MkBoxed", 0, vec![Type::String], vec![])],
            );
            let pairish = insert_type(
                &mut table,
                &module_path,
                "Wrap",
                &[],
                vec![("MkWrap", 0, vec![Type::ADT(boxed.clone(), vec![])], vec![])],
            );
            tables.insert(module_path.clone(), table);
            let roots = [
                ConcreteType::String,
                ConcreteType::ADT(boxed, vec![]),
                ConcreteType::ADT(pairish, vec![]),
            ];
            let mut module = object_module();
            let dealloc = declare_dealloc(&mut module);
            let mut registry = DropGlueRegistry::new(module_path, dealloc, None);
            for i in order {
                registry
                    .request_if_owning(&mut module, &tables, roots[*i].clone())
                    .unwrap();
            }
            let mut out: Vec<(ConcreteType, LinkerSymbol)> = registry
                .finish()
                .unwrap()
                .into_iter()
                .map(|(ty, (sym, _))| (ty, sym))
                .collect();
            out.sort_by(|a, b| a.1.as_ref().cmp(b.1.as_ref()));
            out
        }
        assert_eq!(run(&[0, 1, 2]), run(&[2, 1, 0]));
        assert_eq!(run(&[0, 1, 2]), run(&[2, 0, 1]));
    }

    // spec: appendix-c-nfr §C.1.4 (NEGATIVE) — the completeness fence. An entry
    // left `Defining` at `finish()` means a body was never emitted for a type a
    // release site can call; that is a hard compilation error, never a silently
    // missing symbol. S0 moved WHERE `finish()` runs (after body compilation);
    // this pins that WHAT it checks is unchanged.
    #[test]
    fn finish_rejects_an_entry_that_never_reached_defined_neg() {
        let module_path = ModuleFullPath::from("user");
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        tables.insert(module_path.clone(), SymbolTable::new(module_path.clone()));
        let mut module = object_module();
        let dealloc = declare_dealloc(&mut module);
        let mut registry = DropGlueRegistry::new(module_path.clone(), dealloc, None);
        registry
            .request_if_owning(&mut module, &tables, ConcreteType::String)
            .unwrap();
        // Force the state back to `Defining`, the shape a re-entrant definition
        // failure would leave behind.
        registry
            .entries
            .get_mut(&ConcreteType::String)
            .unwrap()
            .state = DefinitionState::Defining;
        let err = registry.finish().unwrap_err();
        assert!(
            err.to_string().contains("did not reach Defined state"),
            "{err}"
        );
    }

    // spec: appendix-c-nfr §C.1.4 (NEGATIVE) — a non-concrete/non-owning key is
    // rejected at the registry boundary, never served a shallow release (D2).
    #[test]
    fn a_non_owning_scalar_key_is_rejected_by_shape_neg() {
        let module_path = ModuleFullPath::from("user");
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        tables.insert(module_path.clone(), SymbolTable::new(module_path.clone()));
        let registry = DropGlueRegistry::new(
            module_path,
            {
                let mut module = object_module();
                declare_dealloc(&mut module)
            },
            None,
        );
        let err = registry.shape(&tables, &ConcreteType::Int).unwrap_err();
        assert!(
            err.to_string().contains("non-owning type requested"),
            "{err}"
        );
    }

    // spec: appendix-c-nfr §C.1.4 — recursive decrementing is required for
    // arbitrary concrete field graphs, with no fixed nesting limit.
    #[test]
    fn no_fixed_depth_cutoff_exists_in_canonical_registry() {
        let source = include_str!("drop_glue.rs");
        assert!(!source.contains(concat!("MAX_DROP_", "GLUE_DEPTH")));
        assert!(!source.contains(concat!("drop_glue_", "depth")));
    }
}
