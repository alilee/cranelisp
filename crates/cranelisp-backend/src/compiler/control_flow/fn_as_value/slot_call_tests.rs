//! A function value's wrapper calls its target through the target's GOT slot,
//! whether the target is in the unit being compiled or in another module
//! (design/backend/compile-to-module.md §12.2).
//!
//! The JIT cases compile through `compile_to_module`, then repoint the
//! target's slot at another body. A wrapper that loads the slot follows the
//! repoint; a wrapper that calls the target's code directly does not.
//!
//! The object cases read the relocations `compile_to_module` leaves in an
//! object: a direct call leaves a call relocation against the callee's
//! symbol, a call through a slot leaves none. A planted direct call proves the
//! scan detects.

use crate::test_support::*;

fn int_fn() -> Type {
    Type::Fn(vec![Type::Int], Box::new(Type::Int))
}

/// `(defn name [n] result)`, returning `n` itself when `result` is `None`.
fn unary_defn(name: &str, result: Option<i64>, base: u32) -> Defn {
    let body = match result {
        Some(value) => Expr::IntLit {
            value,
            span: Span::new(base + 5, base + 8),
            inferred_type: Some(Box::new(Type::Int)),
        },
        None => Expr::Var {
            name: Symbol::from("n"),
            span: Span::new(base + 5, base + 6),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        },
    };
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("n"), None)],
            body,
            span: Span::new(base, base + 10),
        }],
        visibility: Visibility::Public,
        span: Span::new(base, base + 10),
    }
}

/// `(defn takes [] (let [f target] (f 1)))`, with the value use of `target`
/// carried to `target_fq`.
fn value_consumer(target_fq: &FQSymbol) -> (Defn, HashMap<Span, FQSymbol>) {
    let value_span = Span::new(110, 112);
    let body = Expr::Let {
        bindings: vec![(
            Symbol::from("f"),
            Expr::Var {
                name: target_fq.symbol.clone(),
                span: value_span,
                resolved_call: None,
                inferred_type: Some(Box::new(int_fn())),
            },
        )],
        body: Box::new(Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("f"),
                span: Span::new(120, 121),
                resolved_call: None,
                inferred_type: Some(Box::new(int_fn())),
            }),
            args: vec![Expr::IntLit {
                value: 1,
                span: Span::new(122, 123),
                inferred_type: Some(Box::new(Type::Int)),
            }],
            span: Span::new(119, 124),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        span: Span::new(100, 125),
        inferred_type: Some(Box::new(Type::Int)),
    };
    let defn = Defn {
        name: Symbol::from("takes"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::new(100, 125),
        }],
        visibility: Visibility::Public,
        span: Span::new(100, 125),
    };
    (defn, HashMap::from([(value_span, target_fq.clone())]))
}

/// Install `af` (identity) and `bf` (constant 101) in `target_module`, and the
/// consumer of `af` as a value in `user`. Compile, repoint `af`'s slot at
/// `bf`'s code, and return what the consumer computes.
fn run_after_repointing_target_slot(target_module: &str) -> i64 {
    let user = ModuleFullPath::from("user");
    let home = ModuleFullPath::from(target_module);
    let af_fq = FQSymbol {
        module: home.clone(),
        symbol: Symbol::from("af"),
    };
    let af = unary_defn("af", None, 0);
    let bf = unary_defn("bf", Some(101), 20);
    let (takes, carriers) = value_consumer(&af_fq);

    let tables = empty_tables();
    let (af_slot, bf_slot) = {
        let mut st = SymbolTable::new(home.clone());
        let af_slot = install_def_entry(&mut st, af.clone());
        let bf_slot = install_def_entry(&mut st, bf.clone());
        if home == user {
            install_def_entry_with_targets(&mut st, takes.clone(), &carriers);
        }
        tables.insert(home.clone(), st);
        (af_slot, bf_slot)
    };
    if home != user {
        let mut st = SymbolTable::new(user.clone());
        install_def_entry_with_targets(&mut st, takes.clone(), &carriers);
        tables.insert(user.clone(), st);
    }

    let mut jit = Jit::new(&tables).expect("jit init");
    if home == user {
        compile_names_to_module(
            user.clone(),
            &[af.name.clone(), bf.name.clone(), takes.name.clone()],
            &tables,
            jit.jit_module(),
            false,
        )
        .expect("same-unit compile");
    } else {
        compile_names_to_module(
            home.clone(),
            &[af.name.clone(), bf.name.clone()],
            &tables,
            jit.jit_module(),
            false,
        )
        .expect("target module compile");
        compile_names_to_module(
            user.clone(),
            std::slice::from_ref(&takes.name),
            &tables,
            jit.jit_module(),
            false,
        )
        .expect("consumer module compile");
    }

    {
        let table = tables.get(&home).expect("target table");
        let bf_code = table.got.load_slot(bf_slot);
        assert!(!bf_code.is_null(), "bf's slot is published");
        table.got.store_slot(af_slot, bf_code);
    }

    let ptr = jit
        .get_ptr_by_name(&takes.name, 0)
        .expect("consumer is finalized");
    let takes_fn: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
    takes_fn()
}

// spec: design/backend/compile-to-module.md §12.2 — a wrapper over a target in
// this compilation calls through the target's own slot.
#[test]
fn wrapper_over_same_unit_target_calls_through_its_slot() {
    assert_eq!(
        run_after_repointing_target_slot("user"),
        101,
        "the wrapper over af must load af's slot, so it reaches bf after the repoint"
    );
}

// spec: design/backend/compile-to-module.md §12.2 — control: a wrapper over a
// target in another module already loads that module's slot.
#[test]
fn wrapper_over_other_module_target_calls_through_its_slot() {
    assert_eq!(
        run_after_repointing_target_slot("lib"),
        101,
        "the wrapper over lib/af must load lib's slot, so it reaches bf after the repoint"
    );
}

// ── The object holds no direct call into its own unit ─────────────────────

/// `(defn name [p] body)` over `params`, typed `Int` throughout.
fn defn_of(name: &str, params: &[&str], body: Expr, base: u32) -> Defn {
    Defn {
        name: Symbol::from(name),
        docstring: None,
        variants: vec![DefnVariant {
            params: params.iter().map(|p| (Symbol::from(*p), None)).collect(),
            body,
            span: Span::new(base, base + 40),
        }],
        visibility: Visibility::Public,
        span: Span::new(base, base + 40),
    }
}

fn int_lit(value: i64, at: u32) -> Expr {
    Expr::IntLit {
        value,
        span: Span::new(at, at + 1),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn var(name: &str, at: u32, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span: Span::new(at, at + 1),
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

/// `(let [g bound] (g arg))`, where `bound` has type `bound_ty`.
fn let_apply(bound: Expr, bound_ty: Type, ret: Type, base: u32) -> Expr {
    Expr::Let {
        bindings: vec![(Symbol::from("g"), bound)],
        body: Box::new(Expr::Apply {
            callee: Box::new(var("g", base + 20, bound_ty)),
            args: vec![int_lit(2, base + 22)],
            span: Span::new(base + 19, base + 24),
            resolved_call: None,
            inferred_type: Some(Box::new(ret.clone())),
        }),
        span: Span::new(base, base + 25),
        inferred_type: Some(Box::new(ret)),
    }
}

/// Install, in `user`, a unit taking three of its own functions as values: a
/// plain wrapper over `af`, a curry wrapper over `(add2 1)` and a wrapper over
/// the constructor `MkCell`. Returns the tables and the unit's names.
fn value_wrapper_unit() -> (DashMap<ModuleFullPath, SymbolTable>, Vec<Symbol>) {
    use cranelisp_types::{FQTypeName, ResolvedCall, Scheme, TypeDefInfo, TypeName};
    let user = ModuleFullPath::from("user");
    let fq = |name: &str| FQSymbol {
        module: user.clone(),
        symbol: Symbol::from(name),
    };
    let cell = FQTypeName::new(user.clone(), TypeName::from("Cell"));
    let cell_ty = Type::ADT(cell.clone(), vec![]);
    let to_cell = Type::Fn(vec![Type::Int], Box::new(cell_ty.clone()));
    let add2_ty = Type::Fn(vec![Type::Int, Type::Int], Box::new(Type::Int));

    let af = unary_defn("af", None, 0);
    let add2 = defn_of("add2", &["a", "b"], var("a", 45, Type::Int), 40);

    let plain_span = Span::new(110, 111);
    let plain = defn_of(
        "plain",
        &[],
        let_apply(var("af", 110, int_fn()), int_fn(), Type::Int, 100),
        100,
    );

    let curry_apply = Span::new(209, 216);
    let curry_bound = Expr::Apply {
        callee: Box::new(var("add2", 210, add2_ty)),
        args: vec![int_lit(1, 214)],
        span: curry_apply,
        resolved_call: Some(Box::new(ResolvedCall::AutoCurry {
            target_name: Symbol::from("add2"),
            applied_count: 1,
            total_count: 2,
            trait_resolution: None,
        })),
        inferred_type: Some(Box::new(int_fn())),
    };
    let curry = defn_of(
        "curry",
        &[],
        let_apply(curry_bound, int_fn(), Type::Int, 200),
        200,
    );

    let ctor_span = Span::new(310, 311);
    let ctor_value = defn_of(
        "ctor-value",
        &[],
        let_apply(
            var("MkCell", 310, to_cell.clone()),
            to_cell.clone(),
            cell_ty.clone(),
            300,
        ),
        300,
    );
    let mk_cell = defn_of(
        "MkCell",
        &["v"],
        Expr::ConstrADT {
            type_name: cell.clone(),
            tag: 0,
            fields: vec![var("v", 405, Type::Int)],
            span: Span::new(400, 410),
            inferred_type: Some(Box::new(cell_ty.clone())),
        },
        400,
    );

    let tables = empty_tables();
    let mut st = SymbolTable::new(user.clone());
    install_type_fixture(
        &mut st,
        Symbol::from("Cell"),
        TypeDefInfo {
            name: cell.clone(),
            type_params: vec![],
            constructors: vec![Symbol::from("MkCell")],
        },
    );
    install_ctor_fixture(
        &mut st,
        mk_cell.name.clone(),
        Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: to_cell,
        },
        vec![Symbol::from("v")],
        cell,
        0,
        1,
        None,
        mk_cell.variants.first().cloned(),
        Some(test_codegen_view(
            &mk_cell.name,
            mk_cell.variants.first().unwrap(),
            &HashMap::new(),
        )),
    );
    install_def_entry(&mut st, af.clone());
    install_def_entry(&mut st, add2.clone());
    install_def_entry_with_targets(
        &mut st,
        plain.clone(),
        &HashMap::from([(plain_span, fq("af"))]),
    );
    install_def_entry_with_targets(
        &mut st,
        curry.clone(),
        &HashMap::from([(curry_apply, fq("add2"))]),
    );
    install_def_entry_with_targets(
        &mut st,
        ctor_value.clone(),
        &HashMap::from([(ctor_span, fq("MkCell"))]),
    );
    tables.insert(user, st);
    let names = [af, add2, plain, curry, ctor_value, mk_cell]
        .into_iter()
        .map(|d| d.name)
        .collect();
    (tables, names)
}

/// Whether `reloc` is a call or a jump: the shape a direct call leaves.
fn is_call_or_jump(reloc: &::object::Relocation) -> bool {
    use ::object::{RelocationEncoding, RelocationKind};
    matches!(reloc.kind(), RelocationKind::PltRelative)
        || matches!(
            reloc.encoding(),
            RelocationEncoding::AArch64Call | RelocationEncoding::X86Branch
        )
}

/// Every call or jump relocation in a code section of `bytes` whose target is
/// one of `unit`'s functions, as `"{section}+{offset} -> {unit function}"`,
/// whatever the object format's spelling of the symbol.
fn direct_calls_into(bytes: &[u8], unit: &[Symbol]) -> Vec<String> {
    use ::object::{Object, ObjectSection, ObjectSymbol, RelocationTarget, SectionKind};
    let file = ::object::File::parse(bytes).expect("the emitted bytes parse as an object");
    let unit_function = |name: &str| {
        let bare = name
            .strip_prefix('_')
            .filter(|_| file.format() == ::object::BinaryFormat::MachO);
        unit.iter()
            .find(|u| u.as_ref() == name || bare == Some(u.as_ref()))
    };
    let mut found = Vec::new();
    for section in file.sections().filter(|s| s.kind() == SectionKind::Text) {
        for (offset, reloc) in section.relocations() {
            let RelocationTarget::Symbol(index) = reloc.target() else {
                continue;
            };
            let name = file
                .symbol_by_index(index)
                .and_then(|s| s.name().map(str::to_owned))
                .unwrap_or_default();
            if !is_call_or_jump(&reloc) {
                continue;
            }
            if let Some(target) = unit_function(&name) {
                found.push(format!(
                    "{}+{offset:#x} -> {target}",
                    section.name().unwrap_or("?")
                ));
            }
        }
    }
    found
}

/// Compile the value-wrapper unit to an object. With `plant`, also define in
/// the same module a function that calls `af` by its `FuncId`.
fn value_wrapper_object(plant: bool) -> (Vec<u8>, Vec<Symbol>) {
    use cranelift::prelude::*;
    use cranelift_module::{FuncOrDataId, Module};
    let (tables, names) = value_wrapper_unit();
    let mut obj = make_object_module();
    compile_names_to_module(
        ModuleFullPath::from("user"),
        &names,
        &tables,
        &mut obj,
        false,
    )
    .expect("the value-wrapper unit compiles to an object");
    if plant {
        let Some(FuncOrDataId::Func(af)) = obj.get_name("af") else {
            panic!("af is declared as a function");
        };
        let mut ctx = obj.make_context();
        ctx.func.signature.params.push(AbiParam::new(types::I64));
        ctx.func.signature.returns.push(AbiParam::new(types::I64));
        let planted = obj
            .declare_anonymous_function(&ctx.func.signature)
            .expect("declare the planted caller");
        let mut fctx = FunctionBuilderContext::new();
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let arg = b.block_params(entry)[0];
        let callee = obj.declare_func_in_func(af, b.func);
        let call = b.ins().call(callee, &[arg]);
        let result = b.inst_results(call)[0];
        b.ins().return_(&[result]);
        b.finalize();
        obj.define_function(planted, &mut ctx)
            .expect("define the planted caller");
    }
    let bytes = obj.finish().emit().expect("the object emits");
    (bytes, names)
}

// spec: design/backend/compile-to-module.md §12.2 (Evidence) — over the object
// for a unit holding a plain wrapper, a curry wrapper and a constructor taken
// as a value, no call or jump relocation names a function of the unit.
#[test]
fn object_holds_no_direct_call_into_its_unit() {
    let (bytes, names) = value_wrapper_object(false);
    assert_eq!(
        direct_calls_into(&bytes, &names),
        Vec::<String>::new(),
        "every call to a slotted function goes through its slot"
    );
}

// spec: design/backend/compile-to-module.md §12.2 (Evidence) — detection: a
// direct call planted beside the unit is reported.
#[test]
fn object_relocation_scan_reports_a_planted_direct_call() {
    let (bytes, names) = value_wrapper_object(true);
    let found = direct_calls_into(&bytes, &names);
    assert_eq!(found.len(), 1, "exactly the planted call: {found:?}");
    assert!(found[0].ends_with("-> af"), "names its target: {found:?}");
}
