//! Production-shaped ownership discriminator for the `sequence-io` recursive arm.

use crate::{
    jit::Jit,
    test_support::{
        compile_defns_in_module_with_pattern_ctors, insert_user_fn_stub_typed, install_type_fixture,
    },
};
use cranelisp_types::{
    CallableOrigin, Defn, DefnVariant, Expr, FQSymbol, FQTypeName, MatchArm, ModuleFullPath,
    Pattern, Scheme, Span, Symbol, SymbolRef, SymbolTable, SynthSpec, TemplateBody, TemplateKind,
    Type, TypeDefInfo, TypeName, Visibility,
};
use dashmap::DashMap;
use std::collections::HashMap;

fn io_int() -> Type {
    Type::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO")),
        vec![Type::Int],
    )
}

fn list_io_int() -> Type {
    Type::ADT(
        FQTypeName::new(
            ModuleFullPath::from("collections.list"),
            TypeName::from("List"),
        ),
        vec![io_int()],
    )
}

fn var(name: &str, span: Span, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

fn pure_int(value: i64, span: Span) -> Expr {
    Expr::ConstrADT {
        type_name: FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO")),
        tag: 0,
        fields: vec![Expr::IntLit {
            value,
            span: Span::new(span.start + 1, span.start + 2),
            inferred_type: Some(Box::new(Type::Int)),
        }],
        span,
        inferred_type: Some(Box::new(io_int())),
    }
}

fn list_nil(span: Span) -> Expr {
    Expr::ConstrADT {
        type_name: FQTypeName::new(
            ModuleFullPath::from("collections.list"),
            TypeName::from("List"),
        ),
        tag: 0,
        fields: vec![],
        span,
        inferred_type: Some(Box::new(list_io_int())),
    }
}

fn list_cons(head: Expr, tail: Expr, span: Span) -> Expr {
    Expr::ConstrADT {
        type_name: FQTypeName::new(
            ModuleFullPath::from("collections.list"),
            TypeName::from("List"),
        ),
        tag: 1,
        fields: vec![head, tail],
        span,
        inferred_type: Some(Box::new(list_io_int())),
    }
}

fn sequence_call(arg: Expr, span: Span) -> Expr {
    Expr::Apply {
        callee: Box::new(var(
            "sequence",
            Span::new(span.start + 1, span.start + 2),
            Type::Fn(vec![list_io_int()], Box::new(io_int())),
        )),
        args: vec![arg],
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(io_int())),
    }
}

fn bind_head_to_recursive_tail() -> Expr {
    let recursive_tail = sequence_call(
        var("tl", Span::new(31, 33), list_io_int()),
        Span::new(30, 34),
    );
    let continuation = Expr::Lambda {
        params: vec![(Symbol::from("x"), None)],
        body: Box::new(recursive_tail),
        span: Span::new(25, 35),
        inferred_type: Some(Box::new(Type::Fn(vec![Type::Int], Box::new(io_int())))),
    };
    Expr::Apply {
        callee: Box::new(var(
            "bind",
            Span::new(21, 22),
            Type::Fn(
                vec![io_int(), Type::Fn(vec![Type::Int], Box::new(io_int()))],
                Box::new(io_int()),
            ),
        )),
        args: vec![var("hd", Span::new(22, 24), io_int()), continuation],
        span: Span::new(20, 36),
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("bind"),
        })),
        inferred_type: Some(Box::new(io_int())),
    }
}

fn bind_with_list_owner_live(items: Expr) -> Expr {
    let continuation = Expr::Lambda {
        params: vec![(Symbol::from("result"), None)],
        // `items` is a free variable of the continuation. Its closure capture
        // keeps the original List (and therefore its `hd` owner) alive while
        // the generated recursive IO is driven.
        body: Box::new(Expr::Let {
            bindings: vec![(
                Symbol::from("keep"),
                var("items", Span::new(92, 97), list_io_int()),
            )],
            body: Box::new(pure_int(0, Span::new(98, 101))),
            span: Span::new(91, 102),
            inferred_type: Some(Box::new(io_int())),
        }),
        span: Span::new(88, 103),
        inferred_type: Some(Box::new(Type::Fn(vec![Type::Int], Box::new(io_int())))),
    };
    Expr::Apply {
        callee: Box::new(var(
            "bind",
            Span::new(84, 85),
            Type::Fn(
                vec![io_int(), Type::Fn(vec![Type::Int], Box::new(io_int()))],
                Box::new(io_int()),
            ),
        )),
        args: vec![sequence_call(items, Span::new(82, 87)), continuation],
        span: Span::new(81, 104),
        resolved_call: Some(Box::new(cranelisp_types::ResolvedCall::BuiltinFn {
            name: Symbol::from("bind"),
        })),
        inferred_type: Some(Box::new(io_int())),
    }
}

fn sequence_defn() -> Defn {
    Defn {
        name: Symbol::from("sequence"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("items"), None)],
            body: Expr::Match {
                scrutinee: Box::new(var("items", Span::new(1, 6), list_io_int())),
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: SymbolRef::new(None, Symbol::from("Cons")),
                            bindings: vec![Symbol::from("hd"), Symbol::from("tl")],
                            span: Span::new(10, 14),
                        },
                        body: bind_head_to_recursive_tail(),
                        span: Span::new(10, 36),
                    },
                    MatchArm {
                        pattern: Pattern::Constructor {
                            name: SymbolRef::new(None, Symbol::from("Nil")),
                            bindings: vec![],
                            span: Span::new(40, 43),
                        },
                        body: pure_int(0, Span::new(44, 47)),
                        span: Span::new(40, 47),
                    },
                ],
                span: Span::new(0, 48),
                compiler_generated: false,
                inferred_type: Some(Box::new(io_int())),
            },
            span: Span::new(0, 48),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 48),
    }
}

fn entry_defn() -> Defn {
    Defn {
        name: Symbol::from("sequence_entry"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Let {
                bindings: vec![(
                    Symbol::from("items"),
                    list_cons(
                        pure_int(7, Span::new(61, 64)),
                        list_cons(
                            pure_int(8, Span::new(65, 68)),
                            list_cons(
                                pure_int(9, Span::new(69, 72)),
                                list_nil(Span::new(73, 76)),
                                Span::new(68, 77),
                            ),
                            Span::new(64, 78),
                        ),
                        Span::new(60, 79),
                    ),
                )],
                body: Box::new(bind_with_list_owner_live(var(
                    "items",
                    Span::new(80, 81),
                    list_io_int(),
                ))),
                span: Span::new(59, 104),
                inferred_type: Some(Box::new(io_int())),
            },
            span: Span::new(59, 104),
        }],
        visibility: Visibility::Public,
        span: Span::new(59, 104),
    }
}

fn install_list_fixture(table: &mut SymbolTable) {
    let module = ModuleFullPath::from("collections.list");
    let list = FQTypeName::new(module.clone(), TypeName::from("List"));
    let info = TypeDefInfo {
        name: list.clone(),
        type_params: vec![Symbol::from("a")],
        constructors: vec![Symbol::from("Nil"), Symbol::from("Cons")],
    };
    install_type_fixture(table, Symbol::from("List"), info.clone());
    let generic_list = Type::ADT(list.clone(), vec![Type::Var(0)]);
    table
        .install_template(
            Symbol::from("Nil"),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: generic_list.clone(),
            },
            vec![],
            None,
            0,
            CallableOrigin::Ctor {
                type_name: list.clone(),
                tag: 0,
                field_count: 0,
                internal: false,
                type_def: Some(Box::new(info.clone())),
            },
            TemplateBody::Synth(SynthSpec::new(DefnVariant {
                params: vec![],
                body: Expr::IntLit {
                    value: 0,
                    span: Span::SYNTHETIC,
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::SYNTHETIC,
            })),
            TemplateKind::Parametric,
            vec![],
            Visibility::Public,
        )
        .expect("install Nil constructor template");
    table
        .install_template(
            Symbol::from("Cons"),
            Scheme {
                type_vars: vec![],
                constraints: HashMap::new(),
                ty: Type::Fn(
                    vec![Type::Var(0), generic_list.clone()],
                    Box::new(generic_list),
                ),
            },
            vec![Symbol::from("hd"), Symbol::from("tl")],
            None,
            1,
            CallableOrigin::Ctor {
                type_name: list,
                tag: 1,
                field_count: 2,
                internal: false,
                type_def: Some(Box::new(info)),
            },
            TemplateBody::Synth(SynthSpec::new(DefnVariant {
                params: vec![],
                body: Expr::IntLit {
                    value: 1,
                    span: Span::SYNTHETIC,
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::SYNTHETIC,
            })),
            TemplateKind::Parametric,
            vec![],
            Visibility::Public,
        )
        .expect("install Cons constructor template");
}

/// The `hd` pattern-field load must both receive an independent increment and
/// be the value stored in the newly constructed Bind input field. This follows
/// the specific dataflow edge instead of counting unrelated RC operations.
fn bind_input_has_independent_retain(clif: &str) -> bool {
    let lines: Vec<&str> = clif.lines().collect();
    lines.iter().enumerate().any(|(load_index, load)| {
        let Some((loaded, rhs)) = load.trim().split_once(" = ") else {
            return false;
        };
        if !rhs.starts_with("load.i64") || !rhs.contains("+24") {
            return false;
        }
        let Some(rc_word) = lines[load_index + 1..].iter().find_map(|line| {
            let (word, rhs) = line.trim().split_once(" = ")?;
            (rhs == format!("iadd_imm.i64 {loaded}, 8")).then_some(word)
        }) else {
            return false;
        };
        let retained = lines[load_index + 1..]
            .iter()
            .any(|line| line.contains("atomic_rmw.i64 add") && line.contains(rc_word));
        let Some(bind_input_base) = lines[load_index + 1..].iter().find_map(|line| {
            let (_, stored) = line.trim().split_once("store.i64 notrap aligned ")?;
            let (value, address) = stored.split_once(", ")?;
            (value == loaded)
                .then(|| address.strip_suffix("+24"))
                .flatten()
        }) else {
            return false;
        };
        let bind_tag = lines.iter().any(|line| {
            let (_, stored) = match line.trim().split_once("store notrap aligned ") {
                Some(parts) => parts,
                None => return false,
            };
            let (tag, address) = match stored.split_once(", ") {
                Some(parts) => parts,
                None => return false,
            };
            let address = address.split_whitespace().next().unwrap_or(address);
            let tag_is_bind = lines
                .iter()
                .any(|definition| definition.trim() == format!("{tag} = iconst.i64 2"));
            tag_is_bind && address == format!("{bind_input_base}+16")
        });
        retained && bind_tag
    })
}

// spec: spec/10-io.md §10.12.8; defect: class=rc-miscount locus=the private
// backend→intrinsics Bind ownership seam. The direct structural check identifies
// the producer edge; execution then distinguishes a missing producer reference
// from a consumer release that treats a proven-owned edge as borrowed.
#[test]
fn sequence_io_recursive_bind_keeps_the_matched_io_owned_until_release() {
    let sequence = sequence_defn();
    let entry = entry_defn();
    let user = ModuleFullPath::from("user");
    let lists = ModuleFullPath::from("collections.list");
    let tables = DashMap::new();
    let mut list_table = SymbolTable::new(lists.clone());
    install_list_fixture(&mut list_table);
    tables.insert(lists.clone(), list_table);
    let mut user_table = SymbolTable::new(user.clone());
    insert_user_fn_stub_typed(&mut user_table, "sequence", &[list_io_int()], io_int());
    tables.insert(user.clone(), user_table);

    let mut targets = crate::test_support::call_carriers(sequence.body(), &user, &["sequence"]);
    targets.extend(crate::test_support::call_carriers(
        entry.body(),
        &user,
        &["sequence"],
    ));
    let pattern_ctors = HashMap::from([
        (
            Span::new(10, 14),
            FQSymbol {
                module: lists.clone(),
                symbol: Symbol::from("Cons"),
            },
        ),
        (
            Span::new(40, 43),
            FQSymbol {
                module: lists,
                symbol: Symbol::from("Nil"),
            },
        ),
    ]);

    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let clifs = compile_defns_in_module_with_pattern_ctors(
        &[&sequence, &entry],
        &[],
        &targets,
        &pattern_ctors,
        &tables,
        user,
        jit.jit_module(),
    );
    assert!(
        bind_input_has_independent_retain(&clifs[0]),
        "the matched `hd` load must be independently retained before it is stored in Bind input:\n{}",
        clifs[0]
    );

    let entry_ptr = jit
        .finalize_and_get_ptr(&entry.name, 0)
        .expect("finalize sequence entry");
    let entry_fn: extern "C" fn() -> i64 = unsafe { std::mem::transmute(entry_ptr) };
    let generated_io = entry_fn();
    assert_eq!(
        cranelisp_intrinsics::io::cranelisp_run_io(generated_io),
        0,
        "the generated Bind must remain valid until the original List owner is released"
    );
}
