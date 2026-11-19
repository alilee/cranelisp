//! A function value's wrapper calls its target through the target's GOT slot,
//! whether the target is in the unit being compiled or in another module
//! (design/backend/compile-to-module.md §12.2).
//!
//! Each case compiles through `compile_to_module`, then repoints the target's
//! slot at another body. A wrapper that loads the slot follows the repoint; a
//! wrapper that calls the target's code directly does not.

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
