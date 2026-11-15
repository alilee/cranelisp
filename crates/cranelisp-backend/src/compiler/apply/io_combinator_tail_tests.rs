//! U-18 — an inline IO combinator's operands are never in tail position.
//!
//! `compile_builtin_fn_call`'s combinator arms receive the caller's tail flag as
//! `saved_tail` and must restore it only AFTER `compile_operands`: an operand
//! compiled with the flag still set takes `compile_apply`'s TCO fast path, so a
//! self-call operand becomes the loop jump and the combinator node is never
//! reached (`(race (f n') (Pure 99))` returned the recursion's value).
//!
//! The probes ride the production per-body seam (`probe_defn_clif`) and read
//! the emitted CLIF of `(defn f [x] (race …))` with `f` carrying its own storage
//! FQ, the genuine self-call signal. The discriminator is the function's
//! `return`: it must return the `IO_TAG_SELECT` node's base, and the recursion
//! must be an argument-passing call rather than a `jump`.

use crate::jit::Jit;
use cranelisp_types::{
    Defn, DefnVariant, Expr, FQTypeName, ModuleFullPath, ResolvedCall, Span, Symbol, SymbolTable,
    Type, TypeName, Visibility,
};

const IO_TAG_SELECT: i64 = 6;

fn io_int_type() -> Type {
    Type::ADT(
        FQTypeName::new(ModuleFullPath::from("primitives"), TypeName::from("IO")),
        vec![Type::Int],
    )
}

fn io_int_lit(value: i64, span: Span) -> Expr {
    Expr::IntLit {
        value,
        span,
        inferred_type: Some(Box::new(io_int_type())),
    }
}

/// `(f x)`, the self-call operand. `f : Int -> IO Int`.
fn self_call(apply_span: Span) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("f"),
            span: Span::new(apply_span.start + 1, apply_span.start + 2),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Fn(vec![Type::Int], Box::new(io_int_type())))),
        }),
        args: vec![Expr::Var {
            name: Symbol::from("x"),
            span: Span::new(apply_span.start + 3, apply_span.start + 4),
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }],
        span: apply_span,
        resolved_call: None,
        inferred_type: Some(Box::new(io_int_type())),
    }
}

/// `(race a b)` with the `BuiltinFn` carrier typecheck records.
fn race(a: Expr, b: Expr) -> Expr {
    let name = Symbol::from("race");
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: name.clone(),
            span: Span::new(11, 15),
            resolved_call: Some(Box::new(ResolvedCall::BuiltinFn { name: name.clone() })),
            inferred_type: Some(Box::new(Type::Int)),
        }),
        args: vec![a, b],
        span: Span::new(10, 400),
        resolved_call: Some(Box::new(ResolvedCall::BuiltinFn { name })),
        inferred_type: Some(Box::new(io_int_type())),
    }
}

fn clif_of_f(body: Expr) -> String {
    let defn = Defn {
        name: Symbol::from("f"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module_path = ModuleFullPath::from("user");
    let symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let mut st = SymbolTable::new(module_path.clone());
    crate::test_support::insert_user_fn_stub(&mut st, "f", 1);
    symbol_tables.insert(module_path.clone(), st);
    let targets = crate::test_support::call_carriers(defn.body(), &module_path, &["f"]);
    crate::test_support::probe_defn_clif(
        &defn,
        &[],
        &targets,
        &symbol_tables,
        module_path,
        jit.jit_module(),
    )
}

/// The base values of every node whose tag word (`+16`) is stored as `tag`.
fn node_bases_for_tag(clif: &str, tag: i64) -> Vec<String> {
    let tag_values: Vec<&str> = clif
        .lines()
        .filter_map(|line| {
            let (lhs, rhs) = line.trim().split_once(" = ")?;
            (rhs.trim() == format!("iconst.i64 {tag}")).then_some(lhs)
        })
        .collect();
    clif.lines()
        .filter_map(|line| {
            let code = line.split(';').next()?.trim();
            let (stored, address) = code
                .strip_prefix("store notrap aligned ")?
                .split_once(", ")?;
            tag_values.contains(&stored).then_some(())?;
            address.strip_suffix("+16").map(str::to_string)
        })
        .collect()
}

fn returned_values(clif: &str) -> Vec<String> {
    clif.lines()
        .filter_map(|line| line.trim().strip_prefix("return ").map(str::to_string))
        .collect()
}

/// True iff some block at or after the loop header (`block1`) jumps back to
/// it: the TCO self-call. The entry block's own `jump block1` is not one.
fn has_loop_back_jump(clif: &str) -> bool {
    clif.lines()
        .skip_while(|l| !l.trim().starts_with("block1("))
        .any(|l| l.trim().starts_with("jump block1"))
}

fn assert_race_is_the_result(clif: &str) {
    let bases = node_bases_for_tag(clif, IO_TAG_SELECT);
    let returns = returned_values(clif);
    assert!(
        !bases.is_empty() && returns.iter().all(|r| bases.contains(r)),
        "every `return` of `f` must be the race's IO_TAG_SELECT node \
         (bases {bases:?}, returns {returns:?}); CLIF:\n{clif}"
    );
    assert!(
        !has_loop_back_jump(clif),
        "a race operand must not lower to the TCO loop-header jump; CLIF:\n{clif}"
    );
}

// spec: spec/10-io.md §10.12.8 — a race runs both effects; a self-call in the
// FIRST operand is an effect of the race, not the function's tail call.
#[test]
fn race_first_operand_self_call_is_an_effect_not_a_tail_jump() {
    let clif = clif_of_f(race(
        self_call(Span::new(100, 110)),
        io_int_lit(99, Span::new(200, 202)),
    ));
    assert_race_is_the_result(&clif);
}

// spec: spec/10-io.md §10.12.8 — either operand position; a correction confined
// to the first operand would leave this one jumping.
#[test]
fn race_second_operand_self_call_is_an_effect_not_a_tail_jump() {
    let clif = clif_of_f(race(
        io_int_lit(99, Span::new(200, 202)),
        self_call(Span::new(100, 110)),
    ));
    assert_race_is_the_result(&clif);
}

// spec: spec/12-runtime.md §12.5 — negative leg: the tail flag the race arm
// restores still governs a genuine tail self-call outside any combinator, so
// the correction does not turn TCO off.
#[test]
fn tail_self_call_outside_a_combinator_still_jumps_neg() {
    let clif = clif_of_f(self_call(Span::new(100, 110)));
    assert!(
        has_loop_back_jump(&clif),
        "a tail self-call outside a combinator must still TCO-jump; CLIF:\n{clif}"
    );
    assert!(
        node_bases_for_tag(&clif, IO_TAG_SELECT).is_empty(),
        "no combinator, no select node; CLIF:\n{clif}"
    );
}
