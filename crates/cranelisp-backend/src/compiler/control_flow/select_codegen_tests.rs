// Backend-unit CLIF guards for the S96 Chunk-C race/select node bake
// (`design/backend/io-trampoline.md §16`). `compile_select`/`compile_race`
// (`select.rs`) are name-matched at the `BuiltinFn` apply arm; these units pin
// the emitted `IO_TAG_SELECT` (= 6) node SHAPE at the CLIF layer, in the default
// lane, independent of the reactor/runtime (the end-to-end winner/loser-drop
// behaviour is the `tests/concurrency_cancellation.rs` /qa seam).
//
// Harness: compile a zero-arg `defn` whose body is `(race a b)` / `(select [..])`,
// with the call's `resolved_call` set directly to `BuiltinFn { name }` (the
// typecheck output the backend name-matches on). The branches are plain `int_lit`s
// — the tag bake does not depend on the branch shape, and the runtime semantics
// are covered e2e.

use crate::jit::Jit;
use cranelisp_types::{
    Defn, DefnVariant, Expr, ModuleFullPath, ResolvedCall, Span, Symbol, SymbolTable, Type,
    Visibility,
};
use std::collections::HashMap;

fn int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn vec_lit(elements: Vec<Expr>) -> Expr {
    Expr::VecLit {
        elements,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// An `(name args...)` call whose `resolved_call` is `BuiltinFn { name }` — the
/// shape typecheck produces for `race`/`select` (the `bind` precedent).
fn builtin_call(name: &str, args: Vec<Expr>) -> Expr {
    let n = Symbol::from(name);
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: n.clone(),
            span: Span::SYNTHETIC,
            resolved_call: Some(Box::new(ResolvedCall::BuiltinFn { name: n.clone() })),
            inferred_type: Some(Box::new(Type::Int)),
        }),
        args,
        span: Span::SYNTHETIC,
        resolved_call: Some(Box::new(ResolvedCall::BuiltinFn { name: n })),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// Compile a probe `defn` whose body is `body` and return its CLIF.
fn clif_of_body(body: Expr) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    jit.declare_intrinsics().expect("intrinsics declare");

    let name = Symbol::from("select_codegen_probe");
    let defn = Defn {
        name: name.clone(),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };

    let func_ids = jit.declare_functions(&[&defn]).expect("declare");
    let func_arities: HashMap<Symbol, usize> = HashMap::new();
    let symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let module_path = ModuleFullPath::from("user");
    symbol_tables.insert(module_path.clone(), SymbolTable::new(module_path.clone()));
    let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
    let compile_ctx = jit.build_compile_context(
        &func_ids,
        &func_arities,
        &symbol_tables,
        &module_aliases,
        module_path,
    );
    jit.compile_defn(&defn, compile_ctx)
        .expect("compile")
        .clif_ir
}

// spec: io-trampoline.md §16.4 — `(race a b)` bakes the one `IO_TAG_SELECT` (= 6)
// node over a 2-element branch Vec (the literal `6` at TAG_OFFSET).
#[test]
fn race_builds_select_node_tag_six() {
    let clif = clif_of_body(builtin_call("race", vec![int_lit(1), int_lit(2)]));
    assert!(
        clif.contains("iconst.i64 6"),
        "`race` must construct an IO_TAG_SELECT (tag 6) node; CLIF:\n{clif}"
    );
}

// spec: io-trampoline.md §16.4 — `(select [a b])` bakes the SAME `IO_TAG_SELECT`
// (= 6) node over its Vec-literal branch carrier.
#[test]
fn select_builds_select_node_tag_six() {
    let clif = clif_of_body(builtin_call(
        "select",
        vec![vec_lit(vec![int_lit(1), int_lit(2)])],
    ));
    assert!(
        clif.contains("iconst.i64 6"),
        "`select` must construct an IO_TAG_SELECT (tag 6) node; CLIF:\n{clif}"
    );
}

// spec: io-trampoline.md §16.9 — the structural no-regression guard: an ordinary
// program (no race/select) constructs NO IO_TAG_SELECT node.
#[test]
fn no_combinator_builds_no_select_node_neg() {
    let clif = clif_of_body(int_lit(7));
    assert!(
        !clif.contains("iconst.i64 6"),
        "an ordinary program must construct NO IO_TAG_SELECT (tag 6) node; CLIF:\n{clif}"
    );
}

// --- `sleep` — the runtime-symbol poll-leaf bake (S96 C4, reactor.md §2.18) -----
//
// `(sleep d)` lowers to an `IO_TAG_EFFECT_POLL` (= 4) node whose `code_ptr` is the
// RUNTIME symbol `runtime/sleep_pollfn` (`func_addr`-baked — the NON-GOT path, the
// genuinely-new C4 machinery). These units pin that bake at the CLIF layer in the
// default lane (the park-then-resume behaviour is the intrinsics/e2e seam).

// spec: reactor.md §2.18 — `(sleep d)` builds an IO_TAG_EFFECT_POLL (tag 4) node.
#[test]
fn sleep_builds_poll_node_tag_four() {
    let clif = clif_of_body(builtin_call("sleep", vec![int_lit(100)]));
    assert!(
        clif.contains("iconst.i64 4"),
        "`sleep` must construct an IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
}

// spec: reactor.md §2.18 — the `code_ptr` is the RUNTIME symbol `runtime/sleep_pollfn`,
// resolved as a `Linkage::Import` + `func_addr`-baked (the non-GOT runtime-symbol
// path that distinguishes `compile_sleep` from `compile_poll_effect`'s GOT-slot
// load). The CLIF declares the external fn and takes its address. RED-on-revert: if
// `sleep` were routed through the GOT slot load (a `global_value` + `load`) instead,
// there would be no `func_addr` to a runtime symbol here.
#[test]
fn sleep_bakes_runtime_symbol_code_ptr_via_func_addr() {
    let clif = clif_of_body(builtin_call("sleep", vec![int_lit(100)]));
    assert!(
        clif.contains("func_addr"),
        "`sleep` must bake its poll-fn `code_ptr` via func_addr to the runtime \
         symbol (the non-GOT path); CLIF:\n{clif}"
    );
    assert!(
        clif.contains("sleep_pollfn") || clif.contains("u0:"),
        "`sleep`'s func_addr must reference the imported runtime/sleep_pollfn; \
         CLIF:\n{clif}"
    );
}

// spec: reactor.md §2.18 — the user arg is MILLISECONDS; the backend bakes
// `duration_nanos = d × 1_000_000` (the leaf works in nanos) via `imul_imm v,
// 1_000_000` (the immediate renders in hex: 1_000_000 = 0xf_4240).
#[test]
fn sleep_converts_milliseconds_to_nanos() {
    let clif = clif_of_body(builtin_call("sleep", vec![int_lit(100)]));
    assert!(
        clif.contains("imul_imm") && clif.to_lowercase().contains("f_4240"),
        "`sleep` must convert milliseconds → nanos via `imul_imm v, 1_000_000` \
         (0xf_4240); CLIF:\n{clif}"
    );
}

// spec: reactor.md §2.18 — the structural no-regression guard: an ordinary program
// (no sleep / no poll effect) constructs NO IO_TAG_EFFECT_POLL node and bakes no
// runtime-symbol func_addr.
#[test]
fn no_sleep_builds_no_poll_node_neg() {
    let clif = clif_of_body(int_lit(7));
    assert!(
        !clif.contains("iconst.i64 4"),
        "an ordinary program must construct NO IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
    assert!(
        !clif.contains("func_addr"),
        "an ordinary program must bake NO runtime-symbol func_addr; CLIF:\n{clif}"
    );
}
