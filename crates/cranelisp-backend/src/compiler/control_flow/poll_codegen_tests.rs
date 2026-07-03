// Backend-unit CLIF guards for the poll-construction arm (`compile_poll_effect`).
//
// **S97 ABI v9 (ctx-vtable handle model, `io-trampoline.md §17`).** The v8
// leading-pair operand convention + `inject_poll_leading_pair` pass are DELETED:
// the descriptor `(token, capacity)` never rides on a cranelisp value, a leaf arg,
// or the node — the platform poll-fn computes its token from the handle it holds and
// calls `ctx.acquire` itself. So a poll leaf's natural args are its ONLY args
// (`arg_vals[0..]`), marshaled into the state-closure env at `capture(1+i)`, and the
// node's two former admission slots carry INERT zero/sentinel `iconst`s (nothing the
// trampoline reads). These units pin the v9 node SHAPE + the bake-DELETION at the
// CLIF layer (the `/dev`-owed "no positional bake" absence guard, `io-trampoline.md
// §17.8`), independent of the reactor/loader.
//
// Harness: compile a zero-arg `defn` whose body is `(async-read <arg>)`, where
// `async-read` is a synthetic `DefKind::PlatformEffect` with a chosen `poll_shape`.

use crate::jit::Jit;
use cranelisp_types::{
    DefKind, Defn, DefnVariant, Expr, ModuleEntry, ModuleFullPath, Scheme, SchedulingClass, Span,
    Symbol, SymbolTable, Type, Visibility,
};
use std::collections::HashMap;

fn int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

fn string_lit(s: &str) -> Expr {
    Expr::StringLit {
        value: s.to_string(),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::String)),
    }
}

/// A synthetic `async-read` platform effect: `(Fn [params...] (IO Int))`
/// represented as `Fn([params...], Int)` for codegen (the return is an i64 node
/// pointer). Under v9 `params` is the FULL leaf signature — every param is a leaf
/// arg marshaled into the env (no leading pair is peeled).
fn poll_effect_entry(poll_shape: bool, params: Vec<Type>) -> ModuleEntry {
    let param_names = (0..params.len()).map(|i| Symbol::from(format!("a{i}"))).collect();
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(params, Box::new(Type::Int)),
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names,
        kind: Box::new(DefKind::PlatformEffect {
            scheduling_class: SchedulingClass::Commutative,
            poll_shape,
            got_slot: 0,
            mode_summary: None,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
        value_use: false,
    }
}

/// Build an `(async-read <args...>)` call body with the given arg expressions.
fn async_read_call(args: Vec<Expr>) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("async-read"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        args,
        span: Span::SYNTHETIC,
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// Compile a probe `defn` whose body is `body`, with `async-read` registered in
/// the `user` table as a platform effect of the given `poll_shape` + `params`
/// (the FULL leaf signature under v9 — every param is a leaf arg).
fn clif_of_body(poll_shape: bool, params: Vec<Type>, body: Expr) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    jit.declare_intrinsics().expect("intrinsics declare");

    let name = Symbol::from("poll_codegen_probe");
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
    let mut st = SymbolTable::new(module_path.clone());
    st.insert(Symbol::from("async-read"), poll_effect_entry(poll_shape, params));
    symbol_tables.insert(module_path.clone(), st);
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

/// Blocking-arm probe: `(async-read <arg>)` with `poll_shape:false`.
fn clif_of_blocking_call(param: Type, arg: Expr) -> String {
    clif_of_body(false, vec![param], async_read_call(vec![arg]))
}

/// v9 poll-arm probe: a poll leaf's natural args ARE its only args (no leading
/// pair). `leaf_params` is the full leaf signature; `leaf_args` the call args.
fn clif_of_poll_call(leaf_params: Vec<Type>, leaf_args: Vec<Expr>) -> String {
    clif_of_body(true, leaf_params, async_read_call(leaf_args))
}

// ---------------------------------------------------------------------------
// CLIF inspection helpers — split the probe CLIF at the node alloc (the LAST
// `call ` to runtime/alloc; the closure is allocated first, the node second).
// ---------------------------------------------------------------------------

fn node_store_region(clif: &str) -> &str {
    let idx = clif.rfind("call ").expect("node alloc call present in poll CLIF");
    &clif[idx..]
}

fn closure_store_region(clif: &str) -> &str {
    let idx = clif.rfind("call ").expect("node alloc call present in poll CLIF");
    &clif[..idx]
}

fn store_lines_at<'a>(region: &'a str, offset: &str) -> Vec<&'a str> {
    region
        .lines()
        .filter(|l| l.contains("store") && l.contains(offset))
        .collect()
}

fn stores_const_at(region: &str, offset: &str, value: i64) -> bool {
    let needle = format!("= {value}");
    store_lines_at(region, offset)
        .iter()
        .any(|l| l.trim_end().ends_with(&needle))
}

// spec: design/backend/io-trampoline.md §17.2 (byte-identical-off) — a blocking
// (`poll_shape:false`) effect CALLS the platform fn (`call_indirect`) and constructs
// NO `IO_TAG_EFFECT_POLL` (=4) node.
#[test]
fn poll_shape_false_builds_no_poll_node_and_calls_blocking() {
    let clif = clif_of_blocking_call(Type::Int, int_lit(55));
    assert!(
        !clif.contains("iconst.i64 4"),
        "a blocking effect must NOT construct an IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
    assert!(
        clif.contains("call_indirect"),
        "a blocking effect CALLS the platform fn at the site (call_indirect); CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §17.2 — a poll-shape (`poll_shape:true`)
// effect constructs an `IO_TAG_EFFECT_POLL` (=4) node over a host-built state-closure,
// marshaling its natural leaf args into the env (no leading-pair peel under v9).
#[test]
fn poll_shape_true_builds_io_tag_effect_poll_with_closure_env() {
    let clif = clif_of_poll_call(vec![Type::Int], vec![int_lit(55)]);
    assert!(
        clif.contains("iconst.i64 4"),
        "a poll-shape effect must construct an IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
    // The natural leaf arg (55) is stored into the env capture slot.
    assert!(
        clif.contains("iconst.i64 55"),
        "the leaf effect arg must be marshaled into the state-closure env; CLIF:\n{clif}"
    );
    // Two heap allocations: the state-closure + the node.
    let allocs = clif.matches("call ").count();
    assert!(
        allocs >= 2,
        "poll-node construction must alloc the state-closure + the node (>=2 calls); \
         found {allocs}. CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §17.2/§17.8 (the v9 "no positional bake"
// ABSENCE guard) — under the ctx-vtable model the poll node carries NO scheduling
// state baked from positional args. With a DISTINCTIVE leaf arg (777) the node's two
// admission slots @ +32/+40 must carry the INERT zero/sentinel `iconst`s (0/1), NOT
// the leaf operand 777 — proving the v8 leading-pair positional bake is gone.
#[test]
fn poll_node_does_not_bake_positional_arg_inert_slots_only() {
    use crate::heap::HeapAdt;
    // A single distinctive leaf arg 777 (a v8 build would have peeled it as `token`).
    let clif = clif_of_poll_call(vec![Type::Int], vec![int_lit(777)]);

    assert_eq!(HeapAdt::payload_size(3), 32);
    assert_eq!(HeapAdt::field_offset(1), 32);
    assert_eq!(HeapAdt::field_offset(2), 40);

    let node = node_store_region(&clif);
    // The node's admission slots are INERT — token sentinel 0 @ +32, capacity sentinel
    // 1 @ +40 — NOT the leaf operand 777 (no positional bake).
    assert!(
        stores_const_at(node, "+32", 0),
        "v9: node field 1 (+32) carries the inert token sentinel 0; node region:\n{node}"
    );
    assert!(
        stores_const_at(node, "+40", 1),
        "v9: node field 2 (+40) carries the inert capacity sentinel 1; node region:\n{node}"
    );
    assert!(
        !stores_const_at(node, "+32", 777),
        "v9: the leaf operand 777 must NOT be baked at node +32 (the v8 positional bake \
         is DELETED); node region:\n{node}"
    );
}

// spec: design/backend/io-trampoline.md §17.3 (no leading-pair peel) — under v9 a
// poll leaf's natural args ALL land in the state-closure env (`capture(1+i)`); the
// result slot stays at `capture(0)`. Nothing is peeled to the node.
#[test]
fn poll_env_marshals_all_leaf_args_no_peel() {
    use crate::heap::HeapClosure;
    // Two natural leaf args (55, 66) — under v8 the first two would have been peeled.
    let clif = clif_of_poll_call(vec![Type::Int, Type::Int], vec![int_lit(55), int_lit(66)]);
    let clo = closure_store_region(&clif);

    assert_eq!(HeapClosure::capture_offset(0), 32); // result slot
    assert_eq!(HeapClosure::capture_offset(1), 40); // leaf arg 0
    assert_eq!(HeapClosure::capture_offset(2), 48); // leaf arg 1

    assert!(
        stores_const_at(clo, "+32", 0),
        "result slot sentinel 0 must stay at capture(0)=+32; closure region:\n{clo}"
    );
    assert!(
        stores_const_at(clo, "+40", 55),
        "leaf arg 0 (55) must land at capture(1)=+40 (no peel); closure region:\n{clo}"
    );
    assert!(
        stores_const_at(clo, "+48", 66),
        "leaf arg 1 (66) must land at capture(2)=+48 (no peel); closure region:\n{clo}"
    );
}

// spec: design/backend/io-trampoline.md §17 (no-RC at the bake) — an all-scalar poll
// bake emits no `rc_inc` (atomic_rmw) and null drop glue (no func_addr): the node's
// inert admission slots are scalars and the single leaf is a scalar.
#[test]
fn poll_node_bake_emits_no_rc_inc_for_scalar_carrier() {
    let clif = clif_of_poll_call(vec![Type::Int], vec![int_lit(55)]);
    assert!(
        !clif.contains("atomic_rmw"),
        "an all-scalar poll bake must emit no atomic RC traffic; CLIF:\n{clif}"
    );
    assert!(
        !clif.contains("func_addr"),
        "an all-scalar poll node has null drop glue (no capture-dec); CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §12.7 (GOT load, not call) — the poll arm
// LOADS the poll-fn from the platform GOT slot (baking it as the state-closure
// `code_ptr`) and does NOT `call_indirect` it at the construction site.
#[test]
fn poll_arm_loads_got_slot_and_does_not_call_indirect() {
    let clif = clif_of_poll_call(vec![Type::Int], vec![int_lit(55)]);
    assert!(
        clif.contains("load"),
        "the poll arm must LOAD the poll-fn from the GOT slot; CLIF:\n{clif}"
    );
    assert!(
        !clif.contains("call_indirect"),
        "the poll arm must NOT call_indirect the poll-fn at the construction site; CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §12.7 (arg-capture RC balance) — a HEAP leaf
// arg generates a non-null capture-dec drop glue (`func_addr` baked at the drop-glue
// offset); a SCALAR leaf generates none (null `drop_glue_ptr`).
#[test]
fn poll_arm_heap_arg_generates_capture_dec_glue_scalar_does_not() {
    let scalar = clif_of_poll_call(vec![Type::Int], vec![int_lit(55)]);
    assert!(
        !scalar.contains("func_addr"),
        "a scalar (Int) leaf arg needs NO capture-dec glue (null drop_glue_ptr); CLIF:\n{scalar}"
    );
    let heap = clif_of_poll_call(vec![Type::String], vec![string_lit("hi")]);
    assert!(
        heap.contains("func_addr"),
        "a heap (String) leaf arg must generate the state-closure capture-dec drop glue \
         (func_addr baked as drop_glue_ptr); CLIF:\n{heap}"
    );
}
