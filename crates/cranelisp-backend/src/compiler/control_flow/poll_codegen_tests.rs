// Backend-unit CLIF guards for the S94 poll-construction arm (FIXME 0457;
// `design/backend/io-trampoline.md §12.7`). The arm (`compile_poll_effect` +
// `build_poll_state_drop_glue` + `emit_got_slot_load`) is otherwise reachable
// only via `nt-reactor-e2e`; these units run in the DEFAULT `nt` lane (the
// durable per-fix guard), pinning the emitted node SHAPE at the CLIF layer
// independent of the reactor/loader.
//
// Harness: compile a zero-arg `defn` whose body is `(async-read <arg>)`, where
// `async-read` is a synthetic `DefKind::PlatformEffect` inserted into the `user`
// symbol table with a chosen `poll_shape`. The arm is keyed on `poll_shape` (no
// cargo feature), so a `poll_shape:false` entry exercises the unchanged blocking
// arm and a `poll_shape:true` entry the poll-construction arm — in the same
// default build.

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

/// A synthetic `async-read` platform effect: `(Fn [param] (IO Int))` represented
/// as `Fn([param], Int)` for codegen (the return is an i64 node pointer).
fn poll_effect_entry(poll_shape: bool, param: Type) -> ModuleEntry {
    ModuleEntry::Def {
        scheme: Scheme {
            type_vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![param], Box::new(Type::Int)),
        },
        visibility: Visibility::Public,
        docstring: None,
        param_names: vec![Symbol::from("n")],
        kind: Box::new(DefKind::PlatformEffect {
            scheduling_class: SchedulingClass::Commutative,
            poll_shape,
            got_slot: 0,
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
    }
}

/// Compile `(async-read <arg>)` and return the probe fn's CLIF, with `async-read`
/// registered in the `user` table as a platform effect of the given `poll_shape`
/// + parameter type.
fn clif_of_effect_call(poll_shape: bool, param: Type, arg: Expr) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    jit.declare_intrinsics().expect("intrinsics declare");

    let name = Symbol::from("poll_codegen_probe");
    let body = Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("async-read"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        args: vec![arg],
        span: Span::SYNTHETIC,
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    };
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
    st.insert(Symbol::from("async-read"), poll_effect_entry(poll_shape, param));
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

// spec: design/backend/io-trampoline.md §12.7 (byte-identical-off) — a blocking
// (`poll_shape:false`) effect — every v6 platform — must take the unchanged
// arm: it CALLS the platform fn (`call_indirect`) and constructs NO
// `IO_TAG_EFFECT_POLL` (=4) node. The default build only ever sees
// `poll_shape:false`, so this is the R3 byte-identical-off obligation as a guard.
#[test]
fn poll_shape_false_builds_no_poll_node_and_calls_blocking() {
    let clif = clif_of_effect_call(false, Type::Int, int_lit(55));
    assert!(
        !clif.contains("iconst.i64 4"),
        "a blocking effect must NOT construct an IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
    assert!(
        clif.contains("call_indirect"),
        "a blocking effect CALLS the platform fn at the site (call_indirect); CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §12.7 (poll-node shape) — a poll-shape
// (`poll_shape:true`) effect constructs an `IO_TAG_EFFECT_POLL` (=4) node over a
// host-built state-closure: `code_ptr` (GOT-loaded poll-fn), `drop_glue_ptr`,
// `capture(0)` = result-slot sentinel `0`, `capture(1..)` = the marshaled i64
// args. Pins the new node SHAPE.
#[test]
fn poll_shape_true_builds_io_tag_effect_poll_with_closure_env() {
    let clif = clif_of_effect_call(true, Type::Int, int_lit(55));
    assert!(
        clif.contains("iconst.i64 4"),
        "a poll-shape effect must construct an IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
    // The marshaled arg (55) is stored into the env capture slot.
    assert!(
        clif.contains("iconst.i64 55"),
        "the effect arg must be marshaled into the state-closure env; CLIF:\n{clif}"
    );
    // Two heap allocations: the state-closure + the node (vs the blocking arm,
    // which allocates neither — the DLL builds the blocking node).
    let allocs = clif.matches("call ").count();
    assert!(
        allocs >= 2,
        "poll-node construction must alloc the state-closure + the node (>=2 calls); \
         found {allocs}. CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §13.3 (S95 slice 3 — reserved (token,
// capacity) carrier) — a poll-shape effect's `IO_TAG_EFFECT_POLL` node reserves
// the symmetric `(token, capacity)` slots: the node alloc widens to
// `payload_size(3)` (= 32-byte payload), the state-closure is stored at
// `field_offset(0)` (= +24), a token sentinel `0` is stored at `field_offset(1)`
// (= +32, symmetric with the blocking node's token), and a capacity sentinel `1`
// at `field_offset(2)` (= +40). Pins the reserved offsets + sentinel values so the
// Wave-4 trampoline reads `(token, capacity)` uniformly off any IO node.
#[test]
fn poll_node_reserves_token_capacity_slots_with_sentinels() {
    use crate::heap::HeapAdt;
    let clif = clif_of_effect_call(true, Type::Int, int_lit(55));

    // The widened node alloc: payload_size(3) = 8 + 3*8 = 32 bytes.
    assert_eq!(HeapAdt::payload_size(3), 32);
    assert!(
        clif.contains("iconst.i64 32"),
        "the widened poll node must alloc payload_size(3) = 32 bytes; CLIF:\n{clif}"
    );

    // Capacity sentinel `1` — distinctive (the only `iconst.i64 1` the poll arm
    // emits; args are 55, token + result sentinels are 0).
    assert!(
        clif.contains("iconst.i64 1\n") || clif.contains("iconst.i64 1 "),
        "the poll node must reserve a capacity sentinel of 1; CLIF:\n{clif}"
    );

    // The reserved fields land at the symmetric offsets: token @ field_offset(1)
    // (= +32), capacity @ field_offset(2) (= +40). Assert stores at those offsets.
    assert_eq!(HeapAdt::field_offset(1), 32);
    assert_eq!(HeapAdt::field_offset(2), 40);
    assert!(
        clif.contains("+32"),
        "token sentinel must be stored at field_offset(1) = +32 (symmetric with \
         the blocking node's token); CLIF:\n{clif}"
    );
    assert!(
        clif.contains("+40"),
        "capacity sentinel must be stored at field_offset(2) = +40; CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §12.7 (GOT load, not call) — the poll arm
// LOADS the poll-fn from the platform GOT slot (baking it as the state-closure
// `code_ptr`) and does NOT `call_indirect` it at the construction site (the call
// is the trampoline's job at poll time). This is the load/call distinction that
// is the whole point of the arm vs the blocking arm.
#[test]
fn poll_arm_loads_got_slot_and_does_not_call_indirect() {
    let clif = clif_of_effect_call(true, Type::Int, int_lit(55));
    assert!(
        clif.contains("load"),
        "the poll arm must LOAD the poll-fn from the GOT slot; CLIF:\n{clif}"
    );
    assert!(
        !clif.contains("call_indirect"),
        "the poll arm must NOT call_indirect the poll-fn at the construction site \
         (it bakes it as the closure code_ptr); CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §12.7 (arg-capture RC balance) — args are
// stored into the env via the consuming convention (ownership transfer, NO extra
// inc at the poll arm); a heap-typed arg's reference is balanced by the
// state-closure's capture-dec drop glue. So a HEAP arg generates a non-null drop
// glue (`func_addr` baked at the drop-glue offset), while a SCALAR arg generates
// none (null `drop_glue_ptr`). Pins the RC lifecycle so the next reader cannot
// reintroduce a double-inc / a leaked capture.
#[test]
fn poll_arm_heap_arg_generates_capture_dec_glue_scalar_does_not() {
    // Scalar (Int) arg: NeverHeap ⇒ null drop glue (no func_addr emitted; the
    // poll-fn code_ptr is a GOT `load`, not a func_addr).
    let scalar = clif_of_effect_call(true, Type::Int, int_lit(55));
    assert!(
        !scalar.contains("func_addr"),
        "a scalar (Int) arg needs NO capture-dec glue (null drop_glue_ptr); CLIF:\n{scalar}"
    );
    // Heap (String) arg: the state-closure drop glue is generated to dec the
    // captured arg when the node is consumed — its address is baked via func_addr.
    let heap = clif_of_effect_call(true, Type::String, string_lit("hi"));
    assert!(
        heap.contains("func_addr"),
        "a heap (String) arg must generate the state-closure capture-dec drop glue \
         (func_addr baked as drop_glue_ptr) — the dec side of the consuming transfer; \
         CLIF:\n{heap}"
    );
}
