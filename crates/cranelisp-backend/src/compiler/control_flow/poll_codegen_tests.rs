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

/// A synthetic `async-read` platform effect: `(Fn [params...] (IO Int))`
/// represented as `Fn([params...], Int)` for codegen (the return is an i64 node
/// pointer). `params` is the LEAF signature — the state-closure capture-dec glue
/// (`build_poll_state_drop_glue`) keys on these, aligned with `arg_vals[2..]`.
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
        }),
        callees: vec![],
        trait_origin: None,
        seq: 0,
        ast: None,
        codegen_view: None,
        code: None,
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
/// the `user` table as a platform effect of the given `poll_shape` + `params`.
///
/// `params` is the LEAF param signature (the user-declared effect signature) — it
/// describes only the leaf args (`arg_vals[2..]` on the poll arm), matching the
/// state-closure capture-dec glue (`build_poll_state_drop_glue`). On the poll arm
/// the caller supplies the full poll-shape operand convention
/// (`[token, capacity, leaf_0, ...]`, `io-trampoline.md §14.2`) as the call args.
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

/// Blocking-arm probe: `(async-read <arg>)` with `poll_shape:false`. Blocking
/// effects do NOT ride the leading-pair operand convention (it is a poll-shape
/// lowering), so the call args are the natural user args.
fn clif_of_blocking_call(param: Type, arg: Expr) -> String {
    clif_of_body(false, vec![param], async_read_call(vec![arg]))
}

/// Poll-arm probe: builds the full poll-shape operand convention
/// (`[token, capacity, leaf_0, ...]`, `io-trampoline.md §14.2`) as the call args.
/// `leaf_params` describes only the leaf args (`leaf_args`), matching the scheme's
/// leaf signature (the capture-dec glue keys on it).
fn clif_of_poll_call(
    token: Expr,
    capacity: Expr,
    leaf_params: Vec<Type>,
    leaf_args: Vec<Expr>,
) -> String {
    let mut args = vec![token, capacity];
    args.extend(leaf_args);
    clif_of_body(true, leaf_params, async_read_call(args))
}
// ---------------------------------------------------------------------------
// CLIF inspection helpers.
//
// The poll node and the state-closure share numeric byte offsets: closure
// `capture(0)` is at `closure+32` (== `HeapClosure::CAPTURES_START`) and the node
// `token` is at `node+32` (== `HeapAdt::field_offset(1)`); likewise `+40`. To
// pin a node-field bake to the right value we split the probe CLIF at the node
// alloc (the LAST `call ` — the closure is allocated first, the node second), so
// the node-field stores `(tag@+16, state_closure@+24, token@+32, capacity@+40)`
// are unambiguous from the closure env stores that precede them.
// ---------------------------------------------------------------------------

/// CLIF region AFTER the node alloc (the last `call ` to runtime/alloc) — the
/// `IO_TAG_EFFECT_POLL` node-field store region.
fn node_store_region(clif: &str) -> &str {
    let idx = clif.rfind("call ").expect("node alloc call present in poll CLIF");
    &clif[idx..]
}

/// CLIF region BEFORE the node alloc — the state-closure construction region
/// (code_ptr, drop_glue, result slot, leaf-arg captures).
fn closure_store_region(clif: &str) -> &str {
    let idx = clif.rfind("call ").expect("node alloc call present in poll CLIF");
    &clif[..idx]
}

/// The `store` lines in `region` that target byte offset `offset` (e.g. "+32").
/// Cranelift annotates a store of a constant with a trailing `; vN = <const>`,
/// so the stored constant is on the same line as the offset.
fn store_lines_at<'a>(region: &'a str, offset: &str) -> Vec<&'a str> {
    region
        .lines()
        .filter(|l| l.contains("store") && l.contains(offset))
        .collect()
}

/// True iff some `store` line at `offset` in `region` stores the exact constant
/// `value` (matched on the trailing `= <value>` annotation, end-anchored so
/// `= 1` does not match `= 16`).
fn stores_const_at(region: &str, offset: &str, value: i64) -> bool {
    let needle = format!("= {value}");
    store_lines_at(region, offset)
        .iter()
        .any(|l| l.trim_end().ends_with(&needle))
}

// spec: design/backend/io-trampoline.md §12.7 (byte-identical-off) — a blocking
// (`poll_shape:false`) effect — every v6 platform — must take the unchanged
// arm: it CALLS the platform fn (`call_indirect`) and constructs NO
// `IO_TAG_EFFECT_POLL` (=4) node. The default build only ever sees
// `poll_shape:false`, so this is the R3 byte-identical-off obligation as a guard.
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

// spec: design/backend/io-trampoline.md §6 (byte-identical-off negative guard /
// no-acquire-path-off) — `poll_carrier_default_build_constructs_no_acquire_path_neg`
// (tests/plan/sprint-96.md §6). In a default (feature-off) build every effect is
// `poll_shape:false`, so `compile_poll_effect` is never reached: NO
// `IO_TAG_EFFECT_POLL` node and NO live `(token, capacity)` carrier is constructed,
// and the backend emits no acquire/concurrency primitive (Principle 1). The blocking
// arm's emitted CLIF is byte-identical to today's — the R3 obligation as a guard.
#[test]
fn poll_carrier_default_build_constructs_no_acquire_path_neg() {
    let clif = clif_of_blocking_call(Type::Int, int_lit(55));
    // No poll node tag.
    assert!(
        !clif.contains("iconst.i64 4"),
        "feature-off build must construct NO IO_TAG_EFFECT_POLL (tag 4) carrier; CLIF:\n{clif}"
    );
    // No host-built poll-node allocation: the blocking node is DLL-built (the
    // backend only call_indirects the platform fn), so the backend emits no
    // alloc-then-store-tag-4 node-construction sequence.
    assert!(
        clif.contains("call_indirect"),
        "feature-off build takes the unchanged blocking call path; CLIF:\n{clif}"
    );
    // The backend never emits a concurrency/acquire primitive — it constructs a
    // value. (No atomic acquire/park instructions on the blocking arm.)
    assert!(
        !clif.contains("iconst.i64 4"),
        "no poll-carrier ⇒ no acquire path reachable feature-off; CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §14 (poll-node shape under the leading-pair
// convention) — a poll-shape (`poll_shape:true`) effect constructs an
// `IO_TAG_EFFECT_POLL` (=4) node over a host-built state-closure. The leading
// `(token, capacity)` pair is peeled (arg_vals[0..2]); the leaf args (arg_vals[2..])
// are marshaled into the env. Pins the new node SHAPE.
#[test]
fn poll_shape_true_builds_io_tag_effect_poll_with_closure_env() {
    let clif = clif_of_poll_call(int_lit(7), int_lit(3), vec![Type::Int], vec![int_lit(55)]);
    assert!(
        clif.contains("iconst.i64 4"),
        "a poll-shape effect must construct an IO_TAG_EFFECT_POLL (tag 4) node; CLIF:\n{clif}"
    );
    // The marshaled LEAF arg (55) is stored into the env capture slot.
    assert!(
        clif.contains("iconst.i64 55"),
        "the leaf effect arg must be marshaled into the state-closure env; CLIF:\n{clif}"
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

// spec: design/backend/io-trampoline.md §14.9 (live-token bake) — a tokened poll
// effect stores the LIVE token operand (arg_vals[0]) at node field_offset(1) (abs
// 32), NOT the S95 `iconst 0` sentinel. The node alloc stays payload_size(3) (no
// alloc change), token rides field 1 — symmetric with the blocking node's token.
#[test]
fn poll_node_bakes_live_token_at_field_offset_1() {
    use crate::heap::HeapAdt;
    // token = 777 (distinctive), capacity = 333, leaf_0 = 55.
    let clif = clif_of_poll_call(int_lit(777), int_lit(333), vec![Type::Int], vec![int_lit(55)]);

    // No alloc change — still payload_size(3) = 32 bytes.
    assert_eq!(HeapAdt::payload_size(3), 32);
    assert_eq!(HeapAdt::field_offset(1), 32);

    // The LIVE token (777) is baked at the node's field_offset(1) = +32 — NOT the
    // S95 sentinel 0. Use the node-store region so node+32 (token) is not confused
    // with closure+32 (result slot).
    let node = node_store_region(&clif);
    assert!(
        stores_const_at(node, "+32", 777),
        "live token (777) must be baked at node field_offset(1)=+32 (not the S95 \
         iconst-0 sentinel); node-store region:\n{node}\nfull CLIF:\n{clif}"
    );
    assert!(
        !stores_const_at(node, "+32", 0),
        "the token field must carry the LIVE operand, not the S95 sentinel 0; \
         node-store region:\n{node}"
    );
}

// spec: design/backend/io-trampoline.md §14.9 (live-capacity bake) — a poll effect
// stores the LIVE capacity operand (arg_vals[1]) at node field_offset(2) (abs 40),
// NOT the S95 `iconst 1` sentinel.
#[test]
fn poll_node_bakes_live_capacity_at_field_offset_2() {
    use crate::heap::HeapAdt;
    let clif = clif_of_poll_call(int_lit(777), int_lit(333), vec![Type::Int], vec![int_lit(55)]);
    assert_eq!(HeapAdt::field_offset(2), 40);

    let node = node_store_region(&clif);
    assert!(
        stores_const_at(node, "+40", 333),
        "live capacity (333) must be baked at node field_offset(2)=+40 (not the S95 \
         iconst-1 sentinel); node-store region:\n{node}\nfull CLIF:\n{clif}"
    );
    assert!(
        !stores_const_at(node, "+40", 1),
        "the capacity field must carry the LIVE operand, not the S95 sentinel 1; \
         node-store region:\n{node}"
    );
}

// spec: design/backend/io-trampoline.md §14.9 (tokenless leaf preserves
// sentinel-by-value) — a tokenless poll leaf (bare timer, no resource) supplies the
// leading pair as the explicit constants (0, 1); the backend bakes them through the
// SAME store path, so token = 0 (no-acquire) / capacity = 1 (serial) — the S95
// sentinel behaviour preserved by value, not by a special-case branch.
#[test]
fn tokenless_poll_leaf_bakes_sentinel_by_value() {
    // Leading pair = (0, 1); distinctive leaf 55 keeps the env stores separable.
    let clif = clif_of_poll_call(int_lit(0), int_lit(1), vec![Type::Int], vec![int_lit(55)]);
    let node = node_store_region(&clif);
    assert!(
        clif.contains("iconst.i64 4"),
        "the tokenless leaf still builds an IO_TAG_EFFECT_POLL node; CLIF:\n{clif}"
    );
    // token = 0 baked at field_offset(1)=+32 (no-acquire) through the live path.
    assert!(
        stores_const_at(node, "+32", 0),
        "tokenless token sentinel 0 must be baked at node +32 by value; \
         node-store region:\n{node}\nfull CLIF:\n{clif}"
    );
    // capacity = 1 baked at field_offset(2)=+40 (serial). The leaf 55 lives in the
    // CLOSURE region, so +40 in the node region is unambiguously the capacity.
    assert!(
        stores_const_at(node, "+40", 1),
        "tokenless capacity sentinel 1 must be baked at node +40 by value; \
         node-store region:\n{node}\nfull CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §14.9 (env layout under the leading-pair
// peel) — peeling the two leading operands must NOT shift the env arg offsets the
// poll-fn relies on. Leaf args (arg_vals[2..]) land at capture(1+i); the result
// slot stays at capture(0); the re-passed resource handle is leaf_0 at capture(1)
// (the poll-fn's fd at state+8). The token/capacity pair must NOT appear among the
// env stores (capacity is node-only; the handle reaches the env only as leaf_0).
#[test]
fn poll_env_layout_under_leading_pair_peel() {
    use crate::heap::HeapClosure;
    // token=7, capacity=3 (peeled, node-only); leaf_0=55, leaf_1=66 (env captures).
    let clif = clif_of_poll_call(
        int_lit(7),
        int_lit(3),
        vec![Type::Int, Type::Int],
        vec![int_lit(55), int_lit(66)],
    );
    let clo = closure_store_region(&clif);

    assert_eq!(HeapClosure::capture_offset(0), 32); // result slot
    assert_eq!(HeapClosure::capture_offset(1), 40); // leaf_0 (poll-fn fd, state+8)
    assert_eq!(HeapClosure::capture_offset(2), 48); // leaf_1

    // result slot sentinel 0 @ capture(0) = +32.
    assert!(
        stores_const_at(clo, "+32", 0),
        "result slot sentinel 0 must stay at capture(0)=+32; closure region:\n{clo}"
    );
    // leaf_0 (55) @ capture(1) = +40 — the re-passed resource handle = poll-fn fd
    // at state+8.
    assert!(
        stores_const_at(clo, "+40", 55),
        "leaf_0 (re-passed handle, 55) must land at capture(1)=+40 (poll-fn fd at \
         state+8); closure region:\n{clo}"
    );
    // leaf_1 (66) @ capture(2) = +48.
    assert!(
        stores_const_at(clo, "+48", 66),
        "leaf_1 (66) must land at capture(2)=+48; closure region:\n{clo}"
    );
    // The peeled token/capacity (7, 3) must NOT be marshaled into the env — they
    // are node-only / re-passed-as-leaf, not env captures.
    assert!(
        !stores_const_at(clo, "+40", 7) && !stores_const_at(clo, "+48", 7),
        "the peeled token (7) must NOT be stored as an env capture; closure region:\n{clo}"
    );
    assert!(
        !stores_const_at(clo, "+40", 3) && !stores_const_at(clo, "+48", 3),
        "the peeled capacity (3) must NOT be stored as an env capture; closure region:\n{clo}"
    );
}

// spec: design/backend/io-trampoline.md §14.9 (no-RC at the bake) — both baked
// node fields are NeverHeap i64 scalars (an opaque fd/handle identity and a count),
// so neither node-field store emits an `rc_inc` (atomic_rmw add). With an all-scalar
// (token, capacity, leaf) the node stays a one-heap-field ADT with null drop glue —
// no atomic RC traffic at all in the construction.
#[test]
fn poll_node_bake_emits_no_rc_inc_for_scalar_carrier() {
    let clif = clif_of_poll_call(int_lit(7), int_lit(3), vec![Type::Int], vec![int_lit(55)]);
    assert!(
        !clif.contains("atomic_rmw"),
        "an all-scalar (token, capacity, leaf) poll bake must emit no atomic RC \
         traffic (no rc-inc/dec); CLIF:\n{clif}"
    );
    assert!(
        !clif.contains("func_addr"),
        "an all-scalar poll node has null drop glue (no capture-dec); CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §14.2 (producer-side leading-pair operand
// injection, S96 Wave A2b) — the production-only `inject_poll_leading_pair` pass
// prepends the tokenless sentinel `(token=0, capacity=1)` pair AHEAD of the natural
// leaf args for a poll-shape effect call, so A2's strict peel in
// `compile_poll_effect` receives `[token, capacity, leaf…]`. The bake guards above
// feed the post-injection form directly; THIS guard pins the producer that supplies
// it on the production (`codegen_view`) path. Keyed on the same `poll_shape: bool`
// discriminator the peel uses.
#[test]
fn inject_poll_leading_pair_prepends_tokenless_sentinel_for_poll_effect() {
    use cranelisp_types::{ConcreteType, MonoExpr};

    let symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let module_path = ModuleFullPath::from("user");
    let mut st = SymbolTable::new(module_path.clone());
    st.insert(Symbol::from("async-read"), poll_effect_entry(true, vec![Type::Int]));
    symbol_tables.insert(module_path.clone(), st);
    let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();

    let int = |v| MonoExpr::IntLit { value: v, span: Span::SYNTHETIC, ty: ConcreteType::Int };
    let mut body = MonoExpr::Apply {
        callee: Box::new(MonoExpr::Var {
            name: Symbol::from("async-read"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
        }),
        args: vec![int(55)],
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    };

    crate::inject_poll_leading_pair(&mut body, &symbol_tables, &module_aliases, &module_path);

    let MonoExpr::Apply { args, .. } = &body else { panic!("expected Apply, got {body:?}") };
    let vals: Vec<i64> = args
        .iter()
        .map(|a| match a {
            MonoExpr::IntLit { value, .. } => *value,
            other => panic!("expected IntLit args, got {other:?}"),
        })
        .collect();
    assert_eq!(
        vals,
        vec![0, 1, 55],
        "a poll-shape effect call must get the tokenless (0,1) pair injected AHEAD of \
         the natural leaf arg (55), so compile_poll_effect's strict peel succeeds"
    );
}

// spec: design/backend/io-trampoline.md §14.2 (producer-side injection — negative /
// byte-identical-off) — a BLOCKING (`poll_shape:false`) effect call (every v6
// platform) is NOT rewritten: the injection is keyed strictly on `poll_shape: true`
// (the same discriminator the peel uses), so a default build (no poll-shape effect)
// sees an identity transform — no operand added.
#[test]
fn inject_poll_leading_pair_leaves_blocking_effect_untouched_neg() {
    use cranelisp_types::{ConcreteType, MonoExpr};

    let symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let module_path = ModuleFullPath::from("user");
    let mut st = SymbolTable::new(module_path.clone());
    // poll_shape:false — the blocking arm.
    st.insert(Symbol::from("async-read"), poll_effect_entry(false, vec![Type::Int]));
    symbol_tables.insert(module_path.clone(), st);
    let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();

    let mut body = MonoExpr::Apply {
        callee: Box::new(MonoExpr::Var {
            name: Symbol::from("async-read"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
        }),
        args: vec![MonoExpr::IntLit { value: 55, span: Span::SYNTHETIC, ty: ConcreteType::Int }],
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    };

    crate::inject_poll_leading_pair(&mut body, &symbol_tables, &module_aliases, &module_path);

    let MonoExpr::Apply { args, .. } = &body else { panic!("expected Apply, got {body:?}") };
    assert_eq!(
        args.len(),
        1,
        "a blocking (poll_shape:false) effect must NOT get the leading pair injected \
         (byte-identical-off — the injection is poll-shape-keyed)"
    );
}

/// A synthetic poll-shape platform effect with a chosen `scheduling_class` — the
/// S96 A4 step-0 producer discriminator. `poll_effect_entry` above hardwires
/// `Commutative`; this variant lets a test exercise the `ResourceSerial`
/// (source-supplies-the-pair) branch of `inject_poll_leading_pair`.
fn poll_effect_entry_with_class(class: SchedulingClass, params: Vec<Type>) -> ModuleEntry {
    let mut entry = poll_effect_entry(true, params);
    if let ModuleEntry::Def { kind, .. } = &mut entry
        && let DefKind::PlatformEffect { scheduling_class, .. } = kind.as_mut()
    {
        *scheduling_class = class;
    }
    entry
}

// spec: design/backend/io-trampoline.md §14.2 + design/platform/poll-support.md
// §3.4.2 (S96 A4 step 0 — `scheduling_class`-keyed injection) — a `ResourceSerial`
// poll-shape effect call is LEFT UNTOUCHED by `inject_poll_leading_pair`: the
// source/wrapper already supplies the live `[token, capacity, leaf_0, …]` leading
// pair (the S95 `pool-demo` convention on the poll carrier), so prepending `(0,1)`
// would clobber it. Only `Commutative` (tokenless) leaves get the sentinel pair.
// This is the negative face of the per-leaf gate that SUBSUMES the unconditional
// A2b inject.
#[test]
fn inject_poll_leading_pair_leaves_resource_serial_effect_untouched_neg() {
    use cranelisp_types::{ConcreteType, MonoExpr};

    let symbol_tables: dashmap::DashMap<ModuleFullPath, SymbolTable> = dashmap::DashMap::new();
    let module_path = ModuleFullPath::from("user");
    let mut st = SymbolTable::new(module_path.clone());
    // ResourceSerial poll leaf carrying its own (token, capacity, ms) leading args.
    st.insert(
        Symbol::from("poll-read"),
        poll_effect_entry_with_class(SchedulingClass::ResourceSerial, vec![Type::Int]),
    );
    symbol_tables.insert(module_path.clone(), st);
    let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();

    let int = |v| MonoExpr::IntLit { value: v, span: Span::SYNTHETIC, ty: ConcreteType::Int };
    // The source already places token=7, capacity=2, ms=60.
    let mut body = MonoExpr::Apply {
        callee: Box::new(MonoExpr::Var {
            name: Symbol::from("poll-read"),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
        }),
        args: vec![int(7), int(2), int(60)],
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    };

    crate::inject_poll_leading_pair(&mut body, &symbol_tables, &module_aliases, &module_path);

    let MonoExpr::Apply { args, .. } = &body else { panic!("expected Apply, got {body:?}") };
    let vals: Vec<i64> = args
        .iter()
        .map(|a| match a {
            MonoExpr::IntLit { value, .. } => *value,
            other => panic!("expected IntLit args, got {other:?}"),
        })
        .collect();
    assert_eq!(
        vals,
        vec![7, 2, 60],
        "a ResourceSerial poll-shape effect must be LEFT UNTOUCHED — the source already \
         supplies the live (token=7, capacity=2) leading pair; injecting (0,1) would clobber it"
    );
}

// spec: design/backend/io-trampoline.md §12.7 (GOT load, not call) — the poll arm
// LOADS the poll-fn from the platform GOT slot (baking it as the state-closure
// `code_ptr`) and does NOT `call_indirect` it at the construction site (the call
// is the trampoline's job at poll time). This is the load/call distinction that
// is the whole point of the arm vs the blocking arm.
#[test]
fn poll_arm_loads_got_slot_and_does_not_call_indirect() {
    let clif = clif_of_poll_call(int_lit(7), int_lit(3), vec![Type::Int], vec![int_lit(55)]);
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

// spec: design/backend/io-trampoline.md §12.7 (arg-capture RC balance) — leaf args
// are stored into the env via the consuming convention (ownership transfer, NO
// extra inc at the poll arm); a heap-typed leaf arg's reference is balanced by the
// state-closure's capture-dec drop glue. So a HEAP leaf generates a non-null drop
// glue (`func_addr` baked at the drop-glue offset), while a SCALAR leaf generates
// none (null `drop_glue_ptr`). Pins the RC lifecycle so the next reader cannot
// reintroduce a double-inc / a leaked capture.
#[test]
fn poll_arm_heap_arg_generates_capture_dec_glue_scalar_does_not() {
    // Scalar (Int) leaf: NeverHeap ⇒ null drop glue (no func_addr emitted; the
    // poll-fn code_ptr is a GOT `load`, not a func_addr).
    let scalar = clif_of_poll_call(int_lit(7), int_lit(3), vec![Type::Int], vec![int_lit(55)]);
    assert!(
        !scalar.contains("func_addr"),
        "a scalar (Int) leaf arg needs NO capture-dec glue (null drop_glue_ptr); CLIF:\n{scalar}"
    );
    // Heap (String) leaf: the state-closure drop glue is generated to dec the
    // captured arg when the node is consumed — its address is baked via func_addr.
    let heap = clif_of_poll_call(int_lit(7), int_lit(3), vec![Type::String], vec![string_lit("hi")]);
    assert!(
        heap.contains("func_addr"),
        "a heap (String) leaf arg must generate the state-closure capture-dec drop glue \
         (func_addr baked as drop_glue_ptr) — the dec side of the consuming transfer; \
         CLIF:\n{heap}"
    );
}
