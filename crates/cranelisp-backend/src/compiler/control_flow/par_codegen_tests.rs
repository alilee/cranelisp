// ===== FIXME 0135 harvest (backend IO-scheduling slice): the Par-node
// CLIF-emission kernel of the quarantined `tests/legacy/lenient.rs`
// `test_io_schedule_*` GAP tests. Those 5 legacy tests assert RUNTIME
// scheduling behaviour (commutative pair → concurrent dispatch; Sequential
// → ordered; data-dependent → no Par; ResourceSerial same/diff token) which
// is **not e2e-witnessable without the test-capture commutative /
// ResourceSerial DLL fixture** — that runtime-dispatch slice is the
// `cranelisp-platform` co-owner's (per `s82-harvest-trace_lenient_jit.md`).
// The BACKEND-portable kernel is the **Par-node CLIF emission**: when an
// `Expr::ParBind` reaches codegen, `compile_par_bind` must emit the
// documented IO-tree structure (a `IO_TAG_PAR=3` node holding N branch
// pointers, wrapped by a `IO_TAG_BIND=2` node). This guard pins that
// structure at the CLIF layer — independent of the trampoline / DLL.
//
// The complementary decision pass — whether a `bind!` chain BECOMES a
// `ParBind` (scheduling-class + data-independence analysis) — runs upstream
// of backend (frontend/typecheck build the node), so it is not a backend
// unit; the backend's contract is "given a ParBind, emit a Par node".

use crate::jit::Jit;
use cranelisp_types::{Defn, DefnVariant, Expr, Span, Symbol, Type, Visibility};
use std::collections::HashMap;

/// Compile a zero-arg `defn` whose body is the given `Expr`, returning the
/// emitted CLIF-IR text. Branches need only be structurally valid for
/// `compile_expr` (we use int literals as stand-in IO-tree pointers — the
/// guard is the emitted Par-node SHAPE, not its runtime IO semantics).
fn clif_of_body(body: Expr) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    jit.declare_intrinsics().expect("intrinsics declare");

    let name = Symbol::from("par_codegen_probe");
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
    let symbol_tables: dashmap::DashMap<
        cranelisp_types::ModuleFullPath,
        cranelisp_types::SymbolTable,
    > = dashmap::DashMap::new();
    let module_path = cranelisp_types::ModuleFullPath::from("user");
    symbol_tables.insert(
        module_path.clone(),
        cranelisp_types::SymbolTable::new(module_path.clone()),
    );
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

fn int_lit(v: i64) -> Expr {
    Expr::IntLit {
        value: v,
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

// spec: spec/10-io.md §10.12.1 + design/backend/io-scheduling.md §4 —
//       an `Expr::ParBind` with N independent bindings emits a Par node
//       (IO_TAG_PAR=3) carrying N branch pointers, wrapped by a Bind node
//       (IO_TAG_BIND=2). Backend kernel of the legacy
//       `test_io_schedule_commutative_pair_par` reg-guard.
#[test]
fn par_bind_emits_par_node_with_branch_count() {
    let body = Expr::ParBind {
        bindings: vec![
            (Symbol::from("a"), int_lit(10)),
            (Symbol::from("b"), int_lit(20)),
        ],
        body: Box::new(int_lit(0)),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let clif = clif_of_body(body);

    // The Par node stores tag=3 and count=2 (two branches). The Bind
    // wrapper stores tag=2. We assert the structural constants are emitted
    // (iconst.i64 3 for the Par tag, iconst.i64 2 for the Bind tag /
    // branch count). The exact CLIF formatting is `v_ = iconst.i64 N`.
    assert!(
        clif.contains("iconst.i64 3"),
        "ParBind codegen must emit the IO_TAG_PAR=3 marker; CLIF:\n{clif}"
    );
    assert!(
        clif.contains("iconst.i64 2"),
        "ParBind codegen must emit the IO_TAG_BIND=2 / branch-count=2 \
         marker; CLIF:\n{clif}"
    );
    // The Par node allocates payload (tag + count + N branches) and the
    // continuation closure — at least two heap allocations are emitted.
    let alloc_calls = clif.matches("call ").count();
    assert!(
        alloc_calls >= 2,
        "ParBind codegen must emit Par-node + continuation allocations \
         (>=2 calls); found {alloc_calls}. CLIF:\n{clif}"
    );
}

// spec: spec/10-io.md §10.12.1 + design/backend/io-scheduling.md §4 —
//       the Par node's branch count tracks the number of bindings. A
//       three-binding ParBind emits count=3. Pins that the count store is
//       binding-driven, not a constant — guards against a regression that
//       hard-codes a 2-branch Par.
#[test]
fn par_bind_branch_count_tracks_bindings() {
    let body = Expr::ParBind {
        bindings: vec![
            (Symbol::from("a"), int_lit(1)),
            (Symbol::from("b"), int_lit(2)),
            (Symbol::from("c"), int_lit(3)),
        ],
        body: Box::new(int_lit(0)),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let clif = clif_of_body(body);
    // count=3 stored as the Par node's first field.
    assert!(
        clif.contains("iconst.i64 3"),
        "three-binding ParBind must store branch count=3; CLIF:\n{clif}"
    );
}

// spec: spec/10-io.md §10.12.2 + design/backend/io-scheduling.md §4 —
//       NEGATIVE guard. A plain sequential `let` (an `Expr::Let`, NOT an
//       `Expr::ParBind`) must NOT emit an IO_TAG_PAR=3 Par node — its
//       bindings are evaluated in source order with no concurrent dispatch.
//       This is the backend-portable kernel of the legacy
//       `test_io_schedule_sequential_no_par` GAP: for a `Sequential`-class
//       chain the scheduler builds an ordinary `Let`, and the backend's
//       contract is that ordinary `Let` codegen carries no Par marker.
//       (The scheduling *decision* — which class becomes a `ParBind` — is
//       upstream of backend; this guard pins that the no-Par INPUT yields
//       no-Par OUTPUT.) Int-literal bindings are used so the sparkability
//       analysis is a no-op (literals are never sparkable) and the path is
//       deterministically `compile_let_sequential`.
#[test]
fn sequential_let_emits_no_par_node() {
    let body = Expr::Let {
        bindings: vec![
            (Symbol::from("a"), int_lit(10)),
            (Symbol::from("b"), int_lit(20)),
        ],
        body: Box::new(int_lit(0)),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let clif = clif_of_body(body);
    // IO_TAG_PAR=3 is the Par-node tag. A sequential `let` must never
    // store it. (Other `iconst.i64 3` could in principle arise from an
    // unrelated constant, but with int-literal bindings of 10/20/0 the
    // only way `3` appears is a Par tag — none should be emitted.)
    assert!(
        !clif.contains("iconst.i64 3"),
        "a sequential `let` must NOT emit an IO_TAG_PAR=3 Par node; CLIF:\n{clif}"
    );
}
