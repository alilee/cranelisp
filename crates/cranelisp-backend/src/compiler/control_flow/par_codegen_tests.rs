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
use cranelisp_types::{Defn, DefnVariant, Expr, ResolvedCall, Span, Symbol, Type, Visibility};
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

/// A zero-arg call to the declared probe function `par_codegen_probe`. It is a
/// non-cheap, non-constructor `Apply`, so `is_worth_sparking` returns true —
/// useful as a sparkable binding value in the create-gate tests below.
fn probe_call(span: Span) -> Expr {
    Expr::Apply {
        callee: Box::new(Expr::Var {
            name: Symbol::from("par_codegen_probe"),
            span,
            resolved_call: None,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        args: vec![],
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// A bare variable reference of type Int.
fn var_ref(name: &str, span: Span) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// An inline-primitive `(add-i64 lhs rhs)` apply. `add-i64` is NOT a cheap
/// builtin (CHEAP_BUILTINS holds the operator SYMBOLS `+`/`-`/…, not the `*-i64`
/// primitive names) and not a constructor, so `is_worth_sparking` returns true.
/// The `BuiltinFn` resolution drives inline `iadd` emission.
fn add_i64(lhs: Expr, rhs: Expr, span: Span) -> Expr {
    Expr::Apply {
        callee: Box::new(var_ref("add-i64", span)),
        args: vec![lhs, rhs],
        span,
        resolved_call: Some(Box::new(ResolvedCall::BuiltinFn {
            name: Symbol::from("add-i64"),
        })),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

// spec: design/backend/lenient-eval.md §2.6 + §4.5 — the limit-#2 seam. A `let`
//       whose SECOND binding depends on its sparked FIRST binding
//       (`[(a (probe)) (b (add-i64 a a))]`) sparks BOTH: `b` is admitted as a
//       *dependent* spark whose thunk captures `a`'s IVar pointer and forces it
//       on demand. The structural signature in the enclosing function's CLIF is
//       (1) the create-gate (try_reserve → brif) and (2) an `atomic_rmw … add`
//       at the dependent thunk's closure site — the IVar-CAPTURE INC. No other
//       lenient-`let` codegen path inc's an IVar pointer, so its presence proves
//       `b`'s dependency was captured as an IVar (to force on demand), not bound
//       as a plain value. The negative companion below confirms the inc is
//       absent for a purely-independent pair.
#[test]
fn let_path_dependent_binding_sparks_as_ivar_forced_on_demand() {
    let body = Expr::Let {
        bindings: vec![
            (Symbol::from("a"), probe_call(Span::new(1, 2))),
            (
                Symbol::from("b"),
                add_i64(var_ref("a", Span::new(3, 4)), var_ref("a", Span::new(5, 6)), Span::new(3, 6)),
            ),
        ],
        body: Box::new(int_lit(0)),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let clif = clif_of_body(body);

    // (1) The create-gate runtime branch is emitted (both bindings sparked ⇒
    // n=2 reserved before the first brif), exactly as the independent two-spark
    // case — the dependent binding really sparks, it does not fall back to
    // sequential.
    assert!(
        clif.contains("brif"),
        "a dependent-binding spark must still emit the create-gate; CLIF:\n{clif}"
    );
    let before_first_brif = clif.split("brif").next().unwrap_or("");
    assert!(
        before_first_brif.contains("iconst.i64 2"),
        "the gate must reserve n=2 (both bindings spark); CLIF:\n{clif}"
    );

    // (2) The IVar-capture inc: the dependent thunk's closure site inc's the
    // captured dependency IVar pointer (`heap::emit_rc_inc`), an atomic RMW add.
    // The gate's try_reserve is a `call`; the IVar dec is an atomic RMW *sub*;
    // the only atomic RMW *add* in a lenient `let` of Int bindings is this
    // IVar-capture inc. Its presence is the limit-#2 mechanism (capture the IVar,
    // force on demand).
    assert!(
        clif.contains("atomic_rmw") && clif.contains(" add "),
        "a dependent spark must inc the captured dependency IVar (atomic_rmw add); \
         CLIF:\n{clif}"
    );
}

// spec: design/backend/lenient-eval.md §4.5 — NEGATIVE companion. Two
//       INDEPENDENT sparkable bindings (`[(a (probe)) (b (probe))]`) still spark
//       (the gate is emitted) but neither captures an IVar — independent thunks
//       are built via the simple `compile_expr(Lambda)` path, which inc's no IVar
//       pointer. So no `atomic_rmw … add` appears. This isolates the capture-inc
//       in the positive test to the DEPENDENT path specifically.
#[test]
fn independent_let_bindings_do_not_inc_an_ivar_capture() {
    let body = Expr::Let {
        bindings: vec![
            (Symbol::from("a"), probe_call(Span::new(1, 2))),
            (Symbol::from("b"), probe_call(Span::new(3, 4))),
        ],
        body: Box::new(int_lit(0)),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let clif = clif_of_body(body);

    assert!(
        clif.contains("brif"),
        "two independent sparkable bindings must still emit the create-gate; CLIF:\n{clif}"
    );
    // No IVar-capture inc on the independent path.
    assert!(
        !clif.contains(" add "),
        "independent bindings must NOT inc an IVar capture (no atomic_rmw add); CLIF:\n{clif}"
    );
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

// spec: design/backend/lenient-eval.md §3.6.2 — the create-gate. A `let` with
//       ≥2 independent sparkable bindings must emit the runtime budget branch:
//       a call to `cranelisp_spark_budget_try_reserve` guarding a lenient arm
//       (which calls `cranelisp_ivar_create`/`_spark`) and a direct arm. Pins
//       that the static sparkability decision compiles to a *runtime* gate, not
//       an unconditional spark.
#[test]
fn create_gate_emitted_for_two_sparkable_let_bindings() {
    let body = Expr::Let {
        bindings: vec![
            (Symbol::from("a"), probe_call(Span::new(1, 2))),
            (Symbol::from("b"), probe_call(Span::new(3, 4))),
        ],
        body: Box::new(int_lit(0)),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let clif = clif_of_body(body);

    // Externs are referenced by module index (`u0:N`), not symbol name, in the
    // CLIF text — so the gate is pinned structurally. The create-gate is a
    // runtime branch (`brif`) whose guard is `try_reserve(n)`: just before the
    // FIRST branch the body reserves the count `n = 2` (the two sparkable
    // bindings) via a call. This is the `v0 = iconst.i64 2; v1 = call fnX(v0);
    // brif v1, lenient, direct` shape (lenient-eval.md §3.6.2).
    assert!(
        clif.contains("brif"),
        "the create-gate must emit a runtime branch (brif); CLIF:\n{clif}"
    );
    let before_first_brif = clif.split("brif").next().unwrap_or("");
    assert!(
        before_first_brif.contains("iconst.i64 2"),
        "the create-gate must reserve n=2 (the two sparkable bindings) before \
         branching; CLIF:\n{clif}"
    );
    assert!(
        before_first_brif.contains("call "),
        "the create-gate must call try_reserve before branching; CLIF:\n{clif}"
    );
    // The lenient arm allocates+sparks IVars while the direct arm does not, so a
    // gated site emits markedly more calls than the equivalent non-gated
    // sequential path (which would be just the two binding calls). This pins that
    // the lenient (allocating) arm is actually emitted.
    let call_count = clif.matches("= call ").count() + clif.matches(" call ").count();
    assert!(
        call_count >= 6,
        "the create-gate's lenient arm (create+spark+force per binding) must emit \
         the spark machinery; found only {call_count} calls. CLIF:\n{clif}"
    );
}

// spec: design/backend/lenient-eval.md §3.6.2 — NEGATIVE guard. A single
//       sparkable binding (< the ≥2 gate) must NOT emit the create-gate: no
//       try_reserve, no IVar create/spark. The binding compiles on the ordinary
//       sequential path. Pins that the gate is keyed off the ≥2-candidate
//       threshold, not "any sparkable binding".
#[test]
fn create_gate_not_emitted_for_single_sparkable_binding() {
    let body = Expr::Let {
        // One sparkable binding + one literal (never sparkable) ⇒ < 2 candidates.
        bindings: vec![
            (Symbol::from("a"), probe_call(Span::new(1, 2))),
            (Symbol::from("b"), int_lit(7)),
        ],
        body: Box::new(int_lit(0)),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let clif = clif_of_body(body);

    // No gate ⇒ no runtime branch (the single probe call + the literal compile on
    // the ordinary sequential path; Int bindings emit no rc-dec brif either).
    assert!(
        !clif.contains("brif"),
        "< 2 sparkable bindings must NOT emit a create-gate runtime branch; CLIF:\n{clif}"
    );
}
