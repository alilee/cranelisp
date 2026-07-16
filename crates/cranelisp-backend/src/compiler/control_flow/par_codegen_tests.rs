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
    let mut st = cranelisp_types::SymbolTable::new(module_path.clone());
    // W1 (KC-W0-6): the probe's self-call reads the callee's `resolved_target`,
    // so the probe must be resolvable by the keyed read (`entry_at`). A
    // NotDetermined stub (no GOT slot) resolves to the `FuncId` tail —
    // byte-identical to the pre-W1 direct call.
    crate::test_support::insert_user_fn_stub(&mut st, "par_codegen_probe", 0);
    symbol_tables.insert(module_path.clone(), st);
    let resolved_targets =
        crate::test_support::call_carriers(defn.body(), &module_path, &["par_codegen_probe"]);
    let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
    let compile_ctx = jit.build_compile_context(
        &func_ids,
        &func_arities,
        &symbol_tables,
        &module_aliases,
        module_path,
    );
    jit.compile_defn_with_targets(&defn, &resolved_targets, compile_ctx)
        .expect("compile")
        .clif_ir
}

/// Like `clif_of_body`, but also declares the extra user functions in
/// `extra` (name, arity) so a `Var`-apply against them resolves. Only the
/// probe body is compiled+returned; the extras need only be *declared*.
fn clif_of_body_with_fns(body: Expr, extra: &[(&str, usize)]) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    jit.declare_intrinsics().expect("intrinsics declare");

    let probe_name = Symbol::from("par_codegen_probe");
    let probe = Defn {
        name: probe_name.clone(),
        docstring: None,
        variants: vec![DefnVariant { params: vec![], body, span: Span::SYNTHETIC }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    };
    let extra_defns: Vec<Defn> = extra
        .iter()
        .map(|(name, arity)| Defn {
            name: Symbol::from(*name),
            docstring: None,
            variants: vec![DefnVariant {
                params: (0..*arity)
                    .map(|i| (Symbol::from(format!("p{i}")), None))
                    .collect(),
                body: int_lit(0),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        })
        .collect();

    let all: Vec<&Defn> = std::iter::once(&probe).chain(extra_defns.iter()).collect();
    let func_ids = jit.declare_functions(&all).expect("declare");
    let func_arities: HashMap<Symbol, usize> = extra
        .iter()
        .map(|(name, arity)| (Symbol::from(*name), *arity))
        .collect();
    let symbol_tables: dashmap::DashMap<
        cranelisp_types::ModuleFullPath,
        cranelisp_types::SymbolTable,
    > = dashmap::DashMap::new();
    let module_path = cranelisp_types::ModuleFullPath::from("user");
    let mut st = cranelisp_types::SymbolTable::new(module_path.clone());
    // W1 (KC-W0-6): every call target the probe body dispatches to must be
    // resolvable by the keyed read — the probe itself plus each declared extra.
    // NotDetermined stubs (no slot) resolve to the `FuncId` tail, byte-identical.
    crate::test_support::insert_user_fn_stub(&mut st, "par_codegen_probe", 0);
    for (name, arity) in extra {
        crate::test_support::insert_user_fn_stub(&mut st, name, *arity);
    }
    symbol_tables.insert(module_path.clone(), st);
    let mut known: Vec<&str> = extra.iter().map(|(n, _)| *n).collect();
    known.push("par_codegen_probe");
    let resolved_targets =
        crate::test_support::call_carriers(probe.body(), &module_path, &known);
    let module_aliases: cranelisp_types::ModuleAliases = dashmap::DashMap::new();
    let compile_ctx = jit.build_compile_context(
        &func_ids,
        &func_arities,
        &symbol_tables,
        &module_aliases,
        module_path,
    );
    jit.compile_defn_with_targets(&probe, &resolved_targets, compile_ctx)
        .expect("compile")
        .clif_ir
}

/// A String literal expression (a heap-typed `AlwaysHeap` value).
fn str_lit(v: &str) -> Expr {
    Expr::StringLit {
        value: v.to_string(),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::String)),
    }
}

/// A one-arg call `(f arg)` against a declared user fn `f`. Non-cheap,
/// non-constructor ⇒ sparkable. When `arg` is a heap `Var`, the enclosing
/// spark thunk `(fn [] (f arg))` closes over it — the capture under test.
fn user_call1(f: &str, arg: Expr, span: Span) -> Expr {
    Expr::Apply {
        callee: Box::new(var_ref(f, span)),
        args: vec![arg],
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// A `String`-typed variable reference (heap capture source).
fn str_var(name: &str, span: Span) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(Type::String)),
    }
}

/// A lenient `let` whose two independent sparkable bindings each capture the
/// enclosing heap `String` `s` inside their spark thunk `(fn [] (strwork s))`.
fn heap_capturing_spark_let() -> Expr {
    Expr::Let {
        bindings: vec![(Symbol::from("s"), str_lit("hi"))],
        body: Box::new(Expr::Let {
            bindings: vec![
                (
                    Symbol::from("a"),
                    user_call1("strwork", str_var("s", Span::new(1, 2)), Span::new(1, 3)),
                ),
                (
                    Symbol::from("b"),
                    user_call1("strwork", str_var("s", Span::new(4, 5)), Span::new(4, 6)),
                ),
            ],
            body: Box::new(int_lit(0)),
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// A `LaunchContinue` whose continuation `(strwork s)` captures the enclosing
/// heap `String` `s`. Detached — the continuation capture MUST retain.
fn heap_capturing_launch() -> Expr {
    Expr::Let {
        bindings: vec![(Symbol::from("s"), str_lit("hi"))],
        body: Box::new(Expr::LaunchContinue {
            launched: Box::new(probe_call(Span::new(1, 2))),
            continuation: Box::new(user_call1("strwork", str_var("s", Span::new(3, 4)), Span::new(3, 5))),
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        }),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

// ===== Capture-by-borrow across structured fork-join (Sprint 99 Wave 1b,
// FIXME 0461; ring2-rc.md §5.5.2, lenient-eval.md §4.4.1) — backend-seam guards.
//
// These pin that the `spark_capture_borrow` flag gates the capture-store inc AND
// its symmetric drop-glue dec at the joined-spark emission sites, and that the
// DETACHED `LaunchContinue` path is structurally excluded (never borrow-elided).
//
// The fixtures use a lenient `let` whose two independent sparkable bindings each
// capture the enclosing heap `String` `s` in their spark thunk `(fn [] (strwork
// s))`. The create-gate compiles BOTH arms: the lenient arm sparks (2 capture
// incs on `s`), the direct/over-budget arm compiles the two `(strwork s)` calls
// sequentially (2 consuming incs on `s`). So with the toggle OFF, four
// `atomic_rmw … add` on `s` appear; capture-by-borrow elides ONLY the two
// lenient-arm capture incs, leaving the two direct-arm consuming incs — 4 → 2.
// Symmetrically the drop glue for each borrowed spark thunk is elided (no drop-
// glue `func_addr` stored — a `0` sentinel instead), so the outer function's
// `func_addr` count drops 4 → 2 (two thunks × code_ptr only, no drop-glue ptr).
//
// The env-var toggle (`CRANELISP_CAPTURE_BORROW`) is read once per process via a
// `LazyLock`; nextest's process-per-test isolation makes the on/off split
// between these tests reliable (a plain `cargo test` shared-process run would
// race the LazyLock — the project mandates `cargo nextest run`).

// spec: design/backend/ring2-rc.md §5.5.2 — with the toggle OFF (default), a
//       structurally-joined spark thunk RETAINS its heap captures (byte-
//       identical to pre-S99): the lenient arm emits a capture inc per thunk
//       and a drop glue per thunk. This is the byte-identical-off baseline.
#[test]
fn capture_borrow_off_retains_joined_spark_heap_captures() {
    // The `strwork`-capturing spark bindings are non-recursive, which the S104
    // default M-static admission filter (recursive-SCC ∧ non-tail) declines. This
    // test exercises the capture-borrow *emission* machinery — admission-
    // independent — so pin the syntactic filter that admits these shapes. nextest
    // isolates this per-process, so the set_var cannot leak (as with
    // CRANELISP_CAPTURE_BORROW below).
    // SAFETY: single-threaded test entry, before the SPARK_ADMIT LazyLock is read.
    unsafe { std::env::set_var("CRANELISP_SPARK_ADMIT", "syntactic") };
    assert!(
        std::env::var("CRANELISP_CAPTURE_BORROW").is_err(),
        "this baseline test must run with the toggle unset (nextest isolates it)"
    );
    let clif = clif_of_body_with_fns(heap_capturing_spark_let(), &[("strwork", 1)]);
    // 2 lenient-arm capture incs + 2 direct-arm consuming incs on `s`.
    assert_eq!(
        clif.matches(" add ").count(),
        4,
        "toggle OFF: both spark thunks must RETAIN their heap capture (4 atomic \
         adds on `s`: 2 lenient capture incs + 2 direct consuming incs); CLIF:\n{clif}"
    );
    // Each retaining thunk gets code_ptr + drop-glue-ptr func_addr = 4 total.
    assert_eq!(
        clif.matches("func_addr").count(),
        4,
        "toggle OFF: each spark thunk must emit drop glue (code_ptr + drop_glue \
         func_addr per thunk = 4); CLIF:\n{clif}"
    );
}

// spec: design/backend/ring2-rc.md §5.5.2 — with the toggle ON, a structurally-
//       joined spark thunk BORROWS its heap captures: the capture-store inc AND
//       the drop-glue dec are BOTH elided, symmetrically. The two lenient-arm
//       capture incs disappear (4 → 2 adds; the 2 direct-arm consuming incs
//       remain) and the two drop glues disappear (4 → 2 func_addr).
#[test]
fn capture_borrow_on_elides_joined_spark_heap_captures() {
    // SAFETY: single-threaded test entry, before any spark compile reads the
    // `CAPTURE_BORROW_ENABLED` / `SPARK_ADMIT` LazyLocks in this (nextest-
    // isolated) process. Pin the syntactic filter: the non-recursive `strwork`
    // spark shape is declined by the S104 default M-static filter, but this test
    // exercises admission-independent capture-borrow emission.
    unsafe { std::env::set_var("CRANELISP_SPARK_ADMIT", "syntactic") };
    unsafe { std::env::set_var("CRANELISP_CAPTURE_BORROW", "1") };
    let clif = clif_of_body_with_fns(heap_capturing_spark_let(), &[("strwork", 1)]);
    // Only the 2 direct-arm consuming incs remain; the 2 lenient-arm capture
    // incs are borrow-elided.
    assert_eq!(
        clif.matches(" add ").count(),
        2,
        "toggle ON: the two joined-spark capture incs must be BORROW-elided \
         (4 → 2 atomic adds; only the direct-arm consuming incs remain); CLIF:\n{clif}"
    );
    // Symmetric dec elision: no drop glue for a borrowed-capture thunk.
    assert_eq!(
        clif.matches("func_addr").count(),
        2,
        "toggle ON: a borrowed-capture spark thunk owns nothing, so no drop glue \
         is emitted (4 → 2 func_addr — code_ptr only per thunk); CLIF:\n{clif}"
    );
}

// spec: design/backend/ring2-rc.md §5.5.2.1 / .6 — THE MANDATORY UAF exclusion
//       guard. A DETACHED `LaunchContinue` effect that captures a heap value MUST
//       STILL RETAIN it — the capture must NOT be borrow-elided — even with the
//       toggle ON, because the detached strand outlives the parent's cleanup
//       (borrowing there is a use-after-free of the S98 bug-#2 class). This is a
//       single-process differential: under the SAME toggle-ON, the JOINED spark
//       borrows (its capture incs elide) while the DETACHED launch continuation
//       retains (its capture inc is present) — proving the exclusion is
//       structural (launch never raises `spark_capture_borrow`), not global.
#[test]
fn capture_borrow_on_launch_continuation_still_retains_heap_capture_neg() {
    // SAFETY: single-threaded test entry, before any spark compile reads the
    // `CAPTURE_BORROW_ENABLED` / `SPARK_ADMIT` LazyLocks in this (nextest-
    // isolated) process. Pin the syntactic filter so the joined-spark `spark_clif`
    // sanity leg genuinely exercises the spark path (the non-recursive `strwork`
    // shape is declined by the S104 default M-static filter); the LaunchContinue
    // leg is admission-independent.
    unsafe { std::env::set_var("CRANELISP_SPARK_ADMIT", "syntactic") };
    unsafe { std::env::set_var("CRANELISP_CAPTURE_BORROW", "1") };

    // The joined spark elides its capture incs under the toggle (4 → 2)…
    let spark_clif = clif_of_body_with_fns(heap_capturing_spark_let(), &[("strwork", 1)]);
    assert_eq!(
        spark_clif.matches(" add ").count(),
        2,
        "sanity: the JOINED spark must borrow under the toggle (2 adds); CLIF:\n{spark_clif}"
    );

    // …but the DETACHED launch continuation still RETAINS its heap capture: its
    // one capture inc on `s` is present regardless of the toggle. If the launch
    // path wrongly borrow-elided, this inc would vanish and the detached strand
    // would read a freed `s` (the bug-#2-class UAF).
    let launch_clif = clif_of_body_with_fns(heap_capturing_launch(), &[("strwork", 1)]);
    assert_eq!(
        launch_clif.matches(" add ").count(),
        1,
        "EXCLUSION VIOLATED: the detached LaunchContinue continuation MUST retain \
         its heap capture (1 atomic add on `s`) even with CRANELISP_CAPTURE_BORROW=1 \
         — borrow-eliding a detached capture is a use-after-free (ring2-rc.md \
         §5.5.2.1 / §5.5.2.4); CLIF:\n{launch_clif}"
    );
    assert!(
        launch_clif.contains("func_addr"),
        "the detached launch continuation must still emit its drop glue (retain); \
         CLIF:\n{launch_clif}"
    );
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
    // The dependent binding `b = (add-i64 a a)` has a non-recursive `add-i64`
    // callee, which the S104 default M-static admission filter declines — so `b`
    // would not spark and the dependent-thunk mechanism under test would not fire.
    // Pin the syntactic filter (admission-independent from the §4.5 dependent-thunk
    // emission this test guards). nextest isolates the set_var per-process.
    // SAFETY: single-threaded test entry, before the SPARK_ADMIT LazyLock is read.
    unsafe { std::env::set_var("CRANELISP_SPARK_ADMIT", "syntactic") };
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

// =============================================================================
// Launch-and-continue node emission (S96 Chunk B, slice 5).
// design: design/backend/io-trampoline.md §15 — a `MonoExpr::LaunchContinue`
// lowers to a thin `IO_TAG_LAUNCH=5` node (the launched sub-tree at field 0),
// wrapped by an `IO_TAG_BIND=2` node linking it to a continuation closure that
// discards the (Pure Unit) launch result. The structural twin of `Par` in
// `Bind(Par(..), cont)`. Branches are int-literal stand-ins for IO-tree pointers
// (the guard is the emitted node SHAPE, not its runtime IO semantics).
// =============================================================================

/// Build a `LaunchContinue` node by hand (no surface syntax — synthesised by
/// `/int`'s bind-chain analysis at the §10.12.7 launch shape).
fn launch_continue(launched: Expr, continuation: Expr) -> Expr {
    Expr::LaunchContinue {
        launched: Box::new(launched),
        continuation: Box::new(continuation),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

// spec: spec/10-io.md §10.12.7 + design/backend/io-trampoline.md §15.4/§15.9 —
//       a launch-marked site constructs an `IO_TAG_LAUNCH=5` node storing the
//       launched sub-tree pointer at field 0, wrapped by an `IO_TAG_BIND=2`
//       node. Both tag constants must appear in the emitted CLIF.
#[test]
fn launch_continue_emits_launch_node_wrapped_by_bind() {
    // (launch (effect-subtree) ; continue with 0)
    let body = launch_continue(int_lit(10), int_lit(0));
    let clif = clif_of_body(body);

    // The Launch node stores tag=5 (IO_TAG_LAUNCH) at TAG_OFFSET.
    assert!(
        clif.contains("iconst.i64 5"),
        "LaunchContinue codegen must emit the IO_TAG_LAUNCH=5 marker; CLIF:\n{clif}"
    );
    // The wrapping Bind node stores tag=2 (IO_TAG_BIND).
    assert!(
        clif.contains("iconst.i64 2"),
        "LaunchContinue codegen must wrap the Launch node in an IO_TAG_BIND=2 \
         node; CLIF:\n{clif}"
    );
    // The launched sub-tree pointer (stand-in int 10) is stored into the node.
    assert!(
        clif.contains("iconst.i64 10"),
        "the launched sub-tree value must be compiled + stored at field 0; CLIF:\n{clif}"
    );
    // At least three heap allocations: the Launch node, the continuation closure,
    // and the wrapping Bind node.
    let alloc_calls = clif.matches("call ").count();
    assert!(
        alloc_calls >= 3,
        "LaunchContinue codegen must emit Launch-node + continuation-closure + \
         Bind-node allocations (>=3 calls); found {alloc_calls}. CLIF:\n{clif}"
    );
}

// spec: design/backend/io-trampoline.md §15.7/§15.9 — NEGATIVE / no-regression:
//       an ordinary `Bind`-shaped program (a plain `let`, NOT a LaunchContinue)
//       emits NO IO_TAG_LAUNCH=5 node. The launch node is constructed ONLY at a
//       launch-marked site (structural no-regression: non-launch programs are
//       byte-identical to before this slice).
#[test]
fn non_launch_program_emits_no_launch_node() {
    // A plain sequential let with int-literal bindings (never launch-marked).
    let body = Expr::Let {
        bindings: vec![
            (Symbol::from("a"), int_lit(1)),
            (Symbol::from("b"), int_lit(2)),
        ],
        body: Box::new(int_lit(0)),
        span: Span::SYNTHETIC,
        inferred_type: Some(Box::new(Type::Int)),
    };
    let clif = clif_of_body(body);
    assert!(
        !clif.contains("iconst.i64 5"),
        "a non-launch program must NOT emit an IO_TAG_LAUNCH=5 node; CLIF:\n{clif}"
    );
}
