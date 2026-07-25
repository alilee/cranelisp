//! S113 W2 — the TCO self-call fast-path is a KEYED-read site (`backend.md`
//! §2.7.1; BC §3 invariant 10 / Principle 24 "Resolve once").
//!
//! `compile_apply`'s fast-path 1 decides "is this tail call a self-call?" by the
//! callee `Var`'s carrier (`resolved_target`), NEVER by bare written-name
//! equality. The pre-S113 `*name == *fn_name` match was a name-equality-as-
//! identity judgment: in `(defn s1 [x] (let [s1 (fn [y] y)] (s1 x)))` the inner
//! `(s1 x)` is the LOCAL identity (§4.6 lexical shadow), yet the bare-name match
//! saw `s1 == s1`, TCO-looped into the enclosing `s1`, and hung
//! (`tests/shadowing_scope_lookup.rs::let_shadowed_single_sig_defn_call_resolves_to_local_not_outer`).
//!
//! These probes ride the PRODUCTION per-body seam (`probe_defn_clif` →
//! `compile_defn_in_module`) and inspect the emitted CLIF at the recursion:
//! - a TCO self-jump lowers to `jump <loop-header>` with NO call passing the
//!   argument (`compile_tail_self_call`, `apply.rs`) — on the pre-S113 bug the
//!   `(s1 x)` recursion collapsed to `jump block1(v1)`, the infinite loop;
//! - a local-closure indirect call lowers to a **two-operand** `call_indirect`
//!   (closure-ptr + the argument), `compile_closure_call` in `apply.rs`.
//!
//! The discriminator is `has_arg_passing_call_indirect`: a `call_indirect` whose
//! parenthesised operand list carries more than one operand. A closure CALL
//! passes `(closure_ptr, arg…)`; the closure's DROP-GLUE `call_indirect` (also
//! present, and present on BOTH buggy and fixed code) passes a single operand,
//! so a bare `contains("call_indirect")` would not distinguish the two — the
//! operand count does.

use crate::jit::Jit;
use cranelisp_types::{Defn, DefnVariant, Expr, ResolvedCall, Span, Symbol, Type, Visibility};

/// True iff the CLIF contains a `call_indirect` that passes MORE THAN ONE
/// operand — i.e. an arg-passing call (a closure call `f(closure_ptr, arg)`),
/// as opposed to the single-operand drop-glue `call_indirect(object_ptr)`.
fn has_arg_passing_call_indirect(clif: &str) -> bool {
    clif.lines().any(|line| {
        line.contains("call_indirect")
            // operands are the LAST parenthesised group on the line;
            // a comma inside it ⇒ ≥2 operands ⇒ an arg-passing call.
            && line
                .rsplit_once('(')
                .is_some_and(|(_, ops)| ops.trim_end_matches(')').contains(','))
    })
}

// --- AST fixture builders -------------------------------------------------

fn var(name: &str, span: Span, ty: Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span,
        resolved_call: None,
        inferred_type: Some(Box::new(ty)),
    }
}

/// `(fn [y] y)` — the identity closure, no captures. Fn([Int], Int).
fn identity_lambda(span: Span) -> Expr {
    Expr::Lambda {
        params: vec![(Symbol::from("y"), None)],
        body: Box::new(var(
            "y",
            Span::new(span.start + 1, span.start + 2),
            Type::Int,
        )),
        span,
        inferred_type: Some(Box::new(Type::Fn(vec![Type::Int], Box::new(Type::Int)))),
    }
}

/// `(callee arg_var)` in tail position. `callee_span` is the callee `Var`'s span
/// (the key `call_carriers` records the carrier under); `resolved_call` overlays
/// a dispatch onto the `Apply` node (fast-path-2 fixture).
fn tail_call(
    callee: &str,
    apply_span: Span,
    callee_span: Span,
    arg: &str,
    resolved_call: Option<ResolvedCall>,
) -> Expr {
    Expr::Apply {
        callee: Box::new(var(
            callee,
            callee_span,
            Type::Fn(vec![Type::Int], Box::new(Type::Int)),
        )),
        args: vec![var(
            arg,
            Span::new(apply_span.end - 2, apply_span.end - 1),
            Type::Int,
        )],
        span: apply_span,
        resolved_call: resolved_call.map(Box::new),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// Build a single-variant `defn fn_name [x] body`.
fn defn(fn_name: &str, body: Expr) -> Defn {
    Defn {
        name: Symbol::from(fn_name),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// Compile `defn` through the production per-body seam, returning its CLIF text.
/// `carrier_names` are the callee names that receive a `resolved_target`
/// (typecheck's self-recursion carve-out records the current fn's storage FQ for
/// a genuine self-call, and NOTHING for a shadowing local — the empty slice
/// models the shadow).
fn clif_of(defn: &Defn, carrier_names: &[&str]) -> String {
    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let module_path = cranelisp_types::ModuleFullPath::from("user");

    let symbol_tables: dashmap::DashMap<
        cranelisp_types::ModuleFullPath,
        cranelisp_types::SymbolTable,
    > = dashmap::DashMap::new();
    let mut st = cranelisp_types::SymbolTable::new(module_path.clone());
    crate::test_support::insert_user_fn_stub(&mut st, defn.name.as_ref(), 1);
    symbol_tables.insert(module_path.clone(), st);

    let resolved_targets =
        crate::test_support::call_carriers(defn.body(), &module_path, carrier_names);
    crate::test_support::probe_defn_clif(
        defn,
        &[],
        &resolved_targets,
        &symbol_tables,
        module_path,
        jit.jit_module(),
    )
}

// --- Tests ----------------------------------------------------------------

// spec: spec/04-functions.md §4.6 (lexical shadow) — the non-colliding twin
// (`design/typecheck/monomorphisation.md §11.8.7`). The enclosing defn is named
// `probe`, so there is no name collision at all; `(s1 x)` is unambiguously the
// LOCAL identity closure. It must lower to an INDIRECT closure call, never a TCO
// loop-header jump or a top-level GOT call. This is the `/clif`-inspectable form
// the hang blocked observing.
#[test]
fn probe_twin_local_closure_call_is_indirect_not_tco() {
    // (defn probe [x] (let [s1 (fn [y] y)] (s1 x)))
    let inner = tail_call("s1", Span::new(200, 210), Span::new(201, 203), "x", None);
    let body = Expr::Let {
        bindings: vec![(Symbol::from("s1"), identity_lambda(Span::new(100, 120)))],
        body: Box::new(inner),
        span: Span::new(50, 220),
        inferred_type: Some(Box::new(Type::Int)),
    };
    // `s1` is NOT a carrier name — it is a local; the callee carries no target.
    let clif = clif_of(&defn("probe", body), &[]);
    assert!(
        has_arg_passing_call_indirect(&clif),
        "the local `s1` closure call must lower to an arg-passing `call_indirect`, \
         not a TCO self-jump. CLIF:\n{clif}"
    );
}

// spec: spec/04-functions.md §4.6 (lexical shadow) — the COLLIDING form, the
// hang's exact shape. Enclosing defn AND the let binding are both named `s1`.
// Fast-path 1 must decide self-call by the callee's carrier (absent for the
// local) and fall through to the local indirect call — NOT match the bare name
// and TCO-loop into the enclosing `s1` (the pre-S113 hang). This assertion FAILS
// on the pre-fix `*name == *fn_name` code (which emits a TCO jump, no
// `call_indirect`), so it is the failing-first guard for the fix.
#[test]
fn colliding_shadow_call_is_local_indirect_not_tco_self_jump() {
    // (defn s1 [x] (let [s1 (fn [y] y)] (s1 x)))
    let inner = tail_call("s1", Span::new(200, 210), Span::new(201, 203), "x", None);
    let body = Expr::Let {
        bindings: vec![(Symbol::from("s1"), identity_lambda(Span::new(100, 120)))],
        body: Box::new(inner),
        span: Span::new(50, 220),
        inferred_type: Some(Box::new(Type::Int)),
    };
    // `s1` is the LOCAL — no carrier (models typecheck's carve-out recording
    // nothing for a shadowing binding).
    let clif = clif_of(&defn("s1", body), &[]);
    assert!(
        has_arg_passing_call_indirect(&clif),
        "the shadowing local `s1` must win: `(s1 x)` lowers to an arg-passing \
         `call_indirect`, NOT a TCO self-jump into the enclosing `s1` (the \
         pre-S113 hang: the recursion collapsed to `jump <loop-header>`). \
         CLIF:\n{clif}"
    );
}

// spec: spec/05-monomorphisation.md §5.1.2 (self-recursion back-flow, legal) —
// the genuine tail self-call regression pin. `(defn f [x] (f x))` in tail
// position: the callee carries the current fn's storage FQ `{user, f}` ==
// current storage identity, so fast-path 1 STILL fires (carrier-keyed) and emits
// a TCO loop-header jump — NO call instruction for the recursion. Guards that
// deleting the bare-name match does not regress genuine TCO.
#[test]
fn genuine_self_call_still_tco_loops_via_carrier() {
    // (defn f [x] (f x))
    let body = tail_call("f", Span::new(200, 210), Span::new(201, 202), "x", None);
    // `f` IS a carrier — the callee's `resolved_target` == the current fn's
    // storage FQ, the genuine self-call signal.
    let clif = clif_of(&defn("f", body), &["f"]);
    assert!(
        !clif.contains("call"),
        "a genuine tail self-call must TCO-loop (jump to loop header), emitting \
         NO call/call_indirect for the recursion. CLIF:\n{clif}"
    );
    assert!(
        clif.contains("jump"),
        "a genuine tail self-call lowers to a `jump` to the loop header. \
         CLIF:\n{clif}"
    );
}

// spec: spec/05-monomorphisation.md §5.1.2 — fast-path 2 (SigDispatch mangled-
// name) regression pin. A mono self-recursive variant `countdown$Int` whose body
// `(countdown x)` resolves to `SigDispatch { mangled_name: "countdown$Int" }`.
// Fast-path 2's string compare `current_fn_name == mangled_name` is a MODULE-
// identity compare by construction of the 0519 `{home}/`-embedding mangle
// (`backend.md` §2.7.1 fast-path-2 VERDICT — unchanged by this change-set); it
// must still TCO-loop. NOTE: the mangle carries no `{home}/` prefix here because
// the probe registers the variant under the bare `countdown$Int` name; the test
// pins that the SigDispatch path itself still self-jumps.
#[test]
fn mono_sigdispatch_self_call_still_tco_loops() {
    // (defn countdown$Int [x] (countdown x))  with the recursive Apply carrying
    // SigDispatch { mangled_name: "countdown$Int" }.
    let body = tail_call(
        "countdown",
        Span::new(200, 210),
        Span::new(201, 209),
        "x",
        Some(ResolvedCall::SigDispatch {
            mangled_name: cranelisp_types::JitSymbol::from("countdown$Int"),
        }),
    );
    // The callee name is "countdown" (not a carrier) — fast-path 2 keys on the
    // SigDispatch mangled name, not the callee carrier.
    let clif = clif_of(&defn("countdown$Int", body), &[]);
    assert!(
        !clif.contains("call"),
        "a mono SigDispatch self-call must TCO-loop (jump to loop header), \
         emitting NO call for the recursion. CLIF:\n{clif}"
    );
    assert!(
        clif.contains("jump"),
        "a mono SigDispatch self-call lowers to a `jump` to the loop header. \
         CLIF:\n{clif}"
    );
}
