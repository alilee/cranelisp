//! The branch-forward rule (`design/backend/ownership-codegen.md` §13.3 and
//! the §13.5 tail-argument forwarding row; ACT-1021).
//!
//! A bare `Var` yielded by a branch or arm of a tail-argument `if`/`match` is
//! incremented exactly when its resolved slot holds a frame-owned heap
//! reference ([`super::slot_holds_frame_owned_reference`]). The pure fact is
//! pinned over its slot matrix. The seam cells compile real bodies through the
//! production per-body seam and count the increments one forwarded binding
//! adds: the subject yields the binding, and its control yields an integer
//! literal in the same position, which emits no RC operation. Every other part
//! of the pair is identical, so the difference is the forwarding branch's own
//! emission. The cells cover the four call paths that protect a branch
//! result: `compile_if`, the wildcard arm, `compile_var_pattern_arm` and
//! `compile_data_pattern`.

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, Ordering};

use cranelisp_types::{
    Defn, DefnVariant, Expr, FQSymbol, FQTypeName, MatchArm, Mode, ModeSummary, ModuleFullPath,
    MonoExpr, Pattern, ResolvedCall, Span, Symbol, SymbolRef, Type, Visibility,
};

use super::{SlotFrame, SlotOwnershipFacts, slot_holds_frame_owned_reference};

// ---------------------------------------------------------------------------
// The pure fact
// ---------------------------------------------------------------------------

// spec: spec/12-runtime.md §12.3.1 — a frame owns a slot's reference when the
// slot is heap-typed and not borrowed, or when it is a parameter the frame
// promoted. Promotion never reaches a local binder, which is how a binder that
// shadows a promoted parameter's name is judged by its own mark.
#[test]
fn the_ownership_fact_over_its_slot_matrix() {
    use SlotFrame::{Local, Param};
    // (frame, heap, borrowed, promoted) → frame-owned
    let table = [
        (Local, true, false, false, true),
        (Local, true, true, false, false),
        (Local, true, true, true, false),
        (Param, true, false, false, true),
        (Param, true, true, false, false),
        (Param, true, true, true, true),
        (Local, false, false, false, false),
        (Param, false, false, false, false),
        (Param, false, true, true, false),
    ];
    for (frame, heap, borrowed, promoted, owned) in table {
        let facts = SlotOwnershipFacts {
            frame,
            heap,
            borrowed,
            promoted,
        };
        assert_eq!(slot_holds_frame_owned_reference(facts), owned, "{facts:?}");
    }
}

// ---------------------------------------------------------------------------
// Fixture: (defn go [n o x y] …) in module `main`, with `o : main/Option`
// ---------------------------------------------------------------------------

const GO: &str = "go";

static NEXT_SPAN: AtomicU32 = AtomicU32::new(1_000);

/// A span no other node in the fixture shares; carriers are keyed by span.
pub(super) fn span() -> Span {
    let start = NEXT_SPAN.fetch_add(2, Ordering::Relaxed);
    Span::new(start, start + 1)
}

fn main_module() -> ModuleFullPath {
    ModuleFullPath::from("main")
}

fn option_ty() -> Type {
    Type::ADT(FQTypeName::new(main_module(), "Option".into()), vec![])
}

fn string_ty() -> Type {
    Type::String
}

pub(super) fn vec_ty() -> Type {
    Type::ADT(
        FQTypeName::new("primitives".into(), "Vec".into()),
        vec![Type::Int],
    )
}

pub(super) fn var(name: &str, ty: &Type) -> Expr {
    Expr::Var {
        name: Symbol::from(name),
        span: span(),
        resolved_call: None,
        inferred_type: Some(Box::new(ty.clone())),
    }
}

pub(super) fn int(value: i64) -> Expr {
    Expr::IntLit {
        value,
        span: span(),
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// The control's branch value. An integer literal is not a binding, so the
/// branch-forward rule never increments it, and it emits no RC operation of
/// its own. The fixture is compiled only, never run.
fn not_a_binding() -> Expr {
    int(0)
}

/// `(go 0 o <x_arg> <y_arg>)` in tail position.
pub(super) fn tail_call(x_arg: Expr, y_arg: Expr, heap: &Type) -> Expr {
    Expr::Apply {
        callee: Box::new(var(
            GO,
            &Type::Fn(
                vec![Type::Int, option_ty(), heap.clone(), heap.clone()],
                Box::new(Type::Int),
            ),
        )),
        args: vec![int(0), var("o", &option_ty()), x_arg, y_arg],
        span: span(),
        resolved_call: None,
        inferred_type: Some(Box::new(Type::Int)),
    }
}

/// `(vec-push <source> 1)`, resolved to the builtin in-place COW op.
pub(super) fn vec_push(source: &str) -> Expr {
    Expr::Apply {
        callee: Box::new(var("vec-push", &Type::Int)),
        args: vec![var(source, &vec_ty()), int(1)],
        span: span(),
        resolved_call: Some(Box::new(ResolvedCall::BuiltinFn {
            name: "vec-push".into(),
        })),
        inferred_type: Some(Box::new(vec_ty())),
    }
}

pub(super) fn go_defn(body: Expr) -> Defn {
    Defn {
        name: Symbol::from(GO),
        docstring: None,
        variants: vec![DefnVariant {
            params: ["n", "o", "x", "y"]
                .into_iter()
                .map(|p| (Symbol::from(p), None))
                .collect(),
            body,
            span: Span::SYNTHETIC,
        }],
        visibility: Visibility::Public,
        span: Span::SYNTHETIC,
    }
}

/// The tail-argument forms that yield a branch result, with the constructor
/// carriers a data-pattern arm needs.
#[derive(Clone, Copy, Debug)]
pub(super) enum Form {
    /// `(if n 0 <forwarded>)`
    If,
    /// `(match o [_ <forwarded>])`
    WildcardArm,
    /// `(match o [r <forwarded>])`
    VarPatternArm,
    /// `(match o [(Some s) <forwarded> None 0])`
    DataPatternArm,
}

const FORMS: [Form; 4] = [
    Form::If,
    Form::WildcardArm,
    Form::VarPatternArm,
    Form::DataPatternArm,
];

impl Form {
    pub(super) fn wrap(
        self,
        forwarded: Expr,
        heap: &Type,
        pattern_ctors: &mut HashMap<Span, FQSymbol>,
    ) -> Expr {
        let arm = |pattern, body| MatchArm {
            pattern,
            body,
            span: span(),
        };
        let arms = match self {
            Form::If => {
                return Expr::If {
                    cond: Box::new(var("n", &Type::Int)),
                    then_branch: Box::new(int(0)),
                    else_branch: Box::new(forwarded),
                    span: span(),
                    inferred_type: Some(Box::new(heap.clone())),
                };
            }
            Form::WildcardArm => vec![arm(Pattern::Wildcard { span: span() }, forwarded)],
            Form::VarPatternArm => vec![arm(
                Pattern::Var {
                    name: Symbol::from("r"),
                    span: span(),
                },
                forwarded,
            )],
            Form::DataPatternArm => {
                let mut ctor = |name: &str, bindings: Vec<Symbol>| {
                    let at = span();
                    pattern_ctors.insert(
                        at,
                        FQSymbol {
                            module: main_module(),
                            symbol: Symbol::from(name),
                        },
                    );
                    Pattern::Constructor {
                        name: SymbolRef::new(None, Symbol::from(name)),
                        bindings,
                        span: at,
                    }
                };
                let some = ctor("Some", vec![Symbol::from("s")]);
                let none = ctor("None", vec![]);
                vec![arm(some, forwarded), arm(none, int(0))]
            }
        };
        Expr::Match {
            scrutinee: Box::new(var("o", &option_ty())),
            arms,
            span: span(),
            compiler_generated: false,
            inferred_type: Some(Box::new(heap.clone())),
        }
    }
}

/// The site fact typecheck publishes for a top-level tail-argument `vec-push`:
/// its result transfers into the next iteration's slot and does not escape.
/// No COW decision depends on it (`ownership-codegen.md` §13.3, §13.7); the
/// cells that supply it pin that independence.
pub(super) fn tail_vec_push_does_not_escape(body: &mut MonoExpr) {
    match body {
        MonoExpr::Let { body, .. } => tail_vec_push_does_not_escape(body),
        MonoExpr::Apply { args, .. } => {
            for arg in args {
                if crate::compiler::vec_codegen::cow_site_source(arg).is_some()
                    && let MonoExpr::Apply { escapes, .. } = arg
                {
                    *escapes = Some(false);
                }
            }
        }
        _ => {}
    }
}

pub(super) fn no_site_facts(_: &mut MonoExpr) {}

/// Compile `go` through the production per-body seam and return its CLIF.
pub(super) fn compile(
    defn: &Defn,
    summary: Option<ModeSummary>,
    heap: &Type,
    pattern_ctors: &HashMap<Span, FQSymbol>,
    site_facts: fn(&mut MonoExpr),
) -> String {
    let mut jit = crate::jit::Jit::new_with_symbols(&[]).expect("JIT construction");
    let tables = crate::test_support::option_type_tables();
    crate::test_support::insert_user_fn_stub_typed(
        &mut tables.get_mut(&main_module()).expect("main table"),
        GO,
        &[Type::Int, option_ty(), heap.clone(), heap.clone()],
        Type::Int,
    );
    let resolved_targets = crate::test_support::call_carriers(defn.body(), &main_module(), &[GO]);
    crate::test_support::try_compile_defns_in_module_with_pattern_ctors(
        &[defn],
        &[summary],
        &[],
        &resolved_targets,
        pattern_ctors,
        &tables,
        main_module(),
        jit.jit_module(),
        &site_facts,
    )
    .unwrap_or_else(|e| panic!("compile go: {e}"))
    .pop()
    .expect("one compiled defn")
}

fn increments(clif: &str) -> usize {
    clif.matches("atomic_rmw.i64 add").count()
}

/// A slot row: the body around the forwarded tail argument, the binding the
/// branch forwards, the parameter modes and the heap type of `x` and `y`.
struct Row {
    name: &'static str,
    forwarded: &'static str,
    heap: Type,
    summary: Option<ModeSummary>,
    body: fn(Expr, &Type) -> Expr,
    site_facts: fn(&mut MonoExpr),
    expected: usize,
}

pub(super) fn x_borrowed() -> Option<ModeSummary> {
    Some(ModeSummary {
        param_modes: vec![Mode::Copy, Mode::Owned, Mode::Borrowed, Mode::Owned],
        ..ModeSummary::default()
    })
}

/// The increments the forwarded binding adds on the forwarding branch.
fn forward_increments(row: &Row, form: Form) -> usize {
    let mut subject_ctors = HashMap::new();
    let subject_arg = form.wrap(var(row.forwarded, &row.heap), &row.heap, &mut subject_ctors);
    let subject = go_defn((row.body)(subject_arg, &row.heap));
    let mut control_ctors = HashMap::new();
    let control_arg = form.wrap(not_a_binding(), &row.heap, &mut control_ctors);
    let control = go_defn((row.body)(control_arg, &row.heap));

    let subject_clif = compile(
        &subject,
        row.summary.clone(),
        &row.heap,
        &subject_ctors,
        row.site_facts,
    );
    let control_clif = compile(
        &control,
        row.summary.clone(),
        &row.heap,
        &control_ctors,
        row.site_facts,
    );
    increments(&subject_clif)
        .checked_sub(increments(&control_clif))
        .unwrap_or_else(|| {
            panic!(
                "{} via {form:?}: the forward removed an increment\n--- subject ---\n\
                 {subject_clif}\n--- control ---\n{control_clif}",
                row.name
            )
        })
}

fn assert_rows(rows: &[Row]) {
    let mut failures = Vec::new();
    for row in rows {
        for form in FORMS {
            let got = forward_increments(row, form);
            if got != row.expected {
                failures.push(format!(
                    "{} via {form:?}: {got} increments, expected {}",
                    row.name, row.expected
                ));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

// spec: spec/12-runtime.md §12.3.1 — a frame-owned parameter forwarded bare
// through a branch of a tail argument gains exactly one increment on that
// branch, so the slot release before the jump leaves the next iteration an
// owned reference (ACT-1021 D1, C-PT, C-M). Promotion and a consuming in-place
// COW argument do not change that.
//
// defect: class=uaf locus=crates/cranelisp-backend/src/compiler/fn_compiler.rs::tail_flush_will_dec found=S122 owner=/dev
#[test]
fn a_frame_owned_parameter_forwarded_through_a_branch_is_incremented_once() {
    // The COW row measures a consumed parameter only while the flush really
    // skips `x`: reordering the arguments makes the push copy-only, which
    // restores exactly that one flush release (a glue call, not an inline
    // decrement).
    let forward_x = || Form::If.wrap(var("x", &vec_ty()), &vec_ty(), &mut HashMap::new());
    let flush_releases = |body| {
        let clif = compile(
            &go_defn(body),
            None,
            &vec_ty(),
            &HashMap::new(),
            no_site_facts,
        );
        crate::test_support::count_release_ops(&clif) - clif.matches("atomic_rmw.i64 sub").count()
    };
    assert_eq!(
        flush_releases(tail_call(vec_push("x"), forward_x(), &vec_ty())),
        flush_releases(tail_call(forward_x(), vec_push("x"), &vec_ty())) + 1,
        "precondition: the COW row's `x` is consumed, so the parameter flush skips it"
    );

    assert_rows(&[
        Row {
            name: "Owned parameter into its own slot",
            forwarded: "x",
            heap: string_ty(),
            summary: None,
            body: |arg, heap| tail_call(arg, var("y", heap), heap),
            site_facts: no_site_facts,
            expected: 1,
        },
        Row {
            name: "Owned parameter moved and forwarded into another slot",
            forwarded: "x",
            heap: string_ty(),
            summary: None,
            body: |arg, heap| tail_call(var("x", heap), arg, heap),
            site_facts: no_site_facts,
            expected: 1,
        },
        Row {
            name: "promoted Borrowed parameter into its own slot",
            forwarded: "x",
            heap: string_ty(),
            summary: x_borrowed(),
            body: |arg, heap| tail_call(arg, var("y", heap), heap),
            site_facts: no_site_facts,
            expected: 1,
        },
        Row {
            name: "parameter consumed by an in-place COW argument",
            forwarded: "x",
            heap: vec_ty(),
            summary: None,
            body: |arg, heap| tail_call(arg, vec_push("x"), heap),
            site_facts: no_site_facts,
            expected: 1,
        },
    ]);
}

// spec: spec/12-runtime.md §12.3.1 — a `let` value that a top-level `Var`
// moves and a branch also forwards needs its own increment on the branch: the
// move takes the slot's reference. This row was already protected; a key of
// "released at the jump" would drop it.
#[test]
fn a_moved_let_value_also_forwarded_through_a_branch_is_incremented_once() {
    assert_rows(&[Row {
        name: "owned let value moved and forwarded",
        forwarded: "v",
        heap: string_ty(),
        summary: None,
        body: |arg, heap| Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::StringLit {
                    value: "v".into(),
                    span: span(),
                    inferred_type: Some(Box::new(Type::String)),
                },
            )],
            body: Box::new(tail_call(var("v", heap), arg, heap)),
            span: span(),
            inferred_type: Some(Box::new(Type::Int)),
        },
        site_facts: no_site_facts,
        expected: 1,
    }]);
}

// spec: spec/12-runtime.md §12.3.1 (NEGATIVE) — a slot the frame does not own
// gains no increment. These rows pin emission only; they make no balance claim
// (L4 in `ownership-codegen.md` §13.3 is the open balance question).
//
// - A Borrowed parameter that its own position carries forward bare is not
//   promoted, and the caller owns it.
// - A `let` binder that aliases `y` is borrowed. It shadows the parameter `x`,
//   which the frame promoted; the rule reads the binder's own slot, not the
//   promotion recorded under the shared name.
#[test]
fn a_slot_the_frame_does_not_own_is_not_incremented_neg() {
    assert_rows(&[
        Row {
            name: "Borrowed, unpromoted parameter into another slot",
            forwarded: "x",
            heap: string_ty(),
            summary: x_borrowed(),
            body: |arg, heap| tail_call(var("x", heap), arg, heap),
            site_facts: no_site_facts,
            expected: 0,
        },
        Row {
            name: "borrowed let binder shadowing a promoted parameter",
            forwarded: "x",
            heap: string_ty(),
            summary: x_borrowed(),
            body: |arg, heap| Expr::Let {
                bindings: vec![(Symbol::from("x"), var("y", heap))],
                body: Box::new(tail_call(arg, var("y", heap), heap)),
                span: span(),
                inferred_type: Some(Box::new(Type::Int)),
            },
            site_facts: no_site_facts,
            expected: 0,
        },
    ]);
}
