//! KC-N value-seam keyed-miss negatives (S111 R2, `backend-keyed-consumer.md`
//! §9 / audit `cranelisp-backend-s110.md` §2.6 risk 1). The value-seam siblings
//! of `compiler/apply/keyed_miss_tests.rs`. Four cells:
//!   KC-N3 — carrier-`None` at the fn-as-value GOT seam (`emit_wrapper_call` →
//!           `got_entry_at(None)`, `fn_as_value.rs`): a genuine wrapper target
//!           whose carrier went missing.
//!   KC-N4 — `Some(fq)` fetching nothing at the same GOT seam (dangling
//!           carrier): the entry-miss family at the value read.
//!   KC-N5 — a slot-less `Polymorphic` template referenced as a value: the 0585
//!           loud backstop (`compile_var`, `literals.rs`).
//!   KC-N6 — the FALSE-POSITIVE FENCE: a local / lambda-param reference with a
//!           `None` carrier is NOT a miss (the `variables` check precedes any
//!           keyed read — §1.1 pinned invariant). A regression that treated
//!           None-on-a-local as a hard miss would break every closure body.
//!
//! REACHABILITY NOTE (test-authoring finding, S111 — reported to /sprint, NOT a
//! silent-fallback gap): the `emit_wrapper_call` GOT hard-miss
//! (`fn_as_value.rs:608`) is NOT reachable through a BARE value-position `Var`.
//! `compile_var` gates that path behind `is_known_function` (carrier callable OR
//! name in the current-unit `func_ids`), and `emit_wrapper_call` serves any
//! current-unit name from the direct-FuncId fast path (`func_ids.get`) — so a
//! bare same-unit ref never reaches the GOT read, and a bare cross-unit ref with
//! a missing carrier surfaces as `undefined variable` upstream. The GOT hard-miss
//! is reachable via the AUTO-CURRY wrapper (`(bar 1)` partial application), which
//! has no `is_known_function` gate and threads the Apply-span carrier straight
//! into `emit_wrapper_call`. KC-N3/N4 drive it that way — the same seam, its
//! genuinely-reachable input. The bare-value GOT read is a defensive backstop.
//!
//! KC-N3/N4/N5 pin ALREADY-CORRECT hard-fail behaviour (should pass on write);
//! KC-N6 pins that the fence does NOT over-fire (a clean compile).

use crate::test_support::*;
use cranelisp_types::{DefKind, FQSymbol, ParametricFn, ResolvedCall, Scheme, UserFnState};

/// A `useit` defn whose body is a bare value-position `Var` naming `ref_name`
/// at `ref_span`. Whether that span carries a `resolved_target` is controlled
/// by the `resolved_targets` map threaded into the entry.
fn value_ref_defn(ref_name: &str, ref_span: Span) -> Defn {
    Defn {
        name: Symbol::from("useit"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Var {
                name: Symbol::from(ref_name),
                span: ref_span,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 200),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 200),
    }
}

/// A `useit` defn whose body is the partial application `(<target> 1)` — an
/// `AutoCurry` of a 2-arg `target` with 1 arg applied, `trait_resolution: None`
/// (a plain-fn curry). This is the genuinely-reachable driver for the
/// `emit_wrapper_call` GOT hard-miss: the curry glue's `emit_curry_target_call`
/// falls to `emit_wrapper_call(target_fq)` with the Apply-span carrier, and
/// `target` is NOT a current-unit fn so the func_ids fast path is bypassed.
fn curry_partial_defn(target: &str, apply_span: Span) -> Defn {
    Defn {
        name: Symbol::from("useit"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from(target),
                    span: Span::new(apply_span.start + 1, apply_span.start + 4),
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 1,
                    span: Span::new(apply_span.end - 2, apply_span.end - 1),
                    inferred_type: Some(Box::new(Type::Int)),
                }],
                span: apply_span,
                resolved_call: Some(Box::new(ResolvedCall::AutoCurry {
                    target_name: Symbol::from(target),
                    applied_count: 1,
                    total_count: 2,
                    trait_resolution: None,
                })),
                inferred_type: Some(Box::new(Type::Fn(vec![Type::Int], Box::new(Type::Int)))),
            },
            span: Span::new(0, 200),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 200),
    }
}

// spec: design/arch/backend-keyed-consumer.md §1.2/§10 — a wrapper GOT read
// whose carrier is None is a hard CodegenError (no GOT-slot carrier). KC-N3.
#[test]
fn kc_n3_value_seam_carrier_none_hard_errors() {
    let apply_span = Span::new(400, 410);
    // `bar` is a 2-arg fn NOT compiled in this unit (cross-unit); the partial
    // application's Apply-span carrier is OMITTED — the keying-drift the
    // hard-miss family catches.
    let useit = curry_partial_defn("bar", apply_span);

    let user = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        // No carrier for the curry Apply span.
        let empty_targets: HashMap<Span, FQSymbol> = HashMap::new();
        st.insert(
            useit.name.clone(),
            make_def_entry_slot_with_targets(useit.clone(), 0, &empty_targets),
        );
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let result = compile_to_module(
        user.clone(),
        std::slice::from_ref(&useit.name),
        &tables,
        &mut obj,
        true,
    );
    let err = match result {
        Ok(_) => panic!(
            "a fn-as-value wrapper with NO GOT-slot carrier MUST hard-error \
             (Rev-2 §1.2); a clean compile means a silent fallback was reintroduced"
        ),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains("no GOT-slot carrier") && msg.contains("bar"),
        "value-seam carrier-None must name the reference + the missing carrier; got: {msg}"
    );
}

// spec: design/arch/backend-keyed-consumer.md §1.2/§10 — a wrapper GOT read
// whose carrier fetches no entry is a hard CodegenError (entry-miss). KC-N4.
#[test]
fn kc_n4_value_seam_entry_miss_hard_errors() {
    let apply_span = Span::new(500, 510);
    let useit = curry_partial_defn("bar", apply_span);

    let user = ModuleFullPath::from("user");
    let other = ModuleFullPath::from("other");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        // A carrier IS present but points at a non-existent symbol — the wrapper
        // GOT read fetches nothing.
        let mut targets: HashMap<Span, FQSymbol> = HashMap::new();
        targets.insert(
            apply_span,
            FQSymbol { module: other.clone(), symbol: Symbol::from("ghost") },
        );
        st.insert(
            useit.name.clone(),
            make_def_entry_slot_with_targets(useit.clone(), 0, &targets),
        );
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let result = compile_to_module(
        user.clone(),
        std::slice::from_ref(&useit.name),
        &tables,
        &mut obj,
        true,
    );
    let err = match result {
        Ok(_) => panic!(
            "a fn-as-value wrapper whose carrier fetches nothing MUST hard-error \
             (entry-miss §1.3); a clean compile means a silent fallback was reintroduced"
        ),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains("no GOT-slot carrier") && msg.contains("bar"),
        "value-seam entry-miss must name the reference; got: {msg}"
    );
}

// spec: design/arch/backend-keyed-consumer.md §7 leg 2 (0585) — a slot-less
// Polymorphic template referenced in value position is the loud backstop, NOT
// a silent `undefined variable` leak. KC-N5.
#[test]
fn kc_n5_value_seam_slotless_template_hard_errors() {
    let ref_span = Span::new(600, 603);
    let useit = value_ref_defn("gen", ref_span);

    let user = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        // `gen` is a determined generic template — slot-less, EXCLUDED from
        // codegen. It is present in the table (so the carrier fetches it) but is
        // NOT compiled (not in `names`, so not in func_ids).
        let param_variant = DefnVariant {
            params: vec![(Symbol::from("a"), None)],
            body: Expr::Var {
                name: Symbol::from("a"),
                span: Span::new(10, 11),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 20),
        };
        let scheme = Scheme {
            type_vars: vec![0u32],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
        };
        st.insert(
            Symbol::from("gen"),
            ModuleEntry::Def {
                scheme: scheme.clone(),
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![Symbol::from("a")],
                kind: Box::new(DefKind::UserFn {
                    fn_state: UserFnState::Polymorphic(Box::new(ParametricFn {
                        variant: param_variant,
                        scheme,
                    })),
                }),
                callees: vec![],
                trait_origin: None,
                seq: 0,
                ast: None,
                codegen_view: None,
                code: None,
                value_use: false,
            },
        );
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        // The value ref DOES carry the template's storage key — the mint-that-
        // should-have-happened never did.
        let mut targets: HashMap<Span, FQSymbol> = HashMap::new();
        targets.insert(
            ref_span,
            FQSymbol { module: user.clone(), symbol: Symbol::from("gen") },
        );
        st.insert(
            useit.name.clone(),
            make_def_entry_slot_with_targets(useit.clone(), 1, &targets),
        );
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let names = vec![useit.name.clone()];
    let result = compile_to_module(user.clone(), &names, &tables, &mut obj, true);
    let err = match result {
        Ok(_) => panic!(
            "a slot-less Polymorphic template referenced as a value MUST hard-error \
             loudly (0585 §7 leg 2); a clean compile means the mono-mint gap leaked silently"
        ),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains("without a mono instance") && msg.contains("gen"),
        "slot-less-template value read must raise the precise 0585 message, not \
         `undefined variable`; got: {msg}"
    );
}

// spec: design/arch/backend-keyed-consumer.md §1.1 (row "Local variable / lambda
// param") — a local/lambda-param reference with a None carrier is NOT a keyed
// miss: the `variables` check precedes every keyed read. KC-N6 (the fence).
#[test]
fn kc_n6_local_none_carrier_is_not_a_miss() {
    // `identity [x] x` — the body Var `x` is a param (a local), referenced with
    // NO carrier. This is the overwhelmingly common shape (every closure body),
    // and must compile cleanly — the None carrier is never consulted for a local.
    let identity = Defn {
        name: Symbol::from("identity"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![(Symbol::from("x"), None)],
            body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(700, 701),
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(699, 702),
        }],
        visibility: Visibility::Public,
        span: Span::new(699, 702),
    };

    let user = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        st.insert(identity.name.clone(), make_def_entry_slot(identity.clone(), 0));
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let result = compile_to_module(
        user.clone(),
        std::slice::from_ref(&identity.name),
        &tables,
        &mut obj,
        true,
    );
    assert!(
        result.is_ok(),
        "a local/lambda-param reference with a None carrier is NOT a keyed miss \
         (§1.1 locals-before-keyed-read); it must compile cleanly. A hard-miss here \
         would be a false positive breaking every closure body."
    );
}

// spec: design/arch/typed-resolution-carrier.md §2.7.2 (unit obligation 4) — the
// NEGATIVE twin of KC-N6. A `VarRef::Local` reference whose binder is ABSENT from
// the backend scope stack is a HARD invariant failure (Principle 18) carrying the
// binder IDENTITY — never the old silent "undefined variable". The `Local`
// constructor asserts typecheck bound this reference to a local, so a backend
// scope-stack miss is a producer/backend contract breach, not an unresolved name.
// defect: class=carrier-loss locus=crates/cranelisp-backend/src/compiler/literals.rs::compile_var found=S114 owner=/dev
#[test]
fn kc_varref_local_scope_stack_miss_is_hard_invariant_failure_with_binder() {
    // (defn useit [] ghost) — `ghost` is a free Var, NOT a param, so it is absent
    // from the backend `variables` scope stack. With no carrier threaded, the test
    // harness classifies the uncarried real-span Var as `VarRef::Local { binder:
    // "ghost" }`, so codegen reaches the Local scope-miss hard-fail — exactly the
    // producer/backend contract breach §2.7.2 requires be LOUD.
    let ghost = value_ref_defn("ghost", Span::new(500, 505));

    let user = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        st.insert(ghost.name.clone(), make_def_entry_slot(ghost.clone(), 0));
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let result = compile_to_module(
        user.clone(),
        std::slice::from_ref(&ghost.name),
        &tables,
        &mut obj,
        true,
    );
    let err = match result {
        Ok(_) => panic!(
            "a VarRef::Local reference absent from the backend scope stack MUST hard-error \
             (§2.7.2), not compile silently"
        ),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains("invariant violation")
            && msg.contains("VarRef::Local")
            && msg.contains("ghost"),
        "the hard-fail MUST name the binder identity (§2.7.2 unit obligation 4), \
         not surface a silent `undefined variable`; got: {msg}"
    );
}
