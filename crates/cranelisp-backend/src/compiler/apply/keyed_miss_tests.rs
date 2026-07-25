//! KC-N call-seam keyed-miss negatives (S111 R2, `backend-keyed-consumer.md`
//! §9 / audit `cranelisp-backend-s110.md` §2.6 risk 1). The design's own §9
//! acceptance surface names the keyed-read hard-miss families as *pinned*
//! `CodegenError` message families; before this file NO test asserted any of
//! them, so a regression to a silent `None`-fallback would have been caught by
//! nothing (Rev-2 no-soft-fallback; Principle 18).
//!
//! This is the CALL seam (`compile_direct_call`, `apply.rs`): the ONE keyed
//! fetch (`entry_at`) is reached after locals are filtered upstream
//! (`compile_var_apply`). Two distinct families surface here:
//!   KC-N1 — carrier-`None` on a table-reference call (`resolved_target: None`).
//!   KC-N2 — `Some(fq)` fetching nothing (an entry-miss on a present carrier).
//!
//! Both pin ALREADY-CORRECT S110 behaviour — the seam hard-fails today; these
//! tests should pass on write. The value-seam siblings (KC-N3..N6) live in
//! `compiler/control_flow/fn_as_value/keyed_miss_tests.rs`.

use crate::test_support::*;
use cranelisp_types::FQSymbol;

/// Build a `caller` defn whose body is `(helper)` — an `Apply` of a bare `Var`
/// callee with `resolved_call: None`, so dispatch reaches
/// `compile_var_apply` → `compile_direct_call` (the keyed call seam). The
/// callee `Var` carries `callee_span`; whether a carrier exists for that span
/// is controlled by the `resolved_targets` map the caller passes.
fn caller_calling(callee_name: &str, callee_span: Span, apply_span: Span) -> Defn {
    Defn {
        name: Symbol::from("caller"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            body: Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from(callee_name),
                    span: callee_span,
                    resolved_call: None,
                    inferred_type: None,
                }),
                args: vec![],
                span: apply_span,
                resolved_call: None,
                inferred_type: None,
            },
            span: Span::new(0, 100),
        }],
        visibility: Visibility::Public,
        span: Span::new(0, 100),
    }
}

// spec: design/arch/backend-keyed-consumer.md §1.2/§1.3 — carrier-None on a
// table-reference call is a hard CodegenError (Rev-2 no-soft-fallback). KC-N1.
#[test]
fn kc_n1_call_seam_carrier_none_hard_errors() {
    let callee_span = Span::new(200, 206);
    let caller = caller_calling("helper", callee_span, Span::new(199, 207));

    let user = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        // NO carrier recorded for `helper`'s callee span — the keying-drift the
        // hard-miss family exists to catch.
        let empty_targets: HashMap<Span, FQSymbol> = HashMap::new();
        st.insert(
            caller.name.clone(),
            make_def_entry_slot_with_targets(caller.clone(), 0, &empty_targets),
        );
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let result = compile_to_module(
        user.clone(),
        std::slice::from_ref(&caller.name),
        &tables,
        &mut obj,
        true,
    );
    let err = match result {
        Ok(_) => panic!(
            "a table-reference call with NO resolved_target carrier MUST hard-error \
             (Rev-2 §1.2); a clean compile means a silent None-fallback was reintroduced"
        ),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains("no resolved_target carrier") && msg.contains("helper"),
        "carrier-None call miss must name the reference + the missing carrier; got: {msg}"
    );
}

// spec: design/arch/backend-keyed-consumer.md §1.3 — Some(fq) fetching no
// symbol-table entry is a hard CodegenError (entry-miss). KC-N2.
#[test]
fn kc_n2_call_seam_entry_miss_hard_errors() {
    let callee_span = Span::new(300, 306);
    let caller = caller_calling("helper", callee_span, Span::new(299, 307));

    let user = ModuleFullPath::from("user");
    let tables = empty_tables();
    {
        let mut st = SymbolTable::new(user.clone());
        let _ = st.allocate_got_slot().expect("fresh table has free slots");
        // A carrier IS present, but it points at a symbol that does not exist in
        // any table — the entry-miss family.
        let mut targets: HashMap<Span, FQSymbol> = HashMap::new();
        targets.insert(
            callee_span,
            FQSymbol {
                module: user.clone(),
                symbol: Symbol::from("ghost"),
            },
        );
        st.insert(
            caller.name.clone(),
            make_def_entry_slot_with_targets(caller.clone(), 0, &targets),
        );
        tables.insert(user.clone(), st);
    }

    let mut obj = make_object_module();
    let result = compile_to_module(
        user.clone(),
        std::slice::from_ref(&caller.name),
        &tables,
        &mut obj,
        true,
    );
    let err = match result {
        Ok(_) => panic!(
            "a call whose resolved_target carrier fetches nothing MUST hard-error \
             (entry-miss §1.3); a clean compile means a silent fallback was reintroduced"
        ),
        Err(e) => e,
    };
    let msg = format!("{err:?}");
    assert!(
        msg.contains("fetched no symbol-table entry") && msg.contains("user/ghost"),
        "entry-miss call must name the dangling carrier FQ + the reference; got: {msg}"
    );
}
