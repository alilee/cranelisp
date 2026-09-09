// M1 — the `ScopeChain` matrix (`design/backend/binding-scope.md` §6).
//
// Every scenario is expressed as ONE shared check parameterised by the pop
// operation, then applied twice: to the production `pop_frame`, which must
// satisfy it, and to `pop_frame_by_name` — the pre-repair delete-by-name pop,
// planted here as the fault — which must violate it. That is the arming proof
// in both directions (root `CLAUDE.md` §Assurance): the check is shown to fire
// on the fault, and the rename control shows it stays silent without it.

use super::*;

fn sym(s: &str) -> Symbol {
    Symbol::from(s)
}

fn var(i: u32) -> Variable {
    Variable::from_u32(i)
}

/// The PLANTED FAULT: the pre-repair `pop_scope`, which removed every binder
/// bearing a name the popped frame introduced — including an outer binder that
/// merely shares the name. Test-only; production pops the frame and nothing else.
fn pop_frame_by_name(chain: &mut ScopeChain) {
    let Some(frame) = chain.frames.pop() else {
        return;
    };
    for slot in &frame {
        for outer in chain.frames.iter_mut() {
            outer.retain(|s| s.name != slot.name);
        }
    }
}

/// Scenario 1 — shadow, then leave the shadowing scope. The outer binder must
/// still denote its OWN variable and type.
fn check_outer_binder_survives_inner_shadow(pop: fn(&mut ScopeChain)) -> Result<(), String> {
    let mut chain = ScopeChain::new();
    chain.push_frame();
    chain.bind(sym("b"), var(1), Some(Type::String));
    chain.push_frame();
    chain.bind(sym("b"), var(2), Some(Type::Int));
    pop(&mut chain);

    match chain.resolve(&sym("b")) {
        None => Err("the outer binder `b` is gone after the inner scope closed".into()),
        Some(slot) if slot.var() != var(1) => Err(format!(
            "`b` resolves to {:?}, not the outer binder",
            slot.var()
        )),
        Some(slot) if slot.ty() != Some(&Type::String) => Err(format!(
            "`b`'s type is {:?}, not the outer binder's",
            slot.ty()
        )),
        Some(_) => Ok(()),
    }
}

/// Scenario 2 — the rename control: one identifier apart, nothing shadows. Both
/// pops must satisfy it, which is what proves the scenario-1 failure is caused
/// by shadowing and not by popping.
fn check_unshadowed_outer_binder_survives(pop: fn(&mut ScopeChain)) -> Result<(), String> {
    let mut chain = ScopeChain::new();
    chain.push_frame();
    chain.bind(sym("b"), var(1), Some(Type::String));
    chain.push_frame();
    chain.bind(sym("c"), var(2), Some(Type::Int));
    pop(&mut chain);

    match chain.resolve(&sym("b")) {
        Some(slot) if slot.var() == var(1) => Ok(()),
        other => Err(format!("`b` should be untouched, resolved to {other:?}")),
    }
}

#[test]
// spec: spec/04-expressions.md §4.3 — an inner binder shadows; leaving its scope
// restores nothing because the outer binder's facts were never touched.
fn popping_a_shadowing_frame_leaves_the_outer_binder_intact() {
    assert_eq!(
        check_outer_binder_survives_inner_shadow(ScopeChain::pop_frame),
        Ok(())
    );
}

#[test]
// spec: spec/04-expressions.md §4.3 — arming: the same check FIRES against the
// pre-repair delete-by-name pop.
fn the_shadow_check_detects_a_delete_by_name_pop() {
    assert!(
        check_outer_binder_survives_inner_shadow(pop_frame_by_name).is_err(),
        "planted delete-by-name pop went undetected — the check cannot fire"
    );
}

#[test]
// spec: spec/04-expressions.md §4.3 — the rename control: no shadow, no loss.
fn a_non_shadowing_inner_binder_leaves_the_outer_binder_intact() {
    assert_eq!(
        check_unshadowed_outer_binder_survives(ScopeChain::pop_frame),
        Ok(())
    );
}

#[test]
// spec: spec/04-expressions.md §4.3 — arming, negative leg: the planted fault is
// SILENT when no name is shadowed, so scenario 1's failure is attributable to
// shadowing alone.
fn the_delete_by_name_pop_is_silent_without_a_shadow() {
    assert_eq!(
        check_unshadowed_outer_binder_survives(pop_frame_by_name),
        Ok(())
    );
}

#[test]
// spec: spec/04-expressions.md §4.3 — two binders of one name in one binding
// vector are two slots; each owns its own variable, type and release obligation.
fn two_binders_of_one_name_in_one_frame_are_two_slots() {
    let mut chain = ScopeChain::new();
    chain.push_frame();
    chain.bind(sym("s"), var(1), Some(Type::String));
    chain.bind(sym("s"), var(2), Some(Type::Int));

    let frame = chain.innermost_frame();
    assert_eq!(
        frame.len(),
        2,
        "the displaced binder must still be in the frame"
    );
    assert_eq!(frame[0].var(), var(1));
    assert_eq!(frame[0].ty(), Some(&Type::String));
    assert_eq!(frame[1].var(), var(2));

    let resolved = chain.resolve(&sym("s")).expect("`s` is bound");
    assert_eq!(resolved.var(), var(2), "a name denotes the LATEST binder");
    assert_eq!(resolved.ty(), Some(&Type::Int));

    // The return-value skip is a SLOT reference: it names the second binder, so
    // the displaced first binder keeps its own release obligation.
    let skip = chain
        .resolve_ref_in_innermost_frame(&sym("s"))
        .expect("`s` is bound in this frame");
    assert_eq!(chain.slot(skip).map(BinderSlot::var), Some(var(2)));
}

#[test]
// spec: spec/12-runtime.md §12.3.1 — a direct tail `Var` resolves to one live
// binder slot. A local shadow wins over the parameter, and the latest same-frame
// binder wins over its displaced predecessor.
fn tail_resolution_selects_one_exact_live_slot() {
    let mut chain = ScopeChain::new();
    chain.bind(sym("x"), var(0), Some(Type::String));
    chain.push_frame();
    chain.bind(sym("x"), var(1), Some(Type::String));
    chain.bind(sym("x"), var(2), Some(Type::String));

    let transferred = chain.resolve_slot_ref(&sym("x")).expect("live x slot");
    assert_eq!(chain.slot(transferred).map(BinderSlot::var), Some(var(2)));
    assert_ne!(
        transferred,
        chain.slot_ref(0, 0).expect("parameter slot"),
        "a local x must not transfer the parameter x"
    );
    assert_ne!(
        transferred,
        chain.slot_ref(1, 0).expect("displaced local slot"),
        "the displaced same-name slot remains releaseable"
    );
}

#[test]
// spec: spec/12-runtime.md §12.3.1 — the frame-release path keys on the slot, so
// a duplicate name yields one release obligation per binder, not one per name.
fn a_duplicate_name_frame_yields_one_release_obligation_per_binder() {
    let mut chain = ScopeChain::new();
    chain.push_frame();
    chain.bind(sym("s"), var(1), Some(Type::String));
    chain.bind(sym("s"), var(2), Some(Type::String));

    let heap_slots: Vec<Variable> = chain
        .innermost_frame()
        .iter()
        .filter(|slot| slot.ty() == Some(&Type::String))
        .map(BinderSlot::var)
        .collect();
    assert_eq!(heap_slots, vec![var(1), var(2)]);
}

#[test]
// spec: spec/04-expressions.md §4.3 — a body-local binder shadows a captured
// name for its extent, and the capture is denoted again once that frame closes.
// The capture is never a scope slot, so no body frame can release it.
fn a_capture_is_shadowed_by_a_local_and_survives_it() {
    let mut captures = CaptureEnv::new();
    captures.insert(sym("b"), var(9), Some(Type::String));
    let mut chain = ScopeChain::new();

    let denotes = |chain: &ScopeChain, captures: &CaptureEnv| {
        resolve_binding(chain, captures, &sym("b")).map(Binding::var)
    };

    assert_eq!(
        denotes(&chain, &captures),
        Some(var(9)),
        "no local binds `b` yet"
    );

    chain.push_frame();
    chain.bind(sym("b"), var(3), Some(Type::Int));
    assert_eq!(
        denotes(&chain, &captures),
        Some(var(3)),
        "the local wins while live"
    );
    assert!(
        chain.innermost_frame().len() == 1,
        "the capture must not have become a scope slot"
    );

    chain.pop_frame();
    assert_eq!(
        denotes(&chain, &captures),
        Some(var(9)),
        "the capture survives"
    );
}

#[test]
// spec: spec/12-runtime.md §12.3.1 — the borrowed mark is a property of a
// BINDER: an inner owned binder of a borrowed name is not borrowed, and the
// outer borrowed binder recovers its mark when that frame closes.
fn the_borrowed_mark_belongs_to_the_binder_not_the_name() {
    let mut chain = ScopeChain::new();
    chain.push_frame();
    chain.bind(sym("v"), var(1), Some(Type::String));
    chain.mark_borrowed(&sym("v"));
    assert!(chain.is_borrowed(&sym("v")));

    chain.push_frame();
    chain.bind(sym("v"), var(2), Some(Type::String));
    assert!(
        !chain.is_borrowed(&sym("v")),
        "the inner OWNED binder is not borrowed"
    );

    chain.pop_frame();
    assert!(
        chain.is_borrowed(&sym("v")),
        "the outer binder keeps its own mark"
    );
}

#[test]
// spec: spec/12-runtime.md §12.3.1 — a borrowed parameter resolves through the
// parameter frame, and an unbound name is never borrowed. (Rehomed from
// `fn_compiler::resolve_borrowed_is_innermost_binding_shadow_aware`, FIXME 0692:
// the invariant is unchanged; the structure that carries it moved.)
fn a_borrowed_parameter_resolves_and_an_unbound_name_does_not() {
    let mut chain = ScopeChain::new();
    chain.bind(sym("v"), var(0), Some(Type::String));
    chain.mark_borrowed(&sym("v"));

    assert!(chain.is_borrowed(&sym("v")));
    assert!(
        !chain.is_borrowed(&sym("q")),
        "an unbound name is not borrowed"
    );
}

#[test]
// spec: spec/12-runtime.md §12.3.1 — a same-frame rebinding does not inherit the
// displaced binder's borrowed mark.
fn a_same_frame_rebinding_does_not_inherit_the_borrowed_mark() {
    let mut chain = ScopeChain::new();
    chain.push_frame();
    chain.bind(sym("v"), var(1), Some(Type::String));
    chain.mark_borrowed(&sym("v"));
    chain.bind(sym("v"), var(2), Some(Type::String));

    assert!(
        !chain.is_borrowed(&sym("v")),
        "the second binder owns its value"
    );
    assert!(
        chain.innermost_frame()[0].is_borrowed(),
        "the displaced binder keeps its own mark"
    );
}

#[test]
// spec: spec/04-expressions.md §4.3 — frame classification is by frame, so the
// parameter frame and the let frames stay distinguishable per binder.
fn frame_classification_distinguishes_the_parameter_frame() {
    let mut chain = ScopeChain::new();
    chain.bind(sym("p"), var(0), Some(Type::String));
    chain.push_frame();
    chain.bind(sym("p"), var(1), Some(Type::Int));

    assert!(chain.param_frame_binds(&sym("p")));
    assert!(chain.let_frames_bind(&sym("p")));
    assert!(chain.resolve_ref_in_innermost_frame(&sym("p")).is_some());
    assert_eq!(chain.resolve_indexed(&sym("p")).map(|(i, _)| i), Some(1));
    chain.pop_frame();
    assert_eq!(chain.resolve_indexed(&sym("p")).map(|(i, _)| i), Some(0));
}
