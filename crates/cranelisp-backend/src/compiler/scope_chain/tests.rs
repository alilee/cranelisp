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
// vector are two slots; a name denotes the latest.
fn two_binders_of_one_name_in_one_frame_are_two_slots() {
    let mut chain = ScopeChain::new();
    chain.push_frame();
    chain.bind(sym("s"), var(1), Some(Type::String));
    chain.bind(sym("s"), var(2), Some(Type::Int));

    let resolved = chain.resolve(&sym("s")).expect("`s` is bound");
    assert_eq!(resolved.var(), var(2), "a name denotes the LATEST binder");
    assert_eq!(resolved.ty(), Some(&Type::Int));

    // The displaced binder is still a slot: popping nothing else, it is not
    // reachable by name, but the frame kept it rather than overwriting it.
    assert_eq!(chain.frames.last().map(Vec::len), Some(2));
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
    assert_eq!(
        chain.frames.last().map(Vec::len),
        Some(1),
        "the capture must not have become a scope slot"
    );

    chain.pop_frame();
    assert_eq!(
        denotes(&chain, &captures),
        Some(var(9)),
        "the capture survives"
    );
}
