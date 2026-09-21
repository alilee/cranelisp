//! S122 IOR-5 — an inline IO-combinator result is physically FRESH
//! (`design/backend/s122-closure.md` §8).
//!
//! `bind` / `select` / `race` / `sleep` resolve as `ResolvedCall::BuiltinFn` and
//! are lowered inline by `compile_builtin_fn_call`. Each lowering ALLOCATES a new
//! IO node at rc=1 and takes its operands under the consuming convention; the
//! node never returns an operand, so its result cannot alias a scope binding.
//!
//! Before the correction `value_provenance_with_calls` answered `OwnedTemporary`
//! for that `Apply` (`call_returns_owned_reference` is false for every `Some(_)`
//! carrier outside `SigDispatch`/`TraitMethod`), so `body_has_independent_result`
//! was false and `protect_return_value` retained the new node whenever the
//! exiting frame owned a heap binding. The caller releases that node exactly
//! once, so the retain stranded it and everything it owned. Observed in CLIF
//! before the fix (§8.4 step 1): an `atomic_rmw add` on the Bind node's own RC
//! word in `let1.cl`, and none in the binding-free `sib.cl`.
//!
//! Three tiers:
//!
//! 1. **Pure** — each of the four carriers classifies `Fresh`, directly and
//!    through the `let` that forwards it.
//! 2. **CLIF** — the IOR-5 shape itself (`sequence_io_ownership_tests`'s entry
//!    frame: a live `List` binding around a `bind` result) emits no retain on the
//!    Bind node's own RC word.
//! 3. **Controls** — a mixed join stays `NotOwnedHere` and KEEPS its protect
//!    (eliding it would free the binding's node on the binding arm: a UAF, the
//!    opposite polarity); `vec-get` and friends stay `OwnedTemporary` (an inline
//!    Vec op can return an existing element or an in-place COW source); and a
//!    `bind`-SPELLED `Apply` without the `BuiltinFn` carrier is not `Fresh` —
//!    identity is the carrier, never the spelling (Principle 24).

use super::IoCombinator;
use super::sequence_io_ownership_tests::{entry_defn, io_ownership_fixture, sequence_defn};
use crate::compiler::context::CtorValueShape;
use crate::compiler::fn_compiler::{ValueProvenance, value_provenance};
use crate::jit::Jit;
use crate::test_support::{compile_defns_in_module_with_pattern_ctors, sig_binding};
use cranelisp_types::{
    ApplyRef, ConcreteType, FQSymbol, ModuleFullPath, MonoExpr, ResolvedCall, Span, Symbol, VarRef,
};

/// Nothing here is a constructor — every verdict in this file comes from the
/// resolution carrier, which is exactly what the probeless gates also see.
fn no_ctor(_: &FQSymbol) -> Option<CtorValueShape> {
    None
}

fn local_var(name: &str) -> MonoExpr {
    MonoExpr::Var {
        resolution: VarRef::Local {
            binder: Symbol::from(name),
            binding_span: Span::SYNTHETIC,
        },
        name: Symbol::from(name),
        span: Span::SYNTHETIC,
        resolved_call: None,
        ty: ConcreteType::Int,
    }
}

/// An `Apply` whose callee is SPELLED `name`, carrying `resolved_call`. Keeping
/// the spelling and the carrier independent is what makes the negative controls
/// discriminating.
fn apply_spelled(name: &str, resolved_call: Option<ResolvedCall>) -> MonoExpr {
    MonoExpr::Apply {
        callee: Box::new(MonoExpr::Var {
            resolution: VarRef::Global(FQSymbol {
                module: ModuleFullPath::from("primitives"),
                symbol: Symbol::from(name),
            }),
            name: Symbol::from(name),
            span: Span::SYNTHETIC,
            resolved_call: None,
            ty: ConcreteType::Int,
        }),
        args: vec![local_var("p")],
        span: Span::SYNTHETIC,
        resolved_call: resolved_call.map(Box::new),
        dispatch: ApplyRef::ViaCallee,
        ty: ConcreteType::Int,
        escapes: None,
        confined: None,
        unique_static: None,
        provenance: None,
    }
}

fn builtin_apply(name: &str) -> MonoExpr {
    apply_spelled(
        name,
        Some(ResolvedCall::BuiltinFn {
            name: Symbol::from(name),
        }),
    )
}

/// `(let [p <heap>] body)` — the IOR-5 frame: a scope owning a heap binding, so
/// `protect_return_value` is live at its exit.
fn let_of(body: MonoExpr) -> MonoExpr {
    MonoExpr::Let {
        bindings: vec![(Symbol::from("p"), local_var("io"))],
        body: Box::new(body),
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
    }
}

// ---- 1. pure tier -------------------------------------------------------

// spec: design/backend/s122-closure.md §8.2 — each of the four inline IO
// combinators mints its node, so its result is `Fresh`; `let` forwards that,
// which is the frame the unbalanced protect retain was emitted in.
#[test]
fn every_io_combinator_carrier_is_fresh_through_a_let() {
    for name in ["bind", "select", "race", "sleep"] {
        let direct = value_provenance(&builtin_apply(name), &no_ctor);
        assert_eq!(
            direct,
            ValueProvenance::Fresh,
            "`{name}` allocates a new IO node and never returns an operand, so its \
             result is physically fresh — not `{direct:?}`"
        );
        let through_let = value_provenance(&let_of(builtin_apply(name)), &no_ctor);
        assert_eq!(
            through_let,
            ValueProvenance::Fresh,
            "`let` forwards provenance, so `(let [p …] ({name} …))` is `Fresh` — \
             not `{through_let:?}`"
        );
    }
}

// ---- 2. CLIF tier -------------------------------------------------------

/// Locate the Bind node — the allocation whose `+16` tag word is stored
/// `iconst.i64 2` (`IO_TAG_BIND`) — and report whether its OWN RC word
/// (`base+8`) receives an `atomic_rmw add`.
///
/// Same data-flow method as `sequence_io_ownership_tests::
/// bind_input_has_independent_retain`: the tag store names the node base, an
/// `iadd_imm base, 8` names its RC word, then any atomic add on that word. It
/// deliberately does NOT count `atomic_rmw` occurrences — the Bind node's
/// OPERAND retain is a different and correct one (the consuming convention), and
/// a count cannot tell the two apart.
fn bind_node_rc_word_is_retained(clif: &str) -> bool {
    let lines: Vec<&str> = clif.lines().collect();
    let tag_value_is_bind = |tag: &str| {
        lines
            .iter()
            .any(|definition| definition.trim() == format!("{tag} = iconst.i64 2"))
    };
    lines.iter().any(|line| {
        let Some((_, stored)) = line.trim().split_once("store notrap aligned ") else {
            return false;
        };
        let Some((tag, address)) = stored.split_once(", ") else {
            return false;
        };
        let address = address.split_whitespace().next().unwrap_or(address);
        let Some(base) = address.strip_suffix("+16") else {
            return false;
        };
        if !tag_value_is_bind(tag) {
            return false;
        }
        // Cranelift prints the type suffix only on the first use of a value in a
        // block, so the RC-word address appears as either spelling.
        let Some(rc_word) = lines.iter().find_map(|l| {
            let (word, rhs) = l.trim().split_once(" = ")?;
            (rhs == format!("iadd_imm.i64 {base}, 8") || rhs == format!("iadd_imm {base}, 8"))
                .then_some(word)
        }) else {
            return false;
        };
        lines
            .iter()
            .any(|l| l.contains("atomic_rmw.i64 add") && l.contains(rc_word))
    })
}

// spec: design/backend/s122-closure.md §8.4 step 2 — the IOR-5 shape. A frame
// owning a live `List` binding and returning a `bind` result must NOT retain the
// new Bind node: nothing balances that retain, so the node and its owned subtree
// strand.
#[test]
fn a_returned_bind_node_is_not_protected_by_a_live_heap_binding() {
    let sequence = sequence_defn();
    let entry = entry_defn();
    let fixture = io_ownership_fixture(&sequence, &entry);

    let mut jit = Jit::new_with_symbols(&[]).expect("JIT construction");
    let clifs = compile_defns_in_module_with_pattern_ctors(
        &[&sequence, &entry],
        &[],
        &fixture.targets,
        &fixture.pattern_ctors,
        &fixture.tables,
        fixture.module,
        jit.jit_module(),
    );
    assert!(
        !bind_node_rc_word_is_retained(&clifs[1]),
        "the returned Bind node must carry no protective retain — its caller \
         releases it exactly once, so this retain strands it:\n{}",
        clifs[1]
    );
}

// ---- 3. negative controls ----------------------------------------------

// spec: design/backend/s122-closure.md §8.2 (NEGATIVE, load-bearing) — joins stay
// conservative. `(let [p io] (if c (bind p k) p))` joins a fresh combinator arm
// with a scope binding, and a join is its WEAKEST arm, so the protect STANDS.
// Eliding it would free `p`'s node on the `p` arm: a use-after-free, the opposite
// polarity of the leak this correction removes.
#[test]
fn a_join_with_a_binding_arm_beside_a_combinator_stays_borrowed_neg() {
    let mixed = MonoExpr::If {
        cond: Box::new(local_var("c")),
        then_branch: Box::new(builtin_apply("bind")),
        else_branch: Box::new(local_var("p")),
        span: Span::SYNTHETIC,
        ty: ConcreteType::Int,
    };
    let joined = value_provenance(&let_of(mixed), &no_ctor);
    assert_eq!(
        joined,
        ValueProvenance::NotOwnedHere,
        "one scope-binding arm makes the whole join borrowed; per-arm protection \
         is out of scope, so the conservative protect must remain — got `{joined:?}`"
    );
}

// spec: design/backend/s122-closure.md §8.2 (NEGATIVE) — the rule does NOT extend
// to other builtins. An inline Vec op can return an existing element or an
// in-place COW source, so it keeps `OwnedTemporary`; a per-primitive result
// contract belongs to its owners and is not assumed here.
#[test]
fn a_non_combinator_builtin_stays_owned_temporary_neg() {
    for name in ["vec-get", "vec-set", "vec-push", "add-i64"] {
        let provenance = value_provenance(&builtin_apply(name), &no_ctor);
        assert_eq!(
            provenance,
            ValueProvenance::OwnedTemporary,
            "`{name}` is not an inline IO combinator — its result may alias an \
             argument, so it must keep `OwnedTemporary`, not `{provenance:?}`"
        );
        assert!(
            IoCombinator::of_call(Some(&ResolvedCall::BuiltinFn {
                name: Symbol::from(name),
            }))
            .is_none(),
            "`{name}` must not classify as an inline IO combinator"
        );
    }
}

// spec: design/backend/s122-closure.md §8.2 (NEGATIVE) — identity comes from the
// RESOLUTION CARRIER, never the callee's spelling (Principle 24). A user fn
// literally named `bind` must not inherit the combinator's freshness claim; that
// is the resolver-mirror class, and its wrong answer here is a use-after-free.
#[test]
fn a_bind_spelling_without_the_builtin_carrier_is_not_fresh_neg() {
    let no_carrier = apply_spelled("bind", None);
    assert_ne!(
        value_provenance(&no_carrier, &no_ctor),
        ValueProvenance::Fresh,
        "an `Apply` SPELLED `bind` with no `BuiltinFn` carrier is an ordinary call \
         that may return an aliased argument"
    );
    assert!(IoCombinator::of_call(None).is_none());

    let dispatched = sig_binding("user", "bind");
    assert_ne!(
        value_provenance(&apply_spelled("bind", Some(dispatched)), &no_ctor),
        ValueProvenance::Fresh,
        "a sig-dispatched user `bind` is not the inline combinator"
    );
    assert!(IoCombinator::of_call(Some(&sig_binding("user", "bind"))).is_none());
}
