// nondispatchable_trait_method_0709.rs — S114 Phase-6b, FIXME 0709 pin batch.
//
// spec/07-traits.md §7.1.1 (occurrence rule) settles the fork with NO user
// question: a trait method that mentions the implementing type NOWHERE — no
// parameter of the implementing type, no `self` in return position — "has nothing
// to dispatch on and MUST be rejected for 'no occurrence of the implementing type
// to dispatch on.'" `(deftrait Zeroable (zed [] Int))` is exactly that malformed
// form (empty params, CONCRETE `Int` return, no `self`). Today it is SILENTLY
// ACCEPTED at declaration, and the downstream `(zed)` call leaks past the
// typecheck gate to a raw `codegen error … undefined function: zed` — the F-D2
// check-gate-leak SYMPTOM surviving in the degenerate corner (/repl S114 Phase-6a).
//
// The well-formed return-dispatch twin `(zed [] self)` (spec §7.1.1's own example —
// `self` in return position SATISFIES the occurrence rule) MUST stay accepted; it
// is the GREEN control below. Fix = S115 typecheck: the `check_form_register`
// TraitDecl arm gains occurrence-rule enforcement (none exists today; the only
// §7.1.1-adjacent text is a comment at `traits/impl_check.rs:225`). Both REDs flip
// together on that fix — (ii) is a consequence of (i).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn repl_prims(lines: &str) -> String {
    let out = Cranelisp::new()
        .repl()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .stdin(lines)
        .output();
    format!("{}{}", out.stdout, out.stderr)
}

// (i) RED — the malformed no-occurrence declaration MUST be rejected AT the
// declaration with the spec-pinned diagnostic reason. Today the deftrait is
// accepted silently (`:user/Zeroable ; deftrait`) — no occurrence check exists.
// spec: spec/07-traits.md §7.1.1 — a method mentioning the implementing type
// nowhere MUST be rejected for "no occurrence of the implementing type to
// dispatch on."
// defect: class=silent-accept locus=crates/cranelisp-typecheck check_form_register TraitDecl arm — §7.1 occurrence rule unenforced found=S114 owner=/dev
#[test]
fn nondispatchable_method_rejected_at_declaration_with_occurrence_reason() {
    let combined = repl_prims("(deftrait Zeroable (zed [] Int))\n");
    assert!(
        combined.contains("no occurrence of the implementing type"),
        "`(deftrait Zeroable (zed [] Int))` (concrete return, no self) MUST be \
         rejected at declaration with the §7.1.1 reason 'no occurrence of the \
         implementing type'; today it is silently accepted. Got:\n{combined}"
    );
}

// (ii) RED negative — driving the no-occurrence method's call MUST NOT surface a
// raw codegen `undefined function`; the fault is decidable at declaration (i), so
// it must never reach codegen. Today `(zed)` leaks `codegen error … undefined
// function: zed`. Flips green as a consequence of (i)'s declaration-time reject.
// spec: spec/07-traits.md §7.1.1 — a decidable no-occurrence fault is rejected at
// the typecheck gate, never as a codegen-phase symbol miss (§7.11.2 intent).
// defect: class=silent-accept locus=crates/cranelisp-typecheck check_form_register TraitDecl arm — §7.1 occurrence rule unenforced (leak surfaces as codegen undefined function) found=S114 owner=/dev
#[test]
fn nondispatchable_method_call_neg_no_codegen_undefined_function() {
    let combined = repl_prims("(deftrait Zeroable (zed [] Int))\n(zed)\n");
    assert!(
        !combined.contains("undefined function"),
        "the no-occurrence method call MUST NOT leak a codegen `undefined \
         function` (the fault is decidable at declaration); today it does. \
         Got:\n{combined}"
    );
}

// (iii) GREEN control — the well-formed return-type-dispatched twin `(zed [] self)`
// (renamed `z`/`Zero` to keep it a distinct trait from the RED cells) SATISFIES the
// occurrence rule (`self` in return position). It stays accepted, and a concrete
// ascription `:Int (z)` dispatches to the impl → 0. Guards the fix's boundary: the
// occurrence-rule reject must NOT over-reach into legitimate return-dispatch.
// spec: spec/07-traits.md §7.1.1 — a `self`-return method satisfies the occurrence
// rule and is resolved by a call-site ascription (§3.3.3).
#[test]
fn return_dispatch_self_method_control_stays_accepted_green() {
    let combined = repl_prims(
        "(deftrait Zero (z [] self))\n\
         (impl Zero Int (defn z [] 0))\n\
         :Int (z)\n",
    );
    assert!(
        combined.contains(":primitives/Int 0"),
        "the well-formed `(z [] self)` return-dispatch twin MUST stay accepted and \
         `:Int (z)` MUST dispatch to the Int impl → 0. Got:\n{combined}"
    );
    for leak in ["undefined function", "no occurrence", "codegen error"] {
        assert!(
            !combined.contains(leak),
            "the well-formed return-dispatch control MUST NOT surface `{leak}`. \
             Got:\n{combined}"
        );
    }
}

// (iv) GREEN over-reach control (S115 W1 delta) — a bare-PARAM method with a
// CONCRETE return `(size [x] Int)` SATISFIES the occurrence rule (the unannotated
// param `x` defaults to the implementing type — an occurrence via parameter), so it
// MUST stay accepted. This guards the design's explicit boundary (traits.md §2 /
// spec §7.1.1): "Do NOT reject on concrete return alone; reject only on the
// CONJUNCTION no-param-occurrence ∧ no-self-return." The two RED cells above assert
// the reject FIRES on the malformed no-occurrence form; this cell asserts it does
// NOT over-reach to a bare-param-with-concrete-return method. Born-green today (no
// occurrence check exists) and MUST STAY green through the W4 fix.
// spec: spec/07-traits.md §7.1.1 — a bare-param method satisfies the occurrence rule
// even with a concrete return; the reject must not fire on concrete-return alone.
#[test]
fn bare_param_concrete_return_method_control_stays_accepted_green() {
    let combined = repl_prims("(deftrait Sizeable (size [x] Int))\n");
    assert!(
        !combined.to_lowercase().contains("error"),
        "`(deftrait Sizeable (size [x] Int))` has a bare param `x` (= implementing \
         type, an occurrence) and MUST stay accepted — the occurrence-rule reject \
         MUST NOT over-reach to a concrete-return-with-param method. Got:\n{combined}"
    );
    assert!(
        !combined.contains("no occurrence"),
        "the bare-param concrete-return method MUST NOT surface the no-occurrence \
         reject (occurrence is carried by the bare param). Got:\n{combined}"
    );
}
