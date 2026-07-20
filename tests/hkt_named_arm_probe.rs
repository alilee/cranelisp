// hkt_named_arm_probe.rs — Track E repro-gated probe (s114-test-plan §6; FIXME
// 0590 resolver-mirror convergence). 0590 names a latent-defect SUSPICION: the
// `resolve_type_expr_hkt` / `resolve_type_expr_hkt_impl` resolvers'
// `Named` arms "never error at all — mint on double miss", so an UNKNOWN named
// type reaching an HKT trait-sig / impl-method type expression could be silently
// fabricated as a `Named` instead of rejected.
//
// PROBE OUTCOME (/testing, verified 2026-07-20; BD-A3 probe-first template): the
// suspicion does NOT reproduce e2e through the accessible shapes. An unknown named
// type in an HKT trait method signature — `:(Bogus a)` / `(Bogus b)` in a
// `(deftrait (Functor f) …)` sig — is REJECTED with a located `unknown type
// `Bogus`` diagnostic. The `_hkt` `Named` never-error arm is MASKED by the
// `form.rs::check_type_expr` pre-walk (which errors first), so no silently-wrong
// `Named` fallback is observable from source. Pinned as a BORN-GREEN fence: if the
// 0590 convergence (or any refactor) removes the pre-walk guard, the never-error
// arm would surface and flip this cell RED. Reported to /qa: the `_hkt`/`_hkt_impl`
// `Named`-arm defect, if real, is not e2e-reachable via these shapes — a UNIT-tier
// concern for the 0590 /design deployment (the pre-walk is the only barrier).
// Free-standing.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

fn run_prims(src: &str) -> helpers::e2e::CrOutput {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .output()
}

// Born-green fence: an unknown named type in an HKT trait method signature MUST be
// rejected as an `unknown type`, never silently fabricated as a `Named` by the
// `_hkt` resolver's never-error arm. `(deftrait (Functor f) (fmap [… :(Bogus a) x]
// (f b)))` uses the unknown `Bogus` in an HKT param type position. Guards the 0590
// convergence against exposing the never-error arm.
// spec: spec/07-traits.md §7.3.5 — an unknown named type in a (higher-kinded) trait
// signature/impl-target is a located `unknown type` error, not a minted `Named`.
#[test]
fn hkt_sig_unknown_named_type_rejected_not_silently_minted() {
    let out = run_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(Bogus a) x] (f b)))\n\
         (defn main [] (Pure 0))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        out.status.code() != Some(0) && c.contains("unknown type"),
        "an unknown named type `Bogus` in an HKT trait method signature MUST be a \
         located `unknown type` error — NOT silently fabricated as a `Named` by the \
         `_hkt` resolver's never-error arm (FIXME 0590); got exit {:?}:\n{c}",
        out.status.code()
    );
}

// Twin GREEN control: the same HKT trait with ONLY the higher-kinded type variable
// `f` (no unknown named type) declares cleanly — proving the reject above fires on
// the unknown NAMED type, not on the HKT shape itself.
// spec: spec/07-traits.md §7.2 — a higher-kinded trait declaration with a type
// constructor parameter succeeds.
#[test]
fn hkt_valid_functor_declaration_green() {
    run_prims(
        "(deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))\n\
         (defn main [] (Pure 0))\n",
    )
    .assert_exit(0);
}
