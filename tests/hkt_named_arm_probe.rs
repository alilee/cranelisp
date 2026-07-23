// hkt_named_arm_probe.rs — born-green fence over the S110 resolver convergence
// (audit S114 R-1 rider, FIXME 0724; corrected S115 W1).
//
// NARRATIVE CORRECTION (S115 W1; audit `cranelisp-typecheck-s114.md` §2.2a): the
// earlier comment claimed the observed reject was a never-error `_hkt` `Named` arm
// "MASKED by a `form.rs::check_type_expr` pre-walk (which errors first)". That is
// FALSE — there is NO pre-walk and NO surviving never-error arm. The former mirror
// resolvers (`resolve_type_expr_hkt` / `resolve_type_expr_hkt_impl`) and their
// never-error `Named`-fabrication arms were DELETED in S110 (`5ed07d60`), when the
// four-mirror `TypeExpr` resolver family converged onto the ONE resolver
// (`TypeExprCtx` / `resolve_named`, `crates/cranelisp-typecheck/src/resolve.rs`).
// `resolve_named` ERRORS on an unknown name; there is no fabrication path to mask.
// (FIXME 0590 was verified against that S110 evidence and DELETED at S115 Phase 1.)
//
// WHAT THIS FILE FENCES: an unknown named type in HKT position produces a LOCATED
// `unknown type` error via the ONE converged resolver — the guarantee the S110
// convergence provides. The test is KEPT: if any future refactor reintroduces a
// never-error / mint-on-miss arm at the HKT resolution seam, an unknown named type
// would be silently fabricated as a `Named` and this cell would flip RED. The
// narrative changed; the assertions did not. Free-standing.

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
// rejected as an `unknown type`, never silently fabricated as a `Named`.
// `(deftrait (Functor f) (fmap [… :(Bogus a) x] (f b)))` uses the unknown `Bogus`
// in an HKT param type position. Guards the S110 converged resolver (`resolve_named`)
// against any future refactor reintroducing a never-error / mint-on-miss arm.
// spec: spec/07-traits.md §7.1.4 + spec/08-modules.md §8.6.1 — parameter
// annotations use valid type expressions whose names resolve through ordinary
// module scope; an absent `Bogus` is a located `unknown type`, not a minted type.
// defect: class=wrong-diagnostic locus=cranelisp-typecheck trait-tail probe
// (a bad parameter reclassified the valid `(f b)` return tail as a forbidden
// HKT default body) found=S116 owner=/dev
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
         located `unknown type` error — NOT silently fabricated as a `Named` (the \
         S110 converged `resolve_named` errors on unknown names); got exit {:?}:\n{c}",
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
