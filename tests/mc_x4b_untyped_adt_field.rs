// mc_x4b_untyped_adt_field.rs — MC-X4b (S113, /port `probe/rep.cl` shape).
//
// The untyped-ADT-field type-ambiguity face of the MC-X4 consumer-of-multi-sig
// family (same root: the consumer's mono harvest can't ground the instance). An ADT
// with a TYPED field consumed from a multi-sig return works (GREEN); the SAME shape
// with an UNTYPED field leaks `undefined function` at codegen (RED) — the untyped
// field leaves a residual type var the consumer's request never grounds. The face
// pair fences a PARTIAL fix (typed-only). Owner /dev(typecheck), `class=carrier-loss`.
// Re-authored free-standing from the /port repro (stdlib `conj`/`count` → primitive
// vec ops; the Cell/Grid ADT → a minimal Box). Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// A MULTI-SIG `build` returning a `Box`; `(build 3)` → `(MkBox 41)` (the last
// iteration's `(add-i64 n 40)` at n=1). `unwrap` consumes the ADT via a match.
fn program(field_decl: &str) -> String {
    format!(
        "(deftype Box (MkBox [{field_decl}]))\n\
         (defn unwrap [b] (match b [(MkBox v) v]))\n\
         (defn build\n\
         \x20 ([n]   (build n (MkBox 0)))\n\
         \x20 ([n b] (if (eq-i64 n 0) b (build (add-i64 n -1) (MkBox (add-i64 n 40))))))\n\
         (defn main [] (Pure (unwrap (build 3))))\n"
    )
}

// MC-X4b GREEN twin — the TYPED field `:Int v`: the consumer's instance is ground
// (`Box` over `Int`), so `unwrap` monomorphises and `(build 3)` → `(MkBox 41)` →
// 41.
// spec: spec/05-definitions.md §5.1.2 — a typed-ADT-field consumer over a multi-sig
// return is monomorphised.
#[test]
fn typed_adt_field_consumer_of_multi_sig_return_green() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(&program(":Int v"))
        .output()
        .assert_exit(41);
}

// MC-X4b RED pin — the UNTYPED field `v`: the field carries a residual type var the
// consumer's mono harvest never grounds ⇒ no `unwrap` instance minted ⇒ codegen
// `undefined function: unwrap`. MUST either monomorphise (→ 41) or reject cleanly
// at typecheck — NEVER leak to codegen.
// spec: spec/05-definitions.md §5.1.2 — a consumer of an ADT field must not leak an
// un-monomorphised call to codegen.
// defect: class=carrier-loss locus=crates/cranelisp-typecheck consumer mono harvest over an untyped ADT field (residual Var; same root as MC-X4) found=S113 owner=/dev
#[test]
fn untyped_adt_field_consumer_of_multi_sig_return_neg() {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(&program("v"))
        .output();
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.contains("undefined function") && !c.contains("codegen error"),
        "an untyped-ADT-field consumer over a multi-sig return MUST NOT leak an \
         un-monomorphised call to codegen (`undefined function`) — it monomorphises \
         or rejects cleanly at typecheck (same carrier-loss root as MC-X4); got:\n{c}"
    );
}
