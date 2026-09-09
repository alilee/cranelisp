// mc_x4b_untyped_adt_field.rs — MC-X4b (S113, /port `probe/rep.cl` shape).
//
// The generic-ADT-field face of the MC-X4 consumer-of-multi-sig family (same
// root: the consumer's mono harvest must ground the instance). A monomorphic
// field and an explicitly parameterised field must both reach codegen with a
// concrete `unwrap` instance. The face pair fences a partial monomorphic-only
// fix. Owner /dev(typecheck), `class=carrier-loss`.
// Re-authored free-standing from the /port repro (stdlib `conj`/`count` → primitive
// vec ops; the Cell/Grid ADT → a minimal Box). Free-standing (no stdlib).

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// A MULTI-SIG `build` returning a `Box`; `(build 3)` → `(MkBox 41)` (the last
// iteration's `(add-i64 n 40)` at n=1). `unwrap` consumes the ADT via a match.
fn program(type_head: &str, field_decl: &str) -> String {
    format!(
        "(deftype {type_head} (MkBox [{field_decl}]))\n\
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
        .user(&program("Box", ":Int v"))
        .output()
        .assert_exit(41);
}

// MC-X4b generic face — `(Box a)` declares the residual field parameter
// explicitly. The use fixes `a := Int`, so the consumer harvest must mint the
// concrete `unwrap` instance and the program must return 41.
// spec: spec/05-definitions.md §§5.1.2, 5.2.4.
// defect: class=carrier-loss locus=crates/cranelisp-typecheck consumer mono harvest over a generic ADT field (same root as MC-X4) found=S113 owner=/dev
#[test]
fn generic_adt_field_consumer_of_multi_sig_return_green() {
    Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(&program("(Box a)", ":a v"))
        .output()
        .assert_exit(41);
}
