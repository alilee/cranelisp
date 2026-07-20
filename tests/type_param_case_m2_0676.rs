// type_param_case_m2_0676.rs — M2-TP1 / M2-TP2 (S114, s114-test-plan §5.1).
//
// The M2 head-parser case matrix, type-parameter axis (/qa disposition item 3,
// spec-mandated reject). Spec §2.2.2: "Type parameters MUST be lowercase symbols"
// (EBNF `type_param = SYMBOL (* lowercase *)`); §2.4.2 gives the ground — lowercase
// = type variable, an uppercase symbol is a named-type reference, not a parameter
// binder. §2.2.3 (deftrait) shares the exact same `type_param` production.
//
//   M2-TP1 (deftype) — `(deftype (Box A) …)` MUST be a LOCATED reject. RED: today
//   the `build_type_head` params loop takes any symbol, any case → silent-accept.
//   M2-TP2 (deftrait) — `(deftrait (Functor F) …)` — the P7-mirror twin (same
//   production). BORN-GREEN fence: deftrait ALREADY rejects ("constructor variable
//   must start with lowercase"); the fix must keep it green while flipping TP1 (the
//   two head parsers converging on ONE case rule — audit R1 Done criterion).
//
// Both flip/hold with the W-D1 case-mirror /dev(frontend) change-set. Free-standing
// (no stdlib). Verified /testing 2026-07-20: TP1 silent-accept (exit 0, no error);
// TP2 already located-rejects.

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

// M2-TP1 — deftype uppercase type param MUST be a located reject. `(deftype (Box A)
// [:Int val])` uses an UPPERCASE type param `A`; per §2.2.2 this MUST be rejected
// with a located error naming the lowercase requirement (the same rule the deftrait
// twin below already enforces).
//
// RED at HEAD: silently accepted (`build_type_head`'s params loop takes any symbol,
// any case — `ast_builder.rs` ~607-613) → the program compiles clean and `main`
// runs to exit 0 with no diagnostic. The field is `:Int val` (does NOT reference
// `A`), so the only fault is the uppercase param itself — nothing else can raise.
// Failing-not-ignored.
// spec: spec/02-grammar.md §2.2.2 — type parameters MUST be lowercase symbols.
// defect: class=silent-accept locus=crates/cranelisp-frontend/src/ast_builder.rs::build_type_head type-param loop (accepts any-case symbol; §2.2.2 requires lowercase) found=S114 owner=/dev
#[test]
fn deftype_uppercase_type_param_rejected_neg() {
    let out = run_prims("(deftype (Box A) [:Int val])\n(defn main [] (Pure 0))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("lowercase"),
        "an UPPERCASE deftype type param `(Box A)` MUST be a LOCATED reject naming \
         the lowercase requirement (§2.2.2) — today it is SILENTLY ACCEPTED (no \
         error, `main` runs clean); got:\n{c}"
    );
}

// M2-TP1 control — deftype LOWERCASE type param accepts. `(deftype (Box a) [:Int
// val])` is well-formed (`a` is a type variable). GREEN, must stay green (the fix
// must not over-reach and reject legal lowercase params).
// spec: spec/02-grammar.md §2.2.2 — a lowercase type parameter is accepted.
#[test]
fn deftype_lowercase_type_param_accepted_green() {
    let out = run_prims("(deftype (Box a) [:Int val])\n(defn main [] (Pure 0))\n");
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("lowercase") && out.status.code() == Some(0),
        "a lowercase deftype type param `(Box a)` MUST be accepted; got exit {:?}:\n{c}",
        out.status.code()
    );
}

// M2-TP2 — deftrait uppercase type param BORN-GREEN fence (the P7-mirror twin).
// `(deftrait (Functor F) …)` uses the SAME `type_param` production as deftype
// (§2.2.3 → §2.2.2); the deftrait head parser (`parse_trait_head_shape`) ALREADY
// enforces the case rule and rejects with a located error. This fence pins that
// behaviour: the W-D1 case-mirror fix must flip TP1 (deftype) to match this WITHOUT
// regressing it — the two parsers converging on ONE case rule. GREEN today, must
// stay green.
// spec: spec/02-grammar.md §2.2.3 — a deftrait uppercase type param is rejected
// (shared `type_param` lowercase production, §2.2.2).
#[test]
fn deftrait_uppercase_type_param_rejected_green() {
    let out = run_prims(
        "(deftrait (Functor F)\n  (fmap [:(Fn [a] b) g :(F a) x] (F b)))\n\
         (defn main [] (Pure 0))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        c.to_lowercase().contains("lowercase"),
        "an UPPERCASE deftrait type param `(Functor F)` MUST be a located reject \
         naming the lowercase requirement (§2.2.3/§2.2.2) — this ALREADY holds and \
         must stay green through the W-D1 case-mirror fix; got:\n{c}"
    );
}

// M2-TP2 control — deftrait LOWERCASE type param accepts. `(deftrait (Functor f)
// …)` is well-formed (`f` is a type-constructor variable). GREEN, must stay green.
// spec: spec/02-grammar.md §2.2.3 — a lowercase deftrait type parameter is accepted.
#[test]
fn deftrait_lowercase_type_param_accepted_green() {
    let out = run_prims(
        "(deftrait (Functor f)\n  (fmap [:(Fn [a] b) g :(f a) x] (f b)))\n\
         (defn main [] (Pure 0))\n",
    );
    let c = format!("{}{}", out.stdout, out.stderr);
    assert!(
        !c.to_lowercase().contains("lowercase") && out.status.code() == Some(0),
        "a lowercase deftrait type param `(Functor f)` MUST be accepted; got exit \
         {:?}:\n{c}",
        out.status.code()
    );
}
