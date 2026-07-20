// w3_enforcement_fences.rs — S113 W3 enforcement GREEN fences (audit-flagged binder
// enforcement added at all sites). These pin the newly-landed rejects. Free-standing.

#[path = "helpers/mod.rs"]
mod helpers;

use helpers::e2e::{Cranelisp, PreludeVariant};

// `--run` a program, returning combined stdout+stderr.
fn run_prims(src: &str) -> String {
    let out = Cranelisp::new()
        .with_prelude(PreludeVariant::PrimitivesOnly)
        .run("user.cl")
        .user(src)
        .output();
    format!("{}{}", out.stdout, out.stderr)
}

// LOWERCASE-parenthesized deftype head: `(deftype (point a) …)` — the type name
// `point` is lowercase; a type name must start with uppercase. The parenthesized
// (HKT) head shape does not exempt the uppercase rule.
// spec: spec/05-definitions.md §5.2 — a deftype head names a type (uppercase).
#[test]
fn deftype_lowercase_parenthesized_head_rejected_neg() {
    let c = run_prims("(deftype (point a) (MkP [:a v]))\n(defn main [] (Pure 0))\n");
    assert!(
        c.contains("type name must start with uppercase"),
        "a lowercase parenthesized deftype head `(point a)` MUST be rejected — a \
         type name starts with uppercase (§5.2); got:\n{c}"
    );
}

// QUALIFIED mod head: `(mod foo/bar)` — a `mod`/`mod-` head is a binder and must
// be a simple symbol, not qualified.
// spec: spec/05-definitions.md §5.8 — a `mod` head is a simple module name.
#[test]
fn mod_qualified_head_rejected_neg() {
    let c = run_prims("(mod foo/bar)\n");
    assert!(
        c.contains("not a valid module name"),
        "a qualified `mod` head `foo/bar` MUST be rejected as an invalid module \
         name (§5.8); got:\n{c}"
    );
}

// DOTTED mod head: `(mod a.b)` — likewise rejected.
// spec: spec/05-definitions.md §5.8 — a `mod` head is a simple module name.
#[test]
fn mod_dotted_head_rejected_neg() {
    let c = run_prims("(mod a.b)\n");
    assert!(
        c.contains("not a valid module name"),
        "a dotted `mod` head `a.b` MUST be rejected as an invalid module name \
         (§5.8); got:\n{c}"
    );
}

// mod- (private) qualified head twin.
// spec: spec/05-definitions.md §5.8 — `mod-` head is a simple module name.
#[test]
fn mod_private_qualified_head_rejected_neg() {
    let c = run_prims("(mod- foo/bar)\n");
    assert!(
        c.contains("not a valid module name"),
        "a qualified `mod-` head `foo/bar` MUST be rejected (§5.8); got:\n{c}"
    );
}

// mod- (private) dotted head twin.
// spec: spec/05-definitions.md §5.8 — `mod-` head is a simple module name.
#[test]
fn mod_private_dotted_head_rejected_neg() {
    let c = run_prims("(mod- a.b)\n");
    assert!(
        c.contains("not a valid module name"),
        "a dotted `mod-` head `a.b` MUST be rejected (§5.8); got:\n{c}"
    );
}

// SIMPLE-name accept twin: `(mod good)` — a bare simple symbol PASSES the
// binder-name validation (it does NOT get the qualified/dotted rejection). The
// subsequent submodule-file resolution is a separate concern; the load-bearing
// assertion is that a simple name is NOT rejected as an invalid module name.
// spec: spec/05-definitions.md §5.8 — a simple `mod` head is accepted.
#[test]
fn mod_simple_head_accepts_name_validation_twin() {
    let c = run_prims("(mod good)\n(defn main [] (Pure 0))\n");
    assert!(
        !c.contains("not a valid module name"),
        "a simple `mod` head `good` MUST pass binder-name validation (NOT be \
         rejected as an invalid module name); got:\n{c}"
    );
}

// QUALIFIED-LOWERCASE type-arg in COMPOUND position: `:(Option user/x)` — the
// 0589 sibling. A qualified-lowercase name in a compound type position is a
// named-type REFERENCE that must ERROR as an unknown type, NOT silently mint a
// type variable.
// spec: spec/03-types.md §2.3.8 — a qualified-lowercase type name is a reference,
// not a minted var; it errors as an unknown type.
// defect: class=silent-accept locus=crates/cranelisp-typecheck type-var minting excluded qualified names in compound positions (0589 sibling) found=S113 owner=/dev
#[test]
fn compound_qualified_lowercase_type_arg_errors_not_mints_neg() {
    let c = run_prims("(defn f [:(Option user/x) a] a)\n(defn main [] (Pure 0))\n");
    assert!(
        c.contains("unknown type"),
        "a qualified-lowercase type arg `user/x` in the compound position \
         `(Option user/x)` MUST error as an unknown type (§2.3.8, 0589 sibling), \
         NOT silently mint a var; got:\n{c}"
    );
}
