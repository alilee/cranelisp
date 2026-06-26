//! Type-signature match predicates for importable-symbol search (Pillar 3).
//!
//! Two pure, context-free predicates over the `cranelisp-types` `Type` algebra,
//! called by the `int` indexer to match a query type signature against an
//! indexed symbol's signature. Both compare the scheme's `ty` (the function
//! shape); neither reads `Scheme.constraints` or `Scheme.type_vars` (MVP scope,
//! `design/typecheck/signature-match.md` §2.2). No unifier, no `CheckState`, no
//! `&mut` — the whole point of the MVP over Hoogle subsumption (§5, deferred).
//!
//! - [`signature_matches_exact`] — alpha-equivalence: structurally identical up
//!   to a consistent **bijective** renaming of type variables (§2/§3).
//! - [`signature_matches_partial`] — structural-contains: some subtree of the
//!   candidate is alpha-equivalent to the query (§4). `_exact ⟹ _partial`.
//!
//! Algorithm (§2.1): canonicalise each `Type` by renumbering its `Type::Var`
//! ids — and the `Type::TyConApp` **head** id — to `0,1,2,…` in order of first
//! occurrence, then compare canonical forms with the derived `PartialEq`. The
//! first-occurrence numbering is injective, so equal canonical forms force the
//! same var-sharing pattern (bijective by construction). The HKT head is folded
//! into the SAME numbering (§2.3) so two `TyConApp`s match iff their heads align
//! under the consistent renaming and their args match positionally.
//!
//! The first-occurrence numbering walk is the shared
//! `cranelisp_types::collect_var_ids_ordered` (which numbers the `TyConApp` head
//! per FIXME 0437 — the typecheck-local copy that predated the fix is retired,
//! Principle 7).

use std::collections::HashMap;

use cranelisp_types::{Type, TypeId, collect_var_ids_ordered};

/// Returns true iff `query` and `candidate` are alpha-equivalent: structurally
/// identical up to a consistent bijective renaming of their type variables
/// (`design/typecheck/signature-match.md` §2). Pure; no state, no `&mut`, no
/// `CheckState` — it reads only the two `Type`s.
///
/// Concrete heads must be identical (`Int` ~ `Int`, `Fn` arities match, `ADT`
/// `FQTypeName`s match, `TyConApp` heads renamed like any var). A concrete head
/// never matches a variable (this is exact shape, NOT subsumption).
pub fn signature_matches_exact(query: &Type, candidate: &Type) -> bool {
    canonical_signature_shape(query) == canonical_signature_shape(candidate)
}

/// Returns true iff some subtree of `candidate` is alpha-equivalent to `query`
/// (structural-contains; `design/typecheck/signature-match.md` §4). Pure; no
/// state, no `&mut`, no `CheckState`. Sibling of [`signature_matches_exact`];
/// `signature_matches_exact(q, c)` ⟹ `signature_matches_partial(q, c)` because
/// the candidate's whole tree is one of its own subtrees.
///
/// Each enumerated subtree is canonicalised independently (its own
/// first-occurrence numbering) and compared to the canonicalised query — a
/// sub-shape's alpha-equivalence depends only on the var-sharing pattern within
/// that subtree (§4.2). A single query var does NOT match a concrete candidate
/// subtree (that is subsumption, §5, deliberately excluded).
pub fn signature_matches_partial(query: &Type, candidate: &Type) -> bool {
    let q_canon = canonical_signature_shape(query);
    candidate_contains_canonical(candidate, &q_canon)
}

/// Renumber a `Type`'s vars (and `TyConApp` heads) to `0,1,2,…` by first
/// occurrence (§2.1). Two alpha-equivalent types produce `==` canonical forms.
/// Idempotent. The canonical `Type` is also a suitable index-bucket key.
///
/// `pub(crate)` — the two predicates are the only authorised public surface this
/// sprint (§7); the canonical-shape helper is internal (a §3.1 index-bucket
/// affordance is a future additive export if the indexer needs it).
pub(crate) fn canonical_signature_shape(ty: &Type) -> Type {
    let mut order: Vec<TypeId> = Vec::new();
    collect_var_ids_ordered(ty, &mut order);
    let renaming: HashMap<TypeId, TypeId> = order
        .into_iter()
        .enumerate()
        .map(|(i, id)| (id, i as TypeId))
        .collect();
    rename(ty, &renaming)
}

/// Whether any subtree of `candidate` canonicalises to `q_canon`.
fn candidate_contains_canonical(candidate: &Type, q_canon: &Type) -> bool {
    if &canonical_signature_shape(candidate) == q_canon {
        return true;
    }
    match candidate {
        Type::Fn(params, ret) => {
            params.iter().any(|p| candidate_contains_canonical(p, q_canon))
                || candidate_contains_canonical(ret, q_canon)
        }
        // For `ADT`/`TyConApp` the head/`FQTypeName` is a leaf, not an
        // independently-walkable subtree (§4.2) — only the args recurse.
        Type::ADT(_, args) | Type::TyConApp(_, args) => {
            args.iter().any(|a| candidate_contains_canonical(a, q_canon))
        }
        // Concrete leaves and `Var` have no children — already tested above.
        Type::Int | Type::Bool | Type::String | Type::Float | Type::Var(_) => false,
    }
}

/// Apply a var-id renaming, producing the canonical `Type`. The `TyConApp` head
/// is renamed by the same map (§2.3).
fn rename(ty: &Type, renaming: &HashMap<TypeId, TypeId>) -> Type {
    match ty {
        Type::Var(id) => Type::Var(*renaming.get(id).unwrap_or(id)),
        Type::Fn(params, ret) => Type::Fn(
            params.iter().map(|p| rename(p, renaming)).collect(),
            Box::new(rename(ret, renaming)),
        ),
        Type::ADT(fqtn, args) => {
            Type::ADT(fqtn.clone(), args.iter().map(|a| rename(a, renaming)).collect())
        }
        Type::TyConApp(head, args) => Type::TyConApp(
            *renaming.get(head).unwrap_or(head),
            args.iter().map(|a| rename(a, renaming)).collect(),
        ),
        Type::Int => Type::Int,
        Type::Bool => Type::Bool,
        Type::String => Type::String,
        Type::Float => Type::Float,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{FQTypeName, ModuleFullPath, Type, TypeName};

    fn v(id: TypeId) -> Type {
        Type::Var(id)
    }
    fn func(params: Vec<Type>, ret: Type) -> Type {
        Type::Fn(params, Box::new(ret))
    }
    fn adt(module: &str, name: &str, args: Vec<Type>) -> Type {
        Type::ADT(
            FQTypeName::new(ModuleFullPath::from(module), TypeName::from(name)),
            args,
        )
    }

    // --- signature_matches_exact (§2/§3) ---

    // spec: design/typecheck/signature-match.md §2 — alpha-equivalence MATCH rows
    #[test]
    fn exact_matches_alpha_equivalent() {
        let cases: &[(Type, Type)] = &[
            // (Fn [a] a) ~ (Fn [b] b)
            (func(vec![v(0)], v(0)), func(vec![v(7)], v(7))),
            // (Fn [a b] a) ~ (Fn [x y] x)
            (func(vec![v(0), v(1)], v(0)), func(vec![v(9), v(8)], v(9))),
            // (Fn [Int a] (Vec a)) ~ same renamed
            (
                func(vec![Type::Int, v(0)], adt("m", "Vec", vec![v(0)])),
                func(vec![Type::Int, v(3)], adt("m", "Vec", vec![v(3)])),
            ),
            // (Fn [a] (Option a)) ~ (Fn [z] (Option z))
            (
                func(vec![v(0)], adt("m", "Option", vec![v(0)])),
                func(vec![v(5)], adt("m", "Option", vec![v(5)])),
            ),
        ];
        for (q, c) in cases {
            assert!(
                signature_matches_exact(q, c),
                "expected exact match: {q:?} ~ {c:?}"
            );
            // Symmetry — exact is an equivalence relation.
            assert!(signature_matches_exact(c, q));
        }
    }

    // spec: design/typecheck/signature-match.md §2 — alpha-equivalence NO-MATCH rows
    #[test]
    fn exact_rejects_non_equivalent() {
        // arity differs (1 vs 2 params)
        assert!(!signature_matches_exact(
            &func(vec![v(0)], v(0)),
            &func(vec![v(0), v(1)], v(0)),
        ));
        // sharing pattern differs (params shared vs distinct) — the bijectivity guard
        assert!(!signature_matches_exact(
            &func(vec![v(0), v(0)], v(0)),
            &func(vec![v(0), v(1)], v(0)),
        ));
        // concrete head != variable (exact shape, NOT subsumption)
        assert!(!signature_matches_exact(
            &func(vec![Type::Int], Type::Int),
            &func(vec![v(0)], v(0)),
        ));
        // ADT heads differ (Option != Vec)
        assert!(!signature_matches_exact(
            &func(vec![v(0)], adt("m", "Option", vec![v(0)])),
            &func(vec![v(0)], adt("m", "Vec", vec![v(0)])),
        ));
        // FQ module differs (same-named ADT from two modules) — load-bearing FQ discipline
        assert!(!signature_matches_exact(
            &func(vec![v(0)], adt("m", "Box", vec![v(0)])),
            &func(vec![v(0)], adt("n", "Box", vec![v(0)])),
        ));
    }

    // spec: design/typecheck/signature-match.md §2.1 — bijectivity both directions
    #[test]
    fn exact_bijectivity_is_directionless() {
        // (Fn [a b] a) does NOT match (Fn [a a] a) in EITHER direction.
        let distinct = func(vec![v(0), v(1)], v(0));
        let shared = func(vec![v(0), v(0)], v(0));
        assert!(!signature_matches_exact(&distinct, &shared));
        assert!(!signature_matches_exact(&shared, &distinct));
    }

    // spec: design/typecheck/signature-match.md §2.3 — HKT TyConApp head renaming
    #[test]
    fn exact_hkt_head_renamed_like_var() {
        // (f a) ~ (g b): heads + args both renamed under one numbering.
        assert!(signature_matches_exact(
            &Type::TyConApp(0, vec![v(1)]),
            &Type::TyConApp(5, vec![v(6)]),
        ));
        // (f a) where head == arg sharing pattern matters: (f f-as-arg) is
        // distinct from (f a) — `TyConApp(0, [Var(0)])` vs `TyConApp(0, [Var(1)])`.
        assert!(!signature_matches_exact(
            &Type::TyConApp(0, vec![v(0)]),
            &Type::TyConApp(0, vec![v(1)]),
        ));
        // A TyConApp head does NOT match a concrete ADT head (that is subsumption).
        assert!(!signature_matches_exact(
            &Type::TyConApp(0, vec![v(1)]),
            &adt("m", "Option", vec![v(1)]),
        ));
    }

    // spec: design/typecheck/signature-match.md §2.1 — canonicalisation is idempotent
    #[test]
    fn canonical_shape_idempotent_and_equating() {
        let t = func(vec![v(42), v(7)], v(42));
        let c1 = canonical_signature_shape(&t);
        let c2 = canonical_signature_shape(&c1);
        assert_eq!(c1, c2, "canon must be idempotent");
        // alpha-equivalent pair → equal canonical forms
        assert_eq!(
            canonical_signature_shape(&func(vec![v(0)], v(0))),
            canonical_signature_shape(&func(vec![v(9)], v(9))),
        );
        // sharing-different pair → distinct canonical forms
        assert_ne!(
            canonical_signature_shape(&func(vec![v(0), v(0)], v(0))),
            canonical_signature_shape(&func(vec![v(0), v(1)], v(0))),
        );
    }

    // --- signature_matches_partial (§4 — structural-contains) ---

    // spec: design/typecheck/signature-match.md §4 — positive containment
    #[test]
    fn partial_matches_contained_subtree() {
        // (Vec Int) is the first-parameter subtree of (Fn [(Vec Int)] Bool)
        assert!(signature_matches_partial(
            &adt("m", "Vec", vec![Type::Int]),
            &func(vec![adt("m", "Vec", vec![Type::Int])], Type::Bool),
        ));
        // Int is contained anywhere it is mentioned
        assert!(signature_matches_partial(
            &Type::Int,
            &func(vec![Type::Int], Type::Bool),
        ));
        assert!(signature_matches_partial(
            &Type::Int,
            &adt("m", "Vec", vec![Type::Int]),
        ));
        // (Option a) is the return subtree, under per-subtree alpha-renaming
        assert!(signature_matches_partial(
            &adt("m", "Option", vec![v(0)]),
            &func(vec![v(3)], adt("m", "Option", vec![v(7)])),
        ));
    }

    // spec: design/typecheck/signature-match.md §4.3 — exact ⟹ partial
    #[test]
    fn partial_superset_of_exact() {
        let pairs: &[(Type, Type)] = &[
            (func(vec![v(0)], v(0)), func(vec![v(7)], v(7))),
            (func(vec![v(0), v(1)], v(0)), func(vec![v(9), v(8)], v(9))),
            (
                func(vec![Type::Int, v(0)], adt("m", "Vec", vec![v(0)])),
                func(vec![Type::Int, v(3)], adt("m", "Vec", vec![v(3)])),
            ),
        ];
        for (q, c) in pairs {
            assert!(signature_matches_exact(q, c));
            assert!(
                signature_matches_partial(q, c),
                "every exact match must be a partial match: {q:?} in {c:?}"
            );
        }
    }

    // spec: design/typecheck/signature-match.md §4 / §6 — partial NO-MATCH rows
    #[test]
    fn partial_rejects_uncontained() {
        // sharing-pattern guard carries over: (Fn [a a] a) not in (Fn [a b] a)
        assert!(!signature_matches_partial(
            &func(vec![v(0), v(0)], v(0)),
            &func(vec![v(0), v(1)], v(0)),
        ));
        // concrete leaf differs: (Vec Bool) not in (Fn [(Vec Int)] Bool)
        assert!(!signature_matches_partial(
            &adt("m", "Vec", vec![Type::Bool]),
            &func(vec![adt("m", "Vec", vec![Type::Int])], Type::Bool),
        ));
        // containment is NOT subsumption: a bare var must NOT match a concrete subtree
        assert!(!signature_matches_partial(
            &v(0),
            &func(vec![Type::Int], Type::Bool),
        ));
    }
}
