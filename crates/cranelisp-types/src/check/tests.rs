//! Minimal cover for the `check.rs` resolved-stage DTOs (FIXME 0498).
//!
//! `check.rs` is mostly data-record DTOs. The load-bearing "logic" here is the
//! serde shape of the resolved-call carriers (`ResolvedCall` / `TypeDefInfo`
//! cross the typecheck→backend boundary) and the `MethodResolutions::new`/
//! `Default` seam. These pin the recursive
//! `AutoCurry.trait_resolution: Option<Box<ResolvedCall>>` edge (the only
//! non-flat case) explicitly.
//!
//! NOTE: `MethodResolutions` itself is NOT serde_json-round-trippable — its
//! `HashMap<Span, _>` fields use a struct key, which serde_json rejects (json
//! map keys must be strings). It is a transient in-memory compile-input DTO
//! (`ObjectCompileInput`), never JSON-cached, so this is a latent footgun
//! rather than a live defect; the tests below exercise its population
//! semantics directly and round-trip only the string-keyable value carriers.

use super::*;
use crate::{FQTypeName, JitSymbol, ModuleFullPath, TypeName};

fn fq_trait(module: &str, name: &str) -> FQTraitName {
    FQTraitName::new(ModuleFullPath::from(module), TraitName::from(name))
}

fn fq_type(module: &str, name: &str) -> FQTypeName {
    FQTypeName::new(ModuleFullPath::from(module), TypeName::from(name))
}

// spec: design/arch/fixmes/0498 — new() is the empty resolution set
#[test]
fn method_resolutions_new_is_empty() {
    let mr = MethodResolutions::new();
    assert!(mr.resolved_calls.is_empty());
    assert!(mr.pattern_ctors.is_empty());
    // Default must agree with new() (both are the empty set).
    let def = MethodResolutions::default();
    assert!(def.resolved_calls.is_empty() && def.pattern_ctors.is_empty());
}

// spec: design/arch/fixmes/0498 — each ResolvedCall variant round-trips through
// serde (the cache-restore contract), including the recursive AutoCurry edge.
#[test]
fn resolved_call_variants_serde_roundtrip() {
    let variants = vec![
        ResolvedCall::TraitMethod {
            trait_name: fq_trait("core.fmt", "Display"),
            method_name: Symbol::from("show"),
            impl_type: fq_type("primitives", "Int"),
            mangled_name: JitSymbol::from("Display.show$Int"),
            impl_module: ModuleFullPath::from("core.fmt"),
        },
        ResolvedCall::SigDispatch {
            mangled_name: JitSymbol::from("add$Int+Int"),
        },
        ResolvedCall::BuiltinFn {
            name: Symbol::from("add-i64"),
        },
        // The one recursive shape: an auto-curried trait method carries its
        // concrete resolution nested in a Box.
        ResolvedCall::AutoCurry {
            target_name: Symbol::from("add"),
            applied_count: 1,
            total_count: 2,
            trait_resolution: Some(Box::new(ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            })),
        },
    ];

    for v in &variants {
        let json = serde_json::to_string(v).expect("ResolvedCall must serialize");
        let rt: ResolvedCall = serde_json::from_str(&json).expect("ResolvedCall must deserialize");
        // Re-serialize the round-trip to compare structurally (ResolvedCall
        // has no PartialEq).
        assert_eq!(
            serde_json::to_string(&rt).unwrap(),
            json,
            "ResolvedCall round-trip must be byte-stable"
        );
    }
}

// spec: design/arch/fixmes/0498 — the two Span-keyed maps are independent and
// keyed by exact span; population + retrieval semantics (in-memory contract).
#[test]
fn method_resolutions_population_semantics() {
    let mut mr = MethodResolutions::new();
    let span_a = Span::new(0, 5);
    let span_b = Span::new(10, 20);
    mr.resolved_calls.insert(
        span_a,
        ResolvedCall::BuiltinFn { name: Symbol::from("mul-i64") },
    );
    mr.pattern_ctors.insert(
        span_b,
        FQSymbol { module: ModuleFullPath::from("user"), symbol: Symbol::from("Some") },
    );

    // Distinct spans land in distinct maps; a resolved-call span is not a
    // pattern-ctor span (the two axes never collide).
    assert!(mr.resolved_calls.contains_key(&span_a));
    assert!(!mr.pattern_ctors.contains_key(&span_a));
    assert_eq!(
        mr.pattern_ctors.get(&span_b).map(|s| s.to_string()),
        Some("user/Some".to_string())
    );
    // A miss on an unrelated span returns None (no phantom entries).
    assert!(mr.resolved_calls.get(&Span::new(99, 100)).is_none());
}

// spec: design/arch/fixmes/0498 — TypeDefInfo (name + type_params + ctor names)
// round-trips; the FQTypeName renders `module/name` and ctor order is preserved.
#[test]
fn type_def_info_serde_roundtrip_preserves_ctor_order() {
    let info = TypeDefInfo {
        name: fq_type("user", "Tree"),
        type_params: vec![Symbol::from("a")],
        constructors: vec![Symbol::from("Leaf"), Symbol::from("Node")],
    };
    let json = serde_json::to_string(&info).expect("serialize");
    let rt: TypeDefInfo = serde_json::from_str(&json).expect("deserialize");

    assert_eq!(rt.name.to_string(), "user/Tree");
    assert_eq!(rt.type_params.len(), 1);
    // Constructor tag == index, so ORDER is load-bearing (find_constructor_by_tag).
    assert_eq!(
        rt.constructors.iter().map(|c| c.to_string()).collect::<Vec<_>>(),
        vec!["Leaf".to_string(), "Node".to_string()]
    );
}
