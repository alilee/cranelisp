---
number: 0362
target: /frontend
filed_by: /dev
filed_at: 2026-06-15
sprint_filed: 83
refers_to: crates/cranelisp-frontend/src/ast_builder.rs (parse_annotation_name ~:1481, build_type_expr ~:1652), tests/spec_08_modules.rs::self_qualified_type_reference_resolves_to_local_type, crates/cranelisp-typecheck/src/checker/tests.rs::self_qualified_type_resolves_to_local_product_type
status: open
---

# Qualified type annotation `:t/Box` is not split on `/` in the frontend (root cause of FIXME 0351(b))

## Issue

The e2e `self_qualified_type_reference_resolves_to_local_type` (FIXME 0351(b))
fails with `unknown type \`t/Box\` (from module \`\`)` for:

```
(deftype Box [:primitives/Int v])
(defn unbox [:t/Box b] (match b [(Box x) x]))
(defn main [] (unbox (Box 9)))
```

The diagnostic signature is the tell: the WHOLE `t/Box` is the type **name**
and the **from-module is empty**. That is the shape of an **un-split
`TypeRef`** — `TypeRef { module: None, name: "t/Box" }` — arriving at typecheck.

**Ownership assigned by cross-crate isolation (per `tests/CLAUDE.md
§"Isolating Cross-Crate Failures"`).** The committed typecheck unit
`crates/cranelisp-typecheck/src/checker/tests.rs::self_qualified_type_resolves_to_local_product_type`
drives the typecheck leaf `resolve_type_expr_in_module` directly against a
fixture where module `t` owns a product type `Box`, with BOTH a properly-split
`TypeRef { module: Some("t"), name: "Box" }` AND an un-split
`TypeRef { module: None, name: "t/Box" }`. **All forms resolve at the leaf** —
the shared `cranelisp_types::resolve` splits `t/Box` on `/` internally
(`split_qualified`) and resolves it in module `t`. Therefore the typecheck leaf
and the shared `cranelisp-types::resolve` are BOTH correct; the defect is NOT
in typecheck (the original 0351 target) nor in `cranelisp-types` (the /arch
candidate). It is **in the frontend** — the source `:t/Box` annotation is never
split into `module=t, name=Box`.

## Root cause (frontend, identified by trace)

`crates/cranelisp-frontend/src/ast_builder.rs`:

1. `parse_annotation_name` (~:1481) — for an uppercase-leading annotation name
   (`Box`), it builds `TypeExpr::Named(TypeRef::new(None, TypeName::from(name)))`
   with the WHOLE `"t/Box"` string as the name. It does NOT split the `/`
   module qualifier.
2. `build_type_expr` (~:1652) — same omission for type expressions in general.

The asymmetry: the **trait-ref** path (~:1636–1645) DOES split a qualified name:

```rust
match name.rsplit_once('/') {
    Some((m, n)) if !m.is_empty() && !n.is_empty() =>
        TraitRef::new(Some(ModuleFullPath::from(m)), TraitName::from(n)),
    _ => TraitRef::new(module, TraitName::from(name)),
}
```

Type refs in annotation/type position should apply the same split.

## Proposed resolution

In `parse_annotation_name` and `build_type_expr`, split a qualified type name on
`/` (non-empty module AND non-empty symbol guard, mirroring `split_qualified` in
`cranelisp-types::resolve` and the existing trait-ref split) so `:t/Box` becomes
`TypeRef { module: Some("t"), name: "Box" }`. Bare punctuation / unqualified
names are unaffected by the non-empty-parts guard.

The e2e guard
`tests/spec_08_modules.rs::self_qualified_type_reference_resolves_to_local_type`
flips green once the frontend emits the split TypeRef. Add a frontend unit test
pinning that `:t/Box` parses to `TypeRef { module: Some("t"), name: "Box" }`
(and `:Box` stays `module: None`).

## Operational implication / Context

S83 Phase 5 Wave 2, /dev on cranelisp-typecheck. The 0351(a) field-accessor
synthesis (the other half of 0351) was fixed in the same wave; 0351(b) is
re-routed here because the isolation reassigned ownership from /typecheck to
/frontend. The typecheck isolation unit is committed failing-not-... — actually
it PASSES (the leaf is correct), so it rides as a permanent guard that the leaf
keeps resolving self-qualified type refs. The e2e remains the failing-not-ignored
guard until /frontend lands the split.
