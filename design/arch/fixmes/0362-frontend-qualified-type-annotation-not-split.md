---
number: 0362
target: /qa
filed_by: /dev
filed_at: 2026-06-15
sprint_filed: 83
refers_to: tests/spec_08_modules.rs::self_qualified_type_reference_resolves_to_local_type (the `main` fixture returns bare `Int`, not `IO _`)
status: open
---

# TYPECHECK HALF LANDED (S83 W2, /dev typecheck). RESIDUAL is a /qa e2e FIXTURE defect.

## S83 W2 /dev typecheck update (third layer — fixture `main` shape)

The typecheck half of this FIXME is **DONE and committed**:
`resolve_type_expr_in_module`'s `resolve_terminal` closure
(`crates/cranelisp-typecheck/src/checker.rs` ~:2127) now collapses a
**self-qualified** type ref (`tref.module == Some(current_module)`) to the
**bare** resolution path — composing the leaf name only and consulting the
staging-aware first-hop `read` view — so a module resolves `:t/Box` against its
OWN in-progress cluster staging, exactly as bare `:Box` already did. Root cause:
`cranelisp_types::resolve` routes a qualified `m/Name` straight to
`resolve_qualified`, which reads only COMMITTED `symbol_tables` (never the
staging view), so the in-cluster `Box` (still in staging, not committed) was
invisible to the self-qualified path. A genuinely cross-module qualified ref is
unchanged (Principle 17 — only the SELF case collapses to bare). Unit test
`self_qualified_type_resolves_against_in_cluster_staging`
(`crates/cranelisp-typecheck/src/checker/tests.rs`) pins the cluster-atomic
case: `Box` lives in STAGING only (committed `t` empty); `:t/Box` resolves.

**The e2e guard `self_qualified_type_reference_resolves_to_local_type` STILL
fails — but the error moved PAST typecheck entirely**, proving the type now
resolves:

- BEFORE the typecheck fix: `type error: unknown type `Box` (from module `t`)`
  — `Box` not found in committed `t` (the residual after the frontend split).
- AFTER the typecheck fix: `codegen error: main must return `IO _` (required
  shape `(Fn [] (IO _))`), found: Int` — `:t/Box` resolves; the program
  type-checks; codegen then rejects the fixture's `main` because it returns a
  bare `Int`, not `IO _`.

This is a **third-layer bug — a /qa e2e FIXTURE defect**, NOT a compiler defect.
The fixture's `(defn main [] (unbox (Box 9)))` returns bare `Int`. Verified
directly: wrapping it `(defn main [] (Pure (unbox (Box 9))))` (and importing
`Pure`) makes `--run` exit 9 — confirming the typecheck fix is complete and the
ONLY remaining blocker is the un-wrapped `main`.

### Proposed resolution (/qa, mechanical — mirror the corrected sibling)

The sibling guard `super_import_resolves_parent_type_constructor`
(`tests/spec_08_modules.rs` ~:1641) was already corrected (S82) to wrap its
`main` in `Pure` and import `[primitives [Pure]]`. Apply the identical
correction to `self_qualified_type_reference_resolves_to_local_type`:

```
(import [primitives [Pure]])
(deftype Box [:primitives/Int v])
(defn unbox [:t/Box b] (match b [(Box x) x]))
(defn main [] (Pure (unbox (Box 9))))
;; exits 9
```

The guard flips green once the fixture's `main` returns `IO _`. The
self-qualified-type behaviour-under-test is unchanged by the wrap — it is
exercised by the `:t/Box` annotation on `unbox`, which now resolves.

### Ownership: /qa

Per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` Step 4: the typecheck
unit passes, the e2e fails on a non-compiler error (codegen `main`-shape) ⇒ the
residual is a fixture defect, not a compiler defect. `tests/` is /qa-owned;
/dev (typecheck) does not edit it. Re-targeted `/typecheck` → `/qa`.

---

## S83 W2 /dev frontend update (layered-bug re-target)

## S83 W2 /dev frontend update (layered-bug re-target)

The frontend half of this FIXME is **DONE and committed**: `ast_builder.rs`
now splits `module/Name` → `TypeRef { module: Some(module), name: Name }` for
TYPE refs (`parse_annotation_name`, `build_type_expr`, applied-head), mirroring
the trait-ref `rsplit_once('/')` precedent, guarded on both halves non-empty.
Four unit tests pin it (`parse_annotation_name_splits_module_qualifier`,
`_bare_stays_unqualified`, `_deep_qualified_splits_at_last_slash`,
`parse_type_expr_splits_module_qualifier`).

**But the e2e guard `self_qualified_type_reference_resolves_to_local_type` still
fails** — the diagnostic CHANGED, proving the split now reaches typecheck:

- BEFORE the frontend fix: `unknown type \`t/Box\` (from module \`\`)` — un-split,
  empty from-module (the original 0362 tell).
- AFTER the frontend fix: `unknown type \`Box\` (from module \`t\`)` — correctly
  split (module=`t`, name=`Box`), but `Box` is NOT found in module `t` during
  the full pipeline.

This is a **layered bug**. The FIXME's original premise — "frontend-only;
typecheck + `cranelisp-types::resolve` proven correct via the committed leaf
unit" — is WRONG. The leaf unit
`self_qualified_type_resolves_to_local_product_type` PASSES because it registers
`Box` into module `t` and resolves against `t` immediately, in one frame. The
e2e fails because, in the actual cluster-atomic typecheck pipeline, `Box` is
NOT visible in module `t`'s type table at the point the `:t/Box` annotation is
resolved — a **timing/ordering / cluster-view defect in typecheck integration**,
NOT in the leaf and NOT in the frontend.

### Minimal repro (exact e2e shape, file MUST be named `t.cl` so the module is `t`)

```
;; t.cl  →  cranelisp --run t.cl
(deftype Box [:primitives/Int v])
(defn unbox [:t/Box b] (match b [(Box x) x]))
(defn main [] (unbox (Box 9)))
;; expected: exit 9
;; actual:   type error: unknown type `Box` (from module `t`)
```

Contrast (also `--run`): the **bare** `:Box` form of the same program type-checks
fine (it fails only later at codegen on the test-fixture `main` return shape) —
so local registration of `Box` in module `t` is sound; only the *self-qualified*
resolution path misses it. The defect is in how a self-qualified `module/Name`
TYPE ref is resolved against the still-building local cluster (likely
`resolve_type_expr_in_module` keying the self-home name against a committed view
that does not yet contain the in-cluster `Box`, where the bare-name path roots
at `current_module`'s live staging and DOES see it).

### Ownership: /typecheck

Per `tests/CLAUDE.md §"Isolating Cross-Crate Failures"` Step 4: the leaf unit
passes, the e2e fails ⇒ the bug is in the typecheck integration / cluster
resolution wiring, not the leaf and not the frontend. Re-targeted `/frontend` →
`/typecheck`. The e2e remains the failing-not-ignored guard until /typecheck
lands the cluster-aware self-qualified type resolution; flip it green there.

---

## ORIGINAL FILING (frontend half — now resolved)

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
