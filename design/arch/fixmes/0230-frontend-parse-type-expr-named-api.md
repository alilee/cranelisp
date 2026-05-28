---
number: 0230
target: /frontend
filed_by: /dev (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §12 (Next skills), crates/cranelisp-frontend/, src/platform.rs (parse_type_sig)
status: open
---

# Expose `parse_type_expr` named API for platform sig parsing

## Issue

The platform DLL's `PlatformFn.type_sig` is currently parsed by an
int-side ad-hoc `parse_type_sig` (host-private helper at
`src/platform.rs` / equivalent). The Sprint 71 host-wiring follow-up
(FIXME 0229 + FIXME 0233) intends to replace `parse_type_sig` with a
frontend+typecheck pipeline call so the DLL's declared signatures
flow through the canonical type-parsing path used for cranelisp
source.

To enable that replacement, `cranelisp-frontend` needs a named
public API for parsing a standalone type expression (S-expression
text) into the canonical `TypeExpr` shape.

## Proposed resolution

`cranelisp-frontend` exposes:

```rust
/// Parse a single type expression S-expression into the AST type-expr
/// shape. Used by int's platform loader to parse PlatformFn.type_sig
/// (per FIXME 0233 — replace parse_type_sig with frontend+typecheck path).
pub fn parse_type_expr(src: &str, source_id: ...) -> Result<TypeExpr, ...>;
```

The function reuses the existing `parse` reader + a focused build pass
that targets the type-expr AST production. No new grammar; the surface
already exists internally — the FIXME is the named public binding.

## Operational implication / Context

Naming this as a public-API extension means `cranelisp-frontend`'s
`facades/frontend.md` (now-retired; cranelisp-frontend uses source
rustdoc as the canonical surface) needs a per-item `///` rustdoc on
`parse_type_expr` enumerating the bounded shape (string in, TypeExpr
out, single-expression — not a program form).

The cranelisp-frontend rustdoc + the public-api.txt baseline regenerate
in the same change-set when this lands per the S67-close baseline-diff
discipline.
