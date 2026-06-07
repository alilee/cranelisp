---
number: 0278
target: /spec
filed_by: /sprint
filed_at: 2026-06-06
sprint_filed: 76
refers_to: spec/07-traits.md §7.1 (return-position Self), crates/cranelisp-frontend/src/ast_builder.rs (:1431 parse_annotation_name, :1546 build_type_expr), stdlib/{num/num.cl,compare/eq.cl,compare/ord.cl}
status: open
---

# Spec says return-position `Self` (capitalized); the frontend only accepts lowercase `self` — arbitrate

## Issue

Found during the 0265 repair: spec §7.1 prose says the return position of a
trait method signature uses capitalized `Self`, but the frontend maps ONLY
lowercase `self` → `TypeExpr::SelfType` (`parse_annotation_name:1431`,
`build_type_expr:1546`); capitalized `Self` becomes `TypeExpr::Named("Self")`
and fails resolution with `unknown type: Self` (REPL-verified 2026-06-06).

The as-built stdlib + the 0265 repair use lowercase `self` in return position
(`(+ [a b] self)`) — the form the real compiler accepts.

## Proposed resolution

/spec arbitrates the divergence (per the validate-against-spec discipline the
fix may be to either side):

- (a) Align §7.1 to lowercase `self` in all positions (matches as-built
  compiler + as-built stdlib; one token for "the implementing type"); or
- (b) Keep capitalized `Self` for type position (Rust-familiar) and file the
  enforcement to /dev (frontend) — recognizing `Self` in `build_type_expr`
  alongside `self` (or instead of, in type position).

Whichever way, the spec examples and the stdlib/compiler must end up agreeing;
update §7.1's examples + any traceability annotations accordingly. If (b), file
the follow-on frontend FIXME.

## Operational implication / Context

Cosmetic-to-small; no test currently covers capitalized `Self`. Surfaced and
parked here so the §7.1 prose does not silently contradict the running
compiler. Any sprint.
