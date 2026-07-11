---
number: 0558
target: /qa
filed_by: /sprint
filed_at: 2026-07-11
sprint_filed: 108
refers_to: src/repl.rs::format_trait_display (~L2734-2755); repl/spec.md §4.1.4; S108 D1 (the same wrong-scope class, fixed for type display); design/arch/fixmes (0557 sibling)
status: open
---

# `format_trait_display` roots its lookups at the current scope — a bare prelude-globbed trait may drop `; defn:`/`; impl:` (same class as S108 D1)

## Issue

S108 fixed D1: `format_type_display` rooted its constructor lookup at
`current_module_path()` instead of the type's resolved home, so a
prelude-reachable seeded ADT (`Option`) dropped its `; match:` section. During the
S108 Wave-1 `/review`, the **same wrong-scope class was found un-fixed in the trait
display path**: `src/repl.rs::format_trait_display` (~L2734-2755) roots
`lookup_trait_decl_chain` (`; defn:` methods) and `get_implementing_types_chain`
(`; impl:` types) at `current_module_path()`, and its `defining_module` fallback
(~L2734) mis-homes the primary line to the current scope when the chain does not
resolve.

For a **prelude-globbed trait** — one reachable only via the implicit-prelude
outer-scope fallback bit, with no `Import` edge in the user table (src/CLAUDE.md
§"Prelude as an OUTER SCOPE") — the chain-follow from the user scope can miss,
dropping `; defn:` and `; impl:` exactly as D1's seeded ADTs dropped `; match:`.
`/arch`'s S108 Phase-2 verdict named this "the prelude-trait-enumeration sibling
gap" and deliberately scoped it OUT of S108 (no committed repro; distinct from the
committed D1 RED), with a "note to /qa". This FIXME is that durable record.

Not yet reproduced. Per the cross-skill defect-handoff rule (root CLAUDE.md), a
defect handoff needs a minimal repro before a fix dispatch.

## Proposed resolution

1. `/qa` + `/testing`: author a minimal e2e repro — a bare lookup of a
   prelude-provided trait (e.g. via the `test-standard` prelude's `Display`/`Num`)
   entered at the REPL from the `user` module, asserting the `; defn:` and (per
   §4.1.4, which is DELIBERATELY UNCONDITIONAL — see the FIXME 0542 note at
   repl.rs:2722) `; impl:` sections appear. Confirm whether it actually reproduces
   (the trait may currently resolve for a different reason than types do).
2. If it reproduces: `/dev` (src/) applies the D1-shaped fix — resolve the trait's
   home once (the way `describe_symbol`/the bare-symbol gate already make the
   prelude hop), then root `lookup_trait_decl_chain` / `get_implementing_types_chain`
   at that home rather than `current_module_path()`. Mind the §4.1.4 unconditional
   `; impl:` rule and the locally-defined-first ordering.

## Operational implication / Context

- Same defect CLASS as S108 D1 — a recurring wrong-scope display-lookup. Worth a
  `/arch` glance for whether a single "resolve home, then enumerate from home"
  helper should back all introspection section-lookups (type `; match:`/`; impl:`,
  trait `; defn:`/`; impl:`) so the class cannot recur a fourth time.
- Delete when the repro + fix land (or when the repro proves it does not reproduce,
  recording that finding).
