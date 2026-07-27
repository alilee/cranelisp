---
number: 0933
target: /design
filed_by: /arch
filed_at: 2026-07-28
sprint_filed: 119
refers_to: design/arch/total-concreteness.md §3.5;
  src/platform.rs:360-430 (parse_and_check_platform_type_sig →
  DefKind::PlatformEffect mint; type_vars hard-empty but the parsed ty is
  unchecked for Type::Var), :475-505 (fqize_type_expr — a lowercase manifest
  leaf survives as TypeExpr::TypeVar)
status: open
---

# S120: a platform manifest sig containing a residual `Type::Var` must refuse at the mint

**Target: `/design`(int). S120 scope, small.**

Every shipped platform sig is concrete and `PlatformEffect` schemes are minted
with `type_vars: vec![]` — but nothing refuses a manifest sig whose parsed
type contains a `Type::Var`: a lowercase leaf with no slash parses to
`TypeExpr::TypeVar` and would flow into the scheme unnoticed, smuggling a
polymorphic slotted entry into an otherwise-concrete class. Under the
total-concreteness target (`total-concreteness.md` §2 I-CONC) the
`PlatformEffect` class stays concrete **by construction**: add the mint-side
gate — `parse_and_check_platform_type_sig` refuses, with a located error
naming the offending leaf and the platform fn, when the checked type contains
any residual variable. A platform fn is a hand-written C-ABI body; a
polymorphic platform sig is a declared contract nothing can check.

Unit rows: a concrete sig mints unchanged; a lowercase-leaf sig refuses with
the named leaf; the refusal is a diagnosed load error, not a panic.

Delete this file when the gate design lands.
