---
number: 0420
target: /arch
filed_by: /arch
filed_at: 2026-06-20
sprint_filed: 87
refers_to: crates/cranelisp-types/src/types.rs:108 (impl Display),:182,:188 (dead format_type_display/format_type_with_vars),:163 (type_var_names — live, keep); crates/cranelisp-typecheck/src/unify.rs:141 (format_type_fq, Wave-0 add); crates/cranelisp-typecheck/src/traits.rs:2202 (concrete_type_name strip),:1156,:1803 (no-impl renderers); src/display.rs:181,239 (format_type_qualified_inner / _with_inline_constraints); audits/cranelisp-types-s87.md Finding 1+2+4, audits/cranelisp-typecheck-s87.md S87-1
status: open
---

# FQ Type-rendering consolidation — one parameterized `Type` walk in `cranelisp-types`

## Issue

The S87 Stage-B audit (types Finding 1) found the `Type`-enum walk copy-pasted
**5×** across 3 crates with **2 divergent primitive-naming conventions** (a 6th
site with a 3rd convention is `concrete_type_name`'s strip-to-bare-local in the
no-impl renderer):

| # | Function | Location | Primitive convention | Status |
|---|---|---|---|---|
| 1 | `impl Display for Type` | `cranelisp-types/src/types.rs:108` | bare (`Int`) | live |
| 2 | `format_type_display`/`_with_vars` | `cranelisp-types/src/types.rs:182,188` | bare | **DEAD export** |
| 3 | `format_type_fq` | `cranelisp-typecheck/src/unify.rs:141` | FQ (`primitives/Int`) | live (**Wave-0 add**) |
| 4 | `format_type_qualified_inner` | `src/display.rs:181` | FQ | live |
| 5 | `format_type_with_inline_constraints` | `src/display.rs:239` | FQ | live |
| 6 | `concrete_type_name` no-impl renderer | `cranelisp-typecheck/src/traits.rs:2202,1156,1803` | strip-to-bare-local | live (half-FQ message bug) |

**Recurrence tell** (`memory/feedback_review_root_cause_and_duplication`): the
Wave-0 `format_type_fq` add was individually correct (fixed the type-error renderer
to emit FQ names per spec §5.3) but **deepened** the duplication — a 4th walk added
instead of an existing walk shared. The /arch Phase-2 "keep-distinct" advisory was
correct about the *output conventions* but was applied to the *implementations*.

This is correct-as-shipped (no behavioural bug except the half-FQ no-impl message),
but it is the highest-leverage maintainability debt in the `Type` dependency cone:
a new `Type` variant, or a change to `Fn`/`ADT` rendering, today requires editing
5–6 sites in 3 crates, and the two-convention split invites the exact "fixed one,
others wrong" drift the S86 campaign paid for.

## Proposed resolution

Introduce ONE parameterized walk in `cranelisp-types::types` taking a small config —
`{ primitive_naming: Bare | Qualified, var_naming: Numbered | Lettered(&var_names) }`
(and, if `display.rs`'s inline-constraints renderer is folded in, an optional
constraint map). The 5–6 sites become thin config-selecting callers:

- `impl Display` (#1) → unified walk, `Bare` + `Numbered`.
- `format_type_fq` (#3, typecheck) → unified walk, `Qualified` + `Numbered` — the
  cross-crate re-implementation disappears (typecheck calls a types-crate fn).
- `display.rs` #4/#5 → unified walk, `Qualified` + `Lettered`.
- `format_type_display`/`format_type_with_vars` (#2) → **deleted** (their
  lettered-var capability becomes the `Lettered` config); **keep** `type_var_names`
  (#163 — it IS live, `src/display.rs:116,150`).
- no-impl renderers (#6) → consume the unified walk with the `Qualified` config
  instead of `concrete_type_name`'s strip (fixes the half-FQ message: a
  `(no impl of Eq for Color)` shows `user/Color`, not bare `Color`). **Do NOT
  change `concrete_type_name` itself** — its mangled-name call sites
  (`build_mangled_name`) need the bare name.

**Why types, not typecheck or src/.** `Type` is defined in types; both other crates
already depend on types; a helper here is dependency-free and is the single point all
walks reach. The "keep-distinct" advisory survives **at the output level** (conventions
are config values, not copies). Ships with `public-api.txt` regen per the baseline-diff
discipline (the dead exports + the re-export retire; the new walk's surface is added).

`/arch` (owns `Type`) authors the walk + config in `cranelisp-types`; `/dev` typecheck
+ `/dev` src/ re-point their callers; `/qa` owes a narrow repro for the no-impl FQ fix
(two same-named ADTs in different modules, missing impl, assert the FQ name appears).

## Operational implication / Context

- **Stage-B backlog item B4 (theme T1).** Disposition: **high-value-but-deferrable
  (bucket ii); NOT must-fix-before-Phase-H** — correct as shipped. The escalation
  (`audits/s87-findings.md §5 Escalation 1`) is about *not deepening it further* +
  scheduling the consolidation, not rushing it.
- **Process note for `/review`:** future reviews of any `Type`-rendering or
  name-into-message change must ask "does this walk already exist elsewhere? am I
  adding the Nth copy?" before passing — the Wave-0 episode is the case the
  duplication-recurrence memory describes.
