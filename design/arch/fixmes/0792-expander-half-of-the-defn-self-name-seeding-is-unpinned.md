---
number: 0792
target: /dev (src)
filed_by: /review
filed_at: 2026-07-21
sprint_filed: 115
refers_to: src/expander.rs::expand_defn (the S115 W6 defn self-name seeding,
  fab0b9ac) — no unit pin; and three of the six new
  src/process_form/macro_resolution.rs::tests cells assert only absence.
status: open
---

# The MIRROR half of the §2.5 self-name fix ships unpinned — and half the new shield pins carry no positive control

## Severity
Important (METHOD §2.2 — a fix lands with a unit test at the seam the bug lived
at; the mirror class is exactly what an unpinned twin re-opens)

## Issue

### 1. `expand_defn`'s seeding has zero test coverage

`expansion-qualification-scope.md` §2.5 rules that BOTH walks seed the defn name
into its own body scope, and the W6 change-set does so — `qualify_defn` and
`expander::expand_defn` carry byte-identical blocks. But the six new unit cells
all live in `process_form::macro_resolution::tests`; `src/expander.rs`'s test
module gained **nothing**. Its existing scope cells
(`defn_param_shadows_zero_arg_macro`, `let_binder_and_body_shadow_zero_arg_macro`,
`match_pattern_var_shadows_zero_arg_macro`) cover params/let/match binders — none
covers the defn NAME.

This is not cosmetic. On the expander side `shadows` gates **macro expansion**,
so the seeding is a real semantic change: a module-scope macro whose name
collides with a `defn` being defined no longer expands inside that defn's body.
That is the correct §8.6.3 reading and `/design` authorised it — but it is a
shipped behaviour change with no standing guard, and reverting the expander half
alone leaves the whole suite green. The one-sided-mirror failure mode the
project keeps paying for is here in its inverted form: two-sided fix, one-sided
test.

**Ask:** a cell in `src/expander.rs`'s test module mirroring
`qualify_seeds_defn_name_into_its_body_scope` — a zero-arg macro `g` in the
resolver, input `(defn g [] (g))`, assert the body's `(g)` is NOT expanded (the
existing `expand_zero_arg_macro_outside_defmacro_name_still_recognized` cell is
the ready-made positive control), plus the multi-arity twin.

### 2. Three of the six qualify cells assert only absence

The W6 delivery claim is "six unit pins each with a positive control so the
shield is not a blanket skip." Verified against source, **three** carry one:
`qualify_holds_quoted_datum_verbatim` (`dm/wrap` still qualifies),
`qualify_quasiquote_holds_template_but_qualifies_live_unquote` (`dm/wrap` in the
live unquote), `qualify_holds_defmacro_name_and_params_verbatim` (`dm/wrap` in
the clause body). The other three —
`qualify_quasiquote_nested_unquote_is_not_live`,
`qualify_seeds_defn_name_into_its_body_scope`,
`qualify_seeds_defn_name_into_multi_arity_variant_bodies` — assert only that a
name did NOT qualify. Each would pass under a blanket "qualify nothing here"
regression. They are rescued only by their siblings' controls, which is
coupling, not a control.

**Ask:** add a free defining-module reference to each of those three fixtures
and assert it still qualifies (e.g. `(defn f [x] (f (wrap x)))` with `wrap`
in `dm`).

## Proposed resolution

Both asks above, in one `/dev`(src) change-set. No production-code change is
implied by this FIXME — the shipped behaviour is correct as designed; it is the
standing guard that is missing.

## Context

`/review`(src) S115 W6, change-set `fab0b9ac`. The quote shield itself is
**correct**: `quote_head`'s three-way classifier is behaviour-preserving at both
pre-existing call sites (`Some(Unquote) | None => {}` reproduces the old
`None => {}` fall-through exactly), and `qualify_shield_qq`'s nesting math is a
node-for-node mirror of `expander::shield_qq` (live at `qq_depth == 0`; nested
`quasiquote` +1; unquote under a nested quasiquote −1; nested `(quote …)` NOT
short-circuited, descending at the same depth; brackets at the same depth;
atoms verbatim). No off-by-one.
