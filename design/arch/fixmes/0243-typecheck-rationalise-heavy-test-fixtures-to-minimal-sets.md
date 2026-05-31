---
number: 0243
target: /typecheck
filed_by: /sprint
filed_at: 2026-05-31
sprint_filed: 73
refers_to: crates/cranelisp-typecheck/src/builtins.rs (#[cfg(test)] FixtureBuilder + the five presets), crates/cranelisp-typecheck/src/checker.rs (TestFixture::new / with_content), design/arch/fixmes/0241-arch-synthetic-module-assembly-leaves-typecheck-builder-vocabulary.md, design/arch/fixmes/0239-arch-instantiate-module-symbol-table-from-source-facade.md
status: open
---

# Rationalise heavy typecheck test fixtures to minimal per-test sets (deferred)

## Issue

Sprint 73's Tier-3 wave (commit `e7470e1`) replaced the all-or-nothing
`seed_synthetic_modules`/`seed_test_primitives` monolith with composable
`FixtureBuilder` presets — but to keep the ~110 existing `TestFixture::new()`
call sites green without a mass rewrite, `TestFixture::new()` still delegates to
`FixtureBuilder::full()`, which seeds **all** primitives + builtins (special
forms, Int/Bool/Float/String/Vec, the `macros` Sexp/SList module, the IO ADT,
and every Ring 0/1/3 primitive Def).

The debt: most tests need a *tiny* slice of that world, but pay for the whole
mount on every fixture construction. The fixtures are now far heavier than the
typical test requires.

## Proposed resolution (DEFERRED — user-arbitrated 2026-05-31)

The composable mechanism to fix this already exists: `TestFixture::with_content(builder)`
+ the five opt-in presets. The deferred work is to **walk the ~110 sites and
narrow each to the minimal preset set it actually consumes** (e.g. a pure
arithmetic-inference test wants only `with_primitives()`; a module-resolution
test may want none of the synthetic content). Once narrowed, `full()` becomes a
rarely-used convenience rather than the default, and most fixtures construct a
small, legible starting position.

This could plausibly rationalise the common case down to a very small default
set. Scope it as a mechanical-but-careful per-test narrowing pass; correctness +
green tests dominate (do not chase maximal minimalism into breakage).

## Operational implication / Context

- **Deferred by explicit user direction** at S73 Tier-3 close: "the debt is that
  the test fixtures are now way heavier than most tests should require because we
  mirror all the primitives and builtins. this could be rationalised back to a
  very small set. but this work can be deferred."
- No blocker: the API (`with_content` + presets) is in place; this is purely a
  call-site narrowing pass, no new mechanism required — *unless* the narrowing
  surfaces a footgun in the order-sensitive preset composition (presets must be
  applied in bootstrap order; e.g. `with_macros_sexp()` needs
  `with_builtin_type_names()` first to resolve `Int`). If that bites during the
  narrowing pass, add a dependency-closure step to `FixtureBuilder::seed()` as
  part of this FIXME.
- Coordinate with FIXME 0241 (Tier-1/Tier-2 builder vocabulary — the foundation
  these presets sit on) and FIXME 0239 (the rejected instantiate-from-source
  premise — fixtures build from constructed values, which this pass continues).
