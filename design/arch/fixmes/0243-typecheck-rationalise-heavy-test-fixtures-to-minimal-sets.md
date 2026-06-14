---
number: 0243
target: /typecheck
filed_by: /sprint
filed_at: 2026-05-31
sprint_filed: 73
refers_to: crates/cranelisp-typecheck/src/builtins.rs (#[cfg(test)] FixtureBuilder + the five presets), crates/cranelisp-typecheck/src/checker.rs (TestFixture::new / with_content), design/arch/fixmes/0241-arch-synthetic-module-assembly-leaves-typecheck-builder-vocabulary.md, design/arch/fixmes/0239-arch-instantiate-module-symbol-table-from-source-facade.md
status: resolved
---

> **S82 progress (adt/traits/checker + shared-helper remainder narrowed —
> COMPLETE; FIXME resolved):** The S81-deferred remainder is now narrowed. All
> `TestFixture::new()` (= `FixtureBuilder::full()`) call sites in the four
> remaining files are replaced with minimal per-test presets via local
> `tf*()` helpers; every affected test module is green under the narrower seeds.
>
> - **`adt.rs` (22 tests):** all 20 call sites → `tf()` (empty builder) by
>   default, since each test registers its OWN ADTs and (where it has typed
>   builtin fields) seeds the matching `primitives` Import edge inline. Three
>   internal-constructor tests (`test_is_internal_constructor`,
>   `test_is_internal_constructor_through_import`,
>   `test_exhaustiveness_excludes_internal_constructors`) → `tf_io()`
>   (`with_builtin_type_names().with_io()`) — they read `Bind`'s `internal:true`
>   discriminator off the seeded `IO` ADT. One product-type test
>   (`test_register_product_type_with_fields`) → `with_builtin_type_names()`
>   (its `:Int`/`:Bool` field-type Import edges need the scalar IntrinsicType
>   entries to exist).
> - **`traits/tests.rs` (46 tests):** the four startup-negative tests
>   (`test_no_traits_at_startup`, `test_no_impls_at_startup`,
>   `test_no_core_traits_at_startup`, `test_no_operators_at_startup`) → `tf()`
>   (empty — the most honest "nothing seeded" position). The trait-decl /
>   trait-impl / resolution tests + the shared `tc_with_prims()` helper →
>   `tf_prims()` (`with_builtin_type_names().with_primitives()` — impl `target`
>   is `Int`, bodies call `add-i64`).
> - **`checker/tests.rs` (40 tests):** the bulk → `tf()` (empty) — these build
>   their own modules and seed exactly what they need. Per-test bumps: the three
>   trait-impl-resolution / dispatch-fallback tests
>   (`test_impl_resolution_chain_follows_not_universe_scans`,
>   `test_trait_impl_write_lands_in_trait_home_not_writer`,
>   `test_trait_method_dispatch_falls_back_to_prelude_outer_scope`) →
>   `tf_prims()`; the qualified-sum-ctor test
>   (`fq_sum_ctor_resolves_in_pattern_from_unimporting_module`) → `tf_macros()`
>   (`with_builtin_type_names().with_macros_sexp()` — resolves `macros/SCons`);
>   the internal-ctor-gate test (`prelude_fallback_internal_ctor_gate_rejects_bind`)
>   → `tf_io()`. **`test_bare_module_has_root_contents_only` LEFT at `full()`**
>   — it VALIDATES the fully-seeded world (special forms at root, primitives,
>   IO, macros) while asserting none leak into a bare module; narrowing would
>   defeat the test's purpose (same rationale as S81's `test_trace_not_auto_imported`).
> - **Shared helpers (highest-risk, done last, one per test-run):**
>   `infer/tests.rs::tc()` → `with_builtin_type_names().with_primitives().with_macros_sexp()`
>   (inference tests reference `macros/sconcat`; no IO/special-form lookups; all
>   82 green). `program/tests.rs::tc_with_prims()` →
>   `…with_macros_sexp().with_io()` (program tests reference `Bind`/`Pure`
>   directly + macros; only `with_special_forms()` dropped — no test probes the
>   special-form entries; all 84 green).
>
> **Order-sensitive preset footgun:** did NOT require the dependency-closure
> step in `FixtureBuilder::seed()` — the bootstrap order
> (`with_builtin_type_names()` before `with_primitives()`/`with_macros_sexp()`/
> `with_io()`) was applied explicitly at each helper. No deferred remainder.
> Two `full()` sites remain by design (`test_trace_not_auto_imported` in
> `builtins.rs`, `test_bare_module_has_root_contents_only` in `checker/tests.rs`)
> — both VALIDATE the fully-seeded world and are correctly left at `full()`.
> Full `cargo nextest run -p cranelisp-typecheck` green (387 tests).

> **S81 W-A progress (builtins.rs cluster narrowed; remainder OPEN):** The
> safe, self-evident cluster in `crates/cranelisp-typecheck/src/builtins.rs`
> (the file this FIXME `refers_to`) has been narrowed from `TestFixture::new()`
> (= `FixtureBuilder::full()`) to the minimal preset each test consumes. ~35
> sites narrowed; full `builtins::tests` module green under the narrower seeds
> (46 tests pass). Mapping applied:
> - primitive-scheme reads (`test_add_i64_scheme`, `test_vec_*_scheme`,
>   `test_primitives_registered`, `test_*_have_docstrings`, …) →
>   `FixtureBuilder::new().with_primitives()` (the `seed_test_primitives`
>   schemes construct `Type::Int`/`Type::ADT(primitives/Vec…)` directly — no
>   dependence on `with_builtin_type_names()`).
> - Sexp/SList/sconcat reads → `.with_builtin_type_names().with_macros_sexp()`.
> - `quote-sexp` (lives in primitives, references `macros/Sexp`) +
>   `test_registration_order_no_panic` →
>   `.with_builtin_type_names().with_macros_sexp().with_primitives()`.
> - IO ADT reads → `.with_builtin_type_names().with_io()`.
> - absence/negative tests (`test_no_traits_at_startup`,
>   `test_no_operator_symbols_at_startup`) → `FixtureBuilder::new()` (empty).
> - `test_special_forms_registered` was already narrowed (pre-S81).
> - `test_trace_not_auto_imported` LEFT at `full()` — a negative test over the
>   whole seeded world (Trace is never seeded per Decision 0040, so the
>   assertion is meaningful against a fully-populated table; narrowing adds
>   risk for no real weight reduction).
>
> **Remainder OPEN (deferred — the order-sensitive / footgun clusters the
> "Operational implication" warns about):**
> - `crates/cranelisp-typecheck/src/adt.rs` (~20 `TestFixture::new()` sites) —
>   each test registers its own ADTs; some use **typed ctor fields** that need
>   the field types (`Int`/`Bool`/…) in scope, hitting the `Int`-not-in-scope
>   setup-failure footgun noted in `crates/cranelisp-typecheck/CLAUDE.md
>   §Testing`. Per-test inspection required; not a batch narrowing.
> - `crates/cranelisp-typecheck/src/checker/tests.rs` (~40 sites) and
>   `crates/cranelisp-typecheck/src/traits/tests.rs` (~12 sites) — diverse
>   needs; many exercise module-locality / trait resolution that depends on
>   specific preset combinations.
> - The shared `tc()` / `tc_with_prims()` helpers (one `TestFixture::new()` each
>   in `infer/tests.rs` + `program/tests.rs`, and similar helpers in
>   adt/checker/traits) back MANY tests with diverse needs — narrowing a shared
>   helper is the highest-risk move (one wrong preset breaks every dependent
>   test) and is explicitly the order-sensitive cluster to do last/carefully.
>
> FIXME left OPEN for the adt/checker/traits + shared-helper remainder.

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
