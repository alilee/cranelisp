---
number: 0323
target: /qa
filed_by: /sprint
filed_at: 2026-06-13
sprint_filed: 79
refers_to: tests/spec_platforms_adt.rs (6 round-trip/hash-gate/cache tests), platforms/shapes/, design/arch/platform-interface.md §2 (q-assoc-discovery) §7.2/§7.3, design/arch/fixmes/0289, src/platform.rs::register_platform_in_tc, src/worker.rs::handle_platform
status: open
---

# Complete the platform-ADT round-trip — `shapes` module loading + schema regen (S79 carry → S80)

## Issue

S79 delivered the platform-ADT-round-trip *machinery* (R1 `--link` platform wiring,
0318 platform-fn-IO, the `shapes` fixture, the product-ctor-as-`Def` correction that
made `read_field("w")` reachable) but the **6 `tests/spec_platforms_adt.rs` round-trip
tests ride RED** (failing-not-ignored, ledgered) — the platform-ADT-module-loading path
has never run e2e, and exercising it surfaced one remaining layer that S79 deferred by
user decision (2026-06-13: land the verified correction, finish the round-trip as a
focused follow-up).

**The blocker (Issue 2):** all 6 fail with `type error in platform function 'area'
signature '(Fn [shapes/Rectangle] (primitives/IO primitives/Int))': unknown type
\`Rectangle\` (from module \`shapes\`)`. The platform sig is FQ (`shapes/Rectangle`), but
the test program defines `Rectangle` in its **entry module** (the S79 Wave-0 "simplest"
fixture choice) — so module `shapes` has no `Rectangle` to resolve. Per
`platform-interface.md` §2 (q-assoc-discovery (c)): platform-associated ADT types are
**ordinary importable `.cl` modules** found on the normal module search path (NOT
`CRANELISP_PLATFORM_PATH`). The fixture must make `Rectangle` live in a loadable `shapes`
module the program imports — `(import [shapes [Rectangle]])` — so `shapes/Rectangle`
resolves during the platform sig check.

The typecheck `resolve_named` fix (S79 R2.6 Issue 1) already accepts a product-ctor `Def`
as a type, so once `Rectangle` is *reachable in module `shapes`*, the type should resolve;
this is the first e2e exercise of the platform-type-module load path and may surface
further layers (does the `(platform shapes)` load make `shapes.cl` resolvable / loaded
before the sig check? is `platforms/shapes/shapes.cl` on the search path as module
`shapes`? does `register_platform_in_tc` see the loaded ADT module?).

## Proposed resolution (S80, focused)

1. **`/platform` + `/qa` — fixture**: make `Rectangle` a loadable `shapes` `.cl` module
   (placement + search-path), the test program `(import [shapes [Rectangle]])`; reconcile
   the IO-wrapped sig (0318) with the round-trip's exit/observable witness (the `main`
   returns `IO Int`).
2. **`/dev` int — loading path (if surfaced)**: ensure the `shapes` ADT module is
   loaded/resolvable during `register_platform_in_tc` sig checking (the platform-type
   discovery flow).
3. **`/qa` — schema regen**: once the platform loads, regenerate
   `platforms/shapes/src/shapes.platform-schema` (the S79 placeholder has a sentinel
   layout-hash; the backend generator now emits real `w`/`h` field names post-0319) +
   rebuild the dylib → the dual hash-gate + round-trip + cache-restore go green.
4. **Bundle with related deferred platform/conformance work**: FIXME 0289 items 4-5
   (perturbed-ABI + dispatch-error e2e), 0317 (`main : IO _` enforcement + sweep), 0316
   (import-ambiguity). These are the natural S80 platform/conformance increment.

## Operational implication / Context

S79 closed at ~1195/1202 with the 6 round-trip + 1 intended-RED (`batch_main_pure_int_
return_is_rejected`, 0317) the only reds — both ledgered, failing-not-ignored, durable
records. The round-trip is one fixture layer + schema regen from green; deferred only to
avoid open-ended discovery at S79's end, not because it is blocked on design.
