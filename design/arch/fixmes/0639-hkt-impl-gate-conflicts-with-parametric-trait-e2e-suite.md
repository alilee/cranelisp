---
number: 0639
target: /design
filed_by: /dev
filed_at: 2026-07-17
sprint_filed: 111
refers_to: design/typecheck/hkt.md §5.4 (the FIXME-0628 impl-target gate) — the `!decl.type_params.is_empty()` arity-independent non-constructor reject BREAKS green release-gate e2e tests; needs /spec + user arbitration
status: open
---

# The 0628 HKT impl-target gate (hkt.md §5.4) conflicts with the release-gate e2e suite's treatment of `(deftrait (X a) …)` as a `*`-kind parametric trait

## Summary

CS-4 item 5 was "implement 0628 per hkt.md §5.4 and flip the check-gate-leak
guard." I implemented the ruled gate (remove the usage-derived `is_hkt`; run
con_var validation for every trait with `!decl.type_params.is_empty()`; reject any
non-type-constructor target arity-independently via `scope_resolve` +
`type_def_view_of`). It is **semantically correct for the REAL prelude** — verified:
the real `stdlib`/`tests/fixtures/preludes` regular traits use the BARE head +
`self` form (`(deftrait Num (+ [a b] self))`), which has EMPTY `type_params`, so the
gate does NOT fire on `(impl Num Int)`.

**But the gate breaks GREEN release-gate e2e tests** that use the `(deftrait (X a) …)`
head form (bare con_var `a`, kind `*` usage) impl'd on concrete types, treating it as
a valid **parametric** trait. Confirmed by building with the gate in and running:

| e2e test (owner `/testing`) | shape | disposition with 0628 |
|---|---|---|
| `spec_05_definitions::deftrait_with_docstring_and_method_docstring_does_not_affect_dispatch` | `(deftrait (Sizeable a) (size [a] Int)) (impl Sizeable Int) (size 42)` asserts `:primitives/Int 42` | **REGRESSES** (green→red; impl rejected) |
| `spec_07_traits::trait_deftrait_impl_in_child_module_imported_dispatch_from_parent` | `(deftrait (X a) …) (impl X <concrete>)` | REGRESSES |
| `spec_07_traits::impl_hkt_arity_neg_prelude_provided_target_wrong_arity_rejected` | wrong-arity HKT reject (message change) | message drift |
| `repl_introspection::bare_user_trait_lookup_impl_section_lists_type_not_others` | introspection over `(deftrait (X a)) (impl X <concrete>)` | REGRESSES |
| `repl_introspection::impl_form_display_result_is_exactly_impl_trait_for_type` | same | REGRESSES |

(Full trait/introspection sweep with the gate in: 7 e2e failures across
`spec_07_traits` (2), `spec_05_definitions` (1, excl. the pre-existing frontend RED),
`repl_introspection` (2), plus a message-drift neg.)

## Why no narrower gate resolves it

The 0628 repro (`(deftrait (Zeroable a) (zed [] :a)) (impl Zeroable Int)` → codegen
leak) and the e2e tests (`(deftrait (Sizeable a) (size [a] Int)) (impl Sizeable Int)`
→ works) are the **SAME SHAPE** — a `(Name var)` head with the con_var used only
BARE (never applied `(f a)`), impl'd on a primitive. There is no usage-based or
arity-based discriminator that rejects Zeroable-on-Int while accepting
Sizeable-on-Int. So the gate necessarily either rejects both (breaking the e2e
suite) or accepts both (leaving the 0628 leak).

## The unresolved question (needs /spec + user)

Is a bare-con_var `(deftrait (X a) …)` — where `a` is NEVER used applied — an **HKT
trait** (kind `* -> *`, invalid on a primitive per spec §7.2.3) or a **`*`-kind
parametric trait** (impl'able on concrete types)?

- **hkt.md §5.4 / FIXME 0628 / spec §7.2 EBNF** say `(deftrait (trait_name con_var))`
  is *unavoidably* HKT (§7.1.1: there is no `*`-kind parametric-trait syntax; a
  `*`-kind trait uses `self` + empty `type_params`).
- **The release-gate e2e suite** encodes the opposite: `(deftrait (X a)) (impl X
  Int/Color)` is a valid parametric trait that dispatches. These are `/testing`-owned
  green tests asserting SUCCESS, not defect guards.
- **spec §7.2.1** ties a con_var's arity to its APPLIED usage (`(f a)` ⇒ arity 1). A
  never-applied con_var has undetermined arity — a degenerate/underspecified case the
  spec does not directly address.

## Landing path (a coordinated cross-skill wave, NOT a /dev-only carry)

If the ruling is "bare-con_var `(X a)` is HKT and invalid on non-constructors":
1. **/spec + user** confirm the semantics (§7.2 note on never-applied con_vars).
2. **/testing** migrates the ~7 e2e tests to the `self`-form
   (`(deftrait Sizeable (size [self] Int))`), and adds the 0628 rejection matrix
   (applied/bare × primitive/wrong-arity-ADT/well-kinded-ADT) routed in hkt.md §5.4.
3. **/dev (typecheck)** re-lands the gate AND migrates ~24 crate unit-test fixtures
   from the `(X a)` / `type_params: ["a"]` + `TypeVar("a")` mismodel to the self-based
   form (empty `type_params`, `SelfType` methods). NOTE: constraint-carrying fixtures
   (`register_num_trait_inline`, `register_num_for_int`, the inline `Double` decl)
   REQUIRE `SelfType` (not just empty `type_params`) so the `Num self` constraint
   rides `self` for constrained-fn detection; dispatch-only fixtures work with empty
   `type_params` alone. (This migration was prototyped in CS-4 and reverted with the
   gate — the mechanics are known and green-verified, but it is scope-explosion for an
   "incremental adjacent carries" change-set.)
4. Sibling: `registry.rs::register_trait_decl` (`:117–123`) uses the SAME usage-derived
   HKT guard, so a bare-con_var trait registers via the REGULAR path, not
   `register_hkt_trait` — the root of the companion display defect (`(unwrap 7)` prints
   `:a 7` not `:primitives/Int 7`, FIXME-0628 body). Fixing the impl gate without the
   registration guard leaves that inconsistency.

## What CS-4 landed instead

CS-4 landed the other four items (I-1 diagnosed-error rendering, 0590-R1/OA-1
resolved-overload benign exemption, AP-1 clause-result written-var polymorphism, 0595
Principle-18 rigid-unify + teardown hardening) and **reverted 0628** (gate + the
prototyped fixture migration) pending this arbitration — landing the gate as designed
would ship a red release gate.
