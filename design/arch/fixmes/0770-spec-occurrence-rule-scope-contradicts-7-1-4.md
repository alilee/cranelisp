---
number: 0770
target: /spec
filed_by: /dev
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/07-traits.md §7.1.1 (occurrence rule prose) vs §7.1.4 (Type
  Expressions in Signatures — the `Convertible` example) +
  crates/cranelisp-typecheck/src/traits/registry.rs (the S115 W4 enforcement,
  shipped at the NULLARY scope) + tests/spec_07_traits.rs (five GREEN cells) +
  tests/spec_qualified_name_sweep.rs::deftrait_method_qualified_type_ref_equals_bare
status: open
---

# §7.1.1's occurrence-rule PROSE contradicts §7.1.4's own example; the S115 enforcement ships at the nullary scope only

## Issue

S115 W4 landed the FIXME-0709 declaration-time occurrence-rule reject
(`register_trait_decl`, conventional bare-head traits only; HKT exempt). Reading
§7.1.1's prose LITERALLY — "a method that mentions the implementing type
**nowhere** … MUST be rejected" — over-rejects a shape the spec itself blesses
and the suite pins GREEN:

1. **§7.1.4's own example.** `(deftrait Convertible (convert [:String s] Int))`
   is presented as a legal signature ("`s` is String, not self"). It mentions the
   implementing type nowhere, so §7.1.1's prose rejects it.
2. **The method-level-type-variable form.** `(deftrait Num2 (add2 [:a x :a y] :a))`
   — §7.1.4 permits method-level type variables (`a`, `b`), and §7.3.6's own open
   question names "method-level type variables only" as the candidate answer for
   a non-`self` parameter in a conventional trait. Five spec-traceable cells pin
   this GREEN today: `spec_07_traits::{deftrait_method_annotated_named_param_accepted,
   impl_bare_type_target_dispatches_control,
   impl_qualified_primitive_type_target_resolves_to_canonical,
   trait_path_resolution_unaffected_by_mint_fence}` and
   `spec_qualified_name_sweep::deftrait_method_qualified_type_ref_equals_bare`.
   The strict rule turns all five RED.

**What shipped, and why.** Both of §7.1.1's WORKED malformed examples are
NULLARY (`(zed [] Int)`, `(zed [] :a)`), and both its worked accepted examples
carry a parameter or a `self` return. So the implementation enforces exactly the
nullary corner: **reject iff the method has NO parameters AND no `self` anywhere
in the signature.** That satisfies every worked example on both sides of §7.1.1
while leaving §7.1.4 intact. The two FIXME-0709 REDs flip; nothing else moves.
The scope is stated in the code comment at `registry.rs` and fenced by the unit
cell `traits::registry::tests::occurrence_rule_shipped_scope_accepts_annotated_param_with_concrete_return`.

## Proposed resolution

`/spec` frames the question for the user; `/dev` implements whichever way it is
ruled. The fork is genuine, not a wording tidy:

- **(a) Narrow §7.1.1 to the nullary corner** (matches what shipped and every
  worked example). §7.1.4 stands unchanged; a parameterised method always has an
  argument position to dispatch on, even when that position is a concrete type or
  a method-level type variable. §7.1.1's prose is amended to say so.
- **(b) Keep the broad prose and RETIRE the §7.1.4 `Convertible` example + the
  method-level-type-variable form** for conventional traits. Then the five GREEN
  cells above encode a wrong-accept and must be re-decided by `/qa`/`/testing`,
  and `/dev` widens the predicate to `!method_mentions_self(method)`
  (the predicate is already written and unit-tested for the nested/`Fn`-position
  cases — only the nullary guard would be dropped).

Note for (b): the REPL display those cells pin (`(add2 3 4)` → `:a 7`, an
UNRESOLVED type var in the result position) is itself evidence the broad reading
is describing a real defect — a conventional trait whose methods never mention
`self` attaches its constraint to a variable that appears nowhere in the method
type, so nothing dispatches on it.

## Context

- `design/typecheck/traits.md` §2 "Occurrence-rule enforcement (§7.1.1, S115 —
  FIXME 0709)" — the design of record; its boundary paragraph ("Do NOT reject on
  concrete return alone; reject only on the conjunction no-param-occurrence ∧
  no-self-return") is what the strict reading formalises, and it does not
  anticipate the §7.1.4 collision.
- Enforcement seam: `crates/cranelisp-typecheck/src/traits/registry.rs`
  (`register_trait_decl`, after the HKT branch returns); predicate
  `traits/type_resolve.rs::method_mentions_self`.
- Flipped by the shipped scope: `tests/nondispatchable_trait_method_0709.rs`
  cells (i) and (ii). Held GREEN: cells (iii) `(zed [] self)` and (iv)
  `(size [x] Int)`.
