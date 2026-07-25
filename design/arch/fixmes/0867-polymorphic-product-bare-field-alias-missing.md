---
number: 0867
target: /dev (typecheck)
filed_by: /repl
filed_at: 2026-07-25
sprint_filed: 117
refers_to: spec/05-definitions.md §5.2.6;
  repl/spec.md §3.3;
  tests/spec_field_accessor.rs::bare_alias_resolves_when_field_unique;
  repl/demos/archive/ring4k.demo
status: open
---

# Polymorphic product does not mint its field accessors

## Issue

The Phase 6b REPL replay found that a concrete product mints both its canonical
field accessor and its unique bare convenience alias, while a polymorphic
product mints neither:

```lisp
(deftype (Pair a b) (MkPair [:a fst :b snd]))
(fst (MkPair 42 false))
(Pair.fst (MkPair 42 false))
```

Both accessor forms report an undefined variable. No second `fst` field exists,
so the bare failure is not the specified ambiguity case, and the missing
canonical accessor is independently non-conforming.

`spec/05-definitions.md §5.2.6` makes a unique bare field name an alias of the
canonical `Type.field` accessor without excluding polymorphic products. The
current production guard
`tests/spec_field_accessor.rs::bare_alias_resolves_when_field_unique` covers
only a concrete `Box`, leaving this type-parameter axis untested.

The archived Ring 4K demo now uses ordinary pattern extraction so its
historical FQ-type lesson remains runnable; that demo correction does not
resolve the missing accessors.

## Proposed resolution

`/qa` attributed the missing canonical and bare aliases as one
definition-variant coverage gap and added the Sprint-118 forward-flow row in
`tests/plan/PLAN.md`. `/testing` should now author a narrow,
failing-not-ignored REPL repro that pairs the polymorphic case above with the
existing concrete control and asserts both `Pair.fst` and bare `fst`.

After that reduction, `/qa` will finalize the narrow `/dev` attribution. The
eventual owner should make polymorphic product accessor enrollment mint the
canonical `Pair.fst` definition and the same unique bare
`ModuleEntry::Import` edge as a concrete product, while retaining the existing
duplicate-field ambiguity behavior.

## /qa S118 W1+ ATTRIBUTION FINALIZED (2026-07-25) — retargeted /testing → /dev (typecheck)

The W1 repro landed and REDUCED the axis (`tests/spec_field_accessor.rs`
§"THE CONSTRUCTOR-ARM AXIS", eight-form matrix at HEAD `e15ff20f`): the type
parameter is NOT causal — two polymorphic deftype-level forms mint both
accessors; a CONCRETE distinct-name constructor arm mints neither. **The
defect: accessors are synthesised only from the deftype-LEVEL field list
(plus the same-name single-ctor spelling that reduces to it); a field list
in a named constructor arm whose name differs from the type's contributes
no accessor at all** — every sum type, every distinct-name product,
including this FIXME's `(deftype (Duo a b) (MkDuo …))` case and spec
§5.2.6's own `Option.unwrap` example.

- **Owning seam (single-crate):** `crates/cranelisp-typecheck/src/adt.rs` —
  `synthesise_field_accessors` is invoked only under `if is_product` and
  only over `ctor_infos[0]`; the adjacent comment "Sum/enum fields have no
  total accessor" contradicts spec §5.2.6, which REQUIRES sum accessors and
  already specifies their semantics (partial: succeed on the matching
  variant, runtime panic on mismatch — `Option.unwrap` worked in-spec). No
  open `/spec` question.
- **Fix shape:** synthesise over EVERY constructor arm's field list with
  §5.2.6 partial semantics for multi-arm types; the §8.6.5 bare-alias
  contest classification is untouched (the retained duplicate-field
  negative family in `spec_field_accessor.rs` is the boundary fence). The
  partial-accessor panic face needs its own positive + negative cells in
  the fixing change-set (nothing mints today, so it is untestable until
  then).
- **`class=enumeration-miss` RATIFIED** (`/qa`, vocabulary owner): the
  accessor-source enumeration omits a source family. No re-label.
- Fix is capacity-dependent in S118 (not pre-authorized as a carry; an
  unfixed repro at close needs an explicit user-approved carry). Plan of
  record: `tests/plan/s118-test-plan.md` §6.2.
