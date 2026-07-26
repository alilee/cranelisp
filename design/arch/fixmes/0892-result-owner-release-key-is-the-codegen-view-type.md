---
number: 0892
target: /design
filed_by: /dev
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/int/result-owner.md §1.1 steps 1–2, §4.3, §5 row "missing/non-concrete type at typed exit"; src/result_owner.rs::release_key
status: open
---

# The result owner's release key is the codegen-view `ConcreteType`, not a re-narrowing of the observed `Type`

## Issue

`result-owner.md` §1.1 specifies the owner constructor as:

> 1. narrows `Type → ConcreteType` (`ConcreteType::from_type`, types-owned);
> 2. classifies that `ConcreteType` …

and §5 makes a narrowing failure a **hard located/invariant error**. That
assumes every clean typed-exit result type is concrete. **It is not**, and the
counterexamples are spec-required REPL displays, not corner cases:

| REPL input | observed `Type` | today's display (`repl/spec.md` §1.5 / §4.1) |
|---|---|---|
| `[]` | `(primitives/Vec t1)` | `:(Vec a) []` |
| `None` (prelude `Option`) | `(primitives/Option t2)` | `Option.None` |

Implemented literally, the §1.1 narrowing turned both of these into

```
Error: codegen error at 0..0: program result type `(primitives/Vec t1)` is not
concrete at the typed exit of module `user` …
```

which reds `repl_introspection::display_empty_vec_value` and
`repl_introspection::prelude_option_none_value_display_neg_definition_metadata`.

The deeper point is that the re-narrowing is a **second derivation of a
question backend already answered**, and it can disagree with backend's answer.
Backend keys the result-root pre-request off the compiled body's `MonoExpr`
type (`compile_to_module`'s `result_roots`, `lib.rs:672-699`), which for a
non-strictly-concrete body comes from `MonoExpr::lenient_from_expr` — that walk
fills a non-concrete node with the `ConcreteType::Int` placeholder. So for `[]`
backend's result root is `Int`, backend emits **no glue**, and int re-narrowing
the *observed* type would either hard-error (as above) or, worse, demand a key
backend never published. Either outcome is int reaching a different verdict
from the producer — the §4.1 "never re-derive backend's type encoding" rule
applied to the type itself rather than to the symbol spelling.

## Proposed resolution

Ratify (or correct) what W4 implemented, in `result-owner.md` §1.1/§4.3/§5:

- the release key is the result-producing entry's **`codegen_view` body
  `ConcreteType`**, read in the SAME pass that produces the code pointer (which
  is already §4.3's stated rule, applied to the type as well as the pointer),
  with the `IO` head stripped by the same rule backend's `result_roots` applies;
- `ConcreteType::from_type` over the observed `Type` becomes the **fallback**
  for an entry with no published codegen view, and a narrowing failure THERE
  keeps §5's hard-error status;
- §5's "missing/non-concrete type at typed exit" row is restated accordingly:
  the invariant that must hold is *"int keys on what the producer keyed on"*,
  not *"the observed display type is concrete"*.

`src/result_owner.rs::release_key` + `strip_io_head` are the as-built shape and
carry this rationale inline; the unit rows are
`codegen_view_type_is_the_release_key_not_the_observed_type` and
`codegen_view_io_head_is_stripped_to_the_inner_type`.

## Context

Consequence worth recording for whoever rules: under this shape an unpinned
`[]` at the REPL still leaks its allocation, because backend emitted no glue
for a root it saw as `Int`. That residue is the **lenient-view placeholder**
gap (a typecheck/`lenient_from_expr` question), NOT a result-owner gap — the
owner cannot release what was never emitted, and it is exactly the pre-0745
behaviour for those inputs, so W4 introduces no regression there. If `/design`
wants that closed, it is a separate row against the lenient view, and it wants
`/qa` cover of its own.

Filed from S118 W4 (`/dev`, int/exe-bundle) while implementing §8 slice I4.
