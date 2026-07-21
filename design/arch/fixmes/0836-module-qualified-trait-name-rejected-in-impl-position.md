---
number: 0836
target: /spec
filed_by: /stdlib
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/07-traits.md §7.2 (impl); spec/08-modules.md §8.5 (qualified
  references); stdlib/default/test.cl (the blocked cell)
status: open
---

# `impl` accepts only a BARE trait name — `(impl default/Default Slot …)` is rejected

## Issue

Every other reference position in the language accepts a module-qualified name:
`collections.vec/count`, `macros/sconcat`, `default/default` all resolve. The
`impl` form's trait position does not:

```
(import [default [default]])
(deftype Slot Empty (Filled [:Int n]))
(impl default/Default Slot (defn default [] Empty))
⇒ Error: type error at 0..51: unknown trait: default/Default
```

The same `impl` succeeds if `Default` is imported and written bare. So the
trait must be brought into scope by name; there is no qualified escape hatch.

## Why it bites

It makes "implement a trait" and "do not import that trait's name" mutually
exclusive, and those are not always separable concerns.

Concrete blocked case: `stdlib/default/test.cl` deliberately imports the
`default` METHOD ONLY, without the `Default` trait — that method-only import IS
the module's regression guard for the S113 D2 ruling (method-import suffices for
dispatch, spec §7.11.2), and its header says in so many words not to re-add
`Default`. Adding a `Default` impl for a user-defined type to that module — the
cell owed once FIXME 0672 was fixed, which it now is — requires importing the
very name the guard is defined by omitting. There is no way to write both.

The workaround is to move the cell to another module, which is what S115 did.
That is fine once; as a general rule it means any module that guards an
absent-import property can never also implement.

## Request

`/spec` rules whether the trait position of `impl` is intended to accept a
module-qualified name. Both answers are defensible and neither is recorded:

- **Yes** — `impl` is a reference position like any other and the qualified
  form should resolve; this is then a `/typecheck` gap and the error message
  ("unknown trait") is actively misleading, since the trait is perfectly
  well known.
- **No** — an `impl` binds into the trait's own module (Decision 45) and
  requiring the bare name in scope is a deliberate legibility constraint. Then
  spec §7.2 should say so, and the error should say "trait must be imported by
  name" rather than "unknown trait".

Either way the diagnostic needs to change; today it reports a name it can see.

## Context

Found by `/stdlib` during S115 Phase 6b while retiring the stale FIXME-0672
deferral in `stdlib/default/test.cl`. Low priority as a capability — the
workaround is cheap — but the misleading diagnostic is not, and the rule is
currently unwritten either way.
