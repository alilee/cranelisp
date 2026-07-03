---
number: 0490
target: /int
filed_by: /repl
filed_at: 2026-07-03
sprint_filed: 101
refers_to: repl/spec.md §5.1 (error format), root CLAUDE.md §Design Principles (self-documenting REPL)
status: open
---

# Qualified reference to a non-existent module member yields a misleading re-anchored module error

## Issue

Entering a qualified name whose member does not exist in the named module (e.g.
`primitives/vec` — `vec` is a stdlib macro in `collections/vec.cl`, not a primitives
member) produces:

```
user> (primitives/vec 1 2 3)
Error: module error at 0..0: module 'user.primitives' referenced by 'user.primitives/...' not found (referenced by 'user')
```

Three problems: (1) the reference is re-anchored to `user.primitives` — the user typed
`primitives/`, and `primitives` is a real, loaded module, so naming a phantom
`user.primitives` module is actively misleading; (2) the literal `'user.primitives/...'`
ellipsis leaks a placeholder instead of the symbol the user typed; (3) `at 0..0` is a
bogus span. The actionable message is "module `primitives` has no member `vec`" (ideally
with a hint when the bare name resolves elsewhere in scope, e.g. "did you mean `vec`
(collections.vec, via prelude)?").

Found while exercising the S101 redefinition surface (Phase 6a); pre-existing, not
S101-caused.

## Proposed resolution

When the head component of a qualified reference names a module that is loaded/loadable,
report member-not-found against that module with the member name the user typed and the
correct source span — never synthesize a `<current>.<qualifier>` module path in the
message. Fall back to module-not-found only when the qualifier resolves to no module.

## Operational implication / Context

Every user who qualifies a name that happens to be a macro or lives elsewhere hits this;
the current message sends them hunting for a module that never existed.
