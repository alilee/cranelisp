---
number: 0571
target: /dev
filed_by: /repl
filed_at: 2026-07-12
sprint_filed: 108
refers_to: resolution of a fully-qualified symbol reference entered at the REPL
  without a prior import (`collections.vec/count`); the codegen-layer
  "undefined variable" error and its nested double-wrapping. Reproduced post-S108
  via `collections.vec/count` (contrast `primitives/vec-len`, which resolves).
status: open
---

# FQ-symbol reference to an unimported symbol leaks an opaque, doubly-wrapped codegen error

## Issue

Entering a fully-qualified symbol that has not been imported fails at codegen:

```
> collections.vec/count
Error: codegen error at 0..21: codegen failed for /: codegen error at 0..21: undefined variable: collections.vec/count
```

Contrast a fully-qualified reference to a **seeded primitive**, which resolves
correctly:

```
> primitives/vec-len
:(Fn [(primitives/Vec a)] primitives/Int) <closure>
```

So a FQ reference to a not-yet-imported stdlib symbol fails, while a FQ reference
to a seeded primitive succeeds — an asymmetry the user did not expect ("FQSymbol
not recognised").

Two distinct sub-issues:

1. **FQ-ref semantics (normative — for /spec + user).** Should
   `collections.vec/count` resolve — triggering the module load — given the
   fully-qualified name is unambiguous and needs no import to disambiguate? Or is
   an explicit import still required? This is a language-semantics question
   (relates to the prelude-is-implicit-import model, spec §8.6.4) and the user
   arbitrates. Whichever way it lands changes what the correct behaviour is.

2. **Error quality (a defect regardless of #1's answer).** The failure surfaces
   at the **codegen** layer as "undefined variable," and the message is
   **doubly wrapped** — `codegen error … codegen failed for /: codegen error …
   undefined variable`. An unresolved FQ symbol should be caught at **resolution**
   with an actionable message (e.g. "`collections.vec/count` is not in scope — add
   `(import [collections.vec [count]])`"), not leak a codegen internal. This
   violates the "no valid construct produces an opaque error" Design Principle.

## Assessment (severity: medium — opaque error, possibly a missing resolution path)

Sub-issue #2 is a clear defect on its own: whatever the intended FQ-ref
semantics, the diagnostic must be actionable and must not surface from codegen.
Sub-issue #1 may be intended behaviour (FQ ref still needs an import) but then the
error must *say* that instead of "undefined variable."

## Proposed resolution

- **/dev** — route an unresolved FQ symbol through the **resolution-layer**
  diagnostic (not codegen), producing an actionable "not in scope / import it"
  message, and collapse the nested double-wrapping. If, per the /spec answer,
  FQ-ref-without-import *should* resolve (load the module), that is a larger
  change gated on #1.
- **/spec + user** — answer #1 so /dev knows whether the target behaviour is
  "resolve on FQ ref" or "still requires import, but say so clearly."

**This is a DEFECT** — it needs a failing-not-ignored `/testing` repro (byte
level: a bare FQ reference to an unimported symbol yields the actionable error,
not a codegen leak). This FIXME is the scoping record until that repro lands;
once the test exists, this FIXME is deleted (the failing test is the durable
record + trigger).

## Notes

- "codegen failed for **/**" in the message is suspicious — cross-check the
  parse/resolve path for how the `/` namespace separator in
  `collections.vec/count` is being handled (note `primitives/vec-len` — also
  containing `/` — resolves fine, so the split itself works for seeded modules).
- Related to **0570** (private/test module visibility in `/search`).
