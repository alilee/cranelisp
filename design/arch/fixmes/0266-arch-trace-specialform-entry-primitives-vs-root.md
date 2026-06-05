---
number: 0266
target: /arch
filed_by: /sprint
filed_at: 2026-06-05
sprint_filed: 76
refers_to: src/bootstrap.rs (trace SpecialForm registration), design/arch/tracing.md §3.1 §2.4, design/arch/principles/10-parser-keywords-distinct-syntax.md, design/arch/fixmes/0241-arch-synthetic-module-assembly-leaves-typecheck-builder-vocabulary.md (corrected Trace row), spec/04-expressions.md §4.12.4
status: open
---

# Bootstrap registers `trace` as a SpecialForm entry in `primitives` — contradicts the root-special-form ruling

## Issue

S76 Wave 2's synthetic-module mount (`src/bootstrap.rs`) reconstructs the deleted
`register_builtins` body faithfully — including registering a `trace` `SpecialForm`
metadata entry **in the `primitives` module**, as the pre-ruling body did.

The 2026-06-04 user ruling (tracing.md §3.1, Principle 10 two-category amendment,
spec §4.12.4) makes `trace` a **root special form**: no import, no module path,
NO `primitives/trace`. The corrected FIXME 0241 Trace row says "the *form* `trace`
is a root special form (no primitives entry)". The structural special forms
(`defn`/`let`/`if`/`match`/…) have their SpecialForm metadata entries at root `""`.

The mount's fidelity-to-original was the correct Wave-2 goal (gate review:
fidelity EXCELLENT); this is the one residual where the original body predates the
ruling.

## Proposed resolution

`/arch` confirms the target placement — expected: the `trace` SpecialForm metadata
entry moves from `primitives` to root `""`, alongside the other root special forms
(self-documenting-REPL metadata for `/info trace` etc.); the `Trace`/`TraceCall`
ADT entries + accessors STAY in `primitives` (form/ADT asymmetry, spec §3.2.4).
Then route the one-line mount change to `/dev (int)` (src/bootstrap.rs) — likely a
Wave-3/4 slipstream. Verify no introspection path (`/imports`, `/exports primitives`)
asserts the old placement.

## Operational implication / Context

Cosmetic-to-small: recognition is parser/typechecker-side (`Expr::Trace`) and does
not consult this metadata entry for dispatch; the entry affects REPL introspection
listings. Flagged by the S76 Wave-2 gate review (NOTE 5).
