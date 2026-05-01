---
number: 0005
target: /spec
filed_by: /arch
filed_at: 2026-04-26
sprint_filed: 63
refers_to: spec/09-macros.md §9.3.4 (Module-Wide Availability); spec/05-definitions.md §5.13.2 (Macros — Definition Ordering); design/arch/sequences/exec-flow-compilation.mmd
status: open
---

# Macro availability spec describes a pre-pass model that v4 does not implement

## Issue

Two spec sections describe macro availability in terms of a **pre-pass extraction**:

- **§9.3.4 Module-Wide Availability**: "The compiler extracts and compiles all `defmacro` forms in a pre-pass before processing other forms. This means a macro MAY be used before its `defmacro` form in source order."
- **§5.13.2 Macros**: "The compiler uses a two-pass model: all `defmacro` forms are extracted and compiled in a pre-pass before other forms are processed. This means a macro may be used before its `defmacro` form in source order. This is consistent with Clojure's model where macros are available module-wide."

The v4 form-by-form scheduler (`design/arch/sequences/exec-flow-compilation.mmd`) does not do this. Within a module, forms are processed strictly in source order: a defmacro becomes available only AFTER its form has been typechecked and JIT-codegened. A reference to a macro before its defmacro form is therefore not expandable — it would pass through to the AST builder as a regular function call (the same behaviour the spec already mandates for the REPL).

The forward-reference example in §5.13.2 — `(defn f [x] (double x))` followed by `(defmacro double [x] ...)` — would NOT work under v4. `f` is processed first, the expander sees `double` as an unknown symbol (no macro entry yet), passes through; later `double` is defined as a macro but `f`'s body has already been built as a function call.

## Proposed resolution

`/spec` decides one of:

(a) **Drop the pre-pass model — embrace form-by-form.** Strike the "pre-pass" and "MAY be used before its defmacro form" sentences from both §9.3.4 and §5.13.2. State the actual rule: *within a module, a macro is available to forms that follow its defmacro in source order; forms that precede the defmacro see the symbol as undefined (passes through to AST builder, same as REPL behaviour)*. Removes the file/REPL discrepancy. The Clojure-comparison sentence is dropped — Cranelisp diverges intentionally because form-by-form streaming is the v4 architecture.

(b) **Reinstate the pre-pass in v4.** Re-architect the scheduler to do an eager defmacro scan before form-by-form processing. Significant cost: contradicts the form-by-form streaming model that motivates pipeline-v4 (`design/arch/principles.md`, `design/arch/overview.md`); the scheduler would need a separate phase + dependency tracking for "find all defmacros, compile them, then proceed". `/arch` rejects this option as misaligned with the v4 target architecture.

(c) **Hybrid: pre-pass within module, streaming across modules.** Module's defmacros are extracted up-front (pre-pass per module); other forms then process form-by-form. Adds a phase but preserves the spec wording. `/arch` is open to this if `/spec` deems the forward-reference capability load-bearing for users — but recommends (a) on simplicity grounds.

`/arch` recommends **(a)**. The forward-reference convenience is small; the implementation cost of preserving it is large; the form-by-form principle is a design pillar.

## Context

Surfaced during S63 W2 sequence-diagram authoring (`design/arch/sequences/exec-flow-compilation.mmd`). The diagram's typecheck-phase loop processes forms in source order with no pre-pass; the spec's wording must be reconciled before the diagram can be cited as canonical.

If (a) is adopted, §5.13.2's example must be rewritten so the defmacro precedes its callers. The "consistent with the two-pass model described in §5.13.2" cross-reference in §9.3.4 also disappears.
