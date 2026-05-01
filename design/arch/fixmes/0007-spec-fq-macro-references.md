---
number: 0007
target: /spec
filed_by: /arch
filed_at: 2026-04-26
sprint_filed: 63
refers_to: spec/08-modules.md §8.5.1 (Module-Qualified Names); spec/09-macros.md §9.3 (Macro Resolution); design/arch/sequences/exec-flow-compilation.mmd
status: open
---

# Spec is silent on whether FQSymbol references may resolve to macros

## Issue

§8.5.1 establishes that qualified names `module/name` may reference any module's symbol, with lazy module loading on first reference (line 354: "When a qualified name references a module that has not yet been loaded, the implementation SHOULD attempt to load that module on demand"). The section gives examples for constructors (`core.option/Option.Some`) and trait methods (`core.fmt/Display.show`), but does NOT state whether the resolved symbol may be a **macro**.

§9.3 (Macro Resolution) describes how the expander finds macros — by name in the macro environment — but does not address qualified macro references at all. The grammar admits `(some-mod/some-macro args)`; the spec doesn't say whether that should expand or fall through.

The v4 expander supports it: any FQ form encountered during `expand` triggers `register_module(m2)` + `wait_for_typecheck(m2)`, then looks up the entry in `ST[m2]`; if the entry is a macro, expansion proceeds (with an additional `wait_for_inmem` + `priority_boost_jit` if the macro's code isn't yet jitted). This is the canonical flow in `design/arch/sequences/exec-flow-compilation.mmd`.

`/arch` wants this behaviour authorised by the spec so the v4 implementation is conformant rather than a permissive extension.

## Proposed resolution

`/spec` adds explicit authorisation in one of two locations (or both):

(a) **In §8.5.1 (Module-Qualified Names)**: extend the existing "lazy load on first reference" paragraph with a sentence: *A qualified name may resolve to any kind of symbol, including a macro. When the resolved symbol is a macro, the expander invokes its expansion logic at the qualified call site, just as it would for a bare-name macro reference. The lazy-load behaviour applies equally — a qualified macro reference may trigger registration and typechecking of its defining module.*

(b) **In §9.3 (Macro Resolution)**: add a new subsection (e.g., §9.3.6) titled "Qualified Macro References": *Macros may be invoked through qualified names (`module/macro-name`) without an explicit `import`. The expander resolves qualified macro references identically to qualified function references — it triggers lazy module load (per §8.5.1) and then dispatches to the macro's expansion. There is no syntactic distinction between a qualified macro call and a qualified function call at parse time; the distinction is made when the expander looks up the resolved entry.*

`/arch` recommends **both**: §8.5.1 establishes the principle alongside the existing constructor/trait examples; §9.3.6 elaborates the macro-specific mechanics (the wait-for-typecheck + wait-for-inmem dependency that distinguishes macro calls from value calls).

## Operational implication for v4

The `frontend::expand` facade signature is `expand(sexp, &symbol_tables) †` (per the diagram). Without `&symbol_tables`, the expander could not look up qualified macro references — it would have no access to ST[m2]. Authorising FQ macro refs in the spec ratifies this signature.

The form-by-form streaming model (FIXMEs 0005, 0006) constrains intra-module macro availability to source order; FQ macro refs are NOT constrained by source order — they may target macros in any module that can be registered + typechecked. This asymmetry (within-module = source-order; cross-module = on-demand via FQ + wait) is the natural consequence of the v4 streaming architecture and worth stating explicitly when the spec is updated.

## Context

Surfaced during S63 W2 sequence-diagram authoring. The expansion-side flow in `exec-flow-compilation.mmd` was authored against the spec's silence; `/arch` is filing this FIXME to convert silence into explicit authorisation.

This FIXME is independent of FIXMEs 0005 and 0006 — it can be resolved alone, though resolving all three together produces a coherent module-and-macro spec story.
