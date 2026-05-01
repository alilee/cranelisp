---
number: 0006
target: /spec
filed_by: /arch
filed_at: 2026-04-26
sprint_filed: 63
refers_to: spec/09-macros.md §9.12 (Bootstrapping Order); design/arch/sequences/exec-flow-compilation.mmd; design/arch/overview.md
status: open
---

# Bootstrapping spec describes a two-pass model that v4 replaces with parse-time structural extraction + form-by-form

## Issue

§9.12 Bootstrapping Order describes prelude loading as a **two-pass** sequence:

1. **Pass 1 — Type registration**: All `deftype` forms are scanned, parsed to AST, and registered in the type checker. This makes constructors available for use in macro bodies.
2. **Pass 2 — Sequential compilation**: Forms processed in source order; deftype forms skipped (already registered in Pass 1); defmacros compiled then registered; other forms expanded → AST → typechecked → compiled.

The v4 form-by-form scheduler (`design/arch/sequences/exec-flow-compilation.mmd`) does NOT match this:

- **No Pass 1**. Type registration is form-by-form. A `deftype` becomes available only AFTER its form is processed (just like defns and defmacros).
- **Structural decls extracted at parse time**, not in Pass 1. `frontend::parse` returns `Vec<Sexp> + structural decls`; structural decls (imports, exports, platforms, mod) are written to the SymbolTable via `write_structural_decls` BEFORE the form-by-form loop begins. But these are MODULE-LEVEL declarations (the `(mod foo)`, `(import [bar [*]])`, `(export [...])`, `(platform ...)` forms) — NOT type / value / macro definitions. Deftypes, defns, defmacros remain in the form stream and are processed sequentially.
- **Pass 2 "skipping" doesn't apply**. Every form is processed. Deftypes are NOT skipped — they go through expand → build_form → check_form like any other form (becoming a `ModuleEntry::Def` with `DefKind::TypeDef` or similar).

The §9.12 model assumes module-wide visibility for types and macros via pre-passes. v4 enforces strict source-order visibility within a module.

The four "ordering ensures" claims in §9.12 do not all survive v4:

| §9.12 claim | v4 reality |
|---|---|
| "Macro bodies can reference all type constructors (from Pass 1)" | Only constructors from `deftype` forms BEFORE the macro's defmacro |
| "Macro bodies can call helper functions defined earlier in the file" | Yes — same as v4 |
| "Macro bodies can use earlier macros" | Yes — same as v4 (with the additional v4 mechanism: macro must be JIT-codegened before the form using it can be expanded) |
| "User code can use all macros defined above it" | Yes — same as v4 |
| "(implicit) defmacro MAY appear at any point" | Yes, but availability bounded by source order (not module-wide) |

## Proposed resolution

`/spec` decides one of:

(a) **Rewrite §9.12 to describe form-by-form streaming.** Replace the two-pass narrative with: *Cranelisp processes a module form-by-form in source order. Structural declarations (`mod`, `import`, `export`, `platform`) are extracted at parse time and made available to the typechecker before any form is processed. All other forms — `deftype`, `defn`, `defmacro`, `impl`, `deftrait`, top-level expressions — are processed sequentially: expanded, built into AST, typechecked, and (for forms that produce code) JIT-compiled. A name's availability is bounded by source-order processing in its defining module: a deftype's constructors, a defn's function value, and a defmacro's expansion are all available only to FOLLOWING forms in the same module.* Drop the four "ordering ensures" claims that depend on module-wide visibility; restate the surviving ones in form-by-form terms. Update the example accordingly.

(b) **Reinstate two-pass in v4.** Same architectural cost as FIXME 0005's option (b); `/arch` rejects on the same grounds.

`/arch` recommends **(a)**, in lockstep with FIXME 0005's resolution.

## Context

Surfaced during S63 W2 sequence-diagram authoring. §9.12's description shaped the prelude bootstrap before pipeline-v4 — when the system did have pre-passes — and was not updated when the form-by-form scheduler landed. This FIXME pairs with FIXME 0005 (macro pre-pass): both must be resolved together since they describe two facets of the same defunct module-wide-visibility model.

§9.12 is currently `[Tested tests/macros.rs::macro_uses_another_batch, tests/macros.rs::macro_persists_across_evals]`. Those tests pass under v4, but they exercise the surviving form-by-form behaviour, not the pre-pass model the spec describes. `/qa` should re-examine the test annotations once §9.12 is rewritten.
