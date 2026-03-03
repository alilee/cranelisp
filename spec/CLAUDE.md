# spec/

This directory contains the Cranelisp language specification — the authoritative record of what the language does. It is owned by the `/spec` skill.

## Authority

The spec is the source of truth for the reimplementation. When implementation and spec disagree:
- If the spec is correct: the implementation is wrong, fix it
- If the prototype behavior differs from the spec: check the prototype, then update the spec to reflect actual (intended) behavior

When a spec file and the prototype disagree, run the prototype to determine what is normative, then update the spec.

## Conventions

- Sections 1–10 and 12 are **normative**: they define language requirements
- Section 11 is **non-normative**: it describes the standard library
- Keywords MUST, MUST NOT, SHOULD, SHOULD NOT, MAY follow RFC 2119 semantics
- Examples in spec sections define expected behaviour — all examples must run correctly against the sketch oracle
- EBNF grammar in each section is authoritative
- Typing rules and evaluation judgments are authoritative

## Files

| File | Coverage |
|---|---|
| `01-lexical.md` | Lexical structure, tokens, reader shortcuts |
| `02-grammar.md` | EBNF grammar for all syntactic forms |
| `03-types.md` | Type system, Hindley-Milner, type constructors |
| `04-expressions.md` | Expression evaluation semantics |
| `05-definitions.md` | Top-level forms: defn, deftype, deftrait, impl, defmacro |
| `06-pattern-matching.md` | Match expressions, patterns, exhaustiveness |
| `07-traits.md` | Trait declarations, implementations, method resolution, derive |
| `08-modules.md` | Module system, imports, exports, qualified names |
| `09-macros.md` | Macro system, quasiquote, expansion rules |
| `10-io.md` | IO model, effect nodes, trampoline, par-let/par-bind! |
| `11-stdlib.md` | Standard library reference (non-normative) |
| `12-runtime.md` | Runtime model: RC layout, calling conventions, drop glue |
| `appendix-a-builtins.md` | Builtin primitive reference |
| `appendix-b-examples.md` | Extended examples |
| `index.md` | Spec index |

## Phase A Review Status (first session complete)

All 16 spec files reviewed. Sections confirmed current (no changes needed):
- `01-lexical.md` — tokens, reader shortcuts (quote, quasiquote, anon_fn, gensym, percent params)
- `03-types.md` — HM inference, constrained polymorphism, HKT
- `04-expressions.md` — par-let (§4.12), evaluation order
- `06-pattern-matching.md` — ADT patterns, exhaustiveness
- `07-traits.md` — derive macro (§7.13), HKT traits
- `08-modules.md` — modules, imports, super, inline submodules
- `10-io.md` — automatic IO scheduling (§10.12), ResourceSerial, no explicit par-bind!
- `11-stdlib.md` — non-normative reference
- `12-runtime.md` — lenient evaluation (§12.4.3), RC layout
- `appendix-a-builtins.md`, `appendix-b-examples.md`

Inconsistencies fixed:
- `09-macros.md §9.14` — removed stale item "multi-clause macros not supported" (contradicted §9.2.6)
- `02-grammar.md §2.2.5` — added multi-clause `defmacro` grammar
- `02-grammar.md §2.2.6` — corrected: `mod-` private variant exists
- `05-definitions.md §5.5` — added multi-clause grammar + cross-ref to §9.2.6
- `05-definitions.md §5.8` — corrected: `mod-` is the private submodule form
- `05-definitions.md §5.11, §5.14` — added `mod`/`mod-` to visibility and summary tables

## For the `/spec` skill

**First session (Phase A Step 1)**: ✓ Complete. All 16 files reviewed; inconsistencies fixed.

**Ongoing**: When a compiler skill encounters ambiguous behavior, `/spec` arbitrates: run the prototype (`cd sketch && cargo run -- --run <example>`), decide what is normative, update the relevant spec file.
