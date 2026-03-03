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

## For the `/spec` skill

**First session (Phase A Step 1)**: Review all 16 files. Run examples against the sketch oracle (`cd sketch && cargo run -- --run <example>`). Document divergences between spec text and prototype behavior. Update spec to reflect current (intended) behavior.

**Ongoing**: When a compiler skill encounters ambiguous behavior, `/spec` arbitrates: run the prototype, decide what is normative, update the relevant spec file.
