# spec/

This directory contains the Cranelisp language specification — the authoritative record of what the language does. It is owned by the `/spec` skill.

## Authority

The spec is the source of truth for the reimplementation. When implementation and spec disagree:
- If the spec is correct: the implementation is wrong, fix it
- If the prototype behavior differs from the spec: check the prototype, then update the spec to reflect actual (intended) behavior

The spec only shows the language features and requirements of the compiler, and doesn't prescribe the standard library. There may be multiple standard 
library candidates.

When a spec file and the prototype disagree, run the prototype to determine what baseline was, then update the spec after validating with designer. Eventually, 
the sketch and the spec will diverge because the sketch is not being maintained.

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

**Second session (FIXME resolution)**: Addressed all open FIXME comments across modified files:
- `02-grammar.md §2.2.5` — replaced `when`/`unless` examples (dummy `0` branch) with `my-if` and `my-and`
- `08-modules.md §8.1.1` — clarified module identity is file-path-based; sibling-file `mod` resolution loads a peer module, not a submodule
- `08-modules.md §8.3.2` — clarified `[*]` is glob-all; importing `*` operator requires it alongside other names
- `08-modules.md §8.3.8` — documented that multiple `import` forms accumulate
- `08-modules.md §8.11` — updated lib search order: project config file takes priority; stdlib is not a special language feature
- `09-macros.md §9.5` — resolved auto-lifting question: explicit Sexp constructors required; no auto-lifting
- `09-macros.md §9.6` — removed FIXME; `begin` is a language-level macro expander protocol
- `09-macros.md §9.10` — moved `const`/`def` to §9.10.1/2 (from §9.10.10/11); renumbered rest
- `10-io.md §10.11` — moved complete examples to Appendix B; §10.11 now cross-references appendix
- `11-stdlib.md` — complete rewrite: pared to bootstrapping support for stdlib writers; stdlib itself documented elsewhere
- `appendix-a-builtins.md` — removed stdlib sections (A.3-A.7); builtins only (types, primitive functions, special forms)
- `appendix-b-examples.md` — replaced FIXME with stdlib-assumption preface; added B.11-B.13 from §10.11

**Ongoing**: When a compiler skill encounters ambiguous behavior, `/spec` arbitrates: run the prototype (`cd sketch && cargo run -- --run <example>`), decide what is normative, update the relevant spec file after validating with developer.
