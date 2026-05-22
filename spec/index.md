# Cranelisp Language Specification

<!-- NEG-COVERAGE TRACKING (Sprint 57 Wave 5 disposition — moved from FIXME(/qa) to standing tracker)

Sprint 56 audit found 100 `[Tested ...]` annotations in spec/ and 11 in repl/spec.md without a `[Tested+Neg ...]` counterpart. This is a project-wide backlog — too large for a single wave. Wave 5 resolution: treat this as an ongoing coverage-quality tracker, not a single-point FIXME.

Wave 5 increments: §3.7 HKT, §5.4.2 / §5.4.3 ADT impls, §12.4.2 Lazy Sequences, appendix-a string primitives, repl §1.5 List display, repl §11.1 /expand, repl §4.1.3 related trait impls, repl §4.1.7 primitive lookup — all promoted to `[Tested+Neg ...]` this sprint.

Remaining negative-coverage priority order (for future sprints):
1. Module/import boundaries (§8) — what MUST NOT leak across modules; prioritize private visibility (§8.5) + super import depth boundary (§8.3.8) + primitives-not-in-user-category absence tests
2. Match exhaustiveness (§6.5) — non-ADT scrutinee wildcard requirement, ADT non-exhaustive rejection
3. Visibility / private variants (§5) — `defn-` / `deftype-` / `deftrait-` / `mod-` cross-module negative tests
4. Trait dispatch (§7) — which types MUST NOT satisfy a trait, ambiguous-dispatch rejection
5. REPL category boundaries (repl/spec.md §3, §4) — empty categories omitted, primitives absent from user category

Per CLAUDE.md §"Applying Annotations", MUST/MUST NOT requirements should have both positive and negative coverage. Not every `[Tested]` needs upgrading — some describe display formats where "wrong output" is naturally caught. Requirements about what MUST NOT appear deserve explicit negative tests. -->


**Version**: 0.1 (Draft)

This document specifies the Cranelisp programming language. It describes the syntax, type system, and evaluation semantics in implementation-agnostic terms. Section 11 and Appendix A are non-normative reference documentation describing the reference implementation's standard library. Appendix C defines normative non-functional requirements that constrain implementation strategies. A conforming implementation may use any compilation strategy (JIT, AOT, interpretation) provided it satisfies the behavioral and non-functional requirements described herein.

## Design Philosophy [Tested]

Cranelisp is a statically typed, pure functional Lisp. Its design priorities are:

- **Static types with inference**: Hindley-Milner type inference with traits, constrained polymorphism, and higher-kinded types. No type annotations are required for most programs.
- **Purity via IO type**: Side effects are tracked in the type system via the `IO` type. Pure functions cannot perform IO.
- **Clojure-flavored syntax**: S-expressions with square brackets for parameter lists and vector literals. Commas are whitespace.
- **Self-documenting**: Every construct in the language produces useful feedback when queried — its type, value, or description.
- **Clojure-inspired naming**: Where a standard library is provided, naming follows Clojure conventions where possible.

## Notation Conventions [Tested]

### EBNF Grammar [Tested]

Grammar rules use Extended Backus-Naur Form:

| Notation | Meaning |
|---|---|
| `'literal'` | Terminal string |
| `rule` | Non-terminal reference |
| `a b` | Sequence |
| `a \| b` | Alternation (ordered: first match wins) |
| `a*` | Zero or more repetitions |
| `a+` | One or more repetitions |
| `a?` | Optional (zero or one) |
| `[a-z]` | Character range |
| `[^ c]` | Any character except `c` |
| `( ... )` | Grouping |

### Requirement Levels [Tested]

This specification uses terminology from RFC 2119:

- **MUST** / **MUST NOT**: Absolute requirements. A conforming implementation that violates these is non-conforming.
- **SHOULD** / **SHOULD NOT**: Recommended behavior. Implementations may deviate with good reason, but the implications must be understood.
- **MAY**: Optional behavior. Implementations are free to include or omit.

### Annotations [Tested]

- **Note**: Informational context that is not normative.
- **Implementation-defined**: Behavior where implementations may choose freely, provided the choice is documented.
- **Example**: Illustrative code. Examples use `; →` to show expected results.

## Specification Contents

1. [Lexical Structure](01-lexical.md) — Tokens, whitespace, comments, literals, symbols
2. [Grammar](02-grammar.md) — Syntactic forms in EBNF
3. [Type System](03-types.md) — Types, inference rules, constraints, higher-kinded types
4. [Expressions](04-expressions.md) — Evaluation semantics for each expression form
5. [Definitions](05-definitions.md) — Top-level definition forms
6. [Pattern Matching](06-pattern-matching.md) — Pattern syntax, matching rules
7. [Traits](07-traits.md) — Declaration, implementation, dispatch, built-in traits
8. [Modules](08-modules.md) — File mapping, imports, exports, resolution
9. [Macros](09-macros.md) — Compile-time macro system
10. [IO Model](10-io.md) — Effect tracking, IO type, platform declarations
11. [Standard Library](11-stdlib.md) — Prelude, core modules, primitives (non-normative)
12. [Runtime Model](12-runtime.md) — Abstract value representation, memory, errors

**Appendices**:
- [A: Builtin Reference](appendix-a-builtins.md) — Complete function/type reference (non-normative)
- [B: Examples](appendix-b-examples.md) — Extended example programs
- [C: Non-Functional Requirements](appendix-c-nfr.md) — Memory management, data structures, evaluation, concurrency, compilation, performance, target portability (normative)

## Compilation Pipeline [Tested]

A conforming implementation MUST process source code through the following logical phases (though phases may be combined or reordered as an optimization):

1. **Lexing**: Source text to tokens
2. **Parsing**: Tokens to S-expression tree
3. **Macro expansion**: Expand `defmacro` calls, iterating to a fixed point
4. **AST construction**: S-expressions to abstract syntax tree
5. **Type checking**: Hindley-Milner inference, trait resolution, constrained polymorphism detection
6. **Code generation**: AST to executable form (implementation-defined)
7. **Execution**: Run the `main` function (batch mode) or evaluate expressions interactively (REPL mode)

Note: A REPL is not required by this specification, but is the conventional way to interact with Cranelisp programs during development.
