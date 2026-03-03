# Cranelisp Language Specification

**Version**: 0.1 (Draft)

This document specifies the Cranelisp programming language. It describes the syntax, type system, and evaluation semantics in implementation-agnostic terms. Section 11 and Appendix A are non-normative reference documentation describing the reference implementation's standard library. A conforming implementation may use any compilation strategy (JIT, AOT, interpretation) and any memory management approach (reference counting, tracing GC, region-based) provided it satisfies the behavioral requirements described herein.

## Design Philosophy

Cranelisp is a statically typed, pure functional Lisp. Its design priorities are:

- **Static types with inference**: Hindley-Milner type inference with traits, constrained polymorphism, and higher-kinded types. No type annotations are required for most programs.
- **Purity via IO type**: Side effects are tracked in the type system via the `IO` type. Pure functions cannot perform IO.
- **Clojure-flavored syntax**: S-expressions with square brackets for parameter lists and vector literals. Commas are whitespace.
- **Self-documenting**: Every construct in the language produces useful feedback when queried — its type, value, or description.
- **Clojure-inspired naming**: Where a standard library is provided, naming follows Clojure conventions where possible.

## Notation Conventions

### EBNF Grammar

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

### Requirement Levels

This specification uses terminology from RFC 2119:

- **MUST** / **MUST NOT**: Absolute requirements. A conforming implementation that violates these is non-conforming.
- **SHOULD** / **SHOULD NOT**: Recommended behavior. Implementations may deviate with good reason, but the implications must be understood.
- **MAY**: Optional behavior. Implementations are free to include or omit.

### Annotations

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

## Compilation Pipeline

A conforming implementation MUST process source code through the following logical phases (though phases may be combined or reordered as an optimization):

1. **Lexing**: Source text to tokens
2. **Parsing**: Tokens to S-expression tree
3. **Macro expansion**: Expand `defmacro` calls, iterating to a fixed point
4. **AST construction**: S-expressions to abstract syntax tree
5. **Type checking**: Hindley-Milner inference, trait resolution, constrained polymorphism detection
6. **Code generation**: AST to executable form (implementation-defined)
7. **Execution**: Run the `main` function (batch mode) or evaluate expressions interactively (REPL mode)

Note: A REPL is not required by this specification, but is the conventional way to interact with Cranelisp programs during development.
