# user/

User-facing documentation for Cranelisp. Owned by the `/docs` skill.

## Purpose

This directory contains documentation written for Cranelisp users, not implementors:
- Getting-started guide (installation, first program, REPL orientation)
- Language tutorial (progressive introduction to all features)
- Language guide (feature-by-feature reference for practitioners)
- Error message catalog (common errors with explanations and fixes)

## Structure

- `getting-started.md` — Installation, REPL basics, Ring 0 + Ring 1 + Ring 2A features
- `tutorial/` — Progressive introduction; curriculum data for the `/learn` engine
  - `curriculum.md` — Section/prompt/trigger/answer definitions (Ring 1: sections 14-18, 21)
- `guide/` — Feature-by-feature reference (to be created)
- `errors/` — Error message catalog (to be created)

## Relationship to spec/

The spec (`spec/`) is precise and normative — written for implementors. User documentation is written for programmers using the language: approachable, example-driven, focused on what to do rather than what is formally true.

## For the `/docs` skill

**Sprint 1 (Ring 0)**: Complete. Getting-started guide written covering Int, Float, Bool, arithmetic, let, if, defn, recursion, enum types, pattern matching, batch programs.

**Sprint 2 (Ring 1)**: Complete. Getting-started guide extended with strings, product types, sum types with fields, constructor pattern matching, closures/lambdas, higher-order functions, "putting it together" examples. Tutorial curriculum sections 14-18 and 21 drafted. Usability findings U1.6, U1.7, U1.8 filed.

**Sprint 3 (Ring 2)**: Complete. Getting-started guide extended with Vec section (literals, primitives, polymorphism, immutable semantics, ADT integration, incremental building). Tutorial curriculum section 19 (collections) drafted. Vec primitives added to summary table.

**Sprint 4 (Ring 2A)**: Complete. Getting-started guide extended with Traits section covering: trait concept, operators as trait methods (Num/Eq/Ord), using operators, defining custom traits with deftrait, implementing traits with impl, multiple traits, default methods, constrained polymorphism, trait constraint annotations. Trait operators summary table added. "Putting It Together" examples updated to use operators. "What is Next" updated.

**Feedback loop**: Report to compiler skills when error messages are confusing, when REPL output is unhelpful, or when a concept has no good introduction path. File findings to `tests/plan/usability.md`.
