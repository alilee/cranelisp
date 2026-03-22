# user/

User-facing documentation for Cranelisp. Owned by the `/docs` skill.

## Purpose

This directory contains documentation written for Cranelisp users, not implementors:
- Getting-started guide (installation, first program, REPL orientation)
- Language tutorial (progressive introduction to all features)
- Language guide (feature-by-feature reference for practitioners)
- Error message catalog (common errors with explanations and fixes)

## Structure

- `getting-started.md` — Installation, REPL basics, Ring 0 + Ring 1 + Ring 2A + Ring 4 (IO) features
- `caching.md` — Module caching: `.cranelisp-cache/`, `--no-cache`, invalidation, `.gitignore`
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

**Sprint 5 Wave 4**: Constrained polymorphism section updated with monomorphisation explanation, `max-of` example using `Ord`, and `(double 2.5)` example. Default methods section corrected to show full `Ord` trait declaration with `<=`/`>=` defaults and usage examples. Trait operators summary table expanded with `>`, `<=`, `>=`.

**Sprint 6 (Ring 4)**: Complete. Getting-started guide extended with IO section covering: the IO model (why IO is a type), `print`, `pure`, `do`, `bind!`, `read-line`, platform declarations (`(platform stdio)`), batch programs with IO, "Try it yourself" exercises, IO summary table. "What is Next" updated to reflect IO coverage.

**Sprint 20 (D7 IO validation)**: IO guide validated against working batch mode. Fixed: IO REPL display format updated from `:(IO Int) 0` to `:(IO primitives/Int) (IO.Pure 0)` throughout (matches spec §12.9.1 and actual compiler output). Added `CRANELISP_LIB` environment variable documentation for projects outside the stdlib directory. Fixed batch mode run commands from `cargo run -- file.cl` to `cargo run -- --run file.cl`.

**Sprint 22 Wave 3**: Created `user/caching.md` documenting module caching feature: automatic `.cranelisp-cache/` directory, cache invalidation rules, `--no-cache` CLI flag, cache clearing, `.gitignore` guidance.

**Feedback loop**: Report to compiler skills when error messages are confusing, when REPL output is unhelpful, or when a concept has no good introduction path. File findings as `FIXME(/skill-name)` comments on the relevant spec or design doc.
