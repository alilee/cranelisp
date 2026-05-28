---
number: 0238
target: /dev platform
filed_by: /review (platform)
filed_at: 2026-05-28
sprint_filed: 71
refers_to: crates/cranelisp-platform/src/lib.rs:863-924 (declare_platform! `schema_types:` arm + rustdoc), design/platform/sprint71-redesign.md §7 (macro arm grammar)
status: open
---

# `declare_platform!` proc-macro upgrade — eliminate the `schema_types:` redundancy

## Severity

Suggestion

## Issue

Sprint 71 Wave 2's `declare_platform!` macro arm requires a redundant
`schema_types: [Name1, Name2, ...]` ident list alongside `schema:` because
`macro_rules!` cannot parse a string literal to enumerate identifiers. The
DLL author must list each type-name twice — once inside the schema literal,
once in the ident list. Wave 2 documented this at `lib.rs:867-875` with the
narrative:

> The `schema_types:` list is required alongside `schema:` because
> `macro_rules!` cannot parse a string-literal to enumerate identifiers
> (a proc-macro upgrade is feasible — tracked as a future refinement).

The "future refinement" claim is orphaned — no FIXME currently tracks it.
FIXME 0234 covers the `/abi` REPL emitter (DSL → schema text); it does
NOT cover the macro-side upgrade (schema text → marker-type idents).

## Proposed resolution

In a future cleanup sprint:

1. Add a proc-macro crate (e.g., `cranelisp-platform-macros`) hosting a
   procedural `declare_platform!` that parses the schema literal at expand
   time and enumerates the type names itself.
2. Remove the `schema_types:` arm key from the public macro surface; the
   schema literal becomes the single source of truth.
3. Regenerate `public-api.txt` (the macro surface changes); update the
   rustdoc to remove the "future refinement" narrative.
4. Migrate the Wave 2 worked-examples (`tests/macro_expansion.rs`,
   `tests/worked_examples.rs`) and any production platform DLLs to the
   simplified arm.

Alternative if proc-macro feels heavy: investigate `paste!`-style ident
construction from string literals (likely insufficient — `paste!` is
ident-from-ident, not ident-from-literal).

## Operational implication / Context

Pure ergonomic improvement; zero behavioural impact. DLL authors get a
cleaner single-source-of-truth schema declaration. The proc-macro crate
brings a small build-time cost (proc-macros build host-side) but the cost
is amortised across all DLL crates.

Pairs loosely with FIXME 0234 (the `/abi` REPL emitter) — both are about
the schema-text / marker-types translation surface, from different ends
(REPL emits text; the proc-macro reads text).
