---
number: 0147
target: /int
filed_by: /qa
filed_at: 2026-05-05
sprint_filed: 64
refers_to: tests/legacy/sprint61_bare_primitive.rs, tests/repl_introspection.rs, tests/plan/wave-6-batch-5-audit.md, design/int/bare-primitive-value-path.md
status: open
---

# Harvest tests/legacy/sprint61_bare_primitive.rs into /int unit tests

## Issue

Sprint 64 Wave 6 batch 5 quarantined Sprint 61 Slice 1's bare-primitive
value-path regression guard:

- `tests/sprint61_bare_primitive.rs` (267 LOC, 5 tests, Sprint 61
  Slice 1 fix verification — `src/session_v4.rs::resolve_entry_for_display`
  + `check_bare_symbol_introspection`)

All 5 tests carry forward as REGRESSION-GUARDs into a single existing
e2e file (no new files):

- `tests/repl_introspection.rs` (extended +5):
  - `bare_primitive_add_i64_at_prompt_displays_type_and_fqn` — display-
    format conformance for bare primitive fn (repl/spec.md §1.1)
  - `bare_primitive_parallel_paths_converge_on_same_attribution` — three-
    path convergence guard between bare-value, /sig, and call paths
    (design/int/bare-primitive-value-path.md §2 + §5)
  - `bare_primitive_surface_resolves_identically_across_five_plus_symbols`
    — generalisation across primitives surface (spec/08-modules.md §8.9)
  - `bare_primitive_unknown_name_produces_undefined_error_neg` — negative
    guard against over-broad Slice 1 fix (repl/spec.md §1.1 negative
    complement)
  - `bare_primitive_two_hop_reexport_chain_lands_on_terminal_def` —
    transitive-resolution guard (`user → prelude → primitives` chain;
    bare-primitive-value-path.md §"Post-implementation note" +
    spec/08-modules.md §8.9)

Total carry-forward: **5 tests in 1 file**. On the binary at audit
time (2026-05-05): **5/5 PASS** (the Slice 1 fix is in place; these
guards land green).

The five tests are siblings of the existing
`tests/repl_introspection.rs::bare_primitive_type_int_displays_type_info`
(which covers bare primitive **type** lookup); these five cover bare
primitive **fn** lookup (different resolution path through the symbol
table).

## Inline FIXMEs preserved in legacy/sprint61_bare_primitive.rs

Zero pre-Sprint-63 inline `FIXME(/skill)` markers. The file's
docstring (lines 1–22) and per-test docstrings reference design doc
anchors directly; no migration step required.

## Proposed resolution

`/int` reviews the quarantined file:

1. For each of the 5 carry-forward tests, verify it is e2e-equivalent
   to a `src/` `#[cfg(test)]` unit-tier test that asserts the same
   invariant at the Rust API level. Mapping:

   - The Slice 1 fix area is `src/session_v4.rs::resolve_entry_for_display`
     + `src/session_v4.rs::check_bare_symbol_introspection`. The five
     tests probe that surface end-to-end (display format, three-path
     convergence, primitive-surface generalisation, negative guard,
     transitive resolution). Add `#[cfg(test)]` unit tests in
     `src/session_v4.rs` (or a sibling test module) covering the same
     invariants at the Rust API layer:
     - `resolve_entry_for_display` returns the terminal `Def`
       attribution (not an intermediate `Reexport`) for a primitives-
       qualified bare reference.
     - `check_bare_symbol_introspection` produces the spec-conforming
       output card (Type prefix + qualified name + classification +
       dash separator).
     - Unknown bare names produce a `not found` / `undefined variable`
       error (no silent fallback to similarly-named primitives).
     - The walker traverses ≥ 2 hops in the re-export chain.

2. When the unit-tier coverage is in place, delete
   `tests/legacy/sprint61_bare_primitive.rs`. Git history preserves
   provenance.

## Operational implication / Context

This is the **fifth 100%-GAP-COVER batch in a row** in Sprint 64 Wave
6 (b1: 21/21; b2: 59/61; b3: 36/36; b4: 25/25; b5: 10/10 with a single
failing-not-ignored Defect 6 carry-forward in the sister FIXME 0148).
Per `tests/plan/wave-6-batch-5-audit.md` §"Methodology takeaway":

> The pattern is locked: regression-named work-product files
> exhaustively partition the carry-forward surface — they are
> presumptively discriminating and the per-test review converges
> quickly.

Slice 1 of Sprint 61 was a tightly-scoped fix to one module
(`src/session_v4.rs`); its harvest target is correspondingly compact.
The five e2e carry-forwards are sufficient to detect any regression of
the original fix; the harvest action's value is shifting the same
discrimination axis to the unit tier where Rust API failures point at
the exact lookup routine that broke.

## Cross-references

- Audit document: `tests/plan/wave-6-batch-5-audit.md`
- Carry-forward sources:
  - `tests/repl_introspection.rs::bare_primitive_add_i64_at_prompt_displays_type_and_fqn`
  - `tests/repl_introspection.rs::bare_primitive_parallel_paths_converge_on_same_attribution`
  - `tests/repl_introspection.rs::bare_primitive_surface_resolves_identically_across_five_plus_symbols`
  - `tests/repl_introspection.rs::bare_primitive_unknown_name_produces_undefined_error_neg`
  - `tests/repl_introspection.rs::bare_primitive_two_hop_reexport_chain_lands_on_terminal_def`
- Sibling carry-forward: `tests/repl_introspection.rs::bare_primitive_type_int_displays_type_info`
  (covers bare primitive **type** — different resolution path)
- Sister FIXME: 0148 (Wave 6 b5 wave6_demo_repros)
- Source code areas:
  - `src/session_v4.rs::resolve_entry_for_display` (Slice 1 fix area)
  - `src/session_v4.rs::check_bare_symbol_introspection` (Slice 1 fix
    area)
- Design-doc anchors:
  - `design/int/bare-primitive-value-path.md` (Slice 1 design + fix
    rationale)
  - `repl/spec.md §1.1` (universal output format)
  - `spec/08-modules.md §8.9` (synthetic primitives module + re-export
    provenance)
