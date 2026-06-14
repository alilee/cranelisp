# S82 harvest disposition — tests/legacy/ring3_repl.rs

- **File:** `tests/legacy/ring3_repl.rs`
- **LOC:** 763
- **Tests:** 41 `#[test]` fns (9 stubs already deleted per FIXME 0125 S81 closure)
- **Owning crate(s):** `src/` with `cranelisp-typecheck`
- **FIXME:** 0125
- **Prior audit:** none

## Disposition

40 of 41 COVERED by the active REPL e2e suite (`repl_introspection.rs`,
`repl_lifecycle.rs`, `repl_negative.rs`, `spec_09_macros.rs`). The file
covers ring-3 macro/defmacro display, bare-macro lookup, special-form
classification, macro arity/body negatives, fixpoint expansion, and
deftype/deftrait/impl display — all of which the active suite carries.

| Disposition | Count | Notes |
|---|---:|---|
| COVERED | 40 | defmacro display (×3), bare-macro lookup, special-form classification, arity/body/missing-param negatives, fixpoint, persistence, cross-clause sigs, deftype/deftrait/impl display |
| GAP | 1 | `r3_neg_forward_reference_not_expanded` — forward ref to undefined macro is not expanded → `cranelisp-typecheck/src/macro_expand.rs` (REGRESSION-GUARD) |
| OBSOLETE | 0 | |

## Summary

**41 tests: 40 covered / 1 gap / 0 obsolete**

REGRESSION-GUARD among GAP: 1.

## Exit checklist
- [x] (a) dispositioned; [ ] (b) GAP harvested (Wave 2); [ ] (c) deleted; [ ] (d) README row; [ ] (e) FIXME 0125 closed
