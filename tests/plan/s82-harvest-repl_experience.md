# S82 harvest disposition — tests/legacy/repl_experience.rs

- **File:** `tests/legacy/repl_experience.rs`
- **LOC:** 3136
- **Tests:** 190 `#[test]` fns
- **Owning crate(s):** `src/` (REPL session) with `cranelisp-typecheck`, `cranelisp-backend`
- **FIXME:** 0124 (target /int; cross-crate residue: display→backend, type-inference→typecheck)
- **Prior audit:** none (this is one of the 15 never-audited files)

## Disposition

Audited fresh (S82 Wave 0, read-only). Per-test detail in the audit log;
the headline partition:

| Disposition | Count | Where |
|---|---:|---|
| COVERED | 100 | Ring-0 core: int/float/bool/string display, type reporting, error recovery, recursion, ADT enums, pattern matching, redefinition — matched to `repl_introspection.rs`, `repl_lifecycle.rs`, `repl_negative.rs` |
| GAP | 85 | Ring-1 heap-type display/errors (36: string/ADT/closure/vec/list); Ring-2A trait-operator dispatch + display (30); polymorphic type-var display normalization (8); collection display (11) |
| OBSOLETE | 5 | perf microbenchmarks — `simple_eval_is_fast`, `defn_eval_is_fast`, `session_creation_is_fast`, `fresh_session_can_evaluate_immediately`, `first_five_minutes_workflow` — measure execution speed, not language semantics; not spec-required |

GAP harvest targets: `src/` (display-format REPL output), `cranelisp-backend`
(`display.rs` value-format), `cranelisp-typecheck` (type-var
normalization). Per FIXME 0124 the int `/list`-classification slice is
already harvested into `src/session_v4.rs` `list_classification_tests`.

REGRESSION-GUARD among GAP: 2 (`type_error_does_not_corrupt_state_neg_*`
shape — actually COVERED in `repl_negative.rs::failed_defn_neg_no_partial_binding`;
`ring1_error_has_span_for_heap_type_mismatch` — GAP reg-guard).

## Summary

**190 tests: 100 covered / 85 gap / 5 obsolete**

## Exit checklist
- [x] (a) every test dispositioned in writing
- [ ] (b) all GAP harvested + green in owning crate (Wave 2)
- [ ] (c) file deleted (Wave 2)
- [ ] (d) README row removed (Wave 2)
- [ ] (e) FIXME 0124 closed (Wave 2 — after cross-crate residue lands)
