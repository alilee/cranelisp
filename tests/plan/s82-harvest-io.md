# S82 harvest disposition — tests/legacy/io.rs + io_minimal.rs

- **Files:** `tests/legacy/io.rs` (1377 LOC, 76 tests), `tests/legacy/io_minimal.rs` (133 LOC, 5 tests)
- **Owning crate(s):** `src/` with `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-platform` (post-D43: runtime ABU portions → `cranelisp-intrinsics`/`cranelisp-runtime` successors)
- **FIXME:** 0127
- **Prior audit:** none

## Disposition — io.rs (76)

Primary active coverage: `tests/spec_10_io.rs`. The Pure/Bind/match/let
IO-monad core (38 tests) is COVERED; the platform-effect, RC-discard,
type-error, macro-desugar, and auto-curry clusters (38 tests) are GAP.

| Disposition | Count | Clusters |
|---|---:|---|
| COVERED | 38 | Pure unwrap, Bind chains, bind-rejects-constructor/pattern, IO type-inference, if/match arm consistency, batch exit codes, deferred-data, named-defn continuation, scope capture — all in `spec_10_io.rs` |
| GAP | 38 | platform print/read-line effects (13, +2 reg-guard S57-demo-crash `io_do_print_sequence_*`/`io_bind_bang_print_sequence_*`); then-combinator RC discard (5: Int/String/ADT/chained/unused-heap-param → backend); IO type-errors (6: purity, bind arg types, Int-vs-Bool mismatch, match-arm → typecheck); do/bind! desugar (5 → stdlib); IO+ADT Option (2); pure-as-HOF (1); auto-curry (6 → spec_04_expressions); deep-bind-stack + batch-variant (2 → src/) |
| OBSOLETE | 0 | |

GAP targets per FIXME 0127: platform effects → `cranelisp-platform`;
type-errors/IO-inference → `cranelisp-typecheck`; RC-discard → `cranelisp-backend`;
do/bind! desugar → stdlib; auto-curry → `tests/spec_04_expressions.rs`.

## Disposition — io_minimal.rs (5)

All 5 are S57 Wave-6 SIGBUS minimal regression repros; intent preserved
in `spec_10_io.rs` (`capture_return_inc_does_not_double_free`,
`repl_bind_pure_lambda_no_double_free`, `repl_pure_int_unwraps`).

| Disposition | Count |
|---|---:|
| COVERED | 5 |
| GAP | 0 |
| OBSOLETE | 0 |

## Summary

- **io.rs: 76 tests: 38 covered / 38 gap / 0 obsolete** (reg-guard among GAP: 2)
- **io_minimal.rs: 5 tests: 5 covered / 0 gap / 0 obsolete**

## Exit checklist
- [x] (a) dispositioned; [ ] (b) GAP harvested (Wave 2); [ ] (c) deleted; [ ] (d) README rows; [ ] (e) FIXME 0127 closed
