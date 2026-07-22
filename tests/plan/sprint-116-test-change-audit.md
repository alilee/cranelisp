# Sprint 116 changed-test QA audit

Status: **trace gate closed; workspace comparison pending**

Baseline: `aefe7e11`; audited head: `e51bcd21`.

## Gate

Every test changed during Sprint 116 is untrusted until QA verifies its
assertions against normative language text. A design document is not a spec
requirement. Changed assertions do not count as evidence for their paired
implementation; unchanged e2e tests provide the independent regression gate.

## Inventory and disposition

| Change group | QA disposition | Normative source |
|---|---|---|
| Reader annotation-fold tests (6 new) | Semantics valid; missing test-side trace comments | `spec/01-lexical.md` §1.4.5 |
| AST annotation construction (1 new) | Semantics valid; missing trace | `spec/01-lexical.md` §1.4.5; `spec/03-types.md` §3.3.3 |
| Quasiquote annotated-form tests (4 new) | Semantics valid; missing traces | `spec/09-macros.md` §9.4, especially annotated-form rules |
| `defmacro` synthesized parameter assertion (modified) | Strengthening, not weakening; add structural trace | `spec/01-lexical.md` §1.4.5; `spec/09-macros.md` §§9.1–9.2 |
| `leading_annotation_len` assertion (modified) | Valid migration: parsed input contains one structural node and no prefix sexps | `spec/01-lexical.md` §1.4.5 |
| Degraded-startup `deftrait` fixture (modified) | Valid syntax migration; assertion itself unchanged | `spec/07-traits.md` §§7.1–7.1.1 |
| Frontend `deftype`/constructor tests (5 new) | Semantics valid; missing traces | `spec/05-definitions.md` §§5.2–5.2.2 and `spec/06-pattern-matching.md` §§6.2.1–6.2.2 |
| Trait-tail preservation test (1 new) | Valid boundary test; missing trace | `spec/07-traits.md` §7.1 trailing-element discrimination |
| Trait classifier/conformance tests (16 new) | Trace comments present and point to normative trait requirements | `spec/07-traits.md` §§7.1, 7.1.1, 7.1.5, 7.3; `spec/05-definitions.md` §5.4 |
| Shared-carrier serialization tests (3 new) | Trace comments present; exact section labels need qualification | `spec/01-lexical.md` §1.4.5; `spec/07-traits.md` §7.1 |
| Recursive drop-glue tests (7 new) | Missing traces; behavior is supported by per-type recursive-drop requirement | `spec/appendix-c-nfr.md` §C.1.4 |
| Drop-glue symbol identity tests (5 new) | Existing `// spec:` comments incorrectly cite design; replace with normative trace and label encoding assertions as implementation locks | `spec/appendix-c-nfr.md` §C.1.4 |
| Migrated typecheck fixtures/support | Syntax-only migrations are acceptable only where test purpose/assertion is unchanged | `spec/07-traits.md` §§7.1–7.1.1 |

## Traceability defects to remediate

Missing `// spec:` comments:

- 7 tests in `crates/cranelisp-backend/src/drop_glue.rs`.
- 7 tests in `crates/cranelisp-frontend/src/ast_builder/tests.rs`.
- 4 tests in `crates/cranelisp-frontend/src/quasiquote/tests.rs`.
- 6 tests in `crates/cranelisp-frontend/src/reader/tests.rs`.
- The strengthened existing `defmacro` structural assertion needs the
  annotation-fold section added to its existing trace.

Invalid normative target:

- 5 tests in `crates/cranelisp-types/src/module/tests.rs` use
  `design/backend/transitive-drop-glue.md` after `// spec:`. Replace this with
  §C.1.4 and retain the design reference separately as an implementation lock.

## Acceptance evidence

After trace remediation, QA will:

1. inspect the final changed-test diff for weakened/deleted assertions and new
   `#[ignore]` attributes;
2. run the owning unit-test packages with nextest;
3. run the complete workspace and compare RED names with the reconstructed
   Sprint 116 baseline;
4. report unchanged RED→PASS tests separately from modified tests.

Trace remediation completed without changing an assertion, expected value, or
ignore status. Verification:

- `cranelisp-frontend`: 427 passed.
- `cranelisp-types`: 229 passed.
- `cranelisp-typecheck`: 826 passed.
- `cranelisp-backend`: 495 passed, 1 RED — the independently identified
  `constructor_as_value_falls_through_to_fn_as_value` drop-glue fixture defect.
- Root annotation controls: 3 passed.

Post-gate backend fixture review:

- `constructor_as_value_falls_through_to_fn_as_value` retained every assertion.
  Its synthetic table was completed with the canonical `Option = None | Some
  Int` type/constructor inventory required by §C.1.4 drop-glue generation.
  The initially incomplete one-constructor inventory correctly selected the
  product value layout, confirming why the full sum definition is load-bearing.
  The complete backend package is now 496/496 green.

No `#[test]` entry was deleted and no `#[ignore]` was added in the sprint diff.
The complete-workspace RED-name comparison remains the final QA gate.

## Next skills

- `$testing`: add the missing and corrected test-side trace comments without
  changing assertions.
- `$qa`: re-audit the resulting diff and own the workspace RED comparison.
- `$sprint`: resume implementation only after this gate is closed.
