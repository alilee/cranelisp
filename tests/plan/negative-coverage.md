# Negative Coverage Assessment

Risk-based review of negative test coverage across all spec sections.
Sprint 16 task D5. Created 2026-03-09.

## Tests Written (Sprint 16)

16 negative tests passing, 1 ignored (implementation gap). Tests live in their ring-specific files.

| Test Name | File | Spec Section | Category | Status |
|---|---|---|---|---|
| `neg_glob_export_excludes_private` | tests/ring2.rs | 8.7.3 | P1: Module boundaries | PASS |
| `neg_glob_export_includes_public` | tests/ring2.rs | 8.7.3 | P1: Module boundaries (companion positive) | PASS |
| `neg_circular_module_dependency` | tests/ring2.rs | 8.10.2 | P1: Module boundaries | PASS |
| `neg_super_in_root_module_errors` | tests/ring2.rs | 8.3.6 | P1: Module boundaries | PASS |
| `neg_glob_import_private_not_via_qualified` | tests/ring2.rs | 8.7.3 | P1: Module boundaries | PASS |
| `neg_private_macro_not_importable` | tests/ring2.rs | 8.7.3 | P1: Module boundaries | PASS |
| `neg_occurs_check_infinite_type` | tests/ring2.rs | 3.8.2 | P2: Type system invariants | PASS |
| `neg_constrained_fn_in_closure` | tests/ring2.rs | 3.6.6 | P2: Type system invariants | PASS |
| `neg_hkt_impl_primitive_type_rejected` | tests/ring2.rs | 3.7.4, 7.2.3 | P2: Type system invariants | PASS |
| `neg_impl_missing_method_errors` | tests/ring2.rs | 7.3.1 | P2: Type system invariants | PASS |
| `neg_type_mismatch_int_bool` | tests/ring2.rs | 3.8.6 | P2: Type system invariants | PASS |
| `neg_type_mismatch_fn_arity` | tests/ring2.rs | 3.8.3 | P2: Type system invariants | PASS |
| `neg_nested_pattern_rejected` | tests/ring1.rs | 6.6.1 | P5: Syntax restrictions | PASS |
| `neg_pattern_wrong_binding_count` | tests/ring1.rs | 6.2.1 | P5: Syntax restrictions | PASS |
| `neg_pattern_too_many_bindings` | tests/ring1.rs | 6.2.1 | P5: Syntax restrictions | PASS |
| `neg_multi_sig_bare_value_errors` | tests/ring2.rs | 4.6.3 | P2/P5: Type/syntax | PASS |
| `neg_macro_non_sexp_return_type_batch` | tests/macros.rs | 9.2.3 | P5: Macro restrictions | PASS |

### Additional D3 macro error tests (Sprint 16)

| Test Name | File | Spec Section | Status |
|---|---|---|---|
| `neg_macro_non_sexp_return_type_batch` | tests/macros.rs | 9.2.3 | PASS |
| `neg_macro_non_sexp_return_type_repl` | tests/macros.rs | 9.2.3 | PASS |
| `neg_macro_non_sexp_return_bool_batch` | tests/macros.rs | 9.2.3 | PASS |
| `neg_macro_expansion_depth_limit_exceeded` | tests/macros.rs | 12-runtime | PASS |
| `neg_macro_arity_mismatch` | tests/macros.rs | 9.14 | PASS |
| `neg_macro_error_no_session_corruption` | tests/macros.rs | 9.14 | PASS |

### Implementation Gap Resolved

`neg_constrained_fn_in_closure`: The reimplementation now rejects constrained polymorphic functions used as bare values (e.g., `(let [f add] (f 1 2))` where `add` uses trait dispatch), per spec/03-types §3.6.6. The check is in `infer_var` — constrained fn references outside call position produce a type error.

## Methodology

1. Read every spec file (`docs/spec/*.md`) and identify MUST/MUST NOT requirements.
2. For each requirement, check whether the existing test suite contains both positive AND negative coverage.
3. Assess risk based on five priority categories:
   - P1: Module boundaries (private names, glob exclusions, qualified access restrictions)
   - P2: Type system invariants (constrained poly restrictions, type errors for invalid constructs)
   - P3: Visibility rules (REPL /list /imports /exports category boundaries)
   - P4: Output format boundaries (wrong items absent, misclassification)
   - P5: Syntax restrictions (pattern limitations, phase ordering, placement rules)
4. Prioritize gaps by risk: highest-risk areas where implementation shortcuts can silently violate the spec.

## Coverage Summary

### Legend

| Status | Meaning |
|---|---|
| POS | Positive tests exist |
| NEG | Negative tests exist |
| GAP | No negative tests despite high-risk MUST NOT requirement |
| OK | Adequate positive and negative coverage |
| N/A | Not applicable for negative testing (informational spec text) |

---

## 01-lexical.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 1.3.1 | `-3` parsed as integer, not operator | POS | - | Low | POS |
| 1.3.3 | `trueness` is a symbol, not boolean | - | - | Low | GAP |
| 1.4.2 | Operator MUST NOT be followed by digit | - | - | Low | GAP |
| 1.7 | Token precedence rules | POS | - | Low | POS |

**Assessment**: Low risk. Parser has been stable. Gaps are minor edge cases.

---

## 02-grammar.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 2.1 | `mod`/`import` in wrong phase is error | - | - | Medium | GAP |
| 2.2.5 | Macro MUST return Sexp, else compile error | POS | - | Medium | POS |
| 2.3.4 | `if` condition MUST be Bool | POS | POS | Low | OK |
| 2.3.4 | `if` branches MUST match types | POS | POS | Low | OK |
| 2.3.3 | `let` binding list MUST be even | - | - | Low | GAP |
| 2.5.1 | Constructor binding count MUST match fields | POS | - | Medium | **GAP** |
| 2.5.4 | No nested patterns | - | - | Medium | **GAP** |
| 2.6 | Private defs MUST NOT be imported | POS | POS | High | OK |

**Assessment**: Medium risk. Pattern matching restrictions (no nested patterns, binding count) are under-tested negatively.

---

## 03-types.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 3.6.6 | Constrained fn MUST NOT be used as value | POS | POS | High | OK |
| 3.6.6 | No constrained closures | - | - | High | **GAP** |
| 3.8.2 | Occurs check (infinite type) | - | - | High | **GAP** |
| 3.8.3 | Arity mismatch in function types | POS | POS | Medium | OK |
| 3.8.6 | Type mismatch produces error | POS | POS | Low | OK |
| 3.7.4 | Primitive types rejected as HKT impl targets | - | - | High | **GAP** |

**Assessment**: High risk. The occurs check, constrained closure restriction, and HKT target validation are critical type system invariants without negative tests.

---

## 04-expressions.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 4.4 | `if` condition MUST be Bool | POS | POS | Low | OK |
| 4.6.3 | Multi-sig bare value is compile error | - | - | Medium | **GAP** |
| 4.10 | Vec elements MUST have same type | POS | POS | Low | OK |

**Assessment**: Medium risk. Multi-sig bare value restriction needs negative test.

---

## 05-definitions.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 5.1.2 | Multi-sig MUST have >= 2 variants | - | - | Low | GAP |
| 5.5 | Macro MUST return Sexp | - | - | Medium | GAP |
| 5.11 | Private names MUST NOT be imported | POS | POS | High | OK |
| 5.13.2 | Macro MUST be defined before use | - | - | Medium | **GAP** |

**Assessment**: Medium risk. Forward-reference macro restriction is important but untested negatively.

---

## 06-pattern-matching.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 6.2.1 | Binding count MUST equal field count | POS | - | Medium | **GAP** |
| 6.3.3 | Arm body types MUST agree | POS | POS | Low | OK |
| 6.5 | Non-exhaustive match is compile error | POS | POS | Medium | OK |
| 6.6.1 | No nested patterns | - | - | Medium | **GAP** |
| 6.6.2 | No literal patterns | - | - | Low | GAP |
| 6.6.3 | No or-patterns | - | - | Low | GAP |
| 6.6.4 | No guards | - | - | Low | GAP |

**Assessment**: Medium risk. Pattern restriction enforcement (nested, literal, or-patterns, guards) needs negative tests.

---

## 07-traits.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 7.1.1 | Trait MUST have >= 1 method with `self` | - | - | Medium | GAP |
| 7.2.3 | Primitive types MUST be rejected as HKT targets | - | - | High | **GAP** |
| 7.3.1 | Impl method count MUST match trait | - | - | Medium | **GAP** |
| 7.4.3 | No impl match = compile error | POS | - | Medium | POS |
| 7.8.3 | Constrained fn MUST NOT be first-class value | POS | POS | High | OK |
| 7.12.1 | No default methods on HKT traits | - | - | Medium | **GAP** |

**Assessment**: High risk for HKT target validation. Medium risk for impl method count validation.

---

## 08-modules.md (HIGHEST RISK)

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 8.2.3 | Private submodule MUST NOT be imported from outside | - | - | High | **GAP** |
| 8.2.6 | `mod` MUST be top-level | - | - | Medium | **GAP** |
| 8.3.1 | Import of non-public name is compile error | POS | POS | High | OK |
| 8.3.2 | Glob import excludes private names | POS | POS | High | OK |
| 8.3.6 | `super` in top-level module MUST error | - | - | High | **GAP** |
| 8.4.4 | Export MUST NOT re-export private | POS | POS | High | OK |
| 8.6.4 | Duplicate imports from different sources = error | POS | POS | High | OK |
| 8.6.4 | Definition over import = error | POS | POS | High | OK |
| 8.6.5 | Ambiguous bare name MUST error | POS | POS | High | OK |
| 8.6.6 | Accessing private via qualified ref = error | POS | POS | High | OK |
| 8.7.3 | Private name MUST NOT be exported via glob | POS | - | High | **GAP** |
| 8.7.3 | Private name MUST NOT be accessed via qualified ref | POS | POS | High | OK |
| 8.9.1 | Primitives NOT bare without import | POS | POS | High | OK |
| 8.9.2 | `macros` module NOT implicitly imported | POS | - | Medium | **GAP** |
| 8.10.2 | Circular dependencies MUST error | - | - | High | **GAP** |

**Assessment**: HIGH risk. Multiple P1 module boundary gaps. The most dangerous gaps are:
- Glob exports not leaking private names (has positive test that glob import skips private, but no test that glob EXPORT skips private)
- Circular dependency detection
- `super` in root module
- `mod` placement enforcement

---

## 09-macros.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 9.2.3 | Macro return type MUST be Sexp | - | - | Medium | **GAP** |
| 9.3.4 | Forward reference to macro is NOT expanded | - | - | Medium | **GAP** |
| 9.5 | Zero-arg macro expands as bare symbol | POS | - | Low | POS |
| 9.6 | `begin` NOT valid in user source | - | - | Low | GAP |
| 9.9.5 | Macro arity mismatch = compile error | - | - | Medium | **GAP** |

**Assessment**: Medium risk. Macro return type constraint and arity mismatch are the main gaps.

---

## 10-io.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 10.1.2 | Pure function MUST NOT return IO | - | - | Low | GAP |
| 10.6 | Batch `main` MUST return IO | POS | - | Medium | **GAP** |
| 10.7.2 | Branch consistency (IO vs non-IO) | POS | POS | Medium | OK |

**Assessment**: Medium risk. The `main` return type requirement needs a negative test.

---

## 12-runtime.md

| Section | Requirement | Positive | Negative | Risk | Status |
|---|---|---|---|---|---|
| 12.5 | TCO tail position rules | POS | - | Low | POS |
| 12.7.1 | Type errors are compile-time | POS | POS | Low | OK |
| 12.7.2 | Non-exhaustive match is runtime panic | POS | POS | Medium | OK |

**Assessment**: Low risk. Well covered.

---

## Prioritized Gap List

### Sprint 16 — Addressed

16 passing, 1 ignored (implementation gap). Tests live in ring-specific files.

| Priority | Gap | Spec Section | Test Name | File | Status |
|---|---|---|---|---|---|
| P1-HIGH | Glob export MUST NOT include private names | 8.7.3 | `neg_glob_export_excludes_private` | ring2.rs | PASS |
| P1-HIGH | Circular module dependency MUST error | 8.10.2 | `neg_circular_module_dependency` | ring2.rs | PASS |
| P1-HIGH | `super` in root module MUST error | 8.3.6 | `neg_super_in_root_module_errors` | ring2.rs | PASS |
| P1-HIGH | Glob import private not accessible bare or qualified | 8.7.3 | `neg_glob_import_private_not_via_qualified` | ring2.rs | PASS |
| P1-HIGH | Private macro not importable | 8.7.3 | `neg_private_macro_not_importable` | ring2.rs | PASS |
| P2-HIGH | Occurs check prevents infinite types | 3.8.2 | `neg_occurs_check_infinite_type` | ring2.rs | PASS |
| P2-HIGH | Primitive types rejected as HKT impl targets | 3.7.4, 7.2.3 | `neg_hkt_impl_primitive_type_rejected` | ring2.rs | PASS |
| P2-HIGH | Constrained fn in closure MUST NOT compile | 3.6.6 | `neg_constrained_fn_in_closure` | ring2.rs | PASS |
| P2-HIGH | Missing impl method MUST error | 7.3.1 | `neg_impl_missing_method_errors` | ring2.rs | PASS |
| P2-MED | Type mismatch Int vs Bool | 3.8.6 | `neg_type_mismatch_int_bool` | ring2.rs | PASS |
| P2-MED | Function arity mismatch | 3.8.3 | `neg_type_mismatch_fn_arity` | ring2.rs | PASS |
| P5-MED | No nested patterns | 6.6.1 | `neg_nested_pattern_rejected` | ring1.rs | PASS |
| P5-MED | Constructor binding count mismatch (too few) | 6.2.1 | `neg_pattern_wrong_binding_count` | ring1.rs | PASS |
| P5-MED | Constructor binding count mismatch (too many) | 6.2.1 | `neg_pattern_too_many_bindings` | ring1.rs | PASS |
| P5-MED | Macro return type MUST be Sexp | 9.2.3 | `neg_macro_non_sexp_return_type_batch` | macros.rs | PASS |
| P5-MED | Multi-sig bare value is compile error | 4.6.3 | `neg_multi_sig_bare_value_errors` | ring2.rs | PASS |

### Defer to Later Sprint

| Priority | Gap | Spec Section | Reason |
|---|---|---|---|
| P1-MED | `mod` MUST be top-level | 8.2.6 | Parser handles this implicitly; lower risk |
| P1-MED | Private submodule not importable from outside | 8.2.3 | `mod-` not yet fully implemented |
| P2-MED | Default methods on HKT traits rejected | 7.12.1 | Edge case; HKT defaults not planned |
| P5-LOW | `begin` not valid in user source | 9.6 | Low impact; internal form |
| P5-LOW | No literal patterns | 6.6.2 | Parser naturally rejects these |
| P5-LOW | No or-patterns | 6.6.3 | Parser naturally rejects these |
| P5-LOW | No guards | 6.6.4 | Parser naturally rejects these |
| P5-LOW | `trueness` is symbol not boolean | 1.3.3 | Parser tested; very low risk |
