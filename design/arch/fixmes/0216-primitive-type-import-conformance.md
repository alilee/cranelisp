---
number: 0216
target: /qa
filed_by: /spec
filed_at: 2026-05-23
sprint_filed: 69
refers_to: spec/03-types.md §3.1, spec/08-modules.md §8.9.1, spec/08-modules.md §8.11.4
status: open
---

# Conformance tests — primitive type bare-name import rule

## Issue

Spec §3.1 + §8.9.1 + §8.11.4 sharpened (S69 Phase-3, this fire) to require
prelude re-export or explicit import for bare-name access to primitive
type names (`:Int`, `:Bool`, `:Float`, `:String`). FQ form
(`:primitives/Int`) always works.

The rule is currently un-tested — the prior implementation had a bridge
(`Type::from_name`) that bypassed the rule, masking any test failures
that would have arisen. The bridge is being removed in the S69 Phase-3
architectural cascade.

## Proposed resolution

Write narrow integration tests in `tests/` covering:

1. Bare `:Int` without prelude / without explicit primitives import
   → MUST produce "unknown type" compile-time error
2. Bare `:Int` with explicit `(import [primitives [Int]])` → MUST work
3. FQ `:primitives/Int` without prelude → MUST work
4. Bare `:Int` after prelude re-exports `Int` → MUST work
5. Same battery for `:Bool`, `:Float`, `:String`
6. Same battery for primitive functions (`add-i64`, etc.) — already
   partially covered; cross-reference existing tests.

Annotation: `// spec: spec/03-types.md §3.1`, `// spec: spec/08-modules.md
§8.9.1`, `// spec: spec/08-modules.md §8.11.4`. Mark `[R4 S70]` (or
whichever sprint they land in) in spec annotations.

## Operational implication / Context

Conformance tests must NOT use `#[ignore]` — they must fail visibly
until the architectural cascade (delete `Type::from_name`, register
primitives uniformly) completes per `memory/feedback_failing_not_ignored.md`.
Tests landing red is correct — they're guarding the rule that the
architectural fix makes true.

The architectural-fix sister-work is filed separately (see S69 walk-log
Group B notes); this FIXME is just the test side.
