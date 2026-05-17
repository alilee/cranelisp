---
number: 0188
target: /qa
filed_by: /dev (typecheck)
filed_at: 2026-05-15
sprint_filed: 67
refers_to: tests/facade_pif_rows.rs `row_21_typecheck_env_narrowed_to_facade_two_methods`, tests/facade_pif_rows.rs `fqtypename_binding_resolved_stage_apis_use_fqtypename_not_bare_typename`, design/arch/facades/typecheck.md §"TypeCheckEnv target shape", design/arch/fixmes/0172-..., design/arch/fixmes/0187-..., design/arch/fixmes/0151-...
status: open
---

# qa — PIF row 21 + FQTypeName-binding test thresholds don't match the deferred-narrowing strategy

## Issue

Sprint 67 Wave 3 /dev (typecheck) narrowed `TypeCheckEnv` from 28 → 17 public
methods. The full target (per `facades/typecheck.md` §"TypeCheckEnv target
shape") is 2 methods (`new` + `next_type_id`). The residual 15 methods stay
`pub` because cross-crate `int` consumers depend on them (REPL introspection
in `src/session_v4.rs`, cache reconstruction in `src/worker.rs`,
bootstrap-ordering in `src/platform.rs`). The full closure to 2 methods
requires /dev (int) Wave 3 consumer migration — tracked in FIXME 0187.

This sprint thus delivers **partial-narrowing-with-named-residue** per the
task instructions. FIXME 0172 transitioned to `deferred-with-named-residue`
status; FIXME 0187 names the residue + the migration target for /int.

Two PIF tests fail against this state:

### Test 1: `row_21_typecheck_env_narrowed_to_facade_two_methods`

Asserts `methods.len() <= 4`. Current state: 17 methods. Fails.

### Test 2: `fqtypename_binding_resolved_stage_apis_use_fqtypename_not_bare_typename`

Counts bare-TypeName vs FQTypeName references in the public-api. Asserts
`fq_typename >= bare_typename`. Current state: 4 bare TypeName (all in
external-consumed methods documented as receiver-pinned exception 2),
0 FQTypeName (because all FQTypeName-returning methods narrowed to
`pub(crate)` and dropped from the public surface).

This is the **inversion** the narrowing produces: by hiding
`fqtn_for_type`, `all_type_defs` (FQ-keyed internally), and other
FQTypeName-using methods behind `pub(crate)`, the public surface ends up
holding only the receiver-pinned bare-TypeName exceptions. The test
expected the migration to lift TypeName→FQTypeName at public boundaries;
the narrowing instead hides the boundary entirely.

## Proposed resolution

Two test adjustments aligned with the deferred-narrowing strategy:

### `row_21_*`

Either:

1. **Raise the threshold to ≤17 (current narrowing state)** and update the
   assertion message to reference FIXME 0187 as the path to ≤4 / ≤2.
   Re-narrow the threshold in lockstep with /dev (int) Wave 3 migration of
   each consumer.
2. **Or split the test**: a permissive variant (≤17) that passes today,
   and a strict variant (≤2) that's `#[ignore]`'d with a FIXME pointing
   to 0187. The strict variant un-ignores when /int Wave 3 lands.

Option 1 is simpler; option 2 keeps the strict target visible.

### `fqtypename_binding_*`

The test's assertion (`fq_typename >= bare_typename`) assumed the migration
keeps the FQ-keyed methods at the public boundary. Post-narrowing, they're
`pub(crate)`. Recommend changing the assertion to one of:

1. **`bare_typename <= 4` (count of allowed receiver-pinned exceptions)**.
   The 4 methods (`lookup_type_def`, `get_type_constructors`,
   `get_impls_for_type`, `get_implementing_types`) are documented inline
   with `// FQTypeName exception 2 (receiver-pinned)` annotations. The
   test asserts the exception count, not the FQ count.
2. **Move the FQTypeName-vs-bare assertion to a crate-internal scope** —
   e.g., grep `crates/cranelisp-typecheck/src/checker.rs` source for
   `&TypeName` parameter types and assert each carries an exception
   citation comment.

Option 1 is the cleaner ratchet — caps the bare-TypeName surface at the
documented exception count.

## Operational implication / Context

- **Pure test-side fix.** The /dev (typecheck) Wave 3 source delivers the
  narrowing and exception annotations; only the test thresholds lag.
- **No facade adjustment needed.** `facades/typecheck.md` §"TypeCheckEnv
  target shape" already states the 2-method target and the narrowing
  trajectory; the residue is documented by FIXME 0172 (transitioned to
  deferred-with-named-residue) + FIXME 0187 (consumer migration target).
- **Sequencing.** /qa can land this adjustment in S67 close or defer to
  S68. The current source state is stable; the test failure is the only
  cost of deferral.

## Why a FIXME and not inline TODO

Per `sprints/METHOD.md` §3.3, cross-skill change requests live in
`design/arch/fixmes/`. This is a /qa-targeted test-author concern, not a
/dev source change.
