# Sprint 20 Wave 0 Review — Display Extraction, IO Fix, /mod Fix

**Reviewer**: `/review`
**Date**: 2026-03-19
**Scope**: T0 (display extraction), F1 (IO display fix), F2 (/mod conformance fix)
**Verdict**: PASS with findings

## Files Reviewed

| File | Change type |
|---|---|
| `crates/cranelisp-backend/src/display.rs` | NEW — 654 lines |
| `crates/cranelisp-backend/src/lib.rs` | `pub mod display;` added |
| `src/repl.rs` | Removed moved functions, added re-exports, new `force_io_and_format`, updated `/mod` handler |
| `tests/helpers/mod.rs` | Updated IO display format in `repl_eval_display` |

## Build Verification

`cargo check` passes cleanly. No warnings observed.

---

## Findings

### I-1: Duplication between `format_value` and `format_field_value` (Important)

**File**: `crates/cranelisp-backend/src/display.rs`, lines 33-71 and 599-653

`format_value` (public) and `format_field_value` (internal) share ~80% identical logic for Bool, Float, Int, String, and Fn arms. The only meaningful differences are:

1. `format_value`'s ADT branch delegates to `format_adt_value` and strips the `:Type ` prefix.
2. `format_field_value`'s ADT branch has inline ADT/Vec handling with dot notation.

The checklist (section 6) says: "If two functions share >70% of their logic, unify them with a parameter for the difference." `format_value` could call `format_field_value` directly for the non-ADT arms, or both could delegate to a shared `format_value_core` for the common cases.

Additionally, `format_value`'s ADT branch builds the full `":Type value"` string only to immediately strip the prefix — wasteful string allocation that could be avoided by extracting the value-only ADT formatting.

### I-2: Missing `// SAFETY:` comments on two `unsafe` blocks (Important)

**File**: `crates/cranelisp-backend/src/display.rs`

- **Line 53** (`format_value`, String arm): `unsafe { cranelisp_runtime::read_string_as_str(value) }` — no `// SAFETY:` comment. The validity check exists (line 50) but the `unsafe` block itself lacks the required annotation.
- **Line 619** (`format_field_value`, String arm): Same pattern — validity check at line 616 but no `// SAFETY:` comment on the `unsafe` block.

The review checklist requires: "Every `unsafe` block must have a `// SAFETY:` comment explaining why the invariants hold." Three other `unsafe` sites in this file have proper annotations.

### I-3: No unit tests in `display.rs` module (Important)

**File**: `crates/cranelisp-backend/src/display.rs`

The module has no `#[cfg(test)] mod tests` block. All display format tests remain in `src/repl.rs` (the binary crate), importing from `cranelisp_backend::display`. Per `src/CLAUDE.md`: "Every module gets `#[cfg(test)] mod tests`."

The existing tests in `src/repl.rs` exercise the public API adequately, but unit tests should live next to the code. This is especially important for a module with `unsafe` code — the tests should be co-located with the implementations they verify.

### S-1: Duplication between `format_type_qualified_inner` and `format_type_with_inline_constraints` (Suggestion)

**File**: `crates/cranelisp-backend/src/display.rs`, lines 189-241 and 249-337

Both functions have identical arms for `Type::Int`, `Type::Bool`, `Type::String`, `Type::Float`, `Type::Fn`, `Type::ADT`, and `Type::TyConApp`. The only difference is `Type::Var` handling (bare name vs. inline constraint annotation). A shared helper for the common arms would reduce the ~90 lines of duplicated type formatting.

### S-2: `format_adt_type_qualified` is `pub` but only used in tests (Suggestion)

**File**: `crates/cranelisp-backend/src/display.rs`, line 419

`format_adt_type_qualified` is `pub` but is only referenced externally by test code in `src/repl.rs::tests`. Consider `pub(crate)` with a `#[cfg(test)]` re-export, or accept that tests in the binary crate need `pub` visibility.

### S-3: `collect_var_ids` uses `Vec::contains` for dedup (Suggestion)

**File**: `crates/cranelisp-backend/src/display.rs`, line 530

`collect_var_ids` checks `ids.contains(id)` which is O(n). For the typical ADT with 1-3 type params this is negligible, but a `HashSet` seen-check would be more idiomatic per checklist section 10. Low priority given the small N.

---

## Checklist Walkthrough

| Check | Status | Notes |
|---|---|---|
| No `unwrap()` in pipeline code | PASS | All uses are `unwrap_or_else` with fallbacks |
| No `panic!()` on user input | PASS | Graceful fallbacks for unknown tags, invalid pointers |
| Max ~100 lines per function | PASS | Longest is `format_type_with_inline_constraints` at 88 lines |
| Max 8 parameters | PASS | Max is 7 (`format_adt_heap_value`) |
| No god objects | PASS | |
| String newtypes | PASS | Uses `TypeName`, `ModuleFullPath` correctly |
| Named constants for magic numbers | PASS | Uses `NULLARY_TAG_THRESHOLD`, `HeapAdt::TAG_OFFSET`, etc. |
| No circular dependencies | PASS | `display.rs` depends on `cranelisp_types` + `cranelisp_runtime` + `crate::heap` — all correct direction |
| `// SAFETY:` on unsafe blocks | **FAIL** | See I-2: two blocks missing annotations |
| Unsafe contained | PASS | All `unsafe` is in this one module (for display) + `force_io_and_format` in repl.rs |
| No duplicated logic batch/REPL | PASS | Single `force_io_and_format` serves REPL; test helper mirrors it |
| Result formatting one owner | PASS | All display logic now in `cranelisp_backend::display` |
| Dead code removed from repl.rs | PASS | No `pub fn format_*` remains; only REPL-specific `fn format_*` helpers |

## Correctness Assessment

### T0: Display Extraction
The extraction preserves behavior. All public functions are re-exported from `src/repl.rs` for backward compatibility. The `format_result`, `format_result_value`, `format_value`, `format_type_qualified` signatures are unchanged. Test helpers in `tests/helpers/mod.rs` import via the re-exports correctly.

### F1: IO Display Fix
`force_io_and_format` (line 872-907) produces `:(IO InnerType) (IO.Pure inner_value)` which matches `repl/spec.md` Ring 4 display format and `spec/12-runtime.md` §12.9 table entry for IO. The `catch_unwind` boundary for trampoline panics is correct — it prevents a malformed IO tree from crashing the REPL session. The test helper's `repl_eval_display` (line 302-325) mirrors this format.

### F2: /mod Conformance Fix
`handle_mod` (line 2237-2241) switches to "user" when no argument is given, otherwise to the named module. The prompt change is silent (no confirmation message). This matches `repl/spec.md` §3.1 behavior. The function is clean and minimal.

## Design Doc Assessment

No design doc changes were reviewed. The extraction is a mechanical refactoring that the existing `design/arch/interfaces.md` already anticipated (it lists the display function signatures). No new design doc is needed for this wave.

## Summary

Clean extraction with correct behavior preservation. Three Important findings (duplication, missing SAFETY comments, missing unit tests) and three Suggestions. None are blockers — the code is correct and the dependency direction is sound. The Important findings should be addressed before the ring is complete.
