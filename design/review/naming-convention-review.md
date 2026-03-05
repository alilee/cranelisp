# Naming Convention Review — `cranelisp_` Prefix Removal

**Reviewer**: `/review`
**Date**: 2026-03-05
**Scope**: Cross-skill naming convention change — JIT symbol names, Rust function names, design documents, runtime implementation
**Verdict**: **MOSTLY CONSISTENT — 2 Important findings, 6 Suggestions**

---

## Summary

The `cranelisp_` prefix removal has been applied consistently across all active source files and core design documents. The convention definition in `src/CLAUDE.md` is clear and well-structured. The runtime implementation in `cranelisp-runtime` follows the convention correctly. The core architecture documents (`architecture.md`, `interfaces.md`, `ring0-interfaces.md`, `design-space.md`) are fully clean of stale `cranelisp_` references.

Two classes of issue remain:
1. **Plan files** (`plan-platform.md`, `plan-backend.md`) retain dozens of `cranelisp_` references from the pre-convention era.
2. **Cross-document gaps** where a function is documented in one authoritative source but missing from another.

---

## 1. Convention Definition (`src/CLAUDE.md` lines 26-47)

**Assessment**: Clear, complete, and unambiguous for current needs.

### F-1: Convention is well-structured

The five-category table (User function, Trait method impl, Multi-sig variant, Extern primitive, Runtime infrastructure) with JIT name format, examples, and user-visibility is an effective reference. The six rules are concrete and actionable.

### F-2 (Suggestion): ADT constructor functions not covered in naming table

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/src/CLAUDE.md`, lines 32-38
**Severity**: Suggestion

The naming table covers five categories but does not mention ADT data constructor functions. When data constructors are compiled as functions (Ring 1+), they will need JIT-visible names. Will a constructor like `Some` be registered as `Some` (user function style), `user/Some` (module-qualified), or something else?

Currently in Ring 0, constructors are nullary (bare i64 tags, no JIT function needed). But the convention should anticipate Ring 1 data constructors proactively — this is exactly the kind of ambiguity that leads to inconsistency later.

**Recommendation**: Add a row to the naming table:

| Category | JIT name format | Example | Visible to users? |
|----------|----------------|---------|-------------------|
| ADT constructor | `name` or `module/name` | `Some`, `Cons` | Yes — via module system |

### F-3 (Suggestion): Drop glue functions not mentioned

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/src/CLAUDE.md`, lines 32-38
**Severity**: Suggestion

Per-type drop glue functions (Ring 1+) will be JIT-compiled functions with internal names. The convention does not specify whether these fall under "Runtime infrastructure" (`runtime/drop_glue$Option_Int`?) or get their own category. These are not user-visible but are distinct from both user functions and runtime infrastructure.

**Recommendation**: Either add a row for internal codegen functions, or add a note that compiler-generated internal functions (drop glue, curry wrappers, mono specialisations) follow the existing categories — e.g., drop glue is runtime infrastructure, curry wrappers are user-function-style with a mangling suffix.

---

## 2. Runtime Implementation

### 2a. `crates/cranelisp-runtime/src/lib.rs`

**Assessment**: Clean. All re-exports are correctly named. Comments reference `src/CLAUDE.md` for the naming convention.

### 2b. `crates/cranelisp-runtime/src/alloc.rs`

**Assessment**: Clean. Rust function names are `heap_alloc` and `heap_dealloc` — matching the convention (no `cranelisp_` prefix). `#[unsafe(no_mangle)]` is applied, which is documented as optional in the convention (rule 5). Consistent.

### 2c. `crates/cranelisp-runtime/src/string.rs`

**Assessment**: Clean. All extern function names follow the convention: `heap_alloc_string`, `str_concat`, `str_eq`, `str_len`, `string_identity`, `string_read`. No `cranelisp_` prefix anywhere.

### 2d. `crates/cranelisp-runtime/src/panic.rs`

**Assessment**: Clean. Function is `runtime_panic`, consistent with JIT name `runtime/panic`.

### 2e. `crates/cranelisp-runtime/src/rc.rs`

**Assessment**: Clean. Function is `rc_underflow_check`, consistent with JIT name `runtime/rc_underflow_check`.

### F-4 (Suggestion): `#[unsafe(no_mangle)]` usage is inconsistent but acceptable

**File**: Multiple files in `crates/cranelisp-runtime/src/`
**Severity**: Suggestion

All extern functions have `#[unsafe(no_mangle)]`. The convention (rule 5) says this is "optional — symbols are registered by function pointer via `JITBuilder::symbol()`, not by linker symbol name." The current usage is harmless (helps with debugger stack traces as noted) but could be omitted for consistency with the "optional" guidance. Not actionable — just noting the discrepancy between the "optional" guidance and the universal usage.

---

## 3. Architecture Documents

### 3a. `design/arch/architecture.md`

**Assessment**: Clean. Lines 92-97 correctly use the new naming convention:
- `runtime/alloc` / `runtime/dealloc` (Rust: `heap_alloc` / `heap_dealloc`)
- `runtime/panic` (Rust: `runtime_panic`)
- `str-concat`, `str-eq`, `int-to-string`, etc. (Rust: `str_concat`, `str_eq`, `int_to_string`, etc.)
- `runtime/trace_enter`, `runtime/trace_exit`, etc.

No `cranelisp_` references remain.

### 3b. `design/arch/interfaces.md`

**Assessment**: Clean for what it covers, but has a coverage gap (see F-5).

All JIT names in the extern function declarations (lines 1222-1296) use the new convention. The registration table (lines 1280-1288) is consistent with `runtime.md`. No `cranelisp_` references.

### F-5 (Important): `interfaces.md` missing `str-len`, `runtime/panic`, `runtime/rc_underflow_check` from extern function list

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/design/arch/interfaces.md`, lines 1211-1300
**Severity**: Important

The "Ring 1 Extern Primitives" section in `interfaces.md` lists allocation functions, string primitives, and RC primitives. Three functions that are documented in `runtime.md` are absent from `interfaces.md`:

1. **`str-len`** (Rust: `str_len`) — present in `runtime.md` lines 126, 191 but missing from the `interfaces.md` string primitives section (lines 1230-1274) and registration table (lines 1280-1288).

2. **`runtime/panic`** (Rust: `runtime_panic`) — documented in `architecture.md` line 94 and `runtime.md` line 185, but not declared in the `interfaces.md` extern function section. Ring 0 uses a Cranelift trap instead, but `ring0-interfaces.md` line 1108 says "Ring 1+ will require a thread-local error flag" — the function still needs to be in the interface contract for Ring 1+.

3. **`runtime/rc_underflow_check`** (Rust: `rc_underflow_check`) — documented in `runtime.md` line 186 but not in `interfaces.md`.

**Impact**: `interfaces.md` is described as "complete Rust type signatures for every type that crosses a crate boundary." Missing functions from the authoritative interface document creates ambiguity about whether they are part of the contract.

**Recommendation**: Add these three functions to `interfaces.md` in the appropriate sections, with the same JIT name / Rust name / signature format used for the existing entries.

### 3c. `design/arch/CLAUDE.md`

**Assessment**: Clean. No `cranelisp_` references (only Rust crate names like `cranelisp-types`, which are not JIT symbol names).

### 3d. `design/arch/ring0-interfaces.md`

**Assessment**: Clean. Line 1108 correctly references `runtime/panic` (Rust: `runtime_panic`). No stale `cranelisp_` references.

### 3e. `design/arch/design-space.md`

**Assessment**: Clean. All runtime function references use the new convention (e.g., `runtime/alloc_string`, `str-concat`, `vec-get`, `map-get`). No `cranelisp_` references.

---

## 4. Platform Design Doc (`design/platform/runtime.md`)

**Assessment**: Clean and comprehensive. The JIT Symbol Registration table (lines 181-197) is the most complete single reference for the Rust-to-JIT name mapping. All 14 functions are listed with correct JIT names and categories.

This document is the best single source of truth for the complete mapping. It agrees with `architecture.md` and `interfaces.md` on all shared entries.

---

## 5. Design-Space and Ring 0 (`design/arch/design-space.md`, `design/arch/ring0-interfaces.md`)

Already covered in 3d and 3e above. Both are clean.

---

## 6. Cross-Consistency

### F-6: Agreement across core documents

All three core documents agree on the same JIT names for shared entries:

| Function | `architecture.md` | `interfaces.md` | `runtime.md` |
|----------|-------------------|-----------------|--------------|
| `runtime/alloc` | line 92 | line 1222 | line 183 |
| `runtime/dealloc` | line 92 | line 1226 | line 184 |
| `runtime/panic` | line 94 | **MISSING** | line 185 |
| `str-concat` | line 95 | line 1240 | line 189 |
| `str-eq` | line 95 | line 1245 | line 190 |
| `str-len` | -- | **MISSING** | line 191 |
| `int-to-string` | line 95 | line 1250 | line 193 |
| `float-to-string` | -- | line 1255 | line 194 |
| `bool-to-string` | -- | line 1260 | line 195 |
| `string-identity` | -- | line 1266 | line 192 |
| `parse-int` | -- | line 1272 | line 196 |
| `runtime/alloc_string` | -- | line 1235 | line 187 |
| `runtime/string_read` | -- | line 1295 | line 188 |
| `runtime/rc_underflow_check` | -- | **MISSING** | line 186 |

Where entries exist in multiple documents, names are consistent. The gaps are in `interfaces.md` only (see F-5).

---

## 7. Gaps and Stale References

### F-7 (Important): Plan files retain dozens of `cranelisp_` references

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-runtime/plan-platform.md`
**Severity**: Important
**Lines**: 36-41, 47, 53, 59-62, 68-73, 89-112, 182, 193-194, 239, 244, 254, 259, 313, 315-316, 331, 334, 342, 363-364, 388-389, 395, 470-471, 535-536, 545

This file contains approximately 50 occurrences of `cranelisp_`-prefixed function names (`cranelisp_alloc`, `cranelisp_panic`, `cranelisp_dec_guarded`, `cranelisp_trace_*`, `cranelisp_op_*`, etc.). These are from the pre-convention prototype survey.

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/crates/cranelisp-backend/plan-backend.md`
**Severity**: Important
**Lines**: 100, 357, 513, 517, 522-530, 738

This file contains approximately 10 occurrences of `cranelisp_`-prefixed names (`cranelisp_panic`, `cranelisp_alloc`, `cranelisp_free`, `cranelisp_*`).

**Impact**: Plan files are living documents that skill agents read when implementing. Stale naming in plan files will cause confusion and may lead to inconsistent implementation. A developer reading `plan-platform.md` would see `cranelisp_alloc`
and might implement it that way.

**Recommendation**: Either (a) update both plan files to use the new naming convention, or (b) add a prominent header noting that the naming convention has changed and that all `cranelisp_` references should be read as their new equivalents per `src/CLAUDE.md` §"JIT Symbol Names".

### F-8: Ring 0 review report and checklist retain `cranelisp_` references

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/design/review/ring0-report.md`
**Severity**: Suggestion
**Lines**: 65, 68, 79, 153, 326, 394, 466

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/design/review/ring0-checklist.md`
**Severity**: Suggestion
**Lines**: 13, 97

These are historical artifacts — the Ring 0 report was written before the naming convention change and correctly describes the state of the code at that time. The `cranelisp_panic` references describe a finding (H-1) that has since been resolved (the backend now uses a Cranelift trap, and `runtime_panic` is the new Rust function name). These files should be treated as historical records rather than updated, but a reader may be confused.

**Recommendation**: No action required — these are correctly historical. Optionally, add a note at the top of `ring0-report.md` that naming was updated after the report was written.

### F-9 (Suggestion): `src/CLAUDE.md` rule 5 mentions `#[unsafe(no_mangle)]` but the runtime uses it universally

**File**: `/Users/alilee/Projects.nosync/rust/cranelisp/src/CLAUDE.md`, line 46
**Severity**: Suggestion

Rule 5 says `#[unsafe(no_mangle)]` is "optional" — but every extern function in `cranelisp-runtime` uses it. This is not a contradiction (optional means you may use it), but clarifying whether the project convention is "always use it" or "truly optional" would prevent future inconsistency.

---

## Findings Summary

| ID | File | Lines | Severity | Description |
|----|------|-------|----------|-------------|
| F-2 | `src/CLAUDE.md` | 32-38 | Suggestion | ADT constructor functions missing from naming table |
| F-3 | `src/CLAUDE.md` | 32-38 | Suggestion | Drop glue / internal codegen functions not mentioned |
| F-4 | `crates/cranelisp-runtime/src/*.rs` | various | Suggestion | `#[unsafe(no_mangle)]` used universally despite "optional" guidance |
| F-5 | `design/arch/interfaces.md` | 1211-1300 | Important | `str-len`, `runtime/panic`, `runtime/rc_underflow_check` missing |
| F-7 | `crates/*/plan-*.md` | various | Important | ~60 stale `cranelisp_` references in plan files |
| F-8 | `design/review/ring0-*.md` | various | Suggestion | Historical `cranelisp_` in report/checklist (acceptable as-is) |
| F-9 | `src/CLAUDE.md` | 46 | Suggestion | `#[unsafe(no_mangle)]` guidance vs practice discrepancy |

**Blockers**: 0
**Important**: 2 (F-5, F-7)
**Suggestions**: 5 (F-2, F-3, F-4, F-8, F-9)

---

## Next skills

- `/arch` — Address F-5 by adding missing functions to `interfaces.md`
- `/platform` — Address F-7 by updating or annotating `plan-platform.md`
- `/backend` — Address F-7 by updating or annotating `plan-backend.md`
- `/arch` — Consider F-2 and F-3 when ADT constructors and drop glue are designed for Ring 1
