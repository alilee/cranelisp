---
number: 0190
target: /design (intrinsics)
filed_by: /dev (primitives)
filed_at: 2026-05-15
sprint_filed: 67
refers_to: design/arch/facades/intrinsics.md, tests/facade_compliance.rs::facade_compliance_orphans_match_expected_sprint_67_baseline, crates/cranelisp-intrinsics/public-api.txt
status: open
---

# `cranelisp-intrinsics` facade does not name the renamed `heap_string` / `vec_runtime` modules

## Issue

Sprint 67 Wave 3 (FIXME 0180 close) physically relocated user-callable
string + vec primitives out of `cranelisp-intrinsics` into
`cranelisp-primitives`. The two intrinsics modules that retained the
backend-emitted-call infrastructure were renamed to avoid colliding with
the primitives surface in the `cargo-public-api` baseline:

| Was | Now |
|---|---|
| `cranelisp_intrinsics::string::*` | `cranelisp_intrinsics::heap_string::*` |
| `cranelisp_intrinsics::vec::*` | `cranelisp_intrinsics::vec_runtime::*` |

The rename is mechanical — same `HeapString` layout, same `runtime/alloc_string`
+ `runtime/string_read` + `runtime/vec_new` + `runtime/vec_drop` + COW vec
extern fns. Only the module names changed.

`tests/facade_compliance::facade_compliance_orphans_match_expected_sprint_67_baseline`
reports 2 orphans in intrinsics:

- `heap_string`
- `vec_runtime`

These are the new module names which do not appear (yet) in
`design/arch/facades/intrinsics.md`.

## Proposed resolution

Update `design/arch/facades/intrinsics.md` to:

1. Replace `cranelisp_intrinsics::string` references with
   `cranelisp_intrinsics::heap_string` (or list both, with the rename
   rationale).
2. Replace `cranelisp_intrinsics::vec` references with
   `cranelisp_intrinsics::vec_runtime` (or list both).
3. Note the rename in a short "Module name rationale" subsection per
   `crates/cranelisp-intrinsics/src/lib.rs`'s top-of-file comment that
   already explains the choice.

The rename was driven by the `tests/facade_pif_rows::row_27_*` contract:
`string` / `vec` substrings on the intrinsics pub-api would mask the
primitives-side relocation. Module-renaming was the path of least
disturbance to the backend's call sites (intrinsic_symbols imports were
also updated in the same change-set).

## Operational implication / Context

- Wave 3 `/dev (primitives)` cannot edit `design/arch/facades/intrinsics.md`
  (file-ownership boundary).
- `facade_compliance_orphans_match_expected_sprint_67_baseline` currently
  reports 5 orphans total (2 here + 3 from primitives — FIXME 0189).
  Resolving this FIXME drops the total to 3 (or 0 if 0189 lands too).
- Backend's `intrinsic_symbols()` table in `crates/cranelisp-backend/src/jit.rs`
  was mechanically updated to import from the renamed paths
  (`cranelisp_intrinsics::heap_string::heap_alloc_string`, etc.). No
  symbol-name semantics changed at the JIT-symbol layer.
