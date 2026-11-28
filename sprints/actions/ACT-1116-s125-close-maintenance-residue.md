---
id: ACT-1116
title: S125 close maintenance residue — stale FIXME citations, private doc links, audit F5 row
status: open
priority: advisory
from: sprint
to: dev
sprint: 126
filed_at: 2026-11-28
refers_to:
  - src/marshal.rs
  - crates/cranelisp-intrinsics/src/trace_format.rs
  - crates/cranelisp-backend/src/compiler/control_flow/fn_as_value.rs
  - audits/cranelisp-intrinsics-s125.md
---

## Request

Mechanical repairs, one per owning surface. Each item below was verified on
2026-11-28.

1. **`dev`(`src/`).** `src/marshal.rs:481`, in the test
   `imported_tag_constants_have_pinned_values`, has a `// spec:` line citing
   the retired FIXME 0498. That FIXME is retired and the file is gone.
   Point the line at the current authority.
2. **`dev`(intrinsics).** `crates/cranelisp-intrinsics/src/trace_format.rs`,
   lines 13 and 31, cites FIXME 0255. That FIXME is retired and the file is
   gone. Replace the citation with the current authority.
3. **`dev`(backend).** Five intra-doc links are broken under
   `cargo doc --document-private-items`:
   - `compiler/control_flow/fn_as_value.rs:142`
   - `utilization.rs:356`
   - `literals.rs:281`
   - `context.rs:319`
   - `jit.rs:87`

   The public `cargo doc -D warnings` run is clean.
4. **`audit`.** In `audits/cranelisp-intrinsics-s125.md`, the F5 row overstates
   delivery for bounded contexts. Correct it against what S125 delivered.

5. **`design`(int).** The header of `design/int/s125-binary-clean.md` still
   says that nothing in the document is in source. Since S125, several
   sections describe delivered behaviour.

## Completion evidence

- Items 1 and 2: the document checker reports no finding for those lines.
- Item 3: `RUSTDOCFLAGS="-D warnings" cargo doc -p cranelisp-backend --no-deps --document-private-items` exits 0.
- Item 4: the corrected row.
- Item 5: a header that states the document's current status.
