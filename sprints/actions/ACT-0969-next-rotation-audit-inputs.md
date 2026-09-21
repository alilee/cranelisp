---
id: ACT-0969
title: Hand the uncarried suggestion-grade audit observations to each context's next rotation audit
status: open
priority: advisory
from: audit
to: sprint
sprint: 122
filed_at: 2026-09-21
refers_to:
  - sprints/METHOD.md §2.7
  - crates/cranelisp-frontend/src/ast_builder.rs
  - crates/cranelisp-backend/src/compiler/apply.rs
  - crates/cranelisp-backend/src/compiler/fn_compiler.rs
  - crates/cranelisp-intrinsics/src/io.rs
  - crates/cranelisp-primitives/src/marshal.rs
---

## Request

With the audit reports retired to Git history, a future rotation audit no
longer finds its predecessor in `audits/`. These observations were recorded
during the S122 retention passes as "facts for the next rotation assessment".
None is a finding, none was ever recommended, accepted or declined, and none
is approved work. `sprint` includes the matching lines in the brief when it
dispatches that context's next audit, together with the predecessor's Git
reference, and strikes them as each audit lands.

| Context | Predecessor (Git) | Observation to re-judge, not to act on |
|---|---|---|
| frontend | [historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/frontend-s113.md) | `ast_builder.rs` is 2,396 lines and unsplit (S87 F1, never recommended at S113). S87 F6 — the justified `unreachable!`/`expect` sites — was suggestion grade and never re-derived. |
| backend | [historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-backend-s110.md) | After the R5 funnel split, `compile_apply` is ~240 lines; `apply.rs` is 3,014 and `fn_compiler.rs` 5,202 lines, both larger than at S110. |
| intrinsics | [historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-intrinsics-s115.md) | `io.rs` has grown to 1,847 lines with the reactor work; the 2026-06-14 monolith finding was resolved as filed, so this is a new fact. |
| primitives | [historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-primitives-s116.md) | S87 LOW-2: `marshal.rs` reads and writes cells through offset-indexed `read_i64`/`write_i64` free functions rather than a typed accessor. Suggestion grade; unchanged; never disposed. |
| platform | [historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-platform-s117.md) | Every "ABI v9" statement in that assessment is dated: `ABI_VERSION` is now 11. Read it as history, not as the current contract. |

## Completion evidence

Each row is struck when its context's next rotation assessment has been
dispatched with the row in its brief. Delete the action when the table is
empty. If the rotation audit is itself retired as a practice, put the five
rows to the user once and delete.
