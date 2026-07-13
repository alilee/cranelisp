---
number: 0579
target: /dev
filed_by: /sprint
filed_at: 2026-07-13
sprint_filed: 109
refers_to: cranelisp-typecheck resolution-seam rustdoc + naming (stale S78 block,
  "outer scope" rustdoc, resolve_entry_in_current_module rename). From S108 audit
  `audits/cranelisp-typecheck-s108.md` R-2, accepted S109 Phase 1.
status: open
---

# R-2 — One post-convergence doc-and-naming sweep of the resolution seams

Accepted from the S108 `cranelisp-typecheck` audit assessment (R-2). Quoting:

> **R-2. One post-convergence doc-and-naming sweep of the resolution seams.**
> - Evidence: §2.6/§2.7 — the stale S78 doc block (checker.rs:919–954, false
>   "two-hop is realized caller-side" claim), "outer scope" rustdoc at
>   checker.rs:863/921/1580/1609 and dispatch.rs:362–405, CLAUDE.md:262; the
>   misleading `resolve_entry_in_current_module` name (checker.rs:1571) vs its
>   `_scoped` siblings. Subsumes and widens the already-tracked "scope_resolve
>   stale doc-comment" micro-task (SPRINT.md Inc3).
> - Cost: **small** (mechanical; no assertion or behaviour change). Owner:
>   **/dev** (typecheck).
> - Done: no rustdoc in the crate describes the caller-side retry; `grep -in
>   "outer scope" crates/cranelisp-typecheck/` yields zero conceptual uses
>   (historical citations may remain if past-tensed);
>   `resolve_entry_in_current_module` renamed into the `_scoped` family (e.g.
>   `resolve_entry_scoped`) with a doc naming the intrinsic fallback. Cures the
>   recurrence vector (`/review` already classed misleading resolution rustdoc as
>   one — its S1 finding this sprint), not just the wording.

**Scope:** `cranelisp-typecheck`. **Read first:** the assessment §2.6/§2.7 + the
cited seams. Note the model correction from S108: the prelude is an **implicit
import**, ONE transparent-fallback lookup — NOT an "outer scope" (see
`memory/prelude-is-implicit-import-one-fallback-no-outer-scope`); the rustdoc
must reflect §8.6.4/§8.8.1, not the retired outer-scope framing. `cargo check` +
warning cleanup. Resolve + delete this file when done.

Forbidden git operations: `git stash drop`, `git stash clear`, `git reset --hard`,
`git checkout --`, `git restore`, `git clean -f`, `git clean -fd`. The `git stash`
+ `git stash pop` pair is permitted if the pop completes cleanly.
