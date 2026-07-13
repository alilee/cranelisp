---
number: 0581
target: /dev
filed_by: /sprint
filed_at: 2026-07-13
sprint_filed: 109
refers_to: cranelisp-typecheck S87 residue — half-FQ diagnostics
  (dispatch.rs/monomorphise.rs), _=>None silent drop (form.rs), "user"-defaulting
  dead helper (checker.rs). Wants a /testing twin repro for the S87-1 fix. From
  S108 audit `audits/cranelisp-typecheck-s108.md` R-5, accepted S109 Phase 1.
status: open
---

# R-5 — Disposition the S87 residue batch (three small in-crate items)

Accepted from the S108 `cranelisp-typecheck` audit assessment (R-5). Quoting:

> **R-5. Disposition the S87 residue batch (three small in-crate items).**
> - Evidence: §2.8 — S87-1 half-FQ diagnostics (dispatch.rs:64–70,
>   monomorphise.rs:670–676; user-facing disambiguation failure); S87-3 `_ =>
>   None` silent drop (form.rs:512; frontend-contract break would vanish rather
>   than fail loudly); S87-4 `"user"`-defaulting dead helper (checker.rs:667–671;
>   Principle-17/19 attractive nuisance).
> - Cost: **small** (all three together are one change-set: a
>   `fq_type_name_for_diagnostics` render at the two error sites + an
>   `unreachable!` with invariant message + helper deletion/de-defaulting).
>   Owner: **/dev** (typecheck); the S87-1 fix wants a `/testing` twin repro (two
>   same-named ADTs, assert the FQ name in the diagnostic).
> - Done: the "no impl" message renders both halves FQ under two same-named ADTs;
>   a new `ParsedEntry` variant fails compilation or loudly at
>   `parsed_to_top_level`; no production-reachable helper roots at `"user"`. If
>   any item is instead **declined**, the trail records it.

**Scope:** `cranelisp-typecheck`. **Coordinate:** the S87-1 half-FQ diagnostic
overlaps the dotted-`Type.Ctor` capability work (scope bucket 2 — same-named ADTs
and their FQ display); land the twin repro so it also covers the two-same-named-
constructor case. `cargo check` + warning cleanup. Resolve + delete this file when
done.

Forbidden git operations: `git stash drop`, `git stash clear`, `git reset --hard`,
`git checkout --`, `git restore`, `git clean -f`, `git clean -fd`. The `git stash`
+ `git stash pop` pair is permitted if the pop completes cleanly.
