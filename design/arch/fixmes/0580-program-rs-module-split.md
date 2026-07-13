---
number: 0580
target: /dev
filed_by: /sprint
filed_at: 2026-07-13
sprint_filed: 109
refers_to: crates/cranelisp-typecheck/src/program.rs (3,962 lines) module split.
  Design sign-off by /design on the module cut. From S108 audit
  `audits/cranelisp-typecheck-s108.md` R-4, accepted S109 Phase 1.
status: open
---

# R-4 — Give `program.rs` the `traits/` treatment (module split)

Accepted from the S108 `cranelisp-typecheck` audit assessment (R-4). Quoting:

> **R-4. Give `program.rs` the `traits/` treatment.**
> - Evidence: §2.3 — 3,962 lines; `finalize_check_result_inner` 188 effective
>   and growing (2016–2383), `check_form_body_single_defn` ~287 raw,
>   `pass4_monomorphise` ~260 raw; the in-context precedent
>   (`s87-traits-decomposition.md`) demonstrably improved traits/.
> - Cost: **medium** (mechanical split + test relocation; behaviour-identical).
>   Owner: **/dev** (typecheck), design sign-off by **/design** on the module cut
>   (register / body / finalize / mono-collect is the natural seam set).
> - Done: no `program.rs` submodule exceeds ~1,200 lines; the phase drivers are
>   named sub-functions within budget; `program/tests.rs` splits alongside per
>   METHOD §2.2 attributability.

**Scope:** `cranelisp-typecheck`. Behaviour-identical (no assertion/semantic
change) — a pure decomposition; verify by unchanged suite. **Read first:** the
assessment §2.3 + `s87-traits-decomposition.md` (the precedent). `/design` signs
off the register/body/finalize/mono-collect cut before `/dev` moves code.
`cargo check` + warning cleanup. Resolve + delete this file when done.

## `/design` SIGN-OFF (S109 Phase 3) — cut approved; FIXME stays OPEN for the `/dev` tail

The module cut is signed off in **`design/typecheck/program-decomposition.md`**.
Summary: eight submodules — `mod` (hub + `check_form` dispatcher + accumulator
types), `support` (free-fn toolbox), `callees` (S101 harvest), `register`
(Pass-1, ~880L), `body` (Pass-2, ~590L), `finalize` (merge/finalize, ~820L),
`mono_collect` (Pass-4 collection, ~595L), `test_driver` (`#[cfg(test)]`) — all
under the ~1,200-line gate. Stage A (in-place phase-split of
`finalize_check_result_inner` §2.1, plus `check_form_body_single_defn` /
`pass4_monomorphise`) precedes Stage B (file move + `program/tests.rs` per-submodule
split §3), suite-green between; `public-api.txt` byte-identical (private `mod
program`). Hazards + acceptance contract in the doc §4. Lands LAST in the Phase-5
order (after bucket 2 / 0581 / 0579), rebasing trivially.

**Remaining `/dev` tail (why this FIXME stays open):** execute the move + phase-split
+ test split, verify `public-api.txt` zero-diff, update the `program::tests::`
path citations (CLAUDE.md `callees_*` / cross-module-mono, `tests/plan` — or a
`#[cfg(test)] pub(crate) use` alias). Delete this file when landed + verified.

Forbidden git operations: `git stash drop`, `git stash clear`, `git reset --hard`,
`git checkout --`, `git restore`, `git clean -f`, `git clean -fd`. The `git stash`
+ `git stash pop` pair is permitted if the pop completes cleanly.
