---
number: 0610
target: /dev
filed_by: /sprint
filed_at: 2026-07-15
sprint_filed: 110
scheduled: S110
refers_to: repo/comment hygiene — gitignore agent_trace.txt (+ stray repo-root
  user.cl); refresh stale src/lib.rs module comments. Narrow-deploy /dev to src/
  (the .gitignore line may alternatively ride /sprint's next commit).
status: open
---

# Repo/comment hygiene: gitignore `agent_trace.txt`; refresh `lib.rs` module comments

## Source

S109 `src/` whole-context audit (`audits/src-s109.md` R-6), **ACCEPTED** S110 Phase 1;
plus the S109 Phase-6 `/stdlib` finding (stray repo-root `user.cl`).

## Evidence (quoting the assessment §2.5/§2.2 + S109 Phase-6 findings)

- `agent_trace.txt` (1.0 MB dev-session trace, NG4 artifact) sits untracked at the repo
  root and is NOT gitignored — one `git add -A` away from history.
- Stray repo-root `user.cl` (~131 KB REPL-persistence artifact) poisons the `user`
  module for repo-root REPL eval (`/stdlib` S109 finding). Gitignore + note the cause.
- `src/lib.rs` module comments are stale: `:22-27` ("not yet reachable … FIXME 0176")
  describes the LIVE `cluster` hot path as dormant; `:7/:30/:35` cite the retired
  `facades/int.md`; `:108-114` describes `agent` as a Wave-2 placeholder.

## Done (assessment §3 R-6)

Trace/log/persistence artifacts gitignored; `lib.rs` comments state current facts (or are
deleted where the module rustdoc suffices). Trivial — the `.gitignore` line rides the next
`/sprint` commit if convenient.
