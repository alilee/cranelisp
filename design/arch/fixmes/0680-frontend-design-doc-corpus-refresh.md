---
number: 0680
target: /dev
filed_by: /sprint
filed_at: 2026-07-20
sprint_filed: 114
refers_to: audits/frontend-s113.md §3 R5; crates/cranelisp-frontend/plan-frontend.md §1 (PEG); crates/cranelisp-frontend/src/defmacro.rs:16-18/:210-212/:354 ↔ lib.rs:167-169 narrowing-contract contradiction
status: open
---

# Audit R5 — frontend doc-corpus refresh: the /dev(frontend) crate-local half

Accepted at S114 Phase 1 (user, 2026-07-20) from `audits/frontend-s113.md` §3 R5.

**The /design(frontend) half is DONE (S114 Phase 3)** — re-targeted this FIXME to
`/dev`(frontend) for the crate-local files it owns:

- **`design/frontend/*` (design owner) — COMPLETE:** deleted `macro-resolver-trait.md`
  (superseded ~37 sprints), `implementation-slice-s66.md` (one-shot S66 slice),
  `sprint-70-cascade-plan.md` (one-shot S70 cascade) to git history; corrected
  `frontend.md` §§2/3.1/3.2/4/9 (false `parse_*_sexp` re-export claim, ~2× stale
  LOC/test counts, §3.2 classifier status, §9 register + prune record); rewrote
  `design/frontend/CLAUDE.md` "What to Document" (removed PEG + macro-expander).
  Authored `enforcement-matrices.md`; §9 register has no "archive candidate"
  older than one sprint. Done criteria met for `design/frontend/`.

## Remaining — /dev(frontend), crate-local files

1. **`crates/cranelisp-frontend/plan-frontend.md` §1** — still records
   "Decision: `peg` 0.8" with porting instructions (audit HIGH-5/F3, third
   flagging). The reader is hand-written recursive descent. Refresh §1 to
   "hand-written recursive descent" (or delete the doc — it is a pre-Ring-0
   plan with no live content; git history is the archive).

2. **The `defmacro.rs` ↔ `lib.rs` narrowing-contract contradiction — the
   narrowing story is RULED (`frontend.md` §9.1): `lib.rs` is correct, there is
   NO "narrow back".** FIXME 0098 Phase 2's "migrate `expand` into frontend" was
   withdrawn by S76 W-Macro (`expand` deleted, not migrated), so the event the
   `defmacro.rs` rustdoc conditions its narrowing on never happens. **The losing
   rustdoc is `defmacro.rs:16-18/:210-212/:354`** — delete the "narrows back to
   `pub(crate)` at FIXME 0098 Phase 2 close" sentences. No `public-api.txt`
   change (the helpers are already public and stay so).

**Done (remaining half):** `plan-frontend.md` no longer names `peg`; no two
shipped `crates/cranelisp-frontend/` docs state contradictory narrowing
contracts. (May be batched with FIXME 0681's R6 hygiene sweep — same
`/dev`(frontend) crate-local surface — at /sprint's discretion.)
