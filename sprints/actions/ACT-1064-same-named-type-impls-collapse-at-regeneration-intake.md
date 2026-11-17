---
id: ACT-1064
title: Regeneration keeps one of two impls written for same-named types from different modules
status: open
priority: blocking
from: qa
to: qa
sprint: 124
filed_at: 2026-11-17
refers_to:
  - repl/spec/15-session-persistence.md
  - design/int/session-persistence.md
  - design/int/int.md
  - src/save.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

Lead from `design`(int)
([session persistence §12.3](../../design/int/session-persistence.md#123-enumeration)).
Executed by `qa` on `target/debug/cranelisp` at `4b58ab93`, 2026-11-17, in
scratch directories, no prelude. Modules `a` and `b` each define a type and
`(defn mk [] …)`; the entry imports both as `(import [a []])`, `(import [b []])`.

| Leg | Session | Observed |
|---|---|---|
| Subject | `a` and `b` both define `Box`. At the REPL: `(deftrait Sz (sz [x] Int))`, `(impl Sz a/Box (defn sz [_] 1))`, `(impl Sz b/Box (defn sz [_] 20))`, then `(add-i64 (sz (a/mk)) (sz (b/mk)))` | 21 in the session. The regenerated `user.cl` holds only `(impl Sz b/Box …)` |
| Subject, restart on the cache | `(sz (a/mk))` | SIGSEGV, 3 of 3 |
| Subject, restart with the cache removed | `(sz (a/mk))` | `no impl of trait user/Sz for type Box` |
| Subject, file-loaded | The entry file holds both impls and runs to 21 under `--run`. At the REPL, `(defn extra [] 5)` | The rewritten file holds only `(impl Sz b/Box …)`: a form the user wrote by hand is deleted |
| Control | `b` defines `Crate`; otherwise identical | Both `impl` forms in the file; restart gives 21 |

## Classification: a defect

- **Requirement.** REPL §15.4 rule 1 (round trip) and §15.6.
- **Harm.** The REPL deletes authored source from the user's file, and the
  next session crashes or rejects a call the previous session accepted.
- **Class:** `artifact-underkey`. The regenerator's impl set is keyed by the
  bare `Trait.Type` label, which omits the type's module.
- **Control.** The pair differs only in whether the two types share a name.
- **Seam.** The regenerated file is the keyed set's output and was read
  directly. The key itself is `design`(int)'s source reading, not `qa`'s
  observation.
- **Refuted if** the control loses an impl, or a build that keys the set by
  the settled pair still drops one.
- **The crash face is a hypothesis.** The cache record written at exit holds
  both impls while the saved source holds one, so the restored session
  accepts a call whose implementation the source no longer supplies. It was
  not observed at its own seam. Its trigger disappears with the correction;
  whether a cache record can disagree with its saved source by another
  route stays open.

## Correction

Designed in S124: [int §6.13](../../design/int/int.md#613-import-and-export-entries-and-export-mounts-s124),
impl identity from the writer's record (packet row D10), which keys every
row by the settled pair. No further design is requested.

## Completion evidence

REPRO-1064
([evidence delta §3.7](../../tests/plan/s124-evidence-delta.md#37-repro-1064--same-named-type-impls-collapse-at-regeneration))
fails on the missing form, then passes with its control.
