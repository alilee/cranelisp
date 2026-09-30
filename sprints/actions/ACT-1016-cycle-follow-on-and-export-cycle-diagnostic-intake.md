---
id: ACT-1016
title: Make a reload that closes a module cycle leave every module as a restart does, and report an export-closed cycle as a circular dependency in every mode
status: deferred
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - spec/08-modules.md
  - repl/spec/14-file-watching.md
  - design/int/repl-lifecycle.md
  - design/int/int.md
---

## Disposition

- User-approved carry from S122 to the next increment (S123), 2026-09-30:
  “carry”, in response to the joint fix-now/carry decision for both faces.
- First deferral. Both defects and their completion criteria remain open;
  the requirements are unchanged. This accepts the recorded reload/restart
  mismatch and misleading export-cycle diagnostic until the correction.
- Owner: `qa`. Revisit at S123 scope intake, remeasure both faces on that
  checkpoint, then route evidence and the internal correction to their owners.
- This disposition covers ACT-1016 only, not ACT-1015 or ACT-1017.
- Disposition verification: reopened spec §8.10, REPL file-watching
  requirements and int §6.11's explicitly unimplemented failed-dependency
  refusal. The final ACT-1014 QA report states these faces were not corrected
  or re-probed at `f0d1006f…`; no new execution or resolution is claimed.

## Request

QA measured two defects on source `d056842f…` (dirty on `e4062202`) while
attributing ACT-1014's helper-end row. The prelude is not involved in either.
This intake is carried under the disposition above.
[Attribution record](../../tests/plan/s122-evidence-delta.md#r1-helper-end-row--attribution-2026-09-30);
probes are in `.local/s122-helper-followon-qa-scratch/`.

### Face 1 — the follow-on accepts a module the restart fails

- **Requirement.**
  - REPL §14.6: a restart does not bypass a failure, so a session and a
    restart on the same saved files agree.
  - Spec §8.10.3: a dependent compiles only after its dependency.
- **Face.** The files are `c.cl` `(defn k [] 7)`, `a.cl`
  `(export [c [k]]) (defn f [] 1)`, `b.cl` `(defn g [] (a/k))` and `user.cl`
  `(defn run [] (b/g))`. A save of `a.cl` adds `(defn h [] (b/g))`.
  - The session reports `[errors: a.cl]` naming `b -> a -> b`, with
    `[updated: b.cl]` and `[updated: user.cl]`.
  - A restart fails `b` and `user` with `dependency 'a' failed`, and `/sig b/g`
    finds no definition.
- **Control.** A twin differs only in `b` also defining `(defn g2 [] (a/f))`.
  It fails `a`, `b` and `user`. So `b` fails only when it uses a name that the
  failed `a` table lacks.
- **Mechanism (supported by the control).**
  - [REPL lifecycle §1.2](../../design/int/repl-lifecycle.md#12-poll-and-reload)
    Cycles says the follow-on "fails the earlier members against that
    member's failed table". Nothing realises this. The follow-on rebuilds `b`
    against the failed `a`, and `b` fails only on a missing name.
  - The publication check sees no edge back, because the closing edge was in
    `a`'s failed generation.
  - Refuter: a dependent that uses nothing missing from the failed table ends
    failed.
- **Coverage.** Every existing cycle-reload cell's dependent used a name that
  the failed table lacks. An example is `b`'s `(a/f)` in
  `repl_persist.rs::watch_save_closing_qualified_module_cycle_reports_circular_dependency`.
- **Not in scope: the implicit prelude edge.** At a fresh load, `x` compiles
  and the prelude is refused
  ([int §6.12](../../design/int/int.md#612-the-implicit-prelude-dependency)).
  The session already agrees there. A correction must not fail `x`
  (ACT-1014).

### Face 2 — a cycle closed by `export` is reported as an unresolved name

- **Requirement.**
  - Spec §8.10.1 puts `export` in the dependency graph.
  - §8.10.2 requires the cycle to be reported.
  - QA's [adjudication](../../tests/plan/s122-evidence-delta.md#design-residuals--adjudication-2026-09-30)
    applies §8.5.4 item 6 to `export`: the cycle must not surface as an
    unresolved name.
- **Face.** The Face 1 fixture, with the save of `a.cl` adding
  `(export [b [g]])` instead of `h`.
  - The session reports `'g' not found in module 'b'` and `[updated: b.cl]`.
  - A restart reports the same unresolved name.
  - `--run` with `main.cl` `(defn main [] (b/g))` also reports it, in 3 of 3
    runs. Which module the error names varies between runs.
- **Design falsified.** Int §6.12 "Why only the prelude edge" rests on "every
  other dependency edge is a wait at a fresh load". An `export` edge to an
  in-flight module reports no wait cycle.
- **Relation.** ACT-1014's prelude `export` notice was the same face in a
  session follow-on. The Pass-0 fail-fast
  ([int §6.11](../../design/int/int.md#611-module-cycles-at-publication))
  corrected it there. The fresh-load face is unchanged.

## Completion evidence

1. `design`(int) states the correction, or records a disposition with `sprint`
   and the user. ACT-1014's correction was not directed at these faces, and
   neither face was re-probed on its source `f0d1006f…`.
2. Face 1: `dev` adds a session row pair, shaped like the fixture and control
   above. It is observed RED before the fix. After the fix, `b`'s outcome
   matches a fresh session on the saved files, and the control stays as it
   is.
3. Face 2: `test` adds a spec-traced e2e cell beside the `--run` cycle cells in
   `spec_08_modules.rs`. The cell covers `--run` and REPL startup, and one
   reload leg. Every leg names a circular dependency through `a` and `b`, and
   reports no `not found in module`. The cell is observed RED before the fix.
4. QA judges adequacy and deletes this action.
