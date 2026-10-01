---
id: ACT-1047
title: A backing file that exists but was never recorded must not be overwritten by the next definition
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-10-02
refers_to:
  - repl/spec/15-session-persistence.md §15.1
  - repl/spec/15-session-persistence.md §15.2
  - repl/spec/14-file-watching.md §14.1
  - repl/spec/00-cli-invocation.md §0.5.5
  - src/session_v4/lifecycle.rs::CompilerSession::backing_file_changed_unseen
  - src/session_v4/lifecycle.rs::register_entry_module
  - design/int/repl-lifecycle.md §1.3.1
  - tests/plan/s122-evidence-delta.md
---

## Request

When the REPL starts with no `user.cl` and the user then creates one outside
the REPL, the next definition must not destroy the user's bytes. QA closes
this intake once the outcome the user rules is evidenced.

## Defect

- **Source.** Review N3 (required), `.local/s122-6a/review8-result.md`, with
  the review's probe `.local/review-s122-lock/probe9.py`. QA reproduced it
  with discriminating siblings
  ([record](../../tests/plan/s122-evidence-delta.md#review-n3--a-never-recorded-backing-file-2026-10-02)).
- **Face.** Start with no `user.cl`, write `(defn k [] 9)` to `user.cl` at
  the prompt, then enter `(defn h [] 2)`. The file becomes
  `(defn h [] 2)\n`. The user's definition is lost without a warning, and
  `(k)` is an undefined variable.
- **Class: `lost-update`.** The write chokepoint compares the file on disk
  with the state the session recorded for it. A file with no record passes,
  so regeneration writes over a change it never detected.
  - **Sibling.** The same save and turns, with `user.cl` present at start or
    first written by the session's own regeneration, keep the save. Only the
    presence of a record differs.
  - **Seam (source).** `backing_file_changed_unseen` returns `false` when
    `recorded_source(path)` is `None`. Its doc comment says that case "is not
    reached today"; the probe reaches it.
  - **Refuted if** a module row that creates the backing file of an entry
    registered absent, then regenerates, leaves the file unchanged on current
    code.
- **Where it entered.**
  - `design`(int): REPL lifecycle §1.3.1, Write chokepoint, covers a file that
    differs from its record and a missing file, not a file that exists with
    no record. The design's own rule is that the user's bytes win.
  - `dev`(src): the inaccurate doc comment.
  - **Coverage (QA).** The N1 and N2 allocations varied the save's placement
    against turns and against the watcher's first sight. Every fixture began
    with a `user.cl` the session had read, so none varied whether a record
    existed. The record states to enumerate against the chokepoint are:
    recorded readable, recorded unreadable, recorded after the session's own
    first write, and never recorded.
- **It predates S122.** Before N1 every regeneration overwrote an unseen save.
  N1 protected recorded files only.

## User decision (pending)

The requirement leaves the remedy open. §15.2 and §0.5.5 rule 2 start an
empty module when no backing file exists, and §14.1 says a new file does
nothing until it is referenced. Two outcomes conform to the design rule:

- **Protect only.** The definition stays in the session, the file keeps the
  user's bytes, and the user is told.
- **Load.** The created file is loaded as the entry's source, and later
  definitions are written with it.

`spec` frames the question through `sprint`; the user decides. QA does not
presume either outcome.

## Evidence allocation

- **`test`, now or later: FC-1, the leg both outcomes share.** In
  `tests/repl_persist.rs`, with the staged harness: start with no `user.cl`.
  After the first prompt, `Stage::Write` creates `user.cl` as
  `(defn k [] 9)\n`. Then send `(defn h [] 2)` and end the input. The final
  `user.cl` contains `(defn k [] 9)` (§15.1; design §1.3.1). Control: the same
  stages with `user.cl` present at start as `(defn g [] 1)\n`; the final file
  contains `(defn k [] 9)`.
  - **Before the fix:** subject RED (the file is `(defn h [] 2)\n`), control
    GREEN. Observe it RED with the test source hash before `dev` starts.
  - **Determinism.** The write precedes the turn, and the current code
    overwrites whatever the timing.
  - **Notation:**
    `// defect: class=lost-update locus=src/session_v4/lifecycle.rs::CompilerSession::backing_file_changed_unseen found=S122 owner=/dev`.
- **After the ruling (QA allocates).** The legs that differ: for protection,
  a warning and a byte-identical file; for loading, `(k)` gives 9 and the
  file holds `k` and `h`. `dev` adds the matching module row at the
  chokepoint or at entry registration, RED first, and corrects the comment.

## Completion evidence

- The user's ruling is recorded, and `design`(int) states the rule.
- FC-1 and its ruling legs are observed RED, then GREEN in a full suite, with
  the control GREEN both times.
- `dev` reports the module row RED, then GREEN.
- QA restores the §15.1 band and deletes this intake.
