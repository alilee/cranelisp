---
id: ACT-1048
title: Decide what the REPL does when a loaded source file is deleted mid-session
status: deferred
priority: advisory
from: sprint
to: spec
sprint: 122
filed_at: 2026-10-02
refers_to:
  - repl/spec/14-file-watching.md
  - design/int/repl-lifecycle.md
  - src/watch.rs
---

## Request

State the requirement for a loaded module's backing file that disappears
during a session. The rule must separate a real deletion from an editor's
write-then-rename save, during which the file is briefly absent.

## Observation

Today a missing file is not a change. The module keeps its definitions, and
the next definition writes the file again. `repl/spec/14-file-watching.md`
says nothing about deletion. `design/int/repl-lifecycle.md` §1.2 (Content hash)
records the skip as standing pending this ruling. The skip loses no saved
bytes.

## Disposition

The user carried this to S123 on 2026-10-02 (“carry both”). Spec puts the
question to the user. Design(int) and dev(src) follow any ruling.
