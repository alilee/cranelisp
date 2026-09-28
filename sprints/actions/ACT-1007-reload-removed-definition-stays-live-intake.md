---
id: ACT-1007
title: Retire a definition that a successful watcher reload no longer defines
status: open
priority: required
from: qa
to: qa
sprint: 122
filed_at: 2026-09-28
refers_to:
  - repl/spec/14-file-watching.md
  - design/int/session-transaction.md
  - src/session_v4/lifecycle.rs
---

## Observation

- **Probe D4** (diagnostic, not a permanent test):
  `.local/s122-persistence-four-design-scratch/probe-observed.log`.
  - `user.cl` holds `(defn g [] 1) (defn h [] 2)`.
  - An external edit leaves only `(defn g [] 1)`.
  - The reload reports `[updated: user.cl]`, and `(h)` then returns
    `:primitives/Int 2`.
- **Binary.** The probe ran against the binary built before the S122 P3/P4
  correction, and the log records no digest. That correction changed
  `reload_module`, so the observation needs a current rerun.

## Requirement

`14-file-watching.md` §14.2 step 2 requires a reload to remove the module's
previous definitions before recompiling. §14.4 and §14.5 give the reason: the
source file and the runtime must not diverge. A definition the file no longer
contains stays callable, so they diverge.

## Attribution (provisional)

- **Entry.** The int design leaves this case open:
  [session transaction §7.3](../../design/int/session-transaction.md#73-the-watcher-and-reload-path)
  says a callable absent from reloaded source "is not designed here". No
  watcher cell deletes a definition.
- **Mechanism, hypothesis.** The reload publishes over the retained prior
  bindings, and nothing retires a binding that the new generation omits.
  - Not observed: the retained binding at the symbol table.
  - Refuter: `/info user/h` after the reload reports no binding, although the
    call still runs. That would put the stale behaviour in the GOT or in code,
    not in retention.
- **Class.** Not assigned until the reproduction and the mechanism
  observation. No current vocabulary class fits a missing retirement without
  guessing.
- **Relation to the restart boundary.** The P1 packet that designed
  generation-end retirement is withdrawn. REPL §14.8 does not address removal.
  This defect does not depend on a type change, so it stands on its own.

## Next evidence (for `sprint` to schedule)

`test` commits a minimal unignored RED in `tests/repl_watch.rs`:

- a file-backed module defines `g` and `h`;
- an external edit removes `h`;
- after `[updated:]`, `(h)` is refused as unresolved;
- control: `(g)` still returns 1;
- a dependent case: a module that imports `h` reports `[errors:]` rather than
  running.

## Completion

Close when the RED passes after a correction routed through `design`(int),
and `test` has recorded the `// defect:` line with the class assigned here.
