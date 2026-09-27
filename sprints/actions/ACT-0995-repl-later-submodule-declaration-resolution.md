---
id: ACT-0995
title: Settle REPL imports when a later turn declares a same-named child module
status: deferred
priority: required
from: sprint
to: spec
sprint: 122
filed_at: 2026-09-27
refers_to:
  - spec/08-modules.md
  - repl/spec/15-session-persistence.md
  - repl/spec/18-redefinition.md
  - design/int/int.md
  - src/process_form/form_dispatch.rs
---

## Request

The user deferred this question to the next increment on 2026-09-27. It does
not block S122's same-cluster import-resolution correction. Obtain a language
ruling before changing behavior or requirements.

Verified against §8.11.2–§8.11.2.1 of the module specification and §15.4 of
the REPL persistence specification: declared children take precedence over
root modules, and regenerated source must reproduce live-session values.
Neither rule settles an import resolved in an earlier REPL turn before the
child was declared. The current design retains that earlier binding; saved
source places child declarations before imports, so reloading can change it.

Example: root module `q` defines `(defn g [] 99)` and child module `user.q`
defines `(defn g [] 11)`. In module `user`, enter:

```clojure
(import [q [g]])
(defn h [] (g))
(mod q)
```

The retained-binding design leaves `(g)` and `(h)` returning 99 while
`(q/g)` returns 11; reloading the regenerated source makes all three return
11. This is a specification/design conflict, not yet a permanent executable
reproduction.

Present the consequences of rejecting the later declaration, retargeting
future lookups, or retaining per-turn resolutions. Include already compiled
callers and persistence in the decision. Also clarify how to address a
single-segment root module when a same-named child takes precedence. Do not
infer a ruling on conflicting imports from this action.

## Related open question

S122 review L2 and QA intake add a source-read lead, not an accepted carry:
does a child declaration survive a failed REPL turn or removal on reload?
Verified on 2026-09-27: `record_submodule_on_symbol_table` in
`src/process_form/form_dispatch.rs` appends directly to the live table.
The import resolver and enrollment subsequently read that declaration list.
No harmful outcome has been reproduced, and callable/impl atomicity rules do
not settle module-declaration lifetime. Assess this beside the deferred
turn-order question; do not infer a language choice or an extended deferral.

## Completion evidence

Record the user's ruling in the canonical module and REPL requirements.
Coordinate QA evidence and Binary/int design and implementation. Verification
must distinguish live-session calls, already compiled callers and reload of
the persisted source, with an unignored regression for any confirmed defect.
