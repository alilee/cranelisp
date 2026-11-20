---
id: ACT-1101
title: Once a parametric product type is constructed in a session, every later save of the backing file is refused and its definitions are lost at restart
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-20
refers_to:
  - repl/spec/15-session-persistence.md §15.1
  - src/session_v4/lifecycle.rs
  - src/save.rs::generate_types
  - crates/cranelisp-types/src/lifecycle.rs
---

## Origin

`test`, from a discarded demo draft: showing a fully qualified `Pair` before
a later definition produced a persistence warning. `qa` took it in on
2026-11-20.

## Observation

`qa`, 2026-11-20, the debug binary built from `23448d9c`, no prelude, each
session in its own scratch directory, since removed.

| Session | Warning | `user.cl` afterwards |
|---|---|---|
| `(primitives/Pair 1 2)`, `(defn f [] 1)` | `failed to save …/user.cl: no recorded source for (primitives/Pair [primitives/Int primitives/Int] …); the file keeps its previous content` | **Absent.** A new session refuses `(f)` as undefined |
| `(deftype (P2 a b) [:a x :b y])`, `(P2 1 2)`, `(defn f [] 1)` | The same, for `P2` | The `deftype` only; **`f` is missing** |
| `(import [primitives [Pair]])`, `(Pair 1 2)`, `(defn f [] 1)` | The same | The import only |
| A function whose body builds `(Pair 1 2)`, called, then `(defn g [] 2)` | Twice | The import only: **neither function is saved** |
| `(defn f [] 1)`, `(primitives/Pair 1 2)`, `(defn g [] 2)` | Once | `f` only |
| `(primitives/Pair "a" "b")`, `(defn f [] 1)` | The same | Absent |
| Control: `(deftype (Box a) (Mk [:a v]))`, `(Mk 1)`, `(defn f [] 1)` | None | The type and `f` |
| Control: `(primitives/Some 1)`, `(defn f [] 1)` | None | `f` |
| Control: `(primitives/add-i64 1 2)`, `(defn f [] 1)` | None | `f` |

The same warning and the same missing `f` appear with the standard library
prelude.

## Classification: a defect against REPL §15.1, data loss

- [§15.1](../../repl/spec/15-session-persistence.md): the REPL MUST persist
  interactive definitions, and the backing file MUST be regenerated from
  the module's current state after each definition.
- **Severity: data loss.** Every definition entered after the first
  construction of such a type is absent from the file and from the next
  session. The session prints a warning each time and keeps working.
- **Reach.** A product type with type parameters, which includes the
  seeded `Pair`. A parametric type with named constructors does not show
  it.
- **Age: it predates S124.** A debug binary built from the sprint's
  opening commit, `3155f47f` ("Open Sprint 124", 2026-11-16), in a
  throwaway clone since deleted, gives the same result as the current tree
  in all three subjects and both controls: the warning, the missing
  definition, and the controls saved. `sprints/SPRINT.md` names no opening
  commit; `3155f47f` is the commit that opens the sprint. No bisection was
  needed. The refusing check dates from S122 (`63605970`).
- **A second face is filed separately.** After a refused save the next
  session, restoring from cache, ends on signal 11 when the lost
  definition is called:
  [ACT-1102](ACT-1102-refused-save-leaves-the-cache-ahead-of-the-backing-file-intake.md).

## Attribution: the binary's regeneration, `src/save.rs::generate_types`

Read in source at `23448d9c`, with the control above.

- **The refusing step.** `generate_types` selects every entry of the
  module's table for which `Binding::type_def_info()` answers, and reports
  an entry with no authored record as unrendered, which refuses the whole
  save.
- **Why a product type and not the others.** `type_def_info()`
  (`crates/cranelisp-types/src/lifecycle.rs`) answers for a type
  declaration and for a callable whose origin is a constructor carrying a
  type facet. Only a product type's constructor carries one. An instance of
  that constructor at concrete types sits in the entry module's table under
  its instance key, keeps its template's origin, and so is selected as if
  it were a type declaration. It has no authored record.
- **The instance exclusion exists and is not applied here.** The function
  section of the same file skips minted instances through
  `worker::is_internal_listing_entry`. The type section does not.
- **Control.** A parametric type with named constructors differs only in
  that its constructors carry no type facet, and saves.
- **Module: `src/`.** Whether an instance should keep the type facet at all
  is a second question, for `arch` over `cranelisp-types`; either answer
  leaves the type section selecting by a reader that cannot tell a
  declaration from its instance.
- **Not done.** `qa` did not dump the entry; the name in the warning is its
  instance key. **Refuted if** the unrendered entry is reported by another
  section, or the instance's origin carries no type facet.

## Why coverage missed it

Every persistence cell defines functions, enumerated types, traits and
macros. None constructs a value of a parametric product type before a later
definition.

## Routing

- **`qa` holds this action.**
- **`test`:** T-SAVE-PRODUCT, in the
  [S124 evidence delta §14.3](../../tests/plan/s124-evidence-delta.md#143-allocated-to-test).
- **`design`(int), then `dev`(`src/`):** the correction. Whether it is scheduled before S124 closes is the
  user's: it loses user data.

## Completion evidence

T-SAVE-PRODUCT is committed with `// spec: repl/spec/15-session-persistence.md §15.1`,
observed RED on its file and restart clauses, and passes on the corrected
build with its controls unchanged.

## Evidence state (qa, 2026-11-20, full run at `9bc97297`)

T-SAVE-PRODUCT is committed (`65471409`, locus aligned at `9bc97297`) and
accepted: its three subjects fail on all three clauses and its two controls
pass. Its restart is a cold one, with the cache removed, so the cells do
not meet ACT-1102's crash.

