---
id: ACT-1068
title: Regeneration omits every multi-signature function, deleting it from the user's file
status: open
priority: blocking
from: qa
to: qa
sprint: 124
filed_at: 2026-11-17
refers_to:
  - repl/spec/15-session-persistence.md
  - src/save.rs
  - tests/repl_persist.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

Found by `test` while writing the overload leg of T-D7-b, and reduced to
`tests/repl_persist.rs::s124_overload_definition_survives_restart`.
Re-run and extended by `qa` on the debug build at `2c690be5`,
2026-11-17, in scratch directories, no prelude, `(import [primitives [*]])`.

| Leg | Session | Observed |
|---|---|---|
| Subject, entered | `(defn f ([:Int n] n) ([:String s] (str-len s)))`, then `(f 7)` and `(f "ab")` | 7 and 2 in the session. The regenerated `user.cl` holds the `import` and nothing else; a restart reports `undefined variable: f` |
| Subject, entered, by arity | `(defn g ([n] n) ([a b] (add-i64 a b)))`, then `(g 7)` and `(g 1 2)` | 7 and 3. The file holds the `import` only |
| Subject, file-loaded | `user.cl` holds the `import` and the definition of `f`. At the REPL: `(f 7)`, `(defn extra [] 5)` | 7. The rewritten file holds the `import` and `extra`; the definition of `f` is deleted, and a restart reports `undefined variable: f` |
| Subject, another module | `m.cl` holds the definition of `g`; `/mod m`, then `(defn extra [] 5)` | `m.cl` is rewritten without `g` |
| Subject, a caller survives | The family `f`, `(defn direct [v] (vec-len (f v)))`, then the family redefined | The file holds `direct` and no `f`: source that cannot load |
| Control | `(defn f [:Int n] n)`, then `(f 7)` | The file holds the `import` and the definition |

The file-loaded subject behaves the same on the release build of
2026-11-15, so the defect predates the S124 evidence wave.

## Classification: a defect

- **Requirement.** REPL §15.4 rule 1 (round trip) and §15.6.
- **Harm.** The REPL deletes authored source. Any definition entered in a
  session rewrites the module file without its multi-signature functions,
  and the next session cannot resolve their callers.
- **Class:** `enumeration-miss`. The regenerator's function enumeration has
  no row for a multi-signature family.
- **Control.** The pair differs only in the number of signatures.
- **Seam.** The regenerated file is the enumeration's output and was read
  directly. The site is a source reading at `2c690be5`, not an observation:
  `src/save.rs`'s function section skips a `Decl::Overloaded` entry, and it
  skips the family's `$`-named members as internal names that ride their
  owner's form. No generator writes that owner's form.
- **Refuted if** the single-signature control loses its form, or a build
  whose function section writes a multi-signature family still omits one.
- **An instrument that cannot fire.** `section_entry_claimed_or_excluded`
  answers that a `Decl::Overloaded` entry is claimed by a section
  generator. It is the completeness check named for this failure, and it
  passes the omission.

## Why coverage missed it

- No persistence cell holds a multi-signature definition. REPL §15.4 rule 1
  is cited to cells for single-signature functions, types, traits, impls and
  macros.
- REPL §18.3 (multi-signature redefinition) has had no cell since S121.
- The definition-variants lens was applied to persistence by storage model
  and persisted kind, and never by definition form.
  [PLAN](../../tests/plan/PLAN.md#standing-coverage-audit--definition-variants)
  now names that axis.

## Request

1. `sprint`: a scheduling decision for the user. The correction is in no
   S124 row, and the defect loses user data, which the
   [correction-loop stop rule](../METHOD.md#25-mid-sprint-adjustment) does
   not carry by default. The surface is `src/save.rs`, which W7 (ACT-1064)
   and W8 already edit.
2. `design`(int): place the correction, and say whether the completeness
   check is repaired or removed.
3. `test`: the reproduction's remaining legs, in the
   [evidence delta §3.12](../../tests/plan/s124-evidence-delta.md#312-repro-1068--a-multi-signature-function-is-omitted-from-regeneration).

## Completion evidence

REPRO-1068 fails on the missing form in each subject leg, then passes with
its control; `dev`(`src/`) adds a unit row at the function section for a
multi-signature family, RED before the correction.

## Owner (qa, 2026-11-19)

`src/`. The regenerated file is `src/save.rs`'s output and no other module
writes it. The site stays a source reading until `dev`(`src/`) probes it.
