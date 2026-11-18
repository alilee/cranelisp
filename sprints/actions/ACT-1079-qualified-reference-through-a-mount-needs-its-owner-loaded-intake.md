---
id: ACT-1079
title: A qualified reference through an export mount is refused unless the module that declares the mount is already loaded
status: open
priority: required
from: qa
to: qa
sprint: 124
filed_at: 2026-11-18
refers_to:
  - spec/08-modules.md §8.4.4
  - spec/08-modules.md §8.5.4
  - spec/08-modules.md §8.6.6
  - design/int/int.md §6.12
  - design/int/int.md §6.13
  - src/process_form/dependency.rs
  - tests/plan/s124-evidence-delta.md
---

## Observation

`qa`, on the debug build of `7888c515`, 2026-11-18, no prelude, each leg in
a fresh directory. Found while probing `review`'s lead on the mount cycle
walk (below).

```clojure
;; p.cl
(export [(q s) []]) (defn f [] 1)
;; q.cl
(export [(x t) []]) (defn g [] 5)
;; x.cl
(defn y [] 37)
```

| Leg | Entry `main` returns | Entry imports | `--run` |
|---|---|---|---|
| Subject A: owner not loaded | `(p.s/g)` | none | `module 'p.s' referenced by 'p.s/...' not found`, exit 1 |
| Control A | `(p.s/g)` | `(import [p [f]])` | exits 5 |
| Subject B: a mount of a mount | `(p.s.t/y)` | `(import [p [f]])` | `module 'q.t' referenced by 'q.t/...' not found`, exit 1 |
| Control B | `(p.s.t/y)` | `(import [p [f]])` and `(import [q [g]])` | exits 37 |
| Subject C | `(q.t/y)` | `(import [q []])`, which loads nothing | `module 'q.t' … not found`, exit 1 |
| Control C | `(q.t/y)` | `(import [q [g]])` | exits 37 |

- `--link` refuses subjects A and B with the same text and runs control B
  (37).
- At the REPL `(p.s/g)` is refused before `(import [p [f]])` and yields 5
  after it. `(p.s.t/y)` then yields 37 without an import of `q`, because
  the earlier `(p.s/g)` loaded `q` as its target.

## Classification: a defect

- **Requirement.** Spec §8.5.4: a fully-qualified name is self-sufficient,
  and a reference to an unloaded module must not fail merely because no
  `import` preceded it. §8.6.6 rule 2 and its closing paragraph: resolution
  follows the alias chain, restarting on the rewritten path until it
  resolves or no substitution is possible. §8.4.4: a mount is full and
  transparent.
- **Reading relied on.** §8.4.4's worked example says the owner is "a known
  module". `qa` reads §8.5.4's obligation as covering the owner: `p.cl`
  exists, and each control differs from its subject only in load history.
  If `spec` holds that a mount is reachable only through a loaded owner,
  subjects A and C become a question for the user and subject B stands
  (its owner `p` is loaded).
- **Face.** A legal program is refused in every mode, with a diagnostic
  that names a module path the user did not write (`q.t`).
- **Class:** `wrong-reject`.
- **Entered** with export mounts at W7 (`42e6d929`); mounts were refused
  at parse before it.

## Attribution

- **Mechanism: a hypothesis.** Resolution substitutes through the aliases
  of loaded modules only, and loads a module on reference only when the
  whole substituted path names a file. The owner of a pending path (`p` for
  `p.s`, `q` for `q.t`) is never loaded to read its mounts. Not observed at
  its seam; `dev`(`src/`) probes before correcting.
- **Owner:** `src/` (`design`(int) for §6.13, which states that a reference
  through a mount auto-loads its target and is silent on its owner).
- **Refuted if** a control fails, or a subject passes with the owner
  unloaded.
- **Why coverage missed it.** Every mount cell `qa` allocated reaches the
  mount from a module that imports the owner by name. Load history was not
  varied, and no cell mounts a module that itself mounts another.

## The cycle walk (from `review` of `2dec7450`, static)

`prelude_reach_cycle` follows a pending qualifier only when substitution
yields a module file. A substitution that reveals another owner (`p.s.t`
to `q.t`) never visits that owner, so
[int §6.12](../../design/int/int.md#612-the-implicit-prelude-dependency)'s
fixpoint is not reached for a chain of mounts.

- **Not observable through the binary today.** The chained reference is
  refused by the defect above before any cycle is examined. With the
  reviewer's shape (the prelude writes `p.s.t/y`, `x` takes a prelude type)
  the REPL reports `module 'q.t' … not found` against `prelude.cl`: neither
  the cycle nor `x`'s unresolved type.
- **It becomes observable when the resolver is corrected**, as `x`'s
  unresolved-type error standing where spec §8.5.4 item 6 requires the
  cycle.

## Evidence allocation

`test`, in `tests/spec_08_modules.rs`, `// spec: spec/08-modules.md §8.5.4, §8.6.6`,
`// defect: class=wrong-reject locus=src/process_form/dependency.rs found=S124 owner=/dev`:

- **REPRO-1079-a.** Subject A and control A, in `--run`, `--link` and the
  REPL.
- **REPRO-1079-b.** Subject B and control B, the same modes.
- **REPRO-1079-c.** The chained cycle, beside
  `s124_prelude_cycle_through_nameless_export_mount_reports_cycle` and
  reusing its fixture: the prelude imports `p` and writes `p.s.t/y`; `p`
  mounts `q` as `s`; `q` opts out of the prelude and mounts `x` as `t`; `x`
  takes a prelude type. The output names the `x`/prelude cycle. Control:
  the same chain with `x` opting out resolves and `(reach)` yields 37.
  `// spec: spec/08-modules.md §8.5.4 item 6`, `class=enumeration-miss`,
  `locus=src/process_form/dependency.rs::prelude_reach_cycle`.
- Expected on arrival: subjects A and B RED on `not found`; REPRO-1079-c
  RED on `not found`, and its control RED for the same reason. Both of
  REPRO-1079-c's cells turn green only when the resolver and the walk are
  both corrected.

`dev`(`src/`), module rows, each RED before its correction:

- at the resolver: a path whose longest file-backed prefix declares a
  mount for the next segment resolves when that prefix is not yet loaded,
  and through two mounts;
- at `prelude_reach_cycle`: a pending qualifier whose substitution reveals
  a second owner visits that owner, and the walk reports the cycle
  whichever file is visited first. This row is the only evidence of the
  walk until the resolver is corrected, so it lands with the walk's
  correction and not after it.

## Disposition

Found after the first review-and-correct round on `42e6d929`. It refuses a
program and ends none, so [METHOD §2.5](../METHOD.md#25-mid-sprint-adjustment)
carries it to the next sprint unless the user pulls it in. `qa` retains
this intake.

## Completion evidence

REPRO-1079-a and -b fail on the refusal, then pass in every mode with
their controls. REPRO-1079-c reports the cycle and its control yields 37.
Both module rows pass.
