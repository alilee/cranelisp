---
number: 0917
target: /qa
filed_by: /port
filed_at: 2026-07-26
sprint_filed: 118
refers_to: exemplar/CLAUDE.md §"Solve-path never-freed leak — CURRENT STATE";
  tests/exemplar_ownership_residue_s116.rs (cell #21);
  tests/plan/s118-test-plan.md §11.3 (the lead this replaces);
  design/arch/fixmes/0903-s4-1-frame-key-excludes-two-measured-escapee-families.md
status: open
---

# A match arm returning a NULLARY constructor beside a boxed arm strands the whole loop — the real owner of cell #21

## Issue

A function that matches a **let-bound owned heap ADT temporary** and returns a
nullary constructor (`None`) from one arm and a boxed constructor
(`(Some <heap>)`) from another causes the calling tail loop to free **nothing at
all** — not the wrappers, not the payloads, not the COW copies. The nullary arm
does not need to be taken; its mere presence flips the behaviour.

This is the mechanism behind the Sudoku exemplar's per-solve retention (cell
#21, 12,431 warm), and it survives every guard S118 landed for the neighbouring
shapes: `match_owned_temporary_scrutinee_0810` (14/14 GREEN),
`mixed_arm_match_forward_0726` (4/4 GREEN) and the `gen_ownership_flows`
eliminator axis (all GREEN) at HEAD `501e701f`.

## Minimal repro — free-standing, `PreludeVariant::PrimitivesOnly`, zero stdlib

Subject and control differ **only** in the arms' return values. Verified with
`--run --no-cache` and again through `--link` (same numbers, no crash).

```lisp
(platform stdio)

(deftype Item (A [:Int a]) (B [:Int b]))
(deftype Box [:(Vec Item) items])

(defn item-at [bx i] (match bx [(Box items) (vec-get items i)]))
(defn set-item [bx i it] (match bx [(Box items) (Box (vec-set items i it))]))

;; SUBJECT — one arm returns the NULLARY `None`, the other a boxed `(Some …)`.
;; Neither None arm is ever taken at runtime.
(defn step [bx i d]
  (let [it (item-at bx i)]
    (match it
      [(A x) (if (eq-i64 x d) None (Some (set-item bx i (A d))))
       (B x) None])))

;; CONTROL — identical except that no arm returns a nullary constructor.
(defn step-ctl [bx i d]
  (let [it (item-at bx i)]
    (match it
      [(A x) (if (eq-i64 x d) (Some bx) (Some (set-item bx i (A d))))
       (B x) (Some bx)])))

(defn subject-loop [bx n acc]
  (if (eq-i64 n 0) acc
    (match (step bx 0 5)
      [(Some b2) (subject-loop bx (sub-i64 n 1) (add-i64 acc 1)) None acc])))

(defn main [] (Pure (subject-loop (Box [(A 1) (A 2) (A 3)]) 1100 0)))
```

| loop | N | allocs | deallocs | residue |
|---|---:|---:|---:|---:|
| subject | 100 | 406 | **4** | 402 |
| subject | 1100 | 4406 | **4** | 4402 |
| control | 100 | 406 | 406 | **0** |
| control | 1100 | 4406 | 4406 | **0** |

Slope exactly **4 objects/iteration**; deallocs are **constant**, i.e. the loop
performs no deallocation whatsoever after the first four. The control is exact
at both N, so this is a clean subject/control pair for
`tests/helpers/marginal.rs` (or an absolute-balance assertion — the repro needs
no stdlib prelude, so there is no ambient term to subtract).

## How it was isolated (each of these is exact — balanced at N=100 and N=1100)

Measured on the exemplar at HEAD; every neighbouring shape is clean, which is
what makes the nullary arm the discriminator:

- `cell-at` alone (match-destructure of a borrowed product + `vec-get`);
- `set-cell` alone (COW `vec-set` + re-wrap);
- `(Some g)` over a borrowed parameter, under an inline-match caller;
- `(Some (set-cell …))` — fresh heap payload — under an inline-match caller;
- **mixed alias/fresh arms** (`(if flag (Some g) (Some (set-cell …)))`);
- the same body defined in a **different module** from its caller;
- the full `eliminate` shape with all `None` arms replaced by `(Some g)`
  (`e1`/`e2`/`e3`/`e4` variants: let-bound vs inline scrutinee, literal vs
  computed payload — all balanced).

Add one nullary-returning arm to any of the last three and the loop stops
freeing (`y1` — `None` via `if`; `y3` — bare `None` arm: both 5378 allocs /
**898** deallocs at N=1100 versus `y2`, the same program with the nullary arms
replaced, at 5378/5378).

## Why it matters more than its size suggests

At application scale the exemplar retains **12,376 blocks (~1.13 MB RSS) per
solve, exactly linear in solve count with intercept zero** — no per-session
component. The web marquee grows ~1.17 MB per served request (55.3 MB after 1
request → 125.2 MB after 61), every response correct, throughput near-flat.
Nothing surfaces to the user until the process dies. Full tables in
`exemplar/CLAUDE.md`.

## Proposed resolution

1. `/testing` commits the subject/control pair above as a failing-not-ignored
   cell (`// spec: spec/12-runtime.md §12.3.1`), both toggles and the `--link`
   face — the durable trigger this defect currently lacks.
2. `/qa` re-points cell #21
   (`tests/exemplar_ownership_residue_s116.rs::sudoku_warm_serial_solve_residue_at_most_1400`)
   from the 0903 families to this FIXME. Its `// defect:` line and
   `tests/plan/s118-test-plan.md` §11.3's attribution lead were both written
   against `Grid.cells`, which the exemplar never calls — see the `/port`
   evidence appended to FIXME 0903.
3. `/qa` then attributes (backend release-emission vs typecheck ownership
   summary is `/qa`'s call, not `/port`'s). The visible pattern — a result type
   inhabited by both a nullary tag and a boxed constructor, where emission
   appears to take the `NULLARY_TAG_THRESHOLD`-guarded path for the whole
   value — is offered as an observation, not an attribution.

`/port` makes **no exemplar source change**: `(Some g)`/`None`-returning
`eliminate` is the idiomatic and correct spelling of a fallible step, and
rewriting the showcase around the defect would destroy the measurement.
