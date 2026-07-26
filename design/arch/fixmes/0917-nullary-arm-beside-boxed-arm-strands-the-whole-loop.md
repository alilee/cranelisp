---
number: 0917
target: /design (backend)
filed_by: /port
filed_at: 2026-07-26
sprint_filed: 118
refers_to: exemplar/CLAUDE.md §"Solve-path never-freed leak — CURRENT STATE";
  tests/exemplar_ownership_residue_s116.rs (cell #21);
  tests/plan/s118-test-plan.md §11.3 (the lead this replaces);
  design/arch/fixmes/0903-s4-1-frame-key-excludes-two-measured-escapee-families.md
status: open
retargeted_by: /design (backend)
retargeted_at: 2026-07-26
ruled_at: design/backend/non-concrete-release-contract.md §6
---

# A match arm returning a NULLARY constructor beside a boxed arm strands the whole loop — the real owner of cell #21

> **RULED S119 Phase 3, `/design`(backend) —
> `design/backend/non-concrete-release-contract.md` §6.** Deliberately kept
> OUT of the five-face release-contract table: every type here is concrete,
> there is no residual anything, and folding it into the class would be the
> framing error `/arch`'s restructuring corrected. It shares the window and
> nothing else.
>
> **Locus correction owed and made:** `protect_return_value` lives at
> `crates/cranelisp-backend/src/compiler/rc_emission.rs:156`, in
> `impl FnCompiler` — **not** `fn_compiler.rs`, where `/qa`'s attribution and
> this file's §refers_to place it; `git log -S` confirms it was never there. Call
> sites: `match_codegen.rs:322,574`, `control_flow/lambda.rs:554`,
> `control_flow/launch.rs:261`.
>
> **Mechanism, read at source.** `Expr::ConstrADT` is synthesised only for
> constructor `Def` bodies, so a user-written bare `None` in an arm is a
> `MonoExpr::Var { resolution: VarRef::Global(None) }`, and `value_provenance`'s
> `Var` arm (`fn_compiler.rs:2508-2511`) returns `NotOwnedHere` unconditionally
> without consulting the ctor probe. `NotOwnedHere` is ⊤ and `join` is `max`, so
> **one nullary arm poisons the whole match's provenance** and the protect fires
> on a fresh boxed arm with nothing to balance it.
>
> **Ruling — one lattice point, no new licence arm** (G2): the conflation is in ⊤
> itself, whose own rustdoc describes two different facts ("a scope binding" and
> "a non-heap scalar — no reference at all"). *Carries no reference* is the
> join's **identity**, not its absorbing element. `ValueProvenance` gains a
> **bottom** point `NoReference` below `Fresh`; a bare nullary constructor
> reference and scalar literals classify there; `is_fresh_construction` becomes
> `<= Fresh` and `yields_owned_temporary` becomes `matches!(p, Fresh |
> OwnedTemporary)`. No emission site gains a branch.
>
> **The pin that must be amended:** `provenance_owned_threshold_is_probe_independent`
> cannot survive as an equality (a nullary-ctor `Var` is only distinguishable
> *with* the probe). It is replaced by the strictly stronger **monotonicity**
> pin — the probe may only move a node **down** the lattice, so the probeless
> gates never over-claim and where they differ they take the leak-safe verdict.
> Equality was a proxy for that property; monotonicity states it directly.
>
> **Byte-identity obligation:** moving scalar literals to `NoReference` must be
> proven emission-neutral against `tests/fixtures/clif_baseline/golden/`; a
> non-identity is a finding, not a re-baseline.
>
> Backend-only, no producer dependency, no cross-crate delta. **Piece 1 of the
> ruling's §7 staging** — the narrow independent one, ordered first per `/arch`'s
> severable-fallback order. Acceptance: this file's repro pair ×2 plus cell #21.

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

## `/qa` attribution (S118 P6 close, probe-verified at HEAD `8f955d54`)

**ACCEPTED and attributed: `cranelisp-backend` — an unbalanced
threshold-guarded protect inc at the match-result return seam.** Full record:
`tests/plan/s118-test-plan.md` §11.8.1. The discriminating probe (CLIF dump of
both variants, numbers reproduced exactly: 4406/4 vs 4406/4406):

- The byte-identical caller (`subject-loop`) compiles differently per callee
  and BOTH compilations are correct for their callee's truthful summary
  (control: pre-call inc of `bx` + exit glue release, `MayAliasOf`; subject:
  neither, `Fresh` result + `Borrowed` param). Both release the returned tree
  exactly once. **Typecheck's summaries are exonerated.**
- Subject's `step` ends with `icmp ult v10, 1024; brif …;
  atomic_rmw.i64 add v10+8` — a `NULLARY_TAG_THRESHOLD`-guarded **protect inc
  on the match result** that nothing balances; the returned `(Some …)` tree
  leaves at rc=2, the caller releases one count, the 4-object tree strands at
  rc=1 per iteration. Control's `step` emits no protect inc at that seam.
- Seam: `fn_compiler.rs::protect_return_value`, licensed by the
  `value_provenance`/`is_fresh_construction` join ("fresh iff EVERY arm is
  fresh"). A **nullary `ConstrADT` arm classifies non-Fresh**, flipping the
  whole match result to protect-eligible; the protect is only balanced when
  the result aliases a scope binding whose scope-exit dec lands on it — never
  true for a fresh boxed arm. The guard's runtime SKIP direction is correct;
  the licensed INC is the leak. Refines the filing's observation: not the
  guarded path "for the whole value" — the guarded inc, unbalanced.
- NOT a 0903 family (all types concrete; no residual signature vars). A
  distinct backend axis; do not fold into the 0903 ruling's shape, though the
  same S119 `/design`(backend) window may carry both.

Ruling asked of `/design`(backend), S119 (narrow): the provenance
classification of a nullary `ConstrADT` (a bare tag mints no box and can
alias nothing — Fresh is the sound point), or equivalently the protect
licence (require a genuinely aliasable arm). `/dev` follows with the fix;
cell #21 and the P6-batch repro pair are the acceptance witnesses.

`/testing` (P6 close batch): land the repro pair (marginal, `--run
--no-cache` + `--link` faces, intended RED) and re-point cell #21's
`// defect:` line here — spec in `s118-test-plan.md` §11.8.6.
