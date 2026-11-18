# S124 evidence delta

> **Owner:** `qa`. **Readers:** `test`, dispatched against §6's first row;
> `design` and `dev`, for the attributions and module rows; `sprint`,
> sequencing it; `review`, checking delivered evidence against it.
> **Authority:** the [S124 sprint plan](../../sprints/SPRINT.md) scope and the
> user's rulings of 2026-11-16 and 2026-11-17 (S124-Q1 to Q9, with Q7 as
> re-ruled B and its depth-limit and reporting follow-up), recorded in its
> Notes and scribed in the sections below; the
> [API packet](../../sprints/s124-api-packet.md), every row approved;
> [METHOD §2.2](../../sprints/METHOD.md#22-phase-notes);
> `spec/01-lexical.md` §1.4.2; `spec/03-types.md` §3.2.1 and §3.10;
> `spec/04-expressions.md` §4.6; `spec/07-traits.md` §7.3.3; `spec/08-modules.md` §8.3.5, §8.3.11,
> §8.4 and §8.6.4; `spec/09-macros.md` §9.2.1, §9.2.2 and §9.9.1;
> `spec/10-io.md` §10.6, §10.12.1, §10.12.7 and §10.12.9;
> `repl/spec/05-error-presentation.md` §5.1 and §5.5; `repl/spec/14-file-watching.md`
> §14.2; `repl/spec/15-session-persistence.md` §15.4;
> `repl/spec/16-test-discovery.md` §16.1 and §16.6.
> **Checkpoint:** `main` at `4b58ab93` for sections 1 to 13, and `main` at
> `84719eb6` for section 14, the state of the evidence after wave W5.
> **Scope:** sections 1 to 7 are intake, attribution and the reproductions
> that do not depend on the S124 designs. Sections 8 to 13 are the conditions for the S124
> corrections and the Phase 3 readiness judgment. Section 14 is the standing state
> of the evidence: what is accepted, the failing set, what is returned to
> `test`, and what each correction wave still owes.
> **Held:** one cell, for ACT-0985's remaining shape, on a question with
> `spec` (§10). F-PR-3 is not written, by the user's ruling.

Condition identifiers are local to this record. Every observation below was
made by `qa` in scratch directories outside the repository unless a row says
otherwise.

## 1. The opening failing set

`cargo nextest run --no-fail-fast` on the checkpoint: 7,024 run, 6,975
passed, 49 failed, 1 skipped (153 s).

| Tests | Count | Class | Traces to |
|---|---|---|---|
| The filed guards | 44 | Acceptance evidence, intended RED | The set is identical to the S123 close set; `arch` mapped each guard to its filing in the [architecture review](../../sprints/s124-architecture-review.md#71-the-mapping-verified) §7.1. `qa` confirmed the set, not the per-guard mapping. |
| `citation_drift`, all three tests | 3 | Maintenance check | [S124 scope](../../sprints/SPRINT.md#included) item 6, owner `sprint`, wave W0. The converged checker exits 2 with `inventory.root_memory must be AGENTS.md`, so it inspects nothing. Until W0 lands, no claim rests on the document gate. |
| `user_samples`, both tests | 2 | Maintenance check, run-dependent | [ACT-1061](../../sprints/actions/ACT-1061-sh-save-notice-arrives-after-the-next-prompt-intake.md), §5.1. |

- **Stable failing set: 47.** The two `user_samples` tests are run-dependent
  and are named separately, under the
  [counting rule](PLAN.md#traceability-and-authoring). The opening run
  recorded 48 because only one of them failed in it.
- **No genuine regression.** Every failing test traces to an open record
  with an owner.

## 2. ACT-1034 — attribution

**Owner: typecheck. The REPL/batch difference is cluster shape, not mode.**
The filing is [ACT-1034](../../sprints/actions/ACT-1034-parametric-impl-instance-body-polymorphic-callee-intake.md).

### 2.1 Cluster shape decides the outcome

Each cell's definitions were run in six shapes. "Refused" is
`undefined function` naming the template.

| Shape | A1 | A2 | A3 | C3 |
|---|---|---|---|---|
| REPL, one form per turn (the committed REPL leg) | refused | refused | 7 | refused |
| REPL, all definitions in one `(begin …)` | refused | refused | refused | 8 |
| REPL, program loaded as the entry file | refused | refused | refused | 8 |
| `--run`, one file (the committed batch leg) | refused | refused | refused | 8 |
| `--run`, definitions in an imported module | refused | refused | 7 | refused |
| REPL, definitions imported from a module file | refused | refused | 7 | refused |

- Rows with the same cluster structure agree across the REPL and `--run`:
  rows 2, 3 and 4, and rows 5 and 6.
- A3 fails exactly when the cluster that defines `k7` also holds the root
  that demands the instance. With the definitions in one `begin` and the
  call in a later turn it yields 7 (observed at `2c690be5`); with a caller
  or the call itself inside the `begin` it is refused. C3 fails exactly
  when `twice` was published by an earlier cluster.
- This refutes the reading that part of the fault is in how `src/` drives
  instance minting per mode. [Principle 11](../../design/arch/principles/11-single-pipeline-mode-parameters.md)
  is not engaged.

### 2.2 The producer omits the inner instance

Typecheck's per-cluster callable list (`CRANELISP_OWNERSHIP_TRACE=1`,
`--run`) was read for a failing and a passing shape of the same cell.

| Cell and shape | Outcome | Instances typecheck published |
|---|---|---|
| C3, one file | 8 | `Size.size$Opt [(Opt Int)] Int`; `twice` is listed as a concrete function, not an instance |
| C3, imported | refused | `twice [(Opt Int)] Int`; no `Size.size$Opt [(Opt Int)] Int` |
| A3, one file | refused | `Size.size$Opt [(Opt Int)] Int`; no `k7` instance |
| A3, imported | 7 | `Size.size$Opt [(Opt Int)] Int` and `k7 [Int] Int` |
| A1, one file | refused | `Size.size$Opt [(Opt (Opt Int))] Int`; no `[(Opt Int)]` instance |

- The filing's refutation condition, "typecheck publishes a minted-instance
  key for the inner call and the backend misses it", did not occur. The
  backend refuses a slotless template, as its contract requires.
- Two omissions, both in successor discovery inside a minted instance:
  - **Dispatch hop (A1, A2, C3).** A trait-dispatched call whose target is a
    parametric impl template is never demanded from inside a minted
    instance. C3 passes in one cluster only because `twice` settles concrete
    there, so no instance contains the call.
  - **Free-function hop (A3).** A call to a generic free function is not
    demanded from inside a minted impl-method instance when the callee is a
    template of the same cluster.
- **Confidence.** The owner and the two omissions are observed.
  `design`(typecheck) placed both in successor discovery inside a minted
  instance, and T3 (`c1c938c0`) and T4 (`3a2692e3`) correct them there
  ([monomorphisation §3.10](../../design/typecheck/monomorphisation.md#3103-recursion-through-dispatch)).
- **Refuted if** two runs with the same cluster structure differ between the
  REPL and `--run`, or a failing shape's trace lists the inner instance.

### 2.3 Conditions

The four committed cells stay as they are. They confound mode with cluster
shape, so a correction of one publication state could pass them.

| ID | Condition | Wrong implementation it rejects | Now |
|---|---|---|---|
| T-1034-a | A3 yields 7 with its definitions **and the call `(size (Yep 3))`** in one `(begin …)` at the REPL, and with `k7` and the impl in an imported module under `--run` and `--link` | Demand derived only from templates the table already holds | RED in the `begin` leg (`undefined function: k7`), GREEN in the imported leg. Control, green today: the same `begin` without the call, and the call in the next turn |
| T-1034-b | C3 yields 8 with `twice` and the impls in an imported module, in the REPL and under `--run` and `--link` | Demand derived only for same-cluster callers | RED |
| T-1034-c | A1 yields 5 with its definitions in an imported module, in every mode | A correction keyed on the caller's own module | RED |
| T-1034-d | A method that recurses at its own instantiation: `(impl Len (L a) (defn len [l] (match l [LNil 0 (LCons h t) (add-i64 1 (len t))])))` over `(deftype (L a) LNil (LCons [:a h :(L a) t]))` yields 2 for a two-element list, in every mode | A chain that refuses or re-mints its own key | RED: `undefined function: Len.len$p/L`, `--run` and the REPL |
| T-1034-e | A member that calls a sibling at the implementation's instantiation: `describe` as `(add-i64 4 (size o))` in `(impl Cont (Opt a) …)` yields 5 for `(Yep 3)`, in both member orders and with the impl in an imported module | A redirect written for the method's own name only | RED: `undefined function: Cont.size$p/Opt` in each shape. Control, green today: the same two members in an impl for a type with no parameters |

- **File and trace.** `tests/spec_07_traits.rs`, `// spec: spec/07-traits.md §7.3.3`,
  `class=carrier-loss`, locus as the committed cells.
- **Assertion.** The value, and no `undefined function` text, per leg.
- **Completion.** Each RED leg fails with the template's `undefined function`,
  then all legs pass with the committed A1, A2, A3, C3, C1 and C2 cells.
- **`dev`(typecheck)** owes a unit row for each omission at the site `design`
  names.
- **T-1034-d and T-1034-e are the same filing's third face** (2026-11-17).
  The outer instance is published in both. In T-1034-d the inner demand is
  the instance's own key and the site is never redirected to it; in
  T-1034-e the sibling's instance is omitted. The committed cells reach the
  enclosing implementation only at a nested type, so neither shape was
  enumerated.
- **Re-entry at another instantiation is the same filing's fourth face.**
  Under S124-Q7 (re-ruled B) it is an ordinary dispatch, and every direct
  shape is refused today with the same `undefined function`. Its cells are
  T-Q7-a to T-Q7-d (§9.1).

### 2.4 Census consequence

`arch`'s lead holds. All four programs fail before any code is emitted, so
they contribute no reference-count traffic.

- A census zero for the trait-method partition is acceptance evidence only
  when the same run shows non-zero traffic from A1, A2 and T-1034-b passing.
- [CEN-4](#91-type-concreteness-item-1) states this as the census condition.

## 3. Reproductions allocated to `test`

Each is a minimal, permanent, failing-not-ignored cell with a control that
passes today. All land in the S124 evidence wave. Ranked by harm.

| Rank | ID | One line | Filing | Correction |
|---|---|---|---|---|
| 1 | REPRO-1068 | Regeneration omits every multi-signature function, deleting it from the user's file | ACT-1068 | Not scheduled: `sprint` |
| 1 | REPRO-1064 | Regeneration deletes one of two impls for same-named types; the next session crashes | ACT-1064 | S124, row D10 |
| 2 | REPRO-1066 | A direct `quote-sexp` call on a scalar-payload `Sexp` aborted the debug build | ACT-1066, closed | Corrected by row D5 (backend B1); the cells stay as a fence |
| 2 | REPRO-1063-p | A partial application of `bind` aborts the process in every mode | ACT-1063 | S124, backend row B12 |
| 2 | REPRO-1065 | A user function named `bind` is replaced by the primitive, and a local named like a platform function is scheduled as that effect: a silent wrong value and an abort | ACT-1065 | S124, with ACT-1050 |
| 3 | REPRO-1005-a | Redefining one member of a multi-definition form regenerates a file that restarts locked | ACT-1005 | Carried past S124 |
| 4 | REPRO-0977 | Strands launched by a losing `race` or `select` branch run to completion | ACT-0977 | Carried |
| 5 | REPRO-R1 | Malformed `defmacro` shapes are accepted | ACT-1057 | S124 |
| 6 | REPRO-R3 | `+*1` is read as a symbol and an integer | ACT-1059 | S124 |
| 7 | T-R2-a, T-R2-b, T-R2-c | Second member glob dropped; renamed function import and renamed export rejected | ACT-1056, ACT-0997 | S124, row D3 |
| 8 | REPRO-1061 | A `/sh` save that delivers no notification is never reported | ACT-1061 | S124 |
| 9 | REPRO-0981 | A multi-signature body's independent effects are not scheduled together | ACT-0981 | Carried |
| 10 | REPRO-1063 | A host-promised primitive used as a value is refused at codegen | ACT-1063 | S124, backend row B12 |
| 11 | REPRO-1005-b, REPRO-1005-c | Regeneration reorders definitions and structural forms | ACT-1005 | Carried |
| 12 | REPRO-0915-loc | Two required batch refusals are located at `1:1` and `0..0` | ACT-1036 | S124 |
| 13 | REPRO-1067 | An expression nested about 56 forms deep aborts the compiler | ACT-1067 | Not scheduled: `sprint` |

The carries are the user's 2026-11-16 ruling. REPRO-1062 (§9.1) is
memory-unsafe and lands before any of these. The three rows at rank 2 end in
a process abort or a wrong value and follow REPRO-1064 in the order listed.

### 3.1 REPRO-0977 — launched work outlives its cancelled branch

- **Requirement.** Spec §10.12.7 item 5 and §10.12.9: a detached strand is
  cancelled when the cancellation context it was launched in is cancelled.
- **Harm.** A cancelled request's launched work keeps producing effects and
  holding its permits.
- **Fixture** (platform `poll-pool`, `--run`). `fan` launches `n` logged
  400 ms effects on distinct tokens in the accept-loop shape, then awaits `d`
  ms and yields `d + v`. `other` awaits `d` ms and yields `d + v`. `tail`
  awaits 900 ms and returns its argument, so the process outlives the
  strands.

  ```clojure
  (defn fan [n d v]
    (if (eq-i64 n 0)
        (bind (poll-read 99 1 d) (fn [x] (Pure (add-i64 x v))))
        (let [m (sub-i64 n 1)]
          (bind (poll-log n 1 400 "L") (fn [r] (fan m d v))))))
  (defn other [d v] (bind (poll-read 98 1 d) (fn [x] (Pure (add-i64 x v)))))
  (defn tail [r] (bind (poll-read 97 1 900) (fn [q] (Pure (add-i64 r (sub-i64 q q))))))
  ```

| Leg | Program | Required | Observed |
|---|---|---|---|
| Subject | `(bind (race (fan 3 3000 3) (other 50 4)) tail)` | exit 54, stdout empty | exit 54, stdout `LLL` |
| Subject, `select` | the same with `(select [… …])` | exit 54, stdout empty | exit 54, stdout `LLL` |
| Control: launcher wins | `(bind (race (fan 3 50 3) (other 3000 4)) tail)` | exit 53, stdout `LLL` | as required |
| Control: the strands are launched | `(race (fan 3 50 3) (other 200 4))` | exit 53 | 53; an awaited `fan` would take 1,250 ms and lose |
| Control: an inline effect is cancelled | `(race (bind (poll-log 7 1 400 "D") (fn [x] (Pure (add-i64 x 3)))) (other 50 4))` | exit 54, stdout empty | as required |

- **Wrong implementations rejected.** Strands owned by the drive and never
  by the branch (the subject); cancelling every strand when any branch ends
  (the winning control); no drain at exit (the winning control).
- **Fixture properties that matter.** The branch tails use their results. A
  discarded result makes that effect a launch, and the branch then completes
  at once. `tail` separates cancellation from a process exit that abandons
  the strands: without it the subject still prints `LLL`, during the exit
  drain.
- **Assertion.** Exit code and exact stdout. No wall-clock assertion.
- **File and trace.** `tests/concurrency_cancellation.rs`,
  `// spec: spec/10-io.md §10.12.7`, `class=cancellation-scope-escape`,
  `locus=crates/cranelisp-intrinsics launched-strand supervision`, `found=S124`,
  `owner=/dev`. The locus is provisional: the mechanism is ACT-0977's source
  reading.
- **Limit.** `timeout` and a nested combinator were not probed with launched
  strands. `test` adds a `timeout` leg if it is constructible with the same
  fixture; nesting waits for the realization's design.

### 3.2 REPRO-0981 — multi-signature bodies are not scheduled

- **Requirement.** Spec §10.12.1: the compiler MUST insert `Par` nodes for
  commutative, data-independent pairs. §10.12.5 leaves execution free, so
  the observation is a twin, not an absolute time.
- **Fixture** (`poll-pool`, `--run`). `B` is two 300 ms `poll-read`s on
  tokens 1 and 2 whose results are both used; `BD` makes the second depend
  on the first.

| Leg | Definition | Observed (best of 3) |
|---|---|---|
| Twin 1 | `(defn f [d] B)` | 313 ms |
| Twin 2, subject | `(defn f ([d] B) ([d e] (Pure e)))` | 617 ms |
| Serial control | either form with `BD` | 615 to 617 ms |

- **Assertion.** Twin 2's regime equals twin 1's: both below the serial
  control by a structural margin, taking the minimum of several attempts for
  each upper bound, under the [wall-clock rule](PLAN.md#traceability-and-authoring).
  Values are equal on every attempt.
- **Wrong implementation rejected.** A scheduling pass that enumerates
  single-signature definitions only.
- **Variants.** The chain in the two-parameter clause is serial too (619 ms).
  A single-signature impl method overlaps (315 ms). Spec §7.3's grammar
  gives a method one parameter vector and one body, so there is no
  multi-signature impl-method twin.
- **File and trace.** `tests/spec_10_io.rs`, `// spec: spec/10-io.md §10.12.1`,
  `class=enumeration-miss`, `locus=src/bind_chain_analysis.rs::auto_schedule_defn`
  (its caller's multi-signature guard), `found=S124`, `owner=/dev`.
- **Authority.** Acceptance evidence for §10.12.1 in this implementation,
  which runs `Par` branches concurrently. It does not constrain an
  implementation that runs them serially.

### 3.3 ACT-1005 — regeneration

Every leg enters forms at the REPL, ends the session, and reads the
regenerated `user.cl`. No prelude; names come from one
`(import [primitives [add-i64 Pure Int]])`.

**REPRO-1005-a — a shared record keeps a superseded member.**
Requirement: REPL §15.4 rule 1 (round trip) and §15.6.

| Leg | Session | Required | Observed |
|---|---|---|---|
| Subject | `(begin (defn f [] 1) (defn g [] 10))`, `(defn g [] 20)` | restart: `(f)` is 1, `(g)` is 20 | file holds the `begin` and `(defn g [] 20)`; restart is locked with `illegal redefinition of g in one compilation cluster` |
| Subject, macro | `(defmacro mk2 [a b] …)` expanding to two `defn`s, `(mk2 f g)`, `(defn g [] 20)` | the same | the same lock |
| Control | the `begin` with no redefinition | 1 and 10 | as required |
| Control | plain `(defn f …)`, `(defn g …)`, `(defn g [] 20)` | 1 and 20 | as required |
| Control | the `begin`, then both members redefined | 2 and 20 | as required |

- **Harm.** The user's next session opens locked on a file the REPL wrote.
- **Wrong implementations rejected.** Keeping a multi-definition record
  whole while any member survives (the subject); dropping the record when
  one member is redefined, which would lose `f`.
- **Assertion.** The restart's two values, and no `[errors:` line.
- **File and trace.** `tests/repl_persist.rs`,
  `// spec: repl/spec/15-session-persistence.md §15.4`,
  `class=partial-record-update`, `locus=src/save.rs` regeneration of a
  multi-definition record, `found=S124`, `owner=/dev`.

**REPRO-1005-b — rule 2, authorship order.** Entering `(defn z [] 1)`,
`(defn y [] 2)`, `(defn x [] 3)` must regenerate `z`, `y`, `x`; the file
holds `x`, `y`, `z`. A second leg enters a function, a type, a function, a
macro and a function, and must keep that order; the file groups type,
macro, functions.

**REPRO-1005-c — rule 4, structural order.** Entering `import`, a `defn`,
`export`, `(mod sub)`, `import` must regenerate `mod`, `export`, `import`;
the file holds `mod`, `import`, `export`, with the two imports merged into
one form.

- **Assertion for b and c.** The order of the named forms in the file.
  Restart values are a control: they are correct today.
- **Trace.** `class=authored-order-loss`, `locus=src/save.rs::generate_module_source`.
- **Limit of b.** A leg in which a redefinition keeps its position is green
  today only because the names sort that way; `test` makes that leg use
  names whose entry order is not alphabetical.

**F-1005-d — rule 2's macro exception (S124-Q5).** A redefined function
moves after a macro it newly depends on when that macro follows its original
position.

| Leg | Session | Required | Observed |
|---|---|---|---|
| Subject | `(defn f [] 1)`, `(defmacro m [] (quote 41))`, `(defn f [] (add-i64 (m) 1))` | `m` precedes `f` in the file; restart: `(f)` is 42 | as required |
| Control | the same, with the redefinition `(defn f [] 2)` | `f` precedes `m` | `m` precedes `f`: RED with REPRO-1005-b |

- **Class.** Safety fence for the carried ACT-1005 correction; it passes on
  arrival because the regenerator groups macros first. The control joins
  REPRO-1005-b's RED legs.
- **Wrong implementations rejected.** Authorship order restored with no
  exception (the subject then restarts with an unavailable macro); moving
  every redefined function to the end (the control).
- **File and trace.** `tests/repl_persist.rs`,
  `// spec: repl/spec/15-session-persistence.md §15.4`. No `// defect:` line
  on the subject.

**Not a defect: a definition expanded before a macro's redefinition.** It is
3 in the session and 21 after restart. REPL §15.4's template qualification
states that a persisted macro call is re-expanded with the macro current at
restart. No cell.

### 3.4 REPRO-0915-loc — batch refusals located at `0..0`

- **Requirement.** REPL §5.5, first bullet.
- **Fixture.** The subject form is on line 3 of the entry file; `--run` and
  `--link`.

| Leg | Line 3 | Required | Observed |
|---|---|---|---|
| Subject | `(defn main [x] (primitives/Pure x))` | located on line 3, no `0..0` | `p.cl:1:1: error: codegen error at 0..0: main must be a zero-argument function …` |
| Subject | a `main` that calls `(primitives/discover-tests [])` | located on line 3, no `0..0` | `p.cl:1:1: error: codegen error at 0..0: … references discover-tests …` |
| Subject, macro-produced | `(mk main)`, with `(defmacro mk [n] …)` on line 2 expanding to `(defn ~n [x] (primitives/Pure x))` and the call on line 4 | located on line 4, the written call; no `0..0` | `p.cl:1:1: error: codegen error at 0..0: main must be a zero-argument function …` |
| Subject, not a function | `(defmacro main [] (quote 7))` | located on line 3, no `0..0` | `p.cl:1:1: error: codegen error at 0..0: 'main' in entry module is not a function definition` |
| Control | the committed `batch_main_non_io_return_refusal_is_located_at_main` | — | already RED for the non-`IO` arm |

- **Assertion.** The refusal text is unchanged; the location names the
  subject form's line.
- **What the two added legs reject.** A location read from the
  declaration's own span, which is synthetic for a definition a macro
  produced and absent for a macro; the macro-produced leg puts the
  `defmacro` and its call on different lines, so the template's line is a
  third wrong answer. Authority: REPL §5.5 and
  [io-integration §1](../../design/int/io-integration.md#1-running-a-program).
- **An overloaded `main`** is refused by spec §10.6 (S124-Q9): T-Q9-b,
  §9.6.
- **File and trace.** `tests/spec_10_io.rs` for the arity arm,
  `tests/test_runner.rs` for the `discover-tests` refusal; `class` and
  `locus` as the committed ACT-1036 cell, with
  `locus=src/exe.rs::refuse_dev_session_externs` for the second.
- **What this does not cover.** FIXME 0915's doubled prefix and mangled
  subject: §4.4.

### 3.5 Frontend audit R1, R2, R3

All three are source traces in the audit; each is now executed. No prelude,
`--run`, `(defn main [] (primitives/Pure 0))` unless a leg says otherwise.

**REPRO-R1 — `defmacro` shapes (spec §9.2.1, §9.2.2).**

| Leg | Form | Required | Observed |
|---|---|---|---|
| Subject | `(defmacro m [] (quote 7) (quote 9))`, with `main` returning `(m)` | rejected at the `defmacro` | exit 7 |
| Subject | `(defmacro m [&r x] (quote 1))`, and `[& r x]` | rejected | exit 0 |
| Subject | `(defmacro m [&r &s] (quote 1))` | rejected | exit 0 |
| Subject | `[[&r x]]` and `[[&r &s]]` | rejected | exit 0 |
| Control | `(defmacro m ([] (quote 1) 2))` | rejected | `defmacro clause requires params and body` |
| Control | `[x &]` | rejected | `expected name after '&'` |
| Control (S124-Q2) | `(defmacro m [& [a b]] (quote 7))` | rejected, located at the `&` | `1:14: … expected name after '&'` |
| Control (S124-Q2) | `(defmacro m [[a b] & r] (quote 7))`, called as `(m [1 2])` | accepted | exit 7 |
| Control | `[x &r]`, `[[x &r]]`, `(defmacro m [] (quote 1))` | accepted | exit 0 |

- **Assertion.** Non-zero exit and a diagnostic naming the macro form's
  line; substring match.
- **Wrong implementation rejected.** A correction of the outer parameter
  list alone (the bracket legs), or of parameters alone (the trailing-form
  leg).
- **File and trace.** `tests/spec_09_macros.rs`, `// spec: spec/09-macros.md §9.2.1`
  or `§9.2.2`, `class=silent-accept`,
  `locus=crates/cranelisp-frontend/src/defmacro.rs`, `found=S124`, `owner=/dev`.
- **`dev`(frontend)** owes parser unit rows for each shape.

**T-Q3 — a return mismatch names the offending clause body (spec §9.9.1,
S124-Q3).** The fixture puts each clause body on its own line.

```clojure
(defmacro m
  ([] (quote 7))
  ([x]
     42)
  ([x y] (quote 9)))
```

| Leg | Required | Observed |
|---|---|---|
| Subject | the mismatch is located at line 4, the `42` | `7:1 … at 1000018..1000017`, a synthetic span on the line after the form |
| Subject, shorthand | `(defmacro n [x]` with the body `42` on line 2: located at line 2 | `4:1`, after the form |
| Control | every body `(quote …)` | accepted |

- **Wrong implementations rejected.** The `defmacro` opener's line (the
  ruling's rejected candidate); the first clause's body; any location inside
  the form, which the committed
  `macro_return_mismatch_located_at_definition_neg` accepts.
- **Assertion.** The diagnostic's line, and no line outside the form.
  `test` tightens the committed cell to the body's line in the same change.
- **File and trace.** `tests/spec_09_macros.rs`,
  `// spec: spec/09-macros.md §9.9.1`, `class` and `locus` as the committed
  ACT-1057 cell.

**R2 — module entry grammar (spec §8.3.5, §8.3.11, §8.4).** The audit's
three cases are already RED: ten committed cells under ACT-1056, ACT-0997
and ACT-1055. Three variants reach losses those cells do not.

| ID | Entry | Required | Observed |
|---|---|---|---|
| T-R2-a | `(import [mathx [Shade.* Hue.*]])`, using a constructor of each | both bound | `undefined variable: Dark` |
| T-R2-b | `(import [mathx [(square sq)]])`, then `(sq 7)` | 49 | `expected symbol for import name, got (square sq)` |
| T-R2-c | `(export [mathx [(square sq)]])` in `api`, imported as `sq` | 49 | the same message, raised for the export |
| Control | `(import [mathx [square]])`; `(export [mathx [square]])` | 49 | 49 |

- T-R2-c is the equivalence twin of T-R2-b: row D3 gives imports and
  exports one entry type, and spec §8.4.5 defines the renamed re-export.
- **File and trace.** `tests/spec_08_modules.rs`, `class=wrong-reject`, loci
  as the neighbouring cells.

**REPRO-R3 — operator run followed by a digit (spec §1.4.2).**

| Leg | `main` returns | Required | Observed |
|---|---|---|---|
| Subject | `(let [+* 5] (primitives/add-i64 +*1))` | the reader error | exit 6 |
| Subject | the same with `-*` | the reader error | exit 6 |
| Subject | the same with `->` | the reader error | exit 6 |
| Control | the same with `**` | the reader error | `operator symbol must not be immediately followed by a digit` |
| Control | `(let [+* 5] (primitives/add-i64 +* 1))` | 6 | exit 6 |
| Control | `(primitives/add-i64 +1 -1)` | 0 | exit 0 |

- **Why this fixture.** Binding the operator name makes the malformed token
  evaluate, so the acceptance is observed as a value, not inferred from a
  downstream error.
- **File and trace.** No e2e file owns chapter 1 yet; `test` opens
  `tests/spec_01_lexical.rs` for it. `// spec: spec/01-lexical.md §1.4.2`, `class=silent-accept`,
  `locus=crates/cranelisp-frontend/src/reader.rs::read_plus_or_operator`
  (and `read_minus_or_number`), `found=S124`, `owner=/dev`.

### 3.6 REPRO-1061 — a `/sh` save reported without its notification

- **Requirement.** REPL §14.2 (S124-Q6): a watched save completed by a
  turn's own `/sh` is rebuilt and reported before that turn's next prompt,
  regardless of notification delivery.
- **Harm.** The user's next evaluation runs against a definition the REPL
  has not said it rebuilt; in the subject below it runs against the old one.
- **Technique.** The watcher watches a file's directory. A module file that
  is a hard link can be rewritten through its other name in an unwatched
  directory, so the save delivers no notification. This withholds the
  notification deterministically; the cell makes no claim about hard links.
- **Fixture** (REPL, no prelude). `real/math.cl` defines `sq` as a square;
  `math.cl` is a hard link to it; `user.cl` imports `sq` and defines
  `(defn f [] (sq 3))`.

| Leg | Session | Required | Observed |
|---|---|---|---|
| Subject | `(f)`; `/sh` rewrites `real/math.cl` so that `sq` doubles; `(f)` | `[updated: math.cl]` and `[updated: user.cl]` after the `/sh` line and before the next prompt; then 6 | no notice in any later turn; `(f)` is 9, 3 of 3 |
| Control | the same `/sh` writes `math.cl` | the same | as required |
| Control | the `/sh` command writes nothing | no notice; 9 | not run by `qa` |

- **Wrong implementations rejected.** A settle wait after `/sh` (nothing
  ever arrives in the subject); a comparison that reports an unchanged file
  (the second control); a report with no rebuild (the value).
- **Assertion.** The notices' position relative to the prompts, and the
  value. No sleep in any leg.
- **Conditions.**

| ID | Condition | Class, tier |
|---|---|---|
| T-1061 | The table above | A, e2e |
| M-1061 | With the notification withheld, an armed poll reports a recorded file changed on disk and an unarmed poll does not; a later event for the same save reports nothing ([REPL lifecycle §1.2](../../design/int/repl-lifecycle.md#12-poll-and-reload)) | A, module, `dev`(`src/`) |
| O-1061 | 40 loaded runs of the `user_samples` reload transcript on the corrected build, against the recorded 1 late in 12 | O, measurement, `qa` |

- **File and trace.** `tests/repl_watch.rs`,
  `// spec: repl/spec/14-file-watching.md §14.2`,
  `locus=src/watch.rs::poll_changes` (the post-turn poll's candidate set),
  `class=notification-only-detection`, `found=S124`, `owner=/dev`.
- **Limit.** T-1061 does not exercise the delivery race itself. O-1061
  measures it, and both `user_samples` tests passing in G-0's run is its
  suite face.

### 3.7 REPRO-1064 — same-named type impls collapse at regeneration

Observations and attribution: [ACT-1064](../../sprints/actions/ACT-1064-same-named-type-impls-collapse-at-regeneration-intake.md).

- **Requirement.** REPL §15.4 rule 1.
- **Fixture.** Modules `a` and `b` each define `Box` with one `Int` field
  and `(defn mk [] …)`. The entry imports both with empty name lists and
  declares `(deftrait Sz (sz [x] Int))`.

| Leg | Session | Required | Observed |
|---|---|---|---|
| Subject, entered | `(impl Sz a/Box (defn sz [_] 1))`, `(impl Sz b/Box (defn sz [_] 20))`; end the session; restart | the file holds both forms; `(sz (a/mk))` is 1 and `(sz (b/mk))` is 20 | the file holds the `b/Box` form only; restart ends in SIGSEGV on `(sz (a/mk))` |
| Subject, file-loaded | the entry file holds both forms; `(defn extra [] 5)` at the REPL | the file holds both forms | the `a/Box` form is deleted |
| Control | `b`'s type is `Crate` | as the first subject | as required |
| Control | the file-loaded entry under `--run`, `main` summing both | exit 21 | exit 21 |

- **Wrong implementations rejected.** A set keyed by the bare `Trait.Type`
  label; a correction that keeps both forms and exchanges their bodies (the
  two values are asserted separately, never as a sum).
- **Assertion.** Both `impl` forms in the file, the two restart values, and
  no signal.
- **File and trace.** `tests/repl_persist.rs`,
  `// spec: repl/spec/15-session-persistence.md §15.4`,
  `class=artifact-underkey`, `locus=src/save.rs` impl enumeration key,
  `found=S124`, `owner=/dev`.
- **Limit.** The restart crash is asserted only as "no signal". Its
  mechanism is a hypothesis (ACT-1064).

### 3.8 REPRO-1065 — the bind-chain pass identifies callees by spelling

Observations and attribution: [ACT-1065](../../sprints/actions/ACT-1065-user-function-named-bind-rewritten-as-the-primitive-intake.md).
The correction is [bind-chain analysis §3.1](../../design/int/bind-chain-analysis.md#31-pattern-recognition),
in ACT-1050's change-set. No leg of a to c imports the primitive `bind`.

| ID | Subject | Required | Observed | Controls (pass today) |
|---|---|---|---|---|
| REPRO-1065-a | A user `bind` that adds 100 to each result, over two independent `poll-read`s (`poll-pool`, `--run`) | exit 207 | exit 7 | the function spelled `then`: 207 |
| REPRO-1065-b | `(defn bind [a f] (f (add-i64 a 100)))`, `(bind 5 (fn [x] (add-i64 x 1)))`, every mode | 106 | `undefined function: bind` | spelled `then`; the lambda bound by `let` first; a three-parameter `bind` |
| REPRO-1065-c | The same function in module `m`, called as `m/bind` | 106 | `undefined function: m/bind` | `m/then` |
| T-1065-d | After row D3: the primitive imported as `(bind then)`, over REPRO-0981's independent pair | the regime of the unrenamed twin | not constructible until D3; `test` reports | the unrenamed twin |
| REPRO-1065-e | A parameter named `poll-read`, bound to a user function whose body is a two-step chain, called twice in an independent chain (`poll-pool`, `--run`; fixture below) | exit 0 | abort: `cranelisp_run_io: unknown IO tag 4` | the parameter spelled `rd`: exit 0 |
| T-1065-f | `m` defines the user `bind` of REPRO-1065-b; the entry imports it by name; a `prelude.cl` re-exports the primitive `bind`; one file, `--run`, `--link` and the REPL | 106 | `undefined function: bind`, before and after ACT-1065's correction: the face is [ACT-1075](../../sprints/actions/ACT-1075-polymorphic-candidate-selected-from-a-shared-spelling-is-undefined-at-codegen-intake.md)'s | none that isolates the pass: `then` in all three places also removes the second candidate |

```clojure
(defn slow [t c d]
  (bind (poll-read t c d) (fn [x] (bind (poll-read t c d) (fn [y] (Pure (add-i64 x y)))))))
(defn go [poll-read]
  (bind (poll-read 1 1 150) (fn [a] (bind (poll-read 2 1 150)
    (fn [b] (Pure (sub-i64 (add-i64 a b) 600)))))))
(defn main [] (go slow))
```

- **REPRO-1065-e is a second recogniser with the same fault.** The pass
  reads a platform effect's scheduling class from the callee's spelling, so
  the two calls of the parameter are grouped as a parallel pair. The abort
  is the panic F-0975 (§4.1) names for a grouped step that is not a direct
  effect leaf; the IO node kind behind tag 4 was not read. The control differs only in the
  parameter's spelling and runs serially (629 ms).
  - A `let`-bound lambda named `poll-read` that returns `Pure` yields the
    right value (207) with or without the spelling: no face, no cell.
  - Trace: `class=routing-misclassify`,
    `locus=src/bind_chain_analysis.rs::effect_descriptor`. <!-- doc-check: literal reason="Defect locus as it stood before 32e434dc" -->
- **T-1065-f is the falsifier of the design's import assertion**: a
  cluster's imports are committed before its bodies are analysed, so an
  imported user `bind` is never answered by the prelude's primitive. It
  cannot execute that clause yet: its program is refused by ACT-1075 with
  the pass disabled and with any spelling. Until ACT-1075 is corrected the
  assertion rests on `dev`'s module row
  `ambiguous_bind_is_not_the_primitive`.
- **Not allocated: a cycle peer that defines `bind`.** No legal program
  reaches the state the design names. Spec §8.10.2 refuses every import
  cycle, and both shapes tried (two modules importing each other; a parent
  importing from a child that imports `super`) are refused with
  `circular dependency detected` before any body is analysed, with `bind`
  and with `then`. The claim returns to `design`(int) (§6).
- **Wrong implementations rejected.** Recognition by spelling (a to c, f);
  recognition by the spelling `bind` after resolving imports only for the
  bare form (c); a correction that stops rewriting anything named
  otherwise (d); a correction of the `bind` recogniser that leaves the
  platform lookup on the spelling (e).
- **Assertion.** The value, and no `undefined function` text; for e, exit 0
  and no `unknown IO tag`. T-1065-d follows the
  [wall-clock rule](PLAN.md#traceability-and-authoring).
- **File and trace.** `tests/spec_10_io.rs`,
  `// spec: spec/04-expressions.md §4.6` (d: `spec/10-io.md §10.12.1`),
  `class=routing-misclassify`,
  `locus=src/bind_chain_analysis.rs::is_bind_var`, `found=S124`, `owner=/dev`. <!-- doc-check: literal reason="Defect locus as it stood before 32e434dc" -->
- **`dev`(`src/`)** owes the C8 module rows of
  [bind-chain analysis §7](../../design/int/bind-chain-analysis.md#7-open-obligations),
  including a local named like a platform function.

### 3.9 REPRO-1063 — a host-promised primitive as a value

Observations and attribution: [ACT-1063](../../sprints/actions/ACT-1063-bind-as-a-value-refused-at-codegen-intake.md).
The correction is [compile-to-module §12.1](../../design/backend/compile-to-module.md#121-host-promised-primitives-as-values-act-1063-s124),
backend row B12. No prelude, `(import [primitives [*]])`.

**REPRO-1063 — the value use.** Each leg binds the primitive with `let` and
calls it; "refused" is `fn-as-value wrapper for '<name>' reached codegen with
no GOT-slot carrier`.

| Leg | Primitive | Required | Observed |
|---|---|---|---|
| Subject | `bind`, also passed to `(defn ap [f] …)` | exit 5 | refused |
| Subject | `race` | exit 5 | refused |
| Subject | `select`, by `let` and through `ap` | exit 5 | refused |
| Subject | `sleep` | exit 5 | refused |
| Subject | `nanos` and `name`, applied to `(trace (add-i64 1 2))` | the direct call's value | refused |
| Subject, REPL | `discover-tests` | `:primitives/Int 0` for `(vec-len (d []))` | refused |
| Subject, REPL | `sconcat` (`macros`) | `SList.SNil` for two `SNil` | refused |
| Control | `add-i64`, `str-len` (slot-carrying) | exit 5 | exit 5 |
| Control | `vec-len` (inline, no slot, has a wrapper rule) | exit 5 | exit 5 |
| Control | each subject's direct call | its value | its value |

**REPRO-1063-p — the partial application.**

| Leg | `main` body | Required | Observed |
|---|---|---|---|
| Subject | `(let [k (bind (Pure 5))] (k (fn [v] (Pure v))))` | exit 5 | abort, `misaligned pointer dereference` in `heap_access.rs`; `--run`, the REPL and the linked executable, 3 of 3 |
| Subject | the same through `(defn ap [k] …)`, and with a `Vec` payload | exit 5 | the same abort |
| Subject | `(let [k (race (Pure 5))] (k (Pure 5)))` | exit 5 | the compile worker panics: `can't resolve symbol race`; `--link` the same |
| Control | `(let [k (add-i64 2)] (Pure (k 3)))` | exit 5 | exit 5 |
| Control | `(defn then [io f] (bind io f))`, partially applied | exit 5 | exit 5 |
| Control, REPL | `(let [c (sconcat SNil)] (c SNil))` | `SList.SNil` | as required |

- **Harm.** A legal program is refused with a compiler-internal message; a
  partial `bind` compiles, links and dereferences a wild pointer.
- **Wrong implementations rejected.** A rule for the four IO combinators
  only (the accessor, `sconcat` and `discover-tests` legs); a rule for the
  fn-as-value wrapper that leaves the curry wrapper's by-name import (the
  partial legs); a wrapper-private copy of a lowering whose result disposer
  differs from the direct call's (the balance twin below).
- **Assertion.** The value in every mode, no `GOT-slot carrier` text and no
  signal.
- **T-1063-b — the falsifier `design`(backend) proposed, at the solution
  tier.** For `bind`, `race` and `select`, the value use and the direct
  call of one program with a heap payload (`(Pure [1 2 3])`, result
  measured with `vec-len`) return the same value, and allocations equal
  frees in both under the armed check. A wrapper that builds a node with
  another disposer leaks or stops the armed check. Class A; not
  constructible until B12, since the subject is refused today. That the
  emitted node is identical in tag and fields is a module observation:
  M-1063.
- **`dev`(backend)** owes M-1063: for each IO combinator, the node a
  wrapper emits equals the direct application's in tag, fields and
  disposer, with the wrapper holding no copy of the lowering.
- **File and trace.** `tests/spec_10_io.rs`, `// spec: spec/03-types.md §3.2.1`,
  `class=carrier-loss`,
  `locus=crates/cranelisp-backend fn-as-value and auto-curry wrapper call rules`,
  `found=S124`, `owner=/dev`. The `discover-tests` leg goes to
  `tests/test_runner.rs` and is REPL-only (REPL §16.1).
- **Limit.** `quote-sexp` is slot-carrying and works as a value; its
  direct call is §3.10's subject.

### 3.10 REPRO-1066 — a direct `quote-sexp` call aborted the debug build

**Corrected by B1; the seven cells are a standing fence.** No prelude;
`primitives` and `macros` imported whole. `k` matches `(SexpList xs)` to 5.

| Leg | `main` returns | Required |
|---|---|---|
| Subject | `(Pure (k (quote-sexp (SexpInt 3))))`, every mode | exit 5 |
| Subject, REPL | `(quote-sexp X)` for `X` in `(SexpInt 3)`, `(SexpInt 3000)`, `(SexpBool true)`, `(SexpFloat 1.5)`; and `(SexpInt 3)` bound by `let` first | the quoted form displayed |
| Control | `(quote-sexp (SexpStr "abc"))`; `(let [q quote-sexp] (Pure (k (q (SexpInt 3)))))` | exit 5 |

- **Requirement.** Spec §9.11.1: `quote-sexp` returns the quoted form of
  its argument.
- **What it fences.** A scalar-payload constructor operand that is not a
  tracked allocation reaching the debug build's drop-glue liveness
  assertion. Before B1 the operand was stack-placed and each subject
  aborted with `STALE RC DEC (drop glue)`; the cells went green with B1 and
  no other change.
- **File and trace.** `tests/spec_09_macros.rs`,
  `// spec: spec/09-macros.md §9.11.1`, `class=check-domain-overreach`.

### 3.11 REPRO-1067 — a deeply nested expression aborts the compiler

Observations and attribution: [ACT-1067](../../sprints/actions/ACT-1067-deeply-nested-expression-overflows-compile-worker-stack-intake.md).
No prelude; `(import [primitives [*]])`; `E(n)` is `(add-i64 1 (add-i64 1 … 0))`
nested `n` deep, generated by the cell.

| Leg | Program | Required | Observed |
|---|---|---|---|
| Subject | `(defn main [] (Pure E(64)))`, `--run` | exit 64 | abort, exit 134: `priority-worker-0 … has overflowed its stack` (also at 56, 60 and 100) |
| Subject, never emitted | `E(64)` over a parameter as the body of an uncalled `(defn f [x] …)`; `main` returns 5 | exit 5 | the same abort (probed at 100) |
| Control | `E(48)` | exit 48 | as required |
| Control: syntactic depth, not type depth | an `(Opt … Int)` value of type depth 64 built by a flat `let` chain | exit 5 | as required |

- **Requirement.** The grammar of spec §2.3 does not bound nesting, and REPL
  §5.1 gives every compiler refusal a category and a location.
- **Harm.** The compiler dies on a signal with a runtime message that names
  no source position. Generated code and long operator chains reach the depth.
- **Assertion.** No signal and no `overflowed its stack` text, and the value.
  The cell does not assert that depth 64 is accepted for ever: if a ruled
  nesting limit refuses it, the assertion becomes that limit's located
  diagnostic and returns to `qa`.
- **Wrong implementations rejected.** A correction of the evaluated path
  only (the uncalled leg); a guard that refuses every nested program (the
  controls).
- **File and trace.** `tests/regression.rs`, `// spec: spec/02-grammar.md §2.3`,
  `locus` provisional (the stage was not observed), `found=S124`,
  `owner=/dev`, `class=input-depth-stack-exhaustion`.
- **Limit.** One run per leg; the debug threshold lies between 52 and 56 and
  the release build's between 64 and 200. `--link` and the REPL were not
  probed.

### 3.12 REPRO-1068 — a multi-signature function is omitted from regeneration

Observations and attribution: [ACT-1068](../../sprints/actions/ACT-1068-multi-signature-definition-omitted-from-regeneration-intake.md).
No prelude; `(import [primitives [*]])`. `F` is
`(defn f ([:Int n] n) ([:String s] (str-len s)))` and `G` is
`(defn g ([n] n) ([a b] (add-i64 a b)))`.

| Leg | Session | Required | Observed |
|---|---|---|---|
| Subject, entered | `F`, `(f 7)`; end the session; restart | the file holds `F`; restart: `(f 7)` is 7 and `(f "ab")` is 2 | the file holds the `import` only; restart: `undefined variable: f` |
| Subject, entered, by arity | `G` in place of `F` | the file holds `G`; restart: `(g 7)` is 7 and `(g 1 2)` is 3 | the file holds the `import` only |
| Subject, file-loaded | the entry file holds `F`; `(defn extra [] 5)` at the REPL | the file holds `F` and `extra` | `F` is deleted |
| Subject, another module | `m.cl` holds `G`; `/mod m`, `(defn extra [] 5)` | `m.cl` holds `G` and `extra` | `G` is deleted |
| Control | `(defn f [:Int n] n)` in place of `F`, entered and file-loaded | the file holds it; restart: 7 | as required |

- **Requirement.** REPL §15.4 rule 1.
- **Wrong implementations rejected.** A function section that writes
  single-signature definitions only; one that writes the family for an
  entered definition and loses a file-loaded one, or the reverse; one that
  writes one clause of the family (both restart values are asserted).
- **Assertion.** The form's presence in the file, the restart values, and no
  `[errors:` line.
- **File and trace.** `tests/repl_persist.rs`,
  `// spec: repl/spec/15-session-persistence.md §15.4`,
  `class=enumeration-miss`, `locus=src/save.rs` function-section
  enumeration, `found=S124`, `owner=/dev`.
- **Landed** at `f775478e`: the four subjects and both controls (§14.2).
- **Limit.** A redefined family, a family inside a `begin` and a family a
  macro produced were not probed.

## 4. Carried items that get no reproduction

### 4.1 ACT-0975 — excluded

- **Not a defect.** `src/bind_chain_analysis.rs::classify_expr` classes any <!-- doc-check: literal reason="Function name at this section's checkpoint, 4b58ab93" -->
  bind step that is not a direct platform-effect call as `Sequential`, so a
  `Par` branch is always a single effect leaf. The synchronous trampoline
  never meets a poll, launch or select node behind a `Bind`.
- **Observed.** In an independent pair, each of these as one or both steps
  returned the right value and ran serially (215 to 226 ms against 113 ms
  for the direct-leaf control): a user function that reaches a poll through
  a `Bind`; the same inline; a `race`; two `race`s; a `select`; a launching
  loop; a two-step poll chain.
- **Fence F-0975** (`test`, passes on arrival). Three of those programs (the
  inline `Bind`, the `race` and the launching loop, each paired with a
  direct `poll-read`) yield their values with exit 0 under `--run`. It fails
  with the trampoline's `unknown IO tag` panic if the pass ever admits a
  non-leaf step. Class: safety fence for the exclusion.
  `// spec: spec/10-io.md §10.12.1`.
- The intake is resolved and deleted: F-0975 is committed and passes.
- **One program does reach a non-leaf step:** a local named like a
  platform function (REPRO-1065-e, §3.8). Its cause is the pass's
  spelling lookup, not this exclusion, and it goes with ACT-1065.

### 4.2 ACT-0994 — no public reproduction

- The source claim holds: a claim's loaded completion is keyed by module
  name, not by registration.
- The window is one worker's in-flight object load. A process test cannot
  hold it open, and no harm has been observed.
- **Allocated to `dev`(src) with `design`(int), with the binding decision:**
  a scheduler module test that grants a claim, re-registers the module,
  completes the claim as loaded, and asserts the fresh registration is not
  in memory. What it cannot prove: that a real session reaches the window.

### 4.3 FIXME 0934 — the cancellation face balances

- **Not a defect.** A losing `Pure` with a heap payload is released.

| Program | Allocations | Frees |
|---|---|---|
| `(select [(Pure 7) (Pure 8)])` in a continuation (control) | 7 | 7 |
| `select` of two `(Pure (str-concat …))`, result measured with `str-len` | 13 | 13 |
| `race` of the same two | 13 | 13 |
| `(race (Pure 7) (Pure 8))` (control) | 4 | 4 |
| Four suspended-loser shapes over `poll-pool` | 11 to 19 | equal |

- **Fence F-0934** (`test`, passes on arrival). The `select` and `race`
  heap-payload programs with their scalar controls, `CRANELISP_RC_TRACE=1`
  and `CRANELISP_RC_DEC_CHECK=1`, no prelude, in every mode; allocations
  equal frees and are greater than the control's.
  `// spec: spec/10-io.md §10.12.9` item 4. It is committed and passes in
  every mode; the filing is deleted.

### 4.4 FIXME 0915 — prefix and subject faces

- **A defect with no durable public trigger.** The doubled prefix and the
  module-doubled, `$`-mangled subject appear today only in ACT-1034's
  refusal, for example
  `codegen failed for p/(p/Size.size$p/Opt […] primitives/Int): codegen error at 148..156: …`.
  That refusal disappears when ACT-1034 is corrected in this sprint, and a
  cell asserting the frame on it would then pass with nothing to observe.
- **Evidence stays at the module tier,** with the backend and int halves the
  filing names, under the user's D1 ruling. No `test` cell.
- **The location face has durable triggers:** §3.4.

### 4.5 ACT-0986 — settled

Item 1 was decided by the user on 2026-11-15 (REPL §16.1: in-language
discovery excludes silently). Item 2 is done. The action is resolved.

### 4.6 FIXME 0694 — run-dependent members

- **Class II, nullary member.** 40 of 40 stress iterations passed under
  fourteen busy workers; S121 measured 53 failures in 200 under that load
  shape. It no longer reproduces. No correction is attributed.
- **Every other member** is a single occurrence with no captured condition.
  No reproduction can be written for one, and none is allocated.
- **Class I** (heap corruption, one S115 capture) keeps its owed faces. It
  remains an unattributed memory-safety signal, carried by the user's
  ruling.

### 4.7 ACT-1025 — resolved at S123

Already classified as a fixture assumption and corrected. The filing is
deleted; FIXME 0694 no longer links it.

## 5. Leads

### 5.1 `user_samples` — the reload notice can arrive one prompt late

- Both `user_samples` tests fail on the same step: after a `/sh` turn saves
  a file, the `[updated: …]` lines are missing from that turn.
- Reproduced in scratch at 1 run in 12 under load, 0 in 20 unloaded. In the
  late run the notices follow the next prompt and precede its result.
- **Classified: a product defect** in `src/`, by the user's S124-Q6 ruling,
  and in S124 scope. Reproduction and conditions: §3.6;
  [ACT-1061](../../sprints/actions/ACT-1061-sh-save-notice-arrives-after-the-next-prompt-intake.md).
- Until the correction lands, a suite count names both tests as
  run-dependent.

### 5.2 `ctx.txt`

`src/repl/mod.rs::session_lock_admission_tests::locked_session_refuses_exactly_the_commands_that_run_program_code`
runs `/context ctx.txt`, which writes to the test process's working
directory. The file's modification time moved when that test ran alone and
not when its sibling did. Filed to `dev`(src) as
[ACT-1060](../../sprints/actions/ACT-1060-session-lock-module-test-writes-ctx-txt-to-checkout.md).
The stray file was left in place.

### 5.3 ACT-1017

Resolved at S123; its two guards pass. The filing is deleted: no standing
document links it.

### 5.4 The S123 close set

`.local/s123-close/reds.txt` equals the 44 filed guards of §1, name for
name.

### 5.5 Leads from the Phase 3 designs (2026-11-17)

| Lead, from | Disposition | Where |
|---|---|---|
| Other host-promised primitives as values (`design`(backend), `design`(typecheck); source reading) | **Confirmed, same defect.** `select`, `sleep`, two Trace accessors, `sconcat` and `discover-tests` are refused like `bind`. `quote-sexp` is not: it carries a slot and works as a value | REPRO-1063, §3.9 |
| Partial applications `(bind io)`, `(race a)` (same) | **Confirmed, a worse face than predicted.** `race` panics the compile worker; `bind` compiles, links and aborts on a wild pointer. Same filing and correction | REPRO-1063-p, §3.9 |
| A value use builds the direct call's IO node (`design`(backend), proposed falsifier) | **Allocated at two tiers.** Balance against the direct twin at the solution tier; node identity at the module tier | T-1063-b and M-1063, §3.9 |
| A local named like a platform function (`design`(int); predicted) | **Confirmed, a defect:** an abort, with a spelling control. A face of ACT-1065 | REPRO-1065-e, §3.8 |
| An imported user `bind` with a prelude-exported primitive (`arch`) | **Allocated.** RED on ACT-1075, which masks the import assertion | T-1065-f, §3.8 |
| A cycle peer defining `bind` (`arch`) | **Not allocated: no legal program reaches it.** Returned to `design`(int) | §3.8, §6 |
| Found in passing | A direct `quote-sexp` call on a scalar-payload `Sexp` aborts: a new defect. A parametric method that recurses at its own instantiation is refused: a face of ACT-1034 | REPRO-1066, §3.10; T-1034-d and T-1034-e, §2.3 |

### 5.6 Leads after the S124-Q7 re-ruling (2026-11-17)

Each was re-run by `qa`; the sprint's own probes are the provenance of the
lead, not of the row.

| Lead, from | Disposition | Where |
|---|---|---|
| A free function re-used at `(Opt Int)` in its own body compiles and narrows (sprint probe) | **Not a defect: the function rule, unchanged.** `(defn f [o] (match o [Nope (f (Yep 7)) (Yep x) 1]))` is monomorphic at `(Opt Int)`: it yields 1 for `(f (pick 0))`, and `(f (Yep "s"))` is a type mismatch | The function twin of T-Q7-a, §9.1 |
| The growing free function is refused as `infinite type` (sprint probe) | **Not a defect.** The recursive call unifies with the definition's own type | The function twin of F-PR, §9.1 |
| Inside `impl Size (Opt :Size a)`, `(size (Yep 7))` and `(size (Yep o))` both fail at codegen (sprint probe) | **Two different defects of one filing's seam.** The first is a legal program refused: ACT-1034's fourth face. The second is a program §3.10 refuses, refused by the wrong stage with a compiler-internal message | T-Q7-a and F-PR, §9.1 |
| ACT-1066 exits 5 with `CRANELISP_NO_STACK_ALLOC=1` (coordinator probe) | **Confirmed and re-attributed:** ACT-1049's mechanism at the drop-glue assertion. Not memory-unsafe | §3.10; ACT-1066 |
| A macro-produced `main` with the wrong shape; `(defmacro main [] …)` (`qa`, earlier) | **Both constructible in core forms, both RED today at `1:1` and `0..0`.** Legs of ACT-1036 | REPRO-0915-loc, §3.4 |
| A trait method named `main` (`spec`, S124-Q9) | **Ruled: it does not define `main`.** Today: `entry module has no 'main' function` at `1:1` and `0..0`, so the cell is RED on T-Q8's clauses | T-Q9-a, §9.6 |
| Found in passing | A re-entry whose type doubles at each step is non-terminating with keys of exponential size. `design`(typecheck) confirms by analysis that the depth limit is reached only after types of about 2^64 nodes | No cell: an accepted risk, §10 |

### 5.7 Leads from the closing pass (2026-11-17)

| Lead, from | Disposition | Where |
|---|---|---|
| The depth limit is ruled (user) | **Allocated at the solution tier:** the floor, and the design's constant as its twin | T-DEPTH-a and T-DEPTH-b, §9.1 |
| S124-Q9 is ruled "no", with the multi-arity consequence (user) | **Allocated.** Both programs are refused today at `1:1` and `0..0` | T-Q9-a and T-Q9-b, §9.6 |
| The doubling shape is not refused in bounded time (`design`(typecheck), analysis) | **Not written.** After T4 its subject would exhaust memory in the suite, not fail an assertion; the user accepted the risk | §10 |
| Found in passing | A constructor expression nested 64 deep aborts the compiler before any instantiation: a new defect, and a fixture constraint for the depth cells | REPRO-1067, §3.11; ACT-1067 |
| Found by reading | The design counts implementation-method instances; spec §3.10 counts implementation instantiations. Two members that call each other reach 65 method instances at a type nested 33 deep. **Settled:** the design now counts spec's unit | T-DEPTH-c, §9.1 |
| Found by reading | No committed cell rejects polymorphic recursion in a function; the fold canary evidences only the accepting direction | T-FR, §9.1; §11 |
| Found by reading | `repl_negative::type_error_arg_mismatch` asserts a category and no location, so it never evidenced REPL §5.1 item 2 | §11 |

## 6. Handoffs

| To | What |
|---|---|
| `test` | The evidence wave is delivered and accepted (§14). What remains is §14.3, in the wave each item names. **Completion, unchanged:** each RED fails on its stated assertion and not on setup, each control and fence passes, and the returned clause map names the leg for every row. F-PR-3 is never written. |
| `dev`, per surface | The module rows: CEN-1, CEN-2, M-1062, M-1050, M-1052, M-P15, M-FE, M-1038, M-LAY, M-1061, M-1063, the §2.3 and §3.5 unit rows, and the C8 rows of §3.8. Each is RED before its correction or carries both detection legs. The cells each wave must turn green, and the ones it must not disturb, are §14.2. A RED that stays RED on its correction's tree returns to `qa` unchanged; the cell is not adjusted. |
| `design`(typecheck), `dev`(typecheck) | (1) §2.2: confirm the two sites; unit rows with the correction. T-1034-d shows a third: the instance is published and the site inside it is not redirected. T-Q7-c's REPL leg shows the dispatch hop from a free-function instance that an earlier cluster published (§9.1). (2) The counting unit is settled as the implementation instantiation ([monomorphisation §3.10.3](../../design/typecheck/monomorphisation.md#3103-recursion-through-dispatch)); T-DEPTH-c is its cell. (3) A lead, not observed: the mint recurses once per chain element on the compile worker's stack, and that stack is exhausted today by a source expression about 56 forms deep in the debug build (ACT-1067). T-DEPTH-a and T-DEPTH-c are the falsifiers of "the deepest admitted chain fits"; `dev`'s boundary row 6 should run on a worker-sized stack. (4) `CRANELISP_OWNERSHIP_TRACE` prints no summary for a member of a multi-signature family. No cell depends on it (§9.4); it is recorded as a gap in a diagnostic observer. |
| `design`(int) | (1) [ACT-1068](../../sprints/actions/ACT-1068-multi-signature-definition-omitted-from-regeneration-intake.md): place the correction once it is scheduled, and say whether `section_entry_claimed_or_excluded` is repaired or removed. (2) With `dev`(`src/`): the §4.2 module test when ACT-0994 is scheduled. |
| `dev`(`src/`) | ACT-1060's completion check is met at `8667a868` (§14.2); the filing is `dev`'s to resolve. |
| `sprint` | (1) ACT-1068 needs a scheduling decision from the user: its correction is in no S124 row and it loses user data. (2) Suite readings are taken in the primary harness: thirteen tests fail only in the Codex sandbox (§14.1). (3) The overload leg of T-D7-b is a residual that needs the user's approval (§9.4). (4) The document gate fails on 600 findings, 577 of them ignored-path; their disposal is with the user, and until it is decided no claim rests on that gate. (5) `tests/plan/spec_coverage_reconcile.py` counts a cleared row only when its tag has a "was" clause, so a new obligation tagged `[Uncovered S124]` alone is outside the close gate (§11). The repair is `qa`'s, with its detection test, and needs a pass that may run it. (6) Two questions are queued for the user and hold no cell (§10). (7) ACT-1067 is carried with its reproduction RED. (8) [ACT-1018](../../sprints/actions/ACT-1018-exemplar-warm-solve-residual-intake.md) has no correction in any S124 wave and ACT-1050's is predicted not to move it (§14.4): it needs a route or a recorded carry. |
| `spec` | (1) [Appendix D](../../spec/appendix-d-open-questions.md), S124-Q7: the "counting-unit gap — unresolved" paragraph is stale at `2c690be5`. The design counts implementation instantiations, as spec §3.10 states; the remaining question is the method-level re-entry (§10). (2) Three places where spec §3.10 and §10.6 leave the observation open: §10's list. (3) Whether the language limits the nesting depth of a source expression (ACT-1067), for the user. |

## 7. What was run, and limits

- One full `cargo nextest run --no-fail-fast`; two single module tests for
  §5.2; one 40-iteration stress run of one test under load for §4.6.
- Scratch probes of `target/debug/cranelisp` for every other observation.
  Counts are single runs unless a row gives a rate; §3.2's times are the
  best of three.
- `--link` was not probed for §3 or §4. The cells run every mode where the
  row says so, and a divergence found there returns to `qa`.
- The document checker cannot run on this tree (§1), so this record's links
  were checked by hand.

## 8. Observations made for the designs

Made by `qa` on the checkpoint binary, in scratch directories, no prelude,
`(import [primitives [*]])` only. Authority for §8 to §13 adds the Phase 3
designs: the [release contract](../../design/backend/non-concrete-release-contract.md)
§7 to §9, [backend](../../design/backend/backend.md) §7 and §9,
[trace codegen](../../design/backend/trace-codegen.md),
[trace runtime](../../design/intrinsics/trace-runtime.md),
[monomorphisation](../../design/typecheck/monomorphisation.md) §3.10,
[typecheck](../../design/typecheck/typecheck.md) §12,
[frontend modules](../../design/frontend/modules.md),
[int](../../design/int/int.md) §6.11 to §6.13, §7.6.3 and §16.0, and
[session transaction](../../design/int/session-transaction.md) §2.4.

### 8.1 ACT-1050 — the producer is the binary's bind-chain rewrite

**The absent arm, and none of the three designed owners.** The continuation
that reaches `compile_lambda` is not the node the user wrote.
`src/bind_chain_analysis.rs::make_bind` rebuilds every inline
`(bind io (fn [x] …))` and gives the `bind` callee, the `Lambda` and the
`Apply` one span, the application's. Typecheck records expression types by
span (`CheckState::expr_types`), so the three nodes share one entry and the
`Lambda` does not keep a function type.

| Observation | Subject `(bind (Pure [49]) (fn [v] (Pure 49)))` | Sibling |
|---|---|---|
| Allocations and frees, `--run` | 5 and 4 | let-bound control: 5 and 5 |
| Lambda symbol in the object | `__lambda_main__40_77__`, the span of the whole `bind` form | control: `__lambda_main__48_66__`, the span of the `fn` |
| Lambda body, disassembled | the parameter register is never read; no release | control: calls the `(Vec Int)` drop glue on the parameter |
| Rewrite does not fire: the continuation is `(if true (fn …) (fn …))` or `(let [z 1] (fn …))` | — | 5 and 5 |
| Parameter used twice under the rewrite, armed check | — | 5 and 5, exit 49 |

- **What each row decides.**
  - The body rows meet the filing's refutation condition and do not refute
    it: the subject's lambda emits no release.
  - The two unrewritten siblings differ from the subject only in whether
    `make_bind` fires. They balance, so neither "an inline lambda in a
    builtin's argument" nor `compile_lambda` itself loses the type.
  - The twice-used row refutes a wrong concrete (scalar) type: a
    scalar-typed parameter would skip both retains and stop the armed check.
    It balances because an untyped parameter takes its type from an
    occurrence (`derive_param_type_from_body`). That is the absent arm.
- **Not observed:** the type value itself. No dump prints a lambda node's
  type. The span-keyed table and the rewrite's span reuse are source
  readings at `4b58ab93`; the frontend design names the same collision as a
  hazard ([defmacro synthesis §2.2](../../design/frontend/defmacro-synthesis.md#22-the-body-is-constrained-to-sexp-in-every-clause-shape)).
- **Refuted if** a build whose rebuilt `Lambda` keeps the written lambda's
  span still leaks. The census condition is met (§14.5): the subject records
  one absent-arm record in `Plain`, and its let-bound twin none.
- **Ownership.** The typecheck prediction is right about inference and
  wrong about arrival; the backend's "absent arm" reading is right, and its
  producer is neither typecheck's inference site nor the backend. The
  correction is placed by `design`(int) in the rewrite
  ([bind-chain analysis §3.6](../../design/int/bind-chain-analysis.md#36-reconstruction)):
  each rebuilt node takes the span of the node it replaces. Step 2 of the
  close would refuse the subject, so the correction precedes it.
- **Other faces.** A two-step chain leaks at both continuations (9 and 7).
  A nested payload leaks 2, a `String` 1.
- The filing carries this attribution:
  [ACT-1050](../../sprints/actions/ACT-1050-inline-bind-continuation-unused-heap-argument-leak-intake.md).

### 8.2 ACT-1062 — a match binds another parameter's type (memory-unsafe)

**A defect, confirmed with a control and observed at the emission seam.**
Intake: [ACT-1062](../../sprints/actions/ACT-1062-match-field-binder-takes-another-parameters-type-intake.md).

```clojure
(deftype (P a b) (MkP [:b y :a x]))
(defn f [p] (match p [(MkP y x) (add-i64 x (str-len y))]))
(defn main [] (Pure (f (MkP "abc" 2000))))
```

| Leg | Program | Required | Observed |
|---|---|---|---|
| Subject | above | exit 211 (2003) | SIGSEGV under `--run`, `--link` and the REPL, armed or not |
| Control | fields declared `[:a x :b y]`, otherwise identical | exit 211 | exit 211, 3 allocations, 3 frees |
| Subject, small scalar | the subject with `4` | exit 7 | SIGBUS |
| Subject, unmentioned parameter | `(deftype (R a b) (MkR [:b y]))` matched at `(R Int String)` | exit 3 | the release path panics and the process aborts |
| Control | `(deftype (R b a) (MkR [:b y]))` at `(R String Int)` | exit 3 | exit 3, balanced |
| Subject, accessor | `(deftype (Duo a b) [:b y :a x])`, `(Duo.x d)` and `(Duo.y d)` | exit 211 | SIGSEGV |
| Control | `Duo` with fields in parameter order | exit 211 | exit 211, balanced |

- **Seam.** In the subject's CLIF for `f`, the retain
  (`atomic_rmw add` at `+8`) is applied to the word loaded from the `Int`
  field, and the `String` field is passed to a consuming call with no
  retain. In the control the same retain is on the `String` field. The pair
  differs only in field order.
- **Locus.** `CompileContext::ctor_field_types` pairs type arguments with
  type variables in order of first appearance in the fields, as
  `design`(backend) read. The unmentioned-parameter leg is that reading's
  second prediction and it holds.
- **Refuted if** `cranelisp_types::ctor_field_types_at` returns the same
  wrong pairing for the subject, which would move the fault to the types
  projection.
- **Faces:** a wild atomic write through a scalar, and a use after free.
  The REPL's definition echo shows the correct type
  `(Fn [(P Int String)] Int)`, so typecheck is not implicated.
- **Why coverage missed it.** No type in `stdlib/`, `examples/`,
  `exemplar/`, `user/` or the test corpus mentions its parameters out of
  declaration order (scanned; one phantom-parameter type exists, in a
  reject cell). The definition-variants lens never enumerated
  parameter order against field order. [PLAN](PLAN.md#standing-coverage-audit--definition-variants)
  gains that axis when the cells land.
- **Correction is in scope:** close step 1 (row D1) deletes the walk.

### 8.3 ACT-1039 — the traced set depends on slot contents at codegen

- **Control.** The filing's program records 0 frames under `--run`. With
  `fib` moved to an imported module, which is published before the entry's
  codegen, the same `--run` records 5.
- This confirms the designs' reading
  ([trace codegen §1](../../design/backend/trace-codegen.md#1-the-traced-set-is-fixed-by-slot-claims-not-by-slot-contents))
  and refutes the filing's earlier variant, that compilation order within
  the wrapper set decides it. `CRANELISP_GOT_TRACE` shows the entry's slots
  written in one batch at publication; it cannot show codegen time, so the
  control, not the trace, carries the attribution.
- **Owner: backend,** as designed. The filing is updated.

### 8.4 `bind` as a value

Classified as a defect on spec §3.2.1: §3.9 and
[ACT-1063](../../sprints/actions/ACT-1063-bind-as-a-value-refused-at-codegen-intake.md).

## 9. Conditions for the S124 corrections

One row per condition. **Class:** A acceptance evidence, F safety fence,
O diagnostic observer, M maintenance check. **Tier:** `e2e` is a `test` cell
through the binary; `module` is a `dev` row beside the named seam; `suite`
is a reading `qa` takes from a full run. "Existing" cells keep their
assertions unchanged. Every RED lands failing, not ignored, before its
correction.

### 9.1 Type concreteness (item 1)

| ID | Condition | Class, tier | Wrong outcome it rejects | Completion |
|---|---|---|---|---|
| CEN-1 | Each census point (retain, release, absent, field) records once for its planted fixture, in its partition, shape and class; each concrete twin records nothing on the arms and once in the concrete field class; an inner compiler's record carries its frame's partition | M, module, `dev`(backend) | A point that cannot fire; a field point that never executes; a count taken at the early return, which includes every scalar field | Both legs per point in the instrument's change-set (release contract §7.3, §9) |
| CEN-2 | Emission is byte-identical with the census variable set and unset; the census writes only its file; it is absent from a release build | M, module and the golden lane, `dev`(backend) | An instrument that perturbs what it measures, or text on a stream tests assert | Golden lane clean in the census change-set |
| CEN-3 | First reading: one full default-suite run with `CRANELISP_CATEGORY_CENSUS` set. `qa` attributes every non-concrete record to a producer and reduces each to a cell | O, suite, `qa` | — | Taken at `1a3ab46e`: every record was on the absent arm in `Plain`, owned by the bind-chain rewrite (ACT-1050). Re-read on the W4 tree as CEN-4 (§14.5) |
| CEN-4 | The zero read: zero records in every partition, arm and non-concrete field class, **in a run where** the concrete tallies are non-zero, the ACT-1034 cells A1, A2 and T-1034-b pass and the ACT-1050 and REPRO-1062 cells pass | A, suite, `qa` | A zero from programs that never reach emission (§2.4); a zero from an unset variable or a release binary; a zero in a partition that compiled no frame | Met at `8667a868` (§14.5): zero from every program, with per-partition frame counts from the run's own file. Two records remained from backend module fixtures; step 2 gave one a typed node and the other is row D1's planted negative |
| CEN-5 | After step 2: no test fails outside §1's filed set and the REDs this record allocates, and the golden lane is byte-identical | A, suite and golden lane | A legal program refused by a refusal the close added | Met on the B4 tree (§14.5): the failing set is the pre-B4 set by name, and the golden lane passed |
| REPRO-1062-a | §8.2 subject and control (`P`), every mode: value, and allocations equal to frees | A, e2e | Pairing by first appearance; a correction for products only | RED by signal, then green with step 1 |
| REPRO-1062-b | Unmentioned parameter (`R`) with its control | A, e2e | Pairing that skips an unused parameter | as above |
| REPRO-1062-c | A sum whose constructors mention the parameters in opposite order, `(deftype (E a b) (L [:b l]) (R [:a r]))`, matched at `(E Int String)` on `R`, with the in-order twin | A, e2e | Pairing computed across constructors | as above; `test` reports the observed face |
| REPRO-1062-d | Accessor leg (`Duo`), with its control | A, e2e | A correction of the match lowering that leaves the accessor frame | Green after step 1. No accessor producer correction is owed (`design`(typecheck), `efaf2930`) |
| REPRO-1062-e | **REPL display.** With [ACT-1062](../../sprints/actions/ACT-1062-match-field-binder-takes-another-parameters-type-intake.md)'s `shapes.cl` imported, `(MkP "s" 2000)` displays `:(shapes/P primitives/Int primitives/String) (P.MkP "s" 2000)`. Controls: `(MkQ 2000 "s")` and `(MkP 7 2000)` | A, e2e | A display reader that pairs by first appearance; a correction that reads the declared parameters only when the argument types differ in category | RED by signal, then green with the `src/` display reader's correction |
| REPRO-1062-f | **Trace.** `(trace (obsp (MkP "s" 2000)))` yields a child frame whose first argument is `(P.MkP "s" 2000)` and whose result is `2001`, in `--run`, `--link` and the REPL, read as T-D4-t reads its frame. Controls: `obsq` in order, and `obsps` at `(P Int Int)` | A, e2e | A descriptor baked with another parameter's field type | RED by signal, then green with the backend baker's correction |
| M-1062 | Field types at a concrete instantiation bind each field to its own parameter, for fields out of declaration order and for an unmentioned parameter | A, module, `dev`(backend) | — | The release contract §9 row, RED before step 1 |
| T-1050 | The twelve committed subjects and six controls | A, e2e, existing | A release in the `bind` node; a `Vec`-only correction | Green in every leg, assertions unchanged |
| T-1050-a | A two-step chain whose continuations both ignore a heap argument balances against its let-bound twin, every mode, moves on and off | A, e2e | A correction of the first rebuilt lambda only | RED (residual 2), then green |
| M-1050 | The `Lambda` a rebuilt bind step carries keeps a function type through typecheck, pinned at the rewrite, with every input node given its own span ([bind-chain analysis §7](../../design/int/bind-chain-analysis.md#7-open-obligations)) | A, module, `dev`(`src/`) | A correction keyed on `bind`; a backend release for an untyped parameter | RED before the correction |
| T-1034 | §2.3 | A, e2e | §2.3 | §2.3 |
| T-Q7-a | **Spec §3.10, S124-Q7 (B): direct re-entry at another instantiation is an ordinary dispatch.** Fixture Q7 below. Legs, each yielding 7: `(size (pick 0))` at `(Opt Int)`; `(size (pb 0))` at `(Opt Bool)`, so the re-entry's `(Opt Int)` is demanded by no root; `(size (none2 0))` at `(Opt (Opt Int))`, a shrinking re-entry; and the body variant `(size (Yep (Yep 7)))` reached from `(Opt Int)`, which grows once and settles. `--run`, `--link` and the REPL | A, e2e | The re-entry redirected to the enclosing instance (the `(Opt Bool)` leg then yields 1); a chain that refuses a re-entry no smaller than its predecessor (the grows-once leg); a body judgment that refuses the `impl` | RED today: each is refused with `undefined function: Size.size$…/Opt`. Green with T4. Control, green today: the same `impl` with a `main` that never calls it exits 5, and the REPL accepts the `impl` turn |
| T-Q7-b | The same for a sibling member: `describe` as `(add-i64 4 (size (Yep 0)))` in `(impl Cont (Opt a) …)` yields 5 for `(describe (Yep "s"))`, every mode | A, e2e | A dispatch hop written for the enclosing method only, or for the enclosing instantiation only (T-1034-e passes under it) | RED today: `undefined function: Cont.size$…/Opt`. Control, green today: the same members in an impl for a type with no parameters |
| T-Q7-c | Re-entry through a constrained helper: `(defn wsize [:Size x] (size x))`, with fixture Q7's `Nope` arm as `(wsize (Yep 7))`; `(size (pick 0))` yields 7, every mode | A, e2e | A refusal of helper-mediated re-entry as polymorphic recursion; a chain that refuses a constant re-entry | Green on arrival under `--run` and `--link`, and at the REPL with the helper, the impl and `main` in one `begin`. RED at the REPL with one form per turn: `undefined function: Size.size$…/Opt` inside the `wsize` instance. That is ACT-1034's dispatch hop by cluster shape (§2.1), not a mode difference. Green in every shape with T4 |
| T-Q7-d | Re-entry through another implementation: `(impl Size (Box :Size a) …)` whose body is `(add-i64 (size x) (size (pick 0)))` and an `(Opt :Size a)` body `(add-i64 1 (size (MkBox x)))`; `(size (Yep 3))` yields 4, in both declaration orders, every mode | A, e2e | A chain keyed on one template; a refusal of a cycle between two implementations | RED today. `Box` first: `undefined function`, green with T4. `Opt` first: `no impl of trait` (ACT-0985), green with T2 and T4 |
| F-PR | **Spec §3.10: a chain of implementation instantiations exceeding the depth limit is a type error, reported when an instance is demanded.** Fixture Q7 with the `(Yep x)` arm as `(add-i64 1 (size (Yep o)))`, demanded by `main` as `(size (Yep 3))`. Non-zero exit within the harness timeout; the diagnostic's category is `type error`; it is located at the inner call's line; no `codegen error`, `undefined function` or `0..0`. `--run` and `--link`. REPL: the `impl` turn is accepted, the turn that evaluates `(size (Yep 3))` reports the error, and a following `(size 4)` yields 4 | A, e2e | The chain missing, so the compiler hangs; the refusal left to codegen; a refusal raised at the `impl` form | RED today on the category: refused at codegen as `undefined function`. Green with T4. Controls, green today: the same `impl` with no caller exits 5; the function twin `(defn g [o n] (if (eq-i64 n 0) 0 (g (Yep o) (sub-i64 n 1))))` is a type error (`infinite type`) |
| F-PR-2 | The same through a constrained helper: `(defn wrap [:Size x] (size (Yep x)))`, called as `(wrap o)` from the impl's `size`. The diagnostic is a `type error` located on a line of `wrap` or of the impl's `size`, with the other F-PR clauses. At the REPL the helper and the impl are entered in one `(begin …)`, because each refers to the other; entered as separate forms the declaration itself is refused (`no impl of trait`) | A, e2e | A chain that follows the dispatch arm only: this re-entry passes through a free-function instance | RED today on the category (`undefined function: wrap`). Green with T4 |
| F-PR-3 | A re-entry whose type doubles at each step | — | — | **Never written** (user, 2026-11-17). No second limit is admitted; the shape is an accepted named risk (§12) |
| F-PR-4 | A growing re-entry through two implementations, each dispatching to the other at its own value wrapped: `Opt`'s `(Yep x)` arm is `(size (MkBox o))` and `Box`'s body is `(size (Yep b))`, demanded as `(size (Yep 3))`, in both declaration orders, with F-PR's clauses | A, e2e | A chain keyed on one template | Constructible since T2. Read by `qa` on `24c42430`: both orders are refused as a `type error` under `--run`, located on the line of the refused call; the no-caller control exits 5; at the REPL the demanding turn reports it and `(size 4)` then yields 4. `test` writes it; it is expected green on arrival |
| T-DEPTH-a | **Spec §3.10: the depth limit is at least 64.** Fixture D below at 64 levels: `(size v63)` yields 64, in `--run`, `--link` and the REPL | A, e2e | A count that refuses the 64th instance; a mint that exhausts the compile worker's stack before the limit (ACT-1067 shows that stack is small); an instance symbol for a 64-deep type that the object writer or linker rejects | RED today: `undefined function: Size.size$…/Opt` (ACT-1034's nested face; probed at 2, 64 and 65). Green with T4 |
| T-DEPTH-b | The design's constant: fixture D at 65 levels is refused with F-PR's clauses, located at the impl's `(size x)` line | A, e2e, a design guard ([monomorphisation §3.10.3](../../design/typecheck/monomorphisation.md#3103-recursion-through-dispatch)) | A limit that is never reached, so T-DEPTH-a's fixture proves nothing about depth; a refusal raised at codegen | RED today on the category. Green with T4. It moves with the constant: spec admits any limit of 64 or more |
| T-DEPTH-c | **The limit counts implementation instantiations, not method instances.** Fixture D's type and trait with two members: `sa` as `(sb o)` and `sb` as `(match o [Nope 0 (Yep x) (add-i64 1 (sa x))])`, and an `Int` implementation of both. Each level puts two method instances and one implementation instantiation on the chain. At 64 levels `(sa v63)` yields 64 in every mode; at 65 it is refused with F-PR's clauses | A, e2e | A count of method instances, which refuses at 33 levels; a chain of 128 mints that exhausts the compile worker's stack | RED today (`undefined function`, ACT-1034). Green with T4. Lands before W3 |
| T-FR | **Spec §3.10, the function rule, both directions.** `(defn g [o n] (if (eq-i64 n 0) 0 (g (Yep o) (sub-i64 n 1))))` is a type error at its definition, every mode. `(defn f [o] (match o [Nope (f (Yep 7)) (Yep x) 1]))` yields 1 for `(f (pick 0))`, and adding `(f (Yep "s"))` is a type mismatch | A, e2e | The implementation rule applied to a function's own recursive call: `g` is then accepted and reaches the chain, and `f` is instantiated at two types | Passes on arrival (§5.6) and after T4 |
| Q7-S | On the T4 tree, no test outside F-PR, F-PR-2, F-PR-4, T-DEPTH-b and T-DEPTH-c's 65-level leg fails with the depth diagnostic | A, suite, `qa` | The chain refusing a committed program, a `stdlib/` module, an example or the exemplar | A full run after T4; any hit returns to `qa` before the cell is changed |

**Fixture Q7.** No prelude; `(import [primitives [*]])`.

```clojure
(deftype (Opt a) Nope (Yep [:a v]))
(deftrait Size (size [self] Int))
(impl Size Int (defn size [n] n))
(impl Size Bool (defn size [b] 1))
(defn pick [n] (if (eq-i64 n 0) Nope (Yep n)))
(defn pb [n] (if (eq-i64 n 0) Nope (Yep true)))
(defn none2 [n] (if (eq-i64 n 0) Nope (Yep (pick n))))
(impl Size (Opt :Size a)
  (defn size [o] (match o [Nope    (size (Yep 7))
                           (Yep x) (size x)])))
```

**Fixture D.** Fixture Q7's type, trait and `Int` implementation, with

```clojure
(impl Size (Opt :Size a)
  (defn size [o] (match o [Nope 0 (Yep x) (add-i64 1 (size x))])))
(defn main [] (let [v0 (Yep 0) v1 (Yep v0) … ] (Pure (size vN))))
```

- **The value is built by a flat `let` chain, never by nesting
  constructors.** A constructor expression nested 56 deep aborts the
  compiler for an unrelated reason (REPRO-1067), and would make both legs
  fail on setup. The cell generates the chain.
- **Each level puts one instance on the chain** and adds 1, so the value
  is the depth and the two legs differ by one binding.
- **The count's unit, as the cells read it.** The non-parametric `Int`
  implementation is not an instantiation and does not count. If T-DEPTH-a
  is refused on the T4 tree, the cell returns to `qa` with the observed
  boundary and is not adjusted.
- **Why the `Nope` arm.** Each subject's `main` passes a `Nope`, so the
  re-entering call executes and its value is the program's. A fixture that
  only compiles the arm cannot tell the `(Opt Int)` instance from the
  enclosing one.
- **The F-PR family asserts a category, a location and termination, not
  wording.** `test` reports the text it observes. The exact line is pinned
  only where one successor site exists (F-PR).
- **A location is a line or a span.** REPL §5.1 item 2 admits either. A
  program loaded as the REPL's entry file reports `[errors: p.cl]` and
  `type error at START..END`, as an ordinary type error there does. A REPL
  entry-file leg asserts the file name and that the span's start falls on
  the row's line; it does not assert `p.cl:LINE:`.
- **T-Q7's neighbours stay accepted:** T-1034-d and T-1034-e (the
  enclosing implementation at its own instantiation), A1 and A2
  (constraint-mediated) and C1 (a different implementation).
- **The function rule has its twins and no new cell.** A free function
  re-used at `(Opt Int)` in its own body is monomorphic there (§5.6); the
  committed §3.10 cells own that rule.
- **The boundary at the module tier** is the chain's row 6: 64 mints, 65
  is refused, two alternating implementations are refused at 65 in all,
  and a free-function instance does not count. T-DEPTH-a and T-DEPTH-b
  add what a module row cannot see: the worker's stack, the instance
  symbol in a linked object, and the diagnostic through each mode.
- **`dev`(typecheck)** owes the chain's and the template check's rows at the
  module tier ([monomorphisation §3.10.5](../../design/typecheck/monomorphisation.md#3105-evidence)
  rows 5 to 9), including the method as a value, a partial application and
  a default method's re-entry.
- **Golden re-baselines** (M, `dev`, the existing lane): each is scoped and
  attributed, and exists only where the release contract §7.7 declares one.
  Step 1's is expected to be empty: no corpus type has out-of-order
  parameters (§8.2).
- **Structural claims need no instrument of their own.** "The non-concrete
  arms no longer compile" is evidenced by the entry points' `&ConcreteType`
  parameters and the deleted arms; `review` reads them against the release
  contract §8 reject 17. The census after the close is the measured
  detector for a producer regression.
- **What these cannot prove:** a concrete but wrong type from a producer
  (safety register R18). No S124 instrument observes it; ACT-1062 is an
  instance found by reading.

### 9.2 Cached restore (item 2, ACT-1052)

| ID | Condition | Class, tier | Completion |
|---|---|---|---|
| T-1052 | The committed K-6 guard and its control, `--run`, `--link` and the REPL `/mod` leg | A, e2e, existing | Green, unchanged |
| M-1052 | The six unit rows of [int §7.6.3](../../design/int/int.md#763-slot-layout-identity-act-1052) | A, module, `dev`(`src/`) | Each RED before the key change |
| O-1052 | Warm exemplar start before and after | O, measurement, `dev`(`src/`) | Reported; a memo is added only on a material cost |

No new e2e cell: K-6's control already differs only in whether the slot
moves.

### 9.3 Raise-helper hardening (item 3)

| ID | Condition | Class, tier | Completion |
|---|---|---|---|
| M-P15 | The rewritten census counts production mentions of the panic symbol's name outside `raise`; a planted by-name declaration fails it and the clean tree passes | M, module, `dev`(backend) | Both legs in the change-set |

The handle is structural. The census covers its one residual and is blind
to a computed name, as [backend §7](../../design/backend/backend.md) states.

### 9.4 Principle 27 retirements (item 4)

| ID | Condition | Class, tier | Wrong outcome it rejects | Completion |
|---|---|---|---|---|
| T-D5 | The marginal halves of `tests/vec_set_owning_old_element.rs` and `tests/synthetic_accessor_input_release.rs` run armed and balance | F, e2e, existing | A value that is not a tracked allocation reaching the armed check | Green on the B1 tree, all thirteen. Both halves were already armed; no constructor is kept out of an armed half any longer |
| X-D5 | The three cells that read `stack_slot` leave with the mechanism: both `tests/s105_residual_attribution.rs` cells that assert its value, and the field-presence assertion in `tests/ownership_fences.rs` | M, `test` | An observer of a retired mechanism kept as a gate | Done (`f290a356`). The `tests/perf/s105_*.py` readers parse the ten-field line; their release measurements were not re-run |
| T-D4 | A one-word single-constructor ADT as a `Vec` element, a field of another ADT, a closure capture and the program result: values, REPL §1.5 display, and allocations equal to frees under the armed check, every mode | F, e2e | A consumer that still reads the word as the field: `(Box <address>)`, an unreleased result, a missing element function | Passes before D4 (no allocation) and after it (balanced) |
| T-D4-t | **Spec §4.12.2 item 3.** The same ADT as a traced call's argument: the frame's argument text is `(Box 2000)` and its result text `2001`, with T-D4's value and balance clauses, every mode. A small-payload leg, `(Box 3)`. Controls: a scalar argument and a two-field product | A, e2e | The trace formatter reading the word as a constructor tag (`<unknown-tag:3>`) or as an address (signal 11) | RED before B5 on ACT-1069 (closed): the `(Box 2000)` legs by signal, the small-payload leg on the text. Green at `441e31ea` with no other change (§14.2) |
| T-D7 | **R12's falsifier.** At the REPL, a function is redefined at the same language type with different inferred modes. It has two kinds of live dependent: a direct caller, and a function compiled before the replacement that takes the function as a value and calls it (REPL §18.1: calls and callable values that refer through the slot). The redefinition turn reports no error; later calls through both routes return the new body's values; the session balances under the armed check against a twin whose redefinition keeps its modes; a restart on the saved source agrees | A, e2e | Callers compiled against the old summary miscount after the patch; a value route that keeps the old body; restart differing from the session | RED today on the §18.1.2 rejection; green with D7 |
| T-D7-b | T-D7 for a generic realization and an impl method (§18.7) | A, e2e; the impl-method leg is F | A slot kind that keeps its own comparison | Generic: RED today, refused as `cannot rematerialize prior instance … changed the realization key or ABI`; green with D7. Impl method: passes on arrival and stays. Today's gate does not cover an impl method: the trace shows the summary move from `Borrowed` to `Owned`, the redefinition publishes and the session balances |
| X-D7 | `repl_redefinition::same_type_ownership_abi_change_is_rejected_before_slot_patch` is replaced by T-D7; `caller_free_type_change_publishes` stays. `cache::cache_restored_sum_field_projection_keeps_ownership_abi` keeps its assertion and re-points its `// spec:` line from the removed REPL §18.1.2 to §18.1 | M, `test` | A `// spec:` anchor to a removed section: `spec_link_check.py` reports both today | With D7; the link check then reports none |

- **T-D7 fixture properties.** The pair must change modes: for example
  `(defn f [v] v)` to `(defn f [v] [1])` at `(Fn [(Vec Int)] (Vec Int))`.
  The cell asserts the premise from `CRANELISP_OWNERSHIP_TRACE` (the two
  summaries differ) before it asserts balance; a pair with equal modes
  proves nothing. A second leg runs moves off.
- **No cell holds a closure across the redefinition.** The REPL has no
  top-level value binding, so no value outlives the turn that made it and
  no legal session frees an old body under a live value. REPL §18.1's
  observable is the slot route, which the second dependent exercises.
- **Residual, not written: a member of a multi-signature family.** Awaiting
  the user's approval (§6).
  - *Observed today, one armed program:* a family whose one-argument member
    changes from `v` to `[1]` publishes, and its caller returns the new
    value.
  - *Why no cell:* the trace prints no summary for a family member, so the
    premise cannot be asserted, and the restart clause fails on ACT-1068
    whatever D7 does.
  - *What covers the risk:* row D7 removes the mode read from the types a
    slot comparison would need, which is a compile-time guard for every
    slot kind.
- **Spark density and the borrowed-sibling carrier** need no new condition:
  the default emission is byte-identical (golden lane), and a pre-bump
  cache record is a miss (existing version cell). `test` removes any cell
  that sets `CRANELISP_SPARK_DENSITY_*` or `CRANELISP_NO_STACK_ALLOC`; none
  is in `tests/*.rs` today.

### 9.5 Frontend and the entry carrier (item 5)

| ID | Condition | Class, tier | Wrong outcome it rejects | Completion |
|---|---|---|---|---|
| T-D3 | The committed REDs of ACT-0997, ACT-1055, ACT-1056 and ACT-1057, with REPRO-R1, REPRO-R3 and T-R2-a to T-R2-c (§3.5) | A, e2e, existing and §3.5 | §3.5 | Green, unchanged |
| T-SUP | `(export [super [x]])` in a child module re-exports the parent's `x`; `super` in a root module is a located error for `import` and for `export` | A, e2e | `super` rewritten for imports only | RED on the export leg today (`test` confirms), green with D3 |
| T-DUP | `(import [m [Shade.Blue Shade.*]])` binds `Blue` once and it is usable; the twin `[Shade.*]` behaves the same; `[Shade.Blue]` alone binds `Blue` and not `Shade.Blue` | A, e2e | The two projections binding different local spellings for one member; an ambiguity raised between them | Green with D3 |
| T-MNT-a | A mount alias equal to a declared child is refused, located at the spec, with the `mod` form before and after the `export` | A, e2e | A check that depends on form order | Green with D3 |
| T-MNT-b | A second mount of one alias to a different target is refused in the same form, a later form and a later REPL turn; the same target twice is accepted | A, e2e | A per-form check; a refusal of an idempotent mount | Green with D3 |
| T-REG | A renamed entry, a dotted entry, a member glob and a mounted export each survive a REPL session's regeneration and a cold restart with the same bindings | A, e2e | Regeneration writing `local` as `source`, or dropping a mount | Green with D3 |
| T-Q4-a | **Equal targets, one public route** (§8.4.4, S124-Q4). `p` declares `(import [(lib s) []])` and `(export [(lib s) [x]])`. Inside `p`, `(s/y)` resolves; from an importer of `p`, `(p.s/y)` resolves; in both declaration orders, and after a cached restart | A, e2e | The later writer replacing the entry, so the import hides the mount in one order; a refusal of the equal pair; a restore that reads the families in the other order | RED today (mounts are rejected at parse), green with D3 |
| T-Q4-b | **Different targets refuse.** The import alias targets `lib1` and the mount `lib2`, whose `y` return 1 and 2. Refused in both orders and across two REPL turns, located at the second declaration | A, e2e | A silent reroute: the program runs and returns the other module's value | RED today, green with D3 |
| T-EXP0 | `(export [m []])` is a no-op that loads nothing: with an `m.cl` that does not compile, the program runs. Control: `m` compiles | A, e2e | Loading `m`; rejecting the form as vacuous | RED today (`m`'s error is reported), green with D3 |
| T-ALIAS | Two import aliases binding one spelling to different modules are refused, in one file and across two REPL turns (§8.6.4). Control: distinct aliases | A, e2e | The later alias replacing the earlier | RED today: `(z/v)` returns the second module's value. Green with D3, whose mount writer depends on this refusal |
| T-D10 | Impl identity under a rename (row D10; ACT-0997). `(import [lib [(Box B)]])` with `(impl Show B …)`, and a renamed trait import with an impl of it; each followed by a later definition, then a cold restart: the file holds the impl as written and the restart values agree | A, e2e | A label taken from the settled names on one route and from the written head on another, which refuses every later regeneration | RED today (renames are rejected at parse), green with D3 and D10. REPRO-1064 (§3.7) is the same carrier's second falsifier |
| R3-risk | A reader that rejects `->3`, `+*1` and `-*1` still reads `-3`, `+3`, `-`, `->`, `+=` and `(-> x f)` | F, e2e, added to REPRO-R3's controls | A digit rule applied to a sign followed by a digit | Passes before and after |
| M-FE | [Frontend modules §5](../../design/frontend/modules.md#5-unit-scenarios) rows, the reader's one operator tail, the `defmacro` shapes, T5 and T6 | A, module, `dev` | — | With each change-set |

- **`->3` as a risk to existing source: measured at zero.** No file under
  `stdlib/`, `examples/`, `exemplar/`, `user/`, `repl/`, `platforms/` or
  `tests/fixtures/` holds a signed operator run followed by a digit. A
  one-off scan, not an instrument; R3-risk is the standing control.
- **Not allocated:** the same alias bound twice to one module by two
  imports. §8.6.4 does not say whether the repetition is an error, and
  int §6.13 treats a repeated mount as idempotent; no cell asserts either
  outcome for imports.
- **File and trace for the rows added by S124-Q4:** `tests/spec_08_modules.rs`,
  `// spec: spec/08-modules.md §8.4.4` (T-ALIAS: `§8.6.4`). T-ALIAS carries
  `class=silent-accept`, `locus=src/imports.rs` import-alias writer,
  `found=S122`, `owner=/dev`.
- **Audit R4 and R5** change no behaviour. Their evidence is `dev`'s gate
  and the golden lane.

### 9.6 Get to green (item 7)

| ID | Filing | Condition | Class, tier | Completion |
|---|---|---|---|---|
| T-1038-a | ACT-1038 | `(trace (fib 12))` with sparks enabled records the same frame count as with `CRANELISP_NO_LENIENT=1`, **and** `[SPARK_STATS]` shows `trace_declines` greater than zero; the untraced twin shows spawns greater than zero and `trace_declines` zero | A, e2e, replaces the two committed REDs | RED today (the field is absent and frames are lost), green with rule 1 |
| T-1038-b | ACT-1038 | Traced against untraced `fib 12`, sparks enabled: marginal balance | A, e2e | as above |
| O-1038 | ACT-1038 | A lenient binding created outside a trace and forced inside it: frame count over repeated runs | O, e2e, reported not asserted | The distribution is recorded; see §12 |
| M-1038 | ACT-1038 | [Trace runtime §5](../../design/intrinsics/trace-runtime.md#5-evidence) rows, each flipped by removing its check; the backend row for a trace-form site emitting the gate | A, module, `dev` | With D8's change-sets |
| T-1039 | ACT-1039 | The committed all-modes cell, plus an imported-module leg (5 frames today) | A, e2e | `--run` leg RED then green; the imported leg is the control |
| T-1039-w | ACT-1039 | The imported-module program invoked twice in one directory records the same frames on the second invocation, every mode. Control: the second invocation with `--no-cache` under `--run` and the REPL; under `--link`, which must refuse `--no-cache` (`repl/spec/00-cli-invocation.md` §0.6), the cell's own cold first invocation | A, e2e | RED today: the second invocation records no frame in `--run`, `--link` and the REPL. The `--link` leg is run-dependent, as the failing-set section below records. Green with B10 |
| T-0973 | ACT-0973 | The two committed guards; a nested and a root-level child each refuse in every mode; the entry placement loads; a non-entry module importing `platform.<name>` works | A, e2e | Green |
| T-0973-c | ACT-0973 | A module cached as an entry, then imported as a dependency, refuses and does not restore | A, e2e | RED today: with the platform found on both invocations the cached module is restored and the program exits 0 (the committed cells fail on this). Green with ACT-0973's correction |
| T-1016 | ACT-1016 | The three committed guards and the acyclic re-export control | A, e2e, existing | Green |
| T-0985 | ACT-0985 | The committed cell with the implementation-first control | A, e2e, existing | Green |
| T-1001 | ACT-1001 | `impl_ambiguous_trait_names_both_candidates_neg` with `impl_unknown_trait_diagnostic_control` | A, e2e, existing | Green |
| T-1036 | ACT-1036 | The committed cell and REPRO-0915-loc (§3.4) | A, e2e | Green |
| T-Q8 | S124-Q8, row D12 | An entry file that exists and defines no `main`, under `--run` and `--link`, with definitions and empty: non-zero exit; one stderr line that begins `<file>: error: module error: ` and names `main`; no `0..0`, no line-and-column position after the file name, and no `codegen error`. Controls: T-1036 and REPRO-0915-loc's three subjects (§3.4), where a `main` exists and keeps its location | A, e2e | RED today (`p.cl:1:1: error: codegen error at 0..0: entry module has no 'main' function`, both modes), green with the one-producer gate |
| T-1061 | ACT-1061 | §3.6, with both `user_samples` tests | A, e2e; M for `user_samples` | Green; O-1061 recorded |
| T-Q9-a | S124-Q9 | **Spec §10.6: a trait method named `main` does not define `main`.** An entry whose only `main` is a method of `(deftrait Entry (main [self] (IO Int)))`, with an `Int` implementation: T-Q8's clauses, `--run` and `--link`. Control: the same file with `(defn main [] (Pure 5))` in place of the trait and its impl exits 5 | A, e2e | RED today on the position (`p.cl:1:1: error: codegen error at 0..0: entry module has no 'main' function`), green with the one-producer gate |
| T-Q9-b | S124-Q9 | **Spec §10.6: a multi-arity `main` is refused.** `(defn main ([] (Pure 7)) ([x] (Pure x)))` on line 3: non-zero exit that is not 7; the diagnostic is located on line 3 with no `0..0`. `--run` and `--link`. Control: the zero-argument clause alone exits 7 | A, e2e | RED today on the location (`p.cl:1:1: error: codegen error at 0..0: 'main' in entry module is not a function definition`), green with ACT-1036's correction |
| O-1018 | ACT-1018 | Re-measure the warm solve after ACT-1050 lands | O, measurement, `qa` | The guard passes, or it carries on the measured residual with its number. It reads 2 at `8667a868`, after ACT-1050's correction, and 2 at `84719eb6`, after the close; it carries on that number (§14.4) |

- **T-1038 replaces its predecessors' premise.** The committed cells
  require that a worker ran a traced call. Rule 1 makes that permanently
  false, as the filing's reallocation trigger anticipated. `trace_declines`
  is the positive signal that separates the correction from an absence of
  sparking. The two sparks-disabled controls stay.
- **T-Q8 rejects** a refusal that keeps a position, one that drops its
  category with it (REPL §5.1 item 1; row D12 as approved), and a category
  that names a compiler stage (REPL §5.5). The file is displayed by the
  formatter's rule, so the fixture runs in the entry's directory and the
  cell matches the file name.
- **A `main` that is not a function** has a form, so REPL §5.5 requires
  its location: REPRO-0915-loc's `defmacro` leg (§3.4).
- **T-Q9-a rejects** a gate that reads a bare `main` through typecheck's
  resolution, which answers the method, and then runs or locates it.
- **T-Q9-b rejects** selecting the zero-argument clause and running it
  (exit 7), and a refusal located at `1:1`. It takes the located refusal
  because the entry binds a `main` that has a written form
  ([io-integration §1](../../design/int/io-integration.md#1-running-a-program));
  spec §10.6 does not name its category, so the cell asserts none.

### 9.7 Repository and instrument conditions

| ID | Condition | Class | Owner |
|---|---|---|---|
| M-W0 | The document checker exits 0 and `citation_drift` passes on the converged package | M | `sprint`, W0 |
| M-API | `public_api_relocations` passes against baselines regenerated once, at the Phase 5 checkpoint, under `cargo-public-api` 0.52 or later; each non-empty diff matches its approved row. Row D11 needs no other evidence: nothing emits either retired symbol | M | `dev`, `arch` |
| M-CACHE | Each `CACHE_SCHEMA_VERSION` bump (B5, B8, D3, ACT-1052) makes a prior record a miss | M, existing version cell | `dev` |
| M-LAY | The widened layout census rejects a planted offset constant outside its owner and passes the clean tree (row R10-9) | M, module | `dev`(intrinsics) |
| G-0 | `cargo nextest run --no-fail-fast` reports zero failures on a fresh build of the final tree, or each remaining RED is carried on recorded evidence | A, suite | `qa` at the Phase 5 exit |

## 10. Open questions and what they hold

One cell is held, by the last row.

| Question | State | Effect on evidence |
|---|---|---|
| Is a second limit, on the size of an instance's type, admitted? | **Ruled no** (user, 2026-11-17). The doubling shape is an accepted named risk | F-PR-3 is never written; the risk is in §12 |
| Does the depth limit count implementation instantiations or method instances? | **Settled:** implementation instantiations ([monomorphisation §3.10.3](../../design/typecheck/monomorphisation.md#3103-recursion-through-dispatch)) | T-DEPTH-c is released (§9.1) |
| Does a member that re-enters itself at its own implementation instantiation, at other method-level type variables, count toward the depth? | Queued for the user by `design`(typecheck), which counts it | None. No S124 cell has a member with method-level variables, where the two readings differ. A cell is allocated when it is ruled |
| What category does the multi-arity `main` refusal carry? | Queued for the user by `design`(int) | None. T-Q9-b asserts the location and no category |
| Are two `impl` forms for one `(trait, type)` pair in one cluster a replacement or an error? | With `spec`. §5.4.5 states replacement for an `impl` re-entered in a later input. The compiler accepts both forms and the later one dispatches | Holds the cell for [ACT-0985](../../sprints/actions/ACT-0985-typecheck-forward-reference-and-hkt-intake.md)'s remaining shape, where the earlier form's body uses an implementation declared after the later form |

- **Where the scribed text leaves the observation open,** beside the rows
  above. None holds a cell; each is returned to `spec` (§6).
  - *Whether a non-parametric implementation counts toward the depth.* The
    cells read it as not counting (fixture D). The design's behaviour
    conforms under either reading, because spec fixes a floor and not the
    limit.
  - *What "demanded" means for a REPL definition.* A turn that defines a
    concrete function whose body dispatches into a growing implementation
    demands the instance when it is compiled, by the design; a reader can
    take "demanded" to mean evaluated. F-PR's REPL leg uses an evaluating
    turn and holds under both. No cell asserts the definition turn.
  - *The multi-arity `main` refusal's category.* Spec §10.6 says it is
    refused and does not say as what. T-Q9-b asserts the location REPL
    §5.5 requires of a refusal about an existing `main`, and no category.

## 11. The traceability band

Read against the Phase 3 specifications as scribed on 2026-11-17. A cleared
row stays cleared until the evidence wave: `qa` restores each when `test`
returns its clause map and the cells have been read against the new prose.

**Edited in this pass.**

| Row | Edit | Why |
|---|---|---|
| Spec §3.10, the function-recursion bullet | Restored to `[Tested …]` on the fold canary, accepting direction only | Its text is the pre-S124 rule and the canary observes it. No committed cell rejects a polymorphic recursive call: T-FR |
| Spec §3.10, the heading | Still cleared; its former citation now sits on the bullet it observes | A child bullet is uncovered |
| Spec §3.10, the three implementation rows; §10.6, the two new rows; §9.2.1 | Still cleared; each tag now names its cells and carries a "was" clause | A bare `[Uncovered S124]` is not counted by `spec_coverage_reconcile.py`'s close gate. The gate now lists 23 cleared rows, from 16 |
| Spec §10.6, the heading | Still cleared; the former cell is recorded as evidence of the `IO _` return requirement only | The new rows and the arity refusal are uncovered |
| REPL §5.1, item 2 and the heading | Still cleared; the tag records that `type_error_arg_mismatch` asserts no location | The former citation never evidenced the item |

**Edited at the W1 exit.**

| Row | Edit | Why |
|---|---|---|
| Spec §3.10, the function-recursion bullet | Raised to `[Tested+Neg …]` on the fold canary and three T-FR cells | T-FR passes in every mode: a growing recursive call and a second instantiation are both refused |
| REPL §15.4, the heading | Names rule 1's nonconformance for a multi-signature function | ACT-1068. Rule 1's own citations stand: they observe the forms they name |

**Restored when.**

| Row | Restored when |
|---|---|
| Spec §4.12, §4.12.2 | T-1038-a, T-1038-b and T-1039 are green |
| Spec §12.4.3, appendix C.3.1 | The existing cells are re-read for the outside-trace rule and T-1038-a covers the exception |
| Spec §9.2.1 | REPRO-R1 with its two S124-Q2 controls is green |
| Spec §9.9.1 | T-Q3 and the tightened committed cell are green |
| Spec §8.4.4 | The three committed mount cells, T-MNT-a, T-MNT-b, T-Q4-a, T-Q4-b and T-EXP0 are green |
| Spec §8.6.4 | T-ALIAS, T-MNT-b and T-Q4-b are green; the five former cells still observe the unchanged candidate rules |
| REPL §14.2, the `/sh` sentence | T-1061 is green and O-1061 is recorded |
| REPL §15.4 rule 2 and the authorship note | Carried with ACT-1005: REPRO-1005-b is RED until that correction. F-1005-d covers only the macro exception. The note's `begin` cells are restored to it with rule 2 |
| REPL §18.1 and its first bullet, §18.7 | T-D7 and T-D7-b are green |
| Spec §3.10, the implementation re-entry row | T-Q7-a to T-Q7-d are green |
| Spec §3.10, the depth-limit row | T-DEPTH-a, T-DEPTH-c, F-PR and F-PR-2 are green; F-PR-4 when constructible |
| Spec §3.10, the reporting row | F-PR is green in its batch legs, its no-caller control and its REPL leg |
| Spec §3.10, the heading | Not restored while a child bullet is uncovered (candidate filtering has been since S121) |
| Spec §10.6, the two new rows | T-Q9-a; T-Q9-b |
| Spec §10.6, the heading | Its rows, REPRO-0915-loc's arity leg and the committed return-type cell are green |
| REPL §5.1 item 2 and the heading | T-Q8 is green for the exception and for item 1's category, and a cell that reads a position is cited for the rule: REPRO-0915-loc's subjects qualify |
| REPL §5.5, the heading | T-1036, REPRO-0915-loc with its two added legs, T-Q8 and T-Q9-a are green. It stays partial while FIXME 0915's prefix and subject faces are open (§4.4) |

REPL §1.5's rows kept their citations; the cited cells assert display only,
which is what the amended prose requires. A row still cleared at close is
carried by name; REPL §15.4 rule 2 is expected to be one.

## 12. Readiness for the Phase 3 to 4 checkpoint

**Ready, with two conditions.** Every question ruled by 2026-11-17 is
allocated: S124-Q7 as re-ruled B with its depth limit and reporting rule,
S124-Q8, S124-Q9, row D12, and ACT-1063 and ACT-1065 in scope.

- **The evidence wave ran and is accepted** (§14).
- **Testable.** Every in-scope change has a condition with an observation
  seam that exists or is designed with its detection proof. No approved
  surface is unobservable. Every ruled question and approved row has its
  cells allocated in §2.3, §3 or §9.
- **Conditions on advancing.**
  1. *Order.* The evidence wave runs before row D1's step 1, with
     REPRO-1062 first.
  2. *The counting unit* is settled as the implementation instantiation
     (§10).
- **Not conditions.**
  - The type-size question is ruled: no second limit, and the doubling
    shape is an accepted named risk with no cell.
  - ACT-1067's correction is unscheduled. Its reproduction is RED from the
    evidence wave and is carried by `sprint`'s decision, like the rows of
    §3 marked "Carried".
- **ACT-1063 stays in scope.** Its correction is one surface: both wrapper
  rules are the backend's, and both readings agree no producer owes a
  carrier. The user's named-carry condition is not met. It would be if the
  wrapper rule were keyed on a lifecycle state that the binary's bootstrap
  must change ([int §16.0](../../design/int/int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21));
  the backend design keys it on the resolved entry instead.
- **Residual risks.**
  - *A wrong concrete type is invisible to every S124 instrument* (R18).
    ACT-1062 shows the class is live. After the close the remaining
    instances are the synthetic builder's `Int` placeholder and a defaulted
    constrained parameter. Accepted for S124 only as a named debt; the user
    should see it.
  - *A trace is not deterministic when it forces an IVar created outside
    it* ([trace runtime §4](../../design/intrinsics/trace-runtime.md#4-what-stays-concurrent-during-a-trace)).
    O-1038 measures it. Row D8's basis records it as a residual the row
    does not close.
  - *A cached restart can accept what its saved source rejects.* Observed
    once, as ACT-1064's crash. The trigger goes with that correction; no
    condition observes the cache record against the regenerated source by
    any other route.
  - *Several impl records under one authored label* are asserted
    impossible in row D10's basis, with its two reports as falsifier.
    REPRO-1064 and T-D10 cover the two shapes known to separate the keys.
  - *The census zero is a property of the suite's programs.* A program
    outside the corpus can still reach a refusal the close added. The
    refusal is located, so the face is a compile error, not corruption.
  - *T-D7 covers the shapes it enumerates.* A mode-dependent read in a slot
    kind not listed in T-D7-b would pass unobserved; the types removal
    (row D7) makes such a read fail to compile, which is the stronger
    guard.
  - *The chain refuses some terminating programs,* those whose chain is
    deeper than 64. Spec §3.10 admits it. No such program is known; Q7-S
    reads the suite, the standard library, the examples and the exemplar
    on the T4 tree, and the face is a located type error.
  - *A re-entry whose type grows exponentially is not refused in bounded
    time* by the depth limit (`design`(typecheck), by analysis). After T4
    the face is a compiler that exhausts memory or time on a program the
    specification refuses; before T4 it is today's codegen refusal. No
    cell observes it. Accepted by the user on 2026-11-17; its falsifier is
    a non-contrived program that reaches it.
  - *A chain of 64 mints may not fit the compile worker's stack.* Not
    observed; ACT-1067 shows the stack is exhausted by 56 nested source
    forms in the debug build. T-DEPTH-a observes it after T4.
  - *The compiler aborts on a deeply nested expression* (ACT-1067). A
    signal with no location, in both build profiles at different depths;
    correction unscheduled.
  - *A non-terminating instantiation is found only when a root demands
    it.* An implementation that cannot be instantiated finitely is
    accepted until it is used, in a later REPL turn or by an importer.
    This follows the ruling ("no impl-body check is added"); F-PR's REPL
    leg observes it.
  - *F-PR's wording is not asserted.* Any type error at the inner call's
    line passes its category clause. The cell's fixture is otherwise
    well-typed (its no-caller control), which bounds the confusion.
  - *The trace formatter and the result display are separate renderers.*
    ACT-1069 found them disagreeing on a one-word ADT. D4 removes that
    representation; no condition compares the two renderers on other
    shapes.
  - *A primitive's direct call and its function-value wrapper are separate
    lowerings.* REPRO-1063 found them disagreeing. The backend design
    gives each host-promised primitive one lowering; no condition compares
    the two routes for slot-carrying primitives.
  - *The bind-chain pass's peer-cycle assertion has no observation* (§3.8).
    No legal program reaches it, so its harm is bounded to a refused
    program's diagnostics.
  - *`--link` was not probed* for §3.6 to §3.8, §3.10, §3.11, §8.1's
    siblings, §8.3 or the cells added in the closing pass; the cells run
    it.

## 13. What the later passes ran

No `cargo nextest` run and no build in any: no source changed since §1's
run. All probes are of `target/debug/cranelisp` in scratch directories.

- **Second pass, 2026-11-16.** Twelve programs for §8.1 with
  `CRANELISP_RC_STATS`, two linked and disassembled with `objdump`; nine for
  §8.2 in `--run`, with the `P` pair also linked and at the REPL, and
  `CRANELISP_CODEGEN_DUMP` for the seam; two for §8.3; four for §8.4. Two
  source scans: parameter order against field order across the corpus, and
  signed operator runs followed by a digit.
- **Third pass, 2026-11-17.** Nine programs for §3.8, three on `poll-pool`;
  seven sessions for §3.7; three programs for §3.9; three sessions for §3.6,
  the subject three times; eight for the ruled questions (§3.3, §3.5, §9.5).
- **Fourth pass, 2026-11-17.** Twenty-one programs and four REPL sessions
  for §3.9, two linked; twelve for §3.10; five on `poll-pool` for
  REPRO-1065-e; six module trees for T-1065-f and the two cycle shapes;
  twenty for §2.3's same-instantiation cells and the §3.10 shapes of §9.1
  and §10, three with `CRANELISP_OWNERSHIP_TRACE`; three for T-Q8.
- **Fifth pass, 2026-11-17.** Twenty-two programs and one REPL session for
  §9.1's re-allocated cells (the direct, sibling, helper, two-implementation,
  growing and doubling shapes, and the function twins); six programs for
  the `main` refusals of §3.4, §9.6 and §10, one also linked; the ACT-1066
  subject under `CRANELISP_NO_STACK_ALLOC`, with `CRANELISP_CODEGEN_DUMP`
  for the placement and once on `target/release/cranelisp` (built
  2026-11-15; its commit was not checked).
- **Closing pass, 2026-11-17.** Forty-three programs under `--run`, four
  of them on `target/release/cranelisp`: the nesting-depth subjects and
  controls of §3.11, one with `RUST_MIN_STACK`; fixture D by nested
  constructors at 1, 2, 3, 8, 16, 32 and 64 levels and by a `let` chain at
  1, 2, 64 and 65; one each for T-Q9-a and T-Q9-b.
  `spec_coverage_reconcile.py` and `spec_link_check.py` before and after
  the band edits. The T-DEPTH-c shape, the definition-turn demand and the
  doubling shape were not run: each is a reading.
- Counts are single runs unless a row gives a rate. Every §8.2 subject
  failed on each of its runs.

## 14. The evidence after wave W5

**W5's exit is accepted.** The retain and release paths take a concrete
type and the non-concrete arms are deleted; the census reads zero from every
program on the tree that holds both B4 and B5; ACT-1069's and ACT-1072's
cells pass and both filings are closed; ACT-1018 is re-measured at 2. Two
tests fail on fixtures that B5 made stale, and `test` owes their update
(§14.3). One defect was found at this exit and it is memory-unsafe
([ACT-1076](../../sprints/actions/ACT-1076-trait-dispatch-selects-on-the-first-argument-not-the-self-position-intake.md)).
It predates S124 and is not W5's.

- **Read against:** `main` at `84719eb6`. `test`'s `1ce19145`, `de60dc3c`
  and `84719eb6`; `dev`'s `951622cf`, `240b3a8a`, `152a0def`, `1d965ed5`
  and `441e31ea`; the design commits between them.
- **What `qa` ran**, in the primary harness on the debug build of
  `84719eb6`:
  - the full suite with the census variable set (7,609 run, 192 failed);
  - the backend's 521 module tests alone under the census, and typecheck's
    996 module tests;
  - the four run-dependent cells of §14.1 alone;
  - scratch programs for ACT-1076, ACT-1077, the `Copy` classification
    (§14.6) and the pre-B5 constructor frame (§14.7), with the release build
    of 00:11 on 2026-11-18 (the W2 tree) as the control for "predates W3".
- **Limits.** The B4 tree's full run and census were `dev`'s; `qa` compared
  their failing sets by name and did not repeat them. `review`'s findings on
  B4, B4′ and B5 were read as reported by the coordinator.

### 14.1 The failing set at `84719eb6`

| Class | Count | Traces to |
|---|---|---|
| Opening filed guards | 26 | §1 |
| S124 cells failing on their row's assertion, or by the signal their row names | 162 | The filings and approved rows below |
| `citation_drift::project_documents_conform_to_the_checked_in_declaration` | 1 | Maintenance check (§6, `sprint` item 4) |
| `public_api_relocations::public_api_check_runs_against_all_seven_crates` | 1 | Maintenance check (M-API). Its drift is three removals, all approved: `HeapCategory::Value` (row D4) and the two stack-slot counters (row D5). It clears when the baselines are regenerated at the Phase 5 checkpoint |
| `clif_golden_lane::clif_golden_lane_no_drift` | 1 | Maintenance check on a stale baseline. Both differing frames are attributed to B5 (§14.3 item 1) |
| `ownership_reuse::r5_value_flatten_rc_inc_collapses_vs_two_ctor` | 1 | A witness of the optimisation row D4 retires (§14.3 item 2) |
| Anything else | 0 | No genuine regression |

- **Change from W4 (194):** ACT-1072's three subject cells and ACT-1069's
  six pass; ACT-1075's six new subject cells fail as allocated; the two
  stale fixtures above fail; one run-dependent cell passed in this run.
- **Run-dependent members.** A pass in a loaded run is not a correction,
  and each of these stays a guard. The table gives each cell's result in
  the full runs of 2026-11-18 on the B4, B5 and HEAD trees, and alone.

| Cell | In full runs | Alone | Cause | Counted above |
|---|---|---|---|---|
| `spec_07_traits::s124_1070_jit_call_range_subject` | fails in each | fails, about three runs in ten | [ACT-1070](../../sprints/actions/ACT-1070-jit-direct-call-out-of-range-of-allocator-placed-code-intake.md) | yes |
| `spec_07_traits::s124_two_member_depth_64_run` | passed in all three; failed in three earlier runs | passes | ACT-1070: one run of the program the sixteen-run cell repeats | no |
| `spec_07_traits::s124_1070_jit_call_range_arena_control` | failed once (B5 tree) | passes in 8 s | The harness's 30 s child limit: sixteen concurrent compiles on one allocator arena, under the suite's load. No child reported a result. Returned to `test` (§14.3 item 4) | no |
| `trace::s124_1039_w_subject_link` | failed once (B4 tree) | fails, each run | [ACT-1039](../../sprints/actions/ACT-1039-run-mode-trace-omits-user-functions-intake.md) | no |
| `repl_watch::s124_1061_watched_save_control` | failed once (a run between B4 and B5) and in two W2-tree runs | passes | [ACT-1061](../../sprints/actions/ACT-1061-sh-save-notice-arrives-after-the-next-prompt-intake.md)'s late face: the report followed the next prompt. It is a subject of that filing, not a control (§14.3 item 3) | no |
| `cache::cache_restored_text_after_abi_change_preserves_importer_calls_across_modes` | fails in each | — | ACT-1052 | yes, among the 26 |
| `user_samples::user_documentation_samples_match_the_compiler` | passes in each | — | ACT-1061 (§5.1) | no |

The 162, by filing or approved row:

| Traces to | Cells | Opening guards of the same filing |
|---|---|---|
| ACT-1063 | 38 | — |
| ACT-1056 | 17 | 6 |
| ACT-1036 | 10 | 1 |
| ACT-0997 | 9 | 2 |
| ACT-1075 (six subject legs and T-1065-f) | 9 | — |
| ACT-1057 | 8 | 5 |
| Row D3, the S124-Q4 and module conditions (T-SUP, T-EXP0, T-ALIAS) | 8 | — |
| ACT-0973 | 7 | 2 |
| ACT-1071 | 7 | — |
| ACT-1005 | 6 | — |
| ACT-1074 | 6 | — |
| Row D12, S124-Q8 and Q9 (T-Q8, T-Q9-a) | 6 | — |
| ACT-1055 | 4 | 2 |
| ACT-1062 (REPRO-1062-e, REPRO-1062-f) | 4 | — |
| ACT-1068 | 4 | — |
| ACT-0977 | 3 | — |
| ACT-1059 | 3 | — |
| ACT-1039 (T-1039-w) | 2 | 1 |
| ACT-1064 | 2 | — |
| ACT-1067 | 2 | — |
| ACT-1073 | 2 | — |
| Row D7 (T-D7, T-D7-b) | 2 | — |
| ACT-0981 | 1 | — |
| ACT-1061 | 1 | — |
| ACT-1070 | 1 | — |

The other opening guards are ACT-1016 (3), ACT-1038 (2), ACT-1018 and
ACT-1052 (1 each).

### 14.2 Row groups

"Accepted" means every RED leg was read failing on the row's assertion and
every control and fence passed in the full run. "Accepted green" means the
row's cells were RED on their assertion before the correction and pass in
`qa`'s full run with no change made to them.

| Rows | Judgment | Note for the correcting wave |
|---|---|---|
| T-D4-t, with its small-payload leg and two controls | Accepted green | W5. Six subject cells failed on the B4 tree and pass on the B5 tree; the cells are unchanged since `f4003ad7`. ACT-1069 is closed |
| T-D4 | Green before and after B5, as its row requires | T-D4 and T-D4-t are 24 cells; allocations equal frees under the armed check |
| ACT-1072: 65 sibling members, the 64-member and parameter-order controls | Accepted green | W5. Its module row and the three module rows returned at W4 are in `951622cf` and pass. ACT-1072 is closed |
| ACT-1075: the call and value subjects, the one-candidate and monomorphic controls | Accepted | Six legs RED on `undefined function`, or on the missing instance for the value legs; six control legs pass |
| T-1065-f | RED on ACT-1075 | Its trace locus is §14.3 item 5 |
| REPRO-1062-a to d, M-1062 | Green | 35 cells of the file pass |
| REPRO-1062-e, REPRO-1062-f | Accepted, still RED | Four legs RED on a signal before any clause. No correction is scheduled (§14.4) |
| The twelve ACT-1050 guards, T-1050-a, REPRO-1065-a to c and e | Green | ACT-1065 stays open for T-1065-d (W7) |
| ACT-1071: subject, dispatching and back-edge legs; two controls | Accepted | Seven legs RED: `--run` and the REPL on signal 11, the back-edge `--link` leg at the linker |
| ACT-1070: the sixteen-run cell and its arena control | Accepted | RED by signal 11 or the JIT's assertion on some of sixteen runs. aarch64 Linux only. The control's limit is §14.3 item 4 |
| ACT-1073: the refused two-implementation `begin` | Accepted | RED on `codegen error` where a type error is required. The saving and recovery clauses behind it have not executed |
| ACT-1074: both declaration orders | Accepted | RED on `no overloaded function`; the free-function and earlier-turn controls pass |
| T-1039-w | Accepted | W6. RED on zero frames at the second invocation. `--link` has no `--no-cache` control (§9.6) and its leg is run-dependent (§14.1) |
| REPRO-1068 | Accepted | Four legs RED on the family missing from the saved source; the restart clauses behind it have not executed. Unscheduled |
| T-1001, T-0985, T-1034-a to e, T-Q7-a to d, F-PR, F-PR-2, F-PR-4, T-DEPTH-a to c | Green | Corrected at W3 |
| T-FR, F-0975, F-0934, REPRO-1066, T-D5 | Green, standing fences | They stay green through every wave |
| REPRO-1064, REPRO-1005-a to c, F-1005-d | Accepted | Each subject stops at its first assertion; the restart values run only once that passes |
| REPRO-1063, REPRO-1063-p | Accepted | W6, row B12 |
| REPRO-0977, REPRO-0981, REPRO-1067 | Accepted | Carried RED past S124. REPRO-0981 has no impl-method twin (§3.2) |
| REPRO-R1 with the S124-Q2 controls, T-Q3, REPRO-R3, R3-risk, T-R2-a to c | Accepted | W7 |
| T-1061, REPRO-0915-loc, T-Q8, T-Q9-a, T-Q9-b, T-D7, T-D7-b | Accepted | W8 |
| T-1038-a, T-1038-b | Accepted | W6. T-1038-a's frame-count clause is run-dependent; the cell is RED either way until rule 1 |
| T-1039, T-0973, T-0973-c, T-1016, T-1036 | Accepted | T-0973-c is RED on the missing refusal after a cache hit |
| T-SUP, T-DUP, T-EXP0, T-ALIAS | Accepted | W7 |
| T-MNT-a, T-MNT-b, T-Q4-a, T-Q4-b, T-D10, and T-REG's rename, dotted and mount legs | Accepted as RED on the parser's refusal only | W7. `qa` reads their remaining clauses on the first tree whose parser accepts the forms, before W7 is accepted |

No module row is returned to `dev` from W5.

### 14.3 Returned to `test`

Nothing is returned for a RED that fails on setup. The handoff, in order:

| Order | Item | Expected on arrival |
|---|---|---|
| 1 | **Golden lane, entry `07_trait_dispatch`: re-baseline the two remaining frames, attributed to B5 (`441e31ea`).** `user::main` constructs `(MkBox 5)` on the heap where it passed the bare word. `user::Sizeable.size$user/Tag` differs in one line, the colocated function index of its drop glue (43 to 44), because the `Box` frame's glue now takes index 43. Both are inside the design's acceptance rule ([ownership codegen §7](../../design/backend/ownership-codegen.md#7-one-word-value-flattening--retired)): frames that handle a one-word value directly, and their glue. No other frame or entry | `clif_golden_lane_no_drift` passes |
| 2 | **X-D4: remove `ownership_reuse::r5_value_flatten_rc_inc_collapses_vs_two_ctor`** and the file header's lines for it. It asserts the collapse that row D4 retires. `r5_soundness_couple_unflattened_two_ctor_not_copy_moded` stays. The F2v fixture stays for `s99_fixtures.rs` | One test fewer; no RED in the file |
| 3 | **`repl_watch::s124_1061_watched_save_control`** is a subject of ACT-1061's late face, not a control. Add T-1061's `// defect:` line and name it a subject. The assertion does not change | Unchanged result |
| 4 | **`spec_07_traits::s124_1070_jit_call_range_arena_control`**: a control must report under the suite's load. Give its children a limit that sixteen concurrent single-arena compiles meet in a full run, or run the cell in a serial test group. The subject keeps the same shape as the control | Passes in a full run |
| 5 | **Trace lines, no assertion changes.** The nine ACT-1075 cells (six subject legs, three T-1065-f): `locus=crates/cranelisp-typecheck/src/program/mono_collect.rs::collect_mono_call_sites`. The six T-D4-t subject cells: `fixed=S124/441e31ea`. The three ACT-1072 subject cells: add the `// defect:` line, `class=wrong-reject`, `locus=crates/cranelisp-typecheck/src/traits/monomorphise.rs::receiver_in` (the seam the correction removed), `found=S124`, `owner=/dev`, `fixed=S124/951622cf` | Unchanged results | <!-- doc-check: literal reason="Trace-line loci, including a seam the correction removed" -->
| 6 | **ACT-1076**: subjects A to E with controls A, C and D, every mode (the filing holds the fixtures) | Subject C RED on signal 11; B on the value; A, D and E on the refusal text |
| 7 | **ACT-1077**: the `bind` subject and `then` control beside REPRO-0981 | RED on the serial regime |
| 8, with their corrections | T-1063-b (W6), T-1065-d (W7), X-D7 (W8) | As §9 states |

O-1038 and O-1061 are `qa`'s readings on the corrected trees.

### 14.4 Residuals

- **Four defects end a legal program on a signal and have no correction
  scheduled:** ACT-1070, ACT-1071, ACT-1062's display and trace readers,
  and ACT-1076. A crash is not carried past the sprint without the user's
  decision (METHOD §2.5).
- **Three defects refuse a legal program and have no correction
  scheduled:** ACT-1073, ACT-1074 and ACT-1075. ACT-1076 has that face too.
- **ACT-1073's owner is still provisional.** Typecheck's module row now
  asserts that a refused cluster leaves no implementation registered, and
  passes, while the two REPL cells stay RED. `dev`(typecheck) probes which
  state survives the refusal before correcting it.
- **A multi-signature family's mode-changing redefinition has no cell**
  (§9.4). Awaiting the user's approval.
- **Clauses behind a first RED have not executed** for T-1038-a,
  REPRO-1064, REPRO-1068, ACT-1073's cell, T-1065-f and the mount and
  rename cells. Each wave's adequacy pass reads them when its correction
  lands.
- **ACT-1068 is unscheduled** and deletes authored source in every session
  that defines anything beside a multi-signature function.
- **ACT-1039 is wider than filed.** A traced callee restored from the cache
  is not recorded in any mode; T-1039-w is its cell.
- **ACT-1018 carries on a measured residual of 2** (O-1018, at `84719eb6`:
  14,872 allocations, 14,870 deallocations, the W4 numbers). No S124
  change-set owns it.
- **The bind-chain pass's import assertion has no evidence.** The design
  asserts that a cluster's imports are committed before the pass reads them.
  The module rows commit the imports in their own fixtures, so they show
  only what the pass does once an import is committed. The assertion is a
  debt with a named falsifier, T-1065-f, which executes once ACT-1075 is
  corrected.
- **ACT-1077** leaves an eligible pair sequential. Its harm is lost overlap.
- **The refusals the close added are reached by no program** (§14.5).
  `review` left one finding on the Vec glue refusal's synthetic span with
  `design`(backend). No independent evidence is owed for it: a module row
  asserts the span if the design requires a real one.
- **A proposed `cranelisp-types` change is held for the user's gate:**
  `CallableOrigin::TraitMethod` carrying its member, so the depth chain
  reaches a member by a settled key (`240b3a8a`). The chain recovers the
  member by mangling until then.
- **Suite readings from the Codex sandbox overstate the failing set** by
  thirteen tests that fail on the sandbox's port and timer limits. A
  reading that gates a wave is taken in the primary harness.

### 14.5 The category census

**The census reads zero from every program on the tree that holds step 2
and B5.** FIXME 0903's closure condition is met on `qa`'s reading; closing
the filing is `design`(backend)'s.

- **The instrument after step 2.** The retain and release points left with
  their arms. The absent, field and frame points remain, each with its
  planted positive leg and concrete twin in the backend's module tests.
- **CEN-4, the reading that licensed step 2** (`dev`'s full run at
  `8667a868`, recomputed by `qa` from its file): zero records from any
  program in all four partitions, each with frames. The absent arm in
  `Plain` fell from 600 records in 39 frames on the T4 tree to 0, which
  closes ACT-1050's attribution on the same suite.
- **CEN-5, the reading on the step 2 tree** (`dev`'s full run on the B4 tree
  with the variable set): the failing set equals the pre-B4 set by name,
  apart from the run-dependent members of §14.1, and the golden lane passed.
  No legal program met a refusal the close added.
- **The reading at `84719eb6`** (`qa`'s full run; 225,531 lines):

| Partition | Frames compiled | Distinct symbols | Records on an arm or a non-concrete field class, from a program |
|---|---|---|---|
| `Plain` | 142,234 | 3,468 | 0 |
| `TraitMethod` | 50,928 | 777 | 0 |
| `Ctor` | 30,892 | 863 | 0 |
| `Accessor` | 1,461 | 130 | 0 |

- **Sixteen records are not frames, and all sixteen are the backend's module
  fixtures.** Running the backend's 521 module tests alone under the census
  reproduces the same sixteen lines. Fifteen are the instrument's planted
  legs (frames named `census_…` and `test/fixture`). One is row D1's
  planted negative for a short declaration (`field`, `Plain`, class
  `concrete`, frame `f` in module `user`), which is on no arm. The hand-built lambda
  fixture that recorded on the absent arm at W4 has a typed node and records
  nothing.
- **The reading's conditions hold.**
  - Cache: every e2e program ran in a directory created inside the run.
  - Denominators: every partition compiled frames.
  - Population: the ACT-1034 cells, the ACT-1050 cells and
    REPRO-1062-a to d pass in the same run.
  - No failing test lacks a filing or an attributed fixture (§14.1).
- **What the zero does not cover.** A program that is refused before
  emission compiles no frame for the refused definition. The failing cells
  of ACT-1063, ACT-1056, ACT-1055, ACT-0997, ACT-1074, ACT-1075, ACT-1076
  and the module-form rows are of that kind. An untyped binder in one of
  them is now a located refusal, so the cell that asserts its value fails;
  the census keeps counting.
- **Still not licensed:** any claim about a concrete but wrong type (safety
  register R18). ACT-1062's remaining readers and ACT-1076 show it is live.

### 14.6 Value-flattening retirement (B5, row D4)

**Adequately evidenced.**

- **Structural.** `HeapCategory::Value` and every arm that named it are
  deleted in the backend and the binary. The public-API guard reports the
  one removal.
- **Red to green.** T-D4-t (§14.2).
- **Fences.** T-D4 passes before and after. The W0.b golden corpus passes
  on its attributed re-baseline (`84719eb6`); the L-B1 lane waits on §14.3
  item 1.
- **`Copy` no longer couples to emission.** Typecheck still classifies a
  one-word single-constructor type as `Copy`, and the design states that the
  backend reads no mode. `qa`'s control: one program that passes such a
  value through a recursive hold, a double read, a closure capture, an `if`
  join, a loop and a Vec, against a twin whose type has two `Int` fields.
  The two give the same value and the same `rc_inc`, `rc_dec`, allocation
  and free counts under the armed check, with ownership analysis on and
  off. A third twin with a `String` field balances.
- **Not kept.** The II-G1 collapse witness (§14.3 item 2). Flattening
  returns only with a release-tier lowering, which brings its own witness.

Stack-placement retirement (B1) stands as accepted at W2: REPRO-1066's
cells and T-D5 pass at `84719eb6`.

### 14.7 Defects and leads read at the W5 exit

| Filing | Defect | Entered | Face | Owner |
|---|---|---|---|---|
| [ACT-1076](../../sprints/actions/ACT-1076-trait-dispatch-selects-on-the-first-argument-not-the-self-position-intake.md) | A conventional trait method call selects its implementation from the first argument | Before S124 | Signal 11 or a wrong value when the first argument's type also has an implementation; otherwise a legal program refused. Every mode | typecheck |
| [ACT-1077](../../sprints/actions/ACT-1077-same-named-local-leaves-an-unrelated-bind-chain-sequential-intake.md) | A local named like `bind` or a platform function leaves an eligible chain elsewhere in its definition sequential | W4, with ACT-1065's correction; recorded in the design | Lost overlap | `src/` |
| [ACT-1075](../../sprints/actions/ACT-1075-polymorphic-candidate-selected-from-a-shared-spelling-is-undefined-at-codegen-intake.md), attribution settled | The monomorphisation collectors resolve the written spelling again where the selected identity is already recorded | Before W3 | A legal program refused with a codegen error, every mode | typecheck |

The defects found at the W3 and W4 exits are in their filings: ACT-1070,
ACT-1071, ACT-1062 (widened), ACT-1073, ACT-1074.

**A lead that is not a defect.** Before B5 the `07_trait_dispatch` golden
held a `Box.MkBox` frame that allocated, beside a `size$user/Box` frame that
read its argument as the bare word. The constructor frame was not reached by
a mismatched consumer: a `MkBox` called directly, through a `let`-bound
name and as an argument to a higher-order function each yield the field's
value on the W2 release build and on `84719eb6`. B5 removes the second
representation.

### 14.8 Corrections, in order

Whether ACT-1071, ACT-1073, ACT-1074, ACT-1075, ACT-1076 and ACT-1077 are
corrected in S124, how ACT-1070 is sized, whether ACT-1062's two readers
are pulled in, and ACT-1068's scheduling are the user's decisions and are
not assumed here.

**`dev`(typecheck)**, each after its RED is committed:

1. ACT-1076, with its module row at the dispatch seam.
2. ACT-1071, probing the seam first; if typecheck publishes the importing
   module's key, it returns to `qa` unattributed.
3. ACT-1075, with its module row at the collector.
4. ACT-1073, probing which state survives the refusal (§14.4).
5. ACT-1074.

**`dev`(backend):**

1. ACT-1070.
2. ACT-1062's descriptor baker, with row B10 in W6.

**`dev`(`src/`):** ACT-1062's display reader. It did not travel with B5's
display arm.

**`design`(backend):** close FIXME 0903 on §14.5; dispose of the review
finding on the Vec glue refusal's span.

**Stale rustdoc, comment-only.** `ownership/classify.rs` in
`cranelisp-typecheck` (`dev`(typecheck)) and `lib.rs`, `heap.rs` and
`mono_expr.rs` in `cranelisp-types` (`arch`) describe the deleted
`HeapCategory::Value` arm and `signature_heap_category` as live.

**Before the Phase 5 checkpoint:** ACT-1070, ACT-1071, ACT-1076 and
ACT-1062's two readers corrected, or the user's decision to carry a crash.
