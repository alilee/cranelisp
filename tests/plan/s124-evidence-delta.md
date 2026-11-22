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
> **Checkpoint:** `main` at `4b58ab93` for sections 1 to 13. Section 14 is
> read at `main` `128255fc`, where `qa` took the full run on 2026-11-22; a
> row that names an earlier commit was read there.
> **Scope:** sections 1 to 7 are intake, attribution and the reproductions
> that do not depend on the S124 designs. Sections 8 to 13 are the conditions for the S124
> corrections and the Phase 3 readiness judgment. Section 14 is the standing state
> of the evidence under the [delivery principles](../../sprints/METHOD.md#delivery-principles):
> the failing set by owning module, the focus module's exit list, the carry
> list, and what each role still owes.
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
| `user_samples`, both tests | 2 | Maintenance check, run-dependent | ACT-1061 (closed S124), §5.1. |

- **Stable failing set: 47.** The two `user_samples` tests are run-dependent
  and are named separately, under the
  [counting rule](PLAN.md#traceability-and-authoring). The opening run
  recorded 48 because only one of them failed in it.
- **No genuine regression.** Every failing test traces to an open record
  with an owner.

## 2. ACT-1034 — attribution

**Owner: typecheck. The REPL/batch difference is cluster shape, not mode.**
The filing is ACT-1034 (closed S124).

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

Observations and attribution: ACT-1064 (closed at S124; Git history).

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

Observations and attribution: ACT-1065 (closed at S124; Git history).
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

Observations and attribution: ACT-1063 (closed S124).
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
  ACT-1061 (closed S124).
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
| `dev`(`src/`) | ACT-1060's completion check is met at `8667a868`; the filing is `dev`'s to resolve. |
| `sprint` | (1) ACT-1068 needs a scheduling decision from the user: its correction is in no S124 row and it loses user data. (2) Suite readings are taken in the primary harness: thirteen tests fail only in the Codex sandbox (§14.4). (3) The overload leg of T-D7-b is a residual that needs the user's approval (§9.4). (4) The document gate fails, mostly on ignored-path findings whose disposal is with the user (§14.8); until it is decided no claim rests on that gate. (5) `tests/plan/spec_coverage_reconcile.py` counts a cleared row only when its tag has a "was" clause, so a new obligation tagged `[Uncovered S124]` alone is outside the close gate (§11). The repair is `qa`'s, with its detection test, and needs a pass that may run it. (6) Two questions are queued for the user and hold no cell (§10). (7) ACT-1067 is carried with its reproduction RED. (8) [ACT-1018](../../sprints/actions/ACT-1018-exemplar-warm-solve-residual-intake.md) has no correction in any S124 wave and ACT-1050's is predicted not to move it (§14.4): it needs a route or a recorded carry. |
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
ACT-1063 (closed S124).

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

**Edited at the W6 and W7 exit.** The close gate lists 14 cleared rows,
from 23.

| Row | Edit | Why |
|---|---|---|
| Spec §3.10, the three implementation rows | Restored on the T-Q7, T-DEPTH and F-PR cells | Green since W3. The two-member 64-level leg is cited under `--link`; its `--run` leg ends on ACT-1070 in some runs |
| Spec §8.4 (heading), §8.4.4, §8.6.4 | Restored on the mount, S124-Q4, T-EXP0 and T-ALIAS cells | Green with row D3. §8.4.4's tag names ACT-1079; §8.4's names T-SUP |
| Spec §9.2.1, §9.9.1 | Restored on REPRO-R1 with its controls, and T-Q3 | Green with ACT-1057's correction |
| Spec §12.4.3, appendix C.3.1 | Restored with the strict-trace cells added | T-1038-a covers the exception; the former cells observe the unchanged rule outside a trace |
| Spec §4.12.2 | Still cleared; its tag no longer states ACT-1038's and ACT-1069's defects | Both are corrected. Item 3 waits on ACT-1039 |

**Edited at the W8 exit.** The close gate lists 6 cleared rows, from 14.

| Row | Edit | Why |
|---|---|---|
| Spec §10.6, the heading and its two new rows | Restored on the committed return-type cell, the arity and missing-`main` cells, T-Q9-a and T-Q9-b | Green with `e294852f` |
| REPL §5.1, item 2 and the heading | Restored: three cells that read a position, and T-Q8's cells for the exception. The heading is `[Tested]`, the level of items 1 and 3 | Green with `e294852f` |
| REPL §5.5, the heading | Still cleared; its tag names the `discover-tests` refusal and FIXME 0915's two faces | REPRO-0915-loc's `discover-tests` leg is RED (ACT-1036) |
| REPL §14.2, the `/sh` sentence | Restored with the three T-1061 cells | Green with `b3e3887e`; O-1061 is recorded (§14.2) |
| REPL §18.1's first bullet | Restored with the four T-D7 cells for an ordinary function and a generic realization. The heading returns to `[Uncovered S121]`, its state before S124 | Green with row D7 |
| REPL §18.7 | The conformance paragraph cites T-D7-b's impl-method cells. The heading returns to `[S115]`, its state before S124 | Green with row D7 |

**Restored when.**

| Row | Restored when |
|---|---|
| Spec §4.12, §4.12.2 | T-1039 and T-1039-w are green (T-1038-a and T-1038-b are) |
| REPL §15.4 rule 2 and the authorship note | Carried with ACT-1005: REPRO-1005-b is RED until that correction. F-1005-d covers only the macro exception. The note's `begin` cells are restored to it with rule 2 |
| Spec §3.10, the heading | Not restored while a child bullet is uncovered (candidate filtering has been since S121) |
| REPL §5.5, the heading | REPRO-0915-loc's `discover-tests` leg is green (ACT-1036). It stays partial while FIXME 0915's prefix and subject faces are open (§4.4) |

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

<a id="14-the-standing-state-at-f8c55626"></a>

## 14. The standing state

**The full suite at `128255fc`: 8,109 run, 7,966 passed, 143 failed,
1 skipped, in 265 s. Every failing test traces to an open filing (§14.1).
None is attributed to the backend, this sprint's focus module, which meets
its three exit clauses (§14.9).**

- **Against the 119 at `11ea995e`:** 24 cells arrived RED, all allocated
  reproductions of the Phase 6b intake. No test that passed there fails
  here. No compiler source has changed between the two runs.
- **The category census, armed in this run, reads zero** from every
  program (§14.5).
- **No workspace crate raises a build warning.**
- **The public-API baseline check passes.** One maintenance check fails:
  the document gate, on 576 findings, none in a file `qa` owns (§14.1).
- **Every cleared band is judged.** Of the 108 rows the specification's
  rewrite cleared, 21 are restored and 87 state why they are not
  (§14.14). Seven older rows still await re-judgment.
- **Nothing is with `test`.**
- **What the sprint's evidence does not cover** is §14.13.

Open, by filing, worst first:

- [ACT-1089](../../sprints/actions/ACT-1089-type-command-given-a-definition-commits-it-without-code-intake.md), in `src/`, **memory-unsafe:** `/type` commits what
  it checks. A definition form, or an ordinary expression such as
  `(Some 1)`, makes a later call or evaluation end the process on signal
  11. Fourteen cells RED. Whether its expression face is carried or
  corrected before the sprint closes is with the user.
- [ACT-1106](../../sprints/actions/ACT-1106-effect-constructors-field-is-typed-as-the-io-value-and-holds-a-thunk-intake.md) (5 cells), [ACT-1105](../../sprints/actions/ACT-1105-qualified-primitives-bind-constructs-a-node-shorter-than-the-runtime-reads-intake.md) (1) and
  [ACT-1107](../../sprints/actions/ACT-1107-match-on-io-with-pure-and-effect-arms-is-accepted-and-fails-on-a-bind-node-intake.md) (2): the `IO` constructors, memory-unsafe in the
  first two. With [ACT-1108](../../sprints/actions/ACT-1108-io-is-not-opaque-pure-is-absent-and-the-constructors-are-surface-intake.md) (6 cells: `primitives/pure` is
  absent and `Pure` constructs) they are the opaque-`IO` ruling the
  compiler does not meet. Carried to the next sprint by the user's
  decision.
- [ACT-1102](../../sprints/actions/ACT-1102-refused-save-leaves-the-cache-ahead-of-the-backing-file-intake.md), in `src/`, **memory-unsafe:** a cached restart
  after a refused save. One cell RED. Carried by the user's decision.
- [ACT-1101](../../sprints/actions/ACT-1101-session-save-refused-after-a-parametric-product-type-is-constructed-intake.md), in `src/`, **data loss:** saves refused after a
  parametric product type is constructed. Three cells RED. Carried by the
  user's decision.
- [ACT-1103](../../sprints/actions/ACT-1103-trait-spelled-num-eq-ord-or-display-has-its-impl-body-replaced-by-a-primitive-intake.md) (6 cells) and [ACT-1104](../../sprints/actions/ACT-1104-built-in-vec-is-refused-as-an-implementation-target-intake.md) (3), in
  typecheck: a user trait named `Num`, `Eq`, `Ord` or `Display` is
  overridden by a primitive; no trait can be implemented for a vector
  type.
- [ACT-1096](../../sprints/actions/ACT-1096-declared-child-of-a-library-module-is-replaced-by-a-file-earlier-on-the-search-path-intake.md), in `src/`: a project file at a library child's
  path is loaded and indexed. Nine cells RED.
- [ACT-1109](../../sprints/actions/ACT-1109-function-and-nested-io-values-do-not-display-as-the-closure-and-io-markers-intake.md) (2 cells): the `#closure` and `#io` markers.
  [ACT-1110](../../sprints/actions/ACT-1110-an-unrecorded-trace-root-is-named-skipped-with-an-empty-result-intake.md): the unrecorded trace root, with no cell. Both
  carried.
- [ACT-1100](../../sprints/actions/ACT-1100-selective-derive-import-refusals-intake.md) (6 cells), [ACT-1099](../../sprints/actions/ACT-1099-type-command-refuses-an-expression-that-uses-a-macro-intake.md) (1),
  [ACT-1097](../../sprints/actions/ACT-1097-trait-signature-accepts-a-bare-primitive-type-name-that-is-not-imported-intake.md) (3), [ACT-1092](../../sprints/actions/ACT-1092-search-index-omits-a-module-whose-import-names-an-unloaded-or-compiling-module.md) (2), [ACT-1018](../../sprints/actions/ACT-1018-exemplar-warm-solve-residual-intake.md)
  (5, unattributed; the exemplar guard reads 2), [ACT-1090](../../sprints/actions/ACT-1090-commit-planning-validates-a-covered-member-against-a-table-copied-before-it-published-intake.md)
  (run-dependent; it failed in this run), and the filings of §14.1 from
  before Phase 6.

This section is the standing state under the
[delivery principles](../../sprints/METHOD.md#delivery-principles) (user,
2026-11-19):

| List | Where |
|---|---|
| Every failing test, by owning module, with its severity | §14.1 |
| Carried problems that have no failing test | §14.1, *No failing test* |
| Evidence judged since `f8c55626` | §14.2 |
| The Phase 6b handoff to `test`, and what is held | §14.3 |
| Residuals, and the falsifiers that got no cell | §14.4 |
| Defects opened, narrowed and closed since `f8c55626` | §14.7 |
| Handoffs, in order | §14.8 |
| The backend's exit list | §14.9 |
| No decay | §14.10 |
| Clean house | §14.11 |
| The exit targets, and the bands edited | §14.12 |
| What the sprint's evidence does not cover | §14.13 |
| The bands the specification's rewrite cleared, row by row | §14.14 |

- **Read against:** `main` at `128255fc`. Since `11ea995e`: `spec`'s
  records of the rulings of 2026-11-22 and its stage-two rewrite; `test`'s
  cells for the Phase 6b intake (`60f15a06`, `e9a60317`, `2929d74f` to
  `128255fc`). No file under `crates/`, `src/` or `stdlib/` has changed
  since `e6cdbe90`.
- **What `qa` ran,** in the primary harness on a debug build, holding the
  build alone:
  - `cargo nextest run --no-fail-fast` once, with
    `CRANELISP_CATEGORY_CENSUS` set;
  - the document checker and the band reconciler;
  - by hand, in scratch directories since removed, the subjects and
    controls of every filing opened in Phase 6b;
  - at `9bc97297`: the sprint's opening tree, `3155f47f`, built in a
    throwaway clone for ACT-1101 and ACT-1102;
  - at `121c5c9e`: `cargo build`, read for warnings, and `cargo clippy -p
    cranelisp-backend --all-targets`.
- **Limits.**
  - **One full run.** No cell was repeated, alone or under load.
  - **The 108 bands are judged from `test`'s source walk,** which `qa`
    read whole and checked against source in two rows. `qa` did not
    re-read each cell.
  - **`qa` did not replant a fault.** The module rows' reds and detection
    proofs for row B17 are as `dev` records them.
  - **The opening tree was built for ACT-1101 and ACT-1102 only.**
  - **`qa` did not replay the demos.**
  - **The relocation row's Mach-O leg did not execute.** This host emits
    ELF.

### 14.1 The failing set, by owning module

| Module | Failing | Filings |
|---|---|---|
| `src/` | 71 | ACT-1089 (14), ACT-1096 (9), ACT-1079 (8), ACT-1005 (6), ACT-1100 (6), ACT-1108 (6), ACT-1106 (5), ACT-1068 (4), ACT-1101 (3), ACT-1092 (2), ACT-1109 (2), ACT-1099, ACT-1102, ACT-1105, ACT-1062 (display), ACT-1087, ACT-1090 (1 each) |
| typecheck | 61 | ACT-1076 (15), ACT-1075 (9), ACT-1071 (7), ACT-1074 (6), ACT-1103 (6), ACT-1080 (4), ACT-1082 (4), ACT-1097 (3), ACT-1104 (3), ACT-1073 (2), ACT-1107 (2) |
| **backend (focus)** | **0** | — |
| intrinsics | 3 | ACT-0977 |
| Not attributed to a module | 7 | ACT-1018 (5), ACT-1067 (2) |
| Test and maintenance | 1 | The document gate |
| types, frontend, primitives, platform, exe-bundle | 0 | — |
| **Total** | **143** | No test fails without a filing |

- **The counts are `qa`'s full run at `128255fc`.** Each failing test was
  matched to its filing by the name or comment its source carries.
- **Against the 119 at `11ea995e`:** `src/` +21 (ACT-1108 6, ACT-1106 5,
  ACT-1096 5, ACT-1089 2, ACT-1109 2, ACT-1105 1); typecheck +3 (ACT-1107
  2, ACT-1104 1).
- **The rows below this table are the run at `11ea995e`;** the Phase 6b
  filings' cells are judged in §14.2 and counted in the table above.
- **The document gate: 576 findings.** 547 are ignored-path findings,
  with the user. The other 29 are in files of `sprint` (the plan, two API
  packets and two architecture reviews), `design`(intrinsics) (seven
  establishment findings and one shorthand), `design`(frontend),
  `design`(typecheck), `audit` and `review`'s memory, and one is `test`'s
  unregistered handoff file. None is in a file `qa` owns.
- **Severity** is what the subject did where its assertion states what it
  must do, on the scale memory-unsafe, data loss, wrong value, legal
  program refused, wrong diagnostic, performance only. A filing with
  several faces is listed under its worst.
- **Which assertion each cell fails on** was read at the run that first
  held the cell (§14.2). In this run the seven new reds were read by name
  and outcome against `test`'s report of their messages.

**typecheck** — 58 cells, carried.

| Filing | Cells | Severity, from the failing cells | Attribution |
|---|---|---|---|
| [ACT-1076](../../sprints/actions/ACT-1076-trait-dispatch-selects-on-the-first-argument-not-the-self-position-intake.md) | 15 | **Memory-unsafe** (subject c: signal 11). Also a wrong value (subject b) and refusals of legal programs (subjects a, d, e) | Typecheck, `dispatch.rs` |
| [ACT-1071](../../sprints/actions/ACT-1071-imported-impl-instance-calls-multi-signature-function-through-empty-slot-intake.md) | 7 | **Memory-unsafe.** Signal 11 in six cells; the link is refused in the seventh | **Provisional.** A hypothesis from `review`'s reading, with one supporting observation at the keyed consumer. If `dev`(typecheck)'s probe refutes it, the cells return to `qa` for the backend and `src/` |
| [ACT-1075](../../sprints/actions/ACT-1075-polymorphic-candidate-selected-from-a-shared-spelling-is-undefined-at-codegen-intake.md), with T-1065-f | 9 | Legal program refused: `undefined function` at codegen | Typecheck, `mono_collect.rs`. Read at its seam |
| [ACT-1074](../../sprints/actions/ACT-1074-impl-body-call-to-same-cluster-multi-signature-function-refused-intake.md) | 6 | Legal program refused | **Provisional** |
| [ACT-1082](../../sprints/actions/ACT-1082-reference-through-a-module-alias-names-the-alias-as-the-module-intake.md) | 4 | Legal program refused in one REPL order (1 cell); wrong diagnostic (3 cells) | **Provisional.** The design reads the producer as typecheck's `resolve_qualified` and the reader as the binary. All four are counted to typecheck; the REPL-order cell's trace line names the reader in `src/` |
| [ACT-1080](../../sprints/actions/ACT-1080-return-annotation-mismatch-names-expected-and-actual-reversed-intake.md) | 4 | Wrong diagnostic | **Provisional** |
| [ACT-1073](../../sprints/actions/ACT-1073-refused-cluster-leaves-an-earlier-implementation-shell-registered-intake.md) | 2 | Wrong diagnostic: a call that must be a type error is a codegen error naming an internal symbol | **Provisional** |
| [ACT-1097](../../sprints/actions/ACT-1097-trait-signature-accepts-a-bare-primitive-type-name-that-is-not-imported-intake.md), T-TRAIT-SCALAR | 3 | An illegal program accepted: an unimported bare `Int` in a trait signature | `crates/cranelisp-typecheck/src/resolve.rs::resolve_named`'s scalar fast path, read in source with controls |
| [ACT-1103](../../sprints/actions/ACT-1103-trait-spelled-num-eq-ord-or-display-has-its-impl-body-replaced-by-a-primitive-intake.md), T-TRAIT-SPELLING | 6 | Wrong value: a user's own trait spelled `Num`, `Eq`, `Ord` or `Display` has its implementation for `Int` replaced by a primitive, called directly, as a value and through a constraint | `traits/dispatch.rs::primitive_for_trait_method`, keyed on three bare spellings. Read in source with renamed controls |
| [ACT-1104](../../sprints/actions/ACT-1104-built-in-vec-is-refused-as-an-implementation-target-intake.md), T-VEC-IMPL | 2 | A legal program refused: an implementation for `(Vec Int)` or `(Vec a)` | `traits/impl_check.rs` reads no type parameter on the built-in `Vec`. Provisional as to the site |

**`src/`** — 50 cells, carried.

| Filing | Cells | Severity, from the failing cells | Attribution |
|---|---|---|---|
| [ACT-1102](../../sprints/actions/ACT-1102-refused-save-leaves-the-cache-ahead-of-the-backing-file-intake.md), T-REFUSED-SAVE-CACHE | 1 | **Memory-unsafe.** After a refused save the next cached session restores a definition the backing file does not hold; calling it ends the process on signal 11 | `src/session_v4/lifecycle.rs`: the final persist rewrites the cache from the live table under the unchanged source hash. Read in source with controls. Predates S124 |
| [ACT-1101](../../sprints/actions/ACT-1101-session-save-refused-after-a-parametric-product-type-is-constructed-intake.md), T-SAVE-PRODUCT | 3 | **Data loss.** After a value of a parametric product type is constructed, every later save is refused with a warning and later definitions are absent at restart | `src/save.rs::generate_types` selects the product constructor's instance as a type declaration. Read in source with a control. Predates S124: the opening tree shows it |
| [ACT-1096](../../sprints/actions/ACT-1096-declared-child-of-a-library-module-is-replaced-by-a-file-earlier-on-the-search-path-intake.md), T-MOD-CHILD | 4 | Wrong value: a library's declared child is replaced by a same-path file earlier on the search path, in `--run`, linked, and after a cached launch. By the ruling on S124-Q14 the project file is not part of the program; it is also offered by `/search`, with no cell yet | `src/process_form/dependency.rs::enrol_declared_submodule`, read in source with a control. The index face is attributed to `src/`'s index feed by control only |
| [ACT-1092](../../sprints/actions/ACT-1092-search-index-omits-a-module-whose-import-names-an-unloaded-or-compiling-module.md), T-SEARCH-REACH | 2 | Wrong value: `/search` omits a module whose import names an unloaded module, and answers as from a complete index | `src/session_v4/index_worker.rs::checked_typecheck_module`, at the feed's own report |
| [ACT-1099](../../sprints/actions/ACT-1099-type-command-refuses-an-expression-that-uses-a-macro-intake.md), T-TYPE-MACRO | 1 | A legal query refused: `/type` of an expression that uses a macro | `src/repl/commands.rs::typecheck_only`, provisional: by control, not read in source |
| [ACT-1100](../../sprints/actions/ACT-1100-selective-derive-import-refusals-intake.md), T-MACRO-SIBLING | 6 | A legal program refused: an expansion's reference to a macro of its own module is `undefined variable` under a selective import, at the REPL, under `--run` and linked | `src/process_form/macro_resolution.rs`: heads are recognised in the using module's scope and qualified to the defining module afterwards. Read in source with a control |
| [ACT-1089](../../sprints/actions/ACT-1089-type-command-given-a-definition-commits-it-without-code-intake.md), REPRO-1089, T-TYPE-PURE and T-TYPE-ERR | 12 | **Memory-unsafe.** A definition given to `/type` is committed with no code: signal 11 on the next call in three cells (two `defn`, one `impl`), a replaced signature in one, a stale printed type in one, a `deftype` and a `deftrait` left defined in two. No error is reported after an expression, in five (T-TYPE-ERR: `defn`, `deftype`, `deftrait`, `impl`, `defmacro`). The fifth cell requires the definition's type and reads the previous input's | `src/repl/commands.rs::typecheck_only`, read in source with a control. Carried past S124 by the user's ruling |
| [ACT-1062](../../sprints/actions/ACT-1062-match-field-binder-takes-another-parameters-type-intake.md), REPRO-1062-e | 1 | **Memory-unsafe.** Displaying a value whose type mentions its parameters out of declared order ends on signal 11 at the REPL | `src/display.rs::build_adt_subst`. Read at the seam |
| [ACT-1068](../../sprints/actions/ACT-1068-multi-signature-definition-omitted-from-regeneration-intake.md) | 4 | **Data loss.** The regenerated file omits every multi-signature function | `src/save.rs`, a source reading. The file is that module's output and no other module writes it |
| [ACT-1005](../../sprints/actions/ACT-1005-macro-order-regeneration-edge-cases.md) | 6 | **Data loss** in two cells: the regenerated file no longer compiles and the next session is locked. Wrong value in four: definitions are kept and their authored order is not | `src/save.rs`, a source reading |
| [ACT-1079](../../sprints/actions/ACT-1079-qualified-reference-through-a-mount-needs-its-owner-loaded-intake.md) | 8 | Legal program refused | **Provisional:** the mechanism is a hypothesis |
| [ACT-1087](../../sprints/actions/ACT-1087-trace-form-in-a-prelude-dependencys-child-omits-modules-reached-through-the-prelude-intake.md) | 1 | Wrong value, low harm: a first launch omits a trace frame that later launches record | `src/cache/dependency_record.rs::covered_set`, read at its module row. `arch`'s accepted residual |
| [ACT-1090](../../sprints/actions/ACT-1090-commit-planning-validates-a-covered-member-against-a-table-copied-before-it-published-intake.md), REPRO-1090 | 1 | Wrong value, low harm, run-dependent: a launch that compiles a dependency of a restored module omits that dependency's frames (2 of 30 launches in this run) | `src/worker.rs::plan_staging_commit_inner`, read in source with a control. The order of the two reads is not observed at its seam |

**intrinsics** — 3 cells, carried.

| Filing | Cells | Severity, from the failing cells | Attribution |
|---|---|---|---|
| [ACT-0977](../../sprints/actions/ACT-0977-scoped-launched-work-cancellation-evidence.md) | 3 | Wrong value: effects of a cancelled branch still occur | The runtime's strand supervision. Its realisation goes through `arch`'s effect contract first |

**Not attributed to a module** — 7 cells, carried.

| Filing | Cells | Severity, from the failing cells | What is missing |
|---|---|---|---|
| [ACT-1067](../../sprints/actions/ACT-1067-deeply-nested-expression-overflows-compile-worker-stack-intake.md) | 2 | Legal program refused: the compile worker overflows its stack and the compiler aborts | The stage. Frontend, typecheck, the backend and the binary all recurse on that thread, and no backtrace was taken. The quoted leg points at or before the first stage that walks a quoted body |
| [ACT-1018](../../sprints/actions/ACT-1018-exemplar-warm-solve-residual-intake.md) | 5 | Performance only: one block retained per `print` of a value the caller owns. The exemplar guard (1 cell, reads 2) and T-PRINT-BALANCE (4 cells: a literal and a concatenation, `--run` and linked) | The module. The block is stranded without the standard library and through both test platforms, when `print`'s argument is a value the caller owns outright. The platform crate's consuming capture, the backend's transfer at a platform call and the runtime's node disposal are the candidates; `stdlib/` is not |

- **The backend is one of ACT-1067's candidates.** If its stage is
  attributed to the backend, its two cells join §14.9.

**Test and maintenance** — 1.

| Test | Clears when |
|---|---|
| `citation_drift::project_documents_conform_to_the_checked_in_declaration` | The user disposes the 562 ignored-path findings and the owners repair the other 27 (M-W0); both counts re-read on 2026-11-20 with this pass's edits in place |

**No failing test.** Under *reproduce first* each of these is a carried
problem with no committed reproduction. The older leads in the last row were
read from their filings' headers only.

| Problem | Module | State | A reproduction |
|---|---|---|---|
| `/type` given an expression that applies a parametric constructor makes the next evaluation end on signal 11 (a face of [ACT-1089](../../sprints/actions/ACT-1089-type-command-given-a-definition-commits-it-without-code-intake.md)) | `src/` | **Memory-unsafe. Found and reproduced by `qa`,** with controls, with and without the standard-library prelude | T-TYPE-EXPR, allocated (§14.3) |
| `primitives/pure` does not exist and `Pure` constructs and matches ([ACT-1108](../../sprints/actions/ACT-1108-io-is-not-opaque-pure-is-absent-and-the-constructors-are-surface-intake.md)) | `src/` (the bootstrap) | A nonconformance against the ruling of 2026-11-22. Carried to the next sprint by the user's decision | T-IO-OPAQUE, allocated (§14.3) |
| Function and nested IO values display as `<closure>` and as their node ([ACT-1109](../../sprints/actions/ACT-1109-function-and-nested-io-values-do-not-display-as-the-closure-and-io-markers-intake.md)) | `src/` (display) | A nonconformance against the ruling of 2026-11-22. Carried | T-MARKERS, allocated (§14.3) |
| An unrecorded trace root is `::skipped::` with an empty result ([ACT-1110](../../sprints/actions/ACT-1110-an-unrecorded-trace-root-is-named-skipped-with-an-empty-result-intake.md)) | intrinsics | Nonconforming by source; not observed. Carried | None: no fixture makes a form unrecorded. Module rows with the correction |
| `Effect`'s field is typed as the IO's value and holds a thunk: constructing it with a value, or binding it in a match, ends the process on a signal ([ACT-1106](../../sprints/actions/ACT-1106-effect-constructors-field-is-typed-as-the-io-value-and-holds-a-thunk-intake.md)) | The requirement (spec §10.1), as realised in `src/bootstrap.rs` | **A defect against the specification as written, memory-unsafe. Observed by `sprint`; reproduced by `qa`** in every mode with `Pure` controls | T-EFFECT-FIELD, allocated (§14.3) |
| A match on `IO` with `Pure` and `Effect` arms is accepted and fails on a bind node ([ACT-1107](../../sprints/actions/ACT-1107-match-on-io-with-pure-and-effect-arms-is-accepted-and-fails-on-a-bind-node-intake.md)) | typecheck | **A defect against spec §6.5. Observed by `sprint`; reproduced by `qa`** in every mode with two controls. `adt.rs` leaves internal constructors out of the set to cover; read in source | T-IO-MATCH, allocated (§14.3) |
| A qualified `primitives/Bind` constructs an IO node one word shorter than the runtime reads; the bare spelling is refused ([ACT-1105](../../sprints/actions/ACT-1105-qualified-primitives-bind-constructs-a-node-shorter-than-the-runtime-reads-intake.md)) | `src/` for the seeded node; typecheck for the spelling, provisionally | **A defect under either answer to the user's open question. Observed by `qa`** in emitted code and by controls. Memory-unsafe and latent: a read past the allocation on every forced node; no wrong value observed | T-BIND-SPELLING, allocated (§14.3). The short node has no solution-level cell |
| `/search` offers a symbol from a project file at a library child's path, which the ruling on S124-Q14 says is not part of the program (a face of [ACT-1096](../../sprints/actions/ACT-1096-declared-child-of-a-library-module-is-replaced-by-a-file-earlier-on-the-search-path-intake.md)) | `src/`, provisional | Reproduced by `qa` by hand with a control. Wrong value | T-MOD-CHILD-INDEX, allocated (§14.3) |
| Two processes on one project directory mix cache generations ([ACT-1085](../../sprints/actions/ACT-1085-two-processes-on-one-project-directory-can-mix-cache-generations-intake.md)) | `src/` | Asserted with a named falsifier. The backend's shared temporary name, which was a part, is corrected (`7d5a5d42`) | Judged constructible, and not attempted, below |
| A codegen failure names `__expr` or an instance key as its subject (FIXME 0915, the binary's half; [int §9.1](../../design/int/int.md#91-the-compiler-stage-subject-is-presented-never-carried--ruling-s119-fixme-0915-item-4)) | `src/`, with a carrier that is `arch`'s | True in this read: `codegen failed for __expr in user: …` through ACT-1075's cells. No legitimate program reaches it. Wrong diagnostic | A module row in `src/`, allocated to `dev`(`src/`) (§14.8). No e2e cell: every public trigger is another module's open defect |
| A macro-produced function restored from cache that references `discover-tests` is reported at `0..0` ([ACT-1036](../../sprints/actions/ACT-1036-main-return-refusal-synthetic-location-intake.md)) | `src/` | Stated by `design`(int); with the user | Not checked |
| The link's refusal of a stopped object pass carries `app.cl:1:1` and `0..0` (§14.4) | `src/` | Observed by `qa`; T-LINK-STOP does not assert a location | A clause on T-LINK-STOP, once the design states the location |
| The failed-dependency refusal does not run at a fresh load (§14.4) | `src/` | Asserted with a falsifier; one fixture did not reproduce it | Not found |
| A rewrite while a module's own cached load is outstanding (int §7.7) | `src/` | Asserted with a falsifier; not observed | Not attempted |
| The bind-chain pass's import assertion (§14.4) | `src/` | No evidence | T-1065-f, which executes once ACT-1075 is corrected |
| A multi-signature family's mode-changing redefinition (§9.4) | backend and `src/` | No cell; awaiting the user's approval of the row | Held |
| ACT-0985's remaining shape (§10) | typecheck | Held on a question with `spec` | Held |
| Leads from before S124: ACT-1022, ACT-1015, ACT-1001 (P-2), ACT-0987, ACT-0994, ACT-1003, ACT-1004, ACT-0978, ACT-0979, ACT-0982 | various | Deferred or open in their filings | Not re-read here |

- **ACT-1081's outcome is not in this table.** The specification is silent
  and blocks no test, so under *consistent spec* it is an open question and
  the current behaviour stands.

**ACT-1085: what a reproduction takes.** The falsifier is a warm run whose
result differs from `--no-cache`.

- **Why it can exist.** A `.meta` records nothing about its object's
  content (int §7.7: a restore-side check "would need a length or digest in
  the `.meta`"). A current `.meta` and manifest beside an older `.o` is
  therefore loaded as valid.
- **A sequence that produces it.** Three modules, `lib` compiled first and
  a large module after it.
  1. Process A starts `--run` and is stopped after it writes `lib.meta`
     and before it publishes `lib.o`.
  2. `lib.cl` is rewritten so that a function's result changes.
  3. Process B runs the same command to completion. It writes `lib`'s
     `.meta`, `.o` and the manifest for the new source.
  4. Process A continues, publishes its `lib.o` for the old source, and is
     killed before its object work ends, so it writes no manifest.
  5. A warm `--run` restores `lib` and gives the old result.
- **What it needs that the suite lacks.** A harness primitive that stops,
  continues and kills a child on a change in the cache directory. No
  sequence of user commands selects the interleaving.
- **What it would and would not show.** It would show that interleaved
  writers leave a mixed generation that validates. Its route (a source edit
  during a run, and a killed process) is narrower than the filing's stated
  reach, an open REPL beside a batch command with no edit. Whether that
  reach produces two different objects for one validity key is not known.
- **Not attempted.** It is `test`'s to build on `sprint`'s scheduling, with
  the harness primitive as a change to the suite's helpers.

### 14.2 Evidence judged since `f8c55626`

"Accepted green" means the row's cells were RED on their assertion before
the correction and pass with no change to their assertions.

| Evidence | Judgment | Note |
|---|---|---|
| T-TYPE-EXPR: `repl_introspection::s124_type_expr_*`, three cells (`2929d74f`) | **Accepted, RED as allocated** | Both subjects end on signal 11 after the type answer; the evaluated-first control passes |
| T-IO-OPAQUE and the narrowed `IO` cells: `spec_10_io::s124_effect_field_*`, `s124_io_match_*`, `s124_io_opaque_*`, `s124_bind_spelling_*` (`0cfe3a00`, `c0c6f4e7`) | **Accepted, RED as allocated** | 14 fail: five effect subjects on a signal, the `Pure` constructor accepted, two matches accepted, the four-spelling cell, and five public-lift cells on the absent `primitives/pure`. The subjects build IO values with `sleep 0`, so acceptance stays observable without `pure`. The single-`Pure`-arm match and a checker self-test pass. Cell names keep their earlier wording so backlinks resolve |
| T-TRAIT-SPELLING, narrowed (`ca8f88b9`) | **Accepted** | The six subjects require the implementation's value alone and still fail on the primitive's; three controls pass |
| T-VEC-FUNCTOR: `spec_07_traits::s124_vec_functor_*` (`8bd6b51c`) | **Accepted, RED as allocated** | The subject is refused with `Vec has 0 type parameters`; the `Option` and helper controls pass |
| T-MARKERS: `repl_introspection::s124_markers_*` (`d4e12848`) | **Accepted, RED as allocated** | The closure and nested-IO displays fail; the reader refusal passes |
| T-SCONCAT-PUBLIC and T-DEFAULT-UNDEFINED (`929975de`, `ace94858`) | **Accepted,** green guards | Three cells each, all passing. `test` did not plant a fault in them |
| The backlink walk for 108 cleared bands (`128255fc`) | **Accepted as the clause map** | A source walk, not 108 executions. `qa` read it whole, checked two rows against source, and applied it (§14.14) |
| T-MOD-CHILD-INDEX: `search::s124_child_index_*`, seven cells; T-MOD-CHILD's values (`60f15a06`) | **Accepted, RED as allocated,** on a focused run | Five index subjects fail and the library-only and presence-not-an-error controls pass. The four child subjects fail with values that are not an error status; the override control passes. Read by outcome, with the fixture and clauses read in source |
| T-EFFECT-FIELD, T-IO-MATCH, T-BIND-SPELLING: `spec_10_io::s124_effect_field_*`, `s124_io_match_*`, `s124_bind_spelling_*` (`e9a60317`) | **Accepted, RED as allocated,** on a focused run; narrowed by the ruling (§14.3) | Five effect subjects end on a signal and four `Pure` controls pass; the match subject ends on `match failed` and two controls pass; the spelling cell fails on disagreement and the builtin control passes |
| T-TRAIT-SPELLING: `spec_07_traits::s124_trait_spelling_*`, nine cells (`3904fae8`) | **Accepted, RED as allocated** | Six subjects fail on the primitive's value (8, 8, 10, 9, 9, 5), neither arm of the clause being met. The three renamed controls pass. The refusal arm requires exit 1 and a diagnostic, and no subject's expected value is 1 |
| T-VEC-IMPL: `spec_07_traits::s124_vec_impl_*`, four cells (`3904fae8`) | **Accepted, RED as allocated** | Both subjects fail on the refusal `Vec takes 0 type parameters`. The bare-constructor negative and the `Option` control pass |
| T-TRAIT-ONE-PARAM: `spec_07_traits::s124_deftrait_second_parameter_located_parse_error_neg` (`3904fae8`) | **Accepted,** a green guard | It requires a parse error located in the file |
| T-SPLICE-BARE: `spec_09_macros::s124_splice_without_prelude_or_import_{run,repl}` (`3904fae8`) | **Accepted,** green guards | No prelude and no import; exit 7 and `:primitives/Int 7` |
| T-MOD-CHILD, re-read after the ruling on S124-Q14 | **Stands; one item returned** (§14.3) | Its subjects agree with the ruling. The library's value is 1, which is also the exit status of a refused compile, so they cannot show that the file's presence is not an error |
| T-REFUSED-SAVE-CACHE: `repl_persist::s124_refused_save_*`, three cells (`7c5f009e`, locus at `3904fae8`) | **Accepted, RED as allocated** | The subject drives the restart by staged input, so the signal is captured as a status, and checks all three clauses before asserting. `test` reports it RED on all three with signal 11, and both controls green. The locus is to be replaced now the site is read (§14.3) |
| T-SAVE-PRODUCT: `repl_persist::s124_save_after_*`, five cells (`65471409`, `9bc97297`) | **Accepted, RED as allocated** | The three subjects fail on the warning, file and restart clauses, collected before the assertion so none masks another. The two controls pass. The restart is cold, with the cache removed, because a cached restart ends on a signal (ACT-1102). The defect lines carry `src/save.rs::generate_types` |
| T-MACRO-SIBLING's loci (`8eb12256`) | Accepted | Six subjects name `src/process_form/macro_resolution.rs` |
| `repl/demos/optimization.demo` and `memory-lifecycle.demo` (`46c64e21`, `20ce70c6`) | Accepted as `test` reports | The retired stack placement and flattening acts are gone, and the startup ledger narration matches a zero baseline. `qa` did not replay them |
| The documentation samples, split (`67f9fcc3`) | **Accepted,** a maintenance check | 19 document cells and three guard and proof cells, all passing; the slowest takes 56 s. `test` reports the 93 groups retained, with omission and wrong-output proofs |
| T-MACRO-SIBLING: `spec_09_macros::s124_macro_sibling_*`, eighteen cells (`85f32147`) | **Accepted, RED as allocated** | Six subjects fail and twelve controls pass, at the REPL, under `--run` and linked. `test` added the linked mode, which the allocation left out. The reds' message, `undefined variable: d/inner`, is `test`'s report and matches `qa`'s hand reading. The locus is to be replaced now that the module is attributed (§14.3) |
| T-TYPE-ERR's returned items (`52c848d3`, `7f42d687`) | **Accepted** | `defmacro` is its own subject and fails; the four-form guard cell passes. The error predicate no longer requires a character span |
| T-TRACE-OWNING's returned subjects: `trace::s124_trace_owning_constructed_{record,vector}_{cold,cached,link}` (`31eeea76`) | **Accepted as green guards** | The value is built inside the traced call. All six pass. Neither `test` nor `qa` has seen a solution-level cell fail on the old discard; the fault's detection rests on `dev`'s module row |
| T-STDLIB-ADT-TRAITS, the nested `Display` leg (`b6211d79`) | Accepted | 29 legs pass in three modes |
| T-TRACE-ROOT's stamps (`fb68ef5f`) | Accepted | Nine cells carry `fixed=`; ACT-1094 is deleted |
| The sprint demo `repl/demos/12-tracing-values.demo` (`23448d9c`) | Not judged as evidence | A demo is a showcase. `test` reports 41 demos replayed; the two with stale narration are corrected (above) |
| **ACT-1094's correction** (row B17: intrinsics `ecae99c9`, backend `3c5e41ca`) | **Accepted** | The nine T-TRACE-ROOT subjects pass with `tests/trace.rs` unchanged but for additions since `f1724229`, and the four controls pass. The backend's five `trace_root_*` rows and the seven intrinsics collect rows pass; their reds and planted faults are `dev`'s record. Both reviews returned no finding, as `sprint` reports. The armed census reads zero. No golden changed |
| T-TYPE-ERR: `repl_introspection::s124_type_err_*`, six cells (`c02eb9bc`, `f67f944f`) | **Accepted, RED as allocated; two items returned** (§14.3) | The four subjects fail on both clauses: no error, and `:primitives/String` printed. The control passes. The guard cell is RED on its `defmacro` form, which `qa` wrongly expected to pass and had not run; the cell's other four forms are masked by it. The error pattern requires a character span, which REPL §5.1 does not |
| T-TRACE-OWNING: `trace::s124_trace_owning_{record,vector}_{cold,cached,link}` (`9b9687b4`) | **Accepted as green guards; one subject returned** (§14.3) | All six pass on balance and on result equality. The value is built outside the traced call, so the traced value may not be its only owner, and the cell may not fail on a release with no glue |
| T-TYPE-MACRO: `repl_introspection::s124_type_macro_expression` (`5a544de2`) | **Accepted, RED as allocated** | It fails on the type clause after its control prints 4: `undefined variable: twice` |
| T-STDLIB-ADT-TRAITS: `stdlib_conformance::s124_stdlib_adt_traits_across_modes` (`c5bb106c`) | **Accepted** | 28 legs pass in the REPL, `--run` and linked, with unequal and different-constructor legs. `Pair` has one constructor, so that leg does not exist; the allocation was wrong to ask for it. The nested `Display` leg waits on its text, which `dev`(stdlib) pinned at `e6cdbe90` |
| T-STDLIB-SELFTESTS: `stdlib_conformance::s124_stdlib_selftests_*`, eight shells, with `…_check_detects_empty_and_failed_discovery` (`5c7bd9e9`) | **Accepted,** a maintenance check | 24 modules report tests and no failure. The proof cell shows the check fails on a null import and on a failing test. Each shell takes 5 to 24 s in the full run |
| The exemplar pin (`88406d6c`) | Accepted | Both runner cells exit 43, in 6.1 s and 3.3 s |
| The corrected search fixture (`6137fdf7`) | Accepted | `xf` is valid apart from its import; the cell passes |
| ACT-1034's stamps (`93e3df64`) | Accepted | 53 cells carry `fixed=`; the filing is deleted |
| T-TYPE-PURE: `repl_introspection::s124_type_pure_*`, six cells (`ea6778aa`, `c4282cb5`) | **Accepted.** Three RED as allocated, three guards green | The `impl` cell fails on its status clause at signal 11, with its control passing in the same test. The `deftype` and `deftrait` cells fail on the `/list` clause after a zero exit. The `IO`, `import` and `defmacro` guards each carry their control. No clause reads what `/type` prints |
| T-MOD-CHILD: `spec_08_modules::s124_declared_child_{run,link,cached}_…` and `…_not_replaced_by_earlier_library_file`, with `…_project_module_override_control` (`ccd7f2e4`) | **Accepted, RED as allocated** | Each subject fails on its exit clause with 2 against 1. The cached cell first asserts the library object is cached. The override control passes with 2 |
| T-TRACE-ROOT: `trace::s124_trace_root_*`, thirteen cells (`f1724229`) | **Accepted, RED as allocated** | Eight subjects fail on 40 against 41; the cached legs fail after observing the restored launch. The heap cell fails on result equality with allocations balanced, 22 and 22. The four child controls pass. All nine subjects carry `class=unrecorded-value` |
| T-SEARCH-REACH: `search::s124_search_reach_*`, three cells (`b5ad5600`) | **Accepted, RED as allocated; one fixture returned** (§14.3) | Both subjects fail on the row clause after the `pf` control row is found. The negative cell passes but cannot fail for the reason it was allocated |
| T-TRAIT-SCALAR: `spec_03_types::s124_trait_scalar_*`, five cells (`9ca6948c`) | **Accepted, RED as allocated** | The three subjects fail on the refusal clause at exit 0. The return-position cell does not assert the diagnostic's kind. Both controls pass. The `(Vec Int)` subject is not written: it waits for the correction to show whether it shares the path |
| T-PRINT-BALANCE: `spec_10_io::s124_print_balance_*`, eight cells (`dce11541`) | **Accepted, RED as allocated** | The four subjects fail on the balance clause, 2 against 1 and 4 against 3, in `--run` and linked. The linked reading is new: the block is stranded there too. The four controls balance |
| T-EXEMPLAR-TESTS: `exemplar::s124_exemplar_tests_runner_{lenient,serial}` (`b72742f7`) | **Accepted,** a maintenance check | Both exit 41, in 4.6 s and 2.4 s inside the full run against a 20 s limit. Only the exemplar's top-level sources are copied, which is the runner's own set |
| T-FRAME-NAME: `trace::s124_template_frame_name_{run,link,repl}` (`76165d36`; corrected at `2ffc84d3` over row B16, `c9f573e0`) | **Accepted green.** ACT-1091 is closed and deleted | The cells are the allocated ones and were committed before the correction. All three pass in the full run, cold and warm. **The RED basis is `qa`'s hand reading at `ee65d9aa`** (the frame named by its instance key under the batch's module, the monomorphic control by its module and name; the filing's text is in Git at `044bd8da`) with the fixture the cells hold. `qa` did not see the committed cells fail. They hold one instance |
| The backend's module row for ACT-1091 (`crates/cranelisp-backend/src/compiler/trace_codegen/tests.rs::discovery_names_an_instance_frame_by_its_template`, `2ffc84d3`) | **Adequate** | Two instances of one template both take `m/g`, an authored entry keeps its own name, and the instances keep their table-key order. It covers what the cells cannot: more than one instance. `dev` states it RED first; `qa` did not observe that |
| Row B16's module row in types (`module/tests.rs`, `c9f573e0`) | Adequate at its tier | It replaces the `template_module` row it subsumes. `review` returned no finding on the commit |
| REPRO-1090: `trace::s124_1090_mixed_restore_subject` and `s124_1090_all_restored_control` (`f18652c6`) | **Accepted, RED as allocated** | The fixture, the launch counts and the two clauses are the allocated ones. In the full run the subject fails on its score assertion with 2 of 30 launches at 50, and the control passes. `test` reports ten of ten readings RED, five alone and five loaded, with 1 to 7 launches of 30 at 50. **Cost:** the subject took 61 s and the control 25 s inside the suite, against the 40 s estimated. **Limit:** while the defect is open the subject fails by rate; at 2 of 30 a pass is about one run in eight. `qa` re-reads the launch count when the correction lands with its module row |
| T-TYPE-DEFN: `repl_introspection::s124_1089_definition_reports_its_function_type` (`28176b57`) | **Accepted, RED as allocated** | It fails on its type-line assertion after a zero exit, not on setup. It carries REPRO-1089's `// defect:` line **Withdrawn on 2026-11-20:** the rule it asserts was replaced by the user's final ruling. T-TYPE-ERR replaces the cell (§14.3) |
| REPRO-1088's trace lines (`ee5d5fc0`) | Accepted | Seven subjects carry `fixed=S124/1238b31c` and state the defect in the past tense. No assertion changed; all twelve cells pass |
| The backend's relocation row (`fn_as_value/slot_call_tests.rs::object_holds_no_direct_call_into_its_unit` and `object_relocation_scan_reports_a_planted_direct_call`, `4407b008`; `39db1bb1`) | **Adequate.** The safety fence §14.4 allocated | Both legs are in the change-set: the clean unit reports nothing and a planted direct call is reported by name. `dev` states that a production mutation calling each target by its function id turned the row RED for each wrapper kind; `qa` did not repeat it. The Mach-O spelling `review` found is corrected and does not execute on this host |
| Row K11-a: the public-API baseline check (`c86aa1f7`) | **Passes; a maintenance check** | `public_api_check_runs_against_all_seven_crates`, its version-floor legs and its disposable-crate detection proof pass in the full run |
| REPRO-1086: `trace::s124_1086_subject_{run,link,repl}` with the typed and entry-function controls (`81912028`; corrected by row B10-C2, `94749709`) | **Accepted green.** ACT-1086 is closed and deleted | All nine pass in this read, cold and warm, with no change since `81912028`. The RED basis is `qa`'s hand reading at `f8c55626` (42 in every mode, the control at 40) with the fixture the cells hold. `qa` did not run the cells before the correction |
| REPRO-1088: `trace::s124_1088_{value,partial}_subject_{run,link,repl}` and `repl_redefinition::s124_1088_loaded_value_redefinition_subject`, with five controls (`e839d432`; corrected at `1238b31c`) | **Accepted green.** ACT-1088 is closed and deleted | All twelve pass at `ee65d9aa`, and no cell has changed since `e839d432`. The fixtures are the allocated ones. **The RED basis is `qa`'s hand reading at `4cef5784`** with the same fixtures: 50 for the value subject in each mode and for the partial subject in `--run`, and a third result of 1 for the redefinition subject. `qa` did not see the committed cells fail, and has no reading of the partial subject's `--link` and REPL legs before the correction; they share the `--run` leg's wrapper. The prompt control, which `qa` had not run, passes |
| The backend's module rows for ACT-1088 (`fn_as_value/slot_call_tests.rs`, `1238b31c`) | **Adequate, and stronger than the row the design asked for** | The row repoints the target's slot after compilation and observes the call follow it; `dev` states the same-unit leg RED (1, expected 101) before the change and the other-module control green throughout. The design asked for a reading of the wrapper's CLIF |
| The golden re-baseline [compile-to-module §12.2](../../design/backend/compile-to-module.md#122-every-call-to-a-slotted-function-goes-through-its-slot) predicted for ACT-1088 | **None exists to read; the prediction was false** | The CLIF dump renders no wrapper body, so no golden frame holds the changed call. `qa` confirmed it: `CRANELISP_CODEGEN_DUMP=*` over a program with a plain and a curry wrapper prints five frames and neither wrapper. §14.4 decides the gap |
| The entry-function controls of REPRO-1086 | **Green, and now observers** | They assert that a library form records no frame for the entry's `af`, taken as a value in its defining unit. Since `1238b31c` that call goes through `af`'s slot, so a covered `af` is recorded. The sibling shows it: with `run` moved into the entry file, so that only the form's home differs, the score is 41 in `--run`, `--link` and the REPL (by hand), against the controls' 40 |
| T-1086-helper: `trace::s124_1086_helper_{run,link,repl}` (`cf140ff4`) | **Accepted.** They arrived green, as allocated | Three cells, `[41, 41]` cold and warm. They count frames and pin no frame name, so ACT-1091's correction does not change them |
| Row B10-C2's module rows (`trace_codegen/tests.rs`: `discovery_reads_module_path_whole_only_when_listed`, `discovery_selects_instances_of_covered_templates_from_module_path`; `worker/tests.rs`: `every_target_is_paired_with_its_origins_set` and its siblings) | **Adequate at their tier** | They pin the consumer and the pairing. That typecheck records the template's module for a nested instance is composed only end to end, which T-1086-helper observes |
| REPRO-1087 (`81912028`; C1, `fe385164`; restated at `bcbd291a`) | **The linked leg and the restored leg: accepted green. The first-launch leg: RED, carried.** The restatement is as allocated: `s124_1087_subject_run_first_launch` fails on 40 and `s124_1087_subject_run_restored` passes with its cache-hit clause, at `ee65d9aa` | `s124_1087_subject_run` reads `[40, 41]` in 21 of 21 readings; `s124_1087_subject_link` and both controls pass 21 of 21. The RED basis of the corrected legs is `qa`'s hand reading at `f8c55626` (40 in every launch). The readings ran one cell at a time, not under load |
| REPRO-1089: `repl_introspection::s124_1089_*` (`14341a53`) | **Accepted, RED as allocated** | The existing-definition and new-name subjects fail on the exit status (signal 11), the stale-type subject on the printed `:primitives/String`, the changed-signature subject on the signature; the expression control passes. Read at `ee65d9aa` |
| The trace-line reconciliation and the NUL-credential cell's stdin (`cf140ff4`) | Accepted | No assertion changed. The NUL cell passes |
| C1's module rows (`dependency_record/tests.rs`: `the_object_pass_walk_answers_an_unpublished_prelude`, `an_unpublished_prelude_is_read_as_it_stands`; `scheduler/tests.rs`: `a_held_pass_runs_when_its_member_publishes`, `a_held_pass_runs_when_its_member_fails`, `awaiting_objects_stops_a_pass_held_on_an_unpublished_member`; `nice_worker.rs`: `a_pass_reaching_an_unpublished_prelude_while_objects_are_awaited_stops`) | **Adequate** | Every row int §7.6.4 lists for C1 is present by name |
| Row B15 (`9bee5930`): `module_assembly_tests.rs::sprint56_compile_to_module_ast_none_errors` restated, and `a_failure_outside_any_target_is_the_modules` | **Adequate** | The row's main property is structural: the public conversion that filled an empty module and symbol is removed, so a site with no module in hand does not compile. The two rows pin the variant and its rendering through production `compile_to_module`. No e2e cell: no program reaches an unattributed failure. `qa` did not observe the restated row RED |
| FIXME 0915's backend frame (`a9a8c0c6`, `36e64f27`): three rows through `compile_to_module` | **Adequate. Observed composed** | Each row is stated RED under its planted pre-fix behaviour. Through ACT-1075's cells the frame now reads `codegen error at 1..5: codegen failed for __expr in user: undefined function: conv`: one prefix, a real span, the subject once. The subject itself is the binary's half (§14.1) |
| Trace order within a module (`e8a9cac5`): `discovery_orders_each_group_by_name` | **Adequate** | Closes the hash-map-order residual of the previous read for the trace form's own emission |
| ACT-0968 item 1's remaining arm (`9bb1f0aa`): `a_constructor_pattern_with_no_carrier_is_a_codegen_error` | **Adequate.** Item 1 is discharged | It arrived green, as allocated: a missing row, not a defect |
| The observed-type default (`793af750`, FIXME 0929's binary row): `type_reads_the_expression_scheme_result`, `type_with_no_expr_after_a_clean_check_is_a_located_error` | **Adequate for what the row states; the design's premise is false** | The second row pins a located error where no `__expr` exists. The design calls that state an invariant violation. A definition given to `/type` reaches it ordinarily, and does worse (ACT-1089) |
| Rows K11-c, K11-d, the trace reader's removal and ACT-1084 (`cc04b162`, `bf15e0d6`, `994137dd`, `0478d340`, `0b5d9dc6`, `717dd3a1`, `c95affc2`, `279cc37f`) | Nothing owed beyond the final run | Narrowings and removals: each compiles or does not. `sprint`'s run at `279cc37f` shows no new failure |
| The golden re-baseline (`ec92f77f`) | **Accepted; a maintenance check** | Every one of its 197 changed lines is a `fnN = colocated uN:N sigN` import declaration differing only in its numbers, which is what removing one exported intrinsic predicts |
| The depth-64 cells' child time limit (`81d186c6`) and the trace-line stamps (`15800c44`) | Accepted | As allocated at the previous read. No assertion changed |

**Accepted at `f8c55626` and before, unchanged.** Not re-run in this
read; each cell passed or failed in the `f8c55626` run as its row states.

| Rows | Judgment | Note |
|---|---|---|
| REPRO-1062-f, three cells (B14, `4d2bd8a4`) | **Accepted green** | §14.6 |
| B14's module rows (`crates/cranelisp-backend/src/schema/tests.rs`, and the baker's refusal row) | **Adequate** | Ten rows: an out-of-order product, a sum decided per constructor, an unmentioned parameter, a nested field type, a count mismatch, a concrete declared parameter, the identity pairing, a cross-variable pairing, the scheme read, and the schema walk on the out-of-order product. The last closes the schema-generator lead |
| REPRO-1070, the 16-run cell and its arena control (B13, `790f4c9a`) | **Accepted green** | The subject program ran 160 times alone and 160 times sixteen at once inside the cell, and exits 64 every time (§14.6). This discharges the filing's 96-run reading |
| M-1070-a (`jit/call_reach_tests.rs`), in place of the placement row `qa` allocated | **Adequate** | Placement follows the allocator and cannot be forced out of range. The row asserts the property that makes placement irrelevant: no pc-relative call relocation through the JIT's module. It executes the far call, and a bare `JITModule` control shows the observation detects a near call |
| B8 (`07bb8e84`): the extern shim's sibling slot removed | **Adequate** | A deletion. The validation rows went with the field they guarded. `cache_schema_version_mismatch_falls_through` holds the refusal of a sidecar of the old shape after the bump to 35. Nothing newly fails |
| T-1039, T-1039-w and REPRO-1078 (B10, `f8c55626`) | **Accepted green** | §14.6. REPRO-1078's seeding through completed REPL turns (`73f59825`) fixes the order in which `x` and `u` compile. `qa` did not observe its RED count before the correction; the defect is corrected, so the count no longer decides anything |
| T-1039-lib, three cells (`e53b8760`), written without an allocation | **Adequate for a library function whose parameter type is fixed; a gap for a generic one** | Each cell asserts one library frame and no caller frame, cold and warm, and that the warm leg restored the library. The library function's body fixes its parameter's type. The generic spelling, which is the specification's own example, records the caller's frames (ACT-1086) |
| The finished-module cells, nine (`e53b8760`), written without an allocation | **Adequate** | `arch`'s falsifier in three import positions and three modes, cold and warm, each asserting the callee module was restored. The three `--link` cells carry no `// defect:` line |
| B10's backend rows (`compiler/trace_codegen/tests.rs`) | **Adequate, with one unexecuted branch** | Discovery covers the module and the listed modules only; a listed module with no table is refused; a claimed slot is selected whatever it holds. No row executes the emitted swap over an empty original (§14.4) |
| B10's `src/` rows (`cache/dependency_record/tests.rs`, `worker/tests.rs`) | **Adequate** | Every row int §7.6.4 lists is present by name: the four edge rows, the covered set of a chain, an unpublished or absent member, an unpublished prelude, a later binding's callee, the gap behind a restored member, a child importing its awaiting parent, and the stored set reaching codegen |
| The atomic-write rows (`7d5a5d42`) | In source, module tier | Two rows, stated RED three of three against the fixed name |
| ACT-1077: the C9 rows and `spec_10_io::s124_1077_unrelated_bind_local_keeps_overlap` (`80580252`) | **Accepted green** | §14.10 |
| ACT-0981: the C10 row and `spec_10_io::s124_0981_multi_signature_overlap` (`6c51559d`) | **Accepted green** | §14.11 |
| The review advisory: multi-signature trait-implementation methods enter IO scheduling with no executing witness | **No cell: the path is not reachable from source** | `(impl Go K (defn go ([k d] …) ([k d e] …)))` is refused with `parse error: expected bracket`. The removed filter guarded a state no program can write. A single-signature method's independent pair overlaps (325 ms against 630 ms dependent, `qa`'s probe) |
| Value-flattening retirement (B5, row D4) and stack-placement retirement (B1) | Adequately evidenced, unchanged | As accepted at W5 and W2 |
| T-1052 (K-6) | **Accepted green; a reliable observer** | 0 of 600 loaded runs of its first four legs end on the signal; the harness cell passes 100 of 100 repetitions under load with its linked and REPL legs (§14.7). The settling target's clause for ACT-1052 is met on this tree |
| M-1052, O-1052 | Accepted green | Unchanged |
| REPRO-1083 (`91470bc6`) | Accepted green | Committed before the correction and passes after it; both controls unchanged. The subject waits on the listing of `g` and never on elapsed time. Its trace line carries `fixed=` since `b6ab5154` |
| `cache_index_wait_repeats_until_observed_output_control` (`91470bc6`) | Adequate; a maintenance check | Written without an allocation. It proves the new staged wait repeats on absent output and stops on the third result, which REPRO-1083's premise depends on |
| M-1083 and the one-generation rows (`f2317af0`) | In source, module tier | Five rows, each stated RED before the change. They pass |
| The four restated `tests/search.rs` cells (`96d4677c`) | **Adequate** | They asserted the removed write. Each now asserts the rows a search returns and that the index pass leaves no `.meta` and no `.o`; one plants an invalid `.meta` and requires it byte for byte after the pass; one requires the cache files to appear only after the real import. The settle anchor that was a `.meta`'s existence is now two returned rows and the absent progress note. The startup cell's discriminator is that a module created after the first prompt is not offered: spec §17.19.3 does not require that, so if a later design enumerates new files the clause is the cell's to change |
| The object-publication rows (`3dbc3db5`) | In source, module tier | A stopped publication leaves a miss (stated RED against the direct write); a completed one leaves its bytes alone in the directory |
| The object-pass record and the link's refusal (`79a8c94c`) | In source, module tier | Four rows, two stated RED. T-LINK-STOP, the next row, is the composed observation |
| T-LINK-STOP (`b6ab5154`): `link::link_neg_stopped_dependency_object_pass_refuses_before_startup` and its `--run` control | **Accepted.** It arrived green, as allocated | Its RED basis is `qa`'s observation on the `a205a29f` binary, which wrote the startup objects and went on to the link step, and `dev`'s module row. It cannot show a pass stopped at its object by codegen, emission or publication; the module rows carry those stages |
| The restored-parent failure rows (`9ea2b291`, `a812faaa`) | In source, module tier | Both orders of a parent refused by a failed child, a failed walk past a child in flight, and a failed walk on a module with no declared children. The two rows owed at `79a8c94c` landed at `fab4da36`: a failed walk through the real restore, and a claimed load that fails while the restored parent waits. They pass; `qa` planted no fault against them |
| ACT-1071's back-edge `--link` cell | Accepted, still RED; no change to the cell | It fails on its exit-status assertion as before. The text is now the link's refusal naming `lib`'s object pass, where it was a system-linker error (§14.7) |
| REPRO-1081, the alias cells, the absent-member cells, the in-flight qualified reference, the restored-parent cells, REPRO-0915-loc's `discover-tests` leg | As at the previous read | Their trace lines are reconciled (`19a0a02d`): `fixed=` stamps on the corrected cells, ACT-1082 on the four that stay RED |
| The W8-exit items (`c89dfe7f`, `c4e815d7`, `52be59d7`, `965a9234`, `ff1ac225`, `fed6175c`) | Accepted | The exemplar guard is RED on `retained == 2`, as allocated |
| Row K11-b (`fe4e6484`); row K11-a's compile fence (`7af4023e`) | In source | K11-a's guard command and `tests/AGENTS.md` landed at `c86aa1f7` |
| ACT-1076, ACT-1075, T-1065-f, ACT-1071, ACT-1073, ACT-1074, REPRO-1062-e, REPRO-1068, REPRO-0977, REPRO-1067, REPRO-1005-a to c, REPRO-1079-a to -c, REPRO-1080, the ACT-1082 cells | Accepted, still RED | As at the W8 exit |

### 14.3 Allocated to `test`

**Nothing is with `test`.** Every allocation in this section is committed
and judged (§14.2); its conditions stay as the present-tense statement of
what each cell shows. ACT-1110 has no cell by a named residual.

**T-TYPE-EXPR** ([ACT-1089](../../sprints/actions/ACT-1089-type-command-given-a-definition-commits-it-without-code-intake.md); REPL §3.1), a safety fence.

- **Risk.** The documented use of `/type` makes a later evaluation end
  the process.
- **The cell.** In `s124_type_session`: `/type (primitives/Some 1)`, then
  `(primitives/Some 1)`, then `(add-i64 5 5)`. The process exits 0, the
  second turn prints the value and the third prints 10.
- **A second subject** with a user type: `(deftype (Box a) (Mk [:a v]))`,
  `/type (Mk 1)`, `(Mk 1)`.
- **Control.** The value evaluated first, then queried, then evaluated
  again, prints it twice.
- **Wrong implementation it rejects.** A query that commits the instance
  of a constructor it has not compiled, as built; a correction for
  definition forms only.
- **By hand both subjects end on signal 11** and the control holds.

**T-IO-OPAQUE** ([ACT-1108](../../sprints/actions/ACT-1108-io-is-not-opaque-pure-is-absent-and-the-constructors-are-surface-intake.md); spec §10.1 and §10.2 as ruled on
2026-11-22).

- **Risk.** User code builds or takes apart an IO value, which the runtime
  alone may do; and the one public way to lift a value does not exist.
- **Seam and technique.** One-file programs with no prelude under `--run`.
- **Clauses.**
  1. `(primitives/pure 42)` as `main`'s value exits 42, and
     `/info primitives/pure` shows `(Fn [a] (primitives/IO a))`.
  2. Each of these is refused at compile time with a diagnostic and no
     signal: `(primitives/Pure 5)`; `(primitives/Effect 5)`;
     `primitives/Bind`, bare after an import, qualified, dotted and taken
     as a value.
  3. A match on an IO value is refused at compile time, with constructor
     arms alone and with a wildcard arm.
- **What changes in the committed cells.** T-EFFECT-FIELD's "no signal"
  becomes clause 2's refusal. T-IO-MATCH's two arms become clause 3, and
  its wildcard control becomes a subject. T-BIND-SPELLING's agreement
  becomes refusal of all four. Their `Pure` controls build IO values with
  the constructor: replace them with `primitives/pure` under clause 1.
- **Wrong implementations it rejects.** A gate on `Bind` alone, or on the
  bare name alone (2); refusal of construction that leaves matching (3);
  a `pure` that is the constructor under another name and can be matched
  (3).
- **By hand: clause 1 fails,** the name does not exist; clause 2 fails
  except for the bare `Bind`; clause 3 fails.
- **It will stay RED through the migration** of every fixture that writes
  `Pure`. That is the carried work, not this cell's.

**T-TRAIT-SPELLING, narrowed** ([ACT-1103](../../sprints/actions/ACT-1103-trait-spelled-num-eq-ord-or-display-has-its-impl-body-replaced-by-a-primitive-intake.md)). S124-Q16 is
confirmed and the four traits are library content. Each subject's clause
is now the implementation's value alone; the refusal arm is removed.

**T-VEC-FUNCTOR** ([ACT-1104](../../sprints/actions/ACT-1104-built-in-vec-is-refused-as-an-implementation-target-intake.md); spec §7.2.3).

- **The cell.** With `(deftrait (Functor f) (fmap [:(Fn [a] b) g :(f a) x]
  (f b)))` and a recursive helper over `vec-len`, `vec-get` and
  `vec-push`: `(impl (Functor f) (Functor Vec) (defn fmap [g x] (go g x 0
  [])))`, and `main` returns the third element of `fmap` of an increment
  over `[1 2 3]`: exit 4, under `--run`.
- **Controls.** The same trait implemented for `Option` gives 4; the
  helper called directly gives 4.
- **Wrong implementation it rejects.** A parameter count read as zero for
  the built-in type, as built; a correction of conventional targets that
  leaves the higher-kinded slot.
- **By hand the subject is refused** with `Vec has 0 type parameters`, and
  both controls give 4.

**T-MARKERS** ([ACT-1109](../../sprints/actions/ACT-1109-function-and-nested-io-values-do-not-display-as-the-closure-and-io-markers-intake.md); spec §12.9.1, REPL §1.5).

- **Clauses, at the REPL with no prelude.**
  1. `(let [f (fn [:primitives/Int x] x)] f)` displays `#closure`.
  2. `[(primitives/sleep 0)]` displays `[#io]`.
  3. `#io` and `#closure` as input are each refused, and the session
     continues.
- **By hand clauses 1 and 2 fail** (`<closure>`; `[<unknown-tag:4>]`) and
  clause 3 holds.
- **Committed cells that assert `<closure>`** are migrated with the
  correction, not now.

**T-SCONCAT-PUBLIC** (spec §9.7.3, as ruled at S124-Q12-R1): a guard.

- **The cell.** With no prelude and no import, a `main` that returns the
  length of `(macros/sconcat A B)` for two one-element lists exits 2,
  under `--run` and linked; and `/info macros/sconcat` shows
  `(Fn [(macros/SList macros/Sexp) (macros/SList macros/Sexp)]
  (macros/SList macros/Sexp))`.
- **Do not put `/type` of an expression before an evaluation in the same
  session:** that is T-TYPE-EXPR's defect.
- **By hand it passes.**

**T-DEFAULT-UNDEFINED** (spec §7.1.5, as ruled at S124-Q15): a guard.

- **The cell.** `(deftrait T (req [self] Int) (dflt [self] (nosuch
  self)))` alone is accepted. An `impl` that defines `req` only is refused
  with a diagnostic naming `nosuch`. An `impl` that defines both is
  accepted, and `(dflt Mk)` gives its value.
- **By hand all three hold.**

**T-EFFECT-FIELD** ([ACT-1106](../../sprints/actions/ACT-1106-effect-constructors-field-is-typed-as-the-io-value-and-holds-a-thunk-intake.md); spec §10.1), a safety fence.

- **Risk.** A well-typed program that constructs `Effect`, or binds its
  field in a match, ends on a signal.
- **Seam and technique.** One-file programs with no prelude under `--run`,
  and one REPL session. The match subjects use the `test-capture`
  platform.
- **Subjects.**
  1. `(defn main [] (primitives/Effect 5))`, under `--run` and linked.
  2. `(defn main [] (let [e (primitives/Effect 5)] (primitives/Pure 7)))`:
     the node is built and never forced.
  3. `(primitives/Effect 5)` as a REPL turn.
  4. With `peek` matching `Pure` and `Effect` and returning the bound
     field: `(primitives/str-len (peek (read-line)))`.
- **Clause, for each subject:** the process does not end on a signal. It
  exits with a status, having refused the program with a diagnostic or
  run it.
- **Narrowed on 2026-11-22.** The user ruled `IO` opaque; the clause is
  now refusal with a diagnostic (T-IO-OPAQUE, above).
- **Controls.** `(primitives/Pure 5)` gives 5, and `(peek (primitives/Pure
  7))` gives 7.
- **Wrong implementations it rejects.** A field typed as the IO's value
  and used as a closure, as built (all four); a refusal of construction
  that leaves the match (4); a guard on forcing that leaves the release of
  an unforced node (2).
- **By hand subjects 1 to 3 end on signal 11 and subject 4 on signal 7.**
- **Not asserted:** `(peek (print "MARK"))` yields the thunk's address as
  an `Int`. No outcome for it is common to every answer.
- **Defect line:** `class=scalar-as-pointer`, the locus
  `src/bootstrap.rs` as the seam `io-effect-constructor-seed`,
  `owner=/dev`.

**T-IO-MATCH** ([ACT-1107](../../sprints/actions/ACT-1107-match-on-io-with-pure-and-effect-arms-is-accepted-and-fails-on-a-bind-node-intake.md); spec §6.5).

- **Risk.** A match the checker accepts as exhaustive ends the process on
  `match failed`.
- **The cell.** `peek` with `Pure` and `Effect` arms, applied to
  `(primitives/bind (primitives/Pure 1) (fn [x] (primitives/Pure x)))` as
  `main`'s value, under `--run`.
- **Clause.** The program is refused at compile time with a diagnostic, or
  it runs to a value. Its output never holds `match failed`. **Narrowed
  on 2026-11-22** to the refusal alone (T-IO-OPAQUE, above).
- **Controls.** The same match with a wildcard arm in place of `Effect`
  gives the wildcard's value; with only the `Pure` arm it is refused as
  non-exhaustive.
- **Wrong implementation it rejects.** A cover set that leaves out a
  constructor the user cannot write, as built.
- **By hand the subject ends on the panic with exit 1** and both controls
  hold.
- **Defect line:** `class=wrong-accept`, the locus
  `crates/cranelisp-typecheck/src/adt.rs`, `owner=/dev`.

**T-BIND-SPELLING** ([ACT-1105](../../sprints/actions/ACT-1105-qualified-primitives-bind-constructs-a-node-shorter-than-the-runtime-reads-intake.md);
[IO trampoline §1.3](../../design/backend/io-trampoline.md)).

- **Risk.** One constructor is refused or accepted by how it is spelled,
  and the accepted spellings build a node the runtime reads past.
- **Seam and technique.** One-file programs with no prelude under `--run`,
  each sequencing `(Pure 1)` into a continuation that adds 41.
- **Spellings.** The bare name after `(import [primitives [Bind]])`;
  `primitives/Bind`; `primitives/IO.Bind`; and `primitives/Bind` taken as
  a value.
- **Clause.** The four programs have one outcome: all are refused with a
  diagnostic, or all exit 42.
- **Narrowed on 2026-11-22.** The user ruled `IO` opaque; all four
  spellings are refused (T-IO-OPAQUE, above).
- **Control.** The builtin `bind` in the same program shape exits 42.
- **Wrong implementation it rejects.** A gate applied to the bare name
  only, as built.
- **By hand the bare spelling is refused and the other three exit 42.**
- **What it cannot show.** The short node. On the ordinary path a
  constructor-built node gives the builtin's value and allocation balance,
  with a heap-owning intermediate too. That evidence is a module row,
  owed by `dev` with the correction. **This is a named residual:** the
  read past the allocation has no solution-level cell.
- **Defect line:** `class=silent-accept`, the locus
  `crates/cranelisp-typecheck/src/checker.rs::is_internal_constructor_check_with_state`,
  `owner=/dev`. The locus is provisional.

**T-MOD-CHILD-INDEX** ([ACT-1096](../../sprints/actions/ACT-1096-declared-child-of-a-library-module-is-replaced-by-a-file-earlier-on-the-search-path-intake.md); spec §8.11.2, as ruled at
S124-Q14: the project file "MUST NOT be indexed or loaded", and "its
presence alone MUST NOT be an error").

- **Risk.** `/search` offers an import of a symbol from a file the
  program cannot address, and a qualified reference into the library's
  child reaches the project's file.
- **Seam and technique.** A REPL session run from the project, with the
  library on the path. The library's `m` declares a public child `t`. The
  library's `m/t.cl` defines `v` as 5 and a function found nowhere else;
  the project's `m/t.cl` defines `v` as 6 and another such function. Each
  search is issued twice and the second answer read.
- **Clauses.**
  1. A search for the project file's own function prints no import row.
  2. A search for the library child's own function prints its row.
  3. After `(import [m [f]])`, `(f)` gives 5.
  4. A qualified call of the library child's own function gives its
     value, and a qualified call of the project file's is refused.
  5. The session exits 0, and no turn before clause 4's refusal prints an
     error.
- **Control.** The same session with no project file meets clauses 2 to
  5.
- **Wrong implementations it rejects.** A module named from any file
  under the project root, as built (1, 2, 4); a correction of loading
  that leaves the index (1, 2); a refusal of the mixed hierarchy (5).
- **By hand, clauses 1 to 4 fail** and the control holds.
- **Defect line:** ACT-1096's, with the locus for the index cells as the
  seam name `index-feed-module-enumeration` until the site is read.

**Returned: T-MOD-CHILD's values.** In `s124_child_project` the library's
child returns 1 and every subject asserts exit 1. A compile that is
refused also exits 1, so a build that rejects the project file with an
error passes the cells, and the ruling forbids that outcome. Use values
that are not an error status, for example 5 for the library and 6 for the
project file, and keep the override control at the project's value.

**T-TRAIT-SPELLING** ([ACT-1103](../../sprints/actions/ACT-1103-trait-spelled-num-eq-ord-or-display-has-its-impl-body-replaced-by-a-primitive-intake.md); spec §7.3).

- **Risk.** A program that declares its own `Num`, `Eq`, `Ord` or
  `Display` gets the compiler's primitive where its implementation says
  otherwise, with no diagnostic.
- **Seam and technique.** One-file programs with no prelude, each
  declaring the trait and one implementation for `Int` whose body differs
  observably from the primitive, scored by exit status under `--run`. The
  decision is made in typecheck and does not differ by mode.
- **Subjects.** The six programs of the filing's table: `Num` called
  directly, taken as a value, and reached through a constrained function;
  `Eq`; `Ord`; `Display`.
- **Clause, for each subject:** the result is the implementation's value,
  **or the program is refused with a diagnostic.** It is never the
  primitive's value.
- **Narrowed on 2026-11-22.** S124-Q16 is confirmed and the traits are
  library content: the clause is the implementation's value alone.
- **Controls.** The `Num`, `Eq` and `Display` subjects with the trait
  renamed (`Numb`, `Eqq`, `Displayy`) give the implementation's value.
- **Wrong implementations it rejects.** The spelling-keyed table as built
  (every subject); a correction of direct calls that leaves the value or
  the constrained route (those two subjects); a correction for `Num`
  alone (the other three traits).
- **Defect line:** `class=spelling-keyed-decision`, new in the vocabulary;
  the locus
  `crates/cranelisp-typecheck/src/traits/dispatch.rs::primitive_for_trait_method`;
  `owner=/dev`.

**T-VEC-IMPL** ([ACT-1104](../../sprints/actions/ACT-1104-built-in-vec-is-refused-as-an-implementation-target-intake.md); spec §7.3 Case 1 and §3.2.7).

- **Risk.** No trait can be implemented for a vector type, and the
  refusal tells the user to apply `Vec` to no argument.
- **Seam and technique.** One-file programs with no prelude under `--run`,
  with `(deftrait Sz (sz [self] Int))`.
- **Subjects.** `(impl Sz (Vec Int) (defn sz [v] (vec-len v)))` and
  `(impl Sz (Vec a) …)`, each with `(sz [1 2 3])`: the exit status is 3.
- **Negative.** `(impl Sz Vec …)`, the bare constructor, is refused, as
  Case 1 requires. Do not assert its wording: today's is not the kind
  mismatch the specification describes.
- **Control.** `(impl Sz (Option a) (defn sz [v] 4))` with `(sz (Some 1))`
  gives 4.
- **Wrong implementations it rejects.** The zero-parameter reading as
  built (both subjects); a correction for concrete arguments only (the
  second subject); an acceptance of the bare constructor (the negative).
- **Defect line:** `class=wrong-reject`, the locus
  `crates/cranelisp-typecheck/src/traits/impl_check.rs`, `owner=/dev`.

**T-TRAIT-ONE-PARAM** (spec §2.2.3 and §5.3.2, as ruled at S124-Q11): a
guard.

- **The cell.** `(deftrait (Ix c a) (at [:(c a) x] a))`, with no prelude,
  is refused with a located parse error. By hand: `too many elements in
  trait head`.
- **Control.** The existing one-parameter cell,
  `hkt_deftrait_declaration_with_type_constructor_parameter_succeeds`.
- **What it rejects.** A grammar that again admits a second parameter.
  The committed cell with that message is for an `impl` head, not a
  `deftrait` head.

**T-SPLICE-BARE** (spec §9.7.0 and §8.8.3, as ruled at S124-Q12): a
guard.

- **The cell.** With no prelude and no import:
  ``(defmacro add-all [& xs] `(primitives/add-i64 ~@xs))`` and a `main`
  returning `(add-all 3 4)` exit 7, under `--run` and at the REPL. By hand
  it does.
- **What it rejects.** An expansion of unquote-splicing that names a
  library function, or a compiler helper by a bare name the module must
  import. The committed splice cells run under a primitives-only prelude.

**T-REFUSED-SAVE-CACHE** ([ACT-1102](../../sprints/actions/ACT-1102-refused-save-leaves-the-cache-ahead-of-the-backing-file-intake.md); REPL §15.2), a safety
fence.

- **Risk.** A session that follows a refused save restores, from cache, a
  definition its backing file does not hold. Calling it ends the process
  on a signal.
- **Seam and technique.** T-SAVE-PRODUCT's first subject as session 1,
  then a second session in the same directory **with the cache kept**.
- **Clauses, for session 2 entering `(f)` then `(add-i64 5 5)` after its
  import:** the process exits 0; and `(f)` either gives 1 or is refused as
  undefined. The second turn prints 10.
- **Controls.** Session 2 with the cache directory removed refuses `(f)`
  as undefined and exits 0. A session that saves `f` and `g`, whose file
  is then rewritten to hold `g` only, with the cache kept, refuses `(f)`
  and gives 2 for `(g)`.
- **Wrong implementations it rejects.** A cache written from session
  state after the save was refused, as built (the exit clause); a cache
  that is never trusted after any change (the second control still
  restores `g`).
- **What it cannot show after ACT-1101 is corrected.** That route to a
  refused save is then closed, and the cell passes without reaching the
  defect. `dev`(`src/`) owes a module row that refuses a regeneration by
  construction.
- **Defect line:** `class=artifact-underkey`, the locus
  `src/session_v4/lifecycle.rs::flush_final_persist`, `owner=/dev`.

**T-SAVE-PRODUCT** ([ACT-1101](../../sprints/actions/ACT-1101-session-save-refused-after-a-parametric-product-type-is-constructed-intake.md); REPL §15.1: "the REPL MUST
persist interactive definitions to disk").

- **Risk.** A session that has built one value of a parametric product
  type stops saving. The user sees a warning per definition and loses
  every later definition at restart.
- **Seam and technique.** A REPL session with no prelude and piped input,
  the backing file read afterwards, then a second session in the same
  directory, as the `repl_persist` restart cells.
- **Subjects.**
  1. `(deftype (P2 a b) [:a x :b y])`, `(P2 1 2)`, `(defn f [] 1)`.
  2. `(primitives/Pair 1 2)`, `(defn f [] 1)`.
  3. A function whose body builds `(Pair 1 2)`, called once, then
     `(defn g [] 2)`.
- **Clauses, for each subject:** no output line holds `failed to save`;
  the backing file holds the later definition; a second session evaluates
  it.
- **Controls, which pass today:** the same shape with
  `(deftype (Box a) (Mk [:a v]))` and `(Mk 1)`; and with
  `(primitives/Some 1)`.
- **Wrong implementations it rejects.** A save that refuses on a
  constructor instance, as built (all three); a correction for the seeded
  `Pair` alone (subject 1); one for a REPL expression and not for a
  compiled function body (subject 3); a save that drops the type itself
  (the controls and the file clause).
- **Defect line:** `class=enumeration-miss`, the locus
  `src/save.rs::generate_types`, `owner=/dev`.

**T-MACRO-SIBLING** ([ACT-1100](../../sprints/actions/ACT-1100-selective-derive-import-refusals-intake.md); spec §9.3.4: a macro's expansion
may reference "macros, including macros defined earlier in the same
module").

- **Risk.** A library macro that expands to a call of its own companion
  macro works only if the user happens to import the companion, and is
  otherwise refused as an undefined variable.
- **Seam and technique.** A library module `d` holding
  ``(defmacro inner [x] `(add-i64 ~x 1))`` and two macros that expand to a
  call of it: one by quasiquote, one building the symbol `inner` by hand.
  The using program imports one outer macro by name and nothing else from
  `d`.
- **Clauses.** `(outer 2)` gives 3 for each of the two outer macros, at
  the REPL, under `--run` and linked.
- **Controls, in the same fixture:** with `(import [d [*]])` the result is
  3; with only the outer macro imported, a user-typed `(d/inner 2)` is 3.
- **Wrong implementations it rejects.** A lookup for the expansion's
  macro in the using module's scope, as built (both subjects); a
  correction for quasiquoted references only (the hand-built subject).
- **By hand, both subjects are refused** with `undefined variable:
  d/inner`, in both modes, and both controls give 3.
- **Defect line:** `class=wrong-scope-lookup`, `owner=/dev`, and the locus
  `src/process_form/macro_resolution.rs`.
- **Do not assert** the `begin` diagnostic that the standard library's
  combined `derive` shows. It is a consequence, and its wording is a
  separate lead.

**The Phase 6b allocations, committed.**

| Allocation | Filing | Class | State at `11ea995e` |
|---|---|---|---|
| T-TRAIT-SPELLING | ACT-1103 | Acceptance | 6 RED, 3 controls green |
| T-VEC-IMPL | ACT-1104 | Acceptance | 2 RED, the negative and the control green |
| T-TRAIT-ONE-PARAM | — | Acceptance, a guard | Green |
| T-SPLICE-BARE | — | Acceptance, a guard | 2 green |
| T-REFUSED-SAVE-CACHE | ACT-1102 | Safety fence | 1 RED, 2 controls green |
| T-SAVE-PRODUCT | ACT-1101 | Acceptance | 3 RED, 2 controls green |
| T-MACRO-SIBLING | ACT-1100 | Acceptance | 6 RED, 12 controls green |
| T-TYPE-ERR, replacing T-TYPE-DEFN | ACT-1089 | Acceptance | 5 subjects RED; the guard cell and the control green |
| T-TRACE-OWNING | ACT-1094 | Acceptance | 12 green |
| T-TYPE-MACRO | ACT-1099 | Acceptance | RED |
| T-STDLIB-ADT-TRAITS | — | Acceptance, of the library | Green in three modes, 29 legs |
| T-STDLIB-SELFTESTS | — | Maintenance check | 8 shells and the proof cell green |

**T-TYPE-ERR** ([ACT-1089](../../sprints/actions/ACT-1089-type-command-given-a-definition-commits-it-without-code-intake.md); REPL §3.1: "`/type` given a
definition form MUST report an error. It MUST NOT evaluate the form or
define anything in the session").

- **Risk.** `/type` given a definition answers with the type of whatever
  was evaluated before it, so the user reads a plausible, wrong type.
- **The cell it replaces.**
  `repl_introspection::s124_1089_definition_reports_its_function_type`
  requires the definition's function type. That rule is withdrawn, and the
  cell would fail on a conforming build. Its `defn` subject becomes the
  first subject here.
- **Seam and technique.** `s124_type_session`. **Every session first
  enters the turn `"abc"`,** so an earlier result exists: with none, the
  build prints an error by accident and the cell cannot fail.
- **Clauses, for the response to the `/type` turn alone:**
  1. it holds an error in the form of REPL §5.1: a category and a
     message, with the location's form left open;
  2. it holds no type line. In particular not `:primitives/String`, the
     earlier turn's type, and not a function type, the withdrawn answer.
- **Do not assert the message's words.** The specification calls the
  phrase "definition form has no type" illustrative.
- **Subjects, one cell each:** `(defn q [:Int n] n)`; `(deftype T A B)`;
  `(deftrait Sz (sz [self] Int))`; `(impl Sz T (defn sz [self] 7))` after
  its trait and type; `(defmacro mm [x] x)`.
- **Guards, in one cell:** `(import [primitives [add-i64]])`,
  `(export [primitives [add-i64]])`, `(mod foo)` and `(platform stdio)`
  each meet both clauses.
- **Control.** `/type (add-i64 1 2)` after the same first turn prints
  `:primitives/Int` and no error.
- **Wrong implementations it rejects.** The stale answer as built (the
  four subjects); the definition's own type (clause 2); an error only when
  no earlier result exists (the first turn); a correction for `defn` alone
  (the other three subjects); a refusal of every `/type` (the control).
- **Whether the form is defined is not asserted here.** REPRO-1089's four
  subjects and T-TYPE-PURE hold that, unchanged.
- **Not covered.** `const` and `def` are prelude macros, and no stdlib-free
  session has them as definition forms. The `-` variants share their
  form's path.

**T-TRACE-OWNING** (ACT-1094 (closed S124), *A second defect*; spec §12.3.1
and §4.12.2).

- **Risk.** A traced body whose value owns heap memory strands what the
  value holds, or the value is released before the root's result is
  rendered from it.
- **Seam and technique.** No-prelude programs read through the harness's
  allocation statistics with lenient evaluation off, as
  `trace::s124_trace_root_heap_result_and_balance`.
- **Subjects.** A traced call returning (a) a one-field record whose field
  is a `String` built at run time, and (b) a vector of two such `String`s.
  In each, the value is built inside the traced call, so the trace form's
  release is the one that frees it.
- **Clauses, for each subject:** allocations equal frees; and the root's
  result equals the result of the child frame for that call, and is not
  empty.
- **Modes.** `--run` cold, `--run` restored from cache, and `--link`. The
  module row cannot reach the object modes, where the glue is reached
  through a relocation.
- **Wrong implementations it rejects.** A release with no drop glue (the
  balance clause); a release before the collect call reads the value (the
  equality clause, or a fault); glue that resolves only in the JIT (the
  modes).
- **It arrived green, and `qa` has not seen it fail.** The fault is
  observed only through `dev`'s module row with the old discard planted.
  No earlier tree is built to show the red.

**T-TYPE-MACRO** ([ACT-1099](../../sprints/actions/ACT-1099-type-command-refuses-an-expression-that-uses-a-macro-intake.md); REPL §3.1).

- **Risk.** `/type` cannot answer for any expression that uses a macro,
  and says the macro is undefined.
- **The cell.** In `s124_type_session`, after
  ``(defmacro twice [x] `(add-i64 ~x ~x))``: `/type (twice 2)` prints
  `:primitives/Int` and no error.
- **Control.** `(twice 2)` prints `:primitives/Int 4` in the same session.
- **Wrong implementation it rejects.** A type query that skips macro
  expansion, as built.
- **It fails today** on the type clause.

**T-STDLIB-ADT-TRAITS,** library conformance under the standard-library
exception, in `tests/stdlib_conformance.rs`.

- **Risk.** An implementation that passes its module's self-test is not
  reachable from a user program through the default prelude, or its
  instance is missing from a linked binary.
- **Authority.** The library's own documented behaviour, in its plan and
  its modules' docstrings. It is not the language specification. The
  mechanisms the cell exercises are `spec/07-traits.md` §7.3.3 and
  `spec/08-modules.md` §8.4.8.
- **The cell.** One driver program scored by its exit status, in the REPL,
  under `--run` and `--link`, as the existing `…_across_modes` drivers.
- **Legs.** For each of `Option`, `Result`, `Pair`, `List` and `Either`:
  `Eq` on equal values, on unequal payloads and, where the type has more
  than one constructor, on different constructors;
  `Ord` on one ordered pair; `Display` against the documented text. One
  nested leg, `(Some (Some 1))`, for each trait. `Default` for `Option`.
- **Wrong outcomes it rejects.** An implementation visible only inside
  the library (every leg); an equality that is always true (the unequal
  legs); an instance absent after linking (the linked mode).
- **`dev`(stdlib) confirms the expected texts** where a docstring does not
  give one. `test` does not derive them from the implementation.

**T-STDLIB-SELFTESTS,** a maintenance check on the standard library.

- **What it protects.** The library's evidence is its self-tests
  (`stdlib/AGENTS.md`), and they are run by hand only. The suite compiles
  every public module and runs none of its tests.
- **The cell.** A REPL session over the workspace library that runs each
  module's self-tests by the recipe in `stdlib/AGENTS.md`. Every module
  that declares a test child reports at least one test and no failure.
- **The non-zero clause is the point.** A module loaded by a null import
  reports zero tests, which reads as green.
- **No total is pinned.** A count would change with every library edit.
- **Its authority.** A failure blocks claims about the library. It is not
  acceptance evidence for the compiler.
- **Cost.** `test` reports its time in the suite. If it passes a minute
  under load, split it by the library's top-level shells.

**The Phase 6a allocations, committed.**

| Rank | Allocation | Filing | Class | State at `b72742f7` |
|---|---|---|---|---|
| 1 | T-TYPE-PURE, the `impl` cell | ACT-1089 | Safety fence | RED: signal 11 |
| 2 | T-MOD-CHILD | ACT-1096 | Acceptance | 4 RED, control green |
| 3 | T-TRACE-ROOT | ACT-1094 | Acceptance | 9 RED, 4 controls green; corrected since |
| 4 | T-SEARCH-REACH | ACT-1092 | Acceptance | 2 RED, 1 green |
| 5 | T-TYPE-PURE, the other cells | ACT-1089 | Acceptance | 2 RED, 3 guards green |
| 6 | T-TRAIT-SCALAR | ACT-1097 | Acceptance | 3 RED, 2 controls green |
| 7 | T-PRINT-BALANCE | ACT-1018 | Acceptance | 4 RED, 4 controls green |
| 8 | T-EXEMPLAR-TESTS | — | Maintenance check | 2 green |

**Advisory, not returned.** The `import` and `defmacro` guards of
T-TYPE-PURE look for `undefined` and the name anywhere in the output. They
discriminate today.

Two items are held:

| Item | Held on |
|---|---|
| **T-OWNER,** below | The user's decision to build the cache-owner lock (ACT-1085) |
| The outcome clause and the session-save and restart legs of REPRO-1081 | The user's ruling |

**T-TYPE-PURE** ([ACT-1089](../../sprints/actions/ACT-1089-type-command-given-a-definition-commits-it-without-code-intake.md); REPL §3.1: "`/type` MUST NOT
evaluate a non-pure form", and "the query MUST NOT define anything in the
session").

- **Risk.** A query that is documented as changing nothing changes the
  session: an implementation is installed with no code and the next call
  ends the process; a type or trait appears that no source file holds; an
  effect runs.
- **Seam and technique.** A REPL session with no prelude and piped input,
  as `s124_type_session`. Each cell gives `/type` one form and then reads
  the session by ordinary turns. The `IO` cell loads the `stdio` platform.
- **No clause reads what `/type` itself prints.** That is T-TYPE-ERR.

| Cell | Given to `/type` | Clauses | Control | By hand, before the cell |
|---|---|---|---|---|
| `impl` | `(impl Sz T (defn sz [self] 7))`, after `(deftrait Sz (sz [self] Int))` and `(deftype T A)` | The process exits 0; `(sz A)` is refused with the no-implementation error; a later `(add-i64 5 5)` prints 10 | The same session without the `/type` line refuses `(sz A)` the same way | **Signal 11,** 4 of 4 |
| `deftype` | `(deftype T A B)` | `/list` prints `(no definitions)`; `A` is refused as undefined | — | RED: `T` is listed and `A` resolves |
| `deftrait` | `(deftrait Sz (sz [self] Int))` | `/list` prints `(no definitions)` | — | RED: `Sz` is listed |
| `IO` | `(print "MARK-1")` | `MARK-1` is absent from the output; a later `(print "MARK-2")` prints `MARK-2` | The later turn is the control: the marker is observable and input is not echoed | Passes |
| `import` | `(import [primitives [add-i64]])`, in a session that has not imported it | `(add-i64 1 2)` is refused as undefined | The import entered as a turn, then the call, prints 3 | Passes |
| `defmacro` | `(defmacro mm [x] x)` | `(mm 3)` is refused as undefined | The macro entered as a turn, then the call, is not refused | Passes; `qa` did not run this control |

- **Wrong implementations it rejects.** A correction that stops committing
  `defn` only (the three RED cells); a query that checks by evaluating
  (`IO`, `import`, `defmacro`); a later report for non-value forms that is
  built by running the form (the same three).
- **What it cannot show.** That a pure expression is not evaluated: no
  ordinary turn observes it, and the §3.1 table row carries that claim.
  `platform` has no cell: it is refused today as an undefined name
  before any check, as `import` is. `export` was not probed.
- **"Non-pure" is not defined by the specification.** Every clause above
  holds whether it means an `IO`-typed expression or a form that changes
  the session, so no clause waits on a reading.

**T-TRACE-ROOT** (ACT-1094 (closed S124); spec §4.12.2: the value "is used
only to produce the root trace node's formatted result string").

- **Risk.** A trace value does not say what the traced expression
  evaluated to. A correction can also format the value after releasing it,
  or leak it.
- **Seam and technique.** A program whose exit status is decided by
  matching the root `TraceCall` and comparing its result field, as the
  filing's subjects do; no prelude.
- **Clauses.**
  1. The root's result of `(trace (ident 42))` is `"42"`.
  2. The root's result of `(trace 42)`, with no call in the body, is
     `"42"`.
  3. For a body whose value is heap-allocated (a `String` returned by a
     one-argument function), the root's result equals the result field of
     the child frame for that call, and the run's allocation statistics
     balance.
- **Modes.** Clauses 1 and 2 under `--run` cold, `--run` restored from
  cache, `--link`, and the REPL. Clause 3 under `--run` only. The modes are
  earned: the formatting descriptor reaches an object through a relocation
  the JIT does not use.
- **Control.** The child frame of clause 1's call holds `"42"`, in the
  same program.
- **Wrong implementations it rejects.** The discard as built (1, 2); a
  correction on the path that swaps slots and not on the path that finds
  no traced function (2); a format after the release, or an unreleased
  value or string (3); a descriptor that works only in the JIT (the modes).
- **No clause reads the root's name or parameters.** Spec §4.12.8 and the
  compiler disagree about them; the question is with `spec` (§14.8).
- **Defect class: `unrecorded-value`,** added to the
  [controlled vocabulary](../AGENTS.md#defect-repro-notation--defect) for
  these cells. Locus: `crates/cranelisp-backend/src/compiler/trace_codegen.rs::compile_trace`;
  owner `/dev`.
- **What it cannot show.** Which of the two compile paths a given program
  takes. `dev`(backend) owes a module row for each with the correction.

**T-SEARCH-REACH** ([ACT-1092](../../sprints/actions/ACT-1092-search-index-omits-a-module-whose-import-names-an-unloaded-or-compiling-module.md); REPL §17.19 R10: "a reachable
module MUST NOT be omitted merely because it or a dependency is not yet
loaded or is still compiling in the session").

- **Risk.** `/search` answers `no importable symbols matched`, as from a
  complete index, for a symbol the project defines.
- **Seam and technique.** A REPL session with no prelude over a project
  root of four modules, none loaded and with no cache: `p` defines `pf`;
  `m` imports `pf` from `p` and defines `mf`; `t` imports `mf` from `m` and
  defines `tf`; `x` imports a name from a module that does not exist and
  defines `xf`. Each query is issued twice, and the second answer is read,
  as the existing `search_cf2` cells do.
- **Clauses.**
  1. `/search mf` prints the row `(import [m [mf]])`.
  2. `/search tf` prints the row `(import [t [tf]])`.
  3. `/search xf` prints no row `(import [x [xf]])`, and the session exits
     0.
- **Control.** `/search pf` prints `(import [p [pf]])` in the same session:
  the feed ran and settled, and the fault is the dependency.
- **Wrong implementations it rejects.** Imports resolved from the session's
  tables only, as built (1, 2); one level of dependency loading (2); a
  result that depends on which of a module and its dependency the feed
  meets first, since `m` sorts before `p` and `t` after `m` (1, 2); rows
  taken from a module whose imports cannot be resolved (3).
- **Fixture property.** Match the whole import form. `/search tf` also
  prints an unrelated `primitives` row today.
- **Named residual, accepted by the user on 2026-11-20: the *still
  compiling* clause has no solution-level cell.** Its face needs a dependency that is registered and not yet
  published when the feed reaches the dependent. By hand it appeared in
  115 of 420 launches under fourteen-way load and 0 of 30 alone, with a
  1,200-definition fixture. A cell built from user commands cannot select
  that interleaving. Its evidence is the second module row below.
- **`dev`(`src/`) owes two module rows with the correction,** over
  `checked_typecheck_module`: the dependent's rows are produced when its
  dependency (i) is absent from the live tables with its source on the
  path, and (ii) is registered in the live tables with no definitions yet.
  Row (ii) is seen to fail before the correction.

**T-MOD-CHILD** ([ACT-1096](../../sprints/actions/ACT-1096-declared-child-of-a-library-module-is-replaced-by-a-file-earlier-on-the-search-path-intake.md); spec §8.2.5: a `mod` declaration
resolves "to the child directory path only").

- **Risk.** A library runs a file its source does not name, because a
  project or an earlier library directory holds a file at the same
  relative path. That includes a private child.
- **Seam and technique.** The filing's four files, with `lib/` as a
  library directory and `proj/` the project root. The exit status is the
  value of the library's function.
- **Clauses.**
  1. `--run` exits 1.
  2. `--link`, then the binary, exits 1.
  3. `--run` exits 1 on a launch that follows a cached launch made before
     `proj/m/t.cl` existed.
  4. With `proj/m/t.cl` absent and a second library directory, earlier on
     the path, holding only `m/t.cl` with the other value, `--run` exits 1.
- **Control.** With `proj/m.cl` and `proj/m/t.cl` both present the exit is
  2: the project replaces the module and its child, as §8.11.2 allows, and
  the fixture's second file is loadable.
- **Wrong implementations it rejects.** The search-path probe as built
  (1, 2); a correction at fresh enrolment that the cached route does not
  share (3); one that excludes the project root only (4); one that stops
  honouring the project's own module (the control).
- **No clause reads what `proj/m/t.cl` is** when `m` is the library's. That
  is a question for `spec` (§14.8).

**T-TRAIT-SCALAR** ([ACT-1097](../../sprints/actions/ACT-1097-trait-signature-accepts-a-bare-primitive-type-name-that-is-not-imported-intake.md); spec §3.1 and §8.9.1).

- **Risk.** A module compiles with a type name it never brought into
  scope, in one family of positions only, so the import rule holds or not
  by where the name is written.
- **Seam and technique.** One-file programs with no prelude and a fully
  qualified `main`, under `--run`. Typechecking does not differ by mode.
- **Subjects, each refused with a nonzero exit and a diagnostic that names
  `Int`:**
  1. `(deftrait T (f [self] Int))`. **Do not assert the diagnostic's
     kind:** §3.1 gives an unknown type and §7.1's trailing-element rule an
     undefined name.
  2. `(deftrait T (f [self :Int n] primitives/Bool))`, which also says
     `unknown type`.
  3. `(deftrait (F f) (cnt [:(f Int) x] primitives/Bool))`, which also
     says `unknown type`.
- **Controls.** Subject 1 with `primitives/Int`, and with
  `(import [primitives [Int]])` first, each exit 0.
- **Wrong implementations it rejects.** The fast path as built (all
  three); a correction in the conventional context and not the
  higher-kinded one (3); one for the return position only (2); a refusal
  of the qualified or imported name (the controls).
- **What it does not cover.** `(Vec Int)` in a signature is also accepted,
  by a path `qa` did not read; `test` adds it as a fourth subject if it is
  refused by the same correction, and reports it otherwise.

**T-PRINT-BALANCE** ([ACT-1018](../../sprints/actions/ACT-1018-exemplar-warm-solve-residual-intake.md); spec §12.3.1; the
[stdio contract](../../platforms/stdio/spec.md), consumer requirement 4).

- **Risk.** Each `print` of a value the caller owns strands one block.
  Performance only; it is the whole of the exemplar guard's residual.
- **Seam and technique.** A no-prelude program over the `test-capture`
  platform, read through the harness's allocation statistics with lenient
  evaluation off.
- **Subjects, each with allocations equal to frees:** a `main` of
  `(print "a")`; a `main` of `(print (str-concat "a" "b"))`. Under `--run`
  and `--link`.
- **Controls, which balance today:**
  `(bind (Pure "abc") (fn [s] (print s)))`, where the argument is a
  continuation's parameter, and `(Pure 0)`.
- **Wrong implementations it rejects.** A release that is missing for an
  owned argument (the subjects); a correction that releases twice where
  the argument is retained first (the first control, which would then
  fail or fault).
- **It does not attribute the block** among the platform crate, the
  backend and the runtime. It stays unattributed with ACT-1018.

**T-EXEMPLAR-TESTS,** a maintenance check on the exemplar.

- **What it protects.** `exemplar/tests.cl` is run by hand only, so the
  showcase can stop passing its own tests without a failing test.
- **The cell.** From a scratch copy of `exemplar/`, with the workspace
  standard library and platforms, `--run tests.cl` exits with the count
  `exemplar/AGENTS.md` states, with lenient evaluation on and with
  `CRANELISP_NO_LENIENT=1`.
- **Its authority.** A failure blocks claims about the exemplar. It is not
  acceptance evidence for the compiler, and it is not the evidence that
  parallel and serial evaluation agree: that claim's cells are the suite's
  own. The count is the exemplar's (41 at `b72742f7`, 43 since `8fd21ddd`);
  `dev`(exemplar) and `test` change the two together.
- **It uses the standard library** under the exemplar's standing
  exception, as `tests/exemplar_web.rs` does.


**T-OWNER** (ACT-1085; int §7.7, *One cache owner per project directory*),
held. Stated now so the allocation is on record; it is re-read against the
design when the lock is scheduled.

- **Risk.** Two processes on one project directory write one cache, and a
  later cached launch runs an object that does not match its source.
- **Seam and technique.** A REPL session held at its prompt by the staged
  harness, which has loaded neither `app` nor `lib`. While it waits, a
  second process runs `--run app.cl` in the same directory.
- **Clauses.**
  1. The second process exits 41 inside the cell's time limit.
  2. The project's cache directory is byte for byte the same before and
     after the second process; in particular it holds no `app.o`.
  3. After the first session ends, a further `--run app.cl` leaves
     `app.o` in the project's cache.
- **Control.** The second process with no session alive leaves `app.o` in
  the project's cache.
- **Wrong implementations it rejects.** No exclusion (clause 2); a lock
  that waits (clause 1); a lock that outlives its owner (clause 3).
- **What it cannot show.** That two generations no longer mix: that needs
  a particular interleaving, which no fixture built from user commands
  selects. The design's falsifier stays a named residual.

### 14.4 Residuals

**Decided in this read: recorded, no cell.**

| Asserted residual | Decision | Reason |
|---|---|---|
| The nice worker meets no covered member without a table (int §7.6.4) | Record. The existing cells observe its falsifier | Its falsifier is an object pass stopped by B10's located error. A stopped pass refuses the link (T-LINK-STOP), so each `--link` trace cell fails if it occurs on their paths. Under `--run` a stopped pass leaves no object and the next launch compiles the module again |
| C1's stop: no program that builds has an object pass still held on an unpublished member when objects are awaited (int §7.6.4, *The object pass waits*) | Record. Existing cells observe its falsifier | The stop refuses the link and leaves no object. `trace::s124_1087_subject_link` and `trace::s124_1087_subject_run_restored` are in the one population where a pass is held, and each fails if the stop occurs. Every other `--link` cell and every cell asserting a cache hit observes it elsewhere. The stop itself is pinned by two module rows (§14.2) |
| No module outside `arch`'s population compiles while the prelude is unpublished (int §7.6.4, *Which modules compile while the prelude is unpublished*) | Record. **No cell: no fixture is known** | The falsifier is a scheduler-trace reading, and `design`(int) read the load paths and found no program that produces it. The harm is a first launch with fewer trace frames. One reading supports the claim: a form in a module the prelude does not reach, beside a 400-definition prelude, recorded its frame in 10 of 10 cold launches (`f8c55626`) |
| The prelude is read as it stands for a module compiled before it publishes (int §7.6.4; `arch`'s decision in tracing §5.1) | **A cell: REPRO-1087's first-launch cell, RED** | The residual stands by `arch`'s decision and is carried on that cell as a defect of the binary (ACT-1087). C1 corrected the restored and linked launches |
| A macro checkpoint's covered set is a subset of the finished module's (int §7.6.4; tracing §5.1) | Record | The falsifier needs a trace form evaluated inside a macro clause, whose extent can enter only modules already in the checkpoint's set. Tracing §5.1 names the one route outside it: a function value the clause obtains at run time, for example from `discover-tests`. The harm is a shorter diagnostic value in compile-time code. A cell costs more than the residual. Not probed |
| Within a module, trace wrapper, descriptor and slot order followed a hash map (review advisory) | **Closed for the trace form** (`e8a9cac5`, with its module row) | A control module with no trace form also gave differing objects across cold builds (`f8c55626`), so whole-object bytes are not a function of the source, and no design requires them to be. Not re-measured |
| The emitted swap installs a wrapper only over a non-zero original (`trace_codegen.rs`) | Record; a module row if `dev`(backend) can write one cheaply | No row executes the guard. A call through an empty slot fails with or without it, so the guard changes no outcome `qa` can name |

**Wrapper bodies have no golden, and get none.** The correction of
ACT-1088 changed only wrapper bodies, and no golden frame moved (§14.2).

- **What a golden would add.** It is a change detector: any edit to
  wrapper emission would show as a hunk. `qa` can name no wrong outcome it
  rejects that the committed evidence passes. A direct call restored in the
  plain or the curry wrapper fails the backend's slot-call row and
  REPRO-1088.
- **What it would cost.** The CLIF dump would have to render wrapper
  bodies, which is a backend change, and both corpora would be captured
  again and re-read at every later wrapper change.
- **The residual is elsewhere.** Tracing §3.5 grades the obligation
  measured for the wrapper and notes that it is not structural: a new
  emission site that calls a slotted function by its function id still
  compiles. A wrapper golden does not see a new site either.
- **The cheaper observer of that residual is the object's relocations.**
  A direct call to a function of the unit leaves a call relocation against
  the function's symbol; a call through a slot leaves none. By hand, over a
  program with a plain and a curry wrapper: the object from a binary built
  before the correction (a release build of 2026-11-18) holds
  `R_AARCH64_CALL26 af` and `R_AARCH64_CALL26 add2`; the object from
  `ee65d9aa` holds no call relocation at all.
- **The module row is in source** (`4407b008`, §14.2). It is a safety
  fence for tracing §3.5's obligation over the objects `compile_to_module`
  emits. It cannot show a JIT-only emission path.

**Standing.**

- **Two processes on one project directory share its cache with no
  exclusion** (ACT-1085). The face is a later cached launch that runs code
  differing from its source. It predates S124, is asserted with a named
  falsifier and is not reproduced; its control is designed and not built.
  It is not carried past the sprint without the user's decision.
- **The review of `a812faaa`, `3dbc3db5` and `79a8c94c`** was to ride the
  integrated review with two questions (can a reader the restore walk runs
  wait on the module being walked; can a stopped-pass record survive a
  later publication). Whether those three and the two questions were
  covered is `sprint`'s to confirm (§14.8).
- **The link's refusal carries a synthetic location** (`app.cl:1:1`,
  `module error at 0..0`) for a condition that has no source position. A
  lead for `design`(int); not filed.
- **ACT-1081's outcome has no ruling.** Every route accepts the program.
- **A REPL definition holding a trace form, and a module a later turn
  loads,** is open with the user
  ([tracing §5.1](../../design/arch/tracing.md#51-which-modules-a-form-covers)).
  Current behaviour stands and no cell holds it.
- **Row D3's mounts are evidenced only through a loaded owner** (ACT-1079),
  and the cycle walk's fixpoint over a chain of mounts has no executed
  evidence.
- **The failed-dependency refusal does not run at a fresh load**
  ([int §6.11](../../design/int/int.md#611-module-cycles-at-publication),
  *Failed dependency*). Asserted with its falsifier: a module that
  compiles at a restart and is refused by a session rebuild. One fixture
  of `qa`'s did not reproduce it.
- **ACT-1036 leaves one residual:** a macro-produced function restored
  from cache that references `discover-tests` is reported at `0..0`.
  `design`(int) accepts it; the user has been asked. No cell.
- **`/type` in a locked session** admits `/type` and refuses every
  definition (REPL §14.5). `/type` given a definition there was not probed
  (ACT-1089).
- **The search index omits a module whose import names a module that is
  not loaded or is still compiling** ([ACT-1092](../../sprints/actions/ACT-1092-search-index-omits-a-module-whose-import-names-an-unloaded-or-compiling-module.md)).
  The search then answers as from a complete index. It is a defect
  against REPL §17.19 R10. The *still compiling* clause has no
  solution-level cell and is a named residual awaiting the user's approval
  (§14.3, T-SEARCH-REACH).
- **ACT-1018 carries on a measured residual of 2,** and its guard measures
  it. Its block is stranded without the standard library (2026-11-20);
  the earlier reading that it was not is withdrawn in the filing.
- **A rewrite while a module's own cached load is outstanding** is
  recorded in int §7.7 as a residual with its falsifier. Not observed.
- **ACT-1073's owner is still provisional,** and the clauses behind a first
  RED have not executed for REPRO-1068, ACT-1073's cell and T-1065-f.
- **A multi-signature family's mode-changing redefinition has no cell**
  (§9.4). Awaiting the user's approval.
- **The bind-chain pass's import assertion has no evidence.** Its named
  falsifier is T-1065-f, which executes once ACT-1075 is corrected.
- **Suite readings from the Codex sandbox overstate the failing set.** A
  reading that gates a wave is taken in the primary harness.

### 14.5 The category census

**The census reads zero from every program at `128255fc`.** It was armed in
the full run at that commit, and in the four before it with the same
result.

- **The instrument.** The absent, field and frame points, each with its
  planted positive leg and concrete twin in the backend's module tests.
- **The reading** (298,887 lines):

| Partition | Frames compiled | Distinct symbols | Records on the absent arm or a non-concrete field class, from a program |
|---|---|---|---|
| `Plain` | 187,497 | 4,847 | 0 |
| `TraitMethod` | 67,100 | 874 | 0 |
| `Ctor` | 42,695 | 913 | 0 |
| `Accessor` | 1,579 | 132 | 0 |

- **Sixteen records are not frames:** six on the absent arm and ten field
  reads. All sixteen are the backend's module fixtures, by frame name:
  the `census_*` frames, the `fixture` frames of module `test`, and one
  read, in a frame named `f`, of a hand-built short declaration that no
  program can declare. They are the same sixteen as at `39db1bb1`.
- **Against `39db1bb1`** (222,690 lines): 75,793 more lines, with 75 more
  tests, among them the standard library's self-tests and its trait
  driver. `qa` kept no per-test count, so the rise is not attributed to
  programs. The zero is read against this run's frames.
- **Row B17 changed what a trace form emits:** its body's value is now
  released through drop glue. The zero covers the frames that compile a
  trace form in this run.
- **What the zero does not cover.** A program refused before emission
  compiles no frame for the refused definition.
- **Still not licensed:** any claim about a concrete but wrong type (safety
  register R18). ACT-1062's display reader and ACT-1076 show it is live.

### 14.6 The cells that were run-dependent

Read at `f8c55626` and not repeated. One cell has failed on load since:
`environment_supply::credential_with_nul_neg_refuses_without_disclosure_or_panic`,
once at `9bee5930`, in the harness and on no assertion. Its stdin is
corrected (`cf140ff4`).

28 cells. Each ran ten times alone (`-j 1`), ten times with fourteen cells
running at once, and once in the full suite.

| Cells | Correction | Alone | Fourteen at once | Full suite |
|---|---|---|---|---|
| `spec_07_traits::s124_1070_jit_call_range_subject` | B13, `790f4c9a` | 10 of 10 | 10 of 10 | passes |
| `spec_07_traits::s124_depth_64_{run,link,repl}`, `s124_two_member_depth_64_{run,link,repl}` | B13 | 60 of 60 | 45 of 60. **All 15 failures are the harness's 30 s child limit;** none is a signal or the JIT's range assertion | pass |
| `trace::trace_records_user_function_calls_in_every_mode`, `s124_1039_w_subject_{run,link,repl}` | B10, `f8c55626` | 40 of 40 | 40 of 40 | pass |
| `trace::s124_1078_subject_{run,link}` | B10 | 20 of 20 | 20 of 20 | pass |
| `trace::s124_1039_lib_neg_caller_frames_{run,repl,link}` | B10 | 30 of 30 | 30 of 30 | pass |
| `trace::s124_finished_module_*`, nine | B10 | 90 of 90 | 90 of 90 | pass |
| `match_field_parameter_order::s124_1062_f_subject_{run,link,repl}` | B14, `4d2bd8a4` | 30 of 30 | 30 of 30 | pass |
| **Total** | | **280 of 280** | **265 of 280** | 28 of 28 |

- **The 15 are load, not ACT-1070.** The loaded run kept the fourteen
  processors near full use (31 processor-minutes in 154 s). The failing executions ended at 30.05
  to 31.06 s and the passing ones of the same cells at 12 to 29 s, one
  distribution cut by the limit. By cell: `s124_two_member_depth_64_repl`
  8, `s124_depth_64_repl` 4, `s124_two_member_depth_64_link` 2,
  `s124_two_member_depth_64_run` 1.
- **Control, without the harness's limit.** The two-member depth-64 program
  ran 96 times through the binary, sixteen at once: 96 of 96 exit 64, in
  47 s.
- **The 16-run cell.** Ten executions alone and ten under load are 320 runs
  of its subject, sixteen at once inside each cell. Every run exits 64. At
  the rate observed before the correction (4 of 16 runs ending on the
  signal or the assertion), 320 independent clean runs would have a chance
  below one in 10^39.
- **What this does not show.** Nothing here was run on the tree before each
  correction.

### 14.7 Defects and leads read at this exit

| Filing | Defect | Entered | Face | State |
|---|---|---|---|---|
| [ACT-1108](../../sprints/actions/ACT-1108-io-is-not-opaque-pure-is-absent-and-the-constructors-are-surface-intake.md) | `IO` is not opaque: `primitives/pure` is absent and `Pure` constructs and matches | The requirement was ruled on 2026-11-22 | Nonconformance; its unsafe faces are ACT-1105, 1106 and 1107 | **Opened on 2026-11-22; carried to the next sprint by the user's decision.** Observed by hand; attributed to the bootstrap's seeding, read in source. No cell yet: T-IO-OPAQUE |
| [ACT-1109](../../sprints/actions/ACT-1109-function-and-nested-io-values-do-not-display-as-the-closure-and-io-markers-intake.md) | Function and nested IO values do not display as `#closure` and `#io` | The requirement was ruled on 2026-11-22; the `<unknown-tag:4>` row is older | Wrong display | **Opened on 2026-11-22; carried.** Observed by hand; attributed to the binary's display, not read. No cell yet: T-MARKERS |
| [ACT-1110](../../sprints/actions/ACT-1110-an-unrecorded-trace-root-is-named-skipped-with-an-empty-result-intake.md) | An unrecorded trace root is `::skipped::` with an empty result | The requirement was ruled on 2026-11-22 | Wrong value, under concurrent tracing only | **Opened on 2026-11-22; carried.** Read in source and design; not observed. No cell: a named residual |
| [ACT-1106](../../sprints/actions/ACT-1106-effect-constructors-field-is-typed-as-the-io-value-and-holds-a-thunk-intake.md) | `Effect`'s field is typed as the IO's value and treated as a thunk | The specification's declaration (§10.1); not dated | **Memory-unsafe:** signal 11 on constructing it with a value, forced or not; a thunk's address read at another type on a match | **Opened from `sprint`'s lead on 2026-11-22.** Reproduced in every mode with `Pure` controls; attributed to the requirement as realised in `src/bootstrap.rs`, read in source. No cell yet: T-EFFECT-FIELD (§14.3) |
| [ACT-1107](../../sprints/actions/ACT-1107-match-on-io-with-pure-and-effect-arms-is-accepted-and-fails-on-a-bind-node-intake.md) | A match on `IO` with `Pure` and `Effect` arms is accepted and fails on a bind node | Not established | An accepted program ends on `match failed` | **Opened from `sprint`'s lead on 2026-11-22.** Reproduced in every mode with two controls; attributed to typecheck's exhaustiveness check, read in source. No cell yet: T-IO-MATCH (§14.3) |
| [ACT-1105](../../sprints/actions/ACT-1105-qualified-primitives-bind-constructs-a-node-shorter-than-the-runtime-reads-intake.md) | A qualified `primitives/Bind` constructs an IO node one word shorter than the runtime reads; the bare spelling is refused | Before S124: the two-field seed is S76's, the third word S121 to S122's | Memory-unsafe, latent: a read past the allocation; a call through the stray word on a path not reached | **Opened from `sprint`'s lead on 2026-11-22.** The node's size is observed in emitted code with the builtin as control; the reader is read in source. The ordinary path matches the builtin. No cell yet: T-BIND-SPELLING (§14.3) |
| [ACT-1103](../../sprints/actions/ACT-1103-trait-spelled-num-eq-ord-or-display-has-its-impl-body-replaced-by-a-primitive-intake.md) | A trait spelled `Num`, `Eq`, `Ord` or `Display` has its implementation for a primitive type replaced by a primitive | Before S124: in typecheck since 2026-06-21, in the backend before | Wrong value, every mode, no diagnostic | **Opened from `arch`'s determination on 2026-11-21.** Reproduced by hand for all four spellings with renamed controls; attributed to `primitive_for_trait_method`, read in source. T-TRAIT-SPELLING is committed, 6 cells RED |
| [ACT-1104](../../sprints/actions/ACT-1104-built-in-vec-is-refused-as-an-implementation-target-intake.md) | The built-in `Vec` is refused as an implementation target | Not established | A legal program refused, with a self-contradicting diagnostic | **Opened from `arch`'s determination on 2026-11-21.** Reproduced by hand with controls; attributed to typecheck's implementation check, provisionally as to the site. T-VEC-IMPL is committed, 2 cells RED. The higher-kinded face is held on S124-Q16 |
| [ACT-1102](../../sprints/actions/ACT-1102-refused-save-leaves-the-cache-ahead-of-the-backing-file-intake.md) | After a refused save the cache holds definitions the backing file does not, and the next cached session calls one | Before S124: the opening tree shows it | **Memory-unsafe:** signal 11 | **Opened from `test`'s observation on 2026-11-20.** Reproduced by hand with three controls. Attributed to `src/session_v4/lifecycle.rs`, read in source. T-REFUSED-SAVE-CACHE is committed, 1 cell RED |
| [ACT-1101](../../sprints/actions/ACT-1101-session-save-refused-after-a-parametric-product-type-is-constructed-intake.md) | After a value of a parametric product type is constructed, every later save of the backing file is refused | Before S124: present on the opening tree. The refusing check dates from S122 | **Data loss:** later definitions are absent at restart. A warning is printed each time | **A defect against REPL §15.1; it predates S124.** A binary built from the opening commit `3155f47f` shows it in all three subjects. Attributed to `src/save.rs::generate_types`, read in source. T-SAVE-PRODUCT is committed, 3 cells RED |
| [ACT-1100](../../sprints/actions/ACT-1100-selective-derive-import-refusals-intake.md) | A macro's expansion that references a macro of its own module is refused unless the using module imports that macro | Not established | A legal program refused | **Opened by `docs`; a defect against spec §9.3.4.** Reduced without the standard library, with controls. **Attributed to `src/`'s expansion driver,** read in source: heads are recognised in the using module's scope and qualified afterwards. T-MACRO-SIBLING is committed, 6 cells RED |
| [ACT-1099](../../sprints/actions/ACT-1099-type-command-refuses-an-expression-that-uses-a-macro-intake.md) | `/type` refuses an expression that uses a macro | Not established | A legal query refused, with a diagnostic naming a defined macro as undefined | **Opened by `qa` on 2026-11-20.** Reproduced by hand with a control; attributed to `src/`'s type query, provisionally. T-TYPE-MACRO (§14.3) |
| Recorded in ACT-1094 | A traced body's value that owns heap memory was released with no drop glue | S20 | Performance only: what the value holds is stranded | **Corrected at `3c5e41ca` and accepted** on `dev`'s module row and its planted fault. T-TRACE-OWNING passes; one subject is returned so the end-to-end cell can fail on it (§14.3) |
| Recorded in ACT-1094 | A second thread's skipped or unswapped trace form pushed onto, or popped from, the recording thread's stack | Before S124 | Wrong value, run-dependent: a recorded tree depends on scheduling. No memory hazard | **Corrected at `ecae99c9` and accepted** on `dev`'s seven module rows and their detection proofs, which pass. Never observed by a cell; no fixture selects the interleaving |
| ACT-1034 (closed S124) | A parametric implementation's method instance could not call a polymorphic callee | S122 intake | Legal program refused | **Closed and deleted.** Every cell passes; 53 stamps (`93e3df64`); bands restored |
| [ACT-1096](../../sprints/actions/ACT-1096-declared-child-of-a-library-module-is-replaced-by-a-file-earlier-on-the-search-path-intake.md) | A declared child of a library module is loaded from a same-path file earlier on the search path | The resolving line dates from 2026-06-21; no earlier tree was run | Wrong value, every mode | **Re-judged after the user's ruling on S124-Q14: it stands, and gains a face.** The project file is not part of the program; it is loaded (4 cells RED) and offered by `/search` (no cell yet: T-MOD-CHILD-INDEX). Attributed to `src/`'s child enrolment, read in source; the index face by control only |
| [ACT-1097](../../sprints/actions/ACT-1097-trait-signature-accepts-a-bare-primitive-type-name-that-is-not-imported-intake.md) | A trait signature accepts a bare primitive type name the module has not imported | The resolver's convergence, `5ed07d60` (2026-07-16), keeping earlier behaviour | An illegal program accepted | **Opened from `audit`'s finding R6; a defect against spec §3.1.** Reproduced by hand with controls; attributed to typecheck's scalar fast path, read in source. T-TRAIT-SCALAR is committed, 3 cells RED |
| ACT-1094 (closed S124) | A trace root's result is the empty string | S20 (`01eff049`), with the sentence it violates | Wrong value, every mode | **Closed and deleted.** Corrected under row B17 and accepted at `121c5c9e` (§14.2); nine stamps (`fb68ef5f`). One question stays with `spec` |
| [ACT-1092](../../sprints/actions/ACT-1092-search-index-omits-a-module-whose-import-names-an-unloaded-or-compiling-module.md) | The search index omits a valid module whose import names a module that is not loaded or is still compiling | The private index typecheck dates from S91; the requirement was ruled on 2026-11-20 | Wrong value: a missing search row, with the complete-index answer | **A defect against REPL §17.19 R10,** re-classified on the user's ruling. Reproduced by hand with a control; attributed to `src/`'s index feed at its own report. T-SEARCH-REACH is committed, 2 cells RED; the still-compiling clause is a named residual. `qa` holds it; the correction is `design`(int)'s and `dev`(`src/`)'s |
| ACT-1091 | An instance's trace frame was named by its instance key | The requirement was ruled on 2026-11-20 | Wrong diagnostic string | **Closed and deleted.** Corrected at `2ffc84d3` over row B16; §14.2 |
| [ACT-1090](../../sprints/actions/ACT-1090-commit-planning-validates-a-covered-member-against-a-table-copied-before-it-published-intake.md) | Commit planning copies a covered member's table and reads its readiness afterwards | S124 delivered the covered set (`f8c55626`); entered at int §7.6.4 | Wrong value, low harm, run-dependent: one launch omits a module's frames | **Open; carried.** Reproduced by hand with a control; attributed to `src/`. REPRO-1090's subject is run-dependent: it passed at `b72742f7` and failed at `121c5c9e` (1 of 30 launches) |
| ACT-1088 | A function taken as a value in the unit that defines it was called directly, not through its slot | Before S124 | Wrong value | **Closed and deleted.** Corrected at `1238b31c`; §14.2 |
| [ACT-1089](../../sprints/actions/ACT-1089-type-command-given-a-definition-commits-it-without-code-intake.md) | `/type` given a definition commits it to the live session with no code | Before S124 | **Memory-unsafe:** signal 11 on the next call. Also a replaced live definition and a stale printed type | **Open; carried past S124 by the user's ruling.** REPRO-1089 is committed, four cells RED. The user ruled that `/type` reports a definition's type; T-TYPE-DEFN is committed, RED. `deftype`, `deftrait` and `impl` are committed too, and the `impl` gives signal 11: T-TYPE-PURE is committed, 3 more cells RED |
| [ACT-1087](../../sprints/actions/ACT-1087-trace-form-in-a-prelude-dependencys-child-omits-modules-reached-through-the-prelude-intake.md) | A trace form in a declared child of a prelude dependency omits modules reached through the prelude | S124 delivered the coverage rule | Wrong value, low harm | **Narrowed.** C1 (`fe385164`) corrected the restored and linked launches. The first launch is `arch`'s accepted residual, carried RED |
| ACT-1086 | A trace form in a generic library function recorded calls inside the function its caller passed | S124 delivered the library rule for a fixed parameter type only | Wrong value | **Closed and deleted.** Corrected by row B10-C2 (`94749709`); §14.2 |
| [ACT-1085](../../sprints/actions/ACT-1085-two-processes-on-one-project-directory-can-mix-cache-generations-intake.md) | Two processes on one project directory share its cache with no exclusion | Before S124 | A later cached launch runs code that differs from its source | Open; asserted, not reproduced; with the user |
| [ACT-1071](../../sprints/actions/ACT-1071-imported-impl-instance-calls-multi-signature-function-through-empty-slot-intake.md) | An instance of an imported parametric implementation calls a multi-signature function through an empty slot | Before S124 W3 | Signal; the link's refusal in the back-edge leg | Open; attribution provisional |
| [ACT-1082](../../sprints/actions/ACT-1082-reference-through-a-module-alias-names-the-alias-as-the-module-intake.md) | An absent member reached through a module alias is reported against the alias; in one REPL order the alias is looked up as a module | Not established | Diagnostic; refusal in one order | Open; held at the user's gate |

**Why coverage missed them.**

- **ACT-1088.** Every cell that took a function value and then traced or
  redefined it took the value in a later unit than the definition, or from
  another module. The axis "value taken in the defining unit, or in a later
  one" was not enumerated. It is one more instance of a batching axis: the
  same program entered as one file and as prompt turns.
- **ACT-1089.** `/type` had one cell, with an expression. No cell gave a
  slash command that takes an expression a form that is not one. Whether
  the other such commands (`/time`, `/mem`, `/expand`, `/ast`, `/clif`)
  share the fault is not probed.
- **ACT-1090.** Every trace cell restores all of its modules or none. The
  axis "one module restored while a module it depends on compiles" was not
  enumerated, and the settled-member rule's module rows give the walk a
  fixed view and a fixed predicate.
- **ACT-1091.** No cell named an instance's frame, because the spelling was
  open with the user.
- **ACT-1092.** Every search cell indexes modules that import only
  built-in modules or modules the session has loaded. The axis "a reachable
  module imports another reachable module the session has not loaded" was
  not enumerated.
- **ACT-1094.** Every trace cell reads a child frame, a frame count or the
  root's name. No cell reads the root's result, and §4.12.2's band listed
  evidence for items 1 to 3 beside a closing sentence that had none. A
  band on a section does not show which of its sentences has a cell.
- **ACT-1096.** Every cell with a declared child keeps it under the
  project root, where the search-path probe and the child directory are
  the same file. The axis "the declaring module is found in a library
  directory" was not enumerated for `mod`.
- **ACT-1097.** The import rule's refusal cells use an annotation and a
  type field. The axis "position of the type name" stopped short of trait
  signatures, where the module rows fix the fast path as intended.
- **ACT-1018's withdrawn reading.** `qa` concluded from one stdlib-free
  run that the path allocated nothing, and did not keep the reading's
  counts. A negative reading is recorded with its numbers.
- **ACT-1099.** `/type` had cells for a primitive call and a function
  call. The axis "the expression uses a macro" was not enumerated for any
  slash command that takes an expression.
- **The owning-value leak.** T-TRACE-ROOT's heap leg used a `String`, which
  holds nothing further. `qa` allocated "heap-valued" and did not separate
  a value that owns other heap values, which is where drop glue matters.
- **ACT-1089's expression face.** The expression control queried a call
  of a monomorphic function. `qa` allocated one expression shape and
  called it the control for all of them; the shape that mints an instance
  was never queried.
- **ACT-1106 and ACT-1107.** The `IO` cells construct `Pure` and reach
  `Effect` only through a platform. No cell constructs `Effect` or matches
  on an `IO` value, though the specification calls `IO` an ordinary ADT.
  The axis "what an ordinary ADT permits" was never applied to it.
- **ACT-1105.** The cells for the internal constructor use the bare name,
  which is refused. The axis "the same name, qualified" was not enumerated
  for a refusal that is meant to hold for a declaration, not a spelling.
- **ACT-1096's index face.** `qa` reproduced the load through a private
  child and did not ask what else names a module from a file's path. The
  search index does.
- **ACT-1103.** Every trait cell that implements `Num`, `Eq`, `Ord` or
  `Display` for a primitive type gives the implementation the primitive's
  own meaning, on the suite's test prelude. No cell gives one a body that
  differs from the primitive, so the substitution was unobservable.
- **ACT-1104.** The implementation-target cells use user types and
  `Option`. The axis "the target is a built-in parameterized type" was not
  enumerated.
- **ACT-1102.** Every restart cell follows a session whose saves
  succeeded. The axis "the previous session's last save was refused" was
  not enumerated, and no public route to a refused save was known before
  ACT-1101.
- **ACT-1101.** Every persistence cell defines functions, enumerated
  types, traits and macros. None constructs a value of a parametric
  product type before a later definition. The axis "what the session has
  evaluated, not only what it has defined" was not enumerated for
  regeneration.
- **ACT-1100.** The macro-availability cells define and use a macro in one
  module, or import a module's whole surface. The axis "an expansion
  references a macro the using module did not import" was not enumerated.
- **`defmacro` given to `/type`.** `qa` allocated it as a guard from a
  reading with no earlier expression, the one session shape in which the
  defect prints an error. A guard is allocated from the same session shape
  as its subjects.
- **The stale ACT-1034 bands.** Its cells turned green during S124 and no
  read of this section compared the passing set with the bands that named
  cells as failing. A band that names a failing cell is re-read whenever
  that cell passes.

**The `index:` note in REPRO-1090 is ACT-1092's seam and does not touch
the score.** The cell's turn loads `m`, so the session lists `m`'s rows
whether or not the note printed (29 of 29 launches, by hand). The cell
prints the note and does not decide on it, which is right.

**Lead: the cost of the depth-64 programs.** The two-member program takes
2.4 s and 321 MB alone in a debug build, and 8 to 30 s under load. Its
stage is not attributed and no requirement bounds it. Its eight cells have
a child time limit the suite's load does not approach (`81d186c6`).

**ACT-1083's attribution is closed on the aggregate it explained.** The
two binaries ran in one session on one machine, with the same scripts and
28 parallel processes.

| Reading | `a205a29f` | `79a8c94c` |
|---|---|---|
| The deterministic program, 200 loaded runs | 7 in 200 | 41 in 200 |
| K-6's first four legs, 300 loaded runs | signal in 24 | signal in 0, and 0 in a second 300 |
| The same legs as load for the next row, 6,000 runs | — | signal in 0 |
| The harness cells K-6 and REPRO-1083, linked and REPL legs included, 100 repetitions under that load | — | 100 of 100 pass |

- **Residual, as a number:** 0 of 6,600 script runs and 0 of 100 harness
  repetitions on the corrected build.
- **At the seam.** After the session, `lib`'s manifest entry is still the
  first launch's key, the next launch misses on it and rebuilds `lib.o`.
  With the session omitted, or the object deleted, the result is the
  same; with an edit that moves no slot the rebuilt object is byte for
  byte the old one.
- **The earlier builds** are in ACT-1083's table: signal in 300 of 300
  before the S122 dependency record, in 285 to 287 through `e294852f`,
  and in 24 to 29 from ACT-1052's correction to `a205a29f`.
- **Why coverage missed it.** `qa` accepted K-6 on one full run where it
  failed about one loaded run in twelve. A cell whose fixture includes a
  REPL session over a cache is read under load before it is accepted.

**ACT-1071's back-edge leg now fails at the object pass.** The link's
refusal reads: the pass for `lib` cannot compile the instance of `helper`
at `(Opt Int)`, because its call carries a resolved target keyed under
`lib` for which `lib`'s symbol table holds no entry.

- **What it adds.** A target is published under the library module for an
  instance that is not installed there. That is the filing's hypothesis,
  observed at the keyed consumer for this variant.
- **What it does not add.** The subject and the dispatching variant link
  and give 42, so the observation is of the back-edge variant only. The
  producer is still not observed at its own seam, and the attribution
  stays provisional.
- **The earlier linker error was a consequence.** The pass stopped without
  a report and the link went on without `lib.o`.
- **The cell is unchanged.** It asserts the exit status and the absence of
  an error, and fails on both as before.

**Other reads.**

- **The result-polymorphic `main` is settled by the specification**
  (§3.11.1) and reported as a located type error in both batch modes.
- **The alias cells did not need a ruling to be RED.** Spec §8.6.6 and
  §8.5.4 edge 4 decide the behaviour. What waits on the user is the
  cross-crate meaning of the gap's module, which is the correction's
  route.

### 14.8 Handoffs, in order

**Can proceed now, in this order.**

1. **`test`:** nothing is allocated. Remove the transient handoff file
   under `tests/fixtures/s124-handoff/`. `qa` took its clause map into the
   judgments table and its backlink walk into the last table of this
   section.
2. **`qa`:** the seven older cleared rows; the index feed's enumeration
   site for ACT-1096.
3. **`sprint`:**
   - the backend meets its three exit clauses at `128255fc` (§14.9);
   - **ACT-1101 predates S124** and is carried on three failing cells; it
     does not hold the sprint under *no decay* (§14.10);
   - **ACT-1102 is memory-unsafe and also predates S124.** Its cell is
     committed and its site is read;
   - **ACT-1103 and ACT-1104 are new, from `arch`'s determinations.**
     ACT-1103 predates S124; ACT-1104's age is not established;
   - **ACT-1089 has a face on an ordinary expression** that the user's
     carry decision did not have before it: `/type (Some 1)` then
     `(Some 1)` ends the process;
   - the failing count is 143 (§14.1);
   - the document gate's 29 findings outside ignored paths are listed by
     owner in §14.1;
   - `arch`'s row B18 is with the user, and ACT-1110's correction waits on
     it;
   - the suite takes 265 s, and 4 m 44 s with its build;
   - §14.13 is what a user accepting the sprint should know is not
     covered;
   - return ACT-1094's outcome to `training`, ACT-1096's to
     `dev`(exemplar), ACT-1097's to `audit`'s disposition and ACT-1018's
     to `dev`(stdlib);
   - schedule or decline ACT-1085's reproduction (§14.1);
   - `sprints/SPRINT.md` §Settling target still lists zero failures; its
     Notes state the target ruled on 2026-11-19;
   - the root memory's testing guidance states about 170 s at 5,687 tests;
     the suite took 265 s at 8,109 at `128255fc`;
   - ACT-1083 is marked resolved and its file is still present.
4. **`design`(int):**
   - **int §7.6.4 derives the covered set from the prepared view under a
     readiness read it does not order** (ACT-1090). The correction's shape
     is `design`(int)'s; `dev`(`src/`) then owes the module row with it;
   - ACT-1092: how the feed resolves a module's imports without the
     session having loaded them, and whether ACT-0952's dependency
     discovery is that correction. Carried on T-SEARCH-REACH unless the
     user schedules it;
   - ACT-1102: a refused regeneration publishes no cache generation
     ahead of the backing file;
   - ACT-1101: the type section of regeneration excludes instances, as
     the function section does. Whether an instance keeps its type facet
     is `arch`'s;
   - ACT-1100: recognition of an expansion-produced macro head in the
     defining module's scope. It touches `arch`'s macro-availability
     model;
   - ACT-1096: a declared child resolved from its declaring file's
     directory, on the fresh and the cached routes. Carried on T-MOD-CHILD
     unless the user schedules it;
   - [result owner §4.3](../../design/int/result-owner.md) says `__expr` is
     absent after a clean check only through an invariant violation, and
     that the only face is a wrong display. A definition given to `/type`
     falsifies both (ACT-1089), and `/type` now has a required answer for
     one (REPL §3.1);
   - FIXME 0929 targets it: the binary row is in source (`793af750`), so
     its closure is `design`(int)'s to judge.
5. **`dev`(`src/`):**
   - **one module row for FIXME 0915's subject, RED today:** over the
     existing private failed-turn witness (`src/worker/tests.rs`, a
     production `CodegenFailed` at a prepared target), the text the batch
     formatter and the REPL's error line print names neither `__expr` nor
     an instance key as its subject. It asserts presentation at the display
     boundary and pins no carrier. `qa` did not find it in source at
     `39db1bb1`;
   - resolve ACT-1060, whose completion check is met again.
6. **`design`(backend):** FIXME 0915 still targets `design`(backend) with
   its backend half built. What remains is the subject's carrier, which is
   `arch`'s, and its projection, which is int's. Re-target it or split it.
   The other record repairs of the previous read are done (`39703c49`,
   `42acf9a8`); `qa` did not re-read the release contract §7.2.1's status
   line.
7. **`arch`:**
   - the carrier for the codegen subject (int §9.1, *Where statement 2
     can be realised*): a public change in types and the backend;
   - ACT-1094's correction hands the body's formatted value to the root
     frame, across the interface between the backend and intrinsics.
     Carried on T-TRACE-ROOT unless the user schedules it.
8. **`spec`:** spec §4.12.8's first example shows the root of
   `(trace (fact 5))` named for `fact`, with its parameters; the compiler
   and the trace cells have a root named `::trace::` with the call as its
   child, and §4.12.2 does not say what the root's name and parameters are
   (ACT-1094). It blocks no test.

   Also blocking no test: a skipped trace form's result, which §4.12.6
   does not name ([trace runtime §7.3](../../design/intrinsics/trace-runtime.md));
   what a file at `{project_root}/m/t.cl` is when
   `m` resolves to a library directory (ACT-1096); and whether a default
   method body naming an undefined function is reported at the trait's
   declaration (ACT-1097, *Lead*).
9. **`design`(typecheck):** ACT-1097's correction, carried on
   T-TRAIT-SCALAR unless the user schedules it; ACT-1104's, carried on
   T-VEC-IMPL; ACT-1103's, after `arch` and the confirmed classification.

**Waits on the user.**

| Decision | Holds | Principle |
|---|---|---|
| A one-sentence exception in spec §4.12.3 for a form compiled before the prelude publishes ([tracing §5.1](../../design/arch/tracing.md#51-which-modules-a-form-covers)) | ACT-1087's one RED cell, which is restated if the exception is ruled | Consistent spec |
| A REPL definition holding a trace form and a later-loaded module; a library module reached only by a qualified name (tracing §5.1) | No test. Current behaviour stands | Consistent spec: silent without blocking |
| A public change `arch` escalates: the resolution gap's module (ACT-1082); `CallableOrigin::TraitMethod` carrying its member | ACT-1082's 4 cells | Public-API changes |
| The ignored-path findings of the document checker | The document gate | — |
| Whether ACT-1085's control is built | T-OWNER | Reproduce first: it has no reproduction |
| Whether ACT-1099's correction is scheduled with ACT-1089's | T-TYPE-MACRO | Clean house: both are in `typecheck_only` |
| Whether ACT-1100's correction is scheduled | T-MACRO-SIBLING's 6 RED cells | The standard library's `derive` meets it |
| Whether ACT-1089's expression face is carried with the rest | T-TYPE-EXPR, once committed | It is memory-unsafe on the ordinary use of `/type` |
| `arch`'s row B18, typed trace entries | ACT-1110's correction | Public-API changes |
| Whether ACT-1101 and ACT-1102 are corrected before the sprint closes | T-SAVE-PRODUCT's 3 RED cells; T-REFUSED-SAVE-CACHE's 1 | Data loss and a memory-unsafe restart. Neither is S124's own, so *no decay* does not require it |

**Carried, with nothing owed this sprint beyond the failing test:** every
filing of §14.1 outside the backend.

**`docs`, in Phase 6:** `user/guide/modules.md` still says renamed imports
are tracked in ACT-0997.

### 14.9 The backend's exit list

Clean and green is: no failing test attributed to the backend, no build
warning from it, no open review finding on it.

**At `128255fc` the backend is clean and green: no failing test is
attributed to it, it raises no build warning, and no review finding is
open on it.** No backend source has changed since `3c5e41ca`.

| Clause | State at `128255fc` |
|---|---|
| No failing test attributed to the backend | **Met.** 0 of the 143 failing tests. ACT-1094's nine cells pass. The backend's module tier passes, 537 of 537 |
| No build warning from the backend | **Met.** Read at `121c5c9e`, with the same backend source: `cargo build` and the run's build report no warning from a workspace crate. `cargo clippy -p cranelisp-backend --all-targets` reports none from the backend; its 13 are in `cranelisp-types` (7), `cranelisp-intrinsics` (3) and `cranelisp-platform` (3), as before |
| No open review finding on the backend | **Met, as `sprint` reports:** the reviews of `ecae99c9` and `3c5e41ca` returned no finding. `qa` did not read them |

**Two caveats, both unattributed cells.** ACT-1101 is attributed to
`src/` and is not one of them. ACT-1067's two cells have four
candidate modules and ACT-1018's five have three; the backend is one of
each. If either is attributed to the backend, its cells are failing tests
of the focus module.

**Failing tests.**

| Filing | State at `128255fc` |
|---|---|
| ACT-1094 | **Closed and deleted.** Nine subjects, four controls and twelve owning-value cells pass |
| ACT-1018, only if its module is the backend | 5 cells, unattributed among the platform crate, the backend and the runtime |
| ACT-1091 | Closed and deleted. Three cells and a module row pass |
| ACT-1088 | Closed and deleted. Seven subjects and five controls pass |
| ACT-1086 | Closed and deleted. Its correction was shared by the backend and the binary (row B10-C2) |
| ACT-1039, ACT-1070, ACT-1078 | Closed and deleted at an earlier read |
| ACT-1062 | The backend reader is closed (`4d2bd8a4`). The filing stays open for the display reader in `src/`, 1 cell |
| ACT-1067, only if its stage is the backend | 2 cells, unattributed. A backtrace at the overflow decides; this environment has no debugger |

**Build warnings: none,** re-read at `121c5c9e`. `cargo build` reports no
warning from a workspace crate. `cargo clippy -p cranelisp-backend
--all-targets` reports none from the backend; its 13 warnings are in the
crates it depends on (`cranelisp-types` 7, `cranelisp-intrinsics` 3,
`cranelisp-platform` 3), as at `ee65d9aa`. Cargo reports one
future-incompatibility notice, for `nix v0.28.0`, which the binary reaches
through `rustyline`.

**Review findings.**

| # | Finding | State |
|---|---|---|
| 1 | The review of the exit commits to `f8c55626` | Closed: no required finding on the backend. Its one advisory, hash-map order, is corrected (`e8a9cac5`) |
| 2 | The backend commits `e8a9cac5`, `9bb1f0aa`, `a9a8c0c6`, `36e64f27`, `9bee5930`, `717dd3a1`, `994137dd`, `1238b31c`, and the backend half of `94749709` | No finding, as `sprint` records. `qa` did not read the review |
| 3 | `c9f573e0` (types, row B16) | No finding, as reported to `qa` |
| 4 | `2ffc84d3`, `4407b008`, `5a9c4f07` | One required finding: the relocation scan's Mach-O symbol spelling in `slot_call_tests.rs`. Answered at `39db1bb1`; the re-read confirmed it, as `sprint` records. No public item outside row B16 |

**The backend's backlog.** `qa` opened each record's source on 2026-11-20.

| Record | State |
|---|---|
| ACT-0964, FIXME 0747 | Deleted by `design`(backend) (`35f41389`) |
| FIXME 0931 | Closed by `arch` (`26fbee2f`) |
| FIXME 0929 | Not the backend's. Its binary row is in source; `design`(int) closes it |
| ACT-0968, item 1 | Discharged (`9bb1f0aa`). The action stays open for its frontend rider |
| FIXME 0915, the backend half | **Built** (`a9a8c0c6`, `36e64f27`, row B15 at `9bee5930`), with rows, and observed composed (§14.2). The file stays open for the binary's half, which is carried (§14.1) |
| Compile-to-module §12.1 and §12.2 | In source, and the design says so |
| The relocation row for tracing §3.5 | In source (`4407b008`) |
| A multi-signature family's mode-changing redefinition (§9.4) | Held on the user's approval of the row. No cell |

### 14.10 No decay

A module is worse when a test or a reading shows a regression S124 caused
and has not corrected.

**No module S124 touched is shown worse than at the sprint's opening, by
any test or by the one opening-tree reading taken.**

- **Basis: the full run at `128255fc` against the opening run** (§1: 7,024
  run, 49 failed). Of the 143 failing tests, 141 are cells committed in
  S124 as reproductions, each on a filing. The other two failed at the
  opening: the document gate and ACT-1018's guard. No test that passed at
  the opening fails; each of `qa`'s eight full runs was compared with the
  one before it.
- **The failing count rose from 49 to 143 by reproduction,** not by
  regression.
- **[ACT-1101](../../sprints/actions/ACT-1101-session-save-refused-after-a-parametric-product-type-is-constructed-intake.md) and [ACT-1102](../../sprints/actions/ACT-1102-refused-save-leaves-the-cache-ahead-of-the-backing-file-intake.md) are not decay.** `qa`
  built the sprint's opening commit, `3155f47f`, in a throwaway clone and
  ran ACT-1101's three subjects and two controls and ACT-1102's rows on
  it. Each gives the same result as the current tree: the save is
  refused, the later definition is missing, the cached restart ends on
  signal 11, and the controls save. `sprints/SPRINT.md` names no opening
  commit; `3155f47f` is "Open Sprint 124".
- **The reading is of those sessions only.** It does not show that
  nothing else in `src/` changed for the worse.

| Module | Changed in S124 | Worse than the opening tree | Basis |
|---|---|---|---|
| backend | Type concreteness; FIXME 0915's frame, row B15, trace order, row B10-C2, the trace reader, K11-d's fixtures, the wrapper's slot call, the instance frame's name, the relocation row, row B17's closing tail | Not shown worse | 0 failing tests; 537 module tests pass; no warning; census zero |
| types | The template-module accessor, K11-c, K11-d, ACT-1084, row B16 | Not shown worse | 0 failing tests; the baseline check passes; clippy's 7 warnings are unchanged since `ee65d9aa` |
| typecheck | The S124 type-concreteness and successor-discovery corrections | Not shown worse | Its 61 failing cells are S124 reproductions; every cell of ACT-1034 passes |
| `src/` | C1, row B10-C2, the observed-type default, K11-d's fixtures, ACT-1084 | Not shown worse | Its 71 failing cells are S124 reproductions; none passed at the opening. ACT-1101 and ACT-1102 are present on the opening tree |
| intrinsics | The unused trace reader removed; row B17's collect entry and skip mark | Not shown worse | Its 3 failing cells are ACT-0977's reproductions; 404 module tests pass. Four golden cells changed by import numbering only and were re-baselined (§14.2) |
| primitives, frontend, platform | Nothing since `f8c55626`; their earlier S124 changes are read in §13 | Not shown worse | 0 failing tests |
| `stdlib/` | Trait implementations for `Option`, `Result`, `Pair`, `List` and `Either`; `vec-flatten` and `derive` self-tests | Not shown worse | Every public module compiles and runs; 24 modules' self-tests pass in the suite; the trait driver passes 29 legs in three modes. The combined `derive` under a selective import is refused (ACT-1100), by a defect that is the binary's |
| `exemplar/` | Copied test files removed; two tests added to the runner; multi-signature helpers | Not shown worse | The runner exits 43 in both evaluation modes; the web, link-parity and regression cells pass; the residue guard reads 2, as at the opening |
| `examples/` | The learning sequence's S124 additions | Not shown worse | `examples` cells pass; `training` reports 152 of 152 replay cells |
| `user/` | Guides reorganised; carried limits stated beside use | Not shown worse | The documentation-sample cell passes, 93 groups |
| `repl/demos/` | The sprint demo; two older demos corrected | Not shown worse | `test`'s replay: 41 demos, all complete |

**Defects in what S124 delivered,** which no opening-tree reading shows as
a regression:

- **ACT-1090 and ACT-1087's first launch.** The covered set is new in
  S124; before it a form read every loaded table. Whether the opening tree
  recorded the frames in either fixture was not run.
- **ACT-1096 and ACT-1097 predate S124** by their source dates
  (2026-06-21 and 2026-07-16).
- **ACT-1101 and ACT-1102 predate S124,** by the opening-tree reading.
  **ACT-1103 predates it** by its source date. ACT-1104's age is not
  established.
- **The age of ACT-1099 and ACT-1100 is not established.** They sit in
  code S124 did not change, by `qa`'s reading of the change list and not
  by a run.
- **ACT-1088, ACT-1089, ACT-1092 and ACT-1094 predate S124.** The direct
  call was the wrapper's oldest arm; `/type` has committed its cluster
  since at least S110; the index feed's private typecheck dates from S91;
  the trace form has discarded its body's value since S20.
- **ACT-1091** was a nonconformance against a requirement ruled on
  2026-11-20. It is corrected.
- **ACT-1077 and ACT-0981** stay closed.

**What this does not cover.**

- A regression in a program that no test holds.
- Cost. Row B13 makes every JIT call far, stack placement was retired by an
  approved row, and compile-to-module §12.2 adds one load to each call
  through a same-unit function value. `qa` took no time comparison across
  any of them.
- **The suite's own time.** 265 s at 8,109 tests against 153 s at 7,024 at
  the opening. REPRO-1090's two cells are 86 s of test time between them.

### 14.11 Clean house

| Change | Module | Carried defects beside it | Outcome |
|---|---|---|---|
| ACT-1077's correction | `src/bind_chain_analysis.rs` | ACT-0981 | Included and closed |
| ACT-1062's backend correction (B14) | backend | The display reader, `src/display.rs` (1 cell, memory-unsafe) | Not included. It is another module's file and stays carried |
| B10, C1 and row B10-C2 | backend and `src/cache`, `src/worker.rs`, `src/session_v4/nice_worker.rs` | ACT-1079 only if the change reached `src/process_form/dependency.rs` | It did not (int §7.6.4, *Clean house*) |
| The observed-type default (`793af750`) | `src/repl/commands.rs`, `src/pipeline.rs` | ACT-1089, in the function the change edited | Found by `dev` with the change and reported; not included. Carried past S124 by the user's ruling |

- **No non-focus module is taking a larger change in what remains**
  (§14.12).
- **Typecheck holds 61 of the 143 failing cells and has no change
  scheduled.** If it is opened, ACT-1071, ACT-1073 and ACT-1074 share the
  cluster and multi-signature seam, and ACT-1075 and ACT-1076 the dispatch
  and instance-collection seam. ACT-1097 is at the resolver, a seam none
  of them shares.

### 14.12 Between `39db1bb1` and the Phase 5 exit

Under the principles the exit needs the focus module clean and green, no
decay, and every other problem on a failing test.

| Target | State |
|---|---|
| The backend clean and green | Met at `128255fc` (§14.9). It was not met at `b72742f7`, on ACT-1094, which is corrected |
| Every other failing test carried on record by module, with severity | Met (§14.1). 143 failing, none without a filing. ACT-1110 has no cell, by a named residual |
| No module the sprint touched left worse | Met on the basis of §14.10 |

**The Phase 5 exit is taken** (`sprints/SPRINT.md`, Notes), with the
review closed as `sprint` records it.

**Since the exit, in Phases 6a and 6b.** Every allocation is committed and
judged (§14.2), and the full run at `128255fc` gives the table above.
Nothing is with `test`. A further full run is owed only if source changes.

**Carried without a failing test,** for `sprint` to present: the rows of
§14.1, *No failing test*. FIXME 0915's subject row in `src/` (§14.8) would
put the binary's half on a test.

**The checkpoint's baseline diffs.** The user approved the first on
2026-11-20. The types baseline gained one line at `c9f573e0`, row B16's.
`qa` did not compare the baselines with the packet in this read.

**The traceability band.** Seven rows are cleared and await `qa`'s
re-judgment; `spec_coverage_reconcile.py` names them. `spec` cleared two
more at `21101921` and both are restored below.

**Bands edited in this read.**

| Row | Edit | Why |
|---|---|---|
| Spec §4.12.4, the heading and the `name` row | Restored to `[Tested …]` with T-FRAME-NAME's three cells and the backend's module row | ACT-1091 is corrected |
| Spec §4.12.3, the heading and the whole-program row | Still partial; they now name REPRO-1090's failing subject | The cell is committed |
| REPL §3.1, the `/type` sentence | Still nonconforming; it now names T-TYPE-DEFN's failing cell | The cell is committed Superseded by the row for the final ruling, below |
| REPL §3.1, "MUST NOT evaluate a non-pure form" | From uncovered to nonconforming, naming T-TYPE-PURE's three failing cells and its three passing guards | `deftype`, `deftrait` and `impl` are committed by the query (ACT-1089) |
| REPL §17.19 R10, the reachability sentence | From uncovered to nonconforming, naming T-SEARCH-REACH's two failing cells | ACT-1092. The still-compiling clause has no cell |
| REPL §17.19, the index paragraph | Restored to its two cells | Both still observe the private typecheck and the macro omission, which `21101921` did not change. The added clause points at R10, whose band carries the nonconformance |
| REPL §17.19.5 | Restored to its two cells | Their unindexable module references an undefined name, so it is invalid in every session and the no-rows allowance applies to it under R10. The added sentence points at R10 |
| Spec §4.12.2 | Restored to tested, naming T-TRACE-ROOT's cells and the backend's module row | ACT-1094 is corrected and accepted |
| Spec §9.3.4 | From tested to partial, naming T-MACRO-SIBLING's six failing cells | An expansion that references a sibling macro is refused under a selective import (ACT-1100) |
| REPL §15.1 | From tested to partial, naming T-SAVE-PRODUCT's three failing cells and two controls | After a parametric product type is constructed, later saves are refused (ACT-1101) |
| REPL §15.2 | From tested to partial, naming T-REFUSED-SAVE-CACHE's failing cell | After a refused save a cached restart calls a definition the file does not hold (ACT-1102) |
| The rows the rulings of 2026-11-22 changed: spec §10.1, §10.2, §3.2.3, §12.9.1, §4.12.5, §4.12.6; REPL §1.5's closure row | Nonconforming or partial, each naming its filing and cells | ACT-1108, ACT-1109, ACT-1110 and the three `IO` filings |
| Spec §4.12.2, §4.12.4 and its `name` row, §4.12.7, §4.12.8 | Restored to their cells | The synthetic `::trace::` root is what the compiler gives (S124-Q13) |
| Spec §7.1.5 | Restored to its cells, with the S124-Q15 rule noted as holding by hand | T-DEFAULT-UNDEFINED is allocated |
| Spec §8.8.3 and appendix C §C.2.4, `qa`'s own notes | They no longer call S124-Q16 unconfirmed | The classification is confirmed |
| 108 further rows cleared by the stage-two rewrite | 21 restored to their cells; 87 marked with the reason they are not | `test`'s backlink walk, row by row in §14.14 |
| Spec §8.11.2, cleared by `spec` for S124-Q14 | Partial: the search order restored to its four cells and the override control; the new rule nonconforming, naming three of T-MOD-CHILD's failing cells; the index clause without a cell | The project file is loaded and indexed (ACT-1096) |
| Spec §2.2.3, §5.3.2, §9.7.0, §8.8.3 and appendix C §C.2.4 | They name the cells committed at `3904fae8` | T-TRAIT-ONE-PARAM, T-SPLICE-BARE, T-TRAIT-SPELLING and T-VEC-IMPL are committed |
| Spec §2.2.3 and §5.3.2, cleared by `spec` for S124-Q11 | Restored to their cells, with the one-parameter cell added to §2.2.3 | The cells show a bare head, a one-parameter head and the binder refusals, none of which the ruling changed. The refusal of a second parameter holds by hand and has no cell: T-TRAIT-ONE-PARAM |
| Spec §5.3, the section summary | Restored to tested | Its children are |
| Spec §9.7.0, the splicing sentence, new at S124-Q12 | Tested, naming two committed splice cells | They run with a primitives-only prelude and no library. T-SPLICE-BARE adds no prelude and no import |
| Spec §11.4, cleared for S124-Q12 | Restored to its cell | It shows a prelude loads. The changed sentence points at §9.7.0 |
| Spec §8.8.3, the core/library rule | From uncovered to partial, with no cell named | It is mostly a rule about the specification itself. ACT-1103 is a known conflict. Nothing is allocated against the unconfirmed Q16 inventory |
| Spec appendix C §C.2.4, cleared for S124-Q11 | Partial: item 1 tested by two higher-kinded cells; ACT-1104 named; items 2 and 3 without a cell | It was never tested (`[S24]`). The rest waits on S124-Q16 |
| REPL §3.1, the definition-form paragraph and the table row | They name T-TYPE-ERR's five failing cells and T-TYPE-MACRO's | The cells are committed |
| Spec §8.2.5 | From tested to partial, naming T-MOD-CHILD's four failing cells and its override control | A library's declared child is replaced (ACT-1096) |
| REPL §3.1, the definition-form paragraph, cleared by `spec` at `39be7cfe` | Nonconforming, naming REPRO-1089's four failing subjects; the required error has no cell; T-TYPE-DEFN's cell is named as asserting the withdrawn rule | The four subjects still show that nothing may be defined. T-TYPE-ERR is allocated |
| REPL §3.1, the `/type` table row, cleared by `spec` | Partial: tested for an expression by three cells; a definition form and a macro expression are nonconforming | The cell it named, `sig_shows_type_signature`, does not run `/type` |
| Spec §7.3.3 and §5.4.3 | The clause on a body that discharges its constraint moves from defective to tested, naming ACT-1034's passing cells | Every cell of ACT-1034 passes in the run at `b72742f7` |
| Spec §12.3.1 | From tested to partial, naming T-PRINT-BALANCE's four failing cells and the exemplar guard | A value the caller owns, passed to a platform function, is never released (ACT-1018) |
| Spec §3.1 | From tested to partial, naming T-TRAIT-SCALAR's three failing cells and two controls | The import rule is not applied in a trait signature (ACT-1097) |

### 14.13 What the sprint's evidence does not cover

For a user accepting S124. Each line is a limit of the evidence, not a
defect report; the defects are §14.1.

**Known defects carried, by what they do.**

- **Data loss, on failing tests:** a REPL session stops saving once a
  value of a parametric product type, `Pair` among them, has been built
  (ACT-1101); a multi-signature function is omitted from the regenerated
  file (ACT-1068); regeneration can reorder definitions so the file no
  longer loads (ACT-1005).
- **Memory-unsafe, no test yet:** `/type` of an expression such as
  `(Some 1)`, then evaluating it, ends the process (ACT-1089).
- **Memory-unsafe, on failing tests:** constructing `primitives/Effect`
  with a value, or binding its field in a match, ends the process on a
  signal (ACT-1106); an IO node built by the qualified `primitives/Bind`
  is one word shorter than the runtime reads (ACT-1105, latent).
- **An accepted program that panics, on a failing test:** a match on `IO`
  with `Pure` and `Effect` arms fails on a bind node (ACT-1107).
- **Rulings of 2026-11-22 the compiler does not yet meet:** the opaque
  `IO` and `primitives/pure` (ACT-1108), the `#closure` and `#io` markers
  (ACT-1109), the unrecorded trace root (ACT-1110), and `race` as library
  code. The suite, the examples and the guides still write `Pure`.
- **Bands.** Of 108 rows cleared by the specification's rewrite, 87 are
  not covered as now written (§14.14): 25 are library illustrations with
  no language witness, 32 are partly covered, 13 have no direct witness,
  10 are section rollups over uncovered children, and 7 name a cell that
  does not show the row. Seven older rows still await re-judgment.
- **Memory-unsafe, on a failing test:** the session after a refused save
  restores a definition its file does not hold, and calling it ends the
  process (ACT-1102).
- **Wrong value, on failing tests:** a user's own trait named `Num`,
  `Eq`, `Ord` or `Display` has its implementation for a primitive type
  ignored (ACT-1103); a project file at a library child's path replaces
  the child (ACT-1096), and `/search` offers its symbols, with no test
  yet.
- **Legal program refused, on failing tests:** no trait can be implemented
  for a vector type (ACT-1104).
- **Memory-unsafe, on failing tests:** `/type` given a definition
  (ACT-1089); trait dispatch on a non-first self position (ACT-1076); an
  imported parametric implementation calling a multi-signature function
  (ACT-1071); displaying a value whose type parameters are out of declared
  order (ACT-1062).
- The rest of §14.1 refuses legal programs, accepts an illegal one, or
  gives a wrong value or diagnostic.

**Not measured.**

- **Cost.** No time or memory comparison was taken across the sprint. It
  retired stack placement and one-word flattening and made every JIT call
  far.
- **Programs no test holds.** *No decay* is a statement about the suite's
  tests and one opening-tree reading. ACT-1101 was in the product for the
  whole sprint, and before it, with no test holding its shape.
- **Repetition.** Each standing-state run is one run. Cells that depend on
  timing were not repeated under load at this read; REPRO-1090 passes in
  some runs and fails in others.
- **Earlier trees.** The opening tree was built once, for ACT-1101 and
  ACT-1102. The age of ACT-1099 and ACT-1100 is open.
- **Other hosts.** Every reading is on Linux emitting ELF. The Mach-O leg
  of the relocation row has never executed here.
- **Release builds.** The suite and the census run on a debug build; the
  census is compiled out of a release build.

**Evidence that rests on a module row alone.**

- REPL §17.19 R10's *still compiling* clause (accepted by the user).
- The cross-thread trace-stack correction: no solution-level cell can
  select the interleaving.
- The owning-value release of a traced body: its solution-level cells
  have never been seen to fail.
- A concrete but wrong type at codegen (safety register R18): the census
  counts absent and non-concrete types only.

**Not attributed.** ACT-1018 (one stranded block per `print` of an owned
value) and ACT-1067 (a deeply nested expression aborts the compiler) have
no module, and the backend is a candidate for each.

**Open with `spec`, blocking no test.** A trace root's name and
parameters; a skipped trace form's result; what a project file at a
library child's path is; whether a default method body is checked at its
trait's declaration; whether a `begin` of two expressions is reported in
the words it is.

**Showcase, not evidence.** The demos, the exemplar's runner, the
documentation samples and the learning sequence's replay show the
delivered surfaces still work as their authors recorded. They are
maintenance checks and do not accept compiler behaviour.

### 14.14 Bands cleared by the specification's rewrite

`spec` cleared 108 rows at `2fe6d28f` and in its stage-two rewrite. `test`
walked each row's `// spec:` backlinks at `506ee06e` and compared the cells
with the row as now written; `qa` applied the result at `128255fc`. This
table is that walk's durable record. A row whose verdict begins *Retains*
is restored to its cells; every other row's band states the verdict and
points here.

| Row | Where | Verdict | Reason, as `test` read it |
|---:|---|---|---|
| 1 | 01-display-format.md §1.2 | Partial | Scalar envelope cells retain their typed-value assertions; section rollup cannot be restored over the closure marker RED or unevidenced elision uniformity (row 90). |
| 2 | 01-display-format.md §1.2 | Mismatch / RED replacement | display_int_result evaluates integer addition only; it cannot observe an anonymous function. s124_markers_closure_display now rejects the retired marker, RED on <closure>; its concrete Int signature does not cover the illustrated polymorphic signature. |
| 3 | 01-display-format.md §1.2 | Retains with limit | Named-reference cells require primitives/vec-len or mathx/gcount and reject codegen / <closure>. Their imports are explicit or empty. They do not reject the newly forbidden #closure token; add that negative during the marker migration. |
| 4 | 01-display-format.md §1.2.1 | Fixture migration | Notice/payload ordering and the absent-notice negative still discriminate execution/display order. Three cells construct Pure; migrate those fixtures to pure with ACT-1108. Platform-print notice and batch output equivalence do not depend on that constructor. No new pure coverage from their current green. |
| 5 | 01-display-format.md §1.3 | Partial | Use the per-kind defn/deftype/deftrait/impl cells in repl_introspection, rather than the zero-arg-defn witness for every kind. defn_display_neg_not_closure checks the retired token only. Canonical-home twins in ps_d1_impl_confirmation_home assert foreign type/trait homes, but currently load the workspace library; they do not prove prelude independence. |
| 6 | 01-display-format.md §1.5 | Retains with limit | Same named-reference assertions as row 3. Explicitly imported gcount and qualified vec-len observe canonical names; no proof yet against replacement with #closure. |
| 7 | 01-display-format.md §1.5 | Retains | Both cells define List inline. Exact recursive value/whole-line assertions reject raw pointers, type tokens interleaved with values, or a special built-in-list requirement. PrimitivesOnly supplies scalar names explicitly, not stdlib. |
| 8 | 01-display-format.md §1.5 | Partial / stale expectation | Inline Seq and bounded child observe an unforced infinite tail and head 7. The literal <closure> assertion contradicts the new #closure clause; retain termination evidence only until marker migration. No library dependency. |
| 9 | 01-display-format.md §1.5 | Partial | The two cited cells observe named-reference and imported/FQ envelopes, not every value reached through computation. Their retired-token negative needs migration; T-MARKERS adds an anonymous-value RED, not a universal envelope proof. |
| 10 | 03-slash-commands.md §3.9 | Partial rollup | The existing target-resolution cells still observe switching/refusal. Rows 11–16 hold environment parity only for the selected test preludes, not arbitrary or empty prelude contents; dotted/lib-directory target limits already recorded in the row remain. |
| 11 | 03-slash-commands.md §3.9 | Partial | devloop_fresh_prelude_using_mod_turn_compiles supplies TestStandard and requires result 7 with no undefined-variable error. It shows provided + remains available, not that no operator is required with an empty prelude. A prelude absence discriminator is absent from these cells. |
| 12 | 03-slash-commands.md §3.9 | Partial / fixture mismatch | devloop_fresh_mod_turn_bare_type_alias_resolves supplies Int through PrimitivesOnly, while m.cl imports nothing. Its 7/no-unknown-type assertions show a prelude alias, not the newly stated own-file import clause. Needs a module-local-import fixture. |
| 13 | 03-slash-commands.md §3.9 | Partial | devloop_cache_restored_prelude_using_mod_turn_compiles preserves the directory and requires result 7 after restart. It rejects loss of + in a restored namespace; it does not assert a cache-hit diagnostic, so also passes if every module is recompiled. |
| 14 | 03-slash-commands.md §3.9 | Retains | TestStandard is a deliberately supplied prelude. Result 7 plus no undefined-variable diagnostic rejects a fresh /mod environment losing that provided +. The example does not make + mandatory language content. |
| 15 | 03-slash-commands.md §3.9 | Retains with cache limit | The same TestStandard setup and saved directory exercise the restart axis; result 7 rejects loss of the prelude name. No assertion forces the restore mechanism rather than recompilation (row 13). |
| 16 | 03-slash-commands.md §3.9 | Mismatch | The named cell has no Int import in m.cl; the alias comes from its PrimitivesOnly prelude. It does not prove an import written in the file body survives /mod. Do not restore this row from that cell. |
| 17 | 10-terminal-styling.md §10.3 | Partial | display_exact::source_comment_colour_off_carries_no_sgr_neg and its whole-block twin reject SGR in plain output; callable_and_accessor_coexistence_colour_off_carries_no_sgr_neg covers a second surface. They do not establish the whole R1–R15 role table or the new marker bytes under colour-on. No exact §10.4 backlink. |
| 18 | 10-terminal-styling.md §10.4 | Illustration | Worked styling example is subordinate to §10.3. No direct test backlink; scalar/no-SGR cells do not validate every illustrated role or the new #closure text. Do not grade the illustration as fully tested. |
| 19 | 11-macro-introspection.md §11.1 | Partial | expand_user_defmacro only looks for add-i64 anywhere in stdout. It neither isolates the /expand response nor checks fixed point, unchanged non-macro form, no evaluation, valid Sexp or state after an expansion error. Its macro is defined inline; no stdlib dependency. |
| 20 | 03-types.md §3.2.2 | Partial / module seam | `crates/cranelisp-typecheck/src/adt/tests.rs::test_resolution_validates_registered_arity` registers local Option/Color and checks accepted/rejected type arities. It does not observe a seeded primitives/Option, distinct same-spelled local identity, constructor shape or no-prelude qualified use; those new clauses need other evidence. |
| 21 | 03-types.md §3.3.4 | Retains with fixture limit | spec_03_types::returned_rank1_polymorphic_fn_accepted asserts equal written/unwritten schemes; single_poly_instance_used_at_two_types_value_restriction_neg and rank2_argument_applied_at_two_types_neg reject misuse. The result-only-var cells distinguish ambiguity at use from rejection at definition. Test preludes are explicit; batch fixtures still use Pure, so the new pure examples are not covered. |
| 22 | 04-expressions.md §4.6.3 | Partial / stale names | Existing auto_curry_two_param_partial_apply and auto_curry_three_param_partial_apply require 3/60; auto_curry_passed_to_higher_order_fn requires 15; local_closure_auto_curry_non_trait_control_resolves_to_local requires 0. Negative functions are now auto_curry_too_many_args_error_neg / auto_curry_wrong_type_error_neg, not the old bare names. Constrained examples use TestStandard-defined traits. Result behavior survives the rewrite, but #closure examples and the whole multi-signature restriction are not proven by these former citations. |
| 23 | 04-expressions.md §4.11 | Partial rollup | No direct §4.11 backlink. Chained application and branch/match cases observe individual results; a pure arithmetic result alone cannot prove all sequencing/deferral clauses. Reconcile by child/form, not the old section-level Tested tag. |
| 24 | 04-expressions.md §4.11 | Partial | No direct §4.11 backlink to this paragraph. Bind-chain print sequencing (spec_platforms) rejects reversed effects; lenient result parity (spec_12_runtime) allows concurrency. Neither proves physical left-to-right pure evaluation, which is intentionally unobservable. Old Pure fixtures still need migration. |
| 25 | 05-definitions.md §5 | Partial / two bands | stdlib_conformance::stdlib_def_qualified_head_rejected_binder_neg and stdlib_const_qualified_head_rejected_binder_neg assert qualified-head refusal and no silent binding. They load the actual library and do not assert the span at the written macro head or the dotted spelling. Keep binder evidence separate from the unproven written-span band; these are library-route witnesses, not mandatory core macro names. |
| 26 | 05-definitions.md §5.6 | Library-only / mismatch | macro_const_int/string are workspace-library conformance and retain their 42/hi assertions for that library only. exemplar::batch_const_macro_in_main defines its own macro size; it does not exercise const at all. No language obligation that const exists; expansion/binder rules need native-form evidence. |
| 27 | 05-definitions.md §5.6 | Partial / two bands | stdlib_const_qualified_head_rejected_binder_neg observes an error and absence of user/fmt/PI via the library macro. It does not assert dotted-head refusal or the written-head location; no restored claim for either missing clause. Core language does not require this macro. |
| 28 | 05-definitions.md §5.7 | Library-only | macro_def_basic/expression load the workspace library and require 42/3. They still test that library's macro; they do not make def core or establish evaluation-once, visibility or every native expansion rule. |
| 29 | 05-definitions.md §5.7 | Partial / two bands | stdlib_def_qualified_head_rejected_binder_neg and stdlib_def_bare_head_accepts_twin distinguish qualified refusal from a valid bare binding. Neither asserts a dotted spelling or source-span provenance. Both intentionally depend on the actual library; do not infer an obligatory macro. |
| 30 | 05-definitions.md §5.11 | Partial | private_defn_callable_in_module requires result 42 for a private helper used locally. It does not reject imports from outside the subtree or exercise all private definition variants. The rewrite labels const/def as illustrative; no coverage for those follows from a defn-only test. |
| 31 | 05-definitions.md §5.14 | Rollup / no direct witness | No §5.14 test backlink found. Native form tests and library-conformance macro tests must be judged separately; the summary alone is not one independently observed behavior. Do not restore a universal Tested rollup. |
| 32 | 07-traits.md §7.9 | Retains with spelling limit | user_trait_simple defines Inc and its Int impl inline and requires 15. This proves user trait dispatch without stdlib, but not every spelling: the six T-TRAIT-SPELLING REDs show the same mechanism does not hold for Num/Eq/Ord/Display. |
| 33 | 07-traits.md §7.12 | Rollup | The heading has no prose or direct backlink; its child restrictions retain their own evidence. Do not assign a test to an empty heading or promote it above its least-covered child. |
| 34 | 07-traits.md §7.13 | Library illustration | No §7.13 test backlink. derive and its helpers are user/library macros, not required language forms. Missing derive-conformance evidence is not a compiler defect; generic macro expansion and trait impl obligations live elsewhere. |
| 35 | 09-macros.md §9.6 | Retains / partial total | Three cited inline-macro cells require alpha-before-omega, successful type-before-impl dispatch (41), and an error/no-dispatch for reversed order. They reject reordered/spurious registration without a library dependency. They do not by themselves observe every nested/batch begin rejection or the generated-defmacro publication checkpoint. |
| 36 | 09-macros.md §9.10 | Library-only | The four spec_11_stdlib cells use the workspace library. Their when/cond/thread/vec values still observe that library's macros, not required names, layouts or expansions. Bare names are supplied deliberately by that prelude; do not restore normative macro-name coverage. |
| 37 | 09-macros.md §9.10.12 | Library-only / partial | macro_when_true, macro_when_false_none and macro_when_option_body_nests_the_wrap distinguish Some/None and unconditional nesting for actual library when. No unless negative/positive evidence follows from those cells; this subsection is illustrative, not a core obligation. |
| 38 | 10-io.md §10.1.1 | Partial / fixture migration | io_propagates_into_inferred_return_type checks the inferred IO signature of a Pure-producing function. It does not call a platform operation or a wrapper of that operation. Keep that narrow inference observation only; migrate Pure before claiming the new public pure surface. |
| 39 | 10-io.md §10.2.3 | Mismatch / RED public lift | pure_bool_unwraps_inline applies Pure, not pure. It cannot cover the rewritten ordinary-function interface, Bool/String/None lift examples or first-class/partial application. T-IO-OPAQUE public-lift cells are RED on the missing name; Bool/etc remain unallocated. |
| 40 | 10-io.md §10.3 | Partial / fixture migration | bind_triple_chain requires 6 from nested primitive binds using an explicit PrimitivesOnly prelude. It observes composition, not non-execution at construction or the entire scheme; its Pure terminators must migrate. A library bind spelling is not assumed by this fixture. |
| 41 | 10-io.md §10.3.1 | Partial / fixture migration | bind_pure_to_pure_plus_one requires 43, rejecting a dropped/wrong continuation value. It cannot prove that constructing the bind performs no effect (there is no observable effect). It uses Pure, so public pure remains uncovered. |
| 42 | 10-io.md §10.4 | Library-only | macro_do_returns_last asserts 3 using the actual workspace macro. It neither makes do mandatory nor proves the compiler recognizes only expanded core bind. This remains library conformance only; Pure fixture migration is carried. |
| 43 | 10-io.md §10.4.1 | Partial / native witness | spec_platforms::bind_chain_print_sequence_with_pure_terminator_emits_all asserts exact one/two stdout and exit 42 with explicit bind imports, without do or bind! or stdlib. It tests the expanded core behavior, not an actual macro's expansion; replace its terminal Pure during the migration. |
| 44 | 10-io.md §10.4.2 | Library illustration / no direct witness | No exact §10.4.2 backlink. The library do cells test selected values, not a universal core form or all IO-only refusal cases. Core sequencing requirements belong to bind and native typing. |
| 45 | 10-io.md §10.4.3 | Library illustration / no direct witness | No exact §10.4.3 backlink. The printed greeting/show examples are not executed by an exact sample test here; the compiler does not owe these library names. |
| 46 | 10-io.md §10.5 | Library-only | macro_bind_bang_single_binding requires 42 using workspace bind!. Retains that library observation; no assertion proves an exact expansion or a mandatory bind! form. The native bind acceptance cells are separate. |
| 47 | 10-io.md §10.5.1 | Library illustration / no direct witness | No exact §10.5.1 backlink. No test of the expansion strings follows from a successful library bind! result. New pure in the illustrated expansion is absent in the compiler. |
| 48 | 10-io.md §10.5.2 | Library-only / partial | macro_bind_bang_sequential_reference requires 10 when y uses x through actual library sugar. It rejects losing earlier-binding scope, but does not cover all IO-type refusal or evaluation-order clauses; current fixture still uses Pure. |
| 49 | 10-io.md §10.5.3 | Library illustration / no direct witness | No exact §10.5.3 backlink. The distinction between discarded and named results is illustrative sugar over bind; library do/bind! cells cannot establish a required syntax. |
| 50 | 10-io.md §10.8 | Insufficient former witness | io_values_deferred defines deferred and immediately calls it, asserting 99. It has no observable side effect and cannot distinguish eager execution from deferral. The rollup's still-pending isolation/comparison children must remain visible. |
| 51 | 10-io.md §10.8.1 | Partial / module seam and migration | `crates/cranelisp-intrinsics/src/io/tests.rs::test_run_io_pure` constructs an internal node, forces it once and requires 42. It does not observe public pure, effect deferral, bind composition or node reuse. The named reuse cells cover sequential Pure/Effect only and still use constructor fixtures; Launch/EffectPoll/concurrent reuse remain unmeasured as recorded. |
| 52 | 10-io.md §10.8.2 | Partial / weak depth | run_mode_deep_bind_chain_named_continuation requires 8 from nine binds, rejecting a dropped/reordered continuation. Nine frames would also pass a recursive implementation; it does not prove O(1) depth. Current Pure terminals need migration; the deeper intrinsics module witness is separate, not solution-level proof. |
| 53 | 10-io.md §10.8.3 | No direct witness | No §10.8.3 backlink. The specified choose/print two-input discriminator is not in the former covering set; io_values_deferred does not discriminate it (row 50). Return to QA as an effect-isolation gap. |
| 54 | 10-io.md §10.8.4 | Mixed summary | No §10.8.4 backlink. The new user-inspection clause is observed RED by T-IO-OPAQUE; stack/ordering/deferral need their own witnesses. The Haskell column is explanatory comparison, not executable compiler behavior. |
| 55 | 10-io.md §10.10 | Retains narrow ABI witness | link_repeated_platform_adt_marshal_does_not_corrupt_heap uses an inline Rectangle, explicit primitives and 200 linked platform calls; exit 0 rejects accumulated heap corruption. It does not establish every ABI layout/signature rule. Its terminal Pure requires migration, not a stdlib dependency. |
| 56 | 10-io.md §10.10.3 | No direct witness / module allocation | No exact §10.10.3 solution backlink. The allocator callback's identity/layout is a module/ABI condition; a surviving marshal loop alone cannot distinguish every wrong allocator callback. Route to QA/dev rather than manufacture a middle-tier test. |
| 57 | 10-io.md §10.12 | Partial / wrong former summary witness | resource_serial_same_token_serializes measures exclusion, not the newly stated independence analysis on core binds. auto_io_independent_diff_token_parallelizes_e2e and its dependent/Sequential controls are nearer candidates; timing alone does not prove a composed node when sequential runtime execution is allowed. |
| 58 | 10-io.md §10.12.1 | Partial / over-strong timing | auto_io_independent_diff_token_parallelizes_e2e requires sub-midpoint overlap for explicit primitive bind chains in run/link; dependent and Sequential controls require serialization. They distinguish scheduling outcomes, but mandatory observed overlap is stronger than the rewritten runtime MAY (sequential execution allowed). QA must separate compiler composition evidence from runtime performance. |
| 59 | 10-io.md §10.12.1 | Partial / same issue | Same core-bind fixtures as row 58. Their timing cannot prove composition independently of runtime execution strategy; no unchanged blanket Tested judgment is warranted for the MAY clause. This is a QA classification handoff, not a newly classified product defect. |
| 60 | 10-io.md §10.12.4 | Partial | resource_serial_same_token_serializes asserts a lower elapsed bound in run/link. It rejects overlap on one token but cannot reject serial effects executed in reversed source order. concurrency_capacity::same_token_capacity_1_blocking_serial_and_source_ordered and the poll twin add exact stdout order; all are explicit bind fixtures, with carried Pure migration. |
| 61 | 10-io.md §10.12.4.1 | Partial / timing classification | Capacity cells cover distinct/shared pools, N+1 parking and capacity-1 source order on blocking and poll carriers. They use explicit imports and core binds. Lower timing bounds observe admission ceilings; upper overlap bounds demand more than the paragraph's permitted sequential execution, so QA must retain those as implementation-performance evidence only. |
| 62 | 10-io.md §10.12.4.1 | Retains ceiling; partial whole row | same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks and its poll twin assert lower bounds rejecting all N+1 effects overlapping; their upper bounds demand saturation/overlap, not required by this MAY. No direct observation of each begin instant; wall clock is the declared discriminator. Pure terminals await migration. |
| 63 | 10-io.md §10.12.5 | Partial / mechanism-neutrality | concurrency_cancellation::blocking_par_without_select_waits_for_both_workers_control observes join behavior for the current mechanism. It cannot require rayon/reactor selection. The normative value/order/permit clauses need their dedicated cells; mandatory overlap checks cannot grade the allowed sequential alternative. |
| 64 | 10-io.md §10.12.7 | Partial rollup | launch_and_continue_runs_concurrently_launcher_does_not_await observes an unused-result/disjoint-token bind loop; degree_n_bounds_inflight_launched_effects_nplus1_parks observes throttling. They do not cover all eligibility/cancellation ownership clauses (ACT-0977). Both use Pure terminals awaiting migration; no do spelling is needed. |
| 65 | 10-io.md §10.12.7 | Retains current detached witness | launch_and_continue_runs_concurrently_launcher_does_not_await asserts a positive duration floor (effects ran) and an upper overlap bound (launcher did not await five effects). Its source is a primitive bind loop; result-unused eligibility is explicit. It observes the detached path, not a language requirement to detach every eligible call. |
| 66 | 10-io.md §10.12.7 | Partial / constructive eligibility | The same fanout loop has an unused continuation parameter and returns 0; its value does not use the effect result. This shows a legal discarded-result shape, not an independent dynamic test that no launched result can ever be observed. The rule is conditional on unused-result eligibility. |
| 67 | 10-io.md §10.12.7 | Retains panic clause | detached_faulting_effect_exits_the_process asserts a nonsignal nonzero exit and exactly the permitted panic report; the nonfaulting fanout control requires completion. This rejects recovery/continued launch execution. Explicit primitives, with Pure terminal migration still carried. |
| 68 | 10-io.md §10.12.7 | Retains with fixture limit | degree_n_bounds_inflight_launched_effects_nplus1_parks uses distinct tokens and degree=2, so the lower timing bound rejects unbounded launch admission. Its upper bound also demands overlap of the current implementation. No library sugar; terminal Pure migration remains. |
| 69 | 10-io.md §10.12.8 | Partial / surface split | select and sleep cells exercise language operations; race/timeout cells currently import primitives/race or implement a helper themselves. The new classification requires library derivation, so existing primitive-race greens cannot establish the public library contract. Empty-select and winner/cancellation clauses are separable below. |
| 70 | 10-io.md §10.12.8 | Retains value; cancellation partial | concurrency_cancellation::select_returns_first_completed_value requires FAST as exit status with the fast branch in the middle; wrong source-first/last/index results differ. select_only_winner_value_returned_losers_side_effects_absent_neg adds losing-output absence. No library or Pure construction is needed for those direct select fixtures. |
| 71 | 10-io.md §10.12.8 | Retains separated winner | The same middle-fast select fixture requires FAST and completion before SLOW. It rejects source-order-first selection when the later branch completes first. It does not choose a winner for simultaneously-ready ties, which the spec deliberately leaves unspecified. |
| 72 | 10-io.md §10.12.8 | Retains value/index discriminator; example unbuilt | select_returns_first_completed_value returns FAST milliseconds, distinct from middle index 1. That rejects index-returning implementations. The new tagged-value example using public pure has no covering cell here; do not infer its availability from the result-only witness. |
| 73 | 10-io.md §10.12.8 | Partial / core versus library | select_only_winner_value_returned_losers_side_effects_absent_neg rejects running all select branches to completion. The two race cells exercise primitives/race, now withdrawn from required core surface, so migrate them to select or a local/library derivation before core claims. The cancellation-context contrast remains ACT-0977; losing-output absence alone does not prove all resource releases. |
| 74 | 10-io.md §10.12.8 | Library illustration | timeout_io_completes_before_deadline_returns_result and timeout_io_exceeds_deadline_fires_and_cancels_io_neg use a test-local timeout derivation, not required core syntax. They observe Some/None and losing completion absence for that derivation only; it still uses primitive race and Pure. No new public-library claim is established. |
| 75 | 10-io.md §10.12.8 | Partial | sleep_parks_for_duration_then_resumes_and_continues asserts a duration floor and exit 7 after the timer; linked twin asserts exit 7 only. Neither reads the sleep payload (continuation ignores it), so the specified result 0 is not proven. A duration lower bound alone would also accept seconds instead of milliseconds; do not claim the unit's negative direction from it. Pure continuation migration remains. |
| 76 | 10-io.md §10.12.8 | Retains with mode limit | The four empty-select cells require the message, nonsignal nonzero exit, no fabricated value, bounded completion, and run/REPL termination parity. They use direct select with explicit or qualified primitives. The carried set does not establish the linked leg from these citations alone. |
| 77 | 11-stdlib.md §11.2 | Partial inventory | trace_returns_trace_type and the Trace import/FQ cells retain selected seeded-Trace observations. The bare-name negative is weak (contains TraceCall suffices), not a decisive unresolved-name assertion. Pure constructor execution cannot prove opaque IO; T-IO-OPAQUE is RED. Newly listed seeded Option/Result/Pair are not inventoried by this former set. Non-normative reference table does not create a second spec authority. |
| 78 | 12-runtime.md §12.4 | Rollup / partial | Judge strictness, lazy ADTs, lenient scheduling and explicit control separately (rows 79–84). A Tested rollup cannot stand while descendants carry marker/pure migration and unmeasured clauses; no one direct section test. |
| 79 | 12-runtime.md §12.4.1 | Partial / insufficient former witness | application_chained requires 3 from nested pure inc calls. It does not distinguish eager versus lazy argument evaluation, let order, one-branch-only evaluation or first matching arm. No library dependency, but no complete strictness claim from this cell. |
| 80 | 12-runtime.md §12.4.1 | Partial | No exact §12.4.1 paragraph backlink. Bind/print ordering observes effect order, not unobservable scheduling among independent pure operands; lenient value-parity cells are relevant candidates. Neither justifies grading physical evaluation order by result alone. |
| 81 | 12-runtime.md §12.4.2 | Retains core lazy-ADT behavior | Both cells declare Stream inline, with explicit primitives, and require 42/37 while constructing an infinite thunked tail. Eagerly forcing the tail times out. This matches user-controlled laziness and requires no built-in Seq; Pure main terminals await migration. |
| 82 | 12-runtime.md §12.4.3 | Retains clauses with gaps | Panic-exit predicates reject recovery, continuation, signals and duplicate reports; dual-panic accepts either message. Nonpanicking twins assert actual spawns. Trace frame-count plus trace_declines and untraced-spawns distinguish the strict trace exception. Result parity cells alone do not grade heuristic policy. Existing Pure fixtures still need migration; no blanket all-clauses restoration. |
| 83 | 12-runtime.md §12.4.3 | Partial / changed permission | Lenient ON/OFF result cells reject result corruption; trace decline/spawn controls observe the exception. Fixed overlap/spawn demand must be judged against the paragraph's allowed sequential implementation, not promoted to universal acceptance. No new language requirement is inferred here. |
| 84 | 12-runtime.md §12.4.3 | Partial | apply_arg_single_expensive_preserves_result_parity requires the same result with ON/OFF, but explicitly delegates no-spark emission to another tier. It cannot prove the cost/at-least-two heuristic never spawns. Cheap/mixed let result cells have the same limitation; source-only mapping, no new module claim. |
| 85 | 12-runtime.md §12.5 | Retains selected tails / partial total | Million-depth countdown and 100k match/let tests reject stack growth at those tail sites. Accumulator and non-tail cells only assert values (5050/55), not frame behavior. They do not prove every tail position or macro-expanded tail; Pure/library macro migration is separate. |
| 86 | 12-runtime.md §12.5 | No dedicated depth discriminator | Fanout's five-launch and four-launch degree loops are too shallow to falsify linear stack growth; ordinary million-depth pure TCO cannot prove launch/trampoline interaction. No exact launch-depth cell located in this backlink walk. Return this clause to QA without equating shallow success to constant space. |
| 87 | 12-runtime.md §12.7.6 | Retains report clauses / platform-value gap | platform_errors cells assert one unprefixed FQ-named stderr line, nonzero nonsignal exit and no resumed REPL; nonfaulting twins finish. auto_io_par_branch_panic_exits_neg checks a parallel panic. These reject recovery and wrong report shape; they do not observe expected platform failures returning Option/Result values. The --test leg remains module-only as recorded. |
| 88 | 12-runtime.md §12.7.7 | No direct witness | No §12.7.7 backlink. Ordinary Option/Result matching does not prove the absence of panic/error/throw/raise core entries. The example's explicit primitive imports remove a prelude assumption, but do not create executable evidence for the entire negative inventory. |
| 89 | 12-runtime.md §12.9 | Insufficient former witness | display_int_result only observes scalar REPL output. It cannot prove trace/REPL formatting equality, independence from a user Display impl, ADT formatting or marker rules. T-MARKERS supplies two narrow REDs, not canonical-format uniformity. |
| 90 | 12-runtime.md §12.9.3 | Mismatch | display_int_result displays 3; it never reaches vector/string/depth thresholds or compares trace output. No uniform elision or unchanged underlying-value assertion follows. Return the SHOULD clauses to QA as unevidenced by this cited cell. |
| 91 | appendix-a-builtins.md §A.2 | Partial reference inventory | vec_literal_int observes a Vec type prefix; defmacro_identity_expands only proves an identity macro result, not every Sexp/SList constructor; pure_int_unwraps_inline uses the retired constructor. These cannot justify the expanded seeded-type inventory or opaque IO. Treat the non-normative reference separately from normative source sections. |
| 92 | appendix-a-builtins.md §A.2 | RED opaque IO | No former cell (S9). T-IO-OPAQUE now observes public lift absence and accepted constructors/matches; it provides RED evidence of the rewritten opaque contract. The bare-Bind and pure-only-match refusals are narrow greens, not total opacity. |
| 93 | appendix-b-examples.md §B.1 | No backlink / library example | Hello-world explicitly imports the reference prelude and show. No direct B.1 cell; generic print tests do not execute this exact program. Reference example, not a mandatory compiler-provided show function. |
| 94 | appendix-b-examples.md §B.2 | No backlink / library example | Factorial explicitly imports arithmetic/show from the reference prelude. No direct B.2 cell; unrelated recursion tests cannot establish this exact sample's output under its imports. |
| 95 | appendix-b-examples.md §B.3 | No backlink / library example | Inline ADTs and Display impls depend on explicitly imported library Display/do/show. No direct B.3 witness for the combined output; trait and ADT unit results elsewhere are narrower. |
| 96 | appendix-b-examples.md §B.4 | No backlink / fixture blocked | The sample uses library bind! and new public pure. No direct B.4 cell; pure is absent (ACT-1108), so the rewritten sample cannot currently be accepted by a conforming-output guard without that product work. |
| 97 | appendix-b-examples.md §B.5 | No backlink / library example | The Seq collection functions come from the explicit reference prelude. No direct B.5 witness; inline Stream tests prove the core thunk mechanism, not these library transformations or this full transcript. |
| 98 | appendix-b-examples.md §B.6 | No backlink / library example | The example explicitly imports macros data and core.syntax/slist. No direct B.6 witness for 42/Some99/30 together; no implicit requirement for slist or when is inferred from generic macro tests. |
| 99 | appendix-b-examples.md §B.7 | No backlink / library example | Higher-order code uses explicit prelude arithmetic and do/show. No direct B.7 witness; individual closure/curry tests do not execute its combined sample or establish a mandatory library layout. |
| 100 | appendix-b-examples.md §B.8 | No backlink / library example | Threading macros and collection helpers are explicit reference imports. No direct B.8 cell; spec_11_stdlib threading cells are library-specific and do not validate this exact pipeline. |
| 101 | appendix-b-examples.md §B.9 | No backlink / library example | The sample's map over Vec/List/Seq relies on the reference library. No direct B.9 cell; native multi-signature tests do not prove its container helpers or output. |
| 102 | appendix-b-examples.md §B.10 | No backlink / library example | Num/show are supplied by the reference prelude. No direct B.10 cell; constrained core tests observe selected dispatch results, not this combined reference output or every trait spelling (ACT-1103). |
| 103 | appendix-b-examples.md §B.11 | No backlink / library example | Three prints are sequenced by explicitly imported library do. No direct B.11 cell; exact native-bind print tests are candidates for the expansion mechanism only, not execution of the authored macro sample. |
| 104 | appendix-b-examples.md §B.12 | No backlink / fixture blocked | The conditional uses new pure for its non-effect branch. No direct B.12 witness; Pure-based branch-unification cells cannot prove the rewritten interface, absent under ACT-1108. |
| 105 | appendix-b-examples.md §B.13 | No backlink / fixture blocked | The combined do/bind!/read-line sample imports the reference library and ends with new pure. No direct B.13 cell or exact stdin/transcript witness; public pure absence is a product blocker, not a test setup completion. |
| 106 | appendix-c-nfr.md §C.3.2 | Partial / architectural clauses | Core-bind scheduling timing witnesses and select cancellation/output witnesses map to the behavioral parts of §10.12. The same-token order cells distinguish exclusion from order. No one cell proves emitted-node insertion or all detached cancellation contexts; ACT-0977 remains. Underlying infrastructure guarantees need module/arch evidence, not a new internal-session integration tier. |
| 107 | appendix-c-nfr.md §C.4.4 | Architectural / no solution cell | No C.4.4 backlink. Registerable opaque Chan, reusable pool and dispatch extensibility are future architecture constraints; current IO tests cannot prove that new channels need no core-dispatch change. Route to arch/QA, not a fabricated language test. |
| 108 | index.md §Notation | Editorial / no runtime cell | Notation defines EBNF, requirement levels and explicit example scope, not one runtime behavior. No direct notation backlink. Tests with chosen preludes show only their fixtures; they cannot establish that no prelude is assumed throughout the prose. QA/spec must judge this editorial summary separately. |
