# Sprint 115 — sprint-wide test plan (Phase 3, 2026-07-20, /qa)

> **Retained dated record.** Only the sections that current source, tests,
> open filings or [the current plan](PLAN.md) cite by number remain, with their
> original numbering: §3.1, §6 (6.1, 6.5), §8 (8.1, 8.2), §9.5 and §10.2. §9.5
> keeps the only verbatim capture of the 0694 Class I heap corruption. They
> are S115 allocations, attributions and observations, not current status; each
> RED, carry, count or line number is dated 2026-07-20/21 and must be compared
> with current source before reuse. The risk read, the carry-RED flip
> constraints (§1), the 0604 wave rows other than §3.1, the 0702 cells, the
> §8.3–§8.6 and §9.6 dispositions and the other removed sections are
> recoverable with `git show a07823d8:tests/plan/s115-test-plan.md`; the riders,
> certification numbers, W7 dispositions and exit statement with
> `git show 48d6e713:tests/plan/s115-test-plan.md`. Filing 0694 carries the
> open load-dependent members. Filing 0798 carries the module-alias qualifier
> defect formerly at §10.3.
## 3. The 0604 wave — test design (Track B, O1; /dev(src) + /testing)

### 3.1 The synthesized-trigger unit test (/testing; the fail-on-revert guard)

**Design constraint discovered at Phase 3 (matrix R7 row): the existing
chokepoint test cannot serve.** The former binding-era test is superseded by
`src/imports/tests.rs::candidate_closure_rejects_out_of_closure_public_write`, which
injects a public import whose source LACKS the name — a shape that the
current provider-existence predicate AND the corrected
declared-export-closure predicate both reject. It fails on revert of the
CHOKEPOINT but not on revert of the CORRECTION. The new trigger must be the
discriminating cell:

1. **Trigger cell (RED against today's predicate by construction, GREEN
   with the correction — authored failing-first)**: synthetic tables where
   the source module genuinely PROVIDES the name publicly (the live
   phantom's shape — e.g. `primitives` providing `bit-and`, which it really
   does: `cranelisp-primitives/src/lib.rs:412`), injected as a PUBLIC
   import entry into a terminal `prelude` table whose DECLARED export
   closure does NOT include it → assert the diagnosed error; assert the
   message self-identifies as an internal R7 invariant breach naming the
   seam + module + name + source edge (the arch §4 tier-3 sub-form ruling —
   never mistakable for a user diagnostic). Interleaving-independent: a
   direct call against constructed tables, no session, no threads.
2. **False-fire fence (same change-set)**: a public write INSIDE the
   declared closure passes — including the subtree-private re-export shape
   the current rustdoc names as the deliberate permit (`collect_specific`
   already vetted it), and prelude's own public definition (§8.4). The
   corrected predicate must not reject the legal population.
3. **Census-row guard**: if `commit_staging_to_live` is ROUTED through the
   gate (vs a named legal-skip), one unit at that seam pins the routing
   (an out-of-closure public staged entry is rejected at commit — fails on
   revert of the routing). If a legal-skip is ruled, the skip's rationale
   is asserted in the census table (rustdoc/artifact), and the plan records
   WHY no test exists (enumerated deferral).
4. **Existing test retained** as the provider-existence negative sibling;
   /testing corrects its falsified comment ("primitives has NO bit-and",
   `imports/tests.rs:904–942`) in the same rider — the fixture mechanics
   stay valid as a synthetic; only the claims-to-mirror-reality narrative
   is false. /dev(src) corrects the `src/imports.rs:251` predicate comment
   (arch revision 2) in the wave.

## 6. New-instrumentation coverage rows (METHOD §2.2 — every owed matrix item that lands gets its tests)

### 6.1 R6 validation seam (/dev(backend, cache) change-set)

Unit tier (enumerated; each fails on revert of its validation arm):

1. Corrupt sibling-slot index (out of range) → diagnosed `CacheStale`, never
   trusted into emission.
2. Corrupt summary param index — a persisted `MayAliasOf(k)` with `k` ≥
   arity → `CacheStale` (the `arg_origins[k]` OOB hazard the register
   names).
3. Corrupt span key / malformed `callees` FQ → per-family `CacheStale`
   class asserted distinct (the class taxonomy is the census's).
4. Valid meta round-trips untouched (false-fire fence).

E2e (assessed BEFORE the fix, per METHOD §2.2 — warranted: observable
end-to-end and crosses the cache boundary): ONE cell — tamper a persisted
`.meta.json` field (summary index) in a warm cache dir, re-run → recompile
+ correct output, no crash, no stale-summary elision (extends the CS-1/AG-1
schema-gate family with a FIELD-level face). /review verifies census
completeness against the rustdoc artifact (arch revision 3).

### 6.5 Fix-wave unit obligations (enumerated so nothing falls through)

- §1.1: each corrected/added §16.2 rule-table row exercised at the unit
  tier (chained-link protect present in the emitted accounting).
- §1.3: TraitDecl registration arm accept/reject pair.
- §1.4: tail-jump flush ADT-wrapped-param arm; entry-frame protect license
  both toggles.
- §1.5: wrapper-emission totality per carrier state + illegal-state located
  error.
- §1.6: impl registration same-type accept / changed-type reject.
- §1.7: restore-notice count-from-record seam.
- 0604: §3.1 cells.

## 8. Mid-Phase-5 disposition batch (post-W3, 2026-07-21, /qa)

Evidence-only batch (no suite run — /review(backend) held the run token).
Every verdict below was checked against SOURCE at the W3 tree, not against
the wave reports.

### 8.1 FIXME 0745 — ATTRIBUTION: the entry-`main` heap-payload leak is the
### PROGRAM-RESULT-VALUE lifetime seam, owned by int

**Falsification claims VERIFIED.** /dev's two measurements are consistent
with source:

- `crates/cranelisp-intrinsics/src/panic.rs::cranelisp_run_program` (step 4)
  calls `io::drive_io(main_result)` then `drop::consume_io_tree(main_result)`
  and returns `ProgramOutcome { exit_code: inner, .. }`.
- `io.rs:236-243` (and the `:986` twin): the `IO_TAG_PURE` arm reads
  `field0` and returns it **without an inc**.
- `drop.rs:303-307`: the `IO_TAG_PURE` arm is a deliberate no-op on the
  payload ("Pure's payload is opaque — the trampoline returns it to the
  caller as the final value"), while the box itself is freed.

So the payload's single reference **transfers to the returned value**, and
the accounting inside the compiled code is coherent. `protect_return_value`
is NOT the seam, mechanism (a) has no referent (the leak reproduces with no
`let`), and §2.1 is re-scoped to faces 3 (0720) only. **The re-attribution
is ACCEPTED.**

**Owner (my placement): `/design`(int) → `/dev`(src), with a REQUIRED
`/arch` consult on the release mechanism.** Grounds:

1. **Nobody releases the program result value, in any mode.** Verified by
   absence: `src/` contains no rc-dec / value-release call site at all
   (`grep -rn "release_value\|consume_value\|rc_dec" src/` → only a
   `src/CLAUDE.md` prose hit). `--run`/`--link` route
   `main` → `cranelisp_run_program` → `ProgramOutcome.exit_code` →
   `src/main.rs:331` (truncate to exit code); the REPL routes
   `src/pipeline.rs:148-151` → `program_outcome_to_result` →
   `ExprOutcome::Value` → `display::result_value_doc` (which DEREFERENCES a
   heap result). Neither path decs.
2. **Only int knows the result TYPE.** The driver's whole type knowledge is
   `main_returns_io: bool`; `src/main.rs:331` already branches on
   `ty == Type::Int`. The heap-vs-immediate judgment and the drop-glue
   selection can only be made where `ty` lives.
3. **This is Decision 24 (consuming convention) at the ONE call boundary
   whose caller is Rust host code rather than generated code.** Framing the
   defect that way is what makes it a single seam instead of an IO quirk.

**Defect class: `rc-miscount`** (leak). Not `carrier-loss`, not `uaf` — the
accounting is coherent, the final owner simply does not exist. Locus for
the pin's `// defect:` re-locus (a /testing rider, since the current locus
`compiler/rc_emission.rs::protect_return_value` is now falsified):
`src/` program-result-value lifetime seam (`pipeline.rs::
program_outcome_to_result` + `main.rs` exit conversion + the REPL display
consumer), `owner=/dev` unchanged, `found=S114` unchanged.

**Fix constraints (binding on whoever takes it):**

- **Release strictly AFTER consumption.** Decing the payload inside
  `consume_io_tree`'s `Pure` arm, or backend-side before the return, is a
  **UAF on the LIVE REPL path** — not merely the defensive one. Correction
  to 0745's citation: `src/repl/format.rs:598` is documented-unreachable for
  current callers; the live dereference is `pipeline.rs:149` →
  `ExprOutcome::Value` → `display::result_value_doc`. The UAF conclusion is
  unchanged and now stronger (it is on the ordinary path).
- **Mode-uniform by construction.** REPL / `--run` / `--link` must reach the
  release through ONE path (P11); a `--run`-only release is a
  `mode-divergence` defect in waiting. Note the asymmetry that makes this
  easy to get wrong: under `--run`/`--link` the leak is harmless in effect
  (process teardown reclaims it) and is observable ONLY through the M3
  parity mode / the tier-4 oracle lane; at the REPL it is a real
  per-expression accumulating leak. The oracle lane is the acceptance
  instrument precisely because the `--run` face is otherwise invisible.
- **A type-erased release does not exist today.** `HeapHeader`
  (`crates/cranelisp-types/src/heap.rs:18-24`) is `{alloc_size, rc}` — no
  drop-glue pointer. Releasing an arbitrary typed result therefore needs
  either (a) a type-directed release entry int can call (glue lookup —
  trivial in JIT, NOT free under `--link`), or (b) a scoped mechanism
  covering the shapes a program result can take. **Choosing between these
  is an `/arch` call, not a `/dev` one** — it is the cross-crate half of
  this attribution.
- **Do not add a second ownership model at `consume_io_tree`.** The
  opaque-payload contract there is correct as documented; the symmetric
  hygiene option (inc in `drive_io`'s Pure arm + dec in the `consume_io_tree`
  Pure arm) is accounting-neutral and does NOT fix the leak — it must not be
  mistaken for the fix.

**Scope question (open; decides fix size, NOT the owner).** Is the class
IO-specific or general result-value ownership? Source says general (see 1
above — no release exists for any result). Confirming one-liner, for the
owning skill, not a blocker for placement: at the REPL with
`CRANELISP_RC_STATS=1`, compare `(let [s "hi"] s)` (heap result, non-IO)
against `(let [s "hi"] 9)` (immediate result). If the former leaks 1 and the
latter balances, the entry-payload pin is ONE FACE of a general seam and the
fix must be authored at that grain (and `/testing` owes a non-IO sibling pin
in the same change-set).

**Routing verdict for /sprint: this RED does NOT flip in S115.** It needs a
`/design`(int) pass plus an `/arch` mechanism ruling; W3/W4 are backend and
typecheck; W6 is a scheduled src window but is scoped to impl-redefinition +
0718 and has no design input for this. Carry
`adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2`
into certification as an **attributed carry with a NEW owner** (the S115
exit statement must say so explicitly — a carry whose attribution moved is
not the same carry). §1.4's "ONE sweep, three faces" acceptance is
**re-scoped to the two 0720 faces, both of which flipped**; the
entry-payload face leaves that row. Do NOT author the toggle-ON sibling pin
now (0745 is right: a second RED for one unfixed defect).

### 8.2 FIXME 0746 — m3 re-plant: §4.1 prong-2 lifecycle case, CONFIRMED;
### re-plant SYNTHETIC

**Confirmed, on source.** `tests/ms_p6_mode_self_tests.rs`'s `LEAK_PROG`
(`(defn g [] (let [s "hi"] (Pure 9)))`) plants exactly the general
G2/item-26 `protect_return_value` over-inc that W3 change-set 2 fixed. The
test's own FLIP-HAZARD comment predicted this verbatim, and this is the
**second** staleness of the same plant (first: S114 FIXME 0690, when the F-R1
fix balanced the entry-`main` shape). **Not a regression** — the compiler
moved in the correct direction and the fence's stimulus evaporated.

This is `memory-safety-coverage.md` §4.1 **prong 2** (an e2e capability
fence whose plant is a live compiler defect) reaching its end of life. Both
compliant dispositions are available; I rule the order:

1. **PREFERRED — re-plant SYNTHETIC** (the S114 MS-P6 precedent,
   `safety_lane_detects_falsified_clean_expectation_capability_green`,
   `7c2d5168`): a test-only injected imbalance at the intrinsics allocator /
   diagnostics seam, behind an env gate that is inert unless set. This makes
   the fence fail-on-revert of **the MODE** rather than of an unrelated fix
   — the only shape with a non-expiring half-life. Requires a small
   `/dev`(intrinsics) hook + a `/testing` re-plant, and the hook MUST join
   `crates/cranelisp-intrinsics/src/diagnostics/tests.rs::all_gates_default_off` (the byte-identical-off
   fence) in the same change-set.
2. **FALLBACK (compliant, no user sign-off needed) — retire
   `m3_parity_catches_planted_leak` with a §4.1 tombstone.** Prong 1 is
   already in place (four parity self-tests at
   `crates/cranelisp-intrinsics/src/diagnostics/tests.rs:100/:108/:116/:124`)
   and prong 3 is already in place (`m3_parity_no_false_abort_on_clean` keeps
   the M3 env wiring exercised end-to-end). The tombstone must name the
   drained fault set (0690 F-R1 entry-`main`; S115 W3 item-26 general
   protect), the unit-tier successor, and the surviving wiring face.

**REJECTED: 0746's candidate 1** (re-plant on the entry-`main` heap-payload
leak). Per §8.1 that defect is real, live, and owned outside backend — but
planting on it repeats the exact anti-pattern for a third time, and it now
has an owner and a fix path. A capability fence must not be collateral of
someone else's fix.

**Routing: W7, and it must NOT reach certification RED.** 0746 stays
`target: /testing` with the ruling appended and a named `/dev`(intrinsics)
dependency for shape 1; if W7 capacity does not admit the hook, `/testing`
takes shape 2 in the same slot. Either way the RED is gone before the ≥2
certification runs, and the outcome is recorded on this row.

**Standing rule (added to `memory-safety-coverage.md` §4.1):** a prong-2
plant drawn from a live defect is **self-expiring** — prefer a synthetic
plant whenever a test-only injection hook is constructible at the seam the
mode instruments; draw from a live defect only when it is not.

## 9. CERTIFICATION — the S115 suite state (W7, 2026-07-21, /qa)

### 9.5 FIXME 0694 — the flap family adjudicated: TWO phenomena, not one

The evidence that was missing for three sprints arrived at W6: two in-suite
failures captured **verbatim**. They are not the same kind of event, and the
single most consequential thing this section says is that **treating them as one
"flap family" would have sent one investigation after two different bugs**.

**Member 4 — `macro_clause_interior_alias_double_free_run`** (`…/scratchpad/suite_r3.log:1235`):

```
thread 'macro_clause_interior_alias_double_free_run' panicked at
tests/macro_expansion_interior_alias_double_free.rs:132:5:
… → `main` returns `(Pure 3)` → exit 3; got exit None:
free(): chunks in smallbin corrupted
```

`free(): chunks in smallbin corrupted` is **glibc's own heap-consistency
detector aborting the subprocess**. Exit `None` = killed by signal, no exit
code. This is not a threshold, not a timeout, not a slow machine: it is the
allocator finding its free-list metadata overwritten. **A memory-safety datum.**
Note what else that run shows — the file's four sibling faces (`_repl`, `_link`,
`_m1_on_quarantine_face`, `_m1_off_assert_face`) all PASSED in the same run, so
this is per-process and per-mode, not a machine-wide condition.

**Member 1 — `nullary_return_dispatch_method_only_import_no_codegen_leak`** (`…/scratchpad/suite_r2.log:1299`):

```
Error: codegen error at 14..15: codegen failed for /:
codegen error at 14..15: undefined function: z
```

A **compile-time diagnostic**, produced by a subprocess that then exited
cleanly. Nothing was corrupted; a symbol the compiler needed was not there when
it looked. This is the signature of a **publication/enrolment ordering
question** — the `shared-state-write-race` class, the same class 0604 hardened.

**Verdict: TWO phenomena, sharing ONE enabling condition.**

The shared enabling condition is real and explains why both look like "load
flaps": every e2e test spawns its own `cranelisp` subprocess, and each subprocess
is itself multi-threaded (index worker, rayon sparks, IO reactor). Host CPU
oversubscription under a full nextest run changes *intra-subprocess* thread
interleaving. That is one condition, and it is why both families surface only
under suite load.

But what breaks is different, the owners are different, and the severity is not
comparable:

- **Class I — heap-invariant violation** (member 4). A memory-safety defect.
  Candidate mechanism: concurrent RC/drop on a shared cell, or a
  double-release/overrun, in a subprocess whose workers interleave differently
  under contention. Note the aggravating history: this test is the repro for
  0638, a double-free *fixed* at S114 W5 (`58ac8e46`). Either the fix was
  incomplete, or a *second* mechanism reaches the same heap — and the S98 lesson
  is binding here: **a "fix" verified by symptom absence under one condition may
  be a false green from perturbation**. Severity: highest in the set.
- **Class II — publication/enrolment ordering** (members 1 and 3; both are
  REPL-mode cells of the SAME multi-sig / no-impl-fallback seam family, which is
  itself a discriminating datum and argues one bug, not two). A correctness
  defect with no memory-unsafety. If it happened deterministically it would be a
  plain `carrier-loss`/`wrong-reject`.
- **Class III — unclassified** (members 2 and 5). One observation each, no
  captured output. Member 2 explicitly is NOT explained by the 0615
  binary-provenance race (the `cfg(not(feature = "agent"))` face runs in the
  DEFAULT suite). **Honest status: unclassified.** Two observations do not make a
  class, and I decline to assign them to I or II.

**Which parts of the above are hypothesis.** Per METHOD §2.2, an attribution
needs a **discriminating control** and a **seam observation**. Stating it plainly:

- **Established (observed):** the two failure signatures, verbatim; that they are
  categorically different kinds of event; that sibling faces passed in the same
  run; that members 1 and 3 sit on the same seam family; that all five pass in
  isolation.
- **Hypothesis (NOT established):** that intra-subprocess thread interleaving is
  the mechanism for either class; that Class II is a publication-order race;
  that Class I is a data race rather than a latent deterministic overrun whose
  manifestation is layout-dependent. **I have symptom captures and zero seam
  observations.** No part of this mechanism story should be cited as
  attributed; filing 0694 carries the experiments that remain.

## 10. New dispositions (W7, /qa)

### 10.2 FIXME 0787 — dotted-reference over-reach cells: RETIRED

`/review`'s finding was correct and material: of the 13 "fences" claimed as the
over-reach control for the `.` axis, **10 carry no dot at all** and would stay
GREEN under a coarse `name.contains('.')` over-reach. They discriminate a real
and different thing (the reject did not eat legal bare binders); they do not
discriminate the `.` axis. The design's own named hazard — `core.io/pure`, a
qualified reference whose MODULE half is dotted — was unfenced in both tiers.

`/testing` landed all four proposed cells at W7. **Disposition, all four items:**

1. **The matrix records them** — [historical Sprint 115 PLAN rows](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md), five cells: `--run` and REPL faces of the dotted-module-half
   reference, the `export` twin, the alias form, and the degenerate case.
2. **The unit tier is NOT the agreed home for the degenerate case.** `/testing`
   pinned `a.` / `.b` / bare `.` e2e as located reader errors, and that is the
   right call — it is a Principle-16 twin of bare `/`, and bare `/` is pinned
   e2e. Keep both tiers.
3. **The REPL face earns its place** by asserting the *rendered* type keeps the
   whole dotted home (`:user.util/Wid`), so a truncating splitter fails on
   display as well as on resolution. Two independent observations of one fault
   is what the reference column was missing.
4. **The missing mutation proof is noted, not waived.** `/testing` could not run
   one (it requires editing `crates/cranelisp-frontend/`, outside its boundary).
   The cells are structural over-reach controls by construction, but per §9.5's
   bar that is *argument*, not *demonstration*. **`/dev`(frontend) confirms
   fail-on-revert in one line at its next touch of that seam** — carried as a
   rider, not a gate.

**0787 retires.** Its ask is discharged.

**Its undispositioned tail is NOT discharged, and it is a defect** — see §10.3.
`/testing` correctly flagged `(u/helper)` as "outside this FIXME's ask" and
routed it to me rather than silently dropping it. That routing is what caught a
spec violation.
