# S123 second-deferral carry triage

> **Owner:** `qa`. **Reader:** the user, deciding each carry's disposition;
> `sprint`, routing the outcome. **Authority:** [METHOD §2.4](../../sprints/METHOD.md#24-deferral)
> item 5 and [§2.6](../../sprints/METHOD.md#26-escalation) trigger 3.
> **Checkpoint:** HEAD `f747990f`, source unmodified, 2026-11-15.
> **Status:** a decision input for the S123 Phase 2 checkpoint. It decides
> nothing; the user decides every disposition.

The set is the "Excluded and carried to S124" list in
[SPRINT.md](../../sprints/SPRINT.md). The S122 package table is in
[S122 evidence](s122-evidence-delta.md#final-disposition-proposal-2026-09-30).
The [Phase-5 checkpoint carries](s122-evidence-delta.md#phase-5-checkpoint-carries-approved-2026-09-30)
are in the same record.

## Recommendation summary

- **Do not carry; do in S123.** These are cheap, unblocked by any gate, or
  their stated carry reason is now false:
  - FIXME 0915: its falsifier has fired;
  - ACT-1025, ACT-1032 and FIXME 0934's cancellation cell;
  - the misclassified K11 safety tails (0903, 0929, 0761, 0747, 0891, 0931,
    0848 and 0857), which move into the ownership chain already in scope;
  - the missing REDs for confirmed defects (§2.3);
  - the user questions behind K6 C3, ACT-1020, ACT-1048 and ACT-0986 item 1.
- **Third deferral: carrying needs your sign-off.**
  - Every legacy FIXME in the set: 0694, 0747, 0761, 0785, 0811, 0848, 0857,
    0863, 0891, 0900, 0903, 0915, 0929, 0931, 0933 and 0934.
  - ACT-0962.
  - For 0694 Class I, a heap-corruption event, I recommend an explicit
    residual ruling rather than a carry.
- **May carry as a second deferral, with the rationale below.** These must
  ship in S124 or come back for sign-off:
  - the K5 realization;
  - K7 R1 realization and R4;
  - K8;
  - ACT-1015, 1016, 1017, 1022, 1033, 1034, 1036, 1038 and 1039;
  - ACT-0955, 0963 and 0971, ACT-1003, ACT-1018, ACT-0960 and audit R10.
  Their REDs and gate packets land in S123 where §2 says so.

## 1. How the counts are established

- A deferral is one sprint close at which the item was in scope or open and
  was carried without delivery. In S121 every legacy FIXME was in scope: its
  [FIXME debt section](../../sprints/archive/sprint-121.md#fixme-debt)
  includes all 84 records, and none is presumed deferred. S122's closure-stream
  table allocated each surviving record exactly once
  ([S122 record](../../sprints/archive/sprint-122.md)). A legacy FIXME carried
  out of both has two prior deferrals, so a carry to S124 is its third.
- All 16 legacy FIXMEs in this set appear in both allocations. 0694 also
  appears in every archive from S114 to S122.
- The S122 table records "unknown" for several of these. The user approved
  that carry with "no count is inferred". This triage reconstructs counts from
  the archives as evidence for the S124 decision. It does not reopen the S122
  approval.
- LLVM is user direction, not a filing, an ignored test or a review finding.
  §2.4.5 does not apply to it.

## 2. Structural causes across the set

Each item keeps deferring for one of six reasons. Most items have more than
one.

### 2.1 The gate packet was never scheduled

The carry reason for these is the inter-crate public-API user gate:

- K5 N1 (`ImportNames`);
- the K11 baseline batch (ACT-0955, ACT-0963 item 2, ACT-0971);
- audit R10;
- ACT-1033.

None is blocked by the gate itself. Each defers because no sprint scheduled an
`arch` presentation. S123 already presents one packet, ACT-1040's option-A
intrinsic. Since the S122 close rule (`a9e40b03`), baselines regenerate once
per phase, so one combined presentation costs little more than the panic packet
alone.

ACT-1033 is not independent of that packet. The `runtime/panic` catalog row
already disagrees with its Rust function, which returns nothing where the
catalog declares a result. Option A adds a panic intrinsic to the same
hand-maintained catalog.

**Routing (`arch`):** present one packet in S123 Phase 3:

- ACT-1040 option A;
- the ACT-1033 catalog-signature agreement, preferably single-sourced from the
  Rust signature;
- `ImportNames` with its persistence impl-identity obligation;
- ACT-0955, ACT-0963 item 2 and ACT-0971;
- R10.

Realization may still carry. The decision should not.

### 2.2 A carry whose first act is a user question that was not asked

- K6 C3: does "contain" extend through a named ADT's fields?
- K6 C4: the naming decision.
- ACT-1020: CLI §0.5.6, §0.5.5 and spec §8.1 disagree, and ACT-1020 records
  that S122 did not put the question.
- ACT-1048: the deletion rule.
- ACT-0986 item 1: narrow the requirement, or build a warning channel.

Each first act needs a few minutes of `spec` framing and a user answer, not a
sprint slot. Carrying without asking is the mechanism of the deferral.

**Routing (`spec`):** frame all five in S123 Phase 3.

### 2.3 Confirmed defects carried without a committed RED

[METHOD §2.2](../../sprints/METHOD.md#22-phase-notes) requires a
failing, un-ignored reproduction first. The root guidance says a reproduced
defect joins the suite permanently. These are observed, and no committed test
cites them:

| Item | Observation | RED owner |
|---|---|---|
| ACT-0997 | `(import [lib [(Box B)]])` rejected at parse, including §8.3.5's self-rename. Source confirms `expect_symbol(item, "import name")` in `crates/cranelisp-frontend/src/module_extract.rs` | `test` |
| ACT-1016 | Face 1: a reload accepts a module that a restart fails, measured with a control. Face 2: the export-cycle diagnostic | `test` |
| ACT-1017 | A dependency's span is rendered in the loader's file, observed in `--run`, `--link` and at REPL exit | `test` |
| ACT-0973 | **Confirmed by this triage** (§5) | `test` |
| ACT-1001 P-3 | `resolve_impl_trait_ref` maps every non-private resolve error, `Ambiguous` included, to `unknown trait` (`crates/cranelisp-typecheck/src/traits/impl_check.rs`) | `test` |

Without a RED the suite shows nothing, so each carry costs the coordinator
nothing and the item drifts. These REDs are cheap, need no gate and should land
in S123 whatever the fix disposition.

### 2.4 Parked in a deferred vessel, and misclassified there

K11 puts twelve legacy tails into ACT-0962. ACT-0962 has been the roadmap's
"next increment" since S122 and is itself carried again. §2.4.4 rules that
"scheduled elsewhere in the roadmap" is not a deferral reason.

K11 classes these tails as assurance maintenance with "no compiler acceptance
authority". Source and the backend audit contradict that for several of them:

| Tail | What it actually is | Where it belongs |
|---|---|---|
| 0903 | The non-concrete RC licence. `emit_heap_binding_decs`'s shallow-dec arm and `Err ⇒ Mixed` are still in source. Its faces are scalar-as-pointer (memory-unsafe). The audit's F5 says exposure is unknown | S123 audit R8, already in scope: the §7.3 census |
| 0929 | Fabricated concreteness in the release path. `unwrap_or(ConcreteType::Int)` is live in `crates/cranelisp-backend/src/drop_glue.rs`, and `unwrap_or(Type::Int)` in `compiler/context.rs` | R8 and the §7.4 structural close |
| 0931 | The R17 constructor-partition census | the same census |
| 0891 | Deferred on 0903 since S119 | closes with 0903 |
| 0747 | Collapses the return patches onto the provenance contract, which is the surface of the option-2 decision | the option-2 decision (step 2) |
| 0761 | The RC lane is differential, so it is blind to a leak both lowerings share. The option-2 measurement compares an all-Owned toggle against current emission | must be stated as a limit of step 1's measurement |
| 0848, 0857 | Detection proofs and regrading for the allocator modes and `CRANELISP_RC_DEC_CHECK`. The plant protocol now exists (`crates/cranelisp-intrinsics/src/diagnostics/tests.rs`), so 0848 may be largely stale | before step 4's armed batch relies on those modes |

The [assurance rule](../../CLAUDE.md#assurance--how-we-know-something-holds)
makes this binding: an instrument is unverified until it is proven to detect.
S123 step 4 arms `CRANELISP_RC_DEC_CHECK`; its proof is 0848/0857's subject.

The rest of K11 is maintenance and may follow ACT-0962: 0785 (one solution
guard), 0811 (a process row), 0863 (checkpoint coverage), 0900 (a token
grain, suggestion severity), L-B1, and fmt and clippy.

**Routing (`sprint`, with `design`(backend) and `arch`):** fold 0903, 0929,
0931, 0891 and 0747 into the S123 ownership chain. Make 0761's limit part of
the step 1 framing in the option paper; that is `arch`'s. Put 0848/0857
reconciliation ahead of step 4.

### 2.5 The carry rationale has been falsified

FIXME 0915 is carried because "no public trigger exists". Two S122 filings are
public triggers of exactly its frame:

- ACT-1036: `codegen error at 0..0` on a non-IO `main`.
- ACT-1034: `codegen failed for p/(p/Size.size$p/Opt …)`, with a doubled module
  and a `$`-mangled subject in every mode.

ACT-1036 names itself as 0915's falsifier witness. S123 also includes ACT-1041,
an uncaught panic reported as a codegen error under `--run`. That is the same
presentation seam: the category prefix and the location of a batch diagnostic.

**Routing (`design`(backend) and `design`(int)):** schedule 0915's frame with
ACT-1041, ACT-1036 and ACT-1017's prefix. Together they are one presentation
correction, not four.

### 2.6 Run-dependent residuals without a reproduction

K10 (0694 with ACT-1025) defers because attribution needs load-shaped
experiments and no member reproduces. Carrying is cheap, but one member is a
heap-corruption event: Class I, glibc `smallbin corrupted`, one S115 capture,
600 loaded runs in S122 without reproduction. Re-carrying it without the owed
faces and without a ruling leaves a memory-safety claim graded by inspection,
which the root guidance calls the failure state.

ACT-1025 does not belong in this class. A source read supports its fixture
hypothesis:

- `Scheduler::wait_inmem_complete_blocking` (`src/scheduler.rs`) returns once
  every module has `inmem_done` set.
- `notify_processed_ready` (`src/worker.rs`) deliberately sends the in-memory
  notification before `notify_typecheck_done`.
- So the waiter can return before `user`'s pool is terminal, which the test
  assumes it is.

This supports the hypothesis; it is not an observation at the seam.

## 3. Deferral count and sign-off

"This carry" is the count a carry to S124 would make.

| Item | Filed | Prior deferrals (evidence) | This carry | Sign-off |
|---|---|---|---|---|
| 0694 | S114 | ≥ 2 (S121 and S122 allocations; open in every archive S114–S122) | ≥ 3 | **required** |
| 0747, 0761, 0891 | S115/S118 | ≥ 2 (S122 record; S121 and S122 allocations) | ≥ 3 | **required** |
| 0785, 0811, 0848, 0857, 0863, 0900, 0903, 0915, 0929, 0931, 0933, 0934 | S115–S119 | 2 (S121 and S122 allocations) | 3 | **required** |
| ACT-0962 | S122 | 2 (user deferral at filing; repeat carry at S122 close) | 3 | **required** |
| ACT-0955 | S121 | 1 (S122 scope, carried) | 2 | no |
| ACT-0963 | S122 | 1. The S115 recommendation it restores lapsed unfiled from 2026-07-22 | 2 | no, by record |
| All other actions in the set | S122 | 1 | 2 | no. They ship in S124 or return for sign-off |
| LLVM | — | user direction | — | outside §2.4.5 |

## 4. Per-package triage

Risk is the harm of carrying again, read as harm × likelihood after existing
mitigations. **Rec** is my recommendation; the user decides.

### K5 — names read by their written spelling (ACT-0997, 1001, 0985, 0987, 1003)

- **Why it defers.** One mechanism recurs: a reader resolves the written
  spelling rather than the canonical key. It surfaces as five filings, and the
  only fix that removes the class runs through the `ImportNames` gate (§2.1).
- **Risk.**
  - N1: medium. A spec-admitted form is rejected, and
    `src/syntax/cheatsheet.txt` advertises it. There is a workaround. The
    persistence impl-identity hazard stays latent only while renames are
    rejected, so a careless fix to N1 alone creates data loss.
  - N2: low. The diagnostic drops the alternatives, but the rejection is
    correct.
  - N3: low to medium. ACT-0985's confirmed wrong-reject of a §5.13.1
    forward impl already has a RED.
- **Rec.** Commit the N1 and N2 REDs (§2.3) and the `ImportNames` gate
  decision (§2.1) in S123. The realization may carry. N1 must never be fixed
  without the impl-identity evidence ACT-0997 names.

### K6 — platform admission (ACT-0973, 0979, FIXME 0933, Q12)

- **Why it defers.** It is reached only by platform authors, C3 is gated on an
  unasked question (§2.2), and 0933 has been "small, S120 scope" since S119.
- **New evidence.** ACT-0973 is confirmed in both shapes (§5). A root-level
  non-entry module loads the platform, and a nested one is silently skipped;
  §10.9.1 requires a compile-time error for both.
- **Risk.** Low to medium. These are wrong-accepts at a trust boundary, where
  foreign code's declared signature is trusted. A library that loads a
  platform contradicts the entry-only rule. `require_io_return` checks only
  the return, so a function-typed parameter would pass. No shipped platform
  does either.
- **Rec.** In S123: commit the RED, ask C3, and land 0933's mint gate. 0933
  is a one-function refusal in `src/platform.rs` and sits at its third
  deferral. The C4 collision may carry with C3's answer.

### K7 — runtime concurrency (ACT-0977, 0975, 0981, FIXME 0934)

- **Why it defers.** R1 needs `arch` and `design`(intrinsics), plus a
  completion witness that does not exist. R4 consists of unconfirmed
  reachability leads.
- **Risk.**
  - R1: medium. An approved requirement is unrealized: launched work outlives
    a cancelled launching branch. It has no RED.
  - R4: low.
  - 0934's cancellation face: medium, because it is unobserved, and it is
    cheap to observe.
- **Rec.** In S123, add 0934's losing heap-payload `Pure` cell, with its scalar
  control, to the step 4 armed batch. Commit R1's RED with its winning-branch
  control. R1's realization and R4 may carry.

### K8 — persistence leads (ACT-1005 with P6 and P7, ACT-0994)

- **Why it defers.** The leads are unobserved. P7 is an accepted
  nonconformance with REPL §15.4 rules 2 and 4. The user placed ACT-1005 in
  "S123 or S124".
- **Risk.** Medium for P7 and the macro-order case. The regenerated file is the
  user's source; if its order cannot cold-load, the session restarts locked,
  with recoverable but broken bytes. Low for ACT-0994.
- **Rec.** Carrying to S124 is within the user's window, and ACT-1005 must ship
  there. S123 already reopens the same writer (`src/save.rs`) for ACT-1047, so
  run ACT-1005's falsifier probe while it is resident.

### K9 — diagnostics and discovery (FIXME 0915, ACT-0986)

- **0915: must not carry on its stated rationale** (§2.5). Third deferral.
- **ACT-0986 item 1.** Ask the user (§2.2).
- **Risk.** Low to medium. Users and the training sequence meet these frames
  (ACT-1034, 1036, 1017).

### K10 — run-dependent residuals (FIXME 0694, ACT-1025)

- **Rec.**
  - 0694 Class I: either run the owed faces (scrub, single-threaded at equal
    load, `--link` and REPL) inside the S123 armed batch, or have the user
    rule an explicit residual. A plain carry is not adequate.
  - Class II, Class III, the inverse-polarity member and the reactor panic
    may carry with sign-off. They show no observed harm beyond a run-dependent
    RED.
  - ACT-1025: `dev`(src) makes the test self-attributing in S123 (§2.6); do
    not carry.
- **Risk.** Class I is high harm at low likelihood. The others are low.

### K11 — assurance maintenance and the baseline batch

- **Rec.** Move the safety tails (§2.4) and the gate batch (§2.1) into S123.
  The remaining maintenance tails may carry to ACT-0962 with sign-off, only if
  the user names the sprint that *is* ACT-0962's increment. Otherwise they
  defer by construction.
- **Risk.** High if the safety tails carry, because S123's measurement and the
  decision rest on instruments those tails question. Low for the rest.

### Loose actions

| Item | Why it defers | Risk of a further carry | Rec |
|---|---|---|---|
| ACT-1015 | An unconfirmed lead, though the stdlib's prelude re-exports have this shape | medium if real: fresh load and reload disagree | `test` reduction in S123; the fix may carry |
| ACT-1016 | Confirmed, carried with no RED | medium: a reload accepts what a restart fails, and the REPL lock work in S123 is adjacent | RED in S123 (§2.3); the fix may carry |
| ACT-1017 | Confirmed diagnostic, no RED | low to medium: it misleads users and was reported by `training` and `docs` | RED now; fix with the 0915 frame (§2.5) |
| ACT-1020 | Unasked spec question | low, but the REPL and batch name different files for one target, which is a mode divergence | ask in S123 (§2.2) |
| ACT-1022 | An unreduced +2 lead | low: ordinary leak | commit the `MarginalPair` in the step 4 batch; it costs one cell |
| ACT-1032 | Maintenance, no slot | **medium for S123 specifically.** A cache written in place under `exemplar/` can make the step 1 warm-solve measurement describe an earlier binary | do in S123 before step 1, or at least purge and record the purge in the measurement |
| ACT-1033 | Gate-bound | medium: the false catalog rows sit beside option A's new intrinsic | in the §2.1 packet |
| ACT-1034 | RED committed; split from its sibling | medium: the spec's canonical §7.3.3 example shape is refused in every mode | co-schedule with ACT-1035, which is in S123 on the same parametric-impl machinery |
| ACT-1036 | RED committed | low | with the 0915 frame |
| ACT-1038 | RED committed | low: diagnostic feature; leaks and frames lost under sparks | may carry |
| ACT-1039 | RED committed | low to medium: a `--run` versus REPL and `--link` divergence | may carry; it ships in S124 |
| ACT-1048 | Unasked spec question | low: no bytes are lost today | ask in S123 |
| ACT-1018 | Re-measured after the ownership work, by plan | low: ordinary leak, RED committed | carry as planned. The re-measurement is its S123 act, so it is not a deferral of work |

### Later increments

- **Audit R10.** Gate-bound; in the §2.1 packet.
- **LLVM.** User direction; outside §2.4.5.
- **ACT-0962.** Third deferral. Name its sprint or rule a residual (§2.4).
- **ACT-0960.** It overlaps S123's environment-file rulings: provider and
  model configuration, and precedence. **Routing (`arch`):** decide whether the
  S123 `.env` and user-configuration loader is the channel that ACT-0960's
  project configuration later extends. Otherwise S123 builds an interim second
  configuration channel (Principle 8). ACT-0960 records that the agent spec
  forbids TOML provider configuration, so `spec` reconciliation is needed
  either way. The carry itself is low risk.

## 5. Probe evidence (ACT-0973)

- **Binary.** `target/debug/cranelisp`, sha256 prefix `aa01c46b52d520e0`,
  built 2026-11-15. Source is unmodified against `f747990f`.
- **Setup.** Fresh scratch directories, `--no-cache`,
  `CRANELISP_PLATFORM_PATH=target/debug`, and `(import [primitives [*]])` in
  every module.

| Case | Shape | Exit | §10.9.1 requires |
|---|---|---|---|
| Root-level non-entry | `lib.cl` declares `(platform stdio)`; the entry imports `lib/k` | 7 (accepted; the platform loads) | compile-time error |
| Nested non-entry | `a/b.cl` declares `(platform stdio)`; the entry imports `a.b/j` | 8 (accepted; skipped silently) | compile-time error |
| Control | the entry declares `(platform stdio)` | 9 | accepted |

Source: `handle_platform` (`src/process_form/platform.rs`) returns `Continue`
for a dotted module path, and its rustdoc claims this follows §10.9.1. The
root-level case takes the load path. This is diagnostic evidence. The
permanent RED and its class are `test`'s and `qa`'s at intake.

## 6. Limits

- §1–§5 ran no tests. Statements that a guard is currently GREEN, such as
  the 0916 pair, are taken from the backend audit and not re-observed. §7
  states its own scope and limits.
- 0848's staleness is a source read of the plant protocol's presence, not a
  verification of coverage. Its owners still verify before retiring it.
- The deferral counts in §3 are reconstructed from archive allocation tables.
  Whether "in scope and carried at close" counts as a §2.4.5 deferral is the
  user's reading; this triage applies it uniformly.

## 7. Option-2 discriminator 1: the defect class under the toggle (2026-11-15)

Answers the first discriminator in the
[architecture review](../../sprints/s123-architecture-review.md) §3.3, at the
user's direction ("do the pre-check"). It is a diagnostic observer for the
option-2 reading choice (§3.1). It authorizes no Phase 3 work.

### 7.1 Answer

- **All three defects survive the all-Owned lowering.** With
  `CRANELISP_NO_OWNERSHIP` set, ACT-1030 still stops with `USE-AFTER-FREE`,
  ACT-1026's D1 subjects still leak one block, and ACT-1028's shapes still
  leak one block. Each one-difference control balances in both polarities.
- **Reading R does not remove these faults.** The review's first branch
  holds, with one refinement for each action:
  - **ACT-1030.** The toggle changes `user::go`'s emission, and the fault
    stays. At the CLIF seam, both polarities emit an increment on `q` before
    the parameter flush for a bare `alias` tail argument. Neither emits it
    for the `let`-wrapped argument, whose flush then releases the box the
    next iteration reads. This is ACT-1030's hypothesis, now observed at its
    seam and backed by a balancing control. The rule is shared by both
    polarities, as audit F3 states.
  - **ACT-1026.** The toggle does not touch these programs. The CLIF of `f`
    and `main` is identical in both polarities. The fault is in the
    structural rule both polarities share (`value_provenance` on a
    forwarding join). The toggle cannot reach it.
  - **ACT-1028.** The toggle changes the emission of `main` for every shape,
    and of `f` for the in-place and forwarding shapes. The leak does not
    change. The in-place twin and `d2c_ctl2` allocate 2/1 with analysis on
    and 3/2 with it off. The earlier record of `d2c_ctl2` "balanced with
    analysis on" does not hold at this binary. The candidate control,
    `(defn f [v] (vec-set v 0 5))`, balances in both polarities. That is the
    balanced one-difference control ACT-1028 asked `test` to build. Its
    mechanism is still unattributed.
- **Not established.** Whether reading U or U′ removes these faults was not
  measured. The faults' survival under reading R is necessary for the
  review's "only reading U, or instance repair" claim, but does not prove
  it.

### 7.2 Method and provenance

- **Checkpoint.** HEAD `f747990f`. Source, tests and specs are unmodified.
  The only working-tree changes are coordination documents.
- **Binary.** `target/debug/cranelisp`, sha256 prefix `aa01c46b52d520e0`,
  the same as §5. It was the binary before and after every probe. Both the
  nextest setup build and the probes used it.
- **How the toggle reaches a child.** `cranelisp_types::ownership_analysis_off`
  reads the variable once per process. The marginal harness
  (`tests/helpers/marginal.rs::run_child`) calls `env_clear()`. Only
  `CRANELISP_LIB`, `CRANELISP_PLATFORM_PATH`, the instrument and
  `Child::env` extras get through. The committed cells add only
  `CRANELISP_RC_DEC_CHECK`. Setting the toggle on `cargo nextest` therefore
  never reaches these children. The committed cells measure analysis-on
  only.
- **Analysis-on.** The committed cells ran under `cargo nextest run
  --no-fail-fast` with the two test binaries named.
- **Analysis-off (both polarities, for comparison).** The cells were
  replicated by direct probes. Each child ran in a fresh temporary directory
  with `--run user.cl --no-cache`, stdin null and a cleared environment.
  The environment had `CRANELISP_PLATFORM_PATH` and `CRANELISP_RC_STATS=1`
  (the harness default instrument). `CRANELISP_RC_DEC_CHECK=1` was added
  when armed, and `CRANELISP_NO_OWNERSHIP=1` when off. The programs are the
  committed cells' source text. On the analysis-on polarity, the probes
  reproduce the nextest faces exactly.
- **Evidence that the toggle took effect.** Per-function CLIF
  (`CRANELISP_CODEGEN_DUMP=*`) was compared across two runs for each
  polarity. `user::*` bodies are stable run to run. The
  `user::(primitives/IO.Pure …` closure is not stable, and it is excluded.
  For ACT-1028, the allocation counts also change with polarity.
- **Raw evidence.** `.local/s123-option2-precheck/`: `probe.py`
  (`f1d8fbdf…`), `probe.jsonl` (`99a70b66…`), `nextest-default.log` and the
  `go-1030-*.clif` seam dumps.

### 7.3 Per-cell faces

Here, "armed" means `CRANELISP_RC_DEC_CHECK=1`. "Unarmed" faults are caught
by the always-on debug liveness check in `vec_runtime.rs::assert_live`, so
arming does not change any face. "a/d" is allocations/deallocations. Exit
134 (SIGABRT) is the probe's `-6`. Where the CLIF column says "differs", the
toggle changed at least one `user::` body.

| Cell | Role | On, armed | On, unarmed | Off, armed | Off, unarmed | CLIF on vs off |
|---|---|---|---|---|---|---|
| ACT-1030 L6, `(let [t (match p [b b])] alias)` (committed control half) | subject | abort, `USE-AFTER-FREE` in `vec_push_copy(src)`, buffer freed by `vec_drop`; no counters | same | same | same | differs |
| ACT-1030 shadow half, `(let [t (match p [alias alias])] alias)` (committed subject half) | subject | same abort | same | same | same | differs |
| ACT-1030 owned binder, `(let [t (match p [b b]) u (vec-push [] 0)] alias)` | control (refutation leg) | exit 3, 9/9 | same | same | same | differs |
| ACT-1030 bare `alias` (A-T shape) | control | exit 3, 6/6 | same | same | same | differs |
| ACT-1030 predicted, `(let [t 0] q)` | subject | same abort | same | same | same | differs |
| ACT-1026 D1-M | control | exit 2, 2/2 | same | same | same | identical |
| ACT-1026 D1-M | subject | exit 2, 2/1, residual 1 | same | same | same | identical |
| ACT-1026 D1-L | control | exit 2, 2/2 | same | same | same | identical |
| ACT-1026 D1-L | subject | exit 2, 2/1, residual 1 | same | same | same | identical |
| ACT-1028 `d2c_ctl` | subject | exit 1, 3/2 | same | exit 1, 3/2 | same | differs (`main` only) |
| ACT-1028 in-place twin | subject | exit 1, 2/1 | same | exit 1, 3/2 | same | differs |
| ACT-1028 `d2c_ctl2` | subject | exit 1, 2/1 | same | exit 1, 3/2 | same | differs |
| ACT-1028 candidate, `(defn f [v] (vec-set v 0 5))` | control | exit 1, 2/2 | same | same | same | differs (`main` only) |

- **Committed cells (nextest, analysis on, armed).**
  - `vec_push_match_binder_same_name_shadow::push_under_a_same_name_shadowed_match_binder_balances`
    is RED: the control child aborts with `USE-AFTER-FREE`.
  - `join_forwards_its_binder::match_yielding_its_binder_consumed_in_frame_releases_the_value`
    and `…::let_yielding_its_binder_consumed_in_frame_releases_the_value` are
    RED: control 2/2, subject 2/1.
  - The two D2 cells are GREEN.
- **ACT-1030 CLIF seam.** In `user::go`'s recursive branch, both polarities
  do the following:
  - **Bare sibling.** Push, then `atomic_rmw add` on `q`'s slot, then
    release `p` and `q`, then jump carrying `q`.
  - **L6.** Push, then release `p` and `q` with no increment, then jump
    carrying `q`. The released box is the one the next iteration's push
    copies from.
  - **Inline increments in `go`.** L6 has 1 with analysis on and 0 with it
    off. The bare sibling has 2 and 1. The owned-binder control has 2 and
    1.

### 7.4 Attribution and confidence

- **ACT-1030: high.** The seam observation and the balancing one-difference
  control agree in both polarities. The tail-argument protection does not
  depend on the toggle, and the `let`-wrapped form falls outside it.
- **Refuted if** either of these is observed:
  - a toggle-off build stops emitting the bare sibling's increment while
    the sibling still balances;
  - the owned-binder control stops armed on a rerun at this binary.
- **ACT-1026: high that the toggle cannot reach it.** The CLIF is
  byte-identical in both polarities. The mechanism itself is as already
  recorded in ACT-1026.
- **ACT-1028: the polarity answer is high-confidence.** Both polarities were
  measured. The mechanism stays unknown. This record supplies the balanced
  control, but no seam observation.
- **For the option-2 decision: medium.** The faults are in shared structural
  rules, so reading R leaves them in place. This record does not show that
  reading U or U′ would remove them. That depends on which rules U′ keeps
  (§3.4).

### 7.5 Variants owed to `test` (described, not committed)

- **A committed polarity face.** Give each pair cell a toggle-off twin that
  adds `.env("CRANELISP_NO_OWNERSHIP", "1")` to both children through
  `Child::env`, for example on the `armed` and `shadowed_alias_loop`
  helpers. Only per-child arming reaches the child, so the twin uses no
  suite-level variable. Whether the twins earn their cost is QA's allocation
  after the user's option-2 choice. They are not needed for this answer.
- **ACT-1028.** Use the candidate control in §7.3 as the balanced half of
  the committed cell ACT-1028 asks for.

### 7.6 Limits

- `--run` only. REPL and `--link` faces were not measured.
- The probes replicate the harness environment. They are not the committed
  cells.
- The "unarmed" column keeps `CRANELISP_RC_STATS` set, as the harness does.
  No run was fully uninstrumented.

## 8. Option-2 discriminator 2: in-place against copy updates (2026-11-15)

Answers the second discriminator in the
[architecture review](../../sprints/s123-architecture-review.md) §3.3, at the
user's direction ("run the second pre-check"), for reading U′. It is a
diagnostic observer for `design`(backend)'s U′ rule classification. It
authorizes no Phase 3 work.

### 8.1 Answer

- **The exemplar's warm solve takes the in-place arm zero times.** All 11,593
  dynamic `vec-set`/`vec-push` updates take the copy arm. The counts are the
  same with `CRANELISP_NO_OWNERSHIP` set, and the same serial and lenient.
- **The exemplar's complexity does not rest on in-place updates today.** Its
  cliff is already present under current emission, as the known
  copy-per-guess backlog (0408) records. It cannot show whether U′ needs a
  uniqueness-preserving rule, because it gives the rule nothing to preserve.
- **The in-place arm is load-bearing elsewhere, and only in one shape.** With
  analysis on, a COW op written directly in a self-tail loop updates in place
  every time: 1,000 of 1,000 for `vec-set` and for `vec-push`, with 2
  allocations. The same loop through any one-line wrapper copies every time:
  1,000 of 1,000 and 1,002 allocations. This holds for a same-module wrapper,
  for the stdlib's `collections.vec/conj` and for `assoc`. The exemplar reaches
  every Vec through `assoc`/`conj` (`exemplar/CLAUDE.md` §Conventions), so it
  never has this shape.
- **The toggle already removes in-place updates.** With
  `CRANELISP_NO_OWNERSHIP` set, the direct loop copies 1,000 of 1,000 too.
  The R14 count at `vec_codegen.rs::vec_set_uniqueness` and in
  `compile_vec_push` raises a live `Var` source to rc 2. The review's §3.2
  statement that "the toggle keeps the move and COW exemptions" is false for
  this shape. The toggle number therefore already includes a quadratic cost
  on direct update loops; it is not only a constant factor.
- **For U′.** Whether a uniqueness-preserving rule must be retained depends on
  the direct-loop shape, which the stdlib uses in its own loops (for example
  `vec-map-loop` and `vec-concat-loop`), not on the exemplar. A uniform rule
  that keeps the wrapper result above would make every such loop quadratic.
- **Not established.**
  - Why a wrapper defeats the probe. A caller-side retain held across the call
    is plausible and unmeasured.
  - How many copies the static arms add. See §8.3.

### 8.2 Counts

`hit` and `miss` are `[RC_STATS]` `reuse_hit` and `reuse_miss`; "a/d" is
allocations/deallocations. "On" is current emission and "off" is
`CRANELISP_NO_OWNERSHIP=1`.

| Workload | On: hit / miss | On: a/d | Off: hit / miss | Off: a/d |
|---|---|---|---|---|
| Exemplar `solver.cl`, warm, serial | 0 / 11,593 | 26,457 / 26,406 | 0 / 11,593 | 26,457 / 25,901 |
| Exemplar `solver.cl`, warm, lenient | 0 / 11,593 | 26,457 / 26,406 | 0 / 11,593 | 26,457 / 25,901 |
| D1 direct `vec-set` loop, 1,000 iterations | 1,001 / 0 | 2 / 2 | 1 / 1,000 | 1,002 / 1,002 |
| D4 / L0 direct `vec-push` loop, 1,000 | 1,000 / 0 | 2 / 2 | 0 / 1,000 | 1,002 / 1,002 |
| D2 direct loop, source shared at entry | 1,000 / 1 | 3 / 3 | 1 / 1,000 | 1,002 / 1,002 |
| L1 same-module `myconj` wrapper | 1 / 1,000 | 1,002 / 1,002 | 1 / 1,000 | 1,002 / 1,002 |
| L3 same-module `myassoc` wrapper | 1 / 1,000 | 1,002 / 1,002 | 1 / 1,000 | 1,002 / 1,002 |
| L2 stdlib `conj`, L4 stdlib `assoc` (cold, `--no-cache`) | 1 / 1,000 | 2,199 / 2,153 | same | same |
| L5 `(match b [(Box c) (Box (vec-set c 0 n))])` | 1 / 0 | 2,003 / 2,003 | same | same |

- The single hit in the wrapper rows and in D1 is the initial `vec-push` in
  `main`.
- L2 and L4's residual of 46 is the cold compile term (FIXME 0889), not the
  loop.
- L5 copies 1,000 times by the static arm (2,003 allocations), which the
  instrument does not tally (§8.3).
- **Wall time, warm, stats off, single runs.** On: 0.82 s serial and 0.91 s
  lenient. Off: 0.77 s and 0.86 s. The polarities are the same order of
  magnitude, as identical COW counts predict.
- **Exemplar residue.** On, the warm residual is 51, the
  [ACT-1018](../../sprints/actions/ACT-1018-exemplar-warm-solve-residual-intake.md)
  RED. Off, it is 556. The toggle-off figure is a new diagnostic observation,
  outside this question; nothing is filed for it.

### 8.3 Instrument and its proof

- **Instrument.** `CRANELISP_RC_STATS` emits `runtime/reuse_hit` at the top of
  each in-place arm and `runtime/reuse_miss` on each dynamic copy arm
  (`vec_codegen.rs::emit_vec_set_in_place`, `emit_vec_set_cow_core`,
  `emit_vec_push_cow_core`). Every in-place store and the `vec-push-grow` call
  sit in those two cores, and every static, wrapper and proof-elided lowering
  routes through them. So **`reuse_hit` counts every in-place update exactly**.
- **It distinguishes the arms.** D1 and D4 take the in-place arm 1,000 times
  and the copy arm 0 times. D2 takes the copy arm once and then the in-place
  arm. The toggle-off rows invert D1 and D4. The allocation counts move with
  the copy count in every row.
- **It does not see the static copy arms.** A `vec-set` whose source is read
  later (`VecSetUniqueness::KnownShared`) and a `vec-push` not at last use
  call the copy extern with no tally. D3,
  `(let [w (vec-set v 0 9)] (add-i64 (vec-get v 0) (vec-get w 0)))`, executes
  a copy and reports `reuse_miss=0`; L5 shows the same at scale. **`reuse_miss`
  is therefore a lower bound on copies.**
- **This does not change §8.1.** The in-place count is exact, and it is 0. By
  source census, every COW site the exemplar reaches is the source's last use
  in `collections.vec/conj` or `assoc`. That census is asserted, not measured.
- **The smallest temporary measurement, not built.** Emit
  `runtime/reuse_miss` (or a separate static-copy tally) on the
  `KnownShared` return in `emit_vec_set_cow_core` and on the non-last-use
  branch of `compile_vec_push`. It is a throwaway spike under Principle 08.
  It is needed only if U′'s cost estimate must count static copies.

### 8.4 Method and provenance

- **Checkpoint.** HEAD `f747990f`. Source, tests and specs are unmodified.
- **Binary.** `target/debug/cranelisp`, sha256 prefix `aa01c46b52d520e0`, the
  same as §5 and §7, before and after every run.
- **Exemplar runs.** Each polarity and lenience ran in a fresh temporary
  directory holding a copy of `exemplar/*.cl`, with no `.cranelisp-cache/`
  present (ACT-1032 controlled). The environment was cleared except `PATH`,
  `CRANELISP_LIB`, `CRANELISP_PLATFORM_PATH`, `CRANELISP_NO_LENIENT` for
  serial, and the polarity variable. The sequence was a cold run then a warm
  run, both with `CRANELISP_RC_STATS=1`, as the residue cell does. Wall times
  came from a separate fresh copy with stats off. Its warm stdout matched.
- **Agreement with the committed cell.** A targeted
  `cargo nextest run --test exemplar_ownership_residue_s116` reported the same
  warm line: 26,457/26,406, hit 0, miss 11,593. Cold and warm counts of
  `reuse_*` were equal in every probe.
- **Microprobes.** Each ran in a fresh temporary directory with
  `--run user.cl --no-cache`, stdin null and a cleared environment. Only L2
  and L4 set `CRANELISP_LIB`.
- **Raw evidence.** `.local/s123-option2-precheck/d2/`: `probe2.py`
  (`21f9c561…`), `probe2.jsonl` (`df23ed2f…`), `probe3.py` (`823a8d18…`),
  `probe3.jsonl` (`57f69efe…`), `nextest-residue.log` (`e5fce2c6…`).

### 8.5 Confidence and falsifiers

- **High that the exemplar takes no in-place update.** The count is exact,
  deterministic across cold, warm, serial and lenient runs, and equal to the
  committed cell's.
- **High that wrapping a COW op defeats in-place updates under current
  emission.** One-difference pairs L0/L1 and D1/L3 differ only in the wrapper.
- **Medium for the U′ consequence.** It rests on the stdlib's direct loops
  being the workloads that need the rule. No stdlib-heavy workload was
  measured.
- **Refuted if** any of these is observed:
  - a warm exemplar solve at this binary reports `reuse_hit` above 0;
  - an in-place store or `vec-push-grow` call outside the two cores;
  - L1 reports in-place hits on a rerun.

### 8.6 Limits

- `--run` only. REPL and `--link` were not measured.
- Static copies are not counted (§8.3).
- The wrapper mechanism is unattributed.
