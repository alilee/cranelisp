# Sprint 121 consolidated QA plan — lifecycle and runtime crossing

**Status:** Phase 5. C1's types source/review gate is GREEN and its source
surface is frozen; W1's cross-stream cache evidence tail remains retained-open
as recorded in §3.6. C2's frontend source/review gate is GREEN and its source
may freeze; its process-acceptance tail remains retained-open at §5.2 and
§8.3. The ledger/private-state crate correction is adequate to enter retained
downstream integration under §3.8; its independent BF-2 acceptance condition
remains HOLD until the root test binary compiles and the allocated all-mode
cell executes. The qualified-candidate correction and its typecheck consumer
pair are closed under §3.9, and the fresh typecheck crate census is 863/863;
the all-target check is warning-free and the typecheck source reservation is
released into root integration. BF-2 and QR-3 remain unexecuted until the root
test binary compiles. This document allocates evidence; it changes no test and
records no result that has not been observed. For guarded redefinition and the
REPL-spec split, §10 is the controlling amendment and supersedes every earlier
row that assumes callable cascades, broken symbols, trap stubs, a T1 cure, or a
macro-redefinition receipt delivered to that retired machinery.

**Authority:** `qa`. The governing requirements are `spec/`, `repl/spec.md`
and the adopted architecture. The crate visit records allocate implementation
details; they do not replace acceptance evidence.

## 1. Readiness judgment

**GO to present the Phase-3 → Phase-4 proposal for user approval.** R1–R4 are
all current-sprint prerequisite defects, all four now have a settled mechanism,
owner, minimal reproduction and exit evidence, and none is an accepted
residual or future action:

1. R1 is the ruled three-state `payload_glue` protocol: `0 = Scalar`,
   `1 = Claimed`, otherwise `Owned(glue)`; force and teardown use aligned
   `swap(1, AcqRel)`, exactly one force may observe `0`/glue and access the
   payload, and a loser observing `1` raises the stable runtime error before
   payload access.
2. R2 is fully designed inside C5 I0b as `BridgeJoinState` + `BridgeTicket` +
   worker-owned `WorkerBridgeLease`, with a weak `CancelBridgeGuard` and a
   zero-live-bridge reactor return gate. It preserves the existing owner and
   cancellation policy, so no architecture return is pending.
3. R3 is fully designed as C4 B9: one exhaustive
   `Realization × ParamFlow` discharge plan shared by direct value and
   auto-curry wrappers, with no six-name production policy.
4. R4 is fully designed as the returned-tag-directed C4 B5 stamp plus C7's
   ABI-10 layout, rebuilt fixtures and platform-side pin, with C4's independent
   absolute-offset pin and C5's atomic claim/discharge.

This GO is a readiness judgment, **not permission to start Phase 4**. User
approval is the sole remaining Phase-4 proposal-entry gate. After approval,
G0's format normalization, canonical public-API command/tool pin and the
stray user.cl in the examples directory are the remaining W0 work. The
bounded 0694 D1 experiment is discharged at §3.5, with D2/D3 routed to C6.
The remaining W0 work gates the C1/W1 source reservation; it is not a circular
precondition to asking for Phase-4 approval. Section 8 records the distinct
proposal, C1-reservation and wave-exit gates.

The separately ruled 0859 observer, `/learn`, and the network lesson remain
future-triggered actions. They do not carry any part of R1–R4.

The inherited `5,681 passed / 19 failed / 1 skipped` run is a diagnostic
baseline, not acceptance. Eighteen failures are attributed carried defects;
the stray examples-directory user.cl failure is not. C1 source reservation
requires that W0 attribution, and Sprint-121 exit requires a fresh whole-suite
census with no unexplained RED.

## 2. Evidence tiers and naming

The repository has exactly two test tiers:

- **Acceptance:** process-level tests under `tests/`, invoking REPL, `--run`,
  or `--link` and the produced binary. These are owned by `test` under this QA
  allocation.
- **Unit:** `#[cfg(test)]` modules under the owning crate's `src/`, authored by
  that crate's `dev` stream.

There is no session-building integration tier. In the matrices below,
**integrated evidence** means an acceptance test that crosses settled crate
facades, followed by the whole-workspace gates. Public-API, schema, ABI,
citation, formatting and lint checks are maintenance or boundary checks, not
compiler acceptance substitutes.

Proposed names are stable allocation identities. `test` may improve a name
without weakening its scenario, polarity, citation, or owner.

## 3. Safety findings and minimal discriminating evidence

| ID | Finding | QA disposition | Owning stream | W3 gate |
|---|---|---|---|---|
| R1 | One shared `Pure` node forced on two lanes can transfer one payload twice | **current-sprint prerequisite defect; design closed, not an accepted residual** | C5-intrinsics I0b implements the ruled atomic claim, error ferry, discharge and observer; `test` owns acceptance | one successful ownership transition, loser refuses before field-0 access, one transfer and exact cleanup |
| R2 | A cancelled `Select` loser severs its structured join while a blocking `Par` worker is in flight | **current-sprint prerequisite defect; design closed, not an accepted residual** | C5-intrinsics I0b implements `BridgeJoinState`/ticket/lease; no arch return unless implementation changes the facade or cancellation policy | root teardown follows every worker exit acknowledgement; poll cancellation remains prompt |
| R3 | `emit_d24_adaptation` post-decs Borrowed params after an extern shim already discharged them; six string rows survive | **current-sprint prerequisite defect; design closed, not an accepted residual** | C4 B9 implements the `Realization × ParamFlow` plan; C5-primitives preserves the authoritative declaration facts | all six value wrappers discharge exactly once; user-function Borrowed adaptation remains |
| R4 | Platform-return `Pure` stamp writes beyond the node unless selected by returned tag and backed by the wider ABI | **current-sprint prerequisite defect; design closed, not an accepted residual** | C4 B5 tag stamp + C7 P0/fixtures + C5-intrinsics I0b | tag-directed stamp, ABI 10, independent pins and E1–E3 green |

### 3.1 R1 — shared `Pure` double force

The production mechanism is the exact atomic C5 claim in
`design/intrinsics/s121-c5-intrinsics-visit.md` §4.4 and §9.1. There is no
production "second clear": a force performs one tag-guarded
`AtomicI64::swap(Claimed, AcqRel)` at field 1 before reading field 0. Observing
`Scalar` or `Owned(glue)` is the one successful ownership transition;
observing `Claimed` is a losing refusal and reaches the standard error ferry
without reading, incrementing, decrementing or returning the payload.

The diagnostic observer is retained, with corrected semantics:

- under `CRANELISP_RC_DEC_CHECK`, record successful run-lane ownership
  transitions as `(node pointer, strand id)` for the duration of a run;
- a **second successful ownership transition of the same node pointer** is the
  fault; observing `Claimed` is recorded separately as the expected losing
  classification, not misreported as a second success;
- the positive plant deliberately bypasses or reverts the claim so the same
  heap-payload node can make two successful transitions and the observer must
  fire. This proves the old two-owner mechanism would still be detected;
- equal-but-distinct nodes, one single force and the unarmed/healthy corpus are
  the identity, cardinality and instrumentation controls.

Acceptance allocation:

| Cell | Scenario | Required observation |
|---|---|---|
| `io_pure_witness_s121::shared_pure_forced_on_two_lanes_transfers_once` | the smallest language-level `Par`/`race` shape that shares one constructed heap-payload `Pure` between two force lanes | exactly one successful claim and field-0 read; the other lane returns `Pure node forced more than once` through the standard ferry before payload access; successful-transition observer stays silent; one transfer and exact abort cleanup |
| `io_pure_witness_s121::equal_but_distinct_pure_nodes_are_independent_control` | identical shape with two separately constructed `Pure "same"` nodes | one success per distinct pointer, no duplicate report or force error, exact balance |
| `io_pure_witness_s121::single_lane_heap_pure_control` | one heap-payload `Pure`, one force lane | unchanged value and exact balance |

The source is aliasable, so the shared-pointer acceptance row is required; the
unit plant is not a substitute for it. The tombstone is already the ruled
`Claimed = 1` state inside the ABI-10 word; no second state word, side table or
post-W3 ABI amendment is permitted.

### 3.2 R2 — cancelled loser with an in-flight blocking `Par` worker

Acceptance allocation extends `tests/concurrency_cancellation.rs`:

| Cell | Scenario | Required observation |
|---|---|---|
| `select_loser_joins_inflight_blocking_par_worker_before_teardown` | a deterministic short winner races a loser whose internal `Par` has entered a barrier-controlled blocking worker; cancellation occurs only after the worker reports “entered” | winner returns; no loser result/fault or later-node side effect reaches the winner; lifecycle observes worker exit before root teardown; no access-after-teardown report, panic, abort or hang; heap and resource counts return to baseline |
| `blocking_par_without_select_waits_for_both_workers_control` | the same loser subtree run without cancellation | parent does not finish before barrier release and joins both workers normally |
| `select_poll_only_loser_remains_bounded_control` | existing poll-only cancellation shape | existing prompt cancellation and permit/interest release remain unchanged |

C5-intrinsics unit evidence owns the deterministic seam. One
`BridgeJoinState` is shared by reactor and spawned bridges; the worker holds the
ticket's only strong `WorkerBridgeLease`, while the armed cancellation guard
holds a weak ticket plus the permit. Hold the worker after `Spawned`, select a
sibling winner, and require the ordered trace
`Spawned → CancelRequested → WorkerExited → RootTeardown`. Before barrier
release, the live count is non-zero and root teardown is absent; after release,
the lease decrements and wakes exactly once, the reactor observes zero, and the
root tears down exactly once. The early-lease-release plant must invert the
last two events. Sender loss and worker unwind each release/wake once;
non-cancelled error ferry and poll-only no-lease cancellation are controls.
Wall-clock alone is diagnostic; the barrier, live count and acknowledgement are
the discriminators.

This is not the detached-strand carve-out. The worker belongs to a `Par` inside
a `Select` branch, so cancelling the branch must drop its future and run cleanup
without abandoning an executing child. The required outcome preserves
`spec/10-io.md` §10.12.9 and `spec/12-runtime.md` §12.4.4; it does not invent a
new cancellation policy.

### 3.3 R3 — Decision-24 wrapper double discharge

The closed population is exactly:

`str-len`, `str-eq`, `neq-string`, `starts-with?`, `ends-with?`, `contains?`.

The proposed `primitive_value_d24_s121` acceptance target must enumerate the
six names rather than sample one. Unary rows use `call1`; binary rows use
`call2`. Every row is run
under `--run --no-cache` with `CRANELISP_RC_STATS=1` and
`CRANELISP_RC_DEC_CHECK=1`, twice on fresh string literals. Before the repair,
the value-wrapper path is expected to produce a located stale decrement or an
abort; after it, the result is correct and every argument is discharged once.

| Population/position | Acceptance obligation |
|---|---|
| six rows, ordinary applied call | green control: the extern shim remains the one Decision-24 discharger |
| six rows, function value via `call1`/`call2` | failing-first then green; no wrapper post-dec after the consuming extern shim |
| representative binary row, auto-curry | same exact-once result; proves the second reachable wrapper position |
| `string-identity` via `call1` | `IntoResult` control: returned ownership remains live, and no Borrowed adaptation is involved |
| `vec-len` via the existing two HOF cells before P0 | pre-flip control: green through the extern/GOT path, proving the observer is not generically noisy |

C4 B9 unit evidence belongs beside `fn_as_value::emit_d24_adaptation`: an
`ExternShim` with a consuming `ParamFlow` emits no post-call dec; a
backend-compiled user function whose summary genuinely borrows still emits the
wrapper-owned post-call dec. A kind-blind deletion fails the second row. The
classifier is exhaustive over `Realization` and `ParamFlow`, with no wildcard;
direct value and auto-curry paths consume the same positional plan exactly
once. The repair authority is the keyed declaration/`ParamFlow` plus
`Realization`, never a name list of the six strings.

The temporary `vec-len` leak after B9 removes its accidental wrapper dec is not
an accepted residual. The pre-P0 path control runs at B8, before B9; B9 then
hands directly to primitives P0 with no execution or promotion between them.

### 3.4 R4 — platform-return `Pure` overrun

R4 is fully allocated and remains a prerequisite:

- C4 unit rows load the returned tag. `Effect` stores its fn-name at absolute
  offset 40; `Pure String` stores the canonical `drop<String>` identity at
  offset 32; `Pure Int` stores zero at 32; every other tag and every
  non-platform call emits no store. A control-flow walk proves both stores are
  dominated by their tag branch.
- C4 has a local compile-time `PURE_GLUE_ABS_OFFSET == 32` pin.
- C7 independently has
  `HEAP_HEADER_SIZE + IO_PURE_GLUE_OFFSET == 32`; no shared joint assertion or
  root fallback is allowed. The two owner-local pins are the zero-revisit
  detector.
- C7 moves `ABI_VERSION` 9→10 once. A fixture declaring stale version 9 must
  fail with `AbiVersionMismatch`; changing only that fixture to version 10
  must load.
- Integrated platform-return acceptance is C7 E1–E3: unforced `pure-string`
  tears down with zero leaked strings; forced `pure-string` transfers one live
  string and never double-frees; unforced `pure-int` performs no discharge or
  zero-word call.

No platform-returning `Pure` fixture may execute in an intermediate tree. The
safe state contains all of C4's tag-directed stamp, C7's widened node/ABI and
fixtures, and C5's atomic claim/discharge.

### 3.5 FIXME 0694 — D1 attribution and the remaining C6 observation

**Evidence class: diagnostic observer, not acceptance.** D1 ran against HEAD
`18bca20d07a0b563314ff38f38c93486809bb980` with test binary SHA-256
`c3286dae44220694a56134719b19714b737c5bcef716ac63c89158d5896a64e4`.
The unloaded isolation control was reported GREEN 1/1. With one test binary,
no concurrent peer Cranelisp test process, the test's own sequential child
invocations and twelve non-Cranelisp `yes` workers on thirteen logical CPUs,
200 direct repetitions produced **147 pass / 53 fail**.
Every failure was the REPL face's same compiler diagnostic at
`tests/helpers/e2e.rs:708`: `undefined function: z`; there was no timeout,
spawn failure, heap signal or second failure class. The captured load-run log
was `/tmp/s121-0694-d1.log`, SHA-256
`6450eb8485f6198df6bf38ac7277a9c59a68589225aff9739d0627b883a3032d`.
The unloaded 1/1 control is reported evidence but is not present in that load
capture and is not a stability claim.

D1 establishes only the branch it was designed to discriminate:

- non-Cranelisp host CPU contention is sufficient to expose the exact fault
  while only one Cranelisp subprocess is active;
- other Cranelisp subprocesses, a shared cache/tmpdir/`CRANELISP_LIB`, or a
  repository `user.cl` are therefore **not necessary** to reproduce this
  member. They may amplify a full-suite occurrence, but they are not its
  required cause; and
- the harness panic is the reporter for missing `42`, not the product failure.
  The product observation is the cleanly surfaced codegen refusal for `z`.

D1 does **not** establish that the staging→live gate is the mechanism, that a
data race exists, that C1's carrier is wrong, or that any other 0694 roster
member shares this cause. Its 26.5% manifestation rate describes this one
binary/load arrangement and is neither an acceptance threshold nor a general
probability. The mechanism attribution remains provisional until D2 and D3.

**D2 — ordered seam observation, C6 N1/N5.** The
`CRANELISP_MODULE_TRACE` hook attached to the retired binding-shaped closure
check is not a publication observation and is removed with that false gate;
it cannot support D2. Within the single retained C6 reservation, add
change-set-local diagnostic events under that environment gate at the
already-reserved real seams: N1's
`commit_staging_to_live` records the `zlib/z` entry publication and whole-batch
completion; N5's REPL/eval boundary records the user expression becoming
readable. Against the same host-load shape, run at most 200 repetitions and
stop after capturing one same-signature failure and one passing control.

- Attribution succeeds only if the failing trace orders the user read before
  `zlib/z`/batch publication while the passing trace orders publication before
  the read.
- If the relevant events are absent, or failure and control have the same
  order, D2 falsifies this seam attribution. D1 alone must not authorize a
  publication fix.

**D3 — detection proof, same C6 reservation.** At the same generic publication
gate, arm the already-specified temporary dev-only delay before live
publication. On an otherwise unloaded instrumented binary, the armed leg must
produce the exact `undefined function: z` diagnostic 5/5; the unarmed twin must
return `42` 5/5. Record both binary and capture hashes. A different error, a
non-deterministic armed leg, or an unarmed failure does not demonstrate the
mechanism. Remove the delay hook and the extra experiment-only events before
C6 closes; the existing process-level test remains the standing guard.

D2/D3 are observations over N1/N5's already-designed single publication gate;
they add no facade, cache carrier, lifecycle state or C1 work. FIXME 0694 stays
open until they establish or falsify the mechanism and the corrected C6 build
passes its ordinary and load controls. W0's bounded-D1 prerequisite is
nevertheless discharged because its branch is adjudicated and its consequence
has an owner, a bounded discriminator and an existing source reservation.

### 3.6 C1 source-review and W1 cache-evidence split

**Adjudication: C1 REOPEN SOURCE GO; W1 EVIDENCE TAIL RETAINED-OPEN.** C3's
executing facade falsifier legitimately reopened C1 for the architecture-approved
`TraitMethod` record, checked body funnels and opaque method/shell transactions.
The corrected source passes 219/219 isolated types tests and the focused 9/9
falsifier set; its independent finding-scoped re-review reports PASS with no
surviving finding. Check, all-target clippy with `test-support` and denied
warnings, rustdoc with denied warnings, formatting, canonical public API and
diff are green. The one S121 schema constant remains 25. The types source
surface may be frozen and re-released to C3 without another planned revisit.

C1-owned citations are green. The full live citation ratchet has exactly one
maintenance finding: `design/int/heisenbug-race-closure.md` still points to a
pre-rewrite line anchor beyond the paused C3 `infer.rs` file's current end. That
finding governs C3's document/source currency, not C1 lifecycle correctness or
its instruments. It does not block C1 re-release or
resuming C3; C3's document wash must repair it before C3 or the sprint claims a
green full-citation gate.

Those results are not evidence that a schema-24 sidecar was refused or that a
schema-25 sidecar loaded. The persisted-cache gate is
`cranelisp-backend::cache::serialize`, and C4 B1 owns both its lifecycle
validation arms and the backend wash needed to compile it. The default
solution-test harness currently stops in the intentionally pending primitives,
typecheck and backend consumer washes. That compile refusal is neither a stale
cache negative nor a cold control.

No independent `test` change belongs at the C1 source gate merely to create an
unexecutable RED. Keep the W1 evidence reservation open. At the first C4 B1
backend-compilable tree, execute the smallest direct boundary pair:

- write/load one valid current `SymbolTable` stamped 25, including a lifecycle
  claim, tombstone and unslotted `TraitMethodRecord`, as the control; and
- change only that sidecar's `schema_version` to 24 and require
  `CacheStale::SchemaMismatch { found: 24, expected: 25 }` before lifecycle
  payload access.

That pair proves the exact sidecar fence but is not process-level acceptance.
When the root compiler is executable after the allocated consumer washes, the
independent `test` row must cold-compile a minimal module, prove its untouched
schema-25 sidecar is reusable, patch only the sidecar stamp to 24, and prove a
recompile/restamp to 25. C6's commit-gate-capable tree then runs the separate
concrete→template stale-closure trap row. Generic 0/1 mismatch tests, a
manifest-only mismatch, a textual read of the constant, or successful types
serde are controls; none substitutes for those exact observations.

The C1 module and external-consumer evidence includes these discriminators:

1. The exhaustive `CallableOrigin × Life` plant runs through
   `SymbolTable::validate_lifecycle`, not only the private legality helper, so
   deletion of the load-boundary call makes the matrix fail.
2. Wrong-payload controls cover both halves of the shared classifier: an
   origin-incompatible `TemplateBody` and an origin-incompatible concrete
   `Realization` return `IllegalRealization` through the transition and
   born-settled funnels without mutating the table.
3. `Declared.prior` participates as a claim at the uniqueness/range boundary;
   the matrix also includes a duplicate retired-slot pair. Existing tests cover
   live/live and
   live/tombstone collisions, but not every member of the ruled
   claims-plus-tombstones authority.
4. `MonoDemand.site` is diagnostic-only: varying only the span retains the
   instance key, while varying the storage `FQSymbol.symbol` in the same module
   changes it.
5. In the ruled alias-precedence discriminator, a referring-scope alias and a
   same-spelled real module coexist and the alias target wins. Existing exact,
   scoped-isolation, public/private submodule-walk, depth and undeclared-path
   cells cover the rest of C1's alias allocation; C3 owns the caller and C6
   owns writer/restore acceptance.
6. The I-1 head/terminal discriminator at the types seam makes a private
   prelude alias chaining to a public terminal return the asking module's
   original not-found result, while the otherwise-identical public alias must
   resolve to that terminal. A private terminal and a public re-export do not
   distinguish which visibility the fallback checks.
7. The same-module `BindingBody::Alias` recursion runs through
   `chain_follow_committed_depth`: an acyclic alias whose target is present in
   the caller's union view resolves, while both a self-cycle and a two-entry
   cycle return bounded not-found. The scoped `ModuleAliases` depth test covers
   a separate map and walker and cannot detect removal of this guard.

The review additions are also load-bearing: the external integration target
constructs every public non-exhaustive lifecycle record through its published
constructor/funnel; `install_instance` derives the storage key from
`InstanceLink`; ordinary concrete installation cannot author a backlink; and
both pre-mutation installation and restored-table validation reject a
key/backlink mismatch exactly.

The executing-falsifier reopen adds nine focused controls, each retaining its
named wrong outcome:

1. `trait_method_dedicated_funnel_cannot_be_bypassed_or_removed` rejects both
   generic installation and generic removal while preserving the installed
   method; the existing idempotent/conflict and dispatchable-not-defined twins
   prove the dedicated state remains usable and never enters codegen.
2. `checked_view_identity_refuses_without_mutation` rejects both checked
   settlement and ownership publication when the view names another binding;
   `ownership_publication_keeps_summary_twins_equal` proves the accepted path
   publishes the annotated site facts and both summary carriers together.
3. `rollback_callables_refuses_published_template_hidden_slot` and
   `rollback_callables_refuses_published_removed_binding_slot` plant the two
   ways a newly published slot can disappear from the live binding shape. Both
   refuse before restoring either bindings or tombstones.
4. `staged_impl_shell_refuses_payload_identical_intervening_write` proves the
   shell token observes revision identity rather than payload equality;
   `stage_impl_shell_refuses_wrong_trait_home_without_mutation` and
   `transaction_tokens_refuse_wrong_table_identity` pin canonical placement
   and table-specific token authority before mutation.
5. `external_consumer_can_author_lifecycle_records_and_instance_funnel`
   compiles and executes the checked settlement, callee, ownership,
   `TraitMethod`, callable-retention and shell-token facade from outside the
   crate. In-crate access alone cannot prove this public surface is usable.

C4 still owns mapping an invalid restored lifecycle to `CacheStale`; C3 and C6
retain their producer, caller and writer gates. These are downstream consumer
obligations, not reasons to retain or revisit the settled types source. Sprint
may open C2/C3 while recording the state exactly as **C1 source gate GREEN;
W1 evidence tail RETAINED-OPEN**. W1 is neither failed nor closed, and no full
suite claim is made until the coordinated consumer washes restore an executable
workspace.

FIXME dispositions follow the same boundary. **0637 is not closable at C1**:
its representation is settled, but C4 B1 must validate an out-of-range
`ExternShim.borrowed_sibling` through the one cache-load loop and map it to the
precise `CacheStale` class. **0931 is not closable at C1**: C1 structurally
retires the generic-constructor template slot, while C3 still owes the concrete
instance producer and C4/test still owe the zero-template-frame census and
language acceptance. QA classifies both as downstream evidence-gated; sprint
and the owning records perform their eventual closure.

### 3.7 W3 use-site candidate-selection evidence delta

**Judgment: GO for failing-first evidence and implementation.** The authority is
`spec/03-types.md` §3.5.3, §3.9.3 and §3.10;
`spec/06-pattern-matching.md` §6.2.1, §6.2.2, §6.4.1 and §6.5;
`spec/07-traits.md` §7.4.1; `spec/08-modules.md` §8.6.4–§8.6.5; and the
approved `design/typecheck/use-site-candidate-selection.md`. The correction is
observable and constructable through the existing typecheck fixtures. There is
no authority or testability blocker.

| ID | Evidence class and changed condition | Plausible wrong outcome | Lowest discriminating layer and existing evidence to extend |
|---|---|---|---|
| CS-1 | **Acceptance evidence — syntactic filtering.** A contested spelling retains only declarations legal in its use role; annotation heads select one concrete-type facet before considering traits and report category-local ambiguity | a value, trait or constructor creates a false ambiguity in a type position; several types incorrectly fall through to one trait; a non-constructor reaches pattern typing | `dev` unit/module. Extend `resolve::tests::{test_resolve_product_ctor_as_type,test_resolve_applied_product_ctor_as_type}` and `program::register::tests::single_trait_bound_param_resolves_via_try_type_then_trait` with exact multi-candidate type/type+trait/type+value controls |
| CS-2 | **Acceptance evidence — ordinary HM selection.** A module value and a direct call select exactly one declaration when argument, result, concrete annotation or surrounding expected-type constraints make one compatible; a monomorphic local alias preserves the same source-use constraint | raw cardinality rejects a valid program, declaration order wins, or direct and aliased calls disagree; result-only and expected-type information is ignored | `dev` unit/module at inference. Extend the contested-accessor fixtures in `adt::tests` and the ordinary call/annotation fixtures in `infer::tests`; use one twin per selecting axis and the same fixtures in direct and local-alias form |
| CS-3 | **Acceptance evidence — final outcomes.** Zero compatible survivors is a no-matching-declaration error distinct from an unknown spelling; several survivors at the ordinary-constraint fixed point are ambiguity; a later ordinary constraint may shrink the set to one | zero is mislabeled undefined/ambiguous, several silently select one, or settlement reports ambiguity before already-available constraints propagate | `dev` unit/module in the candidate settlement unit, with unknown-name controls from `resolve::tests::test_resolve_unknown_type` and post-drain controls from `program::finalize::tests::deferred_overload_return_var_in_let_value_resolves_post_drain` |
| CS-4 | **Safety fence — no combination search.** The two-site `f`/`g` shape in the approved design remains ambiguous when only joint guessing discovers `Bool`; adding an independent ordinary `Bool` constraint settles both | global branching accepts the unsupported program, or an over-broad refusal rejects the independently pinned control | `dev` unit/module at the settlement loop. The paired unpinned/pinned fixture is the detection proof; no broader process layer adds discrimination |
| CS-5 | **Safety fence — isolated trials and replay-only commit.** An incompatible candidate cannot change real substitution, fresh-ID progression, active constraints, warnings or final carriers; reversing candidate insertion leaves the same result | a failed trial poisons the next trial, consumes real IDs, changes diagnostics, or makes selection order-dependent | `dev` unit/module with before/after state snapshots and reversed-order twins in the candidate unit; a clean compatible control proves the instrument's negative leg |
| CS-6 | **Acceptance evidence — canonical verdict.** Unique settlement records the terminal identity in `VarRef` and the corresponding `ApplyRef`; no successful body retains a missing candidate-backed verdict or re-derives the written alias | `user/v`, a rename, or the wrong home is recorded instead of `user/Box.v`; the call records `ViaCallee`/dispatch for a different declaration; a checked body reaches the view gate unresolved | `dev` unit/module. Strengthen `program::mono_collect::tests::{resolved_target_bare_ctor_carrier_is_canonical_member_key,resolved_target_bare_accessor_carrier_is_canonical_member_key,resolved_target_renamed_import_carrier_is_source_storage_key}` and the simple/trait call carrier assertions in `program::body::tests::annotation` |
| CS-7 | **Acceptance evidence — callable handoff.** Selecting a trait-method declaration or overload group feeds the existing trait dispatch, clause selection, auto-curry and monomorphisation paths; the selected canonical declaration, not a second bare lookup, determines the final callable | declaration selection is mistaken for impl/variant selection, the wrong trait home dispatches, or candidate calls bypass/duplicate existing overload and auto-curry settlement | `dev` unit/module. Add contested-declaration twins around `traits::dispatch::tests::resolved_target_cross_module_trait_method_records_impl_writer_module` and `program::finalize::tests::overloaded_call_caller_generalizes_over_resolved_return_not_deferred_var`; compare final carriers with canonically qualified controls |
| CS-8 | **Acceptance evidence — constructor settlement.** Scrutinee and provisional binder/body constraints select the data or nullary constructor; `pattern_ctors` stores its canonical identity; exhaustiveness runs against settled parent identities and is unchanged by arm/declaration order | the wrong same-named constructor supplies binder types or tag, arm order chooses it, or pre-settlement exhaustiveness reports a false missing/covered constructor | `dev` unit/module by extending `infer::tests::test_infer_match_data_constructor_pattern` and `adt::tests::{test_exhaustiveness_all_covered,test_exhaustiveness_missing_constructor}` with contested data/nullary, binder-type and reversed-order twins |
| CS-9 | **Acceptance evidence — diagnostics.** Ambiguity lists every and only surviving deduplicated canonical identity; no-match is distinct from an unknown spelling; the location is the written use/pattern and display order has no precedence meaning | an accessor-only reconstruction omits a trait method/constructor, an eliminated candidate is listed, an alternative is duplicated, or iteration order changes the winner or set | `dev` unit/module at the candidate diagnostic builder. Strengthen `adt::tests::cross_cluster_bare_field_ambiguity_message_lists_canonical_alternatives` from accessor-owner reconstruction to mixed canonical survivors and pair it with CS-3's unknown/no-match controls |
| CS-10 | **Acceptance evidence — exposure identity/cardinality.** Export, implicit prelude, Live and Cluster registration each retain exactly the intended two terminal identities, with no duplicate or lost candidate | success-only assertions conceal first-wins, duplicate exposure or an extra candidate in one provenance/mode | `dev` unit/module. Strengthen `form::tests::{def_over_export_candidate_is_allowed,def_over_prelude_fallback_is_allowed,def_over_import_candidate_acceptance_is_mode_uniform}` so export and prelude assert the exact canonical set and each Live/Cluster arm independently asserts cardinality two and the same two identities; retain `checker::tests::prelude_fallback_unions_local_and_prelude_candidates` as the exact prelude control |
| CS-11 | **Safety fence — product/sum boundary.** Product fields retain one canonical accessor plus their bare exposure; sum payload labels retain neither canonical nor bare accessor candidates | selection work revives partial sum accessors or drops a product exposure to avoid a contest | `dev` unit/module. Retain and rerun `adt::tests::{product_field_synthesises_concrete_accessor,test_register_polymorphic_option,accessor_candidate_coexists_with_nonaccessor_binding}`; no new matrix is earned |

W4 defaulting/lifecycle, Packet C `instantiate_demands`, every Rust public-API
line, cache schema, emitted/platform ABI, crate edge and broad integration run
remain outside this delta. A focused diff maintenance check must show that W3
did not move any of them; that check supplies scope currency, not candidate-
selection acceptance evidence, and authorizes no baseline regeneration.

An independent `test` handoff is earned for the process-visible selection and
diagnostic outcome, but no new test file or duplicate matrix is earned. Repair
the superseded expectation in
`tests/spec_field_accessor.rs::bare_alias_ambiguous_canonical_both_work` so a
contested accessor call selected by its argument succeeds while an unconstrained
first-class use remains ambiguous and lists both canonical alternatives. Retain
`tests/spec_field_accessor.rs::cross_module_contested_bare_accessor_selects_by_type_and_no_match_neg`
as the type-directed success and no-match control. Retain and strengthen the
existing all-mode/order witnesses
`tests/spec_06_pattern_matching.rs::{contested_bare_pattern_resolves_against_determined_scrutinee,contested_bare_pattern_indeterminate_scrutinee_poisoned_neg,contested_bare_pattern_differing_layout_twins_both_orders}` and the terminal-identity controls
`tests/spec_08_modules.rs::{glob_and_reexport_of_same_terminal_dedup,distinct_terminal_overlap_collides}`. These process cells prove facade
composition and diagnostics; they do not substitute for CS-5, CS-6 or CS-10's
internal exact-state observations.

W3 implementation completion is evaluable while unrelated W4 failures remain:
every new or changed CS-1–CS-10 cell must fail for its named reason before the
repair and pass afterward; CS-11's retained controls must remain green before
and after; the focused typecheck module set and named process cells must contain
no new or unexplained RED; insertion/order twins must agree; the selected
carrier assertions must name exact canonical identities; and the W3 source/
baseline diff must show no movement on the excluded boundaries. A fresh
finding-scoped `review` then checks the approved correction and this allocation.
The ambient W4 roster remains attributed and cannot close, mask or weaken any
W3 cell.

### 3.8 Checked-body ledger/private-state review correction

**Judgment: GO for one `cranelisp-typecheck` correction basket; the stream
remains HOLD until it passes.** Source inspection confirms the review findings
against `program/mod.rs::BodyLedger`, `program/callees.rs`,
`traits/impl_check.rs::finalize_impl_method_writeback`, and
`program/body.rs::check_defn_body`. The authority is the approved
`design/typecheck/checked-body-publication.md` §§2.3–7 and §§11.2–11.6,
`spec/04-expressions.md`'s lexical-shadow rule, and `spec/05-definitions.md`
§5.1.1. No public API, schema, ABI, crate edge, or new language rule is needed.

| ID | Class and condition | Plausible wrong outcome | Lowest adequate evidence, owner and existing evidence to extend | Limit |
|---|---|---|---|---|
| LC-1 | **Safety fence — structural ledger lifecycle and atomic indexing.** Only registration can create a registered handle, only a successful body check can consume it into a checked handle, and only publication can consume the checked handle. Register/rekey refuses a target or publication collision before changing either index or the body store. | A caller can check or consume the same record twice and discovers the error only at runtime; a distinct target silently replaces `by_publication`, leaving the two indexes to name different owners. | `dev`: replace the runtime-invalid-transition assertions in `program::ledger_tests::ledger_enforces_registered_checked_consumed_lifecycle` with the construction discharge supplied by the private representation; extend `ledger_rejects_duplicate_direct_targets_but_accepts_distinct_clauses` with a distinct-target/same-publication plant and exact pre/post index/store equality. Finding-scoped review verifies that no same-module construction escape remains. | The collision unit cannot prove source-level transition unconstructability; the private type/API shape and review supply that proof. It does not prove publication contents, covered below. |
| LC-2 | **Safety fence — Gap discards and rebuilds attempt-local ledger state.** A failed cluster attempt leaves no checked body or index available to its retry; a fresh attempt reconstructs registrations from the original forms. | A registered/checked record survives the dependency Gap, so retry reports a duplicate, selects the old body, or publishes twice. | `dev`: extend `form::tests::gap_on_missing_module_plain` with a Cluster-mode twin: discard the first staging context after the Gap, add the dependency, retry the same forms with fresh staging, and require one successful callable with the retried body. Reuse the existing plain/alias Gap controls. | This proves the typecheck transaction boundary, not that `int` schedules the dependency and retries; standing `tests/process_form_dispatch.rs` acceptance owns orchestration. |
| BF-1 | **Safety fence — complete body-frame isolation.** Lexical depth and every frame field—rigid/written variables, recursion pair, pending name/pattern candidates, and user-function references—restore together on both inference failure and candidate-settlement failure. | A failed body leaks one field into its sibling even though the currently sampled rigid/scope/reference fields look restored. | `dev`: extend `program::body::tests::body_frame_and_scope_restore_together_on_body_error` to seed and compare every field, retain its inference-error leg, and add one candidate-settlement-error leg through the same helper. | The snapshots prove isolation, not that candidate selection itself chooses the right declaration; CS-1–CS-11 retain that authority. |
| BF-2 | **Acceptance evidence — a parameter shadows the same-named top-level function for both typing and carriers.** `(defn f [f] (f 41))` types `f` in the body as the parameter; genuine unshadowed recursion remains monomorphic recursion. | Carrier construction says local while inference overwrites the parameter with the recursion binding, producing the wrong outer scheme or rejecting a valid higher-order call. | `dev`: strengthen `program::mono_collect::tests::carriers::self_recursion_carveout_skips_param_shadow` to assert the exact function-typed parameter scheme as well as `VarRef::Local`, retaining `self_recursion_carveout_fires_for_genuine_recursion` as control. Independent `test`: extend `tests/carrier_totality.rs` with the same-name `f` higher-order call through all three modes and require the expected value. | The process cell proves observable shadowing and mode composition; it does not expose the internal recursion-frame carrier, which the module pair proves. |
| MR-1 | **Safety fence — one complete resolution handoff.** The final sweep moves one `MethodResolutions` containing `resolved_calls`, `pattern_ctors`, `var_refs`, and `apply_refs`, leaving no active-state residue. | A future split transport silently drops one population while ordinary call-resolution tests stay green. | `dev`: add one `program::finalize` unit that seeds a distinct sentinel in each of the four populations, invokes `sweep_post_pass_outputs`, and asserts all four moved intact and the active record is empty. The whole-struct move is the constructive control. | This proves transfer completeness, not the semantic correctness of each producer; their existing inference, pattern, candidate and view tests remain authoritative. |
| ML-1 | **Safety fence — exact same-module mono-template lookup.** A demand selects its checked body through the exact publication target, never source order, symbol similarity, or AST shape. | Two similar local templates cause specialization of the sibling body while the requested mangled name still looks plausible. | `dev`: extend `program::mono_collect::tests::carriers` with two same-scheme, deliberately similar checked bodies carrying distinct result sentinels; request each target and assert its minted body comes from that exact ledger record. | This does not cover imported committed templates, which continue to use the symbol table and retain their existing cross-module tests. |
| CA-1 | **Safety fence — impl/default/HKT callees publish atomically with the body.** Each shared-tail producer passes its final canonical callees into its single checked settlement; no fallible post-settlement callee write remains. | The callable publishes with empty callees, then a discarded `replace_callees` failure leaves reverse-dependency metadata incomplete. | `dev`: strengthen `program::callees::tests::{callees_records_impl_method_body_reference,callees_records_default_method_body_reference}` and add the HKT sibling so the three producer kinds assert the exact settled callee vector. A focused source check requires the shared writeback to have one settlement call carrying those callees and no subsequent writer. | These cells prove typecheck supplies one payload; C1's existing settlement tests prove the table funnel's own no-mutation-on-error property. |
| CA-2 | **Acceptance evidence — default-body `SigDispatch` keeps the trait-home module.** Harvesting uses the module in which the default body was checked even after the writer module is restored. | A default defined in module `traits` and realized in module `user` records `user/group$…` instead of `traits/group$…`; same-module defaults conceal the error. | `dev`: extend `callees_records_default_method_body_reference` with a trait-home ≠ impl-writer fixture whose default calls a local multi-signature function, then assert the exact trait-home `FQSymbol` in the settled callees. A same-module twin remains the control. | This proves producer identity, not the integration reverse-index consumer; existing session-transaction acceptance retains that responsibility. |
| DG-1 | **Maintenance check — crate guidance matches the landed ownership and strict-view models.** `crates/cranelisp-typecheck/CLAUDE.md` names the ledger/body frame, atomic local settlement and whole resolution handoff instead of removed maps, snapshot harvesting or best-effort publication. Its view guidance and `program/support.rs` describe residual-parameter defaulting, strict retry and located refusal—not the retired lenient fallback. | A later developer recreates parallel maps/post-publication callee writes or restores `lenient_from_expr` because the standing source guidance still calls that fallback deliberate. | `dev` owns the guidance repair. Focused searches for superseded carriers and stale `lenient` claims, plus semantic comparison with the approved design, are sufficient; finding-scoped review confirms current behavior is described. | Search cannot prove prose meaning; review supplies that comparison. This is maintenance evidence, not product acceptance. |

Only BF-2 earns new independent `test` work because it changes a directly
observable language path that the existing internal carrier assertion allowed
to pass incorrectly. All other conditions are private representation,
transaction or metadata seams and stay with `dev`; adding process duplicates
would not discriminate a further plausible outcome.

**Final adequacy, 2026-09-03.** The crate implementation and module evidence
are **GO** and the source reservation is **RELEASED** into downstream/root
integration.
The focused LC-1…DG-1 selector is 12/12. After the qualified-candidate
correction, a fresh full crate run is 863/863, the strict-view selector is 4/4,
and all-target compilation is warning-free. Format/diff checks exit green, and
the initial review plus its finding-scoped re-reviews have no surviving
correction finding. The only typecheck public-baseline line is the separately
approved `instantiate_demands`; this private correction adds none.

DG-1 is **CLOSED**: `program/support.rs` and
`crates/cranelisp-typecheck/CLAUDE.md` now describe residual-parameter
defaulting, strict retry and located refusal instead of an active
`lenient_from_expr` fallback. The finding-scoped re-review reports no surviving
issue. The wording-only repair changed no executable, test or public API.

LC-1 is a construction discharge at the transition seam. The private
`RegisteredBodyHandle<'ledger>` borrows one record's registration and state;
it carries no `BodyId` or caller-supplied ledger, and consuming `finish` is the
only operation that can produce `Checked`. Dropping the handle preserves the
registered record and both indexes for ordinary error rollback. The owning
drain can produce only checked bodies; encountering a remaining registered
record returns an internal compiler error and publishes nothing. That last
refusal checks dynamic attempt completeness at typecheck finalization—it is not
a language-runtime check, generated guard or panic—and is compatible with the
approved rollback rule.

The overall ledger/private-state acceptance condition nevertheless remains
**HOLD**, because `tests/carrier_totality.rs::callable_param_shadows_same_named_top_level_function_all_modes`
is present and discriminating but has not executed: root compilation currently
stops on 114 attributed cross-crate migration errors. Do not record BF-2 green
from its source or from the module twin. The synchronous trigger is the first
root build on which those migration errors are cleared; run
`cargo nextest run --test carrier_totality -E 'test(callable_param_shadows_same_named_top_level_function_all_modes)'`
immediately, requiring the REPL/`--run`/`--link` result 42. A failure reopens
BF-2 in typecheck; a pass closes the remaining ledger/cleanup acceptance hold
without another exploratory review unless the correction changes.

The zero-warning maintenance condition is **CLOSED**:
`cargo check -p cranelisp-typecheck --all-targets` exits cleanly with no
warning. The unconsumed view-refusal aggregate, recorder and getter are absent;
defaulting, strict retry and the located refusal remain unchanged. The distinct
keyed `ownership/fixpoint.rs::residual_param_frames` observation remains. The
updated design and independent review confirm that this removes only dead
instrumentation, not the conservative ownership refusal or its evidence.

The checked-body citation hold is **CLOSED**: the three superseded symbols
`annotate_and_writeback_single_defn`, `write_callees_to_module_entries` and
`harvest_callee_edges` no longer occur in the design record, and the live
citation ratchet reports no finding for them. Remaining baseline citation
findings are outside this source release.

### 3.9 Qualified terminal-candidate resolution correction

**Final judgment: QR-1 and QR-2 are adequate and CLOSED; GO to root
integration. QR-3 remains HOLD and unexecuted until the root binary compiles.**
`spec/08-modules.md` §8.9.2 and
`spec/09-macros.md` §§9.1.3/9.4.4 require compiler-emitted qualified
`macros/SCons`/`macros/SNil` references to work without importing `macros`.
The two former REDs
`builtin_qualified_extern_keeps_abi_name_and_exact_storage_home` and
`builtin_immediate_autocurry_keeps_exact_storage_home` now reach and pass their
intended ABI/storage claims.

Current `cranelisp-types::ResolutionScope` routes qualified lookup through the
named module's candidates, preserving their terminal identities and public
exposure. The landed
[`resolve::tests::qualified_short_exposure_resolves_exact_terminal_without_leaking_or_exposing_private`](../../crates/cranelisp-types/src/resolve/tests.rs)
discriminates the original wrong-reject mechanism, exact identity, no-import
boundary and private exposure. Its landed sibling
`resolve::tests::qualified_short_exposure_preserves_distinct_terminal_ambiguity`
proves that a qualified non-canonical spelling preserves both distinct
terminal identities and returns the §8.6.5 ambiguity. The QR-1 set passes 5/5,
QR-2 passes 2/2, and the full typecheck crate passes 863/863. The
finding-scoped re-review has no surviving finding. This remains a correction
inside the established resolution contract, not a new language or boundary
decision.

| ID | Class and condition | Plausible wrong outcome | Lowest adequate evidence and owner | Limit / falsifier |
|---|---|---|---|---|
| QR-1 | **CLOSED 5/5 — acceptance evidence + safety fence.** Qualified lookup follows the named module's complete candidate set without importing it, preserves visibility and exact terminal identity, and does not choose among distinct terminals. | `macros/SNil` is rejected although `macros/SList.SNil` exists; a repair leaks the short name, exposes a private candidate, returns the alias as storage identity, or silently selects one qualified target-module candidate by iteration order. | `/arch` types-owned module evidence: [`qualified_short_exposure_resolves_exact_terminal_without_leaking_or_exposing_private`](../../crates/cranelisp-types/src/resolve/tests.rs) covers the unique case; sibling `qualified_short_exposure_preserves_distinct_terminal_ambiguity` requires `ResolveError::Ambiguous` containing exactly both canonical `FQSymbol`s. `unqualified_import_chain_returns_terminal_storage_key`, `qualified_resolution_uses_referring_module_alias`, and `qualified_private_terminal_is_reported_private` are the controls. Both QR-1 tests carry the allocated spec and plan trace comments. | The unique test isolates target-table traversal from registration/import faults; the sibling falsifies a collapse or premature choice. These units do not prove typecheck consumption; QR-2 supplies that evidence. |
| QR-2 | **CLOSED 2/2 — acceptance evidence.** Existing cross-crate consumers reach their original assertions. | Resolution is repaired in isolation but typecheck still rejects the qualified constructor, or records the written short alias rather than the canonical storage home. | Unchanged `program::mono_collect::tests::carriers::{builtin_qualified_extern_keeps_abi_name_and_exact_storage_home,builtin_immediate_autocurry_keeps_exact_storage_home}` reach and pass their original ABI/storage assertions. | A future failure before those assertions reopens qualified consumption; a failure at them remains the original typecheck carrier defect and must not be folded into QR-1. |
| QR-3 | **HOLD, unexecuted — independent acceptance.** Import-free qualified constructor use through the executable. | Crate consumers pass but the language path still rejects the spelling or compiler-emitted quasiquote constructors at process level. | `/test`: no new test source. On the first root build that compiles, rerun existing `spec_09_macros::{unquote_splicing_at_top_level_desugars,quote_in_defn_body_desugars}`. The first directly uses `macros/SNil` without importing `macros`; the second exercises the compiler-emitted constructor path under `PrimitivesOnly`. | These process cells cannot identify the resolver seam. They remain unexecuted—not green—while the root build is blocked by the attributed cross-crate migration errors. |

No public signature, generic, bound, variant, field, visibility, re-export,
consumer edge, serde shape, schema or ABI change is allocated, so the
inter-crate public-API user gate is not triggered. `/arch` owns the correction
because this repository assigns `cranelisp-types/` source to that role. The
finding-scoped re-review accepts the current architecture/rustdoc distinction:
“direct” selects the one named module, while the resolver returns that module's
complete candidate set for a non-canonical spelling. The generated public API
is exact, with no correction delta. Any future proposal to change a public
shape or crate edge stops and returns through the user gate. No further
typecheck crate rerun is required unless source changes: the fresh census is
863/863. Root integration is next. On the first root build that compiles, run
BF-2 using §3.8's command and QR-3 using
`cargo nextest run --test spec_09_macros -E 'test(unquote_splicing_at_top_level_desugars) | test(quote_in_defn_body_desugars)'`
synchronously; neither is green before execution. The qualified-resolution
source, zero-warning maintenance condition and overall typecheck source
reservation are released. These retained process conditions govern root
integration and do not by themselves reopen the crate source.

## 4. Exact W3 ordering and the no-repeat ruling

There is **no safe sequence of independently landed, independently runnable
crate visits**. The dependencies form a crossing:

- C4 B5 needs C7 P0 for its platform-return `Pure` store to be in bounds and
  C5 I0a for execution;
- C7's `Pure`-returning fixture needs C4 B5's tag-directed stamp;
- C5 I0b needs both the C4 layout/stamp and C7 ABI 10;
- C5-primitives P0 needs C4 B8 dormant first and must follow C4 B9
  immediately, because B9 removes `vec-len`'s accidental wrapper balance;
- C5's I2/P1/P2 typed-signature cut must be coherent across the runtime pair.

The only zero-repeat schedule is therefore a **braided W3 integration block**.
Each crate has one agent/source reservation which remains held across the named
pause; no crate is released and re-dispatched:

1. **Open the one C5-intrinsics visit and land I0a only.** It is
   behavior-identical and gives C4 an executable `free_io_node`. Keep the
   reservation; do not start I2.
2. **Open the one C7 visit and stage P0's ABI-10 node, constant and independent
   offset pin.** Do not add or execute the `Pure`-returning fixture yet, and do
   not close the visit.
3. **Run the one complete C4 visit, B1→B9.** This includes B5's tag-directed
   platform stamp, B8's dormant `vec-len` arm and, last, R3's B9
   `Realization × ParamFlow` repair. C4 has I0a and the staged in-bounds C7
   layout. At B8, before B9 begins, run the two HOF cells only to record the
   still-live GOT path/no-stale-dec control. Then land B9 and close C4 once;
   do not execute integrated acceptance or promote the transient tree.
4. **Immediately open the one C5-primitives visit and land P0.** This is the
   hard B9→P0 adjacency: the declaration flip removes the inconsistent extern
   row and activates B8's existing inline arm, with no backend edit. Keep the
   primitives reservation for step 7; there is no test execution, suite,
   warm-cache capture or wave promotion between B9 and P0.
5. **Resume and close the same C7 visit:** add the `Pure` fixtures only after
   C4's stamp exists, complete P1–P3 and every fixture rebuild, then close C7.
   The fixtures exist but do not execute before step 6.
6. **Resume the same C5-intrinsics visit for I0b and I1.** I0b lands R1's
   atomic force claim, teardown claim/discharge, error ferry and observer in
   one change-set, together with R2's bridge lease/return gate; I1 lands the
   `Sexp` walk. Only now run R1/R2, R4 E1–E3 and the wider IO/Sexp acceptance
   set. Keep the intrinsics reservation for step 7.
7. **Run the separate typed-funnel subwave, with C4 closed:** land
   C5-intrinsics I2 and then C5-primitives P1/P2 as one coordinated signature
   cut, with no suite or promotion between the two halves; finish I3/P3 and
   close both retained C5 reservations. This satisfies the rule that I2 shares
   no wave with C4 and that P0 precedes P1.
8. Run both crate-unit sets, the complete integrated W3 acceptance set and all
   public-API/emitted-ABI checks before promoting W3.

The C7 pause across steps 2/5, C5-intrinsics pauses across steps 1/6/7 and
C5-primitives pause across steps 4/7 are continuations of one reserved visit,
not new source visits: same owner, same agent, same working tree and source
reservation, no release, no second brief and no re-census. This preserves
widen-before-stamp-execution, stamp-before-fixture-execution, atomic
claim-with-discharge, dormant-before-activation, B9→P0 adjacency and
I2-after-C4 simultaneously. If the workflow cannot retain reservations across
those pauses, **no valid no-repeat order exists and W3 remains blocked**. QA
does not waive either the safety ordering or the one-touch rule.

No warm cache is captured inside W3. The first warm-cache acceptance capture
is after C1 schema 25, C3 CS-6, C4 and the complete W3 block.

## 5. C1–C7 and U8 evidence matrix

### 5.1 C1 — `cranelisp-types`, lifecycle and schema

| Class | Exact evidence | Owner/exit |
|---|---|---|
| unit | exhaustive `Life × CallableOrigin` legality at every funnel and load; `slot ⇒ Concrete/approved foreign state`; duplicate claim and claim+tombstone collision reject; `Declared.prior` and ABI-changing displacement conserve the old slot; retired slots are never reissued; serde/clone-invalid states are rejected at load | C1 `dev`; all plants reject for their intended invariant and valid controls load |
| unit | `MonoDemand.template` and `InstanceLink.template` accept storage `FQSymbol` only; one constructor derives the instance key; scoped alias walk covers exact, longest-prefix, submodule and undeclared cases | C1 `dev` |
| unit | `TraitMethodRecord` is dispatchable but never defined; its dedicated install path cannot be bypassed or generically removed. Checked settlement/ownership reject wrong view identity before mutation. Opaque callable/shell transactions reject published introduced slots, payload-identical intervening writes, wrong trait home and wrong-table tokens, with accepted rollback/commit controls | C1 `dev`; reopen falsifier set 9/9 and focused re-review PASS |
| unit | Packet A1 publication rejects a wrong module, compiled staging owner, duplicate/missing/surplus ABI decision, illegal binding collision and invalid resulting slot map without changing live state; accepted mixed clusters publish deterministically and return one record per staged binding with every displaced owner. Compiled-owner publication returns the submitted owner on refusal and the prior owner on replacement; `mark_broken` retains its slot and returns any displaced body owner | C1 `dev`; focused ownership-conservation and transaction-atomicity set GREEN before the A1 public baseline is presented for user review |
| acceptance | schema-24 sidecar refuses wholesale as stale; schema-25 cold/warm control loads a lifecycle claim, tombstone and unslotted `TraitMethodRecord`; concrete→template redefinition followed by another mint leaves a stale closure trapped rather than retargeted | `test`; after C1, with the warm control recaptured after C3/C4 as required |
| boundary | `CACHE_SCHEMA_VERSION` changes **24→25 exactly once**; the approved reopen stays within that incompatible window. `cranelisp-types/public-api.txt` has the initial C1 regeneration plus one finding-scoped regeneration for `TraitMethodRecord`, opaque transaction tokens and role-specific funnels; the current canonical comparison is exact | `arch`/C1; no C3/C6 regeneration |

### 5.2 C2 — frontend quote/deftype/annotation wash

| Class | Exact evidence | Owner/exit |
|---|---|---|
| unit | `QuoteHead` classifier covers all four variants and `None` with no wildcard; qualified `macros/quote` and wrong arity are negative; unquote/unquote-splicing outside quasiquote still recurse to the existing backstop; quote inside a quasiquote template remains structural, not newly intercepted | frontend `dev` |
| unit | `expand_quasiquotes_is_idempotent_fixpoint` compares the first and second expansion as exact `Sexp`, not only `format_flat()`, and includes `` `(let [x# 1] x#) ``. `Sexp::PartialEq` observes every nested span and generated symbol, while `format_flat()` deliberately erases spans | frontend `dev`; GREEN in the isolated 432/432 frontend run |
| unit | explicit-declaration matrix: bare monomorphic and parenthesized polymorphic positives; missing field type in product and sum arms; undeclared standalone and nested variables; parenthesized empty head; every reject asserts the field/head span and appends no `ParsedEntry` | frontend `dev`; GREEN in the isolated 432/432 frontend run |
| acceptance | `tests/spec_05_definitions.rs` covers §5.2.4 rejection and proves a failed declaration does not make the type, constructor or product accessor usable. Explicit `(deftype (B a) (Mk [:a v]))` coverage preserves construction and matching at concrete instantiations | `test`; retained until the first executable root-compiler gate after C3 and W3's hard B9→P0 adjacency; `[Tested+Neg]` band for spec §5.2.4 |
| acceptance | existing quote/quasiquote, macro and structural-annotation cold/warm paths rerun. FIXME 0785's one missing exact guard feeds `(deftrait Bad (show [x] :String))`, asserts the located `annotation missing expression` reader refusal at the colon, then proves `Bad` was not registered; the existing bare-return and annotated-default-body positives are its controls | `test`; retain with the §5.2.4 process row rather than authoring an unexecutable test |
| boundary | no frontend public API, schema or ABI delta beyond consuming C1's classifier | diff review |

### 5.3 C3 — typecheck lifecycle, mono and carrier producers

| Class | Exact evidence | Owner/exit |
|---|---|---|
| unit | four hand-mint sites are unreachable/deleted; `settle_concrete` refuses residual types; zero-census detection proofs; A-MINT re-synthesises polymorphic product accessors; sum payload labels mint no accessor; one `MonoDemand` constructor covers all three collectors and bare/dotted product-accessor spellings deduplicate | typecheck `dev` |
| unit | 0799 discriminating pair: free-variable curry pinned by a reachable use succeeds, unpinned codegen-reaching value rejects, with observation of the actual `try_auto_curry` arm; drain-table seam cells remain | typecheck `dev` |
| unit | **0869 producer:** record ⟺ shell on commit; rollback leaves neither; same-key re-impl upserts to one; all five record fields equal shell construction values; both `impl$` mints use `trait_impl_key` | typecheck `dev`; gate C6 N3 |
| unit | **0798 caller:** `normalize_self_qualified` passes the referring module and the fixture seeds aliases only through `module_alias_key` | typecheck `dev`; gate C6 N3 |
| acceptance | generic constructor/accessor, HKT impl method, renamed-import generic, F2 dispatch-to-template, residual-parameter defaulting and 0916 wild-write repros cover every producer population; no new corpus refusal after the armed census | `test` plus existing e2e carriers |
| acceptance | 0553 reload seed: captured `MonoDemand` restores the same instance; stale demand produces the specified warning and continues; gap/invariant failure remains an error; synthetic site cannot collide with a span-keyed carrier | `test`, completed through C6 N2 |
| boundary | `cranelisp-typecheck/public-api.txt` has exactly one addition, `instantiate_demands`; C3 makes no types-baseline, schema or ABI change | C3 public-api gate |

### 5.4 C4 — backend realization, release and emitted code

| Class | Exact evidence | Owner/exit |
|---|---|---|
| unit | exhaustive `Realization` lowering, load validation arms, category census with positive plant and concrete negative, no fallback fabrication, `CtorField` concrete-only, result-root/nullary/binding convergence rows | backend `dev` |
| unit | R3's extern-vs-user wrapper polarity; R4's full tag/store/dominance matrix; direct dormant `("vec-len", 1)` arm execution and absence of an element-type lookup; local `PURE_GLUE_ABS_OFFSET == 32` | backend `dev` |
| acceptance | seven 0907 IO release cells; nested unrun `Pure` subtree releases once; Q3/Q1 with Q2/Q4 controls; existing result-root and 0916 repros; R3 six-row matrix | `test` |
| emitted-code | B1/B2/B3 and B8 are byte-identical; B4 permits only the attributed `f4_sudoku` frame; B5 re-baselines only IO-release and blocking platform-call frames; B6 re-baselines only 0906-covered bodies; B9 removes the redundant dec only from affected extern value/auto-curry wrappers, while `Body` and `IntoResult` frames remain byte-identical. Every other CLIF delta is unexpected | scoped golden diff review |
| boundary | zero backend public API, schema and ABI changes | diff review |

### 5.5 C5-intrinsics — teardown, annotation and typed handles

| Class | Exact evidence | Owner/exit |
|---|---|---|
| unit | closed IO and Sexp tag enums with no catch-all; `SexpAnnotated` tag 7 discharges both fields; `Pure` field 1 is the aligned atomic word at absolute 32; force and structural teardown both `swap(Claimed, AcqRel)` before payload access; only teardown observing glue calls it with field 0; `SpineTransferred` accepts only `Claimed`; all three publication edges are pinned | intrinsics `dev` |
| unit | catalog is exactly 38 with `runtime/free_io_node` arity 1/no return and excludes `vec-len`; handle drop-bomb positive/clean/unwind triplet; R1 second-successful-transition plant plus equal-distinct/single/unarmed controls; R2 `BridgeJoinState` lifecycle, early-lease-release plant, normal, sender-loss, unwind and poll-only controls | intrinsics `dev` |
| acceptance | nested unrun `Pure`, forced heap `Pure`, scalar `Pure`, annotated macro/Sexp ownership, R1 and R2 cells | `test`; W3 integrated |
| boundary | emitted-call ABI adds only `runtime/free_io_node`; Rust public baseline adds the `handle` module and exactly nine changed public `consume_*`/`dec_shallow_io` signatures (the tenth funnel signature is private); no schema/ABI-version edit | intrinsics public-api/catalog review |

### 5.6 C5-primitives — realization and shim facts

| Class | Exact evidence | Owner/exit |
|---|---|---|
| unit | declaration → `ParamFlow` → handle-kind derivation over every extern row; six string rows derive owned handles despite analysis `Mode::Borrowed`; compile-fail contradiction cases; `vec-len` is Inline, slot-less, and has no extern shim/export; uniform-body-template roster is a lifecycle projection and `vec-len` is absent | primitives `dev` |
| acceptance | existing `vec_len_as_value_two_instantiations_of_one_hof_control` and `vec_len_as_value_through_hof_returns_length_control` record the GOT path at C4 B8 **before B9**, then run after P0 through the inline arm with exact balance; applied behavior unchanged; R3 matrix green | `test`; path observation is required, not result alone; nothing runs in the B9→P0 interval |
| boundary | `cranelisp-primitives/public-api.txt` removes exactly `pub mod cranelisp_primitives::vec`; emitted ABI removes only the `vec-len` export/GOT slot; no schema or ABI-version edit | primitives public-api/symbol review |

### 5.7 C6 — binary/executable bundle

| Class | Exact evidence | Owner/exit |
|---|---|---|
| unit | both restore seams call C1 validation; commit freeze moves to tombstones; manifest slot `i` equals descriptor `i`; residual platform signature refuses at its located descriptor; 0553 outcomes and synthetic sites | int `dev` |
| diagnostic | **0694 D2/D3:** change-set-local ordered publication/read events discriminate failure from pass at N1/N5; the generic delay plant reproduces the exact `undefined function: z` face 5/5 while its unarmed twin returns `42` 5/5; all temporary experiment code is absent at C6 exit | `qa` directs and adjudicates; C6 `dev` provides the reserved seams; diagnostic evidence cannot replace the existing acceptance row |
| acceptance | **Docstring facade consumer:** `src/agent/pull.rs::apply_docstring_edit` uses C1's reviewed `set_plain_callable_docstring` funnel and preserves the established success/not-found/non-function messages before regeneration. Existing all-features unit cells `set_doc_userfn_records_docstring`, `set_doc_missing_symbol_reports_not_found_no_false_success` and `set_doc_non_userfn_refused_not_recorded` are the discriminating consumer set; the existing restart and honest-failure agent tests retain process coverage | C6/root integration; no new or duplicate test. C1's focused lifecycle/payload/refusal 3/3 proves the funnel itself, while these existing consumers prove error mapping and regeneration orchestration |
| acceptance | **0798:** alias matrix both polarities; two modules each alias `u` to different targets and cannot see the other's mapping; undeclared `u/name` remains a located module-not-found; submodule alias parity fresh and warm | `test`; both writer paths and both consumer paths exercised |
| acceptance | **0869:** fresh and warm sibling-written impl dispatch; restore outcomes `Enrolled`, `AlreadyEnrolled`, and divergence-as-hard-error; both cache entry points; no pre-CS-6 cache reused | `test`; existing `cache_restores_sibling_written_trait_impls_for_dispatch` is the core carrier |
| acceptance | 0868 child matrix; 0553 reload; 0889 macro ownership exact zero; `/mem` reports `deallocs +2, live +0`; prepared-turn failure matrix; colour-on sole-element annotation plus existing colour-off bytes | `test` |
| boundary | zero public API, schema, ABI and exe-bundle delta; no private alias mint survives; no source-form reload replay survives | diff/search gates |

### 5.8 C7 — platform ABI, facade and fixtures

| Class | Exact evidence | Owner/exit |
|---|---|---|
| unit | ABI constant 10; `CLIO::pure` three-word allocation with zero sentinel; independent offset pin; schema type-key success and unknown-type vs unknown-field negatives; marker/manifest/current-header rows | platform `dev` |
| acceptance | stale-v9 refusal plus version-10 load control; R4 E1–E3; existing platform run/link/poll/resource fixtures rebuilt and green | `test`; integrated W3 exit |
| boundary | platform public baseline adds exactly `schema_declares_type` and `IO_PURE_GLUE_OFFSET`; `declare_platform!` gains the optional `adts:` external-author arm; ABI changes 9→10 exactly once | C7 boundary review |
| exclusion | 0463 adds no platform capability and no acceptance row this sprint; its future trigger is a separately scheduled reusable network platform or deterministic server lesson | accepted future action, not an R1–R4 residual |

### 5.9 U8 — user surfaces and whole-system closure

| Class | Exact evidence | Owner/exit |
|---|---|---|
| acceptance | run every spec/repl band touched above; stdlib and examples; all exemplars, with C7 owning only `exemplar/platforms/web/`; docs and training commands execute against the settled binary; cold/run/link/REPL parity where the behavior has all three modes | `test`, `docs`, `training`, examples owners |
| traceability | spec §5.2.4 names the new positive and negative cells; stale `[S115]` cleared rows are re-judged; no dead test names; malformed/missing spec links are repaired by their document owners rather than baselined | QA close gate |
| exclusion | no test, code, docs or training material claims `/learn`; zero normative `/learn` text remains in `spec/` and `repl/spec.md`. ACT-0951 is the only future trigger | U8 search gate |
| integrated | fresh full nextest census with no unexplained RED; format, check and per-surface clippy green; public API/schema/ABI gates green; examples file-set clean; citation and role-wiring maintenance gates green | W6 close; not replaceable by focused runs |

### 5.10 Accepted future-triggered actions

These decisions do not weaken R1–R4:

| Item | Current disposition | Exact revival trigger |
|---|---|---|
| 0859 `ProjectionOf` production observer | retire unexecuted; the source survey found no production RC distinction after materialisation, so a new observer would create a seam with no consumer | a production lowering or ABI path carries projection provenance past materialisation such that `ProjectionOf` can change emitted ownership behavior; QA then allocates the smallest declaration-only mutation witness before that consumer lands |
| 0052 `/learn` | future action under ACT-0951; excluded from S121 | complete user-ruled feature contract for routing, triggers, state, persistence and user behavior |
| 0463 network lesson | future action with no facade widening | a reusable network platform or deterministic server-driving lesson is independently scheduled |

## 6. Boundary-gate ledger

| Surface | Required delta | Forbidden delta |
|---|---|---|
| cache schema | C1: 24→25 once | any C2–C7 second bump; any compatibility shim for an in-window empty 0869 carrier |
| types public API | C1 lifecycle/carrier changes plus the approved declaration-family aggregation; the latter canonical delta is +177/-85 | an unreviewed extra item or implementation before its exact gate |
| typecheck public API | C3: one `instantiate_demands` addition | any second mono engine or C6 change |
| backend public API | approved declaration-family target input/removals plus `load_cached_object` returning `CallableTarget` keys; canonical delta +3/-47 | any further unreviewed change or exposing private emitted-label grammar |
| intrinsics public API | additive `handle` module + nine changed public `consume_*`/`dec_shallow_io` signatures | publishing `free_io_node` solely for linkage convenience |
| primitives public API | remove one empty `vec` module line | any other removal/addition |
| platform public API | add `schema_declares_type` and `IO_PURE_GLUE_OFFSET`; macro `adts:` arm reviewed separately | treating macro invisibility in the baseline as no external API change |
| emitted ABI | add `runtime/free_io_node`; remove `vec-len` export/GOT slot | any other intrinsic/primitive symbol or arity change |
| platform ABI | 9→10 once | backend-local version gate, v9 mode, footprint absorber, or second bump |

Each Rust baseline uses:

`cargo +nightly public-api -s --omit auto-derived-impls -p <crate>`

with the G0-settled `cargo-public-api >= 0.52`. `cranelisp-test-support` is never
generated. A baseline diff is reviewed before replacement and lands beside its
source change.

## 7. Authoring and execution order

1. After Phase-4 approval, run G0 attribution and maintenance prerequisites as
   W0; do not reserve C1 until its exit gate is green.
2. Failing-first R1/R2/R3 minimal reproductions and their controls. R1's and
   R2's unit plants may land with their observers, but the planned acceptance
   names are reserved before a cure.
3. C1 unit/boundary rows, then source review. Retain W1's unexecuted cache
   evidence exactly as §3.6 allocates: the direct 24/25 sidecar pair at C4 B1,
   and process acceptance plus the stale-closure row when the root compiler
   becomes executable. Continuing the ruled downstream wash does not declare
   that retained evidence green.
4. C2 units and source review; C3 units and failing carriers through CS-6.
   Retain C2's §5.2.4 process matrix and 0785's exact malformed-return guard
   without authoring unexecutable test source. Run them at the first valid root
   compiler after C3 and W3's hard C4 B9→C5-primitives P0 adjacency; a
   frontend-boundary unit is not process acceptance for registration,
   construction, matching or access.
5. The braided W3 block of §4, with no unsafe intermediate cache or fixture
   run.
6. C6 units and acceptance, capturing the first valid warm schema-25 cache
   only after the producer and layout gates.
7. U8 user-facing pass, traceability reconciliation and the full gate.

No test is ignored to advance a wave. A new RED outside the named expected set
stops the affected stream for attribution. An observer counts as evidence only
after its planted positive, clean negative and unarmed/silence legs all pass.

## 8. Entry and exit gates

### 8.1 Phase-3 → Phase-4 proposal gate

**GREEN — GO to present for user approval.** R1's architecture ruling, R2's
C5 design, R3's C4 B9 design, R4's reconciled C4/C7 design and both independent
offset pins are closed. The sprint coordinator has authorized the
retained-reservation braid: the same owner, agent and source reservation pauses
and resumes; it is never released or redispatched. Every proposed test has an
owning tier, authority citation, discriminating polarity and named exit.

The only remaining entry condition is explicit user approval of Phase 4. G0 is
planned Phase-4 work, not a prerequisite to presenting that proposal.

### 8.2 W0 exit / C1 source-reservation gate

C1/W1 remains **closed** after approval until the first W0 block proves all of:

- inherited format drift is normalized before any product-source reservation;
- the single public-API regeneration command and `cargo-public-api` tool floor
  are settled, pinned and used consistently; no baseline is regenerated early;
- the examples-directory user.cl input contamination is identified and
  resolved or given a fresh explicit user ruling, leaving a collision-free
  source baseline.

The 0694 W0 sub-gate is already **GREEN**: §3.5 records D1's attributed outcome
and routes the remaining diagnostic evidence to C6 N1/N5 without reopening C1.

These are the exact C1 reservation prerequisites. A failure here blocks W1,
not the already-approved Phase-4 proposal.

### 8.3 Later wave gates

- **C1 reopen source-review gate — GREEN:** C1 lifecycle/alias/schema
  implementation, §3.6's original discriminators and nine executing-falsifier
  controls are green at 219/219 isolated plus focused 9/9; the independent
  finding-scoped re-review is PASS; schema remains 25 exactly once; and the
  approved second baseline generation compares exactly under the canonical
  command. C1-owned citations are green. The one full-corpus citation finding
  belongs to the paused C3 `infer.rs`/int-doc wash and does not block C1.
  Freeze/re-release C1 and resume C3 with no further planned C1 revisit.
- **W1 retained evidence exit — OPEN:** C1 source review is green. This tail
  closes only when C4 B1's direct current-25 load/stale-24 refusal pair is
  green, the first executable root compiler supplies the process-level
  cold/current-sidecar/stale-24 restamp evidence, and the concrete→template
  stale closure traps through C6's commit gate. Until then W1 is retained/open,
  not failed and not silently promoted.
- **C2 source-review gate — GREEN:** exact `Sexp` equality, including the auto-gensym
  input, closes the idempotence observation gap; the head-mode and quote units
  are green; review has no surviving product-correctness finding; FIXME 0937's
  record closure and the frontend documentation wash are complete; and the
  boundary has no public-API/schema/ABI delta. C2 source may then freeze without
  pretending its process tail ran.
- **W2 source exit / W3 entry:** C2's source-review gate is green; C3 CS-1
  supplies the 0798 referring-module caller and CS-6 supplies the 0869
  transactional carrier producer; C3's public-API and census gates are green.
  No pre-CS-6 warm cache enters W3. C2's process tail is retained-open, not
  failed and not silently promoted.
- **W3 exit:** the §4 braid completed without a released/repeated crate visit;
  B9→P0 had no intervening acceptance or promotion; I0b was not split; R1–R4,
  IO/Sexp, `vec-len` pre/post path and exact-balance rows are green; C4/C7 pins
  each equal absolute 32 independently; ABI is 10 with stale-9 refusal;
  public-API/schema/emitted-ABI deltas match §6; no unsafe intermediate cache
  was captured; and, once the root compiler is valid after P0, C2's retained
  §5.2.4 process matrix, 0785 guard and standing quote/macro/annotation process
  regressions are green with no partial registration.
- **W4 exit:** C6 restores 0798 and 0869 through both cache entry points and
  all N-bundle acceptance/boundary gates are green.
- **U8/W5 exit:** the user-facing conformance, docs/training/example pass is
  green and `/learn` remains excluded exactly as §5.9 states.
- **W6 sprint exit:** a fresh full-suite census has no unexplained RED, every
  carried failure is re-attributed, and formatting, checks, clippy, public API,
  schema, ABI, citation and role-wiring gates are green.

## 9. Macro-checkpoint amendment — compact evidence delta

### 9.1 Readiness

**HOLD at the macro-checkpoint correction gate.** `spec/09-macros.md` §9.12.1 distinguishes the
two publication domains: dependency modules publish independently, while the
defining module atomically publishes the macro parent, active clauses and its
own generated realizations. The approved architecture and int design are
therefore observable without choosing between conflicting requirements. No
new runtime observer or public test seam is required. Independent review found
that macro-redefinition receipts are dropped at the checkpoint boundary, the
macro-specific MC-1/2/3/4/7/8/10/11/12 unit fences have not been supplied,
bootstrap lifecycle refusal still panics, and a retired binding-shaped
terminal-closure check is a hard-coded false green. The correction delta below
must close before this amendment can return to review or claim candidate
closure.

The evidence below extends the existing C1, C3, C4 and C6 reservations. It is
not a new cross-crate wave: types first proves the approved absent-key
`ChangeAbi` semantics, then typecheck/backend supply their private guards, and
the root int visit composes those settled parts once.

### 9.2 Lowest discriminating evidence

| ID | Condition and plausible wrong outcome | Lowest evidence and owner | Existing evidence to extend; limit |
|---|---|---|---|
| MC-1 | A macro is invisible until its parent, every active clause, defining-module generated realizations and owners are complete. A clause/type/codegen/publication failure must leave none of that attempt live and must preserve the complete prior generation. | **Safety fence, root unit — `dev`(int).** Drive the one checkpoint helper through typecheck failure, second-clause failure, generated-realization failure, backend failure and publication refusal; compare parent, clauses, owner identities, GOT cells, tombstones, candidates, revisions, introspection and typecheck products before/after. The successful control exposes all members together. | Replace the `PreparedMacroTurn` tests in `src/process_form/macro_clause.rs`; strengthen `tests/spec_09_macros.rs::repl_error_recovery_no_partial_macro` so it proves the failed name is unavailable and a clean same-name definition can subsequently publish. The process test cannot observe internal realizations or owners; the unit does. |
| MC-2 | A successful checkpoint survives a later expansion, non-macro typecheck or backend failure. Rolling it back, or publishing an ordinary prefix beside it, is wrong. | **Acceptance, process — `test`; safety fence, root unit — `dev`(int).** Add direct-first-definition and expansion-produced variants in one REPL process, then invoke the committed macro after the later error and prove ordinary members of the failed HM cluster are absent. Root units inject the backend failure, which is not cheaply expressible as stable language syntax. | Extend `macro_persists_across_evals`, the failed-codegen family in `tests/spec_11_stdlib.rs`, and the generated-macro shape in `tests/s76_macro_availability.rs::macro_generates_defmacro_available_to_later_use`; do not duplicate their successful controls. |
| MC-3 | Authored/generated, first-definition/redefinition, and REPL/batch/reload routes must use the same checkpoint rule. A successful redefinition remains current even if the later §18 cure fails; batch failure state is not externally inspectable after process exit. | **Safety fence, root route-matrix unit — `dev`(int).** Feed the shared checkpoint operation with direct/generated provenance and first/replace/reload cadence; after an injected later failure assert the selected generation. **Acceptance, process — `test`:** keep the existing all-mode successful macro control and extend the reload error-block/report control; do not claim it proves hidden post-failure state. | `tests/build_confidence.rs::mode_equiv_macro_user_defined` remains the REPL/`--run`/`--link` success control. Exact checkpoint retention for batch and §18-cure failure is unit authority because the public process either exits or is deliberately error-blocked by §14.4–§14.5. |
| MC-4 | A 3→1 replacement retires exactly prior indices 1 and 2 for the same parent in the parent/active-clause transaction; 1→3 allocates fresh slots. Prefix scans, ordinary/foreign removal, pointer clearing, slot reuse or partial retirement are wrong. | **Safety fence, types unit + root unit — `dev`.** Extend `crates/cranelisp-types/src/module/tests.rs` with mixed replacement/removal success, `prior_slot: Some`/`published_slot: None`, frozen `AbiChanging` tombstones, displaced-owner return, one revision increment, 3→1→3 fresh slots, and late-refusal byte-for-byte equality. Root tests derive the exact `M..N` keys from parent metadata and reject missing, `Plain`, foreign-group, non-private and slotless rows. | Types proves the generic transaction, not macro authorization. Root proves only same-parent `MacroClause` rows can request absence. No process test can discriminate slot identity or owner retention. |
| MC-5 | Omission alone never deletes; absent-key `PreserveAbi`, missing/non-callable/slotless/candidate-only targets, duplicate decisions and locally dangling candidates refuse the complete plan and return every submitted owner. | **Safety fence, types unit — `dev`(types).** Extend `staged_publication_refusals_are_atomic_and_owner_safe`, `compiled_staged_publication_returns_all_owners_after_late_multi_row_refusal` and the compiled-refusal matrix with exact pre/post state and drop-spy controls. | Existing owner-key exactness remains the control. This layer cannot prove int chooses only macro clauses; MC-4 does. |
| MC-6 | Forward macro use remains an ordinary unresolved reference, while non-macro forms on both sides of a checkpoint remain one mutually recursive, all-or-nothing HM cluster. | **Acceptance, existing process tests — `test`.** Re-run the S76 direct and REPL-`begin` forward negatives. Extend the existing `begin` mutual-forward-reference/failed-partial-publication family with a macro checkpoint between two non-macro definitions. | `tests/s76_macro_availability.rs::{macro_used_before_defmacro_is_unresolved_neg,repl_begin_cluster_forward_macro_use_is_unresolved_neg}` already discriminate no hoisting. `macro_persists_across_evals` alone does not prove HM cluster scope. |
| MC-7 | A dependency published while a macro waits survives later parent failure; dependency rows must not be copied into the defining-module staging table. | **Safety fence, root scheduler/checkpoint unit — `dev`(int).** Force one legal dependency gap, complete that module, fail the parent, then assert the dependency's live generation and an unchanged target module. | Keep `macro_clause_calls_imported_helper_at_expansion_works` and its ill-typed twin as process controls. Their success/failure cannot distinguish retained publication from a later recompile. |
| MC-8 | A gap before/during the checkpoint retries that macro; a gap after a committed direct or generated macro resumes only the unprocessed suffix. Replaying the origin, losing the earlier ordinary prefix, or accepting a real second same-name form is wrong. | **Safety fence, deterministic root continuation unit — `dev`(int); acceptance, one process composition — `test`.** Inject gaps on both sides and count checkpoint/codegen attempts plus the final ordinary cluster members. The process case combines an expansion-produced macro, lazy dependency and one later use; it requires one ordered definition result with no duplicate row or diagnostic. | **IMPLEMENTED/GREEN:** `generated_macro_checkpoint_is_not_replayed_after_later_dependency_gap_neg` now passes after literal `begin` members were processed in source order and continuation omitted committed macros (full S76 13/13; compact macro/search set 15/15). The original falsifier was lost begin-local checkpoint availability. This closes the process-composition row only: absence of a duplicate row or diagnostic alone cannot replace the deterministic attempt/cursor unit, and the full MC-1–MC-13 exit remains open. |
| MC-9 | A macro parent and `CallableOrigin::MacroClause` are not language values. Bare, self-qualified, child/imported and fully-qualified value/call resolution must reject them; only macro-head recognition/execution may use them. | **Safety fence, typecheck unit + backend unit — `dev`.** Seed arbitrary clause keys (the spelling is implementation-defined) and exercise each resolution route through the common language-value projection. Add a backend checked-carrier plant proving a hand-built ordinary reference to a clause refuses before emission. **Acceptance, process — `test`:** one-argument macro parent in value position rejects while invocation and introspection remain controls. | Do not write an e2e test against `__macro_*` spelling. Unit construction is the legitimate non-vacuous caller. Existing `/list`/`/info` macro tests remain presentation controls, not value-admission evidence. |
| MC-10 | A macro reader observes old parent+clause+pointer+owner or new parent+clause+pointer+owner, never a mixed generation, and its cloned owner outlives guard release through invocation. | **Safety fence, deterministic root concurrency unit — `dev`(int).** Barrier the reader before/after the single read-guard snapshot while a writer replaces the generation; use distinct metadata/pointer/owner sentinels and a drop spy. Finding-scoped review verifies the production reader performs no split lookup. | An e2e stress loop would be slower and could pass without exercising the forbidden interleaving; none is allocated. |
| MC-11 | Cache restore accepts exactly the active-parent↔private same-group `MacroClause` bijection and rejects missing, duplicate-index, surplus, wrong-group, wrong-visibility, wrong-ABI, non-concrete and legacy-`Plain` clause rows as stale. | **Safety fence, types/cache unit — `dev`(types/backend/int as the owning load seam).** Plant each invalid relation and one valid multi-clause control; prove the ordinary stale/regenerate route is taken. **Acceptance, existing process test — `test`:** cold/warm macro behavior remains identical. | Extend the lifecycle/cache validation tests and `tests/cache.rs::cache_load_imports_macros_traits_installed`; process equality cannot prove malformed sidecars were refused for the intended reason. |
| MC-12 | No GOT update becomes reachable before whole-batch finalization; on compiled-publication refusal every touched cell is restored while all candidate owners remain live, then owners are returned/dropped exactly once. | **Safety fence, root unit — `dev`(int), plus existing types drop-spy units.** Inject a late batch/refusal after at least one touched cell and assert event order `write → refusal → restore-all → owner-release`, old pointer bytes, no new reachable binding, and exact drop counts. | Replaces the old reserved-cell cleanup test. Types proves owner conservation but cannot observe backend GOT compensation. |
| MC-13 | The amendment adds no Rust item, cache/schema/backend/platform interface, temporary macro world, macro-specific drop-glue publisher, or fresh-`TraitImpl` behavior. | **Maintenance/process evidence.** Compare generated `cranelisp-types`, `cranelisp-typecheck` and `cranelisp-backend` API output with their checked-in baselines; require zero diff. Search production `src/` for `PreparedMacroTurn|TurnCheckWorld|TurnDelta` and candidate/reserved unpublished invocation remnants. Diff review rejects any trait-impl registration/restoration edit, and the existing typecheck trait-impl units plus `cache_restores_sibling_written_trait_impls_for_dispatch` rerun. | API and searches prove surface/absence only. Existing behavior tests, not grep, protect TraitImpl semantics. No schema bump, platform fixture, ABI or new public-API user gate is expected. |

The definition-result correction has two separately attributable conditions:

| ID | Condition and plausible wrong outcome | Evidence and status |
|---|---|---|
| DR-1 | One submitted form that publishes multiple definitions reports every published canonical identity once and in emitted order. Selecting a single “subject”, scanning ambient table state, inventing a row at publication, or replaying an already-published macro after a dependency gap is wrong. | **GREEN:** `session_v4::types::tests::{turn_definitions_preserve_emitted_order_across_retry, turn_definitions_refuse_unrecorded_publication}`, `tests/spec_09_macros.rs::macro_emitted_definition_batch_lists_all_definitions_in_order`, and `tests/spec_11_stdlib.rs::def_definition_echo_lists_every_emitted_definition_in_order`. |
| DR-2 | A zero-argument macro binding is presented as `:(Fn [] macros/Sexp) … ; defmacro` in its definition result, `/info`, and `/sig`. This is its compile-time transformation signature. Its expansion result type is observable only when the bare macro is evaluated; projecting that type onto the macro binding is wrong. Destructuring and variadic clauses retain `; pattern:` metadata where `Fn` cannot express their call shape. | **GREEN:** `session_v4::types::tests::definition_batch_has_no_singular_type`, `repl::commands::sig_display_helper_tests::{format_macro_display_uses_compile_time_transform_signature,format_macro_display_retains_variadic_pattern}`, `tests/repl_introspection.rs::{defmacro_display_multi_clause,info_multi_clause_macro_shows_clause_count,sig_macro_preserves_bracket_pattern_shape}`, and `tests/spec_11_stdlib.rs::def_info_and_sig_describe_macro_while_bare_use_expands_value`. REPL §§1.1, 1.3, 4.1.6 and 11.2–11.4 carry the user-approved 2026-09-05 one-line transformation-signature rule. |

### 9.2a Independent-review correction delta

This is the complete added evidence delta. Existing generic prepared-publication
units remain controls; they do not acquire macro authority merely because the
checkpoint calls the same helper.

**Current condition status:** MC-2/MC-3 are RED because their successful macro
redefinition receipt is lost. MC-1/MC-4/MC-7/MC-10/MC-11/MC-12 and the root
half of MC-8 are OPEN for their allocated deterministic fences. MC-8's process
composition is GREEN only. MC-5/MC-6/MC-9 retain their reported green evidence;
MC-13 remains OPEN until the corrected root diff and final generated baselines
are inspected. Bootstrap fallibility and truthful candidate closure are
additional correction gates and do not borrow an MC identifier.

| Correction | Smallest discriminating evidence and reuse | Exit observation |
|---|---|---|
| **Redefinition receipt delivery — MC-2/MC-3.** A successfully published macro redefinition must reach the existing §18 outcome sink exactly once whether later processing returns Done, Gap or Err, and whether the checkpoint is direct, expansion-produced, REPL-eval or reload/recheck driven. | Add one parameterized root unit, `macro_redefinition_receipt_reaches_outcome_sink_once_across_routes_and_terminal_outcomes`, at the source-walk/checkpoint result carrier. Inject only the later terminal result and record the existing `apply_redefinition_outcomes` input; use distinct target/generation sentinels to detect loss, replay and duplication. Retain `redefine::tests::{outcome_clears_broken_covers_new_classified_redefinition_shapes,t1_downgrade_trigger_route_cells}` for sink semantics and the existing macro reload/process cells for public routing; do not repeat the cure matrix. | Every successful checkpoint supplies its one receipt before the turn finishes or suspends; later Gap retry and later Err neither lose nor replay it. Failed checkpoints supply none. |
| **Macro transaction — MC-1.** | Add `macro_checkpoint_failure_preserves_complete_prior_generation`, using real malformed/second-clause failure and one private late-publication refusal injection. Compare the complete parent/clause set, slots, GOT bytes, owner identities, tombstones, revision, typecheck product and introspection with the prior snapshot; the success twin observes the complete new generation. Reuse `worker::tests::{prepared_codegen_failure_strategy_matrix_leaves_live_state_unchanged,prepared_multi_member_codegen_failure_is_all_or_nothing,prepared_publish_installs_entry_drop_glue_and_planned_retention_only}` for generic backend/owner behavior rather than duplicating their matrices. | No failed macro attempt leaks a member or presentation/product residue; successful publication exposes the complete generation. |
| **Route durability — MC-2/MC-3.** | Add one table-driven root unit, `macro_checkpoint_durability_route_matrix`, over direct/generated × first/replacement × eval/recheck. Inject a later ordinary/backend/cure failure after checkpoint success and assert the selected macro generation and receipt cardinality. Existing process tests retain user-visible REPL and all-mode success authority. | The new generation remains current on every route; ordinary failed-cluster members remain absent; batch exit is not misclaimed as hidden-state evidence. |
| **Surplus authorization — MC-4.** | Add `macro_surplus_retirement_authorization_matrix` at `validate_surplus_clauses`: the valid 3→1 control selects exactly indices 1 and 2; missing, `Plain`, foreign-group, public, non-canonical-ABI and slotless twins refuse without a decision. Reuse the completed types absent-key `ChangeAbi` transaction/owner tests for retirement mechanics and 3→1→3 slot freshness. | Only exact private, slotted, same-parent `MacroClause` rows can become absent-key retirement decisions. |
| **Dependency independence — MC-7.** | Add `macro_dependency_publication_survives_parent_failure` at the scheduler/checkpoint seam. Deterministically complete one dependency, inject parent failure, and assert the dependency generation remains live while the target module equals its pre-attempt snapshot. Existing imported-helper process twins remain controls. | Dependency publication survives; no dependency row enters target staging. |
| **Continuation — MC-8.** | Add `macro_checkpoint_continuation_attempt_matrix`. Count checkpoint/codegen presentations for gaps before, during and after direct and generated checkpoints; assert the retained ordinary prefix and terminal suffix exactly. Reuse the green `generated_macro_checkpoint_is_not_replayed_after_later_dependency_gap_neg` as the one process composition. | Before/during retries once after resolution; after-checkpoint resumes without replay; a genuine second source definition still refuses. |
| **Reader generation — MC-10.** | Add `macro_invocation_snapshot_is_one_generation_and_retains_owner` at the private read-snapshot seam. Barrier old/new replacement around the single guard, use distinct parent/clause/pointer/owner sentinels, then drop the table-side owner before invocation and observe the cloned owner still live. | Each read is wholly old or wholly new; no mixed tuple and no owner drop before invocation returns. |
| **Cache relation — MC-11.** | Add `macro_cache_parent_clause_bijection_matrix` at the actual cache validation/load seam: one valid multi-clause control plus missing, duplicate-index, surplus, wrong-group, public, wrong-ABI, non-concrete and legacy-`Plain` variants. Assert the typed stale reason and ordinary regenerate branch. Retain `cache_load_imports_macros_traits_installed` only as cold/warm process control. | Every invalid relation is rejected for the intended relation before use; the valid relation restores all owners. |
| **GOT compensation — MC-12.** | Add `macro_publication_refusal_restores_all_got_cells_before_owner_release` at `compile_and_publish_prepared`'s existing refusal/compensation seam. A test-only ordered event sink records at least two writes, late refusal, every restore, then candidate-owner drops; assert prior bytes and no reachable new binding. Reuse the types drop-spy refusal units for submitted-owner conservation. | Exact order is `write+ → refusal → restore-all → owner-release+`, with old pointers restored and each owner released once. |
| **Fallible bootstrap.** A lifecycle collision or malformed seed must be a located compiler error, never `unwrap`/`unreachable`/panic. | Make the root synthetic-module initialization chain return `Result` and add `bootstrap_lifecycle_conflict_returns_error_without_unwind`: pre-seed the first special-form key with an incompatible binding, call the production mount entry, and assert a located error. Existing successful mount tests are the negative leg. A bounded source check requires no lifecycle-install `unwrap_or_else(unreachable!)` in production `bootstrap.rs`. No bootstrap atomic-rollback condition is added without design authority. | Initialization success is unchanged; a planted lifecycle refusal returns through the caller and the process does not unwind. |
| **Truthful candidate-closure gate.** Candidate exposure, not a parallel binding map, is the governed cross-module carrier. | Retain `worker::tests::{commit_staging_to_live_rejects_out_of_closure_public_write,commit_staging_to_live_permits_declared_public_reexport}` and the existing `check_candidate_closure` polarity/cardinality matrix, renaming stale `check_terminal_closure_*` test names to the real seam. Replace `bootstrap_seeds_pass_the_terminal_closure_gate` with `bootstrap_public_candidate_exposures_are_self_aliases_or_private`, iterating `all_name_candidates` and proving every public seed terminates in its own module. Delete the no-op `check_terminal_closure`/`write_is_closure_valid`, their binding-only test, and stale ONE-gate prose/calls. | All candidate-writing routes call `check_exposed_candidate_closure`; out-of-closure public cross-module exposure fires, declared/self/private controls stay green, and no hard-coded-true shadow gate can satisfy the claim. |

### 9.3 Stale evidence to retire or reinterpret

- `/search` currently excludes macro declarations under `repl/spec.md`
  §17.19.2a. The retired EV-3 macro-row expectation is replaced by
  `search_ignores_macro_declaration_but_keeps_ordinary_definition_neg`; a
  macro result row is not evidence.
  [ACT-0952](../../sprints/actions/ACT-0952-complete-semantic-search-indexing.md)
  remains the future semantic-index action and does not weaken or override the
  current exclusion.

- Every `src/process_form/macro_clause.rs` test whose subject is
  `PreparedMacroTurn`, `TurnCheckWorld`, `TurnDelta`, reserved unpublished GOT
  cells or cross-module rollback is invalidated. Preserve a behavioral claim
  only by moving it to MC-1, MC-7, MC-8 or MC-12. In particular,
  `composed_macro_turn_later_failure_rolls_back_every_product` asserts the
  opposite of §9.12.1 for a successfully published dependency and must not be
  renamed into a false checkpoint test.
- `macro_persists_across_evals` proves only use after an ordinary successful
  definition turn. `repl_error_recovery_no_partial_macro` proves only session
  continuity. Neither supports the new atomicity/durability annotations until
  strengthened as MC-1/MC-2 require.
- `macro_body_calls_helper_function_in_run_mode`,
  `multiple_macros_interleaved_with_defns_compose`, and
  `macro_body_drives_three_level_call_graph` return quoted syntax containing a
  later runtime call; they do **not** call the helper at expansion time and
  remain valid. The unquoted S76 helper negatives are the §9.3.4 rejection
  authority.
- The §5.13, §9.3.4, §9.6, §9.12 and §9.13 bands were re-judged against the
  completed process rows and now cite their current evidence. Claims without
  sufficient current evidence remain explicitly `[Uncovered S121]`; no
  historical citation was retained merely to make the checker green.

### 9.4 Wave exit

The macro-checkpoint amendment exits only when MC-1–MC-13 are green, the
strengthened process tests carry exact `// spec:` links, the independent review
has no surviving correctness finding, bootstrap's planted lifecycle refusal is
returned without unwind, the executable candidate-closure routes and detection
proof are truthful with no shadow no-op gate, and the root library plus affected
crate tests compile and pass. A failure in the unchanged public-API comparison,
a new schema/platform/ABI delta, or a TraitImpl behavior change returns to the
appropriate architecture/user gate instead of being accepted as implementation
fallout.

## 10. Guarded-redefinition evidence delta

This section supersedes every earlier row in this plan where it assumes the
retired machinery named above. The source-ordered macro-checkpoint conditions
MC-1–MC-12 remain current where they protect atomic publication, dependency
independence, continuation, owner lifetime, cache relations, or GOT
compensation. The approved authority is `repl/spec/18-redefinition.md` and its
cross-carriers. Tests are evidence for that behavior, not targets for preserving
the superseded implementation.

**Readiness: HOLD for realization.** Architecture must first publish the exact
cross-crate proposal, including the language-type/internal-ABI boundary, live
reverse-scan ownership and restart/gap behavior, and the atomic publication
grain for each declaration class. Any inter-crate public-API delta then returns
to the user for exact pre-implementation approval; after implementation, every
affected generated `public-api.txt` diff returns for the separate confirmation
gate. A claimed zero delta is also checked against generated output. QA may
author the evidence after the proposal settles its legitimate seams, but no
test or product implementation starts from this allocation alone.

### 10.1 REPL-spec split maintenance checks

`spec_link_check.py` and `spec_coverage_reconcile.py` are **maintenance
checks**. They govern traceability-instrument currency, not language behavior.
Their failure blocks coverage and release claims that depend on them; it does
not turn a documentation-path migration into a product defect.

The post-split maintenance gate is now green (2026-09-05):

- `spec_link_check.py`: 2,444 citations scanned; 2,431 OK, zero MIS-CITED,
  zero MALFORMED, and 13 skipped free-form notes. The seven retired §18.1.1
  references were re-judged rather than made artificially resolvable.
- `spec_coverage_reconcile.py --mode check`: 772 live citations, zero dead,
  zero missing-name, and zero cleared-coverage rows across the language and
  sectioned REPL specifications.
- `verify-citations.py --corpus live`: 476 documents and 8,392 citations with
  zero findings against the existing ratchet.
- The checkers' isolated planted-fault suites pass 2/2 and 4/4 respectively,
  including old-path alias resolution, absent/duplicate anchor rejection,
  split-leaf discovery, missing-test-name detection, and cleared-row detection.

`test` migrates both checkers without rewriting the 2,285 external
`repl/spec.md` occurrences:

| Check | Required migration | Detection proof and negative control |
|---|---|---|
| test → spec | Treat `repl/spec.md` as a stable logical alias. For a citation carrying a §anchor, search the headings of every numbered `repl/spec/*.md` normative leaf; continue to accept a direct leaf path. Do not treat `index.md` as normative content. File-level citations may continue to resolve to the compatibility pointer. | In an isolated temporary root, an old-path `// spec: repl/spec.md §18.2` and a direct-leaf citation both pass. Changing only the anchor to absent `§18.99` produces MIS-CITED. A duplicate numeric heading in two leaves is an error rather than first-match success. The existing 576 split-only failures go green; the seven retired-anchor and 68 unrelated failures remain visible until independently repaired. |
| spec → test | Enumerate all 21 normative leaves, report their physical file and line, and canonicalize both an old-path back-reference and a direct-leaf back-reference to one logical `repl/spec.md` identity for anchor joins. Keep mutation modes scoped to the physical leaf that owns the bracket. | In an isolated temporary root, a `[Tested tests/sample::present]` bracket in a leaf joins a test carrying the old-path back-reference and passes. Renaming only `present`, or putting a broken bracket in a leaf omitted by the old scanner, fails. A cleared row in a leaf remains a failing cleared-coverage result. |

The checker change-set removed only split-path false failures. The residual
citations were repaired or re-judged by their owners; none was hidden in an
allowlist. QA then re-judged all 57 cleared coverage markers against current
test bodies: 38 now cite current positive/negative evidence and 19 remain
plain `[Uncovered S121]`. The obsolete accessor/method-collision rejection and
same-name method import-conflict tests were deliberately not cited as evidence.

Seven live line-sensitive references cannot use the logical alias because a
pointer has no stable corresponding line. Their owners replace line numbers
with semantic section anchors in the same split-maintenance change-set:

| Occurrences | Owner | Replacement target |
|---|---|---|
| `repl/spec/03-slash-commands.md` and `src/repl/format_type.rs` — old line 198 for the shared related-name layout | `spec`, `dev`(int) | the governing §3.3 layout plus the related-symbol section; remove the line number |
| `design/arch/fixmes/0050-promote-list-seq-pretty-printer-aspirational.md` front matter and body — old line 319 | `arch` | `repl/spec/01-display-format.md` §1.5 |
| `tests/repl_introspection.rs` and `src/display.rs` — old §1.5 line 309 product rendering | `test`, `dev`(int) | `repl/spec/01-display-format.md` §1.5 |
| `tests/display_exact.rs` — old §3.11 lines 992–1000 | `test` | `repl/spec/03-slash-commands.md` §3.11 |

### 10.2 Lowest discriminating product evidence

Unless a row says otherwise, process evidence is a fresh, prelude-minimal REPL
session because redefinition is live-session behavior. `dev` adds a unit test
at every changed implementation seam; `test` adds only the independent cells
below. Error cells assert required information and order by substrings, not
byte-exact punctuation.

| ID | Approved condition and plausible wrong outcome | Lowest evidence, polarity and owner |
|---|---|---|
| GR-1 | A same-language-type callable edit is legal with direct callers and captured callable values only when every existing slot has an ABI-compatible `ModeSummary` under §18.1.2. An accepted edit patches the existing slot and performs no dependent recheck or special report. An advisory-only summary change is legal; a parameter- or result-mode change rejects before publication even with no callers, retaining the old body, slot and source and explaining unchanged language type versus changed ownership ABI. | **Acceptance — `test`:** retain `redefine_body_only_stale_closure_late_binds_new_body`, `redefine_body_only_neg_no_cascade_report_no_dependent_recompiles`, `redefinition_updates_live_callers`, and the session-history late-binding cells as same-mode positives, re-cited to §18.1/§18.1.2; add one inferred same-type/mode-changing rejection whose old callable remains usable and whose rejected source is absent after restart. **Safety fence — `dev`:** after architecture names the seam, compare `None` with all-Owned/Fresh and advisory-only differences as compatible controls; reject parameter- and result-mode differences before slot patch. Exercise the gate over an ordinary slot, every member of an overload candidate, every existing generic realization, and every materialized impl method, with whole-unit state/source preservation. No dependent typecheck/codegen attempt occurs in either leg. |
| GR-2 | A type change with no blocker publishes; a direct call, first-class value use, or settled-but-not-codegenerated definition blocks. A transient expression result does not. Rejection preserves old source/body and reports target, old type, proposed type, all direct blockers sorted and deduplicated, then remedy; it excludes transitive and unrelated definitions. | **Acceptance — `test`:** one no-dependent positive and one transient-result control; one compact blocker fixture with call/value definitions entered in deliberately non-sort order, plus one transitive and one unrelated control. Assert rejection, ordered required fields, old calls still work, and rejected source is absent after restart. **Safety fence — `dev`:** at the internal state seam named by architecture, a committed settled-but-not-codegenerated definition blocks; late publication refusal is byte-for-byte state preserving. Public-process evidence MUST NOT manufacture otherwise-unreachable compiler state. |
| GR-3 | The target's self-edge does not block; a distinct mutually recursive sibling does. Concrete realizations normalize to one authored callable, so multiple specializations cannot duplicate or hide a blocker. | **Acceptance — `test`:** a recursive no-external-dependent type change succeeds; its mutual-recursion twin rejects. Instantiate one generic dependent at two types before the attempted change and require its canonical name exactly once in the diagnostic. **Unit — `dev`(int/typecheck as architecture assigns):** reverse scan excludes only the target self-edge and normalizes every concrete key to its authored owner. |
| GR-4 | A multi-signature definition is one family. Body edits and clause reordering with the same signature set hot-reload only when every existing member slot is ownership-ABI compatible; one incompatible member rejects the complete family. Adding, removing or changing a signature is atomic and blocked by any external member dependent. Family self/sibling edges do not block, and rejection retains every old clause. | **Acceptance — `test`:** a same-set reorder/body edit with an external caller; an external-dependent add/remove rejection proving all old clauses still dispatch and no new clause leaked; a family-internal sibling-call control with no external dependent that permits a set change; and a same-set candidate with one mode-incompatible member that retains every old member. **Unit — `dev`:** `redefine::tests::classify_internal_names_and_callable_family_boundaries` is GREEN and proves single↔family representation changes compare their complete signature sets; the remaining unit allocation proves order-independent family-set comparison, normalized/deduplicated/sorted blocker union, and complete ownership-ABI validation before any member patch. |
| GR-5 | Callable and macro visibility are immutable in both directions during live redefinition; rejection retains live behavior and backing source. | **Acceptance — `test`:** a four-cell `{defn,defmacro} × {public→private,private→public}` matrix, each followed by a successful use of the prior definition and restart proof that the rejected spelling was not persisted. Deftype and trait visibility rejection is covered in their structural/interface matrices. |
| GR-6 | Macro replacement is atomic and future-only: an existing expanded definition keeps its old body, a later expansion uses the new macro, and reload/restart re-expands authored calls with the then-current macro. Macro arity/shape changes do not invalidate old expansions. Ordinary calls/value uses inside a clause remain blockers for an ordinary callable type change. | **Acceptance — `test`:** live old-expansion/new-expansion twin; changed-arity twin; separate reload and restart reconstruction cells; failed replacement preserves the complete prior macro. Rewrite the existing macro-clause/helper redefinition test to require rejection and prior-helper behavior; its diagnostic names the authored canonical macro parent once even when multiple private clauses block, never a compiler-generated clause name (§10.5). **Safety fences — `dev`:** retain applicable MC-1–MC-12 checkpoint, continuation, owner and cache controls; delete the receipt-to-cascade assertion. |
| GR-7 | Same-name `deftype` re-establishment accepts only identical runtime/naming structure. Docs and positional sum labels are non-structural; every structural change rejects regardless of callers without changing old values, ctors, accessors or docs. | **Unit matrix — `dev`:** product/sum, visibility, alpha-equivalent params, ctor order/tags/names, payload arity/type, and product field/accessor name/type/order, each with one equal control. **Acceptance — `test`:** type+ctor doc update and sum-label rename succeed; representative product-layout and sum-tag/order changes reject and old constructed values still match/access correctly. |
| GR-8 | A trait interface is immutable modulo bound-variable alpha-renaming. Docs update live. A same-interface default-body edit affects future realizations only: an existing materialized default stays old, a new impl gets the new template, and explicit re-`impl`/reload/restart rematerializes the latest template; explicit overrides remain their own bodies. | **Unit matrix — `dev`:** visibility, conventional/HKT head, method set, required/default class, arity, types and constraints, with alpha-equivalent and doc/default-body controls. **Acceptance — `test`:** rejected representative interface change preserves prior dispatch; one live old-impl/new-impl/re-impl sequence discriminates template timing and explicit override; reload and restart reconstruction cells acquire the latest default. |
| GR-9 | Re-`impl` remains atomic at whole `(trait,target)` pair grain; omitted defaults use the current template, every existing materialized method must remain ownership-ABI compatible, and a failed candidate leaves every old method. FIXME 0832 is a defect, not an exception. | **Acceptance — `test`:** retain the four `impl_redefinition_dispatch` cells, add/retain a two-method failed-candidate cell that proves neither candidate method leaked, add a candidate whose one method changes ownership ABI and prove neither candidate method leaked, and keep `trait_method_tail_s116::reimpl_default_body_calls_replaced_sibling` failing and unignored until its fix turns the same test green. It is never deleted, ignored or weakened. |

### 10.3 Superseded evidence disposition

`test` performs this reconciliation before implementing new §18 coverage, so a
green result cannot be manufactured by keeping tests for behavior the language
now forbids.

- **Retire without replacement as behavior:** the broken/trap presentation and
  recovery cells
  `redefine_abi_change_broken_caller_direct_call_traps_with_provenance`,
  `redefine_broken_caller_value_use_wrapper_minted_before_break_reaches_trap`,
  `redefine_broken_caller_curried_partial_reaches_trap`,
  `redefine_broken_caller_info_and_sig_report_broken_status`,
  `redefine_recovery_fixing_caller_clears_broken`,
  `redefine_recovery_reverting_callee_recompiles_caller`,
  `redefine_trap_invocations_leak_bounded_per_trap`,
  `trap_presented_in_normative_runtime_error_format`,
  `sig_broken_symbol_primary_line_matches_bare_lookup_fully_qualified`, and
  `bare_lookup_broken_symbol_info_still_shows_definition_source`.
- **Rewrite as pre-publication rejection evidence (GR-2/GR-3/GR-4):** every
  `redefine_abi_change_*`, `type_change_redefinition_*`,
  `redefine_concrete_to_*`, `redefine_unannotated_*`, `t1_downgrade_*`,
  `t1_full_cure_*`, `t1_reload_failure_error_block_lifts_on_caller_repair`,
  and `redefine_cascade_report_neg_macro_clause_caller_folds_to_owning_macro`
  cell whose source actually changes the language type. Collapse duplicate
  fixtures into the discriminating matrix; do not retain stale/recompiled/
  broken report assertions.
- **Rewrite as ownership-ABI rejection evidence (GR-1/GR-4/GR-9):** a cell
  whose language type stays equal but whose inferred parameter or result mode
  changes proves §18.1.2 rejection, not the different-language-type path in
  GR-2. Preserve one ordinary-callable process example; cover overload,
  existing-realization and materialized-impl breadth at the architecture-owned
  seam without duplicating process fixtures.
- **Retain and simplify:** same-type late-binding, existing-slot and
  no-special-report cells whose ownership ABI remains compatible, including
  `persist_body_only_redefinition_neg_keeps_slot`,
  the `ls1_body_only_*`/same-type session-history cells, and
  `repl_lifecycle`'s same-type caller propagation cells. Rename “propagates”
  prose where it implies recompilation; the evidence is slot late binding.
- **Rewrite persistence:** `persist_abi_change_redefinition_restart_runs_correctly_from_cache`
  becomes the caller-free type-change reconstruction cell;
  `persist_abi_change_allocates_fresh_slot_hole_survives_restart` retires
  because fresh-slot holes are no longer a language requirement;
  `persist_unannotated_downgrade_restart_unifies_on_latest_definition_sibling`
  and `restart_with_broken_backing_file_reaches_prompt_and_accepts_repair`
  become rejection-does-not-write/prior-source-restarts cells; the fresh and
  cache-restored file-backed cascade pair becomes rejection parity with the old
  callable still usable.
- **Preserve unrelated fences:** §14.2 watcher recompilation of dependent
  *modules*, reload error blocking, macro checkpoint atomicity/durability,
  ordinary failed-cluster rollback, candidate closure, fallible bootstrap,
  cache owner/GOT compensation, and the existing whole-pair `impl` tests. They
  do not acquire §18 cascade authority and must not be deleted by a broad
  `cascade|broken|trap` name sweep.

The seven former test-side `§18.1.1` citations have been retired or rewritten
and re-cited to current authority. The removed heading remains unresolvable, as
proved by the traceability checker's absent-anchor control.

### 10.4 Exit gates

**Current integrated census (2026-09-05):** after the declaration-family API
baselines were approved and regenerated, 5,740 tests ran; 5,716 passed, 24
failed and 1 was skipped. The public-API and traceability failures are absent.
The remaining REDs are allocated as CLIF goldens (7), superseded
cascade/redefinition evidence (5), FIXME 0907's `Bind` defect including its two
aggregate reporters (7), shadowing (2), vec-query (2), and one stale spec-03
assertion. This is an attribution inventory, not an acceptance: each cluster
still needs its owning disposition below.

1. Architecture is approved; every public-API pre-gate is recorded before
   implementation, and the generated post-change baseline matches that exact
   approval.
2. Both traceability maintenance checks carry positive and planted-negative
   detection proofs, scan the split corpus, and report residual debt honestly.
3. GR-1–GR-9 execute at their allocated layer; every changed implementation
   seam has its unit fence, and no process test constructs internal session
   state.
4. Obsolete cascade/broken/trap assertions are absent, while §14 watcher and
   macro-checkpoint fences remain. FIXME 0832 stays failing-not-ignored until
   fixed, then the unchanged reproduction is green and marked fixed.
5. A fresh `cargo nextest run --no-fail-fast` has no unexplained RED. The
   checker results, full-suite census, review, and generated API evidence are
   all required; one cannot substitute for another.

### 10.5 Macro-clause blocker display identity — resolved ruling

The user ruled on 2026-09-04 that a compiler-private macro clause retains the
actual stored `callees` edge, but a blocker diagnostic normalizes that clause to
the authored canonical macro parent. Multiple blocking clauses belonging to one
macro deduplicate to one parent; distinct macro parents remain distinct. A
compiler-generated clause name is implementation-defined and MUST NOT leak into
the diagnostic. The exact normative amendment was approved and applied to
`repl/spec/18-redefinition.md` §18.2 on 2026-09-04; GR-6's identity assertion is
therefore released from its specification hold.

## 11. Standalone result-handoff disposal carrier

This post-plan wave addresses only ownership after an IO branch has produced a
value and before that value reaches its next language owner. It does not amend
the language behavior, platform interface, public Rust API, or ABI 10.

| Risk | Discriminating evidence | Exit |
|---|---|---|
| Runtime and continuation both dispose one Bind input | `io::tests::bind_handoff_disarms_runtime_owner_before_continuation_consumes` makes the continuation perform its one disposal and asserts the runtime adds none | exact count 1 |
| Par loses heterogeneous per-slot authority or reorders it | backend `par_bind_carries_one_disposer_per_branch`; intrinsics `abandoned_par_buffer_disposes_every_initialized_slot` records distinct slot values through distinct disposer callbacks | source-order pair layout and exact count 2 |
| A nested trampoline transfers a terminal value before its caller applies fault/cancellation policy | immediate re-arming at every sync/async branch boundary; `serial_group_first_fault_prevents_later_owning_effect` and `async_capacity_one_first_fault_prevents_parked_owning_effect` pin the capacity-1 first-error boundary | later parked effect never starts; already-produced values remain armed until transfer or drop |
| A cancelled blocking loser returns after its receiver disappeared | `io::tests::poll_arm::cancelled_blocking_branch_disposes_its_late_result_worker_side` waits for the foreign call to enter, drops the receiving future, then observes the worker-side result disposal | deterministic exact count 1; no timing-only success condition |
| The reactor returns while a cancelled Select loser still has an entered blocking Par worker | §3.2 acceptance triplet plus `bridge_join_lifecycle_holds_root_until_cancelled_worker_exits`; the paired early-release plant inverts the final events | held worker exits before root teardown; exact RC balance; planted inversion detected |
| Select disposes its winner before outward handoff | backend `race_carries_result_disposer_only_for_owning_payload`; intrinsics `select_winner_transfers_common_disposer_to_top_level_caller` observes zero disposal before the caller consumes the returned winner | winner transfers once; late-loser case is the blocking cancellation row above |
| Launch silently leaks an unobserved owning result | backend `launch_continue_carries_detached_result_disposer`; intrinsics `launch_supervisor_disposes_unobserved_owning_result_once` drains the supervisor and observes its disposal | exact count 1 |
| A completed/cancelled/fault sentinel is confused with a language value | `TrampolineOutcome::{Completed,Stopped}` structure plus the existing empty-select and fault suites | only `Completed` can acquire a `ProducedValue` owner |
| Disposer words are mistaken for IO-tree children | updated Bind/Par/Select/Launch drop fixtures, including Par's 16-byte descriptor stride | all node teardown suites green |
| Function-address glue works only in JIT mode | `spec_10_io::linked_bind_owning_result_disposer_relocates_and_runs` | linked executable exits 17 |

The wave gate is the full backend and intrinsics package suites, the focused
linked witness, all-target checks, exact seven-crate public-API comparison,
`git diff --check`, and fresh independent review. A broader workspace result is
reported only as part of Sprint 121's final integrated census; it is not
substituted for these edge-specific ownership assertions.

## 12. Result-context specialization

QA allocation for implementers and independent review. Authority is the approved
[current identity contract](../../design/arch/interfaces.md#instance-identity-funnel)
(the [S121 approved packet](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/s121-result-context-specialization.md)
retains dated approval provenance)
and [typecheck design](../../design/typecheck/result-context-specialization.md),
under `spec/03-types.md` §§3.3.4, 3.6.3–3.6.4 and 3.11.3. Scheduling, executed
evidence and current gate status belong to the sprint ledger.

| Condition / plausible wrong outcome | Lowest discriminating evidence and owner |
|---|---|
| Concrete substitution identity distinguishes result-only instances; repeated uses and different diagnostic sites do not invent new identities. An argument-only key would collide. | **Acceptance, types `dev`:** extend `module/tests.rs` instance/demand fixtures for distinct type vectors, equal-vector reuse and site-independent keys; preserve selected-template/home distinction. |
| Derivation and replay agree on every generic position. Numeric inference-ID order, duplicate occurrences or lost higher-kinded heads would reconstruct the wrong signature. | **Acceptance, typecheck `dev`:** one compact canonical-order family covering alpha-renumbered variables, repeated variables and resolved higher-kinded heads. Assert the vector and reconstructed full type; residual variables produce no concrete demand. |
| Equal value arguments with different required results reach distinct concrete bodies and slots; equal substitutions reuse the same instance. Successful checking alone can hide an under-keyed body. | **Acceptance, typecheck `dev`:** extend mono-collection/mint units with nullary returned closures, nonzero-argument result-only variables and returned containers. Inspect concrete schemes, `InstanceLink`s, call dispatches and slots, including an equal-substitution repeat. |
| Complete context reaches each differently shaped producer and survives nested rechecks. Flattening an ordinary function-valued result as auto-curry, discarding a value-reference result or reading an outer span map would choose the wrong instance. | **Acceptance, typecheck `dev`:** ordinary-call/function-value/auto-curry sibling cases, one selected-overload-arm case and one imported nested-hop case. The latter uses the defining scope and discriminates inner versus outer type maps. Extend existing argument-driven trait and recursion safety fences for the migrated self-recursion/inner-call identity consumers; no duplicate all-mode matrix for these private seams. |
| Replay needs no expression map and validates generic-vector length, not value-call arity. A partial zip could silently mint an incomplete instance. | **Acceptance, typecheck `dev`:** extend `form/tests.rs::instantiate_demands_mints_and_deduplicates_existing_instance` with result-only demands and stable-slot replay; malformed length installs nothing. Retain existing absent-home gap, stale-root continuation and hard-invariant-error controls with the new carrier. |
| Independent result-context calls execute correctly through the compiler boundary, not only in typecheck fixtures. | **Acceptance, independent `test`:** extend `shadowing_scope_lookup::result_only_returned_closure_specializes_at_int_and_string` to REPL, `--run` and linked execution, retaining exit/value 200 and the concrete annotated control. This existing permanent RED is the primary fix falsifier, not new defect intake. |
| Generic definitions remain admissible, but an unresolved runtime use and one shared closure used at incompatible types are rejected by typecheck. A stricter obsolete test could force the wrong product behavior. | **Acceptance, independent `test`:** replace the expectation in `spec_03_types::result_only_var_unresolved_use_ambiguity_not_rank1_neg`: an unused `g` wrapping `constf` is accepted; an actual unresolved runtime use is rejected. Keep absence of GOT-slot, backend and rank-2 diagnostics. Reuse `single_poly_instance_used_at_two_types_value_restriction_neg` for the shared-instance boundary; cover the changed semantic cases across modes using the existing harness. |
| New cache links retain complete substitution identity; schema-25 data is never interpreted under the new meaning. A successful cold compile does not prove cache restoration. | **Acceptance, backend `dev`:** serialized concrete-instance link round-trip under schema 26, paired with an exact schema-25 `SchemaMismatch` refusal before payload decoding. **Acceptance, independent `test`:** minimal result-context program, uncached/cold/warm output equivalence plus an actual cache-hit observation, reusing the existing cache harness. The unit pair proves the refusal boundary; the process witness proves compiler consumption. |
| The delivered boundary matches the approved packet, with no incidental ABI change. | **Maintenance:** generated public-API comparison contains only the approved types delta; return the actual diff to the user for confirmation. Schema is 26 and platform ABI is unchanged. Generated-name/CLIF assertions are maintenance evidence, reconciled after the behavioral conditions above, not authority to change semantics. |

No additional specification or public-API decision is required by this
allocation. New seam tests precede their fixes; existing REDs demonstrate their
own detection, and new controls need the scoped revert/plant proof required by
the standing QA contract. Unit fixtures own internal identity observations;
process tests do not construct symbol tables or compiler sessions. No new
runtime detector or platform matrix is allocated.

The independent process witnesses are
`tests/shadowing_scope_lookup.rs::result_only_returned_closure_specializes_at_int_and_string`
and `tests/shadowing_scope_lookup.rs::concrete_returned_closure_annotation_control`
for all-mode values 200 and 100;
`tests/spec_03_types.rs::result_only_var_unused_named_wrapper_accepted`,
`tests/spec_03_types.rs::result_only_var_unresolved_use_ambiguity_not_rank1_neg`
and `tests/spec_03_types.rs::single_poly_instance_used_at_two_types_value_restriction_neg`
for all-mode admission/refusal boundaries; and
`tests/cache.rs::cache_result_only_returned_closure_specializations_agree_uncached_cold_and_warm`
for unchanged output and a cache hit on the generic's defining module. Its
hit assertion must reject a no-cache warm leg even when the value remains 200.
Internal identity and restoration remain allocated to the module witnesses
above; process output alone does not prove the complete stored substitution.

The separate staging-layout condition behind
`cache::cache_restored_sum_field_projection_keeps_ownership_abi` is allocated in
§13. Its warm leg builds a fresh cache, so invalidating old caches cannot
satisfy it. Overall Phase-5 acceptance additionally needs the reconciled full
census and remaining closure streams.

## 13. Staging-aware value layout

Historical S121 QA allocation for the [approved exact API packet](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/s121-staged-value-layout-api.md).
The user approval recorded in the sprint ledger releases serial types then
typecheck implementation. This delta changes declaration access, not layout
eligibility or the live-redefinition ownership-ABI rule (§10 GR-1/GR-4).

| Changed condition / plausible wrong outcome | Lowest discriminating evidence and owner |
|---|---|
| The table wrapper and lookup entry point compute identical layouts. A second walk or projection could diverge. | **Acceptance, types implementation owner:** extend existing shared-layout fixtures to compare both entry points, including absent tables/metadata and scalar bases. Retain one constructor-name projection, concrete-field projection and recursive walk; independent review verifies this structural discharge. |
| Constructor identity and eligibility remain exact. A poisoned bare alias, product facet or recursive field could acquire an invalid Copy layout. | **Safety fences, types implementation owner:** reuse/extend local layout and constructor fixtures for canonical-key preference with conflicting bare metadata, canonical-absent bare fallback, product constructor facets, missing/wrong binding kinds, single versus zero/multiple constructors or fields, non-concrete fields, heap/Vec exclusion, nested cross-module fields and self/mutual cycles. Assert explicit expected layouts as well as wrapper parity so two equally wrong results cannot pass. No duplicated process matrix. |
| Both ownership consumers see the coherent staged view. A published-only consumer, or fallback after a present but ineligible staged binding, can disagree with the other consumer or backend. | **Acceptance, typecheck `dev`:** red-first local siblings exercise eligible staging over absent/ineligible published metadata and ineligible staging over eligible published metadata. Observe Copy classification and uniqueness eligibility separately, preserving uniqueness's String/ADT restriction and inverse layout polarity. Pin absent-staged-key fallback and nested lookup into another module using the existing probe fixtures; a shared adapter alone does not prove both callers use it. |
| Identical authored source reconstructs equal correct ownership independently of restored functions. Equal output alone can conceal the inference discrepancy. | **Acceptance, existing root module witness:** retain `src/worker/tests.rs::cache_preloaded_sum_projection_recheck_preserves_ownership`; fresh-import, restored and restored-without-authored-functions schemes and summaries agree, with Copy asserted explicitly. Restored metadata retains slots and schema while code is absent and GOT pointers are null; the unchanged live ABI guard accepts the staged result. The original RED demonstrates detection at this composed inference seam. |
| A repaired compiler produces and consumes its own valid entry metadata. Silently skipping metadata preload can pass output equality and leave cache files present. | **Acceptance, independent `test`:** reuse `tests/cache.rs::cache_restored_sum_field_projection_keeps_ownership_abi`: uncached/cold/warm legs return 40, with fresh private cache state. **Binary `dev` observation seam:** one `CRANELISP_MODULE_TRACE`-gated entry-metadata-preloaded event after successful installation in `src/session_v4/lifecycle.rs::preload_entry_slot_assignments`. `test` asserts the exact main-module event for warm execution and its absence for cold/no-cache execution. Detection proof disables caching for the warm leg: output stays 40 but the restoration assertion fails. Entry bodies intentionally recompile; this event does not claim object-code reuse. No new harness. |
| Corrected inference does not admit an incompatible live replacement or churn live slots. | **Safety fences, existing witnesses:** rerun `tests/repl_redefinition.rs::same_type_ownership_abi_change_is_rejected_before_slot_patch` and the existing root guarded-publication/slot-high-water controls. Preserve rejection, prior callable behavior and slot stability; no new refusal matrix is allocated. |
| The example-level symptom disappears with the same input. | **Diagnostic observer:** rerun example 35 cold and warm on the repaired compiler and report remaining example-35 failures numerically against its recorded failure. This reconciles the aggregate symptom; the module and cache witnesses carry acceptance authority. |
| The delivered public boundary matches the exact approval. | **Maintenance, types owner plus independent review:** generated baselines show exactly the packet's one added types API line, no removal/change and no delta in other crates. Return that actual diff for user confirmation. Cache schema and platform ABI remain unchanged. |

Local tests precede their respective fixes; owners report the discriminating
RED and GREEN or focused fault-plant result. Reuse existing controls where they
already cover the listed invariant. The independent evidence allocation only
extends the existing cache witness; internal state stays in module tests.
No runtime detector, additional mode matrix or cache migration is allocated.

The entry-preload event supplies fixture reachability evidence. The root unit
witness installs restored metadata directly, so it cannot detect a skipped
production preload; file existence alone cannot distinguish unused cache data.
One opt-in event at completed installation discriminates that residual without
introducing fixture tampering, another slot-lifecycle scenario or a runtime
enforcement check. Its wording is diagnostic, not a new language requirement.

Old defective-compiler caches are not a compatibility acceptance condition:
the packet retains the build-ID revision boundary, and a dirty rebuild at the
same revision can preserve that ID. Fresh repaired-build cold-to-warm evidence
is required; disabling caching, bypassing an ABI guard or bumping the schema
cannot satisfy it. Final adequacy consumes the owners' executing evidence and
independent review, and wave passage additionally requires the generated API
confirmation. Executed counts and the final gate disposition are recorded in
the sprint ledger; this allocation makes no whole-sprint acceptance claim.

## 14. Example and generated-artifact maintenance

Example 33's batch source follows `spec/05-definitions.md` §5.13: one
definition per canonical name, with forward references inside the cluster.
`examples/33-definition-ordering.cl` contains six binary pass counts and returns
6 only when its direct, forward and chained function/trait calls all succeed.
`tests/examples.rs::every_example_runs_with_documented_exit` maintains the
renamed file's exact exit expectation and complete on-disk file-set check;
signal deaths remain distinct from normal exits. This is **maintenance
evidence** for the teaching artifact. Existing definition-ordering and live
redefinition tests retain language acceptance authority; the example does not
replace them. Direct uncached/cold/warm execution and the examples aggregate
reconcile the reported example failure without a new test matrix.

CLIF drift is a **diagnostic observer** until backend design attributes each
changed frame to an approved implementation change. Candidate/binary hashes
and original-golden hashes provide capture provenance, not correctness.
Recapture is allocated only after that attribution identifies the permitted
files and deltas, any unexplained difference is resolved, and the relevant
behavioral witnesses remain satisfied. The attributed snapshot then carries
**maintenance** authority over that artifact; a snapshot alone cannot establish
ownership safety or authorize different language behavior. Execution counts,
capture paths and the current recapture decision belong to the sprint ledger.

### 14.1 Fresh owning result through a wrapper

The `f4_sudoku` return-protection deltas are a **diagnostic observer**;
`tests/nullary_arm_beside_boxed_arm_0917.rs::forwarding_fresh_option_releases_its_payload`
is the independent **acceptance** witness for the reproduced wrapper leak.
The owning runtime condition is release of unreachable heap ownership; the
suspected mechanism is an extra reference on the fresh boxed result returned
through the wrapper. Existing 0917
nullary-versus-boxed siblings can share that wrapper behavior and subtract the
same leak; correct solver output cannot discriminate it.

**Independent `test` allocation:** use the existing `helpers::marginal`
`MarginalPair` with `RcStats` for a free-standing wrapper/direct-helper sibling.
Keep declarations, owning payload, successful result, caller disposal and
iteration count equal within each pair. The helper produces a fresh `Some`
box; the subject returns it through the suspect wrapper and the control calls
the helper directly. Capture CLIF to verify the reduction retains the
identified guarded return-retain and executes its boxed-result branch. Losing
that shape during reduction does not discharge the original observation.

Compare two bounded iteration counts and report both raw counter pairs and the
incremental residual. Under `spec/12-runtime.md` §12.3.1, extra completed
iterations must not strand additional unreachable owners: the wrapper-minus-
direct residual slope is zero. A fixed compile-time offset is not a runtime
leak; a zero slope where both siblings leak likewise cannot prove either
balanced. Inspect each child's growth and reduce a shared leaking helper if
necessary. Assert successful expected values independently of allocator data.
Reuse the harness capability fences; no absolute prelude residue threshold or
new harness is allocated.

The retained witness compares 8 and 32 iterations, checks each child's expected
exit and requires zero direct-helper and wrapper-minus-direct residual growth.
Its equal-allocation, zero-direct-residual control discriminates retained
ownership from extra allocation; the executing counts belong to the sprint
ledger. Classify the symptom `rc-miscount` and route it to backend design.
The emitted-code and source-control analysis must establish the correction
seam before implementation; this witness alone does not license changing every
return-protection site. The discriminating emitted witness is helper call →
guarded retain of its returned Option → parameter cleanup → return; the direct
helper lacks that additional retain. Both summaries may report parameter
aliasing because the fresh container contains that parameter. Reachability
does not negate the callable's independent returned reference.

**Backend `dev` delta, after design handoff:** extend local emitted-code
ownership tests red-first for forwarding actual callable returns carrying
Fresh, alias and projection summaries while heap cleanup remains present.
Assert transfer without a second retain and preservation of required cleanup.
A sibling returning a raw scope binding still needs protection; mixed joins
cannot inherit transfer permission from only one owning arm. Reuse the
existing COW return-source and direct-vec-get versus user-call projection
fences. `OwnedTemporary` includes inline COW operations, so blanket protection
elision for that category is not an authorized correction. Preserve physical
freshness semantics and let design identify the smallest shared private
classification that discriminates these ownership cases. No public-API,
schema or language-rule change is allocated.

Begin with `--run` and ownership enabled. Ownership disabled may supply a
separate diagnostic comparison when needed; both children of each marginal
pair use the same ownership setting, and cross-setting subtraction is not
evidence. If the symptom is reproduced, retain the minimal spec-traced,
failing-not-ignored test and route the measured result, CLIF and falsifying
control to backend design before a fix. Mechanism attribution remains
provisional until that control separates it. A confirmed correction requires
its local owner-seam witness and a rerun of the original f4 observation;
broader mode evidence is allocated only for a demonstrated composed residual.

### 14.2 Bounded snapshot handoff

The original f4 execution's absolute allocator residual alone cannot assign a
cause. Its repeated-workload observation distinguishes growth from fixed
compiler cost; the same-driver control below assigns that growth to solver
work rather than the measuring driver. Neither the different warm exemplar's
residue bound nor removal of the suspect retains substitutes for this control.
With no pre-correction f4 runtime measurement, report no aggregate before/after
reduction.

Before f4 recapture, independent `test` measures its committed solved-grid
workload at two small runtime repetition counts, using the same definitions,
compiler and environment with a consuming scratch driver. Each iteration
must produce checksum 154. Report raw allocation/deallocation counts and
incremental residual; fixed compilation cost cancels rather than acquiring
an absolute allowance. Keep the driver outside the golden fixture and ensure
its own result handling does not account for a nonzero difference. Zero
growth, alongside the explained original CLIF and the corrected permanent
wrapper witness, discharges this workload's runtime concern. Nonzero growth
requires narrow residual intake before f4 recapture. This is one diagnostic
pair, not a new solver, ownership-toggle or mode matrix, and it proves nothing
about the fixture's unexecuted backtracking path.

For a nonzero difference, the already-allocated driver control retains the
same declarations, repetition counts and result consumption, replacing only
`solve-once` with `(Pure 154)`. Its zero incremental residual would establish
the solver-workload retention independently of driver overhead. Retain any
confirmed defect as an unignored spec-traced reproduction. The next reduction
separates grid construction from propagation/solve with the same input and
normal result disposal; do not infer the cause from another retained-object
count or start a compiler correction before a discriminating control exists.
The fixed callable-forwarding witness keeps its own acceptance authority.
A separate f4 residual does not retroactively falsify that correction; its
fix or explicit residual disposition is a separate sprint gate decision.

The confirmed residual intake spans grid construction and subsequent solver
work, with the no-work driver balanced. The partial permanent witness retains
the original solved-grid workload; its mechanism remains unattributed. The
smaller vector-building attempt changes reuse behavior across sizes and cannot
serve as a falsifying sibling for this residual. Do not authorize a COW,
recursion or ownership-summary correction from those counts alone.

The minimal isolation compares a recursive vector builder
returning `Some(Grid xs)` with a raw-vector builder wrapped afterward into the
same result graph. Keep payload size fixed while repeating the workload to
separate retention from size-dependent reuse changes. Both paths must return
and consume the same values. Ownership-summary and emitted COW differences
are attribution evidence, not permission to change their contracts or proof
that every f4 residual has the same cause.

`tests/s99_fixtures.rs::nested_result_vec_builder_releases_repeated_workloads`
retains that same-result-graph comparison at fixed payload size. Its assertions
require both balanced control growth and zero additional subject growth, with
correct values in both children. The private COW transfer correction restores
balance by releasing the old slot when the COW result owns a retained
reference. This witness remains distinct from the original f4 partial witness.
Adding
an extra source-level use to force escape would change the alias condition
and needs its own relevance argument; it is not required to complete this
minimal-reproduction handoff.

The sprint ledger records the user's subsequent authorization to investigate
and fix this residual. Readiness is GO for investigation; implementation is
limited to a demonstrated private correction. Trace the varying per-operation
escape decision from its producing site through `pending_cow_escapes` to the
borrowed-source retain branch. Equal whole-function summaries do not establish
equal per-site facts. The observed emitter is not sufficient evidence to
attribute the defect to backend rather than an upstream producer.

**Typecheck correction:** deterministic recursive/nonrecursive controls
establish stale site facts when recursive summary changes do not re-enter their
own callable.
The source seam is
`crates/cranelisp-typecheck/src/ownership/fixpoint.rs::compute_cluster_with_cap`;
`transfer::walk_apply` derives argument escape facts from working summaries.
The owner pins the same recursive boxed-builder fixture under explicitly
reversed callable-universe orders, comparing both final summaries and the
specific COW site's escape fact. Independently transferring the body under
the final converged summaries must agree with stored facts. This deterministic
control distinguishes the measured producer defect from source inspection
alone. Re-enter an already-harvested self-dependency when its summary changes;
acceptance requires the unchanged recursive order/final-transfer witness and
nonrecursive control to pass. Retain the cap-exhaustion conservative fact,
confinement and uniqueness fences — as delivered, the cap-exhaustion fact is
carried by ABSENCE from the published map (the optimistic seed is dropped
before publication and the map has one write site, a completed walk), with
`param_modes` falling to `Owned` and `result_unique_of` to `false` on absence,
and by the cluster-`members` fence that refuses a previous compile's persisted
summary on all three private reads. Absence, not the seed, is what the
retention claim now rests on; the `members` fence carries detection proofs on
each of its three reads and a membership-keyed negative twin. A serial
typecheck reservation is required before that owner's edits; no backend
workaround or new boundary is allocated.

Correct producer facts may stabilize the downstream retaining path rather
than cure its runtime leak. Assess the typecheck correction on consistent,
final-summary-derived site facts, its package evidence and independent review.
Rerun the minimal and full-f4 witnesses to classify the remaining consumer
behavior; a continuing RED does not license weakening a correct escape fact
or claiming the whole ownership defect closed.

The retained direct-control growth assertion remains load-bearing: a zero
marginal can hide equal leaks. The COW transfer correction preserves the
unique-source retain and releases the old slot before the tail backedge when
the result acquires its own reference. Local controls retain required
pre-protection and demonstrate detection when it is removed. Correct escape
facts and true escaping borrowed-source protection remain intact; a shared
leak is not grounds to weaken them or remove the control assertion.

An f4 child with no exit code and no output/counters has an unknown termination
cause, not an allocator verdict. Capture its raw process status, OS termination
signal when actually available, timeout disposition and both output streams
under the same identified compiler before interpreting it. If that failure
does not share the demonstrated minimal mechanism, retain separate attribution.
The producer correction's acceptance remains based on its converged-fact
controls, package evidence and independent review; runtime closure still
requires the two permanent witnesses and explained f4 behavior.

**Independent crash isolation:** rerun the unchanged minimal builder and f4
witnesses on the identified corrected compiler. If f4 still terminates,
preserve the raw status and reuse its fixed solved-grid input to separate
construction/checksum from propagation/solve only as needed. Consume returned
owners and check the expected checksum in each surviving stage. Obtain a
native stack for the failing stage where available; a fault location alone
does not establish the ownership cause. Retain a meaningful minimal crash
reduction beside the existing partial witness before routing a fix. Stop when
the stage, stack and discriminating control establish an owner; no solver-wide
or mode matrix is allocated. The accepted builder correction does not close
the crash, and a remaining compiler quality check is reported separately from
its executing correctness evidence. Goldens remain unchanged.

The implementing owner supplies a red-first local witness at the demonstrated
seam, with a sibling that behaves differently when the proposed cause is
absent. Reuse
existing borrowed/owned COW, true escaping-source retain and tail-transfer
cleanup fences; do not remove required protection to stabilize allocator
counts. Independent `test` reruns the permanent minimal and original f4
witnesses after the correction, including unchanged-source repeat evidence
that exercises the formerly differing site decisions. Keep source, compiler
and observed-site provenance explicit; a single passing minimal run cannot
close the observed variation. No additional fixture matrix is allocated.
If the cause requires another owner, route the discriminating evidence before
that owner's serial implementation; interface and semantic changes retain
their user gates. Goldens remain held until ownership evidence settles.

Any explicit deferral retains the permanent witness failing and unignored.
Deferral leaves the normal clean quality gate unsatisfied; it does
not permit weakening allocator assertions, hiding the test or declaring the
compiler leak-free from recaptured snapshots. Any wider interface or semantic
proposal follows its existing user gate. Executed counts and the user's scope
decision belong to the sprint ledger.

`test` owns changes to the committed golden fixtures. For the 18 candidates
outside `f4_sudoku`, backend design's per-frame attribution identifies the
permitted delta; capture manifests bind original golden, candidate and compiler
hashes. Before replacement, verify original hashes still match the worktree,
fresh repeated capture is deterministic and each fixture executes its expected
result. Collect replacements in one fixture visit after the f4 investigation
settles where practical. Keep f4 unchanged until its ownership observation is
resolved; any new unexplained drift returns to design. After the bounded
replacement, execute the affected seven snapshot checks and review the actual
golden diff against attribution. This is maintenance acceptance, not permission
to repair a compiler by changing expected output.

### 14.3 Post-correction census classification

The whole-suite census taken after the correction (5,839 run / 5,830 passed /
9 failed / 1 skipped, 172 binaries) classifies as follows. Nothing in it is a
genuine regression; the classification, not the count, is the evidence.

**Expected-RED set.** `ownership::transfer::tests::self_shadowed_reach_set_result_is_top`
(`cranelisp-typecheck` lib tier) is a deliberate failing-not-ignored repro of
the self-shadowed reach-set residual. Its record and trigger is its own
`// defect:` line; its class is `enumeration-miss` (`tests/CLAUDE.md`
§"Defect-repro notation" — ratified for the dataflow reach-set instance), and
its control `renamed_binder_reach_set_result_is_top` differs only in the binder
name and is GREEN. It flips when roots resolve to parameter indices at `Origin`
construction. Any census that reports it is reporting a known open defect.

**Superseded (2026-09-07, shadowing wave).** §20.3 landed: roots now resolve to
parameter indices at `Origin` construction, and the cell FLIPPED GREEN. The final
S121 census (`/tmp/cranelisp-s121-shadow-final-J6xI72/full-suite.log`, 5,854 run /
5,846 passed / 8 failed / 1 skipped, sources sha-verified against the live tree)
does not report it, so a census reporting it again is a REGRESSION, not a known
open defect. `spec_10_io::resource_serial_diff_token_parallelizes` is likewise
GREEN there, confirming the load-sensitivity reading above. The one non-golden RED
in that census is the newly authored `shadowed_param_reach_stale_rc_dec::binder_rename_must_not_change_rc_counters`
(backend-attributed; rows in [S121 shadowed-parameter evidence](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md)). The seven CLIF-golden REDs are the same seven cells and the
recapture hold stands.

**Timing instrument, not a product RED.** `spec_10_io::resource_serial_diff_token_parallelizes`
observed 302 ms against its 300 ms midpoint under whole-suite CPU saturation.
The assertion discriminates ~200 ms (concurrent) from ~400 ms (sequential), so a
302 ms observation is not the scheduling signature it guards; the same cell was
GREEN in the pre-correction census on the same corpus. It is a **maintenance
check** whose margin is load-sensitive, and its in-file narration as a
permanently-RED S83/S84 guard is stale. Do not relax the inequality; re-observe
it on an unloaded run before treating a failure as the FIXME-0353 defect.

**CLIF goldens — the divergence content moved, the RED set did not.** The seven
golden REDs are the same seven cells as before the correction. Six re-observe
byte-identically. `clif_golden_lane::clif_golden_lane_no_drift` does not: within
the 40-line diff window the lane prints per corpus entry, 5 of its 14 diverging
entries changed content across the correction — `04_vec_cow_loop`,
`08_adt_in_vec_projection`, `f1_machinery`, `f2_contention`,
`f3_inverted_search` — while 9, including `f4_sudoku`, are unchanged. The lane
dumps with ownership ENABLED (it unsets `CRANELISP_NO_OWNERSHIP`), and the
visible additions are in the conservative direction (`04_vec_cow_loop` gains an
`atomic_rmw … add` retain, entries gain colocated cleanup calls and keep a
block parameter live). Deltas beyond each 40-line window are unmeasured.

Consequence for §14 recapture: the per-frame attribution these goldens await
must be re-derived on the post-correction tree for at least those five entries.
The pre-correction attribution to the earlier lifecycle / result-context /
staged-layout delta remains true of what it covered but no longer covers the
whole divergence, so it cannot be inherited. CLIF drift stays a **diagnostic
observer** and the recapture hold stands.
