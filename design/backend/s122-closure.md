# S122 selected backend closure

Owner: `/design` (backend). Status: **Selected backend runtime-consumer and Q4
alias corrections delivered and independently reviewed; solution-golden
evidence and the Q5 paired measurement complete; the §8 IOR-5 correction is
implemented; the ACT-0974 extern entry convention (co-landed with its
primitives half), the ACT-1021 branch-forward rule, its consuming-COW amendment
and the amendment's last-use alias correction, and the ACT-1024 COW retention
correction with the match-seam retirement it requires, are implemented in the
working tree, uncommitted and not accepted; `test`'s V2 passed and
`review`(backend) found no blocking finding; K4 is complete and `qa` judged
Phase 5's evidence adequate ([K4 record](../../tests/plan/s122-evidence-delta.md#final-test-visit-k4--record-and-phase-5-adequacy-2026-09-30)); user acceptance and phase
approval pending**. The Phase-6b ACT-1037 `vec-set` index guard (§9) is
built and independently reviewed, and `qa` closed ACT-1037 on 2026-10-01
([closure record](../../tests/plan/s122-evidence-delta.md#act-1037--vec-set-bounds-check-closed)); its `--link` GREEN rests on `test`'s W3 run, which
W4's full suite re-observes. The ACT-1040 panic-propagation options (§10) are
costed as a proposal awaiting the user's decision. The
Phase-3 scope and existing contracts were authorized 2026-09-09 against
compiler checkpoint `dc78ddbe` and package checkpoint `98436c9`; this design
has completed independent runtime review with no material findings. This
document is the current entry point for the delivered selected S122 work in
`crates/cranelisp-backend/`. It does not reopen the S121 backend visit or assign
the current generic-replacement and sequence-IO failures.

The bounded context remains `design/arch/bounded-contexts.md` §3. The selected
change has no new public backend API, generated backend baseline delta, emitted
raw ABI, platform ABI, persistent representation, or compiler mode. Its only
cache-schema change is ACT-0974's value-only bump
([non-concrete-release-contract.md](non-concrete-release-contract.md) §7.6). It consumes `ConcreteType::result_root()` and the approved intrinsics
`Owned` contract. The separate uniform executable-identity migration and cache
schema 29 state remain governed by their existing architecture record; this
slice neither changes nor re-dispositions them.

## 1. Delivered backend slice and remaining gates

The selected source and module-test work is delivered and independently
reviewed, except where a row below states otherwise, and its solution-golden
evidence is complete (§3). The Q5 paired
measurement is complete (§6). Final API confirmation and integrated acceptance
remain open:

| Obligation | Backend path | Dependency |
|---|---|---|
| 0898 result-root consumer | `crates/cranelisp-backend/src/lib.rs` | delivered using `ConcreteType::result_root()` |
| 0906 shared nullary-tag guard | `crates/cranelisp-backend/src/compiler/vec_codegen.rs` | delivered through `heap::emit_rc_inc_guarded`, which already owns the lower guard |
| Typed closure fixture | test module in `crates/cranelisp-backend/src/compiler/control_flow/launch.rs` | delivered using intrinsics `handle::Owned` and `drop::consume_closure(Owned)` |
| Source guidance affected by the helper census | `crates/cranelisp-backend/CLAUDE.md` | delivered beside implementation |
| Q4 macro returned-alias ownership | selected-arm projection in `crates/cranelisp-backend/src/lib.rs`; match/return ownership in `crates/cranelisp-backend/src/compiler/` | delivered with focused and public evidence; independently reviewed with no material finding |
| ACT-0974 extern entry convention | `compiler/apply.rs`, `compiler/control_flow/fn_as_value.rs`, `compiler/fn_compiler.rs`, `cache/mod.rs` (value-only schema bump) | designed at [non-concrete-release-contract.md](non-concrete-release-contract.md) §7.6 and implemented in the working tree, co-landed with the primitives half (`string-identity` moves its argument). The SI cells went RED first; `string_primitive_value_discharge` is 10/10 at V2, and neither the primitives nor the backend review found a blocking issue. K4 is complete and `qa` judged it adequate, retiring ACT-0974 ([K4 record](../../tests/plan/s122-evidence-delta.md#final-test-visit-k4--record-and-phase-5-adequacy-2026-09-30)); user acceptance is pending |
| ACT-1021 parameter forwarded through a tail-argument branch | `compiler/fn_compiler.rs` and `compiler/vec_codegen.rs`, plus `heap.rs` for last-use aliases; the four protect paths in `compiler/control_flow/let_if.rs` and `compiler/match_codegen.rs` read the same fact unchanged | designed at [ownership-codegen.md](ownership-codegen.md) §13.3 (branch-forward rule, one ownership fact, consuming COW argument and its last-use alias correction); the rule, the amendment and the alias correction are in the working tree; `test`'s after-fix run passed with `copy_only_tail_push_protects_its_forwarded_match_alias` GREEN, V2 kept the tail family GREEN, and review found no blocking finding; K4 is complete and `qa` judged it adequate, retiring ACT-1021 on K4's armed and unarmed replay ([K4 record](../../tests/plan/s122-evidence-delta.md#final-test-visit-k4--record-and-phase-5-adequacy-2026-09-30)); user acceptance is pending |
| ACT-1024 in-place COW on a frame-owned `Var` released twice | `compiler/vec_codegen.rs` (two-state source classification; the recorded retain decisions are deleted), `compiler/apply.rs` (the claim set around the self-tail arguments; the escape threading is deleted), `compiler/fn_compiler.rs` (the claim set and its one reader; the return-COW claim, keyed by site; the retain reconciliation is deleted), `compiler/match_codegen.rs` (the arm plan without a COW input) | designed at [ownership-codegen.md](ownership-codegen.md) §13.7 and implemented in the working tree on top of the ACT-1021 amendment, with the match-seam retirement that fixes ACT-1027 (user-approved for S122). `dev`'s release gate and affected e2e pass; V2 passed with the ACT-1024 cells and both ACT-1027 faces GREEN, and review found no blocking finding; K4 is complete and `qa` judged it adequate; user acceptance is pending. ACT-1026's leak is exposed on the mutate branch and is carried, as is ACT-1028 |
| ACT-1037 `vec-set` index guard | `compiler/vec_codegen.rs`, with the wrapper cells beside `compiler/control_flow/fn_as_value.rs` | designed at §9; the user approved the fix for S122. Built in the working tree; review found no blocking finding; `qa` judged it adequately evidenced and closed ACT-1037 ([closure record](../../tests/plan/s122-evidence-delta.md#act-1037--vec-set-bounds-check-closed)), with the `--link` GREEN resting on `test`'s W3 run and re-observed by W4's full suite; user acceptance is pending |

No `tests/` path is part of the backend reservation. Any actual affected CLIF
golden is test-owned and is selected from the produced diff, not predicted from
file names. Dependency pauses do not release the backend owner.

## 2. Canonical result-root use — 0898

`compile_to_module` now derives `result_roots` through the canonical projection:

```rust
bodies
    .iter()
    .map(|body| body.ty().result_root().clone())
```

The proactive drop-glue request loop and `CompilationArtifacts.drop_glues`
remain unchanged. This is the same one-hop rule already tested in
`cranelisp-types`: a well-formed non-empty `primitives/IO a` yields `a`; every
other type, including malformed/nullary IO, remains itself. Backend neither
normalizes recursively nor adds a second validation policy.

The delivered changed-call-site unit compiles an owning `IO` result in a fixture where no
other body seam requests the inner glue, and observes the inner result-root key
in the artifacts. A non-IO owning result is the control. The types unit battery
remains the semantic authority; the backend unit proves only that
`compile_to_module` supplies the right argument to the existing glue registry.
No subprocess test is added for code deduplication.

## 3. Shared Vec nullary-tag guard — 0906

`heap::emit_rc_inc_guarded(builder, module, ptr)` already owns the complete
guarded atomic increment. Its private lower helper
`emit_nullary_skip_guard` owns the unsigned
`ptr < NULLARY_TAG_THRESHOLD` decision and routes bare tags directly to the
continuation. Both former hand-written Vec copies now route through the existing
high-level emitter:

1. `build_elem_inc_fn` calls `heap::emit_rc_inc_guarded` in its `guarded` arm,
   then returns the original value;
2. the four call sites of the local `vec_codegen::emit_guarded_rc_inc` call
   `heap::emit_rc_inc_guarded` instead, and the local wrapper deletes.

`NULLARY_THRESHOLD_I64` has left `vec_codegen.rs`'s imports. The lower
`emit_nullary_skip_guard` remains private to `heap.rs`; no new backend helper
visibility is needed. This is the S122 source-backed narrowing of
the S121 one-prologue ruling ([non-concrete-release-contract.md](non-concrete-release-contract.md) §3.6).

The four callers of `emit_guarded_rc_inc` continue to derive `Mixed` from the
element's heap category. `build_elem_inc_fn` keeps its existing category-derived
guard selection. The fold must not add an independent caller-authored polarity
or infer pointerhood from value magnitude outside the shared helper.

The heap inc/dec consumers and both former Vec copies now share one comparison
and branch direction through the same guarded-inc emitter. The existing control-flow walker
`assert_threshold_guarded_rmws` is reused for the two changed Vec emissions
(moved into test support only if visibility requires it). It must prove that
each RC operation is on the not-taken arm of `ptr < threshold`, so counting the
threshold constant is insufficient. Existing scalar and temporary-element
controls remain unchanged.

The fold can change Cranelift block creation order for the two former copies,
so CLIF block labels may change while behavior does not. Module evidence is
green. The scoped golden re-baselines attribute only canonical frame renames
and the Q4 clause release, with no 0906 instruction change, and the goldens
pass in the last full run
([QA allocation](../../tests/plan/s122-evidence-delta.md#final-integration-failures--classification-and-allocation),
[acceptance basis](../../tests/plan/s122-evidence-delta.md#phase-5-acceptance-reconciliation-2026-09-27)).
A broad baseline refresh or semantic inference from textual identity is a
review reject.

## 4. Typed `consume_closure` fixture

The launch-continuation regression fixture in
`compiler/control_flow/launch.rs` now adapts its transferred raw fixture owner
immediately before the typed Rust call:

```rust
// SAFETY: the fixture has transferred the continuation owner out of the
// deliberately unconsumed Bind node and consumes it exactly once below.
let cont = unsafe { cranelisp_intrinsics::handle::Owned::from_abi(cont_ptr) };
cranelisp_intrinsics::drop::consume_closure(cont);
```

The delivered fixture constructs the handle immediately before the call; it
does not copy, store or convert it back to raw. The existing fixture remains the behavioral evidence:
after invoking the continuation and consuming its closure owner, the captured
String survives because the consuming-call increment balances closure drop.
This is a test-source adaptation to the approved Rust contract. Backend-emitted
closure-drop imports and their `extern "C" fn(i64)` ABI remain raw and unchanged.

## 5. Current record and evidence tails

These dispositions prevent stale titles from enlarging the selected source
change. They do not delete filings or weaken their surviving evidence needs.

| Records | Current disposition in this backend visit |
|---|---|
| 0898, 0906 | Delivered: backend source, focused module evidence and solution-golden evidence (§3). Both are retired; `dev`(backend) re-verified 0906 against source and deleted it under K3 on 2026-09-30. Neither record licenses a broader refresh. |
| 0637 | Borrowed-sibling cache validation and its out-of-range/highest-legal-slot unit already exist. Evidence/record reconciliation only; no backend change. |
| 0747 | The S121 one-finder consolidation is superseded by the current slot-identity and carrier-keyed designs. The three functions answer different questions and remain separate; §5.1 is the final design disposition, with no backend source change. |
| 0761, 0781, 0782 | Existing ownership-flow and match/scope guards carry the delivered behavior. QA/test reconcile locus and coverage tails; backend does not reimplement the fixes. |
| 0891, 0903, 0916, 0917, 0931 | Historical template/TCO/frame mechanisms are partly superseded. The current `signature_heap_category` residual fallback is not changed in this selected pass. QA first remeasures the exact current corpus/CLIF condition; any surviving violation returns to its attributed producer/backend design rather than entering 0898/0906 by proximity. |
| 0900 | Defect-token granularity is test-owned maintenance and has no backend source consequence. |
| 0907, 0934 | Tag-directed IO disposal, the ABI-10 Pure witness, backend construction/adoption stamps, and their backend units are delivered. Unrun-Bind/cancellation evidence is reconciled by QA/runtime owners. The current sequence-IO RED is not attributed to these mechanisms. |
| 0915 | Carried to S123 under K9 (C5) in the [approved disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30). The display shape alone does not establish doubled or mangled public diagnostics, and no legitimate stable public codegen-failure trigger is known. Preserve the existing diagnostic until that condition is observable; do not redesign it from an unarmed witness. |

### 5.1 0747 — retire the manufactured consolidation

The current source no longer supports the premise that three ad-hoc finders
answer one value-flow fact:

- `return_var_in_scope` returns an exact `SlotRef` for the latest same-frame
  binder. Scope cleanup needs this identity because repeated/shadowed names can
  own different release obligations;
- `return_cow_source_in_scope` recognizes only a carrier-keyed tail COW source
  in the current frame and returns its `Symbol` for the existing COW ownership
  decision;
- `operand_live_binding_root` traces alias provenance through `Let` and
  forwarding `Match` across any live frame. It deliberately returns a name and
  is not a cleanup-slot selector.

The S121 reach-class enum would combine distinct output identities, liveness
domains, and consumer thresholds without removing a duplicated determinant.
It would need adapters back to `SlotRef` and `Symbol`, recreate scope queries at
the consumers, and enlarge the shadowing/borrow proof surface. That cost buys no
behavioral or emission change. The original contradiction is therefore resolved
by retiring the consolidation requirement, not by choosing either of its
byte-identity compromises. The current three functions are the smallest
truthful design.

No new test mirrors this no-change disposition. Existing `scope_chain` tests
pin repeated-name and shadow identity, `return_cow_source_tests` pin the
carrier-keyed current-frame cases, and
`binding_indirection_classifier_tests` pin the wider provenance traversal.
Review checks that these remain separate by purpose and that no name-only
cleanup skip replaces `SlotRef`. The 0747 record can close through document and
evidence reconciliation; no user-facing behavior or prior public contract is
changed.

The Phase-5 stop is explicit: generic-replacement and sequence-IO mechanisms
remain unassigned until their existing public RED/control pairs yield a bounded
reproduction and source attribution. This backend visit must not use 0898,
0906, a stale IO record, or a type resemblance to guess either correction.

## 6. Evidence and review exit

Focused run `4dbc0fbe-7b3f-4fce-bb45-dca42c492dba` passes the four selected
result-root, Vec-polarity and typed-launch rows. Full backend run
`cb4a87e5` passes 586/586. Compile and format checks pass. Clippy reports the
14 existing backend warnings; strict workspace lint remains blocked by
pre-existing types/backend findings rather than a new selected-slice warning.

The completed independent runtime review covered:

- the 0898 changed-call-site unit and the existing types helper evidence;
- the delivered shared guard's control-flow polarity observations for both Vec
  emission shapes;
- the behaviorally unchanged launch-continuation fixture after its typed call adaptation;
- Q4's selected-arm parameter carriage and compilation-local actual match-owner
  outcome, including the focused and public balance observations;
- the relevant existing record-tail evidence, cited rather than duplicated;
- the delivered backend local checks.

Q5's paired after-state is measured. The fixed-session residual fell from 1143
to 46 on the matched input, library, configuration and build posture. QA keeps
the 46 as an unclassified diagnostic, not a gate, and does not call it harmless
or a proved leak
([runtime checkpoint](../../tests/plan/s122-evidence-delta.md#runtime-evidence-checkpoint--matched-residual-and-golden-limit)).
A zero-session-residue claim would need that provenance first. QA's K4 visit
closed the remaining evidence tail, the final generated API confirmation and
the integrated suite ([K4 record](../../tests/plan/s122-evidence-delta.md#final-test-visit-k4--record-and-phase-5-adequacy-2026-09-30)).

The accepted slice excludes new helper visibility, a new result-root rule, any
emitted ABI change caused by the Rust handle migration, a third nullary-tag guard
spelling, a broad CLIF refresh, or an unattributed generic/IO fix. No concrete
API gap is open: `result_root`, the shared guard shape, and the approved `Owned`
constructor are sufficient.

## 7. Delivered Q4 macro alias correction

QA's [existing Q4 public pair](../../tests/plan/s122-evidence-delta.md#q4-remaining-alias-residual-after-host-migration)
previously passed the nullary expansion but retained one cell for the
one-argument identity macro. The pre-correction CLIF for
`ident$macro-clause$0` contains two retains of the extracted returned child: one
inside the matching constructor arm and one at the function-return join. The
same function consumes the argument-list root once. This was an acceptance
failure under [`macro-turn-ownership.md` Rule 0](../int/macro-turn-ownership.md#rule-0--the-macro-clause-abi-declares-its-ownership-it-is-never-inferred),
and supplied the correction's discriminator, not a permitted ABI residual.

The generated-label lookup was a real backend defect but was not the source of
either retain. `collect_compile_targets` resolves the
authoritative `CallableTarget::MacroClause` arm and reconstructs the executable
definition as `ident$macro-clause$0`; `defn_param_types` then looks up that label
as a table binding even though the scheme is owned by the parent macro's selected
clause. This exact body recovers the same `(SList Sexp)` type from the typed
`__args__` match scrutinee, so parameter cleanup remained present. The delivered
correction carries the already-selected arm's scheme parameter types in
lockstep from compile-target projection into parameter binding and retires the
label-based relookup. It changes no macro ABI, public type, or crate boundary.

The two retain sites have different local reasons. The constructor arm must
upgrade the borrowed extracted `Sexp` before the argument-list owner is
released. The later function-return protection does not know that every normal
edge into this match merge already carries an independently owned result, so it
protects the same child again. Do not remove the arm upgrade and do not insert a
balancing release. The delivered correction uses the existing ownership handoff:

- match lowering reports whether every normal outgoing arm has already
  materialized or transferred an independent result owner after its arm-local
  cleanup; a non-returning panic edge does not weaken that result;
- the enclosing return-protection decision consumes that outcome and suppresses
  its retain only when all normal match paths carry an independent owner;
- any arm that forwards a borrowed view of a still-live outer binding without
  materialization keeps the conservative outer protection.

The outcome comes from the same per-arm lifetime and protection operation that
emits the CLIF: match lowering records whether protection actually established
an independent owner, and the enclosing return decision reads that
compilation-local result. It does not predict ownership from syntax. The
carrier remains backend-private and compilation-local; no `cranelisp-types`,
cache, public API, emitted-call ABI or macro-clause convention changes.

The pre-correction backend module observation compiles the existing
identity clause and its existing constructor-result/nullary control through the
real `CallableTarget::MacroClause` projection. It records the selected arm
scheme, bound parameter heap category, absent ownership summary, and the owner
decision at both retain sites. The retained observer summary is
`/tmp/s122-backend-q4-observer-summary-dc78ddbe.log`: it confirms the required
arm-local upgrade followed by the redundant outer protection and the generated
label's absence as a table binding.

After correction, the same module row records exactly one child retain on the
identity path, one argument-root consume after result materialization, and no
new retain on the constructor-result/nullary control. The affected focused set
passes 19/19 in run `7777a8dc-2485-4e44-ab5c-11f5a75ad7c7`, and QA's existing
public pair passes 2/2 in run `0ce70208-1654-41a3-887f-89431a0b7b84`. The
independent backend review found no material defect. No additional mode matrix
or public seam is added. Solution-golden evidence (§3) and the Q5 paired
measurement (§6) are complete; final API confirmation and integrated macro/host
evidence remain open.

## 8. IOR-5 — an IO-combinator result is fresh

The correction is implemented. The two IOR-5 public balance cells and IOR-2
pass with zero marginal residual. [QA's evidence plan](../../tests/plan/s122-evidence-delta.md)
owns acceptance and the remaining scope limits.

### 8.1 Mechanism, read at source

The pre-fix failure, confirmed by emitted-code observation:

- `bind`, `select`, `race` and `sleep` resolve as `ResolvedCall::BuiltinFn`,
  and `compile_builtin_fn_call` lowers them inline. Each lowering allocates a
  new IO node at rc=1. The node takes over its operands under the consuming
  convention: a `Var` operand is retained and a temporary is transferred. The
  node never returns an operand.
- `value_provenance_with_calls` classifies such an `Apply` as
  `OwnedTemporary`, because `call_returns_owned_reference` answers `false` for
  every `Some(_)` carrier other than `SigDispatch`/`TraitMethod`.
- `protect_return_value` retains the result whenever the exiting frame owns a
  heap binding and `body_has_independent_result` is false. The caller releases
  the node once. The protective retain therefore strands the node and
  everything it owns, and nothing balances it.
- Before the correction, CLIF showed the extra retain on the new Bind node
  before the binding release; the inline control had none (§8.4).

### 8.2 Correction

- **Classify the IO-combinator carrier as `Fresh` in `value_provenance_with_calls`.**
  Physical freshness is the true fact. `TransferredCall` would claim a possible
  parameter alias that does not exist.
- **One classification, used by every reader of this fact.** The backend-private
  `apply.rs::IoCombinator` classifies the four `BuiltinFn` carriers.
  Three readers consume it:
  - the spark exclusion;
  - `compile_builtin_fn_call`'s interceptors, matched exhaustively;
  - the provenance `Apply` arm, which matches every variant to `Fresh` with no
    wildcard.

  With this shape, adding a combinator whose lowering does not mint a node is a
  compile-time decision, not a silent claim (Principles 07 and 24).
- **Identity comes from the carrier, not the spelling.** An `Apply` whose
  callee is spelled `bind` but whose carrier is not `BuiltinFn` is not
  classified by this rule.
- **The rule does not extend to other builtins.** Inline Vec operations can
  return an existing element or an in-place COW source, so they stay
  `OwnedTemporary`. An extern shim such as `string-identity` may return its
  argument, so it is never `Fresh`. Its owned-transfer result is classified by
  the entry-convention derivation
  ([non-concrete-release-contract.md](non-concrete-release-contract.md) §7.6),
  not by this rule.
- **Joins stay conservative.** `(if c (bind p k) p)` joins to `NotOwnedHere`,
  so its protect remains. Per-arm protection is out of scope.

### 8.3 Behavioural reach

- `yields_owned_temporary` already accepts `Fresh`, and `is_fresh_construction`
  is used only by tests.
- The only emitted change is therefore the one read by
  `body_has_independent_result`: protect elision at function, binding, lambda,
  continuation and match-arm exits, including `match_codegen`'s
  independent-arm plan.
- Nothing else changes: no `cranelisp-types` change, no public API or
  `public-api.txt` delta, no emitted-call ABI change and no intrinsics or
  platform change.
- There is no cache-schema bump. The elision is confined to each frame's own
  emission and moves no convention a cached object shares with separately
  compiled code
  ([bump rule](module-caching.md#142-cache_schema_version-ownership)).
- CLIF goldens containing a heap-binding scope that returns an IO combinator
  change, with attribution to IOR-5 only.

### 8.4 Evidence and falsifiers

- Pre-fix CLIF showed an extra `atomic_rmw add` on the returned Bind node's
  RC word in the let-bound subject, absent in the inline control. The corrected
  CLIF removes only that pointer calculation, increment constant and retain.
- The classification and emitted-retain module cells were observed red before
  the provenance correction, then green. They live in
  `crates/cranelisp-backend/src/compiler/apply/io_combinator_freshness_tests.rs`.
- Borrowed-result controls pass before and after: the new mixed-join cell
  observes `NotOwnedHere` classification; existing return-ownership CLIF
  evidence observes the protective retain. Non-combinator builtins stay
  `OwnedTemporary`, and a
  `bind` spelling without the builtin carrier does not classify as `Fresh`.
- Both IOR-5 cells and IOR-2 pass with zero marginal residual. A check trip,
  double release or changed value refutes the correction.
- The reused-Pure program returns 7 in run, linked and REPL observations with
  checks armed. Existing CLIF goldens pass without regeneration.

## 9. ACT-1037 — `vec-set` index guard

Built in S122 Phase 6b and accepted by independent review with no blocking
finding. The requirement is `spec/12-runtime.md` §12.7.2.1. `qa` closed
ACT-1037 on 2026-10-01 and deleted the filing; [its closure record](../../tests/plan/s122-evidence-delta.md#act-1037--vec-set-bounds-check-closed)
holds the reproductions, attribution and evidence. Every cell went RED for the
intended reason and is GREEN in every mode; the `--link` leg's GREEN is
`test`'s W3 observation, which W4's full suite re-observes. The standing rule
is [backend.md §7](backend.md#7-runtime-failure), "One Vec index guard".

### 9.1 Mechanism, read at source

- `emit_vec_set_cow_core`'s in-place arm computes `data_ptr + idx*8`, then
  decrements the old element and stores the new one there, with no index
  comparison.
- `compile_vec_set`'s non-last-use arm calls `vec-set-copy` directly. The helper
  (`cranelisp-intrinsics` `vec_runtime.rs::vec_set_copy`) stores the new element
  only at an in-range index. Otherwise it returns an unchanged copy, and the
  new element's reference is lost.
- `emit_vec_query_into`'s `vec-set` arm reaches the same core, so value-position
  and auto-curry uses share the fault.
- Only `emit_vec_get_core` compares the index. The CLIF in ACT-1037 confirms
  the difference.

### 9.2 Correction

- **Share `vec-get`'s guard.** Extract the comparison, panic block and message
  from `emit_vec_get_core` without changing `vec-get`'s emitted instructions.
  The `vec-set` core then opens with the same guard. It needs the
  `runtime/panic` entry, resolved as `vec-get`'s callers already resolve it: a
  missing declaration is a located codegen error.
- **Fold the copy-only site into the core.** The core's uniqueness input
  becomes one closed choice with three cases. Each carries only what its arms
  need:

  | Case | Emitted arms | Source release on copy |
  |---|---|---|
  | Proven unique, with no separate owner | in place only; no rc probe | none, because the copy arm is not emitted |
  | Dynamic | rc probe, in place or copy | the owned or borrowed polarity, as today |
  | Known shared (not last use) | copy only; no probe, merge or reuse tally | none, because the source is not consumed |

  - The proven-unique case also requires that the source have no separate
    owner, which is the condition under which it would classify `Owned`. It
    never retains the source, so a proven-unique source that a slot also
    releases would lose a needed retain. Such a source takes the dynamic case.
    On today's inputs no site moves: every node carrying the uniqueness proof
    yields an owned temporary. The condition stops typecheck's proof and the
    backend's ownership classification from disagreeing silently.
  - A known-shared site with an owned-source release is then inexpressible
    (Principles 07, 18 and 20).
  - Afterwards `vec-set-copy` is named by exactly one backend emission site,
    inside the core.
- **Emitted change.** Every `vec-set` lowering gains the guard.
  - The known-shared case emits the previous copy-only instructions after the
    guard.
  - The proven-unique case no longer emits its unreachable copy block, so its
    instructions change beyond the guard. Runtime reuse counts do not change,
    because the block never ran.
- **Unchanged.**
  - No `cranelisp-types` or public API change, and no `public-api.txt` delta.
  - No emitted-call ABI, intrinsics or platform change.
  - No cache-schema bump. The guard is confined to each frame's own emission
    ([bump rule](module-caching.md#142-cache_schema_version-ownership)).
- **Goldens.** CLIF goldens that contain `vec-set` change, attributed to
  ACT-1037, and `test` re-baselines them. Review found no golden under
  `tests/` containing a proven-unique site. `vec-get` goldens stay
  byte-identical. A `vec-get` diff refutes the extraction.
- **Not in scope.** The sentinel-escape crash of
  [backend.md §7](backend.md#7-runtime-failure) (ACT-1040, §10) survives this
  correction.
  After `(defn g [v i] (vec-set v i 99))`, the guard raises the panic inside
  `g`, but a caller that computes `(vec-len (g [1 2 3] 9))` then dereferences
  the sentinel. ACT-1037's cells consume the result inside the panicking
  function, so they do not reach it.
- **Routed, not required.** The helper's caller precondition,
  `0 <= idx < len`, is unstated in the helper's rustdoc and in the
  [catalog convention](../arch/bounded-contexts.md) row for `vec-set-copy`.
  Those carriers belong to `dev`(intrinsics) and `arch`. The correction does
  not depend on them.

### 9.3 Seam and module evidence

`dev`(backend) changed `crates/cranelisp-backend/src/compiler/vec_codegen.rs`:

- `emit_vec_get_core`: extract the guard.
- `emit_vec_set_cow_core` and its operand bundle: add the guard and the
  three-case uniqueness input.
- `compile_vec_set`: route the non-last-use arm through the core.
- `emit_vec_query_into`: pass the dynamic case.

Module cells, observed RED on the pre-fix tree in the same change-set:

- **Execution, per case.** New cells in `vec_codegen/` cover the
  proven-unique, dynamic and known-shared cases. Each uses the indices `-1`,
  the length and `100000000`, expects the exact §12.7.2.1 message, and has an
  in-range control that returns the updated value.
  - On the pre-fix tree the unique cases corrupt or crash, and the known-shared
    case returns silently.
- **Heap elements.** Repeat the in-place case with String elements. The wild
  old-element decrement is its unsafe step.
- **Wrapper.** Add out-of-range and in-range cells for value-position
  `vec-set` beside `vec_set_as_value_wrapper_inline_emits_and_updates_element`
  in `control_flow/fn_as_value/value_use_tests.rs`.
- **Structure.** For each case, the emitted CLIF shows the index comparison
  against the loaded length and the `runtime/panic` call before the element
  store and before the `vec-set-copy` call. This holds in the proven-unique
  case, where the rc probe is absent.
- **Negative.**
  - `vec-get`'s emitted CLIF is unchanged.
  - `cow_polarity_tests.rs` keeps its release and retain counts, with the
    fixture declaring `runtime/panic`.
  - The in-range RC cells in `vec_set_rc_tests.rs` and the `cow_*` modules
    stay green.
- **Acceptance.** ACT-1037's cells turn GREEN in every mode, and C1 and C2
  still pass. `qa` judged this met on 2026-10-01
  ([closure record](../../tests/plan/s122-evidence-delta.md#act-1037--vec-set-bounds-check-closed)); the `--link` leg rests on `test`'s W3 run.

## 10. ACT-1040 — panic propagation (proposal)

**Status: proposal, not adopted.** The user decides between a correction in
S122 and a carry to S123. [backend.md §7](backend.md#7-runtime-failure) stays the
standing rule until then, with its falsification recorded there. The
requirements are `spec/12-runtime.md` §12.7.2, §12.7.4 and §12.7.8 items 1, 2, 4
and 5. [ACT-1040](../../sprints/actions/ACT-1040-panic-sentinel-reaches-heap-consumer-intake.md)
holds `qa`'s cells, attribution and allocation.

### 10.1 Mechanism, read at source

- The panic shape returns `0` from the faulting frame only. No emitted code
  reads the error slot. After the call instruction, the result from each
  call primitive in `compiler/apply.rs` flows straight into post-call
  decrements, the closure-result protecting increment and the consumer. The
  call primitives are the direct, GOT-indirect, closure and extern calls,
  including `cranelisp_ivar_force`.
- Every slot reader is outside JIT code: the int hosts,
  `cranelisp_run_program`'s pre-IO and post-IO peeks, `catch-runtime-error`,
  the IO trampoline's peek after each continuation, and the IVar ferry.
- `runtime/panic` overwrites the slot on every raise. So a later panic raised
  while a frame is still using the sentinel replaces the first message.
- Two scalar faces are not among ACT-1040's cells. Observed 2026-10-01 with a
  copy of the debug binary built after `88bbbd12` and the primitives-only
  prelude, after `(defn lookup [v i] (vec-get v i))`:
  - Q1: `(defn scan [v i] (if (lt-i64 (lookup v i) 100) (scan v (add-i64 i 1)) i))`,
    then `(scan [1 2] 0)`. The REPL never returns: each iteration panics and
    continues with `0`.
  - Q2: `(div-i64 10 (lookup [1 2] 9))` reports `division by zero`, not the
    index panic.
  - Both are memory-safe, but they violate §12.7.2 ("cannot resume") and
    §12.7.4.1.

### 10.2 The fact every option rests on

- Every JIT function returns one `i64`. Every raising frame returns `0` with
  the slot set:
  - the panic shape and the trap stub;
  - the out-of-line `div-i64` primitive and `quote-sexp`'s error sentinel;
  - `cranelisp_ivar_force`, which passes the thunk's result through;
  - the trampoline.
- **For an `AlwaysHeap` result, `0` is not an inhabitant.** Allocation never
  yields null, and stack placement yields a frame address. So a `0` there
  proves a pending panic without reading the slot.
- For `NeverHeap`, `Value` and `Mixed` results, `0` is an ordinary value:
  `Int` 0, `false`, `0.0` or nullary tag 0. Only the slot can tell those apart.
  A `Mixed` consumer tests the nullary threshold before any dereference, so
  it reads `0` as a tag. That is why these faces are not memory-unsafe.

### 10.3 Options

| | Mechanism | Gate | Cache | Size | Closes |
|---|---|---|---|---|---|
| **A0** | Typed zero test after each `AlwaysHeap` call | none | no bump | about ACT-1037's scale | every ACT-1040 cell and the memory-unsafe face |
| **A** | A0, plus a slot query on a zero result of any other category | arch + user (a new intrinsic) | no bump | A0 plus a small increment | A0's scope, Q1 and Q2 |
| C | `runtime/panic` jumps non-locally to the nearest boundary | arch + user (the panic ABI and new boundary API) | none | large, 3–4 crates | all, with a UB risk |
| D | Native unwinding through Cranelift unwind tables | arch + user (public API and technology) | bump | multi-sprint | all, and enables cleanup |

#### A0 — typed zero-sentinel propagation

- **Mechanism.** Immediately after the call instruction, before any post-call
  decrement, protecting increment or consumer, a call whose result category
  is `AlwaysHeap` branches on the result. `0` goes to one shared block per
  function that returns `0`. The frame's owned values leak, which
  §12.7.4.1 and §12.7.8 item 4 permit. The result is used only in the
  non-zero continuation.
  - Other categories get no test.
  - An emitted wrapper whose only use of the result is `return` needs no test.
    Its Decision-24 parameter decrements act on live values, and the return
    passes the `0` on. Examples are the curry and value-position adapters and
    the GOT-slot literal wrapper.
  - The category comes from the `Apply` node's type through the one
    category derivation. That type is always present at the single dispatch
    in `fn_compiler.rs`.
- **Surfaces.** Backend emission only:
  - the four call primitives in `compiler/apply.rs`, each taking the result
    category as a required input so that no caller can omit it;
  - the three `cranelisp_ivar_force` sites;
  - the trace wrapper, which formats the original call's result.
- **Gate.** None. No public-API, `cranelisp-types`, intrinsics, platform or
  emitted-call ABI change, and `runtime/panic` is unchanged. The existing
  sentinel convention gains its first in-code reader.
- **Cache.** No bump. The change is confined to each caller frame's emission
  ([bump rule](module-caching.md#142-cache_schema_version-ownership)). A stale
  frame behaves as today until its module rebuilds, and a rebuilt compiler
  invalidates it through build identity and the compiler fingerprint.
- **Size.** Roughly 100–150 source lines and 150–250 module-test lines in one
  `dev`(backend) pass. `test` re-baselines the CLIF goldens that contain an
  `AlwaysHeap` call, attributed to ACT-1040. It runs after ACT-1037 lands,
  because both touch the backend crate.
- **Evidence.**
  - *Module, RED first.* Execution cells: a String-returning callee panics,
    and the caller consumes the result, releases it unused, or reaches it
    through the GOT, closure and IVar-force paths. The panic is reported with
    no fault. Structure cells: the zero test precedes every post-call RC
    operation. `NeverHeap`, `Value` and `Mixed` calls and tail-returning
    wrappers carry no test. In-range controls keep their values and RC counts.
  - *End to end.* `test`'s allocated R1–R6 cells in every mode, the C2 and C3
    controls, and the `vec-set` sibling after ACT-1037.
  - *Non-null premise.* A false propagation silently truncates an evaluation,
    so the full suite measures the premise. Prove detection with a one-off
    mutant that tests every category: the suite must go RED.
  - *Cost.* One compare-and-branch on a register per such call. Check the
    order of magnitude once on the exemplar, with stats off.
- **Residual.**
  - Q1 and Q2 remain. They are pre-existing and not memory-unsafe, but they
    violate §12.7.2 and §12.7.4.1. `qa` should take them in as a separate
    intake, since ACT-1040's cells do not cover them.
  - A heap type that the category seam misclassifies as `Mixed` gets no test.
    This is asserted with a falsifier: a `Mixed` consumer that dereferences
    without the threshold test.
  - Only `catch-runtime-error` clears the trace guard on a panic; the int
    hosts do not. A callee panic inside a `(trace …)` body in the REPL
    can leave the guard set. This is read at source and not observed, and
    in-frame panics share it today. It routes to `design`(intrinsics).
  - Optional companion: first-error-wins in `runtime/panic` would close Q2
    under A0 without an API change. It is `design`(intrinsics)'s decision, and
    `arch` must confirm it is not a panic-ABI change.

#### A — complete propagation

- **Mechanism.** A0, plus one change: a zero result of any other category
  calls a new slot-query intrinsic that reads the slot without clearing it.
  If a panic is pending, the frame propagates. A non-zero result pays nothing
  more than under A0.
- **Surfaces.**
  - `cranelisp-intrinsics`: one exported function beside the slot, and its
    catalog entry.
  - Backend: the slow path in A0's helper.
  - The `--link` bundle must export the new symbol.
- **Gate.** The inter-crate public-API user gate applies. There is a new
  catalog entry, a new public export in the intrinsics `panic` module, and a
  new consumer edge from backend emission. `arch` presents the delta. The
  slot gains a reader, but `runtime/panic`'s contract is unchanged. `arch`
  rules whether that counts as a panic-ABI change.
- **Cache.** No bump. Old objects do not import the symbol, and the runtime
  always ships with its compiler. The evidence must show that no sidecar
  persists a table derived from the catalog.
- **Size.** A0 plus about 20 intrinsics lines and about 30 backend lines, with
  cells, the `arch` packet, user approval and confirmation of the generated
  `public-api.txt` diff. A0's work is reused whole.
- **Evidence.**
  - A0's evidence.
  - Q1 and Q2 as RED-then-GREEN cells in every mode.
  - A module cell showing that a zero `Int` result with an empty slot
    continues.
  - A performance measurement inside the design window. `false`, `0` and
    nullary tag 0 are common results, so the slot query's frequency must be
    measured, not assumed. If it is material, an exported process-wide
    pending counter can filter the query. That counter falls under the same
    gate.
- **Residual.** The leaks on propagation, which the spec permits. The
  category seam no longer matters for propagation.

#### C — non-local exit (rejected)

- `runtime/panic` stops returning and jumps to the innermost boundary on the
  thread. The boundaries are:
  - the int hosts and the expander;
  - `cranelisp_run_program` and `catch-runtime-error`;
  - trampoline continuation calls;
  - IVar thunk runs;
  - the strand and reactor completion boundaries.
- There is no codegen change and no cache impact.
- It is a panic-ABI change with new boundary API across intrinsics, primitives
  and int, so it needs arch and user approval.
- Rust does not support returns-twice calls. The project's existing
  `sigsetjmp` uses recover only from faults.
- Soundness requires that no skipped Rust frame holds a pending destructor.
  Examples are IVar's spark-depth and peak guards and the primitives' `Owned`
  locals. Nothing can make that structural, and a missed frame corrupts guard
  or lock state.

#### D — native unwinding (potential extension)

- **Mechanism.**
  - Register Cranelift unwind information for JIT code.
  - Emit `.eh_frame` into each object, which needs a new dependency.
  - Make `runtime/panic` and every export that JIT code calls `C-unwind`.
  - Catch the panic at the boundaries.
- **What it buys.** Rust destructors run, the non-panic path costs nothing,
  and landing pads could later remove the leak.
- **What it costs.** A public-API and technology change, a
  `CACHE_SCHEMA_VERSION` bump, and multi-sprint work.
- **Triggers.**
  - A spec requirement for panic locations or backtraces.
  - Leaks accumulating in long-running supervised strands, such as a
    §12.7.9 server with frequent faulted requests.
  - A's measured cost exceeding budget.

#### Rejected without costing

- *Sentinel-tolerant consumers.* Every dereference site would need a guard,
  and the evaluation would still resume, against §12.7.2.
- *Host fault recovery.* It turns the panic into a signal, against §12.7.8
  item 1. `catch-runtime-error` would still fail, and the recovery skips Rust
  frames as C does.

### 10.4 Recommendation

- Land **A0 in S122**, after ACT-1037.
  - It closes every ACT-1040 cell and the memory-unsafe face in every mode.
  - It needs no gate and no cache bump, at about ACT-1037's scale.
- `qa` takes Q1 and Q2 in as a separate intake.
- **Carry A to S123** through the `arch` packet and the user gate. It finishes
  on A0's seam.
- Record D as a potential extension with the triggers above. Reject C.
- Carrying ACT-1040 whole to S123 would ship the release compiler with a
  reachable null dereference that also defeats the only recovery construct.
