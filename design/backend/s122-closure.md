# S122 selected backend closure

Owner: `/design` (backend). Status: **Selected backend runtime-consumer and Q4
alias corrections delivered and independently reviewed; solution-golden,
final Q5/API and integrated acceptance pending**. The
Phase-3 scope and existing contracts were authorized 2026-09-09 against
compiler checkpoint `dc78ddbe` and package checkpoint `98436c9`; this design
has completed independent runtime review with no material findings. This
document is the current entry point for the delivered selected S122 work in
`crates/cranelisp-backend/`. It does not reopen the S121 backend visit or assign
the current generic-replacement and sequence-IO failures.

The bounded context remains `design/arch/bounded-contexts.md` §3. The selected
change has no new public backend API, generated backend baseline delta, emitted
raw ABI, cache schema, platform ABI, persistent representation, or compiler
mode. It consumes `ConcreteType::result_root()` and the approved intrinsics
`Owned` contract. The separate uniform executable-identity migration and cache
schema 29 state remain governed by their existing architecture record; this
slice neither changes nor re-dispositions them.

## 1. Delivered backend slice and remaining gates

The selected source and module-test work is delivered and independently
reviewed. Scoped solution-golden selection, final Q5/API evidence and
integrated acceptance remain open:

| Obligation | Backend path | Dependency |
|---|---|---|
| 0898 result-root consumer | `crates/cranelisp-backend/src/lib.rs` | delivered using `ConcreteType::result_root()` |
| 0906 shared nullary-tag guard | `crates/cranelisp-backend/src/compiler/vec_codegen.rs` | delivered through `heap::emit_rc_inc_guarded`, which already owns the lower guard |
| Typed closure fixture | test module in `crates/cranelisp-backend/src/compiler/control_flow/launch.rs` | delivered using intrinsics `handle::Owned` and `drop::consume_closure(Owned)` |
| Source guidance affected by the helper census | `crates/cranelisp-backend/CLAUDE.md` | delivered beside implementation |
| Q4 macro returned-alias ownership | selected-arm projection in `crates/cranelisp-backend/src/lib.rs`; match/return ownership in `crates/cranelisp-backend/src/compiler/` | delivered with focused and public evidence; independently reviewed with no material finding |

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
`s121-c4-visit.md` §8.2.

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
green, but actual solution-golden selection remains pending until the root
compiler consumers migrate and the complete attributed diff can be inspected.
Re-baseline only affected functions/fixtures with attribution to 0906. A broad
baseline refresh or semantic inference from textual identity is a review reject.

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
| 0898, 0906 | Backend source and focused module evidence are delivered. Actual solution-golden selection and integrated evidence remain open; neither record licenses a broader refresh. |
| 0637 | Borrowed-sibling cache validation and its out-of-range/highest-legal-slot unit already exist. Evidence/record reconciliation only; no backend change. |
| 0747 | The S121 one-finder consolidation is superseded by the current slot-identity and carrier-keyed designs. The three functions answer different questions and remain separate; §5.1 is the final design disposition, with no backend source change. |
| 0761, 0781, 0782 | Existing ownership-flow and match/scope guards carry the delivered behavior. QA/test reconcile locus and coverage tails; backend does not reimplement the fixes. |
| 0891, 0903, 0916, 0917, 0931 | Historical template/TCO/frame mechanisms are partly superseded. The current `signature_heap_category` residual fallback is not changed in this selected pass. QA first remeasures the exact current corpus/CLIF condition; any surviving violation returns to its attributed producer/backend design rather than entering 0898/0906 by proximity. |
| 0900 | Defect-token granularity is test-owned maintenance and has no backend source consequence. |
| 0907, 0934 | Tag-directed IO disposal, the ABI-10 Pure witness, backend construction/adoption stamps, and their backend units are delivered. Unrun-Bind/cancellation evidence is reconciled by QA/runtime owners. The current sequence-IO RED is not attributed to these mechanisms. |
| 0915 | The display shape alone does not establish doubled or mangled public diagnostics, and no legitimate stable public codegen-failure trigger is known. Preserve the existing diagnostic until that condition is observable; do not redesign it from an unarmed witness. |

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

The remaining evidence tail is the actual scoped solution-golden diff, final
generated API confirmation, Q5's final paired after-state after this backend
correction, and the later integrated suite allocated by QA.

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
or public seam is added. Actual solution-golden selection, Q5 remeasurement,
final API confirmation and integrated macro/host evidence remain open.
