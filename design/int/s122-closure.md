# S122 selected Binary/int closure

Owner: `/design` (int). Status: **Phase-5 correction design, active delivery
record**. The original Phase-3 scope and existing contracts were
authorized 2026-09-09
against compiler checkpoint `dc78ddbe` and package checkpoint `98436c9`; Phase
5 was authorized 2026-09-10. On 2026-09-10 the user selected §5 Option A's
private failed-codegen substitution evidence and approved the uniform
concrete-signature identity plus exact public API packet in
`design/arch/s122-overload-reorder-publication.md`. This document is the current
entry point for the selected S122 work in `src/` and
`crates/cranelisp-exe-bundle/`; it does not reopen the rest of the Binary/int
surface.

The bounded context remains `design/arch/bounded-contexts.md` §6. Existing
subsystem designs remain authoritative for their subjects. This delta records
the source-reconciled implementation shape, dependency order, evidence needs,
and the approved failed-codegen evidence choice. The types-owned identity API
and its Binary/int consumers are delivered; Binary/int adds no public boundary,
persistent schema, runtime ABI, logging guarantee, provider, or fault mode.

## 1. One continuous source reservation

One `/dev` owner retains this Binary/int reservation through dependency pauses
and Phase 5. A dependency landing is a continuation point, not a reason to
rediscover or divide the work into new tickets.

| Selected obligation | Binary/int files | Dependency or stop condition |
|---|---|---|
| Reload-demand recovery and session surface | `src/redefine.rs`, `src/session_v4/lifecycle.rs`, `src/session_v4.rs`, `src/worker.rs`; `src/eval.rs` only if the existing outcome/warning handoff needs it | Q7's source carrier, demand-only and foreign-remap module discriminators, watcher provenance, complete-plan ordering, and scoped reviews are delivered; final integrated evidence remains pending |
| Macro-call ownership | `src/marshal.rs`, `src/expander.rs`, `src/process_form/macro_clause.rs` | Binary/int's typed transfer, fixed all-Owned clause convention and host result discharge are delivered; backend's Q4 correction is reviewed and the public pair passes 2/2 |
| Shared quote classifier | `src/expander.rs`, `src/process_form/macro_resolution.rs` | Both int walkers consume `cranelisp_types::{quote_head, QuoteHead}`; quote behavior is unchanged |
| Canonical result root and `/mem` | `src/result_owner.rs`, `src/repl/commands.rs` | Both int consumers are delivered; Q6 observes the rendered heap result and the post-release counter snapshot |
| Failed-turn recovery evidence | private unit surface in `src/worker.rs` | Use the approved §5 private substitution; no production flag is authorized |
| Eval production follow-up | none selected | Open Binary/int source only if an approved live configuration proves the condition in §6 |

`crates/cranelisp-exe-bundle/` remains inside the reservation and caller census,
but the current source inspection proves no selected change there. Generic and
IO-shaped roots are not assigned to Binary/int by resemblance.

## 2. Reload restores explicit monomorphization demand

The target module's historical concrete instances are captured before its
ordinary prepared commit as data. For every admitted replaced generic base or
family—including a same-language-type body edit—select each target-module
entry in `Life::Concrete { minted_from: Some(link), .. }` whose
`link.template` belongs to that base or family. Capture the actual live storage
key beside the complete old `InstanceLink`; together they are private
preparation provenance. For an ordinary generic, project the replacement
demand from that same target and type arguments. For an overload family, first
map the old arm to the unique staged arm with the same canonical language type,
then project the demand from the staged arm and captured type arguments. Derive
the replacement key from that matched staged scheme through the approved
context-bearing `MonoDemand::instance_key`. Deduplicate by prior key and staged
demand key. `CallableArmId` is generation-local roster position; it is not
cross-generation clause correspondence or executable identity.

Source checking can leave a matched overload arm in one of two valid staged
states. A parametric arm remains a template for ordinary demand replay. A
sibling call can instead settle the arm concrete in place: the staged arm then
already carries its authoritative scheme, body and whatever metadata source
checking produced, but has no `InstanceLink` backlink. Its entry and codegen-view
`mode_summary` may still be absent. This raw source-staging state is neither a
reusable template nor the linked, ownership-complete realization required by
publication.

The Q1 control settled the replacement/instance lifecycle correction on
2026-09-10. A caller-free replacement without a prior realization returns the
new value, while the otherwise identical case with a prior concrete
realization returns the stale value. Current source also excludes `__expr` from
`ReverseIndex`, returns from `drive_t1_full_cure` when its named stale-caller
set is empty, and lets the typechecker treat a visible `Life::Concrete` at the
demand's instance key as already settled. The public control discriminates a
stale previously realized instance; the empty-caller route is a source-backed
inference rather than a directly instrumented observation.

The same-type pre-correction RED added the other required polarity: after a
concrete call realized `f [_] -> Int` with body `7`, replacing it with the same
scheme and body `42` left the old realization returning `7`; the otherwise
identical no-prior-realization control returned `42`. Capture is therefore
based on an admitted generic replacement, not only on a language-type change.

The pre-correction generic overload-family RED adds a distinct condition. The legal family
`(defn f ([:a x] 7) ([:a x :b y] 42))` realizes both clauses, then reverses the
unchanged clause roster. The old preparation path replayed an old ordinal
against the new roster and rejected it as a declined same-type demand.
The old callers still return `7` and `42` because publication never happened;
that is rollback behavior, not successful late binding. Under
`repl/spec/18-redefinition.md` §18.3 the replacement must instead publish as one
complete family and both existing callers must reach the corresponding new
bodies. No wrong-body or memory failure has been observed.

The corrected binding cadence is part of the original ordinary prepared turn:

1. check the proposed source into its ordinary unpublished staging table;
2. validate the authored replacement against the live base or family,
   including declaration class, visibility and the §18.2 blocking-dependent
   rule;
3. project the historical demand set for every admitted replaced generic base
   or family from the still-live module, capturing each actual prior key and
   old link regardless of whether its language type changed;
4. for a same-type overload family, pair each captured old arm with exactly one
   staged arm by the canonical `LanguageType` already used by the family
   redefinition guard; reject the candidate if correspondence is missing or
   ambiguous;
5. derive each staged demand key from the matched staged scheme; install an
   exact linked instance for a matched arm already settled concrete in place,
   then call `instantiate_demands` for the remaining template demands into the
   same source staging table through an int-owned cloned read world that masks
   exactly the captured prior instance keys while preserving every unrelated
   same-module and cross-module entry;
6. classify the rematerialized and declined instance keys as below, compile the
   complete base-plus-realizations candidate, and publish it once through the
   ordinary prepared transaction;
7. only after successful publication, perform the ordinary confirmation,
   introspection and backing-source updates.

This work occurs inside `prepare_cluster_commit`, before
`plan_staging_commit`, compilation or any live publication. The post-publication
`apply_redefinition_outcomes` T1 reload is not the Q1 implementation: a failure
there could no longer preserve the complete prior base-plus-realizations
candidate. Q1 adds no dependent recompilation or cascade. Persisted-source
watcher reload remains a separate path and reuses the same private
rematerialization helper with its source-or-demand staging.

A persisted reload may carry saved demands even when source checking produces
no authored staging row for the reloaded module. In that demand-only case,
preparation creates the module's empty unpublished staging table and continues
through the same demand planning, ownership completion, compilation and atomic
publication path. An empty source cluster is therefore not an early return when
reload demands remain.

A saved demand whose template owner is another module resolves against that
owner's current live generation. An ordinary target keeps its selected target;
an overload target tests the current arms and accepts exactly the one whose
scheme derives the historical caller's canonical concrete-signature key.
Missing or multiple matches reject the candidate. No prior ordinal is treated
as cross-generation identity, and no alias or secondary key registry is added.

The target-clean read world in step 5 is load-bearing. On a private clone of the
live target table, the existing absent-key `ChangeAbi` operation masks the
complete set of captured prior instance keys before constructing the
staging-first typecheck view. The replacement demand names the matched staged
arm and receives that arm's authoritative staged scheme, so neither integration
nor typecheck asks the new roster to interpret an old ordinal. Integration does
not render or parse the readable key itself.
The replacement base and newly materialized instances live in staging;
unrelated same-module callees remain visible from the cloned fallback. An old
captured instance therefore cannot satisfy the typechecker's legitimate
same-world deduplication rule. The cloned world and staging table drop on
failure; the live table, GOT cells and code owners remain untouched. No
Binary/int backend mechanism changes; backend compatibility remains in the
architecture-owned migration.

For a concrete-in-place overload arm in step 5, install the exact demand link
through the existing instance lifecycle funnel before replay. Require an
overload-arm target, a source-staged concrete body with no existing backlink or
compiled code, and agreement between the approved scheme-derived key and the
captured staged key. Carry the checked scheme, body, parameters, source AST,
callees, visibility, value-use fact and any available ownership metadata into
the linked instance, and require the lifecycle funnel to return that exact key.
If a summary is available, carry it through the existing lifecycle operation
while the entry is still staged; this copy is not proof that ownership completion
has run. Record the key as already materialized so ordinary replay cannot
instantiate its body a second time. If an exact linked instance is already present,
accept it idempotently only when its backlink equals the expected demand link.
Any mismatch or lifecycle refusal rejects the candidate before live
publication.

Both the remaining template demands and the linked concrete-in-place instances
consume the completed typecheck producer in
`design/typecheck/monomorphisation.md` §3.8.6. `instantiate_demands` runs the
private ownership pass over the same check state and staging-first world after
the successful full demand drain. That follow-on pass sees the already
materialized body even though replay filters out its demand, and completes
ownership before Binary/int plans publication. Binary/int uses the resulting
summary and must not reuse the prior instance summary or weaken the compatibility
guard. The concrete-in-place path avoids only template body re-instantiation; it
does not bypass ordinary ownership completion. Neither path changes a public
function signature, error surface, schema, or ownership toggle.

Apply the ordinary redefinition guard to the authored source before demand
injection. A successfully rematerialized key is then a derived member of that
same candidate, not a second independently authored live edit. The later
staging validation may omit only the duplicate guard application for the exact
captured keys whose `InstanceLink.template` belongs to the already-admitted
base or family. For a same-language-type base or family edit, every prior
realization must rematerialize with the same realization language and ownership
ABI and derive the same concrete-signature key. Existing same-key `PreserveAbi`
keeps its slot and displaces the prior owner through the ordinary publisher.
Any decline, key mismatch or ownership-ABI mismatch rejects the complete
original candidate before publication, even when no caller exists.

For a caller-free language-type-changing base, a rematerialized realization
whose key and ownership ABI remain compatible may preserve its slot. A changed
concrete-signature key or ownership ABI uses `ChangeAbi`, receives a fresh slot,
and retires the captured prior key in the same candidate; a declined old
instance is likewise an absent-key `ChangeAbi` retirement. This is the existing
§18.1.2 permission for a caller-free language-type-changing replacement; it does
not admit ACT-0953's stronger same-language-type ownership-ABI change. A
language-type-changing base with a named blocking dependent rejects before
rematerialization. Neither path recompiles dependents.

An unchanged overload clause may move from old arm `i` to staged arm `j`, but
the approved executable identity is the canonical authored family plus its full
concrete function signature. After semantic arm correspondence, the staged
demand derives the same key from arm `j`'s scheme. The staged binding therefore
publishes at the existing key with an updated `InstanceLink.template` backlink
to arm `j`; existing caller references and their GOT slot remain valid. The
prior key is retained separately in private preparation data for decline or
retirement and is never reconstructed from the staged selector.

The approved types packet owns key projection and its error vocabulary.
Binary/int supplies the authoritative matched template scheme to
`MonoDemand::instance_key(&Scheme) -> Result<Symbol, InstanceKeyError>`,
propagates derivation failure through the existing rematerialization failure
path, and compares the resulting staged key with the captured prior key before
choosing publication. It does not duplicate type substitution, signature
rendering, key validation, or fallback to an ordinal spelling. No alias
registry, cross-key publication variant, special family-edge repair, or
cross-module metadata mutation is required.

All production context-free key calls in the current Binary/int surface are in
`src/worker.rs`. The remaining calls are fixtures in `src/worker/tests.rs`, the
`src/redefine.rs` test module, and the `src/process_form/macro_clause.rs` test
module. Adapt each to obtain the exact selected template scheme from its table
or fixture and handle the typed error; do not add a local formatter or a stored
signature copy. `crates/cranelisp-exe-bundle/` has no instance-key consumer.

The current ordinary planner derives codegen targets from a staged AST. Demand
instantiation has no new source AST, so the private prepared-transaction helper
must also accept the exact successful demand targets when it constructs the
prepared batch. This is an extension of the existing prepare → whole-batch
compile → publish core, not another publisher. No live symbol, GOT cell,
introspection entry, result-owner route, or warning becomes visible before the
whole demand batch compiles. Successful publication uses the same owner
retention, drop-glue routing, introspection and final write guard as an ordinary
turn.

For a caller-free language-type-changing base, declined stale demands remain
`CheckResult` warnings and their old captured instance keys retire only in the
same successful publication; omission alone must not preserve them. A decline
while rematerializing a same-language-type base is instead a candidate failure.
A `Gap` follows the existing synchronous load → wait → retry cadence. Any other
failure takes the established CS-3 error-blocked recovery floor and leaves the
session usable. A repeat of the same demand is idempotent inside the
target-clean check world.
The persisted-source reload half of this S122 slice separately deletes
`capture_instantiation_drivers`, `reload_module`'s `extra_forms` parameter, and
all synthetic `__expr` replay. Each prepared candidate has one demand
instantiation trigger. The approved ACT-0954 surface change deletes only public
`CompilerSession::re_register_module`; the private scheduler operation and the
synchronous lifecycle reload remain. The obsolete source-presence assertion for
that wrapper retires with it. No replacement public session method is added.

Watcher polling keeps its actual cadence: `main.rs` calls `poll_and_reload`
after a completed ordinary or agent turn and before the next prompt. It does not
poll while line input blocks.

The attributed unit RED belongs at the Binary/int preparation seam. Seed a live
template plus its previously realized concrete instance, with no blocking
dependent, and stage the replacement template. The one original prepared-turn
witness must show the base and a newly materialized body at the same
concrete-signature instance key in one candidate before initial publication.
Include an unrelated same-module helper used by the new generic body to prove
that masking only the affected instance keys preserves ordinary lookup. For a
same-type ABI-compatible body edit, assert that the key is included, the
replacement body is compiled, `PreserveAbi` is selected and the slot is
unchanged. For the caller-free identity-to-constant ownership change, assert
`ChangeAbi`, a fresh
published slot and retirement of the old slot. A companion unit proves that a
captured key whose demand is declined becomes an explicit absent-key retirement
decision only for the language-type-changing path.

Add one Binary/int unit for same-type overload reordering. It captures both old
links, proves that each old scheme maps to the matching staged scheme rather
than the same ordinal, and uses alpha-renamed, reordered template schemes to
exercise the established semantic comparator. Both staged demands must
rematerialize at their captured concrete-signature keys, retain their prior
slots through same-key `PreserveAbi`, publish backlinks to the matched staged
selectors, and leave existing named-caller references unchanged. Observe the
current callable targets and prior-owner retention through the ordinary
compile/publish transaction, not only successful key construction. A missing or
ambiguous arm match, key-derivation failure, or same-type key/ABI mismatch must
leave the complete prior family, instances, slots, GOT cells and owners
unchanged. Reuse the existing constrained-scheme comparator control; no
cross-key swap, family-edge producer, or separate publication mechanism is
part of this evidence.

RP4 adds the concrete-in-place polarity. Its module subject starts from a cached
historical overload instance with no type arguments and a replacement arm
already staged as `Life::Concrete` with no backlink. Preparation must produce
no decline warning, enroll the matched staged target, preserve the full
signature key and ABI metadata, and publish through the same atomic transaction.
The unchanged public program must return `3` in fresh and cached REPL, `--run`
and `--link` modes. The module subject was armed by intended RED run
`f54bf8f6-6d25-44f1-99bc-94e10643b0f4`; the corrected subject and six sibling
lifecycle controls pass 7/7 in run
`8799b247-1bb8-4a89-80e8-8614f736eec9`, and the six-mode public witness passes
in run `9d5b51ba-f957-444a-bcc8-60e3d1253278`.

Arm failure only after real candidate preparation or compilation work. It must
leave the old authored scheme/body, prior instance slot/code/GOT,
introspection, and backing source unchanged; the next ordinary call must still
use the old definition. Retain controls that reject a same-language-type
ownership-ABI change and a language-type change with a named blocking
dependent. These units cover the int-owned decisions without changing
typecheck's existing-instance idempotence test.

Public evidence keeps the pair in `tests/spec_11_stdlib.rs`:
`same_session_generic_redefinition_without_vec_import` has a prior realization,
and `generic_redefinition_without_prior_realization_uses_replacement_control`
does not. Both must return the replacement after the correction. Existing
`same_type_generic_redefinition_after_realization_uses_replacement` and
`same_type_generic_redefinition_without_prior_realization_control` supply the
same-type prior-realization pair; both must return `42`. Existing
`successful_vec_flatten_then_same_name_generic_redefinition_completes_session`
remains an integrated acceptance case, without implying a separate backend or
RC cause. Existing evidence also covers set deduplication, Gap retry without
duplicate publication, and a failed batch with no partial publication. The
public API check records the approved wrapper removal; no test calls the
deleted method.

The permanent pair
`generic_overload_family_reorder_preserves_realized_named_callers` and
`generic_overload_family_already_reordered_fresh_session_control` is the public
discriminator for the generation transition. The subject requires two complete
generic-family confirmations, both signatures twice, no replacement error or
cascade report, and results `7`/`42` before and after the reorder. The fresh
control requires one complete family confirmation and results `7`/`42`. Keep
the already-green concrete-family reorder pair as a separate control; it does
not exercise captured generic demands. The recorded run
`61a51698-402e-453e-ab3b-fb8fa8f32aa4` is one pass and one failure against
checkpoint `dc78ddbe` plus the retained S122 working tree. The first failure is
during replacement preparation; process success and still-callable old bodies
do not satisfy the subject.

Q7's permanent source-level witness now inspects both the `Int` and `String`
concrete bodies before a later evaluation can remint either demand. Its planted
stale-body control returns `7` in
`/tmp/s122-int-q7-demand-carrier-plant-red-dc78ddbe.log`; the restored module
witness passes in `/tmp/s122-int-q7-reload-green-dc78ddbe.log`. This records the
corrected demand carrier at its owning seam. The demand-only replay, foreign
overload remap, ordinary rematerialization controls and `Annotated`
single-owner completeness pass 13/13 in run
`236d2b5d-d8d2-4dfd-8261-02a13085449c`; scoped re-review found no surviving
issue in those three findings. The watcher provenance and complete-plan
ordering corrections are also delivered and reviewed; §7 retains final
integrated evidence.

## 3. Macro and quote ownership

`design/int/macro-turn-ownership.md` remains the normative protocol. The
executable clause's non-null entry pointer stays leased by its `Code` owner from
argument marshalling through protected invocation, result copy, and result
release. That code-page lease and runtime heap ownership are different domains.
Heap handles are frame-local and never enter publication, continuation, or
retention pools.

The argument marshaller constructs one single-owner tree using consuming child
handles. It applies no protective increments and carries no private RC helper.
Crossing the declared `SexpListToSexpI64V1` ABI transfers the argument owner to
the compiled clause. On success, the returned Owned result is validated, read
through a borrowed view into an independent compiler `Sexp`, and consumed
exactly once. After transfer, int never attempts argument cleanup. A protected
trap can bypass compiled cleanup and therefore forfeits that one argument tree;
this bounded residual is explicit and must not be described as all-path zero
residue. Rust-side double cleanup after the non-local exit is forbidden.

The types-owned `cranelisp_types::{quote_head, QuoteHead}` classifier is the
single quote-head fact. Both the expander walk and macro-resolution walk consume
it unchanged; `src/expander.rs` has no private classifier. This changes no
quote semantics or facade.

Binary/int's module evidence records the all-Owned ABI pin, the transfer before
protected invocation, one successful result consume and no host argument
cleanup after a trap. The same delivered surface uses the shared quote
classifier in both int walkers; no extra semantic quote matrix is required.
Backend has delivered the separate Q4 returned-alias correction through its
selected-arm parameter carrier and compilation-local match-owner outcome. The
affected backend set passes 19/19 and the existing public macro pair passes 2/2
in run `0ce70208-1654-41a3-887f-89431a0b7b84`; independent review found no
material defect. Preserve that pair and the explicit trap forfeiture in final
integrated evidence.

## 4. Result root and truthful `/mem`

`src/result_owner.rs::release_key` consumes the producer's concrete codegen type
and calls `ConcreteType::result_root()`. The private `strip_io_head` copy is
deleted. The canonical one-hop `IO a -> a` rule, including malformed/non-IO
behavior, stays owned by `cranelisp-types`; Binary/int adds no heap predicate.

For `/mem <expr>`, the measurement order is: open counters, evaluate, render or
otherwise observe the result, call
`EvalResult::release_program_result()` at the existing chokepoint, then close
the counters and compute the delta. `Ok(None)` and `Err` contain no result
owner. `/time` is unchanged. The result is observed and released exactly once,
while the owning JIT/linker code lease is live.

QA's strengthened Q6 process witness observes the rendered heap value and a
post-release `/mem` counter snapshot, with its scalar control unchanged. The
recorded 1/1 pass is `/tmp/s122-int-q6-mem-result-dc78ddbe.log`; credit only
that allocated ordering and value observation. It is not the evidence for Q4
macro balance or Q5's matched session comparison, and it does not establish
integrated runtime closure.
No-result and error paths must continue to avoid manufacturing a release.

## 5. Failed-codegen recovery and diagnostic identity

Source inspection establishes that the four historical `vec-flatten`
codegen-failure witnesses no longer trigger codegen failure; two can pass
without exercising recovery. No stable, legitimate public-language program is
currently known to enter backend codegen and fail there. Backend error arms
found in the census represent invalid typed internal states or environmental
failure and must not be promoted into a language contract.

The transaction design remains unchanged: a prepared unit is compiled as one
batch, and only the successful batch may publish. Diagnostic identity is the
exact `CallableTarget` set carried by that batch, including overload arm and
generated targets; it is not inferred from the expression head.

On 2026-09-10 the user approved **Option A — private substitution**. Refactor
the private worker prepare → compile → publish core to take a private compile
operation. The production caller supplies the existing backend compile
operation. A `src/worker.rs` unit supplies an operation that first invokes that
real backend operation for at least one real prepared target, records that the
target GOT cell changed while the local JIT code owner is still live, and then
returns a deterministic error before publication. The outer transaction must
restore the recorded cells before that owner can drop. The unit proves the
pre-error mutation occurred, then proves the live table, GOT cells,
retained/compiled owners, publication/introspection state and warning stream
equal the pre-turn snapshot, and finally proves the next ordinary turn succeeds
in the same session. A separate assertion checks that the diagnostic names the
prepared batch's exact targets. A closure that merely returns `Err` without
producing the state to compensate is not evidence. The seam is a private
function or closure parameter; it introduces no trait layer, public flag,
public API, environment switch, or runtime branch.

Public successful session-recovery controls remain part of the evidence. The
source census must also record explicitly that no stable, legitimate public
program is known to reach this backend failure. The private unit proves the
transaction ordering and compensation edge; it does not prove public failure
reachability. This design does not permit inventing a faulty language program
or adding an injectable production failure mode.

## 6. Eval production stop

The first eval harness is a test-owned client of the real `--features agent`
process, using ordinary REPL stdin. The existing process interface, stub
provider, provider environment, bounded tool/repair loop, and agent event files
are sufficient for the selected generic-replacement and ordered-sequence-IO
tasks. `--yes` is used only in an explicitly approved run configuration so a
consent read cannot consume grader forms.

No Binary/int production change is selected. Logs remain best-effort; the
harness validates their presence and parseability before using log-derived
metrics. No new logger or provider is introduced. The present provider request
can ask for up to 64,000 output tokens. If the approved live-run budget requires
a lower or configurable request cap, that exact configuration is the trigger
for a small follow-up design in this still-open Binary/int stream. Until then,
changing the client would be speculative.

## 7. Review and handoff gates

The approved types identity producer and Binary/int context-bearing consumers
are delivered. The corrected complete-frame CLIF corpus passes 14/14: 23 frames
are one-for-one executable-identity renames and no instruction or control-flow
change remains. Its whitespace-name parser and smoke pair passes 2/2. The exact
runtime API baseline has been generated and matches the approved packet:
intrinsics is `+38/-9` and the other six surfaces are unchanged. The user
confirmed that baseline on 2026-09-11. Binary/int adds no API line. The other
approved public changes remain ACT-0954's wrapper removal and the nine typed
consume APIs; `instantiate_demands` is an already approved upstream contract.

The watcher provenance-selection correction is delivered and reviewed: its
public direct/transitive pair passes 2/2 in run
`c073e7f0-1922-4a27-b7d3-f7e95b2756bf`, and the affected watcher set passes
14/14 in run `55802f4f-748b-4f95-8f75-c79051886953`. Complete-plan ordering is
also delivered: the module pair passes 2/2 in run `a58ef193` after the armed
0/2 run `beacb3e6` (`/tmp/s122-int-q7-watcher-order-red-dc78ddbe.log`), the
unchanged public pair passes 2/2 in run `be88574b`, and the watcher set passes
14/14 in run `977c5ba4`. The complete plan orders dependency components before
acyclic downstream consumers and simultaneously changed roots dependency before
consumer regardless of input order, while preserving current path admission,
selected closure and once-only execution. It uses the existing watcher contract
and adds no graph API or language-cycle semantics. Scoped re-review verified
that `poll_and_reload` consumes this complete plan and found no surviving issue.

Q5's final matched measurement in
`/tmp/s122-runtime-q5-final-after-dc78ddbe.log` records allocs 1198, deallocs
1152 and residual 46, compared with the original residual 1143 under the same
input, library, environment, debug build and no-cache posture. QA accepts that
paired reduction; the 46 surviving cells remain explicitly unclassified and
are neither a zero target nor evidence of harmless overhead or a new leak.

QA owns the eval conditions and policy; `/test` owns the executable harness and
remaining integrated evidence, while `/arch` owns the generated public API
baseline confirmed by the user on 2026-09-11. `/dev` must return for design
review only if the eval run proves the precise configuration gap in §6. The
delivered reload rematerialization, watcher correction and review, macro
host/Q4, quote classifier, result-root, `/mem` and Q5 comparison need no second
correction pass. The generated runtime diff is
`/tmp/s122-runtime-public-api.diff`; it matches the approved packet and has user
confirmation. Final integrated acceptance remains the completion gate.
