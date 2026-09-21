# Sprint 121 consolidated QA plan — lifecycle and runtime crossing

> **Retained dated record (S122 consolidation).** Only the sections that current
> source, tests, designs or [the current plan](PLAN.md) cite by number or row
> identifier remain, with their original numbering: §3 (3.1, 3.3, 3.8, 3.9), §4,
> §5.10, §10 (10.2, 10.3), §12 and §14 (14.1, 14.2). They are S121 allocations and
> observations, not current status; [S122 evidence](s122-evidence-delta.md) owns
> the active allocation. References below to a section that is no longer here —
> and the status, matrices, gates and census that were removed — are recoverable
> with `git show 48d6e713:tests/plan/s121-test-plan.md`.

**Authority:** `qa`. The governing requirements are `spec/`, `repl/spec.md`
and the adopted architecture.
## 3. Safety findings and minimal discriminating evidence

| ID | Finding | QA disposition | Owning stream | W3 gate |
|---|---|---|---|---|
| R1 | One shared `Pure` node forced on two lanes can transfer one payload twice | **current-sprint prerequisite defect; design closed, not an accepted residual** | C5-intrinsics I0b implements the ruled atomic claim, error ferry, discharge and observer; `test` owns acceptance | one successful ownership transition, loser refuses before field-0 access, one transfer and exact cleanup |
| R2 | A cancelled `Select` loser severs its structured join while a blocking `Par` worker is in flight | **current-sprint prerequisite defect; design closed, not an accepted residual** | C5-intrinsics I0b implements `BridgeJoinState`/ticket/lease; no arch return unless implementation changes the facade or cancellation policy | root teardown follows every worker exit acknowledgement; poll cancellation remains prompt |
| R3 | `emit_d24_adaptation` post-decs Borrowed params after an extern shim already discharged them; six string rows survive | **current-sprint prerequisite defect; design closed, not an accepted residual** | C4 B9 implements the `Realization × ParamFlow` plan; C5-primitives preserves the authoritative declaration facts | all six value wrappers discharge exactly once; user-function Borrowed adaptation remains |
| R4 | Platform-return `Pure` stamp writes beyond the node unless selected by returned tag and backed by the wider ABI | **current-sprint prerequisite defect; design closed, not an accepted residual** | C4 B5 tag stamp + C7 P0/fixtures + C5-intrinsics I0b | tag-directed stamp, ABI 10, independent pins and E1–E3 green |

### 3.1 R1 — shared `Pure` double force

> **Superseded observable (2026-09-21).** The user ruled that IO values are
> reusable descriptions of work, so the refusal this section expects of a second
> force is a defect, not acceptance. No cell below was ever written. The live
> allocation is [reuse of an IO value](s122-evidence-delta.md#reuse-of-an-io-value--defect-allocation);
> the text below stays as the S121 record.

The production mechanism is the exact atomic C5 claim in
`design/intrinsics/ownership-and-disposal.md` §6.1. There is no
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

### 5.10 Accepted future-triggered actions

These decisions do not weaken R1–R4:

| Item | Current disposition | Exact revival trigger |
|---|---|---|
| 0859 `ProjectionOf` production observer | retire unexecuted; the source survey found no production RC distinction after materialisation, so a new observer would create a seam with no consumer | a production lowering or ABI path carries projection provenance past materialisation such that `ProjectionOf` can change emitted ownership behavior; QA then allocates the smallest declaration-only mutation witness before that consumer lands |
| 0052 `/learn` | future action under ACT-0951; excluded from S121 | complete user-ruled feature contract for routing, triggers, state, persistence and user behavior |
| 0463 network lesson | future action with no facade widening | a reusable network platform or deterministic server-driving lesson is independently scheduled |

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
