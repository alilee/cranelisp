# S124 Phase 2 architecture review

**Owner:** `arch`. **Reader:** the user and `sprint`, at the Phase 2 → 3
checkpoint. **Status:** proposal, 2026-11-16. It approves nothing; the exact
public-API deltas are in the [S124 API packet](s124-api-packet.md).
**Checkpoint:** `main` at `3155f47f` plus the uncommitted `SPRINT.md` edit.
**Retention:** working document; fold its accepted results into the owning
carriers and retire it at the S124 close.

The review was read-only. No source, test, specification or design file was
edited, no build or test ran, and no probe was executed. Every claim below
about source was read at the checkpoint; §9 lists what was opened. The document
checker exits 2 on this tree (item 6), so these two files are unchecked by it.

## Verdict

The approved scope fits the existing crate boundaries. It needs no new crate
and no new cross-crate mechanism. It does need seven public-API deltas, one
specification ruling and three scope corrections before design starts.

| Item | Crosses a crate interface? | Before design starts |
|---|---|---|
| 1 Type concreteness | One new consumer edge (D1); otherwise interior to backend and typecheck | Gate D1; accept the widened close in §1.3 |
| 2 ACT-1052 | No, on one condition (§2) | Nothing |
| 3 Raise-helper hardening | Yes: D2, a contraction | Gate D2 |
| 4 Principle 27 retirements | Yes: D4–D7; spark density has none | Gate D4–D7; the §18.1.2 ruling (§4.5) |
| 5 Frontend | Yes: D3, the import and export carrier | Gate D3 |
| 6 Package convergence | No crate interface; three architecture positions (§6) | The user's adoption choices |
| 7 Get to green | One possible delta, not yet listable (D8) | The trace decision (§7.2) |

Sign-off is conditional on the user's answers in §8.

---

## 1. Type concreteness (item 1, with ACT-1050 and ACT-1034)

### 1.1 Findings

- **Both fabrication arms stand as FIXME 0903 states.**
  `FnCompiler::emit_release` takes a guarded shallow dec when
  `ConcreteType::from_type` fails, and `signature_heap_category` maps `Err` to
  `Mixed` (`crates/cranelisp-backend/src/compiler/fn_compiler.rs`,
  `compiler/rc_emission.rs`).
- **The census does not exist.** No census instrument is in
  `rc_emission.rs`; the word appears there only in a comment. The
  [release contract](../design/backend/non-concrete-release-contract.md) §7.3
  is open work, as filed.
- **The typecheck routes the obligations document names are in source.**
  `monomorphise_synth`, `derive_mono_demand`, `mono_demand_from_spans`,
  `build_concrete_codegen_view` and `default_residual_parameters` all exist.
  The [obligations design](../design/typecheck/non-concrete-producer-obligations.md)
  reads as delivered, while the S123 close records the same populations as
  exempt from monomorphisation. Reading cannot settle which is true; the
  census can. This is why the census runs first.
- **`MonoExpr::lenient_from_expr` has no production caller outside
  `cranelisp-types`.** All 14 root call sites sit inside `#[cfg(test)]`
  modules, and the backend's two are in `test_support.rs`. The obligations
  design's residual row is accurate.
- **The census needs no new carrier.** `CallableOrigin` already has the
  `Plain`, `TraitMethod`, `Ctor` and `Accessor` partitions the census keys on.
- **The structural close adds one consumer edge.**
  `cranelisp_types::ctor_field_types_at` is published and has no consumer
  outside its crate. Contract §7.4 makes the backend its first. A new
  cross-crate consumer edge is a gated change: packet row D1.

### 1.2 ACT-1034 shares item 1's producer population

- The guards fail where the backend finds a slotless template: the entry
  fetched in `compile_direct_call` has no GOT slot, and the name reported is
  the template's. That is the lifecycle's intended refusal of a `Template`
  for which no instance was demanded (contract §7.1, obligations §2.5).
- The missing demand is a call inside a minted parametric impl-method
  instance. Obligations §2.4 makes trait-dispatched calls with a template
  target one more trigger of the same collector. ACT-1034 is therefore a gap
  in that population's successor discovery, not a separate mechanism.
- **Provisional.** The producer was not observed. *Refuted if* typecheck
  publishes an instance key for the inner call and the backend misses it;
  the owner is then backend or `src/`.
- **Mode divergence.** Cells A3 and C3 diverge between the REPL and batch in
  opposite directions. Whatever the producer, part of the fault is in how
  `src/` drives instance minting per mode, which
  [Principle 11](../design/arch/principles/11-single-pipeline-mode-parameters.md)
  forbids. `qa` attributes it before `design` places the fix.

### 1.3 Scope adjustments

1. **Read the census zero only after ACT-1034 is corrected.** Its four
   programs are refused before emission today, so they contribute no traffic.
   Nested parametric impl instances are the likeliest source of a residual
   word in a trait-method frame; the S123 close records that no free-standing
   program is known to reach one. A zero read while they are refused is
   vacuous for the `TraitMethod` partition.
2. **The close must cover the absent-type arm.** `emit_dup` and
   `emit_release` both return at once for `ty: None`, and `compile_lambda`
   falls back to `derive_param_type_from_body`, which yields `None` for a
   parameter the body never uses. An untyped word is uncategorised, so
   skipping its release is rule R-1's fault in its quiet form. FIXME 0903's
   closure names two arms; this is a third. The settling target ("the
   non-concrete arms no longer compile") holds only if a binder's stored type
   cannot be absent or residual. That is backend-interior and needs no API
   delta. `design`(backend) owns the representation.
3. **ACT-1050 is probably that third arm.** Its subject is an unused heap
   parameter of an inline lambda, and its attribution names the early return.
   The action's first act (observe the type reaching `compile_lambda`) still
   decides. *Refuted if* the subject's parameter arrives typed.
4. **Set the typecheck wave's scope from the census output.** The producer
   routes exist in source, so the remaining typecheck work is whatever the
   census measures, plus ACT-1034. Do not scope it from the S123 close prose.
5. **`lenient_from_expr` stays out of item 1.** Its narrowing is the approved,
   unlanded S123 row K11-d (§8.6). The settling target does not need it.

---

## 2. ACT-1052 (item 2)

- **Verified.** `DependencyRecord` maps each module in the transitive closure
  to a source hash (`src/cache/dependency_record.rs`). After an ABI-changing
  REPL edit and a textual revert, slot layout is no longer a function of the
  source, so the record under-keys the artefact.
- **Position.** The record must identify what the importer's object was
  derived from: the dependency's published slot layout, not only its text
  ([Principle 7](../design/arch/principles/07-single-source-of-truth.md)).
- **No API delta is needed.** `CachedModuleRef::dependency_hashes` is a map
  of opaque strings that `check_manifest` compares for equality. The binary
  supplies both sides. `design`(int) can change what the string identifies
  without touching the backend's manifest surface.
- **Condition.** A correction that adds a typed field to `CachedModuleRef`
  or `CacheManifest`, or changes `check_manifest`, returns to the gate.
- **Schema.** The meaning of a persisted value changes, so
  `CACHE_SCHEMA_VERSION` is bumped in the same change-set.

---

## 3. Raise-helper hardening (item 3)

- **Verified.** `CompileContext::panic_func_id` is a public
  `Option<FuncId>` on a public struct. Any backend code that holds a
  `CompileContext` can make a `FuncRef` for `runtime/panic` without
  `raise::emit_raise`. The existing census matches spelling, so an alias
  passes it.
- **`CompileContext` has no consumer outside the backend.** The only
  outside mentions of `cranelisp_backend::compiler` are comments in typecheck
  and intrinsics.
- **Position.** Make the `compiler` module and `CompileContext`
  crate-private (packet row D2, which is S123's approved and unlanded row
  R10-4). The panic handle then becomes a type private to `raise`, whose
  only use is inside `emit_raise`. That part is interior and adds no public
  item.
- **Rejected:** a new public wrapper type for the field. It would widen the
  surface to protect a field nothing outside the crate reads.
- **Grade after the change:** structural. A bypass has no value from which
  to build the call.

---

## 4. Principle 27 retirements (item 4)

[Principle 27](../design/arch/principles/27-dev-tier-optimises-only-against-blow-up.md)
governs all five. Each retiring mechanism's typecheck fact keeps being
produced and producer-tested.

### 4.1 Stack placement (closes ACT-1049)

- Backend-interior deletion (`emit_stack_alloc`, `IMMORTAL_RC`, the
  eligibility gates, `CRANELISP_NO_STACK_ALLOC`), per
  [ownership codegen](../design/backend/ownership-codegen.md) §4.
- Public effect: the intrinsics tally pair `rc::stack_slot_hits` and
  `rc::tally_stack_slot` loses its producer (packet row D5).
- ACT-1049 closes with it: no stack-placed value reaches `rc_dec_check`.
- **Ordering recommendation.** Land this as the first backend change-set,
  before the census. Today an armed half containing a `NoEscape` constructor
  stops on a false positive, so cells keep such constructors out of armed
  halves (ACT-1049, "Consequence for evidence"). Item 1's evidence depends on
  the armed check. The retirement also re-baselines the whole golden corpus
  once, before the census and close claim byte-identical or scoped diffs.

### 4.2 Value flattening

- `HeapCategory::Value` is public and has root consumers
  (`src/result_owner.rs`, and `src/display.rs` reads the same layout).
  Packet row D4.
- `cranelisp_types::value_layout` stays public as a retained fact.
- Compiled layout changes, so `CACHE_SCHEMA_VERSION` is bumped.

### 4.3 Spark density

- No public item names it: the baselines contain no density symbol. The
  retirement is backend-interior. `MonoExpr`'s `escapes` and `confined`
  fields lose their last backend reader and remain as retained facts.

### 4.4 The borrow-elision carrier

- `Realization::ExternShim { borrowed_sibling }` has had no producer since
  ACT-0974. Packet row D6 (S123's approved, unlanded row R10-8). It changes
  a persisted type, so `CACHE_SCHEMA_VERSION` is bumped.

### 4.5 The mode-ABI redefinition gate and ACT-0953 (needs a ruling)

- **Verified premise.** Outside tests, the backend reads `mode_summary` in
  one place: the cache loader's index validation
  (`cache/serialize.rs`). No emission site reads a `ModeSummary`, `Mode`,
  `ParamFlow` or `ResultMode`. A compiled slot's contract is therefore the
  same for every mode summary: every call position consumes its arguments.
- **Consequence.** REPL §18.1.2 calls itself an interim gate that exists
  because ownership modes "form the ownership ABI" of a live slot. They no
  longer do. The gate now refuses redefinitions that are safe.
- **ACT-0953 is discharged by subtraction.** It asked for a compile-time
  adaptation that preserves old callers across a mode change. Under uniform
  counting none is needed: there is nothing to adapt.
- **What the user decides.** Removing §18.1.2 is a normative change to the
  REPL specification (§8.1).
- **Public effect if removed.** The three `ModeSummary` predicates the gate
  uses lose their consumers (packet row D7). The two root sites are
  `src/redefine.rs` and `src/worker.rs`.
- **Grade.** Asserted with a named falsifier until `qa`'s cell runs: a
  same-type redefinition that changes the inferred modes, with live callers
  and callable values, must balance under the armed check in every mode. A
  backend emission read of a mode summary would refute the premise.

---

## 5. Frontend (item 5)

### 5.1 The import and export carrier (ACT-0997, ACT-1056, audit R2)

- **Verified.** `ImportNames` classifies a whole list:
  `Specific(Vec<Symbol>)`, `Glob`, `MemberGlob(Symbol)`, `None`.
  `parse_names_list` returns `MemberGlob` at the first `.*` entry and drops
  the rest. `ExportSpec` has no alias field, and the export parser requires
  a plain symbol for the module.
- **The specification asks for per-entry classification.** §8.3's grammar
  makes each name a bare symbol, a dotted member, a renamed pair or a member
  glob, and §8.3.11 requires every entry to be classified independently.
  §8.4 applies the same grammar to exports and adds the mount alias.
- **Position: one entry type, used by imports and exports** (packet row D3).
  A list holds entries; an entry is a binding with its source and local
  names, or a member glob. `ExportSpec` gains the alias `ImportSpec` already
  has.
- **`local` is always the bare name the entry binds.** The frontend derives
  it once: the written name for a plain entry, the member for a dotted one,
  the second symbol for a rename. The installer binds `local` and never
  re-derives it ([Principle 24](../design/arch/principles/24-resolve-once.md)).
- **This makes ACT-1055 unrepresentable.** Its mechanism is
  `collect_specific` binding a dotted entry under its written spelling. With
  D3 there is no written spelling to bind. ACT-1055 should land with D3, not
  as a separate fix to code D3 rewrites.
- **The mount needs no new lookup mechanism.** The
  [alias contract](../design/arch/module-alias-scoped-lookup.md) §2 already
  stores export mounts as public alias entries and walks them. Only the
  carrier and its writer are missing. `ModuleAliases` is rebuilt at restore
  from persisted table fields; that rebuild must read `exports` as well as
  `imports` and `submodules`. `arch` amends §2.1 with the change.
- **Supersedes S123 row N1.** N1 changed only `Specific`'s payload and could
  not carry a mixed list.
- **Rejected: merging `ImportSpec` and `ExportSpec` into one type with a
  visibility field.** §8.4.0 would justify it, but `SymbolTable` persists
  them as two fields with many readers. The churn buys no guard.

### 5.2 The rest

| Subject | Interface effect | Note |
|---|---|---|
| ACT-1057 | None | Frontend synthesis constrains the clause body to `Sexp` |
| Audit R1 (macro shapes), R3 (signed reader) | None | Frontend interior, after `qa`'s reproductions |
| Audit R4 | None | Frontend interior |
| Audit R5 | None | Factual repair. The `lib.rs` rustdoc that says `trace` fails when linked contradicts spec §4.12.9; `arch` approves correcting it, since the promise is false and no policy changes |

---

## 6. Package convergence (item 6)

No crate interface is involved. Three points are architecture's; the adoption
choices are the user's (§8.5).

- **`AGENTS.md` as root memory.** Required by the converged checker. The
  rename touches three `arch`-owned memories (`design/arch/`,
  `design/arch/principles/`, `crates/cranelisp-types/`), 63 citations in
  `design/arch/` and 252 comment lines across 120 Rust files. The comment
  edits are source edits and run serially. `arch` updates its own carriers
  in the W0 change-set; the
  [shared-checker contract](../design/arch/s122-shared-document-checker.md)
  is one of them.
- **Risk to name in W0.** The package's consuming guide does not mention
  `CLAUDE.md`. The Claude host loads `CLAUDE.md` memories on entering a
  directory; this session relied on that. Whether it loads `AGENTS.md` the
  same way is unverified here. `sprint` owns host-entry guidance and should
  measure it on one directory before renaming the rest.
- **Rust context standard: stay unadopted.** It assumes service-shaped
  contexts (facade, adapters, authority values) and a `DESIGN.md` per crate.
  Cranelisp already holds the same properties: one design home per crate
  under `design/`, the bounded-context statement, and seven generated
  baselines under a failing guard. Its mechanical check would add a second
  public-API inventory beside `public-api.txt`
  ([Principle 7](../design/arch/principles/07-single-source-of-truth.md)).
- **Rust build standard: decline for now.** It gives each role its own
  build tree. `target/` is 72 GB today; twelve roles would multiply it. The
  repository already runs source-editing work serially and allows one test
  run at a time, so the isolation buys little here.
- **Spec traceability standard.** It overlaps the annotation band `qa`
  maintains and `tests/plan/spec_coverage_reconcile.py`. Two coverage
  authorities would disagree. `qa` and `spec` should assess it before the
  user decides; architecture has no stake beyond that.
- **Shared-tree guard.** It refuses the git operations root guidance already
  forbids. It is a constructive, cheap control with no architecture effect.
- **`ux`.** Declared and not dispatched; no boundary changes.
- **Handoff to `sprint`.** `standing-documents.toml` establishes
  `sprints/s123-*.md` only. These two files need `sprints/s124-*.md`.

---

## 7. Get to green (item 7)

### 7.1 The mapping, verified

The 44 filed guards recorded at the S123 close
(`.local/s123-close/reds.txt`, taken at `d3db8dc8`) were matched to their
filings by each test's own `// defect:` and action citation where present.
The counts in `SPRINT.md` are right, with one correction.

| Action | Guards | Verified against |
|---|---|---|
| ACT-1050 | 12 | `tests/bind_unused_heap_argument.rs` |
| ACT-1052 | 1 | `tests/cache.rs`, `artifact-underkey` at `DependencyRecord` |
| ACT-1057 | 5 | `tests/spec_09_macros.rs`, the action's named cells |
| ACT-1056 | 6 | `spec_08_modules`: three mount cells, three mixed-list cells |
| ACT-0997 | 2 | `box_import_renamed_…`, `box_import_self_rename_…` |
| ACT-1055 | 2 | `selective_member_…` |
| ACT-1034 | 4 | `spec_07_traits`, cells A1, A2, A3, C3 |
| ACT-1038 / ACT-1039 | 2 / 1 | `tests/trace.rs` |
| ACT-0973 | 2 | `tests/platform_errors.rs` cites ACT-0973 |
| **ACT-1016** | **3** | Two export-cycle cells, and `reload_failed_reexport_dependency_matches_restart_neg`, which cites "ACT-1016 face 1" |
| ACT-0985 | 1 | `impl_body_uses_impl_declared_later_in_cluster` |
| ACT-1001 (P-3) | 1 | `impl_ambiguous_trait_names_both_candidates_neg` |
| ACT-1036 | 1 | `spec_10_io` |
| ACT-1018 | 1 | `exemplar_ownership_residue_s116` |

- **Correction.** The row "ACT-1017 (probable)" is ACT-1016 face 1.
  ACT-1017's own text says it was resolved on 2026-11-15, and its two guards
  pass. The resolved filing is still in `sprints/actions/`; `qa` deletes it.
- **Limit.** The mapping was checked against the S123 close list, which
  `SPRINT.md` says equals the opening tree's filed set. The suite was not
  re-run.

### 7.2 Per-root interface positions

| Action | Interface effect | Position |
|---|---|---|
| ACT-1034 | None expected | Rides item 1 (§1.2) |
| ACT-1038 | Possibly intrinsics (D8, not yet listable) | See below |
| ACT-1039 | None expected | A `--run`-only omission is a mode divergence ([Principle 11](../design/arch/principles/11-single-pipeline-mode-parameters.md)); mechanism is provisional and `qa`'s |
| ACT-0973 | None | See below |
| ACT-1016 | None | `src/` publication and reload; no carrier changes |
| ACT-0985 (cluster order) | None | Typecheck interior: register a cluster's impls before checking any body |
| ACT-1001 P-3 | None | Typecheck interior: the impl-head resolver swallows an ambiguity |
| ACT-1036 | None | `src/exe.rs` raise site takes a span |
| ACT-1018 | None | Re-measure after ACT-1050 |

- **ACT-1038.** The trace installs its wrappers in the process-wide GOT, and
  a wrapper formats its arguments before the runtime knows whether the
  calling thread records. Two faults follow: worker calls are unrecorded,
  and their formatted strings leak. Spec §4.12.2 requires "normal strict
  evaluation" and that every call be recorded. Recommended decision (§8.4):
  sparks are declined for the trace's dynamic extent, and no wrapper
  allocates before it knows it has a consumer. Both halves cross the
  backend/intrinsics seam. Whether the existing spark-admission and
  trace-entry intrinsics can carry them without a signature change is for
  `design`(intrinsics) and `design`(backend) to list. A changed or added
  export returns as packet row D8 before implementation. `arch` then
  corrects the two named-intrinsic rows in [tracing](../design/arch/tracing.md).
- **ACT-0973 needs no specification answer.** Spec §10.9.1 is unambiguous: a
  `platform` form in a non-entry module is a compile-time error. The K6
  questions it was grouped with were answered at S123.
  `src/process_form/platform.rs` skips the form when the module path
  contains a dot, and its comment claims the specification says so. That
  test keys on the shape of a name
  ([Principle 19](../design/arch/principles/19-no-module-privileged-by-name.md)),
  which is also why a root-level non-entry module is treated differently.
  The correction keys on the session's entry module.

### 7.3 Second-deferral triage (METHOD §2.6, trigger 3)

The S123 record asks why groups K5 and K6 keep deferring. The structural
reason is the same for both: a group label carried a gate that only one member
needed, and the label outlived the question.

- **K5 "needs the `ImportNames` gate".** Only ACT-0997 touches `ImportNames`.
  ACT-0985's guard and ACT-1001 P-3 are typecheck-interior and were never
  blocked by it.
- **K6 "needs a spec answer and a naming decision".** Both answers were
  recorded at S123. ACT-0973's guards rest on a requirement that was never in
  question.
- **Recommendation.** Carry and schedule by filing, each with its own stated
  dependency. Group labels are for reporting only.

---

## 8. Decisions for the user

### 8.1 Retire the interim ownership-ABI gate (REPL §18.1.2)

- **Problem.** The gate refuses a same-type live redefinition whose ownership
  modes differ, because modes used to shape a compiled slot. Since the S123
  cutover they do not (§4.5).
- **Recommended resolution.** Remove §18.1.2 and its diagnostic. A same-type
  redefinition publishes whatever its modes. ACT-0953 closes.
- **Tradeoffs.** A later release tier that specialises a slot by mode would
  need its own rule; Principle 27 places such specialisation outside the
  tiers that redefine live. Keeping the gate costs users refusals with no
  safety return, and keeps three public predicates alive for it.

### 8.2 The public-API gate: rows D1–D7

- **Problem.** Items 1, 3, 4 and 5 cannot start without them.
- **Recommended resolution.** Approve D1–D6 as written. Approve D7 only with
  §8.1.
- **Tradeoffs.** D3, D4 and D6 each change a persisted shape and bump the
  cache schema; every user's cache rebuilds once per bump. D2 and D6 are
  rows the user approved in S123 that did not land.

### 8.3 The shape of the import carrier (inside D3)

- **Problem.** Three open defects (ACT-0997, ACT-1055, ACT-1056) come from
  one carrier that classifies a whole list.
- **Recommended resolution.** One entry type shared by imports and exports,
  with the bound local name carried explicitly.
- **Tradeoffs.** It is a larger change than S123's N1 and touches every
  match on `Specific`. N1 alone would leave ACT-1056 needing a second pass
  over the same type and ACT-1055 fixed in code that pass rewrites.

### 8.4 Tracing under parallel evaluation (ACT-1038)

- **Problem.** A traced callee that sparks runs on workers that do not
  record, and leaks.
- **Recommended resolution.** Evaluation inside a trace is strict for its
  whole dynamic extent.
- **Tradeoffs.** A trace then does not show how the program parallelises,
  and its timings are sequential. Recording worker frames would keep
  parallelism visible but needs a new cross-thread merge in the trace
  runtime, and makes the recorded tree depend on scheduling.

### 8.5 Package adoption choices (item 6)

- **Problem.** The converged package requires one convention and offers
  several optional ones.
- **Recommended resolution.** Adopt `AGENTS.md` (required) and the
  shared-tree guard. Keep the Rust context standard unadopted. Decline the
  Rust build standard for now. Hold the spec traceability standard for
  `qa`'s and `spec`'s assessment. Declare `ux` as not dispatched.
- **Tradeoffs.** Declining the build standard keeps one 72 GB build tree and
  today's lock contention. Declining the context standard keeps cranelisp's
  own layout, which the package's check does not understand.

### 8.6 Third deferrals and approved rows that never landed

- **Problem.** S123 packet rows B2 and B3 were approved for the S123 close
  and are not in source: `lenient_from_expr`, `ExternShim::borrowed_sibling`
  and the backend's unused public items are all still public. A ruling
  without a scheduled slot is an open item (METHOD §2.2). The K7–K11 groups
  are at their third deferral.
- **Recommended resolution.** S124 lands the two rows its own items need
  (D2 and D6). The remaining B2 and B3 rows and the K-groups carry only on
  the user's explicit confirmation, filing by filing (§7.3).
- **Tradeoffs.** Landing all of B2 and B3 now is mechanical but adds a
  seven-baseline regeneration to a very large sprint.

---

## 9. What was opened

| Claim relied on | Opened |
|---|---|
| FIXME 0903, the release contract | `fn_compiler.rs::emit_release`, `emit_dup`; `rc_emission.rs::signature_heap_category`; contract §7 |
| Producer obligations | The design; the named functions located in `traits/monomorphise.rs`, `program/mono_collect.rs`, `program/support.rs` |
| `lenient_from_expr` callers | Every call site against its file's `#[cfg(test)]` boundaries |
| ACT-1050 | `control_flow/lambda.rs` parameter typing; both `compile_lambda` callers |
| ACT-1034 | The action; contract §7.1; obligations §2.4–§2.5. Source producer not observed |
| ACT-1052 | `src/cache/dependency_record.rs`; int §7.6; the backend manifest baseline |
| P-15 | `raise.rs`; the backend baseline; every `panic_func_id` site; external references to `cranelisp_backend::compiler` |
| Principle 27 rows | `ownership-codegen.md` §0, §4, §7, §9, §13.4; the three baselines; backend readers of mode summaries, `value_layout` and the escape facts |
| Mode-ABI gate | REPL §18.1.2; `ownership.rs::abi_eq_opt`; `src/redefine.rs`; `src/worker.rs`; `cache/serialize.rs` |
| ACT-0997, 1055, 1056, audit R2 | Spec §8.3, §8.3.5, §8.3.11, §8.4, §8.4.4; `module.rs` carriers; `module_extract.rs::parse_names_list`; the alias contract §1–§2 |
| ACT-0973 | Spec §10.9.1; `src/process_form/platform.rs`; the S123 answers to K6 |
| ACT-1038 | The action; spec §4.12.2, §4.12.6 |
| ACT-1016, 1017, 0985, 1001 | Each action; each guard's citation lines |
| Item 6 | `.agents/CONSUMING.md`; the three standards' openings; `standing-documents.toml`; `AGENTS.md`; `.codex/config.toml` |
| Item 7 mapping | `.local/s123-close/reds.txt` |
