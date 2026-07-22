# Sprint 116: Safety First, Settled Syntax

**Status**: PHASE 5 LANGUAGE (ACTIVE)

**Goal**: Clear every one of the 29 S115 certification failures, restore confidence in the load-dependent memory-safety state, and make the S115-settled trait and constructor syntax true in the compiler without adding parallel semantic paths.

**Audit**: cranelisp-primitives (FIRMED Phase 4 — last assessed in the S87-era pass; next long-unassessed context after the recent src/backend/frontend/typecheck/intrinsics sequence)

## Scope

Sprint 116 is a safety-and-conformance sprint. It deliberately holds the standing SROA / `--release` frontier until the load-dependent heap-corruption event is characterized and the S115-settled syntax has an implementation.

### Track A — memory safety and ownership (first, safety-gated)

1. Pull `macro_expansion_interior_alias_double_free::macro_clause_interior_alias_double_free_run` out of FIXME 0694 and treat it as the sprint's first-class, highest-severity defect. Reproduce under controlled load, preserve the allocator diagnostic, reduce before fixing, identify the violated ownership invariant, and land the permanent failing-not-ignored repro with the fix.
2. `/arch` rules on FIXME 0837 before the nested-ownership fixes: whether 0835, 0810, 0760, 0796, and the depth cliff are one transitive-discharge class; whether `MAX_DROP_GLUE_DEPTH` may remain; and how this joins the intrinsics audit R-6 header / typed-context boundary question.
3. Execute every baseline-RED fix through the mechanism authorized by that ruling. The heap-corruption member, nested-SList face (0835), all ten 0810 cells, all three 0760 cells, and the 0688 TCO loop-parameter cells are mandatory shipping groups. 0796 joins when required by the common mechanism. No per-seam shallow patch is admissible, but architectural difficulty is no longer a standing permission to carry a baseline RED.
4. Close both 0688-attributed backend seams that disappeared from the open-FIXME scan after attribution: entry-`main`/program-result over-retention (the 0745/R15 result-owner instance) and TCO tail-jump loop-parameter replacement without release. Attribution being resolved is not defect closure.
5. Re-establish the certification split: deterministic suite state and load-dependent state are reported separately. No memory-safety event may close on symptom absence, M1/quarantine perturbation, or an exact scalar alone.

### Track B — implement the S115-settled language surface

1. Implement §7.1's single `method_sig` production (FIXME 0838): resolve the one trailing element as type-or-body, accept conforming default methods, reject the deleted three-element spelling, and cover the default-method occurrence column (0826/0832/0833 as applicable).
2. Implement the settled constructor-form rules already pinned in `tests/deftype_constructor_form_rulings_s116.rs`: content-free parenthesized constructors reject; nullary/type-name sharing rejects except the settled product-type case; all definition/pattern/value mirrors agree.
3. Resolve FIXME 0845 after the user's duplicate-field-name ruling; duplicate constructors already have the consistent rejection direction and committed REDs. `/qa` supplies the 15-cell PLAN/annotation rows from 0847 before the implementation gate closes.
4. Implement the settled structural annotation fold from FIXME 0708 across the frontend/int/types carrier seam, including its cache-schema consequence and the existing RED flip trigger. Do not add a second annotation representation or a macro-specific pairing rule.

### Track C — detection proof and record integrity

Subject to user acceptance of the S115 intrinsics audit recommendations:

1. Build R-1's inert test-only fault injection at the intrinsics alloc/diagnostics seam; prove M1, M2, M3 and the A1–A4 release faces detect their planted faults, including fail-on-revert evidence and the e2e M3 production-wiring cell.
2. Land the small intrinsics convergence batch: count-free catalog authority (R-2), one heap-read owner (R-3), removal/protection of dead public counter-reset surface (R-4), reactor citation repair (R-5), and the split-owner record-integrity corrections (R-7).
3. `/qa` implements the S115 process findings needed by this sprint's gates: spec-change coverage invalidation (0803/0804), constructor-form traceability (0847), eliminator/reaching-context risk rows (0830/0831), and honest detection-proof grades.

### Explicitly out of scope

- Multi-field SROA and the LLVM `--release` tier remain next-frontier work after this safety/conformance sprint.
- Display protocol 0050 and `/learn` 0052 stay on their existing Phase-H schedule.
- 0604 is investigated only through the already-recorded contamination/environment discriminator (0818); no quiet-run speculative fix is permitted.
- The remainder of the S115 FIXME inventory is not silently absorbed, but **every S115 certification RED is in scope**. Phase 3 may add a non-RED item only when it is a dependency of Tracks A–C; any broader scope change returns to the user.

## S115 RED closure ledger

This ledger is the Sprint 116 exit contract. S115's close prose listed groups totaling 28 stable REDs; its 29th certification failure was the separately named load-dependent heap-corruption manifestation. Sprint 116 closes neither by scalar arithmetic nor by deleting attribution records: every group below must be green and the load-dependent member must carry mechanism-level closure evidence.

| Baseline group | Count | Defect seam | S116 closure |
|---|---:|---|---|
| 0810 owned temporary scrutinee | 10 | Backend match ownership, including constructor and var-pattern faces | Mandatory Track A transitive-discharge implementation + all ten green |
| 0760 nested capture/drop depth | 3 | Backend capture glue and `MAX_DROP_GLUE_DEPTH` fallback | Mandatory named/per-concrete recursive glue + all three green |
| 0688 result-owner/TCO family | 3 | Entry-result over-retention plus TCO loop-param slot replacement | Mandatory 0745/R15 result protocol + explicit TCO replacement release; all three green |
| 0708 macro-argument annotation fold | 1 | Frontend/int annotation carrier seam | Mandatory `Sexp::Annotated` schema window; green |
| Duplicate constructor names | 3 | Frontend constructor registration | Mandatory reject-on-second rule; all three green |
| Settled constructor-form rulings | 8 | Frontend definition/pattern/value mirrors | Mandatory implementation; all eight green |
| Load-dependent heap-corruption manifestation | 1 observed certification member | `macro_clause_interior_alias_double_free_run`; allocator detected corrupted smallbin | Mandatory controlled reproduction, reduction, root fix, and repeated load certification green |
| **Total** | **29** | | **Zero S115 baseline REDs at exit** |

### Zero-baseline-RED gate

- Sprint 116 does not close with any of the 29 S115 certification failures still red.
- Any newly discovered defect is pinned immediately. Carrying that new RED beyond S116 requires an explicit user-approved scope adjustment with rationale; it cannot become a carry merely because it was found late.
- The final report enumerates the test names under each ledger group and reconciles them name-for-name against the S115 certification set. Counts are secondary evidence.

## Phase 1 user decisions

1. **Scope approval — APPROVED 2026-07-22.** Tracks A–C stand as drafted.
2. **S115 intrinsics audit disposition — ALL ACCEPTED 2026-07-22.** R-1 through R-6 filed as 0848–0853; split-owner R-7 filed as 0854–0857. The disposition trail is recorded in `audits/cranelisp-intrinsics-s115.md`.
3. **Duplicate field names (FIXME 0845) — RULED 2026-07-22.** `(deftype T [:Int a :Int a])` rejects with a located error on the second field, symmetric with duplicate parameters and required by §8.5.2's unique `Type.member` referent. `/spec` must scribe the ruling before its implementation wave.

## FIXME debt

This table is the proposed in-sprint set, not a claim that every open S115 FIXME is absorbed. Audit-derived rows are added only after user acceptance.

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0694 | /qa | open | Split the named heap-corruption member from the publication/enrolment and unclassified load-dependent events; Track A priority 1. |
| 0688 family | /dev(backend + int result seam) | attribution resolved, defects open | Three S115 REDs lost from open-FIXME scanning after 0688 deletion; mandatory result-owner + TCO closure. |
| 0708 | /spec → implementation owners | open | Normative ruling is settled (structural fold); implement and flip the existing RED. |
| 0745 | /design(int) + /arch | open | Must consume the Track-A header/typed-context ruling; no isolated release patch. |
| 0760 | /design | open | Conditional on 0837's grouping ruling and bounded matrix. |
| 0796 | /design(backend) | open | Same reaching seam as 0760; conditional on 0837. |
| 0803/0804 | /qa + /spec | open | Make spec-change annotation invalidation mechanical for Track B. |
| 0810 | /testing → design/dev | open | Conditional nested-ownership eliminator family; permanent REDs already landed. |
| 0818 | /qa | open | Environment/probe-contamination discriminator for 0604; no speculative source fix. |
| 0826 | /dev | open | Default-method occurrence cell joins the §7.1 implementation. |
| 0830/0831 | /qa | open | Add eliminator axis and risk ranking before grouped ownership closure. |
| 0832/0833 | /testing | open | Default-method/re-impl conformance cells; disposition with §7.1 work. |
| 0835 | /qa → implementation owners | open | Nested SList heap corruption; minimum Track-A shipping face after reduction. |
| 0837 | /arch | **resolved P2** | One transitive-discharge class; fixed-depth fallback forbidden; canonical R15 + BC §4b invariant 16. |
| 0838 | /dev(frontend + typecheck) | open | Settled single-production trait syntax, explicitly deferred to S116. |
| 0845 | /spec | **resolved P3** | Constructor and field binders are pairwise unique within one `deftype`; both rejects locate the second occurrence. `/testing` still owns the duplicate-field pin. |
| 0847 | /qa | **resolved W1 static** | Durable PLAN rows landed for all 15 constructor-form cells; coverage annotations are deliberately not promoted before runtime evidence. |
| 0848 | /dev(intrinsics) | open | R-1: production-path detection proofs; Track C gate. |
| 0849 | /arch → /dev(intrinsics) | **arch-resolved P2** | Count-free authority approved; source/test rename routed to Track C. |
| 0850 | /dev(intrinsics) | open | R-3: converge raw heap reads; third-sprint must-ship. |
| 0851 | /arch → /dev(intrinsics) | **arch-resolved P2** | Removal of `reset_counts` + `bytes_peak` approved; baseline diff routed to Track C. |
| 0852 | /dev(intrinsics) | open | R-5: repair 62 stale reactor citations. |
| 0853 | /arch | **resolved P2** | Two-word header retained; typed-exit owner inventory recorded in R15/BC §4b. |
| 0854 | /design(intrinsics) | open | R-7 design-record currency. |
| 0855 | /dev(intrinsics) | open | R-7 local-memory count removal. |
| 0856 | /arch | **resolved P2** | R13 regraded to unit-boundary asserted; composed integration cells remain `/qa`. |
| 0857 | /qa | open | R-7 honest R8/mode detection grades. |

### Aging items and escalation check

- 0050 and 0052 remain intentionally scheduled with the later `--release` polish tier; this sprint does not reopen that user-approved schedule.
- 0553 and 0637 remain future-dependency obligations and are not pulled without their trigger.
- Intrinsics audit R-3 is a third-sprint recurrence from S87 and therefore should ship if accepted; a further deferral would require explicit user sign-off.
- FIXME 0604 is long-running but its current gate is evidentiary, not elapsed time: the falsified-comment/census work landed, and 0818 provides the next discriminating experiment.

## Architecture review (Phase 2)

**Verdict: APPROVED WITH ORDERING REVISIONS (2026-07-22); ZERO-RED TOP-UP APPROVED.** Tracks A–C and the user-expanded 29-RED closure ledger are technically coherent and contain no required interim architecture provided the gates below are observed. Track A is first and blocks every ownership implementation wave; Track C's detector-proof seam may proceed independently as a diagnostic change-set. Track B is structurally independent, but its annotation fold must use the already-ruled carrier and one schema window. The 0688 TCO replacement seam is an R15 ownership-displacement instance and fits the existing type-directed mechanism; it adds no header, ABI, or cross-crate carrier.

### Architecture rulings

1. **0837 is one safety class, not one patch.** The shared invariant is transitive discharge: releasing an owned heap value must discharge all transitively owned fields at arbitrary finite value depth. 0835, 0810, 0760, 0796, and the depth cliff are members of that class, but their publication/transfer seams remain separately owned. `MAX_DROP_GLUE_DEPTH` may not remain as a shallow-release fallback and may not merely be raised. The target mechanism is reusable named/per-concrete type-directed drop glue whose generated recursion follows runtime values, avoiding both a fixed inline-depth ceiling and infinitely expanded compiler recursion. The implementation order is: (a) controlled reduction and permanent repro for the corruption face; (b) `/design`(backend) actor/value-lifetime map and glue mechanism; (c) `/qa` bounded matrix spanning depths 1, 2, 4, 5, and >5 plus recursive-value termination; (d) migrate 0835 first, then 0810/0760/0796 only through that mechanism. No per-seam shallow patch is admissible.
2. **0853 retains the two-word header.** `HeapHeader { alloc_size, rc }` stays unchanged. No third type-id/drop-pointer word and no generic type-erased releaser are introduced. The releasing-owner inventory is: generated lexical/container ownership → backend type-directed glue; known runtime protocol trees → their intrinsics `consume_*` owner; `Pure` payload → transferred to the program-result owner; JIT run/REPL result → int's `(i64, Type)` seam through last observation, then release; linked result → generated startup stub through exit-code conversion, then release; platform/DLL values → the typed `CLOwned<T>` and callback contract. Any newly discovered exit is a design defect until added to this inventory and R15.
3. **0745 is the program-result instance of R15.** It does not require an intrinsics ABI extension. `/design`(int) must specify one semantic release protocol across run, REPL, and link: observe/display/convert first, then exact-once type-directed release. The JIT host may select glue from the carried `Type`; the linked stub selects the same glue at compile time. A JIT-only helper or an IO-specific special case is rejected under the single-pipeline and no-interim principles.
4. **0708 has one intentional cross-crate carrier and one cache window.** Use the settled `Sexp::Annotated { annotation, subject, span }` representation from `design/arch/annotated-sexp-node.md`; do not add metadata, pairing sidecars, or a macro-only representation. This changes the serialized `Sexp`/symbol-table shape, so `CACHE_SCHEMA_VERSION` must bump once (22→23 unless another approved carrier lands in the same coordinated window). Public-API baselines for `cranelisp-types` and any facade re-export affected by the new enum variant must be regenerated; the frontend builder signatures need no new public entry point. The tag-7 macro-visible `SexpAnnotated` constructor is a language/catalog addition, not a Rust ABI layout change.
5. **0851 public API: removal approved.** Remove `reset_counts()` and `bytes_peak()`; there are no repository consumers, and retaining `reset_counts()` can invalidate M3's evidence. This is a deliberate subtractive `cranelisp-intrinsics` public-API change requiring rustdoc cleanup and `public-api.txt` regeneration, but no cache-schema, heap-layout, C-ABI, or intrinsic-catalog change. `alloc_count`, `dealloc_count`, `bytes_allocated`, and `bytes_current` remain. No guarded replacement is authorized absent a concrete consumer.
6. **Audit architecture dispositions.** R-2/0849 is approved: count-free rustdoc and `name_set_is_exactly_expected`, with `EXPECTED_NAMES.len()` the sole number authority. R-4/0851 is approved as removal. R-6/0853 is resolved by rulings 1–3 and canonical R15/BC §4b invariant 16. R-7/0856 is resolved: R13 is unit-boundary asserted, with only composed fork-join integration evidence owed. These approvals route source and baseline edits to `/dev`; architecture FIXMEs may close after their owned canonical record is committed.
7. **0688 TCO top-up: R15 displacement instance, backend-owned.** A tail self-jump reuses the loop-header parameter slots; replacing one slot ends the old slot owner's lifetime. The backend must release the superseded typed value through the common named/per-concrete glue unless the existing move/COW exemption proves the same owner is carried into the next iteration. Classification and release are separate: `fn_compiler` owns one replacement/transfer predicate (bare move, control-flow protection, borrowed state, and in-place-COW cases), while the common glue owns transitive discharge. Ordering is binding: design/land the glue contract first; then wire `flush_superseded_heap_params_before_tail_jump` to it. A local ADT-only dec, a new TCO-specific glue generator, or changing only `is_heap_type(Gr)` while retaining depth-limited inline glue is an interim patch and is rejected. The bare-Vec and carry-forward controls remain required.
8. **0688/0745 reconciliation: one glue contract, two lifetime seams.** TCO replacement remains entirely inside backend-generated typed code; 0745 is the distinct typed-context exit into the program-result owner. They share glue identity and transitive behavior, not ownership policy. After the backend glue contract is settled, the TCO seam may consume it directly; `/design`(int) then specifies how the `(i64, Type)` owner selects the same per-type release after display/exit conversion, and how linked startup emits the compile-time equivalent. Neither seam waits for the other's policy implementation, but neither may invent a private release mechanism.
9. **Phase-3 interface ruling — module-qualified symbol + keyed artifact.** Add exactly one `cranelisp-types` naming primitive: `drop_glue_symbol_name(&ModuleFullPath, &ConcreteType) -> LinkerSymbol`, using an injective complete-type encoding. Backend keeps the behavior-owned carrier: `DropGlueArtifact { symbol: LinkerSymbol, jit_address: Option<usize> }`, returned as `CompilationArtifacts.drop_glues: HashMap<ConcreteType, DropGlueArtifact>`. `compile_to_module` keeps its signature and proactively emits exported glue for concrete owning return types (including `IO`'s inner type) in the same registry/transaction. Fresh JIT performs a direct type-keyed artifact read; cache-hit uses existing `Linker::get_symbol`; linked startup emits a relocation to the same module-qualified symbol. The address is valid only under the existing `Arc<Jit>` retention owner. No GOT slot, arbitrary JIT symbol API, serialized address/map, cache bump, heap/ABI change, or second compile entry is approved. Required public-baseline deltas: the one types function; backend's `DropGlueArtifact`, its two public fields, and the `CompilationArtifacts.drop_glues` field.
10. **Phase-3 interface ruling — one unresolved method tail, one classified authority.** `cranelisp-types` adds the frontend-stage `UnresolvedTraitMethodSig { name, docstring, params: Vec<(Symbol, TypeExpr)>, tail: Sexp, span, hkt_param_index }`; `TraitDecl.methods` becomes `Vec<UnresolvedTraitMethodSig>`. Typecheck alone classifies it into `TraitMethodSig { name, docstring, params, kind: TraitMethodKind, span, hkt_param_index }`, where the authoritative closed sum is exactly `TraitMethodKind::Required { ret_type: TypeExpr } | TraitMethodKind::Default { body: Expr, result_constraint: Option<TypeExpr> }`; `TraitDeclInfo.methods` remains `Vec<TraitMethodSig>`. The unresolved tail and its exact span survive frontend intact, including `Sexp::Annotated`; annotated defaults store the subject as `body` and the annotation once as `result_constraint`, never also as a duplicate outer expression annotation. The legacy parallel `ret_type + default_body` fields are removed in the same coordinated change, and no unresolved method may enter the symbol table. This coalesces into the approved cache schema 22→23 window. The exact required baseline delta is `cranelisp-types/public-api.txt`; frontend and typecheck baselines must be regenerated as zero-diff checks because neither adds a public entry point, re-export, or carrier.

### Phase 3 requirements

- `/design`(backend) must replace the depth-cutoff shape with named/per-concrete glue, show recursive-type termination without compile-time unrolling, include the 0688 TCO replacement/transfer matrix, and conform §9's exported-name/artifact projection without changing `compile_to_module`'s signature. `/design`(int) must consume the keyed artifact/name contract while covering fresh JIT, cache-hit, REPL, run, and linked startup as one result-owner protocol.
- `/qa` must define the transitive-discharge matrix before implementation, keep load-dependent certification separate, and require M1/M2/M3/A1–A4 positive detection proof before Track C closes.
- `/design`/`/dev` for annotation folding must stage corpus repair 0785 before the reader flip and coordinate the single schema-23 window. The carrier wave is serial: types first lands the dormant unresolved/classified shapes and deletes the legacy parallel fields; frontend then fills only `UnresolvedTraitMethodSig`; typecheck classifies transactionally into `TraitMethodSig` before symbol-table publication. The reader flip follows those consumers in the same 22→23 window.
- Every public-surface change rides with its `public-api.txt` diff. No full suite runs occur in Phase 2.

**Next skills**

- `/arch` — approve the exact `cranelisp-types::drop_glue_symbol_name` implementation and both ruled types baseline deltas during their implementation waves.
- `/qa` — produce the Track-A depth/exit matrix and Track-C detection-proof gates.
- `/design`(backend), then `/dev`(backend) — design and implement the transitive glue mechanism serially.
- `/design`(int), then `/dev`(src/exe-bundle) — design and implement the unified result-release protocol.
- `/dev`(types), then `/dev`(frontend), then `/dev`(typecheck) — land and consume the ruled method carriers serially inside the annotation schema window after 0785; regenerate the types baseline and verify zero frontend/typecheck baseline diffs.
- `/design`/`/dev`(frontend/types/int) — coordinate the remaining settled annotation carrier consumers and schema window after 0785.

## Skill plans (Phase 3)

### `/qa` — COMPLETE

Plan of record: `tests/plan/s116-test-plan.md`.

- Reconciles the contract name-for-name as 28 deterministic baseline REDs plus the separately observed load-dependent corruption member = 29.
- Makes depths 1/2/4/5/>5, recursive termination, eliminators, ownership displacement, typed-context exits, toggles, and run/link/REPL explicit acceptance axes.
- Requires positive production-funnel proof and fail-on-revert evidence for M1/M2/M3/A1–A4; diagnostic grades remain asserted-but-unproven until those proofs land.
- Separates deterministic and load-dependent certification and binds close to zero baseline REDs by test name.
- Gives concrete acceptance criteria to backend, int/exe-bundle, intrinsics, frontend/typecheck, annotation-carrier, testing, and review surfaces.

**Next skills:** `/testing` for missing RED-first cells; narrow `/design` for backend, int/exe-bundle, intrinsics, frontend/typecheck, and annotation carrier; `/sprint` for Phase-4 sequencing. The `/spec` ruling is complete below.

### `/spec` — COMPLETE

- Scribe constructor-name uniqueness across every arm spelling within one `deftype`; duplicate rejection is located at the second occurrence.
- Scribe field-name uniqueness across the whole `deftype`, including different sum-type arms; duplicate rejection is located at the second occurrence.
- Reconcile §8.5.2 so canonical `Type.member` uniqueness accounts for constructor/constructor and field/field collisions as definition-site rejects while preserving legal cross-type reuse.
- Clear the changed §5.2.2 and §8.5.2 coverage annotations for `/qa` to re-establish only after the new negative cells and existing positive coverage are audited.

Acceptance: the settled 2026-07-22 ruling is normative in §5.2.2; §8.5.2's uniqueness argument is complete; no cross-type semantics change; FIXME 0845 is resolved and removed.

**Next skills:** `/testing` adds the located duplicate-field RED with `// spec:` trace; `/qa` plans and audits the cleared coverage rows; `/design`(frontend/typecheck) specifies one definition-time uniqueness path; `/sprint` sequences the implementation wave.

### `/design` (backend) — COMPLETE

Plan of record: `design/backend/transitive-drop-glue.md`.

- Selects one named/per-concrete type-directed drop function and a compilation-local `Declared | Defining | Defined` registry; declaration-first construction makes recursive and mutually recursive types finite at compile time while generated calls follow runtime values.
- Removes `MAX_DROP_GLUE_DEPTH`, `drop_glue_depth`, and every shallow fallback. No borrowed-builder clone, seam-specific deep releaser, JIT-only helper, header word, or type-erased generic release is admissible.
- Consumes architecture ruling 9: `drop_glue_symbol_name(module, concrete_type)` is the sole module-qualified identity; exported bodies project as `CompilationArtifacts.drop_glues: HashMap<ConcreteType, DropGlueArtifact>`. Fresh JIT carries a retained address, cache-hit uses `Linker::get_symbol`, and linked startup relocates to the same symbol; no signature change, GOT slot, serialization, cache bump, arbitrary symbol API, or second compile entry.
- Gives match-owned scrutinees one per-arm lifetime plan: protect/transfer escaping fields before exact-once wrapper release; inline and let-bound spellings, constructor and var patterns use the same rule.
- Folds explicit lambdas, auto-curry and other compiler-synthesised environments into one capture-glue builder, satisfying 0760/0796 at the mechanism grain.
- Defines one replacement/transfer predicate for TCO slot flush: exact bare/control-flow/COW owner carry transfers; fresh, copied, unrelated and unknown values replace and release through canonical glue; borrowed aliases never license suppression.
- Supplies the required submodule × complexity/edge/negative unit-test matrix and binds implementation order to registry/glue first, then 0835, match, capture/curry and TCO migration.

FIXMEs 0760, 0796, 0810 and 0835 remain open: this pass satisfies the design ruling, not their implementation/test closure.

**Next skills:** `/arch` authors the exact naming contract and verifies public-baseline deltas; `/qa` reconciles the per-arm and displacement negatives; `/dev`(backend) implements serially with unit tests; `/review`(backend) checks every slice against the no-interim constraints.

### `/design` (int/exe-bundle) — COMPLETE

Plan of record: `design/int/result-owner.md`; master design updated at
`design/int/int.md`.

- Defines one armed program-result owner carrying the successful `(i64, Type)`
  through its last observation, narrowing once to `ConcreteType`, and then
  invoking backend's canonical per-type glue exactly once. `Pure` transfers its
  payload to the owner and selects the inner `a`, never `IO a` glue.
- Fresh JIT reads `CompilationArtifacts.drop_glues` directly by concrete type
  and pairs the address with `Code::Jit(Arc<Jit>)`; cache-hit derives the same
  module-qualified symbol and resolves it through `Linker::get_symbol`, paired
  with `Code::Linker(Arc<Linker>)`. Missing keys/symbols/addresses fail loudly;
  there is no scan, serialization, or late compilation fallback.
- REPL fully formats before release; `--run` computes its exit code before
  release and releases before session shutdown; linked startup computes the
  exit code, calls an ordinary relocation to the same symbol, then exits. Error
  outcomes carry no successful result owner and invoke no result glue.
- Gives submodule × complexity/edge/negative unit scenarios for pipeline owner
  construction, artifact routing, cache load, REPL display, run lifecycle,
  startup CLIF, and exe-bundle linkage. Ordering and exact-once tests record
  observation, glue call, and code-owner drop events.
- Rejects a JIT-only or IO-only helper, display-owned dec, unguarded raw address,
  generic/type-erased release, shallow fallback, serialized pointer/map, and an
  exe-bundle wrapper releaser. Compiler concurrency and observability designs are
  unchanged.

FIXME 0745 remains open: this pass settles design but does not implement or flip
the RED.

**Next skills:** `/arch` verifies the ruling-9 consumption and reconciles the
backend doc's pre-ruling linkage wording; `/qa` checks the negative matrix;
`/dev`(int/exe-bundle) implements serially with unit tests; `/review` checks the
owner/retention/ordering contract.

### `/design` (intrinsics) — COMPLETE

Plan of record: `design/intrinsics/diagnostic-modes.md`; index updated at
`design/intrinsics/CLAUDE.md`.

- Marks M1/M2/M3 and A1--A4 implemented while preserving the open positive
  proof obligation; removes the drained FIXME-0656 rider.
- Defines a crate-private closed eight-plant protocol, armed only by two exact
  child environment values. It is compiled for M3 e2e proof but adds no
  public/exported/catalog/ABI/schema/IR surface and makes no mutation while off.
- Requires fresh subprocesses, an explicit environment allow-list, unique temp
  directories and `--no-cache`; shared-process env mutation is inadmissible.
- Routes plants through production alloc/dealloc/RC funnels; M2 observes through
  `heap_access`; validation precedes mutation. Every detector has positive,
  clean and disabled-detector fail-on-revert polarity without UB.
- Restores the M3 compiler-child counter→atexit→report→abort cell and clean
  sibling; unit children own both imbalance polarities.
- Specifies the convergence batch: one heap-read owner, one Vec-layout owner,
  count-free catalog authority, counter API removal, and reactor-path grep-zero.
- Supplies the submodule × complexity/edge/negative matrix and serial order.

FIXMEs 0848, 0850, 0852, 0855 and 0857 remain for implementation or their
owners. FIXME 0854 is resolved by this design update.

**Next skills:** `/arch` checks the public-surface gate; `/qa` aligns detector
labels and grades; `/dev`(intrinsics) implements with unit tests; `/testing`
adds M3 e2e; `/review` checks unarmed behavior and control safety.

### `/design` (frontend) — COMPLETE

Plan of record: `design/frontend/s116-syntax-and-annotation.md`; master design
updated at `design/frontend/frontend.md`.

- Makes `reader::read_colon_prefix` the one recursive producer of
  `Sexp::Annotated`, covering every form and macro-argument position without a
  positional or macro-specific pairing path; malformed structure rejects in the
  reader while type-half validation remains in AST building.
- Binds migration to 0785 corpus repair before the flip, dormant carrier and
  consumer waves inside the single schema-23/public-baseline window, then one
  coordinated producer flip and mirror retirement.
- Normalizes constructor spellings through one arm parser and validates one
  definition-wide constructor-name set plus one field-name set. Duplicate errors
  locate the second occurrence; partially emitted `ParsedEntry` vectors are
  forbidden. Definition and pattern spellings mirror the settled rules.
- Parses §7.1 as exactly one raw trailing element and leaves type-or-default
  resolution to typecheck; it never commits an application-shaped default body
  to the type parser.
- Supplies frontend submodule × complexity/edge/negative unit scenarios. No
  frontend public entry point changes; concurrency is unchanged.

FIXMEs 0708 and 0838 remain open for implementation. FIXME 0785 remains the
pre-flip corpus prerequisite. FIXME 0788 is resolved by removing stale verbatim
diagnostic copies from frontend design.

**Next skills:** `/arch` confirms the method-tail carrier and schema window;
`/qa` + `/testing` complete missing REDs and 0785 repair; `/design`(typecheck)
specifies resolution; `/dev`(frontend) implements serially; `/review` checks the
one-carrier and second-occurrence invariants.

### `/design` (typecheck) — COMPLETE

Plan of record: `design/typecheck/s116-method-signature-resolution.md`; master
and trait design updated at `design/typecheck/typecheck.md` and
`design/typecheck/traits.md`.

- Classifies the one unresolved method tail once with a side-effect-free,
  non-raising type-resolution probe; resolvable means required, otherwise the
  same form is a default body. `Sexp::Annotated` is structurally a body and its
  annotation is the optional result constraint.
- Replaces the legacy mandatory-return-plus-optional-body authority with one
  closed required/default semantic sum. The unresolved and classified carrier
  shapes are `/arch`-owned and share schema 23; typecheck adds no public API.
- Applies occurrence at declaration time to argument or return/result-constraint
  positions, never by scanning a default body; HKT stays exempt by branch.
- Infers unannotated defaults per impl, checks annotated defaults as ordinary
  constraints, and uses one conformance path for first impl and re-impl.
  Parameter arity is checked symmetrically before body checking; no binder is
  dropped and no partial enrollment is published.
- Rebuilds omitted defaults against the new settled sibling set on re-impl,
  covering 0832 without a redefinition-only repair. Supplies the required
  submodule × complexity/edge/negative unit matrix for 0826/0833 and §7.1.
- Updates the shipped occurrence-rule record and resolves design-owned FIXME
  0827; implementation/test FIXMEs remain open.

**Next skills:** `/testing` lands missing RED-first cells; `/dev`(types) lands
the ruled carrier and types baseline first; `/dev`(frontend), then
`/dev`(typecheck), consume it serially with unit tests; `/review` checks classification,
conformance and atomic enrollment; `/sprint` sequences Phase 4.

Remaining Phase-3 plan: any other annotation-carrier surface Phase 2 proved
touched. `/dev` is not dispatched during Phase 3.

## Waves (Phase 4)

Source edits and tests are serialized throughout. “Parallel” below means dependency-independent scope only; no two editing or test-running agents overlap.

### Wave 1 — QA-first complete RED surface

| Skill | Crate | Task | Status |
|---|---|---|---|
| `/testing` | sprint-wide | Author every missing RED-first cell from `s116-test-plan.md`: duplicate field, depth/recursive termination, displacement/typed exits, detector wiring, §7.1/default-method negatives, annotation round-trip/cache; reconcile all open `/testing` FIXMEs and preserve the exact 29-name baseline | done — authoring complete; execution verification environment-blocked (cargo-nextest absent and dependency index unavailable), retained for later gate |
| `/qa` | sprint-wide | Audit the landed tests against the plan, add durable PLAN rows/constructor annotations where evidence permits, and freeze the name-for-name gate before implementation | **done** — static authoring gate PASS; runtime execution verification environment-blocked and retained for certification |

**Gate:** all required tests exist and intentionally fail for the named missing behavior; every open `/testing` or `/qa` FIXME is resolved, retargeted, or explicitly deferred by its owner. No implementation starts against an incomplete matrix.

**`/qa` gate verdict (2026-07-22): PASS (static authoring).** All original 29 names remain;
new intended REDs are separately enumerated; depth 1/2/4/5/>5, recursive,
typed-exit, trait/default, constructor, annotation, and composition cells are
statically present with correct polarity and no new ignores. The repaired M3
child now uses the exact closed arm/plant, restored library/platform paths,
`--no-cache`, and a valid imported-`Pure` IO entry; its abnormal positive and
successful clean sibling are discriminating. The restored 0741 guard has a
numeral-free name, body-bounded scan, exact count 17, and direct exclusions for
both retired fields. No tests ran because nextest/dependency resolution is
environment-blocked; runtime color remains uncertified and mandatory before
final certification.

### Wave 2 — shared carriers and schema-23 window

| Skill | Crate | Task | Status |
|---|---|---|---|
| `/arch` | cranelisp-types | Implement `Sexp::Annotated`, `UnresolvedTraitMethodSig`, `TraitMethodKind`, `TraitMethodSig`, and `drop_glue_symbol_name`; bump schema 22→23 once; regenerate the types public baseline and prove frontend/typecheck baselines zero-diff | pending |
| `/review` | cranelisp-types | Verify exact ruled carriers, injective glue identity, one schema window, no parallel legacy authority, and baseline completeness | pending |

**Gate:** `/arch` approves the complete public/interface set; stale schema rejects; no second annotation/method/glue carrier exists.

### Wave 3 — canonical backend glue foundation

| Skill | Crate | Task | Status |
|---|---|---|---|
| `/dev` | cranelisp-backend | Implement declaration-first named/per-concrete recursive glue registry, exported identity/artifact projection, JIT/cache/link behavior, and remove `MAX_DROP_GLUE_DEPTH` plus all shallow fallback | pending |
| `/review` | cranelisp-backend | Review registry termination, recursive/mutual types, glue identity/cache/link parity, and grep-zero fixed-depth fallback | pending |

**Gate:** depth 1/2/4/5/>5 and recursive-termination foundation tests pass; no consumer migration lands through an interim glue path.

### Wave 4 — backend ownership consumers

| Skill | Crate | Task | Status |
|---|---|---|---|
| `/dev` | cranelisp-backend | Migrate 0835 SList construction, 0810 match lifetimes, 0760/0796 explicit+synthetic capture teardown, and 0688 TCO replacement/transfer to the canonical glue | pending |
| `/review` | cranelisp-backend | Review each consumer against R15 and the no-shallow-patch rule; require submodule scenario matrices and all 0810/0760/TCO baseline cells green | pending |

**Gate:** all backend-owned baseline REDs are green in both analysis toggles and required modes; no per-seam private releaser.

### Wave 5 — unified program-result ownership

| Skill | Crate | Task | Status |
|---|---|---|---|
| `/dev` | src/ + cranelisp-exe-bundle | Implement the armed observe-then-release owner across REPL, `--run`, cache-hit, and linked startup using the canonical glue artifact/symbol | pending |
| `/review` | src/ + cranelisp-exe-bundle | Verify `Pure` inner-type selection, exact-once/error ordering, retained code lifetime, and single-pipeline parity | pending |

**Gate:** all 0688/0745 result-owner cells are green; run/REPL/link share one semantic protocol.

### Wave 6 — settled syntax and trait semantics

| Skill | Crate | Task | Status |
|---|---|---|---|
| `/dev` | cranelisp-frontend | Land 0785 prerequisite, flip recursive annotation folding, normalize constructor arms, enforce constructor/field uniqueness and form rulings, and emit the one unresolved method tail | pending |
| `/review` | cranelisp-frontend | Verify one producer/enforcement seam, second-occurrence spans, pattern/definition mirrors, and no macro-specific fold | pending |
| `/dev` | cranelisp-typecheck | Classify the one tail transactionally; implement required/default closed semantics, occurrence, defaults, conformance, and re-impl atomic enrollment | pending |
| `/review` | cranelisp-typecheck | Verify no legacy three-element authority, malformed-type-vs-body polarity, occurrence columns, sibling defaults, and atomic publication | pending |

**Gate:** 0708, duplicate-constructor, duplicate-field, all eight constructor-form REDs, §7.1/default-method cells, and stale-cache/round-trip cells are green.

### Wave 7 — intrinsics detection proof and convergence

| Skill | Crate | Task | Status |
|---|---|---|---|
| `/dev` | cranelisp-intrinsics | Implement the closed test-only plant protocol, M1/M2/M3/A1–A4 positive proofs, heap-access/Vec convergence, counter API removal, count-free catalog, citation and local-memory corrections | pending |
| `/testing` | sprint-wide | Land M3 counter→atexit→report→abort e2e and clean control through production wiring | pending |
| `/qa` | sprint-wide | Witness fail-on-revert evidence and regrade R8/modes honestly | pending |
| `/review` | cranelisp-intrinsics | Verify validation-before-mutation, no UB, unarmed byte identity, environment isolation, public baseline, and production-funnel coverage | pending |

**Gate:** all eight detector rows have positive/control/off discrimination; accepted audit FIXMEs close consistently with their files and records.

### Wave 8 — certification and user-facing phases

| Skill | Crate | Task | Status |
|---|---|---|---|
| `/qa` + `/testing` | sprint-wide | Two identical deterministic full runs; loaded reduction; at least three captured full runs for the corruption member; exact 29-name reconciliation; zero S115 baseline REDs | pending |
| `/repl`, `/port`, `/stdlib`, `/examples`, `/docs` | user surfaces | Phase 6a standing-quality assessment, then Phase 6b action against what actually shipped | pending |
| `/audit` | cranelisp-primitives | Whole-context assessment to `audits/cranelisp-primitives-s116.md` | pending |

**Gate:** certification and every user-proxy plan/action complete; audit landed; any newly discovered RED blocks close absent explicit user-approved carry.

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P2 | `/arch` | sprint scope + R15/header/0688/ruling-9 interfaces | inherited | inherited | — |
| P3 | `/qa` | sprint-wide test plan | inherited | inherited | — |
| P3 | `/spec` | duplicate constructor/field uniqueness | inherited | inherited | — |
| P3 | `/design` | backend, int/exe-bundle, intrinsics, frontend, typecheck (serialized) | inherited | inherited | — |
| P3 | `/arch` | glue artifact + method-tail carrier gates | inherited | inherited | — |

## Notes

- 2026-07-22: Phase 1 draft authored from the S115 close record, open FIXME scan, Phase-H roadmap, and `audits/cranelisp-intrinsics-s115.md`. No audit recommendation has entered the backlog yet; all seven await user disposition. No language ruling has been inferred for duplicate field names.
- 2026-07-22: USER approved Tracks A–C. USER ruled duplicate field names within one `deftype` reject with a located error on the second field. Phase 1 remains open solely for disposal of the S115 intrinsics audit recommendations.
- 2026-07-22: USER accepted all seven S115 intrinsics-audit recommendations. Filed 0848–0853 for R-1..R-6 and 0854–0857 for R-7's four owners; appended the audit disposition trail. Phase 1 gate complete; advanced to Phase 2 architecture review.
- 2026-07-22: USER expanded scope to clear every S115 certification RED. Reconciliation found 28 stable grouped REDs plus the separately manifested load-dependent heap-corruption member = 29. Added the closure ledger; made 0810/0760/0688 mandatory; zero-baseline-RED is now the exit gate. Returned Phase 2 for a narrow 0688 TCO/R15 top-up.
- 2026-07-22: `/arch` APPROVED the zero-RED top-up. The 0688 TCO seam is an R15 ownership-displacement instance using the common named/per-concrete glue after one backend-owned replacement/transfer predicate; 0745 remains the distinct program-result owner consuming the same glue contract. No header/ABI/carrier change. Phase 2 complete; advanced to Phase 3 design.
- 2026-07-22: Phase 3 COMPLETE. `/qa` reconciled the exact 29-name contract; `/spec` scribed duplicate constructor/field uniqueness; backend/int/intrinsics/frontend/typecheck designs landed; `/arch` fixed the glue artifact and method-tail carriers with one schema-23 window. Phase 4 organized eight serialized waves and firmed `cranelisp-primitives` audit. Advanced to Phase 5; Wave 1 `/testing` is next.
- 2026-07-22: `/arch` approved the zero-RED top-up. 0688 TCO replacement is an R15 ownership-displacement instance: backend's one replacement/transfer predicate decides whether the old loop-param owner moves, and the common named/per-concrete glue performs any owed transitive release. 0745 remains the distinct result-boundary owner consuming the same glue contract after observation.
- 2026-07-22: Wave-1 `/testing` partial: added duplicate-field second-occurrence RED + distinct control; §7.1 inferred/annotated default, deleted-spelling, broad occurrence and re-impl/default-sibling cells; finite recursive 0/1/many discharge cell; and the missing checked-in `16-modules` e2e row. Closed testing FIXMEs 0805, 0820 and 0832 against landed cells; explicitly deferred out-of-scope 0798/0799. The exact 29 baseline names were not renamed or removed. Required narrow execution could not run because `cargo-nextest` is absent; `cargo check --tests` was also blocked by unavailable crates.io index/cranelift. M3 e2e remains deliberately pending until Wave 7 exposes the closed injection contract; typed-result mode and structural annotation round-trip cells remain before the Wave-1 gate.
- 2026-07-22: Wave-1 `/testing` authoring COMPLETE. Added typed-result owner e2e across run/REPL/link (nested `Pure` payload, both ownership toggles where applicable, scalar control), recursive/macro/qualified annotation folds, malformed/dangling negatives, cold/warm structural-cache round-trip, exact closed-protocol M3 leak child plus clean control, the warm-cache Sudoku residue `<=1400` application guard, impl extra-parameter first/re-impl negatives, and the numeral-free/direct-absence SharedState guard. Closed testing FIXMEs 0741, 0810, 0833 and 0840 after verifying their cited sources and landing their cells; 0798/0799 remain explicitly deferred outside Tracks A--C. Original 29-name ledger remains byte-for-name intact. Newly authored intended REDs: `deftype_duplicate_field_name_rejected_at_second_occurrence_neg`; `inferred_default_body_is_the_single_tail_and_dispatches`; `annotated_default_body_is_one_structural_tail`; `deleted_return_type_plus_body_spelling_rejected_neg`; `nonnullary_no_self_occurrence_rejected_at_declaration_neg`; `reimpl_default_body_calls_replaced_sibling`; `first_impl_extra_parameter_rejected_neg`; `reimpl_extra_parameter_rejected_and_prior_impl_survives_neg`; `finite_recursive_values_zero_one_many_terminate_and_balance`; `run_nested_pure_payload_observed_then_released_both_toggles`; `linked_nested_pure_payload_converts_then_releases`; `repl_nested_heap_value_displays_before_exact_release`; `nested_and_application_annotations_fold_recursively`; `qualified_compound_annotation_round_trips_through_macro`; `structural_annotation_cold_warm_cache_round_trip`; `dangling_annotation_at_eof_rejected_neg`; `annotation_before_closing_delimiter_rejected_neg`; `m3_parity_catches_injected_imbalance`; `sudoku_warm_serial_solve_residue_at_most_1400`. New/brought-forward green controls: distinct field names, required bare-type tail, scalar result modes, M3 clean child, checked-in `16-modules` exit 47, and the numeral-free SharedState structural guard. Execution remains a later gate obligation because this environment lacks `cargo-nextest` and cannot resolve the dependency index; no substitute `cargo test` was used.
- 2026-07-22: Wave-1 `/qa` recheck PASSED the static authoring gate. The repaired M3 child restores the cleared library/platform environment, runs a valid `Pure` IO entry with `--no-cache`, and preserves exact closed-protocol positive/clean polarity. The restored 0741 guard is numeral-free in name, scans only the `SharedState` body, asserts the exact field count, and directly excludes both retired parking fields. Wave 2 may proceed; runtime execution remains environment-blocked and mandatory before certification.
- 2026-07-22: `/testing` repaired QA's Wave-1 M3 fixture blocker. The env-cleared compiler child now restores only `CRANELISP_LIB` and `CRANELISP_PLATFORM_PATH`, uses an explicit `Pure` program whose local String allocation is observed through `str-len` and normally discharged, and preserves the exact `s116-detection-proof-v1` + `M3Leak` plant. Wave 1 is ready for `/qa` recheck; this records fixture readiness, not an execution gate pass.
- 2026-07-22: `/testing` restored the fully verified FIXME 0741 resolution after a formatting-cleanup reversal: `shared_state_pub_field_count_guard` has no frozen numeral, retains the exact 17-field creep tripwire, and directly asserts `module_sexps` and `suspend_states` are absent from the bounded `SharedState` body. FIXME 0741 remains correctly closed. Wave 1 remains ready for `/qa` recheck.

## Outcome (Phase 7)

### Delivered

- Pending.

### Deferred (with rationale)

- Pending.

### Findings (record in FIXME's if not already)

- Pending.

## Next skills

`$sprint` sequences Phase 4 from the completed QA/design/architecture gates. The
method-carrier path is `/testing` REDs and 0785 repair, then serial
`/dev`(types) → `/dev`(frontend) → `/dev`(typecheck), followed by narrow
`/review`; `$arch` checks the ruled types public-baseline delta. Independent
backend and result-owner waves follow their recorded dependency gates.
