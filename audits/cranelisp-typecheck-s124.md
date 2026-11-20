# cranelisp-typecheck — S124 whole-context assessment

## 1. Verdict

**Would a lean second implementation look like this? At the boundary and core
type algorithms, largely yes; in settlement, retained analysis and maintained
explanation, no.** A direct inferencer, canonical name resolution, concrete
specialisation and one typed publication boundary are credible. Repeated
settlement windows, identity re-resolution, an analysis with no current
optimising consumer, and conflicting descriptions add substantial avoidable
work around them.

| Attribute | Grade | Assessment |
|---|---|---|
| Design quality | C | Cohesive compiler responsibility and useful shared resolution/publication seams. Early generalisation and several settlement windows require compensating scans; retained ownership production serves a future tier. |
| Design realisation | C | Inference, ADTs, concrete views and demand replay have real implementations and evidence. Selected identities are discarded by collectors; the cluster-atomic promise is contradicted by the recorded failed-impl behaviour. |
| Simplicity and volume optimality | D | The default path computes and persists ownership facts unused by current optimisation; code, module evidence, cache validation and several documents maintain that capability. Settlement also repeats work rather than having one dependency-complete point. |
| Duplication | C | The type-expression resolver, child walkers and instance engine are shared. Identity selection is repeated after resolution; scheme refresh and explanation occur at several sites. |
| Risk-weighted production-path coverage | C | Strong local negative/property tests and permanent mode-specific defect guards exist. Ordinary trait signature positions and polymorphic candidate selection escaped earlier coverage. Several mechanisms remain provisionally attributed. |
| Maintainability | D | The aggregate burden spans the core compilation path, persisted products, tests, technical documents and cross-role interface coordination. Local module decomposition alone does not remove it. |
| Memory and contract freshness | D | Public rustdoc contradicts the manifest and source; the master still schedules delivered work; one typecheck design citation fails the document checker. |

**Requirement fulfilment: partial.** Ordinary inference and many advanced paths
work, but legal programs can select the wrong implementation, fail at codegen,
or, in QA's existing evidence, terminate on a signal. Refused input can leave
state that affects later turns. Diagnostic roles and alias handling also have
recorded failures. This is not a release-readiness sign-off.

**Maintenance-economy grade: D, independently of correctness.** The avoidable
weight crosses a core path and several maintained layers: the ownership
producer/fixpoints, persisted facts and validation, substantial producer tests,
and design/assurance documents; settlement compensation adds another recurring
cost. It would compound in a larger compiler. Development remains practicable,
so F is unwarranted. Current correctness, past approval, useful individual
tests and the cost of removing this structure do not improve this grade.
Disposition remains a separate decision.

## 2. Record, requirements and posture

| Field | Value |
|---|---|
| Context | `crates/cranelisp-typecheck/`, `design/typecheck/`, its public API baseline, relevant requirements, tests and open filings |
| Increment/date | Sprint 124, Phase 6a; 2026-11-20 |
| Source checkpoint | `main` at `46e195c7`; clean working tree on entry |
| Owner/readers | `audit`; coordinator and user deciding disposition in S125 Phase 1 |
| Authority | [Audit contract](../.agents/skills/audit/SKILL.md), composed quality/document skills, [rotation method](../sprints/METHOD.md#27-rolling-whole-context-audit), [audit collection](AGENTS.md) |
| Restrictions | Read-only outside this assessment; no Cargo, builds or test runs; existing compiler probes only from private scratch directories |
| Disposition | Pending; no finding authorises a fix, new control, API change or phase transition |

Other roles committed specification, QA and action updates during this audit.
The typecheck source and design remained identical to the named checkpoint;
the later search and `/type` updates do not alter the assessed findings or the
full-run numbers below. Only the assessment path is included in this commit.

In ordinary language, this context must determine what types a program has,
reject incompatible uses with useful locations, choose the intended declaration
and trait implementation, check data constructors and matches, and make every
reachable generic use executable at its concrete types. Interactive definitions
must obey the same language rules as files, and failed input must not change
subsequent behaviour. Required capability comes from [types](../spec/03-types.md),
[expressions](../spec/04-expressions.md), [definitions](../spec/05-definitions.md),
[patterns](../spec/06-pattern-matching.md), [traits](../spec/07-traits.md),
[modules](../spec/08-modules.md), the normative
[non-functional requirements](../spec/appendix-c-nfr.md), and REPL
[errors](../repl/spec/05-error-presentation.md) and
[redefinition](../repl/spec/18-redefinition.md). Architecture and tests do not
add language requirements.

The project is delivering one release compiler with interactive, file and
standalone executable use. This crate owns neither deployment nor user files;
its symbol-table output affects code generation and persisted compiler caches.
The cost of bad typing includes wrong machine-code calls, not merely a poor
editor experience. Source changes are reversible, but a crashed user process
and saved session consequences are observable harm. No production workload or
compile-time profile was supplied for this audit.

The smallest credible realization is a shared type algebra and unifier,
lexical scopes, inference over dependency-complete binding groups, one name
selection seam, a deduplicated concrete-demand worklist and typed publication
through a transaction boundary. ADT exhaustiveness needs only constructor
coverage because the required patterns are flat. Callee information and
located dependency gaps support interactive replacement and module loading.
Conservative uniform reference counting can execute this language without an
interprocedural optimisation analysis. A future optimisation tier can justify
that analysis when it has a consumer. This is an economic counterfactual, not
an approved replacement architecture.

## 3. Weight, paths and evidence

### 3.1 Aggregate inventory

Mechanical reading at the checkpoint (lines describe burden, not thresholds):

| Surface | Observed weight and implication |
|---|---|
| Crate Rust | 79 files, 67,560 lines; 1,004 literal `#[test]` attributes. Separating test paths/support and inline test modules leaves approximately 24,547 production-region lines and 43,013 test/support lines. |
| Production explanation | 7,755 comment-only and 1,219 blank lines within those production regions. Much commentary explains retired migrations, intermediate states and old field names. |
| Core orchestration | `program/`: 6,530 production-file lines and 13,512 test/support lines. `traits/`: 5,008 and 5,321 respectively. |
| Ownership | Nine production files, 3,509 lines; six test files, 6,379 lines. Three strata, fact publication, site annotation, tracing and an environment toggle remain maintained. |
| Design | 22 Markdown files including the design memory, 8,482 lines. The master is a useful map, but it also retains delivered implementation planning. |
| Public boundary | 76 baseline lines. Cluster checking, type-expression checking, demand replay, search predicates, result carriers, access guards and trace hooks; no code-generator dependency. |
| Dependencies | Types, frontend and DashMap. Frontend serves expression/type-expression construction; its presence is architectural, despite the facade's contrary claim. |

The ownership total excludes the additional shared carriers, backend cache
validation and solution tests. The crate test total is source inventory, not a
fresh executed-test count or evidence of coverage sufficiency. No build-time or
runtime cost is inferred numerically from line counts.

### 3.2 Important paths

| Path | Source trace, evidence and limits |
|---|---|
| Ordinary inference | `form.rs::check_forms` → registration → `program/body.rs` → `infer.rs`, `unify.rs`, `scheme.rs` → final annotation/publication. A private-scratch identity program plus `add-i64` exits 42. Unification has occurs/rigidity checks and scheme tests; this probe is one positive observation. |
| Forward references and overloads | Registration gives bodies shared variables; body-boundary refresh generalises earlier bodies again; finalization drains overloads, refreshes schemes and harvests single/multi-signature demands. The explicit O(forms × definitions) debt is documented in [monomorphisation §5.1](../design/typecheck/monomorphisation.md#51-generalisation-ordering-debt). |
| Candidate to concrete instance | Candidate selection records `VarRef::Global`; `program/mono_collect.rs` tests that a global verdict exists, then several collectors call `resolve_terminal_fq_scoped` on the spelling. A second resolution can lose the selected identity. Existing ACT-1075 controls separate polymorphism from candidate multiplicity (R2). |
| Trait dispatch | `traits/dispatch.rs::try_resolve_trait_method_decl` selects `hkt_param_index`, falling back to a bare-method index/default zero. For conventional methods this fails when the implementing type occurs later, or only in the return. Scratch subject exits 101, its self-first control 2 (R1). |
| ADTs/matches | `adt.rs` registers through the shared ADT builder; `infer.rs::check_constructor_pattern` instantiates constructor fields and records identities. Exhaustiveness uses settled constructor identities. The [ADT design](../design/typecheck/adt.md) records incomplete pattern-candidate lifecycle conformance rather than claiming it complete. |
| Failed cluster | Local staging is discarded, but trait shells live at the trait's home. `check_pending_trait_impls` commits successes individually and abandons only remaining shells after an error. QA's local/imported REPL subjects demonstrate a surviving earlier shell (R1); the exact division of rollback ownership remains provisional. |
| Concrete boundary | `program/support.rs::build_concrete_codegen_view` distinguishes non-concrete input from missing resolution. Shared view construction and callee harvesting are credible responses to observed omissions; replacing them with another independent validator would add little value. |
| Ownership publication | `ownership/fixpoint.rs::run_pass5` collects/clones concrete bodies, computes strata and calls `ownership/publish.rs`; publication clones/annotates views and writes facts. Finalization and demand replay invoke it. Backend emission has no optimisation reader of these facts; persisted result indices are still validated by cache deserialization (R3). |
| Error roles/aliases | `program/body.rs` unifies body type before expected return type; the scratch return annotation reports `expected Float, got Int`. `checker.rs::resolve_qualified` preserves the written module in member-absent gaps, unlike its alias-substituted module-unknown arm. Existing ACT-1080/1082 carry subjects and controls. |

Mechanism classification:

- **Directly required:** type inference, constrained annotations, static trait
  selection, ADTs, flat exhaustiveness, concrete specialisation and diagnostics.
- **Necessary enabling shape:** substitutions/fresh variables, lexical frames,
  canonical identities, a demand cache/worklist and staged publication. Direct
  AST traversal and keyed reads suffice; a second compiler framework would not
  simplify these obligations.
- **Responses to observed harm:** strict concrete views, shared callee harvest,
  rejection of unresolved references and permanent subject/control defect
  tests. These protect real failures. Their presence does not prove every
  producer or settlement window correct.
- **Compensating structure:** repeated generalisation, overload drains and
  mono harvests. They keep current paths functioning but retain ordering and
  seam obligations a dependency-complete settlement could avoid (R4).
- **Future extension with present cost:** ownership optimisation facts and
  their production/evidence/persistence apparatus (R3). The future release
  rationale explains retention but does not make it necessary for the current
  executable's behaviour.
- **Unsupported explanatory weight:** stale per-site counts, old lifecycle
  descriptions and delivered plans presented as current work (R5).

### 3.3 Execution and instrument limits

The authorized existing binary's SHA-256 was
`2f3ac7c6c0064ba849a8e28e7894be51128d744e2118b3add828b547d7ce960b`.
Its build-to-source identity was not independently established; scratch
observations are binary evidence, corroborated where stated by current source.
No crash probe, exponential-type probe or new benchmark was needed.

The [S124 evidence delta §14](../tests/plan/s124-evidence-delta.md#14-the-standing-state)
records the full suite at `39db1bb1`: 7,926 run, 7,846 passed, 80 failed,
one skipped, 274 seconds. Its typecheck allocation is 47 failing cells across
seven filings. That is a QA report at an earlier checkpoint, not a new run at
this audit's HEAD. The named tests, assertions and filing mechanisms were
opened; signals and the full matrix were not re-executed here.

The public baseline was read and compared with facade exports/signatures at a
source level. Its Cargo-backed regeneration was prohibited. The existing API
guard has both clean and deliberately changed-surface detection legs in
`tests/public_api_relocations.rs`; their source presence is not a fresh
execution proof. Ownership tests include refusal, convergence, residual-frame
and lattice controls. They discriminate producer behaviour; with no optimising
consumer, they do not establish an end-user optimisation benefit.

The document checker ran without a baseline and exited 1 with 590 findings.
One originates in `design/typecheck/hkt.md`: the cited helper
`impl_echo_type_name` is absent from [the named source file](../src/session_v4/types.rs). Global findings are
not new audit defects, and the checker does not establish substantive truth
where a reference resolves successfully.

## 4. Findings and routing

All priorities below are assessment priorities, not authorisation to reopen
S124. Cost classes describe the likely extent of owner investigation, not
estimates or mandatory implementations. Reuse existing filings for existing
failures; do not create duplicate tickets.

### R1 — Required trait behaviour and failure atomicity remain broken

**Priority: high; owner: QA intake, then coordinator-routed context work.
Cost: medium to large; unresolved.**

The independent dispatch probe confirms ACT-1076's wrong-value face. Its
source explicitly chooses an HKT/default-zero index rather than deriving the
conventional implementing-type position from the settled signature. Spec
§7.1.1/§7.1.4 permits that position anywhere and in the return. QA's committed
`s124_1076_subject_c_*` tests document the memory-unsafe face; their
`control_c_*` twins move `self` first. The signal result is inherited QA
evidence, not a newly observed signal.

Other existing failures must retain their distinct attributions:

| Existing carrier | Assessment and handoff |
|---|---|
| ACT-1071 | Imported implementation calling an overloaded helper: seven failing cells, including signals and one link refusal. The published-home hypothesis has partial support; do not claim the producer mechanism proven for every leg. QA retains attribution before a fix. |
| ACT-1073 | A refused multi-impl cluster leaves an earlier shell observable. The successful-before-failure commit loop supports the mechanism, and the e2e controls inspect subsequent calls and saving. The unconditional facade rollback promise is already falsified; QA determines the complete rollback owner. |
| ACT-1074 | Impl bodies cannot use a same-cluster overloaded function that free functions can use. `register_cluster` performs the impl-body sweep before final overload settlement. This supports, but does not independently measure, the provisional ordering attribution. |
| ACT-1080 | Wrong expected/actual roles, independently reproduced for an Int return annotation and Float body. The body-first unification order supports typecheck attribution; use existing four subjects and two controls. |
| ACT-1082 | Alias written as module in gaps: four recorded failures. Source confirms the producer asymmetry. Keep its public meaning change at the existing architectural gate; this audit grants no API approval. |

Requirement failures are present; closure is not achieved by documenting them.
Permanent e2e reproductions already exist for these filings. Module tests at the
identified seams remain part of their correction obligations, not audit work.

### R2 — Monomorphisation throws away a selected identity

**Priority: high; owner: QA via existing ACT-1075, then design(typecheck).
Cost: medium; unresolved.**

Spec §8.6.5 permits a shared spelling when constraints select one candidate.
The `collect_mono_call_sites` local-call conversion and sibling collectors
re-resolve that spelling after checking only the *kind* of its recorded
verdict. `program/support.rs::callee_has_keyed_carrier` returns a boolean,
so it cannot transport the selected identity. The source and QA's two
orthogonal controls support the stated producer loss. Existing call/value
subjects in `tests/spec_08_modules.rs` assert execution and the absence of
codegen misses; a qualified next-turn call is an additional discriminating
control in the filing.

This is also avoidable maintenance cost: every collector must separately
remember shadow protection, canonicalisation and module context. The
[monomorphisation design](../design/typecheck/monomorphisation.md#31-components)
already states the simpler rule: consume the verdict. Route the existing
requirement repair; no extra identity verifier is recommended.

### R3 — A future optimisation analysis imposes present multi-layer cost

**Priority: high for economic disposition; owner: arch through sprint.
Cost: large across owners; unresolved.**

Current uniform counting executes correctly without inferred ownership modes.
S124 removes the remaining stack-placement, flattening and density mechanisms;
the [ownership spine](../design/arch/ownership-inference.md) and
[interior design](../design/typecheck/ownership-inference.md#11-soundness-frame)
explicitly retain fact production for the release tier. Independent source
reading finds backend fact mentions as constructors/tests and cache
validation, not current optimisation decisions. This does not assert there
are zero readers of *any* ownership-related datum: value-use marks and cache
validation are distinct consumers and need consideration in a disposition.

The default compiler still clones bodies, runs modes/confinement/uniqueness,
publishes annotated views, persists summaries, validates their indices, and
maintains 6,379 lines of local tests plus shared evidence and designs. A
conservative compiler does not require these facts to implement consuming
calls, COW or typed drop glue; those have their own current mechanisms. No
measured current benefit from the retained analysis was found. No numerical
compile-time penalty is claimed without a profile.

These outputs and tests are real, locally coherent engineering; they are
nevertheless substantial future capability on today's delivery path. Prior
approval and a future consumer do not make its maintenance cost disappear.
Arch should present the retention-versus-isolation/removal tradeoff to the
user, accounting for value-use needs and persisted representation. This
assessment does not authorise deletion, a toggle change or a schema change.
Reconsidering an active optimisation needs an actual release-tier consumer,
measured benefit and its allocated soundness evidence; it does not justify
more speculative controls now.

### R4 — Settlement compensation amplifies ordinary changes

**Priority: medium; owner: design(typecheck), with arch for boundary effects.
Cost: medium to large; unresolved.**

`program/body.rs` refreshes earlier polymorphic schemes at each body boundary.
`program/finalize.rs` contains closely related generalisation walks, overload
settlement and complementary/repeated mono harvests. The design acknowledges
the O(forms × definitions) compensation and the helper-last limitation.
Maintaining which frame is settled at which invocation is a recurring code,
review and evidence obligation, not simply a long function.

FIXME 0776 already records the settlement-seam issue and distinguishes a
required polarity argument (structural) from correct caller placement
(asserted with a named falsifier). Preserve that distinction. A new seam
registry or repeated checker would measure the compensation, not remove its
cost. Assess a dependency-complete settlement when this interior is next
changed; the document's proposed linear cures require design validation and
must preserve binding-group and interactive semantics. This is an economic
finding, not a claim of a newly reproduced helper-last defect or demonstrated
compile-time regression.

### R5 — Published explanations no longer describe the delivered context

**Priority: medium; owners: arch for public contracts, design(typecheck) for
designs, dev for source commentary, sprint for any method propagation.
Cost: small to medium; unresolved.**

Directly verified mismatches:

- `src/lib.rs` says typecheck never depends on frontend; its manifest and
  bounded-context dependency table explicitly do. The frontend calls are
  legitimate construction, not evidence of a new boundary leak.
- The facade describes `TypeCheckEnv` table accessors as crate-private;
  `public-api.txt` exposes both. It gives obsolete register/read-site counts
  and promises unconditional failure rollback despite ACT-1073.
- `design/typecheck/typecheck.md` §12 still schedules T5/T7. Current
  `resolve_impl_trait_ref` uses the declaration name and `prepare_trait_impl`
  fills the authored label. ACT-0997 is marked resolved. The table's census
  row also waits on readings already in S124 §14.5. This is stale scheduling,
  not evidence of missing implementations.
- `design/typecheck/hkt.md` cites the absent impl-echo helper, a checker
  finding confirmed by source search.
- The master says every baseline change requires the user's prior approval;
  root guidance instead permits arch approval when its three questions pass.
  Contributors would encounter an unnecessary escalation if they followed
  the lower document alone.

Repair the lower claims and remove delivered planning after extracting any
useful contract. Do not strengthen the implementation merely to match stale
prose or copy public contracts into another inventory. These contradictions
cap the document quality below B even if all remaining links resolve.

### R6 — Trait signatures bypass the primitive import rule

**Priority: medium; owner: QA intake through coordinator, then spec only if
an intended exception is claimed. Cost: small investigation; unresolved.**

Spec §3.1 requires bare primitive type names to be imported or re-exported;
fully qualified names are always available. No trait-signature exception was
found. The resolver's `scalar_fastpath` deliberately preserves an older
exception for trait/HKT signatures.

The following complete no-prelude file exits 0 in the authorized binary:

```clojure
(deftrait T (f [self] Int))
(defn main [] (primitives/Pure 0))
```

Controls, each with that same fully qualified `main`:

| Declaration | Observed |
|---|---|
| `(deftrait T (f [self] primitives/Int))` | Exit 0 |
| `(import [primitives [Int]])` followed by the bare-Int trait | Exit 0 |
| `(defn f [] :Int 1)` with no import | Exit 1, `unknown type Int` |

The subject should reject the unresolved bare type under §3.1. This is an
observed inconsistency, not an unexecuted future hazard. QA should preserve
the minimal failing-not-ignored reproduction and controls and assess the
trait/HKT context distinction before routing a correction. No test was
committed here because the dispatch forbids writing outside `audits/`; the
permanent reproduction is an explicit unresolved handoff. Historical
compatibility language in the resolver design does not authorise a semantic
exception.

### R7 — Normative collection-trait obligations contradict the restriction

**Priority: medium for requirements clarity; owner: spec through sprint.
Cost: small clarification, potentially larger only if behaviour is changed;
unresolved.**

Appendix C is normative under [spec guidance](../spec/AGENTS.md).
[Collection extensibility](../spec/appendix-c-nfr.md#c24-collection-extensibility-s24)
says multi-parameter collection traits MUST be expressible.
[Current restrictions](../spec/07-traits.md#7121-current-restrictions)
explicitly forbid multi-parameter type classes, and the following future
extensions table lists them as unimplemented. The appendix still frames
activation with the retired ring axis.
Neither the single-parameter implementation nor a passing HKT test resolves
these competing requirements.

Ask spec to frame the conflict for the user. This audit makes no choice and
does not prescribe multi-parameter support or acceptance tests under an
invented reading. The conflict is current authority drift even though it
does not block the concrete reproductions above.

## 5. Strengths, residuals and completion

The context remains recognisable and cohesive. It has no scheduler, machine
code generator, filesystem writer or independent deployment surface. The
single type-expression resolver, canonical type identity reader, body frame,
shared child walkers, typed concrete view and shared instance engine remove
real opportunities for drift. Module tests generally live with their owning
seams; joins, fixpoint refusal and negative outcomes receive substantive
controls. Permanent failing tests preserve known defects rather than hiding
them. These strengths support continued delivery but do not compensate for
R3/R4's maintenance cost.

Existing open leads retain their present carriers: ACT-0985's duplicate-impl
question, ACT-0987's primitive-identity/rigidity leads, ACT-1001 P-2's
unreproduced index hazard, and ACT-1034's recorded instance work. Their
remaining behaviour was not exhaustively rerun or re-attributed. Type-size
growth is a user-accepted named risk in `sprints/SPRINT.md`; no exponential
probe or extra bound is proposed. ACT-1067's stack failure remains
unattributed across stages. Neither is silently assigned to typecheck.

Assessment limits: no fresh suite/build/lint/coverage or generated baseline;
no exhaustive requirement-to-test reconciliation; no mutation experiments;
no compile-time profile, release-tier benefit measurement or platform matrix;
no new observation at the imported-instance slot-publication seam. Repository
suite figures and signal outcomes remain explicitly attributed to QA. The
document checker failure remains open with its existing owners.

Final document validation discovers this assessment and reports zero findings
against it. The shared tree's final checker reading is 591 findings (exit 1),
with concurrent edits outside this assessment; it is not a clean repository
gate. Whitespace validation passes. All compiler-probe scratch directories
were removed.

**Next invocation: sprint.** Present R1–R7 for user disposition in the next
Phase 1, reuse existing intakes for R1/R2, and route R6's permanent
reproduction to QA/test under the authorized phase. R3 goes to arch for an
economic decision; R4 to design; R5 to the named document owners; R7 to spec.
No action was filed, source changed, test run or push performed by this audit.
