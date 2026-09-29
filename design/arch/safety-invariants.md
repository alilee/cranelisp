# Safety invariants — the assertion ladder and the foundational-invariant register

**Owner: `arch`.** This document is the maintained register of the invariants
the memory-safety argument relies on (§4), the ladder of mechanisms that assert
them (§2) and the soundness frame for analysis narrowing (§3).
[Principle 25](principles/25-narrowing-carries-its-check.md) is canonical in
the principles index; §5 is its ratification record. The register is re-audited
at every Phase-2 architecture review, and a new safety-eliding surface — a new
analysis, mangle family, persisted carrier or trust boundary — adds its row in
the change-set that introduces it. Arriving unregistered is the defect.

## §1. The class: unsound narrowing of a safety judgment

The memory-model spine rests on monotone soundness
([ownership inference §2.1](ownership-inference.md#21-the-mode-lattice)): every
analysis dimension has a conservative ⊤, and widening toward ⊤ is always safe.
That protects one direction only. Every optimization is a **narrowing** — a
static judgment stronger than ⊤ on whose strength a safety operation is elided:
an RC protect or increment, an atomic RMW, a distinct drop-glue symbol, a bounds
validation, a recompile. Nothing about monotone soundness checks that a
narrowing preserved soundness; a wrong one silently removes the operation and
stays invisible until an input constructs the case the judgment got wrong.

Two structural facts, both paid for in S111:

1. The class recurs anywhere a safety operation is elided by a static judgment.
   Keyed identity (a mangle narrows many semantic identities to one symbol),
   cache trust (bytes narrowed to valid indices), GOT indexing and type-scheme
   generalization all produced the same shape in one sprint.
2. A class closes by assertion mechanism, never by an instance patch. Each
   instance patch needed an adversarial follow-up to find the next layer.

## §2. The assertion-mechanism ladder

For every safety-eliding narrowing and every foundational invariant the design
question is "which is the strongest applicable tier?", and the answer is
recorded in §4.

1. **Unconstructable** ([Principle 18](principles/18-enforce-invariants-structurally.md),
   [Principle 20](principles/20-model-invariants-by-representation.md)). The
   violation has no representation. Often available for a producer seam even
   when a summary — a claim about dynamic behavior — cannot itself be a data
   shape.
2. **By-construction witness.** The narrowing ships a checkable artifact whose
   validity implies the property. Model: `cranelisp_types::drop_glue_symbol_name`
   (`crates/cranelisp-types/src/module.rs`) — every variable-length component
   length-prefixed and hex-encoded, so the mangle is prefix-free and decodable,
   injective for all inputs, pinned by the `module/tests.rs` round-trip battery.
   Rule: every mangle from semantic identity to symbol either ships a decoder
   witness (or is injective by construction with a structure pin) or is
   additionally keyed by a disambiguator (span or discriminator).
3. **Seam assertion.** The invariant is checked exactly where it could break,
   so a violation names its seam the moment it happens. Two sub-forms:
   - **In-process invariant breach ⇒ always-on `assert!`** — a compiler defect;
     located hard-fail, never release UB, never a laundered `Result`.
   - **Untrusted external data (persisted cache, DLL exports) ⇒ diagnosed error
     and safe recovery** at the load boundary (`CacheStale` → recompile;
     layout-hash refusal).
4. **Differential equivalence against the conservative fallback.** For a
   narrowing justified by whole-program analysis, where no local witness
   exists, the optimized lowering must be observationally equivalent (output,
   exit, heap balance) to the conservative lowering, which must stay
   permanently reachable (the analysis-off toggle,
   [ownership inference §6.2](ownership-inference.md#62-the-differential-oracle-r7)).
   The check is a standing nextest-visible lane, `tests/safety_oracle_lane.rs`
   with the `SafetyMatrix` combinator (`tests/helpers/e2e.rs`); lane
   mechanics, corpus policy and cadence are `qa`'s
   (`tests/plan/memory-safety-coverage.md`).
5. **Dynamic self-check lanes.** Properties observable only at runtime (RC
   balance) get a checking mode that converts silent corruption into diagnosed
   failure under test: the allocator-seam diagnostic modes and RC seam checks
   ([diagnostic modes](../intrinsics/diagnostic-modes.md)). They ride tier 4's
   lanes.

Example-based testing and adversarial review are discovery, not checks. A green
suite over examples asserts nothing about the inputs nobody wrote; the ladder
exists so each invariant has a check that quantifies over all inputs (tiers
1–2), all executions through a seam (tier 3), or a maintained equivalence
(tiers 4–5).

## §3. Soundness by construction for narrowing

The ownership transfer walk is a lattice-monotone abstract interpretation whose
rules are enumerated and classified, so an unsound narrowing is a visible rule
violation rather than a fact someone must discover adversarially. The
requirements, realized in the typecheck interior
([ownership inference — typecheck §3.3](../typecheck/ownership-inference.md#33-the-walk-and-its-rule-table)):

- **(a) The origin axis has an explicit ⊤.** On the result-origin axis the
  conservative point is "may reach anything the inputs reach"; `Fresh` and
  unconditional `AliasOf`/`ProjectionOf` are the strong claims that license
  elision. Information loss in the walk moves toward May, never toward a
  stronger claim: a container's origin is at least the join of its elements'
  parameter reach, and the same rule governs capture and element-store-return.
- **(b) The producer seam is unconstructable.** Conditional and unconditional
  origins are distinct variants (`Origin::{Unconditional, Conditional}`,
  walk-internal in `crates/cranelisp-typecheck/src/ownership/transfer.rs`),
  and the hard-claim publish arms match only the unconditional variant.
  Publishing a hard claim from a conditional origin has no representation.
- **(c) The rule table is enumerated and normative.** One row per construct,
  each classified widening (always admissible), precision-preserving, or
  narrowing (admissible only with a named justification recorded on the row).
  `review` rejects a `transfer.rs` change that adds or alters a rule absent from
  the table. The table, not the example pins, is the completeness argument.
- **(d) The end-to-end discharge is tier 4.** The conservative all-`Owned`
  lowering is the definition of correct behavior for the memory model; an
  elision is correct iff equivalent to it, and an elision that cannot keep its
  conservative twin reachable is inadmissible. Keyed identity routes to tier 2
  and persisted trust to tier 3 instead — their "conservative fallback" is
  per-identity uniqueness and diagnosed refusal, not a toggle.

## §4. The foundational-invariant register

**Status vocabulary**, descending strength: `unconstructable` (tier 1) ·
`witnessed` (tier 2) · `asserted` (tier 3) · `gated` (tier 4 standing) ·
`dynamic-lane` (tier 5) · `matrix-tested` (example pins with a completeness
argument) · `example-tested` (the gap) · `unasserted` (the hole). A row at
`example-tested` or `unasserted` is an open item against `arch`: it gets a
mechanism, or the row records why none is reachable.

**Detection-proof requirement.** `asserted`, `gated` and `dynamic-lane` each
require a cited capability proof on the row: the test that plants the fault and
observes detection (fail-on-revert for gates and seam asserts, per-variant
negatives for validators, planted triggers for lanes and modes), or a named
live catch of a real defect. Without the citation the honest status is
`asserted-but-unproven` (`gated-but-unproven`, `lane-unproven`), ranked below
`matrix-tested` and equally open. The citation should name the fault class
planted, because its complement is the instrument's blind spot — and a blind
spot is invisible exactly while the instrument is green (R7's history). An
existence claim about a mechanism is not a capability claim about the
instrument.

**Row candidates pending `arch` disposition:** FIXME 0776 (an operation run at
N non-equivalent seams needs an enumerated seam taxonomy) and FIXME 0783 (a
syntactic node-kind test standing in for the derived answer). Neither is a row
until ruled.

| # | Invariant (what safety relies on) | Status | Mechanism owed | Owner / seam |
|---|---|---|---|---|
| R1 | **Ownership-summary truth** — no published summary or mode lets a consumer elide a protect, increment or atomic the dynamic behavior needs | §3 mechanism landed: lattice and rule table (typecheck design §3.3), producer split (`transfer.rs`); tier-4 `gated` through R9. Chained may-alias links are covered by rule composition — a conditional origin carries the spans of every `MayAliasOf` link on its chain and the projection rule forces the escape fact at all of them ([typecheck design §4.5](../typecheck/ownership-inference.md#45-may-alias-links)) | Contingency, routed to `arch` when triggered: a link created inside an imported, summarised user function whose caller-frame span cannot drive the backend retain must ride the summary — a `cranelisp-types` carrier and schema change (typecheck design §4.5, §12) | `design`(typecheck) `ownership/transfer.rs`; `qa` gate |
| R2 | **Elision-consumer safe default** — an unknown or new summary variant keeps the safety op | `unconstructable` (exhaustive `ResultMode` matches, no `#[non_exhaustive]`). Re-verified S121 on the `MayAliasAny` landing: exactly two silent `== Fresh` reads (backend `return_is_fresh_by_summary`, types `ModeSummary::is_abi_conservative`), both safe-direction; no third binary read ([interfaces — ownership-inference carriers](interfaces.md#ownership-inference-carriers)) | Maintain: `review` re-runs the `_ =>` / `== Fresh` census on every variant landing | landed (types + backend) |
| R3 | **Declared-fact truthfulness and reachability** — a primitive whose emission deviates from the consuming convention carries declared, reachable facts | `matrix-tested` (whole-table sweep, 5-site/1-helper pin) | Evaluate single-sourcing the emission convention as one artifact consumed by both `crates/cranelisp-primitives/src/ownership_facts.rs` and backend `vec_codegen`; today the declaration and the emission are prose-tied twins in two crates ([Principle 07](principles/07-single-source-of-truth.md)) | `design`(backend + primitives) |
| R4 | **Keyed-identity injectivity** — every mangle from semantic identity to symbol is injective or additionally disambiguator-keyed | Census complete ([S115 backend design §4](../backend/s115-carrier-and-rc-sweep.md#4-r4--mangle-family-injectivity-census-owed-o3-deliverable-4)). Drop glue `witnessed` (§2 tier 2). GOT data symbol `witnessed`: `crates/cranelisp-types/src/module.rs::got_data_symbol_name` is injective by construction over the non-platform domain with a round-trip battery. Inner-fn, closure/curry glue and trait-method-value wrapper names disambiguator-keyed (span + discriminator; `crates/cranelisp-backend/src/compiler/resolution/tests.rs`). Typecheck's `$`/`+`-join instance mangle stands: it is a keyed-identity mangle — a pure function of home, name and concrete argument types — not a resolution product carried past a seam, so it belongs to this row's census and not to the carrier contract. Platform export names uniqueness-keyed | **Recorded residual:** a platform whose name begins `d`, `h`, `u` or `_` could collide with the escape image of a contrived root-module spelling; the close is loader-side platform-name validation, not a mint change | types mint: `arch`; loader validation: `design`(platform) |
| R5 | **GOT index in range** — every slot read or write is below the table size; allocation is fallible | `asserted-but-unproven`: always-on `assert!` in `GotTable::{store_slot, load_slot}` (`crates/cranelisp-types/src/got.rs`), fallible allocation, and the cache-seam diagnosed error for both persisted slots — `callable_got_slot()` and `borrowed_sibling_slot` — under R6 (`CacheStale::{GotSlotOutOfRange, SiblingSlotOutOfRange}`). No planted out-of-range cell exercises the in-process assert (`crates/cranelisp-types/src/got/tests.rs` has none) | A planted out-of-range cell at the in-process seam. The borrowed-sibling slot is validated at the load boundary by the R6 census (FIXME 0637 resolved 2026-09-24) | `arch` (types) with `qa` allocation |
| R6 | **Persisted-index trust boundary** — every index, key or slot deserialized from `.meta.json` is validated at load; a violation is a diagnosed `CacheStale`, never trusted into emission | `asserted` — proven. One validation loop in `deserialise_meta_with_build_id` (`crates/cranelisp-backend/src/cache/serialize.rs`; the census table is that module's rustdoc — five families, one `CacheStale` class each). Per-class planted-corruption cells and the false-fire fence in `crates/cranelisp-backend/src/cache/serialize/tests.rs` (spec-annotated §4 R6) | Maintain: a new persisted index adds its row and arm in its introducing change-set (the `WrittenTraitImpl` carrier did — [trait-implementation persistence](trait-impl-cache-carrier.md)) | `dev`(backend, cache); `review` census completeness |
| R7 | **Terminal-table export closure** — a module never accepts a new public entry outside its declared export closure (spec §8.6.4's mechanical shadow; the prelude case is the motivating instance) | `asserted` (tier-3 diagnosed error) — proven at the unit boundary. The one chokepoint `src/imports.rs::check_exposed_candidate_closure` rejects an out-of-closure public candidate in every build with a message that self-identifies as an R7 breach; import installation and `commit_staging_to_live` (`src/worker.rs`) route through it. Cells `src/imports/tests.rs::{candidate_closure_rejects_out_of_closure_public_write, candidate_closure_rejects_provided_name_outside_declared_exports, candidate_closure_permits_name_in_declared_exports, candidate_closure_permits_when_declared_exports_unknown, candidate_closure_generalizes_beyond_prelude}` plant the fault and the negative legs. Acceptance record: [prelude-table write isolation §4](../int/int.md#67-public-candidate-exposure--the-export-closure-gate). The predecessor guards were provider-existence-shaped and blind to the live phantom; the phantom was never re-induced after the gate landed | Maintain: a public-insert seam that bypasses the gate is a `review` finding. Falsifier: a public write reaching a live table without passing candidate exposure | `dev`(src); `design`(int) |
| R8 | **RC balance** — every allocation has exactly one net free; scope decrements match increments | `dynamic-lane`: quarantine (M1), scrub (M2) and alloc/free parity (M3) modes plus the A1–A4 RC/alloc seam checks, env-gated and byte-identical off, hooked on the two single-sourced funnels (`crates/cranelisp-intrinsics/src/diagnostics.rs`; [diagnostic modes](../intrinsics/diagnostic-modes.md)); unit synthetic self-tests per mode (`diagnostics/tests.rs`). Production stays unasserted by design (cost) | The modes' grades at the production funnels are awaited, never assumed: FIXME 0848 (`dev`: fault-plant hook and fail-on-revert proofs) and FIXME 0857 (`qa`: per-mode regrade, dead citation repaired) | landed (intrinsics + backend); `qa` lanes |
| R9 | **Differential-oracle equivalence** — analysis-on ≡ analysis-off observationally and heap-balanced (the meta-invariant of §3d) | `gated` — proven: acceptance was a defect RED under the lane (fail-on-revert by construction) and the lane has a named live catch (MS-P7, a `--link`-only COW UAF). Lane: `tests/safety_oracle_lane.rs` + `SafetyMatrix` | Maintain; corpus grows with the matrix shapes (`tests/plan/memory-safety-coverage.md`) | `qa`-owned lane |
| R10 | **Resolve-once keyed reads hard-fail** ([Principle 24](principles/24-resolve-once.md)) — downstream consumers never re-derive; a miss is a diagnosed error | `asserted`, proof partial by seam. Call and value seams proven: `crates/cranelisp-backend/src/compiler/apply/keyed_miss_tests.rs` and `crates/cranelisp-backend/src/compiler/control_flow/fn_as_value/keyed_miss_tests.rs` each observe their hard-error arm fire. Pattern seam `asserted-but-unproven`: `compile_constructor_pattern` (`crates/cranelisp-backend/src/compiler/match_codegen.rs`) has two hard-miss arms (carrier-`None`, entry-miss) and no test asserts either message family; a revert to a lenient arm would pass every positive suite | One negative cell per pattern-seam arm in the call-seam shape — ACT-0968 (`dev`, backend module tier; `dev` reports which seam fires if the harness refuses earlier). On landing, cite the cells here and restore the full proof | mechanism landed (backend); `dev`(backend) via ACT-0968; `qa` allocation |
| R11 | **Concreteness at codegen** — no `Type::Var` reaches RC classification, slot emission or a mangle: I-CONC (only a concrete signature has a callable slot), I-FRAME (every compiled frame and emitted site is concrete), I-EMIT (the emitted tree references no polymorphic callable) — [total concreteness §2](total-concreteness.md#2-the-invariants). Rationale retained: the S84 form was stated over a table with unstated exceptions, so it was asserted nowhere and two hand-mints violated it while this row read `unconstructable`; the cure removed the exceptions instead of partitioning the invariant | I-CONC `unconstructable` for a fresh claim (`CallableSlot`'s field is private; every settlement funnel converts through `ConcreteType::from_type`); the retained `Life::Declared { prior }` conforms and is `asserted` with a falsifier (a read of `prior` outside the lifecycle funnels reaching slot emission — QA's 2026-09-21 census found none); `asserted` at the load boundary (`SymbolTable::validate_lifecycle`, planted cell `crates/cranelisp-types/src/module/tests.rs::load_validation_rejects_nonconcrete_and_out_of_range_claims`, positive leg only). I-FRAME body path `unconstructable` (`MonoExpr` has no variable case); signature path is R17. **I-EMIT not delivered**: `bind`, `race`, `select`, `catch-runtime-error` remain polymorphic host-promised entries referenced by name; the closed roster is pinned by `src/bootstrap.rs::bootstrap_generic_uniform_body_roster_is_closed` | The I-EMIT dispositions ([total concreteness §3.3](total-concreteness.md#33-the-uniform-realization-roster)): re-kind `bind`/`race`/`select` inline after MEASURE-RK; per-instantiation instances for `catch-runtime-error`. No filing carries them — `sprint` schedules or records an owned deferral. FIXME 0931's evidence disposition. R17's arm flip | `arch` contract; `design`(typecheck/backend/int) for I-EMIT; `qa` for the 0931 evidence |
| R12 | **Published-pointer retention** ([Principle 22](principles/22-published-pointers-have-retention-owners.md)) / ABI-epoch slot freeze, per table; a whole-file rebuild reissues indices under its quiescent-boundary obligations instead ([symbol-table lifecycle §4.3](symbol-table-lifecycle.md#43-slot-identity)) | Grade **not re-established this pass**. Landed: the commit gate is the single slot-policy authority ([session transaction §7.1](../int/session-transaction.md#71-the-commit-gate-is-the-single-slot-policy-authority)) and `got_trace` records slot-freeze events; ABI-epoch versioning is conservative for non-concrete targets (`src/redefine.rs`, reuse-and-patch), and S121 rejects a same-type live replacement whose `ModeSummary` would change (ACT-0953). Whether a seam assertion fires on a write to a frozen slot was not read | `design`(int) states the grade with its detection proof, or records `unasserted`. Design home: [ownership inference §5.6](ownership-inference.md#56-commit-soundness--abi-epoch-slot-versioning-no-stop-the-world) | `design`(int); `arch` for ACT-0953 |
| R13 | **Fork-join error-slot ferry** — a worker panic reaches the join; no silent swallow (spec §12.4.3) | Unit-boundary `asserted` — proven: `crates/cranelisp-intrinsics/src/ivar/tests.rs::{test_ivar_force_ferries_panic_to_joiner, ivar_force_backoff_wait_reraises_ferried_panic, ivar_inline_claim_dual_panic_first_error_wins}` plant both ferry polarities and the first-error rule | One integration assertion at each distinct production fork→join composition boundary through the scheduler/reactor; do not rebuild the proven IVar mechanism | `qa` integration tier with `design`(intrinsics) boundary census |
| R14 | **COW count-truth** — the runtime `rc == 1` in-place branch is sound iff every live independently owned reference is counted; an uncounted (borrowed) source reaches a COW op only under an analysis-proven bound; analysis-off counts everything | Partial. Toggle-off classifies every COW source `Owned` ([backend ownership codegen §13.7](../backend/ownership-codegen.md#137-cow-mutate-and-grow-branches--the-settled-contract)); the escape-fact correction and the immediate projection face landed (S115); chained faces are covered by R1's rule composition with the negative control stated there (a chain returned whole is projected by the caller) | The R1 imported-link contingency; checks are the tier-4 lane and R8's DEC_CHECK | `design`(typecheck) links; `dev`(backend) consume seam |
| R15 | **Transitive discharge and typed-context ownership** — replacing or releasing an owned heap slot discharges every transitively owned field at any finite depth; where static type is no longer carried, ownership has already transferred to a named type-aware releasing owner. Retain the two-word `HeapHeader`; no type word, no generic type-erased deep release | Mechanism landed: one named `drop<T>` per concrete owning type through `DropGlueRegistry` and `drop_glue_symbol_name`; `MAX_DROP_GLUE_DEPTH` and the shallow-dec fallback removed ([transitive drop glue §1](../backend/transitive-drop-glue.md#1-binding-outcome)); the result exit narrows once to `ConcreteType` and reads glue through the keyed contract ([result owner](../int/result-owner.md)). Glue identity is structural (one emitter); release-gate correctness is `asserted` pending the open items | FIXME 0903 (the heap-binding release gate is keyed on type, must be keyed on frame) | `design`(backend) glue/TCO/artifact; `design`(int) result boundary; `qa` displacement/exit matrix |
| R16 | **Structural embedding takes exactly one reference** (RE-1/RE-2) — a runtime helper that embeds an existing heap structure into a new one by pointer takes exactly one `rc_inc`, on the node it stores; the inc count for one embed is 1 regardless of the embedded structure's size. Dual: every `cranelisp-intrinsics::drop::consume_*` releases the one handed reference and descends only on the last | `asserted` — proven (RED-first, fail-on-revert): `crates/cranelisp-primitives/src/marshal/tests.rs::{re1_embed_takes_exactly_one_reference_whatever_the_tail_size, re1_embed_inc_tally_is_one_per_call_plus_one_per_copied_item}`; fault classes bounded: producer over-inc, deep-walk regression, move-variant | Maintain: a new embedding producer adds its inc-count fence in its introducing change-set. The typed-handle option ([ownership-stratum options](ownership-stratum-options.md#2-option-1--typed-handle-discipline-in-the-runtime-pair)) would raise this row toward tier 1 | `dev`(runtime pair) `marshal.rs`; statement [structural embedding §2](../runtime/s118-structural-embedding-ownership.md#2-the-invariant-stated-declaratively) |
| R17 | **Heap category before RC operation** (contract rule R-1) — no RC operation is emitted on a word whose heap category codegen cannot name from the word's own static type. A residual type variable is the absence of a category, not `Mixed`; the nullary-tag threshold discriminates tags from pointers, never scalars from pointers | `unasserted`. The violating seam stands: `Err(_) ⇒ HeapCategory::Mixed` in `signature_heap_category` (`crates/cranelisp-backend/src/compiler/rc_emission.rs`), measured S119 at 3,646 bare-`Var` licences with two reproduced SIGSEGVs ([release contract §2.3](../backend/non-concrete-release-contract.md#23-census-b--the-retain-seam-signature_heap_categorys-err--mixed)). The declaration channel feeds it structurally: `extract_constructor` (`crates/cranelisp-backend/src/compiler/context.rs`) materialises constructor field types from the declaration's scheme, so a polymorphic product's field type is permanently `Type::Var`; the arm-flip criterion is unreachable while it stands (NC-5, `tests/plan/s119-test-plan.md` §3.7) | The permanent debug-profile census ([release contract — the category census](../backend/non-concrete-release-contract.md#73-the-category-census-armed-open)), then the per-family flip of the arm to a located error on measured zero traffic ([the R-1 structural close](../backend/non-concrete-release-contract.md#74-the-r-1-structural-close-open)). Declaration-channel cure: field-type materialisation delegates to the types-owned refusing projection `ctor_field_concrete_types` (`crates/cranelisp-types/src/heap.rs`) or an instantiation-substituting sibling beside it — never a hand-rolled scheme walk. End state `asserted` | `dev`(backend) `rc_emission.rs`; `design`(backend) `CtorMeta` |
| R18 | **No fabricated concreteness** (contract rule R-2; Principle 25 on the type channel) — no component presents a downstream gate with a type, category, shape or mode more concrete than it knows. An unsatisfiable gate is a producer obligation, never a licence to invent. Model spellings: `crates/cranelisp-typecheck/src/program/support.rs` (explicit `ViewBuildError::NotConcrete` match) and `ctor_field_concrete_types` (`crates/cranelisp-types/src/heap.rs`, one residual field refuses the whole constructor) | `unasserted`. Instance census, re-located at source 2026-09-24: (1) the R17 `Err ⇒ Mixed` arm — open; (2) the type-keyed shallow-dec arm — discharged with R15; (3) `lenient_from_expr`'s `unwrap_or(ConcreteType::Int)` placeholder (`crates/cranelisp-types/src/mono_expr.rs`) — open, staged retirement per its rustdoc and FIXME 0931; (4) fixpoint residual-parameter seeding — discharged (residual frames are excluded from the walk and publish nothing; FIXME 0929 note); (5) `unwrap_or(ConcreteType::Int)` for a missing Vec element type in `crates/cranelisp-backend/src/drop_glue.rs` — open, located refusal owed; (6) `unwrap_or(Type::Int)` in `extract_constructor` (`crates/cranelisp-backend/src/compiler/context.rs`) — open, rides the R17 cure; (7) a defensive dead arm in `fn_compiler.rs` — not re-located this pass, spelling only; (8) int defaults to `Type::Int` for an absent display or expression type (`src/pipeline.rs`, `src/repl/commands.rs`, `src/eval.rs`) flowing toward the R15 result seam — severity ungraded | Backend: R17's census and arm flip; typecheck: settlement and installation gated through types-owned operations, residual defaulting with a strict-retry self-check and located refusal ([producer obligations §3.3](../typecheck/non-concrete-producer-obligations.md#33-the-mechanism-and-its-self-check)); `design`(int) grades (8). Enforcement ruling (2026-07-27, census-as-enforcement): `ConcreteType`'s variants stay `pub`; the NC-2 two-family census allow-list (`tests/plan/s119-test-plan.md` §3.7) is the standing detector — a new site REDs the cell in its own change-set. Once landed with its detection proof the residual grade is asserted-with-a-named-falsifier | `dev`(backend), `dev`(typecheck), `design`(int); FIXME 0929 carries the census |
| R19 | **IO-node stamp writes are tag-licensed** — a post-call store into a returned IO node is licensed by the returned node's tag, never by the call target's kind alone, and each arm's offset is in bounds for that tag's layout | Mechanism landed; `asserted-but-unproven`. The post-call stamp in `crates/cranelisp-backend/src/compiler/apply.rs` dispatches on the returned node's tag ([total concreteness — the platform-return seam](total-concreteness.md#the-platform-return-seam--stamps-are-tag-licensed-r19)); `crates/cranelisp-backend/src/compiler/apply/platform_fn_name_stamp_tests.rs::platform_return_stamps_are_tag_dominated_for_heap_and_scalar_payloads` walks control flow for tag dominance of both stores. No fail-on-revert observation of that cell is cited. The defect it replaced: a kind-keyed unconditional store out of bounds for a returned `Pure` node | A cited fail-on-revert observation of the tag-dominance cell (`qa` allocation); then the row grades `asserted`. End state structural: no store emittable outside its tag arm at the one chokepoint | `dev`(backend); `qa` acceptance |
| R20 | **An IO value is a reusable description of work** (user ruling 2026-09-21; `spec/10-io.md` §10.8.1 owns the language statement): forcing one node any number of times, sequentially or concurrently, is valid and memory-safe. A force never moves a field out of a published node; references are discharged only by `free_io_node` at count zero. `Pure` retains its payload; `Effect` owns a repeatable `Fn + Send + Sync` thunk (platform ABI 11) | Delivered and integrated (S122; the generated platform baseline user-confirmed 2026-09-21, final QA adequate). Per-property grades: [total concreteness — grades](total-concreteness.md#grades): `Pure` retain and teardown **measured**; thunk thread-safety **structural**; no store to a published node **asserted with a falsifier** (a non-construction store to such a node's field in intrinsics); one `rc_inc` inverse of one `drop<T>` per payload category **asserted with a falsifier** | Residuals are separate intakes, not accepted semantics: `Launch` still moves its sub-tree out through a non-atomic sentinel and `EffectPoll` re-enters one state closure (second forces unmeasured); the severed join (pre-existing use-after-free window); the abort-path leak; DLL-side capture-panic containment (asserted with a named falsifier) | `qa` intakes; `design`(intrinsics/platform) |
| R21 | **A published summary is a converged claim** — a present `ModeSummary` is derivable only from a converged transfer walk; no other constructor of a published summary exists. Corollary: a present `result: Fresh` is the strongest result claim and is never minted as a recovery literal; the conservative spelling of a whole summary is its absence ([ownership inference §6.1](ownership-inference.md#61-the-conservative-point-is-total)) | **Regraded 2026-09-24 — the refusal landed.** `compute_cluster_with_cap` (`crates/cranelisp-typecheck/src/ownership/fixpoint.rs`) refuses the whole cluster on cap exhaustion and residual-parameter frames publish nothing; the publication funnel (`ownership/publish.rs`) refuses too; the literal constructors (`top`, `reset_to_top`, `conservative_site_facts`) no longer exist. Grade: **structural** for the constructor; **asserted with a named falsifier** for the queue — a walkable member queued and never walked ([typecheck design §10.2](../typecheck/ownership-inference.md#102-refusal)). Measured instrument: the refusal trace line (`crates/cranelisp-typecheck/src/ownership/trace.rs`); cells `crates/cranelisp-typecheck/src/ownership/fixpoint/tests.rs::{cap_exhaustion_refuses_the_cluster_and_publishes_nothing, cap_exhaustion_refuses_site_facts_and_uniqueness_too, uniqueness_cap_exhaustion_refuses_the_whole_cluster, a_converging_cluster_refuses_nothing_and_publishes_a_full_summary_map}` (positive and negative legs), `crates/cranelisp-typecheck/src/ownership/publish/tests.rs::a_refused_cluster_publishes_nothing_through_the_funnel`, `crates/cranelisp-typecheck/src/ownership/trace.rs::the_refusal_line_names_the_stratum_and_its_budget` | The absent-callee `Fresh` premise remains asserted with its falsifier stated at [typecheck design §10.4](../typecheck/ownership-inference.md#104-an-absent-callee-result-reads-fresh); attributing its two populations is `qa`'s. A second construction site of a published summary found by a later census falsifies the structural claim | `dev`(typecheck) `ownership/{fixpoint,publish}.rs`; `qa` reachability falsifier |

## §5. Principle 25 — ratification record

Principle 25, *Narrowing carries its check*, was authored here as the S111
memory-safety assessment's candidate and **ratified by the user at the S111
Phase-7 close (2026-07-18) as a single principle** — the split into a
differential-checkability principle and an assert-at-seam principle was offered
and declined. Its text lives only at
[principles/25](principles/25-narrowing-carries-its-check.md); cite it from
there. §§2–4 here are the frame it governs.

## §6. Cascade status

The S111 `design` cascade, by task, so the citations to it stay readable:

1. Monotone walk, rule table and producer split — landed S113 (R1).
2. Backend censuses: (i) every safety-eliding consumer read mapped to its
   summary premise and safe-direction default (the R2 discipline made
   complete) — **open**, `design`(backend); (ii) symbol-mint census — landed
   S115 (R4); (iii) see R5.
3. Persisted-trust boundary census and the one validation seam — landed S115
   (R6).
4. Live-table seam assertion for the export closure — landed as the one
   diagnosed chokepoint (R7); R12's slot-freeze grade is owed separately.
5. Tier 4 as a standing nextest-visible gate — landed S113 (R9).
