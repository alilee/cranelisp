# Sprint 121: Release rebaseline and FIXME closure

**Status**: CLOSED — 2026-09-09, with explicitly accepted residuals.
The Phase-5 green checkpoint is historical, not the final whole-suite result.
The accepted outcome and evidence are in
[the closure outcome](#outcome-phase-7).

**Goal**: Restore a clean, attributable release baseline and drain the legacy
filing backlog by verifying every live FIXME and action against current source
or executing evidence, resolving stale records, and delivering a quality gate
that distinguishes product defects from repository and environment failures.

**Audit**: `src/` proposed — the unspent rotation carried by the Sprint 120
out-of-rotation assessment; confirmed at Phase 4 per `sprints/METHOD.md` §2.7.

## Phase approvals

| Transition | Checkpoint presented | User approval | State |
|---|---|---|---|
| Phase 6b → Phase 7 | Accepted residuals, archive, roadmap, commit and push; contribute reviewed package changes at close, adopt upstream at next opening | 2026-09-09, “approved to close the sprint, commit and push”; contribution/adoption separation confirmed, “proceed” | approved; closed with accepted residuals |
| Start → Phase 1 | User requested a FIXME-cleanup and project-rebaseline sprint with a sound quality gate | 2026-08-31, initiating request | approved |
| Phase 1 → Phase 2 | This scope draft and its architecture-review proposal | 2026-08-31, “proceed” | approved |
| Phase 2 → Phase 3 | Architecture outcome and Phase-3 proposal | 2026-09-01, “approvedd” | approved |
| Phase 3 → Phase 4 | Readiness outcome, wave braid and efficiency controls | 2026-09-01, “adopt those learnings and proceed to next phase” | approved |
| Phase 4 → Phase 5 | Wave plan and Phase-5 proposal | 2026-09-01, “lets proceed with sprint” | approved |
| Phase-5 wave replan | Isolate name-candidate convergence as W3, then resume the remaining crate streams | 2026-09-02, “otherwise agree”; Packet B public API approved 2026-09-02, “yes” | approved; W3 realizing |
| Packet-B realization corrections | Preserve primitive ownership at extern/inline birth and expose read-only all-candidate enumeration | 2026-09-02, “approved” | approved; realized in `cranelisp-types` |
| Packet-A1 generated baseline | Exact combined Packet-A1/Packet-B `cranelisp-types` baseline | 2026-09-02, “yes” | accepted and baselined; independent re-review PASS |
| W3 use-site candidate selection | Private typecheck carrier, syntactic filtering, isolated HM trials, fixed-point settlement and canonical writeback | 2026-09-02, “approved” | approved for implementation; QA evidence delta next |
| W3/C3/W4 typecheck repackage | Retain one typecheck reservation so candidate settlement and the existing overload lifecycle are completed through one progress-aware driver without reopening the same source | 2026-09-02, “approved” | approved; realizing as one crate stream |
| Checked-body ledger and private-state cleanup | Private body-occurrence ledger plus the five-item cleanup basket in `design/typecheck/checked-body-publication.md` §11; no public API, schema, ABI or language change | 2026-09-03, “approved” | approved; realizing inside the retained typecheck stream |
| Packet C public API | Exact additive `instantiate_demands` signature and crate-root re-export proposed in `design/arch/bounded-contexts.md` §2; no dependency, schema or platform-ABI change; forecast one typecheck baseline line | 2026-09-02, “approved” | implementation authorized; generated baseline confirmation remains pending |
| Packet-A accessor API derivation | Architecture may derive the exact types-owned atomic same-type accessor replacement/candidate-reconciliation proposal | 2026-09-02, “approved” | complete; exact two-method proposal returned |
| Packet-A accessor public API | Exact `replace_unpublished_synthesized_template` and `replace_unpublished_synthesized_concrete` methods recorded in [S121 lifecycle record](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md) | 2026-09-02, “approved” | implementation authorized; generated two-line types baseline confirmation remains pending |
| Packet-A accessor generated baseline | Exact incremental two-line `cranelisp-types/public-api.txt` result after implementation | 2026-09-03, “yes” | confirmed; Packet-A public gate complete |
| Root set-doc metadata API | Exact additive `SymbolTable::set_plain_callable_docstring` proposal in [S121 lifecycle-public-api-review record](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/s121-lifecycle-public-api-review.md); implementation and generated baseline are separate gates | implementation approved 2026-09-03, “yes”; generated line confirmed 2026-09-03, “approved” | public API gate complete; types 255/255, review clean and QA-released to root consumer |
| Root compiled-publication API | Exact additive `CompiledPublicationRejection` and `SymbolTable::publish_compiled_staged` transaction in [S121 lifecycle-public-api-review record](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/s121-lifecycle-public-api-review.md) §11; existing owner-free `publish_staged` remains unchanged | design approved 2026-09-03, “ok”; exact generated twelve-line baseline confirmed 2026-09-03, “yes” | public API gate complete; types 262/262, independent review clean and QA-released to root publication consumer |
| Macro compilation checkpoint | A `defmacro` commits its complete expansion-time closure after that macro typechecks and codegens; a later form failure does not roll it back; nonmacro definitions retain one all-or-nothing HM cluster. Delete the unpublished candidate-world mechanism and resume after dependency gaps from source position, never compiled candidate state. | 2026-09-03, “ok” | normative, architecture and int-design carriers **converged** (verified 2026-09-03 at handover); source held for QA readiness |
| Explicit callable retirement semantics | `StagedPublicationDecision::ChangeAbi` may explicitly retire a live slotted callable with no staged replacement; omission alone never removes a binding. The old slot is tombstoned and frozen, its owner is displaced, and mixed replacements/removals validate before mutation. Macro shrink selects only exact private `MacroClause` rows belonging to its staged parent. | 2026-09-03, “yes” | public semantic contract approved; no Rust signature, generated-baseline, schema, backend, platform or ABI delta expected |
| Macro dependency publication clarification | Correct §9.12.1 so dependency modules publish independently before the defining module's atomic parent/active-clause/generated-realization checkpoint and survive parent failure | 2026-09-03, “yes” | specification corrected; QA's sole readiness HOLD closed |
| `/search` macro boundary | Sprint 121 excludes macro declarations from every search feed and does not execute macros while indexing unloaded source. A complete semantic index through the normal compiler is future work, not an index-only macro representation. | 2026-09-03, “write an action for it as future expansion, and avoid the macro problem eg. ignore macros in /search” | `repl/spec.md` §17.19 reconciled; implementation and negative evidence green; [ACT-0952](../actions/ACT-0952-complete-semantic-search-indexing.md) records the separately gated expansion |
| Root-review correction and session-constructor API | Use a stack-only move-only publication receipt settled on every Done/Gap/Err route; delete the no-op binding closure gate in favor of the candidate-shaped gate; complete MC-1–MC-13 safety fences; make bootstrap lifecycle construction fallible with `CompilerSession::new(...) -> Result<CompilerSession, CranelispError>`. | 2026-09-04, “yes” | architecture/design documentation and finding-scoped realization authorized; no scheduler mailbox or persisted receipt state |
| Redefinition simplification | Same-language-type body redefinition remains legal with callers and patches the existing slot. A language-type-changing redefinition is legal only when the existing definition has no callers; otherwise reject it before publication, retain the live definition and require a new name. | 2026-09-04, “first reading was the intended one” | supersedes the redefinition-cascade/receipt branch; exact caller boundary and hidden ABI treatment return to specification and architecture before implementation |
| Redefinition dependent lookup | A blocking dependent is a committed settled definition whose stored `callees` contains the target in call or value position, whether or not codegen has run. Derive dependents on demand by reverse-scanning the live tables, normalize concrete instances to their base callable, and exclude only the target's self-edge. | 2026-09-04, “happy to proceed with this” | approved; no stored callers map, cache-schema change or public API change; overload and macro boundaries remain at the user gate |
| Redefinition visibility | Declaration visibility is immutable for an existing canonical callable or macro name during live redefinition: `defn`↔`defn-` and `defmacro`↔`defmacro-` changes are rejected. A visibility change requires persisted-source reload/restart or a new name. | 2026-09-04, “yes” | approved; prevents live import/export/glob/prelude/macro-resolution tables from diverging; matches the already-approved structural/interface lock for types and traits; exact consolidated normative wording remains at the user gate |
| Redefinition rejection diagnostic | A rejected callable language-type change identifies the canonical target, old and proposed language types, and every direct blocking dependent after normalization/deduplication, sorted by canonical name; it tells the developer to retain the old type or introduce a new name. Transitive callers are excluded. | 2026-09-04, “yes” | approved; required information and ordering are normative, punctuation/layout remain implementation-defined; overload-family blockers are collected across the family before deduplication |
| Macro-clause blocker display identity | When a compiler-private macro clause is a direct blocking dependent of an ordinary callable, dependency storage remains on the clause but the rejection diagnostic normalizes it to the authored canonical macro parent. Multiple blocking clauses of one macro deduplicate to one parent; distinct macro parents remain distinct blockers. | 2026-09-04, “yes” | approved; compiler-generated clause names remain implementation-defined and never leak into the user-facing diagnostic; exact normative wording remains at the user gate |
| Multi-slot publication atomicity | Atomic overload-family and whole-pair `impl` replacement is a turn/publication guarantee: validate and compile the complete unit, leave the complete old unit on failure, expose no partial candidate through resolution/introspection, and ensure calls begun after successful confirmation use the new unit. It is not a generation-snapshot guarantee for computations already running concurrently with the redefinition. | 2026-09-04, “yes” | approved; avoids shared family-generation indirection and per-call runtime cost; exact normative clarification remains at the user gate |
| Generic same-type redefinition | A same-language-type generic body edit eagerly rematerializes every existing concrete realization as one base-plus-realizations candidate and patches their existing slots. Callers are not re-typechecked or recompiled; future demands instantiate from the new template. Any candidate failure retains the complete old generic definition and realizations. | 2026-09-04, “yes” | approved; preserves the ordinary late-binding guarantee for already-realized generic calls without reviving dependent cascades; exact normative clarification remains at the user gate |
| Redefinition declaration class | Live redefinition of an existing canonical name must preserve its declaration class. Single- and multi-signature `defn` remain one callable class governed by §§18.1–18.3; `defmacro`, `deftype`, and `deftrait` are separate classes. A class change is rejected atomically and requires persisted-source reload/restart or a new canonical name. | 2026-09-04, “yes” | approved; distinct-canonical candidate ambiguity remains unchanged because this rule concerns one identical canonical identity; exact normative clarification remains at the user gate |
| Interim live-slot ownership compatibility | Until slot ABI is decoupled from ownership inference, a same-language-type replacement of any existing live Cranelisp callable slot is legal only when its ABI-bearing parameter and result modes are compatible under `ModeSummary::abi_eq_opt`; advisory-only summary changes remain legal. An ABI-bearing mode change rejects atomically with prior body/source retained and a diagnostic explaining unchanged language type versus changed ownership ABI. This covers ordinary functions, overload members, existing generic realizations, and materialized impl methods; macro clauses retain their separate fixed ABI. A caller-free language-type change may use a fresh slot and mode; reload/restart recompiles coherently from source. | 2026-09-04, “yes” | approved as an explicit temporary language restriction, not a hidden implementation limitation; supersedes the proposed universal consuming-slot ABI redesign; exact normative wording is applied at `repl/spec/18-redefinition.md` §18.1.2 and the future decoupling action remains open |
| Redefinition concurrency scope | The actual REPL does not proceed while watcher changes are compiling: `poll_and_reload` waits for reload completion before the prompt can evaluate another form. Sprint 121 therefore adds no publication clock, generation witness, concurrent-cache admission rule, or macro-cutover mechanism. The unused public asynchronous `CompilerSession::re_register_module` wrapper remains unchanged while restoring a good build. | 2026-09-04, “minimise the change until we get a good build - let's proceed” | architecture narrowed to the existing synchronous REPL boundary; [ACT-0954](../actions/ACT-0954-review-asynchronous-re-registration-contract.md) records the separate public-facade contract risk for later review |
| Overload redefinition grain | Treat one multi-signature `defn` as one overload family whose language type is its complete clause-signature set. Body-only edits and clause reordering preserve that type. Adding, removing or changing a signature is type-changing and is rejected when any member has an external dependent; same-family self/sibling edges do not block it. | 2026-09-04, “whole family” | approved; rejected publication retains the complete prior family; macro and declaration-class boundaries remain at the user gate |
| Macro redefinition and persistence | Macro invocations are expanded before HM checking and do not become stable runtime dependencies. A successful atomic macro redefinition affects future expansions only; already-compiled definitions keep their expansion until next typecheck, while reload/restart re-expands persisted authored source under the then-current macro definition. | 2026-09-04, “agreed qualify s15.4” | approved; qualify §15.4 rather than add durable macro-use provenance; macro-clause calls to ordinary functions remain normal `callees`; exact consolidated normative wording remains at the user gate |
| Nominal-type redefinition | A committed `deftype` may be re-established only with the same runtime and naming structure; any structural same-name change is rejected atomically regardless of callers, leaving the prior type, constructors and accessors live. Structural identity includes visibility, product/sum shape, alpha-equivalent parameters, ordered constructor identities/tags and payload types/arities, plus product field/accessor names/types/order. Type/constructor docstrings and positional sum-payload labels are non-structural. | 2026-09-04, “yes” | approved; no live-value tracking or versioned type identity; exact consolidated normative wording remains at the user gate |
| Trait declaration redefinition | A committed trait's interface is immutable: visibility, conventional/HKT shape, method set, required/default classification, arities, types and constraints must remain equivalent; binder renaming may be alpha-equivalent. Documentation updates are live. A same-interface default-body edit affects only future realizations; existing impl methods remain until an explicit re-`impl`, reload or restart materializes the latest template. | 2026-09-04, “yes” | approved; qualify §15.4 for historical generated default realizations; existing atomic whole-pair `impl` hot reload remains unchanged; exact consolidated normative wording remains at the user gate; focused 2026-09-04 execution confirms `trait_method_tail_s116::reimpl_default_body_calls_replaced_sibling` is still RED, so FIXME 0832 is allocated to this trait/redefinition stream and must not disappear as if resolved |
| REPL specification structure | Split the 3,000+ line REPL specification into a navigable directory of structured files without changing normative meaning; prepare the redefinition delta separately for user review. | 2026-09-04, “dispatch spec to split out the repl spec into a directory of structured files” | structural split complete with byte-identical body proof; semantic edit gate remains closed; QA checker routing and citation compatibility remain in this wave |
| Declaration-family aggregation | One authored multi-signature `defn` or `defmacro` creates one module binding that owns its ordered variants or clauses. The two declaration kinds retain distinct typecheck/expansion semantics and share only aggregate ownership, typed arm identity and whole-family publication. | direction approved 2026-09-04, “this seems better”; exact §14.1 packet approved 2026-09-04, “approved”; generated types delta and §14.2 backend amendment approved 2026-09-05, “approved” | realized across types, typecheck, backend and integration. Canonical generated deltas are types +177/-85 and backend +3/-47; independent regeneration is exact and the all-seven-crate relocation gate passes 3/3. Public-API gate complete. |
| Ordered definition results | One submitted form may publish several definitions, and the REPL lists every published canonical identity in emitted order. A macro displays one compile-time `Fn` transformation signature per clause, remains classified as `defmacro`, and never projects the type of its expansion onto the binding. | 2026-09-05, “go this direction - I think the display will be consistent with the underlying cranelisp macro-transform function (as far as possible)” | root-only `EvalResult::Definitions` API approved and realized; the approved REPL presentation amendment is applied without an inter-crate API, schema, cache or runtime ABI change; focused formatter and acceptance evidence is green |
| Macro `/doc` presentation | `/doc <macro>` remains a docstring-only command, like `/doc` for every other definition; it does not render the macro's typed symbol card or `defmacro` classification. | 2026-09-05, “yes” | §11.2.4 reconciled with §3.1, §17.5.1 and existing behavior; its two allocated macro tests require the exact response and pass 2/2; the misplaced documented-macro trace is repaired; no implementation or API change |
| Traceability maintenance reconciliation | Re-judge every cleared coverage marker against current test bodies; restore only current evidence, leave unsupported claims plainly uncovered, and do not cite tests that assert superseded behavior. | 2026-09-05, “yes” | 57 markers reconciled: 38 restored to current evidence and 19 retained as `[Uncovered S121]`; both traceability directions, planted-fault checker suites, the live citation ratchet and `git diff --check` are green; no normative prose changed |
| IO teardown and platform ABI packet | Add the private emitted `runtime/free_io_node` target; move the nine public Rust consume funnels to the closed `Owned`/`Borrowed` handle surface; advance the platform ABI to 10 by appending `Pure.payload_glue`; add `IO_PURE_GLUE_OFFSET`, `schema_declares_type`, and the optional schema-backed `adts:` macro arm. No language-spec, cache-schema, types/backend Rust API, GOT-layout, or existing emitted-symbol change. | 2026-09-05, “yes” | exact cross-crate API/ABI packet approved for the braided C5 → C7 → C4 → C5 implementation order; generated baselines and implemented ABI/fixture evidence remain a separate confirmation gate |
| Platform API implementation + baseline noise | The implemented platform surface adds exactly `IO_PURE_GLUE_OFFSET` and `schema_declares_type`; `adts:` adds no generated baseline row. Keep Sprint 121's canonical baseline format, then omit generated auto-trait impls through one coordinated migration next sprint. | 2026-09-05, “otherwise approving those changes” | post-implementation platform API approved; [ACT-0955](../actions/ACT-0955-omit-auto-traits-from-public-api-baselines.md) owns the next-sprint command/guard/all-baseline migration |
| Result-handoff disposal carrier | Put disposal authority on the private edge that receives a produced result: Bind carries `drop<a>` for its inner value; Par carries one disposer per branch; Select carries one common disposer; Launch carries the detached result disposer. Runtime-produced values remain armed until explicit continuation/buffer/supervisor/top-level transfer and dispose on cancellation or fault. | 2026-09-05, “approved” | complete; independent review PASS; no platform-authored node, public Rust API, language specification, `ABI_VERSION = 10`, or `cranelisp_run_io(i64) -> i64` change; [ACT-0956](../actions/ACT-0956-blocking-select-ready-loser-disposal-evidence.md) retains the one advisory extra-evidence case |
| Capacity-1 first-error behaviour | A same-token serial group stops at its first runtime error; it does not start later parked effects. Already-started concurrent work still follows structured cancellation and disposal. | 2026-09-05, “I agree with your recommendation” | implementation and backend design align to `spec/12-runtime.md` §12.4.3 and `spec/10-io.md` §10.12.4; no normative specification or public API change |
| Phase 5 → Phase 6a | Accepted green delivery; assess docs, examples, stdlib, exemplar and REPL, plus the scheduled read-only `src/` audit; return a grouped action plan | 2026-09-08, “approved” | approved |
| Phase 6a → Phase 6b | Five user-facing streams recorded below; retain current `def` application behavior and defer 0800 face 3; exact spec edits remain separately reviewed | 2026-09-09, “yes” | approved |
| Phase 6b → Phase 7 | Delivered artifacts and exact close operations | — | pending |

## Phase-6b completion record

User approved the five-stream package and explicit 0800 face-3 deferral on
2026-09-09. Current `def` behavior and diagnostics remain unchanged; the
future API choice returns to user review. Phase 7, commit and publication are
not authorized. The user approved the exact three specification-record
corrections on 2026-09-09; spec applied only those hunks, verified against
pre-edit snapshots in `/tmp/cranelisp-s121-phase6b-spec-before-YcI1mK/`.
Evidence/reports: `/tmp/cranelisp-s121-phase6b-M0qqm2/`.
The approved record-only edits corrected the delivered `/search` status and
exact-in-scope inventory row, and removed the disproven FIXME-0832 failure
paragraph. The canonical text is in `repl/spec/17a-agent-language-awareness.md`,
`repl/spec/03-slash-commands.md` and `repl/spec/18-redefinition.md`; the original
before/after packet is recoverable from Git history. The Phase-6a temporary
reports are unavailable after the session boundary; approved scope and role
outcomes remain in this record and the completion package. Prior test results
are accepted historical evidence, not executions repeated in this phase.

| Role | Work | State |
|---|---|---|
| spec, native `/root/spec`, Codex Terra/high | exact before/after record-only spec packet | complete/released; exactly three approved prose hunks applied and snapshot-diff verified; coverage annotations unchanged |
| qa, native `/root/qa`, Codex Terra/high | timeout coverage-gap and fix evidence | adequate; PLAN updated to `[Tested]`; `/tmp/cranelisp-s121-timeout-qa-fix.md` |
| docs, native `/root/docs`, Codex Terra/high | cohesive `user/` correction and transcript verification | complete; obsolete timeout warning removed; checks pass |
| test, native `/root/test`, Codex fallback | permanent timeout RED/control | complete; established RED→GREEN in all three modes; fixed-history comments reconciled; released |
| arch, native `/root/arch_timeout`, Codex Terra/high | identify owning compiler seam and bounded correction | attributed to private typecheck mono-recheck function-value harvesting |
| design, native `/root/design_timeout`, Codex Terra/high | bounded typecheck correction and unit RED seam | complete; `/tmp/cranelisp-s121-timeout-fix-Lw3dXC/design.md` |
| dev, native `/root/dev_timeout`, Codex Terra/high | private typecheck fix, unit RED→GREEN and focused evidence | complete; original crate suite 899/899 plus added cross-module unit RED→GREEN; final focused units 2/2; released |
| review, native `/root/review_timeout`, Codex Terra/high | independent incremental typecheck inspection | complete; both evidence findings resolved; no outstanding finding |
| qa, native `/root/qa`, Codex Terra/high | Phase-6b stdlib evidence allocation | intake/PLAN complete; original RED + control GREEN adequate for user fix decision; `stdlib-qa.md` |
| test, native `/root/test`, Codex fallback | stdlib public execution evidence | complete/released; original runtime RED and explicit-bind sibling GREEN in all modes |
| dev, native `/root/dev_stdlib`, Codex Terra/high | cohesive stdlib completion | complete/released with sequence-io explicitly deferred; 0780 filing closed after guide evidence; `stdlib-records.md` |
| docs, native `/root/docs`, Codex Terra/high | annotated-Sexp helper user-guide example | complete/released; fresh helper/raw-match replay passes; `docs-helper.md` |
| arch, native `/root/arch_sequence`, Codex fallback | 0780 architecture-record handoff | complete/released; annotated-Sexp contract and inventory reference delivered helpers; no architecture change |
| qa, native `/root/qa`, Codex Terra/high | helper/documentation adequacy closeout | adequate/released; PLAN records helper scope and evidence limits; `stdlib-qa.md` |
| arch, native `/root/arch_sequence`, Codex Terra/high | sequence-io runtime defect attribution | complete; backend↔intrinsics owning-edge boundary, crate still unassigned; `sequence-arch.md` |
| qa, native `/root/qa`, Codex Terra/high | sequence-io discriminating unit and coverage gap | user deferred further work; permanent runtime RED/control retained; no active investigation |
| dev, native `/root/dev_sequence`, Codex Terra/high | production-shaped backend ownership discriminator | complete/released; anchored hd retain/store and execution GREEN; backend 582/582; only cfg(test) changes |
| test, native `/root/test`, Codex fallback | actual public sequence-io emitted-reference diagnostic | complete/released; dump omitted concrete sequence frame, no attribution; further work deferred |
| training, native `/root/training`, Codex Terra/high | approved examples stream | complete/released; default-method lesson retains exit 58; inventory reconciled; 37-entry cold/warm run/link matrix 148/148; `training.md` and `sequence-matrix.log` |
| test, native `/root/test`, Codex fallback | REPL demo completion | complete/released; guarded redefinition and library discovery PTY replay both exit 0; `repl-demos.md` |
| test, native `/root/test`, Codex fallback | exemplar linked-web evidence | complete/released; final f84a563f linked/run journeys 2/2 including explicit HTTP404 and body; `linked-web.md` |
| qa, native `/root/qa`, Codex fallback | 0832 coverage/status reconciliation | complete/released; §7.1.5 annotation band and PLAN reuse accepted PASS; no normative change or rerun |
| dev, native `/root/dev_exemplar`, Codex fallback | exemplar completion | complete/released; records/comments reconciled without exact HTTP404 evidence claim; `exemplar.md` |
| review, native `/root/review`, Codex fallback | linked-web test delta | complete/released; sole HTTP404 evidence finding corrected and finding-scoped re-review clear; `linked-web-review.md` |
| qa, native `/root/qa`, Codex fallback | exemplar evidence closeout | adequate/released; corrected linked/run HTTP allocation satisfied; no additional review for mechanical exemplar records; `qa-readiness.md` |
| qa, native `/root/qa`, Codex fallback | S120 audit R-2/R-5/R-6 evidence reconciliation | complete/released; R-2/R-5 met, R-6 partial; Python suites 23/23 + 10/10; `audit-r256.md` |
| qa, native `/root/qa`, Codex fallback | final Phase-6b acceptance allocation | fresh full default nextest allocated; expected one deferred sequence-io RED and one existing ignored benchmark; `acceptance-qa.md` |
| test, native `/root/test`, Codex fallback | final-tree acceptance observation | complete/released; 5905 run / 5901 pass / 4 fail / 1 skip, 131.473s, 3d3fde5b; subsequent classification and user-approved carries below; `acceptance-test.md` |
| qa, native `/root/qa`, Codex fallback | unexpected acceptance failures | complete; stale failure trigger and separately reproduced generic-redefinition defect; user accepted top-priority next-sprint carry |
| test, native `/root/test`, Codex fallback | post-redefinition isolation | complete/released; vec case SIGSEGV11; scalar generic cases return stale0 despite new body42; monomorphic control GREEN; `redefinition-isolation.md` |
| qa, native `/root/qa`, Codex fallback | redefinition defect intake and coverage gap | complete/released; PLAN records user-accepted top-priority carry and coverage repair; suitable to present records-only Phase7, not all-green/fixed; `redefinition-qa.md` |

User approved fixing the reproduced `core.io/timeout` wrong rejection on
2026-09-09 (“ok let's fix the defect”); this does not approve the separate
spec-record edits. The private typecheck mono-recheck correction now passes
the permanent public regression through REPL, run and link without changing
the real stdlib, specification, public API or ABI. Attribution and pre-fix evidence are recorded below with the public
regression, counterfactual and final-source results. The lambda counterfactual
distinguishes a constructor used as a value; the timeout observation does not
independently prove loser cancellation.

Docs updated eight `user/` files. Fresh existing-binary observations cover
feature-off agent flags, `/syntax`, same-type redefinition (2→11), blocked
type change retaining 11, examples 21/23 (243/178), and inline race (111).
Scoped diff/citation checks passed for that documentation work. Report:
`/tmp/cranelisp-s121-phase6b-M0qqm2/docs-report.md`.

**Current checkpoint:** timeout fix verified, independently reviewed and judged
adequate by QA; documentation and coverage records reconciled. **The user has
deferred the sequence-io runtime defect and directed work to move on.** Its
permanent unignored RED and explicit-bind GREEN control remain; no further
reduction, diagnosis or fix is active. The examples stream is complete: the
default-method lesson retains exit 58, inventory records are reconciled, and
all 148 cold/warm run/link checks passed. Stdlib's final record cleanup is
complete; the helper guide also passes its fresh REPL replay. Item 0780 is
closed; arch reconciled its remaining helper-status references. Spec's approved
record corrections and changed REPL demo replays are complete. Linked-web and
run-control HTTP journeys pass 2/2 including the review-added HTTP404 status
assertion (`f84a563f-f4a1-4e91-ad8f-5323c31eb221`, 5.129s; linked 3.227s,
run 1.858s). Raw output: `/tmp/cranelisp-s121-linked-web-review-3pvG1t/nextest.log`.
Exemplar records/comments are reconciled; independent review is clear. No
source/runner reservation remains; QA judges the scoped linked-web evidence
adequate, and reviewer closeout is complete. QA also judges the
helper/documentation evidence adequate; no tests were rerun for record cleanup.
The stdlib observations below remain a
partial-delivery record, not a claim that the stream is all green. Helpers and
their checks, final stdlib records and the user-guide example are delivered.
The exact three spec-record corrections are approved and applied.
Any further public API, architecture,
ABI/schema or normative change still needs separate review. The five Phase-6b
user-facing streams are delivered with the sequence-io defect explicitly
deferred, not an all-green current workspace claim. Prior audit R-1–R-8
reconciliation is recorded in `audits/shared-role-integration-s120.md` §9:
R-2/R-5 met, R-4 open, R-1/R-3/R-6/R-7/R-8 partial. The user approved the
remaining tooling/documentation residuals as next-sprint carries on 2026-09-09;
[ACT-0957](../actions/ACT-0957-shared-role-audit-residuals.md) owns the handoff.
Final-tree acceptance run `3d3fde5b-001f-4179-a076-2e1502fa6a96` completed:
5905 run / 5901 passed / 4 failed / 1 skipped in 131.473s. Acceptance initially held:
besides the deferred sequence-io failure, two `spec_11_stdlib` failure-path
tests failed and the citation gate caught the coordinator's future archive
path in the draft close proposal. That draft wording is corrected and the
citation ratchet passes (486 documents, 8526 citations, zero findings). QA
confirms the diagnostic test's former `vec-flatten` failure trigger now
succeeds, so it cannot exercise failure attribution. The no-partial-publication
test also has an unarmed trigger, but its missing replacement-call and `/info`
output is a separate unclassified symptom; child status was not asserted.
Next proposed evidence is a same-session successful-redefinition control with
explicit child exit status, followed by a genuinely armed failure-path
probe/control if available. The user approved isolation on 2026-09-09; test
completed the minimal redefinition subject/control and explicit child-status
observation. The vec case signals 11. Removing vec/import reduces the issue to
a scalar generic replacement returning the old identity result 0 instead of
42, while `/info` exposes the new type/body. A monomorphic replacement control
passes. Runs `970011df-7f8e-4734-989e-02776f415023` (2 RED) and
`a0a0d4fb-2034-408a-8243-c03c5111cc51` (1 RED / 1 GREEN) are retained in
`/tmp/cranelisp-s121-redefinition-NqbQ0D/`; three permanent RED tests and one
GREEN control were added. The internal locus remains unassigned. No compiler
fix or failure-trigger replacement was performed. The user subsequently directed
wrapping S121 and prioritising this work at the top of the next sprint.
The generic-redefinition defect remains in the three enabled RED tests;
[ACT-0958](../actions/ACT-0958-rearm-failed-turn-recovery-coverage.md) carries the
associated but distinct failed-turn coverage repair. Investigation is stopped;
these are accepted residuals, not fixes. QA judges the complete original run,
targeted isolation and corrected citation check sufficient to present
close, without another whole-suite run. The user subsequently approved Phase 7,
commit and push under [the recorded close approval](#outcome-phase-7).
Original acceptance raw log:
`/tmp/cranelisp-s121-phase6b-acceptance-iFoDVf/nextest.log`. The historical
all-green Phase-5 result is not reused as the current suite result.
The later close approval authorizes commit and publication, not another fix. The real
stdlib is not a workaround surface for this compiler defect.

Permanent guard:
`tests/stdlib_conformance.rs::stdlib_timeout_public_concrete_call_and_lambda_control_across_modes`.
Pre-fix nextest `c876b99b-1d8f-4c89-be86-85a9936c26f8` established RED:
the unchanged public subject failed in REPL/run/link while the test-private
copied-stdlib lambda counterfactual passed in all three. The conformance
test's import-only scope explains the missing generic-call coverage.
Raw log `/tmp/cranelisp-s121-timeout-red-r1J5hE/nextest-counterfactual.log`,
SHA-256 `462dbbf236f8976fb47f05f9012412352a5002cbc57d6f2471c14cd858289f46`.
Test execution rebuilt the binary; its provenance is distinct from docs'
prebuilt Phase-5-identical binary. Final-source nextest
`6c976cd1-5232-455c-b82c-d5ba2d53b142` passes all three allocated checks:
public timeout, adjacent constructor-as-value, and public-module conformance
(3/3, 42.679s; `/tmp/cranelisp-s121-timeout-final-VhsBvl/nextest.log`).
Earlier conformance launches have unknown outcomes, not proven failures;
this completed observation supersedes them. The final typecheck crate run
`80f02108-6a26-47bf-b3dd-461a78bf0815` passes 899/899. No fresh all-green
workspace claim is made.

The additional cross-module unit distinguishes template home from caller-local
storage: pre-fix RED `03ef0c2f-5b69-4b72-85db-2f87e8b669ac`, final GREEN
`ce29f5d2-0cfb-4416-a996-18ae21f6091b`. Both final focused units pass together
(`b61d384b-05e6-478e-88fb-0f4e9082d2ea`, 2/2;
`/tmp/cranelisp-s121-timeout-final-VhsBvl/units.log`). Production source is
unchanged from the reviewed final hash `dd083bd287dba644a1e3c60fc188eb3407525618c2a4959024141d827de17d60`.
Finding-scoped re-review closes both evidence findings. Test comments now
record the fixed cause; assertions and fixtures are unchanged.

### Phase-6b stdlib runtime intake

**Current disposition — deferred by the user:** “let's leave this issue red
and move on for now.” This supersedes the earlier investigation/repair
approval below. Keep the public defect test unignored and its passing control;
do not resume investigation without a new user decision. QA owns the retained
intake; the implementation crate remains unassigned. At a future resumption,
reduce the real failing source before expanding compiler fixtures. The issue
is not fixed, and any full-suite report must show this expected RED explicitly.

The new permanent
`tests/stdlib_conformance.rs::stdlib_core_io_public_scalar_driver_across_modes`
parses and compiles, then aborts in REPL, run and link with `STALE RC DEC
(drop glue): dec of non-live heap pointer` at
`crates/cranelisp-intrinsics/src/drop.rs:283`. The linked stack includes
`runtime/free_io_node`; neither that stack nor the diagnostic's old FIXME
wording establishes the faulty producer or ties this to an earlier defect.
Nextest `4689e358-c374-420e-b1e2-7a62bd75e7fb`, log
`/tmp/cranelisp-s121-stdlib-driver-1ClNNH/driver-rerun.log`, establishes the
runtime RED after a test-fixture syntax correction. QA owns classification
and evidence adequacy; the subsequent bounded repair approval is recorded below.

The preceding batch `c45a6b00-f382-4be6-a219-b2c19620c563` passes the helper
macro client, timeout/cancellation and public-module maintenance checks. Its
driver failure was fixture syntax, not runtime evidence. No all-green stdlib
claim is made. Helpers and six new polarity self-tests are implemented; the
module's discovery run passes 11/0/0. Main independently repeated the fresh
REPL recipe with `--no-cache`, process exit 0, retained in
`/tmp/cranelisp-s121-helper-verify-NhQR9I/discovery.log`; binary SHA-256
`4f2d353204fd27637d13365b6a3bebd06f76a43e0550b6a66db7ba4d9dd155e4`. Final owned
records and the user-guide example are delivered. Fresh guide replay in
`/tmp/cranelisp-s121-docs-helper-7qDLL2/repl.out` returns 42 for both helper
calls and 7 for both raw-match calls, process exit 0. The stdlib owner closed
0780; QA judges this bounded helper/documentation evidence adequate, without
an allocator, cache, prelude-absence negative or whole-stdlib claim. The invalid
provisional IO discovery child was removed; the permanent public driver is
retained unignored. QA symptom-classifies this as `rc-miscount` and allocates
one sibling retaining actions/order/imports/results but replacing only outer
`sequence-io` with explicit `bind`. That control passes all modes in
`14edca3e-eb22-4a36-942c-157dfc64282b` (1/1, 4.292s); original remains RED
in `b6bc3df4-b8f9-481d-84c9-1810be93a8b8`. Outer sequence aggregation is
therefore a necessary public trigger in this witness, not an internal-cause
attribution. Both tests remain permanent. No source/test runner is active;
QA judges the pair sufficient for the user's next defect decision. The user
approved investigation and repair (2026-09-09, “yes”), conditional on an
actual-seam unit RED before compiler changes. Arch is identifying the owning
seam; the responsible crate and ownership operation are not yet established.
This approval does not authorize specification, public-API, ABI or architectural
changes. Live citation ratchet passes (485 docs, 8,522 citations,
zero new findings); scoped whitespace checks pass.

The first backend discriminator is GREEN (`e961edd6-471e-48d4-9138-415ae59e1bb2`):
the exact matched `hd` is retained before storage in `Bind`, and the three-Pure
fixture executes successfully with the original list owner captured. This is
not the public failure and does not assign an intrinsics cause. Its typed AST,
local constructor fixtures, effects and ownership graph differ from the public
program. QA is selecting the next closer-to-public discriminator; no production
repair is eligible from this result. Private test support now accepts existing
pattern-constructor carriers instead of discarding them; existing callers are
unchanged. Full backend nextest passes 582/582
(`0dde1c56-8026-4060-a83b-eb014fee292d`). Evidence and pre-edit snapshots:
`/tmp/cranelisp-s121-phase6b-M0qqm2/sequence-dev.md`. QA's next allocation is
one unchanged public-carrier run with the existing `CRANELISP_CODEGEN_DUMP`
filter for `core.io`. That completed capture re-aborted but omitted the concrete
sequence frame; it did not observe the required ownership edge. Report:
`/tmp/cranelisp-s121-phase6b-M0qqm2/sequence-test.md`. No production repair was
made. The source/test reservation is released and investigation is deferred.

## Completed Phase-6a assessment

User accepted Phase 5 and approved Phase 6a on 2026-09-08. Assessments consume
the settled compiler below; no implementation, normative/API changes, commit,
publication or Phase-6b work is authorized. The output is one grouped
user-facing action plan, with the `src/` audit recommendations retained for
next-sprint disposition. Assessment reports: `/tmp/cranelisp-s121-phase6a-jeM0WW/`.

| Role | Surface | Provider/model/effort | Harness/task | State |
|---|---|---|---|---|
| docs | user documentation | OpenAI GPT-5.6 Terra/high, user-approved Codex fallback | native `/root/docs` | complete; `docs.md`, Phase-6b corrections proposed |
| training | examples | OpenAI GPT-5.6 Terra/high, user-approved Codex fallback | native `/root/training` | complete; `training.md`, bounded lesson/record proposal |
| dev | stdlib | OpenAI GPT-5.6 Terra/high, user-approved Codex fallback | native `/root/dev_stdlib` | complete; `stdlib.md`, evidence/library proposals |
| dev | exemplar | OpenAI GPT-5.6 Terra/high, user-approved Codex fallback | native `/root/dev_exemplar` | complete; `exemplar.md`, record reconciliation and web-link evidence proposal |
| spec | REPL | OpenAI GPT-5.6 Terra/high, user-approved Codex fallback | native `/root/spec` | complete; `repl.md`, record/demo reconciliation; no new normative ruling |
| audit | src | OpenAI GPT-5.6 Terra/high, user-approved Codex fallback | native `/root/audit` | complete; `audits/src-s121.md`, next-sprint disposition |
| qa | stale coverage/limitation records | OpenAI GPT-5.6 Terra/high, existing user-approved Codex role | native `/root/qa` | complete; `qa-records.md` |

Concurrent training and audit launches were refused with `agent thread limit
reached`. After docs finished, training launched successfully: assessments can
proceed serially as slots release. All assessments and the scheduled `src/`
audit are complete. No provider substitution was needed. No compiler source,
normative requirement, public API or test changed during Phase 6a.

The Phase-6b proposal groups work into REPL records/demos, user documentation,
examples, stdlib and exemplar streams. It requests explicit deferral of the
unselected 0800 face-3 `def` application API choice. Exact spec-record edits
still return to the user before implementation. Audit recommendations do not
authorize implementation; F-1 needs current-authority reconciliation, not an
automatic return to the older reload design. The Phase-6b approval is recorded
above; exact specification edits retain their separate user gate.

Prior audit reconciliation is now recorded in
`audits/shared-role-integration-s120.md` §9, replacing its placeholder with
clause-based evidence and unresolved decisions. The original plan was not
proof of resolution: only R-2 and R-5 are fully met. The user approved the
remaining tooling/documentation residuals as next-sprint carries through
ACT-0957; publication stays separately gated. Existing `/learn` and
network-example deferrals stand.

Docs proposes one cohesive `user/` correction: align live-development guidance
with current redefinition rules; correct feature-off agent flags; document the
delivered `/syntax` command and `/search` macro exclusion; update the inventory.
Sprint verified the contradictory guide/spec and flag/source pairs directly.
The report's question about old 0832 has existing executing evidence: the final
gate log records `reimpl_default_body_calls_replaced_sibling` PASS. Reuse that
evidence when assessing whether the old documented limitation should remain.
Documentation implementation is authorized by the Phase-6b gate above.

## Accepted Phase-5 evidence

**Current checkpoint: 2026-09-08.** Binding-scope and tail-transfer corrections
are delivered, independently reviewed and QA-accepted. The user-approved
maintenance wave is implemented: direct emitted-code singleton/two-candidate
coverage replaces indirect no-speedup inference, runtime parity still requires
40, exactly 19 attributed goldens are refreshed, and stale f4 commentary is
corrected. No compiler behavior, public API or specification prose changed.

**Latest full gate: GREEN.** 5,897 run, 5,897 passed, zero failed, one skipped
in 100.450s (`f0054f85-8f4d-434d-8470-d3058cd26994`). All capacity and golden
tests pass. The approved measurement repair exposes linked-executable time
separately and leaves the existing compiler-lifecycle duration unchanged.
Thresholds, `--run` result checks and capacity-1 ordering checks are preserved.

Evidence and raw logs: `/tmp/cranelisp-s121-phase5-evidence-pOBpoR/`, including
`maintenance-dev-report.md`, `maintenance-test-report.md`,
`maintenance-review-report.md` and the preceding 19-file attribution/captures.
The binary remains identical to the pre-maintenance compiler, SHA-256
`429f130bba7b3ba134892572b8491c1a0277e81264190e6957cd043b7787a7ba`.
The invalid sandbox partial run is retained separately, not combined with the
authoritative local-server result.

Named Codex GPT-5.6 Terra/high roles completed serialized source work:
`/root/dev` supplied the direct pair (2/2; adjacent 38/38 and 3/3),
`/root/test_maintenance` supplied e2e/goldens and the full gate, and
`/root/review_maintenance` independently found and rechecked the strengthened
create/spark-chain assertion. No review finding remains. The initial overlapping
call-count predicate was corrected before the timing assertion was retired.
The earlier four timing failures (`4d1013a0`, 5,892/4/1) and two serial REDs
(157ms and 154ms against 150ms) remain historical evidence. User-approved
isolation distinguished linked capacity-2 execution (127–131ms) from ordered
capacity 1 (191–195ms) and capacity 3 (66–71ms), all exit 180; it reproduced
no capacity-2 runtime fault. Compiler lifecycle and 20ms polling contaminated
the old observation, without a measured attribution for every historical delay.

User approved the test-only repair (“agreed”, 2026-09-08).
`/root/test_maintenance` implemented it; `/root/review_capacity` identified and
rechecked the wrong-phase falsifier. The final single-target control compares
with independent linked execution and rejects compiler-only and combined
intervals. Focused capacity/helper tests pass 6/6; no review finding remains.
QA accepts the repaired measurement evidence and final gate
(`capacity-measurement-qa-report.md`): focused 6/6, full 5,897/5,897,
resolved review, 794 live coverage links and 2,477 test citations with no
findings. The final citation-marker correction is comment-only, with no
executable change after the gate. No test runner or maintenance hold remains.

Capacity reports and logs: `/tmp/cranelisp-s121-capacity-isolation-0VnQCq/`.
Authoritative final log: `capacity-measurement-full-nextest-replacement.log`,
SHA-256 `e06b51a60fcd3fac0e7a5cff40df33f93589efed48367f8effca3b0d25a1690d`.
Earlier reports of external termination were incorrect: the tools yielded while
the runs continued. Both logs have complete summaries; the earlier `c8f0b3e0`
run (122.044s, also 5,897 passed) predates the final regression correction and
is not substituted for the final gate. Phase 5 was accepted at the Phase-6a
transition above; release and commit remain unapproved.

**Historical checkpoint: 2026-09-07.** User approved the fresh census
and grouped Phase-5 closure. The chronology below records subsequent repairs.

**Earlier integrated result:** after staged-layout and example repairs,
`cargo nextest run --no-fail-fast --status-level fail --final-status-level fail`
ran **5,795 tests: 5,788 passed, seven CLIF checks failed, one skipped** in
100.165 seconds (nextest `f4e64d3e-cf35-40d4-93c7-bf2b11956291`). Log:
`/tmp/cranelisp-s121-pre-clif-census-20260907.log`, SHA256
`645f205578306859a7d88c4eee0e4705db4bb7a352d18ee47850a80d4fd8c7fd`.
This run used required local-server permissions and supersedes the earlier
census counts below. Backend attribution explains 18 of 19 fixture deltas;
`f4_sudoku` remains held for six added guarded return retains. QA allocated
a bounded wrapper-versus-direct-helper marginal reproduction in test-plan §14;
test completed it without compiler or golden edits and released its reservation.
The paired reproduction (`554250b8`)
demonstrates a leak: direct helper alloc/free is 25/25 at eight iterations and
97/97 at 32; wrapper is 25/1 and 97/1, with equal correct outputs. The wrapper
retains three objects per iteration. Test confirmed the emitted seam;
QA confirmed duplicate ownership acquisition when forwarding an already-owned
callable result. The permanent failing repro is
`tests/nullary_arm_beside_boxed_arm_0917.rs::forwarding_fresh_option_releases_its_payload`
(final RED `18726a04`; evidence `/tmp/cranelisp-s121-wrapper-return-BHWyR6`).
`/root/dev_backend_closure` completed the backend-private correction under
test-plan §14.1 and released its reservation. Freshness semantics,
borrowed/COW protections and public API/schema/ABI remain unchanged; no goldens
may be refreshed before corrected ownership evidence and review. All 19
snapshots await one cohesive, attributed fixture visit.
The backend's production-compilation unit pair went from one RED/one GREEN to
2/2 GREEN. Private implementation is ready for read-only review by
`/root/review_backend_return_ownership` while dev completes its serialized
evidence. Backend passes 555/555; the unchanged marginal regression and related
0917/Vec controls pass 16/16, with alias/projection/COW/TCO controls 33/33.
Independent review finds no correctness/structural issue; local documentation
reconciliation remains with dev. All six questioned f4 return retains are gone
with cleanup retained. Fresh f4 exit is 154; observed alloc/free is 4,139/2,358,
which is not a marginal leak measurement. QA and backend design assess this
remaining evidence before recapture; no pre-fix runtime-counter comparison is
claimed. Artifacts: `/tmp/cranelisp-s121-owned-return-K4OO0e`. Backend design's
final comparison finds 37/44 f4 frames byte-identical to the initial candidate;
seven frames remove 11 redundant result-retain guards, with calls and cleanup
retained. No unexplained CLIF delta remains. QA §14.2 requires only an
independent once-versus-twice solved-grid runtime comparison before f4 recapture;
absolute child-process allocation counts do not establish a runtime leak.
`/root/test_staged_layout` now owns the sole source/test/build reservation for
that comparison and the conditional 19-file attributed snapshot refresh.
Final backend run `431d4bb2` passes 555/555; focused ownership runs `8ae14d8f`
and `fc3ac80e` pass 16/16 and 33/33. All-target check, rustdoc with warnings
denied, format and whitespace pass. Clippy was not rerun in this slice; no
zero-new-clippy or strict warning-clean claim is established by those checks.
The independent f4 diagnostic is nonzero: one solve alloc/free 4,140/2,359
(residual 1,781), two solves 8,279/4,717 (residual 3,562), with correct checksum
scores 1/2. Growth is 1,781 per solve, unlike the earlier absolute observation.
Artifacts: `/tmp/cranelisp-s121-f4-runtime-DaIjlY`. QA has confirmed the allocated
same-shape no-work driver control and bounded pipeline-stage reduction; test
retains the reservation. Recapture is stopped. The completed wrapper correction
remains independently green; no additional compiler change is yet authorized.
The no-work driver has zero growth (alloc/free 2/2 then 3/3), confirming runtime
retention. Grid construction plus checksum grows 161 objects per iteration;
the remaining solver pipeline adds 1,620. A smaller Vec-push probe did not
preserve the measured behavior and is not an attributed cause. Reduction stops
at this partial reproduction. The permanent unignored guard is
`tests/s99_fixtures.rs::s99_f4_solved_grid_releases_repeated_workloads`;
targeted RED `0ec84c72` fails only on incremental retention 1,781 versus zero,
with all outputs and driver-control checks passing. Test released source and
runner; scoped format/whitespace/citations pass. Raw evidence and log remain at
`/tmp/cranelisp-s121-f4-runtime-DaIjlY`. The last full census predates this guard.
QA recommends a separately approved bounded investigation of grid construction,
then checking whether that cause explains the solver remainder. Broader
investigation or implementation returns to the user. No snapshot overwrite or
accepted deferral is implied; all 19 goldens remain unchanged and Phase 5 remains
open.

User initially approved **reproduction and minimal isolation only**, then a separate
fix-versus-defer decision: “we can then decide if the problem is worth fixing
before moving on.” Test completed that reservation with a faithful minimal
program and discriminating control, without changing compiler or snapshots.
Isolation removes Sudoku, strings and cell types. The permanent minimal witness
is `tests/s99_fixtures.rs::nested_result_vec_builder_releases_repeated_workloads`:
recursive vector construction returns `Some(Grid xs)`; the same-result-graph
control wraps the result of a raw-vector builder afterward. At fixed eight
pushes and one/two workload repetitions, the measured control alloc/free is
4/4 then 7/7; subject is 8/4 then 15/7, with correct outputs 8/16. This
demonstrates four retained objects per build in that run. An earlier targeted
run was GREEN: the small case's triggering emission condition remains unresolved,
so it is a conditional reduction, not a deterministic replacement for the full
f4 guard or an explanation of all 1,781 objects. Four existing captures of the
same source and compiler make the variation concrete: runs 1/3 allocate/free
8/4, runs 2/4 balance 4/4; all return 8 and retain the same ownership summary.
Their emitted CLIF differs by an extra retain in the unique vector-reuse branch.
Artifacts: `/tmp/cranelisp-s121-grid-reduction-DMrJ8V/fixed-subject`. Test released
source and runner; scoped formatting/whitespace and 15 citations pass. QA finds
the reduction sufficient for the user's scope decision. Backend design's
read-only assessment locates the varying retain at
`crates/cranelisp-backend/src/compiler/vec_codegen.rs::retain_reused_source`
and its interaction with recursive ownership transfer. The faulty producer of
the operation-level escape information is not established; equal whole-function
summaries do not establish equal per-operation information. Unconditionally
removing the retain would be unsafe for genuinely escaping borrowed sources.
Minimal isolation is complete. User subsequently approved **further investigation
and fixing**: “let's do more fix and investigation.”
`/root/dev_backend_closure` holds the sole source/test/build reservation to
identify the varying operation-level input and deliver a demonstrated, bounded
private correction. QA coordinates evidence and attribution read-only. An
out-of-crate cause is handed to its owner before edits; specification,
architecture and inter-crate API changes retain their user gates. Goldens remain
held. No further private correction has yet been applied at this checkpoint.
Dev compared the existing identical-source captures: the leaking run includes
the `vec-push` span 221..236 in its escape-site set, while the balanced run
omits it despite equal whole-function summaries. This establishes variation in
the backend's upstream input. Backend released its reservation without edits or
runs. `/root/dev_typecheck_layout` now owns the sole source/test/build reservation
for QA's deterministic producer control: explicit reversed processing orders and
stored escape facts compared with transfer under final converged summaries.
Self-dependency exclusion in the fixpoint is an unproven lead. A demonstrated
private correction may proceed, but converged facts may still expose a separate
TCO ownership mismatch; convergence and runtime leak closure require distinct
evidence. The deterministic local control is RED: reversed explicit processing
orders produce equal final summaries but different stored escape facts for the
same vector operation; transfer under final summaries agrees with the escaping
result. The non-recursive sibling passes (run
`f4c6884e-ad74-406e-becf-74757c12beef`: one PASS, one RED). Serial QA handoff
confirmed the cause and permits removing the modes-worklist self-dependency
exclusion. Existing conservative-cap and related ownership controls remain
required. Producer convergence is accepted separately from runtime leak closure:
correct escape facts may expose a deterministic backend TCO/COW defect. No
provider substitution or weakening of escape facts is authorized.
The private self-reentry correction is implemented; the focused convergence and
ownership selection passes 33/33. Full typecheck/static gates and unchanged
runtime witnesses are pending. A fresh independent review will follow serially
because its parallel spawn hit the agent thread limit.
Full typecheck now passes 862/862; check/format pass and clippy succeeds with
347 unchanged warning records, none attributed to this correction. Runtime
follow-up is unresolved: three repeated minimal runs fail consistently because
both control and subject grow from alloc/free 8/4 to 15/7 (four retained objects
per build, correct outputs); their marginal difference alone is zero. The full
f4 child terminates before RC counters (no exit code, empty stderr), which is
not a balance verdict. QA intake must distinguish shared retention and child
termination; guards and correct escape facts remain unchanged.
Fresh independent review `/root/review_typecheck_self_reentry` finds no issues:
self-dependency refresh restores existing convergence semantics, queue
deduplication and cap fallback remain intact, and the test helper stays
crate-private under `cfg(test)`. Typecheck released source/build ownership.
QA accepts the producer correction independently. `/root/dev_backend_closure`
now owns the sole source/test/build reservation for the runtime follow-up under
test-plan §14.2: capture f4's actual process status, then trace the existing
fixed-size builder's reuse retain and recursive transfer/cleanup. A demonstrated
private backend correction may proceed with red-first module evidence; no
runtime correction or snapshot change has occurred at this handoff.
The direct raw f4 run now confirms OS signal 11 (SIGSEGV), subprocess status
-11, empty stdout/stderr and no RC counters after about 0.036 seconds. It is not
a timeout. Crash attribution remains separate from the builder's measured
retention until a control links their mechanisms.
Backend unit RED `deefaf38` demonstrates the shared-decision mismatch:
`retaining_cow_tail_argument_releases_its_old_source_owner` validates the
non-retaining transfer, then fails because retaining COW still exempts the old
parameter from flushing. Read-only backend design confirms the private repair
fits the existing owner-continuity contract: identical pointers do not establish
continuity of the same owning reference. Protection and flushing must share the
decision; no specification or public API change is required. The crash remains
separately open.
The shared-decision private correction passes seven focused checks, and the
unchanged minimal runtime builder now passes (`9a77cb15`). Full f4 remains RED
without counters, consistent with the separately measured SIGSEGV. The backend
owner is completing a borrowed-value control and release gates; the runtime
crash is not closed by the minimal witness.
The production borrowed-sibling control passes (`6cf9bc06`). Disabling only the
pre-protection consumer's retain probe while leaving flushing correct makes it
fail for missing protection (`e3331e9f`); the plant is removed. Fresh independent
review `/root/review_backend_cow_transfer` assesses the shared-decision delta
read-only while dev runs its full backend gate.
The backend correction is complete and independently reviewed without findings:
557/557 backend tests (`b796f542`), 47/47 relevant e2e controls (`dd26aa3d`),
and the unchanged minimal guard pass. The exact fixed-size source returns 8,
allocates/frees 4/4 and records eight reuse hits, zero misses; CLIF retains the
producer's increment and now releases the old parameter before the backedge.
All-target check, formatting and whitespace pass. Clippy was not rerun and
remains an outstanding release check. Dev released the runner and source.
QA is allocating independent runtime verification and bounded f4 crash isolation;
the full fixture's SIGSEGV is not repaired by this evidence.
The outstanding backend clippy command now succeeds (primary-run
`cargo clippy -p cranelisp-backend --all-targets --message-format=json`): 38
warning records, none in either changed Rust file; existing other-file debt
remains. Log: `/tmp/cranelisp-s121-backend-cow-clippy.jsonl`. QA accepts the
bounded correction. `/root/test_staged_layout` owns the sole source/test/build
reservation for independent unchanged-witness reruns and current-binary raw f4
status, followed only as needed by faithful pipeline-stage and native-stack
isolation. Compiler source and goldens stay frozen during that test visit.
Independent current-binary run `6e64ee24` confirms the minimal guard PASS and
full f4 FAIL. Raw status records SIGSEGV 11 after 0.140 seconds, no output or
counters. Construction→checksum is now balanced at 735/735 with checksum 154;
the crash is downstream of construction. Artifacts:
`/tmp/cranelisp-s121-post-cow-CuqY6q`. Native debugger tools are unavailable in
the checked executable locations; source-level stage reduction continues, with
no unsupported native-stack or cause claim.
The test provider interrupted one turn with a content-filter error; the same
agent resumed only the existing source-level reductions, with no tool installation
or native inspection machinery. No repository files changed during that visit
before resumption. Propagation-only and a single `eliminate-from-peers(g, 0, 4)`
both reproduce SIGSEGV 11. Test began reducing that peer pass with compiler
source and goldens unchanged.
The resumed source-only test turn encountered the same provider content-filter
failure. Dispatch is now **tooling-blocked**, not waiting for an active agent;
no model/harness substitution or further reproduction work is authorized as a
workaround. The confirmed checkpoint is balanced construction and SIGSEGV in
propagation and one peer-elimination pass. Existing permanent full/minimal
witnesses and scratch stage sources/status files remain intact. The two verified
private fixes stand; crash attribution and all golden refreshes remain open.
Resume the same bounded test task after resolving provider access; changing
models or harnesses merely to evade this restriction is not an authorized path.
The user explicitly selected Fable for the legitimate compiler-correctness
investigation. A normal configured QA dispatch ran with provider
safeguards and permissions unchanged: Claude/Fable, high effort, session
`08fc18c2-ab62-4a30-9f1d-483e1dbf763b`. It was interrupted after diagnostic
shell commands required permission and QA created an out-of-scope Rust test
driver to run scratch cases through Cargo. No bypass was authorized. The driver
was moved out of the test suite to the run's `interrupted-driver.rs` artifact;
the existing regression-test file hash is unchanged. Compiler, specification
and golden files remain frozen. The bounded
brief and result are under `/tmp/cranelisp-s121-fable-qa-Vt0n9y`, with the
standard closed dispatch row in `.local/subagents.jsonl` records an error
outcome. Fable independently reran the existing minimal regression successfully
(run `8aa9de99-c9bd-4771-b622-19663f5f0d39`, one pass), but returned no completed
crash attribution. The user subsequently authorized broad local investigative
discretion for Fable as sole diagnostic runner. A fresh QA dispatch uses the
existing wrapper's `auto` permission mode (normal automatic review, no bypass),
with brief `broad-investigation.md` and result `broad-result.json` under the same
scratch directory. Shell diagnostics, reductions, scratch scripts and focused
builds/tests are authorized; product/spec/API/golden edits, Git mutations,
installation and system changes remain excluded. QA completed at 05:32 UTC
(session `54174265-d19b-4145-93f4-b2eb882c73c9`), with no repository edits.
Its `attribution.md` demonstrates a returned-vector lifetime failure and reports
an unsafe present-`Fresh` fallback; worklist cap exhaustion and the precise
non-convergent sequence still require direct unit-seam confirmation. The user
approved preserving the reductions and confirming that mechanism before any
design/API implementation. Test completed on Opus with no permission denials,
adding three failing regression cells and a passing annotated non-permuting
control in `tests/s99_fixtures.rs`; no compiler edits. Its report is
`/tmp/cranelisp-s121-test-witness/test-report.md`, and transport evidence is
`test-result.json` in the QA scratch directory. Dev/typecheck completed on Opus
(session `4380c14b-bc78-424b-af49-acef50db7c60`) and released both reservations.
Test-only observation directly confirms a period-two `MayAliasOf(1)` /
`MayAliasOf(0)` oscillation, cap exhaustion at both the production bound and
10,000 visits, and fallback publication across the cluster. Two new unit guards
fail; the non-permuting control passes. Crate result: 863/865, only those two
new REDs (run `a19d1ccd-7df1-4550-9625-6b460fad3d8f`). Report:
`/tmp/cranelisp-s121-dev-typecheck-ownership/unit-report.md`; transport evidence
is `unit-result.json` in the QA scratch directory. No production fix was made.
The user approved proposal preparation. Arch completed on Fable (session
`ed341c00-5622-48f8-95af-14a2a4348cb4`), with no repository edits or permission
denials. Proposal: `architecture-proposal.md` in the QA scratch directory;
transport evidence: `arch-result.json`. It recommends absent ownership
publication on analysis failure and a `ResultMode::MayAliasAny` variant for
convergence (+1 forecast public-API line, cache schema 26→27, platform ABI
unchanged). After clarification of the correctness and optimisation benefits,
the user approved correcting the issue in this direction: safe absence fallback,
`MayAliasAny` addition and cache schema 26→27, with platform ABI unchanged.
The user confirmed the exact generated public-API delta. Design/typecheck
completed on Opus (session `9623ea73-3381-4fdb-b270-ad5fadf10822`); §19 of the
existing ownership design settles reach-set union, conditional-result composition
and one empty-publication refusal. Report: `design-report.md` in the QA scratch
directory. It also measured a false-`Fresh` composed summary without exhaustion
(F-2); an end-to-end fault for that additional shape was not demonstrated.
Both Fable runs stopped on provider usage credits: arch/types session
`4bca0a76-c5d8-4caf-a68c-3e3db87c1d7c`, QA session
`0229c857-5bb3-45df-bbe0-5e375f092f0a`. No agent is active. QA wrote a complete
`qa-readiness-report.md` before the transport error: GO with module-level
conditions, no new independent test dispatch, and correction of the unsupported
eight-run probability claim during the later test-file visit. Arch/types left
the approved enum variant and partial documentation edits; no completed report,
generated baseline or release evidence. The source reservation remains held for
completion, not released. Consumer matches and schema update remain pending;
the intermediate tree is not claimed buildable or verified. User previously
authorized Opus fallback, but the shared dispatcher lacks a per-run model
override. The user approved adding that capability: `--model MODEL` now applies
only to one dispatch, with default allocation/effort/permissions unchanged;
23 fake-provider/lifecycle tests pass (two new override tests failed first).
Arch/types has resumed on explicitly authorized Opus via `types-resume-opus.md`,
with result `types-opus-result.json` in the QA scratch directory. It completed
successfully (session `fe5a8f0f-c76c-4f1a-8db2-10df3e354238`) and released the
reservation. Types 280/280 pass, fmt clean, no new ownership-file clippy warnings;
both reported fault plants were removed. Generated API delta against the
pre-resumption baseline is exactly `+ pub cranelisp_types::ResultMode::MayAliasAny`,
with no removals or modifications; the user explicitly confirmed this delta.
Report: `types-report.md`. No shared role allocation changed. Dev/typecheck is
completed on Opus (session `378ed753-8597-4657-9fd9-43aa7e974810`), with 883/883
crate tests passing and no new touched-file clippy warnings. Its report and
result are `typecheck-implementation-report.md` / `typecheck-implementation-result.json`
in the QA scratch directory. Reach-set composition and empty refusal are implemented;
the old convergence REDs pass. Reported fault plants were restored. Independent
review completed on Opus (session `1766c863-5e4f-4514-aae4-f40f6f1d4072`), with
no blocking regression and four required claim/evidence findings in
`review-typecheck-report.md`. The shadowing hypothesis is not yet reproduced;
QA classified the basket read-only through `qa-review-basket.md` (session
`331610a7-0741-4f6e-9ff5-064a94326dd8`, explicitly authorized Opus fallback).
Dev/backend completed successfully on Opus
(session `f428e860-d675-4e9f-b748-a53eebbbff82`) and released source/build ownership;
`backend-carrier-report.md` records cache schema 27 and focused runtime evidence.
Backend consumers include an exhaustive match in its
`return_ownership_tests.rs` helper; that is test-side only, no new API delta.
The rebuilt compiler passes all 23 `s99_fixtures` cells, including the crash,
wrong-result and repeated-workload release witnesses. Backend crate tests pass
558/558; focused controls pass 57/57 and 54/54. Six held CLIF snapshot checks
remain red, with no recapture. Review-finding disposition and QA adequacy remain
pending; this is not a full-suite claim. Test completed `test-runtime-close.md`
on Opus (session `ce038071-e915-4719-90c5-8027c9d69535`), independently confirming
23/23 runtime and 57/57 control cells on the schema-27 binary. The repeated-solve
probe has zero absolute and incremental retained objects (4,140/4,140 and
8,279/8,279 allocs/deallocs). Its comment-only correction leaves assertions intact.
`qa-review-basket-report.md` confirms the old eight-cell provenance basket was
already green in the pre-wave census: the readiness row was stale, not a new
fix. Snapshot divergence also predates this wave. Both roles completed and
released before the follow-up below.

**Approved correction — review R2.** Ownership-analysis seeds and completed
walk results share one map. Current control flow overwrites seeds before normal
publication, but the claimed structural exclusion is not earned. The user approved
separating published walk outputs from the working seed map, plus the bundled
module evidence and subsequent focused review/full-suite verification. Dispatch
`typecheck-review-fix.md` (dev/Opus high, session
`50c19ccc-dc46-4752-9710-fc48b73bab0b`) completed and released. Its report records
the approved separate output map, R3/R4 detection proofs and local comment repairs.
Typecheck is 889/890 green: the only failure is the new unignored R1 shadowing
result-source probe, with a green renamed-binder control. The hypothesized
widening failure did not reproduce because the existing escaped-binding drain
covers that shape. No shadowing repair was made. Runtime `s99_fixtures` stays
23/23 green; the seventh previously held CLIF test was re-observed red.
Finding-scoped review (`typecheck-finding-review.md`, read-only, Opus high session
`91607cf6-9d46-461a-8028-abaa2b747502`) and the backend test-only visit
(`backend-review-evidence.md`, sole source/build owner, Opus high session
`d7d110d9-2c0a-4446-95c3-afc98c88cc85`) have completed.
Both completed successfully and released: review confirms R2/R3/R4 with no
blocking code finding, leaving F1 source-comment accuracy and F2 defect-class
metadata; backend added the allocated assertion only and proved detection.
The coordinator ran the approved full census, bounded to 300 seconds, log
`/tmp/cranelisp-s121-final-check-zlEbH9/full-suite.log`. Expected REDs were seven
held CLIF checks plus the new R1 probe. No snapshot recapture occurred.
The full census completed (nextest `efe831a7-74a3-4fe3-997c-64d32f008e73`):
5,839 run, 5,830 passed, 9 failed, 1 skipped in 169.240 seconds. The extra failure
is `spec_10_io::resource_serial_diff_token_parallelizes`, 302ms against <300ms.
It passes three serial isolated reruns with unchanged assertions and threshold
(`timing-rerun-1.log` through `timing-rerun-3.log` beside the full log). The
full-run failure remains recorded; these reruns do not establish its cause or
erase it. The coordinator has released the test runner.
Runtime binary SHA-256:
`d3c10369ebb929e814c588ffacd9debdd5d3407eb3749e339d0357e953cc901d`.
Design/typecheck completed its owned record corrections (`typecheck-review-records.md`,
Opus high session `98a3f103-7cc8-443c-9f49-afa840584585`); report present and
reservation released. QA (`qa-post-review-adequacy.md`, authorized Opus high
session `1bb7abef-2c53-4bf4-b5d1-e7448d4db0cd`) reached the provider session limit
before producing its verdict. Its partial owned edits are preserved: the stale
provenance claim in [historical QA plan](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md), the allocated refusal wording in the
S121 test plan, and the ratified `enumeration-miss` vocabulary extension in
`tests/CLAUDE.md`. That interrupted attempt produced no final QA report.

**Quota interruption, resumed.** The final comment-only dev dispatch
(`typecheck-final-record-fix.md`, Opus session
`0513c989-36e3-4991-afb5-d6495198090f`) was refused with zero tool uses and made
no edits. Provider reports reset at 21:20 Australia/Melbourne on 2026-09-07.
The user confirmed quota is available again. Dev resumed on Opus high (session
`e529ebe1-8307-46a5-bf53-2f10b30d18e7`, `typecheck-final-record-fix.md`) and
completed F1's source comments, F2's `class=enumeration-miss` annotation and the
fault-plant record clarification. Its report confirms comment-only edits and
clean rustfmt; the coordinator independently verified unchanged non-comment
content in both Rust files. The binary hash and saved runtime results are unchanged.
QA resumed read-only on the authorized Opus fallback (session
`051f00dd-389a-46a2-9f94-1d96b9f32e0b`, `qa-final-resume.md`) and completed
`qa-post-review-adequacy-report.md`: the approved correction is adequate, with
no whole-sprint release recommendation. Its mechanical closure condition is
satisfied by the completed dev report and coordinator checks. Live citations:
481 documents, 8,473 references, zero findings; scoped whitespace checks clean.
Both agents completed successfully and released; no agent or test runner is active.

**Pre-shadowing-wave checkpoint (superseded below).** The publication correction and allocated evidence
are complete. R1's shadowing result-source defect remains measured, unignored
and unrepaired; no runtime UAF was demonstrated, and no repair or carry has been
approved. QA classifies the seven held CLIF checks separately from product
acceptance and the isolated-passing timing failure as a maintenance observation,
preserving the original failure. Backend's claimed new-variant elision hazard
was falsified by QA: `== Fresh` returns false for another variant and protection
is kept, so that claim creates no architecture or implementation work.
The next R1 scope decision, golden recapture and phase advancement remain with
the user. No additional implementation or shadowing repair is authorized.
Remaining owned record repairs are not
implicitly closed by passing code review or the census. The backend evidence
gap is closed; the post-wave full-suite obligation is measured above.
The user approved preparing the shadowing correction as its own small wave.
Design/typecheck completed `shadowing-design.md` (Opus high, session
`652e9d0b-fbaf-4130-880e-10b1af3aff45`) and released its reservation.
`design/typecheck/ownership-inference.md` §20 is explicitly PROPOSED; the report
is `shadowing-design-report.md` in the same scratch report directory. Only owned
design documents changed. No agent or test runner remains active.
The proposal returns to the user before coding; no shadowing implementation is
authorized. Two material inputs accompany this checkpoint:

- Design's scratch program C (`/tmp/cl-design-shadow-2WL3/c.cl`) reportedly aborts
  under the existing binary, while its renamed-binder control `d.cl` exits clean.
  This is new runtime evidence beyond the previously measured result-axis probe;
  QA attribution and a permanent independent reproduction remain owed.
- The coordinator rejects §20.5's claim that `BUILD_ID` necessarily invalidates
  caches on rebuild. Opened `crates/cranelisp-backend/build.rs` and
  `crates/cranelisp-backend/src/cache/mod.rs`: the ID is package version plus HEAD,
  and the existing S103 note explicitly identifies dirty builds sharing that ID.
  Cache invalidation remains unresolved; the design's no-schema-bump conclusion
  is not accepted. Route the exact compatibility delta through arch/user review
  before implementation; do not silently expand this private correction.

The proposed representation, remaining local-name limitations and compatibility
question return together for review. No specification or public API was changed.
The user approved the stable parameter-identity direction, conditional on QA
runtime validation and cache compatibility being resolved before coding.
Two bounded read-only role passes are dispatched: `shadowing-qa-readiness.md` (QA,
the sole existing-binary probe runner) and `shadowing-cache-review.md` (arch,
no execution). Both use the canonical Fable/high allocation and write scratch
reports only. Fable refused both immediately for exhausted usage credits, with
zero tool uses (QA session `f1d4ac43-8a78-4e85-91a1-b456015bb383`; arch session
`111de81a-1657-4bbf-a0d2-b6653fcaaabb`). Both same-scope passes were retried on
the previously authorized Opus/high fallback (QA session
`7c172a81-be94-45fd-bc44-5239aa2791c9`; arch session
`f053ec35-2fbc-4819-97fc-5af0e6fb7012`). They return an evidence delta and compatibility proposal; no
implementation, schema change or phase advancement is authorized by this gate.
Arch completed and released: `shadowing-cache-review-report.md` recommends
`CACHE_SCHEMA_VERSION` 27→28 in the landing change-set, using existing wholesale
cache rejection. No serde shape, platform ABI or generated public-API line
changes; backend owns the constant, version note and existing canary update.
User approval remains required. The report was relocated unchanged from the
repository root to its instructed scratch destination. QA remains active.
QA's written `shadowing-qa-readiness-report.md` validates C's runtime failure and
rename control, and allocates independent runtime/RC-parity evidence plus the
missing ABI-axis module cell. Readiness is conditional on design record repair
and resolving §20.5(ii)'s unsupported harmless-imprecision claim for retained
local-name capture recursion. No capture redesign is authorized. The coordinator
closed QA's binary/source-mtime caveat by rechecking the same binary SHA256 and
both non-comment source hashes recorded at the previous comment-only checkpoint;
all match. The coordinator does not accept the reports' claim that example B
returns `p`: the actual `/tmp/cranelisp-qa-shadow-e8zefR/B.cl` passes `true`, so
the shown source selects `"lit"`. Its runtime-alias claim is not evidence for
this wave and returns to the record owner; C's independent evidence remains.
QA completed successfully and released. Both role passes are complete; no
agent or test runner is active. Mechanical checks: scoped whitespace clean,
live citation ratchet 481 documents / 8,476 references / zero findings.
The user approved the exact 27→28 cache compatibility delta. One batched
design-record correction (`shadowing-design-reconcile.md`, design/typecheck,
Opus high, session `15acd594-d0b5-437f-82e4-b82c3dc6ea70`) now covers the accepted direction, cache
decision, verified observations and the retained-capture limitation. Any new
architectural solution returns to the user; independent repros precede coding.
Design reconciliation completed successfully and released; no agent or runner
is active. Report: `shadowing-design-reconcile-report.md` in the scratch report
directory. Cache approval, the limited historical drain measurement and the
rejected runtime interpretation of B are reconciled in the owned design.
The pass proposes one substantive refinement: make an unconditional origin's
parameter index mandatory (`usize`, not `Option<usize>`) and delete the
name-following recursion in `classify_capture_escape`. Its source census finds
each such origin seeded from a parameter or inherited from an operand.
The coordinator returns this refinement to the user before implementation,
despite the report recommending immediate sequencing. §20.7's "not a design
question" wording does not authorize this additional change. No new schema or
public API change is proposed beyond the approved 27→28 bump.
The mandatory index prevents an absent index; it does not alone prove that the
chosen index is correct. Inherited-index correctness and removed-recursion
behavior still need the allocated module evidence. Owner follow-up also needs
to reconcile §20.3's remaining `param: Some(i)` wording with the proposed
mandatory field. These are not grounds to invent more runtime machinery.
The user now approved the mandatory-index refinement and recursion removal,
and proceeding to failing regression tests and implementation. The shadowing
wave is realizing within Phase 5: independent `test` evidence first, then
serial typecheck/backend implementation, scoped review and QA adequacy. The
approved schema bump remains 27→28. `shadowing-test-red.md` dispatches the
allocated runtime/control and silent RC-parity tests (Opus high); it is the
sole source/build/test runner. No new public API, spec semantics, golden
recapture or phase advancement is authorized.
Test completed (Opus high, session `6c6e8c67-5306-4c30-af9e-6efb82073eeb`):
`tests/shadowed_param_reach_stale_rc_dec.rs` adds six independent cells, four
intentional reds and two green rename controls. Four focused runs agree; the
combined prior R1 basket is 4 passed / 4 failed. The rebuilt binary reproduces
the earlier abort and marginal one-inc/one-dealloc difference. Report:
`shadowing-test-red-report.md`. C″'s differing oracle sensitivity is QA intake,
not an allocated new condition or reason to delay the approved repair.
The source reservation now passes to dev/typecheck through
`shadowing-dev-typecheck.md` (Opus high), the sole source/build/test runner.
Provider session: `e62b1ffa-daab-4c6b-b007-3a786728f6cb`.
Module ABI/flow evidence precedes the fix; existing independent assertions
remain unchanged. Backend's approved cache bump follows serially.
Dev/typecheck completed and released (`shadowing-dev-typecheck-report.md`):
896/896 module tests pass; three of four independent reds flip green, controls
stay green. Rename-counter parity remains red with equal allocation/deallocation
balance and a balanced inc/dec difference reported even with ownership disabled.
The report also measures a pattern-shadowing result-provenance loss; its
transient module probe was removed, so durable failing evidence is still owed.
QA will classify both findings in one bounded read-only pass
(`shadowing-qa-parity.md`, authorized Opus fallback). The sole source/build/test
reservation passes to dev/backend for the approved 27→28 cache bump
(`shadowing-dev-backend-cache.md`, Opus high). No additional pattern repair or
backend behavior change is authorized by these reports.
Backend cache completed (session `3ddb396b-f256-49d2-8e45-c391d50fe8d4`):
27→28 is applied; a new schema-27 rejection witness was red before the bump
and green after. Cache module 79/79, backend 559/559, independent cache 44/44.
QA completed its finding classification (session
`8b441a82-d8ef-4baf-b8ce-13300cd715ed`): pattern-origin loss is an implementation
gap in approved §20.3, not a new design decision; the remaining balanced-counter
asymmetry is a backend finding with mechanism still hypothetical and no broader
investigation authorized. Test metadata re-attribution remains owed.
The source reservation is now `shadowing-pattern-completion.md` (dev/typecheck,
Opus high): permanent module red/control, approved origin inheritance and the
one QA-allocated runtime probe. Independently, `shadowing-review-cache.md`
(review/backend, Opus fallback) inspects the completed cache-only delta read-only.
Pattern completion finished (session `5278306c-d942-44d2-b95c-9f00b9936c52`):
the permanent result-axis subject flips red→green, rename control and provenance
suppression remain green; typecheck 898/898. Report and retained probe are
`shadowing-pattern-completion-report.md` and `pattern-shadow-rc-probe/` in the
scratch report directory. The probe shows no pre/post runtime change on that
shape, but a subject/control allocation difference survives ownership OFF;
this is further backend intake, not an implemented or authorized backend fix.
The report's statement that the cache bump has not landed is stale: schema 28
is already applied by the completed preceding backend pass.
Cache review completed (session `2fe50e85-3540-4d19-8f3b-34cfb2e64362`): no
blocking/required findings; two backend wording advisories retained.
Now active: `shadowing-test-records.md` (test, metadata/assertion-message only)
and `shadowing-review-typecheck.md` (independent read-only review, Opus fallback).
No source runner is active on production code; no broader backend investigation
is authorized. Final integrated census and QA adequacy remain owed.
Active closing passes: test metadata session
`d1000e56-4a94-476b-8a7e-8aa391814bbc`, independent typecheck review session
`b45939c4-4a75-4017-9070-2b77cd7720b3`, and design as-built reconciliation
session `917fe40e-6c9a-4465-8e43-bd2f304bd3b6`. All use Opus/high (review on
the authorized fallback); only the test metadata and owned design docs may
change, not production code. The fresh final evidence directory is reserved at
`/tmp/cranelisp-s121-shadow-final-J6xI72`; no census has run there yet.
Those record passes completed. Typecheck review completed with no blocking or
reach-repair code defect, three required evidence/record findings and four
advisories (`shadowing-review-typecheck-report.md`). QA is classifying R1 in
its final adequacy pass; design and dev own R2/R3's factual record corrections.
The regenerated typecheck and backend public APIs exactly match their current
baselines with the existing blanket/auto-derived filters; no baseline rewritten.

**Fresh shadowing-wave census:** nextest
`d74fe705-e1fb-4f15-bd04-799fcc042d3c`, 137.273 seconds, **5,854 run / 5,846
passed / 8 failed / 1 skipped**. All eight are the seven held CLIF checks plus
the QA-classified backend rename-counter guard. The prior timing failure is
not present in this run. Raw output and pre/post-verified source hashes are in
`/tmp/cranelisp-s121-shadow-final-J6xI72`. No production/test behavior changed
during the census; all five source hashes matched afterward.
Final active passes: QA adequacy (`shadowing-qa-close.md`, session
`ce5126f3-5120-478f-b3f9-27ba0278ac76`), design R2 record correction
(`shadowing-design-review-records.md`) and dev/typecheck comment-only R2/R3
repair (`shadowing-dev-review-records.md`). No re-review or repeat census is
owed for verified comment-only corrections. No backend investigation or phase
advancement is authorized.
**Current user checkpoint — shadowing correction implemented and QA-accepted.**
QA completed `shadowing-qa-close-report.md`: the stable-origin correction,
mandatory index, capture-recursion removal, pattern completion and epoch 28 are
adequate as a bounded correction; no whole-sprint release judgment. Review R1
is resolved as a precisely stated evidence residual, not proof that the pattern
shape can never need e2e evidence. QA completed its owned coverage-band and plan
updates. Review R2/R3 are corrected by completed design/dev record passes
(`shadowing-design-review-records-report.md`, session
`40eb8d41-6abb-4f9b-a277-39eabee31256`; `shadowing-dev-review-records-report.md`,
session `c1f7061e-c45f-4b73-844b-b648490ac064`). New-cell citation repairs are
complete; pre-existing duplicate-cell/citation and whole-guidance-budget
advisories remain for their allocated close/future disposition.
The final comment-only pass preserved both Rust token streams; the coordinator
also independently matched both comment-stripped hashes and the census binary
hash `73d703accbf689475c58c32132d66bcf09194911a7bf6a41c75242e6761956f8`.
No agent or test runner remains active. Scoped whitespace checks are clean;
live citations: 481 documents / 8,496 references / zero findings before this
final coordination update. No commit, golden recapture or phase advancement.
The user confirmed both zero generated API diffs and approved QA's bounded
backend subject/rename/non-parameter-shadow investigation on 2026-09-08.
Dispatch `dev` (backend) for diagnosis only, using existing RC-site observations
and retained scratch probes. Return the mechanism and proposed repair scope to
the user before implementation. No fix, API/spec change or deferral is approved.
The known backend red and seven CLIF holds remain.
Diagnosis dispatched through `.agents/tools/claude_role.py` to Claude `dev`,
Opus/high, session `4303beb8-9702-4be1-9331-ba11d9ad208c` (completed successfully,
538.3 seconds; provider model `claude-opus-5`).
Brief/report destination: `/tmp/cranelisp-s121-fable-qa-Vt0n9y/backend-shadow-diagnosis.md`
and `backend-shadow-diagnosis-report.md` in that directory. Repository edits
are excluded; scratch probes are retained. Approval-record citation check:
481 documents / 8,496 references / zero findings.
Diagnosis outcome: backend scope pop deletes shadowed names without restoring
the outer binding. The non-parameter-local control reproduces the same missing
retain/release pair; related retained probes demonstrate a rejected outer-name
lookup and one leaked allocation on the default path. The coordinator checked
the reported pop/cleanup/protect source sites and raw refusal/leak outputs.
No UAF was established and no repair was applied. The unchanged-source rebuild
produced binary SHA-256
`dafe264ca7ad84ccb965c36b4a35f14b95bcfa71758105540d9c1f3f65592633`;
this is distinct from the previous census binary. Probe commands and results
are retained in `backend-shadow-scope-probe/` beside the report.
The report's next-step list is not authority: stale typecheck defect-locus
repairs were already completed, and its claim that BUILD_ID handles every
uncommitted codegen rebuild is not accepted. Cache invalidation must be assessed
with the eventual repair; private non-serialized state alone does not settle
cached machine-code validity. QA classification and a bounded backend design
proposal with permanent reproductions are proposed next, not dispatched.
User follow-up authorizes the repair sequence and establishes it as the
standard discovered-defect workflow (`METHOD.md` §2.2): permanent minimal
RED reproductions first, then design and implementation to GREEN; parallel QA
review explains the missed scenario and assesses systematic coverage gaps.
Existing spec/architecture/public-API approval gates remain in force.
Active dispatches: `test` writes/runs the minimal refusal/leak reproductions;
`qa` reviews coverage read-only in parallel. Briefs, results and reports are
under `/tmp/cranelisp-s121-scope-repair-bPzLW8/` (`test-red.md`, `qa-gap.md`).
Test owns the sole source/build/test reservation. Backend design follows the
established REDs, not a serial QA prerequisite; substantive design/API questions
return to the user before implementation. No commit or phase advance approved.
Test: Claude Opus/high, session `2cee8231-28c1-4331-a560-062844350de4`.
QA Fable/high session `9a642979-5fad-4e91-a097-01fb3e8a5ddc` ended immediately
with HTTP 429 exhausted credits and zero tokens; no assessment ran. Retrying
the same named QA role and brief on the user's previously authorized Opus
fallback; role authority, high effort and read-only scope are unchanged.
QA fallback active: Claude Opus/high, session
`38fa685a-f3dd-4436-8f6a-f43d1ae3e754`. RED checkpoint executed in
`tests/shadowed_param_reach_stale_rc_dec.rs`: 10 tests, 7 PASS / 3 RED;
new outer-local lookup and marginal-leak guards fail for the measured defects,
their controls pass, and the prior RC-parity guard remains RED. Raw output:
`/tmp/cranelisp-s121-scope-repair-bPzLW8/test/nextest-focused.txt`.
Backend `design` proceeds from those REDs while test finishes its report and
QA continues independently: Claude Opus/high, session
`078d82a0-55c8-4f22-900e-46e1c3e742b1`, brief `design.md` in the same scratch
directory. Design is read-only proposal work; no product edits or builds.
Test completed successfully (648.9 seconds, `claude-opus-5`): four new cells
in the existing file, two RED defects and two GREEN controls; focused total
7 PASS / 3 RED, arming guard 4/4, test citations zero malformed/mis-cited.
QA completed successfully (616.8 seconds, `claude-opus-5`), report
`qa-gap-report.md` in that directory. Its inspected corpus exposes an untested
scope-exit/restoration observable and incomplete sibling-state coverage; this
is a systematic gap, not only two missing examples. Its static corpus scan
has stated extraction limits, so exact whole-repository completeness is not
accepted. QA corrects its earlier refuter: non-parameter shadowing refutes a
parameter-only explanation, not the broader name-underkey mechanism. Proposed
class: `binder-name-underkey`, covering all three backend REDs.
QA allocates a scalar restoration control and module evidence for the related
binding-state lifecycle; design may replace detective rows with constructive
invariants where justified. QA's report-only coverage-band, plan and standing
lens updates remain owed; they were not silently applied in parallel. Spec
prose changes (including splitting requirement rows) still require user review.
Any register regrade is routed to its owner, not adopted from this report.
Only the backend design session remains active; no test runner remains.
Design completed: `design-report.md` in the same scratch directory. Proposed
private backend shape is one scope chain owning each binder's complete facts,
with a separate function-lifetime capture environment; related write-only glue
state is proposed for deletion. About ten backend files are affected. This
compiler-structure decision returns to the user, not directly to implementation.
The user settles same-form repeated names as legal sequential shadowing, using
`(let [a 1 a (+ a 1)] a)` as the discriminating example (result 2). Each
initializer sees the preceding binding; the new binding applies afterward.
The ruling includes the same behavior with sparks enabled, not a restriction
introduced to accommodate the backend. Spec clarification and minimal permanent
RED reproductions are authorized; the proposed backend representation is not.
Design's additional publication-order and TCO-shadow failure claims are not
executed reproductions: apply the newly established RED-first process before
calling them defects or claiming them fixed. Its no-epoch-bump recommendation
depends on an executing warm-cache check of the compiler-mtime invalidation
path; no cache decision or public-API delta is approved by a report.
The report also notes an onward read-only census delegation despite its brief's
no-delegation constraint; this is a dispatch deviation, not added authority.
QA report corrections and coverage updates remain part of this repair's close,
not new spec authority. No product implementation, source commit or golden
refresh occurred. All top-level role dispatches have completed; user gate next.
Following that ruling, `test` is assigned the same-form and spark-rebinding
reproductions; read-only QA coverage review runs alongside it. In particular,
the source lead is the sparked-name set not being cleared by a non-sparked
rebinding, and the name-to-IVar map visiting only sparked binders. These are
source observations, not runtime results. Test must establish a discriminating
RED or report the control that refutes the suspected runtime consequence.
Briefs/results: `/tmp/cranelisp-s121-rebinding-2ll8aL/`. Test owns the sole
source/build/test reservation. Spec will apply only the user-approved semantic
clarification after that reservation releases. No fix, public-API or cache
change, golden refresh, commit or phase advance is authorized by this step.
Rebinding RED dispatch: Claude `test`, Opus/high, session
`7934a9bf-b54f-4746-8b07-1b076e77bc18` (active). Parallel coverage review:
Claude `qa`, Opus/high, session `a66ac64f-b66c-469f-9b57-3f9ad3a19210`
(active), using the user's fallback after Fable's prior HTTP429 credit refusal.
Rebinding test and QA dispatches completed. `tests/same_form_rebinding.rs`
adds nine permanent cells: 7 GREEN / 2 RED. The user's arithmetic example
already yields 2; the REDs are lenient lowering yielding 21 instead of 15 after
a sparked→non-sparked rebinding, and a same-form heap binding's marginal leak
of +1. No-lenient, renamed-binder, dependent-spark and sparked→sparked controls
pass. Existing shadowing file remains 7 GREEN / 3 RED; related focused
expression/runtime/spark/citation suites pass 182/182. No product fix.
Reports/raw evidence are `test-report.md`, `qa-report.md` and `test/` in the
same scratch directory. QA finds the same-form multiplicity/spark-transition
coverage axis missing; its source attribution preceded these executing results
and needs consolidation at the repair's QA close. Do not adopt its statement
that tests could not observe the gap: the new tests do; representation limits
are implementation facts, not limits on observable testability.
Spec now has the sole edit reservation to scribe the user's exact ruling in
§4.3, including the dependent-initializer example, and invalidate affected
coverage annotations. No additional normative change or implementation allowed.
Spec completed successfully: Claude Opus/high, session
`8999bc52-ee16-47a8-b39c-1a04b7a36a59`, report `spec-report.md` in the same
scratch directory. §4.3 explicitly permits repeated names and illustrates
`(let [a 1 a (+ a 1)] a)` => 2; "fresh name" becomes "fresh binding" to
match the approved reuse rule. No change to spark rules, typing, deallocation
timing or nested-shadowing semantics. The coordinator accepts that terminology
hunk as the user's same-name/new-binding ruling, not a new policy. §4.3's
summary coverage tag is invalidated with its former citations preserved;
QA restoration and new PLAN rows remain owed at consolidated repair close.
Final citation check: 481 documents / 8,499 references / zero findings;
test-side links: 2,482 citations / zero malformed or mis-cited. Coverage
reconcile reports the intentionally cleared §4.3 row, not a release pass.
All dispatches have completed; no agent or runner remains active. RED-first
checkpoint is delivered with two additional measured backend failures. Next
is to reconcile the pending backend design with the measured spark dependency
case before returning its structural proposal to the user. No fix, commit,
golden refresh, cache/public-API change or phase advancement occurred.
User approved the next bounded design update: reconcile the existing backend
proposal with all five measured scope/rebinding REDs, then present one compact
structural proposal for review. Dispatch `design` (backend), scratch/read-only
only; no implementation or new normative/public-API decision is approved.
Brief and destination: `/tmp/cranelisp-s121-rebinding-2ll8aL/design-update.md`
and `design-update-report.md`. Prior QA reviews are inputs, not new work to
repeat; the sole active role has no onward-delegation authority.
Active: Claude `design`, Opus/high, session
`a6ad3463-e60f-4fcf-9c9a-3dcba1a24102`; shared wrapper, auto permission mode.
Approval-record checks: whitespace clean; 481 documents / 8,499 citations /
zero findings. No build or test runner active.
Design update completed in `design-update-report.md`: proposes per-binder scope
slots plus binding-position-keyed spark state. Before user presentation, sprint
returned three precise coherence questions to `design`: combined value/type
publication versus excluded ordering change; all-slot-keyed cleanup claim versus
retained name-keyed skip sets; and the claimed structural uniqueness of emitted
Variables. No proposal is accepted from a contradictory report. Finding-scoped
read-only clarification brief/result: `design-coherence.md` and
`design-coherence-report.md` in the same scratch directory. No new census,
implementation, test run, normative edit or onward delegation authorized.
Finding-scoped design clarification completed: Claude Opus/high, session
`e6fa402f-eeba-4510-b0ee-c716745be353`, report `design-coherence-report.md`.
The addendum governs where the update disagrees: publish a binder's value/type
together after its RHS; a separate runtime-failure claim for the prior early
type publication requires a RED first. Slot-identity guarantees cover the
frame-release path, not the retained name-keyed TCO/capture/transfer attributes;
their suspected failures remain unmeasured and are not claimed fixed. Unique
Variable construction is not proven merely by grouping fields: the implementer
must enforce the claimed construction boundary or report the honest weaker
grade. No machinery is authorized merely to preserve report wording.
Both design sessions are released, with no source/build/test activity. Present
the consolidated backend-only scope-slot + positional-spark proposal to the
user; no implementation, deferral disposition, public-API/schema change or
phase advance is yet approved. QA coverage record consolidation remains owed.
Golden refresh and Phase 6a remain unapproved.

User approves the consolidated backend repair scope: per-binder lexical slots,
positional spark state, value/type publication after the initializer, separate
capture environment, and deletion of the two unused closure-glue bookkeeping
fields. This authorizes implementation within Phase 5, not a public API, schema,
specification, golden, commit or phase change. Sequence: design records the
approved shape while read-only QA allocates the remaining publication-order and
warm-cache evidence; test preserves required pre-fix evidence; dev implements
with module tests; independent review and QA close the repair together.
Unmeasured TCO/capture suspicions are neither fixed nor silently deferred.
Current dispatch briefs and reports use the rebinding scratch directory above.
Design record completed: Claude Opus/high `f4ae4f82-28ac-4e3a-8904-ed0e8fdc3a5e`;
canonical target `design/backend/binding-scope.md`. Read-only QA allocation
completed: Claude Opus/high `f69596de-7763-4f58-b091-d87a0b315faa` (authorized
Fable-credit fallback). Reports: `design-record-report.md`, `qa-remaining-report.md`.
Test takes the sole reservation for warm-cache pre-fix evidence. QA allocates
publication-order evidence at dev's module seam before implementation; a
type-changing e2e leak alone cannot distinguish it from the existing cleanup
defect. Post-fix GREEN cannot retrospectively prove or refute that attribution.
The report's request to reapprove D1–D6 is stale: the consolidated user scope
is already approved. Report-only residual acceptance is not user deferral.
Test pre-fix handoff completed: Claude Opus/high
`be16147b-7366-457a-8c74-4d2ce535c184`, `test-prefix-report.md`.
Preserved compiler/project/cache: `/tmp/cranelisp-s121-t1-cache-qVu0mv/`.
Imported-module warm hits repeatedly return 21, with unchanged object hashes
and mtimes; mtime-only compiler control invalidates cache. Post-fix leg owes 15.
Type-changing same-form regression guard is GREEN pre-fix (residual zero);
the original five REDs remain. Dev now takes the sole source/build/test
reservation for approved repair and module RED-to-GREEN evidence. No schema
decision follows from the pre-fix control alone; no new runtime defect claimed.
Backend dev completed: Claude Opus/high
`e8148001-9575-4cb8-ac8e-20fefd953032`, `dev-repair-report.md`; incremental
checkpoint/diff and raw evidence in `dev-repair/`. Five original REDs GREEN;
both e2e files 20/20, backend final 576/576. Final full suite: 5,885 run /
5,878 pass / seven held golden failures / one skipped (103.373s,
`d78dbbaa`). Golden failure payloads match the pre-repair checkpoint; no refresh.
Warm-cache repair leg and subsequent hit return 15; schema 28 unchanged.
Filtered backend API before/after is identical (558 lines). New module
detection evidence includes post-implementation fault planting; do not describe
that as a pre-implementation RED sequence. Shell-write use deviated from the
brief's apply_patch constraint. Independent review and QA adequacy now run
against the frozen delivered checkpoint; no phase advancement or commit.
Review completed: Claude Opus/high `aac38a94-3748-45fe-bfc4-6b19eeccba39`;
QA completed: Claude Opus/high `15194590-dce7-4f7d-a5af-83feb7590c94`.
Both used the authorized Fable-credit fallback. Reports `review-repair-report.md`
and `qa-close-repair-report.md`: five-fix evidence adequate, with required
follow-up on par-continuation capture-type emission, golden comparison scope,
and M2 detection-claim wording. Only six golden failure payloads were compared;
the lane's generic failure does not establish identical full-corpus output.
No additional par runtime defect or correction is accepted from source inspection.
Bounded scratch-only pre/post probe now assigned to dev; QA reconciles findings
and removes its unapproved [S122] residual scheduling. Source stays frozen.
Test annotation/status cleanup and design as-built consolidation remain owed;
the wave is not closed, and no residual has been silently deferred.
Finding-scoped QA completed: Claude Opus/high
`310c14a3-b05d-43d4-a56d-469a6c986d71`, `qa-findings-report.md`.
PLAN residual now [S121], unresolved; no carry approved. Golden comparison
scope is six full payloads plus capped 40-line lane windows, not the full
corpus. M2 has an executing negative leg and recorded post-implementation
mutation evidence, not a historical RED or permanent mutation seam.
Bounded dev probe completed: Claude Opus/high
`77ff0314-629b-420f-a80f-d59e71e2c200`, `dev-par-probe-report.md` and
`dev-par-probe/`. Pre-fix par continuation using a heap capture aborts with
STALE RC DEC; repaired compiler returns 8, in run and link (five repeats).
Local/scalar/single-bind/no-IO-schedule controls pass both versions. Source
unchanged by probe. This is an additional observed correction, not yet a
permanent regression guard or approved widening. Generated par-body CLIF is
not exposed by the existing dump; global emission-identity claim stays narrow.
Probe rehashes live binary as a9b4db7b… (prior dev report's 85a0ac2a… is not
the live hash); source snapshot matches, but final acceptance must re-establish
fresh build provenance rather than rely on mtime alone.
All roles completed, no runner active. User checkpoint: retain the additional
par-capture correction with permanent pre-fix RED/post-fix GREEN evidence,
and add the two QA-allocated same-name capture/transfer module controls before
consolidated record closure, or obtain explicit alternative disposition.
Neither further correction nor residual carry is inferred. Phase 5 remains.
User approves the finishing scope: retain the observed par-capture correction
with permanent old-RED/new-GREEN regression evidence; add the two remaining
same-name capture-ownership/tail-transfer module controls; finish associated
design, test-status and traceability records. Test takes the first sole
source/build reservation; read-only QA handles the par coverage escape alongside
it. Then backend dev adds the allocated module evidence and in-scope memory
cleanup, followed by consolidated records and affected review/QA checks. This
does not approve new architecture, spec/API/schema changes, carries, goldens,
commits or phase advancement. Existing live scratch directory remains canonical.
QA allocation completed: Claude Opus/high
`0e18d697-e8a2-4696-91f0-2910b8eaed0b` (authorized Fable-credit fallback),
`qa-finish-allocation-report.md`. Existing par module cells omit capturing
continuation bodies; allocated one outer-retain fence plus the already-approved
two residual subject/control pairs. No new compiler observation seam.
Test handoff delivered and reservation released: Claude Opus/high
`a3aa14b9-d27a-4305-9d8c-f5499a469f09`, `test-finish-report.md`.
Permanent `tests/par_cont_capture_consuming_use.rs`: same test binary against
old compiler gives one subject FAIL (run/link) and four controls PASS; repaired
compiler 5/5. Combined files 25/25. Five older defect annotations/statuses
updated. Final class ruling and runtime spec band remain QA-owned.
Feature-unified suite binary differs from plain-bin build; test handoff records
both hashes and source fingerprint, resolving the earlier provenance mismatch.
Backend dev takes sole source/build/test reservation for final module evidence
and in-scope memory cleanup. No new production fix is authorized by a failing
control; any required expansion returns with its RED and design impact.
Provider block: both test and dev wrappers terminated on Claude's weekly quota
limit, reset reported 2026-09-11 07:00 Australia/Melbourne. Test session
`a3aa14b9-d27a-4305-9d8c-f5499a469f09` had already delivered its report, permanent
guard, controls and final-focused-run.log (25/25); wrapper outcome is error,
not successful completion telemetry. Backend finishing session
`34333fc2-1f51-47eb-9247-a23bf61d2728` stopped during source inspection; no report
or module controls produced. Coordinator confirms backend source still exactly
matches dev-repair/after-backend-src. No agent/test runner remains active.
Remaining: two residual module pairs and par outer-retain fence, memory/design
consolidation, final QA traceability/class ruling and affected verification.
Do not rerun completed e2e work or claim the finishing scope complete. Provider
substitution needs user direction under root CLAUDE dispatch rules; no automatic
model/harness change or phase advance. Brief dev-finish.md is ready to resume.
User explicitly authorizes Codex models for the remaining roles after the
Claude quota block. Resume named `dev` in the primary harness, GPT-5.6 Terra /
high, task `/root/dev`, using the existing dev-finish.md brief and sole
source/build/test reservation. This is a task-specific provider override, not
a repository role-allocation change. Completed test work is not repeated.
User pause interrupted `/root/dev` before edits or builds. On explicit resume,
the same Codex role confirms read-only pre-pause activity and no live command;
it resumes the existing finishing brief and preserves dev-finish/before.
Codex `/root/dev` completed the bounded finishing visit, report
`dev-finish-report.md` and `dev-finish/focused-evidence.md`. Capturing ParBind
outer-retain fence 1/1, M2 2/2, par e2e 5/5 after fresh build. No product,
API/schema/spec/golden change; M2 wording and crate-memory cleanup completed.
The added `same_name_tail_transfer_releases_the_displaced_binding` remains a
permanent unignored RED (nextest `acc932d2-766f-4b06-84b2-69f604e96d62`):
same-name subject has two calls before the recursive backedge, rename control
three. Name-keyed tail_transfer_skip exempts the displaced binder as well as
the actual transferred binder. Required binder-identity correction is not yet
authorized; no fix or full-suite replay was attempted.
Codex `/root/qa`, GPT-5.6 Terra/high, completed read-only observation allocation:
`qa-capture-observation-report.md`. Tail RED is a binder-name-underkey safety
fence sufficient for design/user triage; runtime marginal evidence is assessed
by test if correction is approved. Par class remains rc-miscount, avoiding
unnecessary taxonomy rewrite. Capture-membership's existing module observation
cannot reach the separate lambda body; no fabricated state, runtime defect or
accepted carry is claimed. This limitation remains explicit for final adequacy.
All active role work is released. Next user decision: apply binder identity to
tail-transfer skip decisions; remaining design/QA standing records stay in the
same repair reservation until its outcome is settled. Phase 5, seven old golden
holds and the new module RED remain; no phase, commit or recapture approval.
User approves the narrow binder-identity tail-transfer correction with explicit
order: isolate and preserve runtime RED, then fix to GREEN. Codex `test`
(`/root/test`, GPT-5.6 Terra/high) owns the first sole source/build reservation;
`/root/qa` performs the bounded coverage-escape review read-only alongside it.
The approved correction does not extend to capture-membership optimization or
new spec/public API/schema changes. Design records the approved private shape
after the runtime RED, then dev implements and affected review/QA closes the
repair. No new approval loop is needed for this already-approved scope.
Runtime RED is established and the test reservation released:
`tail-test-red-report.md`, permanent
`tests/same_form_rebinding.rs::tail_transfer_releases_the_displaced_same_name_binder_run_and_link`.
Both modes return 8; control alloc/dealloc 10/9, same-name subject 10/8
(marginal +1). Harness detection controls pass 3/3. QA's parallel
`tail-qa-gap-report.md` attributes the coverage escape to binder multiplicity
at tail transfer; the existing cross-frame controls do not cover it.
Codex `/root/design` (GPT-5.6 Terra/high) now owns the bounded design-record
visit, followed by `/root/dev` for the approved private correction. No source
build runs concurrently with that record visit.
Design recorded the approved slot-transfer contract in
`design/backend/binding-scope.md` (`tail-design-report.md`). Codex `/root/dev`
implements; both permanent REDs now pass on the final correction, including
runtime run/link nextest `d847d6b6-88e7-4a16-8b5f-3cf06a87b16a`.
Codex `/root/review` (GPT-5.6 Terra/high) found no substantive source issue;
its one final-delta check covers the private argument bundle needed to remove
a new Clippy warning. `/root/qa` now reconciles owned coverage records while
dev completes broader gates and the final suite. No full-green or release
claim is made before those results; seven prior golden holds remain.
Tail repair delivered (`tail-dev-report.md`): run/link control and subject now
both allocate/deallocate 10/9 and exit 8, eliminating the extra displaced-binder
leak without claiming the shared residual is fixed. Backend final suite 579/579;
full nextest `59756968-bbbf-44c2-bc86-0f67a5c009e4`: 5,894 run, 5,886 passed,
8 failed, 1 skipped. Failures are the seven old golden holds plus
`apply_arg_single_expensive_stays_serial`; the latter passed its same-source
focused rerun (`2c24e9ce-e6e8-411b-b982-b61e130ecab0`), which does not erase the
full-suite timing failure or establish its cause. No additional product repair
or golden refresh was made. Scoped build/check/format gates pass, Clippy has
zero new warnings, independent final-delta review has no findings.
Dev released source/build ownership; test applied only `fixed=S121`, and design
marked the correction delivered. Final binary hash independently confirmed:
`429f130bba7b3ba134892572b8491c1a0277e81264190e6957cd043b7787a7ba`.
QA final adequacy and the document checks complete this correction, not Phase 5.
QA accepts the evidence for the approved tail correction
(`tail-qa-final-report.md`); final review reports no substantive finding.
The full-suite timing failure remains a non-reproduced witness-reliability
concern requiring explicit disposition before overall release, alongside the
seven held goldens. Live citation ratchet: 482 documents, 8,514 citations,
zero findings; scoped whitespace clean. No phase advancement or commit.

Earlier intake census:

`cargo nextest run --no-fail-fast --status-level fail --final-status-level fail`
completed with required local-server permissions in 94.084 seconds:
**5,789 tests run, 5,779 passed, 10 failed, 1 skipped**. Raw output:
`/tmp/cranelisp-phase5-census-unsandboxed-20260907-nXQiKE.log` (nextest
`96de9c49-a980-4393-a514-365313d0b0c0`). The default-sandbox attempt had 13
additional port-denial/reactor-backstop failures, all absent on this run.
This supersedes older integrated counts and resume instructions
below; earlier checkpoints remain historical evidence, not current holds.

| Closure stream | Census failures | Next action |
|---|---:|---|
| Warm-cache ownership reconstruction | 1 | Staged-layout wave complete, including user confirmation of generated +1 API; cache repro returns 40 with verified metadata preload, example 35 cold/warm returns 100 |
| Backend callable/value handling | 0 | Vec-query and result-context specialization repairs are complete and pass the fresh census |
| Test maintenance | 0 | Approved rejection-and-retention assertions and canonical trait-method display pass; stale devloop row deleted as approved, global checks have zero missing names/miscitations |
| Examples aggregate | 1 | Repaired: example 33 direct uncached/cold/warm exit 6; aggregate 4/4 passes (35 top-level examples plus three directory cases). Example 35 unchanged |
| Citation maintenance | 1 | Two obsolete free_io_branches references repaired; subsequent live citation ratchet has zero findings, without baseline extension |
| CLIF baselines | 7 | Fresh drift collection and read-only backend attribution in progress; no recapture until deltas are explained |

Independent platform review found no implementation/API defect but found the
already-allocated R4 E1–E3 DLL-return ownership tests absent. The test visit
added those three cells: discard heap-valued `Pure`, force and release its
string result, and discard scalar-valued `Pure`. Existing CLIF/layout tests do
not execute that DLL adoption boundary. Examples' focused rerun reports exactly
two failures out of 35: example 33's duplicate definition and example 35's
unexpected ownership-ABI replacement rejection, now reproduced on warm-cache
loading despite its source containing no authored replacement.

QA `/root/qa_census_closure` classified the census read-only. Backend
`/root/dev_backend_closure` completed the private `vec-len` wrapper correction
with scalar/heap ownership guards and detection plants removed before its final
green run. `/root/test_phase5_closure` completed and released the evidence
visit: six migrated assertions and three DLL ownership cells pass **9/9**.
Independent
`/root/review_platform_closure` passed the previously
approved platform implementation/API; the allocated DLL evidence is now green.
A new integrated census and reconciled evidence return to the user
for the Phase-5 acceptance checkpoint. Specification, architecture and
inter-crate public-API changes still require explicit user review.

Read-only `/root/dev_typecheck_closure` found that current demand production and
specialization identity retain argument types, not the required concrete result
context. Removing the nullary-call filter alone cannot realize or distinguish
the result-only specializations required by `spec/03-types.md` §3.11.3. That
repair is now approved and implementing as recorded below; the test visit
retains the existing failures and adds a discriminating reduction/control.
The backend's absent-element-type disposal fallback was corrected in the
completed B4 visit recorded below.

### Closure handoff — result-context wave complete

**2026-09-07:** User approved the exact result-context clarification now applied
in `spec/03-types.md` §§3.3.4, 3.6.3 and 3.6.4. It replaces argument-only
specialization and naming prose with complete concrete generic substitutions,
and distinguishes independent calls from incompatible shared-instance and
unresolved runtime uses. Changed coverage remains for QA reassessment; scoped
test-to-spec citations passed 93/93. No compiler or public API changed with
that specification edit.

On “ok keep moving”, `/root/arch_result_context` prepared the standalone
[result-context architecture/API proposal](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/s121-result-context-specialization.md).
It proposes substitution-based `type_args`, explicit `from_type_args`
constructors on the two existing carriers, and cache schema 25→26, with no
platform ABI or new consumer edge. Generic-variable positions follow structural
first occurrence, not numeric inference-ID order. **User approved the architecture
and exact API packet on 2026-09-07 (“approved”).** The pre-implementation API
gate is satisfied for that packet only; generated-baseline confirmation remains
a separate user gate. `/root/design_result_context` owns the typecheck interior
design and `/root/qa_result_context` the compact evidence/readiness allocation.
The [typecheck interior design](../../design/typecheck/result-context-specialization.md)
is complete with no additional API/semantic question, source citation 1/1 and
clean whitespace checks. It includes the argument-derived recursion and nested
call consumers in the same crate visit. Remove superseded argument-only prose
from the master/subsystem design during implementation's as-built reconciliation.
QA readiness is **GO** in `tests/plan/s121-test-plan.md` §12: compact evidence
allocation complete, 48 citations checked with zero findings and whitespace
clean. Acceptance remains pending execution/review. The test visit must correct
the obsolete unused-generic-wrapper rejection against the already-approved
specification, preserving the genuine unresolved-runtime-use negative.
The reservation order is types →
typecheck → backend cache → binary/integration → independent review and API
confirmation, all within Phase 5.

**Resumed 2026-09-07:** named Codex dispatch is operational after the user's
retry. `/root/dev_result_types` completed the approved types migration:
276/276 package tests, all-target check, formatting and whitespace passed;
the identity guard detected deliberately discarded substitutions. The generated
API delta is exactly four removed/four added lines, pending user confirmation.
`/root/dev_typecheck_recovery` completed and released the source/test reservation:
858/858 package tests, all-target check, formatting and whitespace passed;
three as-built design documents passed 82 citation checks. Three lost mint-seam
tests were restored; the 18 remaining removed tests cover the retired private
name encoder. Independent `/root/review_typecheck_result` closed its one
dispatch-evidence finding after concrete consumer-target assertions were added.
Reversed-order and wrong-dispatch plants were detected and removed before the
final run. Normal clippy exits successfully with 153 library / 187 test
warnings; strict warning cleanliness remains unmet by existing lint debt.
Independent
read-only `/root/review_types_recovery` found no material types finding and
confirmed the exact four-removed/four-added API delta against the pre-wave
snapshot; it did not rerun the implementer's tests. Backend
`/root/dev_backend_result` completed schema 26 and schema rejection before
symbol-table decoding: cache 25/25 and backend 552/552, check/format/whitespace
passed; the link-loss plant was detected and removed. Existing clippy warnings
remain (11 library / 14 test), none in its changed files. Independent backend
review found no material issue. `/root/dev_binary_result` completed binary
consumer fixtures and evidence: focused 2/2, root library 757/757, all-target
check, formatting and whitespace passed; two detection plants were removed
before the final run. Independent binary review found no material issue.
`/root/test_result_completion` completed and released the final source/test
reservation: allocated behavior 6/6, public-API comparison 3/3 across all seven
crates, scoped formatting and whitespace passed. The warm-hit observer detected
disabled caching even while the program still returned 200; the restored case
passed 1/1. Final independent test review found no issues. QA restored five
result-context coverage tags and reconciled the stale unused-wrapper plan row:
scoped test-to-spec 138/138, three documents / 567 citation checks and whitespace
passed. QA adequacy is PASS and all reservations are released. The global
coverage check still reports two stale devloop test names at
`repl/spec/03-slash-commands.md:357`, with no dead-file or cleared-tag findings;
this is not a whole-sprint green claim. **User confirmed the exact generated
four-removed/four-added API diff on 2026-09-07 (“proceed”).** The result-context
public-API gate is complete. `/root/arch_result_converge` completed canonical
architecture reconciliation in five documents: 215 citations and whitespace
passed, with no unresolved contract question. The referenced packet path stays
stable until coordinated reference reconciliation permits its archive.
`/root/test_closure_census` completed and released the runner; the fresh census
above governs remaining work. Binary added the permanent module RED
`src/worker/tests.rs::cache_preloaded_sum_projection_recheck_preserves_ownership`
and released its idle runner. Identical source infers Borrowed with fresh imports
but Copy with cached metadata, even after removing cached authored functions;
schemes remain equal and the divergence precedes the ABI guard. QA retargeted
the defect to typecheck's published-only metadata input to `CopyClassifier`.
`/root/design_staging_layout` completed read-only assessment: both ownership
layout consumers need staged metadata, but the shared `value_layout` accepts
only published-table-shaped input. Existing staging-first binding lookup cannot
be supplied through that facade. Its recommended lookup-input seam needs an
architecture/public-API proposal and user approval before implementation; no
temporary compilation world or weakened ABI guard is authorized. Reuse the
module and cache repros plus existing live-refusal/slot controls. The approved
realization and current reservation are recorded below.
User approved preparing the exact API proposal (“yes”);
`/root/arch_staged_layout_api` completed the docs-only
[exact API packet](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/s121-staged-value-layout-api.md): one additive
`value_layout_with_lookup` function and a new typecheck consumer edge, with
existing table APIs retained. Two documents / 43 citations and whitespace pass;
no source, baseline, schema or ABI edits. **User approved the exact additive
function and typecheck consumer edge (“ok”).** QA readiness is GO in
`tests/plan/s121-test-plan.md` §13 (57 citations, zero findings, whitespace
clean). Types completed and released: 279/279 package, focused 27/27, absent-API
RED and canonical-key fault detection, all-target check, scoped formatting and
whitespace passed. Generated baseline is exactly +1/0 against
`/tmp/cranelisp-staged-layout-types-api-before.txt`; user confirmed it (“yes”).
Seven existing clippy warnings remain in untouched files.
`/root/dev_typecheck_layout` completed and released: 860/860 package, two
consumer tests RED→GREEN, all-target check, scoped formatting/whitespace passed;
the live citation ratchet reports 481 documents / 8,431 citations with zero
findings. Existing clippy warnings remain, none in its changed files.
Independent types and typecheck reviews found no substantive issues.
`/root/dev_binary_result` completed composed verification: original module RED
turned green unchanged, then diagnostic prints became permanent assertions;
root library 758/758 and live-refusal/restart/slot controls 3/3 passed. Fresh,
restored and restored-without-authored-functions now all infer Copy, retaining
cached slots and the unchanged live ABI guard. Check/format/whitespace passed.
`/root/test_staged_layout` verified cache outputs 40, example 35 cold/warm 100,
live refusal 1/1 and generated API comparison 3/3. Its entry-restoration marker
assertion exposed a missing observation: existing trace markers cover dependency
objects, not entry metadata preload. QA narrowed §13 to one opt-in entry-metadata
preload event after successful installation, with warm presence and cold/no-cache
absence. Root added the gated event after successful installation, with library
check and whitespace passing. Final independent cache witness is 1/1 GREEN:
all three outputs are 40, warm preload is observed, cold/no-cache markers are
absent. A warm-only `--no-cache` plant retained output 40 but failed the marker
assertion; it was removed before the final run. All source/runner reservations
are released. Final binary/integration review found no issues. QA adequacy is
PASS: §13 reconciled to executed witnesses, 58 citations and whitespace pass.
All three independent reviews are clear. **User confirmed the exact generated
one-line API addition (“yes”); the staged-layout wave is complete.** No
whole-sprint or CLIF acceptance is claimed.
Arch consumer-status reconciliation is complete. Serial realization is types → typecheck
→ composed cache/live-refusal evidence → independent review/QA and generated
one-line API confirmation. No additional public delta is authorized.
Arch repaired the two 0907 citations
after verifying current teardown ownership; scoped 23 citations and whitespace
passed. Example 33 is now `33-definition-ordering.cl`; its six checks return 6
uncached, cold-cache and warm-cache. Training released its reservation.
`/root/test_staged_layout` completed the aggregate adjustment (4/4 pass,
nextest `3b00632d`) and released its reservation. All seven CLIF checks still
fail byte comparison (`8a4f45b5`); 19 candidate dumps and full diffs are retained
at `/tmp/cranelisp-s121-clif-evidence-gZ3BAD`, with no goldens edited.
`/root/design_clif_attribution` assesses those deltas read-only; QA assesses
the example repair and maintenance evidence. The integrated census is complete
and primary released the runner. Arch final status reconciliation is complete (43 citations,
zero findings).
User approved deleting the stale devloop row entirely, without replacement or
cross-reference; `/root/spec_remove_devloop_row` completed that exact deletion.
The table remains intact, removed references are absent from `repl/`, and
scoped whitespace checks pass. The global rerun finds 778 live coverage
references, zero dead/missing names; 2,456 test citations with zero malformed or
miscited entries; 8,431 repository citations with zero findings.
CLIF recapture remains held.
`/root/dev_backend_closure` completed and released the
independent B4 correction: missing-element refusal and scalar control are
green, focused 3/3 and full backend 549/549, with all-target and scoped
formatting/diff checks passing. Ten legacy Vec fixtures received concrete
type annotations; no production fallback or API change was introduced.

Permanent reproductions distinguish the completed repair from the remaining defect:

- `tests/shadowing_scope_lookup.rs::result_only_returned_closure_specializes_at_int_and_string`
  now passes across REPL/run/link with result 200; its explicitly typed closure
  control returns 100 in the same modes. This closes the narrow result-context
  reproduction; whole-wave acceptance remains subject to the gates above.
- `tests/cache.rs::cache_restored_sum_field_projection_keeps_ownership_abi`
  reduces example 35 to four forms. No-cache and cold-cache runs return 40;
  the warm-cache run incorrectly rejects its single authored definition as an
  ownership-ABI-changing replacement. Existing caches and the ABI guard are
  preserved. Binary/integration owns the next attributed repair; example 35
  is not a teaching-error repair.

QA's bounded B4 repair is complete as recorded above. The stale QA
element-lookup wording still needs reconciliation. Independent vec-len review
passed before the B4 follow-up. Five of the seven original
stale citations have been repaired mechanically; the two references in the old
0907 filing remain. QA must reconcile citations for the five migrated test
renames. Example 33 still needs its narrow training-owned correction to the
approved batch-definition rule. CLIF recapture and a fresh whole-workspace gate
remain pending. Phase 6a is still unapproved.

## Completed wave checkpoint — result-handoff disposal carrier

**Checkpoint: 2026-09-05. State: COMPLETE; INDEPENDENT REVIEW PASS.**

This standalone wave closes the gap between IO-tree teardown and values already
produced by a branch when cancellation, a fault, or detached completion prevents
normal language-level handoff. The backend derives the canonical concrete drop
glue at each result edge. Intrinsics owns a move-only produced-value guard and
disarms it only at an explicit ownership transfer.

| Edge | Private carrier | Runtime transfer |
|---|---|---|
| Bind | inner result disposer | continuation call or top-level return |
| Par | one disposer beside each branch | initialized result buffer handed to its continuation |
| Select | common branch-result disposer | winning value handed outward; losers remain guarded |
| Launch | detached result disposer | supervisor consumes the discarded completion |

The top-level `cranelisp_run_io` edge carries no disposer because its successful
result is returned to its caller. `TrampolineOutcome` separates a completed
value from cancellation/fault so the integer sentinel `0` is never mistaken for
a language value requiring disposal. This changes private backend↔intrinsics
node layouts only; IO-tree drop walking ignores the scalar disposer words.

Required exit evidence is the focused CLIF carrier set, exact intrinsics
ownership/cancellation tests, a linked owning-Bind relocation witness, full
backend and intrinsics package suites, formatting/diff checks, zero incremental
public-API baseline movement, and fresh independent review.

Implementation evidence is green: backend 546/546, intrinsics 341/341,
concurrency cancellation 14/14, the linked owning-Bind witness 1/1, both
affected packages all-target check, the seven-crate generated public-API
comparison 1/1, 70/70 scoped specification citations, targeted rustfmt, and
`git diff --check`. The cancellation target includes the held
Select→nested-Par worker, ordinary blocking-Par and poll-only controls; the
intrinsics lifecycle pair proves the clean
`Spawned → CancelRequested → WorkerExited → RootTeardown` order and detects a
planted early-release inversion. Fresh independent review found no blocking
issue. [ACT-0956](../actions/ACT-0956-blocking-select-ready-loser-disposal-evidence.md)
retains its advisory request for an additional channel-held Select-loser
disposal witness without holding this wave open.

## Prior active checkpoint — root macro publication correction

**Checkpoint: 2026-09-04. State: SPEC/ARCHITECTURE HOLD; ROOT CORRECTION
PARTIAL.**
The consolidated W3/C3/W4 typecheck stream is complete and released
to root integration. Root integration exposed that Sprint 117's unpublished
`PreparedMacroTurn` world conflicts with the language's source-ordered macro
availability rule. The approved correction makes each complete `defmacro`
closure an immediate module-local publication checkpoint, retains successful
dependency publications, and carries only source continuation across a gap.
There is no cross-module atomic publication set and no temporary executable
candidate world.
This is a historical checkpoint. The active integrated-closure checkpoint above
is the resume authority after context compaction, agent turnover or a stopped
session; the conversation is not the status source.

### Decision controls

- Agents may perform only mechanically equivalent migrations without a cited
  authority. A public-API, architecture, specification, or behavior gap stops
  its stream and returns to the user.
- Tests are evidence, not a green target. No test or assertion may be deleted,
  weakened, inverted, or rewritten to match implementation unless the changed
  behavior is traced to an already-approved rule. Success-only replacement is
  insufficient when candidate identity/cardinality is the obligation.
- Forbidden bridges include dropping payloads, first-wins selection, warning
  suppression, compatibility shims, scans replacing keyed lookup, duplicate
  state, and temporary public mutation escapes.
- Agent completion is not stream acceptance. Root reviews every stream diff;
  a fresh-context reviewer inspects semantic changes, tests, fallbacks, and
  public API before the wave can close.
- Specification changes and every inter-crate public-API change require the
  user's explicit review. Ambiguous or contradictory authority is escalated.

### Phase-5 closure replan — declaration families first

The one-binding family decision is a new architectural wave, not a local macro
namespace patch. It runs before the remaining redefinition implementation so
types, typecheck, backend and Binary/int are not repaired against generated
child bindings and then revisited:

1. `arch` completes the consumer census and presents the exact public API and
   cache-shape packet to the user;
2. after explicit approval, `cranelisp-types` realizes the aggregate records
   and typed arm identity once;
3. typecheck migrates overload selection/publication, then backend and
   Binary/int consume that carrier for codegen, macro checkpoints, cache and
   REPL presentation;
4. redefinition validation is completed against the final aggregate form,
   including whole-family and whole-macro atomicity; and
5. independent review, QA re-judgment, public-API confirmation and the fresh
   integrated gate close the sprint.

The residual-closure and `when`/`unless` specification decisions are already
settled. The macro-clause namespace rule remains uncommitted until this wave
fixes the representation: the specification will state only that `defmacro`
creates one language binding and will not prescribe internal clause storage.

### Stream ledger

| Stream | Durable evidence | State / next action |
|---|---|---|
| `cranelisp-types` representation | absent-key `ChangeAbi` semantics pass 267/267, zero API/schema delta and independent review | QA released to root; macro-specific exact same-parent authorization remains root-owned |
| `cranelisp-typecheck` consolidated stream | internal exact-staging `MacroClause` origin and non-value projection pass 870/870, zero API delta and independent finding-scoped review | QA released to root; BF-2 and QR-3 remain unexecuted until root compiles |
| backend | lifecycle-native fixtures compile; typed `MacroClause` guards 2/2; full suite 540/540 after B5's tag-dispatched platform-return stamp and runtime-owned `drop<IO T>` lowering | B5 source-complete; no backend Rust API, cache schema or GOT-layout change; held with W5 for integrated review/evidence |
| primitives | all-target check green; nextest 98/98 | green locally; public `vec` module preserved |
| frontend | all-target check green; nextest 432/432 | green locally |
| platform | ABI 10, `Pure` sentinel, marker binding, facade wash and shared heap fixture source-complete; all-target/fixture checks green; nextest 82/82; misspelled marker and stale-ABI controls both detect; canonical baseline adds exactly two approved lines and the seven-crate guard passes 3/3 | P0–P3 implementation/public API approved and baselined 2026-09-05; complete independent review and coordinated W5 evidence |
| intrinsics W5 braid | I0a catalog/dispatcher source-complete; catalog 37→38; unknown IO/Sexp tags now use the user-approved gated policy: no guessed field discharge plus outer deallocation ordinarily, hard fail under `CRANELISP_RC_DEC_CHECK`, no unconditional debug assertion | implement and verify I1's closed Sexp walk, then resume I0b under the approved Pure claim/discharge design |
| root integration | all-target check green; workspace library units 3341/3341; S76 13/13. The truthful candidate gate and fallible bootstrap are realized. The declaration-family migration also restores display-only `None`/`[]` without codegen, canonical trait-method self-documentation, declared cached children and strict writer-record impl enrolment; cache + REPL introspection are 225/225 and the non-runtime owner seam is 5/5. Ordered multi-definition results and macro transformation-signature presentation pass the combined REPL/macro/stdlib acceptance gate 308/308. After the declaration-family API baselines were approved and regenerated, the fresh complete gate ran 5,740 tests: 5,716 passed, 24 failed and 1 skipped. The remaining failures are held CLIF goldens (7), superseded cascade/redefinition evidence (5), the one 0907 `Bind` defect including its two aggregate reporters (7), shadowing (2), vec-query (2), and one stale spec-03 assertion. | do not recapture CLIF while product failures remain; execute 0907 through its already-ruled C5/C7/C4 retained-reservation braid and preserve the public-API/ABI gates |
| `/search` interim macro boundary | `repl/spec.md` §17.19 excludes macro declarations from every feed; `tests/search.rs::search_ignores_macro_declaration_but_keeps_ordinary_definition_neg`; search suite 42/42 | source/live/cache projections omit macro rows; unloaded-source indexing does not execute macros; future full semantic indexing is isolated in ACT-0952 |
| traceability maintenance | split-spec checker detection proofs 2/2 and 4/4; forward scan 2,431/2,444 valid with 13 free-form skips; reverse scan 772 live, zero dead/missing/cleared; citation ratchet zero findings | closed; two obsolete rejection tests are intentionally absent from restored coverage; the fresh 5,740-test census confirms the prior citation-drift RED is gone |
| HM candidate selection | exact internal design approved 2026-09-02; QA delta in `tests/plan/s121-test-plan.md` §3.7 is GO; existing e2e cases strengthened | complete through the shared progress-aware settlement driver and retain separately attributable CS-1–CS-11 evidence |
| public API baseline | Every previously approved baseline plus the declaration-family types +177/-85 and backend +3/-47 deltas | all seven canonical comparisons pass; declaration-family generated results and the one backend amendment were confirmed 2026-09-05 |
| Packet-A accessor replacement | exact approved methods implemented; types check/rustdoc/fmt/diff green; nextest 250/250; no Packet-A warning; canonical regeneration adds exactly two incremental lines | generated baseline confirmed 2026-09-03; types source reservation released |
| independent review / integrated QA | backend PASS after two evidence repairs; root/int review FAIL; bootstrap error propagation and truthful closure-gate findings are realized and locally green | QA HOLD; the receipt requirement is superseded, and QA must reallocate the affected cascade evidence after the exact redefinition rule and architecture are approved |

### Open semantic-delta audit

1. **Product/sum accessor boundary — resolved by user ruling (2026-09-02).**
   Product fields mint total canonical accessors and bare candidates. A
   differently named constructor is a sum variant even when it is the only arm;
   its payload labels mint no accessors and are extracted positionally by
   `match`. Repeated labels such as `Sexp.sval` therefore create no symbol-table
   contest. The former FIXME-0867 all-arm widening and partial-runtime-accessor
   proposal are retired. Typecheck evidence improved from 476/840 to 729/840
   immediately after restoring the product boundary; the remaining 111 REDs are
   Packet-B resolution/lifecycle work, not accessor-synthesis authority.
2. **Explicit `deftype` declarations — resolved by user ruling (2026-09-02).**
   A bare type head is monomorphic; a parenthesized head declares the complete
   parameter list; every product field and sum payload is `:Type name`.
   Frontend rejects missing types and undeclared variables at the field span
   before emitting entries. Active generic fixtures now state their parameters
   explicitly. Frontend is 432/432; typecheck remains 729/840, so the migration
   added no Packet-B regression. FIXME 0912 is retired.
3. **Canonical replacement — exact Packet-A public proposal at user gate.**
   Same-type product redefinition cannot retire `Box.v` while the bare `v`
   candidate references it. A1 `publish_staged` is integration-only and
   `retire_abi_changing` would create a dangling candidate plus an invalid
   staging tombstone. Architecture therefore proposes two types-owned atomic
   transitions—template and concrete—whose exact signatures are recorded in
   [S121 lifecycle record](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md). They preserve the candidate vector,
   refuse non-unpublished owners without mutation and leave published-retirement
   policy to A1. The exact methods were user-approved 2026-09-02; their
   generated two-line types baseline remains a separate confirmation gate.
4. **Acceptance strength — review HOLD.** Exact identity/cardinality remains
   missing for export, prelude and both mode-parity arms. Use-site evidence must
   cover syntactic filtering, isolated HM selection, fixed-point ambiguity,
   constructor scrutinee selection, complete canonical diagnostics and selected
   identity writeback.
5. **Authority reconciliation.** Retired def-over-import/prelude rejection and
   accessor warn/suppress comments must be compared with the approved spec and
   corrected only where that authority is explicit; disagreement returns to
   the user.
6. **Checked-body settlement carrier — resolved by user ruling (2026-09-03).** The
   delayed-publication experiment was fully backed out after proving that
   pre-finalization postpasses currently read AST and callees from the symbol
   table. Preserving strict codegen-view construction after all drains requires
   an explicit private checked-body carrier and redirected readers; no
   placeholder lifecycle or optional view is authorized. The exact private
   body-occurrence ledger proposal is recorded in
   `design/typecheck/checked-body-publication.md` §§1–8 and was user-approved
   2026-09-03. The same approval now includes the five-item private-state
   cleanup in §11: fold signature/scope/callee ownership into the ledger, use
   one body frame, carry resolutions whole, remove only the per-form expression
   map, and delete the unread slot stash. Dispatch-queue grouping, a general
   recheck sandbox, wholesale `CheckState` decomposition and every public or
   normative change remain excluded.
7. **Duplicate same-name body ownership — architecture decision required.** A
   self-qualified duplicate definition reaches `update_declared_scheme` after
   the first body has settled the shared binding. The stream must not invent a
   last-declaration or per-form ownership rule. The normative spec does not
   decide separate same-name forms within one uncommitted cluster; the three
   exact choices are held in `design/typecheck/checked-body-publication.md` §9
   for user arbitration. User ruling 2026-09-03 selects rejection: a second
   separate same-canonical-name `defn` in one compilation cluster is an illegal
   redefinition attempt, neither replacement nor augmentation. The rule is now
   normative in `spec/05-definitions.md` §5.13 with the category cross-reference
   in `spec/08-modules.md` §8.6.4; affected coverage is invalidated for QA.
8. **Existing spec contradiction — user gate.** `spec/08-modules.md` §8.10.4
   says definitions compile sequentially to completion, while §§3.5.2, 5.13
   and 9.12 require register-all then check-all for non-macro clusters. The
   scribe did not repair this separate unapproved hunk. Proposed correction:
   macro definitions/uses retain source order; after expansion, non-macro
   definitions form one register-all/check-all cluster.

### Exact resume action

Architecture and int-design reconciliation of the approved immediate macro
checkpoint and explicit absent-replacement `ChangeAbi` semantics is **complete**
(`design/arch/macro-availability-model.md` §§0.4/0.5/0.7,
`design/arch/bounded-contexts.md` §1.8/§2/§6/§11,
`design/arch/interfaces.md` §`check_forms`,
`design/int/macro-turn-ownership.md` §9, `design/int/s121-c6-visit.md` §7/§13.1;
all verified at the 2026-09-03 handover). The approved §9.12.1 clarification is
applied and QA allocated MC-1–MC-13. The first root realization failed
independent review: successful macro redefinition outcomes were discarded
before §18 cure, deterministic safety fences were incomplete, bootstrap used
`unreachable!` on lifecycle refusals, and the retained binding-shaped closure
gate was a documented no-op. QA therefore holds the wave.

The candidate-exposure predicate is now the one truthful closure gate, and
bootstrap propagates lifecycle refusal through the approved fallible
`CompilerSession::new(...) -> Result<CompilerSession, CranelispError>` surface.
Those source changes and their focused evidence are complete. The proposed
publication receipt is no longer resume authority. The user's 2026-09-04
redefinition ruling removes post-publication caller recompilation: a
same-language-type body replacement patches its existing slot; a
language-type-changing replacement may publish only when the existing
definition has no callers, and otherwise fails before publication while the
old definition remains live. No receipt or recursive cascade is implemented
from the superseded branch.

The mechanical `repl/spec/` split is complete: every moved normative body is
byte-identical after reversing only relative-link adjustments, and the largest
section file is 559 body lines instead of a 4,394-line monolith. Before source
work, return the exact §18 semantic delta to the user. Specification must settle
the caller boundary and affected declaration classes, and architecture must
settle any hidden ownership-mode ABI effect without making a same-language-type
replacement unpredictably illegal. The unapproved FIFO/nested-recheck text in
[S121 lifecycle-public-api-review record](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/s121-lifecycle-public-api-review.md) is not authoritative and must
be reconciled by `arch`. In the same structural wave, QA must teach its link and
coverage checkers to resolve `repl/spec/` and preserve old `repl/spec.md §N`
citations through the compatibility entry point; this avoids a 2,285-occurrence
cross-repository rewrite. QA then reallocates the obsolete cascade/receipt
evidence, followed by the remaining root realization, independent review and
integrated QA. The seven live line-number citations to the old monolith are
separately assigned to their current owners. The separate §8.10.4 spec
reconciliation remains pending.
`/search` creates no exception to the macro publication invariant: Sprint 121
omits macro declarations from every feed and does not execute them in the
unloaded-source pass. ACT-0952 retains the viable future normal-compiler path
as a separately specified, architected and user-gated expansion.

## Settling target

At acceptance, a fresh workspace produces an attributable gate result: no
repository/session contamination, no stale coverage record, no unowned RED,
and no filing whose status contradicts its live source or permanent repro.
Every inherited product defect is either green or an explicit user-accepted
residual supported by evidence that decomposition cannot bring it into this
increment. Historical age or sprint size is not a deferral reason.

## Scope

### Included

1. **Re-establish the baseline from live evidence.** Start from the Phase-1
   5,700-test census, classify every RED against its permanent repro and filing,
   and keep root-cause counts separate from failing-test counts. Resolve the
   ignored `user.cl` persistence contamination in the examples root and
   identify how it entered a
   product surface before re-running the census.
2. **Drain filings through the work that owns them.** Route all 84 legacy
   FIXMEs, both open actions and the prior audit recommendations to exactly one
   delivery stream before realization. A stream verifies each assigned record
   against source when that solution area opens, then carries the surviving
   obligation through authority, evidence, implementation, review and filing
   closure while that context is resident. There is no separate backlog-cleanup
   sweep before or after the product work. The eight records currently marked
   deferred receive fresh trigger and deferral-count review in their assigned
   stream; none is presumed deferred in this sprint.
3. **Retire the established RED set.** Work the 18 attributed failures as
   root-cause families rather than independent patches: cache restoration
   (0868/0869), IO constructor/drop-glue modelling (0907), the ruled
   product/sum accessor boundary (0867 retired), `def` presentation (0800/0863), method-only-import and
   launched-grid load dependence (0694), residual result ownership (0913),
   scalar-as-pointer trait codegen (0916), and the scoped post-0917 Sudoku CLIF
   observation. Verify each family against the live source before retaining
   that attribution.
4. **Make quality part of each surface exit.** Each delivery stream owns the
   formatting, compilation, warning, test→spec anchor, coverage, citation and
   filing consequences of its own changes. The delivery-infrastructure stream
   repairs only genuinely shared instruments; the final integrated gate
   observes the resulting tree and is not a scheduled cleanup pass. QA
   classifies each check as acceptance evidence, a safety fence, a diagnostic
   observer or a maintenance check before Phase 4; `test` implements only the
   least-cost executing gate needed for the classified residual risk, with a
   detection proof for every new instrument.
5. **Dispose the Sprint 120 assessment.** Append the user-approved disposition
   to `audits/shared-role-integration-s120.md`. R-1, R-2 and R-5 are closure
   candidates requiring clause-by-clause confirmation. R-3, R-6, R-7 and R-8
   are partially resolved; R-4 remains open. They join the
   delivery-infrastructure stream: owner declarations, missing refusal and
   SIGTERM evidence, dispatch
   session provenance, generated adapter policy, and retired vocabulary/anchor
   cleanup are work, not presumed resolution.
6. **Restore whole-project visibility.** Run the overdue read-only `src/`
   whole-context audit in the Phase 6/7 window and complete the standing
   docs/training/stdlib/exemplar/REPL assessment against the final compiler, not
   merely the implementation delta. Phase 6 consumes the settled stream
   outcomes in one user-facing pass; it does not repeat compiler diagnosis or
   reopen a compiler surface unless that assessment discovers a new product
   defect.

### Current evidence, not yet acceptance

- `cargo nextest run --no-fail-fast`: **5,681 passed / 19 failed / 1 skipped**
  in 199.6 s. Eighteen failures collapse to the established carried set; the
  nineteenth is the unattributed examples-root `user.cl` file-set failure.
- `cargo check --workspace --all-targets`: green, with Cargo's upstream
  `nix 0.28.0` future-incompatibility notice.
- `cargo clippy --workspace --all-targets`: exit 0 but warning-positive; this
  does not meet the repository's zero-warning per-surface handoff rule.
- `cargo fmt --all -- --check`: red on existing Rust source.
- `tests/plan/spec_link_check.py`: 38 mis-cited anchors and 25 malformed
  citations.
- `tests/plan/spec_coverage_reconcile.py`: zero dead test names, but eight
  Sprint-115 coverage rows remain cleared and await QA re-judgment.
- Role wiring: 12 roles, 4 first-read roles, 24 host adapters, 12 allocation
  pairs, 2 composed skills and 26 principles; zero findings.
- Live citation drift: 466 documents / 8,122 citations; zero findings against
  the ratchet. `git diff --check` and `cargo check` are green.

### External operations and exclusions

- No commit, push, publication, dependency update, deployment or remote write
  is authorized by this scope.
- No language semantic change is implied. Any normative question returns to the
  user through `spec`. Every change to public API between crates requires
  `arch` to present the exact proposed delta for explicit user approval before
  implementation; the generated baseline diff returns to the user before the
  wave passes. General phase or wave approval is not API approval.
- `NOTES.md` is user-owned and is not modified or removed under ACT-0947 without
  separate explicit approval. Other candidate root clutter is inspected before
  any removal; Phase 5 approval will name exact destructive targets, if any.
- Existing generated CLIF is never recaptured merely to make a gate green. A
  changed frame requires scoped attribution and an approved re-baseline.
- The `nix 0.28.0` upstream future-incompatibility notice is reported separately
  from repository-authored warnings; changing dependency versions is outside
  scope unless the user later approves it.

## Evidence authority

| Condition or instrument | Class | Governing authority | Result / state |
|---|---|---|---|
| Every compiler RED traces to an open owned defect; no extra RED | safety fence | root `CLAUDE.md` §Testing | red: one unattributed workspace-contamination failure |
| Affected language and compiler behavior | acceptance | `spec/`, `repl/spec.md`, approved design | 18 attributed REDs pending source re-verification |
| Examples, docs, stdlib, exemplar and REPL remain usable | acceptance | user-facing role contracts and specifications | pending Phase 6 assessment |
| Full default suite | acceptance plus carried-defect observer | root `CLAUDE.md` §Testing | 5,681/19/1 baseline |
| Formatting, build and per-surface clippy | maintenance | `sprints/METHOD.md` §2.3 | fmt red; build green; clippy warning-positive |
| Test→spec links and cleared coverage rows | maintenance with traceability safety impact | root `CLAUDE.md` §Requirements/Test Traceability | red: 63 link findings; 8 cleared rows |
| Role wiring and live citation drift | maintenance | root `CLAUDE.md` §Assurance | green |
| CLIF golden lane | diagnostic observer until QA reclassifies the final attributed frame | backend design and scoped attribution record | one known `f4_sudoku` drift |
| `src/` whole-context audit | diagnostic observer | `sprints/METHOD.md` §2.7 | overdue; proposed this sprint |

## FIXME debt

All 84 records are included for source-first disposition. `open` and `deferred`
below describe the inherited file status, not a Sprint-121 decision.

| Target | Inherited status | FIXME numbers |
|---|---|---|
| `arch` | open | 0762, 0776, 0783, 0789, 0821, 0823, 0938, 0939, 0940, 0941, 0942, 0943 |
| `design` | open | 0637, 0740, 0745, 0747, 0777, 0793, 0795, 0871, 0873, 0903, 0907, 0913, 0915, 0916, 0917, 0921, 0924, 0927, 0928, 0929, 0931, 0932, 0933, 0934, 0935 |
| `dev` | open | 0604, 0765, 0782, 0835, 0848, 0868, 0869, 0870, 0874, 0889, 0898, 0906, 0914, 0937 |
| `examples` | open | 0463 |
| `qa` | open | 0694, 0761, 0766, 0771, 0779, 0781, 0785, 0794, 0801, 0811, 0815, 0818, 0841, 0857, 0936, 0944 |
| `review` | open | 0764 |
| `spec` | open | 0708, 0912 |
| `stdlib` | open | 0780, 0800 |
| `test` (legacy target `/testing`) | open | 0900, 0945 |
| mixed legacy targets | deferred | 0050, 0052, 0553, 0798, 0799, 0859, 0863, 0891 |

Open actions ACT-0947 (root-file disposition) and ACT-0950 (doc→doc citation
roots) are included; neither is presumed resolved. ACT-0951 was filed from the
Phase-3 specification gate and is a required future carrier, not current
implementation scope: `/learn` cannot return to a delivery sprint until its
complete feature contract has been user-ruled and recorded.

## Delivery streams (scope topology; not yet Phase-4 waves)

A stream is a crate-shaped writable surface, matching `sprints/METHOD.md`
§§1.1 and 2.1. Cross-crate concerns are dependency spines connecting those
streams; they are not competing thematic streams that reopen the same crate.
Phase 2 may correct a primary allocation or boundary, and Phase 4 turns the
approved streams into waves.

The FIXME list below is a **primary closure allocation**: each legacy record has
one stream responsible for verifying and ultimately disposing it. A filing may
still supply obligations to other streams. Those obligations travel through the
dependency spines and are designed into the receiving crate's single visit.

| Order | Stream and reserved surface | Primary legacy allocations |
|---|---|---|
| G0 | **Delivery control and ledgers** — host wiring, shared verifiers, `sprints/`, `audits/` and common evidence records; no product behavior | 0764, 0765, 0766, 0771, 0783, 0857, 0938, 0939, 0940, 0941, 0942, 0943, 0944, 0945; ACT-0947, ACT-0950; audit R-1…R-8 |
| C1 | **`cranelisp-types` foundation** — cross-crate types, callable/constructor state, cache-visible carriers and their public facade | 0637, 0931 |
| C2 | **`cranelisp-frontend`** — quote recognition, module extraction and the landed annotation representation's remaining frontend records | 0785, 0789, 0801, 0937; 0912 retired by the explicit-field ruling |
| C3 | **`cranelisp-typecheck`** — resolution, traits, ownership inference, monomorphisation, product-accessor/constructor instances and concrete codegen views | 0553, 0762, 0776, 0777, 0779, 0794, 0799, 0913, 0916, 0924, 0929, 0935, 0936; 0867 retired by the product/sum ruling |
| C4 | **`cranelisp-backend`** — lowering, RC/category decisions, drop glue, result-root production and codegen diagnostics | 0747, 0761, 0781, 0782, 0811, 0891, 0900, 0903, 0906, 0907, 0915, 0917 |
| C5 | **runtime pair** — `cranelisp-intrinsics` + `cranelisp-primitives`, including ABI handle vocabulary, marshaling, runtime teardown and primitive realization | 0835, 0848, 0859, 0928, 0932, 0934 |
| C6 | **binary and executable bundle** — `src/` + `cranelisp-exe-bundle`: bootstrap, pipeline, session, reload/cache orchestration, result ownership and REPL implementation | 0050, 0052, 0604, 0694, 0708, 0740, 0745, 0793, 0795, 0798, 0800, 0818, 0863, 0868, 0869, 0889, 0898, 0914, 0921, 0927, 0933 |
| C7 | **`cranelisp-platform` and platform fixtures** — published platform facade, schema, marker binding and shared-heap consumer evidence | 0463, 0870, 0871, 0873, 0874 |
| U8 | **language-facing surfaces** — `stdlib/`, `examples/`, `exemplar/`, `repl/` records and `user/`, changed once after the compiler settles | 0780, 0815, 0821, 0823, 0841 |

All 84 FIXME numbers occur exactly once as primary allocations after the Phase-2
moves 0857 C5→G0, 0708 C2→C6, 0798 C3→C6 and 0889 C5→C6. Primary closure does
not erase contributing arms: Phase 3 returned 0798's single typecheck caller to
C3 and 0869's carrier producer to C3, while C6 still owns both filings' final
disposition. This does not pretend that 84 old files are 84 implementation
units: multi-root records such as 0694 and 0766 supply named handoff obligations,
and Phase 3 combines every obligation reaching one crate into one stream design.

FIXME 0052 remains allocated to C6 for source-verified disposition only. The
user accepted it as a residual during Phase 3 after the specification gap was
exposed; ACT-0951 carries the required future specification package. It causes
no C6 implementation or U8 curriculum touch in Sprint 121.

Source verification found 16 records whose central claim is already resolved
or superseded: 0637, 0708, 0745, 0761, 0762, 0781, 0782, 0785, 0794, 0801,
0821, 0835, 0848, 0891, 0917 and 0944. Eleven are clean disposition candidates;
0708, 0761, 0781, 0794 and 0944 retain a documentary, evidence or downstream
tail in their allocated stream or a named handoff. They size as verification
and retirement work, not as implementation packages. All other records remain
live, partial, trigger-gated or user-gated; the inherited `open` label is not
used as evidence that work remains.

### Dependency spines

The spines preserve established cross-crate direction while crate streams
prevent repeat visits.

| Spine | Governing outcome | Ordered stream handoff |
|---|---|---|
| P1 — total concreteness | Complete one user-approved symbol-lifecycle migration and make every backend frame concrete or refused before codegen; absorb 0924, 0931–0936, 0913 and producer-gated 0916 rather than fixing their symptoms separately; retain the product-only boundary that retired 0867 | C1 → C3 → C4 → C5 → C6 → G0 evidence |
| P2 — ownership and IO release | Converge category-before-operation, result-root identity, IO runtime teardown, payload glue, typed handles and host discharge without a second release mechanism | C3 → C4 → C5 → C6 → U8 acceptance |
| P3 — module/cache/session consistency | Make fresh, cached, reloaded and concurrent publication paths agree for children, trait impls, aliases and mono instances; use one scoped alias mint/walk and a transactional record↔shell trait-impl carrier | G0 opening experiment → C1 scoped alias facade → C3 caller + carrier producer → C6 restore seams → G0 evidence |
| P4 — annotation tail and macro checkpoints | Retire the landed annotation representation's `src/` mirrors, then replace the unpublished prepared-macro world with source-ordered immediate macro checkpoints and carry their language-facing consequences once | C1 transaction amendment → C3/C4 guards → C6 → U8 |
| P5 — platform consumer | Apply the tag-licensed runtime crossing and manifest contracts once at the public platform edge, keeping capability names as platform data rather than language vocabulary | C4 return stamp → C7 ABI/facade/fixtures → C5/C6 consumers → U8 |

FIXME 0050 remains trigger-gated on a display protocol and is not bundled into
the 0800/0863 correction. FIXME 0052's scheduling trigger is live, but the
feature has no complete live specification; the user therefore deferred it to
ACT-0951 rather than allow C6 to guess its behavior.

### Coherent work inside each stream

| Stream | Work designed together | Exit to the next stream |
|---|---|---|
| G0 | **Open:** normalize the pre-existing format drift before any source reservation; reconcile 0945's conflicting public-API commands and tool pin; run the 0694 D1 attribution experiment; identify the examples-root `user.cl` contamination. **Close:** converge ledgers, audit/actions and principles once. Principle authoring 0764/0765 and 0938–0943 is close-only because `principles.md` permits revision only at sprint close. | Sound instruments and collision-free source before C1; one truthful ledger after U8. |
| C1 | Apply the user-selected symbol-lifecycle target once. Add the one `<owner>.<name>` module-alias mint and referring-module-scoped walk, enumerate every public carrier delta and use one schema window, including the coordinated backend `CACHE_SCHEMA_VERSION` edit; verify and retire 0637. | One settled types API, alias facade and cache contract; compilation enumerates the downstream wash. |
| C2 | Treat the annotation flip as landed. Retire 0785/0801, repair the frontend current-state wash, settle 0789's predicate home and update the one live module-extraction record. | One quote predicate and truthful frontend surface; no parser redesign enters C3. |
| C3 | Consume C1/C2 once; combine trait/product-accessor/constructor minting, carrier identity, residual-type and mono-entry obligations. Retain the product/sum negative boundary while landing product A-MINT with 0924; adapt the one scoped-alias caller in CS-1; populate `WrittenTraitImpl` transactionally in CS-6 with record↔shell bijection and `(type, trait)` upsert identity; then hand the census and producer facts to C4/C6. Do not locally repair 0935. | Concrete, canonically named codegen inputs, a real cache carrier and zero census; typecheck surface gate green. |
| C4 | Consume the zero census once; combine release staging, constructor/nullary work, IO calls, result roots and diagnostics. Execute 0916 only after its C3 producer gate; add the dormant `vec-len` value arm in B8; and make the platform-return stamp tag-licensed in B5—Effect metadata at 40, Pure glue at 32, other tags no write. Remove 0898's backend twin and retire resolved C4 filings in the same visit. | Backend lowering and focused CLIF settled; one IO-node layout/crossing contract handed to C7 then C5. |
| C5 | Consume C4's call/ABI needs once; combine the typed consume funnel, `consume_sexp`'s missing annotated-node arm, runtime teardown, mandatory `vec-len` Inline realization and IO payload glue. C4 B8 precedes the declaration flip; C7's widened ABI precedes runtime teardown that reads the new field. Retire the already-landed 0835/0848 work instead of rebuilding it. | One runtime ABI/facade and ownership-fact set for C6; no backend revisit from either runtime crate. |
| C6 | Consume all compiler/runtime facades once; combine the complete annotation-mirror retirement (including the `src/pretty.rs` wrong-accept tail), types-owned scoped alias keying, bootstrap/publication/cache/reload, result release, platform-manifest mint and source-ordered macro checkpoints. Delete the unpublished macro candidate world; gaps retain source continuation only. N3 opens only after C1's alias facade and C3 CS-6. Record 0052's accepted residual without touching `/learn` product code. | Fresh/warm/reload/REPL behavior settled; binary and executable-bundle surface gates green. |
| C7 | Reconcile the platform facade once, bump `ABI_VERSION` 9→10, bind markers, wash the facade and rebuild the shared fixtures in one change-set. Keep DLL Pure glue as a zero sentinel for C4 adoption stamping. FIXME 0463 is evidence/retirement only: capability names remain manifest data and future platform authors use the generic poll/resource/declaration mechanism. Reserve only `exemplar/platforms/web/`; U8 owns the rest of `exemplar/`. | Public platform surface and consumer fixtures green without narrowing the platform-author interface. |
| U8 | Apply accumulated stdlib, examples, exemplar, REPL-record, documentation and training consequences once. Re-test 0815 before retaining its now-stale attribution; enact the already-approved 0823 examples-library ruling and retire 0821. | User-proxy acceptance ready; no compiler diagnosis repeated. |

### No-refix rule

Before Phase 4 approval:

1. Phase 2 verifies every filing against current source and records whether it
   is resolved, superseded, live or trigger-unmet before approving its primary
   allocation.
2. Phase 3 produces one design and QA evidence delta per crate stream, covering
   every dependency spine entering that crate. A later spine may not redesign a
   path already released by the stream.
3. The wave plan reserves every writable implementation submodule and standing
   document to one stream. If two proposed streams need the same path, their
   work is merged into the owning crate stream or one becomes a handoff input.
4. A stream does not implement a local symptom when an approved upstream
   structural change will rewrite that seam. The source-backed migration plan,
   not FIXME age or target label, determines order.
5. Shared indexes and ledgers receive one nominated convergence edit. A legacy
   filing with several roots may wait on several streams, but it does not cause
   those streams to edit the filing independently.

### One-touch stream exit

A stream opens its assigned filings with the owning roles and does not release
its reserved area until one coherent bundle contains:

1. source-verified filing dispositions and any required user/spec/architecture
   decision;
2. one settled QA evidence delta, with obsolete tests or controls removed;
3. implementation and module evidence for the reserved source area;
4. one independent review of the cohesive change-set, with at most the
   finding-scoped correction loop allowed by the sprint contract;
5. synchronized design/current-state records, traceability, citations and
   filing deletion or explicit approved residual; and
6. the surface-local format, build, test and zero-warning-for-surface gate.

The final integrated gate runs once from a fresh acceptance arrangement after
U8. It includes the full suite, workspace build/lint/format, traceability,
citations, role wiring, public-API parity, repository cleanliness and the
Phase-6 user-facing pass. It is an observer of completed streams, not a basket
of work deliberately postponed from them; an unexpected failure reopens only
the stream that owns its root cause.

### Phase-4 efficiency controls

Phase 4 adopts the Phase-3 coordination lessons as delivery constraints:

1. Freeze the Phase-3 specification, architecture, design and QA package unless
   executing evidence falsifies a material fact. Local implementation detail
   does not trigger another design cycle.
2. Keep one named Codex owner for each crate stream. A retained W5 reservation
   pauses and resumes with that same owner; it is not released and
   re-dispatched between braid steps.
3. Close filing status, traceability, citations, format, warnings and local
   evidence once at the owning stream's exit. Do not visit a crate again for a
   separate administrative sweep.
4. Execute W5 from its one ordered checklist and record one coordinated gate;
   do not create independent per-filing schedules inside the braid.
5. Track source-stream reopen count as an efficiency measure. The target is
   **zero**; only executing evidence that falsifies the released stream's
   outcome may increment it, and the sprint log must name the falsifier and
   affected stream.

| Efficiency measure | Current | Target |
|---|---:|---:|
| Product-source streams opened | 2 | 8 crate-shaped streams, once each |
| Released product-source streams reopened | 2 | 0 |
| Phase-3 technical packages reopened without a falsifier | 0 | 0 |

## Architecture review (Phase 2)

`arch` returned **conditional sign-off**. It ratified the nine crate-shaped
streams, exact-once allocation, P1/P2/P3/P5 direction, the 18-RED family
attribution and the prior audit's R-1…R-8 classification. It corrected the four
allocations recorded above and replaced P4 because the annotation flip already
landed. Its conditions are now part of the plan:

1. re-size the streams from the 16 resolved/superseded central claims rather
   than inherited filing labels;
2. settle the user-owned decisions below before per-stream design;
3. give C1 one explicit public-carrier and cache-schema window;
4. run G0's format normalization and public-API-procedure repair before source
   streams reserve overlapping paths;
5. keep principle authoring in G0-close; and
6. require METHOD's zero-warning-for-surface gate, not the weaker
   zero-new-warning wording.

The plan incorporates all six conditions. The user approved the proposed
decision package on 2026-09-01 after separately refining 0463, so Phase 2 is
complete and no architecture or scope decision remains implicit.

### Phase-2 user decision gate

| Decision | Architecture evidence and consequence | Decision state and disposition |
|---|---|---|
| C1 lifecycle target | [S121 lifecycle record](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/symbol-table-lifecycle.md) §9 finds that the dormant `CallableSlot`/`CtorState` flip is a strict waypoint to a unified lifecycle machine. Landing both means two exhaustive washes over roughly 200 sites; the unified target is estimated at 1.5–2× one scoped wash but visits the sites once. | **Partially approved, clarified 2026-09-02** — the `Binding -> Decl -> Callable -> Life` representation and table-owned transition enforcement are accepted. The exact mutation facade and every public API line remain held for review. |
| 0912 undeclared `deftype` fields | The earlier inferred-parameter proposal was rejected on user review. Implicit field typing leaves declaration intent under-specified and creates downstream free-variable states. | **Superseded by user 2026-09-02** — a bare head is monomorphic, a parenthesized head states the complete parameter list, and every field has a written type. Missing types and undeclared variables are located frontend errors. |
| 0052 `/learn` | Its scheduling trigger is met, but the live repository has no complete feature contract. The retired Sprint-0 plan is provenance, not authority; implementation would have to invent routing, triggers, state and persistence. | **Phase-2 inclusion superseded by user 2026-09-01** — defer the feature, remove the provisional spec, and require ACT-0951's complete user-ruled specification before a future implementation sprint. |
| 0050 display protocol | The trigger remains unmet: no display protocol or type-directed pretty-printer exists. Pulling it in would create a new architecture feature solely to unblock its prose. | **Approved 2026-09-01** — defer with the verified trigger and do not couple it to 0800/0863. |
| 0553 instantiate-at-types | Its natural types/typecheck/backend/src seams all open in this sprint; omitting it now schedules another visit to the same monomorphisation/reload surfaces. | **Approved 2026-09-01** — include the narrow set-instantiation entry point and retire source-form replay in the same stream sequence. |
| 0859 projection evidence | The existing survey found no production RC distinction after materialisation. A new observer would manufacture a costly seam with no current consumer. | **Approved 2026-09-01** — accept the existing evidence with the filed revival trigger when projection provenance becomes emission-live. |
| 0463 network-leaf lesson | Example 34 already teaches the language-owned poll mechanism. The current public facade exposes generic `PollFn`, readable/writable reactor registration, resource roles and `declare_platform!` (`crates/cranelisp-platform/src/concurrency.rs`, `crates/cranelisp-platform/src/declare.rs`); `exemplar/platforms/web/src/lib.rs` implements `accept`/`read`/`send` through that facade without an extension. What remains is an optional platform-authored socket library, client driver and network-specific lesson. | **Approved 2026-09-01** — defer the narrowed network lesson. It must not change the platform interface: future platform developers define socket operations using the existing mechanism. Reconsider only when a reusable network platform or deterministic server-driving lesson is independently scheduled. |
| 0934 IO payload glue | The face-4 residual becomes actionable after P1/C4. Including it stamps the existing canonical `drop<T>` at construction, changes the runtime/platform ABI and closes the nested-`Pure` leak; excluding it leaves an explicit release residual. | **Approved 2026-09-01** — include it, with Phase 3 choosing the narrow sound node layout and C7 owning the ABI bump and fixtures. |
| 0789 quote predicates | The structural predicate belongs with the `Sexp` datum; placing it in frontend avoids one types baseline delta but leaves the invariant away from its owner. | **Approved 2026-09-01** — publish the single predicate from `cranelisp-types`; frontend and `src` consume it. |

The 0823 examples-library ruling is already user-approved and is not re-opened;
U8 enacts it and retires superseded 0821. `vec-len` spelling, the exact IO-node
layout and the one schema-window membership are Phase-3 design decisions within
the approved architecture and return at the Phase-3 readiness checkpoint.

## Role plans (Phase 3)

Phase 3 entered with user approval on 2026-09-01.

**Target.** Turn the approved architecture and stream allocations into one
coherent design and QA evidence delta per crate-shaped surface, with exact
facades, schema effects, handoff values and writable-path reservations. The
result must be sufficient to organize the six-wave execution shape without a
later stream redesigning or reopening an earlier crate.

**Included role work.**

1. `spec` records 0912's user-ruled explicit parameter/field rule and settles
   the 0799 and 0841 normative residues without changing unrelated language
   behavior. It removes the provisional `/learn` text; ACT-0951 carries the
   future complete specification instead.
2. `arch` applies the approved unified symbol-lifecycle target, the
   `cranelisp-types` quote-predicate home, the single cache-schema/public-API
   window and the cross-crate IO payload-glue/ABI contract. It also settles
   0945's canonical public-API regeneration procedure before any baseline
   design depends on it.
3. Narrow `design` invocations cover `cranelisp-frontend`,
   `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-intrinsics`,
   `cranelisp-primitives`, the binary/executable-bundle surface and
   `cranelisp-platform`. The runtime pair shares one ordered stream but keeps
   one crate per design invocation.
4. `qa` produces one consolidated, risk-classified evidence plan whose deltas
   are allocated back to those streams, including the 18 RED family, resolved
   filing retirements, cache/schema and ABI boundaries, audit residuals and the
   fresh integrated acceptance arrangement.
5. `sprint` reconciles handoffs, rejects overlapping path ownership and drafts
   the six-wave organization for the Phase-3 checkpoint. It does not make role
   decisions or begin implementation.

**Operations and exclusions.** Phase 3 edits only specification, architecture,
per-crate design, QA-plan and sprint-planning artifacts. It performs read-only
source inspection and deterministic document/reference checks. It does not edit
product code or test implementations, delete filings, normalize source, run
Phase-5 implementation gates, commit, push, publish or deploy. Named `spec`,
`arch`, `design` and `qa` roles use the repository's configured external Claude
transport; their bounded briefs transmit the relevant repository source,
designs, tests/plans and filings to that provider. No remote write is made.

**Exit.** Return to the user when all approved decisions have authoritative
carriers; every stream has one design and evidence delta; public API, schema,
ABI and path collisions are settled; no normative or boundary decision remains
implicit; and the proposed six-wave plan names its ordered handoffs and exact
reservations. User approval is then required for Phase 3 → Phase 4.

### Phase-3 specification outcome

The initial 2026-09-01 proposal inferred parameters from omitted field types.
User review on 2026-09-02 superseded that proposal before implementation:

- `spec/05-definitions.md` §5.2.4 now requires explicit declarations. A bare
  head is monomorphic; a parenthesized head is the complete parameter list; and
  every field is `:Type name`.
- `(deftype Pair [first second])`, `(deftype Box [:a value])`, and `(deftype
  (Box a) [:b value])` are located frontend errors. No hidden parameter is
  inferred or appended.
- Active fixtures are migrated to explicit generic declarations so their
  original type/ownership mechanisms remain under test.
- The 0799 residue is determined by existing §3.11 authority: an outer use that
  pins the residual closure's free variable is accepted and monomorphised
  there. The current rejection is a C3 implementation defect, not a user fork.
- `when`/`unless` now have a truthful normative home with their established
  unconditional `Option` wrapping. QA still owns citation retargeting.
- No normative `/learn` behavior remains in the live specification. ACT-0951
  names the complete future product-specification package and gates any later
  architecture, C6 design, QA plan or implementation for the feature.

The specification gate is clear. Architecture and crate design consume the
0912 error rule and omit `/learn`; neither has an implicit product decision.

### Phase-3 crate-design progress and surfaced gates

| Stream | State | Coherent design outcome / remaining gate |
|---|---|---|
| C1 architecture foundation | complete | unified lifecycle, quote classifier, scoped module-alias mint/walk, one schema/types-baseline window, and `Pure` layout/ABI split ruled |
| C2 frontend | complete | one source/test visit covers quote consolidation, both `deftype` head modes, annotation current-state wash and module rustdoc; no typecheck compensation |
| C3 typecheck | superseded by W3/W4 replan | the earlier one-visit design was falsified by the candidate-set architectural change; `instantiate_demands` and every other cross-crate delta are held for exact user review |
| C4 backend | complete | one realization/release/IO-construction/diagnostic visit; tag-licensed platform-return stamp B5, dormant `vec-len` arm B8 and Decision-24 discharge plan B9 included; producer stores end at publication and C5 atomic ownership begins there |
| C5 intrinsics | complete | one tag-walk/IO/typed-funnel visit; R1's atomic three-state `Pure` claim and R2's counted bridge join are absorbed into I0b, with the retained-reservation W5 braid explicit |
| C5 primitives | complete | one primitives visit; `vec-len` Inline is mandatory, C4 B8 supplies value position, the one-line empty-module API contraction is approved, and C5 edits no backend source |
| C6 binary/exe bundle | complete | one six-bundle visit; 0798/0869 gates discharged; complete annotated-sexp tail included; `/learn` excluded under ACT-0951 |
| C7 platform | complete | one ABI/facade/marker/fixture visit; 0463 deferred without interface narrowing; platform-return safety consumes C4 B5; exemplar ownership split settled |
| Offset detector packaging | complete | independent owner-local compile-time `== 32` pins plus crossing evidence; no C7→backend carve-out, root fallback or repeat crate visit |
| Consolidated QA | complete | R1–R4 are current-sprint prerequisites with closed designs and exact evidence; GO to present Phase 3→4 for user approval |

Three pre-existing runtime risks surfaced while proving the runtime crossing
contracts. QA classifies all three, plus the platform-return overrun, as
current-sprint prerequisites rather than accepted residuals:

1. one shared `Pure` forced on two lanes could transfer its payload twice; R1
   now uses one atomic `payload_glue` claim (`0 | 1 | glue`), permits one winner
   and refuses a loser before payload access;
2. a cancelled `Select` loser can sever the structured join for an in-flight
   blocking `Par` bridge; R2 now retains a counted `BridgeJoinState` until every
   worker lease acknowledges exit; and
3. Decision-24 extern value adaptation decs every `Mode::Borrowed` parameter
   even where the generated extern shim already discharged it; R3 is now C4 B9,
   derived from `Realization × ParamFlow`, with all six string rows as evidence
   rather than implementation policy.

The fourth prerequisite, R4, is the platform-return `Pure` overrun. It is closed
by returned-tag stamping in C4 B5, the C7 ABI-10 layout and fixtures, C5 atomic
claim/teardown, and independent C4/C7 offset pins. R1–R4 all retain failing-first
and control evidence in `tests/plan/s121-test-plan.md`; none is deferred.

## Waves (Phase 4)

The 2026-09-02 Phase-5 replan supersedes the original six-wave organization
below without discarding its completed work or runtime ordering. It isolates
the architectural name-candidate change so that the types, typecheck and int
surfaces are not repeatedly reopened around unrelated work. Approval of this
organization does not waive any wave, specification or public-API gate:

1. **W0 — G0 open:** normalize pre-existing format drift, settle the canonical
   public-API command/tool pin, run the 0694 attribution experiment and resolve
   input contamination before reserving source. **Delivered.**
2. **W1 — C1 lifecycle foundation:** the delivered lifecycle/schema/types
   source package and its retained cache/process evidence tail. The later
   candidate-set work is not folded retrospectively into this wave.
3. **W2 — C2 frontend:** the delivered declaration/quote wash and its retained
   solution-level evidence tail. The former C3 portion is superseded by W3/W4.
4. **W3 — name-candidate convergence:** one vertical architecture and delivery
   wave across the types-owned symbol representation, typecheck candidate
   collection/selection, and int call-site presentation. It establishes the
   agreed rule that colliding visible names may coexist, type information may
   select a unique candidate, and a still-ambiguous use must be canonicalized
   or rejected. Before any product source changes, `arch` must present the
   exact inter-crate API proposal and receive explicit user approval under the
   gate below. W3 then runs one producer-to-consumer migration, one coordinated
   review, and one evidence exit; it does not reopen W1 or masquerade as a
   small continuation of old C3.
5. **W4 — remaining C3:** one typecheck visit through the previously planned
   CS-6 work and C4/C6 handoffs, excluding the candidate mechanism settled in
   W3.
6. **W5 — retained-reservation runtime braid:**
   1. open C5 intrinsics, land I0a, then pause without releasing it;
   2. open C7, stage P0's ABI-10 layout/constant/local pin without the `Pure`
      fixtures, then pause without releasing it;
   3. run C4 B1→B9 once and close C4, observing the pre-P0 `vec-len` GOT path;
   4. immediately open C5 primitives and land P0, with no execution, cache
      capture or promotion between B9 and P0, then retain the reservation;
   5. resume and close C7 P1–P3 and its fixtures, without executing them before
      the C5 crossing is ready;
   6. resume C5 intrinsics I0b/I1 and run the R1/R2/R4 plus IO/Sexp evidence;
   7. run the coordinated typed-funnel subwave—intrinsics I2, primitives P1/P2,
      then I3/P3—and close both retained C5 reservations; and
   8. run the complete W5 unit, process-level acceptance, public-API,
      emitted-ABI and platform-ABI gate before promotion.
7. **W6 — C6:** one binary/executable-bundle visit after C3 CS-6 and the runtime
   facades land.
8. **W7 — U8:** one language-facing pass; C7 alone owns
   `exemplar/platforms/web/`, U8 owns all remaining exemplar material.
9. **W8 — G0 close and integrated gate:** disposition filings/ledgers/actions
   once, then run the fresh full quality gate and user-facing pass.

### Inter-crate public-API user gate

Every wave that could change what one crate exposes to or consumes from
another remains **HOLD** until both checkpoints pass:

1. Before implementation, `arch` presents the exact additions, removals,
   re-exports and Rust signature changes; every affected producer and consumer;
   compatibility, cache-schema and ABI consequences; and the forecast
   `public-api.txt` delta. The user explicitly approves that packet.
2. After implementation, `/review` compares the source, consumer-edge and
   generated baseline diffs with the approved packet. The actual diff is then
   returned to the user and must be explicitly approved before wave promotion.

A general sprint, phase, architecture or wave approval is not approval of an
API packet. Any unlisted item, changed signature, new consumer edge or baseline
mismatch stops the wave and returns to the user. Internal `pub(crate)` changes
and implementation-only changes that leave every cross-crate surface and edge
unchanged do not trigger this gate.

No existing worktree delta is grandfathered. The already-generated
`cranelisp-types/public-api.txt` lifecycle diff and the in-progress
`cranelisp-typecheck/public-api.txt` `instantiate_demands` addition are both
held for user review; neither wave can pass under the former arch-only rule.
W3 is the first prospective application: its organization is approved, but its
API is not, and no W3 product-source work begins until the exact proposal is
presented and approved. [s121 public api review (Git history)](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/sprints/s121-public-api-review.md) is the gate record: Packet A
separates W1's lifecycle boundary from the W3 candidate projection and W4
typecheck entry point currently mixed into the generated worktree baselines.
The user approved the staged/live publication architecture in
[S121 lifecycle-public-api-review record](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/design/arch/s121-lifecycle-public-api-review.md) on 2026-09-02. Its exact
method, carrier and baseline review remains held while `arch` re-derives Packet
A from the approved capability families and production-consumer census.

### W0 execution outcome

**GREEN — C1's technical reservation prerequisites are discharged.** Phase 5
approval is still required before C1 implementation starts.

1. `cargo fmt --all` normalized the six inherited Rust files identified by the
   opening check—two backend files and four types files—and
   `cargo fmt --all -- --check` is green. This was G0 baseline normalization,
   not a product-stream reservation.
2. FIXME 0945 is resolved and retired. `tests/CLAUDE.md` and
   `design/arch/CLAUDE.md` carry one command; the executing guard now enforces
   `cargo-public-api >= 0.52`, uses the same flags and package selector, and
   has a planted 0.51 rejection plus supported-version controls. Its focused
   nextest run passed 3/3, including all seven live baselines.
3. FIXME 0694 D1 is adjudicated. One unloaded control passed; under twelve
   non-Cranelisp CPU workers on thirteen logical CPUs, the single test binary
   produced 147 passes and 53 failures in 200 runs. Every failure was the same
   REPL `undefined function: z` face. Host contention therefore suffices and
   other Cranelisp processes or shared application state are not necessary;
   D1 does not yet prove the publication mechanism. QA routed the bounded D2
   ordered-event pair and D3 anti-vacuity plant into C6 N1/N5's existing
   reservation. No C1 work or design reopening follows.
4. The examples-root `user.cl` was an ignored 95-byte REPL persistence artifact,
   not a numbered learning-sequence file. Its origin cannot be recovered from
   Git because it was ignored; it was moved out of the workspace without loss
   and preserved for user handoff with SHA-256
   `6185165959e4f32e86cfaf7714e273d8cf02e2e4e4195752e26dab2999be84cd`.
   The examples umbrella no longer reports a file-set mismatch; it reaches only
   the two already-attributed FIXME-0907 example REDs.

The W0 package leaves product-source stream opens and reopen count at zero.
The D1 result did not change its owning stream: 0694's remaining evidence rides
the one planned C6 visit, now W6 under the 2026-09-02 replan.

### C1 source outcome

**SOURCE GATE GREEN; W1 EVIDENCE AND USER API REVIEW RETAINED-OPEN.** The
`cranelisp-types` lifecycle package is source-released, but its generated public
baseline has not passed the new user gate. W3 is a separately packaged types
visit rather than a reopen of the W1 lifecycle work.

1. The unified `Binding`/`Callable`/`Life` machine, private table funnels,
   tombstones, typed instance identity, scoped module-alias walk, quote
   classifier and slotless generic ADT recipes replaced the retired lifecycle
   vocabulary in one types visit. `CACHE_SCHEMA_VERSION` is 25 and the types
   public baseline was regenerated once.
2. Executing design and review evidence found two real facade falsifiers before
   release: externally unconstructible lifecycle records and independently
   supplied instance keys/backlinks. The retained owner corrected them with
   role-specific constructors, a types-owned `install_instance` funnel and
   pre-mutation plus restored-state key validation. The one focused re-review
   found no surviving correctness issue.
3. Isolated package nextest passes 196/196 across the library and external
   consumer binary. Types check, warnings-denied all-target clippy and rustdoc,
   formatting, canonical public-API comparison, citations, role wiring and
   diff checks are green. The workspace remains intentionally uncompilable only
   at the allocated C3/C4/C5/C6 carrier wash and was not presented as C1
   evidence.
4. C4 B1 retains the direct schema-25 control/schema-24 refusal and precise
   lifecycle-to-cache-stale evidence. Root/C6 retains process restamp and the
   stale-closure trap. FIXME 0637 therefore remains C4-evidence-gated, and
   FIXME 0931 remains C3/C4/language-evidence-gated.

C1 opened once and was never released then reopened: all executing falsifiers,
corrections, documentation convergence and review occurred inside the retained
reservation. Released product-source stream reopen count remains zero.

### C2 source outcome

**SOURCE/REVIEW GATE GREEN; W2 PROCESS EVIDENCE RETAINED-OPEN.** The
`cranelisp-frontend` surface is frozen and released with no planned source
revisit. Its solution-level evidence waits for the valid root compiler produced
after W3/W4; that tail does not keep typecheck inside W2.

1. The frontend consumed C1's closed `QuoteHead` classifier at all four fold
   sites, made explicit written-versus-omitted `deftype` head modes, used one
   recursive field-type closure walk, rejected invalid declarations before
   emission at the field-name span, and corrected the module-extraction
   contract without changing the frontend public API, cache schema or ABI.
2. Independent review found no product-source correctness defect. Its bounded
   findings were closed inside the retained reservation: exact `Sexp` equality
   now executes an auto-gensym case as well as nested span cases; the module DTO
   documents the delivered direct-vector append contract; and the quote-site
   inventory names the four actual sites.
3. Isolated frontend nextest passes 432/432. Package check, warnings-denied
   clippy and rustdoc, formatting, public-API comparison, citations, role
   wiring and diff checks are green. The ordinary workspace setup remains
   blocked only by the allocated downstream lifecycle wash and is not C2
   evidence.
4. FIXME 0801 was source-verified, folded into 0785 and deleted; 0937 was
   source/document-verified and deleted. FIXME 0785 remains open only for one
   exact malformed trait-return process guard. FIXME 0789's frontend arm is
   complete and remains open only for C6's int-local classifier convergence.
   The retained W2 tail also includes the §5.2.4 positive/reject process matrix,
   two-instantiation construct/match/access coverage, no-partial-registration
   proof and existing quote/macro/annotation cold/warm regressions. QA schedules
   these at the first valid root compiler after C3 and hard B9→P0.

C2 opened once and was never released then reopened: implementation, unit
evidence, documentation convergence, filing dispositions, independent review
and finding-scoped corrections all occurred under one retained reservation.
At C2 release the product-source stream reopen count remained zero.

### C1 executing-falsifier reopen during C3

**REOPENED — exact facade gap, 2026-09-01.** C3's first whole-crate compile
against the settled lifecycle produced 120 source errors. Most are the expected
consumer match wash, but the executing failures exposed required operations
that C1's public `SymbolTable` facade cannot express without forbidden raw
`symbols` access: updating an already-declared callable's settled scheme, AST,
callees, codegen view and ownership summary across `Life::Template` and
`Life::Concrete { realization: Body }`, plus retaining/restoring/removing the
prior trait-impl shell while its writer record participates in the same
transaction.

This is the named falsifier allowed by the no-refix rule. C3 remains retained
and continues only conversions supported by the existing facade. C1 is reopened
through `arch` for the smallest role-specific funnel addition; it may not expose
raw storage, create a second lifecycle vocabulary, mint slots outside C1, bump
the schema again or widen arbitrary mutation. The executing census also found
that a trait method declaration has no truthful lifecycle state: it has a
constrained scheme and reverse trait link but no body or slot, so `Declared`, a
fake `Template` or a concrete callable all misrepresent it. Root therefore
authorized a minimal `Decl::TraitMethod` record and role-specific funnel as an
internal architecture-completeness correction, not a language/spec decision.
The serde shape remains inside the already-open incompatible schema-25 window;
the number does not change and platform ABI is unaffected. The types public
baseline will necessarily receive a finding-scoped second regeneration for the
new downstream funnels and carrier. The released product-source stream reopen
count is therefore **one**, with no ungrounded Phase-3 package reopen.

**REPAIR/RE-RELEASE OUTCOME — GREEN.** Architecture added a truthful unslotted
`Decl::TraitMethod` facet, atomic checked-body/callee/ownership funnels and
opaque callable/shell transaction tokens without reopening raw storage or slot
minting. The retained C1 developer implemented the repair and regenerated the
types public baseline for this finding-scoped reopen; schema remains exactly 25
and platform ABI is unchanged.

The first independent review correctly held the repair on five implementation
hazards and two evidence/documentation gaps: rollback could erase a published
slot hidden in a tombstone, generic non-callable operations bypassed the trait
method funnel, shell rollback was revision-blind, checked views could carry the
wrong symbol identity, shell staging did not enforce trait home, and allocated
fault plants/rustdoc were incomplete. All seven findings were corrected inside
the retained reopen. Nine focused falsifiers and the full isolated types suite
pass (219/219); check, warnings-denied clippy/rustdoc, formatting, canonical
public API and diff gates are green. The one permitted focused re-review found
no surviving issue, and QA issued GO to re-release C1 and resume C3.

C4 B1 additionally retains a schema-25 control containing a lifecycle claim,
tombstone and unslotted trait-method record, paired with a schema-24 refusal
before payload access. Root/C6 retains restamp and stale-closure evidence. The
one full-citation finding created by C3's paused partial `infer.rs` rewrite is
C3-owned and does not contaminate this re-release.

**SECOND EXECUTING-FALSIFIER REOPEN — 2026-09-01.** C3's first complete
behavioral run (453/840) collapsed most failures onto ADT synthesized-key
handling; after that correction, the remaining accessor-collision probe exposed
a lifecycle representation conflict. A module may legitimately contain a bare
field-accessor alias `v` pointing at canonical callable `Box.v` and a bare trait
method declaration `v`. Existing specification/tests require trait declaration
to succeed, the accessor to remain usable, an impl to reject only when its
target owns that field, and the same trait method to dispatch for another
target. C1's one-of `BindingBody::{Alias, Ambiguous, Decl}` cannot currently
represent both facts, while skipping either binding loses semantics. C3 removed
its temporary skip and stopped source edits. This is a second named executing
falsifier, so the released-stream reopen count is **two**; `arch` owns the
smallest truthful identity/resolution repair before either source owner resumes.

**USER-DIRECTED SEMANTIC DIRECTION — 2026-09-02.** Multiple declarations with
distinct canonical identities may expose the same unqualified spelling;
creation or import is not rejected solely because that spelling overlaps.
Resolution belongs at the use site: ordinary contextual and type constraints
may select one candidate, while a use that still has multiple candidates must
use canonical qualification. Inference must filter candidates without global
overload backtracking. This direction supersedes the premise behind the second
C1 repair. The user subsequently approved its exact scope: module-level
declarations, imports, re-exports and derived members with distinct canonical
identities form candidate sets; syntactic context filters first, HM filters
typed values, scrutinee typing filters constructors, lexical shadowing and
module-routing alias conflicts are unchanged, and same-canonical repetition
remains governed by its existing declaration rules. `spec` has recorded that
rule and invalidated the changed coverage claims. C1/C3 remain paused while
`arch` replaces the special-case repair with one candidate-set facade and QA
reallocates the affected evidence.

**ARCHITECTURE FOLD-IN — 2026-09-02.** The user approved one symbol map whose
per-spelling entry retains the canonical binding, when present, and references
to every visible candidate. The parallel serialized `trait_methods` map is
rejected: trait methods, accessors, imports, re-exports and other overloadable
declarations use the same candidate mechanism. W3 must return the exact entry
and candidate carriers—including the fate of `BindingBody::{Alias,
Ambiguous}`—for user review before implementation. Packet A1's atomic live
publication operations remain independently reviewable because they consume a
complete `SymbolTable` and do not expose the candidate representation.

**PACKET B READY — 2026-09-02.** The exact W3 proposal is now recorded in
[s121 public api review (Git history)](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/sprints/s121-public-api-review.md). It keeps `SymbolEntry` private, generalizes the
read-only projection to `NameCandidate`, removes `BindingBody::{Alias,
Ambiguous}` and the parallel trait-method facade, and reduces `Resolved` to
one canonical terminal identity. It also removes the old
definition-over-import rejection API, which now contradicts approved spec
§8.6.4. No product source is authorized until the user approves the exact
delta. If approved, Packet B runs as its own types → typecheck → integration
wave before Packet A1 implementation; downstream work is rebased so each
consumer crate receives the settled candidate facade once.

**PACKET B SPEC PREREQUISITE — APPROVED 2026-09-02.** The user approved the
representation-neutral import-resolution clarification. `spec/08-modules.md`
§§8.3.5, 8.4.0, 8.4.5 and 8.6.2 no longer prescribe
`ModuleEntry::{Import, Reexport}` storage: implementations may retain immediate
or terminal references, but must compare terminal identities and bound any
reference-chain cycles. Observable import, rename, visibility, candidate and
qualification behavior is unchanged. Packet B now waits only on its exact
inter-crate public-API review; product source remains held.

## Coordinator handover (2026-09-03)

Coordination moved from Codex to Claude Code mid-Phase-5. The handover verified
this plan against live source rather than accepting it; findings:

| Claim in the record | Verified state |
|---|---|
| Root integration at 80 migration errors | **Accurate** — `cargo check -p cranelisp --lib` reports exactly 80 errors, 1 warning |
| "architecture and int-design carriers converging" | **Stale** — both converged; the carriers were written after this file's last save. Corrected above |
| `spec/08-modules.md` §8.10.4 contradiction (semantic-delta audit item 8) | **Live and unrepaired** — §8.10.4 still states "Each definition is fully compiled before the next begins". Open user gate |
| Dispatch log completeness | **Incomplete** — see below |

**Dispatch route from here.** The primary harness supplies the definitive shared
allocation directly through its named role agents (`arch`/`audit`/`qa`/`review`
at `fable`, the remaining dispatched roles at `opus`, all at `high`). The
`.agents/tools/claude_role.py` transport is no longer the route for Claude-hosted
roles; it stays available for a role whose allocation this harness cannot offer.

**Dispatch-log gap — recorded, not reconstructed.** Every dispatch from the
2026-09-02 W3 evidence reopen onward ran under the previous Codex coordinator
and was not logged: W3 use-site candidate-selection implementation, the Packet-A
accessor derivation and implementation, the root set-doc metadata packet, the
root compiled-publication packet, the checked-body ledger design, the
`spec/05-definitions.md`/`spec/09-macros.md` rulings, and the macro-checkpoint
`arch`/`design`(int) reconciliation. Their outcomes are durable in the phase
approval table, the stream ledger and the carriers named above; their provider
session identifiers are unrecoverable at handover and are not invented here.

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Harness |
|---|---|---|---|---|---|
| Phase 2 | `arch` | whole Sprint-121 topology and all 84 filings | Claude `claude-opus-5[1m]` (`fable` allocation) | high | `.agents/tools/claude_role.py`; session `30de67b7-2c88-4d71-9feb-7a6e988da22e`; success |
| Phase 3 | `spec` | 0052, 0799, 0841 and 0912 normative residues | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `af297c94-6c26-44c5-b8f5-547af62df288`; success |
| Phase 3 | `spec` | user-ruling follow-up: explicit `deftype` head and `/learn` deferral | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `5cebdfbe-9eab-4e86-bba6-086fd387b592`; success |
| Phase 3 | `arch` | lifecycle/schema, quote facade, IO payload/ABI and public-API procedure | Claude `claude-fable-5` (`fable` allocation) | high | `.agents/tools/claude_role.py`; session `3e031c6c-17fa-4564-8926-d627dbeef10f`; success |
| Phase 3 | `design` (`cranelisp-frontend`) | 0785, 0789, 0801, 0912 and 0937 as one frontend visit | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `edc6dd0f-795e-4be7-b538-29138e1a2f76`; success; omitted-head written-variable question returned to `spec` |
| Phase 3 | `spec` | omitted-head field type-variable closure for 0912 | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `0badce75-e6bf-4753-8532-1a5aafcbf878`; success; existing authority entailed a located frontend reject |
| Phase 3 | `design` (`cranelisp-frontend`) | consume closed omitted-head rule in the existing C2 reservation | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `27183a8a-e9f1-4991-9556-4ce8558799fb`; success; frontend design closed |
| Phase 3 | `design` (`cranelisp-typecheck`) | unified C3 lifecycle, monomorphisation, accessor, auto-curry and census visit | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `ae5e673b-c98a-4dcc-acd8-c31f0e2203f8`; success; 0553 public-facade approval routed to `arch` |
| Phase 3 | `arch` | FIXME 0553 typecheck public-facade gate | Claude `claude-fable-5` (`fable` allocation) | high | `.agents/tools/claude_role.py`; session `3e84d299-82b1-42ec-84ed-6303c23d571b`; approved `instantiate_demands`; success |
| Phase 3 | `design` (`cranelisp-typecheck`) | consume approved 0553 facade and close C3 | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `f6baed25-df9f-4085-ac20-20cf986be33c`; success; C3 design closed |
| Phase 3 | `design` (`cranelisp-backend`) | unified C4 concreteness, release, IO construction and diagnostics visit | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `c11a295e-fded-4b67-8c78-c2b82eeefb8d`; success; Pure run-lane wording conflict routed to `arch` |
| Phase 3 | `arch` | reconcile `Pure` run/teardown lane ownership witness | Claude `claude-fable-5` (`fable` allocation) | high | `.agents/tools/claude_role.py`; session `6d4cc4d5-11af-44fe-b1f2-79f55ab8574b`; clear-before-transfer required; success |
| Phase 3 | `design` (`cranelisp-backend`) | consume final `Pure` lane ruling and close C4 | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `fc6cff6a-0062-4f8a-86b4-e368760e2188`; success; C4 design closed |
| Phase 3 | `design` (`cranelisp-intrinsics`) | unified C5 intrinsics/consume-funnel/IO teardown visit | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `befa5ac1-9768-4c40-a3c5-0ecfe92bf3dc`; success; offset/publication corrections routed to `arch` |
| Phase 3 | `arch` | correct `Pure` witness offset and complete `Par` publication proof | Claude `claude-fable-5` (`fable` allocation) | high | `.agents/tools/claude_role.py`; session `63707d8b-4e9f-4d75-854b-c89ce0744af6`; success; severed-join residual routed to QA intake |
| Phase 3 | `design` (`cranelisp-backend`) | apply witness offset and three-edge publication corrections | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `5cede198-68eb-439d-a498-e7cbb03ab29a`; success; C4 remains closed |
| Phase 3 | `design` (`cranelisp-primitives`) | unified primitives visit, typed funnel and `vec-len` realization | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `79dfcff0-54ba-4432-b2a1-d29e4a0240d2`; success; `vec-len` gate routed to `arch` |
| Phase 3 | `arch` | close `vec-len` lifecycle/backend/public-API gate | Claude `claude-fable-5` (`fable` allocation) | high | `.agents/tools/claude_role.py`; session `ade1a3a9-fff9-483c-892d-5c567e5dae77`; success; dormant arm allocated to C4 B8 |
| Phase 3 | `design` (`cranelisp-backend`) | add dormant `vec-len` arm to the existing C4 visit | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `261d77ba-52be-4c63-b904-1d3617698e69`; success |
| Phase 3 | `design` (`cranelisp-primitives`) | consume the ratified `vec-len` order and API ruling | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `0b027a14-a89c-468f-82e9-4ee2819852da`; success; C5 primitives closed |
| Phase 3 | `design` (`cranelisp-backend`) | repair stale inline value-position lifecycle row | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `4ce449eb-55ff-4dc4-b024-a8a95a88f366`; success |
| Phase 3 | `design` (`cranelisp-int`) | unified C6 binary/executable-bundle visit | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `fd91a09f-8cdf-4b99-8ded-f802218072e2`; success; 0798/0869 gates routed to `arch` |
| Phase 3 | `arch` | scoped module-alias lookup and written-trait carrier producer | Claude `claude-fable-5` (`fable` allocation) | high | `.agents/tools/claude_role.py`; session `d12fd63f-0c78-4d7d-863e-4a8390ec94c2`; success; C1/C3/C6 allocation closed |
| Phase 3 | `design` (`cranelisp-typecheck`) | consume 0798 caller and 0869 producer rulings in C3 | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `c9ea0c20-5c1f-439a-9f01-db7efb68ed1c`; success; CS-6 added inside one visit |
| Phase 3 | `design` (`cranelisp-int`) | consume discharged 0798/0869 gates in C6 | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `e01c2f97-0a78-49cf-9815-f96b1e7ab0f2`; success; C6 blockers closed |
| Phase 3 | `design` (`cranelisp-platform`) | unified C7 facade, ABI, marker and fixture visit | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `4b05e5bd-28f4-4ff7-8146-379d29d760f5`; success; return-stamp safety finding routed to `arch` |
| Phase 3 | `arch` | tag-license the platform-return stamp and allocate it to C4 B5 | Claude `claude-fable-5` (`fable` allocation) | high | `.agents/tools/claude_role.py`; session `9816a972-172f-4f54-9757-dcd9f385f8c0`; success; wild Pure write closed by design |
| Phase 3 | `design` (`cranelisp-platform`) | consume tag-licensed return seam and settle exemplar ownership | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `2f068e32-45d4-4c0a-8d64-43c7e2769fa3`; success; H2 discharged |
| Phase 3 | `design` (`cranelisp-backend`) | reconcile the fourth stamp site and offset pins in C4 | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `16cf97b2-b1f7-440d-a0ec-fd6d0a31feeb`; success; later cross-pin packaging returned to `arch` |
| Phase 3 | `design` (`cranelisp-int`) | allocate annotated-sexp pretty-printer survivor to C6 N5 | Claude `claude-opus-5` (`opus` allocation) | high | `.agents/tools/claude_role.py`; session `e52a8c2e-40cd-430a-bbbf-9c89f367d07e`; success; C6 census closed |
| Phase 3 | `arch` | zero-revisit Pure offset detector packaging | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/arch_cross_pin`; success; independent owner-local pins selected |
| Phase 3 | `design` (`cranelisp-backend`) | consume zero-revisit detector ruling | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_backend_cross_pin`; success; backend wholly C4-owned |
| Phase 3 | `design` (`cranelisp-platform`) | consume zero-revisit detector ruling | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_platform_cross_pin`; success; C7 writes no backend source |
| Phase 3 | `qa` | consolidated R1–R4 attribution, evidence matrix and W3 order | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/qa_s121_readiness`; success; initial no-go returned three design blockers |
| Phase 3 | `arch` | R1 once-only shared-`Pure` ownership | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/arch_pure_once`; success; atomic three-state claim ruled |
| Phase 3 | `design` (`cranelisp-intrinsics`) | absorb R1 and R2 into one C5 visit | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_intrinsics_r1_r2`; success; no architecture return |
| Phase 3 | `design` (`cranelisp-backend`) | absorb R3 B9 and reconcile R1 publication boundary | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_backend_r3_r1`; success; B9→P0 adjacency required |
| Phase 3 | `design` (`cranelisp-platform`) | close R1 residual wording in C7 | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_platform_r1`; success; ABI/layout unchanged |
| Phase 3 | `qa` | final readiness and corrected retained-reservation braid | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/qa_s121_readiness`; success; GO to present Phase 3→4 approval |
| Phase 5 W1 | `dev` (`cranelisp-types`) | unified lifecycle/schema/types implementation and retained corrections | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/dev_c1_types`; success; source gate green at 196/196 |
| Phase 5 W1 | `arch` | C1 public-facade falsifiers and canonical record convergence | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/arch_c1_doc_wash`; success; no user decision required |
| Phase 5 W1 | `design` (`cranelisp-int`) | C1 consumer-document convergence | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_int_c1_doc_wash`; success |
| Phase 5 W1 | `design` (`cranelisp-typecheck`) | C1 ADT consumer check and document convergence | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_typecheck_c1_doc_wash`; success; generic-envelope falsifier routed to `arch` |
| Phase 5 W1 | `review` | independent C1 inspection and one finding-scoped re-review | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/review_c1_types`; success; no correctness finding survives |
| Phase 5 W1 | `qa` | C1 evidence allocation and final adequacy | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/qa_s121_readiness`; GO; cache evidence tail retained for C4/C6 |
| Phase 5 W2 C2 | `dev` (`cranelisp-frontend`) | head-mode, quote-classifier, module-rustdoc implementation and retained unit corrections | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/dev_c2_frontend`; success; source gate green at 432/432 |
| Phase 5 W2 C2 | `design` (`cranelisp-frontend`) | delivered module DTO and quote-site record convergence | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_c2_doc_close`; success; full citations green |
| Phase 5 W2 C2 | `review` | independent cohesive frontend inspection | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/review_c2_frontend`; success; no product correctness finding survives |
| Phase 5 W2 C2 | `qa` | exact-equality discriminator, filing dispositions and source-gate adequacy | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/qa_s121_readiness`; GO; root-process evidence retained after C3/B9→P0 |
| Phase 5 W2 C3→C1 reopen | `arch` | executing-falsifier lifecycle facade and truthful trait-method/transaction contract | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/arch_c1_doc_wash`; success; no user/spec decision required |
| Phase 5 W2 C3→C1 reopen | `dev` (`cranelisp-types`) | bounded facade implementation, tests and one finding-scoped correction loop | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/dev_c1_types`; success; 219/219 plus focused 9/9 |
| Phase 5 W2 C3→C1 reopen | `review` | independent repair inspection and one focused re-review | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/review_c1_reopen`; initial HOLD; focused PASS with no finding surviving |
| Phase 5 W2 C3→C1 reopen | `qa` | repaired-facade adequacy and downstream cache allocation | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/qa_s121_readiness`; GO; C1 re-released, C3 resume approved |
| Phase 5 W3 Packet B | `dev` (`cranelisp-typecheck`) | separable candidate-facade consumer migration and exact identity/cardinality evidence | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/dev_typecheck_w3`; source-complete subset moved 729/840 to 756/840; W4 lifecycle seam held |
| Phase 5 W3 Packet B | `review` | independent inspection of typecheck candidate storage, selection and evidence | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/review_typecheck_w3`; HOLD: syntactic/HM selection and canonical settlement absent |
| Phase 5 W3 design reopen | `design` (`cranelisp-typecheck`) | internal use-site candidate selection, settlement, identity writeback and diagnostics | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/design_typecheck_candidate_selection`; approved by user 2026-09-02 |
| Phase 5 W3 evidence reopen | `qa` | risk-weighted candidate-selection evidence delta and completion criteria | Codex `gpt-5.6-sol` | high | primary-harness named agent `/root/qa_typecheck_candidate_selection`; GO; 11 conditions split between module and focused existing e2e evidence |

## Notes

- Phase 1 performed no role dispatch, source edit, filing disposition,
  destructive cleanup or remote operation.
- The first Phase-2 `arch` dispatch request was refused before process start
  because its external provider would receive repository source, the sprint
  plan, FIXMEs and audit material. The user explicitly approved that disclosure;
  the subsequent named dispatch completed successfully. The refusal has no
  provider session and therefore no dispatch-log row.
- The ignored examples-root `user.cl` predates this census by file timestamp but is
  not treated as harmless: it is an input to the example file-set gate.
- FIXME 0917 remains `status: open` even though Sprint 120 accepted its fix and
  both permanent repro cells are green. It is the first confirmed stale-status
  record; only its owning role may resolve/delete it after source verification.
- The launch-grid and method-only-import cells failed again in focused reruns.
  They are live conditions, not dismissed as intermittent.
- The first detector-packaging `arch` follow-up was interrupted by the external
  Claude provider's session quota. The user then directed continuation with
  Codex models; fresh named Codex roles completed the detector, R1–R4 designs
  and QA recheck without substituting source work for role-owned decisions.

## Outcome (Phase 7)

The user approved closure, commit and push on 2026-09-09. All five Phase-6b
streams are delivered; final acceptance retains the enabled sequence-IO and
generic-redefinition REDs and the failed-turn coverage repair. This is not an
all-green release. See [the closure outcome](#outcome-phase-7) for
exact full-suite and subsequent targeted results, and `sprints/ROADMAP.md`
for the top next-sprint handoff.

The reviewed shared-package contribution is committed at `1172631`, preserving
the revision exercised by this sprint. Contribution is reconciled with remote
main in an isolated checkout; upstream changes are not adopted by Cranelisp
until the next sprint's opening. The user explicitly confirmed this separation.
No further compiler, specification or public-API changes belong to closure.

The approved close operations were to record the accepted residuals, update the
roadmap, archive the live plan, check affected references, and commit/push the
delivered compiler and reviewed five-file shared-package contribution. No
baseline regeneration, compiler repair or consumer adoption of upstream changes
was included. The user separately approved the existing `debug = 1` development
setting; metadata validation passed with no fresh-clone claim.

The shared contribution was published at `98436c9`, a fast-forward retaining
`1172631` as an ancestor; remote readback matched. Dispatcher checks passed
33/33 (Claude), 66/66 (Codex), and statistics checks 10/10. Cranelisp retained
its tested `1172631` gitlink through closure. The post-archive citation check
reported 486 documents, 8,458 citations and zero findings. No permanent RED
was disabled; these are closure observations, not a new whole-suite result.
