# cranelisp-frontend — S123 whole-context assessment

## 1. Verdict

**Would a lean second implementation look like this? Mostly at the boundary and
algorithm level; less so in validation completeness and the maintained material
around them.** The reader, structural annotation node, syntactic builders and
small synthesis kit are credible choices. Missing syntax rejects, a restrictive
module-declaration carrier, obsolete consumption arithmetic and contradictory
guidance keep the delivered context from that shape.

| Attribute | Grade | Assessment |
|---|---|---|
| Design quality | B | Direct recursive parsing, immutable inputs, local validation and a clean syntactic boundary; no framework or execution engine to maintain here. Module extraction does not realize the full required declaration vocabulary. |
| Design realization | C | Shared classifiers, name splitting, synthesis and read-time annotations are implemented. The body-seam roster and annotation explanations describe an older realization; macro shorthand and rest parsing omit required rejection paths. |
| Simplicity and volume optimality | C | The functional decomposition is economical. Constant-width expression-consumption bookkeeping and extensive repeated explanations survive the representation change that removed their purpose. |
| Duplication | C | Important production predicates are shared. The AST test adapter still duplicates entry conversion and sequence routing; annotation and mode contracts are repeated inconsistently across maintained carriers. |
| Risk-weighted production-path coverage | C | 432 crate tests pass, including useful negative and span controls. Malformed macro tails/rest positions, mixed import entries and export aliases remain unprotected in the inspected tests. Many AST cases use a separate sequence adapter. |
| Maintainability | C | Ordinary mechanism changes remain local to this crate, but contributors must reconcile competing guidance and preserve unnecessary bookkeeping. Module grammar repairs can require a types-owned API change. |
| Memory freshness | D | The crate memory describes removed annotation functions and obsolete reader output. Public rustdoc and the master design promise a trace link failure contrary to the specification and implementation commentary. |

**Requirement fulfilment: partial.** Normal reading, AST construction,
annotation transport, declaration extraction and quote synthesis have substantial
executing evidence. Required module forms are rejected or lose entries; malformed
macro declarations and some malformed operators are accepted by the inspected
source paths. These are present conformance gaps, not speculative extensions.

**Maintenance-economy grade: C**, independently of correctness and green tests.
Avoidable weight recurs in code, test adapters, source commentary, local memory
and design documents. It is material but bounded: the crate has no operational
subsystem or pervasive abstraction stack, and most ordinary changes remain local.
The evidence does not support D's systemic delivery multiplication. Conversely,
working algorithms and successful earlier consolidations do not make the
remaining repeated cost negligible enough for B.

## 2. Record, purpose and posture

| Field | Value |
|---|---|
| Context | `crates/cranelisp-frontend`, `design/frontend`, frontend-relevant requirements and tests, and open actions/legacy filings |
| Increment | Sprint 123, Phase 6a |
| Checkpoint | `main`, `f091a8f3e530f6cd3db031fd70175e81241f3472` |
| Date | 2026-11-16 |
| Owner / reader | `audit`; `sprint` and the user deciding the next increment's disposition |
| Prior assessment | [S113 at checkpoint 57253cf2](https://github.com/alilee/cranelisp/blob/57253cf2/audits/frontend-s113.md), read from local Git history; the frontend row of [ACT-0969](../sprints/actions/ACT-0969-next-rotation-audit-inputs.md) is an independently re-judged input |
| Disposition | **Pending S124 Phase 1.** No recommendation authorizes implementation, accepts a residual, changes semantics or blocks S123. |

This is dated evidence, established by [the audit collection](CLAUDE.md), under
[the audit contract](../.agents/skills/audit/SKILL.md) and
[the rotation/disposition rule](../sprints/METHOD.md#27-rolling-whole-context-audit).
The working tree contained unrelated changes to the shared package, a role
adapter, root guidance, the sprint plan and an untracked context file. The
audited crate, design and spec had no diff against HEAD. Only this assessment
was authored; no index/tree-changing Git operation was run.

In ordinary language, the required capability is to turn language text into
faithful structured forms, reject malformed syntax with useful locations,
preserve annotations and documentation, identify written module declarations,
and translate quotation and macro definitions into the forms the compiler can
process. The requirements come from [lexical structure](../spec/01-lexical.md),
[grammar](../spec/02-grammar.md), [definitions](../spec/05-definitions.md),
[traits](../spec/07-traits.md), [modules](../spec/08-modules.md) and
[macros](../spec/09-macros.md). Type inference, loading files, executing macros,
publication and machine-code generation are neighboring responsibilities.

The project is in Phase H, delivering one compiler executable with file and
interactive use. This library processes in-memory source and forms, owns no
durable user data, does no I/O and has no deployment, recovery or telemetry
branch. Source regeneration and cache persistence occur outside its boundary.
Delaying a working compiler for speculative infrastructure would have little
value. That does not excuse losing source forms or rejecting required syntax.

The smallest credible realization in this posture is a byte cursor and recursive
form reader, one structural annotation representation, direct form builders,
one shared declaration grammar, local uniqueness checks, and small quote/clause
synthesis functions. Diagnostics belong at those construction seams. Focused
module tests should drive those same functions; process tests need only observe
the integration promises the module tier cannot establish. No parser generator,
plugin framework, new runtime detector or frontend-specific service is needed.
This is an economic comparison, not a replacement design or new authority.

## 3. Aggregate weight and traced paths

Mechanical inventory at the checkpoint:

| Surface | Observed weight | Interpretation |
|---|---|---|
| Rust source and tests | 12,790 lines in eight module files and five separate test files | Five separate test files account for 6,997 lines; preamble and synthesis tests are inline. These counts describe reading cost, not a quality threshold. |
| Production regions | 5,589 lines before each inline test-module boundary; 1,987 comment-only and 500 blank lines | About 3,102 remaining lines include the actual implementation. Commentary materially affects the apparent monolith size. |
| AST builder | 2,396 lines, plus 4,447 test lines | It contains several related translations; the stronger present simplification case is the obsolete protocol and test adapter, not file length alone. |
| Design products | Eleven documents, 1,790 lines, plus a 75-line design memory | Independently useful subjects exist, but the annotation/body contract is repeated across several products. |
| Crate guidance/facade | 269-line crate memory; 394-line facade, 362 comment-only lines | Boundary promises are buried among repeated contracts, retired migrations and contradictory current claims. |
| Dependencies | Workspace dependency on types, plus direct `dashmap = "6"` | No code imports DashMap; its Cargo comment justifies an alias the facade no longer exports. It is already transitive, so this is minor declaration drift, not demonstrated build overhead. |
| Shared state / operational branches | One atomic synthetic-span counter; ordinary and comment-preserving reads | Both read modes have current consumers. No configuration, logging, filesystem or mode-specific AST branch was found. |

The boundary follows [bounded contexts, frontend](../design/arch/bounded-contexts.md#1-frontend--cratescranelisp-frontend).
Production imports name syntactic types, not resolved `Type`, `Scheme`, backend
or execution APIs. All inspected loops classify syntax, traverse structures or
check local names; none enumerates a symbol table to select a compile-required
identity. **Frontend Principle-24 classification: no semantic identity scan
found in the complete production surface.** This supplies the frontend verdict
missing from [current QA navigation](../tests/plan/PLAN.md); it does not dispose
the other contexts' unfinished classifications.

| Trace | Requirement and realization | Evidence / limit |
|---|---|---|
| Literal and nested form | Lexical precedence → `read_form` → number/string/list reader → located `Sexp` | Reader tests cover normal literals, delimiters, UTF-8 strings and name boundaries. The signed operator branches bypass a negative guard: R3. |
| Annotation in any position | Reader builds `Sexp::Annotated` → quote transport or `build_expr` → `Expr::Annotate`; binder chains peel to bounds | Nested, operand, macro-argument and span tests exist. The representation removes positional sibling scans, but consumption bookkeeping and older prose remain: R4/R5. |
| Definition | `build_forms` desugars once → shared head classifier → shape parser → `ParsedEntry` conversion | Type fields and parameters are validated before entries are emitted; duplicate constructors/fields and invalid tails have focused controls. The test adapter duplicates the sequence/conversion path: R4. |
| Macro declaration | `parse_defmacro` → parameter description → private clause-definition synthesis → ordinary AST building | Fully qualified constructor/type references and shared synthesis primitives are appropriate enablers. Shorthand trailing forms and invalid rest placement survive: R1. Recognition and execution remain outside the crate. |
| Module declaration | Raw forms → shared structural classifier → extraction; `super` normalizes against the containing module before return | Plain imports, globs, simple module names and root-`super` rejection are tested. Mixed entries and export module aliases do not have the required result: R2. |
| Quote/quasiquote | Types-owned exact `quote_head` → depth-aware transformation → qualified constructors → builder | Idempotence, gensym identity, nested quote behavior and raw-quote backstop tests are useful. The direct `build_expr` entry intentionally requires already-desugared input; source-level form entries fold first. |
| Preamble/comments | Optional comment stream; separate physical-line head scan for preamble | Separate scan is earned: blank lines determine the preamble boundary and are absent from the comment stream. Capture tests discriminate blank/form/EOF boundaries. Byte-stable regeneration is not proved by this crate run. |

Mechanism classification and cost judgment:

- **Directly required:** lexical forms, AST translations, annotations, module
  declaration forms, quoted data, docstrings and preamble capture.
- **Necessary enabling mechanisms:** byte spans for located diagnostics;
  construction-time validation; depth and gensym state for quotation;
  qualified constructor synthesis for macros that import no helper names.
  These have concrete semantic obligations; a second execution engine or a
  parser framework would not reduce the present work.
- **Responses to observed risk:** shared head classifier, qualified-name
  splitter, binder reject and synthesis kit remove the drift described by the
  predecessor. Local set checks prevent duplicate declarations before emission.
  Quote backstops fail at the seam that needs desugared input. Their cost is
  bounded and their failure classes remain credible.
- **Unsupported current weight:** constant-one consumed-width protocol and a
  parallel test sequence/conversion adapter; repeated historical commentary and
  contradictory contracts. These add change and review work without a current
  semantic distinction. R4/R5 separate that cost from the useful mechanisms.

The counter and recursion have finite representation/stack limits; this pass
establishes neither unlimited-session span uniqueness nor hostile-input depth
resilience. No workload evidence here earns new protection for those limits.
They do not justify replacing the direct parser or adding runtime monitoring.

## 4. Findings and recommendations

Priorities below are assessment priorities. Cost classes estimate an ordinary
change: small is local; medium requires several mechanisms or an interface
handoff. None is an approved delivery commitment. Source traces are distinguished
from executed failures throughout.

### R1 — Complete macro declaration-shape rejection

**Priority: high. Proposed owner: `qa`. Cost: small for local validation and
module evidence; solution reproduction allocation belongs to QA.**

[Macro syntax](../spec/09-macros.md#921-syntax) admits one body in the shorthand,
and §9.2.2 requires exactly one rest parameter, last. Source inspection finds:

- `crates/cranelisp-frontend/src/defmacro.rs:254`: the shorthand checks only
  that a body exists and copies `children[next_idx + 1]`. Thus
  `(defmacro m [] 1 2)` produces a clause with body `1`, discarding `2`.
  The first body's return type is irrelevant to this shape loss; a valid
  quoted body followed by junk follows the same branch.
- `crates/cranelisp-frontend/src/defmacro.rs:120`: `parse_param_items` keeps
  walking after a rest marker; a later fixed parameter is appended and another
  rest marker overwrites the first. `[&r x]` becomes fixed `x`, rest `r`;
  `[&r &s]` keeps only rest `s`.
- `crates/cranelisp-frontend/src/defmacro.rs:163`: bracket destructuring has
  the same acceptance/overwrite behavior, so fixing only the outer list would
  leave the class open.

These are deterministic source-confirmed wrong acceptances, not newly executed
negative tests. The 25 defmacro tests exercise valid fixed/rest/bracket shapes
and basic malformed declarations, but no inspected cell discriminates these
three losses. The explicit clause parser already requires exactly two forms;
the shorthand is the divergent path.

**Recommendation:** coordinator routes this family to QA for minimal source
reproductions and controls, then the owning design/dev/test work under the
existing defect workflow. No language ruling or structural-rest-node migration
is needed to establish the current syntax obligation. Keep the accepted symbol
encoding in [ACT-0972](../sprints/actions/ACT-0972-structural-rest-marker-reader-form.md)
separate from this defect family.

### R2 — Reconcile module extraction with the required compositional grammar

**Priority: high. Proposed owner: `qa`, then `arch` for any carrier/API delta.
Cost: medium, with public-interface approval potentially required.**

[Import composition](../spec/08-modules.md#8311-accessibility-after-import-testedneg)
requires independent entry classification and explicitly permits
`(import [m [Option Option.*]])`. Exports inherit the grammar, including module
aliases, under §8.4 and §8.4.4.

- `crates/cranelisp-frontend/src/module_extract.rs:362`: in a multi-entry
  names list, encountering a member glob returns immediately. For
  `[Option Option.*]`, accumulated `Option` is discarded. For
  `[Option.* helper]`, `helper` is never examined. The same parser serves
  exports. This is source-confirmed loss of required entries.
- `crates/cranelisp-frontend/src/module_extract.rs:411`: exports require a
  plain symbol for their module spec, so the specified
  `(export [(core.string str) []])` fails before a mount can be represented.
  Imports use `parse_module_spec`; exports do not. This is source-confirmed
  wrong rejection, not proof about downstream mount behavior.
- Renamed names still call `expect_symbol` in the shared names-list parser.
  This is already [ACT-0997](../sprints/actions/ACT-0997-renamed-import-entries-rejected-intake.md).
  Contrary to that action's older statement about missing committed evidence,
  `tests/spec_08_modules.rs:4609` and `tests/spec_08_modules.rs:4622` now contain
  unignored renamed/self-renamed type reproductions with the unrenamed control.
  They were inspected, not run here. The S123 evidence record carries them
  into S124; this audit does not create another rename recommendation.

The crate tests cover singleton member globs and import module aliases. They do
not demonstrate entry union or export aliases. The current whole-list
`ImportNames` choice and export shape cannot express the full requirement;
isolated extra parser branches alone may not suffice. That is an architecture
handoff, not authority for audit to select a new public type.

**Recommendation:** retain ACT-0997 as the rename carrier. Send the two additional
source-confirmed cases to QA through the coordinator, assess them with the
existing carrier limitation, and ask arch to frame any exact API change.
Acceptance evidence should discriminate preserved entries and the import/export
symmetry; no broad module-system rewrite follows from this finding.

### R3 — Apply the operator/digit rule to signed dispatch branches

**Priority: medium. Proposed owner: `qa`. Cost: small.**

[Operator grammar](../spec/01-lexical.md#142-operator-symbols) forbids an operator
run immediately followed by a digit. In
`crates/cranelisp-frontend/src/reader.rs:545` and
`crates/cranelisp-frontend/src/reader.rs:570`, the plus/minus branches recognize
an immediate digit as a signed number, otherwise consume an operator run and
return a symbol without the guard in `read_operator` at line 620.

Consequently `+*1` and `-*1` take the symbol-return branch, then the outer parse
loop reads `1` separately; `*1` takes the general operator branch and errors.
This conclusion is from the complete source path, not an executed negative
probe. It contradicts the crate memory's assertion that the digit restriction
holds for the signed branches too.

**Recommendation:** QA establishes the paired malformed-operator/control cases
at the reader seam and routes the local correction. Preserve ordinary signed
numbers and standalone operators. A lexer framework or second validation pass
would be disproportionate to this branch divergence.

### R4 — Retire obsolete expression-width and parallel test-routing machinery

**Priority: medium. Proposed owner: `design` for the interior decision, with
frontend `dev` and `qa` for implementation/evidence ownership. Cost: small–medium.**

`crates/cranelisp-frontend/src/ast_builder.rs:2133` always returns `(expr, 1)`.
Twelve call sites still calculate widths, advance positions and describe
annotation-aware consumption. `build_if`, argument construction, function
bodies and match-arm parsing carry the protocol even though an annotation is
already exactly one recursive node. The
[annotation design](../design/frontend/annotation-and-declaration-shape.md)
acknowledges this residue; the body-seam and memory explanations keep teaching
the older reason for it. The representation should be buying simpler consumers.

`crates/cranelisp-frontend/src/ast_builder/tests.rs:17` also keeps its own
`ParsedEntry` conversion, followed by a separate per-sexp sequence loop at line
77. The head classifier is now shared, which is an improvement, but the adapter
does not exercise production `build_forms` sequence routing/conversion and
disposition. Dedicated production-entry tests exist; the claim is unnecessary
parallel maintenance and incomplete observation by the adapted cases, not that
the entire suite misses production.

**Recommendation:** have design choose the smallest direct single-node
consumer shape and one appropriate production path for sequence tests; dev
removes the obsolete protocol/adapter where redundant, and QA preserves the
distinct per-form versus sequence obligations. Retain meaningful trailing-input
checks. No public API change, extra test layer or builder file split is implied.

### R5 — Correct and compact the frontend's competing explanations

**Priority: medium. Proposed owners: frontend `design` and `dev`; `arch` for
boundary rustdoc/BC promises. Cost: small–medium, primarily deletion/correction.**

Concrete contradictions reopened against source:

- `crates/cranelisp-frontend/CLAUDE.md:65` says compact annotations read as
  colon-bearing symbols. Lines 80–98 require `try_consume_annotation`, which
  does not exist. The reader creates `Annotated`; the builder consumes it.
- The crate memory and several designs list the trait default body as a caller
  of `build_body_to_end`. The actual callers are the impl method, trace and let
  body. `build_method_sig` preserves one raw tail for typecheck. The newer
  annotation design states this correctly; the older roster remains alongside it.
- `crates/cranelisp-frontend/src/lib.rs:110` promises trace fails when linked.
  [The master design](../design/frontend/frontend.md) repeats it. The
  [expression requirement](../spec/04-expressions.md#4129-build-mode-availability)
  requires availability in every mode; `build_trace` and its nearby source
  commentary correctly describe the retracted refusal. This audit does not claim
  tracing is behavior-identical across modes: ACT-1039 is a separate existing
  implementation issue outside this crate.
- The master design says no types-owned item is re-exported, but the facade
  exports `DefmacroInfo` and `MacroClause` under documented exceptions. Cargo's
  DashMap-alias rationale likewise no longer matches the facade. These are
  factual drift, not proposed boundary-policy changes.
- The crate memory still describes Ring-numbered diagnostics; current source
  names alternatives without Ring numbers. Large facade passages preserve
  retired migration history and repeat the boundary, re-export and DTO contracts
  already maintained elsewhere.

This is material both because it misdirects future work and because it makes
ordinary annotation or boundary changes require reconciliation across code,
rustdoc, memory and several designs. The document checker can validate reference
existence; it cannot establish these semantic claims, and a clean result does
not excuse them.

**Recommendation:** owners correct the false promises and retain each current
fact in its proper canonical home. Reduce historical commentary and overlapping
rosters rather than adding another inventory or verifier. Route any actual API
policy change through arch and the user; factual documentation repair alone
does not authorize one.

## 5. Earlier findings, open carriers and calibration

| Input | Source-first assessment and handoff |
|---|---|
| S113 R1/R7 and ACT-0968 | Shared body checking, uppercase type-head checks, module-name rejects and the dotted-module lexer are present. Read-time annotations supersede sibling scanning. [ACT-0968](../sprints/actions/ACT-0968-qa-audit-evidence-reads.md) retains only its stated frontend lowercase bare-head assertion rider; no separate redispatch is recommended. R1 above concerns the independently unguarded macro parser, not reopening every earlier matrix. |
| S113 R2/R3/R4 | One qualified splitter, shared head classification and one synthesis kit are present. The old full test-router duplication was reduced to shared classification, but entry conversion/sequence adaptation remains: the narrower R4 above records the current cost. |
| S113 R5/R6 | Obsolete design products and retained dead parsers are gone; diagnostics no longer name Ring numbers. Guidance is improved since S113, but current factual contradictions remain under R5. No blanket repetition of the prior cleanup is warranted. |
| ACT-0969: 2,396-line builder | Count confirmed. A large related translation module remains navigable by function groups, with 793 comment-only lines in its production region. No measured change amplification or defect mechanism here justifies a split merely from size. Do not carry the S87 suggestion as implementation work. Reconsider only when an actual grammar change couples independent groups or navigation obstructs a change; inspect that change and choose the smallest separation then. |
| ACT-0969: panic sites | Four production sites: reader UTF-8 extraction after a nonempty peek; dispatch over the classifier's known definition bases; popping an annotation vector after `len() == 1`; and popping splice segments after a splice guarantees one. Their local guards establish the branches' preconditions by inspection. No user-input path to a panic was found, and no replacement error layer is recommended. This is not a claim that arbitrary future callers or enum changes cannot violate a precondition. |
| ACT-0972 | Current rest-symbol encoding is explicitly accepted pending a future representation decision. Preserve it. Activation is the user's decision to open that representation work and its compatibility/API packet, not the malformed-rest finding in R1. |
| ACT-0997 | Existing wrong-rejection carrier; now has committed reproductions. Reuse it, reconcile its outdated evidence statement through its owner, and keep exact API approval with arch. |
| Legacy FIXME 0785 | Reopened the reader fold, generic delimiter test and [filing](../design/arch/fixmes/0785-return-position-annotation-syntax-unenforced-corpus-colonised.md). Its requested exact solution guard remains evidence work; the shape is structurally rejected already. No extra corpus lint or frontend correction is justified. The filing still describes an executable-root gate as future; coordinator/QA should reconcile it with the current delivery posture. |
| ACT-0986 / ACT-0987 | Existing test-discovery attribution and typecheck leads touch frontend evidence or parsed impl bodies but do not transfer their owning work into this audit. Preserve the existing carriers. |

The predecessor's main consolidations paid off: this is not the S113 pattern of
several unaddressed duplicate production classifiers. The current recommendations
are narrower, tied to source-confirmed behavior or identifiable recurring cost.
Neither ACT-0969 suggestion becomes a new unconditional backlog commitment.

## 6. Executed evidence, limits and disposition

- `git rev-parse HEAD` matched the brief; scoped `git diff --name-only HEAD`
  showed no source/design/spec changes. No destructive or mutating Git command
  was run.
- `cargo nextest run --no-fail-fast -p cranelisp-frontend` completed successfully:
  **432 passed, 0 skipped**, one test binary. Build completed in 1.10 seconds;
  nextest reported 0.128 seconds for execution. The configured link prerequisite
  setup ran successfully. No full-suite or root integration test run occurred.
- All production modules and all eleven frontend design products were read;
  targeted unit assertions, applicable solution tests, requirements, facade and
  relevant open filings were inspected. Counts were derived from the files.
- R1–R3's new negative cases are source traces. No scratch probe, new test,
  mutation of another owner's files or process-mode behavioral claim is offered
  as executed evidence. Existing rename reproductions were inspected only.
- The document checker was run after authoring this report using
  `python3 .agents/tools/check_documents.py --root . --config standing-documents.toml`.
  Final result: **exit 0, no findings**, including this assessment.
- This pass does not measure parser throughput, maximum nesting, WASM builds,
  macro execution, persistence fidelity or cross-mode integration behavior.
  The passing crate run establishes the inspected test cases, not complete
  language conformance or release readiness.

| Recommendation | Assessment route | Authorized disposition |
|---|---|---|
| R1 macro syntax losses | `sprint` → `qa`; QA allocates reproductions and owner handoffs | Pending S124 Phase 1 |
| R2 module grammar/composition | `sprint` → `qa`, retaining ACT-0997; `arch` frames any carrier/API delta | Pending S124 Phase 1; existing rename carry retains its own authority |
| R3 operator/digit asymmetry | `sprint` → `qa` for paired reader reproduction/control | Pending S124 Phase 1 |
| R4 obsolete protocol/test adapter | `sprint` → frontend `design`, `dev`, `qa` in ownership order | Pending S124 Phase 1 |
| R5 contradictory/excess explanations | `sprint` → frontend `design`/`dev`, `arch` for boundary promises | Pending S124 Phase 1 |

**Next invocation:** the coordinator receives this report and preserves its
pending disposition under §2.7. QA is the next technical intake for R1–R3 if
the user accepts those recommendations. No source fix, test addition, filing
creation or current-phase advancement was undertaken by audit.
