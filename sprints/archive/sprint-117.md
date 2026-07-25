# Sprint 117: Conformance and Recovery

**Status**: COMPLETE — USER-APPROVED 2026-07-25

**Goal**: Restore non-memory language and REPL conformance, close stale records, and improve the primitives boundary without introducing memory-protection or instrumentation mechanisms that cannot pass the current cyber checks.

**Audit**: cranelisp-platform (next in the established rotation after the
backend → typecheck → src → frontend → runtime sequence)

## Scope

Sprint 117 is deliberately separated from the Phase-H memory-safety and
release-performance frontier. It preserves every existing safety guard but
does not implement the named transitive-release batch or cyber-blocked
ownership diagnostics: allocator/RC event logging, fault injection, detector
modes, or production-path diagnostic hooks. Ordinary behavioral tests,
existing compiler artifacts, and non-instrumented production-emission checks
remain in scope. ABI/layout-changing memory work requires separate approval;
the accepted R-3 boundary convergence is explicitly in scope.

### Track A — qualified traits and stable macro staging

1. Reproduce and reconcile the two distinct qualified-trait positions before
   implementation. FIXME 0794 concerns a qualified trait **reference** in an
   `impl` head, which §7.3 permits but currently mints an unreachable method.
   FIXME 0836 concerns a qualified `deftrait` **declaration binder**, which
   §7.1 rejects. `/qa` attributes the mechanisms; `/spec` frames any remaining
   normative question for the user. Reference positions use canonical
   resolution; declaration binders retain their rejection rule.
2. Reproduce and reduce FIXME 0816: a macro-expanded
   `(begin (deftype ...) (impl ...))` must register definitions in the same
   staged order as its written equivalent. Preserve the positive comparator
   that already succeeds for another trait.
3. Reproduce FIXME 0800 and determine whether leaked internal thunk naming is
   the same macro-publication seam as 0816. Collapse only with evidence; fix
   separately if the mechanisms differ.

Acceptance: permanent failing-first e2e repros carry `// spec:` citations;
qualified and bare `impl` trait references resolve once to the same canonical
trait identity and reachable method mint; qualified declaration binders remain
rejected. Method enrollment, dispatch, and backend targets consume the resolved
identity, not display text. Macro-expanded and directly written definition
sequences have the same registration behavior; no new compilation path, cache
carrier, or memory mechanism is introduced.

### Track B — REPL recovery, display, and introspection

1. Fix FIXME 0817 within `CompilerSession`, the v4 scheduler, and the existing
   per-turn staging/commit boundary. A failed codegen turn discards only that
   turn's staged batch, preserves committed modules and GOT/code retention,
   and leaves later dependency scheduling live. Treat the wrong failing-unit
   name (`codegen failed for /`) as a separately attributable message defect
   rather than silently bundling it.
2. Resolve FIXME 0839 so `/info <Type>` reports the same deduplicated
   `(trait, target-type)` implementation set required on the trait side.
3. Reconcile FIXME 0802 against the current specification and implementation;
   if still live, render constraint-position trait names in the canonical
   qualified form through the existing type renderer.

Acceptance: each defect has a narrow failing-first e2e guard plus unit coverage
for its owning mechanism; Run, Link, and REPL continue through the single v4
pipeline; failed-turn cleanup does not weaken or delete any existing defect
guard.

### Track C — record integrity and non-security primitives cleanup

1. Record the user-approved Sprint-116 `cranelisp-primitives` audit
   dispositions:
   - **accept R-1**, complete-by-construction primitive registration, defaulting
     to a crate-private descriptor; any facade change needs architecture
     approval;
   - **accept R-2**, production-path ownership witnesses, beginning with
     ordinary tests and existing observable behavior; if adequate verification
     demonstrably requires cyber-blocked fault injection or diagnostic hooks,
     return that mechanism to the user rather than silently adding it;
   - **accept R-3**, converge String/Vec layout access on the existing runtime
     owner; compare a narrow owned-`i64` Vec builder/read view with
     purpose-specific `Vec String` helpers, and choose the narrowest boundary
     that makes initialization order and RC responsibility explicit;
   - **accept R-4**, replace the migration log with a current master design
     after the R-1/R-2/R-3 target is settled;
   - **accept R-5**, repair canonical public-surface rustdoc without volatile
     counts. `/arch` approves the statement and `/dev(primitives)` edits it;
     this authorizes no semantic API delta.
2. Complete the historical S115 coverage audit in FIXME 0804. `/spec` supplies
   changed-row provenance; `/qa` alone restores coverage annotations after
   evidence review.
3. Close count and citation drift that does not require diagnostic machinery,
   including FIXME 0855 and mechanically stale records discovered while
   verifying the in-scope FIXMEs against their `refers_to` sources.
4. Produce the formal per-proxy Phase-6a reports carried from Sprint 116; this
   is a process-artifact repair, not a new feature wave.

Acceptance: every accepted audit recommendation has an owner-targeted FIXME;
every declined or deferred recommendation has its rationale recorded in the
audit; the primitives design and rustdoc contain no stale numeric authority;
coverage annotations are restored only by `/qa`; all five proxy assessments
exist before Phase 6b planning.

### Track D — Byte-backed UTF literal and stdlib text design

Design, but do not implement, the user-selected alternative to a native
`Char`: native `Byte`, ordinary `(Vec Byte)`, and a UTF source-literal type
whose payload is representation-identical to `(Vec Byte)`. Practically all
Unicode interpretation—code points, graphemes, normalization, alternate
encodings, and text algorithms—belongs in `stdlib/`. Demonstrate a concrete
stdlib `int-to-string`.

1. `/spec`'s read-only survey is input only. Sprint 117 does not change the
   specification, invalidate coverage, or ask the user to settle the remaining
   language semantics. The design document records every unresolved normative
   question for a future implementation sprint.
2. `/arch` designs the future core boundary: `Byte` with semantic range 0–255
   but an initially permissible 64-bit runtime representation; ordinary
   `(Vec Byte)` using the current Vec representation; and a compiler-certified
   UTF literal nominal type with the same runtime representation as
   `(Vec Byte)`. It covers cross-crate impact, cache/persistence consequences,
   literal lowering, primitive-table changes, REPL display, ABI/layout options,
   migration from native `String`, and stdlib dependencies. There is no
   separate native `Bytes` or `Char`.
   As an explicit feasibility gate, inspect the current Vec layout, allocation,
   generic lowering, element load/store, RC/COW behavior, ABI, cache metadata,
   and primitive/runtime operations to determine whether compact `(Vec Byte)`
   should ship in the same later implementation increment. Recommend
   **ship-together** or **defer** from concrete seam count, interim-architecture
   risk, test surface, and bounded implementation cost—not from assumption.
3. The design uses a general transparent-product rule, not a privileged text
   case: assess whether an eligible one-constructor, one-field product such as
   `(deftype UtfString [:(Vec Byte) s])` can be nominally distinct while
   representation-identical to `(Vec Byte)`. Cover constructor/accessor/pattern
   lowering, trait identity, recursive and polymorphic exclusions, ABI/cache
   consequences, and exact-once RC/drop behavior. Sprint 117 designs this only;
   it does not implement the layout optimization.
4. Narrow `/design` work maps the affected crate surfaces and supplies an
   implementation sequence for a later sprint, separating irreducible literal
   certification and Byte/Vec mechanisms from library-composable text policy.
5. `/stdlib` designs validated text ADTs and algorithms over `(Vec Byte)`,
   including code-point and grapheme views and alternate UTF encodings. It
   designs `int-to-string` using existing arithmetic, including zero, negative
   values, and `MIN_INT`, avoiding absolute-value overflow through
   negative-domain decomposition.
6. `/qa` produces a future verification matrix covering Byte bounds, packed
   representation parity, literal certification, transparent-product identity,
   invalid UTF, display, stdlib code-point/grapheme behavior, mode parity, and
   primitive-to-stdlib migration.

Acceptance: one architecture-owned design document lays out the current
problem, options, recommendation, rejected alternatives, unresolved normative
questions, cross-crate impact, staged implementation strategy, verification
strategy, and future user gates. It shows the irreducible core surface, a
credible stdlib `int-to-string`, and how later compact `(Vec Byte)`
representation can land without a language-type migration. No spec change,
semantic ruling, carrier implementation, primitive removal, cache bump,
compact-Vec work, or test-annotation invalidation lands in Sprint 117.

### Explicitly out of scope — cyber-check constraint

- Sprint-116 Waves 4–5: transitive drop-glue consumers, match/capture/TCO
  release, and entry/program-result release (including 0745, 0760, 0782, 0796,
  0835 and their guards).
- Sprint-116 Wave 7: M1/M2/M3/A1–A4 detector proofs, fault injection, allocator
  or RC diagnostic modes, and FIXME 0848/0857.
- Cyber-blocked ownership instrumentation and generative/instrumented matrix
  expansion, including 0726, 0761, 0778, 0779, 0830, and 0831. Ordinary
  production-path tests for primitives-audit R-2 remain in scope.
- FIXME 0850 remains deferred as the intrinsics-internal `drop.rs` →
  `heap_access`/`vec_runtime` convergence entangled with the blocked batch.
  R-3 is separate: it removes cross-crate Vec offset arithmetic from
  primitives `split`/`join` by delegating to the existing Vec owner. R-3
  neither resolves nor partially closes 0850. Any new narrow `pub unsafe`
  runtime operation requires `/arch`-approved rustdoc and public-API baseline
  change; general mutable offsets are forbidden.
- Load-dependent corruption certification, 0604/0694/0818 investigation, the
  three-run loaded-corruption obligation, and identical-two-run certification.
- Multi-field SROA, LLVM `--release`, RC fusion, display protocol 0050, and
  `/learn` 0052. The release tier remains gated behind the paused safety work;
  this sprint does not route around that gate.

The excluded RED guards remain failing-not-ignored and attributed. They are not
deleted, weakened, reclassified as green, or counted as Sprint-117 regressions.
Their further deferral, including the aged 0850 recurrence, requires explicit
user sign-off as part of this scope approval.

## FIXME debt

| FIXME | Target skill | Proposed S117 status | Notes |
|---|---|---|---|
| 0794 + 0836 | /qa + /spec | in scope | Qualified trait-head conformance; resolve requirement and attribution first. |
| 0800 + 0816 | /qa | in scope | Macro publication/staging; collapse only after a shared mechanism is reproduced. |
| 0817 | /qa → /design(src) → /dev(src) | in scope | Failed codegen batch must not poison later turns. |
| 0802 | /qa | in scope after live verification | Canonical constrained-type display. |
| 0839 | /dev(src) | in scope | `/info <Type>` implementation listing. |
| 0804 | /spec + /qa | in scope | Historical coverage invalidation audit. |
| 0855 | /dev(intrinsics) | in scope | Remove decaying local-memory counts only. |
| 0848 + 0857 | /dev(intrinsics) + /qa | deferred by user constraint | Diagnostic instrumentation excluded. |
| 0850 | /dev(intrinsics) | third deferral requires user sign-off | Raw heap-access convergence excluded. |
| ownership and load-dependent set | multiple | deferred by user constraint | Preserve all guards and attribution. |
| 0858 / 0861 / 0862 | /design(primitives) + /dev(primitives) | accepted, filed | R-1/R-4/R-5; R-4 follows settled R-1/R-2/R-3 design. |
| 0859 | /qa → narrow implementation owners | accepted, filed | R-2: seek ordinary production-path witnesses first; cyber-blocked hooks require a new user decision. |
| 0860 | /design(primitives+intrinsics boundary) | accepted, filed | R-3: remove primitives-owned Vec offset arithmetic; public unsafe/ABI/layout changes require architecture approval. |
| Byte-backed text design | /spec + /arch + narrow design owners + /stdlib + /qa | in scope, design only | Native Byte + `(Vec Byte)` + representation-identical UTF literal; includes compact-Vec feasibility gate. |

## Architecture review (Phase 2)

**Verdict: PASS AFTER REQUIRED REVISIONS (2026-07-23).** Scope is coherent and
can form implementation/design waves with the revisions incorporated above.

- Qualified `impl` references and qualified declaration binders are distinct;
  canonical reference resolution must not undo binder rejection.
- Macro expansion must converge on the existing Pass-1 expansion then shared
  Passes-2/3 registration/check path. There is no macro-only registrar. FIXME
  0800 remains independently gated on attribution and any user/spec ruling.
- Failed-turn recovery remains inside the v4 session and existing transaction
  boundary; no REPL-only compiler path.
- R-1 defaults crate-private. R-2 must witness real lowering: production
  output/CLIF plus observable Run/Link/REPL behavior are admissible, and a
  false fact-table-only change must break a witness. If that requires blocked
  tracing/hooks, return the smallest missing seam to the user.
- R-3 should expose only the narrow runtime-owned operation needed to pin
  allocate/initialize/publish order, invariants, and RC responsibility. No
  types DTO or general offset API is justified.
- Byte-backed text is coherent as design-only work after the user-ruling gate. Its
  future cross-crate/cache/public-surface impact is recorded, not implemented.
- The release frontier remains gated; the sprint does not route around it.

## Skill plans (Phase 3)

Phase 3 opened 2026-07-23.

### `/spec` — text-boundary semantic survey

- **Task**: audit existing String/literal/indexing/conversion requirements;
  produce a compact set of normative questions for the user without selecting
  answers; identify requirements and coverage bands affected by each option.
- **Design refs**: Track D above; `spec/01-lexical.md`,
  `spec/03-types.md`, `spec/12-runtime.md`,
  `spec/appendix-a-builtins.md`.
- **Acceptance**: the user can rule each independent semantic dimension;
  implementation representation remains non-normative; no spec prose changes
  before rulings.

**Status: COMPLETE, SUPERSEDED BY LATER USER RULING (read-only, 2026-07-23).**
The survey found that the initial central
question is the relationship among `String`, `Char`, and `Vec Char`; the
secondary questions are consequences of that boundary. It also established:

- `Char` is not strictly required to express `int-to-string` in stdlib:
  existing integer arithmetic plus an ASCII digit table and byte-indexed
  slicing suffice, including `MIN_INT` via negative-domain decomposition.
  The Character design must therefore compare the Char-mediated and no-Char
  library algorithms.
- Current `String` is valid UTF-8 and its stored length and indexing primitives
  are byte-based. `char-at` returns a single-character `String`; behavior at an
  in-range non-boundary byte offset is unspecified. `substring` likewise does
  not specify non-boundary behavior.
- Existing stdlib text helpers mix byte offsets with “character” terminology
  and are not generally Unicode-correct.
- The user-ruling order is: `String`/`Vec Char` relationship first; then Char
  domain and checked construction; String construction/conversion; indexing;
  literal/display; comparison; exposure and names.

**User ruling (2026-07-23): option 2 selected.**

- `String` remains a distinct packed UTF-8 text value.
- `String` exposes a character-sequence view.
- `String ↔ Vec Char` materialization is explicit.
- `String` and `Vec Char` are neither nominally nor representationally
  identical; String traversal must not promise Vec-like constant-time scalar
  indexing.
- An individual `Char` may use one 64-bit immediate word in the initial
  implementation, but its internal encoding is opaque to language programs.
  This is not a normative `String` encoding or stable ABI guarantee.
- Encoding-specific observations are explicit conversion primitives rather
  than separate native character types. The user supplied
  `as_utf32 :: (Fn [Char] Int)` as the concrete required example. Phase-3
  design must specify whether analogous UTF-8/UTF-16 observations return a
  packed `Int` or a collection, including length and byte-order semantics;
  it must not expose Char's internal encoding.

**Superseding user direction (2026-07-23):** pursue native `Byte`, ordinary
`(Vec Byte)`, and a compiler-certified UTF literal backed
representation-identically by `(Vec Byte)`; push Unicode semantics into
stdlib. Native `Char`, `Bytes`, and the preceding String/Vec-Char model are no
longer the assumed target. Exact literal and stdlib text naming remain open.

### `/arch` — Byte/Vec/UTF-literal architecture and compactness feasibility

- **Task**: produce the cross-crate design and determine whether packed
  `(Vec Byte)` is sufficiently bounded and architecturally final to ship with
  the future Byte/literal increment.
- **Design refs**: Track D; current Vec and String layouts; transparent-product
  proposal; Principles 7, 8, 9, 14, 18, 20, 21, 25.
- **Acceptance**: canonical actor/function model; public and cache/ABI impact;
  transparent one-field-product rule; seam-by-seam compact-Vec assessment;
  ship-together/defer recommendation with implementation and verification
  cost; no implementation.

**Status: COMPLETE (read-only, 2026-07-23).**

- **Proceed** with native `Byte`, initially represented as an i64 value with
  checked semantic range 0–255; ordinary wide-slot `(Vec Byte)`; a
  compiler-certified `Utf8Literal`; and a general transparent one-field-product
  mechanism.
- Transparent heap wrappers are a new representation class, distinct from the
  existing Copy/value flattening. They inherit the sole field's ownership,
  heap category, ABI word, alias/projection behavior, and drop exactly once.
  Widening existing `ValueLayout` to heap fields would incorrectly mark Vec
  pointers Copy and is rejected.
- Prefer **`Utf8Literal`**, because its observable `(Vec Byte)` payload is the
  exact UTF-8 encoding of source text. `UtfLiteral` would falsely imply
  encoding independence.
- **Defer compact `(Vec Byte)`** to the resumed memory-layout/safety frontier.
  Packing crosses at least six safety-sensitive slices: layout carrier;
  backend literal/get/set/push; intrinsics allocation/COW/grow/drop; ownership
  integration; external consumers/display; and ABI/cache migration. Wide slots
  use the final language types and APIs, so deferral creates no interim
  implementation or later stdlib migration.
- Future compact storage is an opaque representation migration. The spec must
  not promise eight-byte Vec slots, and no raw data-buffer ABI may escape.

The design records—without settling—the future user gates: exact literal
encoding/syntax and migration; Byte construction and arithmetic semantics;
automatic versus opt-in transparent products; explicit-only nominal unwrap;
recursive fallback; stdlib text naming/invalid-input policy; native String
transition; and pointer-identity observability.

Further Phase-3 implementation plans do not depend on settling this
design-only track.

**Design document: COMPLETE (2026-07-23).**

- `design/arch/byte-backed-text.md` is the architecture-owned working design.
- It is explicitly non-normative and indexed from `design/arch/CLAUDE.md`.
- It contains the problem, full option set, recommendation, transparent-product
  ownership model, compact-Vec seam inventory and deferral, staged
  implementation strategy, stdlib `int-to-string`, verification matrix,
  public/cache/ABI consequences, risks, future user gates, and archive trigger.
- No spec, code, tests, stdlib, per-crate design, or cache version changed.

### `/qa` — Sprint-wide conformance, recovery, and R-2 plan

- **Task**: live-verify and attribute Tracks A/B; define the failing-first e2e
  set and unit matrices; establish non-instrumented production witnesses for
  R-2/0859; audit 0804 honestly.
- **Plan**: `tests/plan/s117-test-plan.md`, with durable rows in
  `tests/plan/PLAN.md` and `tests/plan/risks.md`.
- **Status: CONDITIONAL PASS (2026-07-24).**

Findings:

- 0794/0836, 0800, 0816, 0817, 0802, and the user-type face of 0839 all
  reproduce.
- `/testing` can draft ungated REDs now for 0800 faces 1–2, 0816, 0817
  recovery plus its separate wrong-unit diagnostic, 0802, and 0839.
- The qualified-trait gate is settled: `impl` reference positions accept bare
  or qualified traits and consume canonical identity; qualified `deftrait`
  declaration binders remain rejected. Function-valued `def` is not a
  language gate: DF-3 is a later `/stdlib` API choice and is outside the
  compiler-owned DF-1/DF-2 work.
- R-2 can proceed without cyber-blocked hooks using production `/clif` plus
  Run/Link/REPL witnesses and mandatory false-fact-only mutation failures for
  Borrowed scalar-result, AliasOf, ProjectionOf, and MayAliasOf.
- The historical 0804 audit restored no unsupported coverage. The constrained
  type-display row in `repl/spec.md` is honestly cleared pending TD-1/TD-2.
- Coverage reconciliation reports zero dead or missing citations and one
  intentional cleared row. No full suite was run.

## Waves (Phase 4 — organized 2026-07-24)

Source edits and test runs are serialized despite independent logical waves.
Byte-backed text remains design-only throughout.

1. **W1 — QA-first e2e guards (`/testing`, sprint-wide).** Land permanent
   failing-first guards for qualified conventional/HKT impl references and
   binder negatives; macro-expanded staging; failed-codegen recovery and the
   separately attributed failing-unit diagnostic; constrained type display;
   `/info <Type>` inverse impl enumeration; and `def` presentation DF-1/DF-2.
   Add R-2 production `/clif` plus Run/Link/REPL witnesses and the
   false-fact-mutation sensitivity checks specified by QA.
2. **W2 — typecheck D/D/R.** Refine against W1, implement canonical
   `FQTraitName` consumption and remove syntax-derived final remangling, then
   review. Binder rejection remains a negative control.
3. **W3 — Binary/int D/D/R.** Implement macro staging, failed-turn recovery,
   diagnostic attribution, shared impl-pair introspection, constrained
   rendering, and generic zero-argument-macro presentation; review as one
   transaction-oriented surface, splitting implementation rounds if needed.
4. **W4 — runtime R-1 and R-2 D/D/R.** Implement the single typed primitive
   declaration inventory, then production ownership witnesses. No diagnostic
   hooks, tracing, detector modes, or fault injection.
5. **W5 — runtime R-3 D/D/R.** Add the two architecture-approved unsafe
   Rust-path Vec-of-String helpers in intrinsics, migrate primitives
   `split`/`join`, update public baseline/rustdoc, and review the exact-once
   transfer and scoped-borrow contract. FIXME 0850 remains excluded.
6. **W6 — runtime records.** Fold R-1/R-2/R-3 into the current runtime master,
   repair primitives rustdoc without volatile counts, and close 0804/0855 plus
   mechanically stale in-scope records under their owning skills.
7. **W7 — Phase 5 gate.** QA evidence reconciliation, architecture public-API
   confirmation, full nextest gate, and unresolved FIXME/review scan.
8. **Phase 6.** User-proxy assessments/actions against what shipped, plus the
   read-only `cranelisp-platform` rotating audit.

### Wave progress

- **W1 QA-first tests: COMPLETE.** Intended REDs were established for the
  remaining compiler/recovery work. Macro staging and basic inverse impl
  enumeration are already green controls. R-2 production witnesses are 8/8
  green without instrumentation. One conventional qualified-impl Link face
  exposed a test output-path collision and is being corrected in the harness.
- **W2 typecheck: COMPLETE, REVIEW PASS.** Qualified conventional and HKT impl
  references resolve once to canonical identity through validation,
  placement/keying, all method mints, rollback/enrollment, and production
  finalization. Qualified `deftrait` negatives remain intact. Four focused
  behavior units cover synthesized defaults, re-impl rollback, no bare
  fallback, and canonical final refresh. Crate gate: 834/834 green; no public
  API/cache/cross-crate delta.
- **W3a transaction and diagnostics: COMPLETE, REVIEW PASS.** Binary now uses
  one owned prepare→whole-batch-codegen→infallible-publish transaction across
  eval and worker cadence; failed turns publish no live table, GOT, retention,
  typecheck-product, or introspection state. Backend preserves exact failing
  member identity at the per-definition lowering seam without a public API
  change. Macro execution compiles an exact, typed-carrier-derived turn closure
  with owned-baseline provenance, required Code/ABI leases, owner-before-pointer
  publication, and rollback-safe reserved GOT cells. The typed builtin carrier
  preserves distinct storage and ABI identities (`macros/sconcat` vs bare
  `sconcat`) with no fallback. Binary 729/729 and typecheck 838/838 green;
  TX1–TX4, S76, and macro lanes green; final reviews PASS.
- **W3b rendering and introspection: COMPLETE, REVIEW PASS.** Constraint
  displays consume stored canonical `FQTraitName` across definition, `/sig`,
  and bare lookup faces. One canonical `(FQTraitName, FQTypeName)` reader
  drives both trait and type implementation drawers with exact target matching,
  canonical deduplication, and deterministic local-before-imported projection.
  TD1/TD2 and IN1–IN3 are green with fixture-truthful FQ expectations and
  isolated inverse-query guards; no public/cache delta.
- **W3c zero-argument-macro presentation: DEFERRED BY USER (2026-07-24).**
  The first implementation made DF1/DF2 green by projecting after publication,
  scanning global introspection provenance, and storing schemes in a parallel
  session map. Review rejected it: projection could fail after live mutation,
  the scan was not resolve-once provenance, and the parallel map had incomplete
  lifecycle ownership. That implementation was removed completely; Binary
  731/731, W3a 4/4, and W3b 5/5 remain green, while DF1/DF2 returned to their
  honest RED state.

  The approved future fix is recorded in
  `design/int/s117-conformance-recovery.md` §1.1.2 and §6 and
  `design/arch/bounded-contexts.md` §6: move the cluster-owned
  `TurnCheckWorld` boundary before Pass 1; stage Pass-1 and
  expansion-emitted macro symbols, introspection, clause code, and owners;
  absorb nested macro preparation into the parent transaction; carry exact
  resolved macro/public-subject provenance; derive `PreparedPresentation`
  against settled candidate tables before backend; and publish
  owners→entries→the complete canonical `Introspection` record exactly once.
  Failure drops the whole turn and clears reserved unreachable GOT cells.
  This reopens the reviewed W3a foundational transaction seam, so the user
  approved moving it to a dedicated Sprint-118 implementation increment
  rather than expanding Sprint 117 further. A deferred owner FIXME records
  the implementation obligation.
- **W4a primitives declaration integrity: COMPLETE, REVIEW PASS.** One private
  56-row typed inventory now derives primitive wrappers, table and GOT
  projections, shim harvest, schemes and metadata, and ownership facts. Its
  closed `UserExtern | UserInline | HarvestExtern` representation makes
  illegal publication/body combinations unrepresentable. Review-requested
  rustc compile-fail cases, a recursive export-source guard, an independent
  full migration-equivalence fixture, and omitted-ownership negative landed;
  FIXME 0864 was resolved and deleted. Primitives 82/82 and relevant e2e/link
  10/10 are green; generated C ABI signatures and the public API baseline are
  unchanged; final review found no Blocker or Important findings.
- **W4b production ownership evidence: COMPLETE, REVIEW PASS WITH EXPLICIT
  PARTIAL DEFERRAL.** Nine ordinary witnesses (five production CLIF and four
  Run/Link/REPL twins) plus two focused typecheck transfer units now separate
  inline Vec body semantics from declaration-summary consumption. Isolated
  mutations prove Borrowed→Owned and AliasOf→Fresh production polarity, and a
  control-flow-merged producer proves MayAliasOf→Fresh through the existing
  `return_is_fresh_by_summary` seam. Architecture traced the sole live path
  from the authoritative inventory through `ModuleEntry`, session seeding,
  `ClusterEnv`, transfer/fixpoint publication, `codegen_view`, and backend;
  there is no stale or alternate metadata source. Bounded ProjectionOf→Fresh
  production shapes were emission-inert, while the real typecheck consumer
  distinguishes ProjectionOf/AliasOf and MayAliasOf/AliasOf. Review passed the
  delivered evidence without hooks, modes, instrumentation, or API changes.
  FIXME 0859 is explicitly deferred to Sprint 118 with the attempted shapes,
  exact missing production-artifact seam, and future resolution/user
  disposition path; W4b does not claim full R-2 closure.
- **W5 runtime-owned Vec-of-String boundary: COMPLETE, REVIEW PASS.** The
  architecture-approved Rust-only intrinsics
  `vec_strings_from_owned(Vec<i64>) -> i64` and
  `with_vec_strings<R>(base, callback) -> R` now own construction and scoped
  read access. Construction transfers fresh HeapString owners exactly once,
  initialises slots before publishing length, and unwinds unpublished
  String/Vec/data allocations exactly once; reads validate metadata and keep
  the slice callback-scoped with no RC action. Primitives `split`/`join` now
  use only that boundary and contain no Vec header/data offset knowledge.
  `join` exits the borrow before allocating its result, then consumes separator
  and Vec-of-Strings exactly once. Identity-based tests prove all input
  allocations die and the result has an independent lifetime. Intrinsics
  283/283, primitives 87/87, and targeted REPL split/join 2/2 are green. The
  only Rust public-API delta is the approved two functions; C ABI and intrinsic
  catalogue are unchanged. Review Blocker 0865 and Important 0866 were
  resolved; target owner verified and deleted FIXME 0860. FIXME 0850 remains
  excluded and untouched.
- **W6 runtime records and rustdoc: COMPLETE, REVIEW PASS.** The retired
  primitives migration log is replaced by a maintained current master covering
  the final R-1/R-2/R-3 actors, flows, invariants, tests, risks, rejected
  alternatives, explicit FIXME 0859 limitation, and untouched FIXME 0850.
  Primitives crate-root rustdoc now describes the real declaration categories:
  `UserExtern` rows own wrappers/GOT slots, `UserInline` Vec rows are direct
  and slotless, and `HarvestExtern` bodies such as `sconcat` belong to their
  owning synthetic module and are absent from `PRIMITIVES_TABLE`. Intrinsics
  guidance uses structural wording rather than decaying counts. The historical
  0804 audit traced seven S115 normative-change commits; QA ran 83 focused
  tests, restored only current coverage, preserved all S117 markers, and left
  eight honest S115 uncovered-debt markers. Reconciliation reports zero dead
  files and zero missing cited functions. FIXMEs 0804, 0855, 0861, and 0862
  were resolved by their target owners; final combined review passed.
- **W7 Phase-5 gate: COMPLETE, QA + ARCHITECTURE PASS.** A W3a cache
  regression discovered by the full gate was reduced to the existing
  six-permutation macro mode-equivalence test: a cache-restored,
  semantically-equal macro clause lacked executable Code/GOT, was omitted from
  the semantic `TurnDelta`, and was then misclassified as a usable baseline
  dependency. The reviewed seed-specific repair enrolls only the freshly
  checked explicit clause when the keyed baseline is non-executable; semantic
  fingerprints, cache schema, W3a atomic publication, public API, and deferred
  W3c presentation remain unchanged. The mode-gating guard's line-sensitive
  allowlist token was also made formatting-stable.

  Clean gate evidence: 5,511 tests run, 5,472 passed, 39 failed, 2 skipped.
  A narrow unsandboxed rerun proved 13 failures were sandbox-only. The slow
  38-module stdlib conformance gate passed separately in 103.66 seconds; its
  apparent hang was cumulative fresh-process/fresh-cache harness cost. The
  product RED set is exactly 26: 23 cyber-excluded/live ownership or detector
  defects, DF1/DF2 under deferred FIXME 0863, and the explicitly excluded
  load-dependent `launch_grid_corrupt` guard. There are zero unexpected
  regressions. Architecture re-gate passed: all eight generated library APIs
  match their tracked baselines, the only intentional public delta is the two
  approved intrinsics Rust helpers, and there is no C ABI, catalogue, cache
  schema, shared DTO, or rejected-W3c residue.
- **Phase 6a assessment: COMPLETE.** REPL, stdlib, examples, docs, and the
  Sudoku exemplar assessed the delivered language from their standing quality
  perspectives and produced action plans. The rotating platform audit landed
  at `audits/cranelisp-platform-s117.md`; its five recommendations remain
  assessment proposals for user disposition in Sprint 118 Phase 1, not
  silently scheduled work.
- **Phase 6b user-facing action: COMPLETE WITH RECORDED FORWARD FLOW.** REPL
  added paired inverse `/info` teaching and replayed all 38 current and
  archived demos. Stdlib added split/join, `str`, `const`, and `def` language
  guards and recorded the Byte/text and negative-domain `int-to-string`
  implementation plans without anticipating unimplemented types. Docs explain
  qualified impls, canonical constraints, inverse introspection, atomic
  recovery, and macro cache parity. Examples retained cold/warm and Run/Link
  parity after a proposed sibling-qualified-impl lesson exposed FIXME 0869
  and was reverted. The exemplar retained byte-identical cold/warm Run output,
  passed 40/40 in parallel and serial modes, and exercised the real R-3
  `split` pipeline; its qualified `Display Cell` adoption likewise reproduced
  0869 warm and was reverted without a workaround. Standalone exemplar Link
  parity remains unverified because platform archives fail earlier with
  unresolved Rust symbols.

  Phase 6 filed three forward-flow findings. FIXME 0867 now targets
  `/testing` for a concrete-vs-polymorphic field-accessor repro. FIXMEs 0868
  and 0869 carry permanent narrow cache REDs; QA recorded them in PLAN and
  verified the precise cache-hit omissions. They add two expected REDs after
  the Phase-5 gate and do not retroactively reopen Phase 5.

### `/design(typecheck)` — qualified trait references

**Status: COMPLETE (2026-07-24).** Conventional and HKT `impl` slot-1
references resolve once from the complete written `TraitRef` to a
crate-private settled `{FQTraitName, TraitDeclInfo}` carrier. Kind and pairing
validation, trait-home placement and impl keying, explicit/default/HKT method
minting, rollback, re-impl enrollment, and final refresh consume that
canonical identity. `program/finalize.rs` must stop remangling from
`TopLevel::TraitImpl`; `deftrait` binder rejection remains frontend-separated.
Existing carriers suffice, so there is no public API, cache-schema, or
cross-crate delta and no `/arch` FIXME. Design:
`design/typecheck/qualified-trait-impl.md`; master and traits designs updated.

### `/design(Binary/int)` — conformance and recovery

**Status: COMPLETE (2026-07-24).**
`design/int/s117-conformance-recovery.md` pins one prepared-turn
expand→stage→exact-batch→JIT→publish transaction, so failed codegen discards
only the turn's products. It also specifies uniform macro-expanded Passes-2/3
ordering, separately keyed failing-unit diagnostics, one shared canonical impl
pair enumeration for `/info <Trait|Type>`, FQ constraint rendering, and
generic zero-argument-macro presentation for `def` DF-1/DF-2. No public
interface change is required; DF-3 remains a later `/stdlib` + `/repl`
API/experience decision.

### `/design(runtime)` — primitives integrity

**Status: COMPLETE (2026-07-24).** R-1 uses one crate-private typed declaration
inventory to derive the primitive table, shim harvest, and ownership facts.
R-2 uses ordinary production CLIF plus Run/Link/REPL witnesses and
false-fact-only mutation sensitivity, with no tracing, hooks, fault injection,
or detector modes. R-3 rejects a generic erased owned-`i64` builder and
selects purpose-specific Vec-String construction and scoped-read helpers, with
element initialization before publishing length and exact RC transfer/borrow
contracts. FIXME 0860 requested `/arch` approval for that two-function
intrinsics Rust surface. FIXME 0850 remains excluded. R-4/R-5 current-master
and rustdoc targets are recorded in
`design/runtime/s117-primitives-integrity.md`. Architecture approved the pair
as two `pub unsafe fn` Rust-path helpers, recorded the exact invariant in
`design/arch/bounded-contexts.md` §4b invariant 17, and resolved FIXME 0860.

### `/arch` — Phase-3 exit gate

**Status: PASS AFTER ONE APPLIED CORRECTION (2026-07-24).** The qualified
trait, Binary/REPL, primitives-integrity, QA, and nonnormative text designs
form a coherent implementation set with no new shared DTO, cache schema, heap
layout, C ABI, intrinsic-catalog entry, or extra compilation path. The sole
public delta is the approved pair of purpose-specific unsafe Rust-path
Vec-of-String helpers in `cranelisp-intrinsics`, governed by explicit
transfer, publication-last, scoped-borrow, validation, unwind, and exact-once
ownership contracts. Runtime design applied the required unsafe-contract
correction; no user decision blocks implementation.

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P2 | /arch | sprint-wide architecture review | inherited Codex | inherited | — |
| P3 | /spec | Byte/UTF/Character semantic survey, read-only | inherited Codex | inherited | — |
| P3 | /arch | `design/arch/byte-backed-text.md` | inherited Codex | inherited | — |
| P3 | /qa | `tests/plan/s117-test-plan.md` + durable plan/risk rows | inherited Codex | inherited | — |
| P3 | /design | `cranelisp-typecheck`: qualified trait impl identity | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| P3 | /design | Binary/int: conformance and failed-turn recovery | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| P3 | /design | Runtime: primitives integrity R-1/R-2/R-3 | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| P3 | /arch | Phase-3 exit and runtime public-surface approval | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| W1 | /testing | Sprint-wide failing-first e2e and R-2 production witnesses | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| W2 | /design → /dev → /review | `cranelisp-typecheck`: qualified trait identity | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| W3a | /design → /dev → /review + /qa attribution | Binary prepared-turn transaction; backend exact error; macro typed provenance | inherited Codex | inherited | agent-type dispatch unavailable; trigger 1–2 attribution after repeated/layered failures |
| W3b | /dev → /testing → /review | Binary canonical constraint rendering and inverse impl introspection | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| W3c | /design → /dev → /review → /arch → cleanup | Binary zero-argument-macro presentation attempt and future transaction design | inherited Codex | inherited | agent-type dispatch unavailable; deferred after reviewed local approach proved architecturally invalid |
| W4a | /design → /dev → /review → /dev → /review | `cranelisp-primitives`: complete-by-construction declaration inventory and review correction | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| W4b | /testing → /dev → /design → /qa → /testing → /dev(typecheck) → /dev mutation audit → /arch → /testing → /review → record correction → /review | Runtime R-2 production ownership evidence and bounded Projection limitation | inherited Codex | inherited | agent-type dispatch unavailable; architecture escalation after two mutation-insensitive witness designs |
| W5 | /dev(intrinsics) → /review → /dev → /review → /dev(primitives) → /review → /dev → /review → /design closure | Runtime-owned Vec-of-String helpers and primitives split/join migration | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| W6 | /design(runtime) → /dev(intrinsics) → /dev(primitives) → /spec → /qa → /spec closure → /review → rustdoc corrections → /review | Current runtime master, durable rustdoc, record drift, and historical coverage reconciliation | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| W7 | /qa → /arch → full gate → /testing → /design(int) → /dev(int) → /review → clean gate → /qa | Phase-5 evidence/public-interface gate and cached-macro regression repair | inherited Codex | inherited | agent-type dispatch unavailable; escalation triggered by full-gate regression |
| P6a | /repl → /stdlib → /examples → /docs → /port + /audit(platform) | User-facing assessments and rotating platform audit | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| P6b | /repl → /stdlib → /examples → /docs → /port | User-facing actions, replay, integration, and exemplar verification | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |
| P6 gate | /testing → /qa | Phase-6 cache repros, attribution, PLAN integrity, and forward-flow disposition | inherited Codex | inherited | agent-type dispatch unavailable; named fallback |

## Notes

- 2026-07-23: user stated that memory-protection and instrumentation items
  which trip the cyber checks cannot be undertaken. Draft scope treats this as
  a hard implementation constraint, preserves the existing safety evidence,
  and selects an independent conformance/recovery increment.
- 2026-07-23: user added a design-only first-class Character track, motivated
  by moving `int-to-string` and related character-level policy from Rust
  primitives into `stdlib/`.
- 2026-07-23: user approved the amended scope and directed `/sprint` to send it
  to `/arch` for Phase-2 review.
- 2026-07-23: `/arch` returned a conditional pass. All twelve required
  corrections were incorporated; Phase 2 passed and Phase 3 opened.
- 2026-07-23: accepted primitives-audit R-1 through R-5 were filed as FIXMEs
  0858–0862 with the Phase-2 constraints.
- 2026-07-23: `/spec` completed the Character survey read-only. The
  `String`/`Vec Char` user gate is open; no normative prose changed.
- 2026-07-23: user ruled that String is a distinct packed UTF-8 type with a
  character-sequence view and explicit materialization to/from `Vec Char`.
  `Char` may initially use a 64-bit immediate representation; representation
  remains non-normative.
- 2026-07-23: user ruled that Char's internal encoding is opaque and alternate
  encodings are exposed through conversion primitives, concretely
  `as_utf32 :: (Fn [Char] Int)`, rather than through three native character
  types.
- 2026-07-23: the Character exploration shifted toward a native `Byte`, compact
  `(Vec Byte)`, and stdlib UTF ADTs. User identified representation-transparent
  one-field product types—e.g. `(deftype UtfString [:(Vec Byte) s])` with the
  representation of `(Vec Byte)`—as the general mechanism to assess. This
  supersedes treating a native Character type as the assumed solution.
- 2026-07-23: `/arch` completed the compact-Vec feasibility pass. Verdict:
  proceed with Byte + wide `(Vec Byte)` + `Utf8Literal` + general transparent
  products; defer packing as a later opaque representation migration because
  it enters six blocked safety-sensitive slices.
- 2026-07-23: user directed that the Byte/UTF/Character exploration remain
  non-normative this sprint. The sole deliverable is an architecture design
  document containing the problem, options, recommendation, implementation
  strategy, and future decision gates; no spec action.
- 2026-07-23: `/arch` delivered `design/arch/byte-backed-text.md` and indexed
  it. `git diff --check` passes; the design track is complete for Sprint 117.
- 2026-07-24: `/qa` delivered the Phase-3 plan and conditional pass. Ungated
  REDs are ready for `/testing`; two normative questions return to the user.
- No source edits or test runs occur before scope approval and Phase-2 review.

## Outcome (Phase 7)

### Delivered

- Qualified conventional and HKT `impl` trait references now resolve once to
  canonical trait identity while qualified `deftrait` binders remain rejected.
- Failed codegen turns are atomic and recoverable; exact failing-member
  attribution, canonical constrained-type display, and inverse trait/type
  implementation introspection landed through the unified v4 pipeline.
- Macro-expanded staging and cached executable-clause recovery converge on the
  ordinary path without a cache-schema or public-interface change.
- The primitives surface is complete by construction from one typed 56-row
  inventory. Nine ordinary production-path ownership witnesses landed without
  cyber-blocked instrumentation.
- `split` and `join` no longer perform primitives-owned Vec layout arithmetic;
  two architecture-approved intrinsics helpers own Vec-of-String construction
  and scoped reads with explicit exact-once RC contracts.
- Runtime master/rustdoc and the historical coverage audit are current.
- The non-normative Byte-backed text design records the problem, alternatives,
  recommendation, compact-Vec feasibility result, unresolved user gates, and
  staged implementation strategy. No character/text semantics entered the
  specification.
- Phase-6 demos, stdlib guards and plans, examples, documentation, exemplar
  verification, and the platform audit landed as recorded above.

### Deferred (with rationale)

- FIXMEs 0800 and 0863: zero-argument `def` macro presentation. The attempted
  local projection was removed after review; 0863 records the cluster-wide
  prepared presentation transaction required for presentation faces 1–2.
  FIXME 0800 remains the umbrella symptom record and separately owns face 3,
  the unresolved stdlib `def` API decision. Both flow to Sprint 118.
- FIXME 0859: full R-2 ProjectionOf production-artifact sensitivity. Ordinary
  evidence exhausted the currently observable seam; adding diagnostic hooks
  would violate this sprint's cyber constraint.
- FIXME 0850 and all named memory-protection, ownership-instrumentation,
  fault-injection, detector, and load-dependent corruption work remain
  explicitly excluded by user direction.
- FIXMEs 0867–0869 flow to Sprint 118. The first still needs its permanent
  polymorphic-accessor repro; the latter two already have permanent REDs for
  cache-restored private-child enrollment and sibling-written trait impls.
- Exemplar standalone Link parity is unverified because the platform archive
  fails before executable production with unresolved Rust symbols. No
  exemplar workaround or unrelated product investigation was added.
- Compact `(Vec Byte)`, native `Byte`, `Utf8Literal`, transparent-product
  representation, Unicode ADTs, and stdlib `int-to-string` remain design and
  implementation strategy only, pending future normative gates.

### Findings (record in FIXMEs if not already)

- Phase 6 found two distinct cache-restoration omissions: restored parents do
  not schedule declared private children (0868), and per-module cache
  snapshots cannot reconstruct sibling-written trait implementation discovery
  shells (0869). The latter needs architecture approval for any typed cache
  carrier/schema change before implementation.
- REPL replay found that polymorphic products mint neither their canonical nor
  unique bare field accessors (0867), an uncovered definition-variant axis.
- The platform audit rates code and coverage Strong but design realisation and
  memory freshness Weak. Its five recommendations will be accepted or declined
  with the user at Sprint-118 scope; only accepted recommendations become
  FIXMEs.
- The 38-module stdlib conformance test is slow because it performs cumulative
  cold process/cache work; its isolated 103.66-second pass is not a hang.
- The frontmatter allocation audit found all 14 command-role model/effort rows
  mechanically consistent with `sprints/artefacts.md` §II.3. Dispatches used
  the harness's named fallback and inherited Codex tier throughout; recorded
  architecture/QA escalations correlated with the W4b evidence seam and W7
  cache regression.
