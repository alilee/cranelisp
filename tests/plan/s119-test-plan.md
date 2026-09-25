# Sprint 119 QA plan — the non-concrete release contract, and the typed consume funnel

> **Retained dated record.** Only the sections that the safety-invariant
> register and open filings 0761 and 0929 cite by number remain, with their
> original numbering: §3.7 (the NC-series definitions, including the unlanded
> NC-2 census), §4.5 and §5.1. They are S119 allocations and rulings, not
> current status; every RED, census, line number or count below is dated and
> must be compared with current source before reuse. The removed threshold-cell
> retirement (§5.3), the option-2 measurement gate (§7, never recorded), the
> 0694 D1 experiment and flap datum (§8.1–§8.2; the S121 D1 result is in filing
> 0694) and the 0859 disposition (§8.3; retired per [PLAN](PLAN.md)) are
> recoverable with `git show a07823d8:tests/plan/s119-test-plan.md`; the
> baseline, gate map, tranche rows, riders and close gate with
> `git show 48d6e713:tests/plan/s119-test-plan.md`.

## 3. Spine 1 rows — the non-concrete release contract

### 3.7 The R11/R17/R18 negative set (user finding, Phase-5 amendment)

**Provenance.** User finding 2026-07-27: R11 sat graded `unconstructable` from
S84 to S119 with zero negative coverage, and the whole suite is green on all
four live fabrication sites because every cell asserts what should happen and
none asserts what must not. This section is the executable answer. Source
verification for this amendment (mine, at HEAD): the fabrication set is
**four** sites, not five — `fn_compiler.rs:1287` (`.is_err()` →
threshold-guessing branch), `ownership/fixpoint.rs:221`
(`unwrap_or(ConcreteType::String)` — carries an inline "never mis-classified
as Copy" soundness claim, unproven), `mono_expr.rs:836-841`
(`unwrap_or(ConcreteType::Int)`, the 0913 lenient view),
`drop_glue.rs:398` (`unwrap_or(ConcreteType::Int)` for a missing Vec elem
arg). Two sites are the CORRECT refusal pattern and are the models:
`program/support.rs:321` (explicit `NotConcrete` match) and
`types/heap.rs:310-334` (`ctor_field_concrete_types` — one `NotConcrete`
refuses the whole ctor via `Option` collect). `fixpoint.rs:221` and
`drop_glue.rs:398` appear in NEITHER design census nor R18's instance list —
register completeness routed to `/arch` as FIXME 0929. (Disposition
`f5d30808`: asks 1–3 discharged — R18 row extended to all five sites with
grades and owners, model sites named, census-as-enforcement accepted with
the residual graded asserted-with-a-named-falsifier once NC-2 lands; 0929
re-targeted `/design`(backend) as the CtorMeta carrier-ruling anchor.)

**Second finding (coordinator follow-up, verified at source): the
declaration channel, and Type-side laundering.** The backend has two type
sources. The body-AST path is `Var`-free by construction (`MonoExpr`, every
node `ConcreteType`); the OTHER channel is `signature_heap_category(ty:
&Type)` (`rc_emission.rs:478`, ~25 live call sites across `vec_codegen`,
`apply`, `match_codegen`, `lambda`, `par_bind`, `dependent_spark`,
`fn_compiler`), whose `Err(_) ⇒ Mixed` arm is R17's registered violating
seam. One of its feeders is structural, not incidental:
`context.rs:265-284` (`extract_constructor`) materialises
`CtorMeta`/`CtorField` from the ctor **declaration's** scheme, so a
polymorphic product's field type is `Type::Var(a)` **permanently** — a
declaration is polymorphic by nature; monomorphisation substitutes at uses,
and nothing substitutes here. Consequences: (a) **NC-1 is structurally blind
to this channel** — it asserts over slotted entries' schemes, and even after
P-1 lands, `CtorMeta` is still built from the declaration, so NC-1 would be
GREEN while the wild-write channel stayed live — hence NC-5; (b) **R17's
end state depends on this seam**: the arm flip is gated on the census
reading zero, and the declaration channel generates permanent traffic for
every polymorphic-ctor field categorisation until it is closed. There is
also a **Type-side fabrication family** the NC-2 `from_type` pattern is
structurally blind to, because the fabrication happens BEFORE the boundary
and then *passes* `from_type` — laundered concreteness:
`context.rs:280` (`unwrap_or(Type::Int)` when `field_count` exceeds the
scheme's params), `fn_compiler.rs:1214` (defensive dead arm — the preceding
filter guarantees `Some`; unreachable by local construction, still the
wrong spelling), and the int-layer result/display defaults
`src/eval.rs:586`, `src/repl/commands.rs:632`, `src/pipeline.rs:133` (the
fabricated `Int` flows toward the result-release protocol — severity
ungraded). All routed into NC-2 family B + FIXME 0929's extension.

- **NC-1 — the universal slot-gate sweep** (`/dev`(typecheck) unit row,
  authored with CS-1; predicate re-ruled **target-universal** per
  `design/arch/total-concreteness.md` §2, invariant **I-CONC**; FIXME 0930).
  For EVERY symbol-table entry: `callable_got_slot().is_some() ⇒
  scheme.ty.is_concrete()` — whole-table, kind-free. Authored as ONE walk
  asserted through FOUR test fns, so each violating population flips with
  its own fix (the failing-not-ignored convention, per-defect signal):
  1. `…_hand_mints` — the two `UserFn` hand-mints (synthetic accessors,
     residual trait-impl methods) — **RED, flips with CS-1/P-1 this
     sprint**; still the population that would have been RED from S84.
  2. `…_ctor_templates` — every generic-ADT ctor template: user `deftype`
     generics + the bootstrap seeds (`Option.Some`, `Result.Ok/Err`,
     `Pair.MkPair`, `SList.SNil/SCons`, `IO.Pure/Effect`) + `IO.Bind` —
     **RED against FIXME 0931** (S120 ctor-monomorphisation tranche;
     pre-declared close carry, see §11.8). The S119 face-1/I-CT′ work
     proceeds unchanged and does NOT flip this group — `Constructor` slots
     are mandatory fields today, ungated by P-1.
  3. `…_vec_len` — the ONE slotted polymorphic primitive in the system —
     **RED against FIXME 0932** (S120 de-slot; pre-declared close carry).
  4. `…_no_unattributed_violations` — **GREEN**: any violation OUTSIDE the
     three named populations fails here, immediately. This fn is the
     durable universal sweep — as groups 1–3 flip, it alone carries
     I-CONC.

  Fixture: the full bootstrap table + a user polymorphic product with
  synthetic accessor + a generic trait impl + concrete controls. In-fixture
  negative controls proving the sweep does NOT fire on slot-less
  polymorphism: `vec-get`/`vec-set`/`vec-push` (`PrimitiveBody::Inline`,
  slot-less by construction) and the four NC-R roster externs. The reverse
  direction (concrete determined `UserFn` ⇒ slot) stays behaviourally
  enforced by the missing-slot hard failure and is NOT asserted here. The
  FIXME-0926 gate cell is the site-naming sibling for group 1. **Row
  history, kept deliberately:** between 2026-07-27 and 2026-07-28 this row
  carried a kind-partitioned licence table (`f5d30808`) built on the claim
  that `bind` and `catch-runtime-error` are polymorphic slotted primitives.
  The claim was **false at source** — both are slot-less
  `DefKind::PrimitiveExtern`, `callable_got_slot() → None` structurally
  (`src/bootstrap.rs:884-905`, `:1129-1160`;
  `crates/cranelisp-types/src/module.rs:1446-1471`) — and it propagated
  unverified through three hands before `total-concreteness.md` verified
  it. The lesson is root `CLAUDE.md` §Assurance applied to our own
  artefacts: a slot-status claim is a claim about source, checked at source
  before any row is amended over it. The partition table is superseded; do
  not resurrect it. **Known blind spot, by construction:** NC-1 quantifies
  over slotted entries' schemes and cannot see the backend's
  declaration-materialised `CtorMeta` channel — that is NC-5's job; the two
  are a pair, not alternatives.
- **NC-R — superseded.** Its I-ABI label and four-member roster gave way to
  the backend uniform-realization contract. The current production roster
  cell and its closure are [PLAN §S122 — 0936](PLAN.md#s122--0936-production-realization-roster-closure);
  synthetic UniformRust fixtures do not establish that roster.
- **NC-2 — the fabrication census** (`/testing` structural cell, Spine-1
  implementing wave, §3.6 mechanics; precedent
  `drop_glue_legacy_emitter_fence`). Grep-shaped over non-test source: every
  discard-and-substitute of `ConcreteType::from_type` (`unwrap_or…` /
  `.ok()`-then-default / `.is_err()`-branch-to-guess) must be on the pinned
  allow-list, each entry carrying its open-defect citation:
  `fn_compiler.rs:1287` (R18), `fixpoint.rs:221` (0929),
  `mono_expr.rs:836-841` (0913/R18), `drop_glue.rs:398` (0929). The two
  refusal-pattern model sites are named in the cell's rustdoc as the correct
  spelling. A NEW discard site REDs the cell in its own change-set; each fix
  shrinks the pin in the fixing change-set. Detection proof per 0768 in the
  authoring change-set: a temporarily planted discard site REDs the cell,
  recorded, reverted. **Family B (Type-side laundering, same cell, second
  pattern):** `unwrap_or(Type::…)` / `unwrap_or_else(|| Type::…)` in
  non-test source — fabrications that never meet `from_type` as an `Err`
  because they fabricate BEFORE the boundary and pass it after. Pinned
  allow-list at author time, every entry citing 0929:
  `crates/cranelisp-backend/src/compiler/context.rs:280`,
  `crates/cranelisp-backend/src/compiler/fn_compiler.rs:1214` (dead arm —
  filter-guaranteed `Some`; correct spelling is `expect`/`filter_map`),
  `src/eval.rs:586`, `src/repl/commands.rs:632`, `src/pipeline.rs:133`
  (int-layer result/display defaults; severity ungraded — 0929).
  `infer.rs:1290`'s `Type::Var(0)` fallback is out of this family's scope
  (it fabricates a *variable*, not concreteness) and is not pinned.
- **NC-3 — per-site fail-on-revert unit rows** (one per fabrication, riding
  each fix — the enumerated-deferral discipline, so unit-test-per-fix has
  named targets): (a) `fn_compiler.rs:1287` — covered by R17's census + arm
  flip (release contract §5.1); its unit row asserts the located error, never
  the guess branch; (b) `fixpoint.rs:221` — pending the 0929 grading: either
  the arm gains its Principle-25 check (unit row: a residual-typed param
  never seeds below the graded conservative point) or is registered
  legitimate-with-proof and moves to NC-2's model list; (c) `mono_expr.rs` —
  already §3.4's row, unchanged; (d) `drop_glue.rs:398` — unit row: a Vec
  glue request with missing/residual elem arg refuses with a located error,
  never mints Int-elem glue.
- **NC-4 — the accessor boundary repro** (`/testing` e2e, stage-1, RED
  today). The release contract's §2.4 four-line program, `PrimitivesOnly`,
  `--run` + `--link` faces:
  `(deftype (Bx a) [:a v])` / `(defn get [b] (v b))` /
  `(defn main [] (Pure (get (Bx 1024))))`. Subject: payload **1024** exits 0
  with NO signal — RED today (SIGSEGV 139, the `NULLARY_TAG_THRESHOLD`
  boundary). Controls, both GREEN today and staying GREEN: payload **1023**
  exits 255; payload `"hi"` exits 0 — the String control documents WHY the
  suite stayed green for 35 sprints (every heap-typed instantiation passes;
  only scalar payloads ≥ 1024 take the wild write). `// spec:` +
  `// defect: class=scalar-as-pointer
  locus=crates/cranelisp-typecheck/src/adt.rs::synthetic-accessor-mint
  found=S119 owner=/dev(typecheck)`; traces to FIXME 0924 / R11. Joins the
  §1.2 accounting as a stage-1 authored guard; flips at the Spine-1
  implementing wave. Its sum-arm sibling —
  `(deftype (Mb a) Nn (Jj [:a v]))`, payload A/B at the same boundary — is
  the 0926 §1 shape: authored RED-then-GREEN **inside 0867's change-set**
  (rider 1), because 0867 is what makes that surface reachable.
- **NC-5 — the declaration-channel sweep** (`/dev`(backend) unit row,
  RED-first, Spine-1 window). The invariant at the seam, stated
  design-neutrally: **no heap-category decision is made off a residual
  field type materialised from a declaration.** Cell: build a symbol table
  containing a polymorphic product `(Bx a)` (and a concrete control); call
  `ctor_meta_at`; assert every materialised `CtorField.ty` satisfies
  `ConcreteType::from_type(..).is_ok()` OR the materialisation refuses /
  demands an instantiation (however the ruling spells the legal path) —
  RED today (`field_types[0]` is `Type::Var(a)`, permanently). Second
  polarity, the fabrication arm: a ctor whose `field_count` exceeds its
  scheme's params must refuse with a located error, never mint
  `Type::Int` (`context.rs:280`). Routing under the `f5d30808` split: the
  **derivation seam is RULED** — ctor field-type materialisation for
  category/glue purposes delegates to the types-owned refusing projection
  (`crates/cranelisp-types/src/heap.rs::ctor_field_concrete_types`) or an instantiation-substituting
  sibling landed beside it in `heap.rs`, never `context.rs`'s hand-rolled
  `scheme.ty` walk — so NC-5's flip criterion gains a structural leg: the
  fixing change-set retires the hand-rolled walk (grep-shaped pin: zero
  field-type derivation from `scheme.ty` in `context.rs`), and the
  behavioural leg (concrete-or-refuse at `ctor_meta_at`) goes GREEN through
  the delegation. The **carrier shape** (`CtorField { ty: ConcreteType }`
  vs instantiation-keyed materialisation — backend-interior, `pub(crate)`)
  remains `/design`(backend)'s to rule inside the release-contract window
  (FIXME 0929, re-targeted `/design` as the anchor); this cell asserts the
  invariant whichever carrier is chosen. R17 sequencing under the
  `total-concreteness.md` re-ruling: **the arm flip becomes reachable at
  the S120 ctor tranche** (FIXME 0931 — non-concrete templates stop
  compiling, so the census can finally read zero on the polymorphic-ctor
  families); NC-5 is the seam guard that holds the derivation honest until
  and through that tranche.

**Structural-closure note (for the record).** `ConcreteType`'s variants are
`pub`, so `from_type`'s "ONLY way" rustdoc claim is true of conversion but
unenforced against direct literal construction — and every live fabrication
IS a direct literal in `unwrap_or` position, which NC-2's pattern covers.
Full structural closure (sealed variants) would break legitimate exhaustive
matching across the backend; the recommendation to `/arch` in FIXME 0929 is
census-as-enforcement with the residual graded
asserted-with-a-named-falsifier, not a sealing change.

## 4. Spine 2 rows — the typed consume funnel

### 4.5 R8's standing lane (FIXME 0761 — the trigger has fired)

The Track-B cells the S118 deferral waited on are GREEN. The standing
owning-type × position exact-balance lane lands this sprint in the §5.1
normative form:

- **Vehicle:** `tests/gen_ownership_flows.rs` — already the owning-type ×
  position harness (12 positions incl. the S118 eliminator rows). `/testing`
  reconciles its matrix against 0761's axes (let-bound local; borrowed
  argument temporary; returned through N ∈ {0,1,2} lets; TCO loop-carried
  param; closure-env capture; the matched positions) and fills gaps; both
  toggles; a `--link` face for the leak-vs-double-free polarity split.
- **Form:** absolute exact balance is legal here per §5.1(b) — the children
  are free-standing/PrimitivesOnly, macro-free — PROVIDED the binary carries
  one ambient-zero control (a trivial program through the same fixture,
  asserting absolute 0). Remaining `balance_exclusion` entries each carry an
  open-defect citation or are removed.
- 0761 is then actioned: the lane row folds into [historical S119 QA allocation](https://github.com/alilee/cranelisp/blob/dc78ddbee3107043925505531798667dc61f7a03/tests/plan/PLAN.md) and the
  FIXME deletes when the lane lands. Disposition appended to the FIXME this
  phase.
- 0779's decided candidate (1) — the `resolve_auto_curry` seam-polarity unit
  cell, `/dev`(typecheck)-owned — rides the S119 typecheck window (rider 1/3);
  row: `[S119]`, flip = the cell exists and is GREEN with fail-on-revert.

## 5. Option 3 — the normative-form proposal (paper §7 decision 5) and its riders

### 5.1 The proposal (mine to make; lane mechanics are plan-owned)

**N1 — e2e balance lanes.** Any e2e cell asserting allocator balance MUST take
one of exactly two forms:

- **(a) the marginal pair** (`helpers::marginal::MarginalPair`) — control and
  subject differing in **one named axis**, `env_clear` + enumerated allow-list,
  same drive for both halves, asserted quantity = the marginal residual
  (`assert_balanced` / `assert_residual(n)` with a documented closed form).
  Required whenever the child's ambient residual cannot be proven zero: any
  stdlib or macro-invoking prelude, any cold-cache compile-bearing child, any
  REPL session with a prelude.
- **(b) the degenerate absolute** — absolute `allocs == deallocs` over an
  ambient-free child, legal ONLY when the ambient-zero premise is
  **continuously executed** by a named GREEN control in the same binary (a
  trivial program through the identical fixture/env asserting absolute 0 — the
  warm-control pattern of `exemplar_ownership_residue_s116::warm_cache_hit_control_carries_no_ambient_residual`).
  A bare absolute cell with an unexecuted "the prelude is macro-free" premise
  is non-compliant.

**Thresholds are banned outright** for this class (already the
[allocator-balance rule](../CLAUDE.md#allocator-balance-is-measured-marginally-never-absolutely);
this proposal makes it the required form's negative space).

**N2 — the unit-tier lens rule.** A unit row asserting balance **at one
sampled point** is the named anti-pattern (the decision24 blindness: the
sampled point is chosen by the same understanding that wrote the code). A
unit-tier balance row must assert one of:

- a **rate** — the residual is independent of a size axis (measure at ≥2
  values of `|input|`, assert the delta);
- a **tally** — the op count equals a closed form (`incs == |xs| + 1`, pinned
  against the rejected variant, per 0885);
- a **marginal** — delta-vs-control over the in-process RC/alloc counters
  around a closure pair built from ONE parameterised constructor differing in
  one named axis (the §5.2 helper).

Or it names the variant axes it samples and covers them as a matrix. `/review`
treats a new single-point balance row as an Important finding.

**Scope of the normative form:** all balance lanes — `tests/plan/` rows, the
R8 standing lane (§4.5), and every future leak/balance cell. `/arch` owns only
the register linkage (R8's row in `safety-invariants.md` §4 pointing at the
lane); I do not edit that file — the linkage request rides `/arch`'s rider-5
window (0918/0919) and needs no FIXME beyond this named handoff.

**One-axis discipline survives generalization** by construction, not review:
at e2e the harness constructs both children identically except the declared
axis; at unit tier the helper's constructor takes the shared setup once and
the axis as a parameter — hand-built control/subject closure pairs are the
non-compliant spelling.
