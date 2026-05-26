# Sprint 70: Frontend cascade absorption + facade audit walk-through

**Status**: COMPLETE

**Goal**: Absorb the S69 `cranelisp-types` settlement into `cranelisp-frontend` — probed, scoped by `/design` + `/arch`, then executed by `/dev`. Follow with the S69 audit-walk discipline against the regenerated `cargo public-api` baseline. One crate only.

## Scope

Two strictly-sequenced phases. Phase B does not begin until Phase A has committed and `cargo public-api -p cranelisp-frontend` has been regenerated as fresh input.

### Phase A — Absorb types changes into `cranelisp-frontend`

**Cascade is larger than "~7 sites" in two categories.** A scope-time probe (`cargo check -p cranelisp-frontend`) surfaced 33 errors across ~13 distinct S69-origin shape changes. Several are not pure mechanical translations — they touch frontend's builder shapes, expander logic, or trait-related construction patterns, and require per-crate design refresh before `/dev` can act. `/sprint` does not pre-judge mechanical vs design-work; `/design` + `/arch` scope.

#### Probe results (scoping input)

| # | Category | S69 origin | Sites | Likely class |
|---|---|---|---|---|
| 1 | `Symbol.0` private | Principle 18 newtype opacity (Group H) | 2 | mechanical |
| 2 | `TypeName.0` private | Principle 18 newtype opacity (Group H) | 3 | mechanical |
| 3 | `ModDecl.is_private → visibility` | D51 visibility cascade | 1 + tests | mechanical |
| 4 | `ModuleEntry::Import { visibility }` field add | D51 visibility cascade | 1 (+ pattern-match cascade) | mechanical |
| 5 | `ModuleEntry::Reexport` variant deletion (collapse to `Import`) | D51 visibility cascade | 1 | mechanical |
| 6 | `ModuleEntry::Macro` variant deletion → `Def { kind: DefKind::Macro { … } }` | Submission 13 macro-unification | 2 | **design refresh** — frontend's `expand` macro-head dispatch reads through new shape |
| 7 | `DefnVariant.param_annotations` → fused `params: Vec<(Symbol, Option<TypeExpr>)>` | Submission 23 | 3 | **design refresh** — ast_builder construction pattern |
| 8 | `Expr::Lambda.param_annotations` → fused tuple shape | Submission 24 | 1 | **design refresh** — same as #7, mirror site |
| 9 | `TraitMethodSig.default_param_names` field deletion | S69 trait-cascade follow-on | 2 | **design refresh** — confirm new representation |
| 10 | `TraitImpl.{type_args,target_type}` field rename / restructure | S69 trait-cascade follow-on | 2 | **design refresh** — confirm new field surface |
| 11 | `FieldDef.span` now required (no default) | S69 span-discipline | 3 | mechanical (thread Span through) |
| 12 | `TypeRef: From<&str>` removed (explicit construction required) | Newtype opacity follow-on | 3 | mechanical |
| 13 | `TraitRef: From<&str>` removed | Newtype opacity follow-on | 1 | mechanical |

8 of the 33 errors are `E0308` mismatched types, downstream of the shape changes above — they resolve as those resolve.

> **#6 boundary clarification (Phase 2 arch ruling).** Item #6 is the macro-storage shape rotation only — the dispatcher reads through `Def { kind: DefKind::Macro }` instead of `ModuleEntry::Macro`. **`expand`'s invocation-vs-Gap policy is FIXME 0175's call, not S70's.** A2's cascade plan must explicitly cap #6 at the lookup-shape rotation; A3 confirms the cap; A5 verifies no 0175-territory code landed.

Categories 6–10 (~10 sites) flag as design-refresh: not in the sense that *frontend's contract* changes, but in the sense that **frontend's per-crate design doc and internal builder/dispatch patterns** need to absorb the new types-side shapes before `/dev` can translate consistently. The S69 walk-through committed the types-side moves; the per-crate frontend design has not yet caught up to them.

#### Phase A wave structure

| Wave | Skill | Crate | Task | Output |
|---|---|---|---|---|
| A1 | `/sprint` probe | — | `cargo check -p cranelisp-frontend` to enumerate cascade footprint | Done at scope time (table above) |
| A2 | `/design` | cranelisp-frontend | Per-category cascade plan: for #6–#10, refresh relevant `design/frontend/*.md` sections + ast_builder/expand/module_extract patterns to absorb new types shapes; for #1–#5, #11–#13, confirm mechanical translation; flag any item that doesn't fit either | `design/frontend/sprint-70-cascade-plan.md` + per-category disposition |
| A3 | `/arch` | — | Narrow review of A2 plan: confirm no cross-crate interface impact, no facade contradiction, no missed S69 settlement; resolve any item A2 flagged as not-fitting | `/arch` verdict on plan; revisions if any |
| A4 | `/dev` | cranelisp-frontend | Execute the A3-approved plan | Source touches per plan |
| A5 | `/review` | cranelisp-frontend | Change-set review against A2 design intent + S69 settlement | `/review` verdict |

**Phase A exit gate**:

1. `cargo nextest run -p cranelisp-frontend` green
2. `cargo check -p cranelisp-frontend` green
3. `cargo check -p cranelisp-types` green (sanity — types is the only Phase A dependency)
4. `cargo public-api -p cranelisp-frontend` regenerated and committed as fresh baseline input for Phase B
5. **Public-API diff is row-traceable.** Every added / changed / removed public-API line must trace to a S69 cascade row in the probe table above. Non-row-traceable changes are out-of-scope and reverted before close. `/review` confirms at A5. *(Phase 2 arch ruling — prevents opportunistic tidying from muddying Phase B's audit baseline.)*
6. `/review cranelisp-frontend` verdict PASS (Blocker/Important findings actioned or deferred with rationale)
7. Single commit (or focused commit sequence) at gate, named `sprint 70 phase A — cranelisp-frontend cascade absorption`

**Workspace-wide compile WILL be broken on downstream crates after Phase A.** That is the natural state — Phase A's exit gate is frontend-narrow green. Downstream cascade is wave-3 for other crates and out-of-scope this sprint.

### Phase B — Facade audit walk-through (deliberative)

With workspace at Phase A's end-state (frontend green, downstream broken — expected) and fresh `cargo public-api -p cranelisp-frontend` in hand, run the S69 audit-walk discipline against `design/arch/facades/frontend.md`.

**Inputs**:
- Regenerated `cargo public-api -p cranelisp-frontend` baseline (Phase A exit gate output)
- `design/arch/facades/frontend.md` (the asserted target shape)
- The configuration set (Decisions, Principles, BCs, FIXMEs, `design/frontend/*`) that grounds the facade per `memory/feedback_configuration_grounds_facade.md`

**Method**: per-finding 5-block analysis from `memory/feedback_audit_per_item_analysis.md`:
1. **facade-expects** — what `facades/frontend.md` says
2. **source-does** — what `cargo public-api` emits
3. **design-intent** — grounded in Decision / Principle / FIXME; NOT manufactured
4. **difference** — the delta
5. **disposition** — one of: source moves / facade moves / file FIXME / no-action

**Default disposition is source-moves** (per `memory/feedback_hold_to_facade_default.md`). Facade-moves is extraordinary, requires `/arch` invocation + user signoff with explicit Decision-amendment rationale, and the Decision cascade lands in the same change-set per `memory/feedback_decision_cascade_discipline.md`.

**User review gate** — per `memory/feedback_explicit_decision_review.md`, user reviews every disposition before any source touches happen.

**Phase B wave structure**:

| Wave | Skill | Crate | Task | Output |
|---|---|---|---|---|
| B1 | `/arch` | — | Audit walk-through: produce per-finding 5-block memo against the regenerated public-api baseline | `design/arch/facades/frontend-audit-s70.md` |
| B2 | (user review) | — | Per-finding disposition review and arbitration | User-arbitrated disposition column on each finding |
| B3 | `/dev` or `/arch` | cranelisp-frontend (source-moves) / facades+ (facade-moves) | Action user-approved dispositions in-sprint; file FIXMEs for cross-cutting or deferred items | Source / facade touches + FIXMEs filed |
| B4 | `/review` | cranelisp-frontend | Final change-set review + close gate | `/review` verdict |

**Phase B exit gate**:
1. Audit memo committed at `design/arch/facades/frontend-audit-s70.md`
2. Every finding has a user-arbitrated disposition (no `TBD`, no deferred-without-rationale)
3. Source-moves: actioned in-sprint by `/dev` if narrow + mechanical; FIXME-filed if cross-cutting
4. Facade-moves: actioned by `/arch` with Decision-amendment cascade landing in the same change-set
5. `cargo public-api -p cranelisp-frontend` regenerated at close, diff matches audit dispositions

## Rationale — why frontend, why now, why this sequencing

- **Cleanest edge of the dep DAG**. `cranelisp-frontend` depends only on `cranelisp-types`. The cascade footprint is smaller than any other consumer crate. This sprint shakes out the **per-crate facade-assertion methodology** (probe → design refresh → arch review → dev → review → public-api regen → audit walk) before the middle-ring crates (`cranelisp-intrinsics`, `cranelisp-backend`, `cranelisp-typecheck`) — each with ~3× the consumer surface — follow.
- **S69 calibration is fresh**. The audit-walk method (5-block analysis, configuration-grounded design-intent, hold-to-facade default) was calibrated in S69 with arbitration count collapsing 24 → 2 once configuration was loaded. Sprint 70 exercises it on the next crate while muscle memory is still in `memory/`.
- **Probe-first, then scope, then execute** — the S69 walk-through taught us that mixing mechanical cascade with deliberative arbitration produces churn (see `memory/feedback_facade_walk_no_interior.md`). Probe-first surfaces the actual footprint so `/design` + `/arch` can scope honestly before `/dev` is invoked. "Mechanical" is a *finding* of A2/A3, not an *assumption* of scope.
- **Two-phase A→B sequencing** keeps mechanical cascade (Phase A) and facade audit (Phase B) cleanly separated. Phase B audits a stable, frontend-green baseline; it does not audit a moving target.

## Out-of-scope (deferred with explicit rationale)

| Item | Why deferred | Target sprint |
|---|---|---|
| Wave-3 consumer cascade for the 5 other crates | Each has its own facade audit walk-through to run; bundling defeats per-crate calibration | S71+ (one per crate, sequenced) |
| FIXME 0098 Phase 2 (`expand` migration + `ExpansionError` enum) | Blocked on FIXME 0175 `/arch` resolution | When 0175 resolves |
| FIXME 0175 `/arch` ruling on `expand` dep widening | `/arch` work, may be triggered by Phase B if audit surfaces the gap as actionable | When `/arch` arbitrates |
| FIXME 0151 FQTypeName implementation | Cross-crate migration; out-of-scope for frontend-narrow sprint | Per `project_fqtypename_priority.md` |
| FIXME 0218 types-facade-retired compliance test | `/qa` work, follows cross-crate cascade completion | S72+ |
| Phase 6 user-facing assessment | Sprint touches no language-visible surface | Waived in close (S69 + S65 + S63 precedent) |

## FIXME debt

Open FIXMEs touching `cranelisp-frontend` or `facades/frontend.md`. S70 actions only those tagged "In-scope".

| FIXME | Target | Status | S70 disposition |
|---|---|---|---|
| 0098 | /dev (multi-crate) | open | Out-of-scope — blocked on 0175 |
| 0100 | /dev (cross-crate) | open | Surface check during Phase B; action deferred unless Phase B forces |
| 0151 | /types | open | Out-of-scope |
| 0175 | /arch | open | Out-of-scope unless Phase B triggers |
| 0218 | /qa | open | Out-of-scope |

No new FIXMEs pre-filed. Phase B is expected to file FIXMEs for cross-cutting or design-refresh dispositions not actioned in-sprint.

## Architecture review (Phase 2)

**Verdict (2026-05-24)**: **APPROVE WITH REVISIONS** — folded into scope.

Both required revisions applied:
1. Phase A exit gate row 5 added — "public-API diff is row-traceable" constraint prevents opportunistic tidying from muddying Phase B's audit baseline.
2. Probe table footnote added — #6 boundary clarification caps the macro-storage shape rotation against bleed into FIXME 0175 territory.

Substantive findings from the review (full memo in conversation; key points captured here for durability):

- **Phase A wave structure (A1–A5) is sound and A3 is not redundant with Phase 2.** Phase 2 reviewed the planned pipeline before any plan existed; A3 reviews the per-category cascade plan `/design` will author at A2. Documentary review, not code review (A5 is code review). Skipping A3 would replicate the un-cascaded-Decision failure mode S69 catalogued.
- **Cascade categories #6–#10 are correctly placed inside `/design cranelisp-frontend`'s remit.** None is a facade-level change in disguise; none is a cross-crate concern requiring escalation. All are consumer-side reads of `cranelisp-types` shapes the S69 walk already committed. Per-row confirms:
  - #6 `ModuleEntry::Macro` deletion → `Def { kind: DefKind::Macro }`: dispatcher lookup-shape rotation; facade already names the new shape; refresh is `expand.rs` pattern-match sites + `design/frontend/*.md` narrative. **Boundary capped via the new footnote.**
  - #7 `DefnVariant.param_annotations` → fused tuple: ast_builder-internal construction shape; exported signatures unchanged.
  - #8 `Expr::Lambda` fused tuple: mirror of #7.
  - #9 `TraitMethodSig.default_param_names` deletion: consumer-side; `/design` confirms new layout, updates `parse_deftrait`.
  - #10 `TraitImpl.{type_args,target_type}` restructure: consumer-side in `parse_impl`; frontend doesn't re-export `TraitImpl`.
- **#6 ∩ FIXME 0175 are structurally disjoint.** #6 is the storage-shape rotation; 0175 is the invocation-vs-Gap policy inside `expand`'s body. Whichever of 0175's (a)/(b)/(c)/(d) eventually lands, the dispatcher still reads through `Def { kind: DefKind::Macro }`. **No Phase A work is redone if 0175 resolves.**
- **Phase B audit method faithfully replicates S69 precedent.** One refinement carried in: block 3 (design-intent) must be grounded in a named Decision / Principle / FIXME from the start — `/arch` authoring B1 should not produce findings without configuration grounding, avoiding S69's first-pass-then-recalibrate dynamic.
- **Principle 8 (interim-architecture) clean.** Nothing in Phase A is interim. The watch-out is /design at A2 resisting "while we're at it, deepen `expand`'s invocation path" — capped explicitly by the #6 footnote.

Verdict: advance to Phase 3 with both revisions folded.

## Skill plans (Phase 3)

### /design cranelisp-frontend

- **Task**: Author the per-category cascade plan for Wave A2 — disposition all 13 probe rows; for design-refresh items #6–#10, outline the `design/frontend/*.md` refresh and the source pattern change `/dev` will execute at A4.
- **Crate** (narrow-deployed): `cranelisp-frontend`
- **Design refs**: `design/arch/facades/frontend.md` (target); `design/arch/facades/cranelisp-frontend-audit-s69.md` (S69 audit findings for overlap); `design/frontend/*.md` (owned per-crate design surface); `sprints/archive/sprint-69.md` Submissions 13/22/23/24 + D51 + Group H (cascade origins); FIXME 0175 (the #6 boundary).
- **Acceptance**: `design/frontend/sprint-70-cascade-plan.md` committed; all 13 rows dispositioned; #6 cap explicit and verifiable; design-refresh targets named (DONE or PENDING-A4); no source touches, no facade touches, no cross-crate proposals.

**Phase 3 outcome** (2026-05-24): plan delivered at `design/frontend/sprint-70-cascade-plan.md` (319 lines). 13/13 rows dispositioned: 8 mechanical, 5 design-refresh (#6, #7, #8, #9, #10). All design refreshes PENDING-A4. #6 boundary cap verified — Gap-emission, `is_macro_head`, invocation path explicitly NOT touched.

**Three open questions surfaced for `/arch` at A3, one critical:**

1. **CRITICAL — Row #6 missing types-side variant.** `DefKind::Macro` is referenced as the macro-storage destination shape in:
   - The `cranelisp-types` file's own rustdoc (8 sites in `module.rs` + `parsed.rs`)
   - The S69 Submission 13 / Submission 22 macro-unification cascade
   - `design/arch/facades/frontend.md` §80–82 (per `/design`'s read)

   But the actual `DefKind` enum at `crates/cranelisp-types/src/module.rs:864–925` has only `Primitive`, `PlatformEffect`, `UserFn`, `Overloaded`, `Constructor` — **no `Macro` variant**. S69's macro-unification was incompletely cascaded: rustdoc and consumer-side references point at a target the variant set never reached.

   This is an `/arch` ruling (cranelisp-types is `/arch`'s owned source) AND a user decision. Three branches:
   - **(a) S70 absorbs the types-side variant add** — `/arch` adds `DefKind::Macro { clauses_meta, sexp, source }` (or whichever fields S69 Submission 13 specified); row #6 proceeds at A4. Small cross-crate expansion of S70 scope; clean closure of the un-cascaded decision.
   - **(b) Drop row #6 from S70, FIXME-defer to S71** — file FIXME `target: /arch` "complete Submission 13 cascade — add DefKind::Macro variant"; S70's Phase A skips row #6; `expand.rs` retains the `ModuleEntry::Macro` pattern-match until S71. Tightest scope but leaves the un-cascaded state visible across a sprint boundary.
   - **(c) Re-confirm alternative destination shape** — `/arch` rules that the rustdoc is aspirational and the actual destination is different (e.g., `DefKind::UserFn { constrained_fn: …, macro_clauses: Some(…) }`, or storage outside `DefKind` entirely). Requires reconciling the rustdoc + facade + S69 narrative against the alternative.

2. **#9 spec reading** — `/design` proposes trait-method no-default branch calls `build_annotated_params` because spec §5.3 EBNF carries param names for required methods too. If `/arch` disagrees, route via FIXME `target: /spec`.

3. **#2 re-attribution** — `/design` folded `TypeName.0` under #12 (no direct `.0` sites in current cargo check output). Clerical; `/arch` confirms at A3 whether the SPRINT.md probe rows are binding-as-listed or summary.

## Waves (Phase 4)

{Pre-shaped above per phase. Finalised after Phase 3.}

## Notes

**2026-05-24** — Phase-1 scope-time probe: `cargo check -p cranelisp-frontend` → 33 errors across 13 distinct S69-origin shape changes. Catalog folded into Phase A scope. The "~7 sites" estimate from the sprint prompt is superseded by the catalog above; Phase A is no longer a single-wave mechanical sweep but a probe → design → arch → dev → review pipeline.

**2026-05-24 (step 1 commit `4cfd01e`)** — Phase 3 types-solidness step 1: `DefKind::Macro` variant authored per S69 Submission 13 close, then amended to D41-compliant `{ clauses_meta }` shape after user-led re-examination revealed pre-D41 shadow fields (`sexp`, `source`) carried forward from S69 narrative without D41 grounding. Rustdoc grounded in D41 + D38 + BC §int + sequence diagrams; names `Introspection` (`src/session_v4.rs:566`) as canonical store. Cache-hit residual gap surfaced + tracked at FIXME 0220 (lazy file re-read; not Introspection serialization). Dead `MacroClauseInfo.source` removed across types + frontend + int. FIXME 0219 filed (save.rs macro arm unification).

**2026-05-25 (step 2 — types-solidness sweep)** — `/arch` ran targeted solidness sweep against the four failure modes Phase-3 step 1 surfaced. Memo at `design/arch/cranelisp-types-solidness-sweep-s70.md`. Sweep verdict TYPES SOLID with 5 actionable + 1 informational finding. User walked each disposition individually: #1+#2 (D41 violations on `ModuleEntry::TypeDef.sexp`/`TraitDecl.sexp`) → source-moves; #3 (`ParsedEntry::TypeDef.type_params: Vec<TypeName>` newtype regression) → source-move via spec §5.2 + newtype-discipline grounding; #4 (`Pattern::Constructor.name` lift to FQ binding) → source-move via new `SymbolRef` type (parallel to TraitRef/TypeRef) + sidecar storage — deferred to step 3; #5 (`ConstrainedFn.defn` S35 cascade incompleteness) → source-move after confirming multi-sig × constrained-poly rejection is structural (filter at `program.rs:2148`); #6 (`Sexp::Comment` liveness) → no action.

**2026-05-25 (step 2 commit `0c202e3`)** — Step 2A landed by `/arch`: 4 narrows in `cranelisp-types` (TypeDef.sexp dropped, TraitDecl.sexp dropped, type_params narrowed, ConstrainedFn narrowed to `variant: DefnVariant`); rustdoc citations land for each; `public-api.txt` regenerated (3743 → 3706 lines; incidentally cleared S69 Sub 41 deep-path staleness). Step 2B fired three parallel `/dev` agents: `/dev typecheck` (9 sexp:None drops + 4 ConstrainedFn renames + form.rs conversion delete + 1 read site at traits.rs:1316); `/dev int` (save.rs unified to 4-arm-symmetric reads from Introspection via local helper; FIXME 0219 closed by absorption + file deleted); `/dev frontend` (Symbol→TypeName conversion at ast_builder.rs deleted). Frontend error count returned to 33 baseline; typecheck landed at 282 (+5 above 277 pre-step-2A baseline — 3 step-2-introduced sites at traits.rs:1354+1361 + program.rs:1637, 4 pre-existing latent sites at adt.rs/checker.rs from S35/S23 cascade not done in typecheck; all carried as typecheck wave-3 cascade for S71+). Types crate green.

**2026-05-25 (step 3 commit pending)** — Step 3 settled the cranelisp-types facade for finding #4 (Pattern::Constructor lift). `/arch` authored only — consumer cascade defers to wash-through per user directive ("settle the cranelisp-types facade in code; consequential impacts on other crates will be dealt with as we wash through"). Three changes in `cranelisp-types`: (1) **SymbolRef type added** at newtype.rs as syntactic-stage analogue to FQSymbol — parallel to TraitRef/TypeRef shape; full surface (Display, derives, ::new, re-exported from lib.rs); rustdoc cites D47 + TraitRef/TypeRef precedent + first consumer pointer. (2) **Pattern::Constructor.name: Symbol → SymbolRef** at ast.rs:62-88; rustdoc cites D47 + sidecar location + S70 sweep finding #4. (3) **`MethodResolutions.pattern_ctors: HashMap<Span, FQSymbol>` sidecar added** at check.rs — option (i) chosen over option (ii) standalone struct on grounds of shared lifecycle + access shape + DTO discipline; MethodResolutions rustdoc rewritten as "per-Span resolved-stage data" with the (i)-vs-(ii) grounding spelled out; S69 Submission 31 wrapper-vs-alias choice vindicated by this first extension. Baseline regen: +107/-1 lines (now 3812 total). Cascade introduced into consumer crates (frontend +2, typecheck +2, backend +unknown delta) — washes through in natural cycles per directive.

## Outcome (Phase 7)

### Delivered

**18 commits** across three phases. Final state: `cargo check -p cranelisp-frontend -p cranelisp-types` green; `cargo nextest run -p cranelisp-frontend` 259/259 passing; `cargo public-api -p cranelisp-frontend --simplified` byte-identical to row-traceable baseline; `cargo doc -p cranelisp-frontend --no-deps` clean (zero warnings).

**Phase 3 — Types-solidness arc** (3 commits):
- `4cfd01e` — step 1: `DefKind::Macro` variant added (was rustdoc-only at 8 sites; never reached the enum); D41-compliant single-field `{ clauses_meta }` shape (dead `MacroClauseInfo.source` removed across types + frontend + int)
- `0c202e3` — step 2: 4 narrows per types-solidness sweep (TypeDef.sexp + TraitDecl.sexp dropped per D41; `ParsedEntry::TypeDef.type_params` Vec<TypeName>→Vec<Symbol> per spec §5.2; `ConstrainedFn { defn: Defn }` → `{ variant: DefnVariant }` per S35 cascade closure)
- `b291a38` — step 3: `SymbolRef` type added; `Pattern::Constructor.name: Symbol` → `SymbolRef`; `MethodResolutions.pattern_ctors` sidecar per D47

**Phase A — Frontend cascade absorption** (8 commits):
- `cda7a0c` — wave A3: cascade plan refresh (5 feature-progress groups A-E) + Pattern::Constructor rustdoc clarification
- `519ae91` → `2060ae7` — wave A4: 5 group commits absorbing 14 probe rows (newtype + span discipline; module visibility; macro lookup-shape; fused param tuple; trait/impl); 35 → 0 errors trajectory
- `a4fc9e0` — A5 follow-up: 7 stale doc-comments in expand.rs refreshed

**Phase B — Facade settlement + retirement** (7 commits):
- `5e20405` — foundation: 3 missing types authored (SymbolTables, ModuleAliasEntry, ModuleAliases) per 5th-lens configuration→source completeness sweep; D41 amendment (Option D refined — D41 #3 Introspection-direct-write retracted; CompilationArtifacts return + produce_disasm on-demand; FIXME 0221 closed by amendment)
- `ced64ab` → `f9ae663` — audit cascade: 6 commits actioning all 8 audit findings (F1+F2+F3 expand signature + typedef lift + Arc drop; F5 rustdoc refresh; H1+H2 S69 carries re-exports; S1 extract_module_declarations signature; S2 defmacro span wiring; F6 ExtractedDeclarations #[non_exhaustive]; clippy lint suppression)
- `49eb483` — facade retirement: `facades/frontend.md` deleted (252 LOC); narrative folded into `lib.rs //!` preamble + per-item `///` rustdoc + `bounded-contexts.md` §1; mirrors S69 Submission 42 for types; 23 cross-references swept

### Deferred (with rationale)

| Item | Severity | Target sprint | Rationale |
|---|---|---|---|
| **FIXME 0221** — backend D41 source rotation | Important | S71+ | Per facade-first-migration discipline; consumer-cascade wash-through model. Backend source still has pre-D41 signature; rotation owed in next backend-touching sprint. |
| **FIXME 0222** — typecheck cascade off S70 narrows | Important | S71+ | Same model. Typecheck currently at 282 errors (+5 above 277 pre-S70 baseline): 3 step-2-introduced sites (S35 invariant cascade) + 4 latent S35/S23 sites. Mechanical given S35 grounding. |
| **FIXME 0223** — facade-text staleness | Suggestion | Opportunistic | PrimitiveKind cited 4× across facades (retired S69 Sub 36); ConstructorInfo cited 1× (retired post-S69 ctor-as-Def cascade). Narrative drift, not contract drift. |
| **Phase 6 user-facing assessment** | Waived | N/A | Sprint touches no language-visible surface; user-proxy skills have no new behavior to validate. S69 + S65 + S63 precedent. |
| **FIXME 0175** — `cranelisp_frontend::expand` invocation gap | Open | When /arch arbitrates dep widening | #6 boundary cap held throughout S70 — expand body stays Gap-on-every-macro-head deferred-skeleton; module_aliases parameter is structural wiring; invocation path remains in src/expander.rs. /arch ruling on (a)/(b)/(c)/(d) dep widening still owed. |
| **Finding #6** — `Sexp::Comment` variant liveness | No-action | — | Per user direction. Variant may be aspirational reader-mode infrastructure; verification deferred to a future opportunistic trace. |

### Findings (methodology lessons + skill feedback)

**1. The 5th-lens audit methodology — configuration→source completeness.** Phase B introduced a new audit lens beyond S69's four (un-cascaded decisions in code; dead fields; struct-vs-rustdoc drift; D41-violation shapes). The 5th lens walks **configuration** (facades + BC + Decisions + Principles + per-crate design docs) and checks whether every named type identifier exists in source. This sweep caught 3 missing types (`SymbolTables`, `ModuleAliasEntry`, `ModuleAliases`) + 1 DAG-inversion question (`Introspection` placement) that the prior 4 lenses missed by construction (they walk source, not configuration). Worth codifying as a standing audit method.

**2. Facade-retirement-into-source-rustdoc — pattern stable at 2 data points.** S69 Submission 42 retired `facades/types.md` into `cranelisp-types/src/lib.rs //!` + per-item rustdoc + `bounded-contexts.md` §7. S70 Phase B B3-C retired `facades/frontend.md` into the parallel sites. The pattern is reproducible: cross-cutting overview → //! preamble; per-item commentary → /// rustdoc; cross-type narrative not fitting a single item → BC. 6 remaining crate facades can adopt the same retirement pattern when their respective audits complete.

**3. Configuration-grounds-the-facade discipline validated rigorously.** Every finding in the Phase B frontend audit cited at least one named Decision / Principle / BC / FIXME. Zero arbitrations. Zero facade-moves. The S69 calibration (arbitration count 24→2 once configuration fully loaded) repeated at Phase B (0 arbitrations from the start). The methodology holds: when configuration is canonical and grounded, dispositions emerge mechanically.

**4. Un-cascaded-Decision failure mode appeared in multiple forms.** Three instances surfaced this sprint:
- Rustdoc-vs-code drift: `DefKind::Macro` referenced at 8 rustdoc sites in cranelisp-types but missing from the enum (S69 narrative ruled the shape; variant addition never landed in code).
- Facade-target-stating without source landing: `SymbolTables`, `ModuleAliases`, `ModuleAliasEntry` named in BC §7 + frontend/int facades but absent from source.
- Decision-amended-without-source-rotation: D41 #3 (Introspection direct-write) committed in the Decision doc but never landed in source; created a DAG inversion the moment the audit walked it.

In each case, `feedback_decision_cascade_discipline.md` (the rule that Decision changes must cascade their source/facade/sequence updates in the same change-set) was the right diagnostic. The discipline survived the sprint stress-test; the lesson is reinforced.

**5. Plan-narrative-staleness as a failure mode.** The cascade plan's row #6 CRITICAL FINDING (claiming `DefKind::Macro` variant missing) persisted across 3 Phase 3 commits + Phase A entry because no one refreshed the plan after step 1 landed the variant. /arch's broad A3 review caught it. The lesson: when a step lands a change that affects an existing plan, the plan refresh is part of that step's commit. Worth a memory entry on plan-cascade discipline. The S69 Sub 42 precedent (types facade retired in same commit as the source rustdoc additions) is the model.

**6. "Settled with follow-up" verdict shape.** /arch's settled-verdict memo distinguished "types-crate is structurally complete for the work this sprint will do" from "every configuration-named question resolved." That distinction matters — it's the difference between blocking-on-perfection and shipping-with-named-follow-up. The shape was useful here (FIXME 0221's Introspection question was named follow-up, not blocker; resolved later in Phase B by the D41 amendment) and worth standardizing for future per-crate audits.

**7. /sprint orchestration data point — 18 agent fires across the sprint.** Multi-agent coordination worked. The single-session-with-multiple-commits pattern (A4 group execution; B3-B audit cascade) was particularly effective — one /dev agent works through a feature-progress sequence in one session, commits at each transition, reports observable progress (error-count drops). More efficient than per-group separate fires.

**8. User reflection on /arch's architectural principles.** Per /sprint Phase 7 discipline. The principles invoked this sprint (3 — DAG; 7 — single source of truth; 15 — facade types live with behavior; 17 — module locality; 18 — enforce invariants structurally) all performed well. No new principles surfaced as needed. No revisions to existing principles seem warranted. The placement heuristic (Principle 15 — multi-consumer types belong in cranelisp-types) was tested by ModuleAliases authoring and held. The facade-first-migration discipline (`feedback_facade_first_migration.md`) was tested by the B3-A→B3-B→B3-C arc and held — types moved first; consumers wash through in their own time; facade retires last.
