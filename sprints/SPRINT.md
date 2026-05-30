# Sprint 72: `cranelisp-typecheck` facade alignment + retirement

**Status**: PHASE 5 LANGUAGE (ACTIVE) — Wave 4 (Phase B close review)

**Goal**: Bring `cranelisp-typecheck` source into facade alignment, then fold `facades/typecheck.md` into typecheck rustdocs (4th data point on the facade-retirement pattern). Acceptance is `cargo check -p cranelisp-typecheck` green; workspace-wide green is **not** a S72 acceptance criterion.

## Scope

Three stacked deliverables, all within the typecheck crate edge. Pipeline order has frontend done S70 → **typecheck this sprint** → backend/intrinsics/primitives/int still owing their own audits in later sprints.

**Load-bearing surfaces today**: `cranelisp-types` (S69), `cranelisp-frontend` (S70), `cranelisp-platform` (S71). Everything else — backend, typecheck consumers, int — can still slip. S72 makes typecheck the 4th load-bearing surface.

### A. Absorb the types changes (FIXME 0222 + cascade-to-typecheck-green)

Drain the typecheck cascade left by S70's types-side narrows. Named scope: 7 sites in `traits.rs:1354/1361`, `program.rs:1637`, `adt.rs:278/377`, `checker.rs:588/682` — but the S70 pre-baseline was already at 277 errors before the +5 step-2 additions. Phase A walks every typecheck-internal cascade error to ground.

Acceptance: `cargo check -p cranelisp-typecheck` clean. **Workspace-wide green is explicitly NOT in scope** — downstream consumers (backend, int) still owe their own cascade work in later sprints and stay red until then.

The S35 invariant (metadata canonical on parent `ModuleEntry::Def`, payload-only on inner `DefnVariant`) is the load-bearing principle for the 7 named sites; the broader cascade may surface additional invariants — `/arch` arbitrates as they emerge.

**Decision-class checkpoint** (per `/arch` Phase 2 revision 1, amended by user 2026-05-28): when the walk surfaces a *non-mechanical* invariant — i.e., facade-vs-source ambiguity, new boundary type, sealed-trait change, FQTypeName boundary movement, etc. — `/dev typecheck` pauses and **`/sprint` surfaces the issue to the user for arbitration**. User personally reviews facade-related problems until confident the pattern is stable. `/arch` is consulted only if user routes the question to it. Mechanical cascade (S35/S23 invariant applications) does NOT trigger the checkpoint.

### B. Align typecheck source to `facades/typecheck.md`

`facades/typecheck.md` is the binding contract (`feedback_hold_to_facade_default`, `feedback_facade_first_migration`). 5-lens audit (per `feedback_audit_5th_lens_completeness`) walks facade-vs-source. Default disposition is **source moves** to match facade; facade-moves are exception-only (retracted/sloppy/evolved-past) and require explicit Decision-style arbitration.

Acceptance: every audit finding dispositioned; source aligned; `cargo check -p cranelisp-typecheck` still green after the alignment edits.

### C. Fold the facade into typecheck rustdocs (retirement, 4th data point)

After source-facade alignment is achieved. Per `/arch` Phase 2 revision 2, the facade text **partitions explicitly** between two destinations:

- **Source rustdoc** (`crates/cranelisp-typecheck/src/lib.rs` `//!` preamble + per-item `///` on every public item) absorbs: contract, types-originated-here, per-item invariants, per-item rustdoc narrative. Becomes canonical surface for typecheck.
- **`bounded-contexts.md §2`** absorbs: cross-surface narrative, invariants 1–10, module-locality rationale (Principle 17 + Decision 0045 grounding) — the *what crosses the boundary and why the boundary lies here* layer.
- Per-crate `design/typecheck/typecheck.md` is **NOT** a retirement target — it stays `/design`'s interior-design doc (how the inference engine, traits resolution, monomorphisation are organized inside the crate), untouched by retirement. Splitting cross-surface narrative into a per-crate design doc would dilute the canonical doc set and break the 5th-lens audit invariant.

Then:

- Cross-references updated across canonical doc set.
- `design/arch/CLAUDE.md` exception list extended to 4 retired facades (types S69 §7, frontend S70 §1, platform S71 §5, typecheck S72 §2).
- `cargo public-api -p cranelisp-typecheck` baseline regenerated; every baseline line named in lib.rs preamble or per-item rustdoc.
- **Facade compliance test** (S67 W0) passes against the new edge.
- `facades/typecheck.md` git-rm'd.

### Out of scope (deferred)

- **Workspace-wide green** — backend, int, and other consumer crates stay red. Their cascade work belongs to their own audit sprints.
- **Host-wiring sprint** (FIXMEs 0229–0235, platform-redesign follow-on) — S73 candidate.
- **Backend audit + FIXME 0221 (D41 rotation)** — same audit-and-retire treatment for the backend crate; S73 or S74 candidate.
- **Intrinsics / primitives / int facade audits** — same pattern; later sprints.
- **`/qa` conformance-triad-enhancement** (FIXMEs 0218 + 0224–0228) — separate sprint.
- **Concurrency carries** (S62 deferrals) — still queued behind facade arc.

## FIXME debt

Triage list refined by `/arch` Phase 2 revision 3.

| FIXME | Target | Filed | Status | Disposition this sprint |
|---|---|---|---|---|
| 0222 | /dev typecheck | S70 | open | **In scope — Phase A primary driver.** S70 types-cascade absorption. |
| 0173 | /dev typecheck | — | open | **In scope — Phase B.** `CheckPass` removal + `ModuleCheckAccumulator` relocation; facade already target-states D44 third amendment, so this closes as Phase B alignment lands. |
| 0177 | /typecheck | S66 | open | **In scope — Phase A.** `check_forms` cross-form state regression; likely closes during cluster-mode shape settling. |
| 0179 | /typecheck | S66 | open | **In scope — Phase A/B.** Cluster-mode union-read follow-up to D44/W3b-2c.1. |
| 0172 | /typecheck bootstrap | — | open | **In scope — Phase B if narrowing lands.** Eliminate short-name fallback chains in `defining_module_for`; facade names this as Wave 3 narrowing target. Defer if Phase B doesn't reach it. |
| 0098 | /dev frontend+typecheck+int | S65 | open | **Triage only — handoff to host-wiring sprint (S73).** ResolutionGap/CheckError/ExpansionError migration is cross-crate; surface if Phase B alignment forces movement, otherwise defer. |
| 0033 | /typecheck | — | open | **Triage — may resolve mechanically during Phase A.** Monodefn redundant side maps. |
| 0187 | /int | S66 | open | Out of scope unless Phase A boundary forces it. |
| 0188 | /qa | S66 | open | Out of scope. |
| 0231 | /typecheck | S71 | open | Out of scope — sig typechecking entry is host-wiring sprint (S73). |
| 0226 | /qa | S71 | open | Out of scope. |
| 0151 | retired | S65 | closed S68 | Reference only — FQTypeName completion precedent. |
| Newly-filed | — | S72 | — | Decision-class arbitrations surfaced during Phase A walk → file forward per safety-valve checkpoint. |

## Architecture review (Phase 2)

**Verdict**: APPROVE-WITH-REVISIONS (2026-05-28).

The DRAFT is technically coherent and pointed at canonical target state. No interim-architecture risk (Principle 8). Three revisions applied above:

1. **Phase A boundary** — added explicit Decision-class checkpoint as safety valve against unbounded cascade-walk slide. Mechanical S35/S23 invariant applications continue uninterrupted; Decision-class arbitrations pause and route through `/arch` + `/sprint`.
2. **Phase C migration partition** — explicitly stated split: contract + per-item invariants → lib.rs `//!` + per-item `///`; cross-surface narrative + invariants 1–10 + module-locality rationale → `bounded-contexts.md §2`. Per-crate `design/typecheck/typecheck.md` stays interior-only and is NOT a retirement target.
3. **FIXME triage** — added 0173, 0177, 0179, 0172, 0033 with dispositions; 0098 marked triage-only with handoff to host-wiring sprint (S73).

### `/arch` arbitration answers (preserved for design phase)

- **Q1 Technical coherence**: A → B → C ordering correct. A precedes B because audit needs stable source; B precedes C because folded facade text must match what got built.
- **Q2 Cascade-width**: `/arch` will arbitrate during walk per revision-1 checkpoint. `cargo check -p cranelisp-typecheck` green is right acceptance gate.
- **Q3 Source-vs-facade threshold**: default flip correct (source-moves-to-facade). Facade is target-stating (385 LOC, four major invariant sections, deeply grounded in D44/0045/0046/0047/0048). Sections expected to hold facade-side: invariant 10 (module-locality, Principle 17 + D45), `check_forms` signature (D44 third amendment), `TypeCheckEnv` narrowing target (≥28 methods drop to `pub(crate)` per S67 PIF row 21). Sections to re-validate during 5-lens audit: `register_imports`/`register_exports` free-fn shape (S67 hack-back from FIXME 0192 — may have evolved); trace hook surface (verify `cranelisp-int` actually installs); two legacy crate-root re-exports marked for housekeeping removal.
- **Q4 Migration site**: BC §2 only — see revision 2.
- **Q5 Public-API**: `crates/cranelisp-typecheck/public-api.txt` confirmed as contract-update site; facade compliance test (S67 W0) anchors on it; Phase C acceptance requires (a) regen, (b) every baseline line in rustdoc, (c) compliance test green.
- **Q6 FIXME triage**: see revised table above.
- **Q7 Principle 8**: no interim-architecture commitments in DRAFT; only Principle-8-adjacent risk is emergent-invariant-during-Phase-A, mitigated by revision 1.

## Skill plans (Phase 3)

### Sprint-open ground truth (verified 2026-05-28 via `cargo check -p cranelisp-typecheck`)

- **284 errors** at S72 open — +2 above S70 close baseline (282) per FIXME 0222. Pre-step-2 baseline was 277. Cascade is wider than 0222's named 7 sites.
- Distribution: `traits.rs` 106 / `program.rs` 84 / `builtins.rs` 65 / `checker.rs` 42 / `infer.rs` 13 / `adt.rs` 7 / `resolve.rs` 5 / other 14.
- 20 mechanical-with-precedent edit categories identified (C-1 through C-20) — see `/design typecheck` Phase A plan (preserved as response artefact).

### `/design typecheck` — Phase 3 plan (returned 2026-05-28)

**Phase A (cascade absorption) — ordered 8-step work plan** for `/dev typecheck`:

1. **A.4.1 Imports** (5 min) — fix `program.rs:34` + `builtins.rs:28`. Unblocks downstream.
2. **A.4.2 builtins.rs sweep** (~65 errors) — drop `primitive_kind`/`jit_name`; `Scheme.vars` → `type_vars`; add `seq`/`visibility` fields.
3. **A.4.3 adt.rs sweep** (~7 errors) — `ModuleEntry::Constructor` → `Def { kind: DefKind::Constructor }`. Touches FIXME-0222 sites 278+377.
4. **A.4.4 checker.rs sweep** (~42 errors) — `param_annotations` retired (fused-tuple rewrite); add `seq`/`visibility`. Touches FIXME-0222 sites 588+682.
5. **A.4.5 traits.rs sweep** (~106 errors) — `MethodResolutions` struct (was HashMap); `TraitImpl.target_type` → `target`; `TypeRef` accessor. Touches FIXME-0222 sites 1354+1361.
6. **A.4.6 program.rs sweep** (~84 errors) — `ModuleEntry::Reexport` retired; `Expr::ConstrADT` match arm; `DefKind::SpecialForm` → `ModuleEntry::SpecialForm`. Touches FIXME-0222 site 1637.
7. **A.4.7 infer.rs + resolve.rs tail** (~18 errors) — secondary cascade fallout.
8. **A.4.8 Verify green** — `cargo check -p cranelisp-typecheck` returns 0 errors.

**Decision-class checkpoint triggers identified**: `Expr::ConstrADT` typing rule wiring; builtin registration source (`cranelisp_types::primitives()` aggregate); `MethodResolutions::pattern_ctors` population at write sites; `TypeRef` vs `TypeName` confusion at resolved-stage boundaries.

**Phase B (5-lens audit)**: walk every section of `facades/typecheck.md`. 10 facade sections to re-validate; predicted dispositions captured per-section. FIXMEs expected to close: 0173 (CheckPass retirement), 0179 (cluster-mode union-read), 0033 (MonoDefn side maps), 0172 (short-name fallback chains, conditional on FIXME 0187 status). 0177 escalates to Decision-class if still failing post-Phase-A.

**Phase C (retirement)**: facade text partitions across 14 sections; ~41 public items need `///` rustdoc; ~12 cross-reference sweep targets identified; per-item rustdoc structure mirrors S69/S70/S71. Per-crate `design/typecheck/typecheck.md` NOT touched.

### `/qa` — Phase 3 test plan (returned 2026-05-28)

**Phase A regression-risk triage**: 7 categories assessed. Low-risk: S35 metadata rerouting, Scheme rename, `seq` field add. **High-risk**: `MethodResolutions` API loss at 18 sites (likely Decision-class trigger). **Medium-risk**: `Expr::ConstrADT` non-exhaustive at `program.rs:128` + `:2719` — if resolved with `todo!()` shims, ADT construction compiles but runtime-fails. **Latent-risk**: `Reexport` → `Import + Visibility::Public` collapse — chain-follow semantics may shift; 21 sites.

3 candidate PLAN rows (R-S72-A1/A2/A3) authored only if Phase A walk surfaces real defects.

**Phase B audit-surfaced**: 5 surfaces named for re-validation (per `/arch` Q3). Test shape proposed for each; rows added only if drift is behaviour-level.

**Phase C facade compliance — clarified by user 2026-05-28**: The text-grep mechanism in `tests/facade_compliance.rs` is the wrong abstraction post-retirement — there's nothing to grep against once a facade file is gone (per S69/S70/S71). The right discipline going forward is **baseline-diff between `cargo public-api` runs** — emergent diffs surface for review. Re-anchoring the compliance test is NOT in S72 scope. The S69/S70/S71 broken-test condition is a separate problem, outside this sprint.

**S72 Phase C scope (corrected)**: conform typecheck source to `facades/typecheck.md` first; resolve all issues against the facade; THEN fold `facades/typecheck.md` into source rustdoc + BC §2. The `cargo public-api` baseline regen at Phase C close is the only public-surface contract artefact. No compliance-test re-anchor work in this sprint.

**Test discipline**: failing-not-ignored for behaviour-level defects; `/dev typecheck` writes unit tests in `crates/cranelisp-typecheck/src/`; `/qa` writes e2e in `tests/`; cross-skill handoffs require minimal repro per `feedback_cross_skill_minimal_repro`.

### Expected Phase 5 invocations

- `/dev typecheck` — Phase A cascade drain (8 sub-waves per /design plan); Phase B source-alignment edits; Phase C rustdoc authoring + cross-ref sweep + facade git-rm + `cargo public-api` baseline regen.
- `/review typecheck` — change-set review at Phase A close + Phase B close + Phase C close (3 fires).
- `/qa` — Phase A defect repros (if any behaviour-level defect surfaces); Phase B drift tests (if any surface). **No compliance-test re-anchor work in this sprint** — separate problem, outside S72 scope.
- **User arbitration** — replaces /arch Phase A safety-valve fire; user reviews facade-related problems until confident the pattern is stable.

User-proxy skills (Phase 6): waived (no language-visible surface change). `cargo public-api -p cranelisp-typecheck` baseline diff is the Phase 6 contract artefact.

## Waves (Phase 4)

Six sequential waves. Phase 3's QA-first sprint-wide stage (METHOD §2.5 Stage 1) is **abbreviated** this sprint: no failing-spec-surface tests authored up-front because the work is build-recovery + structural narrowing, not new feature coverage. Tests land in-line as Phase A/B surface defects (per `/qa` Phase 3 plan).

### Wave 1 — Phase A cascade absorption (/dev typecheck)

`/dev typecheck` executes /design's 8-step plan as one fire with 8 sub-checkpoints. Pauses at any Decision-class surface; user arbitrates.

| Step | Files | Errors expected to drain | FIXME(s) closing |
|---|---|---|---|
| 1.1 Imports | program.rs:34, builtins.rs:28 | unblocks rest | — |
| 1.2 builtins.rs sweep | builtins.rs | ~65 | — |
| 1.3 adt.rs sweep | adt.rs | ~7 | partial 0222 (lines 278+377) |
| 1.4 checker.rs sweep | checker.rs | ~42 | partial 0222 (lines 588+682); 0177 (likely) |
| 1.5 traits.rs sweep | traits.rs | ~106 | partial 0222 (lines 1354+1361) |
| 1.6 program.rs sweep | program.rs | ~84 | partial 0222 (line 1637); 0179 (likely) |
| 1.7 infer.rs + resolve.rs tail | infer.rs, resolve.rs | ~18 | 0033 (likely) |
| 1.8 Verify green | (all) | 0 | **0222 full close** |

**Acceptance**: `cargo check -p cranelisp-typecheck` returns 0 errors; `cargo nextest run -p cranelisp-typecheck` no new failures.

### Wave 2 — Phase A close review (/review typecheck)

`/review typecheck` reviews Wave 1 change-set: blocker findings, important findings, structural debts. Verdict gates Wave 3.

### Wave 3 — Phase B 5-lens audit + source-alignment (/design + /dev typecheck)

Two-step:

- **3a** — `/design typecheck` runs 5-lens audit of `facades/typecheck.md` vs. post-Wave-1 source. Authors per-finding disposition list (5-block template); source-moves default per `feedback_hold_to_facade_default`. Predicted FIXMEs closing: 0173, 0172 (conditional). 0177 escalates to user if still failing.
- **3b** — `/dev typecheck` applies source-moves dispositions. Each cluster of related edits followed by `cargo check -p cranelisp-typecheck` to stay green.

**Acceptance**: every finding dispositioned; `cargo check -p cranelisp-typecheck` still green; FIXMEs 0173/0172 closed if reached.

### Wave 4 — Phase B close review (/review typecheck)

`/review typecheck` reviews Wave 3 change-set. Verdict gates Wave 5.

### Wave 5 — Phase C retirement (/dev + /design typecheck)

Single coordinated fold:

- **5a** — `/dev typecheck` authors `crates/cranelisp-typecheck/src/lib.rs` `//!` preamble + per-item `///` on ~41 public items (folds facade contract + per-item invariants).
- **5b** — `/design typecheck` migrates cross-surface narrative + invariants 1–10 + module-locality rationale to `bounded-contexts.md §2`.
- **5c** — `/dev typecheck` runs `cargo public-api -p cranelisp-typecheck` → regenerates `crates/cranelisp-typecheck/public-api.txt` baseline. Verifies every baseline line is named in lib.rs `//!` or per-item `///`.
- **5d** — Cross-reference sweep across ~12 files cited by `/design` (interfaces.md, arch/CLAUDE.md, cranelisp-types-settled-verdict-s70.md, design/frontend/wave-3a-build-form.md, design/platform/implementation-slice-s66.md, design/int/int.md, design/int/implementation-slice-s66.md, tests/facade_compliance.rs cite-only). `design/typecheck/typecheck.md` NOT touched.
- **5e** — `design/arch/CLAUDE.md` exception list extended (4th retired facade).
- **5f** — `facades/typecheck.md` git-rm.

**Acceptance**: facade file deleted; baseline regenerated; cross-refs swept; check still green.

### Wave 6 — Phase C close review (/review typecheck)

Final PASS gate. `/review typecheck` reviews Wave 5 change-set against the new edge (lib.rs rustdoc + BC §2 + public-api.txt). Verdict gates Phase 7 close.

### Inter-wave protocol

- **Decision-class arbitration**: any wave that surfaces a facade-related ambiguity or non-mechanical boundary question pauses, `/sprint` surfaces to user, user arbitrates. /arch consulted only if user routes.
- **/qa interleave**: any defect-class repro surfaced during Wave 1 or 3 produces a committed failing-not-ignored test in `tests/` (e2e by /qa) or `crates/cranelisp-typecheck/src/` (unit by /dev typecheck). Per `feedback_repros_join_suite`.
- **Forbidden git ops**: every agent prompt repeats the standard list (`git stash drop`, `git stash clear`, `git reset --hard`, `git checkout --`, `git restore`, `git clean -f`, `git clean -fd`).

## Notes

- 2026-05-28: Sprint opened by `/sprint` after user request "what module can we flow through next?". Choice arbitrated to typecheck on pipeline-order grounds.
- 2026-05-28: User clarified scope — only types/frontend/platform are load-bearing today; S72 acceptance is `cargo check -p cranelisp-typecheck` green, NOT workspace-wide green. Phases A → B → C (absorb cascade, align source to facade, fold facade into rustdocs).
- 2026-05-28: `/arch` Phase 2 verdict APPROVE-WITH-REVISIONS; 3 revisions applied (Phase A boundary checkpoint, Phase C migration partition, FIXME triage expansion).
- 4th data point on the facade-retirement pattern (types S69 §7 → frontend S70 §1 → platform S71 §5 → typecheck S72 §2). If the pattern holds, it's stable; if it strains here, lesson captured.
- 2026-05-29: Wave 1 fired. 4 Decision-class triggers surfaced and user-arbitrated: (T1) delete `register_primitives` flow per D48; (T2) extract shared `instantiate_ctor` helper for both `Pattern::Constructor` and `Expr::ConstrADT`; (T3) populate `MethodResolutions.pattern_ctors` at the shared site; (T4) `param_annotations` cascade mechanical. Wave 1 close: lib + tests build GREEN; FIXMEs 0222, 0177, 0179, 0033 closed.
- 2026-05-30: Wave 1 tail/fixture work surfaced **structural Phase B scope**: `Int`/`Float`/`Bool`/`String` are dual-represented (`Type::Int` variant AND `ModuleEntry::TypeDef` for `primitives/Int`); `fqtn_for_bare_type_name` has a hard-coded primitive-type-name fallback that bypasses the symbol table — parallel to the `defining_module_for` smell already cleaned up for traits at S67. **Phase B activates the dormant `ModuleEntry::IntrinsicType { ty: Type }` variant (S69 Sub 30)** as the name-resolution entry for built-in scalars; deletes `fqtn_for_bare_type_name`'s hard-coded fallback; routes all type-name lookups through the symbol table uniformly. Per user two-orthogonal-dimensions model: **provenance** (which module: `primitives` vs user) × **kind/shape** (which `ModuleEntry` variant: `IntrinsicType` vs `TypeDef` vs `TraitDecl`). 26 failing-not-ignored tests at Wave 1 close are Phase B's acceptance spec.
- 2026-05-30: Wave 2 /review verdict PASS-WITH-FINDINGS (0 Blocker, 4 Important, 5 Suggestion). Important findings resolved in close-out: **I-1** FIXME bookkeeping (0222/0177/0179 closed via integration repros + `git rm`; 0033 confirmed open as Phase B target); **I-2** facade refresh — `ClusterRead`/`ClusterWrite` renamed to `SymbolTableRead`/`SymbolTableMut`; interior `pub(crate)` parallel pair retired (`ClusterContext::Cluster::staging` adopts `RefCell<&'a mut SymbolTable>` to preserve single-pair invariant); **I-3** oracle gap deferred via newly-filed FIXME 0239 (/arch — generalized "instantiate module symbol table from source" facade concept); **I-4** module tightening — `pub mod builtins`/`pub mod trace` → private; crate-root re-exports preserved. Wave 2 close: public-api.txt regenerated (-81/+156 lines); `cargo check -p cranelisp-typecheck` + `--tests` GREEN; 320 pass / 26 fail; new integration tests `regression_0177_*` + `regression_0179_*` committed.
- 2026-05-30: Wave 3a /design typecheck authored `design/typecheck/phase-b-plan.md` (Parts 1–8). User-ratified expanded scope: Part 1 IntrinsicType activation (4 scalars Int/Bool/Float/String); Part 2 + 2b + 5 coherent refactor (fqtn fallback delete + Tier 2 universe walk delete + naming unification `trait_home_for`/`fqtn_*`/`lookup_constructor_type*` → `resolve_trait`/`resolve_type`/`resolve_constructor` returning `Result<T, ResolveError>` with 5-variant enum incl. `PrivateInaccessible`); Part 3 MonoDefn side-map stop; Part 4 5-lens audit source-moves; Part 7 FIXME closures. User personally arbitrated A3 facade pushback (rejected /design's "no-change" — universe walk gratuitous, deleted).
- 2026-05-30: Wave 3b /dev typecheck executed Parts 1, 2, 2b, 3, 4 (A7 only; A1/A4 deferred via newly-filed FIXME 0240 for cross-crate `module_aliases` threading), 5, 7. **All 26 IntrinsicType cluster failures resolved.** Final: **346 pass / 0 fail / 0 skip**. public-api.txt regenerated (+308/−81; ResolveError appears; A7 `TypeCheckEnv::current_symbol_table[_mut]` promoted to `pub`). FIXMEs deleted: 0173. FIXMEs updated with status notes (typecheck-internal portion closed; awaits cross-crate): 0172, 0098. FIXME filed: 0240 (/arch — facade rename cascade for resolve_* family + A1/A4 module_aliases threading coordination).

## Outcome (Phase 7)

To be filled at close.
