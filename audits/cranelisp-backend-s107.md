# cranelisp-backend — S107 Whole-Context Assessment

> **Cycle.** Inaugural in-rotation `/audit` assessment (`sprints/artefacts.md` §I.7,
> instantiated §II.1; rotation riskiest-first, backend first). Dated 2026-07-11,
> between sprints, immediately after S107 close. Disposed at S108 Phase 1.
>
> **Predecessors.** `audits/cranelisp-backend-s87.md` (2026-06-20, Stage-B deep
> audit) refreshing `audits/backend-20260423.md`. Both predate the acceptance-trail
> protocol — no disposition sections exist; §1 below reconstructs the trail from
> `sprints/archive/sprint-87.md` and the live source.
>
> **Scope note.** The crate's source has been quiescent for two sprints: the last
> source commit is `3e923dc7` (2026-07-07, S105 Wave 0 instrumentation); S106/S107
> did not touch it. This assessment therefore evaluates the S103–S105
> ownership/perf arc's end-state plus everything older. `crates/cranelisp-backend/CLAUDE.md`
> was seeded 2026-07-11 (untracked at audit time) and is per dispatch NOT assessed
> for staleness; spot-checks of its claims against code are recorded in §2.6.
>
> **Method.** Read-only. Evidence gathered from source (`crates/cranelisp-backend/`),
> `design/backend/`, `design/arch/fixmes/`, `tests/plan/ledger.md`,
> `sprints/archive/sprint-{87,100..107}.md`, and a scripted >100-line function
> census over non-test sources. No build or test run (tree shared with a
> concurrent seeding chain, per dispatch).

Crate size at HEAD: 38,433 lines of `.rs` under `src/` + `tests/`; ~14.1k in
dedicated test-sibling files plus ~2–3k in inline `#[cfg(test)]` mods →
production code ≈ 21–22k lines across `compiler/` (hub-and-submodule),
`cache/`, `heap.rs`, `jit.rs`, `exe.rs`, `schema.rs`, and support modules.

---

## 1. Baseline reconciliation — the S87 findings, three weeks on

The S87 audit closed with 12 findings; sprint-87's synthesis filed FIXMEs for
three (0417, 0419, 0420 — `sprints/archive/sprint-87.md` line 350) and executed
several more as in-sprint hygiene. Reconstructed trail:

| S87 finding | Status now | Evidence |
|---|---|---|
| **F1** two `build_isa` helpers | **STILL OPEN — third consecutive audit** | `jit.rs:49` (`pub(crate) fn build_isa()`, hardcodes `is_pic=false`) vs `cache/object.rs:144` (`build_isa(is_pic: bool)`); bodies identical modulo the parameter. Both claim primacy: `jit.rs:46-48` "Single construction point for the entire backend" vs `cache/object.rs:140` "Single ISA construction point (architecture decision 7)" and `lib.rs:32-33`/`cache/object.rs:10-11` "the **single** ISA construction point". Named in the S87 synthesis (T6) but never filed; no change landed. |
| **F2** `Jit::compile_defn`/`build_compile_context`/`CompileArtifacts` dead-in-prod; eager disasm survives | **STILL OPEN** | `jit.rs:587` (`compile_defn`), `jit.rs:712` (`build_compile_context`), `jit.rs:35` (`CompileArtifacts` with `disasm` field). Every caller is a test (`module_assembly_tests.rs:362`, `compiler/control_flow/{launch.rs:387 (in #[cfg(test)] mod at :263), par_codegen_tests.rs:57/:117, poll_codegen_tests.rs:115, select_codegen_tests.rs:79}`, `compiler/vec_codegen/temp_drop_rc_tests.rs:56`, `jit/tests.rs:177/:374`). `jit.rs:650` still `set_disasm(true)` unconditionally — the eager-disasm capture the D1b ruling + FIXME 0418 retired int-side survives here. `design/backend/implementation-slice-s66.md` row 1 acceptance criterion (d) — "`Jit::compile_defn` deletion observed in source" — was never met. |
| **F3** vec-set/vec-push consuming-inc asymmetry | **RESOLVED** (S87 W5, FIXME 0417, commit `88a9e0c4`) | `vec_codegen.rs:284` rustdoc: "`vec_set_copy` does NOT inc the new `val`"; `emit_vec_set_copy_temp_compensation` gone from source. Guard tests live at `compiler/vec_codegen/{vec_set_rc_tests,cow_polarity_tests}.rs`. |
| **F4** functions over ~100-line budget | **PARTLY — worst offender grew again** | See §2.1 census. `compile_resolved_call` 153 (04-23) → 271 (S87) → **323** (`apply.rs:417`). |
| **F5** `emit_extern_call_1..4` arity ladder | **RESOLVED** (S87, commit `80b16f05`) | Consolidated into `compiler/extern_call.rs` (262 lines, one slice-based helper + tests). |
| **F6** vec COW skeleton clone (2 sites) | Residual, low | `compile_vec_set` (`vec_codegen.rs:290`) / `compile_vec_push` (`vec_codegen.rs:372`) still separate but both shrank post-0417; S87 already rated this Suggestion at the 2-site threshold. No recommendation this cycle. |
| **F7** cache-layer "Wave 2b" migration residue | **STILL OPEN — third consecutive audit, rationale now vacuous** | See R2 evidence in §3. |
| **F8** `exe.rs` stale `#[allow(dead_code)]` + "currently red, re-wires S77" | **STILL OPEN** | `exe.rs:72-77` comment + attr unchanged; the function is live — called via `src/exe.rs:50` re-export from `src/session_v4/lifecycle.rs:1964`. Fifteen sprints stale. |
| **F9** `FunctionArtifacts` survives though design claims deletion | **STILL OPEN** | `lib.rs:267` (`pub(crate) struct FunctionArtifacts`), returned by `compile_defn_in_module` (`lib.rs:1588,1642`). `design/backend/backend.md:83` and `design/backend/compile-to-module.md:47` both state `CompilationResult` + `FunctionArtifacts` are "DELETED" per the D41 rotation — half true (`CompilationResult` is gone). |
| **F10** host-callback lens: backend clean | Unchanged; re-verified not re-litigated. Model-B question closed definitively since (effect-concurrency.md §12.1 retired FIXME 0407). |
| **F11** twin symbol-table walkers | **RESOLVED** (S87 W5b) | `compiler/resolution.rs:1-10` rustdoc: all four resolvers share `resolve_chain` (`resolution.rs:82`) + `resolve_driven`, "each resolver supplies only its terminal `read` closure (P7 …; audit F11)". |
| **F12** `lib.rs` test warehouse; `literals`/`match_codegen` untested | **RESOLVED** (S101, FIXME 0495, commits `42fc3a2d`/`98982fd1`) | Flat crate-root `tests.rs` (5,861 lines at S101) no longer exists; 25+ per-submodule test siblings (`heap/tests.rs`, `cache/linker/tests.rs`, `compiler/resolution/tests.rs`, topical `*_tests.rs` …); `compiler/literals.rs:429` and `compiler/match_codegen.rs:666` now carry local test mods. `lib.rs` is 1,742 lines total. |

**Scorecard: 5 resolved, 2 partial/residual, 5 still open.** The pattern in the
open five is uniform: everything the S87 synthesis converted into a FIXME or an
in-sprint work item landed; everything left as prose in the assessment did not.
That is precisely the gap the §I.7 acceptance protocol (this cycle onward) exists
to close — each §3 recommendation below either gets a FIXME at S108 Phase 1 or an
explicit decline on the record.

---

## 2. Current state by quality attribute

### 2.1 Simplicity

**Structure is good and holding.** The S87 W5b decomposition survived intact:
`compiler/mod.rs` is a 90-line hub, `compiler/control_flow.rs` a 71-line hub;
codegen concerns live in per-concern submodules (`apply`, `fn_compiler`,
`resolution`, `extern_call`, `rc_emission`, `literals`, `match_codegen`,
`trace_codegen`, `vec_codegen`, `control_flow/{let_if,par_bind,lambda,fn_as_value,
sparkability,launch,select,utilization,…}`). No dead production entry points of
the `compile_to_object`-stub class were found.

**Function-level complexity is re-accreting where the work happened.** Census of
non-test functions ≥100 lines (brace-counting script over `src/`, test files and
`#[cfg(test)]` regions excluded where separable): ~30 functions, topped by:

| Lines | Function | Location |
|---|---|---|
| 373 | `compile_to_module_impl` | `lib.rs:780` |
| 323 | `compile_resolved_call` | `compiler/apply.rs:417` |
| 270 | `generate_startup_object_checked` | `exe.rs:121` |
| 235 | `Linker::load_object` | `cache/linker.rs:229` |
| 209 | `compile_trace` | `compiler/trace_codegen.rs:691` |
| 191 | `compile_apply` | `compiler/apply.rs:154` |
| 179 | `compile_lambda_body` | `compiler/control_flow/lambda.rs:372` |

`compiler/apply.rs` is now the crate's largest module (2,210 lines) and carries
five of the >100-line functions (`compile_resolved_call` 323, `compile_apply`
191, `compile_direct_call` 119 at `apply.rs:1100`, `compile_poll_effect` 112 at
`apply.rs:1363`, `compile_consuming_arg_list_moded` 112 at `apply.rs:955`) —
the S100–S105 ownership-modes work (B3.2 moded args, fault-guard funnel, poll
effects) all landed into the same dispatch bodies. `compile_resolved_call` has
now grown across three consecutive audits while being named in each.

### 2.2 Maintainability

**Seams and naming are strong.** The resolution seam is exemplary post-F11
(`resolution.rs` module rustdoc names the one walker + one driver and cites the
audit finding). `heap.rs` remains the sole importer of cross-crate layout
constants with `const _: () = assert!(…)` offset pins. Env gates are uniformly
`OnceLock`-memoized, documented byte-identical-off, with provenance rustdoc.

**Comment honesty has localized failures.** Three classes found:
- Mutually contradictory single-source claims on the two `build_isa`s (§1 F1).
- Transient-state comments documenting states 15+ sprints dead: `exe.rs:72-77`
  ("currently red post-W2/W3; re-wires S77" + `#[allow(dead_code)]` on a live
  function called from `src/session_v4/lifecycle.rs:1964`).
- "Temporary" markers with no live referent: `cache/serialize.rs:319-338` and
  `cache/mod.rs:324-325` say shims exist "so that pre-Phase-5 callers in
  `/int`-owned code continue to compile during the Wave 2b parallel migration" —
  a workspace grep finds **zero** consumers of `CacheMetadata`,
  `cranelisp_backend::got::`, or `cranelisp_backend::codegen_types::` outside the
  backend crate itself (sole external hit: a comment in
  `crates/cranelisp-types/src/pipeline.rs:34`).

**Unsafe usage** is confined and conventional: test-side `transmute`-to-fn-ptr
harnesses, `Send`/`Sync` impls on `Code` (`code.rs:107-108`), `GotEvent`
(`got_observer.rs:118-119`), `LinkerArtefact` (`artefact.rs:70-71`), and
intrinsics string reads — each adjacent to a justifying comment. One latent
release-mode UB hazard is documented but unresolved (see R7): GOT slot
allocation is unchecked (`cranelisp-types/src/module.rs:609-613` monotone
`+= 1`; `cranelisp-types/src/got.rs:135-150` `debug_assert!` only), with
`got.rs:26-30` (backend) explicitly recording "in release, slot 1024 would
index out of bounds (UB)" and noting ABI-epoch fresh-slot churn (S101 R3
machinery, now live) accelerates approach to the bound.

### 2.3 Duplication

The two S87 duplication families that were consolidated (extern-call ladder,
import-chain walkers) have stayed consolidated — no re-cloning observed.

**One whole-context mirror family remains, and its defect class has now bitten
twice.** Three drop-glue builders share one skeleton (filter heap-categorized
captures → early-return `None` → span+discriminator-keyed name → idempotency
skip → per-capture dec body): `build_closure_drop_glue`
(`compiler/control_flow/lambda.rs:187`), `build_auto_curry_drop_glue`
(`compiler/control_flow/fn_as_value.rs:938`), `build_adt_drop_glue_fn`
(`compiler/vec_codegen.rs:769`). The naming/identity discipline (fold
`inner_fn_discriminator()` into the glue name, never span alone) and the
declare-idempotent/define-once discipline are re-stated per site — and the
identity half has produced two separate defects on two different mirrors:
FIXME 0350 (closure glue collision under monomorphisation, per the
`lambda.rs:228-237` comment) and ledger item 25 (`curry_drop_glue_{span}`
collision, `tests/plan/ledger.md:188`, fixed S102 B3.1). The fix comments
cross-reference each other as "precedent" (`fn_as_value.rs:975-985`) — the
textbook P7/P8 signal that the discipline wants one home, per the standing
`/review` root-cause-and-duplication feedback.

The `build_isa` pair (§1 F1) is the other live duplication — trivial but now
the longest-standing named finding in the crate.

### 2.4 Design realisation

**Recent design is well realised.** The S100 `design/backend/ownership-codegen.md`
(refreshed 2026-07-07) tracks the landed increments (B3.2 borrow-elision modes,
B3.3 confined non-atomic RC, B3.4 stack-alloc via gate 5, B2 reuse tokens, H2
per-mechanism RC_STATS with grammar pinned §13.2.1); `lenient-eval.md` and
`ring2-rc.md` were maintained through S103–S105. The S103–S105 perf-arc
instrumentation is uniformly env-gated byte-identical-off as designed, and the
parked parallel/memory-model items were moved to
`design/arch/backlog/performance.md` with provenance (S106 WS-J) rather than
left dangling.

**The master design doc has decayed in the other direction.** `design/backend/backend.md`
(last touched 2026-07-03, but only sectionally):
- Cites `design/arch/facades/backend.md` as "authoritative" at lines 3, 5, 7,
  38, 322, 418, 444 — that facade was **retired S75 W5b** (→ BC §3 + source
  rustdoc, per `design/arch/CLAUDE.md` §facades). A reader following the doc's
  own authority pointer finds nothing (`design/arch/facades/` now contains only
  s69/s70 audit files).
- §Module inventory (line 97 region) describes a tree three reorganizations old:
  "`lib.rs` 4655 … ~3,932 lines of tests at the bottom" (actual: 1,742 total,
  tests in siblings), "`jit.rs` 1241" (actual: 913), "`cache/object.rs` 707"
  (actual: 332), MED-2 narrative at line 276 still describing zero local
  compiler tests.
- Claims `FunctionArtifacts` deleted (line 83; likewise
  `compile-to-module.md:47`) while it lives at `lib.rs:267` — the unreconciled
  S87 F9.
- Cites FIXME 0100 as open (lines 322, 418); the fixmes directory holds only
  0050/0052/0463/0553.

**Unarchived executed/superseded one-shots** sit beside the live docs despite
`design/backend/archive/` existing: `implementation-slice-s66.md` (executed;
its acceptance row 1(d) contradicts the source, §1 F2), `s87-decomposition.md`
(executed), `w5-retirement-fold-mapping.md` (executed), `sprint19-panic-boundary.md`,
`sprint51-fqtypename-cache.md`, and three sketch-era docs written in live voice
about a deleted oracle (`auto-curry-and-run-tests.md`, `hkt-codegen.md`,
`ast-sourced-codegen.md` — e.g. `hkt-codegen.md:50` "The sketch
(`sketch/src/codegen/primitives.rs`) implements…"; the sketch was deleted at S87
close).

### 2.5 Test-suite shape

**The S101 flag is cleared.** The flat ~5.9k-line crate-root `tests.rs` over the
submodules (METHOD §2.2 named anti-pattern, flagged S101) no longer exists:
tests live as per-submodule siblings (25+ files: `{module}/tests.rs` plus
topical `*_tests.rs` such as `compiler/apply/moded_arg_rc_tests.rs`,
`compiler/vec_codegen/{cow_polarity,vec_set_rc,vec_push_rc,reuse_proof,
temp_drop_rc}_tests.rs`, `compiler/control_flow/{par,poll,select}_codegen_tests.rs`),
with `test_support.rs` (946 lines) as the shared harness and two documented
crate-root exceptions (`module_assembly_tests.rs` 1,734, `clif_dump_tests.rs`).
Submodule×scenario-class attributability is genuinely good: RC polarity, COW,
moded-arg, sparkability, and redefinition seams each have a named home.
`literals.rs` and `match_codegen.rs` — the last two zero-test modules at S87 —
now carry local tests (`literals.rs:429`, `match_codegen.rs:666`).

**Integration tier**: extensive backend-touching e2e (`ownership_fences`,
`ownership_reuse`, `vec_query_value_use`, `repl_redefinition` families). The
suite's single failing-not-ignored guard at S107 close
(`ownership_reuse::chaining_toggle_off_allocates_intermediate`,
`tests/plan/ledger.md:136`) is owned by `/typecheck` (0528 carry), not backend.
The two S102 backend defect guards (ledger items 25/26) flipped green in the
B3.1 seam work. No backend-owned RED exists.

**One shape caveat**: the shared CLIF-probe harness that most codegen-behaviour
tests use is the dead-in-prod `Jit::compile_defn` path (§1 F2), not the
production `compile_to_module` → `compile_defn_in_module` path — the unit tier
exercises a parallel compilation front door that production never runs. The
CLIF emission core (`FnCompiler`) is shared, so coverage is real, but
context-construction drift between the two paths would not be caught.

### 2.6 Memory freshness

Assessed target per dispatch: `design/backend/` currency (crate `CLAUDE.md` is
hours old). Findings are §2.4's second half: the master doc's authority
pointers, module inventory, and deletion claims are decayed (dead references +
superseded facts + stale counts — three of the four decay classes), and
`design/backend/CLAUDE.md` (last commit 2026-03-05) fails all four: it names
the retired `/backend` skill as owner, points to `sketch/docs/` (deleted S87)
as a live reference, and instructs "per-ring evolution" documentation (ring
axis retired S64).

Spot-checks of the freshly seeded crate `CLAUDE.md` against code (accuracy
only, per dispatch): `CACHE_SCHEMA_VERSION = 16` ✓ (`cache/mod.rs:297`); GOT
1024-slot unchecked allocation ✓ (`cranelisp-types/src/module.rs:609`,
`got.rs:26-30`); test-sibling convention + the two crate-root exceptions ✓
(file census); extern-call consolidation ✓ (`compiler/extern_call.rs`);
env-gate table locations ✓ (spot: `heap.rs`, `compiler/fn_compiler.rs`,
`cache/manifest.rs`). No inaccuracies found in the sampled claims.

---

## 3. Recommendations

Seven, ordered by leverage within cost class. No live defects were uncovered
(the one release-mode UB hazard, R7, is latent and already documented in-source
as an open design question — it has no failing observable behaviour to repro
today; it is filed here as a recommendation, not routed to `/qa`).

### R1 — Delete `jit.rs::build_isa`; route `Jit::new`/`new_with_symbols` through `cache::object::build_isa(false)` [small, /dev (backend)]

**Evidence**: `jit.rs:49` vs `cache/object.rs:144` — identical bodies modulo the
`is_pic` parameter; production callers `jit.rs:321`/`jit.rs:357`; one test-side
import `primitives_inline.rs:426` (inside the `#[cfg(test)]` mod at `:414`).
Both carry "single construction point" rustdoc (`jit.rs:46-48`,
`cache/object.rs:140`, `lib.rs:32-33`) — at most one can be true. Open since the
04-23 audit's #1 recommendation; named again S87 (F1) and in the S87 synthesis
(T6); never filed. `jit.rs::build_isa` is `pub(crate)` — no public-surface change.
**Done**: one `build_isa` in the crate; `jit.rs` callers and the
`primitives_inline.rs` test call `crate::cache::object::build_isa(false)` (or the
crate-root re-export); the contradictory rustdoc collapses to one true claim;
`public-api.txt` byte-identical.

### R2 — Interim-residue deletion pass: "Wave 2b" cache shims, `CacheMetadata` envelope, `got.rs`/`codegen_types.rs` re-exports, `exe.rs` stale markers [small, /dev (backend)]

**Evidence**: the residue's stated justification is now vacuous — the markers
say the shims exist for external "pre-Phase-5 callers" (`cache/serialize.rs:319-321`,
`cache/mod.rs:324-325`), and a workspace grep finds **zero** consumers of
`CacheMetadata`, `cranelisp_backend::got::*`, or `cranelisp_backend::codegen_types::*`
outside the backend crate. Inventory: `#[allow(deprecated)]` ×5 in
`cache/mod.rs` (`:381,:398,:445,:507,:558`) + `cache/object.rs`
(`:37,:188,:331`); the `CacheMetadata` envelope threaded through
`build_cache_packet` (`cache/object.rs:186-197`) and `CachedModule.metadata`;
the 9-line `got.rs` shim ("Later sprints remove the re-export", `got.rs:6` —
written Sprint 56, ~50 sprints ago; note the S101 slab-invariant test module
below it at `got.rs:37-104` must be REHOMED, not deleted); the
`codegen_types.rs` 13-line re-export shim; and `exe.rs:72-77`'s
`#[allow(dead_code)]` + "currently red post-W2/W3; re-wires S77" on a function
live at `src/session_v4/lifecycle.rs:1964` (twin marker on
`generate_startup_object_checked`, `exe.rs:120`). Third consecutive audit for
the cache half (04-23 MED-1 "~30 markers" → S87 "~45, not fewer" → unchanged).
`CacheMetadata`/`build_cache_packet`/`got`/`codegen_types` are on the public
surface (`public-api.txt:183,219-238,272`) — the change-set must regenerate the
baseline per the design/arch baseline-diff discipline, but with no external
consumers the risk is nil.
**Done**: `CacheMetadata` and the deprecated `build_cache_packet` envelope
parameter gone; `got.rs`/`codegen_types.rs` deleted (slab tests rehomed;
`GOT_TABLE_SIZE`/`NULLARY_TAG_THRESHOLD` consumers import from
`cranelisp-types`); zero `#[allow(deprecated)]`/"Wave 2b" markers under
`cache/`; `exe.rs` allow+comment removed; `public-api.txt` regenerated in the
same change-set; `cargo check -p cranelisp-backend` warning-clean.

### R3 — Disposition the `Jit::compile_defn` test-harness path: gate it `#[cfg(test)]` and drop the eager-disasm capture [small, /dev (backend)]

**Evidence**: §1 F2 — `jit.rs:587/:712/:35` have exclusively test callers (14
sites, listed in §1) yet compile as production code, and `jit.rs:650`
`set_disasm(true)` unconditionally captures disassembly per compile — the
eager-disasm machinery retired everywhere else at S87 Wave 0 (FIXME 0418).
`design/backend/implementation-slice-s66.md` row 1(d) scheduled this function's
deletion; it survived as the de-facto unit-test harness instead.
**Done** (minimum): `compile_defn`/`build_compile_context`/`CompileArtifacts`
carry `#[cfg(test)]` (or move into `test_support.rs`), and the `disasm`
field/`set_disasm(true)` capture is removed (its only consumer is
`jit/disasm_tests.rs`, which can opt in locally). **Done** (better, at `/dev`'s
option): the harness delegates to the production `compile_defn_in_module` seam
so the unit tier exercises the real front door — this also closes §2.5's
parallel-path caveat. Either way `public-api.txt` is unchanged (all
`pub(crate)`).

### R4 — Protocol-boundary splits for the re-accreting dispatch bodies: `compile_resolved_call`, `compile_to_module_impl`, `compile_apply` [medium, /dev (backend), split plan via /design if contested]

**Evidence**: §2.1 census. `compile_resolved_call` (`apply.rs:417`) is 323
lines — third consecutive audit over budget, growing each time
(153 → 271 → 323) because it is the funnel where every new call-site concern
lands (fault guards S81, moded args + fences S102–S103). `compile_to_module_impl`
(`lib.rs:780`, 373) and `compile_apply` (`apply.rs:154`, 191) braid setup /
per-kind dispatch / artefact assembly the same way. `compiler/apply.rs` at
2,210 lines is now the largest module — the S87 decomposition's win is eroding
at exactly the most-edited seam. The S87 diagnosis stands: split at protocol
boundaries (builtin / trait-method / sig-dispatch / auto-curry / poll-effect
arms; per-phase helpers for `compile_to_module_impl`), not by line count.
**Done**: the three named functions each under ~150 lines with arms extracted
as named `FnCompiler` methods; no behaviour change (CLIF golden corpus
byte-identical); `apply.rs` trending down, not up, at the next audit.

### R5 — One drop-glue emission discipline: consolidate the identity+idempotency skeleton shared by the three glue builders [medium, /design (backend) then /dev]

**Evidence**: §2.3. `build_closure_drop_glue` (`lambda.rs:187`),
`build_auto_curry_drop_glue` (`fn_as_value.rs:938`), `build_adt_drop_glue_fn`
(`vec_codegen.rs:769`) re-implement the same skeleton, and the subtle half —
glue-name identity must fold the mono discriminator, plus declare-idempotent/
define-once — has produced two real defects on two different mirrors (FIXME
0350; ledger item 25, `tests/plan/ledger.md:188`), with the fixes
cross-referencing each other as "precedent" (`fn_as_value.rs:975-985`). Per the
standing `/review` root-cause feedback, a defect class recurring across mirrors
is past the consolidation threshold. This is design-shaped first: the shared
helper's parameterization (capture source × heap-category source × name scheme)
should be specified against backend §13's wrapper-identity rule before code
moves.
**Done**: one glue-emission helper owns naming identity + idempotency; the three
builders supply only their capture/layout specifics; a unit test pins the
identity rule once (distinct monos ⇒ distinct glue; one create-gate's two arms ⇒
one glue); the three per-site restatements of the rule reduce to pointers.

### R6 — Design-doc currency pass over `design/backend/` [medium, /design (backend); design feedback]

**Evidence**: §2.4/§2.6. Specifically: (a) `backend.md` lines 3/5/7/38/322/418/444
cite the S75-retired `facades/backend.md` as authoritative — repoint to
`bounded-contexts.md` §3 + source rustdoc per the retirement record in
`design/arch/CLAUDE.md`; (b) `backend.md` §Module inventory + MED-2 narrative
(lines ~97-112, 276) describe the pre-S87/pre-S101 tree — refresh or excise in
favour of the crate `CLAUDE.md` seam map; (c) reconcile the `FunctionArtifacts`
deletion overclaim (`backend.md:83`, `compile-to-module.md:47`) with the
as-built `pub(crate)` survivor at `lib.rs:267` — either record its survival as
an internal per-symbol helper or pair with a `/dev` change inlining it; (d)
rewrite `design/backend/CLAUDE.md` (2026-03-05: retired `/backend` owner,
deleted `sketch/docs/` reference, retired ring axis); (e) move the executed
one-shots (`implementation-slice-s66.md`, `s87-decomposition.md`,
`w5-retirement-fold-mapping.md`, `sprint19-panic-boundary.md`,
`sprint51-fqtypename-cache.md`) and the sketch-voiced trio
(`auto-curry-and-run-tests.md`, `hkt-codegen.md`, `ast-sourced-codegen.md`)
into `design/backend/archive/` with one-line supersession notes.
**Done**: every live doc under `design/backend/` has resolvable authority
pointers and no claims falsified by the source; historical docs live in
`archive/`; the next audit's freshness pass over this directory is clean.

### R7 — Surface GOT slot exhaustion as an error instead of release-mode UB [small, /arch (the seam is `cranelisp-types`), backend co-consumer]

**Evidence**: `cranelisp-types/src/module.rs:609-613` (`allocate_got_slot` is
unchecked monotone `+= 1`); `cranelisp-types/src/got.rs:135-150` (`store_slot`/
`load_slot` guard with `debug_assert!` only — compiled out in release, so slot
1024 is an out-of-bounds write/read into a fixed
`Box<[AtomicPtr<u8>; 1024]>`). Backend's own invariant record
(`crates/cranelisp-backend/src/got.rs:26-33`, S101 item d) names this the
"RESIDUAL RISK … EXHAUSTION, not movement" and notes the S101 ABI-epoch
fresh-slot churn (now live: every ABI-changing redefinition allocates a fresh
slot and freezes the old one) makes long agentic-REPL sessions approach the
bound materially faster than one-slot-per-definition did. Phase H is the
release-compiler phase — "debug-only guard against UB" is the wrong final
state. The in-source note calls it "an unresolved surfaced-error question, not
a bug to fix locally" — this recommendation asks `/arch` to resolve that
question: pick the surfacing point (fallible `allocate_got_slot` at the
session/typecheck allocation seam is the natural one; a hard-checked
`store_slot` is the backstop) and land the ~20-line change with a unit test.
Cross-crate (`cranelisp-types` + consumers), hence routed to `/arch` rather
than `/dev (backend)`.
**Done**: slot exhaustion in a release build produces a diagnosed session error
(not UB); a unit test pins the boundary behaviour at slot 1023→1024;
`got.rs:26-33`'s residual-risk note updates to point at the cure.

---

## 4. Disposition trail

*Appended at S108 Phase 1 by `/sprint` + the user — not by `/audit`. Each
recommendation above: accepted (→ FIXME number) or declined (+ rationale).*
