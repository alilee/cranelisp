# cranelisp-typecheck audit — 2026-05-30

> **Lineage.** This iterates the 2026-04-23 audit (`typecheck-20260423.md`) against the
> Sprint 72 Phase B state. It folds in the S72 `/review` deep audit (KnownTypes deletion,
> entry-metadata restructure, `register_builtins` disconnect, cluster-atomic refactor).
> The 2026-04-23 findings are re-evaluated below — some closed, most structural ones persist.
> Method: direct source inspection + `/review` deep audit + structural metrics. Read-only;
> no remediation applied.

## State summary

**The crate is in a clean Phase-B-close state on the axes S72 touched, but the
structural-duplication debt the 2026-04-23 audit named as "the largest active issue"
is largely still open.** Phase B was a *resolution-and-boundary* sprint, not a
*structural-consolidation* sprint, and the metrics show exactly that signature:

- **Resolution unified.** `KnownTypes`/`KnownTypeKind` + the three `known_type_names*`
  snapshot builders are deleted; all type/trait/constructor resolution now flows through a
  single terminal resolver (`checker.rs:resolve_terminal_entry_and_home` →
  `chain_follow_to_home`) injected as one closure into `resolve.rs`. No parallel dispatchers.
  Resolution is `Result`-threaded with **zero production panics on resolvable input** (audit
  HIGH-4 honoured). This closes the `known_type_names` portion of old Finding 5 and FIXME 0172's
  typecheck-internal fallback chains.
- **Entry metadata regularised.** `docstring` is now a direct `ModuleEntry` field (un-nested);
  no visibility duplication; `IntrinsicType` carries visibility + docstring; intrinsic scalars
  carry spec §3.1 docstrings.
- **Boundary cut.** `register_builtins` severed from the public interface (`pub(crate)` +
  `#[allow(dead_code)]`, retained as the S73 assembly reference). Synthetic-module assembly is
  leaving typecheck's bounded context.
- **But the four structural-duplication findings (old 1–4) persist or grew**, and the large
  mixed prod/test files (old 6) are unchanged. None of the four builder/visitor/consolidation
  remediations from 2026-04-23 were taken.

### Snapshot metrics (2026-04-23 → 2026-05-30)

Totals are prod+test per file (the 2026-04-23 prod-only figures are noted where comparable).

| File | 2026-04-23 total | 2026-05-30 total | Δ | Note |
|---|---|---|---|---|
| program.rs | 6,985 | 7,006 | ~flat | still the heaviest file |
| checker.rs | 2,798 | 3,904 | +40% | resolution consolidated here (good — single path) |
| traits.rs | ~ (1,839 prod) | 3,220 | grew | dual impl-method flows persist |
| infer.rs | 3,054 | 3,184 | +4% | — |
| builtins.rs | 2,433 | 2,863 | +18% | `seed_test_primitives` + docstrings; KnownTypes removed |
| resolve.rs | — | 406 | — | exemplary: Result-threaded, closure-decoupled |
| cluster.rs | — | 368 | — | new cluster-atomic read/write wrappers |
| **crate total** | ~20,371 | 24,092 | +18% | growth concentrated in resolution + test oracle |

- `ModuleEntry::Def { … }` constructed **159 times** (was ~132) — concentrated in program.rs (69),
  builtins.rs (37), checker.rs (16), traits.rs (14), adt.rs (14). **Increased, not reduced.**
- In-crate tests: **347, all green (~0.97s).**

## Reconciliation — 2026-04-23 findings vs current state

| # | 2026-04-23 finding | Status | Evidence |
|---|---|---|---|
| 1 | `program.rs` multiple effective pipelines | **PERSISTS (+ new layers)** | `check_program`/`check_program_inner` (1853/1861) + `check_repl_input`/`_inner` (1993/2001) still present alongside `check_form`/`check_inner` (580/1282). The cluster-atomic refactor added a *further* internal layer: `check_forms` → `form.rs` `parsed_to_top_level` shim (255) + `map_cranelisp_error` lossy bridge (292) → `CheckPass` (260) + `ModuleCheckAccumulator` (339). Public surface collapsed to `check_forms`; internal path-multiplicity is unchanged or higher. |
| 2 | Duplicated `Expr` traversal | **PERSISTS (unchanged)** | `apply_subst_to_expr` (program.rs:41), `annotate_expr_from_maps` (118), `collect_constrained_calls` (2749), `resolve_deferred_trait_calls` (infer.rs:587). No shared `walk_expr_children` introduced. |
| 3 | `traits.rs` parallel non-HKT/HKT impl-method flows with duplicated tails | **PERSISTS** | `check_impl_method_with_sig` (594) + `check_hkt_impl_method` (788) coexist; S72 threaded `TraitDeclInfo` through both but did not factor the shared writeback tail. |
| 4 | Manual repeated `ModuleEntry::Def` construction | **WORSE** | 132 → 159 occurrences. No constructor/builder introduced. (Note: the parallel S73 plan — FIXME 0241 — proposes kind-shaped `SymbolTable` builders that would absorb much of this.) |
| 5 | Scattered full-scan lookups; `known_type_names` | **PARTIALLY CLOSED** | `known_type_names*` deleted; resolution is single-path. Remaining whole-module scans persist (`all_type_defs`, `lookup_type_def_in_module`, `has_impl_in_module`, `lookup_trait_decl_in_module` — checker.rs:411–1771). The proposed `TypecheckIndexView` facade was not built; the read-scan helpers are simpler but still ad hoc. |
| 6 | Large mixed prod/test files | **PERSISTS** | program.rs 7,006 / checker.rs 3,904 / traits.rs 3,220 / infer.rs 3,184 / builtins.rs 2,863. No test-module splits done. |

## New findings (S72 `/review` deep audit)

All Minor/Nit — no new Critical/Important, no fix-now defects.

- **N1 [Axis 2, Minor]** `form.rs:25–42` module doc is stale and self-contradictory: describes
  read-union staging as a "Wave 3b follow-up" that has in fact shipped (contradicted by passing
  `cluster_mode_reads_union_staging_and_live`). → doc-currency, `/typecheck`.
- **N2 [Axis 2, Minor]** `result.rs:6,17,53–54` rustdoc references singular `check_form`/
  `TypeChecker::check` post-`check_forms` collapse. → doc-currency, `/typecheck`.
- **N3 [Axis 3, Nit]** `cluster.rs:107,116,138` use `panic!` for the same "current module must
  exist" invariant that `checker.rs:317,354,371` express as `unreachable!`. Convention mismatch;
  trivially harmonizable. → `/typecheck`.
- **N4 [Axis 1, Important — already tracked]** facade↔baseline `check_forms` drift: facade
  prescribes 4 params (`module_aliases` threaded); baseline shows 3 (aliases live `CheckState`-local).
  Tracked by **FIXME 0240** (A1/A4). Confirmed-and-deferred, not novel.
- **N5 [Axis 4, accept]** `result.rs` has 0 unit tests (pure data + `From` conversions — acceptable).

## FIXME tracking map

| Concern | FIXME | Target | Status |
|---|---|---|---|
| `register_builtins` facade strike + synthetic-module assembly relocation | 0241 | /arch | open (S73) |
| `register_builtins` call-site migration in int | 0242 | /int | open (S73, blocked by 0241) |
| `seed_test_primitives` test-oracle duplication (old Finding 5 residue) | 0239 | /arch | open (S73) |
| `check_forms`/module_aliases facade cascade + resolve_* rename | 0240 | /arch | open |
| Short-name fallback chains (old) | 0172 | — | **typecheck-internal portion CLOSED** (confirmed deleted) |
| N1–N3 doc-currency + invariant-guard harmonization | *(none yet)* | /typecheck | **un-tracked** — file or fix |

**Structural findings 1, 2, 3, 4, 6 have NO FIXME and NO sprint slot.** They are the 2026-04-23
audit's core thesis, mostly still open. Per project doctrine (audit findings without a tracking
artefact get lost), these warrant either FIXMEs or a dedicated structural-consolidation sprint.

## Prioritized remediation (refreshed)

1. **[High] Collapse `program.rs` to one authoritative pipeline.** Old Finding 1, now compounded
   by the cluster-atomic shim layer. Make `check_forms`'s internal path single; demote
   `check_program`/`check_repl_input` to test-only adapters or delete; retire `CheckPass` +
   `ModuleCheckAccumulator` + `parsed_to_top_level` + `map_cranelisp_error` once the path is unified.
   Natural to bundle with the S73 boundary-redraw wave (FIXME 0241/0242) since both touch startup/check entry.
2. **[High] Factor the shared impl-method writeback tail in `traits.rs`** (old Finding 3).
3. **[Med-High] Introduce kind-shaped `SymbolTable` builders** (old Finding 4) — converges with
   FIXME 0241's proposed `cranelisp-types` builder vocabulary; do them together.
4. **[Med] Shared `Expr` child-traversal helper** (old Finding 2).
5. **[Low-Med] Centralise remaining whole-module scans** behind one read view (old Finding 5 residue).
6. **[Low] Split heavyweight tests** out of the giant files (old Finding 6); do after pipeline consolidation.
7. **[Trivial] N1–N3 doc-currency + `panic!`→`unreachable!` harmonization** — fix-now candidate.

## Agent guidance / traps (updated)

1. **`check_forms` is the public entry; resolution is single-path.** Use
   `resolve_terminal_entry_and_home`/`chain_follow_to_home`; do not reintroduce name-based fallbacks.
2. **`check_program*`/`check_repl_input*` still exist** in `program.rs` — legacy, do not treat as primary.
3. **`register_builtins` is dead legacy** (`pub(crate)`+`allow(dead_code)`) retained as the S73
   assembly reference (FIXMEs 0241/0242) — read it, don't call it, don't delete it yet.
4. **Trait-impl changes still have two flows** (`check_impl_method_with_sig` + `check_hkt_impl_method`).
5. **New `Expr` variants** still require updating four hand-rolled walkers (see N-old-Finding-2 list).
6. **`ModuleEntry::Def` construction is manual in 159 sites** — fields like `got_slot`/`ast`/`code`
   are load-bearing; a builder should own these (converges with FIXME 0241).
7. **`seed_test_primitives` mirrors production primitives** — the surviving test-oracle duplicate
   (FIXME 0239); don't extend it, replace with a shape-flexing source.

## Bottom line

Phase B is a **clean close on what it set out to do**: resolution and lookup are unified and
panic-free, entry metadata is regular, the boundary cut is in place, all 347 tests pass. The
2026-04-23 audit's central warning — *structural duplication in the high-complexity files* — was
**addressed only for the resolution path**; the parallel pipelines in `program.rs`, the duplicated
`Expr` walkers, the dual `traits.rs` impl-method tails, and the 159-site manual `Def` construction
remain open and untracked by any FIXME. The crate is maintainable *today* and clean for Phase-B
acceptance, but the deeper consolidation the prior audit flagged is now the dominant outstanding
maintainability question and should be scheduled (FIXMEs or a structural sprint), ideally riding the
S73 boundary-redraw wave where pipeline-entry and `Def`-builder work naturally converge.
