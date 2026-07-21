# `program.rs` decomposition — S109 hygiene (FIXME 0580, R-4)

Owner: `/design` (typecheck). Status: **design SIGN-OFF — `/dev` executes the move in Phase 5.** Subordinate to `design/typecheck/typecheck.md` (master); the direct precedent is `design/typecheck/s87-traits-decomposition.md` (the `traits.rs` → `traits/` cut). Where this doc and the master disagree, the master wins.

This is the `/design` sign-off on the **module cut** for `crates/cranelisp-typecheck/src/program.rs` (3,962 lines — the largest production module in the crate), accepted from the S108 audit R-4 (`audits/cranelisp-typecheck-s108.md` §2.3) as FIXME 0580. Per the sprint's Phase-4 wave hints, `/arch` wants this sign-off **early** (read-only, parallel) even though the mechanical move lands **last** in Phase 5 (after bucket 2 / 0581 / 0579, so it rebases trivially onto a settled `program.rs`). **`/dev` does NOT move code from this doc yet** — FIXME 0580 stays OPEN for the `/dev` implementation tail.

The done criterion (audit R-4): *no `program.rs` submodule exceeds ~1,200 lines; the phase drivers are named sub-functions within budget; `program/tests.rs` splits alongside per METHOD §2.2 attributability.*

---

## 0. The load-bearing fact that de-risks the whole move

**`program.rs` is entirely crate-private. `lib.rs:227` declares `mod program;` — never `pub mod`, never `pub use program::…`.** So, exactly as for `traits.rs` (`s87-traits-decomposition.md §0`), splitting it into `program/register.rs`, `program/body.rs`, etc. is a **pure intra-crate move**:

1. `lib.rs` keeps the single private `mod program;` line; `program.rs` becomes `program/mod.rs`, the new module root declaring `mod register; mod body; …`.
2. **Every method is on `impl<C, L> TypeCheckEnv<'_, C, L>`**, and Rust allows inherent-impl blocks for one type to be spread across any number of submodules — moving a method to a sibling file needs **no visibility change**; it keeps its `pub(crate)`/private and stays callable from `checker.rs`/`form.rs`/`infer.rs` exactly as before. (Confirm: the impl header at `program.rs:753` is re-opened verbatim in each sibling that hosts methods.)
3. The only visibility care is for the **free functions** the submodules share (the `for_each_child_expr` family, `apply_subst_to_*`, `annotate_*_from_maps`, `mangle_*`, the predicates) — they become `pub(super)` / `pub(crate)`, **never `pub`**. None crosses the crate boundary, so **`public-api.txt` stays byte-identical by construction** (the R-4 acceptance gate: 0580 must show a zero-diff `public-api.txt`, and `/review` checks the pure-decomposition claim).

**Framing for `/dev`: this is a file-organisation refactor, not an API refactor.** The `public-api.txt` invariant holds trivially as long as no item gains `pub` and `mod program` stays private. The real risks are (a) **behaviour drift inside the phase-numbered god functions** (§2) and (b) **accidental visibility-widening** (§4).

---

## 1. The cohesive clusters (validated against the source function map)

The FIXME names the seam set: **register / body / finalize / mono-collect**. Read against the actual file, the clean cut is **seven production submodules + a hub + a test-only driver** — the extra three beyond the named four are the pure free-function toolbox (`support`), the S101 callee-harvest cluster (`callees`, a distinct concern per `crates/cranelisp-typecheck/CLAUDE.md §"Def.callees completeness contract"`), and the `#[cfg(test)]` in-crate driver (`test_driver`). Line ranges are the current `program.rs`; **names are proposals, `/dev` may adjust**.

| # | Target submodule | What moves (current `program.rs` items / line ranges) | Cohesion rationale | ~LOC |
|---|---|---|---|--:|
| 1 | `program/mod.rs` | `//!` module doc; `use`s; `mod …;` decls; the `check_form` **dispatcher** (`:878`) that fans a form to the Register / CheckBody arms; the accumulator metadata types `FormCheckResult` (`:441`) + `ModuleCheckAccumulator` (`:497`) + `MangledNamesByBase` | The hub + the two-pass entry driver + the small result-accumulator types every seam reads/writes. | ~280 |
| 2 | `program/support.rs` | Expr traversal + subst: `for_each_child_expr`(`:52`)/`_mut`(`:105`), `rename_var_at_span`(`:162`), `apply_subst_to_expr`(`:176`)/`_defn`(`:187`)/`_variant`(`:197`); annotation/codegen-view: `annotate_expr_from_maps`(`:204`), `build_concrete_codegen_view`(`:262`), `annotate_defn_from_maps`(`:279`), `annotate_variant_from_maps`(`:291`); manglers + predicates: `mangle_sig`(`:665`), `mangle_type`(`:690`), `types_compatible`(`:721`), `is_trait_impl_mangled_name`(`:557`), `single_trait_bound_from_annotation`(`:578`), `existing_callable_slot`(`:606`), `is_macro_clause_defn_name`(`:619`), `enrich_macro_clause_resolution_error`(`:642`) | The pure free-function toolbox shared across register/body/finalize — the single child-enumeration source (`for_each_child_expr`), the subst walkers, the AST-annotation writers, the name manglers. No `self`; the natural bottom layer. | ~500 |
| 3 | `program/callees.rs` | methods `extract_call_graph_edges`(`:763`), `harvest_callee_edges`(`:804`), `resolved_call_to_fqsymbol`(`:819`); free fns `extract_user_fn_ref_edges`(`:309`), `write_callees_to_module_entries`(`:347`) | The S101 `Def.callees` completeness cluster (CLAUDE.md contract). One concern: "derive and write the caller→callee edge set at each body-check seam." Invoked from `body.rs` + `finalize.rs`; isolated so the 0472 seam discipline lives in one file. | ~230 |
| 4 | `program/register.rs` | **Pass-1 registration**: `check_form_register`(`:893`) + `_single_defn`(`:970`) + `_multi_sig`(`:994`); signature registration `register_defn_signature`(`:2995`), `detect_constrained_fns`(`:2931`), `resolve_bound_param`(`:2966`); the multi-sig family `resolve_multi_sig_overloads`(`:2578`), `refresh_multi_sig_variant_ret_types`(`:2621`), `resolve_variant_types`(`:2667`), `register_mangled_variants`(`:2724`), `register_overloaded_base`(`:2806`), `resolve_pending_overloads`(`:2852`); `register_test_fn_mono_roots`(`:3229`) | The write-side: turn a `TopLevel` into symbol-table signature/type-var/constrained-marker state, including multi-sig overload registration. The §8.6.4 name-freedom seam arms live here (`check_form_register`). | ~880 |
| 5 | `program/body.rs` | **Pass-2 body checking**: `check_form_body`(`:1050`) + `_single_defn`(`:1078`) + `_multi_sig`(`:1366`); `check_defn_body`(`:3160`) | The body-inference concern: check each defn body against its registered signature, harvest resolutions/edges (delegating to `callees.rs`), populate the per-form `FormCheckResult`. | ~590 |
| 6 | `program/finalize.rs` | `merge_form_result`(`:1568`)/`_inner`(`:1578`); `finalize_check_result`(`:1616`); `finalize_check_result_inner`(`:2016`); the post-passes `regeneralize_defn_schemes`(`:1640`), `resettle_polymorphic_schemes`(`:1767`); the ambiguity scan `find_ambiguous_top_level_form`(`:1836`), `is_codegen_ambiguous_type`(`:1932`), `find_ambiguous_value_position`(`:1936`) | The merge + finalize concern: accumulate per-form results, run the cross-defn post-passes (regeneralize, resettle, deferred re-resolve, ambiguity scan, callees/ownership publish), drain the accumulator into `CheckResult`. Hosts the standout god function (§2.1). | ~820 |
| 7 | `program/mono_collect.rs` | **Pass-4 collection/driver**: `pass4_monomorphise`(`:3367`), `collect_imported_constrained_calls`(`:3628`), `local_parametric_call_triggers`(`:3704`), `collect_local_parametric_calls`(`:3733`), `collect_parametric_fn_value_args`(`:3788`), `entry_is_monomorphisable_polymorphic`(`:3835`), `collect_constrained_calls`(`:3858`)/`_excluding_self`(`:3888`), `resolve_auto_curry`(`:3917`), `resolve_expr_types`(`:3952`) | The mono **collection** concern (the per-call **engine** `monomorphise_call` lives in `traits/monomorphise.rs` — this cluster is only the call-site collection + Pass-4 driver). Walks bodies for constrained/parametric call sites, dedups, drives `monomorphise_call`, records `SigDispatch`. | ~595 |
| 8 | `program/test_driver.rs` (`#[cfg(test)]`) | `check_via_forms`(`:2384`), `wrap_exprs_as_defns`(`:2457`), `compute_display_info`(`:2494`), `collect_single_sig_defns`(`:2547`) | The in-crate `#[cfg(test)]` pipeline driver (`check_via_forms` retains the display-bearing `CheckResult` for assertions; production routes through `check_forms` in `form.rs`). `#[cfg(test)]`, `pub(crate)` so every per-submodule test file reaches it. **Note:** `collect_single_sig_defns` is also called from `finalize_check_result_inner` (`:2074`) — if it is not test-only, it moves to `support.rs`/`finalize.rs` instead; `/dev` confirms its callers before placing it. | ~194 |

**Resulting sizes** — all land under the ~1,200-LOC gate (largest is `register.rs` ~880 and `finalize.rs` ~820, both comfortably within budget). No submodule exceeds the target; the FIXME's ceiling is met by the cut alone, before the §2 god-function phasing.

### 1.1 Why the extra three beyond register/body/finalize/mono-collect

- **`support.rs`** — the free-function toolbox (~500L of `self`-less walkers/annotators/manglers) has no home in any single pass; it is the shared bottom layer. Folding it into `mod.rs` would bloat the hub past its role; a dedicated file keeps `mod.rs` a thin declaration/dispatch root.
- **`callees.rs`** — the S101 callee-harvest is a distinct, contract-bearing concern (`CLAUDE.md`, FIXME 0470/0472) invoked from *both* `body.rs` and `finalize.rs`; co-locating its five items keeps the 0472 "every body-check seam harvests" discipline auditable in one place (Principle 7).
- **`test_driver.rs`** — the `#[cfg(test)]` driver is ~194L that would otherwise sit under a `#[cfg(test)]` block in `mod.rs`; a dedicated file keeps the production hub production-only and gives the per-submodule test files one import target.

---

## 2. The phase-numbered god functions — split IN-PLACE first (the S87 lesson)

The R-4 done criterion is two-fold: **file cut** (§1) AND **"phase drivers are named sub-functions within budget."** Three functions are over the ~100-line convention and are the genuine-untangle risk (not the mechanical move). Per the s87 precedent (`s87-traits-decomposition.md §2/§4.1`), **split these in-place in `program.rs` and run the suite green BEFORE the file move** — this isolates the untangle risk from the move risk so a red suite unambiguously fingers one or the other. Do NOT combine them in one change-set.

### 2.1 `finalize_check_result_inner` (~188 effective lines, `:2016–2383`) — the standout

The audit's headline over-budget function (grown ~25% since S87, absorbing the S101 callees harvest + ownership publish). It is **already comment-delimited into phases** (`// Phase 2:`, `// Phase 3:`, `// Pass 2.5:`, `// Pass 3:`), so the extraction is mechanical *if the state-threading order is preserved*. Proposed named sub-methods (each on `impl TypeCheckEnv`, in `finalize.rs`; **`/dev` adjusts names + exact boundaries against the live source**):

| Phase | Approx lines | Proposed extraction | What it does | Invariant to preserve |
|---|---|---|---|---|
| P0 — regeneralize | 2023–2025 | *(inline — already `regeneralize_defn_schemes`)* | Phase-2 generalize-all; clear false-positive constrained markers. | Runs before the deferred re-resolve so schemes are final. |
| P1 — deferred re-resolve | 2027–2056 | `reresolve_deferred_calls(state, working_program)` | Per-defn `resolve_deferred_trait_calls` + `resolve_value_position_trait_methods` over the final subst (multi-sig fans per `__v{i}` variant). | Uses the SAME `working_program`; the multi-sig `__v{i}` internal-defn reconstruction must match the register-side keys. |
| P2 — multi-sig overloads | 2058–2071 | *(inline — already `resolve_multi_sig_overloads`)* | Registers mangled variants; harvests `multi_sig_mangled_names` for the re-annotation below. | Side-effect: writes mangled entries to the symbol table; the base→[mangled] map feeds the re-key step. |
| P3 — constrained collection | 2073–2130ish | `collect_all_constrained_names(state, working_program, accumulator, strategy) -> HashSet<Symbol>` | Pass-3 `detect_constrained_fns` + accumulator drain + the `Additive`-strategy symbol-table scan for cross-call constrained/parametric fns. | The `Additive` scan reads the live table; its `UserFnState` match must stay exactly (constrained OR polymorphic-with-ast). |
| P4 — monomorphise | (calls `pass4_monomorphise`) | *(inline call — engine is `mono_collect.rs`)* | Drives Pass-4 over the collected constrained names. | `pass4_monomorphise` is in cluster 7; finalize only calls it. |
| P5 — annotate + re-key + publish | tail → 2383 | `finalize_annotations_and_publish(state, accumulator, &multi_sig_mangled_names, …) -> CheckResult` | Re-annotate multi-sig entries by mangled name; harvest callees (delegates to `callees.rs`); ownership publish; drain accumulator into `CheckResult`. | The re-key uses `multi_sig_mangled_names` (the `__v{i}` internal keys are gone post-registration); callees writeback is the 0472 seam. |

The slimmed `finalize_check_result_inner` becomes a ~30-line sequential driver (P0/P2/P4 inline calls to existing helpers; P1/P3/P5 the new extractions), each within budget. **The three mutable channels to preserve** (mirroring `s87 §2.2`): `state.subst` (P1's deferred re-resolve mutates it), the symbol table (P2/P5 write mangled/annotated entries), and the `accumulator` (drained in P5). Do not reorder the phases; the deferred re-resolve (P1) must see the regeneralized schemes (P0) and precede the mono drive (P4).

### 2.2 `check_form_body_single_defn` (~287 raw, `:1078–1366`) and `pass4_monomorphise` (~260 raw, `:3367–3628`)

Both are over budget but are **single-concern** sequential drivers (one body-check; one Pass-4 collect-dedup-drive loop). `/dev` reads each and extracts the natural sub-steps to bring the driver under budget — `check_form_body_single_defn` splits into infer-body / harvest-resolutions / harvest-callees / annotate-writeback; `pass4_monomorphise` splits into collect-call-sites / dedup / drive-and-record. These are **lower-risk than `finalize_check_result_inner`** (no cross-phase state-channel subtlety) and may be phased in-place in the same Stage-A change-set, or deferred to a follow-up if capacity is tight — the file cut (§1) alone already meets the ~1,200-line ceiling; the sub-budget phasing is the second half of the criterion and should land, but `finalize_check_result_inner` (§2.1) is the priority.

---

## 3. The test split — `program/tests.rs` (7,505 lines, 141 tests) → per-submodule

METHOD §2.2 attributability: a test's home file corresponds to the production unit it exercises, so a failure attributes to a module. Because the production submodules are flat files (`program/register.rs`), **Rust 2018 resolves a child `#[cfg(test)] mod tests;` in `program/register.rs` to `program/register/tests.rs`** — so each production submodule gets its own sibling test dir with zero mod-rs gymnastics.

Distribution (by the `// spec:` banners surveyed in the current `program/tests.rs`):

| Test home | Tests that move there |
|---|---|
| `program/register/tests.rs` | defn/deftype/typedef registration, polymorphic typedef, multi-sig registration + arity/type/duplicate-sig + call-site variant resolution (`:227–475`, `:927–1000`, `:1658–1957`) |
| `program/body/tests.rs` | body inference, forward references, string-return types, internal-ctor `Bind`/`Pure` head+pattern rejection, builtin-fn method resolution (`:304–878`) |
| `program/finalize/tests.rs` | `check_form`/`check_via_forms` identity (Category 1/2, `:2117–2560+`), display-info, concrete-boundary codegen-view / Phase-2b mono-population (`:1352–1536`) |
| `program/mono_collect/tests.rs` | `collect_constrained_calls` (direct/let/if recursion), batch + REPL monomorphise, constrained-fn detection, empty-mono (`:1048–1601`) |
| `program/callees/tests.rs` | the `callees_*` set (CLAUDE.md names `program::tests::callees_*`) |

**Test-path citations that move with the tests** (update in the SAME change-set — these are the only external references to the `program::tests::` paths): `crates/cranelisp-typecheck/CLAUDE.md` names `program::tests::cross_module_imported_constrained_fn_monomorphises_in_defining_scope` (→ `program::mono_collect::tests::…`) and `program::tests::callees_*` (→ `program::callees::tests::…`); `tests/plan/s101-coverage-postmortem.md §2.1` cites `callees_*`. `/dev` owns the CLAUDE.md edit; the `tests/plan` citation is `/qa`'s (file a one-line FIXME `target: /qa` if the path moves, or keep a `#[cfg(test)] pub(crate) use` alias — the alias avoids the cross-skill churn and is the lower-friction choice). The `check_via_forms` driver (cluster 8, `pub(crate)`) is reached from every per-submodule test file via `use crate::program::test_driver::check_via_forms` (or a `mod.rs` re-export).

> **Alternative considered — keep `program/tests.rs` as one file** (as s87 kept `traits/tests.rs`). Rejected: `traits/tests.rs` is ~950 LOC; `program/tests.rs` is 7,505 (334 KB) — an order of magnitude larger, and the R-4 criterion explicitly says "splits alongside." The per-submodule split is the attributability win the size warrants.

**S115 currency note for the `/dev`(0722) executor (`/design`, verified against source — do NOT redesign).** The §3 design is SOUND and re-executable; three currency corrections apply to its anchors, not its logic:

1. **The header count and line ranges are STALE.** `program/tests.rs` is now **10,576 lines / 213 tests** (7,505 / 141 at design time — +40%, audit `cranelisp-typecheck-s114.md` §2.2c). The distribution table's parenthetical line-range anchors (`:227–475`, `:304–878`, etc.) no longer map. `/dev` **re-surveys the current file's `// spec:` banners** (the distribution *logic* — a test's home = the production submodule it exercises — is unchanged; only the line anchors rot).
2. **A `program/support/tests.rs` home is not in the table.** The current tree carries `program/support.rs` (607 LOC) and `program/mod.rs` in addition to the five distribution rows (register/body/finalize/mono_collect/callees). `/dev` assesses whether the +72 new tests introduced a `support`-exercising category (and whether `mod.rs` warrants one); add the row if the banner survey finds support-homed tests. The five-row table is the floor, not necessarily complete for the grown file.
3. **`finalize.rs` re-budget rides the same FIXME (0722, audit R-3).** `finalize.rs` is 1,517 LOC (§3.2 of `typecheck.md`); the §11.8.10 three-window seams are the function-level cut. Cut per-submodule so no `program/` submodule exceeds ~1,200.

The citation-update list (CLAUDE.md `cross_module_imported_constrained_fn_monomorphises_in_defining_scope` → `mono_collect::tests::`; `callees_*` → `callees::tests::`; `tests/plan/s101-coverage-postmortem.md §2.1`) is **still current** (verified against source S115) — those remain the only external references to the `program::tests::` paths.

---

## 4. Migration order + hazard list for `/dev`

**Stage conservatively. One change-set per stage, suite green between each. Do NOT batch.** (The s87 staging discipline, `s87-traits-decomposition.md §4`.)

| Stage | Action | Why this order | Gate |
|---|---|---|---|
| **A** | **Phase-split `finalize_check_result_inner` (§2.1) IN-PLACE** (still in `program.rs`), and — capacity-permitting — `check_form_body_single_defn` + `pass4_monomorphise` (§2.2). | Isolates the one genuine untangle (finalize's cross-phase state channels) from all file-move noise. A red suite here is unambiguously a phase-cut error. | Full `cargo nextest run --no-fail-fast` — no NEW red beyond the known defect guards; `public-api.txt` unchanged. |
| **B** | **Create `program/mod.rs` from `program.rs`; move clusters 1–8 into sibling files** (§1); adjust free-fn visibility to `pub(super)`/`pub(crate)`; split `program/tests.rs` per §3. | The phase-splits are already green, so the move is pure file-organisation. | Suite green; **`public-api.txt` byte-identical** (`diff` it — the R-4 zero-diff gate). |

If capacity allows only one stage, **Stage A only** (the function-budget win on the load-bearing finalize driver; lowest blast radius). Stage B is the navigability win but is mechanical.

**Because Stage B lands LAST in the sprint's Phase-5 order** (after bucket 2 / 0581 / 0579, per the SPRINT.md Phase-4 wave hints), `program.rs` is settled when the move happens — the mechanical cut rebases trivially, and this design sign-off can be reviewed early/parallel without blocking the code.

### Hazard list

1. **`finalize_check_result_inner` phase order is load-bearing** (§2.1). The deferred re-resolve (P1) must follow regeneralize (P0) and precede the mono drive (P4); the `multi_sig_mangled_names` map minted in P2 is consumed by the P5 re-key. An extraction that reorders these, or that re-reads `state.method_resolutions` after P5 drained it, silently mis-finalizes (symptom: a stale/duplicate `SigDispatch` or an un-annotated multi-sig variant).
2. **`check_form` dispatcher stays in `mod.rs`** as the two-pass entry driver; the Register / CheckBody arms live in `register.rs` / `body.rs`. The dispatcher must keep calling them by their unchanged `pub(crate)` names.
3. **Free-fn visibility — the one thing that can break `public-api.txt`.** The `self`-less toolbox fns become cross-file: grant **`pub(super)`** (visible within `program/`), **`pub(crate)`** only where an external caller exists (`build_concrete_codegen_view` — called from `adt.rs`/`traits/impl_check.rs`; `for_each_child_expr`(`_mut`) — used crate-wide; `mangle_type`; `write_callees_to_module_entries`; `harvest_callee_edges`; `apply_subst_to_defn`; `rename_var_at_span`; `check_via_forms` under `#[cfg(test)]`), and **never `pub`**. `/dev` audits each against its callers; the compiler's unused/private-in-public warnings are the cheap signal a cut is clean. A stray `pub` would still not enter `public-api.txt` (private `mod program`) — but keep the minimal visibility as the structural guard (Principle 18).
4. **`collect_single_sig_defns` placement** — it is `#[cfg(test)]`-adjacent (grouped with the test driver) but is ALSO called from `finalize_check_result_inner:2074` (production). Confirm its `cfg`: if production, it moves to `support.rs` or `finalize.rs`, NOT `test_driver.rs`. Do not let the "test driver" grouping strand a production caller.
5. **The `impl<C: CodeStore, L: LinkerStore> TypeCheckEnv<'_, C, L>` header repeats per method-hosting file** — copy it verbatim (the generic bounds + lifetime must match exactly or the methods are not recognised as the same impl).
6. **`use` hygiene per file** — each sibling needs its own `use cranelisp_types::{…}` + `use crate::checker::{CheckState, TypeCheckEnv}` + `use crate::scheme::mono` subset; let clippy drive the minimal set (unused-import warnings signal a clean cut).
7. **Test-path citations move with the tests** (§3) — the CLAUDE.md + `tests/plan` `program::tests::` references; prefer a `#[cfg(test)] pub(crate) use` alias to avoid cross-skill churn, else a one-line FIXME `target: /qa`.

### The behaviour-preserving acceptance contract

- **Suite green throughout** (`cargo nextest run --no-fail-fast`) — no NEW red beyond the known defect guards; the `program/*/tests.rs` split set + the cross-module-mono + `callees_*` tests are the behaviour acceptance set.
- **`public-api.txt` byte-identical** — the structural proof no item gained crate-boundary visibility (holds by construction if no `pub` added and `mod program` stays private).
- **No new inline FIXMEs** (root `CLAUDE.md`); a design gap surfaced by the move is filed `design/arch/fixmes/NNNN-*.md target: /design`.
- **Optional CLIF spot-check** — Stage A touches `finalize_check_result_inner` (the codegen-feeding finalize seam); a `/clif <name>` or `CRANELISP_CODEGEN_TRACE=1` before/after on one multi-sig + one constrained-mono program confirms the emitted IR is unchanged (the strongest behaviour-preservation evidence for the load-bearing driver).

---

## 5. Quality-attribute assessment (per `/design` stewardship)

| Attribute | Effect |
|---|---|
| **Simplicity** (P6) | Net positive — no new complexity; the 3,962-line file becomes eight ~200–880L cohesive files, and the ~188-line finalize god function drops to a ~30-line driver. Carries only the complexity the pipeline demands. |
| **Maintainability** | The headline win — a register change touches `register.rs`, a mono-collection change `mono_collect.rs`, a finalize change `finalize.rs`; bounded blast radius. Matches the audit's "give `program.rs` the `traits/` treatment." |
| **Observability** | Unchanged — no trace surface touched. The CLIF spot-check (§4) is a one-time migration aid. |
| **Concurrency-safety** | Unchanged — `program.rs` holds no shared state; all state is per-call `CheckState` / the borrowed `TypeCheckEnv`. The cut does not alter the mutation discipline. |
| **Performance** | Unchanged — same call graph, same `state.subst` operations; private-method extraction is zero-cost (inlines at the same depth). |
| **Testability** (P5) | Improved — the finalize phase helpers (§2.1 P1/P3/P5) become independently exercisable seams, and the per-submodule test split (§3) attributes a failure to one production unit (METHOD §2.2). |

Principles cited: **6** (complexity budget — the split carries no new complexity, and phasing the finalize driver removes a cognitive-load hotspot), **7** (single source of truth — `callees.rs` co-locates the 0472 harvest discipline; `support.rs` the child-enumeration source), **18** (enforce invariants structurally — minimal free-fn visibility is the `public-api.txt` guard), the s87 precedent (`s87-traits-decomposition.md`) as the in-context template.

---

## 6. FIXME 0580 disposition + next skills

- **FIXME 0580 stays OPEN** — this doc is the `/design` sign-off on the cut (the audit's "design sign-off by /design on the module cut"); the `/dev` implementation tail (the actual move + phase-split + test split + `public-api.txt` zero-diff verification) is Phase-5 work and closes the FIXME. Record: the signed-off cut is §1 (eight submodules), the phase-split is §2, the test split is §3, the hazards §4.
- `/dev` (typecheck) — execute **Stage A** (`finalize_check_result_inner` phase-split in-place, §2.1) suite-green, then **Stage B** (file move + test split, §1/§3), each its own change-set. Lands LAST in the Phase-5 order (after bucket 2 / 0581 / 0579). Mandatory unit-test-per-change applies to any non-trivial phase-boundary adjustment. Delete FIXME 0580 when the move is landed + `public-api.txt` verified zero-diff.
- `/review` (typecheck) — point-in-time review of each stage against this doc: §2.1 finalize state-channels, §4 hazards, the `public-api.txt` zero-diff acceptance. Per `memory/feedback_review_root_cause_and_duplication`, verify no phase extraction deepened a state-channel duplication.
