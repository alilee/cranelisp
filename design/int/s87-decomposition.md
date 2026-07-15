> **HISTORICAL — superseded slice / working doc (triaged S110, FIXME 0607).** A
> point-in-time implementation-slice narrative, retained for the audit trail only; NOT
> current design intent. The durable design is `int.md` (master) plus the subsystem docs
> indexed in `design/int/CLAUDE.md` §"Document index". Where this doc disagrees with the
> current source or the master, the source and master win.

# S87 — `src/` module decomposition (Wave 5: `process_form.rs` + `session_v4.rs`)

> **Status.** Design phase (Sprint 87, Wave 5). `/design` authors the module
> boundaries; `/dev` executes. READ-ONLY on code — this doc is the only artefact.
>
> **Goal (user).** "Coherent and cohesive modules of manageable size." Two src/
> production modules are over the ~budget that the rest of the binary surface now
> sits at after the FIXME 0109 Wave-C/D split (`session_v4.rs` 5417→1428 LOC;
> `worker.rs` 5041→749 LOC). These two are the residual #2 and #6 by corrected
> production LOC (`audits/loc-s87.md`, `audits/src-s87.md §1`).
>
> **Constraint.** A binary crate has no `public-api.txt`; the invariant is purely
> **behavior-preserving** (full suite green, incl. the 14 known-defect guards —
> `CLAUDE.md §Testing) + coherent module boundaries. The `src/` dir-module form
> (`mod foo;` resolving to `foo/` with sibling `foo/tests.rs`) is already proven
> in this crate — `process_form.rs` and `session_v4.rs` BOTH already declare
> `#[cfg(test)] mod <topic>;` siblings (see below), so the test-extraction half of
> Part 1 is already done for these two files. These are pure production-LOC splits.
>
> **Principles in force.** Principle 6 (complexity has a budget — the ~100-line
> function ceiling + the file-size driver), Principle 7 (single source of truth —
> the prelude-fallback dedup §4), Principle 1 (decoupling), Principle 5
> (testability is structural — the cohesive cuts keep each unit testable at its
> seam). Principle 19 (no module privileged by name) is a *watch* item: none of the
> proposed module names introduce a name-keyed dispatch; the cuts are by concern.

---

## 0. Pre-flight: what is already done, and the invariant

**Test extraction is already complete for both files.** Do NOT redo Part-1 work
here:

- `process_form.rs:3208` — `#[cfg(test)] mod tests;` (sibling `process_form/tests.rs`).
- `session_v4.rs` declares **five** `#[cfg(test)]` siblings, not one inline block:
  `platform_enumeration_dedup_tests` (`:2302`), `discover_tests_extern_tests`
  (`:2910`), `persistent_worker_tests` (`:3046`), `bare_primitive_value_path_tests`
  (`:3060`), `list_classification_tests` (`:3064`). The "807 inline-test LOC" the
  maintainability pass cites is spread across these siblings already.

**Consequence for the split.** When `foo.rs` becomes `foo/mod.rs` (or stays
`foo.rs` with submodules — see §1.0), the existing `#[cfg(test)] mod X;`
declarations must be **re-homed onto the submodule that owns the code each test
exercises**, and the sibling test files moved under that submodule's directory.
This is the one non-mechanical wrinkle in an otherwise mechanical split — call it
out per-module below.

**Behavior-preserving invariant (the gate `/review` checks).** Every function
moves byte-for-byte; only its `fn` visibility and `use`/path prefixes change. No
control-flow edits, no signature changes except visibility widening, no merging of
two functions into one (the over-budget splits in §3 are *extractions* — the
extracted helper is called from the now-shorter parent, same code, same order).
The full `cargo nextest run` is green before and after, with exactly the 14 known
failing guards (no 15th red, no guard flipped green by accident).

---

## 1. `src/process_form.rs` (~1765 prod LOC) → `process_form/` submodules

### 1.0 Form of the split

`process_form.rs` is referenced by `lib.rs` as `pub(crate) mod process_form;` and
its public items (`process_cluster_once`, `compile_macro_for_repl`,
`record_imports_on_symbol_table`, `record_submodule_on_symbol_table`,
`check_private_submodule_import`, `has_code_ptr`, `gap_target_module`,
`layout_hash_gate`/`LayoutHashGate`, `splice_inline_mod_to_bare`) are reached from
`worker.rs`, `eval.rs`, `cluster.rs`, and the sibling test file. Two equivalent
Rust forms exist:

- **(A) keep `process_form.rs` as the parent file** + add `mod macro_resolution;`
  etc. inside it (siblings resolve to `process_form/macro_resolution.rs`).
- **(B) convert to `process_form/mod.rs`** + the submodules.

**Recommendation: form (A) for process_form** — the file already declares
`mod tests;` (resolving to `process_form/tests.rs`, so the `process_form/`
directory already exists), and a slim `process_form.rs` parent that holds only the
module declarations + the cluster spine (`process_cluster_once` and its
direct Pass-1/2 callees) reads as the file's "table of contents." This keeps the
externally-cited public re-exports stable: the parent re-`pub(crate) use`s the
moved items so `crate::process_form::has_code_ptr` etc. keep resolving without
touching any caller. (`/dev` MAY choose form B if it proves cleaner; the module
*set* below is the load-bearing decision, not mod.rs-vs-parent-file.)

### 1.1 Target sub-module set

| New module | What moves (current line ranges) | Cohesion rationale |
|---|---|---|
| `process_form/macro_resolution.rs` | `SymbolTableMacroResolver` struct + `impl MacroResolver` (`:61–269`); `read_macro_meta` (`:277–293`); `resolve_macro_sexp_from` (`:311–324`); `compile_macro_with_state` (`:332–366`); `try_expand_sexp` + `ExpandOutcome` (`:508–571`); `qualify_expanded_sexp` (`:583–634`); `macro_clause_jit_name` (`:2891`); `compile_macro_if_needed` (`:2803–2848`); `compile_macro_clause_inline` (`:2859–2881`); `compile_macro_for_repl` (`:2916–2924`) | The on-demand macro-recognition + clause-compile + expansion-walk family. Single concern: "given a macro head in a form being checked, recognize it (with the prelude outer-scope fallback) and ensure its clause code is in memory, then expand." All of it threads `ModuleCompiler`/`CheckState` + the symbol tables. `macro_clause_jit_name`/`has_code_ptr` are its shared name/probe primitives. |
| `process_form/macro_clause.rs` | `compile_macro_clause_core` (`:380–454`); `compile_macro_clause_with_state` (`:466–500`) | The macro-clause *compiler* — the SINGLE implementation (`_core`) + its two thin adapters per `src/CLAUDE.md §"Macro-clause single implementation"`. Kept distinct from `macro_resolution` because it is the **codegen** of a clause (synthesize → expand-qq → build → check → `inline_jit_codegen_for_names`), a different concern from *recognizing/driving* a macro. `compile_macro_clause_inline` (the `ModuleCompiler` adapter) lives with the resolution family because it sources refs from `ctx`; `_with_state`/`_core` live here. *(See §4.A note — the prelude-fallback leaked-default in `_with_state` is unrelated to the §4 display dedup; leave it.)* |
| `process_form/form_dispatch.rs` | `FormKind` enum (`:643–650`); the four `record_*_on_symbol_table` writers (`:671–715`); `classify_form` (`:724–790`); `separate_macros` (`:1001–1026`); `register_macro_in_module` (`:1133–1221`); `pass1_register` (`:2934–2943`, no-op shim); `register_default_methods` (`:2952–2961`); `wrap_exprs_as_defns` (`:3177–3206`) | Structural-form **classification + Pass-1 registration**: turn raw sexps into `FormKind`, write the structural-decl Vecs onto the table, separate macros, register defmacro entries + default-method deferrals, wrap bare exprs. One concern: the pre-typecheck shaping of a cluster's forms. |
| `process_form/dependency.rs` | `BlockAction` enum (`:805–812`); `handle_import` (`:1511–1627`); `check_private_submodule_import` (`:1449–1500`); `handle_export` (`:2159–2227`); `handle_mod` (`:2260–2321`) + `register_submodule_alias` (`:2238–2252`); `drive_submodule` (`:2333–2399`) + `drive_submodules` (`:2407–2423`); `drive_module_dep` (`:1662–1726`); `fq_module_is_loaded` (`:1636–1638`); `gap_target_module` (`:1735–1744`); `register_dep` (`:1767–1811`); `inject_prelude_if_needed` (`:2973–3047`) + `sexps_reference_prelude` (`:3051–3088`); `write_inline_mod_to_disk` (`:2607–2644`); `rewrite_parent_inline_mod` (`:2658–2699`) + `splice_inline_mod_to_bare` (`:2728–2756`) + `find_inline_mod_span` (`:2768–2790`) | The **dependency-driving + structural-handler** family — the gap-orchestration crossing point named in the module header. Every function here either (a) resolves a structural decl into a scheduler `register_module`/`block_for_typecheck` edge, or (b) is its file-IO support (inline-mod write/splice). `register_dep` is the shared per-dep prologue (the F-L residue from `audits/src-s87.md`); `drive_module_dep` is the single FQ-autoload drive seam. This is the largest module by LOC; it is the one cohesive concern that *cannot* be cut finer without splitting the gap protocol (see §5 risk). |
| `process_form/cache_restore.rs` | `try_cache_hit_load` (`:1829–2065`, **split first — see §3.1**); `register_transitive_cached_imports` (`:2083–2149`) | Disk-cache restoration: validity check → meta decode → table install → platform re-resolve → scheduler register → transitive recurse. Self-contained against `cache_restore`'s callers in `dependency.rs` (which call `try_cache_hit_load` before falling through to `register_dep`). Lifts out cleanly per `audits/s87-maintainability.md §2.2`. |
| `process_form/platform.rs` *(optional sub-cut)* | `handle_platform` (`:2503–2604`); `layout_hash_gate` + `LayoutHashGate` (`:2432–2479`) | Platform-form handling: DLL load + §7.2 type-module pre-resolve drive + layout-hash gate + sig registration. ~150 LOC, one concern. **Optional**: if `/dev` prefers a 5-module split, fold `handle_platform`/`layout_hash_gate` into `dependency.rs` (it calls `drive_module_dep` + `register_platform_in_tc`). Recommended as its own file — it is the only structural handler that touches the DLL/schema subsystem, and `layout_hash_gate` is already extracted-for-testability. |

**Spine that stays in the parent `process_form.rs`:** `process_cluster_once`
(`:852–997`), `finalize_cluster` (`:1043–1125`), `pass2_check_bodies_with_expansion`
(`:1249–1306`), `process_regular_form` (`:1318–1422`), `Pass2Result` enum
(`:1225–1237`), `clear_module_codegen` (`:3097–3173`). These are the cluster
orchestration — the file's reason to exist — and they call across into every
submodule above. Keeping them in the parent makes the parent the legible spine.

### 1.2 Visibility hazards (process_form)

Everything currently `fn` (module-private) that a *sibling submodule* now calls
must widen to `pub(super)` (visible to the parent + siblings via the parent) or
`pub(crate)`. Concretely:

- The spine in the parent calls into every submodule → those submodule fns are
  `pub(super)` (`classify_form`, `handle_import`/`export`/`mod`/`platform`,
  `separate_macros`, `register_macro_in_module`, `register_default_methods`,
  `pass1_register`, `wrap_exprs_as_defns`, `try_expand_sexp`,
  `process_regular_form`'s callees, `drive_submodules`, `inject_prelude_if_needed`,
  `compile_macro_if_needed`, `finalize_cluster`'s callees `drive_module_dep`/
  `gap_target_module`/`fq_module_is_loaded`).
- `macro_resolution` ↔ `macro_clause`: `compile_macro_with_state` calls
  `compile_macro_clause_with_state` → `pub(super)`. `compile_macro_clause_inline`
  (in `macro_resolution`) calls `compile_macro_clause_core` → `pub(super)`.
- `dependency` calls `try_cache_hit_load` + `register_transitive_cached_imports`
  in `cache_restore` → both `pub(super)`. `cache_restore` calls back into
  `register_dep` (`dependency`) → `pub(super)`.
- `has_code_ptr` is already `pub(crate)` (reached from `worker.rs`) — keep. It
  belongs in `macro_resolution` (its only in-file callers) but stays `pub(crate)`.
- Items already `pub`/`pub(crate)` and cited externally — keep their visibility and
  **re-export from the parent** so external paths (`crate::process_form::X`) are
  unchanged: `process_cluster_once`, `compile_macro_for_repl`, `has_code_ptr`,
  `gap_target_module`, `check_private_submodule_import`,
  `record_imports_on_symbol_table`, `record_submodule_on_symbol_table`,
  `layout_hash_gate`, `LayoutHashGate`, `splice_inline_mod_to_bare`.
  (`record_imports_on_symbol_table`/`record_submodule_on_symbol_table` are
  `pub(crate)` and referenced from the test file — keep `pub(crate)` and re-export.)

### 1.3 Migration order (process_form)

1. **`cache_restore.rs` first** — it is the cleanest lift (one entry point
   `try_cache_hit_load` + one helper, no callers of the parent spine; it only
   calls `register_dep`, which stays in `dependency`/parent during this step,
   reachable as `super::register_dep`). Do the §3.1 function split *inside this
   move* so the file lands already-decomposed. Run suite.
2. **`macro_clause.rs`** — `_core` + `_with_state`. Self-contained codegen; no
   spine dependency beyond the already-`pub(crate)` `inline_jit_codegen_for_names`
   (in `worker.rs`). Run suite.
3. **`macro_resolution.rs`** — the resolver + walk + on-demand compile. Depends on
   `macro_clause` (step 2). Run suite.
4. **`form_dispatch.rs`** — classification + Pass-1 registration. Run suite.
5. **`dependency.rs` + `platform.rs`** — the gap-orchestration family + platform
   handler last (largest, most spine-coupled). Run suite.
6. **Re-home the test sibling.** `process_form/tests.rs` currently `use super::*`.
   After the split, `super` is the parent; the parent re-exports all moved items,
   so `use super::*` continues to resolve **iff** the parent re-exports cover every
   symbol the tests touch. Audit the test file's `use`s; widen re-exports as needed
   (or move topical test fns next to their submodule as `process_form/<sub>/tests.rs`
   if the test file naturally partitions — optional, defer to `/dev` judgement).

---

## 2. `src/session_v4.rs` (~1428 prod LOC) → `session_v4/` submodules

### 2.0 Form of the split

`session_v4.rs` is `pub(crate) mod session_v4;` in `lib.rs` and is the most
externally-cited module in the crate — `CompilerSession`, `SharedState`,
`SessionSettings`, `RunMode`, `EvalResult`, `TypecheckProduct`, `Introspection`,
`SymbolCategory`/`SymbolInfo`/`SymbolDescription`, `ModuleIntroductionOutcome`,
`TestRunnerState`, `discover_tests_extern`, `parens_balanced`, plus the relocated
`populate_ring0_got_slots`/`is_comment_only`/`intrinsic_type_from_name` and the
re-exports `format_result_value`/`QUIT_SENTINEL` are reached from `main.rs`,
`eval.rs`, `repl.rs`, `worker.rs`, `cluster.rs`, `platform.rs`.

The decisive complication: **`CompilerSession`'s `impl` blocks are spread across
sibling modules already** (`eval.rs`/`repl.rs` carry `impl CompilerSession` blocks
per `src/CLAUDE.md §"Session/REPL module decomposition"`, which is why six fields
are `pub(crate)`). Splitting `session_v4.rs` internally adds *more* sibling
`impl CompilerSession` blocks — the same proven pattern. Use **form (A)**: keep
`session_v4.rs` as the slim parent holding the `CompilerSession` + `SharedState`
**struct definitions** and the module declarations + re-exports; move the free
functions and the lifecycle `impl` methods into submodules. The struct definitions
stay in the parent because every submodule's `impl CompilerSession` block needs the
field set visible, and a struct must have a single definition site.

### 2.1 Target sub-module set

| New module | What moves (current line ranges) | Cohesion rationale |
|---|---|---|
| `session_v4/types.rs` | `RunMode` + `impl RunMode` (`:103–126`); `SessionSettings` (`:133–143`); `CommandResult` (`:150–159`); `EvalResult` + `impl EvalResult` (`:169–219`); `parens_balanced_pub`/`parens_balanced` (`:228–263`); `TypecheckProduct` (`:279–293`); `Introspection` (`:295–302`); `SymbolCategory`/`SymbolInfo`/`SymbolDescription` (`:314–351`); `ModuleIntroductionOutcome` (`:614–625`); `resolve_priority_worker_count` (`:594–603`); `dedup_platform_names_preserving_order` (`:2289–2300`); `extract_def_name_from_sexp` (`:2305–2323`); `is_comment_only` (`:3124–3129`); `intrinsic_type_from_name` (`:3131–3139`) | The **data-transfer + pure-helper layer**: every value type the binary surface passes around (settings, results, introspection DTOs, symbol-display DTOs, the run-mode enum) plus the leaf pure functions (`parens_balanced`, the dedup/extract/comment/type helpers, the worker-count clamp). Zero session-state dependency — all are `&self`-free or operate on borrowed args. This is the most reusable, most testable cut (Principle 5). |
| `session_v4/shared_state.rs` | `SharedState` struct **definition stays in the parent** (see §2.0) — but its *doc-heavy field block* and the `ReadOnlyMacroResolver` struct + `impl MacroResolver` (`:41–79`) move here. | `ReadOnlyMacroResolver` (the `/expand` read-only recognizer) is the one piece of `SharedState`-adjacent behavior that is NOT a `CompilerSession` method and NOT a DTO — it borrows the shared maps directly. *Caveat:* if moving the `SharedState` definition itself proves cleaner for `/dev` (form B with `session_v4/mod.rs`), `SharedState` may live here; the field-privacy story is unaffected (its fields are already `pub`). Recommended: keep both struct defs in the parent, put only `ReadOnlyMacroResolver` here. |
| `session_v4/lifecycle.rs` | `impl CompilerSession` — `new` (`:747–963`, **split first — §3.2**) + all the accessor/lifecycle methods: `project_root`/`lib_dirs`/`platform_dirs`/setters (`:966–1018`), `current_module_path`/`set_current_module`/`current_symbol_table`/`module_table` (`:1020–1083`), `introduce_module`/`introduce_module_blank`/`try_load_cached_for_introduction`/`find_module_source`/`resolve_module_by_name` (`:1085–1181`), `init_watcher` (`:1183`), `symbol_source`/`symbol_sexp`/`symbol_clif` (`:1219–1243`), the second `impl` block `list_user_definitions`…`entry_module` accessors + watcher reload + `register_module`/`re_register_module`/`register_module_with_source`/`trampoline`/`lookup_main_*`/`wait_*`/`mark_entry_eval_owned`/`shutdown`/`register_entry_module`/`link_by_name`/`linked_platform_link_data` (`:1245–2287`); `impl Drop for CompilerSession` (`:2325–2338`); `populate_ring0_got_slots` (`:3092–3121`) | The **session lifecycle** — construct, accessors, module registration, watcher reload, link, shutdown/Drop. This is the residual responsibility set `src/CLAUDE.md §"Session/REPL module decomposition"` names for `session_v4.rs`; it is one coherent concern (the session's own lifetime + the module-graph operations it owns) and is the bulk of the file. `populate_ring0_got_slots` is a `new`-helper, lands here. |
| `session_v4/nice_worker.rs` | `spawn_nice_workers` (`:2356–2371`, `#[cfg(test)]`); `nice_worker_loop` (`:2387–2425`); `compile_module_object` (`:2437–2586`, **split first — §3.3**) | The **nice-worker object-codegen subsystem**: the low-priority thread loop + the single-module `.o`/`.meta.json` writer. One concern (cache-write side codegen), runs on its own threads, touches only `&SharedState`. Lifts cleanly. |
| `session_v4/test_runner.rs` | `TestOutcome` (`:2599–2603`); `discover_test_names` (`:2611–2643`); `run_test_by_name` (`:2651–2715`); `TestRunnerState` + safety impls + `stub` (`:2732–2758`); `TEST_RUNNER` thread-local + `set_test_runner_state` (`:2760–2767`); `alloc_heap_adt` (`:2780–2790`); `discovered_test_wrapper` (`:2807–2824`); `alloc_test_wrapper_closure` (`:2830–2837`); `EligibleTest` (`:2841–2844`); `discover_eligible_tests` (`:2855–2887`); `test_scheme_is_eligible` (`:2894–2908`); `discover_tests_extern` (`:2926–2967`); `read_module_paths`/`alloc_empty_vec`/`alloc_vec_from` (`:2971–3018`) | The **test-discovery subsystem** — the host-promised `discover-tests` extern + its TestRunnerState + the late-bound wrapper-closure machinery + the heap-marshalling helpers. Self-contained per `src/CLAUDE.md §"Test discovery"`; the only session-side coupling is the `tc_modules` raw pointer patched in `new` (which stays in `lifecycle`). |

**Spine that stays in `session_v4.rs` (parent):** the `use`/import block, the
`pub use crate::display::format_result_value;` + `pub use crate::repl::QUIT_SENTINEL;`
re-exports, the `CompilerSession` struct definition (`:632–731`), the `SharedState`
struct definition (`:367–588`), and the module declarations + re-exports of moved
items. The five `#[cfg(test)] mod X;` declarations re-home (see §2.3).

### 2.2 Visibility hazards (session_v4)

- **`SharedState` fields are already `pub`** — `nice_worker.rs`, `test_runner.rs`,
  and `lifecycle.rs` all read them through `&SharedState`/`&self.shared`; no change.
- **`CompilerSession` fields** — the six already-`pub(crate)` fields
  (`worker_pool`, `current_repl_module`, `repl_check_state`, `repl_input_active`,
  `warnings`, `entry_module`) plus `shared`/`error_modules`/`watcher` are reached by
  the `lifecycle.rs` `impl` block. Because `lifecycle.rs` is a *sibling module* (not
  the defining module), Rust field privacy requires these to be `pub(crate)`.
  `shared` is already `pub`; `error_modules`/`watcher` are currently bare (private)
  — **widen to `pub(crate)`** (same pattern, same rationale as the FIXME-0109 Wave-D
  six fields). Document the widen with the existing `// pub(crate) (FIXME 0109 Wave D)
  — module-scoped field privacy` style comment, extended to "+ S87 §2.2".
- **Free fns that move but are called from the parent or other submodules** widen to
  `pub(crate)`: `resolve_priority_worker_count` (called by `new` in `lifecycle`),
  `populate_ring0_got_slots` (already `pub(crate)`), `nice_worker_loop` (called by
  `new`), `compile_module_object` (called by `nice_worker_loop` — same module),
  `set_test_runner_state`/`discover_tests_extern`/`TestRunnerState`/`TestOutcome`/
  `discover_test_names`/`run_test_by_name` (already `pub(crate)`/`pub` — keep).
- **`#[cfg(test)] pub fn spawn_nice_workers`** is referenced from `scheduler.rs`
  tests (`src/CLAUDE.md` notes it) — keep `pub` and **re-export from the parent** so
  `session_v4::spawn_nice_workers` resolves unchanged.
- **The `unsafe impl Send/Sync for TestRunnerState`** must move *with*
  `TestRunnerState` into `test_runner.rs` (orphan-rule: the impl must be in the
  type's defining crate — same crate, any module is fine, but keep it adjacent).
- **`TEST_RUNNER` thread-local + the raw-pointer patch in `new`.** The patch site
  (`new`, in `lifecycle.rs`) writes `(*trs_ptr).tc_modules = …`. `tc_modules` is a
  private field of `TestRunnerState` (now in `test_runner.rs`). The patch uses an
  `unsafe` raw-pointer cast, not field access through a reference — BUT it names the
  field `tc_modules` and the type `TestRunnerState`. Field-name access across module
  boundary requires the field be reachable: **make `TestRunnerState.tc_modules`
  `pub(crate)`** (it is currently private). Alternatively add a
  `pub(crate) fn set_tc_modules(&self, ptr: *const …)` on `TestRunnerState` in
  `test_runner.rs` and call that from `new` — *preferred* (keeps the unsafe write
  encapsulated with the type, avoids a `pub(crate)` raw-pointer field). Flag this as
  the one spot where a thin helper is cleaner than a visibility widen; it is a
  pure refactor of the existing `unsafe` block, behavior-identical.

### 2.3 Migration order (session_v4)

1. **`types.rs` first** — pure DTOs + leaf helpers, zero `CompilerSession`/
   `SharedState` method coupling. Lowest risk. Run suite.
2. **`test_runner.rs`** — self-contained subsystem; introduce the
   `set_tc_modules` helper (§2.2) so `new` stops touching the private field. Run suite.
3. **`nice_worker.rs`** — do the §3.3 `compile_module_object` split during the
   move. Run suite.
4. **`shared_state.rs`** — `ReadOnlyMacroResolver` only (and `SharedState` def if
   `/dev` chooses form B). Run suite.
5. **`lifecycle.rs` last** — the big `impl CompilerSession` blocks + `new` (split
   per §3.2) + `Drop`. Widen `error_modules`/`watcher` to `pub(crate)`. This is the
   highest-touch move; do it once everything it calls is already relocated. Run suite.
6. **Re-home the five test siblings.** Each `#[cfg(test)] mod X;` declaration moves
   to the submodule that owns the code it tests, and the file moves under that
   submodule's dir:
   - `platform_enumeration_dedup_tests` → `lifecycle/` (tests `linked_platform_link_data`
     + `dedup_platform_names_preserving_order`; the latter moves to `types.rs`, but
     the integration-style test exercises the `link_by_name` path — keep under
     `lifecycle/`, re-export `dedup_platform_names_preserving_order` from parent).
   - `discover_tests_extern_tests` → `test_runner/`.
   - `persistent_worker_tests` → `lifecycle/` (session new/shutdown lifecycle).
   - `bare_primitive_value_path_tests`, `list_classification_tests` → these test
     `check_bare_symbol_introspection`/`resolve_entry_for_display` which live in
     **`eval.rs`/`repl.rs`**, not session_v4 — they were declared here historically.
     Leave them declared in the parent `session_v4.rs` (the path resolves to
     `session_v4/<name>.rs`), OR relocate the declaration to `eval.rs`/`repl.rs`
     where the code under test lives — `/dev` judgement, no behavior impact. The
     minimal-change choice is to leave the `mod` declarations in the parent.

---

## 3. Over-budget function splits

These three functions exceed the `src/CLAUDE.md §Code Structure` ~100-line ceiling
and are split **as part of** the relevant module move (do the split in the same
change-set as the relocation so the file lands already-decomposed — Principle 6).
Each split is a pure *extraction*: lift a contiguous phase into a named helper,
call it from the now-shorter parent, identical code and order.

### 3.1 `try_cache_hit_load` (~254L, `process_form.rs:1829–2065`) → `cache_restore.rs`

Nine documented phases (numbered in-source `1.`…`9.`). Extract along the existing
phase comments into named helpers, each `pub(super)` within `cache_restore`:

- **`cache_validity_check(shared, dep, dep_file) -> Option<(CachedModule, String, bool)>`**
  — phases 1–3: already-installed guard, cache-dir check, source read + hash,
  manifest `is_cache_valid`, `try_load_cached_module`, `.o`-exists / generic-only
  gate (`has_codegen_targets`/`needs_inmem_load`). Returns `None` on any miss
  (caller returns `false`); returns `(cached, source_hash, needs_inmem_load)` on hit.
- **`extract_cached_specs(&cached) -> CachedSpecs`** — phase 4: pull `symbols`,
  `mangled_names`, `cached_platforms`, `cached_imports`, `cached_reexport_deps` out
  of the about-to-be-moved table into a small named struct (Principle: no bare
  tuple — `src/CLAUDE.md §Code Structure`).
- **`install_cached_table(ctx, dep, cached)`** — the `into_concrete` +
  `advance_next_id_past_table` + `install_module` triple (`:1966–1973`).
- **`reresolve_cached_platforms(ctx, shared, dep, &cached_platforms) -> bool`** —
  phase between install and register (`:1990–2021`): the per-platform
  `load_and_register_platform` + `kept_dlls` push; returns `false` (cache miss) on
  any platform failure.
- **`register_cached_with_scheduler(ctx, shared, dep, dep_file, symbols, source_hash, needs_inmem_load)`**
  — phases 5–8: scheduler register (object / no-object), typecheck-product create,
  `record_cache_hit`, `cached_module_insert`, file_to_module.
- **transitive recurse** stays as the two `register_transitive_cached_imports`
  calls (phase 9) — already its own fn.

`try_cache_hit_load` becomes a ~40-line orchestrator: validity → extract → install
→ platforms → register → recurse → `true`. **Behavior-preserving:** the early-return
`false` on every miss path is preserved exactly (each helper returns the miss
signal; the orchestrator threads it). Note the delicate ordering invariant
(extract-before-move-of-symbol_table, `:1892`) is honored by `extract_cached_specs`
running before `install_cached_table`.

### 3.2 `CompilerSession::new` (~216L, `session_v4.rs:747–963`) → `lifecycle.rs`

A long-but-linear constructor. Extract the independent setup phases into private
helpers (free fns or `CompilerSession`-associated fns), called in order from `new`:

- **`build_object_cache(&settings, &project_root) -> Arc<ObjectCache>`** — the
  cache-dir + CacheState + `ObjectCache::new` block (`:759–774`).
- **`seed_session_symbol_tables(entry_module, &next_type_id) -> DashMap<…>`** — the
  symbol-table construction: `ensure_module_exists(entry)`, the `PRIMITIVES_TABLE`
  `into_concrete` mount, `mount_synthetic_modules`, `populate_ring0_got_slots`
  (`:787–863`). Returns the populated map (and takes/returns `next_type_id` by ref).
- **`build_shared_state(…) -> Arc<SharedState>`** — the `SharedState { … }` literal
  + the `test_runner_state` build + the post-construction `tc_modules` patch
  (now via the §2.2 `set_tc_modules` helper) (`:871–915`).
- **`spawn_worker_threads(&shared, priority_workers, nice_workers) -> (Vec<Handle>, Vec<Handle>)`**
  — the two spawn loops (`:917–946`).

`new` becomes a ~50-line sequence: resolve dirs → `build_object_cache` → counts →
`seed_session_symbol_tables` → `build_shared_state` → `spawn_worker_threads` →
`CompilerSession { … }` literal. **Behavior-preserving:** the strict construction
ordering (primitives mount before synthetic mount before GOT-populate; Arc built
before the unsafe pointer patch before any thread spawn) is preserved because the
helpers are called in the same order; the unsafe single-writer-pre-spawn invariant
(`:910`) is unchanged (patch still runs inside `build_shared_state`, before
`spawn_worker_threads`).

### 3.3 `compile_module_object` (~150L, `session_v4.rs:2437–2586`) → `nice_worker.rs`

> Note: `audits/src-s87.md §F-D` cites this at ~174L; the maintainability pass at
> ~309L (the latter looks like a mis-count to file-end — the fn ends at `:2586`).
> Either way it is over budget. Extract the codegen pipeline phases:

- **`write_module_meta(shared, module, &meta_path)`** — the `.meta.json` write
  (clone table → `write_meta`) (`:2461–2479`), incl. the parent-dir ensure.
- **`enumerate_codegen_names(shared, module) -> Vec<Symbol>`** — the
  `defined_symbols()` collection (`:2486–2494`).
- **`record_empty_codegen(shared, module)`** — the generic-only / empty-batch
  manifest record + return (`:2495–2506`).
- **`emit_object(shared, module, &names) -> Option<Vec<u8>>`** — ISA build +
  ObjectBuilder + `compile_to_module` + `finish().emit()` (`:2508–2565`); returns
  `None` on any non-fatal codegen failure (caller returns).
- **`write_object_and_record(shared, module, &o_path, &obj_bytes)`** — the `.o`
  write + `record_compiled` + `append_o_path` (`:2569–2585`).

`compile_module_object` becomes a ~25-line orchestrator. **Behavior-preserving:**
every early-`return` (meta-dir failure, empty names, ISA/builder/compile/emit
failure, `.o` write failure) maps to the corresponding helper returning the
miss/`None` signal; the `CRANELISP_CODEGEN_TRACE`-gated `eprintln!`s stay inside
their phase helpers verbatim.

---

## 4. Src-side prelude-fallback dedup (Principle 7)

**Verification of the audit claim (prompt asks).** The re-inline sites flagged by
`audits/src-s87.md §F-G` are **both in `repl.rs`** — `process_form.rs` does NOT
re-inline the introspection-display hop (its `prelude_fallback` reads are the
*compile-path* recognition/injection sites, which are correct and out of scope for
this dedup). The canonical helper is `repl.rs:559 lookup_with_prelude_fallback`
returning `Option<(ModuleEntry<Code>, ModuleFullPath)>`, already used by
`handle_sig`/`handle_doc`/`handle_info` (`:613,:624,:830`).

| Re-inline site (file:line) | Walk implemented | Route through |
|---|---|---|
| `repl.rs:307–346` (`describe_symbol`) | current → prelude (bit-gated, `current != prelude`) → root `""` | `lookup_with_prelude_fallback(name)` — **exact match** to the canonical walk (current → prelude → root). |
| `repl.rs:1690–1712` (`format_eval_result_body`) | current → prelude (bit-gated, `cur != prelude`) — **no root tier** | `lookup_with_prelude_fallback(name)` — see the §4.1 caveat below. |

This is `/dev` work (the canonical helper is `/int`-owned code in `repl.rs`, not a
process_form concern), but it is in the same Wave-5 sub-wave and `/design` records
the exact routing so `/dev` does not re-derive it:

- **`describe_symbol` (`:307–346`):** replace the inline `let (entry, resolved_module)
  = { … }` block with `let (entry, resolved_module) =
  self.lookup_with_prelude_fallback(name)?;`. The canonical helper returns a *cloned*
  `ModuleEntry<Code>` (the inline also `.cloned()`s), and the same module-precedence,
  so this is behavior-identical. The downstream `FQSymbol { module: resolved_module, … }`
  + the `match &entry { … }` consume the same shapes.

### 4.1 Caveat for `format_eval_result_body` — DO NOT blindly route

`format_eval_result_body` (`:1690–1712`) currently walks **current → prelude only,
with NO root `""` tier**, whereas `lookup_with_prelude_fallback` *adds the root
tier*. Routing it through the canonical helper would make a bare special-form name
(`if`/`match`) — which lives at root `""` — newly resolve in the eval-result value
display, where today it returns the `None` arm (`"{symbol} ; defined"` or the
TraitImpl fallback). That is a **behavior change**, not a pure dedup.

**`/design` ruling:** route it through the canonical helper (the root tier is the
*correct* behavior — a special form's value display should chain-follow like any
name, consistent with `describe_symbol`/`/sig`), BUT this crosses the
behavior-preserving line, so it is **not** part of the mechanical decomposition
change-set. `/dev` files it as a separate small change with its own unit test
asserting the value-display of a bare special-form / prelude name, OR the dedup
here is done with a **`root: bool` parameter** added to
`lookup_with_prelude_fallback` (default-true callers keep current behavior;
`format_eval_result_body` passes `root: false` to preserve its exact current
two-tier walk). The parameterized form is the strictly behavior-preserving option
and is the recommended one for this sub-wave; the "let root resolve too" cleanup
can follow as its own guarded change. **Flag to `/review`:** confirm which option
landed and that no eval-result display test changed output.

> Interaction with Wave-0/Wave-3: the §F-A `derive_codegen_batch` DEF-1 seam
> (`worker.rs`) and the §3 DEF-1 cross-crate "one resolution seam" question are the
> Wave-2 `/arch` synthesis's concern (`audits/src-s87.md §3`), NOT this dedup. This
> sub-wave touches only the two *display* re-inlines; it does not alter codegen-batch
> derivation. Keep them separate so the `/arch` seam work is not entangled with a
> mechanical display dedup.

---

## 5. Risk notes for `/dev`

- **Single-agent, serial.** Both files are touched by the same `/dev` agent,
  serially, per `CLAUDE.md §Testing` ("single agent at a time for source-touching
  work" — worktree isolation is broken here). Run `cargo nextest run` after **each**
  numbered migration step (§1.3 / §2.3), not just at the end — a mis-routed `use`
  or a missed `pub(super)` surfaces as a compile error immediately, and the
  step-granular green confirms behavior preservation incrementally.
- **The 14 known-defect guards are the floor.** A genuine regression is any RED
  beyond the named guards (`CLAUDE.md §Testing "Failing-not-ignored…"`). A
  decomposition that flips a guard *green* is also suspect (means a code path moved
  in a way that changed behavior) — investigate, don't celebrate.
- **`process_form.rs` `dependency.rs` is the load-bearing concern — do not over-cut.**
  The gap-orchestration protocol (`handle_import`/`drive_module_dep`/`finalize_cluster`'s
  gap mapping) is the SOLE crate-crossing where a `ResolutionGap` becomes a scheduler
  call (`process_form.rs` header; `src/CLAUDE.md §Cluster-Atomic Orchestration`).
  The Pass-0 handlers (`handle_*`) and the drive seam (`drive_module_dep`) and the
  per-dep prologue (`register_dep`) MUST stay together — splitting block/notify/drive
  across files is the exact anti-pattern `audits/s87-maintainability.md §2.x` warns
  against for `scheduler.rs` ("do not split block/notify/wait across files"). Keep
  `dependency.rs` as one module even though it is the largest; cohesion beats a LOC
  target here (Principle 6 — budget the complexity where the spec demands it).
- **The S78 retry-from-top + FIXME 0342 deferred-submodule ordering** is woven
  through `process_cluster_once` → `finalize_cluster` → `drive_submodules`. These
  three stay in the parent spine (§1.1) precisely so the retry-from-top control flow
  reads in one file. Do not relocate `finalize_cluster` into `dependency.rs` even
  though it calls `drive_module_dep` — its caller is the spine.
- **`compile_macro_clause_*` is a documented single-impl-with-adapters** (`src/CLAUDE.md
  §"Macro-clause single implementation"`). The §1.1 cut keeps `_core`/`_with_state`
  together in `macro_clause.rs` and `_inline` (the `ModuleCompiler` adapter) in
  `macro_resolution.rs`. Do not merge the adapters into `_core` (that would re-collapse
  a deliberate seam) and do not duplicate `_core` (the byte-identical-body convergence
  must not regress — Principle 7).
- **`session_v4.rs` `new` ordering is invariant-critical** (§3.2): primitives mount
  → synthetic mount → GOT populate; Arc build → unsafe `tc_modules` patch → thread
  spawn. The extraction MUST preserve call order; the `set_tc_modules` helper (§2.2)
  must run before `spawn_worker_threads` (single-writer-pre-spawn, the `// SAFETY:`
  comment at `:910`). Carry that SAFETY comment onto the helper.
- **The `unsafe impl Send/Sync for TestRunnerState`** moves with the type
  (`test_runner.rs`); the raw `tc_modules` field stays private + gains a
  `set_tc_modules` setter rather than a `pub(crate)` raw-pointer field (§2.2).
- **Re-exports are the compatibility membrane.** Every externally-cited `pub`/
  `pub(crate)` item that moves into a submodule MUST be re-exported from the parent
  (`pub(crate) use self::<sub>::<Item>;`) so `crate::process_form::X` /
  `crate::session_v4::Y` paths in `worker.rs`/`eval.rs`/`repl.rs`/`main.rs`/
  `cluster.rs`/`platform.rs` resolve unchanged. This is what makes the split
  invisible to callers — verify by grepping each moved-and-cited symbol's external
  call sites compile without edit. (The §1.2 / §2.2 lists enumerate which items.)
- **Doc-comment volume.** Both files carry heavy sprint-history comment blocks
  (`audits/src-s87.md §F7` — "regressed/unchanged"). The comments move *with their
  function* — do not strip them in the split (that is a separate concern; stripping
  here would obscure the diff and lose the rationale `/review` reads against).

---

## 6. Quality-attribute disposition (this sub-wave)

| Attribute | Disposition |
|---|---|
| Simplicity (P6) | The driver. Three over-budget fns split to ≤~100L; two 1400–1765-LOC files become ≤~6 cohesive modules each. |
| Maintainability | Bounded blast radius — a future cache-restore change touches `cache_restore.rs`, a test-discovery change `test_runner.rs`, etc. The §5 "don't over-cut dependency.rs" note keeps the gap protocol legible. |
| Testability (P5) | Improved — `types.rs` (pure DTOs/helpers) and `cache_restore.rs`'s extracted phase helpers are unit-testable at finer seams; the existing sibling test files re-home onto their owning submodule. |
| Concurrency-safety | **Untouched in substance.** The nice-worker loop + `SharedState` field set + the `tc_modules` single-writer-pre-spawn invariant are preserved byte-for-byte; only their file location changes. The §2.2 `set_tc_modules` encapsulation does not alter the unsafe contract. No change to `design/int/concurrency*.md`. |
| Observability | Untouched — the `record_module_event`/`publish_thread_buffer` calls move with their functions. No change to `design/int/observability.md`. |
| Performance | Untouched — pure code relocation; no allocation/dispatch change. |

---

## 7. Next skills

- `/dev` (narrow, `src/`) — execute the two decompositions + the three over-budget
  splits per §1.3/§2.3/§3, serially, suite-green at each step. File the
  `format_eval_result_body` root-tier cleanup (§4.1) as its own guarded change if
  the parameterized behavior-preserving form is not taken.
- `/review` (narrow, `src/`) — confirm behavior preservation (no 15th red, no guard
  flipped), the re-export membrane is complete (external paths unchanged), the
  §5 cohesion notes held (`dependency.rs` not over-cut, `compile_macro_clause_*`
  single-impl preserved), and the §4.1 display dedup did not change eval-result output.
- `/arch` — the §F-A `derive_codegen_batch` DEF-1 seam + the §3 cross-crate
  single-resolution-seam question remain the Wave-2 `/arch` synthesis's concern;
  this sub-wave deliberately does not touch them.
