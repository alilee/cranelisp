# Int — Master Design (Binary surface — `src/` + `crates/cranelisp-exe-bundle/`)

Owner: `/design`. Single source of design intent for the integration layer (`src/` + `crates/cranelisp-exe-bundle/`). Authored Sprint 63; refreshed Sprint 64 against the pinned Decision 40 / 41 / 42 + Principle 14 / 15 configuration.

This document elaborates *within* the bounded context fixed by `design/arch/bounded-contexts.md` §6 and the public surface fixed by `design/arch/facades/int.md`. Where this document and either of those drift, the bounded-context statement and facade win — file FIXME `target: /arch` or update this doc accordingly.

> **S76 implementation plan — see `design/int/s76-implementation-plan.md`.** This master is S64-era and substantially stale w.r.t. the as-built (`cluster.rs`, `cache.rs`, `got_trace.rs`, `trace.rs`, `io_trace.rs`, `display.rs` have since landed in `src/`; many §14/§16 FIXMEs are resolved). The S76 plan is the authoritative sequencing for the facade-arc wash-through (W-Absorb), the parallel-JIT-pipeline collapse (W-Collapse), the LOCKED three-pass macro orchestration (W-Macro), W-Enablement, and host-wiring. Two master claims are **superseded by the S76 LOCKED W-Macro decision** (`macro-availability-model.md` §0): (1) §2 note 4 / §6.3's "macro-vs-fn discrimination is orchestrator-owned via a `MacroInMem` gap peek" — recognition is now a `cranelisp_types::resolve_macro_head` query in int's Pass-1 `process_cluster` expand loop over the committed view, and the `block_for_macro_codegen` path is DELETED not wired (no same-module non-macro clause-callee case exists under the lock); (2) §3/§6's "macro expansion is frontend's job / `int::process_form` is the gap-orchestrator not the expander" — int now OWNS macro execution via `cranelisp_types::MacroExpander` over `src/expander.rs`'s invocation core + `src/marshal.rs`, and the free-standing `expand_sexp_recursive` walk / `SymbolTableMacroResolver` DELETE (BC §6 int bullet).

> **Why int is the largest surface.** int integrates everything. It owns three internal cadences (compilation, REPL, watcher), four observability sinks (scheduler trace, IO trace, GOT trace, introspection store), the only `Code` carrier instantiation site, the gap-orchestration crossing point, the slash-command surface, the cache writer, the file watcher, the line editor, the CLI, the `--link` driver, the prelude loader, and the error formatter. By design, int has the most subordinate docs and the largest LOC count.

> **Audit reconciliation.** `audits/src-20260423.md` (262 lines, 2026-04-23) is the most recent crate audit. It pre-dates Decisions 38 + 39 by 5 days and pre-dates Decisions 40 + 41 + 42 by ten days; its current-state findings (the seven F1–F7 structural issues) remain ground truth, but its target-state direction is partially superseded by the S64 Decisions. Where audit recommendations and 38/39/40/41/42 agree, both are cited; where the Decisions sharpen or supersede, the new model wins and is flagged inline.

---

## 1. Bounded-context recap

Per `design/arch/bounded-contexts.md` §6 — `int` is the *integration layer* spanning two crate paths (`src/` and `crates/cranelisp-exe-bundle/`), treated as ONE surface for triad purposes. It hosts three internal cadences (compilation, REPL, watcher) with distinct execution shapes, coordinates the typed handoffs between them, owns all dev tooling (slash commands, tracing, observability, introspection), and is the only crate that knows the concrete carrier of compiled code.

**Owns**:
- `SharedState` construction and lifecycle (per Decision 38)
- `CompilerSession` — high-level facade `::main` constructs and drives
- Pipeline orchestration: `register_module` (with Phase 0), `process_form` (gap-retry loop), `eval`, `trampoline`
- `CompileScheduler` — single coordination authority (work dispatch + per-symbol/module wait/release)
- Worker pool — priority + nice loops, persistent (Decision 27)
- Object cache orchestration — sidecar `.meta.json` + `.o`, version-checked, cache-hit-via-`register_module`-recursive (Decision 37)
- File watcher — `notify`-based, polled at REPL prompt boundary
- REPL session: line editor, slash-command dispatch, prompt formatting, banner, eval cursor, `current_repl_module`, `regenerate_backing_file`
- Per-symbol introspection store on `SharedState.introspection` (mode-conditional Decision 38) — populated by parse + codegen, consumed by `/source`/`/sexp`/`/clif`/`/disasm`/`/time`
- Error formatter (`Sess::format_error`) — resolves `ErrorLocation` against introspection at display time (Decisions 39 + 42)
- REPL display / pretty-printing (Sess::format_eval_result, Sess::pretty_print) — including the relocated `display.rs` (post-FIXME 0108)
- Platform DLL session retention (`SharedState.kept_dlls`) and the `(platform "name")` load orchestration
- Diagnostic ring buffers — scheduler trace, IO trace (post-Decision 40), GOT trace (post-FIXME 0099). All env-var activated, all parallel `src/*_trace/` modules
- `--link` orchestration: validates `main`, emits `_main` alias `.o` (Decision 36), invokes system linker
- Exe-bundle: the alias-`.o` template + the static archive consumed by `--link`
- CLI parsing (`Action`, `ProjectTarget`, `SessionSettings`, `CliError`)

**Does not own**:
- Source parsing (frontend)
- Macro expansion logic (frontend; `int::process_form` is the gap-orchestrator, not the expander)
- Type inference (typecheck)
- Code emission (backend) — backend writes its own `Code::Jit` directly via Decision 41
- Runtime helpers — RC, allocator, string ops, IO trampoline (runtime)
- Platform ABI contract (platform)
- Boundary types (`cranelisp-types`, owned by `/arch`)

**Crosses the boundary**:
- **Inward**: the public surfaces of all five other crates (per `facades/int.md` §Consumed surface).
- **Outward**: nothing for other workspace crates — `int` is the application root. Exe-bundle exposes a startup stub used only by the system linker.
- **Window types**: cadence-scoped; not exposed to other crates.

**Architectural constraints (load-bearing)**:
- Mutual-import deadlock (Decision 30) — two modules that import each other deadlock the form-by-form scheduler. Documented; not fixed by this design. Workaround: `discover-tests`.
- One `CompilerSession` per process (pipeline-v4 §1).
- Per-batch JIT lifetime (Decision 31, amended by Decision 41 — per-symbol cardinality) — never a long-lived per-worker JIT.

---

## 2. Public surface

`design/arch/facades/int.md` is the authoritative public-API contract (810 lines). This document does not restate the surface; it elaborates the rationale and the internal architecture that backs it.

Three structural notes about the surface worth naming:

1. **`CompilerSession` is the high-level facade.** A single object that `::main` constructs and drives. Wraps an `Arc<SharedState>` (the worker-shareable subset) plus initiator-thread-only state (watcher channel, REPL eval cursor, worker pool handles, accumulated warnings). Every CLI mode (`--run`, `--link`, REPL) constructs the same `CompilerSession`; the only difference is which methods are invoked after `register_module`. Per Principle 11 (single pipeline; mode parameters) — there is exactly one `process_form`, parameterised by mode (and the mode discriminator IS `shared.introspection.is_some()`, not a separate flag).
2. **No re-exports of `cranelisp-types` items in int's public surface beyond what facades elsewhere already publish.** Per Principle 15 (facade types live with their behavior) — int IMPORTS from each implementation crate directly; the int facade re-exports `cranelisp-types` symbols that are part of int's documented API surface (per `facades/int.md` §"Re-exports from cranelisp-types") only as a convenience to consumers of the binary, which is itself a small audience (no out-of-tree dependents on the `cranelisp` binary crate as a library). The Principle-15 external-audience exception applies to platform alone.
3. **`Code` re-export per Decision 41.** `Code` lives in `cranelisp-backend/src/code.rs` (moved per Decision 41 from the previous `src/code.rs` location). int re-exports `pub use cranelisp_backend::Code;` for session-boundary `SymbolTable<Code, ()>` instantiation. Backend constructs `Code::Jit` directly inside `compile_to_module` and writes via `SymbolTable::write_code(&self, sym, code)`; int no longer wraps a backend return tuple. Principle 3 protection (no `cranelisp-types → cranelisp-backend` dep) survives intact.

---

## 3. Current-state summary (per file)

Direct read of `src/` at **Sprint 81** (post-S78 restructure; the S64 FIXMEs + S76 W-Macro/W-Collapse + S77/S78 cluster-atomic restructure have all landed). The two god-files (`session_v4.rs` 6,201, `worker.rs` 6,074) account for ~43% of the 28,592-LOC crate and remain the audit-F1/F2 decomposition target (FIXME 0109 Wave D).

> **S81 staleness correction (was: the S64 snapshot).** The pre-S81 table below claimed `lib.rs` ≈ 25 LOC / 18 public modules, `session.rs` was "legacy v3 session, delete", and listed pending relocations (`code.rs` → backend, `trace.rs`/`io_trace.rs` arrivals, `display.rs` merge) as future work. Those relocations **landed**: `code.rs` (166 LOC) is now the `SessionSymbolTable`/`SessionModuleEntry` alias home (the `Code` enum lives in `cranelisp-backend`, re-exported); `src/trace.rs` was **deleted** (the trace family relocated to `cranelisp-intrinsics`, 2026-06-04 ruling); `display.rs` did NOT merge into `pretty.rs` (both live). Most consequentially, **`session.rs` is no longer the v3 god-file** — see its row + §3.4. The LOC figures + status notes in the table rows below carry the **pre-S81 snapshot**; treat the per-FIXME notes added in §3.4 + §16 as the current overlay until a full /design refresh re-tabulates them.

| File | LOC | Primary responsibility | As-designed status |
|---|---:|---|---|
| `lib.rs` | 83 | Module registry — 5 binary-facing `pub mod` (`observability`, `session_v4`, `got_trace`, `io_trace`, `style` — all `main.rs` imports) + 3 facade-cited `pub mod` (`cluster`, `worker_pool`, `cache`) + `pub(crate) mod` for the rest (now incl. `process_form`, `session_setup`). | **FIXME 0109 Wave B re-confirmed (S81).** Every `pub mod` is justified by a `main.rs` `use cranelisp::…` import or a `facades/int.md` citation; the rest are `pub(crate)`. Already narrowed in the S67 hack-back; Wave B verified the split still holds (a `dead_code`/visibility audit, no structural change). No baseline impact (binary crate). |
| `main.rs` | 405 | CLI parsing + dispatch to Run / Link / REPL via `CompilerSession`. | Stable. The single mode-dispatcher; one path for Run/Link/REPL per Principle 11. |
| `session_v4.rs` | 6,452 | `CompilerSession` god-file: REPL UX, eval, dep registration, watcher, introspection, trace setup, worker lifecycle, link control, tests inline. | **Audit F1 (HIGH).** Decomposition target — split into `eval.rs` + `repl.rs` per §3.3 module map below. **Wave D (carried)** — the slash-command `handle_*` methods are `impl CompilerSession` over many private fields; a `repl.rs` split requires widening field visibilities to `pub(crate)` first (substantial churn), so it is deferred with Wave D, not forced under the S81 carry boundary. |
| `worker.rs` | 2,868 | Priority worker loop + nice worker loop + codegen/cache subsystem (`derive_codegen_batch`, `inline_jit_codegen_*`, `load_cached_module_via_linker`, `handle_cached_codegen`), the macro-compile state helpers, typecheck-dispatch shims (`build_program_compat`, `check_program_compat*`, `process_cluster_with_staging`), and the shared infra types `ModuleCompiler` / `ModuleCheckAccumulator` / `ClusterOnce`. | **FIXME 0109 Wave C LANDED (S81):** the cluster/per-form family (`process_cluster_once`, `process_regular_form` + ~40 family-private helpers) moved to `src/process_form.rs` (~3.0k LOC), shrinking worker.rs from 6,074 → 2,868. Residual Audit-F2 mirrored-path collapse (`_with_state`/`_inline`) is **Wave D (carried)**. |
| `process_form.rs` | 3,466 | **FIXME 0109 Wave C (S81):** the gap-orchestration form-processing family extracted from worker.rs — `process_cluster_once` (whole-cluster Pass-0/1/2 core, the worker/eval entry), `process_regular_form` (per-form expand→build→check), structural-form classification + handlers (`classify_form`, `handle_import`/`handle_export`/`handle_mod`/`handle_platform`), macro recognition + on-demand clause compile (`SymbolTableMacroResolver`, `compile_macro_*`), Pass-1 registration, Pass-2 expand-then-check, dependency driving (`drive_module_dep`, `register_dep`, cache-hit load), module prep/cleanup (`inject_prelude_if_needed`, `clear_module_codegen`, `wrap_exprs_as_defns`). | The permanent Wave-D seam named in §3.3. Sole crate-crossing where a `ResolutionGap` becomes a scheduler call (Principle 1/7). Shared infra types stay in `worker.rs` and are reached via `crate::worker::*`; `process_cluster_once`/`process_regular_form` are `pub`/`pub(crate)` and called by `cluster.rs` + `session_v4::process_single_form`. Has its own `#[cfg(test)] mod tests` (recognize / gap-target / module-alias / layout-hash / splice unit tests moved here). |
| `scheduler.rs` | 2,361 | `CompileScheduler` — work dispatch + per-symbol/module wait/release. | Stable. The single coordination authority. |
| `pipeline.rs` | 446 | Reusable pipeline helpers extracted from session_v4. | Stable; gathers helpers used by both worker and eval paths. |
| `expander.rs` | 517 | Macro-resolver glue between `cranelisp_frontend::expand` and the symbol table. | **FIXME 0098 Phase 4** — `expand_sexp_recursive` migrates to `cranelisp-frontend/src/expand.rs`; what stays in int is the `MacroEnv` adapter (subject to Frontend FIXME 6's "possibly dead" check). |
| `code.rs` | 397 | `Code` enum (legacy location). | **Decision 41 — relocates to `cranelisp-backend/src/code.rs`.** int retains a `pub use cranelisp_backend::Code;` re-export. The `SessionSymbolTable` / `SessionModuleEntry` aliases stay here (or migrate to `session_v4.rs`). |
| `observability.rs` | 1,362 | Scheduler/worker event log; trace flush guards; structured event taxonomy. | Stable. Renames to `src/scheduler_trace/` to fit the three-instance `*_trace` pattern (parallel to `src/io_trace/` and `src/got_trace/`). |
| `platform.rs` | 793 | DLL load (`load_platform_dll`), `resolve_platform_path`, `parse_type_sig`, manifest validation. | **FIXME 0104** — `load_platform_dll` constructs structured `PlatformError` per Decision 42; `Sess::format_error` adds a `Platform(PlatformError)` arm. Stringly-typed errors today; structured tomorrow. |
| `pretty.rs` | 662 | REPL display / value formatting. | Joins `display.rs` post-FIXME 0108; both are "REPL display orchestration" per BC §6 and want to live together. |
| `marshal.rs` | 493 | Sexp marshaling helpers used by macro pipeline. | Stable. |
| `cache_writer.rs` | 219 | Background `.o` + `.meta.json` emit thread (cache-write side, Sprint 56+). | Stable. |
| `save.rs` | 493 | `regenerate_backing_file` per Decision 39 — walks `defn_order`, reads `introspection[fq].source`, atomic write. | Stable. The `module_sources` field is gone; per-defn source on `Introspection.source` is the only source store. |
| `watch.rs` | 181 | `notify`-based file watcher; emits `FileChangeEvent`; polled at REPL prompt boundary. | Stable. |
| `exe.rs` | 695 | `--link` mode: alias-`.o` emission, system linker invocation. | Stable. Lives next to `crates/cranelisp-exe-bundle/`. |
| `bind_chain_analysis.rs` | 849 | §10.12 auto-IO-scheduling: post-expansion AST→AST transform inserting `Expr::ParBind` for data-independent, non-`Sequential` `bind!`-chain pairs. | **S84 (FIXME 0367): being WIRED LIVE.** Pre-S84 this pass was `#[allow(dead_code)]` with zero pipeline callers (no `Par` node ever emitted from user source). S84 wires `apply_bind_chain_analysis` into `process_form::finalize_cluster` over `expanded_program`/`final_working`, before `check_program_compat`, mode-uniform across `--run`/`--link`/REPL (single `process_cluster_once` core). Algorithm stable; the wiring is the work. See `design/int/bind-chain-analysis.md` §5 (live seam) + §5b (PO-0367.1 contract) + §5c (flag). |
| `style.rs` | 131 | Terminal style helpers (colours, attributes). | Stable. |
| `thread_util.rs` | 36 | Thread-naming helper for worker spawn. | Stable. |
| `session_setup.rs` | 525 | **Renamed from `session.rs` (FIXME 0109 Wave A, S81).** Session-construction helpers independent of `CompilerSession`: `CacheState`, `ProjectConfig` + `load_project_config_lib_dirs`, `assemble_lib_dirs`, `assemble_platform_dirs`, `resolve_prelude`, `determine_exit_code`, `apply_bind_chain_analysis`. | **FIXME 0109 Wave A LANDED (S81).** Verified no v3 `CompilerSession`/`Session` type remained (the only `struct CompilerSession` is `session_v4`'s); these helpers are live (callers: `cache.rs`, `platform.rs`, `session_v4.rs`, `worker.rs`). Renamed `session.rs` → `session_setup.rs` to shed the misleading "v3 lingering" connotation. `pub(crate)`-internal; no baseline impact. **S84 correction:** `apply_bind_chain_analysis` was the one *dead* helper in this list (`#[allow(dead_code)]`, zero callers); S84/FIXME 0367 wires it into `process_form::finalize_cluster` and drops the attribute — see `bind-chain-analysis.md` §5.3. |

**Total today**: 28,592 LOC across `src/`. The S64-snapshot relocations (above) have all landed; the headline god-files (`session_v4.rs` 6,201, `worker.rs` 6,074) remain the audit-F1/F2 decomposition targets (FIXME 0109 Wave D, carried to the next arc sprint per the S81 Phase-2 R1 carry boundary).

### 3.3 Target module map (FIXME 0109 Wave D — CARRIED)

The full decomposition target for the two god-files. **This is Wave D and is NOT in S81 scope** (the S81 Phase-2 R1 carry boundary; Principle 8 — a partial god-file split is itself interim debt). Recorded here so the carry is legible.

| Module | Responsibility |
|---|---|
| `session_v4.rs` (residual) | `CompilerSession` struct + lifecycle; `SharedState` construction; `Drop`; worker-pool spawn + join |
| `worker.rs` (residual) | `priority_worker_loop` + `nice_worker_loop`; per-cluster processing on `&SharedState` |
| `src/process_form.rs` | The shared gap-orchestration form chain — **LANDED (Wave C, S81)**: `process_cluster_once` + `process_regular_form` + ~40 family-private helpers. The permanent seam; Wave D builds on it, does not rework it. |
| `src/eval.rs` | REPL eval — wraps the form chain + appends `defn_order` for defining forms; trampolines expression forms |
| `src/repl.rs` | Slash-command dispatch, prompt formatting, banner, line-editor wrapper |

Wave D's extraction sequence (when it runs): `eval.rs` → `repl.rs` → residual `session_v4.rs`; for `worker.rs`, collapse the remaining mirrored paths into single implementations.

### 3.4 FIXME 0109 Waves A/B/C — LANDED (S81); Wave D carried

S81 landed the three terminal-shaped sub-steps of FIXME 0109 (A/B/C). Each is independently complete (a rename, a visibility re-confirmation, a clean extraction) and leaves the tree green (1252 passed / 0 failed / 1 skipped); none is a stepping-stone Wave D reworks (Principle 8). The carry boundary is: **A/B/C landed S81; Wave D + the dependent runtime/observability harvest cluster (FIXMEs 0116/0128/0129/0130/0132/0133/0135) co-carry to the next arc sprint** (the harvested tests need the post-Wave-D `#[cfg(test)]` module homes — `process_form.rs` already has one, established by Wave C).

- **Wave A — `session.rs` → `session_setup.rs` (LANDED, rename).** Confirmed by grep that no v3 `CompilerSession`/`Session` type remained (the only `struct CompilerSession` is `session_v4`'s) and no `crate::session::CompilerSession`/`Session` reference exists. The file held only live `CompilerSession`-independent construction helpers, so Wave A was the cosmetic rename (not a deletion): `git mv session.rs session_setup.rs`, updated the 6 `crate::session::` use-sites (in `cache.rs`, `platform.rs`, `session_v4.rs`, `worker.rs`) and `lib.rs`'s `pub(crate) mod` line. `pub(crate)`-internal; no baseline impact.

- **Wave B — narrow `lib.rs` (re-confirmed).** Re-confirmed the split against `facades/int.md` §"Public surface" + the actual `use cranelisp::…` imports in `main.rs`. The 5 binary-facing `pub mod` (`observability`, `session_v4`, `got_trace`, `io_trace`, `style`) are all `main.rs` imports; the 3 remaining `pub mod` (`cluster`, `worker_pool`, `cache`) are facade-cited; everything else is `pub(crate)` (incl. the new `process_form` + renamed `session_setup`). No demotion needed — the S67 hack-back split still holds. No baseline impact (binary crate).

- **Wave C — extract the `process_form` family (LANDED, clean extraction).** Extracted `process_cluster_once` (the whole-cluster Pass-0/1/2 core, the worker/eval entry) + `process_regular_form` (per-form expand→build→check) + their ~40 family-private helpers (structural-form classify/handlers, macro recognition + on-demand clause compile via `SymbolTableMacroResolver`, Pass-1 registration, Pass-2 expand-then-check, dependency driving, module prep/cleanup) into `src/process_form.rs`. The shared infra types (`ModuleCompiler`, `ModuleCheckAccumulator`, `ClusterOnce`) + the typecheck-dispatch shims (`build_program_compat`, `check_program_compat*`, `ensure_typecheck_product`, `leading_annotation_len`) stay in `worker.rs` (referenced by both the family and the codegen path / external callers) and are reached from `process_form.rs` via `crate::worker::*`. `worker.rs` shrank 6,074 → 2,868 LOC; `process_form.rs` is ~3.0k LOC. The recognize / gap-target / module-alias / layout-hash / splice **unit tests moved with the code** into `process_form.rs`'s new `#[cfg(test)] mod tests`; the private-submodule + introspection tests stayed in `worker.rs` (they share `mk_writer_test_ctx`, a worker-side `ModuleCompiler` builder) and reach the moved `check_private_submodule_import` / `has_code_ptr` / `record_*` via `use crate::process_form::{…}` (these four are `pub(crate)`). `cluster.rs` + `session_v4::process_single_form` call `process_form::process_cluster_once`; `session_v4` calls `process_form::compile_macro_for_repl`. Tree green; `pub(crate)`-internal, no baseline impact.

**Wave D — NOT landed (carried, per the carry boundary).** The `eval.rs` + `repl.rs` split out of `session_v4.rs` (6,452 LOC) was assessed and deferred: the slash-command `handle_*` methods are `impl CompilerSession` methods reaching many *private* fields of `CompilerSession`. Moving them to a sibling `repl.rs` requires first widening those field visibilities to `pub(crate)` (Rust field privacy is module-scoped) — substantial churn that risks the green suite, exactly the ballooning the S81 carry boundary guards against (Principle 8). The `worker.rs` mirrored-path collapse (`compile_macro_clause_with_state` / `_inline`) is likewise carried. Wave C's extraction already established the `process_form.rs` module home the harvest cluster needs, so the carry of Wave D does not block the harvested-test homes for the `process_form` family.

**Carry-boundary non-interim-debt argument (Principle 8).** A/B/C did not produce scaffolding Wave D tears out: A was a rename of an unrelated helper file; B was a visibility re-confirmation Wave D inherits unchanged; C extracted a module that §3.3 *names as a permanent home* (`src/process_form.rs`). Wave D, when it runs, moves `eval.rs`/`repl.rs` OUT of `session_v4.rs` and collapses `worker.rs`'s mirrored paths — it does not undo C's extraction. The partial split is along a seam the full split also respects; there is no rework.

---

## 4. SharedState architecture (Decision 38)

The central structural decision. `SharedState` is the formal worker-shareable subset of the session — defined in `facades/int.md` §"SharedState" and reproduced here for design-intent visibility:

```text
SharedState (interior-mutable; workers hold Arc<SharedState>):
  symbol_tables : DashMap<ModuleFullPath, SymbolTable<Code, ()>>
  scheduler     : Arc<CompileScheduler>
  cache         : Arc<ObjectCache>
  kept_dlls     : DashMap<PathBuf, Arc<DllHandle>>
  introspection : Option<DashMap<FQSymbol, Introspection>>          // mode-conditional
  settings, project_root, lib_dirs, platform_dirs                   // read-only after construction

CompilerSession (initiator-thread-only):
  shared              : Arc<SharedState>
  watcher             : Option<WatcherChannel>
  current_repl_module : ModuleFullPath
  repl_input_active   : Arc<AtomicBool>           // shared with watcher event handler via Arc clone
  worker_pool         : WorkerPool                // joins on Drop
  warnings            : Vec<Warning>              // initiator-collected
```

### 4.1 Per-symbol mutability discipline

After Phase 0 (`register_module`), no code path holds a whole-module `&mut SymbolTable`. Per-symbol writes go through `SymbolTable::insert_or_update(&self, sym, entry)` and `SymbolTable::write_code(&self, sym, code)`, which acquire the inner DashMap's per-entry write lock briefly.

**The two `&mut SymbolTable` operations**:
1. **Phase 0** in `register_module`: `entry(m).or_default()` → `write_structural_decls(decls)` + `defn_order` seed → drop RefMut. Microsecond-scale; once per module.
2. **REPL append**: `append_defn_order(&mut self, sym)` per eval that introduces a new defn. Brief initiator-thread `&mut` hold (microseconds).

Everything else — `insert_or_update`, `write_code`, `install_import_bindings`, `get`, `get_type`, `defined_symbols`, `public_symbols`, `all_symbols`, `allocate_got_slot`, `defn_order` (read) — is `&self`, no RefMut needed.

**Operational consequence**:
- Cross-module read contention disappears. Worker reading m1 via `shared.symbol_tables.get(&m1)` no longer blocks behind another worker's per-form RefMut on m1.
- Per-symbol gap mechanism becomes mechanically sound — `Gap(SymbolTypechecked)` / `wait_for_typecheck_symbol` / `notify_symbol_typechecked` round-trip works without livelock.
- Decision 30's "single worker per module during typecheck" reframes from a *lock-safety requirement* into a *scheduler ordering choice* — the lock layer no longer requires it; the scheduler keeps it as form-sequencing discipline.

### 4.2 No merge step

Workers do not "merge back" into the session. They mutate `shared.*` through interior mutability under per-cell locks, and other workers see the mutation as soon as the lock releases. Warnings are the one exception: `Warning` values route back to the initiator via the work-completion notification, where they are appended to `Sess.warnings`. Initiator-collected, never cross-thread for storage.

Per Decision 41, even the `Code` write happens worker-side: backend's `compile_to_module` calls `SymbolTable::write_code(&self, sym, Code::Jit { jit, ptr })` directly on the worker's `&shared.symbol_tables[scope]`. There is no longer a session-side post-loop that ferries a backend-returned tuple back into the symbol table — the int-side machinery at `worker.rs:2860–3018` collapses into the per-symbol call-site loop:

```rust
for sym in defined_symbols(&shared.symbol_tables[scope]) {
    let jit = Jit::new_with_symbols(&extra)?;
    compile_to_module(scope, &[sym], &shared.symbol_tables, shared.introspection.as_ref(), jit.jit_module())?;
}
```

### 4.3 Introspection placement (Decision 38, mode-conditional)

`shared.introspection: Option<DashMap<FQSymbol, Introspection>>`. The outer `Option`:
- `Some(map)` iff REPL mode OR `CRANELISP_CODEGEN_TRACE` is set (or REPL trace mode).
- `None` in production batch (`--run` non-trace, `--link`).

The presence of the map IS the mode discriminator; there is no separate `is_repl: bool` flag. Production batch pays zero per-symbol metadata cost.

**`Introspection` shape** (per `facades/int.md` §"Introspection"):
- `source: Option<String>` — per-defn source snippet (Decision 39); replaces module-global source store.
- `sexp: Option<Sexp>` — post-expansion s-expression.
- `clif_ir: Option<String>` — CLIF IR text (when trace mode); **eagerly captured** post-codegen.
- `code_size: Option<usize>` — native code size in bytes; **eagerly captured** post-codegen.
- `compile_duration: Option<Duration>` — codegen wall-clock.

> **No `disasm` field.** Native disassembly is NOT a stored introspection
> field — it is **re-derived on demand** (Decision 41 on-demand model). Disasm
> is the most expensive metadata (a full capstone pass over the finalised
> machine code) and is needed only when a human types `/disasm`; persisting it
> for every compiled symbol would tax every REPL eval to serve a rare query.
> The GOT slot already holds the live code address and `code_size` is already
> captured, so `cranelisp_backend::produce_disasm(fq, code_size, symbol_tables)`
> reconstructs the disassembly from the same allocation the backend finalised,
> on the `/disasm` keystroke. This mirrors the eager/lazy split: cheap, often-read
> metadata (`source`/`sexp`/`clif_ir`/`code_size`) is captured at codegen;
> expensive, rarely-read metadata (disasm) is derived at read time.
>
> *Historical note:* an earlier `Introspection.disasm: Option<String>` field +
> a `CompilerSession::symbol_disasm()` accessor were introduced under the
> assumption the backend would write disasm eagerly. The backend never
> populated it (`worker.rs` step 7 sets only `clif_ir` + `code_size`), so the
> field is permanently `None` and the `/disasm` handler reading it always hits
> the dead "no disassembly available" path (S86 defect, ledger guard
> `disasm_command_shows_native_code_for_compiled_fn`). The field + dead accessor
> are vestigial and SHOULD be removed when `/disasm` is rewired (S87 Stage A);
> if removed they cease to be a read site below.

**Population sites** (all conditional on `shared.introspection.is_some()`):
- `process_form` after parse + macro expansion: write `source` + `sexp`.
- `compile_to_module` per-symbol call (Decision 41): backend writes `clif_ir`, `code_size`, `compile_duration` directly into the introspection map via the `Option<&DashMap<FQSymbol, Introspection>>` parameter — no int-side post-processing. Disasm is NOT among them (re-derived on demand, above).

**Read sites**: slash-command accessors on `CompilerSession` (`symbol_source`, `symbol_sexp`, `symbol_clif`, `symbol_code_size`, `symbol_compile_duration`) read the stored fields; `Sess::format_error` for rich inline display; `Sess::regenerate_backing_file` for source emission. `/disasm` is NOT a stored-field read — `handle_disasm` calls `cranelisp_backend::produce_disasm` on demand (see §8.2.1).

Cited principles: P1 (Decoupling), P6 (Complexity has a budget — production carries no overhead), P7 (Single source of truth — one place per-symbol metadata lives), P11 (Single pipeline — one mode discriminator at the integration layer).

---

## 5. Code enum + lifecycle (Decisions 31, 35, 41)

### 5.1 Placement (post-Decision-41)

`Code` lives in `cranelisp-backend/src/code.rs` (Decision 41 amends Decision 35). int re-exports for session-boundary instantiation:

```rust
pub use cranelisp_backend::Code;
```

`cranelisp-types` exposes only the empty marker traits `CodeStore` / `LinkerStore` (Decision 32) and stays Cranelift-ignorant — Principle 3 protected. Backend is no longer C-blind: it constructs `Code::Jit { jit, ptr }` directly inside `compile_to_module`. The previous `cranelisp-backend → cranelisp-types` boundary widens by one item (`Code` lives in backend now), but the types crate's surface tightens by exactly that one item.

### 5.2 Variants

- **`Code::Jit { jit: Arc<Jit>, ptr: *const u8 }`** — fresh-build code from a `compile_to_module` invocation. The `Arc<Jit>` is the retention root for JIT-mmap'd executable pages; `ptr` is the per-symbol entry point. Per Decision 41's per-symbol cardinality, each `compile_to_module` call defines exactly one symbol — so each `Arc<Jit>` clone is owned by exactly one entry, not shared across batched defines. (Multi-symbol modules are processed by N independent `compile_to_module` calls.)
- **`Code::Linker { linker: Arc<Linker>, ptr: *const u8 }`** — cache-hit `.o`-mapped code. The `Arc<Linker>` is the retention root for mmap'd code regions; `ptr` is the linker-resolved per-symbol address. All entries from one cache-hit `.o` share the same `Arc<Linker>` clone.

**Mixed-lineage modules are first-class**: a REPL session that loads cached `.o` for module `M` (entries hold `Code::Linker`) and then evaluates `(defn foo …)` in `M` (the new entry holds `Code::Jit` from a fresh batch) is a normal mixed state. The variant choice lives per-entry; there is no "cache mode" vs "JIT mode" discriminator on the symbol table.

### 5.3 Reclaim — the per-symbol JIT story (Decision 31, amended by Decision 41)

Cranelift 0.116 leaks per-function memory on default `Drop` (`cranelift-jit/src/memory.rs:269-276` does `mem::forget` to preserve fn-pointer validity). Reclaim is necessarily per-JIT, gated by the `unsafe JITModule::free_memory()` safety contract: *"none of the `fn` pointers are called afterwards"*. We satisfy this by:

1. Wrapping `JITModule` in our `Jit` wrapper with a custom `Drop` that calls `unsafe free_memory()` once.
2. Refcounting `Jit` via `Arc`, with one `Arc<Jit>` clone per `Code::Jit { jit, ptr }` entry. With Decision 41's per-symbol cardinality, that's one clone per entry, no sharing.
3. Per-redefinition reclaim falls out: REPL user redefines `(defn f [x] x)` → old `ModuleEntry::Def` is replaced → prior `Code::Jit` drops → `Arc<Jit>` decrement → `Arc::drop` → `Jit::drop` → `unsafe free_memory()`.

**Carry-forward invariant** (`crates/cranelisp-typecheck/src/program.rs:2184-2232`, Wave 3b discovery): `register_defn_signature` clones the existing `code: Option<C>` forward into the rebuilt entry on REPL upsert. Without this, mid-typecheck `Arc<Jit>` drop would call `free_memory()` on JIT pages still referenced by the GOT slot before the new code address is written. This is the fix that made `C: Clone` a `CodeStore` super-bound (Decision 32 Wave 3 close).

**Eval lifetime**: each REPL expression compiles its temp closure on a fresh `JITModule` wrapped in `Arc<Jit>`; the Arc reclaims when the trampoline returns and the value is consumed (per pipeline-v4 §6.2 + facade invariant 6).

**Three scenarios summary**:

| Scenario | Module | Lifetime | Reclaim trigger |
|---|---|---|---|
| REPL eval | Fresh `JITModule` for `__expr` | Per-eval | Custom `Drop` on `Jit` after value consumed |
| Defn JIT (per-symbol) | Fresh `JITModule` per `compile_to_module` | `Arc<Jit>` per entry | Last `Arc<Jit>` clone drops (eviction / redefinition) |
| Object | `ObjectModule` | Per compile batch | Plain `Drop`; no executable memory to reclaim |

Verified by `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` — observes Arc refcount transitions and `jit_free_memory_call_count()` increment.

**Decision 28 retraction**: the older "per-worker persistent JIT" framing (Decision 28) was retracted by Decision 31 — long-lived per-worker JIT coalesces batches and defeats Scenario-2 reclaim. Don't perpetuate.

### 5.4 Code accessor discipline

Every read site that needs the code address calls `code.ptr()`, which variant-matches and returns the inner `*const u8`. The handful of sites that need the lifetime root (JIT-entry registration; Linker-pages observation) variant-match explicitly. `Code: Send + Sync` is `unsafe`-impl'd; the raw pointer is an integer handle into pages the Arc keeps alive. Cited principle: P7 (single accessor — one variant-uniform code-pointer access path).

---

## 6. Pipeline orchestration

### 6.1 `register_module` Phase 0 (Decision 38)

```text
register_module(module):
  parse → ParseProduct { forms, structural }
  // Phase 0: brief &mut SymbolTable hold
  {
    let mut st = symbol_tables.entry(module).or_default();
    st.write_structural_decls(structural);            // imports/exports/platforms/submodules
    st.seed_defn_order(forms);                        // first-registration order
    // RefMut drops here.
  }
  // Cache-hit decision lives in the recursive flow per Decision 37 (§7).
  scheduler.register_module(module);                  // dispatches PriorityWork::Typecheck
  for each import in structural.imports:
    register_module(import.module_path);              // recursive
```

The Phase 0 block is microsecond-scale. The RefMut drop *must* happen before `scheduler.register_module` so workers picking up `PriorityWork::Typecheck` find the SymbolTable reachable via shared `.get()` only.

### 6.2 Worker dispatch + `process_form`

Per `facades/int.md` §"`process_form` — the gap-orchestration retry loop":

```text
worker_loop(shared: Arc<SharedState>):
  loop {
    match shared.scheduler.take_priority_work_blocking() {
      Some(Typecheck(module))    => process_module_forms(&shared, module),
      Some(Jit(fq))              => compile_jit(&shared, fq),
      Some(LoadObject(module))   => load_cache_o(&shared, module),
      None                       => break    // shutdown
    }
  }

process_form(shared: &SharedState, form: Sexp, scope: &ModuleFullPath) -> Result<ProcessedForm> {
  loop {
    let expanded = match expand(form, &shared.symbol_tables) {
      Ok(s) => s,
      Err(ExpansionError::Gap(gap)) => { handle_gap(shared, gap)?; continue; }
      Err(other) => return Err(other.into()),
    };
    let ast = build_ast(expanded)?;
    let scope_table = shared.symbol_tables.get(scope).expect("Phase 0 ran");
    let result = match check_form(ast, &scope_table, &shared.symbol_tables) {
      Ok(r) => r,
      Err(CheckError::Gap(gap)) => { handle_gap(shared, gap)?; continue; }
      Err(other) => return Err(other.into()),
    };
    return Ok(result.into());
  }
}
```

**Frontend and typecheck stay pure.** They surface dependencies as `Err(ExpansionError::Gap)` / `Err(CheckError::Gap)`. `int::process_form` is the *sole* crate-crossing where gap values become scheduler calls. Workers park inside `wait_for_*` calls — never inside frontend or typecheck library code (per Principle 3 — typecheck/frontend depend on `cranelisp-types` only). Per Principle 7 (single source of truth), `handle_gap` is the sole site that translates a `ResolutionGap` into a scheduler/dependency-service action.

### 6.3 Gap-handling protocol

`handle_gap(shared, gap)` translates a `ResolutionGap` value into scheduler operations:

| Gap | Action |
|---|---|
| `SymbolTypechecked(fq)` | `ensure_registered(fq.module)` → `wait_for_typecheck_symbol(fq)` |
| `MacroInMem(fq)` | `ensure_registered(fq.module)` → `wait_for_typecheck_symbol(fq)` → orchestrator-side macro discrimination: peek at the entry; if `DefKind::Macro` and `code.is_none()`, additionally `priority_boost_jit(fq)` + `wait_for_inmem(fq)` |
| `Type(fqt)` | `ensure_registered(fqt.module)` → `wait_for_typecheck_type(fqt)` |

**Termination** — each `handle_gap` call advances dependency state monotonically; subsequent retries see strictly more state. Loop terminates on success, non-gap error, or `SchedulerError::Cycle` (Decision 30 mutual import).

**Macro-vs-fn discrimination** is orchestrator-owned, not `expand`-owned. `expand` returns `MacroInMem(fq)` uniformly for any FQ ref it can't yet resolve; the orchestrator peeks at the entry post-typecheck and only forces a JIT if the entry actually IS a macro with missing code. Functions are NOT speculatively JIT-pushed. (Cited principle: P11 — single pipeline; the discrimination is one place.)

### 6.4 `notify_*` cadence

Per Decision 30 reframed by Decision 38 — scheduler notifications are *ordering* primitives (parallel macro-dep compilation, phased completion), not lock-safety primitives. Workers call:

- `notify_symbol_typechecked(fq)` after `check_form` writes the entry.
- `notify_typecheck_done(module)` after the last form in a module finishes.
- `notify_typecheck_done_from_cache(module)` for cache-hit (Decision 37) — enqueues `LoadObject` not `Jit`.
- `notify_inmem_codegen_complete(fq)` after JIT finalize writes the GOT slot.
- `notify_inmem_codegen_batch_complete(module)` after `LoadObject` populates all GOT slots from cache.
- `notify_object_codegen_complete(module)` after nice-worker `.o` write completes.

The scheduler maps these to readiness states; `wait_for_*` callers unblock when the corresponding state is reached. The audit's F3 (dep-registration split across worker/session/scheduler) is closed by routing all worker-side flows through `process_form`'s gap loop and all session-side flows through `Sess::eval`'s same gap loop — one canonical orchestrator, two callers.

---

## 7. Cache + linker orchestration (Decisions 34, 37)

### 7.1 Cache-hit flow inside `register_module`

Per Decision 37 — cache-hit decision lives INSIDE the recursive `register_module` flow, not in a parallel codepath. The pre-Sprint-58 `try_cache_hit_load` path (a parallel orchestrator) is deleted.

```text
register_module(M):
  if <cache>/M.meta.json exists and schema_version matches:
    deserialise SymbolTable<(), ()> → into_concrete::<Code, ()>() → install
    notify_typecheck_done_from_cache(M)            // enqueues LoadObject(M)
  else:
    parse → typecheck → install                    // fresh build path
    notify_typecheck_done(M)                       // enqueues Jit per defined symbol
  for each import in symbol_tables[M].imports:
    register_module(import.module_path)            // recursive

codegen_worker:
  match work:
    Jit(fq)           => compile_to_module(scope, &[fq.symbol], ..., jit.jit_module())
                         // backend writes Code::Jit directly via SymbolTable::write_code; stores GOT slot
    LoadObject(M)     => Linker::load_object(read M.o) → for each defined symbol s:
                         ptr = linker.get_symbol(bare_name(s)) → write Code::Linker { linker, ptr } → store_slot
```

**Order-independence rationale**: typecheck phase pins the GOT slot LAYOUT (slot indices in `SymbolTable.symbols[s].got_slot`); codegen workers fill slot CONTENTS in any order. No cross-module ordering required for codegen — each module is a self-contained operation on its own SymbolTable + its own JIT (or `.o`).

**No swallowed failures**: a `LoadObject` worker that finds `linker.get_symbol(name) == None` MUST error out with a `CacheLoadError`, not silently push to `loaded_symbols`. The pre-Sprint-58 swallowing was a Decision-31 safety-invariant violation (slot resolves to NULL but worker reports success).

### 7.2 Backend's three return shapes (post-Decision-41)

Per `facades/backend.md` (and Decision 41): backend exposes three entry points — `compile_to_module<M: Module>` for fresh build, `load_object` for cache-hit, `compile_to_object` for `--link`. With Decision 41:
- `compile_to_module` returns `Result<(), CompilationError>` and writes `Code::Jit` directly via `SymbolTable::write_code(&self, sym, code)`. Per-symbol cardinality (one defined-symbol per call); no defined-symbol set traversal inside backend.
- `load_object` returns `Result<LinkerArtefact, CompilationError>` carrying `Arc<Linker>` + symbol-pointer map; int constructs `Code::Linker` per symbol.
- `compile_to_object` returns `Result<ObjectArtefact, CompilationError>` for `--link` mode; int's cache writer + linker driver consume it.

Backend's `CompilationError` lives in `cranelisp-backend` (post-FIXME 0100 Phase 2, originally `cranelisp-types`). The `SymbolNotCompilable` variant lets backend error out with structured information when an entry is invariant-violated rather than panicking.

### 7.3 Cache schema versioning (Decision 34)

`SymbolTable.schema_version: u32` lives at the top of the serialised shape. Cache-load checks it before accepting state; mismatch → `CacheError::SchemaVersionMismatch { found, expected }` and treats the entry as stale. The constant lives in `crates/cranelisp-backend/src/cache/mod.rs` (`/backend`-owned; bumps every time the serialised shape changes). int's worker cache-write path emits the field. Old caches (pre-S58) lack it → default 0 → version-mismatch → reject. Cited principles: P5 (testability — explicit version → explicit failure mode), P8 (the cache envelope IS the target shape).

### 7.4 Linker retention

`Code::Linker.linker: Arc<Linker>` is the per-symbol retention root. When the last `Code::Linker` referencing an `Arc<Linker>` drops (last entry from one cache-hit `.o` evicted/redefined), the mmap'd pages reclaim. Symmetrical with Decision 31 Scenario 2 (per-redefinition reclaim) but at module granularity. `SharedState.kept_linkers` is dissolved (Sprint 58 Wave 3); only `kept_dlls` remains as a session-global side store (orthogonal — DLLs are session-scoped, not per-module).

---

## 8. REPL flow

### 8.1 Eval cursor + defn_order append

Per `facades/int.md` invariants 9 + 10: definitions append to `current_repl_module` (not `user`); `Sess::eval` for a defining form calls `Sched::append_form(current_repl_module, sexp)` and waits for that single symbol's typecheck + jit. The whole module is NOT re-typechecked.

`SymbolTable::append_defn_order(&mut self, sym: Symbol)` — brief per-eval `&mut SymbolTable` window (microseconds). The same shape as Phase 0; the only other `&mut SymbolTable` operation. `defn_order` records canonical first-registration ordering; redefinition replaces in place, preserving original position. (Per Decision 39.)

### 8.2 Introspection populate (Decision 38, mode-conditional)

After `process_form` succeeds for an eval, when `shared.introspection.is_some()`:

```text
introspection.insert(fq, Introspection {
  source: Some(eval_text),                     // for REPL evals; for file-based modules, sliced from file Arc<str> at parse-time
  sexp: Some(expanded.clone()),
  clif_ir: ...,                                // populated post-codegen in worker (Decision 41 — backend writes directly)
  code_size: ..., compile_duration: ...,       // populated post-codegen in worker
  // NB: no `disasm` field — derived on demand (§4.3, §8.2.1)
})
```

Production batch (`shared.introspection == None`) skips the populate path entirely.

### 8.2.1 `/disasm` — on-demand disassembly (Decision 41)

`/disasm <name>` does NOT read a stored field. The handler
(`src/repl.rs::handle_disasm`) re-derives the disassembly at the keystroke:

```text
handle_disasm(name):
  if name empty            -> usage line
  fq = FQSymbol { module: current_module_path(), symbol: name }   // same resolution as /clif's get_introspection
  code_size = introspection[fq].code_size                          // captured at codegen
      else -> "Error: no disassembly available for '<name>'"       // not compiled / no metadata
  match cranelisp_backend::produce_disasm(&fq, code_size, &shared.symbol_tables):
    Ok(text) -> "; disasm for <name>\n{text}"                      // header + capstone lines
    Err(_)   -> "Error: no disassembly available for '<name>'"     // slot empty / not compilable
```

Design points:

- **`produce_disasm` is ALREADY public** (`crates/cranelisp-backend/public-api.txt`;
  def `crates/cranelisp-backend/src/lib.rs`). The S87 fix is pure wiring at the
  int boundary — **no backend surface change, no `cranelisp-types` edit**
  (/arch Phase-2 confirmed: no interface delta).
- **`code_size` is the bridge.** `produce_disasm` requires the caller to supply
  `code_size` (the backend does not persist it; §"The caller supplies code_size"
  in `lib.rs`). int already captures `code_size` eagerly into the introspection
  record (`worker.rs` step 7), so the handler reads it from there and forwards it.
  A name with no `code_size` (never compiled, or batch mode with no introspection
  map) yields the graceful "no disassembly available" line — same shape as the
  other introspection handlers.
- **Symbol-table lookup is backend-side.** `produce_disasm` itself resolves the
  GOT slot from `shared.symbol_tables` and reads the live code bytes; int hands
  it the `FQSymbol` + `code_size` + a `&DashMap` of the symbol tables. The
  module of `fq` is the current REPL module (identical resolution to `/clif`'s
  `get_introspection`), so `/disasm` and `/clif` resolve the same symbol.
- **Why not eager?** See the §4.3 disasm note — disasm is the most expensive
  metadata and rarely read; deriving it on the keystroke keeps every REPL eval
  cheap (Principle 6 — complexity has a budget; the production-batch path pays
  nothing, the REPL pays only when asked).
- **Contrast with `/clif` (the working sibling).** `/clif` reads the eagerly
  captured `intr.clif_ir` (cheap to capture, captured at codegen). `/disasm`
  cannot mirror that path because no `disasm` field is populated — and per
  Decision 41 it SHOULD NOT be. `/disasm`'s correct shape is the re-derivation
  above, not "populate the field too."
- **Vestigial accessor.** `CompilerSession::symbol_disasm()` reads the dead
  `intr.disasm` field; it has no correct caller after this rewire and should be
  removed alongside the field (§4.3 historical note). `/dev` removes both in the
  same change-set or leaves a one-line `// dead — see int.md §4.3` if removal is
  scoped out; the design intent is removal.

This closes the S86 ledger guard `disasm_command_shows_native_code_for_compiled_fn`
(spec: `repl/spec.md §3.1`).

### 8.2.2 `/info` macro card — clause-count line (`repl/spec.md §11.2.2`)

`/info <macro>` renders through `format_def_entry` → `format_macro_display`
(`src/repl.rs`). Per `repl/spec.md §11.2.2` the macro card MUST, for a
**multi-clause** macro, emit a clause-count summary line after the per-clause
signature lines:

```
:user/cond ; defmacro - Multi-way conditional
; [x] -> Sexp
; [x body & rest] -> Sexp
  2 clauses
```

Current `format_macro_display` emits the `:module/name ; defmacro` line, the
docstring comment, and one `; <params> -> Sexp` line per clause — but NOT the
count line. That omission is the S86 ledger guard
`info_multi_clause_macro_shows_clause_count` (spec: `repl/spec.md §11.2.2`).

Design points:

- **Rendering home is `format_macro_display`.** The clause count is computed
  from the same `clauses: &[MacroClauseInfo]` slice the renderer already
  iterates — `clauses.len()`. No new data is needed; `clauses_meta` is already
  carried on the `DefKind::Macro` entry (`describe_symbol`'s bare-lookup arm
  already prints `({N} clause(s), …)` from it, so the count datum is proven
  available — this is a rendering gap, not a data gap).
- **Format: `  N clauses`** — two leading spaces, no `;` prefix (it is a summary
  line, not a comment line), matching the spec worked example exactly. Append it
  as the final line of the returned string.
- **Gate on `clauses.len() > 1`.** The spec's single-clause worked example
  (`/info when`) shows NO count line; only the multi-clause example carries it.
  Emit the line only when there is more than one clause. (Pluralisation is moot
  under this gate — the count is always ≥ 2, so a fixed `"clauses"` is correct;
  no `clause`/`clauses` branch needed.)
- **Scope: `format_macro_display` only — do NOT touch `/sig` or bare display
  divergently.** `/sig` renders macros through a *different* path
  (`format_entry_sig`, NOT `format_macro_display`), so it is unaffected and its
  `[Tested]` guards (`bare_macro_lookup_shows_clause_signature`) stay green.
  `format_macro_display` is ALSO reached by the bare-`defmacro` display
  (`format_def_entry` at the eval-result site) and `/info`; both existing guards
  there (`defmacro_display_single_clause`, `defmacro_display_multi_clause`,
  `bare_macro_lookup`) assert with `contains`, so appending the count line to a
  multi-clause macro is non-breaking. The single-clause guards never trip the
  `> 1` gate.
- **No interface delta.** Pure int-side rendering; `clauses_meta` already on the
  symbol-table entry. /arch Phase-2 confirmed no `cranelisp-types` change.
- **Resolver split.** This is the `/repl` half of the Stage-A pair (the spec
  format question is `/repl`-owned: `repl/spec.md §11.2.2` is the normative
  contract); the rendering lives in `src/` (the `/int`-owned surface). See the
  Phase-4 wave note below on whether the two src/ fixes are one `/dev`
  invocation or two.

### 8.3 `regenerate_backing_file` (Decision 39)

```text
regenerate_backing_file(module):
  let st = shared.symbol_tables.get(module)?;
  let intro = shared.introspection.as_ref().ok_or(IntrospectionRequired)?;
  let mut text = String::new();
  for sym in st.defn_order():
    let fq = FQSymbol::new(module, sym);
    if let Some(info) = intro.get(&fq):
      if let Some(src) = &info.source: text.push_str(src); text.push('\n');
  atomic_write(module_file_path(module), text);
```

The old `module_sources: DashMap<ModuleFullPath, Arc<str>>` field on SharedState is GONE. Per-defn source on `Introspection.source` is the only source store. Cited principle: P7 (single source of truth — per-defn source has one home).

### 8.4 Watcher integration

Per `facades/int.md` invariants 7 + 8 + bounded-context §6.2:

1. REPL never calls `wait_for_*` at startup — the prompt is responsive immediately. The first iteration's STEP 4 `wait_for_inmem_codegen()` catches up the entry module's code.
2. `set_repl_input_active(true)` opens the watcher window during `read_line`; `set_repl_input_active(false)` closes on input submission. STEP 4 catches up everything triggered during the prompt.
3. Watcher events do NOT flow directly into compilation. They cross to the REPL cadence at a poll point and become `re_register_module` calls.

`watch.rs` owns the `notify`-based watcher and the `WatcherChannel` mpsc. The REPL polls at prompt boundary; the prompt-window mechanism is the closure that prevents mid-input watcher interleave.

### 8.5 Slash commands — composed flows over the existing primitives

Per `facades/int.md` §"Composed introspection flows": slash commands are composed flows over `CompilerSession` accessors and other facade calls — not new facade surface. The 17 commands (`/sig`, `/doc`, `/help`, `/type`, `/info`, `/source`, `/sexp`, `/ast`, `/clif`, `/disasm`, `/time`, `/mem`, `/list`, `/imports`, `/exports`, `/expand`, `/mod`, `/reload`, `/run-tests`) all dispatch through `Sess::process_commands`, which decodes the input into a `SlashCommand` enum and either reads the introspection store directly (`/source`/`/sexp`/`/clif`/`/disasm`/`/time`), composes a frontend / typecheck call (`/expand`), or composes a runtime-side primitive (`/mem`, `/run-tests`).

Universal output format (Sprint 14): `:Type {value|name} ; {classification} - {docstring}` + optional related symbol comment lines. Defined in `repl/spec.md`; implemented across `Sess::format_*` family.

---

## 9. Error formatting (Decisions 39 + 42)

`Sess::format_error(&self, err: &CranelispError) -> String` is the integration-layer formatter. It resolves `ErrorLocation` against the current mode and chooses a display strategy:

| Available | Strategy |
|---|---|
| `ctx` (inline snippet) populated | Use it directly — parser path is self-contained |
| `fq` populated + introspection enabled | Look up `shared.introspection[fq].source`; slice using `line_col` for inline rich display |
| Neither (production batch) | `file:line:col: error: message` style |

REPL display path AND production batch CLI display path call this — one formatter, mode-conditional input. Cited principle: P11 (single pipeline — error formatting is one path with mode-conditional input, not separate REPL vs production).

**Error variants formatted**:
- `CranelispError::Parse` / `Reader` / `Expansion` / `Type` / `Codegen` — go through the `ErrorLocation` resolution path above.
- `CranelispError::Platform(PlatformError)` — per Decision 42, post-FIXME 0104. Each variant carries `ErrorLocation`. `format_error` adds a `Platform(PlatformError)` arm using the same mode-conditional source-resolution path. The `(platform "name")` form's span flows into the `location` field at the load call site.
- `CompilationError` (from backend, post-FIXME 0100 Phase 2) — variants like `SymbolNotCompilable` carry `ErrorLocation`; same path.

`Warning` carries the same `ErrorLocation` shape; `Sess::format_warning` (or the same formatter, type-dispatched) handles the warning case uniformly. Cited principles: P5 (testability — error structure is permissive data, formatter is policy layer; both independently testable), P7 (single formatter).

---

## 10. Concurrency model

This section is an overview; the structural diagrams live in `design/int/concurrency/` (target-state, scheduler-lifecycle, dependency-protocol-target, symbol-publication-target, compilation-cadence-batch-run).

**Shape** (from `facades/int.md` §"SharedState" + Decision 38):
- Workers spawned at `CompilerSession::new`; each receives its own `Arc<SharedState>` clone (refcount bump). They live for the session — never per-call `thread::scope`. Joined on `Drop` via `WorkerPool`.
- `take_priority_work_blocking` parks workers on a condvar inside `CompileScheduler`; wakeups come from `enqueue_jit` / `register_module` / `notify_*`.
- `wait_for_*` parks workers (for orchestrator-driven dep waits) inside the scheduler's wait-table.
- The IO trampoline forks Par nodes onto rayon (rayon pool size from `SessionSettings`).

**Invariants**:
1. Workers never see `&mut SharedState` — only `&shared.*`. All mutation through interior mutability of contained types.
2. Per-symbol mutability discipline (§4.1) — no whole-module `&mut SymbolTable` after Phase 0.
3. Scheduler is *the* coordination authority — there is no separate `DependencyService`. The runtime/platform diagrams' merge of work-dispatch + wait/release into one structure is binding.
4. Module-level dispatch ordering — at most one `PriorityWork::Typecheck(module)` at a time (Decision 30 reframed as ordering). Avoids per-module dispatch races; the lock layer no longer requires it.
5. GOT slot writes are atomic-Release; reads are atomic-Acquire (Decisions 31 + 23). REPL redefinition retargets atomically before the old `Arc<Jit>` can drop.
6. Mutual-import deadlock — known, documented (Decision 30); workaround via `discover-tests` for test scaffolding.

The audit's F4 (worker orchestration split across files) collapses under the target shape: priority + nice loops both live in `worker.rs` (or `workers/` subtree); scheduler state in `scheduler.rs`; `SharedState` in `session_v4.rs`.

---

## 11. Observability — three ring buffers + introspection

Post-S64 the observability surface has four sinks, all int-owned:

| Sink | Activator | What it observes | Implementation |
|---|---|---|---|
| Scheduler trace | `CRANELISP_SCHEDULER_TRACE=1` (or REPL trace mode) | Worker lifecycle, scheduler dispatch, notify_*, wait_for_* | `src/observability.rs` (renamed `src/scheduler_trace/` post-cleanup) |
| IO trace | `CRANELISP_IO_TRACE=1` (or REPL trace mode) | IO trampoline transitions, Par fork-join, IVar spark/force | `src/io_trace/` (post-FIXME 0103; relocated from `cranelisp-runtime/src/io_trace.rs`) |
| GOT trace | `CRANELISP_GOT_TRACE=1` (or REPL trace mode) | GOT-slot population events: JitWrite, LinkerWrite, Redefinition | `src/got_trace/` (post-FIXME 0099; new) |
| Introspection store | REPL mode OR `CRANELISP_CODEGEN_TRACE` | Per-symbol metadata: source, sexp, clif_ir, disasm, code_size, compile_duration | `SharedState.introspection` |

The first three are per-thread `VecDeque<Event>` ring buffers with FIFO overflow; activated by env-var; flushed to stderr at session end (with merge-sort across threads via shared `TRACE_ANCHOR` `Instant`). Sinks 2 + 3 are reached via observer-callback contracts owned by their originating crates: `cranelisp_runtime::register_io_observer(...)` (Decision 40) and `cranelisp_backend::register_got_observer(...)` (FIXME 0099). int's session startup registers the observers when the activator is on, no-ops otherwise; the relaxed-load null check costs one branch per call site in the unregistered case.

**The pattern is uniform across the three ring buffers**: each crate that originates events defines the taxonomy (`IoEventTag` / `GotEventTag` / scheduler events), exposes a registration function, and emits through the registered observer. int implements the ring-buffer state, formatter, and dump.

The fourth sink (introspection) is a per-key store, not a ring; it serves slash commands and the rich error formatter. It overwrites on REPL redefinition (per the Decision 31 carry-forward invariant — same key, fresh data).

**Production-batch cost** (`--link` and non-trace `--run`): zero — `shared.introspection == None` means no populate paths run; no observers are registered, so the ring-buffer call sites no-op after the relaxed load + null check.

---

## 12. Quality attributes

| Attribute | This crate's stewardship |
|---|---|
| Simplicity (P6) | Audit F1+F2+F5 are the operative complexity gaps. The 38/39/41 simplification removes three dimensions (per-form RefMut, `module_sources`, the int-side post-loop unpacking after `compile_to_module`). The S64 module decomposition (§3.3) closes the rest. Decision 35/41's `Code` enum is single-cleavage Cranelift exposure — one site, not scattered. |
| Maintainability (P1, P2) | Audit's "split `session_v4.rs` by responsibility" is the centrepiece. Per-symbol mutability + `process_form`-as-sole-crossing closes F3. The three-instance observability pattern (alongside introspection) closes F7's "long historical narratives in hot paths" by routing rationale into `design/int/observability.md`. |
| Observability | §11. Four sinks; one pattern; all production-batch zero-cost. The four-pattern uniformity is a deliberate design choice — once a developer learns the IO-trace shape, the GOT-trace and scheduler-trace shapes are mechanically the same. |
| Concurrency-safety (P4) | §10 invariants. Decision 31 reclaim safety invariant ("Arc-refcount-zero means no fn pointer reachable") is upheld by the GOT swap discipline + the language-level "function values are heap closures, not raw code pointers" rule. Per-symbol mutability discipline removes the per-form whole-module write lock. Decision 41's per-symbol JIT cardinality eliminates batch-level Arc-clone aliasing. |
| Performance (P6) | Per-symbol JIT (Decisions 31 + 41) is the chosen target — long-lived per-worker JIT (Decision 28) was retracted because it coalesces batches and defeats reclaim. Persistent worker pool (Decision 27) avoids per-module thread spawn cost. Cache-hit-via-`LoadObject` skips codegen entirely on cache-hit. Production batch zero-overhead introspection (`shared.introspection == None`) and zero-overhead observer ring buffers (no observer registered → relaxed load + null-check branch). |
| Testability (P5) | `process_form` is a free function over `&SharedState` — testable with a synthetic SharedState. The scheduler's wait/notify primitives are unit-testable in isolation. `Code` reclaim verified by `tests/v4_jit_reclaim.rs` (Decision 31 Scenario 2). `Introspection` populate paths are conditional on a single discriminator — easy to assert in integration tests. The observer contracts are unit-testable: register a captured-events observer; assert events fired in the expected order. |

---

## 13. Decision register (int-relevant)

Active Decisions affecting int (operative this sprint or constraint-bearing):

| Decision | Headline | Status for int |
|---|---|---|
| 30 | Form-by-form scheduler deadlocks on mutual imports | int's scheduler exhibits the deadlock; workaround via `discover-tests` |
| 31 | One `JITModule` per batch; `Arc<Jit>` on entry; custom Drop | Active; verified by jit-reclaim tests; per-symbol cardinality post-Decision 41 |
| 35 | `Code` enum location (operative; amended by Decision 41) | `Code` lives in `cranelisp-backend` post-Decision 41; int re-exports |
| 40 | `trace.rs` + `io_trace.rs` relocate to int; runtime exposes `IoObserver` | Pre-implementation; FIXME 0103 |
| 41 | `compile_to_module` per-symbol JIT cardinality; backend writes `Code` directly | Pre-implementation; amends 31 + 35; FIXME 0098 (typed errors) bundles |
| 42 | `PlatformError` adopts `ErrorLocation`; lives in `cranelisp-types` | Pre-implementation; FIXME 0104 |

Legacy Decisions (outcome embodied in architecture; preserved in `legacy/decisions/` for narrative continuity but no longer the primary reference for new work) — int-specific embodiments include 9, 21, 22, 23, 24, 25, 26, 32, 33, 34, 36, 37, 38, 39. Each of these is "as-built" inside int today; the source code reflects the commitment.

Retracted/superseded Decisions deleted (rely on git for history) include 28 (per-worker persistent JIT — superseded by 31).

---

## 14. As-designed vs as-built

The S64 Decisions (40, 41, 42) and the FIXMEs that close them (0098, 0099, 0100, 0103, 0104, 0107, 0108) define a destination shape that the source has not yet reached. The drift is real and tracked; this section is the consolidated map.

| Drift | As-built today | As-designed (post-FIXME) | Tracker |
|---|---|---|---|
| Typed gap-orchestration errors | Ad-hoc string-parsing in `worker.rs` to detect `Gap`-shaped error returns | Typed pattern-match on `Err(CheckError::Gap(...))` and `Err(ExpansionError::Gap(...))` | FIXME 0098 Phase 4 |
| GOT trace observer | None — GOT writes are silent | `src/got_trace/` ring buffer; `cranelisp_backend::register_got_observer` registered at session startup | FIXME 0099 Phase 2 |
| Single-consumer type homes | `CheckError`, `ResolutionGap`, `CompilationError` live in `cranelisp-types` | Live in their originating crates (`cranelisp-typecheck`, `cranelisp-backend`); int imports directly | FIXME 0100 |
| `trace.rs` + `io_trace.rs` location | Live in `cranelisp-runtime/src/`; ~1,690 LOC of int concerns in runtime | Live in `src/trace/` + `src/io_trace/`; runtime exposes `IoObserver` callback contract; int registers from session startup | FIXME 0103 (Decision 40) |
| `PlatformError` shape | Stringly-typed `Result<…, String>` + `CranelispError::ModuleError` with embedded message | Structured `PlatformError` enum with per-variant `ErrorLocation`; `CranelispError::Platform(PlatformError)`; `Sess::format_error` Platform arm | FIXME 0104 (Decision 42) |
| `display.rs` location | Lives in `cranelisp-backend/src/display.rs` (831 LOC) | Lives in `src/display.rs` (or sub-module of REPL session); BC §6 alignment | FIXME 0108 |
| `code.rs` location | Lives in `src/code.rs` (397 LOC) | Lives in `cranelisp-backend/src/code.rs`; int re-exports | Decision 41 (no specific FIXME; bundled with 0098) |
| Backend per-symbol JIT cardinality | `compile_to_module` returns a tuple; int unpacks at `worker.rs:2860–3018` | `compile_to_module` returns `Result<(), CompilationError>`; backend writes `Code::Jit` directly via `SymbolTable::write_code` | Decision 41 (bundled with 0098) |
| god-file decomposition | `session_v4.rs` (5,417 LOC), `worker.rs` (5,041 LOC) — audit F1 + F2 | Decomposed per §3.3 module map | Audit recommendations 1, 2 — open `/dev` work; no individual FIXME yet |
| Legacy `session.rs` | 543 LOC of v3 session code lingers | Deleted; v4 is the only pipeline | Audit F6 — open `/dev` work |
| `lib.rs` narrowing | 18 public modules exported | Narrows to facade-shape exports (`CompilerSession`, worker loops, scheduler types, etc.) | Audit F5 — open `/dev` work |

The destination shape is the working reference for design. The as-built reality is the working reference for source navigation. Every drift row above has a closure mechanism — either a numbered FIXME or an audit recommendation.

---

## 15. Subordinate topic docs (triage)

> **S88 — `agent.md` is a current, load-bearing subordinate doc (KEEP).** `design/int/agent.md`
> designs the agentic-REPL track: the §5.3 dispatch classifier + `/ask`, the
> `#[cfg(feature="agent")]` `src/agent/` module + `agent_turn` loop, the provider-agnostic
> `LlmBackend` trait (R3), the harvester/relevance-ranker, the always-on primer,
> pull-as-visible-commands, read-only Advise mode, the `[R5]` spec-grep + telemetry
> release-valve seams, and the LLM-free reverse-query commands (`/refs`/`/tests-for`).
> It elaborates within BC §6 (the agent is a REPL-cadence consumer, not a new state window)
> and refines `design/arch/repl-embedded-agent.md` (U1–U6 ratified). Feature-off ⇒ the binary
> is byte-identical to today (the classifier's `Err(other parse error)` arm falls back to
> today's diagnostic). Cited from §8.5 (slash commands) once `/ask`/`/refs`/`/tests-for` land.

The 32 docs in `design/int/` plus the `concurrency/` subdirectory were authored over 12+ sprints and reflect the historical evolution of int. Sprint 64 triage applies the methodology rule: *delete files, rely on git for history if work is fully embodied; preserve if still load-bearing*. Below is the per-doc disposition.

### Concurrency family

| Doc | LOC | Disposition | Rationale |
|---|---:|---|---|
| `concurrency-architecture.md` | 744 | **archive** | Pre-dates Decision 38; documents the per-form RefMut shape that 38 supersedes. Heavily cross-referenced from sibling docs but the references are themselves stale. The current concurrency story lives in §4 + §10 of this master + the `concurrency/` diagrams. |
| `concurrency-audit.md` | 4,290 | **archive** | Sprint-62 audit; superseded by `audits/src-20260423.md` + the S64 Decisions. Audit-trail value preserved by the move. |
| `concurrency-risks.md` | 504 | **archive** | Risk catalogue keyed to pre-38 lock shape. The current risks are §10 invariants. |
| `concurrency-test-strategy.md` | 559 | **refresh** (low priority) | Test catalogue still valid in spirit; some test shapes change under 38. Worth keeping during the §3.3 decomposition. |
| `concurrent-workers.md` | 1,043 | **archive** | Pre-G9 worker model; superseded by `persistent-workers.md` + the active scheduler design. |
| `persistent-workers.md` | 836 | **keep** (with G10 retraction noted at top) | Wave-1 design that landed; describes the active worker-pool shape. |
| `concurrency/` subdir | n/a | **keep** | Target diagrams are current; `archive/` already separates pre-target snapshots. |

### Pipeline / cadence

| Doc | LOC | Disposition | Rationale |
|---|---:|---|---|
| `pipeline-convergence.md` | 553 | **archive** | S26 dual-pipeline analysis; structural superseded by `archive/pipeline-convergence-review.md` (under `design/arch/archive/`). This int-side copy is duplicate. |
| `phase2-codegen-convergence.md` | 1,624 | **archive** | Sprint-54 W3a analysis; superseded by Decisions 22/23/25. Mostly duplicate of `design/arch/archive/codegen-convergence.md`. |
| `step4-macro-blocking.md`, `step5-lazy-discovery.md`, `step7-repl-eval.md`, `step8-platform-registry.md`, `step9-error-cascade.md` | 5 docs, ~3,000 LOC total | **archive** | Step-N execution playbooks (Sprints 23–26). The execution landed; the playbooks served their purpose. The concepts are in §6 + §7 of this master. |

### Cache

| Doc | LOC | Disposition | Rationale |
|---|---:|---|---|
| `cache-hit-loading.md` | 666 | **refresh** | Decision 37 supersedes the high-level shape; the lower-level mechanism description is still useful. Update the §-on-`try_cache_hit_load` to reflect the deletion. |
| `cache-prelude-restoration-repro.md` | 226 | **keep** (defect history) | Specific repro; preserves audit-trail value. |
| `dual-path-persistence-collapse.md` | 1,288 | **keep** | Documents the collapse of the dual-path persistence (a load-bearing event in int's evolution); pointed at by `audits/src-20260423.md`. |
| `symbol-table-cache.md` | 692 | **refresh** | Per-symbol shape needs aligning with Decision 38; some `try_cache_hit_load` references are stale (it's deleted). |

### Macro / expander

| Doc | LOC | Disposition | Rationale |
|---|---:|---|---|
| `macro-resolver-impl.md` | 596 | **refresh** | Frontend FIXME 6 may flag dead `MacroEnv` here — int's `expander.rs` glue. Refresh post-FIXME 0098 Phase 4 (the migration of `expand_sexp_recursive` to frontend). |

### Repro / debug

| Doc | LOC | Disposition | Rationale |
|---|---:|---|---|
| `heisenbug-race-closure.md` | 3,890 | **keep** (defect epic) | The Sprint 61 Slice 3 race investigation; preserved as historical defect record. Massive but high-value when the next race-class issue surfaces. |
| `bind-chain-analysis.md` | 470 | **keep** | bind! chain analyzer description — still load-bearing for `src/bind_chain_analysis.rs`. |

### Settings / config / misc

| Doc | LOC | Disposition | Rationale |
|---|---:|---|---|
| `cranelisp-toml.md` | 412 | **keep** | TOML settings format; load-bearing reference. |
| `repl-lifecycle.md` | 506 | **refresh** | REPL flow steps; some pre-38. Shorter refresh than `concurrency-architecture.md`; high reader-utility. |
| `session-persistence.md` | 469 | **refresh** | `module_sources` references; supersede with Decision 39. The `regenerate_backing_file` shape moved per §8.3 of this master. |
| `observability.md` | 376 | **refresh** | Pre-S64. Refresh to describe the four-sink shape (§11 of this master) — scheduler trace + IO trace + GOT trace + introspection. Single-source the env-var activator table. |
| `terminal-styling.md` | 511 | **keep** | Style spec; load-bearing reference. |
| `private-submodule-import.md` | 304 | **keep** | Edge-case behaviour spec; preserves audit-trail value. |
| `bare-primitive-value-path.md` | 219 | **keep** | Edge-case behaviour spec. |
| `multi-sig-introspection.md` | 254 | **refresh** | Introspection shape — verify against §4.3 / Decision 38. |
| `io-integration.md` | 565 | **refresh** | Sprint-16 design; refresh to align with current `Sess::trampoline` shape and the IO observer pattern (§11). |
| `platform-registry-removal.md` | 642 | **archive** | G8 landed; FIXME 0106 already proposed archive. |
| `symbol-table-generics.md` | 481 | **keep** | Wave-3b implementation playbook for Decision 35. Useful for future C/L parameter changes. |

**Headcount summary**: 32 docs.
- **Archive**: 11 (≈12,000 LOC) — concurrency family pre-38, pipeline-convergence/phase2 duplicates, step-N execution playbooks, platform-registry-removal.
- **Refresh**: 9 (≈4,500 LOC) — cache-hit-loading, symbol-table-cache, macro-resolver-impl, repl-lifecycle, session-persistence, observability, multi-sig-introspection, io-integration, concurrency-test-strategy.
- **Keep**: 12 (≈10,000 LOC) — persistent-workers, concurrency subdir, cache-prelude-restoration-repro, dual-path-persistence-collapse, heisenbug-race-closure, bind-chain-analysis, cranelisp-toml, terminal-styling, private-submodule-import, bare-primitive-value-path, symbol-table-generics, plus this master.

The triage itself is a `/sprint`-coordinated `/dev` task — too large for a single design-pass. Recommended sequencing: archive first (pure delete; commit per group), refresh second (post-FIXME-landing for the cache + observability subset).

---

## 16. Open questions / FIXMEs filed

**S64-era FIXMEs (0098/0099/0100/0103/0104/0108) have all CLOSED** (W-Macro, the trace relocation, the platform-interface landing, the display absorb, and the cluster-atomic restructure resolved them — verified against source S81). The current int FIXME backlog (S81 "clean & green", Phase 3 design):

**S81 Wave 9a — light int items:**

- **FIXME 0013** (`/int`) — `observability.rs::reset_panic_hook_installed_for_tests` mutates process-global panic-hook state without a serialisation lock. Add a `static TEST_GUARD: Mutex<()>` and take it at the top of every test that touches the install path. ~10 LOC; test-only; no baseline impact.
- **FIXME 0194** (`/dev (int)`) — populate `SymbolDescription.related` (currently stubbed `Vec::new()` at `session_v4.rs:1648`). The collector logic already exists for the slash-command display paths (`format_related_section` + the `match`/`impl`/`defn` walks at `session_v4.rs:4503/4510/4541/…`); factor it into private helpers and call them at the `describe_symbol` construction site so callers stop duplicating the lookup. defn/impl/match-arm cross-refs per `repl/spec.md` §3.6. Optionally also threads the original parse-time `ImportSpec` (alias/span/multi-name) through `module_imports` (a separate sidecar-store concern — split out if it grows).
- **FIXME 0217** (`/int`) — inline-module spec §8.2.2 step-2 parent-file rewrite. `handle_mod` (`worker.rs:2650`) calls `write_inline_mod_to_disk` (step 1) but never rewrites the parent file's `(mod name forms…)` → `(mod name)` (step 2). Real behavioural gap (the "one-time creation" + "indistinguishable from manually created" semantics are violated; `inline_body` persists in the symbol table forever). Needs the rewrite + a reload of the parent's structural decls + a new integration test (target /qa for the test). Files: `worker.rs`, possibly `repl/spec.md` §15.4.
- **FIXME 0266** (`/dev (int)`) — move the `trace` SpecialForm metadata entry from the `primitives` module to root `""`. As-built: `bootstrap.rs::register_trace_type` (~L894) inserts it into the `primitives` table; the 2026-06-04 root-special-form ruling + corrected FIXME 0241 Trace row require it at root `""` alongside the structural special forms. ~1-line mount-move (the `Trace`/`TraceCall` ADT + accessors STAY in `primitives` — form/ADT asymmetry). Regression check: `/imports`/`/exports primitives`/`/info trace` reflect the new placement; recognition is parser-side (`Expr::Trace`) and does not consult this entry, so dispatch is unaffected.

**S81 Wave 9b — FIXME 0109 Waves A/B/C only** (see §3.4). The carry boundary: Wave D + the dependent observability harvest cluster co-carry to the next arc sprint.

**Verify-and-plan / cross-skill-gated:**

- **FIXME 0101** (`target: /sprint`) — runtime + platform audit-pass scheduling. **NOT an int-impl item** — it is a `/sprint` scheduling request for `audits/runtime-*.md` + `audits/platform-*.md` passes, and it concerns the runtime/platform crates, not `src/`. No int action; flag to `/sprint` that it sits outside the int component clearance.
- **FIXME 0220** (`target: /arch`) — cache-hit Introspection rehydration. **/arch design question first** — the FIXME explicitly filed `target: /arch` to arbitrate WHERE the rehydration trigger sits (lazy-per-symbol vs eager-per-module vs per-first-edit) + WHETHER to serialize a minimal per-symbol `source_range: Option<Range<usize>>` into the cache. Until /arch rules, the int implementation (a `SharedState::rehydrate_introspection(fq)` private path) cannot be specced. **Blocked on /arch; not actionable as int-impl this wave.** Surface to `/sprint` as needing an /arch ruling before any int wave can take it.
- **FIXME 0281** (`target: /design`) — int-facade trim of the dead `priority_boost_jit`/`wait_for_inmem` priority-codegen machinery. **Folds into FIXME 0298** (the int-facade retire/doc-reorg, a W1 doc item, `target: /arch`). The source already deleted the subsystem (S76 W3 — confirmed: `priority_boost_jit`/`wait_for_inmem`/`PriorityEntry`/`BlockingJitCodegen` are gone from `scheduler.rs`; only `unblock_module` remains); `facades/int.md` still describes it (L649-650, L1077, L1195-1196, L1229). Since 0298 retires `facades/int.md` wholesale (migrating its internal-orchestration content to `design/int/` + `src/` rustdoc), the 0281 trim is subsumed: the dead pseudocode simply does not carry over into the migrated docs, and `scheduler.rs`'s `unblock_module` is documented in its rustdoc. **Recommendation: close 0281 as folded-into-0298** rather than authoring a standalone facade patch on a doc that is being retired. (If 0298 slips past S81, do the standalone trim as a fallback.)

**FIXME 0316 consumer-side (int half of the Wave-1 0316 work):**

- **`insert_detecting_ambiguity` terminal-resolve** (`imports.rs:282-332`, `target: /dev (int)`). Per the /arch Phase-3 ruling (SPRINT.md §3): before emitting `Ambiguous`, chain-follow BOTH the existing and incoming `Import` edge to their terminal `(home_module, canonical_symbol)` via `cranelisp_types::resolve_terminal_entry_and_home` (already `pub` — confirmed exported at `resolve.rs:67`; NO promotion needed) and dedup if the terminals match. Replaces the immediate-source `s1 == s2` test at L301. Pure spec-conformance fix (§8.6.4 "same original definition is NOT ambiguous"). The existing visibility-upgrade branch (L297-309) stays. Needs a /qa test for the glob+re-export-specific overlap case.
- **`recognize_macro_head` collapse to `resolve_with_fallback`** (`expander.rs:262`, the `pub(crate) fn`). Once /arch authors `cranelisp_types::resolve_with_fallback` (the new pub fn unifying the 5 prelude-fallback wrappers — types-side, /arch-owned, lands Wave 1 first), the expander's hand-rolled 3-step retry (first-hop resolve → on-miss-if-bit-on retry-rooted-at-prelude → public-only filter) collapses to one call. **Cross-crate dependency: int rebuilds against the new types seam AFTER /arch lands it.** The 4 checker.rs wrappers are typecheck-owned (the int half is just this expander wrapper). No int baseline impact (binary).

These are tracked in `design/arch/fixmes/NNNN-*.md`; this section mirrors them for design-intent visibility. The S64 audit-recommendation items (`scheduler_trace/` rename, subordinate-doc sweep) are retired: the `*_trace` rename did not survive the S76 trace relocation, and the doc-currency sweep is subsumed by the 0298 facade-retire reorg.

---

## 17. Sketch consultation

**Skipped.** The sketch was single-threaded and had no scheduler, no workers, no SharedState, no per-batch JIT, no observer contracts, no introspection store — none of int's load-bearing structures have a sketch antecedent. Decisions 31, 38, 39, 40, 41, 42 are all post-S58 reframings or pre-implementation commitments. Sketch consultation would have produced synthetic comparison content without value.
