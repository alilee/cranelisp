# Sprint 66 implementation slice — `src/` (int) + `crates/cranelisp-exe-bundle/`

**Status.** draft
**Author.** /design (int), 2026-05-06
**Reads.** `design/arch/facades/int.md` (post-S65 W3 final-state target — the largest facade in the workspace; consumer-side of every other crate); `design/int/int.md` (master design); `design/arch/facades/{types,frontend,typecheck,backend,platform,primitives,intrinsics}.md`; `design/arch/decisions/{0040,0041,0042,0043}.md` + active register entries (0010, 0011, 0027, 0030, 0031, 0035); `design/arch/fixmes/{0098,0099,0100,0103,0104,0107,0108,0150,0151}-*.md`; `design/arch/fixmes/0109-*.md` (deferred); `audits/src-20260423.md` (Sprint 62 — F1–F7 structural-debt findings); `sprints/SPRINT.md` Wave Phase 4 W4a; `design/arch/sprint-65-reshape-phase-2-review.md §3` (slice template).

This slice enumerates the concrete delta between the post-S65 final-state `facades/int.md` and the current `src/` source. It is consumed by `/sprint` as input to S66's wave plan; it is not itself a wave allocation.

The driving facts that define this slice's centre of gravity, in priority order:

1. **`int` integrates everything.** Per master-design §1, this is the largest facade by design — it owns three internal cadences (compilation, REPL, watcher), four observability sinks, the only `Code` carrier instantiation site, the gap-orchestration crossing point, the cache writer, the file watcher, the line editor, the CLI, the `--link` driver, the prelude loader, the error formatter. Every receive-side commitment lands here.
2. **The big arrivals are migrations, not authoring.** FIXME 0103 brings ~1,690 LOC (`trace.rs` + `io_trace.rs`) physically into `src/`. FIXME 0108 brings ~831 LOC (`display.rs`). Both are mechanical relocations with mechanical observer-wiring on the int side; neither is shape-design work. They dwarf the per-row novelty.
3. **D41 mutref pattern is bilateral with backend.** Backend writes `Code::Jit` and `Introspection` directly via `&self`-interior-mutable methods on the shared stores int passes in (`&DashMap<ModuleFullPath, SymbolTable<Code, ()>>`, `Option<&DashMap<FQSymbol, Introspection>>`). The int side collapses the post-loop machinery at `worker.rs:2860–3018` (~150 LOC of unpacking) into the per-symbol call-site loop documented in `facades/int.md` §"`Code` — the per-entry retention root".
4. **ResolutionGap retry loop is already in `facades/int.md`.** Pseudocode is in §"`process_form` — the gap-orchestration retry loop". This slice's contribution is wiring the source-side typed pattern-match to that pseudocode (FIXME 0098 Phase 4) and removing the ad-hoc string-parsing detection that today lives in `worker.rs`.
5. **D43 receive-side is a depends-on rewrite.** Two crate names in `Cargo.toml`; ~30+ import-path edits replacing `cranelisp_runtime::` with `cranelisp_intrinsics::` or `cranelisp_primitives::` per the migration table. Mechanical.
6. **Single-consumer reach-around landings (R4, R5, R6) get *new* int-side homes.** `CacheWritePacket` + `process_cache_packet` (R4) → `src/cache_writer.rs` (already exists; verify shape). `generate_startup_object` (R5) → `crates/cranelisp-exe-bundle/` (new). `TracedFnInfo` (R6) → `src/trace/` (new — joins the FIXME 0103 arrival).
7. **FIXME 0109 (int decomposition) is OUT OF SCOPE.** The audit's F1/F2 god-file split (`session_v4.rs` + `worker.rs`) is sequenced AFTER the S65 FIXMEs land per FIXME 0109's own sequencing note. S66 lands the receive-sides; S67+ does the decomposition against the post-S66 shape. This slice does not touch decomposition.
8. **SharedState shape is largely landed.** `facades/int.md` §"SharedState" carries the formal subset; the source's `CompilerSession` is close to it but not yet split. The S66 work is the formal split (Decision 38 receive-side) — extract `SharedState` from `CompilerSession`, thread the `Arc<SharedState>` to workers, retire the `&mut CompilerSession` worker-reach paths.
9. **Decision 38 may be a vestigial active Decision.** Per `design/arch/CLAUDE.md`'s "Active Decisions" register (excerpted in the Phase 2 review §1.1), the active list reads 0010, 0011, 0027, 0030, 0031, 0035, 0040, 0041, 0042, 0043 — D38 is NOT among them, having moved to `legacy/decisions/` once its commitment fully embodied. This slice cites the legacy file as authoritative for shape but treats the *commitment* (per-symbol mutability + SharedState formalisation) as still-pre-implementation work in source. **Open question 1** verifies this.

---

## 1. Scope from facade — delta table

Action classes (consistent with frontend + typecheck slices for cross-referencing):

- **rename** — symbol exists; signature/name changes
- **signature-change** — symbol exists with the right name but parameters/return type need adjustment
- **shape-pivot** — method form pivots to free-function form, OR struct splits, OR equivalent restructure
- **mutability-pivot** — `&mut` parameter becomes `&` (Decision 38 receive-side)
- **new** — symbol does not yet exist; must be authored
- **migrate-in** — file/code lives in another crate today and physically moves into `src/` (or `crates/cranelisp-exe-bundle/`)
- **migrate-out** — code lives in `src/` today and physically moves to another crate
- **delete** — symbol exists and must be removed
- **consolidate** — multiple parallel paths collapse to one
- **import-rewrite** — pure mechanical `use` path edit; no behaviour change
- **observer-wire** — register an observer with another crate; ring-buffer state lives int-side
- **rustdoc** — pure documentation surface change
- **verify** — facade and source already align; cross-check confirms; no source change

| # | Facade item | Source location(s) | FIXME closed | Action | Acceptance |
|---|---|---|---|---|---|
| 1 | `SharedState` struct extracted from `CompilerSession` per `facades/int.md` §"SharedState" — fields `symbol_tables`, `scheduler`, `cache`, `kept_dlls`, `introspection`, `settings`, `project_root`, `lib_dirs`, `platform_dirs` | `src/session_v4.rs` god-struct currently carries all session state on `CompilerSession`; no formal `SharedState` type | (legacy D38 — operative this sprint as receive-side embodiment) | shape-pivot + new | New `pub struct SharedState` authored; `CompilerSession` holds `Arc<SharedState>` per `facades/int.md` line 23; initiator-only fields (`watcher`, `current_repl_module`, `repl_input_active`, `worker_pool`, `warnings`) stay on `CompilerSession`. All worker entry points take `&SharedState` (or `Arc<SharedState>` at spawn). |
| 2 | Worker entry points pivot: `priority_worker_loop(shared: Arc<SharedState>)`, `nice_worker_loop(shared: Arc<SharedState>)` | `src/worker.rs` priority + nice loops currently take `&CompilerSession` (or equivalent god-struct mutability) | (legacy D38) | signature-change + mutability-pivot | Worker spawn site (`CompilerSession::new`) clones `Arc<SharedState>` per worker; loop body reaches every field via `&shared.*`; no `&mut CompilerSession` reachable from worker code. |
| 3 | `process_form(shared: &SharedState, form: Sexp, scope: &ModuleFullPath) -> Result<ProcessedForm, CranelispError>` — free-function gap-orchestration retry loop | `src/worker.rs` (and `src/session_v4.rs`'s eval path) — ad-hoc detection of unresolved-FQ-symbol-or-type via string-parsing of error messages | 0098 Phase 4 | shape-pivot + signature-change | Free function takes `&SharedState`; pattern-matches `Err(ExpansionError::Gap(...))` from `cranelisp_frontend::expand` and `Err(CheckError::Gap(...))` from `cranelisp_typecheck::check_form`; dispatches via `handle_gap` (`ensure_registered` + scheduler `wait_for_*` + macro-vs-fn discrimination + `priority_boost_jit` when needed); retries until both succeed or non-gap error fires. Termination follows facade rationale (one round-trip per FQ ref). |
| 4 | `handle_gap(shared: &SharedState, gap: ResolutionGap) -> Result<(), CranelispError>` — gap → scheduler-call translator | not yet present (gap-detection logic today is ad-hoc) | 0098 Phase 4 | new | Internal helper per `facades/int.md` §"`process_form`" pseudocode; three arms (`SymbolTypechecked`, `MacroInMem` with macro-vs-fn discrimination, `Type`); macro-vs-fn discrimination is orchestrator-owned (peek post-typecheck; only `priority_boost_jit` if entry IS macro with `code.is_none()`). |
| 5 | `ensure_registered(shared: &SharedState, module: &ModuleFullPath) -> Result<(), CranelispError>` — Phase 0 on-demand registration | not yet present | 0098 Phase 4 + (legacy D38) | new | Internal helper called from `handle_gap`; if `symbol_tables` lacks `module`, runs Phase 0 (parse → `entry(m).or_default()` → `write_structural_decls` + `defn_order` seed → drop RefMut) synchronously; then dispatches `PriorityWork::Typecheck` via scheduler. |
| 6 | `register_module` Phase 0 contract per `facades/int.md` §"register_module Phase 0" + master-design §6.1 | `src/session_v4.rs` register_module today mixes Phase 0 with later phases under single mutability hold | (legacy D38) | shape-pivot | Phase 0 brief `entry(m).or_default()` window holds `RefMut` for `write_structural_decls` + `seed_defn_order`; RefMut drops BEFORE `scheduler.register_module`. Subsequent worker-side reads use shared `.get()`, never `.entry().or_default()`. Acceptance: grep shows zero `.entry().or_default()` calls outside `register_module`'s Phase 0 block + `re_register_module`'s mirror. |
| 7 | Per-symbol mutability discipline through `process_form` body — uses shared `.get(scope)`, NOT `.entry().or_default()` | shared shard read pattern not yet adopted; `process_form`-shaped body doesn't yet exist (row 3) | (legacy D38) + 0098 Phase 4 | embodiment | After row 3 lands: typed assertion that worker code holds zero whole-module `&mut SymbolTable` outside Phase 0 + REPL `append_defn_order`; per-symbol mutation via `SymbolTable::insert_or_update(&self, ...)` and `SymbolTable::write_code(&self, sym, code)` (the latter wired to backend's direct write per row 12). |
| 8 | `compile_to_module` call-site loop — per-symbol JIT cardinality | `src/worker.rs:~2860–3018` post-loop machinery (iterate-over-names + GOT-store + `Code::Jit` construction + three error cascades) | 0098 Phase 4 + Decision 41 | delete + signature-change | Post-loop deletes; replaced by per-symbol call-site loop per `facades/int.md` §"`Code` — the per-entry retention root" + master-design §4.2: `for sym in defined_symbols(...) { let jit = Jit::new_with_symbols(&extra)?; compile_to_module(scope, &[sym], &shared.symbol_tables, shared.introspection.as_ref(), jit.jit_module())?; }`. Backend writes Code via the passed-in `&DashMap`; int does no unpacking. |
| 9 | `compile_to_module` returns `Result<(), CompilationError>` (not the previous tuple) | int side currently unpacks a backend-returned tuple | Decision 41 + 0098 Phase 4 | signature-change | Caller drops the tuple-unpacking; if `Err(CompilationError)` fires, propagate via `CranelispError::Compile(CompilationError)`. Pairs with backend slice's parallel signature change. |
| 10 | `Code` re-export — `pub use cranelisp_backend::Code;` | `src/code.rs` (397 LOC) carries `Code` enum locally | Decision 41 + 0100 Phase 2 | migrate-out + delete | `src/code.rs` deletes (or shrinks to host the int-only `SessionSymbolTable` / `SessionModuleEntry` aliases per master-design §3 row); int re-exports Code from backend. Cargo.toml unchanged (already depends on backend). |
| 11 | `SymbolTable<Code, ()>` instantiation at the session boundary | `CompilerSession` constructor today | Decision 41 (verify) | verify | Confirm `SharedState.symbol_tables: DashMap<ModuleFullPath, SymbolTable<Code, ()>>` per facade line 116; `<Code, ()>` instantiation site is the only place int names `Code` (re-exported per row 10). |
| 12 | `SymbolTable::write_code(&self, sym, code)` reach — backend writes via shared maps int passes in | int's worker post-loop currently calls `write_code` AFTER the backend-tuple unpack (or equivalent) | Decision 41 | mutability-pivot | After row 8 lands: backend's `compile_to_module` calls `write_code` directly on the worker's `&shared.symbol_tables[scope]`. Int never calls `write_code` from `worker.rs` post-codegen. (Int may still call from REPL eval shutdown / cache-load paths — verify-and-classify each call site.) |
| 13 | `Introspection` populate — parse-side: `source` + `sexp` written by `process_form` after parse + macro expansion when `shared.introspection.is_some()` | not yet wired (introspection store doesn't exist as a typed type yet — `module_sources` field on session is the closest analog and per Decision 39 is going away) | Decision 39 (legacy) + 0098 Phase 4 | new + mutability-pivot | After row 3 lands: `process_form` writes `Introspection { source: Some(snippet), sexp: Some(expanded), .. }` to `shared.introspection.as_ref().map(|m| m.insert(fq, intro))`. Field types per `facades/int.md` §"Introspection". |
| 14 | `Introspection` populate — codegen-side: `clif_ir`, `disasm`, `code_size`, `compile_duration` written by `compile_to_module` per Decision 41 | int currently collects post-codegen data via tuple-unpack | Decision 41 + Decision 39 | delete + verify | After rows 8 + 9 land: int does NOT write codegen-side introspection; backend writes directly. Verify call-site loop passes `shared.introspection.as_ref()` correctly; one-line. |
| 15 | `module_sources: DashMap<ModuleFullPath, Arc<str>>` — DELETE per Decision 39 | likely lives on `CompilerSession` or equivalent | Decision 39 (legacy) | delete | Per master-design §8.3: per-defn source on `Introspection.source` is the only source store. Caller `regenerate_backing_file` (row 23) reads from introspection, not from the deleted field. Acceptance: grep `module_sources` returns zero matches in `src/`. |
| 16 | `regenerate_backing_file` reads `defn_order` + `introspection[fq].source` | `src/save.rs` currently reads `module_sources` + per-module text | Decision 39 (legacy) | signature-change | Per master-design §8.3 pseudocode: walk `defn_order`; for each `sym`, look up `intro[fq].source`; write to file path with atomic-rename. Pairs with row 15. |
| 17 | `cranelisp-runtime` dep retires; `cranelisp-primitives` + `cranelisp-intrinsics` deps added | `src/Cargo.toml` (or workspace member) lists `cranelisp-runtime` in `[dependencies]` | 0150 (D43 receive-side) | rename + import-rewrite | Cargo.toml swaps; `pub use cranelisp_runtime::{...}` re-exports update per `facades/int.md` §"Re-exports from `cranelisp-types`" (already says nothing about runtime); imports across `src/` rewrite per 0150 migration table. |
| 18 | Import-path rewrites: `cranelisp_runtime::cranelisp_alloc` → `cranelisp_intrinsics::cranelisp_alloc`; `rc_inc`, `rc_dec`, `consume_shallow`, `dec_shallow_io`, `vec_*`, `heap_alloc_*`, `string_read`, `sconcat`, `quote_sexp`, `cranelisp_run_io`, `io_run`, `run_io_trampoline`, `ivar_*`, `runtime_panic` | various `src/` JIT registration sites, error-arm strings, runtime-fn name lookups | 0150 + 0100 | import-rewrite | Mechanical sweep; per `facades/int.md` §"Consumed surface" the intrinsics list is enumerated. Per Decision 43's category split, every backend-emitted-call target moves to intrinsics. |
| 19 | Import-path rewrites: `cranelisp_runtime::add_i64` (etc.) → `cranelisp_primitives::add_i64`; integer/float/bool ops + `int_to_string`/`parse_int`/`float_to_string`/`bool_to_string`; primitives module-table seeding | various `src/` JIT registration sites + the seed-`primitives`-module-symbol-table site | 0150 | import-rewrite | Per `facades/int.md` §"Consumed surface" `cranelisp-primitives` paragraph. Per-primitive GOT slot allocation + symbol-table entry seeded at session init. |
| 20 | IO observer registration: int registers `cranelisp_intrinsics::register_io_observer(Some(io_trace::record))` at session init when REPL/trace mode or `CRANELISP_IO_TRACE=1` | not yet wired (today io_trace.rs lives in cranelisp-runtime and there's no observer abstraction — it's direct call) | 0103 + 0150 (Phase 2 sequencing — IoObserver lives in intrinsics post-D43) | observer-wire + new | Section in `CompilerSession::new`: `if shared.introspection.is_some() || env::var("CRANELISP_IO_TRACE").is_ok() { cranelisp_intrinsics::register_io_observer(Some(io_trace::record)); install_panic_hook(); }`. Production batch (link, non-trace run) does not register — pays one relaxed null-check per call site. |
| 21 | `src/io_trace/` arrives — per-thread `VecDeque<IoEvent>` ring buffer + `record(tag, event)` observer fn + `flush_to_stderr` formatter + `IoTraceFlushGuard` RAII type | currently lives in `crates/cranelisp-runtime/src/io_trace.rs` (~952 LOC) | 0103 Phase 2 | migrate-in | Physical move from runtime to int. The ring-buffer state, FIFO overflow, env-var activation, and merge-sort across threads via shared `TRACE_ANCHOR` `Instant` (now `cranelisp_intrinsics::trace_anchor()`). Existing tests move with the file. |
| 22 | `src/trace/` arrives — broader scheduler-trace machinery (the int-side parts of the old runtime `trace.rs`) + `TracedFnInfo` (R6) | currently lives in `crates/cranelisp-runtime/src/trace.rs` (~740 LOC) | 0103 Phase 2 + Phase 2 R6 | migrate-in + new | Physical move; the runtime-side `cranelisp_trace_*` extern fns called from JIT-emitted code stay observer-driven (intrinsics keeps the symbols). `TracedFnInfo` per `facades/int.md` §"Tracing helpers" — int-only consumer concern; if a duplicate type lived backend-side previously, deletes (master-design §3 doesn't mention this; OPEN QUESTION 5). |
| 23 | `src/got_trace/` is new — per-thread `VecDeque<GotEvent>` + `record(tag, event)` + `flush_to_stderr` | not yet present | 0099 Phase 2 | new + observer-wire | Parallel shape to `io_trace`. Activator: `CRANELISP_GOT_TRACE=1` or REPL/trace mode. Session init: `cranelisp_backend::register_got_observer(Some(got_trace::record))`. Capacity convention: GOT events are coarser than IO; smaller buffer suffices (e.g. 512 entries vs IO's 4096) — concretise during implementation. |
| 24 | `src/observability.rs` renames to `src/scheduler_trace/` to fit the three-instance `*_trace` pattern | currently `src/observability.rs` (1,362 LOC) | (audit recommendation, master-design §16 item 6) | rename | Pure rename + module-path update; zero behaviour change. Sequenced with rows 21 + 23 (the other two `*_trace` modules land at the same time — treating them as a single observability batch). |
| 25 | `src/display.rs` arrives — `format_type_qualified`, `format_scheme_display` per `facades/int.md` §"Display surface" | currently lives in `crates/cranelisp-backend/src/display.rs` (~831 LOC) | 0108 | migrate-in | Physical move from backend to int. `int`'s `format_eval_result`, `format_command_result`, `format_error`, and slash-command flows call these helpers directly. Backend imports nothing from display post-move. Existing display tests in the file move alongside per `feedback_unit_tests_with_dev`. |
| 26 | `format_eval_result`, `format_command_result`, `format_error` route through display helpers | various sites in `src/session_v4.rs` (or `pretty.rs`) — likely call backend's display today | 0108 | import-rewrite | Update import paths from `cranelisp_backend::display::*` → `crate::display::*` (or the post-relocation path). |
| 27 | `format_error` adds `Platform(PlatformError)` arm — Decision 42 receive-side | `src/session_v4.rs::format_error` does not yet handle structured PlatformError | 0104 + Decision 42 | new + signature-change | Per master-design §9 + facade `format_error` rustdoc: `CranelispError::Platform(PlatformError)` arm uses the same mode-conditional `ErrorLocation`-resolution path as Parse/Reader/Expansion/Type/Codegen. The `(platform "name")` form's span flows into `location.span` at the load call site. Pairs with platform slice's PlatformError construction. |
| 28 | `load_platform_dll` constructs structured `PlatformError` (not stringly-typed) per Decision 42 | `src/platform.rs::load_platform_dll` returns `Result<…, String>` today | 0104 + Decision 42 | signature-change | Variants per `facades/types.md` PlatformError block: ManifestNotFound, ManifestParseError, DllLoadError, SymbolNotFound, SchedulingClassMismatch, etc. Each carries `ErrorLocation`. Caller `(platform "name")` expansion site populates `location.span`. |
| 29 | `cache_writer.rs` — `CacheWritePacket` + `process_cache_packet` co-located per Phase 2 reach-around R4 | `src/cache_writer.rs` exists (219 LOC) but pre-dates the typed packet shape per facade | 0100 Phase 2 (single-consumer relocation) | verify + signature-change | Per `facades/int.md` §"Cache writer": `CacheWritePacket { module: ModuleFullPath, artefact: cranelisp_backend::ObjectArtefact }`; `process_cache_packet(packet, cache: &ObjectCache) -> Result<(), CacheError>` is `pub(crate)`. Acceptance: file matches facade shape; CacheWritePacket carries `cranelisp_backend::ObjectArtefact` (not a tuple). |
| 30 | `crates/cranelisp-exe-bundle/` — `generate_startup_object` arrives per Phase 2 reach-around R5 | `src/exe.rs` (695 LOC) carries the `--link` orchestration today; the alias-`.o` builder may not be a separate function yet | 0100 Phase 2 (R5) | new + migrate-in/out | Per `facades/int.md` §"Link orchestration helpers": `pub fn generate_startup_object(entry_module: &ModuleFullPath, main_slot: usize) -> Result<Vec<u8>, CranelispError>;` lives in `crates/cranelisp-exe-bundle/`. Builds the alias `.o` per Decision 36; `link_by_name` calls it. Backend stays uniform (bare-Local for every function including main). The body of `src/exe.rs`'s alias-emission code physically moves to the new crate. |
| 31 | `link_by_name` updates collected-`.o` link to reference `cranelisp-intrinsics` + `cranelisp-primitives` static archives instead of `cranelisp-runtime` archive | `src/exe.rs` system-linker invocation lists `cranelisp-runtime` archive | 0150 + Decision 43 | rename | Per `facades/int.md` §"Link orchestration" step 5: post-D43, the previously-single `cranelisp-runtime` archive is replaced by these two siblings. Build script paths captured in consts. |
| 32 | `Sess::wait_for_typecheck_type(fqt: &FQTypeName)` — FQTypeName retry path | scheduler API may already expose; verify | (legacy D38) + 0151 (FQTypeName) | verify | Per `facades/int.md` line 367 `wait_for_typecheck_type` exists; verify the source-side scheduler implementation matches the FQTypeName parameter type (not bare TypeName). 0151 (FQTypeName) carries this commitment forward; this slice's contribution is the consumption confirmation. |
| 33 | `Sess::install_panic_hook` — installs a panic hook that flushes IO trace + scheduler trace ring buffers per `facades/int.md` §"Observability" | not yet present (existing trace flush guards use Drop only) | 0103 Phase 2 (paired) | new | Idempotent (called once at session init when trace mode is active); defers to `io_trace::flush_to_stderr` + `scheduler_trace::flush_to_stderr`. Per `facades/int.md` line 565. |
| 34 | `kept_linkers` field — DELETE (Sprint 58 Wave 3 closure already in master-design §7.4 but possibly incomplete in source) | `src/session_v4.rs` may carry `kept_linkers` | (audit-tracked; master-design §7.4) | verify-then-delete | Per master-design §7.4: only `kept_dlls` remains as a session-global side store. Per-symbol Linker retention via `Code::Linker.linker: Arc<Linker>`. Acceptance: grep `kept_linkers` returns zero in `src/`. |
| 35 | `MacroResolver` trait deletes (Decision 8 retracted; replaced by `&SymbolTables<C, L>` direct lookup per FIXME 0098 Phase 2) | `src/expander.rs` (517 LOC) carries the MacroResolver glue | 0098 Phase 2 (frontend slice) + Phase 4 (int slice) | delete | After frontend slice's row migrating `expand_sexp_recursive` to `cranelisp-frontend`: `src/expander.rs` reduces to (or deletes); the MacroEnv adapter may stay if frontend's "possibly dead" check (frontend FIXME 6) confirms it's still needed. Verify-then-delete (or verify-then-shrink). |
| 36 | `Sess::process_form` (CompilerSession method) delegates to free-function `worker::process_form(&self.shared, ...)` | not yet present (free-function form doesn't exist; row 3) | 0098 Phase 4 | new | Per `facades/int.md` line 39 + the in-line note "actual Rust may keep it as a CompilerSession method that immediately delegates to a free function". |
| 37 | `Sess::insert_symbol(&mut self, processed: &ProcessedForm, target: &ModuleFullPath)` | currently bundled into the session_v4 god-method | 0098 Phase 4 + (legacy D38) | shape-pivot | Distinct method per `facades/int.md` line 40; brief `&mut SymbolTable` window via `append_defn_order` for new defns; per master-design §8.1 "REPL append" is the only other `&mut SymbolTable` op besides Phase 0. |
| 38 | `Sess::trampoline(&mut self, module_name: &str) -> Result<(i64, Type), CranelispError>` | `Sess::trampoline` exists but possibly takes `module_name: &str` per facade (verify) | (verify-only) | verify | Per `facades/int.md` line 49. The runtime cadence entry per `exec-flow-runtime`. |
| 39 | `pub use` from `cranelisp-types` — facade re-export wall per `facades/int.md` §"Re-exports from cranelisp-types" | `src/lib.rs` likely re-exports a different set today | 0109 (Wave B — narrow lib.rs) — DEFERRED | (deferred) | Per `facades/int.md` lines 829–839: 33-item re-export wall. **This row is OUT OF SCOPE in S66 per FIXME 0109 deferral (audit recommendation 4).** Listed for completeness; work happens in S67+ vertical. |
| 40 | `session.rs` (v3) — DELETE (audit F6) | `src/session.rs` (543 LOC) | 0109 Wave A — DEFERRED | (deferred) | OUT OF SCOPE per FIXME 0109. Listed for completeness; work happens in S67+ vertical. |
| 41 | `session_v4.rs` decomposition (audit F1) — DELETE | n/a (decomposition) | 0109 Wave D — DEFERRED | (deferred) | OUT OF SCOPE per FIXME 0109. Listed for completeness; work happens in S67+ vertical. |
| 42 | `worker.rs` decomposition (audit F2) — DELETE | n/a (decomposition) | 0109 Wave C + Wave D — DEFERRED | (deferred) | OUT OF SCOPE per FIXME 0109. Listed for completeness; work happens in S67+ vertical. |
| 43 | `OwnedPlatformFnDescriptor` `#[non_exhaustive]` (R9 on the int side — verify) | platform owns the type; int consumes | 0107 (R9 already landed `25fa73a`) | verify | Verify int's pattern-match sites on `OwnedPlatformFnDescriptor` honour the `#[non_exhaustive]` discipline (catch-all arm); no source change expected since R9 truth-telling already landed. |
| 44 | `Sess::list_user_definitions`, `describe_symbol`, `module_imports`, `module_exports`, `current_repl_module`, `set_current_repl_module`, plus per-symbol introspection accessors (`symbol_source`, `symbol_sexp`, `symbol_clif`, `symbol_disasm`, `symbol_code_size`, `symbol_compile_duration`) | `src/session_v4.rs` has equivalents but routing through `module_sources` and the older introspection structure | (legacy D38, D39) | signature-change | Per `facades/int.md` lines 80–93: each accessor reads `shared.introspection[fq].*` (not the deleted `module_sources`). Mechanical conversion of ~6 method bodies. |
| 45 | `SlashCommand` enum — verify variants per `facades/int.md` line 254 | likely already present | (verify) | verify | Per facade lines 254–260: 17 commands per master-design §8.5 + `repl/spec.md`. Verify enum complete; add `Quit` if missing. |
| 46 | `EvalResult`, `EvalValue`, `HeapRetention` shapes per facade lines 206–239 | likely already present in similar shape | (verify) | verify | Mechanical signature confirmation. |
| 47 | `Introspection` struct — formal type per `facades/int.md` §"Introspection" | not yet authored as a formal type (probably scattered fields today) | Decision 39 (legacy) + Decision 41 | new | Per facade lines 294–321: `pub struct Introspection { source, sexp, clif_ir, disasm, code_size, compile_duration }`. `#[non_exhaustive]`. |
| 48 | `cranelisp-frontend` consumed surface aligns with frontend slice (`expand`, `build_ast`, `parse`, `parse_*_sexp`, `expand_quasiquotes`, `parse_preserving_comments`, `ParseProduct`, `DefmacroInfo`, `Ast`, `ExpansionError`) | currently consumes a different surface (the in-int expander.rs is the resolver) | 0098 Phase 2 (frontend) + Phase 4 (int) | import-rewrite | Mechanical sweep per `facades/int.md` line 850. Pairs with row 35 (MacroResolver delete) — once `cranelisp-frontend::expand` is the source of truth, all int sites consume from there. |
| 49 | `cranelisp-typecheck` consumed surface aligns with typecheck slice (`check_form` free-function form, `CheckResult`, `CheckError`, `CheckState`, `TypeCheckEnv`, `register_builtins`, trace install hook) | currently consumes the older `TypeCheckEnv::check_form` method form via various paths | 0098 Phase 3 (typecheck) + Phase 4 (int) | import-rewrite + signature-change | Mechanical sweep per `facades/int.md` line 851. The signature change is wrapping `check_form` to take `&SymbolTable` not `&mut SymbolTable` — pairs with typecheck slice row 1. |
| 50 | `cranelisp-backend` consumed surface aligns with backend slice (`compile_to_module` returns `Result<(), CompilationError>`; `Code` re-export; `CompilationError` carries `SymbolNotCompilable` variant; `GotObserver` + `GotEvent` + `GotEventTag` + `GotProvenance` + `register_got_observer`; cranelift re-exports) | currently consumes pre-D41 backend surface | Decision 41 + 0099 Phase 1 + 0100 Phase 2 | import-rewrite + signature-change | Mechanical sweep per `facades/int.md` line 852. Pairs with backend slice's parallel signature changes. |
| 51 | `cranelisp-platform` consumed surface aligns with platform slice (`HostContext`, `HostCallbacks`, `OwnedPlatformFnDescriptor`, `PlatformFn`, `load_manifest`, `parse_type_sig`, `derive_jit_name`); `HostContext::dispatch` removed | currently consumes pre-§2.13 platform surface | Decision 42 + (§2.13 already landed) | verify + import-rewrite | Per `facades/int.md` line 855. `int` constructs `HostCallbacks` at session init pointing at intrinsics fns (post-D43, callbacks point into intrinsics not runtime — verify this rewrite). |
| 52 | Session-init observer bundle — at `CompilerSession::new` end, conditionally register IoObserver + GotObserver, install panic hook | not yet wired (today's code skips observer registration entirely) | 0099 Phase 2 + 0103 Phase 2 + (legacy D38) | new | Per `facades/int.md` lines 522–527 + 545 + 562: a single bundled init block at session construction; activator mode: `shared.introspection.is_some()` OR specific env-var. |
| 53 | Cache-hit-typecheck path — `notify_typecheck_done_from_cache` → enqueue `LoadObject` (not `Jit`) | per master-design §7.1 + Decision 37; verify source | Decision 37 (legacy) | verify | Cache-hit decision lives in recursive `register_module` flow per master-design §7.1 pseudocode. The pre-Sprint-58 `try_cache_hit_load` parallel orchestrator stays deleted. Acceptance: grep `try_cache_hit_load` returns zero. |
| 54 | LoadObject worker — error on `linker.get_symbol(name) == None` (no swallowed failures) | `src/worker.rs` LoadObject path may pre-Sprint-58 swallow | (legacy operational invariant) | verify | Per master-design §7.1 "No swallowed failures": LoadObject worker errors with `CacheLoadError` (or equivalent typed variant) on missing symbol; never silently pushes to `loaded_symbols`. |

**Total rows: 54.** By action class:

- **verify**: 11 rows (11, 14, 32, 34, 38, 43, 45, 46, 51, 53, 54)
- **import-rewrite**: 8 rows (17, 18, 19, 26, 35 → trending-toward-delete, 48, 49, 50, 51) — mechanical
- **new**: 9 rows (1, 4, 5, 13, 23, 27, 30, 33, 36, 47, 52)
- **migrate-in**: 4 rows (21, 22, 25, 30 — paired)
- **migrate-out + delete**: 2 rows (10, 30 — paired with new)
- **shape-pivot**: 4 rows (1, 3, 6, 37) — including row 1's compound shape-pivot+new
- **signature-change**: 8 rows (2, 3, 9, 16, 27, 28, 29, 44, 49, 50)
- **mutability-pivot**: 3 rows (2, 7, 12, 13 — paired)
- **delete**: 4 rows (8, 15, 34 — verify-then-delete, 35 — verify-then-delete)
- **rename**: 2 rows (17, 24, 31)
- **observer-wire**: 2 rows (20, 23)
- **embodiment**: 1 row (7)
- **deferred** (FIXME 0109): 4 rows (39, 40, 41, 42) — listed for completeness

(Several rows compound multiple action classes — the headline row 3 is shape-pivot + signature-change + new — counted under primary verb above.)

Single-action distribution (counting compound rows by primary verb, ignoring deferred): import-rewrite 8, verify 11, new 9, signature-change 8, migrate-in 4, mutability-pivot 3, delete 4, shape-pivot 4, rename 3, observer-wire 2, migrate-out 1, embodiment 1, plus 4 deferred.

---

## 2. Ordering within the slice

The slice has internal dependencies that bind the work order. Ordering is shaped by external prerequisites (other slices' row-1 shapes must land first), by physical-relocation discipline (move files before rewriting their callers), and by the audit's recommendation that decomposition (FIXME 0109) sequences AFTER the receive-side work.

1. **External prerequisites (NOT in this slice)**:
   - **Types slice** — FIXME 0098 Phase 1: lands `ResolutionGap`, `CheckError` (pending OQ in typecheck slice §6 about CheckError home), `ExpansionError`, `CompilationError` (post-FIXME 0100 Phase 2 home is in backend, not types — coordinate). Also FIXME 0151's FQTypeName threading. Phase 1 prerequisite for rows 3, 4, 27, 28, 49, 50.
   - **Frontend slice** — `expand` migrates from `src/expander.rs` to `cranelisp-frontend`; `ExpansionError` exists; `parse`/`build_ast` final shape lands. Prerequisite for rows 35, 36, 48.
   - **Typecheck slice** — `check_form` free-function form returning `Result<CheckResult, CheckError>` lands; `register_builtins` single-table shape; per-symbol mutability discipline reaches typecheck's mutation paths. Prerequisite for rows 3, 49.
   - **Backend slice** — `compile_to_module` returns `Result<(), CompilationError>` and writes Code/Introspection directly; `Code` lives in `cranelisp-backend/src/code.rs`; `register_got_observer` exists; `display.rs` ready to receive (prep — int-side row 25 is the move). Prerequisite for rows 8, 9, 10, 12, 23, 25, 50.
   - **Platform slice** — `PlatformError` carries `ErrorLocation`; `HostContext::dispatch` removed; `OwnedPlatformFnDescriptor` `#[non_exhaustive]`. Prerequisite for rows 27, 28, 51.
   - **Primitives slice + Intrinsics slice + Runtime-retiring slice** (D43): the new crates exist with the migration table executed; `cranelisp-runtime` retires (per FIXME 0150). Prerequisite for rows 17, 18, 19, 31. **0103 Phase 1 (runtime exposes IoObserver) has been folded into 0150 Phase 2 — IoObserver lives in cranelisp-intrinsics post-D43 per Decision 43 + Phase 2 review §1.1.** Prerequisite for row 20.

   This is by far the most external prerequisite-heavy slice in the sprint. **Every other slice except `/qa` is an upstream dependency.**

2. **Wave A — physical relocations land first (zero-dep mechanical moves)**.
   - Row 21 (`src/io_trace/` arrives from runtime).
   - Row 22 (`src/trace/` arrives from runtime; `TracedFnInfo` joins).
   - Row 25 (`src/display.rs` arrives from backend).
   - Row 24 (`src/observability.rs` rename to `src/scheduler_trace/`).
   - Row 30 (`crates/cranelisp-exe-bundle/` receives `generate_startup_object` — prep step; the body moves out of `src/exe.rs`).
   - Row 10 (delete `src/code.rs`; re-export from backend).

   These are file-shuffles that establish int's post-relocation footprint. They must precede the import-rewrite sweep so that downstream rewrites have a stable target. ~1.5–2 days.

3. **Wave B — Cargo + import-rewrite sweep (mechanical, large blast radius)**.
   - Row 17 (`Cargo.toml` swap: runtime out, primitives + intrinsics in).
   - Rows 18, 19 (intrinsics + primitives import rewrites — every JIT registration site, every runtime-fn name lookup, every error-arm string).
   - Row 31 (`exe.rs` linker invocation — runtime archive → primitives + intrinsics archives).
   - Rows 48, 49, 50, 51 (frontend, typecheck, backend, platform consumed-surface alignment).
   - Row 26 (display imports follow row 25's relocation).

   Single coordinated commit (or one per crate) to minimise inconsistent intermediate states. ~1 day mechanical; tests must compile after this wave or a defect is live.

4. **Wave C — `SharedState` extraction + worker mutability pivot (the structural centrepiece)**.
   - Row 1 (`SharedState` struct extracted from `CompilerSession`).
   - Row 2 (worker entry points pivot to `&SharedState`).
   - Row 6 (Phase 0 brief-window discipline).
   - Row 7 (per-symbol mutability discipline embodiment).
   - Row 11 (verify `SymbolTable<Code, ()>` instantiation).
   - Row 34 (verify-then-delete `kept_linkers`).

   The most invasive structural change. Touches `session_v4.rs` and `worker.rs` (the F1+F2 god-files) extensively. Per the principle of pivoting before decomposing (master-design §16 + FIXME 0109's "AFTER S65 FIXMEs" sequencing), this lands BEFORE any decomposition happens. ~3–4 days.

5. **Wave D — `process_form` gap-orchestration retry loop (the contract centrepiece)**.
   - Row 3 (`process_form` free-function shape; typed pattern-match on `ExpansionError::Gap` and `CheckError::Gap`).
   - Row 4 (`handle_gap` translator).
   - Row 5 (`ensure_registered` Phase-0-on-demand).
   - Row 36 (CompilerSession-method facade delegating to free function).
   - Row 35 (verify-then-shrink-or-delete `expander.rs`'s MacroResolver glue).
   - Row 32 (verify `wait_for_typecheck_type` FQTypeName parameter).

   Lands AFTER Wave C (because `process_form` consumes `&SharedState`). The typed pattern-match is mechanical once frontend + typecheck slices' typed errors exist; the gap-handling logic IS the facade pseudocode. ~1.5–2 days.

6. **Wave E — `compile_to_module` per-symbol JIT call-site loop + Introspection wiring**.
   - Row 8 (delete the worker.rs:2860–3018 post-loop; replace with per-symbol call-site loop).
   - Row 9 (drop tuple-unpacking of `compile_to_module` return; handle `Result<(), CompilationError>`).
   - Row 12 (verify backend writes `Code::Jit` directly via `&self`-interior-mutable methods; remove duplicate `write_code` calls from int).
   - Row 13 (parse-side Introspection populate).
   - Row 14 (verify codegen-side Introspection writes happen backend-side, not int-side).
   - Row 47 (`Introspection` formal type authored).

   Pairs with backend slice's row landing the per-symbol cardinality. ~1 day.

7. **Wave F — Decision 39 source-store collapse**.
   - Row 15 (delete `module_sources` field — by this point, nothing reads it because Wave C/D/E rerouted to introspection).
   - Row 16 (`regenerate_backing_file` reads from introspection).
   - Row 44 (per-symbol introspection accessors route through `shared.introspection`).

   ~half-day. Strictly sequential after row 13/47 land.

8. **Wave G — Decision 42 PlatformError receive-side**.
   - Row 28 (`load_platform_dll` constructs structured PlatformError).
   - Row 27 (`format_error` adds Platform arm).
   - Row 43 (verify `OwnedPlatformFnDescriptor` `#[non_exhaustive]` pattern-match sites).

   Independent of waves C–F (different files). Parallelisable with Wave E or F if context allows. ~half-day.

9. **Wave H — Observability finalisation**.
   - Row 20 (IO observer registration at session init).
   - Row 23 (`src/got_trace/` authored + GotObserver registration).
   - Row 33 (`install_panic_hook` authored).
   - Row 52 (session-init observer bundle).

   Sequenced AFTER Wave A (the physical relocations land first) and Wave C (because the activation gate is `shared.introspection.is_some()`). ~half-day per observer (so ~1.5 days for IO + GOT + panic-hook bundle).

10. **Wave I — facade-surface verifies + small alignments**.
    - Rows 38, 45, 46, 51, 53, 54 (verify-class).
    - Rows 29, 37 (cache_writer + insert_symbol shape verification).

    ~half-day. Mostly grep-and-classify.

11. **Wave J — DEFERRED per FIXME 0109** (audit F1, F2, F5, F6 — decomposition + lib.rs narrow + session.rs delete). Rows 39, 40, 41, 42. Out of scope.

**Wave summary**: A → B → C → (D + E + G + H in parallel where possible) → F → I → [J deferred].

The total wave count (excluding J) is 9 internal mini-waves; `/sprint` will collapse these into S66 sprint-waves at the wave-plan boundary based on context budget. The strict sequencing constraints are:
- Wave A precedes Wave B (relocations before import rewrites).
- Wave C precedes Waves D, E, F, H (SharedState shape is universal).
- Wave D precedes Wave E (process_form is the per-symbol-call-site driver — though E could land first if D is delayed, which would mean retaining ad-hoc detection temporarily).
- Wave F succeeds Waves D + E (introspection populate must happen before deleting `module_sources`).
- Wave I closes verification.

---

## 3. Estimated effort

**Three-to-four S66 waves for `/dev` (int) — the largest single per-crate slice in the sprint by code volume and migration complexity.** This is consistent with master-design §1's "int is the largest surface" framing and with the audit's F1+F2 god-file sizing (5,417 + 5,041 = 10,458 LOC across the two affected files alone).

Sizing breakdown:

- **Wave A — physical relocations** (rows 10, 21, 22, 24, 25, 30): **~1.5–2 days**. ~2,500 LOC of files-arriving (1,690 from runtime + 831 from backend) + ~150 LOC of files-departing (`src/code.rs` 397 minus the surviving aliases ~150). Mechanical `git mv` + minor adjustments to `lib.rs`/module declarations. Tests move with files.
- **Wave B — Cargo + import-rewrite sweep** (rows 17, 18, 19, 26, 31, 48, 49, 50, 51): **~1 day**. ~80–120 import-path edits across `src/`. Some sites are `pub use` re-export shims that simplify or delete; some are direct `use` clauses. Build passes after the wave.
- **Wave C — SharedState + mutability pivot** (rows 1, 2, 6, 7, 11, 34): **~3–4 days**. The structural centrepiece. Touches `session_v4.rs` (5,417 LOC) and `worker.rs` (5,041 LOC) extensively. Field-by-field migration off `CompilerSession` onto `SharedState`; worker thread-creation site retargets to clone `Arc<SharedState>`; every `&mut self` access by workers becomes `&shared.field`. Tests need to compile against the new shape — large-but-mechanical adjustment.
- **Wave D — process_form retry loop** (rows 3, 4, 5, 32, 35, 36): **~1.5–2 days**. Authoring `handle_gap` from facade pseudocode is straightforward. Wiring the typed pattern-match in place of ad-hoc detection is straightforward once typed gaps exist (frontend + typecheck slices' work). The verify-then-delete on `expander.rs`'s MacroResolver glue is the only real risk — if frontend's "possibly dead" check (frontend FIXME 6) determines `MacroEnv` is still load-bearing, it stays; if not, it deletes. Plan for delete; tolerate stay.
- **Wave E — compile_to_module call-site loop** (rows 8, 9, 12, 13, 14, 47): **~1 day**. Deleting the worker.rs post-loop machinery is small — ~150 LOC out. Wiring the new per-symbol call-site loop is small — ~30 LOC in. The Introspection populate (row 13) is small — one conditional insert per `process_form` success path. Authoring the formal `Introspection` struct (row 47) is small — type definition with `#[non_exhaustive]`.
- **Wave F — D39 source-store collapse** (rows 15, 16, 44): **~half-day**. Delete the field; rewrite `regenerate_backing_file`; rewrite the ~6 introspection accessors to read from `shared.introspection`. Grep-and-classify all `module_sources` references first (zero acceptable).
- **Wave G — PlatformError receive-side** (rows 27, 28, 43): **~half-day**. Authoring the structured PlatformError construction and the format_error arm.
- **Wave H — Observability finalisation** (rows 20, 23, 33, 52): **~1.5 days**. Authoring `src/got_trace/` from scratch (parallel shape to `io_trace`); wiring three observer registrations; authoring `install_panic_hook`. The GOT trace authoring is the largest sub-item — ~200 LOC including ring-buffer state, FIFO overflow, env-var activation, formatter, RAII guard.
- **Wave I — facade-surface verifies + small alignments** (rows 11, 14, 29, 32, 34, 37, 38, 43, 45, 46, 51, 53, 54): **~half-day**. Mostly grep-and-classify.

**Total: ~10–13 working days = ~2.5–3 S66 waves.** Comparable in scale to the typecheck slice; somewhat more than frontend/backend/platform individually.

The slice is **wave-fissurable in two natural points**:
- **First fissure** — between Wave B and Wave C. Waves A + B (physical relocations + Cargo/import sweep) form a coherent first block — purely mechanical migration; the receive-side of the multi-crate D43 + relocation work. After this block, every other crate's source surface is reachable via the new paths, and downstream consumer rewrites can land in any order.
- **Second fissure** — between Wave C and Waves D/E/F/G/H. Wave C (SharedState pivot) is the largest structural change and stands alone; Waves D + E + F + G + H are the receive-side commitments to other slices' structural changes (D41, D42, FIXME 0098, 0099, 0103) and largely parallelise.

If the sprint envelope tolerates ~2 waves only for int, the irreducible minimum is Waves A + B + C — the structural foundation for everything else. Receive-side rows for the headline contracts (D41 mutref, D42 PlatformError, ResolutionGap retry loop, observability) defer to a follow-up sprint if necessary, with same-sprint `/arch` FIXMEs documenting the deferral rationale per S65 Hard Constraint #1's tolerance commitment. **However, deferring D + E + F + G + H is risky** — those rows are the load-bearing receive-sides for backend/frontend/typecheck/platform/runtime-retiring slices; if they don't land alongside the upstream slices' source changes, the multi-crate workspace doesn't compile. Strong recommendation: land all of A + B + C + D + E + F + G + H in S66.

If int is wave-budget-binding, **`/sprint` should consider expanding S66's int-targeted wave envelope rather than splitting receive-side work across S66 + S67**.

---

## 4. Dependencies on other crates' slices

Bilateral dependency table — each row identifies the corresponding entry in the depended-on (or depended-upon-by) crate's slice. **Int sits at the bottom of the dep graph** — every other crate is upstream; nothing downstream depends on int (int is the application root).

| This slice's item | Depends on | In the other crate's slice |
|---|---|---|
| Row 3 (`process_form` typed pattern-match on `ExpansionError::Gap`) | `ExpansionError::Gap(ResolutionGap)` exists in `cranelisp-frontend` | frontend slice (FIXME 0098 Phase 2): land `ExpansionError` enum in frontend; `MacroInMem(FQSymbol)` is a Gap variant produced by `expand` |
| Row 3 (`process_form` typed pattern-match on `CheckError::Gap`) | `CheckError::Gap(ResolutionGap)` exists in `cranelisp-typecheck` | typecheck slice (FIXME 0098 Phase 3 + 0100 Phase 1): land `CheckError` in typecheck (post-relocation); `Gap(ResolutionGap)` and `TypeError { location: ErrorLocation, .. }` variants |
| Row 3 (`ResolutionGap` enum reachable to int) | `ResolutionGap` lives in `cranelisp-types` (multi-consumer exception per Principle 15) | types slice (FIXME 0098 Phase 1): land `ResolutionGap` enum in `cranelisp-types`; variants `SymbolTypechecked(FQSymbol)`, `MacroInMem(FQSymbol)`, `Type(FQTypeName)` |
| Row 3 (`process_form` shape — `&SharedState` parameter) | typecheck's `check_form` accepts `&SymbolTable<C, L>` (not `&mut`) | typecheck slice row 1 + row 12: `check_form` mutability-pivot to `&SymbolTable` — the typecheck-side mirror of int's per-symbol mutability discipline |
| Row 8 (per-symbol JIT call-site loop) | `compile_to_module` accepts the multi-arg signature with `&DashMap<ModuleFullPath, SymbolTable<Code, ()>>` and `Option<&DashMap<FQSymbol, Introspection>>` | backend slice (Decision 41): land `compile_to_module(scope: &ModuleFullPath, defined: &[Symbol], symbol_tables: &DashMap<...>, introspection: Option<&DashMap<...>>, jit_module: ...) -> Result<(), CompilationError>` |
| Row 9 (handle `Result<(), CompilationError>`) | `CompilationError` enum lives in `cranelisp-backend` (post-FIXME 0100 Phase 2) | backend slice (FIXME 0100 Phase 2): relocate `CompilationError` from `cranelisp-types` to `cranelisp-backend`; variants per `facades/backend.md` §"Errors" including `SymbolNotCompilable` |
| Row 10 (Code re-export) | `Code` enum lives in `cranelisp-backend/src/code.rs` (post-Decision 41) | backend slice (Decision 41): relocate `Code` from int to backend; backend constructs `Code::Jit { jit, ptr }` directly |
| Row 12 (`SymbolTable::write_code(&self, sym, code)` reach) | `SymbolTable` has `&self`-interior-mutable `write_code` method | types slice (FIXME 0008): per-symbol mutability discipline embodied on `SymbolTable` API |
| Row 13 (parse-side Introspection populate from `process_form`) | `process_form` is the post-parse + post-expansion site; Introspection struct exists | this slice + master-design §8.2 |
| Row 17 (Cargo.toml swap) | `cranelisp-primitives` + `cranelisp-intrinsics` crate skeletons exist; `cranelisp-runtime` retires | runtime-retiring slice + primitives slice + intrinsics slice (FIXME 0150 Phase 1 + Phase 2): the crate split lands |
| Rows 18, 19 (intrinsics + primitives imports) | every symbol in the migration table lives in its post-D43 home | runtime-retiring slice + primitives slice + intrinsics slice (FIXME 0150 Phase 2): per-source-file migration table executed |
| Row 20 (IO observer registration to intrinsics) | `cranelisp_intrinsics::register_io_observer` exists | intrinsics slice (FIXME 0150 Phase 2 + 0103 Phase 1 folded): IoObserver registration API lives in `cranelisp-intrinsics`; `IoEvent`, `IoEventTag`, `register_io_observer`, `trace_anchor` all surfaced |
| Row 21 (`src/io_trace/` arrives from runtime) | runtime-retiring slice physically deletes `crates/cranelisp-runtime/src/io_trace.rs` | runtime-retiring slice: the file moves out (or duplicates briefly during the sprint window — `/sprint` chooses) |
| Row 22 (`src/trace/` arrives from runtime) | runtime-retiring slice physically deletes `crates/cranelisp-runtime/src/trace.rs` | runtime-retiring slice |
| Row 23 (GOT observer registration to backend) | `cranelisp_backend::register_got_observer` + `GotObserver` + `GotEvent` + `GotEventTag` + `GotProvenance` exist | backend slice (FIXME 0099 Phase 1): land GOT observer contract in `cranelisp-backend/src/got_observer.rs` |
| Row 25 (`src/display.rs` arrives) | backend slice physically deletes `crates/cranelisp-backend/src/display.rs` | backend slice (FIXME 0108): the file moves out |
| Row 27 (format_error Platform arm) | `PlatformError` exists with `ErrorLocation` per variant | platform slice + types slice (Decision 42): `PlatformError` enum in `cranelisp-types` (per Decision 42's "lives in cranelisp-types"); `CranelispError::Platform(PlatformError)` variant |
| Row 28 (load_platform_dll PlatformError construction) | `PlatformError` variants per platform's needs | platform slice (Decision 42): variant set finalised |
| Row 29 (`CacheWritePacket` carries `cranelisp_backend::ObjectArtefact`) | `ObjectArtefact` is a public type in `cranelisp-backend` | backend slice: `ObjectArtefact { object_bytes: Vec<u8>, sidecar: SymbolTable<(), ()> }` (or equivalent) public type |
| Row 30 (`generate_startup_object` lives in exe-bundle) | `crates/cranelisp-exe-bundle/` crate exists | this slice (the exe-bundle is part of int's BC per master-design §1) — possibly authored alongside this slice's int work, possibly a single-crate-skeleton landing |
| Row 31 (linker invocation references primitives + intrinsics archives) | static archives for both crates exist | runtime-retiring slice + primitives slice + intrinsics slice: `[lib]` configurations enable static archive output |
| Row 35 (`MacroResolver` delete) | frontend's `expand` is the source of truth for macro resolution | frontend slice (FIXME 0098 Phase 2): `expand` migrated; `MacroResolver` trait dropped (Decision 8 retracted) |
| Rows 48, 49, 50, 51 (consumed surface alignment) | each upstream crate's facade-conformant public surface | frontend slice + typecheck slice + backend slice + platform slice (each crate's row 1 alignment) |
| Row 52 (session-init observer bundle) | both `cranelisp_intrinsics::register_io_observer` and `cranelisp_backend::register_got_observer` exist | intrinsics slice + backend slice: both registration APIs land |

**Cross-crate count: ~24 distinct dependency rows naming 7 other slices** — types slice (4 rows), frontend slice (3 rows), typecheck slice (2 rows), backend slice (8 rows — the densest dependency), platform slice (3 rows), intrinsics slice (4 rows), runtime-retiring slice (4 rows), primitives slice (2 rows). The qa slice is named in §5 (e2e tests).

The dependency graph from int's perspective is **dense and acyclic, with deep upstream fan-in**. Int is the leaf consumer; every other crate's row 1 (or its key receive-side facing-int row) is an upstream prerequisite. No cycle; no triad-cycle hazard. Per Principle 3 (dependency flows toward stability), int sits at the bottom of the DAG and depends on every other implementation crate.

**Wave sequencing implication for `/sprint`**: Int's Wave A (physical relocations) requires runtime-retiring + backend slices' "remove the file" rows to be complete OR coordinated as `git mv` sequenced atomically. Int's Wave B (import sweep) requires every upstream crate's row 1 to be at least authored. Int's Waves C–H are receive-side embodiments and can land alongside (or slightly after) the upstream rows that motivate them. **If `/sprint` runs the upstream slices in parallel within an early S66 wave and folds Int's A + B into a follow-up wave that synchronises with all of them, the dependency graph collapses to two macro-waves.**

---

## 5. Test surface impact

### Existing tests touched

`src/` carries inline tests within most files (a known structural-debt item per audit F1 — `session_v4.rs` carries large in-file tests). `tests/` (the e2e suite) is `/qa`'s domain, NOT this slice.

Unit-test impact within `src/`:

- **`session_v4.rs` tests**: heavy adaptation to `SharedState` extraction (Wave C, row 1). Tests that today instantiate `CompilerSession` directly retarget to instantiate the post-Wave-C shape. **Significant volume; mostly mechanical** (re-route field accesses through `Arc<SharedState>`).
- **`worker.rs` tests**: heavy adaptation to free-function `process_form` (Wave D, row 3). Tests that drive worker behaviour through ad-hoc detection retarget to the typed-Gap path. **Moderate volume**; the pattern-match shape is simpler than the current ad-hoc shape.
- **`scheduler.rs` tests**: minor — `wait_for_typecheck_type` confirmation (row 32) may need a unit test if not already present.
- **`save.rs` tests**: moderate adaptation per row 16 (`regenerate_backing_file` reads from introspection, not `module_sources`). Tests today probably fixture the deleted field; rewrite to fixture introspection entries.
- **`platform.rs` tests**: PlatformError construction tests (row 28). Moderate volume; mechanical once the variants are pinned.
- **`expander.rs` tests**: depending on Wave D, row 35's verify-then-delete outcome. If MacroEnv stays, tests stay; if deletes, tests delete.
- **observability/io_trace/got_trace tests**: tests move physically with their files (Waves A, H). New `got_trace` tests authored from scratch (~3–5 unit tests for ring-buffer overflow, env-var activation, formatter output).

### New unit tests authored inside `src/`

Per the project test strategy memory (`feedback_unit_tests_with_dev`, `project_test_strategy.md` — unit tests with /dev), narrow tests authored inside `src/` for this slice's new code:

- **`process_form` returns Gap-typed errors and dispatches via handle_gap** (acceptance for rows 3, 4). Stub `SharedState` with empty symbol_tables; call `process_form` with a form referencing unresolved `m2/foo`; assert one of: (a) function eventually succeeds after stub-typecheck-completion event fires, (b) returns `SchedulerError::Cycle` on stubbed cycle, (c) returns non-Gap error with stubbed error.
- **`handle_gap` macro-vs-fn discrimination** (acceptance for row 4). Stub a SymbolTable with an entry that's a macro vs an entry that's a function; pass `MacroInMem(fq)` for each; assert macro path triggers `priority_boost_jit`, function path does not.
- **`ensure_registered` runs Phase 0 synchronously** (acceptance for row 5). Stub `shared` without module M; call `ensure_registered(shared, M)`; assert post-call `shared.symbol_tables.contains_key(M)` and structural decls were written.
- **`SharedState` extraction — workers don't see `&mut`** (acceptance for rows 1, 2). Compile-time verification (the type signatures enforce); plus a test that spawns a worker, sends it a work item, and asserts mutation visible to the initiator via `&shared.field` reads.
- **Per-symbol mutability discipline — no whole-module `&mut SymbolTable` outside Phase 0** (acceptance for rows 6, 7, 23). Grep-and-assert: count `entry().or_default()` and `&mut SymbolTable` reachable from worker code; expect zero matches outside the single Phase-0 block.
- **`Introspection` populate — populate iff `shared.introspection.is_some()`** (acceptance for rows 13, 14). Construct `shared` with `introspection = None`; run `process_form`; assert no populate. Construct with `introspection = Some(...)`; run; assert populate happened.
- **`module_sources` field deletion verification** (acceptance for row 15). Compile-time verification (the field doesn't exist); plus runtime assertion that `regenerate_backing_file` reads exclusively from `shared.introspection`.
- **`regenerate_backing_file` walks `defn_order` and concatenates from introspection** (acceptance for row 16). Stub introspection with two entries; stub `defn_order` with both syms in known order; call; assert output text is concatenation in order.
- **`format_error` Platform arm uses ErrorLocation** (acceptance for row 27). Construct `CranelispError::Platform(PlatformError::ManifestNotFound { location: ... })`; format; assert output contains the location's file:line:col coordinate.
- **`load_platform_dll` returns structured PlatformError on missing manifest** (acceptance for row 28). Stub a `(platform "nonexistent")` form; assert `Err(PlatformError::ManifestNotFound { .. })`, not stringly-typed.
- **IoObserver registration is conditional on activator mode** (acceptance for row 20). Construct `shared` with `introspection = None` and `CRANELISP_IO_TRACE` unset; assert `cranelisp_intrinsics::register_io_observer` was NOT called (mockable). With either activator true: assert WAS called.
- **GotObserver registration is conditional on activator mode** (acceptance for row 23). Mirror.
- **`got_trace::record` overflow behaviour** (acceptance for row 23). Push >capacity events; assert FIFO eviction.
- **`install_panic_hook` is idempotent** (acceptance for row 33). Call twice; assert no double-install.

**~14 new unit tests authored inside `src/`** for this slice.

E2E coverage of the gap-orchestration retry loop, the per-symbol JIT cardinality (D41 receive-side), the structured PlatformError display, and the observability flushes is `/qa`'s domain in `tests/`. Per `feedback_repros_join_suite.md` and `project_test_strategy.md`, this slice files FIXMEs against `/qa` if the S66 test plan slice doesn't enumerate:

- An e2e test exercising `process_form`'s typed pattern-match on Gap (frontend Gap + typecheck Gap, separate scenarios).
- An e2e test exercising D41 per-symbol JIT cardinality (multi-defn module with introspection populated correctly per symbol).
- An e2e test exercising structured PlatformError surfacing in REPL display.
- An e2e test exercising IO + GOT trace flush on session shutdown.
- An e2e test exercising panic-hook flush.

**File against `/qa`**: 5 e2e test enumerations if the test plan slice is silent on these. Per feedback memory, these are e2e (`tests/`), not unit — the unit tests above are this slice's contribution; the e2e is `/qa`'s.

### Existing e2e tests touched

E2E tests in `tests/` exercise the binary; `--run` and REPL behaviour SHOULD be invariant under this slice's migrations. Watch for:

- E2E tests asserting on stringly-typed PlatformError output (row 28) — adjust to match the structured format.
- E2E tests asserting on ad-hoc gap-detection error messages (row 3) — adjust to match the typed-Gap-resolution path.
- E2E tests inspecting `module_sources` directly (row 15) — adjust to inspect introspection, or delete if redundant with introspection-tier coverage.

The `/qa` slice owns the e2e re-tuning.

---

## 6. Open questions

The facade and master-design carry through cleanly for most rows. The slice surfaces five narrow questions where authoring met an edge:

1. **Decision 38 status — active or legacy?** `design/arch/CLAUDE.md`'s active register lists 0010, 0011, 0027, 0030, 0031, 0035, 0040, 0041, 0042, 0043 — D38 is NOT among them. Master-design §13 cites D38 in the int-relevant Decisions table and treats it as load-bearing this sprint; `facades/int.md` invariants 15, 16, 17 cite Decision 38 as binding contract. The slice's tentative interpretation: D38 has *moved to legacy* per the active-register policy ("once a Decision's commitment lands fully into the architecture, the Decision becomes vestigial and moves to legacy/decisions/") because the facade carries its commitments; but the *source* has not yet embodied them. The slice therefore treats D38 as legacy-but-implementation-pending — citing the legacy file as authoritative and the *embodiment* as the work this sprint. **If `/arch` regards this as substantive (i.e., D38 should re-enter the active register because S66 carries pre-implementation commitments), file `design/arch/fixmes/0152-arch-d38-active-status.md` targeting `/arch`.** Otherwise no source change; the slice's Wave C work proceeds against the legacy file as authority.

2. **`SharedState` extraction sequencing — separate sprint or this sprint?** Wave C is the most invasive change in this slice — the `CompilerSession` god-struct splits into `Arc<SharedState>` + initiator-only state. Master-design §3.3's "module map" anticipates this split as part of the broader `session_v4.rs` decomposition (audit F1 + recommendation 1). FIXME 0109 sequences the *full decomposition* AFTER S65 FIXMEs. **Question**: is the SharedState struct extraction itself part of FIXME 0109's deferred work, or is it the prerequisite "shape pivot" that 0109's decomposition then continues? Slice's tentative interpretation: SharedState extraction lands in S66 (in this slice's Wave C) because every other receive-side row depends on it; the *full decomposition* (splitting `session_v4.rs` into `session/`, `session/eval.rs`, `session/repl_loop.rs`, etc.) is what 0109 defers to S67+. **If `/arch` regards SharedState extraction as itself-decomposition and therefore deferred under 0109, the slice loses its centre of gravity** — every other receive-side row (D41, D42, ResolutionGap, observability) needs a smaller staging shape. File `0153-arch-sharedstate-vs-decomposition-sequencing.md` if substantive.

3. **0109 `process_form` extraction timing.** FIXME 0109 Wave C extracts `process_form` from `worker.rs` to `src/process_form.rs` as a sequenced wave. This slice's row 3 + row 36 land `process_form` as a free function in S66 per `facades/int.md`'s explicit "actual Rust may keep it as a CompilerSession method that immediately delegates to a free function" footnote. **Question**: is the free-function landing in this slice (S66) "a small placement choice that lands the contract" or "a partial execution of 0109 Wave C that should be deferred"? Slice's tentative interpretation: the free-function landing IS contract-load-bearing (typed pattern-match against typed gaps requires a clean call site); the file-location choice (whether `worker.rs:process_form` or `src/process_form.rs`) is the deferred decision. The slice authors `process_form` as a free function in `worker.rs` (or `worker::process_form`) for S66; 0109 Wave C extracts the file in S67+. **Confirm with `/arch` if substantive.**

4. **`OwnedPlatformFnDescriptor` non-exhaustive (R9 / 0107)** — the substance-scoping says it's already landed in commit `25fa73a`; verify no int-side pattern-match drift. The slice's row 43 is a verify-row; if drift surfaces, the row converts to a real edit (mechanical: add a wildcard arm). **Not a substantive open question; a verify-class item.**

5. **`TracedFnInfo` duplicate type ambiguity (R6)** — `facades/int.md` §"Tracing helpers" says: "If a duplicate type previously existed on backend's side, it deletes; `TracedFnInfo` lives in int". Master-design §3 doesn't mention a duplicate type. **Question**: is there a duplicate type in `cranelisp-backend` today that needs deleting alongside the relocation? If yes, the slice's row 22 must coordinate with backend slice (file a FIXME); if no, the row is a clean-relocate. Probably no — but wants verification during implementation. **Verify-class; if substantive, file `0154-arch-tracedfninfo-duplicate.md` (targets backend slice).**

If `/arch` regards any of these as substantive (substantive = changes the slice's row count or wave sequencing), the slice files as sequential FIXMEs (`0152`–`0154`). **Tentative count: 1–3 FIXMEs may be filed during S66 implementation depending on `/arch`'s read of D38 status (Q1) and SharedState extraction sequencing (Q2).** Per Principle 4 (uninvented answers), the slice does not unilaterally resolve — it surfaces.

---

## 7. Cross-references

- `design/arch/facades/int.md` — public-API contract (this slice's target; W3-revised post-Decision-38/41/43 shape; ~810 lines)
- `design/int/int.md` — master design (this slice's contract layer; §1 BC recap, §3 current-state, §4 SharedState architecture, §5 Code lifecycle, §6 pipeline orchestration, §7 cache+linker, §8 REPL flow, §9 error formatting, §10 concurrency, §11 observability, §13 Decision register, §14 as-designed-vs-as-built drift map, §16 open /dev work)
- `design/arch/facades/types.md` — Decision 39 (`ErrorLocation`); FQTypeName threading per FIXME 0151; `ResolutionGap` Phase 1 home
- `crates/cranelisp-frontend/src/lib.rs` //! preamble + per-item rustdoc on `expand` + `ExpansionError` — `expand` post-FIXME-0098 home + `ExpansionError` enum (post-S70 B3-C facade retirement; `facades/frontend.md` retired)
- `design/arch/facades/typecheck.md` — `check_form` free-function + `&SymbolTable<C, L>` mutability-pivot + `CheckError` post-relocation home
- `design/arch/facades/backend.md` — Decision 41 per-symbol JIT mutref pattern; `Code` location; `CompilationError` post-relocation home; `GotObserver` (FIXME 0099 Phase 1); display departure (FIXME 0108)
- `crates/cranelisp-platform/src/lib.rs` //! + per-item rustdoc + `bounded-contexts.md` §5 — Decision 42 PlatformError + ErrorLocation; OwnedPlatformFnDescriptor `#[non_exhaustive]` (post-S71 W4 facade retirement; `facades/platform.md` retired)
- `design/arch/facades/primitives.md` — D43-new crate; user-callable extern functions int seeds into the `primitives` synthetic module
- `design/arch/facades/intrinsics.md` — D43-new crate; backend-emitted intrinsics + IoObserver registration API per Decision 40 + 43
- `design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md` — D40 commitment text
- `design/arch/decisions/0041-compile-to-module-per-symbol-jit-direct-writes.md` — D41 commitment text (amends D31, D35)
- `design/arch/decisions/0042-platform-error-adopts-error-location.md` — D42 commitment text
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` — D43 commitment text (retracts D14, reframes D15)
- `design/arch/legacy/decisions/0038-*.md` — D38 SharedState formal subset (legacy but operative this sprint as receive-side embodiment per OQ 1)
- `design/arch/legacy/decisions/0039-*.md` — D39 per-defn source on Introspection (legacy but operative)
- `design/arch/fixmes/0098-*` — multi-crate ResolutionGap/CheckError/ExpansionError migration; this slice executes Phase 4
- `design/arch/fixmes/0099-*` — GotObserver implementation; this slice executes Phase 2
- `design/arch/fixmes/0100-*` — single-consumer-type relocations; this slice's import-rewrite work
- `design/arch/fixmes/0103-*` — trace.rs + io_trace.rs runtime → int relocation; this slice executes Phase 2
- `design/arch/fixmes/0104-*` — int's `load_platform_dll` PlatformError construction; this slice executes Phase 3
- `design/arch/fixmes/0107-*` — OwnedPlatformFnDescriptor `#[non_exhaustive]`; R9 already landed
- `design/arch/fixmes/0108-*` — display.rs backend → int relocation; this slice receives
- `design/arch/fixmes/0109-*` — int decomposition (session_v4.rs + worker.rs split; lib.rs narrow; session.rs delete); **DEFERRED to S67+ per its own sequencing note**
- `design/arch/fixmes/0150-*` — D43 implementation (runtime split into primitives + intrinsics); this slice's Wave A + Wave B receive
- `design/arch/fixmes/0151-*` — FQTypeName implementation (filed S65 W3); this slice's row 32 verify confirms consumption
- `audits/src-20260423.md` — current-state audit; F1 (session_v4.rs god-file), F2 (worker.rs god-file), F3 (dep-registration split), F4 (worker orchestration split), F5 (lib.rs not thin facade), F6 (session.rs legacy), F7 (long historical narratives in hot paths). F1+F2+F5+F6 are FIXME 0109 — DEFERRED. F3+F4 collapse under this slice's Wave C+D landings.
- `sprints/SPRINT.md` Wave Phase 4 W4a — slice-authoring wave
- `design/arch/sprint-65-reshape-phase-2-review.md §3` — slice template authority
- `design/frontend/implementation-slice-s66.md` — companion slice (frontend); cross-references with this slice on ExpansionError producer + `MacroResolver` deletion
- `design/typecheck/implementation-slice-s66.md` — companion slice (typecheck); cross-references with this slice on CheckError + `process_form` orchestrator-side mirror entries
- `crates/cranelisp-runtime/src/{trace,io_trace,io}.rs` — physically migrating files (Wave A receive-side)
- `crates/cranelisp-backend/src/display.rs` — physically migrating file (Wave A receive-side)
- `src/{session_v4,worker,scheduler,session,code,expander,save,platform,exe,cache_writer,observability}.rs` — current sources under reshape; large-but-mechanical adaptation
- `crates/cranelisp-exe-bundle/` — receives `generate_startup_object` per Phase 2 reach-around R5 (Wave A)
