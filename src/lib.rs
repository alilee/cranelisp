// cranelisp library: pipeline, REPL, and shared functionality.
//
// Sprint 67 hack-back (`/dev (int)`): only the modules that `src/main.rs`
// imports via `use cranelisp::...` need to be `pub mod`. Everything else is
// narrowed to `pub(crate) mod` — they are internal to the library crate, used
// by sibling modules but not part of the binary-facing public surface. See
// `design/arch/facades/int.md` §"Public surface".
//
// External consumers (binary + legacy tests via `cranelisp::...`):
// - `observability`   — `src/main.rs:12` (panic-hook install, flush)
// - `session_v4`      — `src/main.rs:13` (`CommandResult`, `CompilerSession`, `SessionSettings`)
// - `got_trace`       — `src/main.rs:14`
// - `io_trace`        — `src/main.rs:14`
// - `style`           — `src/main.rs:66` (`init_color`)
pub mod observability;
pub mod session_v4;
pub mod got_trace;
pub mod io_trace;
pub mod style;

// Facade-cited but not yet reachable from external consumers — keep `pub`
// so the dead_code lint accepts these as part of the published surface per
// `design/arch/facades/int.md`. Once `process_cluster` / `insert_cluster`
// activate on the hot path (FIXME 0176) and `bind_chain_analysis` re-wires
// into the worker, these become live without further narrowing churn.
pub mod cluster;

// WorkerPool — facade entry point for the worker thread pool owned by
// `CompilerSession`. Re-exported per `design/arch/facades/int.md` L25 + L201.
// Sprint 67 Cluster B sub-fire 2a.
pub mod worker_pool;

// ObjectCache — facade entry point for the on-disk `.o` + sidecar cache
// owned by `SharedState`. Re-exported per `design/arch/facades/int.md`
// L519-549. Sprint 67 Cluster B sub-fire 3.
pub mod cache;

// Internal — accessed only via `crate::*` paths inside the library.
pub(crate) mod bind_chain_analysis;
// bootstrap — synthetic-module mount (FIXME 0242). int reconstructs the
// special-forms / intrinsic-type / macros / Option / IO / Trace / TestResult
// seeding that the deleted `cranelisp_typecheck::register_builtins` body
// performed, building entries directly via `ModuleEntry::def` + plain struct
// literals. See `design/arch/fixmes/0242-*`.
pub(crate) mod bootstrap;
// imports — int-side import/export installer (int plan §1.4). Writes per-symbol
// `ModuleEntry::Import` bindings + module-path aliases; replaces typecheck's
// struck `register_imports`/`register_exports`. See `design/arch/fixmes/0242-*`
// §S76-addendum (2) + bounded-contexts.md §2 invariants 2+8.
pub(crate) mod imports;
pub(crate) mod cache_writer;
pub(crate) mod code;
pub(crate) mod display;
pub(crate) mod exe;
pub(crate) mod link;
pub(crate) mod expander;
pub(crate) mod marshal;
// session_setup — session-construction helpers independent of `CompilerSession`
// (CacheState, ProjectConfig, lib/platform-dir assembly, prelude resolution,
// exit-code determination, bind-chain analysis application). Formerly named
// `session.rs`; the v3 `CompilerSession`/`Session` god-type it once held was
// deleted in a prior sprint (FIXME 0109 Wave A — verified no v3 type remains;
// renamed to shed the misleading "v3 lingering" connotation).
pub(crate) mod session_setup;
pub(crate) mod pipeline;
pub(crate) mod platform;
pub(crate) mod pretty;
// process_form — the cluster / per-form gap-orchestration family extracted
// from worker.rs (FIXME 0109 Wave C). `process_cluster_once` +
// `process_regular_form` + their family-private helpers. The permanent home
// named in `design/int/int.md` §3.3 Wave-D target map.
pub(crate) mod process_form;
// eval — REPL eval form-chain extracted from session_v4.rs (FIXME 0109 Wave D).
// `eval` + `process_form_cluster`/`process_single_form` (eval-thread dep-retry
// loop) + `codegen_and_execute` + `check_bare_symbol_introspection` +
// `register_dep_for_eval`. The §3.3 Wave-D target home.
pub(crate) mod eval;
// repl — slash-command dispatch, prompt/banner formatting, line-editor entry
// points, introspection-display helpers; extracted from session_v4.rs
// (FIXME 0109 Wave D). The §3.3 Wave-D target home.
pub(crate) mod repl;
// repl/ module deleted — v4 REPL is driven by CompilerSession in main.rs + session_v4.rs.
// FileWatcher extracted to watch.rs; remaining features (save, trace, run-tests) are future work.
pub(crate) mod save;
pub(crate) mod sched_dump;
pub(crate) mod scheduler;
// syntax — the `/syntax` topic-indexed core-language cheat-sheet (design/int/
// agent.md §22, repl/spec.md §17.17). UNCONDITIONAL (default build) — the
// command is not feature-gated; only the agent *pull* of it rides the `agent`
// feature. A pure delimiter parser over the embedded `syntax/cheatsheet.txt`.
pub(crate) mod syntax;
pub(crate) mod thread_util;
// trace — DELETED S76 (FIXME 0256, trace ruling 2026-06-04). The 12
// `cranelisp_trace_*` bodies + the descriptor-driven formatter now live in
// `cranelisp_intrinsics::trace` and are published via `intrinsics_table()`;
// `Jit::new(symbol_tables)` registers them. int hosts no `(trace ...)` runtime.
pub(crate) mod watch;
pub(crate) mod worker;

// agent — embedded-agent module seam (Sprint 88 Phase 5, Wave 2 foundations).
// Entirely `#[cfg(feature = "agent")]`: feature-off ⇒ this module does not
// exist and the binary is byte-identical to today (design/int/agent.md §1,
// §3.1; repl/spec.md §17.1). Holds the §5.3 dispatch classifier
// (`classify_for_agent`) + the Wave-2 `agent_turn` placeholder. Wave 3 fills
// the loop (rig `CompletionModel` + harvester + primer + pull) and adds the
// `rig-core` optional dep under this feature — NOT this wave (agent.md §6).
#[cfg(feature = "agent")]
pub mod agent;
