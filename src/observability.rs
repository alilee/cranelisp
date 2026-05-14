//! Scheduler / worker event log — Slice 0 observability infrastructure.
//!
//! See `design/int/observability.md` for the full design and the companion
//! `design/backend/io-trampoline-trace.md` for the IO-trampoline sibling.
//!
//! ## Overview
//!
//! Thread-local ring-buffer trace of scheduler and worker pool-state
//! transitions (`register_dep` publish, `register_module` register,
//! `is_typechecked` hit/miss, pool flips, `clear_module_state`,
//! `recompile_module`). Activated by the env var
//! `CRANELISP_SCHEDULER_TRACE`:
//!
//! - unset  → `None`; hot path is a single `OnceLock` load + null check,
//!   no recording, no formatting, no allocation.
//! - `"1"` or `"*"` → `Some(TraceFilter::All)`; every instrumented site
//!   appends to the caller's thread-local ring buffer.
//! - `"foo"` or `"foo,bar"` → `Some(TraceFilter::Selective(...))`; only
//!   events whose module-path payload matches one of the listed names
//!   are recorded.
//! - anything else (e.g. just whitespace after `=`) → `None`. Malformed
//!   values never panic.
//!
//! Timestamps come from the shared `cranelisp_intrinsics::io_trace::trace_instant_anchor()`
//! anchor so this log and the IO trampoline log can be merge-sorted on a
//! single timebase (per /arch Phase 3a cross-doc consistency requirement).
//!
//! ## Non-goals
//!
//! - No `Serialize` / `Deserialize` — events are in-process only. MUST
//!   NOT appear in any `cranelisp-shared` / `cranelisp-types` boundary
//!   type, `.meta.json`, `CacheEntry`, or on-disk artefact.
//! - No `cranelisp_alloc` usage inside event storage — host allocator
//!   only, to avoid recursion through RC-traced allocation paths.
//!
//! ## Parse-once env-var pattern
//!
//! `CRANELISP_SCHEDULER_TRACE` is parsed **once** into a
//! `OnceLock<Option<TraceFilter>>` on the first `record_event` (or
//! direct `filter()` / `dump_*`) call. Mirrors the convention in
//! `tests/CLAUDE.md §"Diagnostic Logging"`. Per-event string parsing
//! is forbidden.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::OnceLock;
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread::ThreadId;

// ---------------------------------------------------------------------------
// Env-var name constant (test-helper + documentation aid)
// ---------------------------------------------------------------------------

/// Name of the env var that gates this trace. Exposed so tests can parse
/// the variable indirectly through `parse_filter_from_env_value` without
/// touching the process-global `OnceLock`.
pub const fn scheduler_trace_env_var() -> &'static str {
    "CRANELISP_SCHEDULER_TRACE"
}

// ---------------------------------------------------------------------------
// Filter (env-var parse once)
// ---------------------------------------------------------------------------

/// Filter parsed from `CRANELISP_SCHEDULER_TRACE`.
///
/// Constructed lazily; the outer `Option` on the static (`None`) signals
/// tracing is disabled entirely. `All` records every event; `Selective`
/// records only events whose module-path payload matches one of the
/// entries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TraceFilter {
    /// Record every tag regardless of payload.
    All,
    /// Record only events whose module-path payload matches one of the
    /// listed module names. Names are compared exactly (string equality
    /// on the `ModuleFullPath`'s `&str` form).
    Selective(Vec<String>),
}

static SCHEDULER_TRACE_FILTER: OnceLock<Option<TraceFilter>> = OnceLock::new();

/// Parse the `CRANELISP_SCHEDULER_TRACE` env var once. Unset, empty, or
/// malformed values yield `None`.
fn parse_filter_from_env() -> Option<TraceFilter> {
    match std::env::var(scheduler_trace_env_var()) {
        Ok(v) => parse_filter_from_env_value(&v),
        Err(_) => None,
    }
}

/// Pure parser — separated for testability. Visible to tests so they can
/// exercise every branch without touching the OnceLock.
pub fn parse_filter_from_env_value(raw: &str) -> Option<TraceFilter> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return None;
    }
    if trimmed == "1" || trimmed == "*" {
        return Some(TraceFilter::All);
    }
    // Comma-separated module-name list. Empty entries after split are
    // dropped; an all-empty list (e.g. a lone ",") yields None.
    let names: Vec<String> = trimmed
        .split(',')
        .map(|s| s.trim())
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect();
    if names.is_empty() {
        None
    } else {
        Some(TraceFilter::Selective(names))
    }
}

/// Return the active filter, initialising the `OnceLock` on first call.
///
/// Init site decision: the filter `OnceLock` is populated by the first
/// `record_event` call (or by any direct access such as `dump_*` /
/// `filter()`). This avoids a dedicated startup hook in `main.rs` — the
/// scheduler / worker instrumentation is always the first hot code to
/// emit, so the lazy init coincides with the first instrumented site.
/// If a future startup hook is added it can call `filter()` explicitly
/// to prime the parse before the first event.
fn filter() -> Option<&'static TraceFilter> {
    SCHEDULER_TRACE_FILTER
        .get_or_init(parse_filter_from_env)
        .as_ref()
}

// ---------------------------------------------------------------------------
// Event taxonomy
// ---------------------------------------------------------------------------

/// Scheduler / worker event tag. Taxonomy grounded in `src/scheduler.rs`,
/// `src/worker.rs`, and `src/session_v4.rs` as of Sprint 61 Wave 1.
///
/// `repr(u8)` keeps the tag a single byte inside the event struct.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum SchedulerTraceTag {
    /// `register_dep` published dep_sexps to `shared.module_sexps`
    /// (`src/worker.rs` + form-handler callers, plus
    /// `src/session_v4.rs::register_dep_for_eval`). This is the
    /// publish-before-register site that Sprint 58 W6 Defect 1 hardened.
    RegisterDepPublish,
    /// `scheduler.register_module` — module first enters the scheduler
    /// from a callsite (worker form handler OR REPL session entry).
    RegisterModuleRegister,
    /// `scheduler.register_module_cached` — cache-hit fast path
    /// (`src/scheduler.rs:329`) registered a module at TypecheckDone.
    RegisterModuleCached,
    /// `scheduler.re_register_module` — file-watcher or REPL reload
    /// path (`src/scheduler.rs:368`).
    ReRegisterModule,
    /// `scheduler.reset_module` — Failed → removed (single module).
    ResetModule,
    /// `scheduler.reset_all_failed_modules` — REPL cascade reset.
    ResetAllFailed,
    /// `scheduler.is_typechecked` returned `true` (fast-path hit — pool
    /// observed as TypecheckDone or Complete).
    IsTypecheckedHit,
    /// `scheduler.is_typechecked` returned `false` (fast-path miss —
    /// pool observed as Unregistered / Next / Working / Blocked /
    /// Failed, or None-as-typechecked fallthrough for absent modules).
    /// Note: the current implementation treats `None` as `true`; this
    /// tag fires only when pool is present and non-done.
    IsTypecheckedMiss,
    /// A module entered the `TypecheckWorking` pool (worker claimed it
    /// from `typecheck_first` or `typecheck_next`).
    ModuleStateTypechecking,
    /// A module advanced to `TypecheckDone` via `notify_typecheck_done`.
    ModuleStateTypechecked,
    /// A module transitioned to the `Failed` pool.
    ModuleStateFailed,
    /// Typecheck worker transitioned a module to `TypecheckBlocked`
    /// (waiting on a dep symbol).
    ModuleStateBlocked,
    /// Worker transitioned a module from Blocked back to First/Next.
    ModuleStateUnblocked,
    /// REPL / file-watcher-driven module recompile (`session_v4::reload_module`).
    RecompileModule,
    /// REPL-side state wipe before `reload_module` proceeds. Named for
    /// parity with the sketch / v3 pipeline's `clear_module_state`
    /// method; in v4 this is the `reload_module` prologue that clears
    /// `typecheck_products`, `suspend_states`, and the module's `code`
    /// fields.
    ClearModuleState,
    /// `session_v4::republish_module_sexps_from_symbol_table` — the
    /// caller-side H5 REPL-persistence republish fires. Sprint 61 Wave 3
    /// step 3e instrumentation (H4 race-closure fix Change B): exposes
    /// the ordering of the REPL-eval thread's user-sexps republish
    /// relative to the persistent worker's subsequent
    /// `register_imports` lookup on the dep. Emitted from
    /// `src/session_v4.rs:1192-1209`.
    RepublishFromSymbolTable,
    /// `handle_import` is consulting `symbol_tables[dep]` via the
    /// `register_imports` fast path. Sprint 61 Wave 3 step 3e
    /// instrumentation (H4 race-closure fix Change B): exposes the
    /// reader-side of the publish-vs-flag race so the post-fix dump can
    /// prove the `RepublishFromSymbolTable` event precedes the
    /// `RegisterImportsLookup` event on the eval thread. Emitted from
    /// `src/worker.rs::handle_import` at the fast-path check.
    RegisterImportsLookup,
    /// `TypeCheckEnv::ensure_module_exists` either created a fresh
    /// `SymbolTable` for the module or observed one already present.
    /// The observed branch is reported via the `state` field on the
    /// `Module` payload:
    ///
    /// - `state = Some(0)` → `Created` (this call built and inserted
    ///   the table).
    /// - `state = Some(1)` → `AlreadyPresent` (another concurrent
    ///   caller had already inserted).
    ///
    /// Sprint 61 Wave 3 step 3e'' instrumentation (H6 race-closure fix
    /// per `design/int/heisenbug-race-closure.md §8.3.4` + /arch mini
    /// review §3d''). The emission crosses the crate boundary via the
    /// `cranelisp_typecheck::trace::install_symbol_table_ensure_hook`
    /// install-a-function-pointer pattern — typecheck does not depend
    /// on this crate. Cost when the sink is uninstalled (unit tests):
    /// one relaxed OnceLock load + null check, no formatting.
    SymbolTableEnsure,
}

/// Event payload. Inline enum — no heap allocation per event, no string
/// indirection. `String` is the owned module path; `ModuleFullPath` at
/// the call site is cloned into an owned `String` by `record_event`.
/// (This is an integration-layer type; the boundary prohibition is on
/// `cranelisp-shared` / `cranelisp-types` — owned String here is fine.)
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SchedulerTracePayload {
    /// Payload for every module-scoped event: the module path. Some
    /// tags (`IsTypecheckedHit` / `Miss`) also carry the observed pool
    /// discriminant as `state` for post-hoc analysis.
    Module { module: String, state: Option<u8> },
    /// Payload for bulk events that do not name a specific module
    /// (e.g., `ResetAllFailed`).
    Bulk { count: usize },
}

impl SchedulerTracePayload {
    /// Borrow the module path if this payload carries one. Used by the
    /// `Selective` filter to decide whether an event matches.
    fn module_path(&self) -> Option<&str> {
        match self {
            SchedulerTracePayload::Module { module, .. } => Some(module.as_str()),
            SchedulerTracePayload::Bulk { .. } => None,
        }
    }
}

/// One scheduler / worker event. `Send + Sync` (enforced by the
/// `assert_send_sync` const below) so buffers can be merged across
/// threads at dump time.
#[derive(Debug, Clone)]
pub struct SchedulerTraceEvent {
    /// Monotonic nanoseconds elapsed since `trace_instant_anchor()`.
    pub timestamp: u64,
    /// Standard-library `ThreadId` of the emitting thread.
    pub thread_id: ThreadId,
    /// Stable, monotonic per-thread ordering key (merge-sort tie-breaker).
    pub thread_ord_id: u64,
    /// Event tag.
    pub tag: SchedulerTraceTag,
    /// Tag-dependent payload.
    pub payload: SchedulerTracePayload,
}

// Compile-time assertion: events cross thread boundaries at dump time.
const _: fn() = || {
    fn assert_send_sync<T: Send + Sync>() {}
    assert_send_sync::<SchedulerTraceEvent>();
    assert_send_sync::<SchedulerTracePayload>();
    assert_send_sync::<SchedulerTraceTag>();
};

// ---------------------------------------------------------------------------
// Thread-local ring buffer
// ---------------------------------------------------------------------------

/// Per-thread ring buffer capacity. Matches `IO_TRACE_BUFFER_CAPACITY`
/// in `cranelisp-runtime::io_trace` so the two traces are sized
/// consistently (per /arch Phase 3a cross-doc consistency note).
pub const SCHEDULER_TRACE_BUFFER_CAPACITY: usize = 65_536;

/// Process-wide thread ordinal counter. Distinct from the IO trace's
/// counter — each trace has its own monotonic sequence because they are
/// merged independently at dump time.
static NEXT_THREAD_ORD_ID: AtomicU64 = AtomicU64::new(0);

thread_local! {
    static SCHEDULER_TRACE_BUF: RefCell<VecDeque<SchedulerTraceEvent>> =
        RefCell::new(VecDeque::with_capacity(SCHEDULER_TRACE_BUFFER_CAPACITY));

    static SCHEDULER_TRACE_THREAD_ORD: RefCell<Option<u64>> = const { RefCell::new(None) };
}

/// Return this thread's ordinal id, assigning a fresh one on first call.
fn thread_ord_id() -> u64 {
    SCHEDULER_TRACE_THREAD_ORD.with(|cell| {
        let mut slot = cell.borrow_mut();
        if let Some(id) = *slot {
            id
        } else {
            let id = NEXT_THREAD_ORD_ID.fetch_add(1, Ordering::Relaxed);
            *slot = Some(id);
            id
        }
    })
}

/// Global registry of thread-local buffer snapshots taken at dump time.
static PUBLISHED_BUFFERS: OnceLock<std::sync::Mutex<Vec<Vec<SchedulerTraceEvent>>>> =
    OnceLock::new();

fn published_buffers() -> &'static std::sync::Mutex<Vec<Vec<SchedulerTraceEvent>>> {
    PUBLISHED_BUFFERS.get_or_init(|| std::sync::Mutex::new(Vec::new()))
}

// ---------------------------------------------------------------------------
// Hot-path emit
// ---------------------------------------------------------------------------

/// Record a scheduler / worker event. Call sites in `src/scheduler.rs`,
/// `src/worker.rs`, and `src/session_v4.rs` are unconditional one-liners
/// — this function checks the filter and returns early when tracing is
/// disabled.
///
/// Hot-path cost when disabled: `OnceLock::get` (amortised to a single
/// relaxed load after the first call) plus one null check. No
/// formatting, no heap allocation on the disabled path.
#[inline]
pub fn record_event(tag: SchedulerTraceTag, payload: SchedulerTracePayload) {
    let Some(f) = filter() else { return };
    // Selective filter: drop events whose module path doesn't match any
    // listed name. Bulk events (no module path) always pass.
    match f {
        TraceFilter::All => {}
        TraceFilter::Selective(names) => {
            if let Some(mp) = payload.module_path()
                && !names.iter().any(|n| n.as_str() == mp)
            {
                return;
            }
        }
    }
    let anchor = cranelisp_intrinsics::io_trace::trace_instant_anchor();
    let timestamp = anchor.elapsed().as_nanos() as u64;
    let ord = thread_ord_id();
    let event = SchedulerTraceEvent {
        timestamp,
        thread_id: std::thread::current().id(),
        thread_ord_id: ord,
        tag,
        payload,
    };
    SCHEDULER_TRACE_BUF.with(|cell| {
        let mut buf = cell.borrow_mut();
        if buf.len() == SCHEDULER_TRACE_BUFFER_CAPACITY {
            buf.pop_front();
        }
        buf.push_back(event);
    });
}

// ---------------------------------------------------------------------------
// Ergonomic helpers for common emit shapes
// ---------------------------------------------------------------------------

/// Emit a module-scoped event with no pool-state discriminant.
#[inline]
pub fn record_module_event(tag: SchedulerTraceTag, module: &(impl AsRef<str> + ?Sized)) {
    record_event(
        tag,
        SchedulerTracePayload::Module {
            module: module.as_ref().to_string(),
            state: None,
        },
    );
}

/// Emit a module-scoped event that carries a pool-state discriminant
/// (used by the `is_typechecked` hit/miss tags so the dumper can name
/// the observed `ModulePool`).
#[inline]
pub fn record_module_event_with_state(
    tag: SchedulerTraceTag,
    module: &(impl AsRef<str> + ?Sized),
    state: u8,
) {
    record_event(
        tag,
        SchedulerTracePayload::Module {
            module: module.as_ref().to_string(),
            state: Some(state),
        },
    );
}

/// Emit a bulk event (not tied to a single module).
#[inline]
pub fn record_bulk_event(tag: SchedulerTraceTag, count: usize) {
    record_event(tag, SchedulerTracePayload::Bulk { count });
}

// ---------------------------------------------------------------------------
// SymbolTableEnsure bridge (Sprint 61 Wave 3 step 3e'' — H6 fix)
// ---------------------------------------------------------------------------
//
// The `cranelisp-typecheck` crate does not depend on this binary crate, so
// it cannot call `record_module_event_with_state` directly. Instead, this
// module provides a forwarding function that the binary installs into
// `cranelisp_typecheck::trace::install_symbol_table_ensure_hook` at
// startup. Typecheck-crate call sites emit through the installed pointer;
// the pointer resolves to `record_symbol_table_ensure_forward` below.
//
// See `design/int/heisenbug-race-closure.md §3d''` for the /arch
// mini-review approval of this cross-crate wiring.

/// Sink function that translates a typecheck-crate
/// `SymbolTableEnsureOutcome` into a scheduler-trace
/// `SymbolTableEnsure` event. Invoked via the function pointer
/// installed by [`install_symbol_table_ensure_hook_to_scheduler_trace`].
///
/// The `outcome` is encoded into the `Module` payload's `state` field
/// (0 = Created, 1 = AlreadyPresent) so the `format_event_line`
/// machinery can render it without a new payload variant.
pub fn record_symbol_table_ensure_forward(
    module: &cranelisp_types::ModuleFullPath,
    outcome: cranelisp_typecheck::SymbolTableEnsureOutcome,
) {
    record_module_event_with_state(
        SchedulerTraceTag::SymbolTableEnsure,
        module.as_ref(),
        outcome.as_u8(),
    );
}

/// Install the forwarding function pointer into the typecheck crate's
/// trace slot. Call once from `main()` before any typecheck work
/// begins.
///
/// Idempotent — `cranelisp_typecheck::install_symbol_table_ensure_hook`
/// is backed by a `OnceLock`; the first install wins, subsequent calls
/// are no-ops.
pub fn install_symbol_table_ensure_hook_to_scheduler_trace() {
    cranelisp_typecheck::install_symbol_table_ensure_hook(
        record_symbol_table_ensure_forward,
    );
}

// ---------------------------------------------------------------------------
// Dump
// ---------------------------------------------------------------------------

/// Drain this thread's ring buffer and return it, sorted by
/// `(timestamp, thread_ord_id)`. The thread-local buffer is left empty.
pub fn dump_thread_buffer() -> Vec<SchedulerTraceEvent> {
    let mut out: Vec<SchedulerTraceEvent> = SCHEDULER_TRACE_BUF
        .with(|cell| cell.borrow_mut().drain(..).collect());
    out.sort_by_key(|e| (e.timestamp, e.thread_ord_id));
    out
}

/// Publish this thread's buffer into the process-wide registry. Intended
/// for test-failure dump hooks: each worker thread drains its buffer
/// into the registry, the main thread then merges everything via
/// `dump_all_buffers`.
pub fn publish_thread_buffer() {
    let drained = dump_thread_buffer();
    if drained.is_empty() {
        return;
    }
    if let Ok(mut guard) = published_buffers().lock() {
        guard.push(drained);
    }
}

/// Merge every published buffer plus the calling thread's live buffer
/// into a single sorted vector. Sort key is `(timestamp, thread_ord_id)`
/// so ties break deterministically.
pub fn dump_all_buffers() -> Vec<SchedulerTraceEvent> {
    let mut all: Vec<SchedulerTraceEvent> = Vec::new();
    if let Ok(guard) = published_buffers().lock() {
        for b in guard.iter() {
            all.extend_from_slice(b);
        }
    }
    let local = dump_thread_buffer();
    all.extend(local);
    all.sort_by_key(|e| (e.timestamp, e.thread_ord_id));
    all
}

/// Format a single event as a stderr line. Static strings for tag names
/// are resolved at dump time only; the hot path never formats.
pub fn format_event_line(e: &SchedulerTraceEvent) -> String {
    let tag_name = match e.tag {
        SchedulerTraceTag::RegisterDepPublish => "RegisterDepPublish",
        SchedulerTraceTag::RegisterModuleRegister => "RegisterModuleRegister",
        SchedulerTraceTag::RegisterModuleCached => "RegisterModuleCached",
        SchedulerTraceTag::ReRegisterModule => "ReRegisterModule",
        SchedulerTraceTag::ResetModule => "ResetModule",
        SchedulerTraceTag::ResetAllFailed => "ResetAllFailed",
        SchedulerTraceTag::IsTypecheckedHit => "IsTypecheckedHit",
        SchedulerTraceTag::IsTypecheckedMiss => "IsTypecheckedMiss",
        SchedulerTraceTag::ModuleStateTypechecking => "ModuleStateTypechecking",
        SchedulerTraceTag::ModuleStateTypechecked => "ModuleStateTypechecked",
        SchedulerTraceTag::ModuleStateFailed => "ModuleStateFailed",
        SchedulerTraceTag::ModuleStateBlocked => "ModuleStateBlocked",
        SchedulerTraceTag::ModuleStateUnblocked => "ModuleStateUnblocked",
        SchedulerTraceTag::RecompileModule => "RecompileModule",
        SchedulerTraceTag::ClearModuleState => "ClearModuleState",
        SchedulerTraceTag::RepublishFromSymbolTable => "RepublishFromSymbolTable",
        SchedulerTraceTag::RegisterImportsLookup => "RegisterImportsLookup",
        SchedulerTraceTag::SymbolTableEnsure => "SymbolTableEnsure",
    };
    // `SymbolTableEnsure` overloads the `state` field on the Module
    // payload to carry the `Created | AlreadyPresent` discriminator
    // (0 = Created, 1 = AlreadyPresent). For readability, format the
    // symbolic name rather than the numeric code on this tag. All
    // other tags with a `state` value continue to render it as
    // `pool=<N>`.
    let is_ensure = matches!(e.tag, SchedulerTraceTag::SymbolTableEnsure);
    let payload = match &e.payload {
        SchedulerTracePayload::Module { module, state: Some(s) } if is_ensure => {
            let outcome = match s {
                0 => "Created",
                1 => "AlreadyPresent",
                _ => "Unknown",
            };
            format!("module={module} outcome={outcome}")
        }
        SchedulerTracePayload::Module { module, state: Some(s) } => {
            format!("module={module} pool={s}")
        }
        SchedulerTracePayload::Module { module, state: None } => {
            format!("module={module}")
        }
        SchedulerTracePayload::Bulk { count } => format!("count={count}"),
    };
    format!(
        "[SCH] ts={ts} thr={thr:?}/{ord} {tag}\t{payload}",
        ts = e.timestamp,
        thr = e.thread_id,
        ord = e.thread_ord_id,
        tag = tag_name,
        payload = payload,
    )
}

/// Write every published + live-thread event to stderr, one per line,
/// merge-sorted by `(timestamp, thread_ord_id)`. Prefixes the output
/// with `=== CRANELISP_SCHEDULER_TRACE DUMP ===` so the section is
/// unambiguous in interleaved test output. No-op when the filter is
/// disabled.
pub fn flush_to_stderr() {
    if filter().is_none() {
        return;
    }
    let events = dump_all_buffers();
    if events.is_empty() {
        return;
    }
    let stderr = std::io::stderr();
    let mut guard = stderr.lock();
    let _ = std::io::Write::write_all(
        &mut guard,
        b"=== CRANELISP_SCHEDULER_TRACE DUMP ===\n",
    );
    for e in &events {
        let _ = std::io::Write::write_all(&mut guard, format_event_line(e).as_bytes());
        let _ = std::io::Write::write_all(&mut guard, b"\n");
    }
}

// ---------------------------------------------------------------------------
// Process-exit & panic wiring (Sprint 61 Wave 1 follow-on)
// ---------------------------------------------------------------------------
//
// `flush_to_stderr()` alone does nothing unless someone calls it. This
// section provides the two primitives `main.rs` consumes to wire flush
// to process-teardown paths:
//
//   * `SchedulerTraceFlushGuard` — RAII drop-on-scope-exit. Binary
//     `main()` holds one; its `Drop` calls `flush_to_stderr()` on
//     normal return.
//   * `install_panic_hook()` — chains `flush_to_stderr()` in front of
//     the previously-registered panic hook (e.g. the default unwinder)
//     so a panic still prints the trace before the stack unwinds and
//     the thread-local ring buffers are dropped.
//
// Mirror of the /backend-side pattern in
// `crates/cranelisp-runtime/src/io_trace.rs` — see
// `design/backend/io-trampoline-trace.md §6.1` for the rationale.
//
// Scenarios covered:
//   (b) Normal return from `main()` — `SchedulerTraceFlushGuard::drop`
//       runs.
//   (c) Panic reaching the hook — chained flush runs before unwind.
//
// Scenarios NOT covered:
//   * `std::process::exit(code)` — Rust `Drop` does not run; the
//     scheduler trace would not be flushed from these call sites.
//     `src/main.rs` uses `process::exit` at both the normal Run-mode
//     exit and in argv-parse error paths; the Run-mode call is
//     deliberately left in place (spec §12.6 requires the exit code
//     escape). Argv-parse errors happen before any scheduler event
//     could be emitted.
//   * SIGKILL / SIGABRT before the hook runs — kernel-terminated; no
//     user-space flush is possible.
//   * `std::process::abort()` — no hook runs.

/// RAII guard whose `Drop` calls [`flush_to_stderr`]. Intended to be
/// held by `main()` in the binary crate so the trace is drained before
/// the thread-local ring buffers are dropped at normal return.
///
/// Zero-cost when `CRANELISP_SCHEDULER_TRACE` is unset —
/// `flush_to_stderr` short-circuits on an empty filter.
///
/// **Does not cover** `std::process::exit()` — Drop does not run in
/// that path.
///
/// Construction is infallible and carries no state; the unit field
/// exists only to make the type non-constructible from outside the
/// module except via [`SchedulerTraceFlushGuard::new`].
pub struct SchedulerTraceFlushGuard(());

impl SchedulerTraceFlushGuard {
    /// Construct a new guard. Holding this value alive defers a
    /// `flush_to_stderr` call to its `Drop` site. Typically invoked
    /// once at the top of `main()`.
    pub fn new() -> Self {
        Self(())
    }
}

impl Default for SchedulerTraceFlushGuard {
    fn default() -> Self {
        Self::new()
    }
}

impl Drop for SchedulerTraceFlushGuard {
    fn drop(&mut self) {
        flush_to_stderr();
    }
}

/// Tracks whether [`install_panic_hook`] has already installed our
/// chained hook. Idempotent by design — a second call is a no-op so
/// downstream callers (tests, defensive main entry) can invoke it
/// without fear of stacking duplicate flushes.
static PANIC_HOOK_INSTALLED: std::sync::atomic::AtomicBool =
    std::sync::atomic::AtomicBool::new(false);

/// Install a `std::panic::set_hook` that flushes the scheduler trace
/// to stderr before delegating to the previously-registered hook
/// (typically the default unwinder that prints the panic payload +
/// backtrace).
///
/// **Idempotent.** Safe to call multiple times from the same process —
/// only the first call installs; subsequent calls are no-ops.
///
/// The chain order is deliberate: **flush first, then delegate.** The
/// default unwinder terminates the thread; thread-local ring buffers
/// are dropped during that unwind, so we must drain them BEFORE handing
/// control downstream.
pub fn install_panic_hook() {
    use std::sync::atomic::Ordering;
    if PANIC_HOOK_INSTALLED
        .compare_exchange(false, true, Ordering::AcqRel, Ordering::Acquire)
        .is_err()
    {
        return;
    }
    let previous = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        // Best-effort flush. Never panic from inside a panic hook —
        // `flush_to_stderr` itself is panic-free (stderr writes use
        // `let _ =`), but guard any future additions with catch_unwind.
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(flush_to_stderr));
        previous(info);
    }));
}

/// Test-only reset hook for the idempotent-install guard. Allows a
/// single test to reinstall the hook to observe the install path
/// twice. Not part of the stable API.
//
// FIXME(/int) — Sprint 61 Wave 1 /review I-1 (first-time deferral).
// This function mutates process-global state (`PANIC_HOOK_INSTALLED` +
// `std::panic::set_hook`) without a serialisation lock. Safe under
// `cargo nextest run` (subprocess-per-test) but fragile under
// `cargo test` where tests share a process. Recommended fix: add a
// `static TEST_GUARD: Mutex<()> = Mutex::new(())` and take the lock
// at the top of every test that calls this + `install_panic_hook`.
// See `design/review/sprint-61-wave-1-slice-0.md` §Importants I-1.
// Deferred once — ship by Wave 5 or next sprint, else escalate.
#[cfg(test)]
fn reset_panic_hook_installed_for_tests() {
    PANIC_HOOK_INSTALLED.store(false, std::sync::atomic::Ordering::Release);
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    // --- Env-var parse coverage -------------------------------------------

    #[test]
    fn parse_filter_one_is_all() {
        assert_eq!(parse_filter_from_env_value("1"), Some(TraceFilter::All));
    }

    #[test]
    fn parse_filter_star_is_all() {
        assert_eq!(parse_filter_from_env_value("*"), Some(TraceFilter::All));
    }

    #[test]
    fn parse_filter_empty_is_none() {
        assert_eq!(parse_filter_from_env_value(""), None);
    }

    #[test]
    fn parse_filter_whitespace_only_is_none() {
        // An env var set to just whitespace should not produce a
        // recording filter — the user likely cleared it intentionally.
        assert_eq!(parse_filter_from_env_value("   "), None);
        assert_eq!(parse_filter_from_env_value("\t\n"), None);
    }

    #[test]
    fn parse_filter_single_module_name_is_selective() {
        assert_eq!(
            parse_filter_from_env_value("user"),
            Some(TraceFilter::Selective(vec!["user".to_string()])),
        );
    }

    #[test]
    fn parse_filter_comma_separated_modules_is_selective() {
        assert_eq!(
            parse_filter_from_env_value("user,prelude,primitives"),
            Some(TraceFilter::Selective(vec![
                "user".to_string(),
                "prelude".to_string(),
                "primitives".to_string(),
            ])),
        );
    }

    #[test]
    fn parse_filter_tolerates_spaces_around_commas() {
        assert_eq!(
            parse_filter_from_env_value("user , prelude"),
            Some(TraceFilter::Selective(vec![
                "user".to_string(),
                "prelude".to_string(),
            ])),
        );
    }

    #[test]
    fn parse_filter_lone_comma_is_none() {
        // All-empty list after split → None, not Selective([]).
        assert_eq!(parse_filter_from_env_value(","), None);
        assert_eq!(parse_filter_from_env_value(",,"), None);
    }

    #[test]
    fn parse_filter_from_env_unset_is_none() {
        // Snapshot + restore pattern (cf. /backend io_trace tests).
        let prev = std::env::var_os(scheduler_trace_env_var());
        // SAFETY: test body restores before returning.
        unsafe { std::env::remove_var(scheduler_trace_env_var()); }
        let parsed = parse_filter_from_env();
        if let Some(v) = prev {
            unsafe { std::env::set_var(scheduler_trace_env_var(), v); }
        }
        assert_eq!(parsed, None);
    }

    #[test]
    fn parse_filter_from_env_one_is_all() {
        let prev = std::env::var_os(scheduler_trace_env_var());
        unsafe { std::env::set_var(scheduler_trace_env_var(), "1"); }
        let parsed = parse_filter_from_env();
        match prev {
            Some(v) => unsafe { std::env::set_var(scheduler_trace_env_var(), v) },
            None => unsafe { std::env::remove_var(scheduler_trace_env_var()) },
        }
        assert_eq!(parsed, Some(TraceFilter::All));
    }

    // --- Ring buffer discipline -------------------------------------------
    //
    // These tests exercise the lower-level thread-local-buffer path
    // directly (bypassing the process-global OnceLock filter) so they
    // are robust against test-execution order.

    fn force_push(count: usize) {
        SCHEDULER_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            for i in 0..count {
                if buf.len() == SCHEDULER_TRACE_BUFFER_CAPACITY {
                    buf.pop_front();
                }
                buf.push_back(SchedulerTraceEvent {
                    timestamp: i as u64,
                    thread_id: std::thread::current().id(),
                    thread_ord_id: thread_ord_id(),
                    tag: SchedulerTraceTag::RegisterDepPublish,
                    payload: SchedulerTracePayload::Module {
                        module: format!("m{i}"),
                        state: None,
                    },
                });
            }
        });
    }

    #[test]
    fn ring_buffer_wraps_at_capacity() {
        let _ = dump_thread_buffer();
        let overflow = SCHEDULER_TRACE_BUFFER_CAPACITY + 9;
        force_push(overflow);
        let dumped = dump_thread_buffer();
        assert_eq!(dumped.len(), SCHEDULER_TRACE_BUFFER_CAPACITY);
        // Oldest retained event is index 9 (0..9 were evicted).
        assert_eq!(dumped.first().unwrap().timestamp, 9);
        assert_eq!(dumped.last().unwrap().timestamp, (overflow - 1) as u64);
    }

    #[test]
    fn dump_clears_thread_buffer() {
        let _ = dump_thread_buffer();
        force_push(4);
        assert_eq!(dump_thread_buffer().len(), 4);
        assert!(
            dump_thread_buffer().is_empty(),
            "second dump should find the buffer empty"
        );
    }

    // --- Filter semantics --------------------------------------------------

    #[test]
    fn disabled_filter_suppresses_record() {
        // Drain first, then attempt to record. If the global filter was
        // primed by an earlier test as enabled, skip the behavioural
        // assertion — parse-layer tests already cover the disabled
        // branch directly.
        let _ = dump_thread_buffer();
        if filter().is_some() {
            return;
        }
        record_module_event(SchedulerTraceTag::RegisterDepPublish, "u");
        let dumped = dump_thread_buffer();
        assert!(
            dumped.is_empty(),
            "record_event must not emit when filter is None"
        );
    }

    #[test]
    fn selective_filter_drops_non_matching() {
        // Exercise filter matching at the payload level without
        // relying on the process-global OnceLock.
        let filter = TraceFilter::Selective(vec!["foo".to_string()]);
        let matching = SchedulerTracePayload::Module {
            module: "foo".to_string(),
            state: None,
        };
        let non_matching = SchedulerTracePayload::Module {
            module: "bar".to_string(),
            state: None,
        };
        let bulk = SchedulerTracePayload::Bulk { count: 3 };

        fn passes(f: &TraceFilter, p: &SchedulerTracePayload) -> bool {
            match f {
                TraceFilter::All => true,
                TraceFilter::Selective(names) => match p.module_path() {
                    Some(mp) => names.iter().any(|n| n.as_str() == mp),
                    None => true, // bulk events always pass
                },
            }
        }
        assert!(passes(&filter, &matching));
        assert!(!passes(&filter, &non_matching));
        assert!(passes(&filter, &bulk));
    }

    // --- Anchor alignment --------------------------------------------------

    #[test]
    fn timestamp_is_after_anchor_init() {
        // First call primes the anchor; second call's `elapsed` is
        // strictly positive (nanosecond resolution — a function call
        // between the two loads is orders of magnitude longer).
        let anchor = cranelisp_intrinsics::io_trace::trace_instant_anchor();
        let first = anchor.elapsed().as_nanos();
        // Perform a small amount of work so the second read differs.
        let _ = (0u64..100).sum::<u64>();
        let second = anchor.elapsed().as_nanos();
        assert!(
            second > first,
            "shared Instant anchor must tick forward: first={first} second={second}"
        );
    }

    #[test]
    fn anchor_is_the_shared_runtime_anchor() {
        // The /int scheduler log and /backend IO log MUST reference the
        // same OnceLock<Instant>. Verify by pointer equality.
        let a = cranelisp_intrinsics::io_trace::trace_instant_anchor();
        let b = cranelisp_intrinsics::io_trace::trace_instant_anchor();
        assert!(std::ptr::eq(a, b), "shared anchor must be stable OnceLock");
    }

    // --- Merge-sort across threads ----------------------------------------

    #[test]
    fn merge_sort_across_threads_is_monotonic() {
        // Clear residue.
        let _ = dump_all_buffers();

        let handle_a = std::thread::spawn(|| {
            SCHEDULER_TRACE_BUF.with(|cell| {
                let mut buf = cell.borrow_mut();
                for ts in [2u64, 4, 6, 8] {
                    buf.push_back(SchedulerTraceEvent {
                        timestamp: ts,
                        thread_id: std::thread::current().id(),
                        thread_ord_id: thread_ord_id(),
                        tag: SchedulerTraceTag::RegisterModuleRegister,
                        payload: SchedulerTracePayload::Module {
                            module: format!("a{ts}"),
                            state: None,
                        },
                    });
                }
            });
            publish_thread_buffer();
        });
        let handle_b = std::thread::spawn(|| {
            SCHEDULER_TRACE_BUF.with(|cell| {
                let mut buf = cell.borrow_mut();
                for ts in [1u64, 3, 5, 7] {
                    buf.push_back(SchedulerTraceEvent {
                        timestamp: ts,
                        thread_id: std::thread::current().id(),
                        thread_ord_id: thread_ord_id(),
                        tag: SchedulerTraceTag::RegisterModuleRegister,
                        payload: SchedulerTracePayload::Module {
                            module: format!("b{ts}"),
                            state: None,
                        },
                    });
                }
            });
            publish_thread_buffer();
        });
        handle_a.join().unwrap();
        handle_b.join().unwrap();

        let merged = dump_all_buffers();
        assert!(
            merged.len() >= 8,
            "expected >=8 merged events, got {}",
            merged.len()
        );
        for pair in merged.windows(2) {
            assert!(
                (pair[0].timestamp, pair[0].thread_ord_id)
                    <= (pair[1].timestamp, pair[1].thread_ord_id),
                "merge-sort must produce monotonic (ts, thread_ord) pairs"
            );
        }
        // Timestamps 1..=8 must all be present in the merged output.
        for expected in 1u64..=8 {
            assert!(
                merged.iter().any(|e| e.timestamp == expected),
                "missing timestamp {expected} in merged output"
            );
        }
    }

    #[test]
    fn thread_ord_ids_are_distinct_per_thread() {
        let main_ord = thread_ord_id();
        let child_ord = std::thread::spawn(thread_ord_id).join().unwrap();
        assert_ne!(main_ord, child_ord);
    }

    // --- Payload introspection ---------------------------------------------

    #[test]
    fn payload_module_path_extracts_module() {
        let p = SchedulerTracePayload::Module {
            module: "user".to_string(),
            state: Some(3),
        };
        assert_eq!(p.module_path(), Some("user"));
        let b = SchedulerTracePayload::Bulk { count: 2 };
        assert_eq!(b.module_path(), None);
    }

    // --- Sprint 61 Wave 3 step 3e — H4 race-closure instrumentation -------
    //
    // Two small tests: one verifies emission via record_module_event (tag
    // reaches the thread-local buffer), one verifies format_event_line
    // outputs the tag name as a static string.

    #[test]
    fn s61w3_new_tags_record_via_module_event() {
        // Drain to start from a known-empty state. Then push each of the
        // two new tags directly into the thread-local buffer (bypassing
        // the process-global OnceLock filter, which may or may not be
        // enabled depending on test-execution order — same pattern as
        // `force_push` above).
        let _ = dump_thread_buffer();
        SCHEDULER_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            buf.push_back(SchedulerTraceEvent {
                timestamp: 1,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::RepublishFromSymbolTable,
                payload: SchedulerTracePayload::Module {
                    module: "user".to_string(),
                    state: None,
                },
            });
            buf.push_back(SchedulerTraceEvent {
                timestamp: 2,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::RegisterImportsLookup,
                payload: SchedulerTracePayload::Module {
                    module: "helper".to_string(),
                    state: None,
                },
            });
        });
        let dumped = dump_thread_buffer();
        assert_eq!(dumped.len(), 2);
        assert!(matches!(dumped[0].tag, SchedulerTraceTag::RepublishFromSymbolTable));
        assert!(matches!(dumped[1].tag, SchedulerTraceTag::RegisterImportsLookup));
    }

    // --- Sprint 61 Wave 3 step 3e'' — H6 SymbolTableEnsure tag --------
    //
    // Two small tests mirror the step 3e pair above: one verifies
    // emission reaches the thread-local buffer for the new tag, the
    // other verifies `format_event_line` renders the outcome
    // symbolically ("outcome=Created" / "outcome=AlreadyPresent")
    // rather than as a numeric pool state.

    #[test]
    fn s61w3_symbol_table_ensure_records_via_module_event_with_state() {
        let _ = dump_thread_buffer();
        SCHEDULER_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            // outcome=Created (state=0)
            buf.push_back(SchedulerTraceEvent {
                timestamp: 1,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::SymbolTableEnsure,
                payload: SchedulerTracePayload::Module {
                    module: "helper".to_string(),
                    state: Some(0),
                },
            });
            // outcome=AlreadyPresent (state=1)
            buf.push_back(SchedulerTraceEvent {
                timestamp: 2,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::SymbolTableEnsure,
                payload: SchedulerTracePayload::Module {
                    module: "helper".to_string(),
                    state: Some(1),
                },
            });
        });
        let dumped = dump_thread_buffer();
        assert_eq!(dumped.len(), 2);
        assert!(matches!(dumped[0].tag, SchedulerTraceTag::SymbolTableEnsure));
        assert!(matches!(
            &dumped[0].payload,
            SchedulerTracePayload::Module { state: Some(0), .. }
        ));
        assert!(matches!(
            &dumped[1].payload,
            SchedulerTracePayload::Module { state: Some(1), .. }
        ));
    }

    #[test]
    fn s61w3_symbol_table_ensure_format_line_renders_outcome_symbolically() {
        let created = SchedulerTraceEvent {
            timestamp: 200,
            thread_id: std::thread::current().id(),
            thread_ord_id: 0,
            tag: SchedulerTraceTag::SymbolTableEnsure,
            payload: SchedulerTracePayload::Module {
                module: "helper".to_string(),
                state: Some(0),
            },
        };
        let line = format_event_line(&created);
        assert!(
            line.contains("SymbolTableEnsure"),
            "format_event_line must name new tag: {line}"
        );
        assert!(
            line.contains("outcome=Created"),
            "Created outcome must render symbolically: {line}"
        );
        assert!(
            !line.contains("pool="),
            "SymbolTableEnsure must NOT render as `pool=` (that reading \
             is reserved for scheduler pool-state tags): {line}"
        );

        let present = SchedulerTraceEvent {
            timestamp: 201,
            thread_id: std::thread::current().id(),
            thread_ord_id: 0,
            tag: SchedulerTraceTag::SymbolTableEnsure,
            payload: SchedulerTracePayload::Module {
                module: "helper".to_string(),
                state: Some(1),
            },
        };
        let line = format_event_line(&present);
        assert!(
            line.contains("outcome=AlreadyPresent"),
            "AlreadyPresent outcome must render symbolically: {line}"
        );
    }

    #[test]
    fn s61w3_new_tags_format_line_names() {
        let republish = SchedulerTraceEvent {
            timestamp: 100,
            thread_id: std::thread::current().id(),
            thread_ord_id: 0,
            tag: SchedulerTraceTag::RepublishFromSymbolTable,
            payload: SchedulerTracePayload::Module {
                module: "user".to_string(),
                state: None,
            },
        };
        let line = format_event_line(&republish);
        assert!(
            line.contains("RepublishFromSymbolTable"),
            "format_event_line must name new tag: {line}"
        );
        assert!(line.contains("module=user"), "payload formatting: {line}");

        let lookup = SchedulerTraceEvent {
            timestamp: 101,
            thread_id: std::thread::current().id(),
            thread_ord_id: 0,
            tag: SchedulerTraceTag::RegisterImportsLookup,
            payload: SchedulerTracePayload::Module {
                module: "helper".to_string(),
                state: None,
            },
        };
        let line = format_event_line(&lookup);
        assert!(
            line.contains("RegisterImportsLookup"),
            "format_event_line must name new tag: {line}"
        );
        assert!(line.contains("module=helper"), "payload formatting: {line}");
    }

    // --- Event size sanity -------------------------------------------------

    #[test]
    fn event_struct_is_bounded() {
        // A typical event carries a heap-allocated String for the
        // module path. The stack-resident struct should still be small
        // — target <= 96 bytes (ThreadId is 8B, u64 × 2 is 16B, tag 1B
        // + padding, payload 32B for a String header + state). Guard
        // against accidental bloat.
        let sz = std::mem::size_of::<SchedulerTraceEvent>();
        assert!(
            sz <= 128,
            "SchedulerTraceEvent grew to {sz} bytes (cap 128)"
        );
    }

    // -----------------------------------------------------------------
    // Sprint 61 Wave 1 follow-on — SchedulerTraceFlushGuard +
    // install_panic_hook
    // -----------------------------------------------------------------
    //
    // These tests validate the wiring primitives added for the
    // subprocess-exit / panic drain. They do NOT assert that stderr
    // actually received the bytes — capturing stderr inside a unit test
    // is fragile across Rust toolchains. Instead they verify the
    // observable-from-Rust invariants:
    //
    //   * SchedulerTraceFlushGuard::new + drop runs without panic.
    //   * Drop calls flush_to_stderr (observed indirectly by checking
    //     the thread-local buffer is drained after drop, when the
    //     filter is enabled; when disabled the drop is a no-op and
    //     the buffer is left untouched).
    //   * install_panic_hook is idempotent (second call is a no-op).
    //   * A panic inside catch_unwind after install_panic_hook still
    //     delegates to the prior hook.
    //
    // Mirrors the /backend-side tests in
    // `crates/cranelisp-runtime/src/io_trace.rs`.

    #[test]
    fn flush_guard_drops_without_panic() {
        // Must not panic. Filter may be either state — flush is a no-op
        // when disabled.
        let _ = dump_thread_buffer();
        {
            let _g = SchedulerTraceFlushGuard::new();
        }
        // Second drop in sequence: also must not panic.
        let _ = SchedulerTraceFlushGuard::default();
    }

    #[test]
    fn flush_guard_drop_calls_flush_when_filter_enabled() {
        // Seed events directly (bypasses the filter check). The Drop
        // calls `flush_to_stderr`, which calls `dump_all_buffers`,
        // which drains the thread-local VecDeque — so after drop the
        // buffer is empty IF the filter is enabled. When the filter
        // is disabled (common in the test process), `flush_to_stderr`
        // short-circuits and the buffer stays populated; in that case
        // we verify the drop at least did not panic and we drain
        // manually so we leave the thread-local clean for peers.
        let _ = dump_thread_buffer();
        SCHEDULER_TRACE_BUF.with(|cell| {
            let mut buf = cell.borrow_mut();
            buf.push_back(SchedulerTraceEvent {
                timestamp: 42,
                thread_id: std::thread::current().id(),
                thread_ord_id: thread_ord_id(),
                tag: SchedulerTraceTag::RegisterDepPublish,
                payload: SchedulerTracePayload::Module {
                    module: "wired".to_string(),
                    state: None,
                },
            });
        });

        {
            let _g = SchedulerTraceFlushGuard::new();
        }

        if filter().is_some() {
            // Flush ran. Buffer must be empty now.
            let residual = dump_thread_buffer();
            assert!(
                residual.is_empty(),
                "guard drop under enabled filter must drain the \
                 thread-local buffer; residual = {}",
                residual.len()
            );
        } else {
            // Clean up so sibling tests start from an empty buffer.
            let _ = dump_thread_buffer();
        }
    }

    #[test]
    fn flush_guard_drop_noop_when_filter_disabled() {
        // When the filter is None, the guard's drop must be a no-op —
        // specifically, it must not panic and must not emit anything.
        // We can't assert on stderr directly, but we can assert on the
        // thread-local buffer: if it was empty before, it remains
        // empty after (no side effect).
        let _ = dump_thread_buffer();
        if filter().is_some() {
            // Another test primed the filter — skip; the enabled path
            // is exercised by the sibling test above.
            return;
        }
        assert!(dump_thread_buffer().is_empty());
        {
            let _g = SchedulerTraceFlushGuard::new();
        }
        assert!(
            dump_thread_buffer().is_empty(),
            "disabled-filter drop must not emit or mutate state"
        );
    }

    #[test]
    fn install_panic_hook_is_idempotent() {
        // Reset so this test can assert the first-install path itself.
        reset_panic_hook_installed_for_tests();

        // First call installs. We can only observe this indirectly —
        // the atomic flip — because std::panic::set_hook has no
        // introspection API.
        install_panic_hook();

        // Second call is a no-op (returns without panic). If the guard
        // failed to short-circuit we would install a second hook on
        // top, leading to double-flushes on real panics downstream.
        install_panic_hook();

        // Reset so subsequent tests can re-install if they need to.
        reset_panic_hook_installed_for_tests();
    }

    #[test]
    fn install_panic_hook_runs_flush_on_panic() {
        // Install on a fresh slot. We can't directly observe the flush
        // writing to stderr, but we CAN observe the delegation chain:
        // the prior hook must still run after ours. Verify this via a
        // prior hook that mutates a shared atomic.
        reset_panic_hook_installed_for_tests();

        static PRIOR_HOOK_RAN: std::sync::atomic::AtomicBool =
            std::sync::atomic::AtomicBool::new(false);
        PRIOR_HOOK_RAN.store(false, std::sync::atomic::Ordering::Relaxed);
        // Park the test suite's own prior hook first. After we're done
        // we restore it.
        let original = std::panic::take_hook();
        std::panic::set_hook(Box::new(|_info| {
            PRIOR_HOOK_RAN.store(true, std::sync::atomic::Ordering::Release);
        }));
        // Now install our chaining hook on top of that recording hook.
        install_panic_hook();

        // Trigger a panic inside catch_unwind so this test itself
        // doesn't abort.
        let _ = std::panic::catch_unwind(|| {
            panic!("observability test panic — expected");
        });

        assert!(
            PRIOR_HOOK_RAN.load(std::sync::atomic::Ordering::Acquire),
            "prior panic hook must run after install_panic_hook (chain)"
        );

        // Restore the test harness's original hook and clear our guard
        // so we don't poison sibling tests.
        std::panic::set_hook(original);
        reset_panic_hook_installed_for_tests();
    }
}
