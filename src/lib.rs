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

// Internal — accessed only via `crate::*` paths inside the library.
pub(crate) mod bind_chain_analysis;
pub(crate) mod cache_writer;
pub(crate) mod code;
pub(crate) mod display;
pub(crate) mod exe;
pub(crate) mod expander;
pub(crate) mod marshal;
pub(crate) mod session;
pub(crate) mod pipeline;
pub(crate) mod platform;
pub(crate) mod pretty;
// repl/ module deleted — v4 REPL is driven by CompilerSession in main.rs + session_v4.rs.
// FileWatcher extracted to watch.rs; remaining features (save, trace, run-tests) are future work.
pub(crate) mod save;
pub(crate) mod scheduler;
pub(crate) mod thread_util;
// trace — int-hosted 12 `cranelisp_trace_*` JIT-emitted-call bodies per
// Decision 40 / Path B1 (S67 W4). Registered via `int_intrinsics()` at every
// JIT-build site. The 12 fns retain identical `#[no_mangle]` extern names so
// backend-emitted CLIF resolves the symbols at `JITBuilder::symbol(...)` time.
pub(crate) mod trace;
pub(crate) mod watch;
pub(crate) mod worker;
