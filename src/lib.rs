// cranelisp library: pipeline, REPL, and shared functionality.
//
// Exposes the pipeline and REPL modules so that integration tests
// can use them directly.

pub mod bind_chain_analysis;
pub mod cache_writer;
pub mod cluster;
pub mod code;
pub mod display;
pub mod exe;
pub mod expander;
pub mod marshal;
pub mod observability;
pub mod session;
pub mod session_v4;
pub mod pipeline;
pub mod platform;
pub mod pretty;
// repl/ module deleted — v4 REPL is driven by CompilerSession in main.rs + session_v4.rs.
// FileWatcher extracted to watch.rs; remaining features (save, trace, run-tests) are future work.
pub mod save;
pub mod scheduler;
pub mod style;
pub mod thread_util;
pub mod watch;
pub mod worker;
