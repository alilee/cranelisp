// WorkerPool — facade entry point for the priority + nice worker thread pools
// owned by `CompilerSession`.
//
// Sprint 67 Cluster B sub-fire 2a per `design/arch/facades/int.md` L25
// + L201 (`#[non_exhaustive] pub struct WorkerPool { /* opaque */ }`).
//
// The struct holds the JoinHandle vectors for both priority and nice worker
// pools spawned by `CompilerSession::new`, plus the `nice_workers` count used
// by `wait_object_complete` to short-circuit the wait when zero nice workers
// are running. The methods are the facade-prescribed shape for the rest of
// the int crate (and the binary) — callers go through `worker_pool.shutdown()`
// and `worker_pool.nice_worker_count()`, never reach inside.
//
// Per the user discipline note on Cluster B: this is the method-surface
// landing. Internal data shape can stay interim — the test is that callers
// depend on `WorkerPool::shutdown` + `WorkerPool::nice_worker_count` so S68
// can reshape internals (e.g., bundle a shutdown signal beside the handles,
// switch to a different join model) without changing call sites.

use std::thread::JoinHandle;

/// The thread-pool facade owned by `CompilerSession`.
///
/// Wraps the priority + nice worker `JoinHandle` vectors. Constructed in
/// `CompilerSession::new` from the spawn loops; joined on `shutdown()`
/// (called by `CompilerSession::shutdown` + `Drop`).
pub struct WorkerPool {
    /// Priority worker thread handles — persistent for the session lifetime.
    /// Joined in `shutdown()` after the scheduler is signalled.
    priority_handles: Vec<JoinHandle<()>>,

    /// Nice worker thread handles — persistent for the session lifetime.
    /// Joined in `shutdown()` after the scheduler is signalled.
    nice_handles: Vec<JoinHandle<()>>,

    /// The requested nice-worker count. Persisted because
    /// `wait_object_complete` needs to short-circuit when zero nice workers
    /// are running (no `.o` files will ever be produced; otherwise the wait
    /// would block forever).
    nice_workers: usize,
}

impl WorkerPool {
    /// Construct a `WorkerPool` from the spawned handles.
    ///
    /// `nice_workers` is the originally requested count (NOT the length of
    /// `nice_handles` — the spawn loop may have failed to spawn some, though
    /// in practice that panics and the session never reaches this point).
    pub fn new(
        priority_handles: Vec<JoinHandle<()>>,
        nice_handles: Vec<JoinHandle<()>>,
        nice_workers: usize,
    ) -> Self {
        Self {
            priority_handles,
            nice_handles,
            nice_workers,
        }
    }

    /// Number of nice workers requested at construction.
    ///
    /// Used by `wait_object_complete` to skip the wait when zero nice
    /// workers exist (tests with `nice_workers: 0`).
    pub fn nice_worker_count(&self) -> usize {
        self.nice_workers
    }

    /// Join all worker threads.
    ///
    /// The scheduler shutdown flag must already be set before calling this
    /// (workers observe shutdown via `take_priority_work_blocking` /
    /// `take_object_codegen` returning `None`). Idempotent: a second call
    /// joins nothing because the handle vectors are drained on first call.
    ///
    /// Join errors (panicked worker) are silently ignored to match the
    /// pre-WorkerPool shape — see `design/int/persistent-workers.md §5.2`.
    pub fn shutdown(&mut self) {
        // Join priority worker threads first. A worker mid-codegen will
        // finish its current work item, re-enter `take_priority_work_blocking`
        // at the loop top, observe shutdown, and exit.
        for handle in self.priority_handles.drain(..) {
            let _ = handle.join();
        }
        // Then nice workers. They observe the shutdown flag via
        // `take_object_codegen()` returning None and exit their loop.
        for handle in self.nice_handles.drain(..) {
            let _ = handle.join();
        }
    }
}
