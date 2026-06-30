//! SIGUSR1-triggered scheduler-state dump — a durable lost-wakeup diagnostic.
//!
//! The scheduler is a concurrency kernel with a documented layered-heisenbug
//! history (S93 Invariant-PP / H5–H7; the intermittent full-suite hang under
//! CPU oversubscription). When a `cranelisp` child hangs, every compute thread
//! is parked on a futex and nothing is queued — so the ONLY way in (no gdb,
//! ptrace_scope=1, no root) is in-process. This module gives the live binary a
//! signal-triggered snapshot of the scheduler coordination state (every
//! module's pool + `blocked_on` edge + waiter list, plus the queue contents):
//! `kill -USR1 <pid>` on a hung child prints, to its stderr, exactly which
//! module is stranded and on what — pinning the dead wakeup edge.
//!
//! ## Async-signal safety
//!
//! Acquiring the scheduler `Mutex` inside a signal handler is unsound (the
//! handler can interrupt a thread that already holds the lock → self-deadlock;
//! `Mutex`/IO are not async-signal-safe). So the handler does the ONE
//! async-signal-safe thing — an atomic store — and a dedicated **watchdog
//! thread** does the actual lock-and-dump on a normal stack. The handler never
//! touches the scheduler, never allocates, never does IO.
//!
//! ## Gating (stays in-tree as a permanent diagnostic)
//!
//! Armed only when `CRANELISP_SCHED_DUMP_ON_SIGUSR1` is set in the environment.
//! Unset (the default, including the whole test suite): no handler is
//! installed, no watchdog thread is spawned, and SIGUSR1 keeps its default
//! disposition (terminate) — zero cost, zero behaviour change. Armed: a single
//! handler + a single watchdog are installed process-wide (idempotent across
//! the many sessions a process might build); each session registers a `Weak`
//! ref so a dump covers every live scheduler.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock, Weak};

use crate::session_v4::SharedState;

/// Set by the SIGUSR1 handler (async-signal-safe store); observed + cleared by
/// the watchdog thread.
static DUMP_REQUESTED: AtomicBool = AtomicBool::new(false);

/// Live sessions to dump on request. `Weak` so a dropped session does not keep
/// its `SharedState` (and its worker threads) alive; dead entries are skipped.
static REGISTRY: OnceLock<Mutex<Vec<Weak<SharedState>>>> = OnceLock::new();

/// Latches once the handler + watchdog have been installed, so repeated
/// `arm_if_enabled` calls (one per session) install them exactly once.
static ARMED: OnceLock<()> = OnceLock::new();

fn registry() -> &'static Mutex<Vec<Weak<SharedState>>> {
    REGISTRY.get_or_init(|| Mutex::new(Vec::new()))
}

/// SIGUSR1 handler. The ONLY async-signal-safe operation: an atomic store. No
/// lock, no allocation, no IO — the watchdog does all of that on a real stack.
extern "C" fn handle_sigusr1(_sig: libc::c_int) {
    DUMP_REQUESTED.store(true, Ordering::SeqCst);
}

/// Arm the SIGUSR1 dump for `shared` if `CRANELISP_SCHED_DUMP_ON_SIGUSR1` is
/// set. Registers the session and (once per process) installs the signal
/// handler + spawns the watchdog thread. No-op when the env var is absent —
/// the permanent-in-tree gate.
pub fn arm_if_enabled(shared: &Arc<SharedState>) {
    if std::env::var_os("CRANELISP_SCHED_DUMP_ON_SIGUSR1").is_none() {
        return;
    }
    registry()
        .lock()
        .unwrap_or_else(|e| e.into_inner())
        .push(Arc::downgrade(shared));

    // Install the handler + watchdog exactly once for the process. `set`
    // succeeds for the first caller only.
    if ARMED.set(()).is_ok() {
        install_handler();
        spawn_watchdog();
    }
}

#[cfg(unix)]
fn install_handler() {
    // SAFETY: registering a process signal handler. `handle_sigusr1` is a plain
    // `extern "C"` fn that only does an atomic store (async-signal-safe).
    unsafe {
        libc::signal(
            libc::SIGUSR1,
            handle_sigusr1 as *const () as libc::sighandler_t,
        );
    }
}

#[cfg(not(unix))]
fn install_handler() {}

fn spawn_watchdog() {
    let _ = std::thread::Builder::new()
        .name("sched-dump-watchdog".to_string())
        .spawn(|| {
            loop {
                std::thread::sleep(std::time::Duration::from_millis(50));
                if DUMP_REQUESTED.swap(false, Ordering::SeqCst) {
                    dump_all();
                }
            }
        });
}

/// Walk the registry and write each live scheduler's state to stderr. Runs on
/// the watchdog thread (a normal stack), so locking + IO are safe here.
fn dump_all() {
    use std::io::Write as _;
    let mut guard = registry().lock().unwrap_or_else(|e| e.into_inner());
    // Prune dead weaks while we hold the lock.
    guard.retain(|w| w.strong_count() > 0);
    let live: Vec<Arc<SharedState>> = guard.iter().filter_map(Weak::upgrade).collect();
    drop(guard);

    let stderr = std::io::stderr();
    let mut out = stderr.lock();
    let _ = writeln!(
        out,
        "\n###### CRANELISP_SCHED_DUMP_ON_SIGUSR1 (pid {}): {} live session(s) ######",
        std::process::id(),
        live.len(),
    );
    for shared in &live {
        let _ = out.write_all(shared.scheduler.dump_state_to_string().as_bytes());
    }
    let _ = out.flush();
}
