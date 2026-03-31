// Thread utility functions shared across worker threads.
//
// Provides OS-level priority management for nice (low-priority) workers
// and priority promotion during hot flush.

/// Set the calling thread's scheduling priority to below-normal (nice 10).
/// Best-effort — failure is silently ignored.
///
/// Used by nice worker threads (object codegen) and the background cache
/// writer to avoid competing with priority workers for CPU time.
pub fn set_nice_priority() {
    #[cfg(unix)]
    {
        // SAFETY: setpriority is a standard POSIX API. We're setting our own
        // thread's priority, which is always permitted.
        unsafe {
            libc::setpriority(libc::PRIO_PROCESS, 0, 10);
        }
    }
}

/// Restore the calling thread's scheduling priority to normal (nice 0).
/// Best-effort — failure is silently ignored.
///
/// Used by nice workers during hot flush (priority escalation) to ensure
/// object codegen completes promptly before linking.
pub fn set_normal_priority() {
    #[cfg(unix)]
    {
        // SAFETY: setpriority is a standard POSIX API. Restoring to nice 0
        // is permitted if the process started at nice 0 (which is the default).
        unsafe {
            libc::setpriority(libc::PRIO_PROCESS, 0, 0);
        }
    }
}
