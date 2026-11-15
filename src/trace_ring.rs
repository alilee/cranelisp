//! The per-thread event ring shared by the three trace sinks
//! (`design/int/observability.md` §7).
//!
//! A thread's ring publishes its remaining events into its sink's
//! process-wide registry when the thread-local is destroyed. That covers a
//! worker thread that exits and the process exit: `exit` destroys the calling
//! thread's thread-locals before it runs the `atexit` flush hook, so a ring
//! that did not publish would lose the events of the thread that ended the
//! process, typically the one that panicked. Every access after destruction
//! is a no-op rather than a panic, because a panic inside the `extern "C"`
//! exit hook aborts the process and replaces its exit status.

use std::cell::RefCell;
use std::collections::VecDeque;
use std::sync::Mutex;
use std::thread::LocalKey;

/// A sink's process-wide registry of published per-thread buffers.
pub(crate) type Registry<E> = fn() -> &'static Mutex<Vec<Vec<E>>>;

/// A bounded FIFO ring: at capacity the oldest event is dropped.
pub(crate) struct LocalRing<E: 'static> {
    events: RefCell<VecDeque<E>>,
    capacity: usize,
    registry: Registry<E>,
}

impl<E: 'static> LocalRing<E> {
    pub(crate) fn new(capacity: usize, registry: Registry<E>) -> Self {
        Self {
            events: RefCell::new(VecDeque::with_capacity(capacity)),
            capacity,
            registry,
        }
    }

    fn push(&self, event: E) {
        let mut events = self.events.borrow_mut();
        if events.len() == self.capacity {
            events.pop_front();
        }
        events.push_back(event);
    }

    fn drain(&self) -> Vec<E> {
        self.events.borrow_mut().drain(..).collect()
    }

    /// The ring's events, for sink tests that plant events directly.
    #[cfg(test)]
    pub(crate) fn borrow_mut(&self) -> std::cell::RefMut<'_, VecDeque<E>> {
        self.events.borrow_mut()
    }
}

impl<E: 'static> Drop for LocalRing<E> {
    fn drop(&mut self) {
        let remaining: Vec<E> = self.events.get_mut().drain(..).collect();
        if remaining.is_empty() {
            return;
        }
        if let Ok(mut published) = (self.registry)().lock() {
            published.push(remaining);
        }
    }
}

/// Record `event` on this thread's ring. Dropped once the ring is destroyed.
pub(crate) fn push<E: 'static>(ring: &'static LocalKey<LocalRing<E>>, event: E) {
    let _ = ring.try_with(|ring| ring.push(event));
}

/// Drain this thread's ring; empty once the ring is destroyed, whose events
/// are then in the registry.
pub(crate) fn drain_local<E: 'static>(ring: &'static LocalKey<LocalRing<E>>) -> Vec<E> {
    ring.try_with(LocalRing::drain).unwrap_or_default()
}

#[cfg(test)]
mod tests;
