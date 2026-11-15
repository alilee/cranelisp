use std::sync::{Mutex, OnceLock};

use super::*;

fn registry() -> &'static Mutex<Vec<Vec<u32>>> {
    static REGISTRY: OnceLock<Mutex<Vec<Vec<u32>>>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(Vec::new()))
}

thread_local! {
    static RING: LocalRing<u32> = LocalRing::new(2, registry);
}

fn published() -> Vec<Vec<u32>> {
    std::mem::take(&mut *registry().lock().unwrap())
}

// spec: design/int/observability.md §7 — the ring is bounded FIFO: at
// capacity the oldest event is dropped, and a drain empties it.
#[test]
fn ring_drops_its_oldest_event_at_capacity() {
    std::thread::spawn(|| {
        for event in [1, 2, 3] {
            push(&RING, event);
        }
        assert_eq!(drain_local(&RING), [2, 3]);
        assert!(drain_local(&RING).is_empty());
    })
    .join()
    .unwrap();
}

// spec: design/int/observability.md §7.1 — a thread's undrained events reach
// the registry when its thread-local is destroyed, so the exit hook, which
// runs after the exiting thread's thread-locals are gone, still sees them.
// The negative leg: a drained ring publishes nothing.
#[test]
fn destroyed_ring_publishes_its_remaining_events() {
    let _ = published();
    std::thread::spawn(|| push(&RING, 7)).join().unwrap();
    std::thread::spawn(|| {
        push(&RING, 8);
        let _ = drain_local(&RING);
    })
    .join()
    .unwrap();
    assert_eq!(published(), [vec![7]]);
}
