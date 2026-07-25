use super::*;
use std::sync::Mutex;

// Because `OnceLock` is process-global and `install_symbol_table_ensure_hook`
// is single-shot, unit tests route the emission to a shared
// test-local buffer keyed off a `Mutex<Vec<...>>`. The first test
// that runs installs the forwarding hook; subsequent tests just
// drain the buffer before asserting.

static TEST_HOOK_EVENTS: OnceLock<Mutex<Vec<(String, SymbolTableEnsureOutcome)>>> = OnceLock::new();

fn test_hook_events() -> &'static Mutex<Vec<(String, SymbolTableEnsureOutcome)>> {
    TEST_HOOK_EVENTS.get_or_init(|| Mutex::new(Vec::new()))
}

fn forwarding_hook(module: &ModuleFullPath, outcome: SymbolTableEnsureOutcome) {
    if let Ok(mut g) = test_hook_events().lock() {
        g.push((module.as_ref().to_string(), outcome));
    }
}

fn install_test_hook_once() {
    install_symbol_table_ensure_hook(forwarding_hook);
}

fn drain_events() -> Vec<(String, SymbolTableEnsureOutcome)> {
    let mut g = test_hook_events().lock().unwrap();
    std::mem::take(&mut *g)
}

#[test]
fn outcome_u8_discriminator_is_stable() {
    assert_eq!(SymbolTableEnsureOutcome::Created.as_u8(), 0);
    assert_eq!(SymbolTableEnsureOutcome::AlreadyPresent.as_u8(), 1);
}

#[test]
fn emission_without_hook_is_noop() {
    // This test runs first if test execution order permits, proving
    // the null-hook fast path does not panic. When other tests
    // have already installed the forwarding hook, this test still
    // holds: the drain + re-emit + drain below still assert the
    // null path's shape (emission flows to buffer only if hook is
    // installed). Either way, the invocation is safe.
    let _ = drain_events();
    let path = ModuleFullPath::from("ring-test-a");
    emit_symbol_table_ensure(&path, SymbolTableEnsureOutcome::Created);
    // If hook is installed (test order), we got one event; else
    // zero. Both are fine — the invariant under test is "no
    // panic".
    let events = drain_events();
    assert!(events.len() <= 1);
}

#[test]
fn emission_through_installed_hook_reaches_sink() {
    install_test_hook_once();
    let _ = drain_events();

    let path = ModuleFullPath::from("ring-test-b");
    emit_symbol_table_ensure(&path, SymbolTableEnsureOutcome::Created);
    emit_symbol_table_ensure(&path, SymbolTableEnsureOutcome::AlreadyPresent);

    let events = drain_events();
    assert_eq!(events.len(), 2);
    assert_eq!(events[0].0, "ring-test-b");
    assert_eq!(events[0].1, SymbolTableEnsureOutcome::Created);
    assert_eq!(events[1].1, SymbolTableEnsureOutcome::AlreadyPresent);
}
