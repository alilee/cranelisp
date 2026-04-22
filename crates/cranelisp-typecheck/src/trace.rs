//! Observability hook for typecheck-crate-internal events.
//!
//! The `cranelisp-typecheck` crate does not depend on the `cranelisp`
//! binary crate (nor on `cranelisp-runtime`), so it cannot call the
//! integration-layer observability sink in `src/observability.rs`
//! directly. Instead, the binary crate installs a function pointer at
//! startup; typecheck-crate call sites invoke it via the inline
//! `emit_symbol_table_ensure` helper. When the pointer is uninstalled
//! (e.g., in unit tests that bypass `main()`), emission is a null
//! check and a no-op.
//!
//! Design: per `design/int/heisenbug-race-closure.md §3d''` /arch
//! mini-review — the `SymbolTableEnsure { module, outcome }` tag lives
//! in `src/observability.rs` (integration-crate-internal) and the
//! crate boundary is crossed via this install-a-function-pointer
//! pattern so `cranelisp-types` gains nothing (Principle 3
//! preserved).
//!
//! Thread safety: the hook slot is a `std::sync::OnceLock<SymbolTableEnsureHook>`.
//! Install is single-shot from `main()` (or test harness) before any
//! typecheck work begins; all subsequent emissions are reads of the
//! already-set pointer. No store-after-read races exist by construction.

use cranelisp_types::ModuleFullPath;
use std::sync::OnceLock;

/// Discriminator for the `SymbolTableEnsure` trace event.
///
/// - `Created` fires from inside `entry().or_insert_with(...)` — this
///   call actually built and inserted the `SymbolTable` for the given
///   path.
/// - `AlreadyPresent` fires from the fall-through when the entry was
///   already `Occupied` — another concurrent caller won the race.
///
/// Value discipline: mapped to `u8` (0 = Created, 1 = AlreadyPresent)
/// when crossing to the `src/observability.rs` sink so the integration
/// layer does not have to re-import this type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolTableEnsureOutcome {
    /// The ensure call built and inserted a fresh `SymbolTable`.
    Created,
    /// The ensure call found the `SymbolTable` already present.
    AlreadyPresent,
}

impl SymbolTableEnsureOutcome {
    /// Compact u8 encoding for crossing the integration-layer boundary.
    #[inline]
    pub fn as_u8(self) -> u8 {
        match self {
            SymbolTableEnsureOutcome::Created => 0,
            SymbolTableEnsureOutcome::AlreadyPresent => 1,
        }
    }
}

/// Function-pointer signature for the `SymbolTableEnsure` sink.
///
/// The binary crate installs a forwarding function that calls
/// `cranelisp::observability::record_symbol_table_ensure(module, outcome)`.
/// The typecheck crate never imports that path; only the installed
/// pointer is used at the call site.
pub type SymbolTableEnsureHook = fn(module: &ModuleFullPath, outcome: SymbolTableEnsureOutcome);

static SYMBOL_TABLE_ENSURE_HOOK: OnceLock<SymbolTableEnsureHook> = OnceLock::new();

/// Install the `SymbolTableEnsure` observability sink. Idempotent —
/// only the first call wins; subsequent calls are silent no-ops.
///
/// Called once from `src/main.rs` on process start (alongside the
/// other `install_panic_hook` / flush-guard wiring). Tests that want
/// to observe emissions install a test-local sink before exercising
/// the code path.
pub fn install_symbol_table_ensure_hook(hook: SymbolTableEnsureHook) {
    let _ = SYMBOL_TABLE_ENSURE_HOOK.set(hook);
}

/// Emit a `SymbolTableEnsure` event to the installed sink, if any.
///
/// Hot-path cost when no sink is installed: a single relaxed
/// `OnceLock::get` load + null-check. No allocation, no formatting.
#[inline]
pub fn emit_symbol_table_ensure(module: &ModuleFullPath, outcome: SymbolTableEnsureOutcome) {
    if let Some(hook) = SYMBOL_TABLE_ENSURE_HOOK.get() {
        hook(module, outcome);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // Because `OnceLock` is process-global and `install_symbol_table_ensure_hook`
    // is single-shot, unit tests route the emission to a shared
    // test-local buffer keyed off a `Mutex<Vec<...>>`. The first test
    // that runs installs the forwarding hook; subsequent tests just
    // drain the buffer before asserting.

    static TEST_HOOK_EVENTS: OnceLock<Mutex<Vec<(String, SymbolTableEnsureOutcome)>>> =
        OnceLock::new();

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
}
