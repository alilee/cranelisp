---
number: 0123
target: /int
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: src/session_v4.rs::handle_command (ReplCommand::Reset arm), repl/spec.md §3
status: open
---

# `/reset` slash command not implemented — returns "command not yet available in v4 REPL"

## Issue

Per `repl/spec.md §3`, the `/reset` slash command must clear all user
definitions and reload the prelude, leaving the REPL session in a fresh
state but alive. The current v4 implementation in
`src/session_v4.rs::handle_command` has a `ReplCommand::Reset` arm that
clears `self.error_modules` and the file watcher state but then returns
the literal string `"command not yet available in v4 REPL"` (line 1745).
User definitions are NOT cleared.

This was surfaced during the Sprint 64 Wave 3 e2e test port (Batch 7 —
REPL surface). The new test
`tests/repl_lifecycle.rs::reset_clears_user_defns` fires a `(defn foo
[] 42)` form, then `/reset`, then `(foo)`, and expects the second `(foo)`
to fail with an undefined-symbol error. It currently fails because `foo`
remains defined after `/reset`.

## Proposed resolution

Implement the `Reset` arm in `src/session_v4.rs::handle_command` to:

1. Clear all user-defined symbols from `self.shared.symbol_tables`
   (or rebuild the tables from the seeded `primitives` module).
2. Reset the current module to `user`.
3. Reload the prelude per `spec/08-modules.md §8.11.1` resolution
   tier 1 (project_root/prelude.cl).
4. Return a success message such as `"REPL state cleared, prelude
   reloaded"` per `repl/spec.md §3`.

Implementation may want to factor a `reset_session(&mut self)` helper
that the constructor and the `/reset` handler both call.

The companion test `tests/repl_lifecycle.rs::reset_session_continues`
already passes — the session remains alive across the `/reset` no-op —
but `reset_clears_user_defns` must pass for `/reset` to be considered
implemented.

## Operational implication / Context

- The integration-tier `repl_experience.rs` did not test `/reset` because
  `ReplSession::eval` does not parse slash commands. The defect was
  hidden behind the Rust-API boundary; the e2e port surfaces it.
- Until the fix lands, the failing test
  (`reset_clears_user_defns`) is the parity-rule durable record per
  `memory/feedback_repros_join_suite.md` and `memory/feedback_failing_not_ignored.md`.
- The companion `/reset` semantics tests in `repl_introspection.rs`
  (none yet — `/reset` is a lifecycle command, not introspection)
  do not exist. The single Wave 3 failing test is sufficient.

## Sketch comparison

The sketch's `/reset` works by reconstructing the `ReplSession` from
scratch and re-importing the prelude. The reimplementation can copy
that approach if the v4 session does not have a clean separation
between user state and seeded state.
