# Archived — pre-target concurrency diagrams

These diagrams capture the **pre-target** internal concurrency state of the int crate. They are kept for audit-trail value: showing the design defects (split protocols, ambient shared state, dual stores) that the target shape closes.

They are NOT the target architecture and MUST NOT be cited as design intent.

| File | Captures |
|---|---|
| `current-state.svg` | Pre-target int-internal architecture: dependency publication split across `session_v4.rs` + `worker.rs` + `scheduler.rs`; REPL-only and worker-visible state coexisting in one broad `SharedState`; split worker ownership. |
| `dependency-protocol-current.svg` | Pre-target dependency publication / registration / wait / resume protocol — implemented across multiple authorities. |
| `symbol-publication-current.svg` | Pre-target symbol publication flow — publish-before-read contract spread across typecheck, scheduler, and reader fast paths. |

For the target diagrams, see the parent directory.
