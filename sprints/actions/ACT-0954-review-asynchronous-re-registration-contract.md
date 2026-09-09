---
id: ACT-0954
title: Review the asynchronous CompilerSession re-registration contract
status: open
priority: future
from: arch
to: arch
sprint: 121
filed_at: 2026-09-04
refers_to:
  - src/session_v4.rs
  - src/session_v4/lifecycle.rs
  - src/scheduler.rs
---

## Request

The actual REPL watcher path is synchronous: `poll_and_reload` waits for a
module reload to finish before the prompt can evaluate another form. The public
`CompilerSession::re_register_module` wrapper is different: it returns after
queueing background typecheck work, so an external library caller can invoke
`eval` while that work is still publishing. There is no repository production
caller of this wrapper.

Sprint 121 deliberately does not add a publication clock or change the public
wrapper while restoring a good build. A future architecture/API review must
choose and document one coherent contract: make the wrapper synchronous, narrow
or remove the public surface, or provide an explicit safe completion protocol.
Do not add global publication coordination merely to preserve an otherwise
unused asynchronous facade.

## Completion evidence

- The chosen public behavior and every API/baseline consequence are approved by
  the user before implementation.
- A deterministic test covers re-register followed immediately by eval and
  proves that no checked module can publish against an obsolete dependency.
- Normal watcher reload, dependency-gap retry, cache loading, and macro
  checkpoints retain their existing synchronous REPL semantics.
