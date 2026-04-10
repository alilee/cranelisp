---
name: No premature performance workarounds
description: Don't keep parallel code paths for performance — get the single correct path first, tune later
type: feedback
---

Do not keep v1 code paths alive as "performance workarounds" for the v2 pipeline. The whole point of pipeline unification is one path. If compile_unit() is slow for prelude loading, the answer is to tune compile_unit() later — not to maintain a separate v1 batch path.

**Why:** Sprint 28 agents kept routing prelude loading through the v1 batch path because interactive mode was slow for 27 stdlib modules. The user rejected this — it defeats the purpose of unification and prevents ever deleting the v1 code.

**How to apply:** When migrating to a new architecture, always route through the new path. Performance problems in the new path are bugs to fix in the new path, not reasons to keep the old path alive.
