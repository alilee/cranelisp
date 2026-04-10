---
name: Test timeout awareness
description: cargo test completes in a few seconds — if it runs longer, kill and investigate rather than waiting
type: feedback
---

`cargo test` for this project completes in a few seconds at most. If tests run longer than ~10 seconds, they are stuck (infinite loop, runaway memory, etc.) — kill them immediately and investigate rather than waiting with long timeouts.

**Why:** User had to intervene when tests consumed 64GB of memory while the agent waited with 5-10 minute timeouts. The agent should have noticed the abnormal duration and acted.

**How to apply:** Use a short timeout (~30s) for `cargo test`. If it times out, kill it and diagnose the hang rather than retrying with a longer timeout.
