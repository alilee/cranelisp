---
number: 04
title: Parallel development is a first-class constraint
---

# Principle 04 — Parallel development is a first-class constraint

**Statement.** The architecture must enable skills to work concurrently within a ring without blocking each other. This means clear ownership (one skill per crate), interface stubs (typecheck can test without backend), and no shared mutable state between crates.

**Rationale.** Sprint cycle time is dominated by serial handoffs. The boundary structure determines what can run in parallel.

**Consequence.** Per-surface ownership is enforced at the methodology level (one skill, narrow-deployed per crate per the triad model). Boundary stubs are first-class — a typecheck change must be testable against a stub backend, and vice versa. Cross-crate interface changes go through `/arch` review precisely because they affect every parallel team.
