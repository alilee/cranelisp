---
id: ACT-0992
title: Design selective cache invalidation together with compiler optimisations
status: deferred
priority: advisory
from: sprint
to: arch
filed_at: 2026-09-26
refers_to:
  - design/arch/interfaces.md
  - design/int/int.md
  - src/cache/dependency_record.rs
---

## Request

In the increment introducing compiler-managed inlining or constant folding,
design selective invalidation around the dependencies compilation actually
creates. The user approved deferring this work while S122 repairs missing
qualified lookup dependencies using conservative module-hash invalidation.

Distinguish name-resolution dependencies, callable-contract dependencies and
embedded implementation/value dependencies. A compatible terminal body change
may preserve an indirect caller but invalidate a caller containing its inlined
body or folded result. Consider generic specialisation and data-layout
assumptions in the compatibility assessment.

Assess release-only optimisation as an option, including cache separation by
compilation mode/settings. This action does not approve a CLI change, exact API,
schema or selective terminal-body reuse in S122.

## Completion evidence

Architecture and QA establish the contract and discriminating cases: compatible
indirect replacement, export redirection, incompatible callable/layout change,
inlined or folded implementation change, and transitive affected callers.
Verify fresh and cached execution agree across applicable compilation modes.
