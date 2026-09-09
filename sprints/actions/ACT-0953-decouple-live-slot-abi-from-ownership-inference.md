---
id: ACT-0953
title: Decouple live callable-slot ABI from body ownership inference
status: open
priority: future
from: arch
to: arch
sprint: 121
filed_at: 2026-09-04
refers_to:
  - repl/spec/18-redefinition.md §18.1.2
  - design/arch/ownership-inference.md
  - crates/cranelisp-types/src/lifecycle.rs
  - crates/cranelisp-backend/src/compiler
---

## Request

Sprint 121 deliberately rejects a same-language-type live replacement when an
existing callable slot's `ModeSummary` would change. This is an explicit interim
ABI-compatibility restriction: ownership modes are not language type, but they
currently determine the compiled slot contract.

A future sprint may remove that restriction only after `spec` confirms the
stronger live-redefinition promise and `arch` selects a compile-time adaptation
that preserves existing callers without dependent recompilation, fresh-slot
split worlds, runtime ownership checks, or a platform-interface change. The
design must cover ordinary functions, overload members, existing generic
realizations, materialized impl methods, first-class/curry calls, alias and
projection results, TCO, caches, and RC balance. Every inter-crate public API or
generated-baseline delta returns to the user before implementation.

## Completion evidence

- Exact normative and architecture changes are user-approved before source
  work.
- Old callers and callable values reach a same-type replacement across every
  supported ownership-mode transition with balanced RC and no runtime check.
- Cache, public API, performance, and platform-interface effects are measured
  and reviewed; the interim rejection and diagnostic are then retired together.
