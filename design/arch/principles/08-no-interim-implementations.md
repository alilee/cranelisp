---
number: 08
title: No interim implementations of later-ring capabilities
---

# Principle 08 — No interim implementations of later-ring capabilities

**Statement.** If a feature will arrive in a later ring with its proper mechanism, do NOT build a temporary version in an earlier ring. Use the primitives that already exist at the current ring level and defer the user-facing syntax until the real mechanism is ready.

**Rationale.** Interim implementations create throwaway infrastructure that couples into multiple crates and must be unpicked later. The test is: "will this code survive into the ring where the real mechanism arrives?" If not, don't build it.

**Consequence.** Ring 0 should not implement `+` with a bespoke operator dispatch table when Ring 2 introduces `Num.+` via trait dispatch — instead, Ring 0 exposes named primitives (`add-i64`, `add-f64`) and lets `+` wait for traits. Decision 27 (G8 lands before G9) and Decision 31 (per-batch JIT, not per-worker persistent JIT) are direct applications. The `SymbolTable<C, L>` generics activation in Sprint 58 Wave 3 illustrates the converse: deferral remained correct through Phase 3–4 and activation became correct only when the structural foundation was in place AND the generics delivered concrete behaviour rather than abstract cleanliness. *(Sprint origin: Ring-model setup; sharpened in Sprint 26.)*
