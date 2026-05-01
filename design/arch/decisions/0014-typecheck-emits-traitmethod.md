---
number: 0014
title: Typecheck emits `TraitMethod`, backend maps to primitives
status: operative
---

# 0014 — Typecheck emits `TraitMethod`, backend maps to primitives

the typecheck crate always emits `ResolvedCall::TraitMethod` for trait-dispatched operators. The backend recognizes known primitive impls (e.g., `Num.+$Int` → `iadd`) via a static `(TraitName, Symbol, TypeName) → PrimitiveOp` mapping. This keeps typecheck clean and backend-optimizable.
