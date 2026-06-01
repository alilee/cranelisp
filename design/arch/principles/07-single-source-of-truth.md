---
number: 07
title: Single source of truth
---

# Principle 07 — Single source of truth

**Statement.** When a concept (ISA flags, heap classification, primitive type names, structural decls, code pointers) appears in two places, it will diverge. Every concept gets one authoritative location; other sites reference it.

**Rationale.** The prototype had 3 ISA constructions and 9 duplicate primitive-name mappings. Each duplication is a latent divergence. Decisions 25, 26, 32, 33 — placing `code` directly on `ModuleEntry::Def`, scheduling class on the `DefKind::PlatformEffect` variant, structural decls as fields on `SymbolTable`, etc. — are all enforcements of this principle.

**Consequence.** Parallel stores (`PlatformRegistry`, `ModuleStructure`, `SharedState.kept_jits`/`kept_linkers`, `try_cache_hit_load`'s parallel registration walk) are architectural defects whether or not they happen to be "fast paths" — they re-introduce divergence by construction. The `defined_symbols()` predicate (Decision 22) is the dual: one filter, one canonical location.
