---
number: 0017
title: ~~Core traits registered at startup, not from files~~ — RESOLVED (Sprint 11)
status: operative
---

# 0017 — ~~Core traits registered at startup, not from files~~ — RESOLVED (Sprint 11)

`register_core_trait_decls()` and `register_core_trait_impls()` are removed from `builtins.rs`. Traits (`Num`, `Eq`, `Ord`, `Display`) and their impls are ordinary Cranelisp defined in prelude `.cl` files (`stdlib/core/numerics.cl`, `stdlib/core/formats.cl`), loaded through the standard module pipeline. `import_primitives_into_user()` is retained for genuine primitives only (types, named functions, special forms). Tests that need operators must either load the prelude or define traits inline. See `design/arch/pipeline-orchestration.md` §5.
