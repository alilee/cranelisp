---
number: 0925
target: /arch
filed_by: /design (typecheck)
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/typecheck/non-concrete-producer-obligations.md §5;
  design/arch/fixmes/0924-*.md, 0913-*.md;
  crates/cranelisp-types/CLAUDE.md §"The serde shape IS the cache contract";
  crates/cranelisp-backend/src/cache/mod.rs:375 (CACHE_SCHEMA_VERSION = 23);
  sprints/SPRINT.md §Must-not-interleave ("exactly one schema window, 23→24,
  0869's implementing change-set")
status: open
---

# Both S119 typecheck producer fixes are cache-visible meaning changes, and the sprint authorizes only 0869's window

## Issue

`design/typecheck/non-concrete-producer-obligations.md` rules FIXMEs 0924 and 0913.
Neither changes a serde **shape** — no new variant, no new field, no
`cranelisp-types` delta at all. Both change what an existing serde-visible field
**means** for a population of entries, which the types-crate contract treats
identically to a shape change:

> "**Any serde-visible change — field add/delete/retype, OR a meaning change to what
> an existing field records — bumps `CACHE_SCHEMA_VERSION` … in the SAME
> change-set.**" (`crates/cranelisp-types/CLAUDE.md`)

The bump is a **correctness** requirement here, not hygiene, because in both cases a
stale sidecar silently restores the defect the change-set fixes:

- **0924.** A field accessor / trait-impl method that used to serialise
  `DefKind::UserFn { fn_state: Concrete { got_slot } }` now serialises
  `Polymorphic(ParametricFn)`, and a new population of mono instances appears under
  new `build_mangled_name` keys. A cache built by the pre-fix compiler restores the
  accessor as `Concrete { got_slot }`; the new compiler then compiles that template
  frame again, with residual parameter types. **The memory-unsafety returns on a warm
  cache** — the same wild `atomic_rmw` on a scalar payload ≥ `NULLARY_TAG_THRESHOLD`
  measured at `non-concrete-release-contract.md` §2.4.
- **0913.** `Def.codegen_view: Option<MonoDefnVariant>` is serde-visible and carries
  the body's `ConcreteType`s. A stale sidecar restores the `ConcreteType::Int`
  placeholder root, backend derives no glue for it, and **the leak returns on a warm
  cache**.

`sprints/SPRINT.md` §Must-not-interleave authorizes **exactly one** schema window
(23→24) and assigns it to 0869's implementing change-set, which is rider 2 and
sequenced after tranche A. `/design`(typecheck) is not authorized to resolve the
collision.

## Options, with the design's assessment

| Option | Assessment |
|---|---|
| **(a)** 0924 + 0913 ride 0869's 23→24 window | Forces the typecheck producer work into the `/dev`(src) cache change-set. It couples a memory-safety fix to a cache-restoration fix in one commit and interleaves two tracks the sprint separates everywhere else. **Not recommended.** |
| **(b)** One additional increment, shared by both typecheck producer changes — whichever of 0924 / 0913 lands first takes it; `/arch` assigns the numbering relative to 0869 | The two are one producer surface and can share one bump. Cost is one extra wholesale cache invalidation. The one-window rule exists to stop two change-sets each *silently assuming* it owns the bump — not to cap the count when two independent correctness fixes each require one. **Recommended.** |
| **(c)** Defer 0924's implementation to S120 | Also defers 0916 (×1 RED) and rider 0867 (×3 RED). Available and honest if `/arch` judges window contention worse than the carry. |

## Note on scope

This is the **only** item `design/typecheck/non-concrete-producer-obligations.md`
owes `/arch`. Zero `cranelisp-types` delta and zero `cranelisp-typecheck`
`public-api.txt` delta are confirmed by construction (§5 of the ruling): every type
the obligation needs — `UserFnState::Polymorphic`, `ParametricFn`, `VarRef`,
`ApplyRef`, `MonoDefn`, `ConcreteType` — is already public and already carried;
`build_concrete_codegen_view` and `build_mangled_name` are `pub(crate)`; and
`mangle_trait_method`'s grammar is deliberately **unchanged** (the ruling rejects the
proposed key widening as lossy — see 0924's annotation).
