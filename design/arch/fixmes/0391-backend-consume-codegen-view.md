---
number: 0391
target: /dev
filed_by: /arch
filed_at: 2026-06-17
sprint_filed: 84
refers_to: design/arch/concrete-boundary-type.md §3.0/§3.1/§3.1.1 (Phase 3 + backstop scope), design/arch/bounded-contexts.md §3 invariant 9, crates/cranelisp-backend/src/heap.rs, crates/cranelisp-backend/src/lib.rs, crates/cranelisp-backend/src/compiler/
status: open
---

# Backend (Phase 3) — consume `ModuleEntry::Def.codegen_view` (`MonoExpr`/`ConcreteType`); `classify` becomes total

## Issue

The concrete-boundary arc's Phase-3 threading shape is LANDED in `cranelisp-types`
(/arch, 2026-06-17): `ModuleEntry::Def` carries an additive
`codegen_view: Option<MonoDefnVariant>` field (read through
`ModuleEntry::codegen_view()`), whose `MonoExpr` body carries `ty: ConcreteType`
on every node. The backend must now switch its codegen read path off
`Expr.inferred_type` (a `Type` that *has* a `Var` variant) onto the concrete
view, and `HeapCategory::classify` must become total over `ConcreteType`.

This is the /dev(backend) half. It is **gated on /dev(typecheck) populating
`codegen_view`** (FIXME 0392) — the backend cannot read a view that is not yet
written. Until then the backend keeps reading `ast`/`inferred_type` (the
transitional path; the additive field defaults `None`, suite stays green).

## Proposed resolution

Per `design/arch/concrete-boundary-type.md` §3.0/§3.1 (the per-site map is there):

1. **`HeapCategory::classify` signature + arm deletion** (`crates/cranelisp-backend/src/heap.rs:438`):
   `classify<C, L>(ty: &Type, …)` → `classify<C, L>(ty: &ConcreteType, …)`. DELETE
   the `Type::Var(_) => Mixed` arm (~`:490`) and the `Type::TyConApp(_, _) => Mixed`
   arm (~`:492`) — inexpressible over `ConcreteType`. The match becomes exhaustive
   over `{Int, Bool, String, Float, Fn, ADT}` with NO catch-all and NO panic case.
   `classify` is now **total**. Remove the deferred-`Mixed`-then-panic comment block
   (`heap.rs:456–479`). **Do NOT re-add the 0375 backstop** — the illegal input is
   unconstructable.

2. **The ~13 `inferred_type` read sites → `MonoExpr.ty()`** (7 backend codegen
   files: `compiler/{apply,control_flow,match_codegen,mod,trace_codegen,vec_codegen}.rs`).
   The codegen walk is now over `MonoExpr` (mirrors `Expr`'s 14 non-`Annotate`
   variants), so `expr.inferred_type()` → `mono_node.ty()` (a `&ConcreteType`), and
   each `classify` call passes the `&ConcreteType` directly. Per-site table in §3.1.

3. **`compile_to_module` consumes `codegen_view`** (`lib.rs:660–686`): read
   `entry.codegen_view()` and walk the `MonoDefnVariant.body: MonoExpr`; the
   `compiler/mod.rs::FnCompiler::compile_expr` dispatch (~`:1100`) becomes a
   `MonoExpr`-variant match (no `Annotate` arm — erased at build). Stop
   reconstructing a `Defn` from `ast` + reading `Expr`.

4. **The single relocated backstop — SCOPED to `DefKind::UserFn { Concrete{slot} }`
   (FIXME 0393 resolution, `concrete-boundary-type.md` §3.1.1).** A codegen-reached
   **body-AST-node-typed** entry — `DefKind::UserFn { fn_state: UserFnState::Concrete { .. } }`
   (ordinary concrete defns + mono instances; mono instances ARE this kind) — whose
   `codegen_view()` is `None` is a **located `expect`/`unreachable`** at the
   `compile_to_module` entry: the ONE backstop replacing the four deleted behavioural
   guards. It fires only on a producer bug (a `Concrete{slot}` entry reached codegen
   without a populated view), never on user input. **The `expect` MUST NOT apply to
   the signature-driven kinds**: `DefKind::Constructor` (ctor/accessor), `Primitive`,
   `PrimitiveExtern`, `PlatformEffect` legitimately carry `codegen_view: None` — they
   are codegen'd by signature/extern mechanisms that never read a body node's type.
   Put the `expect` INSIDE the `Concrete{slot}` `UserFn` arm of `compile_to_module`,
   not at the entry destructure (so a `None` on a `Constructor` is never tested
   against it).

5. **Ctor/accessor codegen sources field types from the signature via `from_type`
   (FIXME 0393 resolution, §3.1.1).** `classify` now takes `&ConcreteType`. At the
   THREE signature-read sites (the ctor/accessor codegen's only type reads), convert
   the field `Type` → `ConcreteType` via `ConcreteType::from_type(ty).expect("ctor/
   accessor field type concrete by §3.11.1 — compiler bug if not")` AT the `classify`
   call site (do NOT retype `CtorField`/`variable_types` wholesale — that wider
   retype is optional, out of this FIXME's minimum):
   - `compiler/mod.rs:1066–1098` — function-entry param binding (feeds
     `compile_consuming_arg_list`'s `classify`, `apply.rs:~484`).
   - `compiler/mod.rs:756–769` — `extract_constructor` (`scheme` → `CtorField.ty`).
   - `compiler/match_codegen.rs:452` — `bind_data_pattern_fields` (`classify(ft, …)`).
   This keeps "no `Var` reaches `classify`" TOTAL across BOTH the body-AST path
   (`MonoExpr.ty()` is already `ConcreteType`) AND the signature path (field `Type`
   → `from_type` before `classify`). The `from_type` failure here is the relocated
   compiler-bug `expect`, NOT a user error (§3.11.1 guarantees concreteness upstream).
   **`$Var` free-var multi-sig variants** are excluded from the codegen batch by
   Phase-4 part B (effectively polymorphic — mono sources, not codegen targets); if
   one reaches Phase-3 codegen as `Concrete{slot}` with a free var, the backstop (4)
   firing on it is CORRECT — it has caught a slot-gate/mono bug, not a
   `None`-tolerated case (§3.1.1 disposition 3).

6. **Unit tests** per CLAUDE.md §Testing: `classify` total over `ConcreteType`
   (exhaustive, no panic case); `compile_to_module` reads `codegen_view` for a
   `Concrete{slot}` `UserFn`; the `None`-codegen-view backstop fires on a synthesised
   `Concrete{slot}` `UserFn` target with no view; **the backstop does NOT fire on a
   `DefKind::Constructor` entry with `codegen_view: None`** (the scope guard);
   ctor/accessor field-type `from_type` conversion succeeds on a concrete ctor. The
   `#[should_panic]` 0375-backstop tests retire.

## Operational implication / Context

The §3.11.1 typecheck check STAYS (the user-facing ambiguity diagnostic — it is
NOT a backend concern). `is_representation_undetermined()` is already retired
before Phase 3 (FIXME 0386). `CACHE_SCHEMA_VERSION` already bumped 7 → 8 (/arch,
the field landing) — no further bump. `classify` is backend-internal — no
`public-api.txt` move. Coordinate with FIXME 0392 (population): 0392 lands first
(or in the same wave, populating before the read flip).

**Backstop scope SETTLED (FIXME 0393 RESOLVED + `git rm`'d by /arch, 2026-06-17).**
0393 raised that `codegen_view` is NOT total over the `defined_symbols()` set —
`DefKind::Constructor` ctor/accessor bodies, `$Var` free-var multi-sig variants, and
primitives get `None`. The resolution (steps 4+5 above + `concrete-boundary-type.md`
§3.1.1): the view is total over `DefKind::UserFn { Concrete{slot} }` ONLY (the
body-AST-node-typed targets); ctors/accessors are signature-driven (read field
`Type`s from the `scheme`, convert via `from_type` → `classify`, never a body node's
type) and legitimately carry `None`; the backstop scopes to the `Concrete{slot}`
`UserFn` arm and never trips on them. This brief is now COMPLETE for /dev(backend) —
no open design question remains on the Phase-3 read flip.
