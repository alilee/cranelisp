---
number: 0391
target: /dev
filed_by: /arch
filed_at: 2026-06-17
sprint_filed: 84
refers_to: design/arch/concrete-boundary-type.md §3.0/§3.1 (Phase 3), design/arch/bounded-contexts.md §3 invariant 9, crates/cranelisp-backend/src/heap.rs, crates/cranelisp-backend/src/lib.rs, crates/cranelisp-backend/src/compiler/
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

4. **The single relocated backstop.** A codegen-reached entry whose
   `codegen_view()` is `None` is a **located `expect`/`unreachable`** at the
   `compile_to_module` entry — the ONE backstop replacing the four deleted
   behavioural guards. It fires only on a producer bug (a `Concrete` entry reached
   codegen without a populated view), never on user input.

5. **Unit tests** per CLAUDE.md §Testing: `classify` total over `ConcreteType`
   (exhaustive, no panic case); `compile_to_module` reads `codegen_view`; the
   `None`-codegen-view backstop fires on a synthesised codegen-target entry with no
   view. The `#[should_panic]` 0375-backstop tests retire.

## Operational implication / Context

The §3.11.1 typecheck check STAYS (the user-facing ambiguity diagnostic — it is
NOT a backend concern). `is_representation_undetermined()` is already retired
before Phase 3 (FIXME 0386). `CACHE_SCHEMA_VERSION` already bumped 7 → 8 (/arch,
the field landing) — no further bump. `classify` is backend-internal — no
`public-api.txt` move. Coordinate with FIXME 0392 (population): 0392 lands first
(or in the same wave, populating before the read flip).
