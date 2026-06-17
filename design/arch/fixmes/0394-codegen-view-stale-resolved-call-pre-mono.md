---
number: 0394
target: /design
filed_by: /dev
filed_at: 2026-06-17
sprint_filed: 84
refers_to: crates/cranelisp-typecheck/src/program.rs §build_concrete_codegen_view (~:254) + §check_form_body_single_defn (~:1145), crates/cranelisp-typecheck/CLAUDE.md §"Concrete-boundary codegen_view population", design/arch/concrete-boundary-type.md §3.0/§3.1/§3.1.1
status: open
---

# Phase-3 `codegen_view` is built PRE-mono — it carries stale `resolved_call`s (and is not-yet-consumed by the backend)

## Issue

The Phase-3 backend read-flip (FIXME 0391) is **implemented and green** — the
backend codegen walk is over `MonoExpr`, `HeapCategory::classify` is total over
`ConcreteType` (the `Var`/`TyConApp` arms deleted), and the signature path is
covered. BUT the backend currently sources each entry's body from its `ast`
(rebuilt to `MonoExpr` via a lenient `Expr → MonoExpr` builder), **NOT** from the
typecheck-populated `ModuleEntry::Def.codegen_view` (FIXME 0392), because the
populated view is **stale on `resolved_call`**.

**Root cause — a population TIMING gap.** `build_concrete_codegen_view`
(`program.rs:~254`) builds the view at `check_form_body` time
(`check_form_body_single_defn`, `~:1145`), from the body the entry's `ast` holds
**at that moment**. The mono pass (`pass4_monomorphise` → `monomorphise_call`,
`traits.rs`) runs LATER and **rewrites a caller's call-node `resolved_call`** to
its `SigDispatch { mangled_name }` target (e.g. `(id 7)`'s `id` call →
`SigDispatch { id$Int }`). That rewrite lands on the entry's **`ast`** (mutated in
place) but **NOT on the already-built `codegen_view`** — the view's `id` call node
keeps `resolved_call: None`.

**Observed failure (the 73-test systemic regression this gap would cause if the
backend consumed the view).** Consuming the stale view, a polymorphic call
`(id 7)` mis-dispatches to the slot-less generic `id` (`undefined function: id`)
instead of the mono instance `id$Int`. Reproduces for EVERY polymorphic /
higher-order user call: `(defn id [x] x) (id 7)`, `(ap g x)`, trait-operator HOFs,
constrained-poly auto-curry, etc. — the entire `spec_03`/`04`/`07`/`10`/`12`
polymorphic surface.

## Proposed resolution

Make `codegen_view` reflect the **post-mono** body, so it is the single source of
truth the backend can consume (the §3.0/§3.1 design intent). Options for /design
(typecheck) to weigh:

1. **(Re)build the view AFTER the mono pass rewrites caller `resolved_call`s** —
   move/duplicate the `build_concrete_codegen_view` call to a point downstream of
   `pass4_monomorphise`'s caller-rewrite, OR re-run it on the (now-rewritten) `ast`
   at `finalize_check_result`.
2. **Patch the view in lock-step with the `ast` rewrite** — wherever the mono pass
   mutates a call node's `resolved_call` on `ast`, apply the same edit to the
   corresponding `codegen_view` node (same span).

Either way, the invariant to restore: **`codegen_view`'s `MonoExpr` carries the
same `resolved_call`s as the final `ast`** (mono_expr.rs already specifies the
view carries `resolved_call` verbatim — the gap is purely the build *timing*).

## Operational implication / Context

- **Backend half is DONE and green** (FIXME 0391 closes): `classify(&ConcreteType)`,
  `Var` arm deleted, `MonoExpr` walk across all 7 codegen files + the JIT
  `compile_defn` path, signature-path `Var → Mixed` (`signature_heap_category`),
  the lenient `Expr → MonoExpr` builder. The structural payoff holds — **no
  `Type::Var` reaches `classify` by construction.**
- **What is deferred to this FIXME:** the backend flipping its body source from
  `ast` to `codegen_view`. The flip is a 2-line change in
  `compile_to_module_impl` (`crates/cranelisp-backend/src/lib.rs` — `let body =
  mono_from_expr_signature_driven(&variant.body)` → consume `_codegen_view`) plus
  the `compile_defn` JIT path. The `_codegen_view` / `kind` bindings are already
  in place for that flip; the partition predicate `requires_codegen_view` + the
  scoped-backstop unit tests are landed.
- **Supersedes the §3.1.1 "totality" framing.** §3.1.1 framed `codegen_view` as
  total over `DefKind::UserFn { Concrete{slot} }` with a hard `expect` backstop.
  The LANDED 0392 is **best-effort** (`cranelisp-typecheck/CLAUDE.md` documents
  `None` on a `Concrete` defn whose body does not `from_expr`-convert), so the
  backend uses a lenient builder, not the `unreachable!`. Once this FIXME restores
  a post-mono, resolved-call-correct view, /design should reconcile §3.1.1's
  totality claim with the best-effort reality (either make 0392 total, or restate
  §3.1.1 as best-effort + lenient-fallback).
- A second, smaller best-effort gap also rides on the lenient fallback and is
  closed-by-construction here: a generic **constructor `Def`'s own template body**
  (`(Some [:a val])` → field param `Type::Var a`) and a bare polymorphic REPL
  value (`[]`, §3.11.2 disposition 3) carry `Var`-typed body nodes whose types are
  read ONLY via the signature path (`Var → Mixed`), never the deleted
  `classify(Var)` panic. These are sound; they are NOT the systemic regression
  (that was purely the stale `resolved_call`).
