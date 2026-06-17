---
number: 0393
target: /arch
filed_by: /dev
filed_at: 2026-06-17
sprint_filed: 84
refers_to: design/arch/concrete-boundary-type.md §3.0 ("What populates codegen_view"), §3.1 (the relocated backstop), crates/cranelisp-typecheck/src/program.rs (build_concrete_codegen_view), crates/cranelisp-typecheck/src/adt.rs (ctor + accessor synthetic bodies)
status: open
---

# Concrete-boundary `codegen_view` is NOT total over codegen-bound entries — three populate gaps the Phase-3 backstop (0391) must own

## Issue

FIXME 0392 (LANDED, /dev) populated `ModuleEntry::Def.codegen_view` for
codegen-bound entries and retired the transitional `CheckState.mono_variants`
parallel `Vec`. The §3.0 design asserts **"EVERY `Concrete{slot}` codegen-bound
entry must end with `Some(codegen_view)`"** and §3.1 makes a `None` at a
codegen-reached entry the *single relocated backstop* (a backend `expect`).

Implementing the population surfaced that `codegen_view` is **NOT total** over the
`defined_symbols()` codegen-target set — three distinct entry classes that
`defined_symbols()` yields cannot today be given a `MonoExpr` view via
`MonoExpr::from_expr(body)`:

1. **Constructors + field accessors (`DefKind::Constructor`).** `defined_symbols()`
   yields these (`module.rs:644` — only `Overloaded`/`Constrained`/`Polymorphic`
   are excluded), and `compile_to_module_impl` walks their `ast` bodies
   (`lib.rs:651`). But the ctor synthetic body is `Expr::ConstrADT { …
   inferred_type: None }` with `inferred_type: None` field-`Var` nodes
   (`adt.rs:328`), and the accessor body is `Expr::Match { … inferred_type: None }`
   (`adt.rs:~492`). **`MonoExpr::from_expr` fails on both** (the `NotConcrete::Var(0)`
   un-annotated-node sentinel). The current `ast`-path codegen does NOT read these
   `inferred_type`s — `compile_constr_adt` reads field types from the defn
   signature (`variable_types`), not the node (`apply.rs:784`/`:479`) — so the
   gap is invisible today. **0392 sets `codegen_view = None` for these** (they are
   `DefKind::Constructor`, not `UserFnState::Concrete`, so the 0392 task scope
   correctly excluded them). The `primitives`-module ctors (e.g. `Bind`,
   `builtins.rs:708`) are never `compile_to_module` targets (primitives module is
   never compiled — confirmed), so only **user-`deftype` ctors + accessors** are
   live codegen targets with `codegen_view: None`.

2. **Multi-sig variants with an unconstrained param (`f$Var`).** A clause
   `(defn f ([x] x) …)` with an untyped param mangles to a `Concrete{slot}`
   entry `f$Var` whose body genuinely carries a `Type::Var` param type.
   `from_expr` fails → `codegen_view: None` (best-effort, `build_concrete_codegen_view`).
   This is a genuinely-non-concrete `Concrete`-slotted entry — arguably it should
   not be a concrete codegen target at all (it is effectively polymorphic), but
   that is a typecheck-modeling question, not resolvable in the 0392 populate pass.

3. **Forward-reference / annotation-incompleteness (unit-fixture-only observed).**
   Unit-test fixtures that reuse `Span::SYNTHETIC` for every body node
   (`form::tests`, `infer::tests`) collide on the span-keyed annotation maps, so a
   node's `inferred_type` is left a residual `Var` even though the program is
   concrete. **Not observed in any real (distinct-span) parsed program** — the
   full `--workspace` e2e suite (2714 tests) produced **zero** `from_expr`-fail on
   a real concrete defn (the 0392 validation payoff: every REAL concrete-defn body
   is concrete). This class is a test-fixture artifact, listed for completeness.

Because of (1)+(2), 0392 populates `codegen_view` **best-effort** at the concrete-
defn sites: `Some` on `from_expr` success (the universal real-program case),
`None` on failure (the ctor/accessor/`$Var` gap). The **mono-instance seam keeps
its hard-error** (a minted mono instance MUST be concrete post-Phase-4-A). This
`None`-vs-hard-error asymmetry between concrete defns and mono instances is the
deliberate, documented choice — but it means §3.1's "a `None` at a codegen-reached
entry is the backstop" will fire on **legitimate ctor/accessor/`$Var` entries**,
not only on producer bugs, once 0391 flips the backend read to `codegen_view`.

## Proposed resolution (for /arch — the Phase-3/0391 boundary owner)

Decide how the Phase-3 backend (0391) sources a concrete view for the three
classes, since `MonoExpr::from_expr(body)` cannot build one:

- **Constructors / accessors** — most likely the backend should NOT read
  `codegen_view` for `DefKind::Constructor` at all (it lowers `Expr::ConstrADT`
  structurally from the ctor's `DefKind::Constructor` metadata + signature, never
  from node types). i.e. the relocated backstop's `expect` must be **gated to
  `UserFnState::Concrete` entries only**, OR the ctor/accessor synthetic body must
  be `ConcreteType`-annotated at registration so `from_expr` succeeds. Recommend
  the former (gate the backstop) — it matches how ctor codegen already works.
- **`f$Var` multi-sig variants** — either the typecheck modeling rejects an
  unconstrained-param multi-sig variant as a concrete codegen target (it is
  effectively polymorphic), or the backend tolerates a `None` view for it. This
  needs an /arch+/typecheck ruling.
- Update `concrete-boundary-type.md` §3.0 to state `codegen_view` is total over
  **`UserFnState::Concrete` defn + mono-instance** entries, NOT over the whole
  `defined_symbols()` set, and §3.1 to scope the relocated backstop accordingly.

## Operational implication / Context

This is **not a behaviour regression** — 0392 is produces-but-unread; the backend
still reads `ast`. The gap only matters when 0391 flips the read. Filing now so the
0391 wave reads the backstop scope from a settled ruling rather than tripping the
`expect` on the first user `deftype` ctor. The 0392 suite is green at the
carries-only baseline (5 reds: 0366, 3× auto-IO/0367, 0382); no new red.
