# AST annotation — typed bodies, carriers and publication

Owner: `design` narrow-deployed to typecheck. Subordinate to `typecheck.md` §5.

This document states how typecheck's per-node results reach the symbol table:
what the checked AST carries, which span-keyed carriers exist while a cluster is
checked, and when both become one published body and one concrete codegen view.
Section numbers are stable citation targets for tests and source, so they are
not contiguous.

Governing contracts: the callable lifecycle and its settlement funnels
(`design/arch/symbol-table-lifecycle.md`), the concrete codegen boundary
(`design/arch/concrete-boundary-type.md`), and the typed resolution carrier
([method resolution carriers](../arch/interfaces.md#method-resolutions); producer side in
`typed-resolution-carrier.md`). The checked-body ledger is designed in
`checked-body-publication.md`.

---

## 1. The model

A checked body reaches downstream consumers in two forms, built together at
publication:

| Form | Carries | Read by |
|---|---|---|
| The annotated AST (`DefnVariant`) | `inferred_type` on every `Expr` node; `resolved_call` on `Apply` and on value-position trait-method `Var`s | Regeneration, introspection, template re-instantiation, cache |
| The concrete codegen view (`MonoDefnVariant`) | A fully concrete body with every reference resolved to storage identity | Backend codegen, through `Realization::Body.view` |

Typecheck never publishes an AST whose annotations could still change, and
never publishes a concrete callable without its view. Backend reads no
typecheck side map and re-derives no type or resolution.

## 2. Carriers while a cluster is checked

Inference records its results against source spans, because a node's type and
resolution may be refined by later settlement in the same cluster (deferred
trait calls, overload and auto-curry drains, back-flow from sibling clauses,
monomorphisation):

- `expr_types` — the inferred type of each expression span, still under the
  cluster substitution.
- `MethodResolutions`, the one active resolution record:
  `resolved_calls` (per `Apply`), `pattern_ctors` (per constructor pattern),
  `var_refs` (a typed `VarRef` for every successfully typed `Var`) and
  `apply_refs` (a typed `ApplyRef` for every checked `Apply`).

`var_refs` and `apply_refs` are total: a real-span `Var` or `Apply` with no
entry fails view construction as a located typecheck error rather than reaching
backend. No producer writes either map at `Span::SYNTHETIC`, whose single shared
key would collide. The complete `MethodResolutions` moves once into the module
accumulator; no per-form copy is authoritative.

## 3. Publication

Publication happens once, in `program/finalize.rs::finalize_annotations_and_publish`,
after monomorphisation and dispatch have settled:

1. Resolve every accumulated `expr_types` entry through the final substitution.
2. For each checked body taken from the ledger, write `inferred_type` and
   `resolved_call` onto its nodes from the settled maps
   (`annotate_variant_from_maps`), then apply the final substitution.
3. For a concrete body, build its codegen view from the annotated AST plus
   `pattern_ctors`, `var_refs` and `apply_refs`
   (`build_concrete_codegen_view`), and settle the body, view and callees
   together through `settle_checked_concrete`. A non-concrete body settles as a
   template through `settle_checked_template` and carries no view.
4. Impl and default methods, whose bodies were checked during registration,
   are re-annotated and settled by the same step under the method symbols
   registration already minted.

View construction may default eligible residual type variables before refusing
a body (`non-concrete-producer-obligations.md` §3.2); an unresolved reference is
never defaulted.

---

## 4. Representation on `Expr`

### 4.3 Boxed annotation fields

Every `Expr` variant carries `inferred_type: Option<Box<Type>>`; `Apply`, and
`Var` for value-position trait methods, also carry
`resolved_call: Option<Box<ResolvedCall>>`. Both are boxed so each costs one
pointer with a null niche: an unboxed `Type` would add tens of bytes to every
variant and inflate the whole enum. A wrapping `TypedExpr` was rejected because
every recursive `Expr` position and construction site would change. Both fields
are `#[serde(default)]` and are `None` before typecheck.

---

## 9. Entry categories

A callable's lifecycle state (`Life`) determines what it carries; the full
vocabulary is `arch`'s (`design/arch/symbol-table-lifecycle.md`).

### 9.2 Callables without a compiled body

- `Life::Template` — a constrained or otherwise non-concrete definition. It
  keeps its checked body as the recipe for instances and has no slot; its
  instances are compiled instead.
- A multi-signature family's base name — a dispatch index over its clauses,
  never compiled itself.
- `Life::Inline`, `Life::HostPromised` and extern-shim, DLL or facade
  realizations — no typecheck-produced body.
- `Life::Declared` — registered but not yet settled; it must not survive
  publication.

### 9.3 Multi-signature clauses

Each clause registers under an internal name in Pass 1. When overload
resolution settles a clause with concrete parameters, `register_mangled_variants`
declares it under its mangled name and re-keys the clause's ledger publication
to that name; the clause body is then annotated and published by §3 like any
other body. A clause whose parameters stay non-concrete remains a template keyed
by its normalized mangle and is instantiated through monomorphisation
(`monomorphisation.md` §11).

### 9.4 Monomorphised instances

`monomorphise_call` re-checks the template body at the concrete substitution,
annotates the instance AST and builds its codegen view before registration.
`register_mono_entry` then installs the instance as `Life::Concrete` with its own
slot, the `InstanceLink` to its template, and a key that must equal
`InstanceLink::instance_key` for the realized signature. Publication (§3) does not
re-walk instances. A repeated request for an installed instance is a no-op.

### 9.5 What codegen compiles

Backend compiles exactly the `Life::Concrete` callables realized as
`Realization::Body`, reading the view that realization carries. There is no
separate predicate over entry kinds: a template, a family base or an
unsettled declaration cannot hold a `Body` realization.

---

## 10. Result surface

### 10.2 What a check returns

Per-symbol products — schemes, annotated bodies, views, callees and lifecycle
state — go to staging `ModuleEntry` fields, never to the result value
(BC §2 invariant 3a).

#### 10.2.3 `CheckResult` fields

`CheckResult` carries only cluster-level output for `int`: `warnings`,
`display` (the REPL display payload), and `unresolved_dispatch` (return-
polymorphic dispatch sites still unresolved, `return-poly-dispatch-signal.md`).
It carries no expression types, resolutions, instance list or default-method
list.

#### 10.2.5 Backend test bridge

Some backend unit tests compile hand-built `Defn`s without running typecheck.
They use the backend's test-only `TestCheckResult` to supply the per-span
resolutions and types those bodies need. That aggregate belongs to backend test
support; it is not a typecheck output and must not reappear on `CheckResult`.

---

## 11. Structural declarations

`imports`, `exports`, `platforms` and `submodules` are fields of each module's
`SymbolTable`. `int` writes them when it classifies structural forms; typecheck
only reads them.

### 11.3 Invariants typecheck relies on

1. **Source order.** Each field is append-only in source order, so `.cl`
   regeneration and diagnostics can cite forms by position.
2. **No deduplication.** A repeated form produces a repeated entry, so a
   duplicate-import warning can point at the redundant form.
3. **Per-module.** A module's fields hold only forms written in that module.
4. **Specification, not effect.** `imports` records what the user wrote; the
   per-symbol `Import`/`Reexport` entries record what resolved. The implicit
   prelude import is not recorded in `imports`, because regeneration must not
   emit it; consumers that need the effective scope follow the per-symbol
   chains (Principle 17).
5. **Frozen after the module is checked.** Nothing mutates them after the
   module's typecheck completes.
6. **Persisted.** They round-trip through the cache with the table; only
   runtime-only fields such as the GOT, compiled code and linker state are
   skipped and re-established after restore.

---

## 12. Code and linker generics

`SymbolTable<C, L>` and `ModuleEntry<C>` are generic over marker traits for the
compiled-code and linker stores, so a backend-owned type can live on an entry
without `cranelisp-types` depending on backend (Decision 32). Typecheck is
generic over `C` and `L` and never reads, writes or constrains the code or linker
values: production instantiates them with backend types, and typecheck unit
tests with `()`. Compiled-code lifetime and JIT reclamation are backend's and
`int`'s concern.
