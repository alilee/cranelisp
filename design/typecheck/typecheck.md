# `cranelisp-typecheck` — master design

Owner: `design` narrow-deployed to typecheck. Readers: `design` and `dev` working
this crate, and `arch` checking cross-crate coherence.

This is the crate's single statement of design intent. Every other document in
`design/typecheck/` is a subordinate elaboration of one subject (§10); where a
subordinate and this document disagree, this document wins, and the source wins
over both until the disagreement is repaired.

It designs against, in authority order:

1. [Bounded contexts §2](../arch/bounded-contexts.md#2-typecheck-cratescranelisp-typecheck)
   — what the crate owns and its cross-context invariants 1–10.
2. The published surface — `crates/cranelisp-typecheck/public-api.txt` (the
   checked baseline) and the crate-root rustdoc in `src/lib.rs` (per-item
   contracts).
3. The architectural [principles](../arch/principles.md) and the cross-crate
   rulings that source cites as "Decision N"; the
   [decision label index](../arch/decisions/README.md) resolves each label to its
   current home.

Git history carries how the crate reached this shape; this document states only
the current design and the rationale whose loss would invite a plausible mistake.

---

## 1. Bounded context — what we own

> "Untyped AST becomes typed AST plus populated symbol tables. Typecheck infers
> types, resolves traits, classifies polymorphism, and analyses match
> exhaustiveness." — BC §2

In scope:

- Hindley-Milner inference over every `Expr`, `Pattern` and `MatchArm` variant.
- Trait declarations, impl registration and method resolution, including
  higher-kinded traits, constrained polymorphism and monomorphisation.
- ADT typing: constructor schemes, exhaustiveness, type-parameter instantiation
  and accessor synthesis.
- Per-symbol callee extraction onto each callable's `callees` (the call graph
  typecheck produces for redefinition and emission order).
- Interprocedural ownership inference over the monomorphised call graph
  (`ownership-inference.md`, governed by `design/arch/ownership-inference.md`).
- Dependency-gap signalling: a cross-module dependency that is not yet
  typechecked is returned as `CheckError::Gap(ResolutionGap::…)` for `int` to
  satisfy, never waited on (Principle 3 — the crate sits below the scheduler).

Out of scope: AST construction and macro expansion (frontend); code emission and
RC discipline (backend); scheduling, sessions, module loading and the synthetic
`primitives`/`macros` mount (`int`); runtime helpers (primitives/intrinsics);
shared boundary types (`cranelisp-types`, owned by `arch`).

The crate has no cadence and no shared session state. `int` invokes it
synchronously, one cluster at a time.

---

## 2. Public surface

The canonical surface is `public-api.txt` plus the `lib.rs` rustdoc; this section
is a map, not a second contract.

- `check_forms` — the cluster-atomic entry (Decision 44): checks one cluster's
  `ParsedEntry` list against `SymbolTableAccess` (staging over live), the other
  modules' `SymbolTables`, `ModuleAliases` and `PreludeFallback`, returning
  `Result<CheckResult, CheckError>`.
- `instantiate_demands` — the reload seed: re-requests typed `MonoDemand`s
  through the same monomorphisation worklist after a redefinition
  (`monomorphisation.md` §3.8). It is not a second instantiation engine.
- `check_type_expr` — standalone `TypeExpr → Type` resolution for annotation and
  platform-signature contexts.
- `signature_matches_exact` / `signature_matches_partial` — the importable-symbol
  search predicates (`signature-match.md`).
- Scaffolding exposed for tests and direct drivers: `CheckState`,
  `TypeCheckEnv`, `PreludeFallback`, `advance_next_id_past_table`,
  `SymbolTableAccess`, `SymbolTableRead`, `SymbolTableMut`. Production `int`
  uses the entry functions only.
- Crate-owned result types: `CheckResult`, `CheckError` (`Gap` or located
  `TypeError`), `DispatchGap`, `UnresolvedDispatchSite`.
- The symbol-table-ensure trace hook for `int`'s scheduler tracing.

A `public-api.txt` change is an inter-crate public-API change: it needs the
user's approval before implementation and rides its source change-set under
`design/arch/CLAUDE.md` §"Baseline-diff discipline".

---

## 3. Internal architecture

### 3.1 Module map

| Unit | Responsibility |
|---|---|
| `form.rs` | The public entry functions (§2). |
| `program/` | The cluster pipeline (§5): `register` (Pass 1, including `register/multi_sig`), `body` (Pass 2), `finalize` (post-passes, harvest windows, ambiguity, publication), `mono_collect` (call-site demand collection), `callees` (the callee harvest), `support` (the concrete codegen-view builder), and the `#[cfg(test)]` `test_driver` and `test_support`. `mod program` is private and nothing in it is `pub`; a helper shared between its submodules is `pub(super)`, and `pub(crate)` only when a caller outside `program/` exists. |
| `traits/` | `registry` (trait declarations), `impl_check` (impl registration, HKT impl methods, method minting), `dispatch` (method resolution, dispatch-argument selection and impl lookup at the trait's home), `monomorphise` (the instance engine, `monomorphisation.md` §3.9), `type_resolve` (impl-target, declaration-identity, occurrence and constructor-variable predicates; the trait and HKT signature wrappers over `resolve` are `TypeCheckEnv` methods in `checker.rs`). `mod traits` is private and nothing in it is re-exported publicly; a helper shared between its submodules is `pub(super)`, and `pub(crate)` only when a caller outside `traits/` exists. |
| `ownership/` | The ownership-inference pass: `classify`, `transfer`, `fixpoint`, `confinement`, `uniqueness`, `publish`, `sites`, `trace` (`design/typecheck/ownership-inference.md` §1.3). |
| `checker.rs` | `TypeCheckEnv`, `CheckState`, cross-module lookup and the scope-resolution seam (§3.3). |
| `infer.rs` | Algorithm W per expression variant, with `infer_var` as the reference-resolution chokepoint. |
| `candidate_selection.rs` | Use-site selection among same-spelling canonical candidates (`use-site-candidate-selection.md`). |
| `adt.rs` | ADT registration, exhaustiveness and accessor synthesis. |
| `resolve.rs` | The one `TypeExpr → Type` resolver behind `TypeExprCtx` (`type-expr-resolver-convergence.md`). |
| `unify.rs` | Unification with rigid constraint variables, occurs check and type-error rendering (see [type names in errors](#83-type-names-in-error-messages)). |
| `cluster.rs` | `SymbolTableAccess`, the staging-versus-live choke point (see [staging dispatch](#64-staging-versus-live-dispatch)). |
| `scheme.rs`, `scope.rs`, `result.rs`, `signature_match.rs`, `trace.rs` | Generalise/instantiate, the lexical scope stack, the result types, the search predicates and the trace hook. |
| `builtins.rs` | Test-only synthetic world (`#[cfg(test)]`); production mounts are `int`'s. |

Module tests sit beside their production unit; `crates/cranelisp-typecheck/CLAUDE.md`
§"Testing" names the homes.

### 3.2 Maintainability watch

`checker.rs` is the largest production module and collects lookup helpers that
have no narrower home. Split it along a responsibility seam when a change would
otherwise add a new concern to it; do not split it by size alone (Principle 6).
Open audit points live in the action and filing registers; historical
assessments remain in Git.

### 3.3 Cross-module lookups

Short-name resolution is current-module-only, with per-symbol chain-follow
through `Import`/`Reexport` entries — never a universe scan (Principle 17;
`crates/cranelisp-typecheck/CLAUDE.md` §"Name resolution").
`resolve_terminal_entry_and_home` is the navigation primitive, staging-aware
through `probe_module_entry_owned`. Every bare-name reference resolves through the
one scope seam: `TypeCheckEnv::scope_resolve` / `scope_resolve_in` for a single
terminal, or `scope_resolve_candidates` when the use site selects among
same-spelling canonical candidates (`use-site-candidate-selection.md`).
Registration rejects nothing for sharing a spelling with an import, export,
prelude binding or derived member (`spec/08-modules.md` §8.6.4); the prelude participates only as
the fallback those seams apply.

A centralised lookup index is not planned: it would be a bookkeeping change with
no measured performance need.

---

## 4. Quality attributes

- **Simplicity (Principle 6).** One cluster path, one `TypeExpr` resolver, one
  unification seam and one scope-resolution seam. New behaviour extends these
  seams; a parallel pipeline, resolver or walker is a defect.
- **Observability.** `CheckResult` and the located `CheckError` are the
  diagnostic product. The only trace surface is the symbol-table-ensure hook
  (`design/int/heisenbug-race-closure.md` §8.3.4); per-symbol introspection is
  backend's and `int`'s.
- **Performance.** Cross-module resolution is per-symbol chain-follow; no spec
  criterion pins typecheck time, and performance work waits for a measurement.
- **Testability (Principle 5).** `check_forms` takes its tables as arguments, so
  unit tests drive it through `TestFixture` over `cranelisp-types` alone, with no
  `cranelisp-primitives` dependency.

---

## 5. Pipeline inside `check_forms`

1. **Pass 1 — register** (`program/register.rs`). Each form installs its
   canonical declarations and exposes their module-scope candidates under
   `spec/08-modules.md` §8.6.4: type definitions, trait declarations and
   methods, trait impls, and signature schemes. Distinct canonical declarations
   sharing a spelling coexist; use sites select among them
   (`use-site-candidate-selection.md`). No body is checked.
2. **Pass 2 — body check** (`program/body.rs`). Algorithm W checks each body
   against its registration. The checked AST and initial canonical callees stay
   in the private body ledger (`checked-body-publication.md`); active expression
   and resolution facts stay on `CheckState`. Initial callees come from
   `program/callees.rs::harvest_callees`.
3. **Finalize** (`program/finalize.rs`). Generalisation, overload resolution and
   the multi-signature back-flow drain (`monomorphisation.md` §11), the
   ambiguity backstop, the two post-settlement monomorphisation harvest windows
   (`monomorphisation.md` §3.3), and final publication: each body's AST and
   complete callee set are published together, once
   (`crates/cranelisp-typecheck/CLAUDE.md` §"`callees` completeness"). The
   ownership pass then runs over the published concrete bodies
   (`design/typecheck/ownership-inference.md` §1.2).

All writes go through `SymbolTableAccess`. `int` commits the staging table only
when the whole cluster succeeds.

### 5.1 Per-form dispatch

`check_forms` drives the crate-private per-form entry `program::check_form` once per
form per pass, merges each `FormCheckResult` into one `ModuleCheckAccumulator`, then
calls `finalize_check_result`. None of these is public; `check_forms` is the entry.

| Form | Pass 1 (`Register`) | Pass 2 (`CheckBody`) |
|---|---|---|
| Type definition | Register the type and its constructors (`adt.md`). | Nothing. |
| Trait declaration | Register the declaration and its methods ([trait declaration](traits.md#2-trait-declaration)). | Nothing. |
| Trait impl | Register the impl and check its written method bodies ([trait implementation](traits.md#3-trait-implementation)); return the generated default methods. | Nothing. |
| Single-signature definition | Record the body's registration (fresh parameter and return variables) in the body ledger. | Check the body against that registration. An impl method already checked in Pass 1 is skipped. |
| Multi-signature definition | Register one entry per clause (`monomorphisation.md` §11). | Check each clause body; overload settlement happens in finalize. |

A REPL expression reaches typecheck already wrapped as a zero-parameter definition
named `__expr` and is checked like any definition; it is a monomorphisation root
(`monomorphisation.md` §3.2). The test-only driver (`program/test_driver.rs`)
performs the same wrapping for in-crate tests.

### 5.2 Pass invariants

1. **Every registration precedes every body check.** Checking a body whose
   definition was never registered is an error, not an implicit registration.
   This is what lets a body call a definition later in the cluster (spec §3.5.2).
2. **Pass 1 is one sweep in form order.** Each form registers when it is reached;
   there is no hidden sort by form kind. Default methods produced by impls are
   registered after the sweep and their bodies are checked after the Pass-2 sweep.
   A body may refer to any definition in the cluster. A declaration-level reference
   to a type declared later in the cluster is a different matter; see the open item
   in §11.
3. **One `CheckState` per cluster.** All bodies share one substitution, so a call
   in one body constrains the callee's registration variables. Each Pass-2 body
   starts from the trait constraints Pass 1 left, and definitions already
   generalised are re-settled before each body (`monomorphisation.md` §5.1).
4. **Settlement follows all bodies.** A body's scheme may be generalised and
   written back as soon as its check ends, so later siblings instantiate it
   (`monomorphisation.md` §5.1); that writeback neither settles nor publishes.
   Final generalisation, overload settlement and monomorphisation run in finalize,
   after every body has been checked, so a body's expression types are provisional
   until then. Nothing is published before finalize (§5 step 3).
5. **One accumulator per cluster, owned by one call.** The accumulator is created
   before Pass 1 and consumed by finalize. It is never shared across threads; each
   `int` worker owns its call's `CheckState` and accumulator (§7.1).

---

## 6. Mutation discipline

### 6.1 The contract

`check_forms` never receives `&mut SymbolTable`. It writes through
`SymbolTableAccess` (§6.4), and each module table mutates per entry through its
inner `DashMap`. The only whole-table mutations belong to `int` on the initiating
thread: structural declarations at module registration and the REPL
`defn_order` append after a commit.

This is what makes per-symbol gaps operationally sound: a waiter resumed on
`SymbolTypechecked(fq)` can read the other module's table through shared shard
access, and a second worker's cross-module read does not block behind a
whole-table write lock.

### 6.2 What typecheck writes

- The caller-owned AST is annotated in place (`ast-annotation.md`).
- Declarations, schemes, synthesised accessor and monomorphised entries, and
  checked-body publications go to staging through the types-crate funnels. A
  callable's lifecycle state (`Life`) is set only by those funnels
  (`design/arch/symbol-table-lifecycle.md`); typecheck consumes that vocabulary
  and never grows a local variant beside it.

### 6.4 Staging-versus-live dispatch

`SymbolTableAccess` selects per module: the cluster's own module reads a
staging-over-live union and writes staging (`SymbolTableRead::Cluster`); every
other module reads live. The distinction is absorbed inside the accessors, so no
register or lookup site branches on it. `cluster.rs` rustdoc records the as-built
shape.

---

## 7. Concurrency model

### 7.1 What the crate sees

An `int` worker supplies the cluster's `SymbolTableAccess`, read-only
`SymbolTables` for other modules, the session's `ModuleAliases` and
`PreludeFallback`, and owns the per-call `CheckState`. The crate reads no session
or scheduler state and never waits; dependencies surface as `CheckError::Gap`.

### 7.2 Worker ordering

One worker per module is a scheduler-ordering rule, not a lock-safety
requirement: per-entry locks make concurrent mutation of one table safe. Mutual
imports are `int`'s to diagnose as a cycle (BC §6); typecheck neither detects
nor waits on them.

### 7.3 Gap-return contract

| Gap | Raised when | `int` response |
|---|---|---|
| `ResolutionGap::SymbolTypechecked(fq)` | An FQ value reference names a module not yet typechecked. | Typecheck that module, then retry the whole cluster. |
| `ResolutionGap::Type(fqt)` | An FQ type reference names a module not yet typechecked. | As above. |

Typecheck asks for `SymbolTypechecked`, not `SymbolInMemory`: it needs a scheme,
not compiled code, so a gap never waits on codegen. `ResolutionGap` is shared
with frontend, which alone raises `MacroInMem`.

### 7.4 Rollback

A failed cluster leaves no live mutation: `int` drops the staging table. The
type-variable counter is monotonic and deliberately not rolled back, so ids
minted by a failed attempt are abandoned rather than reused (BC §2 invariant 7).
There is no snapshot/restore primitive.

### 7.5 Guard discipline — hold one table guard at a time

`SymbolTables::get` hands out a per-shard `DashMap` guard; cluster staging hands
out a `RefCell` borrow. A lookup that follows a chain — an import hop, a trait
reference to its home, an import collection feeding a write — **clones the entry
out of the first guard, drops it, and only then takes the next.**

Two guards on one shard where one writes deadlock the process; a second borrow of
the staging table panics. Both need a particular module pair or cluster shape, so
a passing suite is weak evidence. Grade: **asserted with a named falsifier** —
nothing in the types prevents holding two guards; the falsifier is a hang or a
borrow panic on an unexercised crossing. `checker.rs::current_symbol_table`
rustdoc carries the rule where the guards are minted.

---

## 8. Error construction (Decision 39)

Every `CheckError::TypeError` carries an `ErrorLocation`.

### 8.1 Producer policy

| Field | Policy |
|---|---|
| `span` | Always, from the offending node (`Span::SYNTHETIC` for synthetic forms). |
| `file` | When the caller supplied it. |
| `fq` | When the error concerns a determinable definition; the formatter uses it to find the per-definition source. |
| `line_col`, `context` | Left `None`; the integration formatter resolves them. |

Batch output renders `file:line:col` from the span; the REPL uses `fq` for an
inline snippet. Warnings follow the same policy.

### 8.3 Type names in error messages

[REPL error presentation §5.3](../../repl/spec/05-error-presentation.md#53-type-error-quality-tested)
requires a type error to name the expected and actual types fully qualified.
Every type rendered into a typecheck message goes through the shared
`render_type` walk with `PrimitiveNaming::Qualified` (mismatch, rigid-variable
escape and occurs-check messages in `unify.rs`); "no impl" messages name the
canonical trait and the fully qualified impl type. The walk and its naming
conventions are `arch`'s
([bounded contexts §7 "Type rendering"](../arch/bounded-contexts.md#7-cross-crate-types-cratescranelisp-types));
do not add a local type printer.

---

## 9. Traits, monomorphisation and ADTs

### 9.1 Traits

- Typecheck emits `ResolvedCall::TraitMethod` for a trait-dispatched call,
  operators included. Where the resolved impl is a primitive operator
  (`Num.+` at `Int`, for example), typecheck substitutes
  `ResolvedCall::BuiltinFn` itself (`traits/dispatch.rs`), because backend has
  no trait knowledge (Decision 43).
- A trait method's single unresolved tail is classified once, at declaration
  registration, as a required return type or a default body
  (`TraitMethodKind`; `s116-method-signature-resolution.md`).
- An `impl` head resolves once to canonical trait identity; minting, keying,
  rollback and enrolment consume that settled product and never re-read the
  written spelling (`qualified-trait-impl.md`).
- `impl$` storage keys are minted only by `trait_impl_key`. The written-impl
  record is built from the values the impl shell is built from, inside
  `register_trait_impl`'s transaction, and upserts per `(type, trait)`
  ([trait implementation](traits.md#3-trait-implementation).0.1; `design/arch/trait-impl-cache-carrier.md`).

`traits.md` carries the subsystem; `hkt.md` the constructor-variable path.

### 9.2 Constraint propagation (Decision 19)

`generalize` collects trait constraints from active type variables into
`Scheme.constraints`. A constrained function is a template whose concrete bodies
are produced by call-site monomorphisation.

### 9.3 Monomorphisation

No non-concrete type reaches codegen under any reachable instantiation:

- A callable is a codegen target only as `Life::Concrete`; a non-concrete
  definition is `Life::Template` and carries no slot
  (`design/arch/symbol-table-lifecycle.md`;
  `design/backend/non-concrete-release-contract.md`). Typecheck consumes the
  settlement funnels and has no local slot gate
  (`non-concrete-producer-obligations.md`).
- Instances come from one reachable-instance worklist seeded from roots, keyed by
  the complete concrete substitution; each instance is named by the one encoder
  `InstanceLink::instance_key` (`monomorphisation.md` §3.3, §3.5;
  `result-context-specialization.md`). No second mangle grammar.
- A polymorphic product-accessor instance is re-synthesised from its template
  recipe, never produced by re-checking a body.
- A residual type in a codegen view may be defaulted only under the licence in
  `non-concrete-producer-obligations.md` §3.2; otherwise the ambiguity backstop
  refuses it at a located position (`monomorphisation.md` §4).
- Reload demands carry `Span::SYNTHETIC`; a stale demand declines to a warning
  (`monomorphisation.md` §3.8).

`CheckResult` carries no instance list: instances are ordinary concrete
callable bindings published through staging, and `MonoDefn` is a plain
`Defn` wrapper.

### 9.4 ADT typing

`TypeDefInfo`, `ConstructorInfo` and `FieldInfo` describe registered ADTs;
patterns infer by unification with nominal constructor resolution, and
exhaustiveness is checked in `adt.rs` (`adt.md`). Explicit type parameters and
field types are enforced by frontend before typecheck (`spec/05-definitions.md`
§5.2.4); typecheck adds no declaration-shape reject and owns only named-type
resolution. Product types generate accessors named canonically `Type.field`;
bare `field` is a candidate for that spelling, selected at each use
(`fixme-0365-field-accessor-dotted.md`); sum payload labels generate none.

### 9.6 Multi-signature definitions and auto-curry

A multi-signature `defn` produces one entry per signature. It is inference-
equivalent to its clauses as separate mutually recursive functions
(`spec/05-definitions.md` §5.1.2; `monomorphisation.md` §11), and each
constrained clause follows the ordinary template path. Private clause labels
select declarations; executable identity is the authored family plus its full
concrete signature. Auto-currying and its drain seams are in `auto-curry.md`.

### 9.7 Record from settled state (Principle 26)

Every span- or entry-keyed carrier this crate produces is derived once from the
state its settlement window guarantees, never recorded early and patched. The
typed resolution carrier (`typed-resolution-carrier.md` §14) is classified
in-window, with one standing, tripwired re-derivation (`overload_homes`,
`monomorphisation.md` §11.8.9). No typecheck producer writes a `var_refs` or
`apply_refs` entry at `Span::SYNTHETIC`.

The same classification over the rest of the producer surface — callees,
codegen views, pattern constructors, deferred self-call dispatch, scheme
write-backs — has not been done; it is the open typecheck leg of the
[Principle 24 register](../../tests/plan/s111-principle24-register.md), and
its seed is that register's written-name identity battery.

### 9.8 Module aliases

Typecheck follows `ModuleAliases`; it never populates them. Qualified-name
normalisation passes the referring module to `substitute_module_alias`; typecheck
never walks alias segments or spells an alias key itself, fixtures included
(`design/arch/module-alias-scoped-lookup.md`).

---

## 10. Document map

| Subject | Document | Standing |
|---|---|---|
| Inference and substitution | `inference.md` | Current |
| Use-site candidate selection | `use-site-candidate-selection.md` | User-approved; implemented |
| Checked-body ledger and publication | `checked-body-publication.md` | User-approved; implemented |
| Traits: registry, impls, dispatch, defaults | `traits.md` | Current |
| Method-tail classification | `s116-method-signature-resolution.md` | Implemented |
| Canonical trait identity at `impl` | `qualified-trait-impl.md` | Implemented |
| Higher-kinded traits | `hkt.md` | Current |
| Monomorphisation, reload demands, ambiguity backstop, multi-signature back-flow | `monomorphisation.md` | Current |
| Complete-substitution specialization identity | `result-context-specialization.md` | Implemented |
| Non-concrete producer obligations | `non-concrete-producer-obligations.md` | Current: the funnel, one instance identity, accessor re-synthesis and residual-parameter defaulting |
| Return-polymorphic dispatch signal | `return-poly-dispatch-signal.md` | Implemented (`CheckResult.unresolved_dispatch`) |
| Typed resolution carrier | `typed-resolution-carrier.md` | Implemented |
| `TypeExpr` resolver convergence | `type-expr-resolver-convergence.md` | Implemented |
| ADT typing | `adt.md` | Current |
| Field accessors | `fixme-0365-field-accessor-dotted.md` | Current |
| Dotted constructor registration | `dotted-ctor-registration.md` | Current |
| Auto-currying | `auto-curry.md` | Current |
| AST annotation model | `ast-annotation.md` | Current |
| IO typing | `io-types.md` | Current |
| Importable-symbol signature match | `signature-match.md` | Current |
| Ownership inference | `ownership-inference.md` | Current; governed by `design/arch/ownership-inference.md` |
| `render_type` byte table | `s87-fq-walk-consolidation.md` | Historical; held for §2.4 test anchors |

The `program/` and `traits/` cuts are §3.1 and the finalize ordering is
`monomorphisation.md` §3.3. Deleted records and where their content now lives
are listed in `design/typecheck/CLAUDE.md` §"Redirections".

---

## 11. Open design items

- **Principle 26 classification of the remaining producer surface** (§9.7).
- **Declaration-level forward reference within a cluster.** Spec §5.13.1 and
  §8.10.4 let non-macro definitions, including impls, reference types declared
  later in the cluster. Pass 1 registers in form order (§5.2 item 2), and
  `tests/spec_09_macros.rs::macro_expanded_begin_impl_neg_before_deftype_is_rejected`
  requires an impl expanded before its `deftype` to be rejected, citing spec §9.6
  and §8.2. The spec text and that test disagree, and this design takes neither
  side. `spec` owns the reconciliation and `qa` the intake; typecheck's design
  follows the ruling. (Source-read and test-read lead; not executed here.)
- Subject-level open items are in their subject documents: [trait open items](traits.md#11-open-items) and
  `inference.md` §6, for example.
