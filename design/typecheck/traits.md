# Traits — typecheck interior

Owner: `design` narrow-deployed to typecheck. Subordinate to
[`typecheck.md`](typecheck.md) §9.1. It covers trait declarations, impls,
default methods, constrained polymorphism and method dispatch.

Required behaviour is `spec/07-traits.md`. This document uses the following
neighbouring authorities without restating them:

| Subject | Authority |
|---|---|
| Symbol-table declaration vocabulary (`Binding`, `Decl`) and lifecycle funnels | `design/arch/symbol-table-lifecycle.md` |
| Writer-side impl record, the record/shell bijection and enrolment | `design/arch/trait-impl-cache-carrier.md` |
| Canonical trait identity at `impl` slot 1 | [`qualified-trait-impl.md`](qualified-trait-impl.md) |
| Method-tail classification (required return or default body) | [`s116-method-signature-resolution.md`](s116-method-signature-resolution.md) |
| Higher-kinded declarations, the impl kind check and HKT dispatch | [`hkt.md`](hkt.md) |
| Monomorphisation of constrained templates | [`monomorphisation.md`](monomorphisation.md) |
| Selecting one declaration from a contested bare spelling | [`use-site-candidate-selection.md`](use-site-candidate-selection.md) |

---

## 1. Where trait state lives

### 1.1 No registries

The checker is `TypeCheckEnv` plus `CheckState` (`typecheck.md` §3.1, §7.1):

- `TypeCheckEnv` borrows shared state: the type-variable counter, the per-module
  tables, the cluster's staging, `ModuleAliases` and `PreludeFallback`.
- `CheckState` is per-cluster transient state.

Neither holds a trait or impl registry. Trait declarations, method declarations
and impl shells are declarations in the module tables, reached by per-symbol
chain-follow (Principle 17). Only the transient `active_constraints` (§1.5) rides
`CheckState`.

### 1.2 Trait declaration

`Decl::Trait(TraitRecord)` sits under the trait's name in its defining module.
The record carries the resolved `TraitDeclInfo` (name, head type parameters and
classified method signatures) and the docstring. The binding carries the trait's
visibility.

### 1.3 Impl shell at the trait's home (Decision 45)

- **Placement.** An impl's discovery shell, `Decl::ImplShell`, is written to the
  **trait's defining module**, not the writer's. The write target comes from the
  canonical trait identity resolved at slot 1.
- **Key.** The shell is stored under `trait_impl_key(impl_type, trait)`
  (`impl$<FQTypeName>$<FQTraitName>`). `trait_impl_key` is the only construction
  of that key, for both registration and the dispatch-side probe.
- **Contents.** The trait, the implementing type, `impl_module` (the writer, where
  the method definitions live) and the method storage keys.
- **Discovery.** To answer "does `(Trait, Type)` have an impl", follow the chain to
  the trait's home and probe that one key. There is no universe scan and no
  closure walk.
- **Visibility.** Shells are always public (spec §5.11.1). Impl coherence is
  global.

### 1.4 Method declarations

Each trait method is a `Decl::TraitMethod(TraitMethodRecord)` in the trait's
defining module. The record carries the method's constrained scheme, its
parameter names, its docstring and the owning `FQTraitName`. It has the trait's
visibility, so a private trait does not export its operators through the prelude
fallback.

"Which trait owns `m`" means: resolve `m` and read the record's `trait_name`.
That name's module is the trait's home, so `method_to_trait_with_state` returns
the trait together with its home. When a bare spelling names several canonical
declarations, use-site selection settles it first, and
`try_resolve_selected_trait_method` dispatches from the selected record without
re-resolving the spelling.

### 1.5 `ActiveConstraints`

`CheckState.active_constraints` maps type variables to the traits they must
implement while a cluster is inferred:

- entries are added when a constrained scheme is instantiated
  (`instantiate_constrained`) and when a written `:C x` parameter is registered
  (`resolve_bound_param`);
- `generalize` reads it (§6);
- adding an existing `(variable, trait)` pair changes nothing;
- it lives exactly as long as its `CheckState`, which is one cluster. It is not
  cleared between forms, because a later generalisation needs earlier
  constraints.

The test-only `clear_transient_state` resets it after a synthetic world is set up.

### 1.6 The `traits/` module layout

The cut and its visibility rule are in [`typecheck.md` §3.1](typecheck.md#31-module-map).
Each submodule owns one concern:

| Submodule | Concern |
|---|---|
| `traits/mod.rs` | hub: submodule declarations, crate-internal re-exports, `mangle_trait_method` (§3.1) |
| `traits/registry.rs` | write side: a declaration becomes symbol-table state; `ActiveConstraints` |
| `traits/impl_check.rs` | impl recording and method-body checking, including HKT impl methods and default generation |
| `traits/dispatch.rs` | read side: which impl a call resolves to, including dispatch-argument selection for HKT and nullary return-type dispatch |
| `traits/monomorphise.rs` | the instance engine (`monomorphisation.md` §3.9) and `concrete_type_name` |
| `traits/type_resolve.rs` | impl-target, declaration-identity, occurrence and constructor-variable predicates |

Two cohesion rules keep future edits from scattering related logic:

- A dispatch-argument-selection helper lives in `traits/dispatch.rs` beside
  `try_resolve_trait_method`, its caller.
- The bulk trait-declaration scan `find_trait_method_decl` is the one place that
  applies the prelude fallback and its public-head filter to a method-name search.
  It answers "which visible trait declares this method", not a name resolution, so
  it is not folded into the scope resolver. Its result keeps "method absent"
  distinct from "method present with no HKT index".

Each submodule has its own sibling test module (`traits/<unit>/tests.rs`), and `traits/test_helpers.rs` holds the
shared test helpers. Maintainability watch items are in `typecheck.md` §3.2.

## 2. Trait declaration

```clojure
(deftrait Eq
  (= [a b] Bool)                           ;; required: the tail is the return type
  (!= [a b] Bool (not (= a b))))           ;; default: the tail is the body
```

`register_trait_decl` (Pass 1, `typecheck.md` §5.1) runs these steps in order:

1. **Same-module identity probe.** A raw probe of the current module's table, with
   no chain-follow and no prelude hop, asks whether this module already declares
   the trait. Cluster orchestration can retry a module from the top, so an
   identical re-submission is a no-op. A different declaration under the same name
   in the same module is rejected (spec §7.1). The probe answers identity only. A
   trait sharing a spelling with an import, export or prelude binding is a
   distinct candidate, not a conflict (`spec/08-modules.md` §8.6.4;
   `typecheck.md` §3.3).
2. **Method classification.** Each method's single unresolved tail is classified
   once, as a required return type or a default body (s116).
3. **Kind from the head, decided once.** A parenthesised head is higher-kinded if
   and only if its constructor variable is applied somewhere in the method
   signatures. A parenthesised head whose variable is never applied is rejected
   here, with a message naming the bare-head `self` form. A higher-kinded trait
   may not have a default body (spec §7.12.1). Higher-kinded traits continue in
   `register_hkt_trait` ([HKT kind derivation](hkt.md#51-kind-derivation-at-declaration-consumers-read-type_params)). Every later consumer reads the kind from
   `type_params` alone (Principle 24).
4. **Occurrence rule** for conventional traits (below).
5. **Write.** One fresh variable stands for the implementing type, and every
   method shares it. Each method's scheme quantifies that variable, constrained to
   the trait. The method records are installed first, then the trait binding.

**Signature types.** Method signatures resolve through the one `TypeExpr`
resolver, via the trait-signature wrapper on `TypeCheckEnv`
(`type-expr-resolver-convergence.md`). `self` and every bare parameter map to the
shared implementing-type variable. A written variable that is not the trait's
parameter is a fresh method-local variable, co-referring within its signature.

### Occurrence-rule enforcement

Required by spec §7.1.1. In a conventional (bare-head) trait, every method
signature must mention the implementing type at least once. An occurrence is any
of:

- a bare parameter;
- a `:self`-annotated parameter;
- `self` as the return type.

The frontend lowers all three to `TypeExpr::SelfType`, so the single predicate is
`type_resolve::method_mentions_self`. It runs per method in the conventional
branch of `register_trait_decl`, before anything is written. The HKT branch has
already returned by then, so the §7.2 exemption is structural rather than a flag.

- **Reject only the conjunction:** no parameter occurrence and no `self` return.
  Neither a concrete return type nor an empty parameter list is a reason to
  reject. `(size [x] Int)` and `(zed [] self)` are accepted;
  `(cvt [:String s] Int)` and `(zed [] Int)` are rejected.
- **Declaration versus use.** A well-formed method's dispatch and no-impl errors
  are raised at use (§7). Only the no-occurrence form is rejected at declaration.
  That also stops such a method from ever reaching codegen as an undefined
  function.
- **Diagnostic.** The message names "no occurrence of the implementing type to
  dispatch on". It is distinct from the HKT "not a type constructor" rejection
  and from the never-applied-head rejection in step 3.
- **Unit tier.** Tests vary the definition along each axis: parameter versus
  return occurrence, required versus default, nullary versus non-nullary, nested
  type expressions, and conventional versus HKT.

## 3. Trait implementation

Slot 1 of `impl` is a trait reference. It resolves once to a canonical
`FQTraitName` and `TraitDeclInfo`, and every later step consumes that product
(`qualified-trait-impl.md`). No step mints from the written spelling or
re-resolves the bare name.

### Registration pipeline

`register_trait_impl` runs in Pass 1 (`typecheck.md` §5.1):

1. **Resolve the trait** from slot 1 (above).
2. **Kind check** (`hkt.md` §5.4). Slot 1 must echo the declared head shape and,
   for a higher-kinded trait, the constructor-variable spelling. For a
   conventional trait over an ADT, the target must be applied to exactly the
   type's declared arity. Under- and over-application each have their own
   diagnostic.
3. **Field-accessor overlap.** Spec §7.3.1 permits an impl method whose name
   equals a field accessor of the target type. The method and the accessor stay
   distinct canonical declarations
   ([`fixme-0365-field-accessor-dotted.md`](fixme-0365-field-accessor-dotted.md) §2).
   As built, `check_impl_method_accessor_collisions` still rejects such an impl
   before anything is written. That rejection is obsolete. Its defect intake is
   `ACT-0983`, and its removal is §2.1 of the same document.
4. **Completeness.** Every method without a default must be provided
   (`check_impl_methods_present`).
5. **Target identity, resolved once.** The effective target resolves to one
   `FQTypeName`, which every impl-method symbol below uses. For a higher-kinded
   impl this is the bare constructor.
6. **Default methods** (§4).
7. **Stage the carriers** (§3.0.1).
8. **Check method bodies.**
   - Each trait reference in the target's constraint slot (`(Box :Disp a)`)
     resolves through `resolve_trait`. An unknown trait is `TraitNotFound`, for
     every impl kind.
   - `Self` is seeded to the concrete target and each signature resolves against
     it. Arguments of a polymorphic target bind as variables (§3.2).
   - The body is checked by `check_defn_body_with_types` (`inference.md` §4.3).
   - The mangled method definition is written back through
     `finalize_impl_method_writeback`, the tail shared by the conventional and
     HKT paths.
   - A body error restores both staged carriers.
9. **Return** the generated default definitions to Pass 1 (`typecheck.md` §5.2
   item 2).

### 3.0.1 The writer-side record

The cross-crate contract is `design/arch/trait-impl-cache-carrier.md` §§3–4. This
crate decides only where the record is staged: exactly where the shell is.

- **Values.** The record clones the trait, target, writer module and method names
  that the shell is built from. They are resolved once and nothing is re-parsed:
  one derivation feeds two carriers (Principle 24).
- **Tables.** The shell lands in the trait's home; the record lands in the
  writer's own table (`state.current_module` at that point).
- **Transaction.** Both carriers are staged at the same point, both retain their
  prior value, and both are restored on the method-check error arm. A record
  without its shell breaks the bijection that enrolment hard-errors on
  (Principle 26).
- **Identity.** A re-impl of the same `(type, trait)` (spec §5.4.5) replaces its
  record and never appends a second one.
- **Funnels.** Staging and restoration use the lifecycle funnel vocabulary
  (`design/arch/symbol-table-lifecycle.md`), never raw table writes.

### 3.1 Mangling — `mangle_trait_method`

```
{TraitName}.{method}${FQTypeName}        e.g. Num.+$primitives/Int, Describe.describe$a/Widget
```

- **Home-qualified type.** The suffix is the home-qualified type head. Two
  same-named types from different modules are distinct (spec §3.8.4), and a bare
  head would collapse them onto one linker symbol (Principle 20).
- **One mint on both sides.** Dispatch (`try_resolve_trait_method`) and every
  definition site (explicit, HKT and default methods) mint through
  `mangle_trait_method` against the same `FQTypeName`. The definition side uses
  the target resolved once at registration. The dispatch side takes the type from
  the resolved argument's own type (`fq_type_for_dispatch_mangle`) and never
  re-resolves a bare head in the caller's module.
- **Grain is the receiver head.** Type arguments are not part of the suffix, which
  matches impl registration's grain. `Vec Int` and `Vec String` share a head.

### 3.2 Polymorphic conventional targets

A conventional impl over a polymorphic target such as `(Option a)` or
`(Option :Disp a)` is admissible (spec §7.3.5 Case 1, §7.3.3). It registers one
polymorphic impl, and dispatch on a concrete `(Some 3)` finds it.

- The target's **arguments** resolve through the shared annotation resolver,
  using the same variable map as the method signatures. So a target `a` is a type
  variable that co-refers with a like-named signature variable (spec §3.3.1), and
  a concrete argument resolves as usual.
- The target's **head** keeps `concrete_type_for_impl_target`. That path carries
  the §7.3.5 Case-3 rejections (a primitive as an HKT target, arity mismatch),
  which routing the whole target through the general resolver could loosen.

## 4. Default methods

- A default body is the declaration's parsed body (`TraitMethodKind::Default`).
- For each default the impl omits, `generate_default_methods` mints the mangled
  name (§3.1) and returns a `Defn` with that body. A method the impl provides
  wins.
- The defaults are registered after the Pass-1 sweep and checked after the Pass-2
  sweep (`typecheck.md` §5.2 item 2). After that they are ordinary definitions.
- Higher-kinded traits have no default methods (§2 step 3).

`build_default_body`'s hard-coded `Eq`/`Ord` bodies cannot be reached from this
path; see §11.

## 5. Core traits

- **Ordinary source.** The core traits and their primitive impls (`Num`, `Eq`,
  `Ord`, `Display` and others) are standard-library source under `stdlib/`. They
  are checked through `check_forms` like any user module, with no special
  registration path. The optional-prelude principle holds: typecheck needs no
  trait to exist.
- **Test world.** In-crate tests build a synthetic world through the same
  `register_trait_decl` and `register_trait_impl` seams
  (`checker/test_support.rs`, `program/test_support.rs`). `builtins.rs` is
  test-only.

## 6. Constrained polymorphism

A function is constrained-polymorphic when its generalised scheme carries
constraints: `(defn add [x y] (+ x y))` has the scheme
`∀a:Num. (Fn [a a] a)`. It is a template, and its concrete bodies come from
monomorphisation (`typecheck.md` §9.2–§9.3).

`Scheme.constraints` maps quantified variable ids to the traits they must
implement. Constraints propagate in three stages:

- **Instantiation.** `instantiate_constrained` maps each quantified variable to a
  fresh one and records the fresh variable's traits in `active_constraints`.
- **Unification** binds variables in the substitution. It does not move
  constraints.
- **Generalisation.** `generalize` resolves each `active_constraints` entry
  through the substitution. A constraint recorded on `X`, where `X` resolves to a
  quantified `Y`, attaches to `Y`. The per-trait lists are deduplicated, because
  several variables can resolve onto one.

### Detection

- **Eager.** After each body, a trial generalisation decides the definition's
  state. An unconstrained scheme is written back at once (`inference.md` §3). A
  constrained definition is recorded as constrained, and `detect_constrained_fns`
  later reads its `Life::Template { kind: TemplateKind::Constrained(_) }` state
  from the table rather than a parallel marker.
- **Final.** Finalize regeneralises every definition after all bodies. A
  definition whose final scheme has no constraints, because later call sites
  pinned its variables, settles concrete (`monomorphisation.md` §3.3 step 1).
- **Re-resolution.** `resolve_deferred_trait_calls` then retries calls that were
  unresolved when first seen ([method resolution](#7-method-resolution)).

## 7. Method resolution

`try_resolve_trait_method` runs in `infer_apply`. It returns a `PendingDispatch`:
either a resolved `ResolvedCall` recorded at the `Apply` span, or nothing, in
which case resolution is deferred.

1. **Owning trait and home.** Resolve the method's record (§1.4). A name that is
   not a trait method is not dispatched here.
2. **Dispatch argument.** Use the method's `hkt_param_index` (`hkt.md`), otherwise
   argument 0. With no argument at that position, a method whose signature
   returns `self` dispatches on the call's recorded return type. Any other
   signature defers.
3. **Concrete type.** `concrete_type_name` of the resolved dispatch type. The
   scalars and ADTs have one; a variable or function type returns `None`, and
   the call defers.
4. **Impl lookup at the trait's home.** `has_impl_in_home` probes the shell key
   (§1.3). A concrete type with no impl is the located error
   `no impl of trait <FQ trait> for type <FQ type>`.
5. **Primitive short-circuit.** A `(trait, method, type)` in
   `primitive_for_trait_method`'s table becomes `ResolvedCall::BuiltinFn`, and
   backend inlines it. Backend has no trait knowledge (Decision 43), so the table
   lives here. See §11 for how it is keyed.
6. **Otherwise** build `ResolvedCall::TraitMethod`:
   - the trait: its canonical name at its home;
   - the implementing type: an ADT's own `FQTypeName`, or a scalar resolved in the
     trait's home;
   - the mangled symbol (§3.1);
   - `impl_module`, read from the shell. Consumers read it and never re-derive it.

**Deferred resolution.** A call whose dispatch type is still a variable has no
entry. `resolve_deferred_trait_calls` walks a body and retries each trait-method
`Apply` that has no resolution, reading argument types from the substitution-
applied `expr_types` rather than re-inferring. It runs after each body, again in
finalize over every body, and inside impl-method and monomorphisation rechecks.
A call still unresolved in a template body resolves when an instance is
rechecked.

### 7.0.1 Dispatch roots at the method's home (spec §7.11.2)

Importing a method without its trait is enough to dispatch it. A method
reference carries its trait's canonical identity, and that identity names the
trait's home, so every step above roots at that home and none re-resolves a
bare trait name in the caller's scope:

- the impl lookup (`has_impl_in_home`);
- the `FQTraitName` in the resolved call;
- the declaration scan behind `method_self_in_return` and `hkt_param_index`,
  which reads the method from its own trait at that home (`find_trait_method_decl`
  with a trait filter);
- constraint verification during monomorphisation (`verify_constraints`).

The dispatch type follows the same rule. An ADT argument supplies its own
`FQTypeName`: a user ADT that implements a prelude trait keeps its impl in the
user's module, so rooting it at the trait's home would miss it. A scalar has no
embedded home and resolves in the trait's home, which reaches `primitives`.

The same rule has three consequences:

- **Diagnostics name the owning trait** even when it is out of scope (spec
  §7.11.2(c)), because the trait is on the record.
- **Declaring an impl still needs a resolvable trait reference** (spec
  §7.11.2(d)). Slot-1 resolution (§3) is a different seam, and importing a
  method does not license a bare `(impl T …)`.
- **Two same-named imported methods are candidates** (spec §7.11.2(b)). Use-site
  selection settles which one a use denotes before dispatch (§1.4). Import order
  never selects a method.

A resolution product that carries FQ identity must not be narrowed to a bare
name past its seam: resolve once, then carry the identity (Principle 24).

## 8. Monomorphisation

`monomorphisation.md` is the subsystem design. This section records only what
the trait subsystem contributes to it.

- **Collection and driver.** `program/mono_collect.rs::pass4_monomorphise` runs in
  the settlement windows of `monomorphisation.md` §3.3 and derives one complete
  `MonoDemand` per use. Instance identity is the demand's `InstanceLink`
  (`monomorphisation.md` §3.5), not a trait-side mangled key.
- **Engine.** `traits/monomorphise.rs::monomorphise_call` instantiates one template
  from a demand. Its phases and the state channels they preserve are in
  `monomorphisation.md` §3.9. The ambiguity backstop refuses a non-concrete
  instance body (`monomorphisation.md` §4).
- **Cross-module scoping.** An imported template is rechecked in its defining
  module and verified through the instantiation's variable map, and impl lookup
  roots at the trait's home (`monomorphisation.md` §3.7).
- **Output.** An instance is an ordinary concrete entry in the caller's module,
  and its codegen view rides the entry. `MonoDefn` is a plain `Defn` wrapper
  (`monomorphisation.md` §3.6).
- **REPL.** REPL input takes the same `check_forms` path. There is no separate
  REPL monomorphisation pass.

## 9. Multi-signature definitions

Multi-signature definitions are `monomorphisation.md` §11:

- a call that selects a clause records `ResolvedCall::SigDispatch`;
- a clause that calls trait methods is its own constrained template, reached
  through the drain (§11.4). Its constraint stays on that template entry's
  scheme, which is what displays read;
- the importable-symbol predicates are `signature-match.md`.

## 10. Invariants

Violating any of these is an implementation bug.

**Storage and registration**

1. **Dispatch reads settled identity.** A trait-method use reaches dispatch as one
   canonical `TraitMethodRecord`, either because its spelling resolves uniquely or
   because use-site selection chose it. Dispatch reads the trait and its home from
   that record (§1.4, §7.0.1).
2. **Idempotent re-registration.** `register_trait_decl`'s same-module probe
   answers identity only. An identical re-submission is a no-op, and a different
   same-module redeclaration is rejected (§2 step 1).
3. **Impl completeness.** Every impl provides every non-default method.
4. **Impl type-correctness.** Every impl method body checks against the trait
   signature with `Self` set to the concrete target.
5. **Decision-45 placement.** A shell lives in the trait's defining module under
   `trait_impl_key`. Discovery probes that one key. The method definitions live
   in the writer's module, and the shell's `impl_module` points there.

   5a. **Record and shell in bijection.** At every commit boundary, the writer's
   records and the shells its registration wrote are in bijection, with at most
   one record per `(impl_type, trait)` per writer
   (`design/arch/trait-impl-cache-carrier.md` §3).
6. **Record consistency.** A `TraitMethodRecord` names a trait whose declaration
   exists at that home and declares that method.

**Constraints**

7. After generalisation, every `Scheme.constraints` key is one of the scheme's
   quantified variables.
8. `active_constraints` is not cleared between forms within a cluster.
9. `generalize` resolves constraints through the substitution before attaching
   them.

**Monomorphisation**

10. **Templates are not compiled.** A constrained definition is
    `Life::Template` and carries no slot. Only concrete instances reach codegen
    (`typecheck.md` §9.3).
11. **Per-instance views.** Each instance's body view rides its own entry, never
    a program-wide map.
12. **One instance per identity.** Uses with the same complete substitution share
    one instance (`monomorphisation.md` §3.5).
13. **Mangle lock-step.** Dispatch and definition mint through the one
    `mangle_trait_method` against the same `FQTypeName` (§3.1).

    13a. **Canonical trait identity lock-step.** Every impl method (explicit,
    default and HKT) and every re-impl enrolment and finalisation lookup mints
    from slot 1's one resolved `FQTraitName`. Source qualification is never part
    of a method symbol and is never re-resolved after the impl seam.

**Resolution**

14. **Span-keyed resolutions.** A resolution is keyed by its `Apply` span, and each
    span has at most one. A span with no resolution is an ordinary call.
15. **Deferred completeness.** After finalize's `resolve_deferred_trait_calls`,
    every trait-method call with a concrete dispatch type has a resolution. Calls
    with a variable dispatch type are template-body calls, resolved in instance
    rechecks.

**Provisioning**

16. **One registration path.** Core traits and user traits use the same
    `register_trait_decl` and `register_trait_impl` seams (§5).

## 11. Open items

- **Impl-method accessor rejection.** The rejection in §3 step 3 is obsolete.
  Intake is `ACT-0983`, and the removal design is
  [accessor/impl overlap obligation](fixme-0365-field-accessor-dotted.md#21-unresolved-obligation--the-source-still-rejects-the-overlap).
- **Dead default-body fallback.** `generate_default_methods` skips every method
  without a parsed default body before its hard-coded fallback runs, so
  `type_resolve::build_default_body` is reachable only from its own tests. The
  production `stdlib/compare/eq.cl` declares `!=` as required. Retire the helper
  and its tests (`dev`, typecheck). This finding comes from reading the source.
- **The primitive short-circuit is keyed by bare names.** The table in
  `primitive_for_trait_method` (§7 step 5) matches the bare trait, method and type
  names. It ignores the trait's home and the selected impl. A trait named `Num`
  declared in any module, with an `Int` impl of `+`, would dispatch to `add-i64`
  and silently skip the written body; a type named `Int` in another module would
  match too, because `concrete_type_name` returns only the ADT's bare name. That
  contradicts canonical identity (Principle 19; spec §3.8.4 and §7.11.2). This is
  a source-read lead that has not been executed. `qa` takes intake and decides on
  a discriminating repro; if it is confirmed, the fix keys the table on the
  canonical trait and type (`dev`, typecheck).
- **Constraint rigidity in impl-method bodies:** `inference.md` §6.

## 12. Cross-references

- `design/typecheck/typecheck.md` — master design (this document is subordinate).
- `design/typecheck/monomorphisation.md` — the instance engine, settlement
  windows, cross-module scoping and multi-signature definitions.
- `design/typecheck/qualified-trait-impl.md`, `hkt.md`,
  `s116-method-signature-resolution.md`, `use-site-candidate-selection.md`,
  `fixme-0365-field-accessor-dotted.md` — the neighbouring subjects listed at the
  top.
- Sources: `crates/cranelisp-typecheck/src/traits/`; `checker.rs`
  (`method_to_trait_with_state`, `has_impl_in_home`, `generalize`);
  `program/register.rs`; `program/mono_collect.rs`.

---

## Former section numbers

| Former | Now |
|---|---|
| §1.1–§1.5 (registry-free model, `ModuleEntry::TraitDecl`, `ModuleEntry::TraitImpl`, `trait_origin`, `ActiveConstraints`) | §1.1–§1.5, restated in the current `Decl` vocabulary |
| §2 "Registration pipeline" (the name-freedom gate) | §2 step 1. There is no name-freedom gate; sharing a spelling is not a conflict |
| §3 "Sprint 117 — slot 1 is resolved once" | §3, introduction |
| §3.2 TB-24 (poly-applied target) and TB24b (constraint slot) | §3.2; the constraint slot is §3 step 8 |
| §5 "12 core impl registrations" | Removed. The core traits are standard-library source (§5) |
| §7.0.1 D2 | §7.0.1 |
| §7.0.2 D1 (constraint display for multi-signature clauses) | §9. Displays read the clause template's scheme |
| §7 "ResolvedCall", "`primitive_for_trait_method`", "`concrete_type_name`" | §7 steps 3, 5 and 6 |
| §9 "Known interaction limit" (multi-signature with constraints) | Resolved; `monomorphisation.md` §11.4 |
| §11 "Evolution notes" | §11 "Open items". The former follow-ups have landed or were withdrawn |
