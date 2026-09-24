# Concrete codegen boundary

**Owner:** `arch`. **Status:** current contract — delivered. The S84 phased plan that
introduced it is in Git history.

This document states what crosses the typecheck→backend boundary as a typed body, and why.
[Bounded contexts](bounded-contexts.md) §2 (invariant 12) and §3 (invariant 9) summarise it.
[Total concreteness](total-concreteness.md) owns the wider end-of-typecheck invariant, and
[symbol-table lifecycle](symbol-table-lifecycle.md) owns the callable states named here.
Exact signatures are source rustdoc in `crates/cranelisp-types/src/concrete.rs` and
`crates/cranelisp-types/src/mono_expr.rs`.

Section numbers are stable because source and test comments cite them. A retired number
(such as 2.1) is not reused.

## 0. The ruling

> **User, 2026-06-16:** "The main goal is to remove passing generics to the backend — they
> shouldn't even be REPRESENTABLE [there]."

- The boundary carries a type with no variable case, so a generic is unconstructable at
  codegen rather than rejected by a downstream check
  ([Principle 18](principles/18-enforce-invariants-structurally.md),
  [Principle 20](principles/20-model-invariants-by-representation.md)).
- The ruling has two halves, and neither suffices alone:
  1. a concrete-only boundary type (§1);
  2. no generic body is ever a codegen input — only its concrete instances are (§2).
- Rationale retained: before this boundary, four behavioural guards (a debug assertion, the
  ambiguity scan, a classification panic and the slot gate) each tried to prove that a
  representable-but-illegal state never occurred. Arming one of them fired 317 times on the
  valid prelude, because generic bodies were being compiled once as uniform-word templates.
  Do not reintroduce a template fallback or a variable arm to make a failing case compile.

## 1. The boundary type — `ConcreteType`

### 1.1 Name and location

`ConcreteType` lives in `crates/cranelisp-types/src/concrete.rs`. The name states the
property (fully concrete), not a producing process or a consumer.

### 1.2 Shape

- Variants: `Int`, `Bool`, `String`, `Float`, `Fn(params, result)` and `ADT(FQTypeName, args)`.
  There is no `Var` and no `TyConApp` variant.
- The recursion is on `ConcreteType`, so concreteness holds at every depth.
- It derives `Eq` and `Hash`, which `Type` cannot (inference variable ids are unstable across
  runs). It is therefore a stable key for instance identity and drop-glue maps.
- Variants stay public and directly constructible: exhaustive backend matching over the closed
  sum is the safety feature, and sealing them would force wildcard arms. Fabrication is
  controlled by census, not by a constructor gate — see §3.1.1 and
  [safety invariants](safety-invariants.md) row R18.

### 1.3 The fallible conversion

- `ConcreteType::from_type(&Type) -> Result<ConcreteType, NotConcrete>` is the only conversion
  from `Type`. It succeeds iff the type is fully concrete.
- `NotConcrete::Var` is a residual inference variable; `NotConcrete::HktHead` is an unresolved
  higher-kinded head.
- The failure is one fact — *this position's type is not concrete* — that previously surfaced
  as three separate errors: the spec §3.11.1 ambiguity error, "could not monomorphise here",
  and a heap-classification panic.
- `ConcreteType::to_type` is the total inverse embedding.
- `ConcreteType::result_root` strips one `primitives/IO` head. It is the single derivation of
  the program-result root; the backend’s result-root enumeration and the binary’s release
  key both call it.

### 1.4 The check is full concreteness

- Spec §3.11.1 requires full concreteness with no representation-based exemption. An unpinned
  `(Vec a)`, `(Fn [a] a)`, `(Option a)` or `[]` at a codegen-reaching value position is a type
  error even though its machine shape is determinate.
- One verdict serves both sides (Principle 7). `Type::is_concrete()` equals
  `ConcreteType::from_type(..).is_ok()`; the pin is
  `crates/cranelisp-types/src/concrete/tests.rs::from_type_agrees_with_is_concrete`.
  Typecheck's ambiguity scan returns `!is_concrete()`
  (`crates/cranelisp-typecheck/src/program/finalize/ambiguity.rs::is_codegen_ambiguous_type`),
  so the check rejects exactly what the boundary cannot represent.
- The scan visits codegen-reaching value positions only. It does not fire at a callee
  dispatch position, at a named polymorphic definition whose free variables are result-only
  (a slot-free template), or for a bare polymorphic value displayed at the REPL.
- A direct constructor value is not exempt: `(is-some None)` with `None` unpinned is ambiguous.
  The user's escape is an annotation, `(is-some :(Option Int) None)`, so annotation resolution
  of built-in type constructors such as `Vec` is part of this contract.
- Acceptance pins in `tests/regression.rs`: `mono_vec_free_var_value_rejected_neg`,
  `mono_fn_free_var_value_rejected_neg`, `mono_is_some_unannotated_none_rejected_neg`,
  `mono_vec_empty_annotation_pins_and_compiles_pos` and
  `mono_bare_annotated_value_pins_and_compiles_pos`.
- The former representation-determinacy predicate is deleted. Do not reintroduce a predicate
  that admits a type because its layout happens to be known.

## 2. Only concrete instances reach codegen

### 2.2 Templates are monomorphisation sources

- A non-concrete callable settles as `Life::Template`, which has no slot and no view.
  Constrained and parametric templates are symmetric (`TemplateKind`); they differ only in
  how their variables are pinned.
- `SymbolTable::codegen_targets()` is the single codegen-eligibility projection, shared by the
  backend and the binary's workers. It yields only a concrete body realization, so a template
  is excluded by lifecycle shape, not by a kind-exclusion list.

### 2.3 Enumeration

- Instances are the reachable closure from the program roots: `main`, discovered tests,
  concrete top-level values, and every concrete instantiation that reachable call sites demand.
- Deduplication is by instance identity
  ([instance identity funnel](interfaces.md#instance-identity-funnel)). Termination rests on
  rank-1 monomorphic recursion plus that set.
- There is no template to fall back to. A missed instance is a missing callable or the
  ambiguity error, which is what forces enumeration to be complete.

### 2.4 `MonoExpr` — the typed body view

- `MonoExpr` is a parallel post-monomorphisation AST. Every node carries `ty: ConcreteType`
  non-optionally and no node has a `Type` field.
- Rejected alternatives, retained because each is a plausible future shortcut: replacing
  `Expr`'s inference annotation in place (one field cannot hold both the inference-stage and
  the concrete type), and adding a parallel optional concrete field on `Expr` (the node would
  still hold a `Type`, so the guarantee degrades to a reading convention).
- Carried beside the type: the node span; the typed resolution carriers `VarRef` and
  `ApplyRef` ([method resolutions](interfaces.md#method-resolutions)); `resolved_call`
  dispatch metadata; match-arm `resolved_ctor`
  ([constructor keys](dotted-ctor-canonical-keys.md)); and advisory ownership site facts
  ([ownership inference](ownership-inference.md)).
- Erased at build: `Annotate` nodes and parameter `TypeExpr` annotations. Their constraints
  are discharged before the view exists; a lambda's `ConcreteType::Fn` carries its parameter
  types.
- `MonoDefnVariant` wraps a name, parameters, a `MonoExpr` body and a span. `MonoExpr` has no
  `PartialEq`, because float literals do not.
- **The mono-population seam.** Typecheck is the sole view producer.
  `MonoExpr::from_expr(expr, pattern_ctors, var_refs, apply_refs)` runs after the body's types
  are substitution-resolved. It reads the resolution verdict before the node type, so a
  missing verdict is `ViewBuildError::Unresolved` and never degrades into the type error. An
  un-annotated node fails as a non-concrete one does.

### 2.5 Prelude and library generics are on-demand roots

- The prelude is type-checked and its templates are available as sources, but a generic body
  is compiled only as the concrete instances a program reaches. Fully monomorphic prelude
  functions are concrete and compiled once.
- **Cache-schemes-without-codegen.** A module whose only definitions are uninstantiated
  generics has metadata to persist and no object code. Metadata persistence follows the
  typecheck result, not the presence of an object, and the loader accepts a metadata-only
  module. A downstream module compiles the instances it reaches into its own object. Pin:
  the generic-only cached-module test in `src/scheduler/tests.rs`.

### 2.6 First-class generic values

A generic referenced as a value is monomorphised at the use site's expected type. If nothing
pins it, the conversion fails at that position and the user sees the ambiguity error. There
is no special case.

### 2.7 Constrained polymorphism

Trait-constrained and plain parametric templates take one path: neither is a codegen target,
and both specialise to concrete slotted instances per reachable use. An asymmetry between
them was the original leak; treat any new one as a defect.

## 3. Carrier and backend consumption

### 3.0 Where the view lives

- The view is non-optional state of the concrete lifecycle. `CallableArmSettlement::ConcreteBody`
  supplies it at settlement and `Realization::Body { view, code }` holds it
  (`crates/cranelisp-types/src/lifecycle.rs`). A body-realized concrete callable without a
  view is unconstructable, so there is no missing-view backstop.
- The view is on the declaration rather than a separate argument to codegen because the
  symbol table is the per-symbol codegen input (Principle 7). It serialises with the
  declaration; the compiled-code owner beside it is runtime-only.
- Settlement is atomic across scheme, source body, view, callees and slot
  ([symbol-table lifecycle](symbol-table-lifecycle.md)).

### 3.1 Backend consumption

- `compile_to_module` receives `CallableTarget`s and walks `MonoExpr`; every type it reads is
  `MonoExpr::ty()`.
- `HeapCategory::classify` (`crates/cranelisp-backend/src/heap.rs`) takes `&ConcreteType` and
  is total, with no variable arm and no panic case.
- The user-facing ambiguity diagnostic stays in typecheck. The backend carries no scan of its
  own for the same fact.

### 3.1.1 Signature-driven targets

- Constructor and accessor bodies are synthesised and typed by the declaration's scheme, not
  by body node types. Typecheck builds their views with
  `MonoExpr::synthetic_local_from_expr`.
- At a concrete use site the field type converts. A generic declaration such as
  `(deftype (Option a) (Some [:a v]))` presents a residual declared parameter on the
  signature path. `signature_heap_category`
  (`crates/cranelisp-backend/src/compiler/rc_emission.rs`) converts through `from_type` and
  maps a failure to `HeapCategory::Mixed`. It must not abort, and `classify` itself must not
  be widened.
- "No variable reaches `classify`" therefore holds by construction on the body path and by
  total signature classification on the template path.
- Declaration-time rule (user ruling 2026-09-02, spec §5.2.4): a bare head declares a
  monomorphic type, a parenthesised head declares the complete parameter list, and every
  field carries a written type. Missing field types and undeclared variables are located
  frontend errors, so no legal monomorphic declaration has a free field variable.
- Open residuals:
  - Safety-register row R17 grades the `Mixed` fallback as the violating seam and stages
    its per-family flip to a located error once measured traffic is zero; “must not abort”
    above describes the interim rule, not the end state.
  - FIXME 0903 — generic product accessors and generic trait-method instances reach the
    release seam through the signature path; the release contract is
    `design/backend/non-concrete-release-contract.md`.
  - FIXME 0931 — constructors joining monomorphisation, which removes the largest
    signature-path population.
  - `MonoExpr::lenient_from_expr` and `synthetic_local_from_expr` fill a non-concrete node type
    with a placeholder that only the signature path may read. This is the fabrication site
    tracked by safety-register row R18. Ruled end state: both builders are deleted and
    `MonoExpr::from_expr` is the sole view builder, once synthesised bodies are stamped with
    real concrete node types. The lenient builder's direct callers in `src/` and the backend
    are test code, but `synthetic_local_from_expr` has production callers in typecheck and
    `src/bootstrap.rs`. Removal is a public-API change that needs the user's approval;
    ACT-0971 owns the assessment.

## 4-A. Mono-completeness — only all-args-concrete instances are minted

- A hop reached from a generic caller's body must not be minted at the caller's own scheme
  variables. Such an instance is the template under another name, its body cannot convert,
  and a name built by dropping variable-typed parameters can collide.
- The rule is one predicate: a call is a monomorphisation site iff every argument type is
  concrete (`crates/cranelisp-typecheck/src/program/mono_collect.rs::local_parametric_call_triggers`).
  The result is then concrete by the per-instance re-check. There is no separate
  bare-variable-result trigger.
- The rule does not pin any scheme variable; it narrows which instances are minted after
  inference. Distinct concrete calls therefore mint distinct instances, which is the
  polymorphic-accumulator fold invariant. Pins:
  `tests/regression.rs::mono_tier2_fold_accumulator_not_over_monomorphised` and
  `tests/spec_04_expressions.rs::polymorphic_accumulator_fold_does_not_over_unify`. They
  discriminate in both directions: a missing concrete instance and a collapsed scheme.
- If a case appears to need minting on non-concrete arguments, it is the ambiguity error
  (§2.6). Escalate to `arch`; do not re-widen the gate.

## Phase 5 — representation is backend-internal

- Because every codegen value is concrete, spec §12.1 makes each concrete type's runtime
  representation a backend choice. The uniform-word layouts it lists are descriptive.
- Delivered use: value-representation flattening of eligible single-field ADTs, governed by
  [ownership inference](ownership-inference.md) and the shared layout predicate in
  `crates/cranelisp-types/src/heap.rs`.
- Further representation freedom is a user-arbitrated question raised in the
  [release-backend proposal](release-llvm-backend.md).
