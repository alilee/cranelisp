# Trait System

Solution design for the Cranelisp trait system as implemented in Ring 2. Covers trait declarations, implementations, default methods, constrained polymorphism, monomorphisation, method resolution, and core trait bootstrap.

This document is the authoritative design reference for Ring 3 implementers. It describes the data structures, algorithms, and invariants that govern how traits interact with the rest of the typechecker and backend.

## 1. Trait Registry

The trait system is built on three registries stored as fields on `TypeChecker`:

```rust
pub struct TypeChecker {
    pub(crate) trait_registry: TraitRegistry,
    pub(crate) impl_registry: ImplRegistry,
    pub(crate) active_constraints: ActiveConstraints,
    // ...
}
```

### TraitRegistry

```rust
pub struct TraitRegistry {
    pub(crate) decls: HashMap<TraitName, TraitDecl>,
    pub(crate) method_to_trait: HashMap<Symbol, TraitName>,
}
```

- **`decls`**: Maps trait name to its full AST declaration (`TraitDecl`). Stores the method signatures, type parameters, visibility, and span.
- **`method_to_trait`**: Reverse lookup from method name to the trait that owns it. This is the key structure for method resolution -- when `infer_apply` sees a call to `+`, it checks this map to determine that `+` belongs to `Num`.

**Invariant**: Every method name in `method_to_trait` has a corresponding entry in exactly one trait's `decls`. Method names are globally unique across traits (no two traits can declare a method with the same name).

### ImplRegistry

```rust
pub struct ImplRegistry {
    pub(crate) impls: HashMap<TraitName, HashMap<TypeName, RegisteredImpl>>,
}

pub struct RegisteredImpl {
    pub trait_name: TraitName,
    pub impl_type: TypeName,
    pub method_primitives: HashMap<Symbol, Symbol>,
}
```

Two-level map: `trait_name -> impl_type -> RegisteredImpl`. The `method_primitives` field stores the method-to-primitive delegation mapping (used for builtin impls; for user impls, each method maps to itself).

### ActiveConstraints

```rust
pub struct ActiveConstraints {
    pub(crate) constraints: HashMap<TypeId, Vec<TraitName>>,
}
```

Tracks trait constraints on type variables during inference. Populated when a constrained scheme is instantiated (via `instantiate_constrained`), consulted during `generalize` to propagate constraints onto the generalized scheme. Idempotent adds -- duplicate `(TypeId, TraitName)` pairs are ignored.

**Lifetime**: Active constraints accumulate across the checking of a compilation unit. They are NOT cleared between top-level forms in the same batch. The `generalize` method resolves constraints through the substitution, so constraints recorded on one variable correctly attach to the variable it was unified with.

## 2. Trait Declaration (`deftrait`)

### Surface Syntax

```clojure
(deftrait (TraitName a)
  (method1 [a a] a)                           ;; required method
  (method2 [x y] Bool (not (method1 x y))))   ;; default method
```

### Registration Pipeline

`register_trait_decl(&TraitDecl)` performs:

1. **Duplicate check**: Error if `trait_registry.decls` already contains the trait name.

2. **Fresh type variable allocation**: A single `fresh_var_id()` call allocates a type variable for the trait's type parameter (e.g., `a`). All methods share this variable -- they are polymorphic over the same `a`.

3. **Method registration**: For each `TraitMethodSig`, calls `register_trait_method()`:
   - Builds the method's function type via `build_method_type()`.
   - Wraps it in a `Scheme` with `vars: [type_var_id]` and `constraints: { type_var_id: [trait_name] }`.
   - Inserts the method into the symbol table as `ModuleEntry::Def` with `DefKind::UserFn { constrained_fn: None }`.
   - Registers the reverse lookup in `method_to_trait`.

4. **Trait storage**: Stores the `TraitDecl` in `trait_registry.decls`.

5. **Symbol table entry**: Registers the trait name itself as `ModuleEntry::TraitDecl` for REPL introspection.

### Type Variable Allocation

The `build_method_type` function resolves `TypeExpr` values in the method signature against a `var_map`:

- Trait type parameters (e.g., `a`) map to `Type::Var(type_var_id)` -- the shared type variable.
- `TypeExpr::Named("Bool")` resolves to `Type::Bool` via `Type::from_name`.
- `TypeExpr::SelfType` resolves to `Type::Var(type_var_id)`.
- Other `TypeExpr::TypeVar` values that do NOT match trait type parameters get fresh type variables (I3 fix). This handles methods with additional type parameters beyond the trait's own.

**Example**: For `(deftrait (Num a) (+ [a a] a))`, the `+` method gets:

```
Scheme {
    vars: [42],
    constraints: { 42: ["Num"] },
    ty: Fn([Var(42), Var(42)], Var(42))
}
```

This scheme says: `+` is polymorphic over one type variable, constrained to types that implement `Num`.

## 3. Trait Implementation (`impl`)

### Surface Syntax

```clojure
(impl Num Int
  (+ [x y] (add-i64 x y))
  (- [x y] (sub-i64 x y))
  (* [x y] (mul-i64 x y))
  (/ [x y] (div-i64 x y)))
```

### Registration Pipeline

`register_trait_impl(&TraitImpl)` performs:

1. **Trait lookup**: Finds the `TraitDecl` in `trait_registry.decls`. Error if unknown.

2. **Required method check**: `check_impl_methods_present` verifies all methods without `default_body` are provided. Methods with defaults may be omitted.

3. **Default method generation**: `generate_default_methods` creates `Defn` nodes for any missing methods that have defaults. Each gets a mangled name `TraitName.method_name$FQTargetType` (e.g., `Eq.!=$primitives/Int`) — the `$Type` suffix is the **home-qualified** type head (see §"Mangling Convention"). The body is constructed by `build_default_body` (see Section 4).

4. **Impl registration**: Inserts a `RegisteredImpl` into `impl_registry.impls[trait_name][target_type]`.

5. **Method body type-checking**: For each provided method, `check_impl_method` resolves the concrete type for `Self` (e.g., `Int`), builds concrete parameter and return types by substituting the trait type parameter with the concrete type, then calls `check_defn_body_with_types` to type-check the body.

6. **Mangled Defn emission**: Each method produces a `Defn` with mangled name `TraitName.method_name$FQTargetType` (e.g., `Num.+$primitives/Int`). These are returned to the caller for codegen.

### Mangling Convention

Trait method implementations use the naming pattern:

```
{TraitName}.{method_name}${home}/{TargetType}
```

Examples:
- `Num.+$primitives/Int` -- addition for integers
- `Eq.=$primitives/String` -- equality for strings
- `Display.show$primitives/Bool` -- string conversion for booleans
- `Eq.!=$primitives/Int` -- default method, inequality for integers
- `Describe.describe$a/Widget` -- a user impl for a module-`a` ADT

**FQ `$Type` suffix (S102 — 4th lossy-head cure).** The `$Type` suffix carries
the **fully-qualified, home-qualified** type head (`module/Type`), NOT the bare
head. Spec §3.8.4 makes two same-bare-named types from different modules
(`a/Widget` ≠ `b/Widget`) DISTINCT; the pre-S102 bare-head grammar
(`Describe.describe$Widget`) collapsed both onto one linker symbol, so their two
impl bodies collided and every `(describe x)` call dispatched to whichever
same-named `Widget` was in the caller's scope — a silent wrong-dispatch. This is
the same lossy-head class 0519 cured for the mono-instance mangler, now extended
to the trait-method grain. Home-qualifying the suffix makes the symbol
collision-free by construction (Principle 20).

**One mint, both sides — the lock-step invariant (name-path == definition-path).**
The dispatch site (`dispatch::try_resolve_trait_method`) and the
definition/writeback site (`impl_check` — `check_impl_method_with_sig`,
`check_hkt_impl_method`, `generate_default_methods`) mint through the ONE shared
`mangle_trait_method(trait, method, &FQTypeName)` helper against the SAME
canonical `FQTypeName`, or the call's linker symbol would not match the impl
method's definition symbol and dispatch would not resolve. The two sides derive
the `FQTypeName` differently but land on the same value for a given impl:
- **Definition side** — `resolve_type` on the impl target (`impl a/Widget` in
  module `a` → `a/Widget`), resolved ONCE in `register_trait_impl` and threaded
  to all three writeback paths (Principle 7).
- **Dispatch side** — `fq_type_for_dispatch_mangle(&resolved_arg, &fallback)`
  takes the FQ head from the resolved argument's OWN type (an ADT carries its
  home directly). It does NOT re-resolve the bare head in the caller's module
  (the `fallback`, used only for intrinsic receivers whose bare head is globally
  unambiguous) — that re-resolution is exactly the home-erasing bug.

**Grain: receiver HEAD only.** The suffix carries the receiver type's FQ head;
ADT type-args are NOT recursed (`Vec Int` and `Vec String` both yield the head
`primitives/Vec`). This MATCHES the trait-impl registration grain, which names by
the impl target head (`impl_target_name_or_panic`), so the two sides agree.
Arg-distinguishing the trait-method grain would require a coordinated change to
impl registration too and is out of scope for this cure — keeping the head-only
grain is what preserves the lock-step invariant.

*(The `primitive_for_trait_method` short-circuit means Ring-0 operator impls on
primitive types — `Num.+$…/Int`, `Display.show$…/Int`, etc. — never actually
mint a trait-method symbol; they collapse to `ResolvedCall::BuiltinFn` and inline.
The mangle path is exercised by user traits and user impls on ADTs.)*

### Body Type-Checking

`check_impl_method` resolves the concrete self type from `impl_.target_type`:

- Primitive types (`Int`, `Float`, `Bool`, `String`) resolve via `Type::from_name`.
- User-defined types resolve to `Type::ADT(name, [])`.

A `var_map` is pre-seeded with `{ trait_type_param -> concrete_self }`. Each method signature parameter and return type is resolved through `resolve_trait_type_expr` using this map, producing concrete types. The body is then checked against these concrete types using `check_defn_body_with_types`, which pushes a scope, binds parameters, infers the body, and unifies with the expected return type.

**Post-inference**: `resolve_deferred_trait_calls` runs after body checking to resolve any trait method calls within the impl body that couldn't be resolved eagerly (see Section 8).

## 4. Default Methods

Default methods are trait methods with a body that can be omitted from `impl` blocks. The trait declaration specifies the body; implementations inherit it unless they provide their own.

### Declaration

In `TraitMethodSig`, `default_body: Option<Sexp>` signals a default method. When `Some(...)`, the method may be omitted from implementations.

For the core traits, default bodies are flagged with a placeholder (`Sexp::Symbol("default", ...)`) rather than actual Cranelisp source. The `build_default_body` function hard-codes the AST construction for known defaults:

| Method | Body |
|--------|------|
| `Eq.!=` | `(not (= x y))` |
| `Ord.>` | `(< y x)` |
| `Ord.<=` | `(not (< y x))` |
| `Ord.>=` | `(not (< x y))` |

**Ring 3 note**: When user-defined traits with default methods are supported via parsed source, `build_default_body` will need to be replaced with a pipeline that parses the `default_body` Sexp through the frontend's AST builder. The current hard-coded approach only works for the four known builtin defaults.

### Generation

When `register_trait_impl` finds a method not provided by the impl but present in the trait decl with a default body:

1. A mangled name `TraitName.method$home/TargetType` is generated (FQ suffix; see §"Mangling Convention").
2. `build_default_body` constructs the AST body.
3. A `Defn` is created with the default parameter names and the constructed body.
4. The `Defn` is included in the returned vector alongside explicitly provided methods.

Default method `Defn` nodes are returned as `default_method_defns` in `CheckResult` / `ReplCheckResult` and compiled by the backend like any other function.

### Override

If an impl provides a method that has a default, the provided implementation is used instead. The `generate_default_methods` function checks the `provided` set and skips any method found there.

## 5. Core Trait Bootstrap (Decision 17 -- Resolved)

The four core traits (`Num`, `Eq`, `Ord`, `Display`) and their implementations for primitive types are registered during `TypeChecker::new()` by Rust code in `builtins.rs`. This was originally flagged as Decision 17 for elimination; it was resolved in Sprint 9 by routing all registrations through the normal `register_trait_decl` / `register_trait_impl` pipeline (see "Decision 17 Status" below).

### Why Not Parse From Source

Core traits cannot be registered by parsing Cranelisp source because:

1. **Circular dependency**: The frontend (parser, macro expander, AST builder) depends on the typechecker's symbol table, which needs these traits to resolve operators. Loading them from source would require a partially-functional pipeline.

2. **Bootstrap ordering**: `register_builtins()` runs before any Cranelisp source is processed. The trait declarations and implementations must be available before the first `(+ 1 2)` can be type-checked.

3. **No frontend dependency**: The typechecker crate does not depend on the frontend crate. Constructing `TraitDecl` and `TraitImpl` AST structs directly in Rust avoids introducing this dependency.

### Implementation

`register_builtins()` calls:

1. `register_primitives()` -- Ring 0 monomorphic primitives (`add-i64`, `eq-i64`, etc.)
2. `register_ring1_primitives()` -- Ring 1 extern primitives (`int-to-string`, `str-eq`, etc.)
3. `register_vec_primitives()` -- Polymorphic Vec primitives
4. `register_special_forms()` -- Special form entries for introspection
5. `register_core_trait_decls()` -- Constructs `TraitDecl` AST structs and routes through `register_trait_decl()`
6. `register_core_trait_impls()` -- Constructs `TraitImpl` AST structs with real method bodies (delegating to named primitives) and routes through `register_trait_impl()`
7. `clear_transient_state()` -- Clears `expr_types`, `method_resolutions`, and `subst` accumulated during core impl type-checking

The key design principle: core traits use **the same pipeline** as user-defined traits. `register_core_trait_decls` constructs `TraitDecl` structs and calls `register_trait_decl`; `register_core_trait_impls` constructs `TraitImpl` structs with method bodies like `(add-i64 x y)` and calls `register_trait_impl`. The returned `Defn` nodes are discarded because the backend's `primitive_for_trait_method` short-circuits all core methods to inline IR (see Section 8).

### 12 Core Impl Registrations

| Trait | Int | Float | Bool | String |
|-------|-----|-------|------|--------|
| Num | `+` `-` `*` `/` | `+` `-` `*` `/` | -- | -- |
| Eq | `=` | `=` | `=` | `=` |
| Ord | `<` | `<` | -- | -- |
| Display | `show` | `show` | `show` | `show` |

Default methods (`!=`, `>`, `<=`, `>=`) are auto-generated for all Eq/Ord impls.

### Transient State Cleanup

After registering core trait impls, `clear_transient_state()` wipes `expr_types`, `method_resolutions`, and `subst`. This is necessary because `register_trait_impl()` type-checks method bodies (e.g., checking that `(add-i64 x y)` has type `(Fn [Int Int] Int)`), which populates these maps with entries keyed at `Span::SYNTHETIC`. Without cleanup, these entries would leak into user program checking and cause spurious matches.

### Decision 17 Status

Decision 17 was resolved in Sprint 9 (task #4). The original concern was that core traits were registered via bespoke `register_core_traits()` / `register_builtin_impls()` helper functions rather than the normal trait pipeline. The resolution replaced those helpers so that core traits now use the standard `register_trait_decl()` / `register_trait_impl()` code paths:

- **Normal pipeline**: `register_core_trait_decls()` constructs `TraitDecl` AST structs in Rust and passes them to `register_trait_decl()`. `register_core_trait_impls()` constructs `TraitImpl` AST structs (with real method bodies delegating to named primitives) and passes them to `register_trait_impl()`. No special-case registration logic exists.
- **No frontend dependency**: The typechecker crate cannot depend on the frontend crate, so AST structs (`TraitDecl`, `TraitImpl`, `TraitMethodSig`, etc.) are constructed directly in Rust rather than parsed from Cranelisp source. This is a permanent architectural constraint, not a temporary compromise.
- **Transient state cleanup**: `clear_transient_state()` wipes `expr_types`, `method_resolutions`, and `subst` accumulated during core impl type-checking, preventing `Span::SYNTHETIC` entries from leaking into user program checking.
- **Module context**: Core traits are registered in the `primitives` module context (Sprint 9 trait module fix), consistent with how other builtin symbols are scoped.

No Ring 3 macro pipeline dependency was needed. The key insight is that pipeline uniformity (Invariant 14) does not require parsing from Cranelisp source -- it only requires that core traits flow through the same `register_trait_decl` / `register_trait_impl` code paths as user traits, which they now do.

## 6. Constrained Polymorphism

### What It Is

A function is *constrained polymorphic* when its generalized type scheme has non-empty constraints. This happens when the function body calls trait methods, leaving the concrete type unresolved.

```clojure
(defn add [x y] (+ x y))
;; Inferred: add :: forall a:Num. (Fn [a a] a)
```

Here `a` must implement `Num` because the body calls `+`. Unlike unconstrained polymorphism (which can be compiled once), constrained functions must be *monomorphised* at each call site -- the concrete type determines which trait impl to use.

### Scheme.constraints

```rust
pub struct Scheme {
    pub vars: Vec<TypeId>,
    pub constraints: HashMap<TypeId, Vec<TraitName>>,
    pub ty: Type,
}
```

`constraints` maps quantified type variable IDs to the list of traits they must implement. A scheme with empty `constraints` is unconstrained polymorphic (or monomorphic if `vars` is also empty).

### Constraint Propagation

Constraints flow through three stages:

**Stage 1 -- Instantiation**: When a constrained scheme (e.g., `+` with `Num` constraint) is instantiated, `instantiate_constrained` maps old type variables to fresh ones and carries the constraints to the fresh variables in `active_constraints`:

```rust
fn instantiate_constrained(&mut self, scheme: &Scheme) -> Type {
    // Build old_var -> fresh_var mapping
    // For each (old_var, traits) in scheme.constraints:
    //   active_constraints.add(fresh_var, trait)
    apply(&inst_subst, &scheme.ty)
}
```

**Stage 2 -- Unification**: During body checking, the fresh variables from instantiation may be unified with other variables (e.g., the function's parameter type variables). The substitution records these bindings but does NOT move constraints -- they remain on the original fresh variable.

**Stage 3 -- Generalization**: `TypeChecker::generalize` resolves constraints through the substitution:

```rust
fn generalize(&self, ty: &Type) -> Scheme {
    let mut scheme = scheme::generalize(&self.subst, ty, &env_fv);
    // For each (constrained_var, traits) in active_constraints:
    //   let resolved = apply(subst, Var(constrained_var))
    //   if resolved is Var(resolved_id) and resolved_id in scheme.vars:
    //     scheme.constraints[resolved_id] = traits
    scheme
}
```

This is the critical step. The constraint was recorded on a fresh variable (from instantiation), which was unified with one of the function's parameter type variables. The substitution maps the fresh variable to the parameter variable, so the constraint correctly attaches to the scheme's quantified variable.

### Detection

Constrained functions are detected in `pass2_check_bodies` using a two-phase approach:

**Phase 1 -- Eager marking**: After each function body is checked, a trial `generalize` is performed. If the trial scheme has non-empty constraints, the function is immediately marked as constrained by storing a `ConstrainedFn` in its `DefKind`. This must happen eagerly because later function bodies (in the same compilation unit) may call this function, pinning its type variables to concrete types through the shared substitution.

**Phase 2 -- Final generalization**: After all bodies are checked, all functions are generalized again. If a function's final scheme has no constraints (because later call sites pinned all type variables), any eager `constrained_fn` marker is cleared.

**Phase 3 -- Re-resolution**: A final `resolve_deferred_trait_calls` pass runs over all function bodies. During Phase 1, some trait calls could not be resolved because argument types were still unresolved variables. After Phase 2, those variables may be pinned to concrete types.

### ConstrainedFn Storage

```rust
pub struct ConstrainedFn {
    pub defn: Defn,
    pub scheme: Scheme,
}
```

Stored inside `DefKind::UserFn { constrained_fn: Option<Box<ConstrainedFn>> }`. The `defn` is the original function definition (needed to re-check the body during monomorphisation). The `scheme` is the constrained polymorphic scheme.

## 7. Monomorphisation

### Overview

Monomorphisation generates specialized versions of constrained functions for each concrete type combination encountered at call sites. Each specialization has its own mangled name, method resolutions, and expression types.

### Mangling Convention

```
{fn_name}${Type1}+{Type2}+...
```

Where `Type1`, `Type2`, etc. are the concrete parameter types. Examples:
- `add$Int+Int` -- `add` specialized to `(Int, Int)`
- `add$Float+Float` -- `add` specialized to `(Float, Float)`

### Batch Pipeline (Pass 4)

`pass4_monomorphise` in `program.rs`:

1. **Collect call sites**: Walk all non-constrained function bodies with `collect_constrained_calls`, finding `Apply` nodes whose callee is a known constrained function. Records `(fn_name, arg_spans, call_span)` triples.

2. **Resolve argument types**: Look up concrete types from `resolved_expr_types` using the argument spans.

3. **Deduplicate**: Build a key `"fn_name$Type1+Type2+..."` and skip if this specialization was already generated.

4. **Monomorphise**: Call `monomorphise_call` for each unique specialization.

5. **Record dispatch**: Insert `ResolvedCall::SigDispatch { mangled_name }` into `method_resolutions` for each call site.

### monomorphise_call

`monomorphise_call(fn_name, arg_types, call_span)` in `traits.rs`:

1. **Look up ConstrainedFn**: Retrieve the original `Defn` and constrained `Scheme`.

2. **Instantiate and unify**: Instantiate the scheme with fresh variables, then unify each parameter type with the concrete argument type. This pins all type variables to concrete types.

3. **Build mangled name**: `name$Type1+Type2`.

4. **Constraint satisfaction check**: For each constraint `(var_id, traits)` in the scheme, resolve the var through the substitution and check that the concrete type has an impl for each required trait. Error if not.

5. **Re-check body**: Save and swap out `method_resolutions` and `expr_types`. Re-check the function body with concrete parameter types via `check_defn_body_with_types`. This produces method resolutions specific to this specialization (e.g., `+` at Int resolves to `Num.+$Int`).

6. **Inner call resolution**: Scan the body for calls to other constrained functions and generate `SigDispatch` entries for them (handles self-recursive constrained calls).

7. **Produce MonoDefn**: Package the mangled `Defn`, per-specialization `resolutions`, and per-specialization `expr_types` into a `MonoDefn`.

8. **Restore state**: Restore the original `method_resolutions` and `expr_types`.

### MonoDefn

```rust
pub struct MonoDefn {
    pub defn: Defn,                       // mangled name, original body
    pub resolutions: MethodResolutions,   // per-specialization call resolutions
    pub expr_types: HashMap<Span, Type>,  // per-specialization expression types
}
```

Each `MonoDefn` carries its own method resolutions and expression types. The backend compiles it as a standalone function, using the per-mono maps instead of the program-wide ones.

### REPL Path

`monomorphise_expr_calls(expr)` handles the REPL case:

1. Scans the symbol table for all constrained function names.
2. Calls `collect_constrained_calls` on the expression.
3. Resolves argument types from `expr_types` (applying the substitution).
4. Calls `monomorphise_call` for each call site.

This runs for both `ReplInput::Expr` and `ReplInput::Defn`.

### Invariants

- Constrained functions are never compiled directly -- only their monomorphised specializations are compiled.
- `constrained_fn_names` in `CheckResult` tells the backend which `Defn` nodes to skip.
- Each `MonoDefn` shares the same `Span` values as the original `Defn` (since the body is reused). The per-mono `expr_types` and `resolutions` override the program-wide maps for this specialization.

## 8. Method Resolution

### Resolution Pipeline

Method resolution happens in `infer_apply` and is refined post-inference by `resolve_deferred_trait_calls`. The result is a `ResolvedCall` entry in `method_resolutions`, keyed by the `Apply` node's span.

#### During Inference (infer_apply)

After unifying callee and argument types:

1. **Trait method check**: `try_resolve_trait_method(name, resolved_args, span)` -- looks up the callee in `method_to_trait`, resolves the first argument's type through the substitution, extracts the concrete type name, checks for an impl, and produces `ResolvedCall::TraitMethod` with the mangled name.

2. **Primitive check**: If not a trait method, checks `is_primitive(name)` and produces `ResolvedCall::BuiltinFn`.

3. **Neither**: No entry in `method_resolutions` -- the backend treats it as a regular function call.

#### Deferred Resolution (resolve_deferred_trait_calls)

During inference, argument types may still be unresolved variables (e.g., in `(defn add [x y] (+ x y))`, the types of `x` and `y` are fresh variables when `+` is processed). The `try_resolve_trait_method` call returns `None` because `concrete_type_name(Var(_))` returns `None`.

After all bodies are checked and the substitution is fully populated, `resolve_deferred_trait_calls` walks the expression tree and retries resolution for any `Apply` node whose callee is a trait method but has no entry in `method_resolutions`. It reads argument types from `expr_types` (applying the substitution) rather than re-inferring.

This runs:
- After each body in `pass2_check_bodies` Phase 1
- After all bodies in `pass2_check_bodies` Phase 3 (re-resolution)
- After body checking in `check_defn_body_with_types` (impl methods, monomorphisation)

### ResolvedCall Enum

```rust
pub enum ResolvedCall {
    TraitMethod {
        trait_name: TraitName,
        method_name: Symbol,
        impl_type: TypeName,
        mangled_name: JitSymbol,
    },
    SigDispatch { mangled_name: JitSymbol },
    AutoCurry { target_name: Symbol, applied_count: usize },
    BuiltinFn { name: Symbol },
}
```

The backend dispatches on this enum in `compile_resolved_call`:

- **`TraitMethod`**: Checks `primitive_for_trait_method` first. If it returns a primitive name, emits inline Cranelift IR or an extern call. If not (user-defined impl), compiles as a direct call to the mangled name.
- **`SigDispatch`**: Direct call to the mangled specialization name (monomorphised constrained function or multi-sig variant).
- **`BuiltinFn`**: Emits inline Cranelift IR via `emit_builtin_op`.
- **`AutoCurry`**: Generates a closure capturing applied arguments (Ring 2 auto-curry).

### primitive_for_trait_method (Decision 14)

Per architecture Decision 14, the typechecker emits `ResolvedCall::TraitMethod` for all trait method calls. The backend decides whether to inline the operation or compile a function call. This keeps the typechecker ignorant of codegen details.

`primitive_for_trait_method(trait_name, method_name, impl_type) -> Option<&'static str>` is a static mapping from `(TraitName, method, Type)` triples to primitive names. It covers 26+ entries across Num, Eq, Ord, and Display for Int, Float, Bool, and String.

If the mapping returns `Some(prim_name)`, the backend emits inline IR (for `PrimitiveKind::Inline` prims like `add-i64`) or an extern call (for `PrimitiveKind::Extern` prims like `int-to-string`). If it returns `None`, the method is a user-defined function and is compiled as a direct call to the mangled name.

**Ring 3 implication**: When macro-compiled functions define trait impls, their methods will NOT appear in `primitive_for_trait_method`. The backend will compile them as direct calls to the mangled function name. This is correct and requires no changes -- the `None` path already handles user-defined impls.

### concrete_type_name

The helper `concrete_type_name(ty: &Type) -> Option<TypeName>` extracts the type name from a resolved type:

| Type | Result |
|------|--------|
| `Int` | `Some("Int")` |
| `Float` | `Some("Float")` |
| `Bool` | `Some("Bool")` |
| `String` | `Some("String")` |
| `ADT(name, _)` | `Some(name)` |
| `Var(_)` | `None` |
| `Fn(_, _)` | `None` |

Returning `None` for `Var` is what causes deferred resolution -- the method call cannot be resolved until the variable is pinned to a concrete type.

## 9. Multi-Signature Functions

### Surface Syntax

```clojure
(defn map
  ([f :Vec v] (vec-map f v))
  ([f :List l] (list-map f l))
  ([f :Seq s] (seq-map f s)))
```

### AST Representation

```rust
TopLevel::DefnMulti {
    name: Symbol,
    docstring: Option<String>,
    variants: Vec<DefnVariant>,
    visibility: Visibility,
    span: Span,
}
```

Each `DefnVariant` has parameters, annotations, and a body -- essentially a standalone function definition.

### Dispatch

Multi-sig dispatch is resolved at type-checking time by matching concrete argument types against variant parameter type annotations. The typechecker produces `ResolvedCall::SigDispatch { mangled_name }` for each call site.

### Mangling Convention

Multi-sig variants use the same `$` separator as monomorphisation:

```
{fn_name}${Type1}+{Type2}+...
```

For example, `map$Vec+Fn` for the Vec variant.

### Interaction with Constrained Polymorphism

Multi-sig functions and constrained polymorphism are not yet combined. A multi-sig variant that calls trait methods is not automatically detected as constrained. This is a known limitation documented in MEMORY.md.

### REPL Status

Multi-sig functions are not yet supported in REPL mode (`check_repl_input` returns a `TypeError` for `ReplInput::DefnMulti`).

## 10. Invariants

These properties must always hold. Violations indicate implementation bugs.

### Registry Invariants

1. **Method name uniqueness**: No two traits declare the same method name. `register_trait_method` would overwrite the `method_to_trait` entry, corrupting dispatch.

2. **Impl completeness**: Every impl provides all required methods (those without `default_body`). Checked by `check_impl_methods_present`.

3. **Impl type-correctness**: Every impl method body type-checks against the trait's method signature with `SelfType` substituted for the concrete target type.

4. **Registry consistency**: If `method_to_trait[m] = T`, then `trait_registry.decls[T]` exists and contains a method named `m`.

### Constraint Invariants

5. **Constraint resolution**: After generalization, every constraint in a `Scheme` references a type variable that is in the scheme's `vars` list.

6. **Active constraints accumulation**: `active_constraints` is never cleared between top-level forms within a single `check_program` call. Constraints from earlier forms may be needed during generalization of later forms.

7. **Substitution resolution**: `generalize` resolves constraints through the substitution. A constraint on `Var(X)` where `subst[X] = Var(Y)` attaches to `Y` in the scheme, not `X`.

### Monomorphisation Invariants

8. **Constrained functions not compiled directly**: The backend must skip any `Defn` whose name appears in `CheckResult.constrained_fn_names`. Only the `MonoDefn` specializations are compiled.

9. **Per-mono isolation**: Each `MonoDefn` has its own `resolutions` and `expr_types`. The backend must use these instead of the program-wide maps when compiling a monomorphised specialization.

10. **Deduplication**: `pass4_monomorphise` generates at most one `MonoDefn` per unique `(fn_name, concrete_arg_types)` combination. Multiple call sites with the same types share the same specialization via `SigDispatch`.

### Resolution Invariants

11. **Span-keyed resolutions**: `method_resolutions` entries are keyed by the `Apply` node's span. Each span maps to exactly one `ResolvedCall`. If a span is not in the map, the backend treats it as a regular function call.

12. **Deferred resolution completeness**: After `resolve_deferred_trait_calls`, every trait method call with concrete argument types has a `ResolvedCall::TraitMethod` entry. Calls with still-unresolved types (inside constrained function bodies) remain unresolved -- they are handled during monomorphisation re-checking.

### Bootstrap Invariants

13. **Transient state cleanup**: After `register_core_trait_impls`, `clear_transient_state` must be called. Failure to clear would leave `Span::SYNTHETIC` entries in `expr_types` and `method_resolutions` that interfere with user program checking.

14. **Pipeline uniformity**: Core traits use the same `register_trait_decl` / `register_trait_impl` code paths as user traits. No special-case logic exists for core traits in the registration pipeline.

## Per-Ring Evolution

### Ring 2A (Current)

- Trait declarations and implementations
- Constrained polymorphism detection and monomorphisation
- Core trait bootstrap (Decision 17 -- resolved in Sprint 9)
- Deferred method resolution
- Default methods for Eq/Ord
- `primitive_for_trait_method` backend optimization
- Multi-signature functions (batch mode only)

### Ring 2B (Current)

- Module-scoped trait declarations and implementations
- Cross-module trait method resolution
- REPL trait declaration and implementation
- REPL on-demand monomorphisation

### Ring 3 (Planned)

- User-defined default method bodies parsed from Cranelisp source (not hard-coded AST)
- Macro-defined trait implementations (macros that expand to `impl` forms)
- Applied types in trait methods (currently returns an error in `resolve_trait_type_expr`)
- Multi-sig + constrained polymorphism interaction
