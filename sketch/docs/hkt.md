# Higher-Kinded Types

## Overview & Motivation

Cranelisp has traits with static dispatch (see `docs/traits.md`), but trait type parameters are always kind `*` — they range over concrete types like `Int`, `Bool`, `Option Int`. This means you cannot express abstractions over type constructors like `Functor`, `Monad`, or `Applicative`, which need a parameter of kind `* -> *`.

The workaround was multi-signature dispatch (see `docs/multi-sig.md`): `map` dispatches on `Vec`, `List`, and `Seq` with separate implementations. But multi-sig dispatch cannot compose generically — you cannot write a function that works over "anything mappable" without knowing the concrete container type at the call site.

The goal is to support **type constructor parameters** in trait declarations, so traits like `Functor` can abstract over `Option`, `List`, or any single-argument type constructor.

## Syntax

### Trait Declaration

```clojure
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
```

The lowercase `f` in `(Functor f)` is a **constructor variable** — it ranges over type constructors (kind `* -> *`), not concrete types (kind `*`). The method signature `(fmap [(Fn [a] b) (f a)] (f b))` uses `(f a)` and `(f b)` as **applied constructor expressions**, meaning "f applied to a" and "f applied to b".

### Implementation

```clojure
(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some x) (Some (f x))])))

(impl Functor List
  (defn fmap [f lst]
    (match lst
      [Nil Nil
       (Cons h t) (Cons (f h) (fmap f t))])))
```

The impl target is a **bare type constructor name** — `Option`, not `(Option a)`. The typechecker infers that `Option` has arity 1, matching the constructor variable `f`'s arity.

## Type System

### Type::TyConApp

A new type variant represents the application of a constructor variable to type arguments:

```rust
Type::TyConApp(TypeId, Vec<Type>)
```

`TyConApp(f_id, [Var(a_id)])` represents the type expression `(f a)` — constructor variable `f` applied to type variable `a`.

### Unification with ADT

When a `TyConApp` unifies with a concrete `ADT`, the constructor variable binds to the "unapplied" constructor and the inner type arguments unify pairwise:

```
TyConApp(f_id, [Var(a_id)])  ~  ADT("Option", [Int])
  => bind f_id -> ADT("Option", [])
  => bind a_id -> Int
```

After substitution, `TyConApp(f_id, [Var(b_id)])` becomes `ADT("Option", [apply(subst, Var(b_id))])` — the constructor is applied to whatever `b` resolves to. By codegen time, all `TyConApp` nodes are fully resolved to `ADT` — there is **zero runtime cost**.

### No Explicit Kind System

Kind checking is implicit. The arity of a constructor variable is determined by its usage in method signatures: if `f` appears as `(f a)`, it has arity 1. Validation happens at impl time — the typechecker checks that the impl target's `type_params.len()` matches the expected constructor arity.

### Scheme with Constraints

Constructor variables in HKT traits receive trait constraints, stored in the same `Scheme.constraints` field used by constrained polymorphism:

```rust
Scheme {
    vars: vec![f_id, a_id, b_id],
    constraints: {f_id: ["Functor"]},
    ty: Fn([Fn([Var(a_id)], Var(b_id)), TyConApp(f_id, [Var(a_id)])], TyConApp(f_id, [Var(b_id)])),
}
```

## Dispatch

### Resolution Path

HKT methods dispatch via the existing trait resolution path: `pending_resolutions` -> `resolve_methods` -> `find_impl_for_type`. No new resolution machinery is needed.

### Dispatch Parameter Index

The dispatch parameter may not be the first argument. For `fmap`:

```
fmap :: (Fn [a] b) -> (f a) -> (f b)
         ^param 0     ^param 1
```

The second parameter `(f a)` carries the constructor. The typechecker uses `hkt_method_info: HashMap<String, (usize, String)>` to map each method name to its `(dispatch_param_index, trait_name)`.

`hkt_param_idx_for_method` scans the method's parameter types to find the first one containing a constructor application — this becomes the dispatch parameter.

### find_impl_for_type

The existing `find_impl_for_type` works unmodified. HKT impls register with bare target names like `"Option"` and `"List"`. When the dispatch parameter resolves to `ADT("Option", [Int])`, the lookup extracts `"Option"` and finds the matching impl.

### Mangled Names

Final mangled names follow the same pattern as existing traits:

| Call | Dispatch Type | Mangled Name |
|---|---|---|
| `(fmap inc (Some 5))` | `Option Int` | `fmap$Option` |
| `(fmap inc (list 1 2 3))` | `List Int` | `fmap$List` |

### Important: Not Constrained Functions

HKT trait methods dispatch via `pending_resolutions`, **not** `pending_mono_calls`. Even though the scheme has constraints (on constructor variables), HKT methods are **not** treated as constrained polymorphic functions. The constraint is on the type constructor, which is resolved by the trait dispatch mechanism — not by monomorphisation.

## Impl Validation

### Constructor Arity

`con_var_arity()` scans method signatures for `Applied` uses of the constructor parameter name and returns the arity (number of type arguments).

`validate_impl()` checks that the impl target's arity matches the expected constructor arity:

```clojure
; OK — Option takes 1 type param, matches (f a)
(impl Functor Option ...)

; ERROR — Int is not a type constructor
(impl Functor Int ...)
; => "Int is not a type constructor (trait Functor expects arity 1)"
```

Primitive types (`Int`, `Bool`, `String`, `Float`) are rejected with a clear error message.

## Display

### Trait Declarations

HKT trait declarations display with their type parameters:

```
cranelisp> Functor
Functor :: (deftrait (Functor f) (fmap [(Fn [a] b) (f a)] (f b)))
```

### Method Types

Constructor variables get `:Trait f` constraint prefix on their first applied use:

```
cranelisp> fmap
Functor.fmap :: (Fn [(Fn [a] b) (:Functor f a)] (f b))
```

### TyConApp Rendering

In REPL type display, `TyConApp` is rendered as `(f a)` using named variables from the standard variable naming pass.

## Prelude

The Functor trait and initial impls are defined in `src/prelude.cl`, located between the Display impls and the Seq type:

```clojure
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))

(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some x) (Some (f x))])))

(impl Functor List
  (defn fmap [f lst]
    (match lst
      [Nil Nil
       (Cons h t) (Cons (f h) (fmap f t))])))
```

## Examples

```clojure
(fmap inc (Some 5))                    ;; => (Some 6)
(fmap inc (list 1 2 3))               ;; => (list 2 3 4)
(fmap inc None)                        ;; => None
(fmap (fn [x] (* x 2)) (Some 3))      ;; => (Some 6)
```

## Implementation Files

| File | Changes |
|---|---|
| `src/types.rs` | `TyConApp` variant, `apply`, `free_vars`, `Display`, `is_heap_type` |
| `src/typechecker/unification.rs` | `unify` (TyConApp vs ADT/TyConApp), `occurs`, `substitute_vars`, `has_type_var` |
| `src/typechecker/mod.rs` | `hkt_method_info` field, `type_params` in `SymbolInfo::TraitMethod` |
| `src/typechecker/traits.rs` | `register_hkt_trait`, `resolve_type_expr_hkt`, arity validation, `hkt_param_idx_for_method` |
| `src/typechecker/inference.rs` | HKT dispatch arg index, skip `pending_mono_calls` for trait methods |
| `src/typechecker/program.rs` | HKT-aware `impl_self_types` pre-unification |
| `src/typechecker/mono.rs` | `collect_var_mapping` and `apply_with` for TyConApp |
| `src/parser.rs` | `symbol()` instead of `uppercase_symbol()` in Applied `type_expr` |
| `src/display.rs` | HKT trait decl display, constructor constraint formatting |
| `src/repl/format.rs` | TyConApp in `collect_type_vars`, `format_type`, `format_type_with_constraints` |
| `src/prelude.cl` | Functor trait + Option/List impls |

## Design Decisions

**TyConApp collapses to ADT after substitution.** By codegen time, every `TyConApp` has been resolved to a concrete `ADT`. This means zero runtime cost and no changes to code generation — the existing ADT compilation handles everything.

**Implicit kind checking via arity.** Rather than introducing an explicit kind system (`*`, `* -> *`, etc.), constructor arity is inferred from usage in method signatures and validated at impl registration. This keeps the type system simpler while catching arity mismatches early.

**Dispatch reuses existing trait resolution.** HKT dispatch does not introduce a new resolution mechanism. The `pending_resolutions` -> `resolve_methods` -> `find_impl_for_type` pipeline works unmodified because HKT impls register with bare constructor names that already match the ADT lookup logic.

**Not constrained polymorphism.** Although HKT schemes carry constraints on constructor variables, HKT methods are resolved through trait dispatch (concrete at every call site), not through monomorphisation. This avoids the complexity of monomorphising over type constructors.

## Limitations

- **HKT + constrained polymorphism interaction not supported.** A function like `(defn map-inc [xs] (fmap inc xs))` that is generic over the Functor cannot be expressed yet — it would require monomorphising over type constructors.
- **Multi-param HKT traits not tested.** Traits like `(deftrait (Bifunctor f) ...)` with arity-2 constructors are a straightforward extension but have not been validated.
- **IO cannot implement Functor.** `IO` is a special `Type` variant, not an ADT, so it cannot be used as a Functor impl target without adapter logic.
- **No Monad/Applicative yet.** These depend on HKT and can be added to the prelude once the foundation is solid.

## Future Extensions

| Feature | Description |
|---|---|
| Monad/Applicative | Add to prelude using HKT — `(deftrait (Monad m) (bind [(m a) (Fn [a] (m b))] (m b)))` |
| Multi-param HKT | e.g., `(deftrait (Bifunctor f) ...)` for arity-2 constructors |
| IO as Functor/Monad | Requires adapter since IO is a special Type variant, not an ADT |
| Constrained HKT functions | e.g., `(defn map-inc [xs] (fmap inc xs))` producing `forall f. Functor f => (f Int) -> (f Int)` |
