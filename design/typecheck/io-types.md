# IO ADT Typing — Design Document

Sprint 16, Task I1. Owned by `/typecheck`.

## Overview

The IO type models deferred computations that produce side effects. It is an ordinary algebraic data type — `Type::ADT(TypeName::from("IO"), vec![a])` — with no dedicated `Type` variant. The type system enforces IO purity tracking through standard Hindley-Milner unification: no special inference rules, no annotations, no compiler flags.

This document covers how the IO ADT is seeded in the typechecker, how its constructors and the `bind` primitive are typed, how `main` is validated in batch mode, and how IO interacts with the existing type system.

## Architectural Constraints

Per the `/arch` review in `sprints/SPRINT.md`:

- **No `Type::IO` variant.** IO uses `Type::ADT`. The spec (10.1.1) states IO is an ordinary ADT with no special type-checking rules. A dedicated variant would add a branch to every `match` on `Type` across all crates.
- **No `Par` constructor (tag=3) yet.** Automatic IO scheduling (spec 10.12) is scoped to a later sprint. Seeding Par now would create dead code and untested paths (principle 8).
- **`ConstructorInfo` needs an `internal` field.** The reimplementation's `ConstructorInfo` (in `crates/cranelisp-types/src/check.rs`) currently lacks this field. It must be added.

## 1. `ConstructorInfo.internal` Field

### Current definition (`crates/cranelisp-types/src/check.rs`)

```rust
pub struct ConstructorInfo {
    pub name: Symbol,
    pub tag: usize,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
}
```

### Required change

Add `internal: bool` with `#[serde(default)]` so cached modules without the field deserialize correctly:

```rust
pub struct ConstructorInfo {
    pub name: Symbol,
    pub tag: usize,
    pub fields: Vec<FieldInfo>,
    pub docstring: Option<String>,
    #[serde(default)]
    pub internal: bool,
}
```

All existing constructor registrations pass `internal: false` (the serde default). Only Bind is `internal: true`.

### Enforcement points

Internal constructors must be rejected at two points:

1. **AST builder / typechecker**: When a constructor call `(Bind x f)` is encountered, if `ConstructorInfo.internal == true`, emit a type error: "cannot construct internal type constructor `Bind`".
2. **Pattern matching**: When a match arm uses `(Bind ...)`, if `ConstructorInfo.internal == true`, emit a type error: "cannot match on internal type constructor `Bind`". Internal constructors are also excluded from exhaustiveness checking — user code cannot and need not cover them.

The sketch enforces this in `typechecker/adt.rs` (constructor application) and `typechecker/inference.rs` (pattern matching). The reimplementation follows the same approach.

## 2. IO ADT Seeding

### Location

The IO ADT is seeded in the typechecker's primitive registration, alongside the existing builtin types (`Int`, `Bool`, `Float`, `String`, `Option`, `Vec`, `List`, `Sexp`, `SList`, `Trace`). This happens in a `register_io_type()` method called from `register_all_builtins()` (or equivalent), within the `primitives` module context.

### Procedure

The seeding reuses the existing `register_type_def()` infrastructure. The typechecker constructs a synthetic `TopLevel::TypeDef` AST node and feeds it through the same registration path as user-defined types. This ensures constructors, accessor functions, `TypeDefInfo`, `ConstructorInfo`, and `ModuleEntry` records are all created consistently.

```
register_io_type():
  1. Save current module path.
  2. Set current module path to "primitives".
  3. Build a synthetic TopLevel::TypeDef for IO with:
     - name: "IO"
     - docstring: "Deferred IO computation tree"
     - type_params: ["a"]
     - constructors:
       - Pure (tag=0): fields = [FieldDef { name: "ioval", type_expr: TypeVar("a") }]
       - Effect (tag=1): fields = [FieldDef { name: "thunk", type_expr: TypeVar("a") }]
     - visibility: Public
  4. Call register_type_def() on this synthetic node.
  5. Add Bind as an internal constructor (tag=2) — see §3.
  6. Restore saved module path.
```

After step 4, the typechecker has:
- `TypeDefInfo` for "IO" with constructors Pure and Effect.
- Constructor schemes: `Pure :: forall a. (Fn [a] (IO a))`, `Effect :: forall a. (Fn [a] (IO a))`.
- Accessor function `ioval :: forall a. (Fn [(IO a)] a)`.
- The type `IO` registered in the `primitives` module's symbol table.

### Why Effect uses `TypeVar("a")` for `thunk`

At the type level, `Effect` is typed as `(Fn [a] (IO a))` — the thunk field is typed as the result type `a`, the same as Pure's `ioval` field. This is an intentional simplification. At runtime, the thunk field is actually a `Box<Box<dyn FnOnce() -> i64>>` (a double-boxed Rust closure), but the type system treats it as the eventual result type `a`. This works because:

1. Users never construct `Effect` directly — platform functions return `Effect` nodes via the `CLIO::effect()` API in the platform crate.
2. Users never access the `thunk` field directly — the trampoline extracts and invokes it.
3. The type parameter `a` correctly represents what the `Effect` will *produce* when forced, which is what matters for type inference.

The sketch uses this same approach (see `sketch/src/typechecker/primitives.rs:633-638`).

### Effect is NOT internal

Per spec 10.1, only `Bind` is marked internal. `Effect` is a normal public constructor. In practice, users do not construct `Effect` values (platform functions do), but the type system does not prevent it. This is consistent with the sketch.

## 3. Bind Constructor (Internal)

Bind has an existential type that HM inference cannot express:

```
Bind :: exists b. (IO b, (Fn [b] (IO a))) -> (IO a)
```

The intermediate type `b` is not exposed to the user — it is the type that the inner IO computation produces and the continuation consumes. HM cannot quantify over `b` existentially.

### Seeding procedure

Bind is added directly to the `TypeDefInfo` after `register_type_def()` creates Pure and Effect. This bypasses the normal constructor registration path because:

1. Bind's type cannot be expressed as a `ConstructorDef` (no existential type syntax).
2. Bind should NOT be registered in the type environment as a callable constructor.
3. Bind's fields use type variables that are independent of the IO type's `a` parameter.

```
add_internal_bind_constructor():
  1. Look up the IO TypeDefInfo in the primitives module.
  2. Allocate fresh type vars: a_id (for IO's type param) and b_id (for the existential).
  3. Build field types:
     - inner :: (IO b) = Type::ADT("IO", [Var(b_id)])
     - cont :: (Fn [b] (IO a)) = Type::Fn([Var(b_id)], ADT("IO", [Var(a_id)]))
  4. Append ConstructorInfo { name: "Bind", tag: 2, fields: [inner, cont],
     docstring: "Chain IO actions (internal — constructed by bind primitive)",
     internal: true }.
  5. Do NOT register Bind in the type environment (no insert_def call).
  6. Do NOT register Bind as a ModuleEntry::Constructor.
```

The Bind constructor exists in `TypeDefInfo.constructors` for REPL introspection (`/info IO` shows all three constructors) but is not resolvable as a name — looking up "Bind" will not find a constructor function.

## 4. `bind` Primitive

### Type

```
bind :: forall a b. (Fn [(IO a) (Fn [a] (IO b))] (IO b))
```

### Registration

`bind` is registered as an inline primitive in the `primitives` module with `PrimitiveKind::Inline`. It is not a function call — the backend emits Cranelift IR inline at each call site to allocate a Bind node (`[tag=2, inner_io_ptr, cont_closure_ptr]`).

```
register_bind_primitive():
  1. Allocate fresh type vars: a_id, b_id.
  2. Build types:
     - io_a = Type::ADT("IO", [Var(a_id)])
     - io_b = Type::ADT("IO", [Var(b_id)])
     - cont_ty = Type::Fn([Var(a_id)], io_b)
     - bind_ty = Type::Fn([io_a, cont_ty], io_b)
  3. Build scheme: Scheme { vars: [a_id, b_id], constraints: {}, ty: bind_ty }
  4. Register in primitives module as:
     - DefKind::Primitive { primitive_kind: PrimitiveKind::Inline, jit_name: None }
     - Scheme as above
     - Docstring: "Chain IO actions: extract value from first IO, pass to continuation"
```

### How bind interacts with inference

`bind` has no special inference rules. It is a polymorphic function with a standard scheme. When the typechecker encounters `(bind io-expr cont-expr)`:

1. Standard function application inference applies.
2. `io-expr` unifies with `(IO a)` for fresh `a`.
3. `cont-expr` unifies with `(Fn [a] (IO b))` for fresh `b`.
4. The result type is `(IO b)`.

The key property is that `a` is shared between the first argument and the continuation's input — the continuation receives the unwrapped value from the IO computation. This falls out of standard unification with no special logic.

## 5. `pure` Function

### Decision: stdlib function, not primitive

`pure` is an ordinary Cranelisp function, not a primitive. Its implementation is trivial:

```clojure
(defn pure "Lift a value into IO" [x] (Pure x))
```

This is consistent with spec 10.2: "`pure` is an ordinary library function that wraps a value in a `Pure` constructor."

### Typechecker impact: none

`pure` requires no typechecker work. Once the IO ADT is seeded with the `Pure` constructor (step 2), the stdlib can define `pure` as an ordinary function. The typechecker infers `pure :: forall a. (Fn [a] (IO a))` from the body `(Pure x)` via standard constructor application.

### Alternative considered and rejected

Making `pure` a primitive would be functionally equivalent but would add an entry to the primitive table for something that works perfectly as a one-line function. The spec explicitly says it is not a special form. The sketch implements `pure` in `lib/core/io.cl` as a stdlib function, confirming this works.

## 6. `main` Validation

### Requirement

Spec 10.6: "Batch programs MUST define a function named `main` with no parameters. The return type of `main` MUST be `IO _`."

### Where validation happens

`main` validation is performed at the end of `check_program()` in the typechecker, after all definitions have been type-checked. This is the same location in the pipeline as the sketch (`sketch/src/typechecker/program.rs:235-263`).

### Validation logic

```
validate_main():
  1. Look up "main" in the current module's type environment.
  2. If not found: error "batch program must define main".
  3. Apply current substitution to get the concrete type.
  4. Match on the type:
     a. Type::Fn(params, ret) where params.is_empty():
        - Match on *ret:
          - Type::ADT(name, _) where name == "IO": OK
          - _: error "main must return IO _, but returns {ret}"
     b. Type::Fn(params, _) where !params.is_empty():
        - error "main must take no parameters, but takes {params.len()}"
     c. _: error "main must be a function"
```

### REPL mode

In REPL mode, there is no `main` validation. Users can define functions with any signature. IO expressions evaluated at the REPL prompt are forced via the trampoline before display (this is an integration concern, not a typechecker concern).

### Batch mode without IO

A batch program that defines `main` returning a non-IO type (e.g., `(defn main [] 42)`) is a type error. This is intentional: in a language with tracked effects, the entry point must declare its intent to perform effects. A pure batch program uses `(defn main [] (pure 0))`.

## 7. Interaction with Existing Type System

IO requires **zero special rules** in the type inference engine. This section explains why, by walking through the key scenarios.

### 7.1 IO propagation through the call graph

When a function calls an IO-returning operation, standard inference propagates the IO type:

```clojure
(defn greet [name]
  (print (str-concat "hello " name)))
```

1. `str-concat` is typed `(Fn [String String] String)`. The argument `"hello "` and `name` unify with String.
2. `print` is typed `(Fn [String] (IO Int))`. The result of `str-concat` unifies with String.
3. The body's type is `(IO Int)`, so `greet :: (Fn [String] (IO Int))`.

No special rule was needed. IO appeared because `print` returns `IO Int`, and that type flowed to `greet`'s return type through normal inference.

### 7.2 `if` with IO branches

```clojure
(if (> x 0)
  (print (show x))    ; (IO Int)
  (pure 0))           ; (IO Int)
```

Standard `if` typing requires both branches to unify. Both produce `(IO Int)`, so unification succeeds with result `(IO Int)`.

If the user writes:

```clojure
(if (> x 0)
  (print (show x))    ; (IO Int)
  0)                   ; Int
```

Unification tries to unify `(IO Int)` with `Int`. `Type::ADT("IO", [Int])` does not unify with `Type::Int`. Type error: "branches of if have different types: (IO Int) vs Int". This is the correct behavior per spec 10.7.2.

### 7.3 IO in `let` bindings

```clojure
(let [io (print "hello")]
  io)
```

1. `(print "hello")` has type `(IO Int)`.
2. `io` is bound to `(IO Int)`.
3. The body `io` has type `(IO Int)`.

This is standard let-binding. The IO value is a description of deferred work — it does not execute at the let-binding point. Semantically, `io` is a data structure (an `Effect` node). The typechecker treats it as any other value.

### 7.4 Nested IO

```clojure
(pure (pure 42))    ; (IO (IO Int))
```

1. Inner: `(pure 42)` has type `(IO Int)`.
2. Outer: `(pure (IO-Int-value))` has type `(IO (IO Int))`.

This is valid. `IO (IO Int)` is a legitimate type — an IO computation that produces another IO computation. The user would need two levels of `bind` to extract the inner `Int`. Standard ADT nesting handles this with no special rules.

### 7.5 IO in data structures

```clojure
(Some (print "hello"))    ; (Option (IO Int))
```

IO values can be stored in any data structure. `(Option (IO Int))` means an optional deferred computation. This works through standard ADT type parameter instantiation.

### 7.6 Functions returning IO

```clojure
(defn make-printer [prefix]
  (fn [msg] (print (str-concat prefix msg))))
;; make-printer :: (Fn [String] (Fn [String] (IO Int)))
```

Higher-order functions that return IO-producing closures work through standard function type inference. The closure's return type is `(IO Int)` because `print` returns `(IO Int)`.

### 7.7 Constrained polymorphism and IO

IO does not interact with trait constraints. There is no `IO` trait — IO is a concrete ADT. A function like:

```clojure
(defn show-and-print [x] (print (show x)))
;; show-and-print :: forall :Display a. (Fn [a] (IO Int))
```

has a constraint on `a` (must implement `Display`) and returns `IO Int`. The constraint comes from `show`, not from IO. Standard constrained polymorphism handles this.

## 8. Platform Function Registration

Platform functions (like `print`, `read-line`) are registered with `PrimitiveKind::PlatformEffect` and IO return types. The typechecker validates that platform function types have IO return types.

### Validation

When a platform function is registered, the typechecker checks that its return type matches `Type::ADT("IO", _)`. This is a simple pattern match:

```rust
fn validate_io_return(name: &str, ty: &Type) -> Result<(), CranelispError> {
    let ret = match ty {
        Type::Fn(_, ret) => ret.as_ref(),
        _ => return Err(/* "platform function must be a function type" */),
    };
    match ret {
        Type::ADT(name, _) if name.as_ref() == "IO" => Ok(()),
        _ => Err(/* "platform function must return IO type" */),
    }
}
```

This validation runs at platform loading time (when the typechecker registers platform function types from the manifest). It prevents platform DLLs from declaring non-IO-returning effectful functions.

## 9. REPL Introspection

After seeding, the IO type should be visible through REPL commands:

- `/info IO` — shows the type definition with all three constructors (Pure, Effect, Bind). Bind is listed but marked "(internal)".
- `/sig Pure` — shows `Pure :: (Fn [a] (IO a))`.
- `/sig bind` — shows `bind :: (Fn [(IO a) (Fn [a] (IO b))] (IO b))`.
- `/doc bind` — shows the docstring from registration.

No special REPL handling is needed — the existing introspection infrastructure reads from `TypeDefInfo` and `ModuleEntry`, both of which are populated by the seeding procedure.

## 10. Implementation Checklist

1. Add `internal: bool` field to `ConstructorInfo` in `crates/cranelisp-types/src/check.rs`.
2. Update `design/arch/interfaces.md` to reflect the new field.
3. Add `internal: false` to all existing `ConstructorInfo` construction sites.
4. Implement `register_io_type()` in the typechecker's builtins module.
5. Implement `add_internal_bind_constructor()` to add Bind with `internal: true`.
6. Implement `register_bind_primitive()` to register `bind` as an inline primitive.
7. Add enforcement: reject construction and pattern matching on internal constructors.
8. Add `validate_main()` logic to `check_program()` for batch mode.
9. Add `validate_io_return()` for platform function registration.
10. Write tests: IO type inference, bind type inference, main validation (positive + negative), internal constructor rejection.

## 11. Sketch References

| Sketch file | What to reference |
|---|---|
| `sketch/src/typechecker/primitives.rs:605-657` | `register_io_type()` — synthetic TypeDef construction |
| `sketch/src/typechecker/primitives.rs:419-447` | `register_bind_primitive()` — bind scheme construction |
| `sketch/src/typechecker/primitives.rs:723-761` | `add_internal_bind_constructor()` — internal constructor seeding |
| `sketch/src/typechecker/program.rs:235-263` | `main` validation logic |
| `sketch/src/typechecker/primitives.rs:1076-1138` | `validate_io_return()` and its tests |
| `sketch/src/typechecker/adt.rs:11-96` | `register_type_def()` — constructor registration flow |

## 12. Rejected Alternatives

### `Type::IO(Box<Type>)` dedicated variant

Rejected by `/arch` (SPRINT.md Architecture Review). Would add a branch to every `match` on `Type`, violate principle 2 (narrow interfaces), and contradict spec 10.1.1 which says IO is an ordinary ADT. The sketch uses `Type::ADT("IO", ...)` and it works.

### `bind` as an extern function instead of inline primitive

Would add function call overhead to every IO chain operation. `bind` allocates a 24-byte Bind node — three stores and one alloc call. This is simple enough to inline. The sketch uses inline codegen for `bind` (see `sketch/src/codegen/primitives.rs`). An extern function would also make RC management harder (the inline approach lets the backend control inc/dec at the call site).

### `pure` as a primitive

Would work but adds unnecessary complexity. `pure` is `(defn pure [x] (Pure x))` — a trivial wrapper around a constructor. Making it a primitive would duplicate what the constructor already does. The spec says `pure` is an ordinary function.

### Seeding Effect as internal

The spec does not mark Effect as internal. While users do not typically construct Effect values directly (platform functions do), there is no reason to prevent it at the type level. Effect's typing as `(Fn [a] (IO a))` is sound — constructing an Effect with a non-thunk value would produce a runtime failure when the trampoline tries to invoke it, but this is analogous to constructing any ADT with incorrect field semantics (the type system tracks types, not runtime invariants of opaque pointers).

If future experience shows that user-constructed Effect nodes cause confusion, this can be revisited by marking Effect as internal. This would be an additive change (setting `internal: true`).
