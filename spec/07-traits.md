# 7. Traits [S21]

This section defines the trait system of Cranelisp -- the mechanism for ad-hoc polymorphism. Traits declare method signatures parameterized over a type (or type constructor). Implementations provide concrete method bodies for specific types. All trait method calls are resolved at compile time via static dispatch.

## 7.1 Trait Declaration [Tested]

A trait declares one or more method signatures parameterized over an implementing type.

```ebnf
trait_decl     = '(' 'deftrait' trait_head docstring? method_sig+ ')'
trait_head     = trait_name                  (* simple trait *)
               | '(' trait_name con_var ')'  (* higher-kinded trait, see 7.2 *)
trait_name     = uppercase_symbol
method_sig     = required_method | default_method
required_method = '(' method_name docstring? '[' param+ ']' type_expr ')'
default_method  = '(' method_name docstring? '[' param+ ']' body ')'
param           = ':' type_expr symbol | symbol
method_name    = symbol
```

The `deftrait` form introduces a named trait with one or more method signatures. All methods use named parameters in square brackets. Required methods end with a return type expression; default methods end with a body expression.

**Parameters:** Bare parameter names default to the implementing type (`self`). Annotated parameters (`:Type name`) have explicit types. `self` (lowercase) in return type position refers to the implementing type (see §7.1.1).

**Disambiguation:** The parser distinguishes required from default methods positionally. The element immediately following the parameter bracket is always the return type; if a further element follows it, that element is the default body:
- `(method_name "doc"? [params] ret_type)` -- a return type follows the bracket and nothing else: the method is required.
- `(method_name "doc"? [params] ret_type body)` -- a body expression follows the return type: the method has a default implementation.

A return type is a type expression: `self` (the implementing type), a named type (`Int`, `Bool`, `String`), an applied type (`(Option self)`, `(Fn [a] b)`), or a type variable.

**Example:** A standard library might define traits for arithmetic, equality, and display:

```clojure
(deftrait Display "Convert to string representation"
  (show "Convert value to string" [x] String))

(deftrait Num "Numeric arithmetic operations"
  (+ "Add two values" [a b] self)
  (- "Subtract two values" [a b] self)
  (* "Multiply two values" [a b] self)
  (/ "Divide two values" [a b] self))

(deftrait Eq "Equality comparison"
  (= "Test equality" [a b] Bool))

(deftrait Ord "Ordering comparisons"
  (< "Test less-than" [a b] Bool)
  (> "Test greater-than" [a b] Bool)
  (<= "Test less-than-or-equal" [a b] (not (> a b)))
  (>= "Test greater-than-or-equal" [a b] (not (< a b))))
```

### 7.1.1 The `self` Type [Tested tests/spec_07_traits.rs::trait_method_no_impl_then_recovery]

Bare (unannotated) parameter names in a method signature have the implementing type. In return type position (or any type-expression position), `self` (lowercase) explicitly refers to the implementing type. When a type implements a trait, the implementing type is substituted for `self` and for all bare parameter types.

> **Note on spelling.** The keyword for the implementing type is the lowercase token `self` — both as the implicit type of a bare parameter and as an explicit return type. There is no capitalized `Self`; writing `Self` denotes an ordinary named type and fails resolution unless such a type exists. This matches the as-built compiler (the frontend maps only the lowercase token `self` to the implementing type) and the standard library, e.g. `(+ [a b] self)`.

```clojure
;; In (deftrait Eq (= [a b] Bool)):
;;   For (impl Eq Int ...): a, b become Int, so = :: Int -> Int -> Bool
;;   For (impl Eq Float ...): a, b become Float, so = :: Float -> Float -> Bool
```

`self` is NOT a type variable -- it is resolved at impl time to the concrete target type. It may appear in return types and in applied type positions (e.g., `(Option self)`).

A trait MUST contain at least one method signature. Each method signature MUST contain at least one parameter of the implementing type (bare or annotated as `self`), except for higher-kinded trait methods (see 7.2).

### 7.1.2 Docstrings

Both traits and individual methods MAY have docstrings. A docstring is a string literal appearing immediately after the trait name (or trait head) or immediately after the method name. Docstrings are accessible through REPL introspection commands.

```clojure
(deftrait Describable "Trait for human-readable descriptions"
  (describe "Return a description string" [x] String))
```

### 7.1.3 Multiple Methods

A trait MAY declare multiple methods. An implementation of the trait MUST provide definitions for all declared methods that do not have default implementations (see 7.1.5).

```clojure
(deftrait Num "Numeric arithmetic operations"
  (+ "Add two values" [a b] self)
  (- "Subtract two values" [a b] self)
  (* "Multiply two values" [a b] self)
  (/ "Divide two values" [a b] self))
```

### 7.1.5 Default Method Implementations [Tested tests/spec_07_traits::default_method_used_when_not_overridden]

A method signature MAY include a default body. Default methods have a body expression as the last element (rather than a return type). The return type of a default method is inferred from its body.

The default body provides an implementation that is used when an `impl` block does not explicitly override the method. Default methods may call other methods of the same trait.

```clojure
(deftrait Ord "Ordering comparisons"
  (< "Test less-than" [a b] Bool)
  (> "Test greater-than" [a b] Bool)
  (<= "Test less-than-or-equal" [a b] (not (> a b)))
  (>= "Test greater-than-or-equal" [a b] (not (< a b))))
```

In the example above, `<=` and `>=` have default implementations derived from `<` and `>`. An `impl Ord` block need only provide `<` and `>`:

```clojure
(impl Ord MyType
  (defn < [x y] ...)
  (defn > [x y] ...))
;; <= and >= are synthesized from the defaults
```

An impl MAY override a default method by providing an explicit definition:

```clojure
(impl Ord Int
  (defn < [x y] (lt-i64 x y))
  (defn > [x y] (gt-i64 x y))
  (defn <= [x y] (le-i64 x y))   ;; explicit override (e.g. for performance)
  (defn >= [x y] (ge-i64 x y)))
```

**Compilation model:** Default bodies are stored as raw S-expressions on the trait declaration. When an `impl` block omits a method that has a default, a `Defn` is synthesized from the default body with the mangled name (e.g. `<=$MyType`). The synthesized defn is type-checked and compiled identically to an explicit impl method, with the dispatch parameter's type pre-unified with the impl target type.

**Restriction:** Default method implementations are NOT supported on higher-kinded traits. A `deftrait` with type constructor parameters (e.g. `(deftrait (Functor f) ...)`) MUST NOT contain methods with default bodies. This is checked at parse time.

### 7.1.4 Type Expressions in Signatures

Return types and parameter annotations MAY use any valid type expression:

- `self` -- the implementing type (in return type or annotation position)
- Concrete types: `Int`, `Bool`, `String`, `Float`
- Parameterized types: `(Option a)`, `(Option self)`
- Function types: `(Fn [a] b)`
- Type variables: lowercase names like `a`, `b`

Bare (unannotated) parameter names always have the implementing type. To give a parameter a different type, use a `:Type name` annotation.

```clojure
(deftrait Mappable
  (map-val [:(Fn [a] b) f x] self))

(deftrait Convertible
  (convert [:String s] Int))        ;; s is String, not self
```

## 7.2 Higher-Kinded Traits [Tested tests/spec_07_traits::hkt_deftrait_declaration_with_type_constructor_parameter_succeeds]

A higher-kinded trait abstracts over type constructors (kind `* -> *`) rather than concrete types (kind `*`).

```ebnf
hkt_trait_decl = '(' 'deftrait' '(' trait_name con_var ')' docstring? method_sig+ ')'
con_var        = lowercase_symbol
```

The trait head is wrapped in parentheses with a lowercase type constructor variable.

```clojure
(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container"
    [:(Fn [a] b) func :(f a) x] (f b)))
```

### 7.2.1 Constructor Variables

The lowercase identifier `f` in `(Functor f)` is a **constructor variable** -- it ranges over type constructors that take one or more type arguments. In method signatures, constructor application is written as `(f a)`, meaning "the constructor `f` applied to type `a`".

The arity of a constructor variable is determined by its usage in method signatures. If `f` appears as `(f a)`, it has arity 1 (kind `* -> *`).

### 7.2.2 Method Signatures

In an HKT trait, all method parameters use named params with explicit type annotations (bare names would default to the implementing type, which is a type constructor -- not useful as a value type):

```clojure
(deftrait (Functor f) "Mappable container"
  (fmap [:(Fn [a] b) func :(f a) x] (f b)))
;;        ^function          ^input    ^output
;;       a -> b            f a       f b
```

The method `fmap` takes a function `(Fn [a] b)` named `func` and a value of type `(f a)` named `x`, returning a value of type `(f b)`.

### 7.2.3 Kind Checking

An implementation MUST validate that the impl target's type parameter count matches the expected constructor arity. There is no explicit kind annotation syntax; kind checking is implicit.

```clojure
;; OK -- Option takes 1 type param, matches (f a)
(impl Functor Option ...)

;; ERROR -- Int is not a type constructor
(impl Functor Int ...)
;; => "Int is not a type constructor (trait Functor expects arity 1)"
```

Primitive types (`Int`, `Bool`, `String`, `Float`) MUST be rejected as HKT impl targets.

## 7.3 Trait Implementation [Tested tests/spec_07_traits::trait_impl_concrete_type, tests/spec_07_traits::user_trait_simple, tests/spec_07_traits::trait_multiple_impls]

The `impl` form provides method bodies for a trait applied to a specific type.

```ebnf
trait_impl   = '(' 'impl' trait_name impl_target method_def+ ')'
impl_target  = concrete_target | polymorphic_target | hkt_target
concrete_target    = type_name
polymorphic_target = '(' type_name constraint* type_var+ ')'
hkt_target         = type_constructor_name
method_def   = '(' 'defn' method_name '[' param* ']' body ')'
constraint   = ':' trait_name
```

There are three forms of trait implementation.

### 7.3.1 Concrete Implementation [Tested tests/spec_07_traits::user_trait_simple, crates/cranelisp-typecheck/src/traits/tests.rs::test_register_trait_impl, tests/spec_05_definitions::deftrait_impl_and_dispatch]

The simplest form targets a specific concrete type.

**Example:** A standard library typically provides trait implementations for primitive types:

```clojure
(impl Display Int
  (defn show [x] (int-to-string x)))

(impl Num Int
  (defn + [x y] (add-i64 x y))
  (defn - [x y] (sub-i64 x y))
  (defn * [x y] (mul-i64 x y))
  (defn / [x y] (div-i64 x y)))

(impl Eq Int
  (defn = [x y] (eq-i64 x y)))

(impl Ord Int
  (defn < [x y] (lt-i64 x y))
  (defn > [x y] (gt-i64 x y))
  (defn <= [x y] (le-i64 x y))
  (defn >= [x y] (ge-i64 x y)))
```

Each `defn` in the impl block MUST correspond to a method declared in the trait. The parameter count MUST match the number of parameters in the trait's method signature. An impl block MUST provide definitions for all methods in the trait that do not have default implementations (see 7.1.5). Methods with defaults are automatically synthesized if not explicitly provided.

**Method-name vs field-accessor collision (FIXME 0365/0439, settled S91).** [Tested+Neg tests/spec_05_definitions::impl_method_colliding_with_field_accessor_rejected_neg] An `impl` whose method name equals an existing **field-accessor** name of the impl target type MUST be **rejected at impl time**, with a diagnostic naming the colliding name and both definition sites (the `deftype` field and the `impl` method). For example, given `(deftype Box [:Int v])` (whose canonical accessor is `Box.v`, §5.2.6), an `(impl SomeTrait Box (defn v [x] …))` is a compile-time error. This is the no-silent-overload-consistent resolution: it prevents the target type from having two distinct `(Fn [Box] …)` denotations for the same dotted name, so the canonical accessor `Box.v` (§8.5.2) always names exactly one thing and never has to disambiguate field-accessor-vs-trait-method. Casing makes the rule's scope exact and complete: constructors are uppercase (§1.4), while field accessors and trait methods are both lowercase, so a field-accessor name can collide *only* with a trait-method name — precisely the case this check covers; a constructor name can never collide with either.

### 7.3.2 Concrete Parameterized Implementation

An impl MAY target a fully applied parameterized type:

```clojure
(impl Display (Option Int)
  (defn show [opt]
    (match opt
      [None "None"
       (Some x) (show x)])))
```

This provides a Display implementation specifically for `(Option Int)`.

### 7.3.3 Polymorphic Implementation with Constraints

An impl MAY target a parameterized type with constrained type variables. Constraints are specified with `:TraitName` prefixes on type variables:

```clojure
(impl Display (Option :Display a)
  (defn show [opt]
    (match opt
      [None "None"
       (Some x) (show x)])))
```

This provides a Display implementation for `(Option a)` where `a` itself has a Display implementation. The constraint `:Display a` requires that the inner type supports `show`.

When this polymorphic impl is used at a call site with a concrete type, the method is monomorphised. For example, `(show (Some 42))` resolves `a` to `Int` and generates a specialization `show$Option$Int` that internally calls `show$Int`.

The implementation MUST search for matching impls in the following order:
1. Concrete impls (exact type match)
2. Polymorphic impls (with constraint satisfaction)

### 7.3.4 Higher-Kinded Implementation [Tested tests/spec_07_traits::hkt_impl_targets_bare_type_constructor_not_applied_form]

An HKT impl targets a bare type constructor name:

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

(impl Functor Seq
  (defn fmap [f s]
    (match s
      [SeqNil SeqNil
       (SeqCons h t) (SeqCons (f h) (fn [] (fmap f (t))))])))
```

The target is the type constructor name alone (e.g., `Option`, not `(Option a)`). The implementation MUST validate that the target is a type constructor whose arity matches the trait's constructor variable.

## 7.4 Method Resolution (Static Dispatch) [Tested tests/spec_05_definitions::deftrait_impl_and_dispatch]

ALL trait method calls MUST be resolved at compile time. There is no runtime dispatch mechanism. Every call to a trait method resolves to a specific implementation based on the concrete type at the call site.

### 7.4.1 Resolution Process

When the typechecker encounters a trait method call:

1. Look up the method name in the type environment to obtain its polymorphic type from the trait declaration.
2. Instantiate the scheme with fresh type variables.
3. Infer the types of the call's arguments and unify with the instantiated parameter types.
4. Record a **pending resolution**: the call site, method name, and the (possibly still-unresolved) dispatch type.
5. After all expressions in the compilation unit are type-checked, apply the final substitution to resolve the dispatch type to a concrete type.
6. Look up the matching impl for the concrete dispatch type and record the resolved mangled name.

### 7.4.2 Name Mangling

Each resolved trait method call maps to a **trait-qualified** mangled name of the form `Trait.method$Type`. The trait name prefix ensures no collisions when different traits define the same method name (e.g., `Num.+$Int` vs `Unchecked.+$Int`).

**Example:** Given traits like those in Section 7.7, typical mangled names would be:

| Call | Mangled Name |
|---|---|
| `(show 42)` | `Display.show$Int` |
| `(show true)` | `Display.show$Bool` |
| `(show 3.14)` | `Display.show$Float` |
| `(+ 1 2)` | `Num.+$Int` |
| `(+ 1.0 2.0)` | `Num.+$Float` |
| `(= 1 1)` | `Eq.=$Int` |
| `(< 3 4)` | `Ord.<$Int` |
| `(fmap inc (Some 5))` | `Functor.fmap$Option` |
| `(fmap inc (list 1 2 3))` | `Functor.fmap$List` |
| `(show (Some 42))` | `Display.show$Option$Int` |

For HKT methods, the mangled name uses the bare constructor name (e.g., `Functor.fmap$Option`), not the fully applied type.

For polymorphic impl specializations, the mangled name includes the concrete inner types (e.g., `Display.show$Option$Int`).

### 7.4.2a Same-Named Methods and Disambiguation

Different traits MAY define methods with the same name. When only one such trait is imported into a module's scope, the bare name resolves unambiguously. When multiple traits with the same method name are visible, the bare name becomes ambiguous and the compiler reports an error suggesting qualified forms.

**Disambiguation syntax:** Use `Trait.method` to specify which trait's method to call:

```clojure
(Num.+ x y)        ; explicitly calls Num's +
(Unchecked.+ x y)  ; explicitly calls Unchecked's +
```

The `Unchecked` trait is NOT exported from the prelude. Users who need it MUST explicitly import it: `(import [core/unchecked [Unchecked]])`. If both `Num` and `Unchecked` are in scope, bare `+` is ambiguous and requires qualification.

### 7.4.3 Impl Search Order

When resolving a method call on a given type, the implementation MUST search in the following order:

1. **Concrete impls**: An exact match for the fully applied type (e.g., `impl Display (Option Int)`).
2. **Bare impls**: A match for the outer type constructor (e.g., `impl Functor Option` for any `(Option a)`).
3. **Polymorphic impls**: A match where the type structure matches and all constraints are satisfied (e.g., `impl Display (Option :Display a)` matches `(Option Int)` because `Int` has a Display impl).

The first matching impl is used. If no impl matches, a compile-time error MUST be reported.

### 7.4.4 Resolution Ordering

Resolution happens in phases after type inference, in a specific order:

1. **Constrained function detection**: Identify functions that use trait methods on unresolved type variables (see 7.8).
2. **First method resolution pass**: Resolve trait methods where types are concrete. When the dispatch type is still a type variable with multiple candidate impls, defer resolution and record a constraint.
3. **Overload dispatch**: Resolve multi-signature function calls using concrete parameter types.
4. **Second method resolution pass**: Resolve remaining methods, including those whose types became concrete after overload resolution.

This ordering is critical. Method resolution must accommodate the possibility that some types are not yet concrete during early passes.

## 7.5 Operators as Trait Methods [Tested tests/spec_05_definitions::deftrait_impl_and_dispatch]

Operator symbols (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`) have no special syntactic status. `(+ 1 2)` is parsed as a regular function application `Apply(Var("+"), [1, 2])`. When defined as trait methods by a library, they dispatch like any other method call through the standard trait resolution mechanism.

**Example:** When a standard library defines these symbols as trait methods, they are resolved at compile time:

| Operator | Trait | Signature |
|---|---|---|
| `+` | `Num` | `self -> self -> self` |
| `-` | `Num` | `self -> self -> self` |
| `*` | `Num` | `self -> self -> self` |
| `/` | `Num` | `self -> self -> self` |
| `=` | `Eq` | `self -> self -> Bool` |
| `<` | `Ord` | `self -> self -> Bool` |
| `>` | `Ord` | `self -> self -> Bool` |
| `<=` | `Ord` | `self -> self -> Bool` |
| `>=` | `Ord` | `self -> self -> Bool` |

```clojure
(+ 1 2)       ; → 3    (resolved to +$Int)
(* 3.0 4.0)   ; → 12.0 (resolved to *$Float)
(= 1 1)       ; → true (resolved to =$Int)
(< 3 4)       ; → true (resolved to <$Int)
(>= 5.0 5.0)  ; → true (resolved to >=$Float)
```

An implementation SHOULD compile operator trait methods for `Int` and `Float` to inline machine instructions (integer add, float multiply, etc.) rather than function calls, so that the trait system imposes zero overhead for primitive arithmetic and comparisons.

## 7.6 Operators as First-Class Values [Tested tests/spec_07_traits::operator_as_first_class_value]

Trait method names, including operators, are ordinary symbols. They MAY be bound to variables and passed as arguments to higher-order functions.

```clojure
(let [f +] (f 1 2))           ; → 3
(let [cmp <] (cmp 3 4))       ; → true
```

When an operator (or any trait method) is used as a value rather than called directly, the implementation MUST wrap it in a closure-compatible representation. The resulting closure captures no environment but carries a code pointer to a wrapper function that dispatches to the correct implementation.

Note: When used as a value, the operator's type is the fully polymorphic trait method type (e.g., `Num a => a -> a -> a` for `+`). The concrete dispatch type is determined at the point where the closure is actually called.

## 7.7 Standard Library Traits (Non-Normative) [Tested]

This section is **non-normative**. The traits below (Num, Eq, Ord, Display, Functor) are not language primitives — they are ordinary `deftrait` declarations defined in the standard library's core modules. They appear here as illustrative examples of the trait mechanism defined in §§7.1–7.6, and to document the semantic contracts (checked arithmetic, IEEE 754 comparison, etc.) that a conforming standard library is expected to provide. The authoritative home for these definitions is the standard library itself (e.g., `core/numerics`, `core/formats`); the REPL displays them under their stdlib-qualified names (e.g., `core.numerics/+`), not as builtins.

**Implementation note — compiler-seeded core traits:** The four core traits (Num, Eq, Ord, Display) and their implementations for primitive types (Int, Float, Bool, String) are defined as Cranelisp `deftrait`/`impl` forms evaluated through the normal pipeline during compiler initialization. They live in the compiler-seeded `primitives` module — the same synthetic module that provides primitive types and functions. This makes them available before the standard library loads. The standard library re-exports these traits via the prelude for user convenience and may layer additional higher-level traits on top, but the core trait *declarations* and *primitive-type implementations* are language infrastructure, not stdlib content. (See Decision 17 in `design/arch/CLAUDE.md`.)

The following traits are available in all programs that load the prelude. They are not compiler intrinsics — they are ordinary trait declarations with ordinary implementations. A standard library typically provides these traits because operators and string conversion depend on them.

### 7.7.1 Num

Numeric arithmetic operations.

**Declaration:**

```clojure
(deftrait Num "Numeric arithmetic operations"
  (+ "Add two values" [a b] self)
  (- "Subtract two values" [a b] self)
  (* "Multiply two values" [a b] self)
  (/ "Divide two values" [a b] self))
```

**Typical implementations:** A standard library typically provides `Num` implementations for `Int` and `Float`.

**Semantics:**

| Type | `+` | `-` | `*` | `/` |
|---|---|---|---|---|
| `Int` | Checked addition (panics on overflow) | Checked subtraction (panics on overflow) | Checked multiplication (panics on overflow) | Checked division (panics on division by zero or MIN/-1 overflow) |
| `Float` | IEEE 754 addition | IEEE 754 subtraction | IEEE 754 multiplication | IEEE 754 division |

**Example:**

```clojure
(+ 1 2)       ; → 3
(- 10 3)      ; → 7
(* 3.0 4.0)   ; → 12.0
(/ 7 2)       ; → 3   (integer division truncates)
(/ 7.0 2.0)   ; → 3.5
(/ 1 0)       ; → panic: "integer division by zero"
(+ 9223372036854775807 1)  ; → panic: "integer overflow in +"
```

### 7.7.1a Unchecked

Unchecked arithmetic operations. Same method names as `Num` but without overflow/div-by-zero checks. Not in the prelude — must be explicitly imported from `core/unchecked`.

**Declaration:**

```clojure
(deftrait Unchecked "Unchecked arithmetic (wraps on overflow, traps on div-by-zero)"
  (+ "Unchecked addition" [a b] self)
  (- "Unchecked subtraction" [a b] self)
  (* "Unchecked multiplication" [a b] self)
  (/ "Unchecked division" [a b] self))
```

**Semantics:**

| Type | `+` | `-` | `*` | `/` |
|---|---|---|---|---|
| `Int` | Two's complement addition (wraps on overflow) | Two's complement subtraction (wraps on overflow) | Two's complement multiplication (wraps on overflow) | Signed integer division (traps on division by zero) |
| `Float` | IEEE 754 addition | IEEE 754 subtraction | IEEE 754 multiplication | IEEE 754 division |

**Example:**

```clojure
(import [core/unchecked [Unchecked]])
(Unchecked.+ 9223372036854775807 1)  ; wraps to -9223372036854775808
```

### 7.7.2 Eq

Equality comparison.

**Declaration:**

```clojure
(deftrait Eq "Equality comparison"
  (= "Test equality" [a b] Bool))
```

**Typical implementations:** A standard library typically provides `Eq` implementations for `Int` and `Float`.

**Semantics:**

| Type | `=` |
|---|---|
| `Int` | Bitwise equality of 64-bit integers |
| `Float` | IEEE 754 equality (`NaN /= NaN`) |

**Example:**

```clojure
(= 1 1)       ; → true
(= 1 2)       ; → false
(= 1.0 1.0)   ; → true
```

### 7.7.3 Ord

Ordering comparisons.

**Declaration:**

```clojure
(deftrait Ord "Ordering comparisons"
  (< "Test less-than" [a b] Bool)
  (> "Test greater-than" [a b] Bool)
  (<= "Test less-than-or-equal" [a b] (not (> a b)))
  (>= "Test greater-than-or-equal" [a b] (not (< a b))))
```

**Typical implementations:** A standard library typically provides `Ord` implementations for `Int` and `Float`.

**Semantics:**

| Type | Ordering |
|---|---|
| `Int` | Signed integer comparison |
| `Float` | IEEE 754 ordered comparison |

**Example:**

```clojure
(< 1 2)       ; → true
(> 5 3)       ; → true
(<= 4.0 4.0)  ; → true
(>= 3 5)      ; → false
```

### 7.7.4 Display

String conversion for human-readable output.

**Declaration:**

```clojure
(deftrait Display "Convert to string representation"
  (show "Convert value to string" [x] String))
```

**Typical implementations:** A standard library typically provides `Display` implementations for `Int`, `Float`, `Bool`, and `String`.

**Semantics:**

| Type | `show` result |
|---|---|
| `Int` | Decimal string representation (e.g., `"42"`, `"-7"`) |
| `Float` | Decimal string representation (e.g., `"3.14"`, `"-0.5"`) |
| `Bool` | `"true"` or `"false"` |
| `String` | The string itself (identity) |

**Example:**

```clojure
(show 42)       ; → "42"
(show true)     ; → "true"
(show "hello")  ; → "hello"
(show 3.14)     ; → "3.14"
```

### 7.7.5 Functor [Tested tests/spec_07_traits::hkt_deftrait_declaration_with_type_constructor_parameter_succeeds]

Maps a function over a type constructor. This is a higher-kinded trait (see 7.2).

**Declaration:**

```clojure
(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container"
    [:(Fn [a] b) func :(f a) x] (f b)))
```

**Typical implementations:** A standard library typically provides `Functor` implementations for `Option`, `List`, and `Seq`.

**Type:** `fmap :: (a -> b) -> f a -> f b`

**Semantics:** `fmap` applies a function to every element inside a container, preserving the container's structure.

| Type | `fmap` behavior |
|---|---|
| `Option` | Applies function to the value inside `Some`; `None` maps to `None` |
| `List` | Applies function to every element, producing a new list |
| `Seq` | Applies function lazily to each element of the lazy sequence |

**Example:**

```clojure
(fmap inc (Some 5))                     ; → (Some 6)
(fmap inc None)                         ; → None
(fmap inc (list 1 2 3))                 ; → (list 2 3 4)
(fmap (fn [x] (* x 2)) (Some 3))       ; → (Some 6)
```

**Functor laws:** Implementations SHOULD satisfy the functor laws, though these are not enforced by the compiler:

1. **Identity**: `(fmap identity x)` is equivalent to `x`
2. **Composition**: `(fmap (comp g f) x)` is equivalent to `(fmap g (fmap f x))`

## 7.8 Constrained Polymorphism Interaction [Tested tests/spec_07_traits::constrained_polymorphism_int_then_float]

When a trait method is called on a type that is still an unresolved type variable during inference, and multiple implementations exist for that trait, the enclosing function becomes a **constrained polymorphic function**. Rather than producing a type error, the type variable acquires a trait constraint.

```clojure
(defn add [x y] (+ x y))
;; add :: (fn [:Num a a] a)
```

The function `add` uses `+` (a `Num` method) on unresolved type variables. Since both `Int` and `Float` have `Num` implementations, the typechecker cannot resolve the call statically. Instead, `add` is typed as `(fn [:Num a a] a)` -- polymorphic with a `Num` constraint on `a`.

### 7.8.1 Monomorphisation

Constrained polymorphic functions are monomorphised at call sites. Each call with concrete argument types generates a specialization:

```clojure
(add 1 2)       ; generates add$Int+Int, uses +$Int
(add 1.0 2.0)   ; generates add$Float+Float, uses +$Float
```

Each specialization resolves its deferred trait method calls with the concrete types. The same `+` call in the function body resolves to `+$Int` in one specialization and `+$Float` in another.

See section 3 (Type System) for full details on constrained polymorphism and monomorphisation.

### 7.8.2 Explicit Constraints

Constraints MAY be annotated explicitly on parameters using the `:TraitName param` syntax:

```clojure
(defn add [:Num x :Num y] (+ x y))
```

Explicit annotations and inferred constraints produce identical results. Explicit annotations serve as documentation and MAY help produce clearer error messages.

### 7.8.3 Limitations

- Constrained polymorphic functions MUST NOT be used as first-class values. `(let [f add] ...)` where `add` is constrained polymorphic produces a compile-time error -- the concrete type must be known at the call site.
- HKT trait methods are NOT constrained polymorphic functions. They dispatch through the trait resolution mechanism, not through monomorphisation. Writing a generic function like `(defn map-inc [xs] (fmap inc xs))` that is polymorphic over all Functors is not supported.

## 7.9 User-Defined Traits [Tested tests/spec_07_traits::user_trait_simple]

Users MAY define their own traits using the same `deftrait` and `impl` forms. User-defined traits are first-class citizens of the trait system and participate in the same dispatch mechanism as built-in traits.

### 7.9.1 Declaration and Implementation

```clojure
(deftrait Describable "Types that can describe themselves"
  (describe "Return a human-readable description" [x] String))

(impl Describable Int
  (defn describe [x]
    (show x)))

(impl Describable Bool
  (defn describe [x]
    (if x "yes" "no")))
```

### 7.9.2 Usage

User trait methods are called with the same syntax as any function:

```clojure
(describe 42)       ; → "42"  (resolved to describe$Int)
(describe true)     ; → "yes" (resolved to describe$Bool)
```

### 7.9.3 Polymorphic ADT Implementations

User traits MAY have polymorphic implementations for algebraic data types, using the same constraint syntax as built-in traits:

```clojure
(deftrait Describable
  (describe [x] String))

(impl Describable (Option :Describable a)
  (defn describe [self]
    (match self
      [None "nothing"
       (Some x) (describe x)])))
```

## 7.10 REPL Introspection [Tested tests/spec_07_traits::deftrait_display_shows_classification]

Implementations that provide a REPL SHOULD support introspection of traits, methods, and operators.

### 7.10.1 Trait Descriptions

Entering a trait name at the REPL SHOULD display its declaration:

```
cranelisp> Display
Display :: trait (show :: (fn [a] String))
```

HKT trait declarations display with their type parameters:

```
cranelisp> Functor
Functor :: (deftrait (Functor f) (fmap [:(Fn [a] b) func :(f a) x] (f b)))
```

### 7.10.2 Method Descriptions

Entering a trait method name SHOULD display its polymorphic type with trait qualification:

```
cranelisp> show
show :: Display a => (fn [a] String)

cranelisp> +
+ :: Num a => (fn [a a] a)

cranelisp> =
= :: Eq a => (fn [a a] Bool)

cranelisp> <
< :: Ord a => (fn [a a] Bool)

cranelisp> fmap
Functor.fmap :: (Fn [(Fn [a] b) (:Functor f a)] (f b))
```

## 7.11 Scope and Visibility [Tested tests/spec_07_traits::trait_deftrait_impl_in_child_module_imported_dispatch_from_parent]

Trait declarations and implementations participate in the module system (see section 8).

- A `deftrait` form registers the trait and all its method names in the declaring module.
- An `impl` form's method implementations are visible per the rule in [§5.11.1](05-definitions.md#5111-impl-visibility--transitive-import-closure) (visibility = reachability of the trait + type names). Where the implementation internally records the impl entry — which module's symbol table holds it — is **implementation-defined**, not pinned by this spec.
- Trait methods are accessible via import like any other symbol.
- Method names from different traits MAY collide. If two traits declare methods with the same name and both are in scope, the result is an ambiguous name error at the call site.

Note: There is no mechanism for disambiguating same-named methods from different traits at a call site. Users SHOULD choose distinct method names across traits, or use qualified references (`module/method`) to avoid ambiguity.

### 7.11.1 Impl Visibility — Transitive Import Closure [S66]

`impl` has no private variant. A trait implementation declared in module L is visible at any call site in module N where **both** the trait and the type are reachable from N through the transitive closure of N's `import` declarations. N does not need to import L directly; the impl follows the trait and type wherever those names propagate (via re-export chains, glob imports, etc.).

This rule has three consequences for trait method resolution (see §7.4):

1. **Impl discovery is bounded by the import graph, not the universe of compiled modules.** When the typechecker resolves a trait method call, it looks for impls only among modules reachable from the current module's import closure.
2. **Re-exporting a trait or type implicitly re-exports its impls.** See [§8.4.8](08-modules.md#848-implicit-impl-re-export). Authors do not — and cannot — enumerate impls in `export` lists.
3. **Impl visibility is determined by the visibility of the trait + type pair.** An impl becomes invisible from a module only when at least one of the trait or the type is unreachable. Private declarations (`deftrait-`, `deftype-`) bound impl reach the same way they bound name reach.

The full normative statement and worked example live in [§5.11.1](05-definitions.md#5111-impl-visibility--transitive-import-closure). The lookup mechanism (pre-computed index vs. on-demand walk) is implementation-defined.

## 7.12 Restrictions and Future Extensions [Tested]

### 7.12.1 Current Restrictions

- **No default methods on HKT traits.** Higher-kinded traits (those with type constructor parameters) do not support default method implementations.
- **Limited automatic deriving.** The `derive` macro supports `Eq`, `Ord`, and `Display` only (see Section 7.13).
- **No supertraits.** A trait cannot require that implementing types also implement another trait (e.g., `Ord` cannot require `Eq`).
- **No orphan rules.** There are no restrictions on which module may define an impl for a given trait-type pair.
- **No multi-parameter type classes.** Traits are parameterized over a single type (or single type constructor for HKT).
- **No associated types.** Traits cannot declare type members.

### 7.12.2 Future Extensions

| Feature | Description |
|---|---|
| Default methods on HKT traits | Extend default implementations to higher-kinded traits |
| Deriving additional traits | Extend `derive` beyond `Eq`, `Ord`, `Display` |
| Supertraits | Declare that one trait requires another (e.g., `Ord` requires `Eq`) |
| Monad / Applicative | HKT traits for monadic sequencing and applicative composition |
| Multi-parameter HKT | Traits like `(deftrait (Bifunctor f) ...)` for arity-2 constructors |
| Trait-dispatched collection verbs | A unified `Functor`/`Foldable`-style abstraction owning bare `map`/`filter`/`reduce`/`count`/`get`/`conj`/`assoc` and `first`/`rest` as single overload-unified entry points across `List`/`Vec`/`Seq`. A standard library reserves these bare names so an interim curated surface stays forward-compatible — see the non-normative naming reservation in [§11.4a](11-stdlib.md#114a-curated-collection-verb-naming-reservation-non-normative). |

## 7.13 Deriving [S21]

The `derive` macro automatically generates trait implementations for user-defined algebraic data types by structural recursion over constructors. It is a prelude macro, not a special form.

### 7.13.1 Syntax

```
(derive [Trait1 Trait2 ...] deftype-form)
```

The first argument is a bracket list of trait names to derive. The second argument is the complete `deftype` form (which is also emitted, so `derive` replaces the standalone `deftype`).

```clojure
(derive [Eq Ord Display]
  (deftype Color Red Green Blue))

(derive [Eq Display]
  (deftype (Option a) None (Some [:a val])))
```

### 7.13.2 Supported Traits

| Trait | Generated method(s) | Algorithm |
|---|---|---|
| `Eq` | `=` | Structural equality: match on constructor tag, then recursively compare all fields with `=`. Nullary constructors compare by identity. Different constructors return `false`. |
| `Ord` | `<`, `>` | Constructor ordering follows definition order (earlier constructors are "less than" later ones). For same-constructor comparison: lexicographic field comparison using `<` and `=`. `>` is derived as `(< b a)`. Default methods provide `<=` and `>=`. |
| `Display` | `show` | Nullary constructors produce their name as a string. Data constructors produce `"Name(field1 field2 ...)"` where each field is rendered via `show`. |

### 7.13.3 Polymorphic Types

For polymorphic types, `derive` propagates trait constraints to type parameters that appear in constructor fields. Only parameters used in field positions receive constraints:

```clojure
(derive [Eq Display]
  (deftype (Pair a b) (MkPair [:a first :b second])))
;; Generates:
;;   (impl Eq (Pair :Eq a :Eq b) ...)
;;   (impl Display (Pair :Display a :Display b) ...)
```

Parameters that do not appear in any field position (phantom types) receive no constraint.

### 7.13.4 Expansion

`derive` expands via the `begin` multi-form mechanism. The expansion output contains the original `deftype` form followed by one `impl` block per requested trait. Each `impl` is generated by a per-trait helper macro (`derive-Eq`, `derive-Ord`, `derive-Display`) that introspects the `deftype` S-expression at compile time.

### 7.13.5 Restrictions

- Only `Eq`, `Ord`, and `Display` are supported. Requesting an unsupported trait name generates a macro with that name (e.g. `derive-Foo`) which will fail at expansion time.
- Nested constructor patterns are not supported in the generated `match` arms — each field is compared or shown via a function call (`=`, `<`, `show`), which requires that field types have the appropriate trait implementation.
- `derive` MUST appear in place of the `deftype` it wraps — the `deftype` form is included in the expansion output.
