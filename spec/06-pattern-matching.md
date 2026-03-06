# 6. Pattern Matching [Tested]

This section defines the syntax, semantics, and type-checking rules for pattern matching in Cranelisp. Pattern matching is used to inspect algebraic data type values and bind their components to variables.

## 6.1 Match Expression Syntax [Tested tests/e2e::e2e_ring1_pattern_matching, tests/e2e::e2e_session_ring1_adt_workflow, tests/ring1::adt_sum_nested_match, tests/ring1::repl_adt_match, tests/ring1::string_from_int_to_string_in_match]

The `match` special form inspects a value (the **scrutinee**) against a series of **arms**, each consisting of a pattern and a body expression.

```ebnf
match_expr   = '(' 'match' expr '[' match_arm+ ']' ')'
match_arm    = pattern expr
```

The scrutinee is any expression. Arms are listed inside square brackets as alternating pattern-body pairs. Arms are tested top-to-bottom; the first arm whose pattern matches the scrutinee value wins, and its body is evaluated.

```clojure
(match scrutinee
  [pattern1 body1
   pattern2 body2
   ...])
```

A `match` expression MUST contain at least one arm.

**Example:**

```clojure
(match color
  [Red   "red"
   Green "green"
   Blue  "blue"])
```

## 6.2 Pattern Kinds [Tested tests/examples::example_11_destructuring]

```ebnf
pattern      = ctor_pattern | wildcard | var_pattern

ctor_pattern = '(' symbol symbol* ')'     ; data constructor with bindings
             | symbol                       ; nullary constructor (see 6.2.4 for disambiguation)

wildcard     = '_'

var_pattern  = symbol                       ; variable binding (see 6.2.4 for disambiguation)
```

### 6.2.1 Constructor Pattern (data) [Tested tests/ring1::repl_adt_product_match, tests/ring1::dual_mode_match_with_field_bindings]

```clojure
(Ctor var1 var2 ...)
```

A parenthesized pattern matches a **data constructor** (a constructor with fields). The first symbol MUST name a known data constructor. The remaining symbols are variable names that bind to the constructor's fields, positionally.

The number of variable bindings MUST equal the number of fields declared in the constructor's `deftype`. A mismatch is a compile-time error.

**Example:**

```clojure
;; Given: (deftype Point [:Int x :Int y])
(match p
  [(Point a b) (+ a b)])
; 'a' binds to the 'x' field, 'b' binds to the 'y' field

;; Given: (deftype (Option a) None (Some [:a val]))
(match opt
  [None         0
   (Some v)     v])
; 'v' binds to the 'val' field of Some
```

Binding names are arbitrary — they need not match the field names from the type definition. Bindings are always positional: the first binding corresponds to the first field, the second binding to the second field, and so on.

### 6.2.2 Constructor Pattern (nullary) [Tested tests/ring0::adt_enum_match, tests/ring0::repl_adt_enum_match, tests/ring0::dual_mode_enum_match, tests/repl_experience::enum_define_then_match, tests/repl_experience::enum_used_in_function_chain, tests/ring1::dual_mode_enum_match]

```clojure
Ctor
```

A bare symbol that names a known **nullary constructor** (a constructor with no fields) matches that constructor exactly and binds no variables.

**Example:**

```clojure
;; Given: (deftype Color Red Green Blue)
(match color
  [Red   "red"
   Green "green"
   Blue  "blue"])
```

### 6.2.3 Wildcard Pattern [Tested tests/ring0::match_wildcard, tests/repl_experience::enum_wildcard_pattern_in_repl, tests/ring1::adt_sum_wildcard_pattern]

```clojure
_
```

The wildcard pattern matches any value and binds nothing. It is typically used as a catch-all in the final arm.

**Example:**

```clojure
(match color
  [Red "red"
   _   "not red"])
```

### 6.2.4 Variable Pattern [Tested tests/ring0::match_var_pattern, tests/ring1::adt_sum_var_pattern]

```clojure
name
```

A bare symbol that is NOT a known constructor and is NOT `_` is a **variable pattern**. It matches any value and binds that value to `name` within the arm body.

**Disambiguation rule:** When a bare symbol appears as a pattern, the implementation MUST resolve it as follows:

1. If the symbol is `_`, it is a **wildcard pattern**.
2. If the symbol names a known constructor (registered via `deftype`), it is a **nullary constructor pattern**.
3. Otherwise, it is a **variable pattern**.

This means that if a constructor and a local variable have the same name, the constructor takes precedence. Constructor names are capitalized by convention, so this conflict is rare in practice.

**Example:**

```clojure
;; Variable pattern: 'x' is not a constructor
(match (Some 42)
  [(Some x) x
   _        0])
; x is bound to 42 in the first arm

;; Binding the entire scrutinee
(match some-value
  [result (+ result 1)])
; 'result' binds to whatever some-value evaluates to
```

## 6.3 Pattern Matching Semantics [Tested]

### 6.3.1 Evaluation Order [Tested tests/ring1.rs::match_eval_order_top_to_bottom]

1. The scrutinee expression is evaluated exactly once.
2. Patterns are tested in order, top-to-bottom. The first pattern that matches the scrutinee wins.
3. Variable bindings introduced by the winning pattern are brought into scope.
4. The winning arm's body expression is evaluated with those bindings in scope.
5. The result of the body is the result of the entire `match` expression.

### 6.3.2 Binding Scope [Tested tests/ring1.rs::match_binding_scope_limited_to_arm]

Variable bindings from a pattern are in scope ONLY within that arm's body expression. They are NOT visible in other arms or outside the `match`.

```clojure
(match (Some 42)
  [(Some x) (+ x 1)    ; x is in scope here
   None     0])         ; x is NOT in scope here
; x is NOT in scope here
```

### 6.3.3 Arm Body Type Agreement [Tested tests/ring1.rs::error_match_arm_type_disagreement]

All arm bodies MUST have the same type. The type checker unifies the types of all arm body expressions. If unification fails, it is a compile-time error.

```clojure
;; Valid: both arms produce Int
(match opt
  [(Some x) x
   None     0])

;; INVALID: first arm produces Int, second produces String
(match opt
  [(Some x) x
   None     "missing"])    ; compile-time type error
```

## 6.4 Type Checking Patterns [Tested]

### 6.4.1 Constructor Patterns [Tested tests/ring1.rs::match_constructor_pattern_type_checking]

When a constructor pattern appears in a `match`, the type checker:

1. Looks up the constructor's parent type and instantiates the type scheme with fresh type variables.
2. Unifies the scrutinee type with the constructor's parent type. If the constructor belongs to `(Option a)` and the scrutinee has type `(Option Int)`, unification binds `a = Int`.
3. Assigns each binding variable the type of the corresponding field, with substitutions applied. In the `(Some x)` example with `a = Int`, `x` gets type `Int`.

All constructor patterns in a `match` MUST be compatible with the scrutinee type. A pattern for constructor `Red` (of type `Color`) in a match on an `(Option Int)` scrutinee is a compile-time error.

### 6.4.2 Variable Patterns [Tested tests/ring1.rs::match_variable_pattern_gets_scrutinee_type]

A variable pattern introduces a binding with the same type as the scrutinee. No type constraint is added — the variable simply receives the scrutinee's type.

### 6.4.3 Wildcard Pattern [Tested tests/ring1.rs::match_wildcard_no_constraints]

The wildcard pattern adds no type constraints and introduces no bindings.

### 6.4.4 Return Type [Tested tests/ring1.rs::match_return_type_unified]

The type of a `match` expression is the unified type of all arm bodies. The type checker unifies the body types pairwise. If any two bodies have incompatible types, it is a compile-time error.

## 6.5 Exhaustiveness [Tested]

Every `match` expression MUST be statically guaranteed to handle all possible values of the scrutinee type. The exhaustiveness rules depend on whether the scrutinee type is a concrete ADT or not.

### 6.5.1 ADT Scrutinee Types [Tested tests/ring1::exhaustive_match_all_constructors, tests/ring1::exhaustive_match_with_wildcard, tests/ring1::exhaustive_match_with_var_pattern, tests/ring1::exhaustive_product_type, tests/ring1::match_three_constructors, tests/repl_experience::match_all_constructors]

When the scrutinee type resolves to a concrete ADT (a type defined via `deftype`), a `match` expression MUST be **exhaustive**: either every constructor of the ADT appears as a constructor pattern in at least one arm, or at least one arm uses a wildcard or variable pattern (which covers all remaining cases).

A non-exhaustive match on a concrete ADT type is a **compile-time error**. The error message MUST name the type and list the uncovered constructors.

**Example:**

```clojure
(deftype Color Red Green Blue)

;; VALID: all constructors covered
(match c [Red 1 Green 2 Blue 3])

;; VALID: wildcard covers remaining cases
(match c [Red 1 _ 0])

;; INVALID: missing Blue — compile-time error
(match c [Red 1 Green 2])
```

### 6.5.2 Non-ADT Scrutinee Types [Tested tests/ring1.rs::match_non_adt_int_var_pattern, tests/ring1.rs::match_non_adt_bool_wildcard]

When the scrutinee type is not a concrete ADT — i.e., it is `Int`, `Bool`, `Float`, `String`, a function type, or a type variable — the type has no finite set of constructors that could be enumerated. In this case, a `match` expression MUST include at least one **wildcard pattern** (`_`) or **variable pattern** as a catch-all arm. A `match` on a non-ADT scrutinee type without a wildcard or variable pattern is a **compile-time error**.

**Rationale:** Cranelisp has no panic/recovery mechanism. The language guarantees that well-typed programs do not encounter runtime match failure. Since non-ADT types cannot be fully enumerated by constructor patterns (there is no way to list all possible `Int` or `String` values as patterns), a catch-all arm is the only way to ensure exhaustiveness.

**Example:**

```clojure
;; VALID: variable pattern catches all Int values
(match n
  [x (+ x 1)])

;; VALID: wildcard catches all String values
(match s
  [_ "matched"])

;; VALID: variable pattern on Bool scrutinee
(match b
  [x (if x 1 0)])
```

Note: `Bool` is a primitive type, not an ADT defined via `deftype`. Since literal patterns are not supported (see Section 6.6.2), there is no way to write constructor patterns for `true` or `false`. A `match` on a `Bool` scrutinee MUST use a wildcard or variable pattern to satisfy exhaustiveness.

### 6.5.3 Runtime Safety Net [Tested tests/ring0::error_non_exhaustive_match_runtime, tests/ring1::non_exhaustive_match_panics]

The runtime panic path ("match failed") remains in generated code as a safety net, but SHOULD be unreachable in programs that pass the exhaustiveness check.

## 6.6 Limitations [Tested]

The following pattern features are NOT supported:

### 6.6.1 No Nested Patterns [Tested tests/ring1.rs::error_nested_pattern]

Patterns MUST NOT contain sub-patterns. Each binding position in a constructor pattern MUST be a plain variable name — not another constructor pattern.

```clojure
;; NOT VALID: nested constructor pattern
(match val
  [(Some (Point x y)) (+ x y)])    ; compile-time error
```

Use nested `match` expressions as a workaround (see Section 6.7.6).

### 6.6.2 No Literal Patterns [Tested tests/ring1.rs::match_non_adt_int_var_pattern]

Integer, float, string, and boolean literals MUST NOT appear as patterns.

```clojure
;; NOT VALID: literal pattern
(match n
  [0 "zero"
   1 "one"
   _ "other"])    ; compile-time error
```

Use `if` expressions or constructor-based wrappers instead.

### 6.6.3 No Or-Patterns [Tested tests/ring1.rs::match_eval_order_top_to_bottom]

A single pattern MUST NOT combine multiple alternatives.

```clojure
;; NOT VALID: or-pattern
(match color
  [(Red | Blue) "extreme"
   Green        "middle"])    ; compile-time error
```

### 6.6.4 No Guards [Tested tests/ring1.rs::match_eval_order_top_to_bottom]

Pattern arms MUST NOT have guard conditions.

```clojure
;; NOT VALID: guarded pattern
(match opt
  [(Some x) when (> x 0) x
   _        0])    ; compile-time error
```

Use `if` inside the arm body instead:

```clojure
(match opt
  [(Some x) (if (> x 0) x 0)
   _        0])
```

## 6.7 Examples [Tested]

### 6.7.1 Matching on Option [Tested tests/ring1::repl_adt_match]

```clojure
(deftype (Option a) None (Some [:a val]))

(defn unwrap-or [:Int default :Option opt]
  (match opt
    [(Some x) x
     None     default]))

(unwrap-or 0 (Some 42))    ; -> 42
(unwrap-or 0 None)          ; -> 0
```

### 6.7.2 Matching on a Custom Sum Type [Tested tests/e2e::e2e_ring1_pattern_matching]

```clojure
(deftype Shape
  (Circle [:Float radius])
  (Rect [:Float width :Float height]))

(defn area [s]
  (match s
    [(Circle r) (* (* 3.14159 r) r)
     (Rect w h) (* w h)]))

(area (Circle 2.0))     ; -> 12.56636
(area (Rect 3.0 4.0))   ; -> 12.0
```

### 6.7.3 Enum Matching [Tested tests/ring0::adt_enum_match]

```clojure
(deftype Color Red Green Blue)

(defn color-name [c]
  (match c
    [Red   "red"
     Green "green"
     Blue  "blue"]))

(color-name Green)    ; -> "green"
```

### 6.7.4 Variable Binding [Tested tests/ring0::match_var_pattern, tests/ring1::adt_sum_var_pattern]

A variable pattern can bind the entire scrutinee value, which is useful as a catch-all that still needs the value:

```clojure
(deftype (Result a b)
  (Ok [:a ok])
  (Err [:b err]))

(defn describe [r]
  (match r
    [(Ok v)  (str-concat "ok: " (show v))
     (Err e) (str-concat "err: " (show e))]))
```

### 6.7.5 Wildcard Usage [Tested tests/ring0::match_wildcard, tests/ring1::adt_sum_wildcard_pattern]

The wildcard is useful for ignoring variants or fields:

```clojure
;; Ignore some variants
(defn is-some [opt]
  (match opt
    [(Some _) true
     None     false]))

;; Catch-all arm
(defn is-red [c]
  (match c
    [Red true
     _   false]))
```

Note: When `_` appears inside a constructor pattern — `(Some _)` — it is a binding name (a variable named `_`), not the wildcard pattern. It binds the field value but by convention the binding is not used.

### 6.7.6 Nested Match Workaround [Tested tests/ring1::adt_sum_nested_match]

Since nested patterns are not supported, use nested `match` expressions to destructure multi-level values:

```clojure
(deftype Point [:Int x :Int y])
(deftype (Option a) None (Some [:a val]))

;; Goal: extract x from (Option Point)
;; Cannot write: (Some (Point x y)) — nested patterns not allowed

(defn get-x [opt]
  (match opt
    [(Some p) (match p
                [(Point x y) x])
     None     0]))

(get-x (Some (Point 3 4)))    ; -> 3
(get-x None)                   ; -> 0
```

### 6.7.7 Product Type Destructuring [Tested tests/ring1::repl_adt_product_match]

Product types (single-constructor types) can be destructured like any other constructor:

```clojure
(deftype Point [:Int x :Int y])

(defn manhattan-distance [p]
  (match p
    [(Point x y) (+ x y)]))

(manhattan-distance (Point 3 4))    ; -> 7
```

Note: For product types, field accessor functions (e.g., `x`, `y`) are also available and may be more convenient than `match` when only one field is needed.

### 6.7.8 Match in Trait Implementations [Tested tests/ring1.rs::match_in_trait_impl, tests/ring2.rs::user_trait_adt]

Pattern matching is commonly used in trait implementations for ADTs:

```clojure
(deftype (Option a) None (Some [:a val]))

(impl Display (Option :Display a)
  (defn show [self]
    (match self
      [None     "None"
       (Some x) (str-concat "(Some " (str-concat (show x) ")"))])))
```
