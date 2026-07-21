# 6. Pattern Matching [Tested]

This section defines the syntax, semantics, and type-checking rules for pattern matching in Cranelisp. Pattern matching is used to inspect algebraic data type values and bind their components to variables.

## 6.1 Match Expression Syntax [Tested tests/spec_06_pattern_matching::match_enum_basic]

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

## 6.2 Pattern Kinds [Tested tests/examples.rs::every_example_runs_with_documented_exit]

```ebnf
pattern      = ctor_pattern | wildcard | var_pattern

ctor_pattern = '(' (symbol | dotted_symbol) symbol* ')'  ; data constructor with bindings
             | symbol | dotted_symbol        ; nullary constructor (see 6.2.4 for disambiguation)

wildcard     = '_'

var_pattern  = symbol                       ; variable binding (see 6.2.4 for disambiguation)
```

### 6.2.1 Constructor Pattern (data) [Tested tests/spec_06_pattern_matching::pattern_data_constructor_binds_fields]

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

**Dotted constructor patterns.** The first symbol of a constructor pattern MAY be a dotted canonical constructor name — `(Maybe.Some x)` matches `Maybe`'s `Some` constructor and binds its field. The dotted form always resolves regardless of scrutinee type, and field-binding arity (above) and exhaustiveness (§6.5) are computed against the type it names.

**Contested bare constructor patterns resolve against the scrutinee type.** When two in-scope types share a bare constructor name (`Maybe` and `Option` each own `Some`), a **bare** constructor pattern for that name resolves against the **match scrutinee's type** — in `(match m [(Some x) …])` with `m : Maybe`, the bare `(Some x)` resolves to `Maybe.Some`. This mirrors how every constructor pattern is already checked against the scrutinee type (§6.4.1): the scrutinee provides the type context that selects the constructor. A bare contested constructor pattern is **poisoned (a compile-time error listing the canonical alternatives) ONLY when the scrutinee type cannot disambiguate it** — i.e. the scrutinee's type is not determined (a polymorphic or unannotated-lambda-parameter scrutinee with no other constraint). In that case, write the dotted form `(Maybe.Some x)` / `(Option.Some x)`.

This is the unifying rule across positions: a contested bare constructor resolves against whatever **type context** is available, and is poisoned only when there is none. In **value** position there is no such context, so a contested bare constructor always poisons (§8.6.5) and the dotted form is required. In **pattern** position the scrutinee type is the context, so a bare contested pattern resolves whenever the scrutinee type is determined, and poisons only when it is not. The dotted form is always available in either position.

### 6.2.2 Constructor Pattern (nullary) [Tested tests/spec_06_pattern_matching::pattern_nullary_constructor]

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

The scrutinee-directed rule of §6.2.1 applies to nullary constructor patterns exactly as to data ones: when two in-scope types share a bare nullary constructor name, a bare `None` pattern resolves against the scrutinee type (`(match m [None …])` with `m : Maybe` → `Maybe.None`), and is poisoned only when the scrutinee type cannot disambiguate it; the dotted form `Maybe.None` / `Option.None` always resolves.

### 6.2.3 Wildcard Pattern [Tested tests/spec_06_pattern_matching::pattern_wildcard_catchall]

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

### 6.2.4 Variable Pattern [Tested tests/spec_06_pattern_matching::pattern_variable_binds_value]

```clojure
name
```

A bare symbol that is NOT a known constructor and is NOT `_` is a **variable pattern**. It matches any value and binds that value to `name` within the arm body.

A variable pattern is a **local binder**: `name` MUST be a **bare (unqualified) symbol**; a qualified **or dotted** spelling (`m/x`, `a.x`) is a compile-time error, span at the pattern (§5, *Binder positions*). [S115] This is distinct from a **constructor** pattern head, which is a *reference* and MAY be dotted (`(Maybe.Some x)`, §6.2.1) — a dotted head is always a constructor pattern, never a variable binder (see below). [S113]

**Disambiguation rule:** When a bare symbol appears as a pattern, the implementation MUST resolve it as follows:

1. If the symbol is `_`, it is a **wildcard pattern**.
2. If the symbol names a known constructor (registered via `deftype`), it is a **nullary constructor pattern**.
3. Otherwise, it is a **variable pattern**.

This means that if a constructor and a local variable have the same name, the constructor takes precedence. Constructor names are capitalized by convention, so this conflict is rare in practice.

A **dotted** symbol in head position of a pattern is always a constructor pattern (never a variable pattern), resolving directly via its parent type per §8.5.2 — the bare-symbol precedence rule above is reached only for bare symbols.

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

### 6.3.1 Evaluation Order [Tested tests/spec_06_pattern_matching::pattern_first_match_wins]

1. The scrutinee expression is evaluated exactly once.
2. Patterns are tested in order, top-to-bottom. The first pattern that matches the scrutinee wins.
3. Variable bindings introduced by the winning pattern are brought into scope.
4. The winning arm's body expression is evaluated with those bindings in scope.
5. The result of the body is the result of the entire `match` expression.

### 6.3.2 Binding Scope [Tested tests/spec_06_pattern_matching::pattern_some_binds_value]

Variable bindings from a pattern are in scope ONLY within that arm's body expression. They are NOT visible in other arms or outside the `match`.

```clojure
(match (Some 42)
  [(Some x) (+ x 1)    ; x is in scope here
   None     0])         ; x is NOT in scope here
; x is NOT in scope here
```

### 6.3.3 Arm Body Type Agreement [Tested tests/spec_06_pattern_matching::pattern_match_arm_body_type_mismatch_names_both_types_strict_neg]

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

### 6.4.1 Constructor Patterns [Tested crates/cranelisp-typecheck/src/infer/tests.rs::test_infer_match_data_constructor_pattern]

When a constructor pattern appears in a `match`, the type checker:

1. Looks up the constructor's parent type and instantiates the type scheme with fresh type variables.
2. Unifies the scrutinee type with the constructor's parent type. If the constructor belongs to `(Option a)` and the scrutinee has type `(Option Int)`, unification binds `a = Int`.
3. Assigns each binding variable the type of the corresponding field, with substitutions applied. In the `(Some x)` example with `a = Int`, `x` gets type `Int`.

All constructor patterns in a `match` MUST be compatible with the scrutinee type. A pattern for constructor `Red` (of type `Color`) in a match on an `(Option Int)` scrutinee is a compile-time error.

### 6.4.2 Variable Patterns [Tested tests/spec_06_pattern_matching::pattern_int_match_with_wildcard]

A variable pattern introduces a binding with the same type as the scrutinee. No type constraint is added — the variable simply receives the scrutinee's type.

### 6.4.3 Wildcard Pattern [Tested tests/spec_06_pattern_matching::pattern_wildcard_catchall]

The wildcard pattern adds no type constraints and introduces no bindings.

### 6.4.4 Return Type [Tested tests/spec_06_pattern_matching::pattern_arms_type_unify]

The type of a `match` expression is the unified type of all arm bodies. The type checker unifies the body types pairwise. If any two bodies have incompatible types, it is a compile-time error.

## 6.5 Exhaustiveness [Tested]

Every `match` expression MUST be statically guaranteed to handle all possible values of the scrutinee type. The exhaustiveness rules depend on whether the scrutinee type is a concrete ADT or not.

### 6.5.1 ADT Scrutinee Types [Tested+Neg tests/spec_06_pattern_matching::pattern_non_exhaustive_match_on_adt_neg]

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

### 6.5.2 Non-ADT Scrutinee Types [Tested+Neg tests/spec_06_pattern_matching::pattern_int_match_with_wildcard]

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

### 6.5.3 Runtime Safety Net [Tested tests/spec_06_pattern_matching::pattern_non_exhaustive_match_on_adt_neg]

The runtime panic path ("match failed") remains in generated code as a safety net, but SHOULD be unreachable in programs that pass the exhaustiveness check.

## 6.6 Limitations [Tested]

The following pattern features are NOT supported:

### 6.6.1 No Nested Patterns [Tested tests/spec_06_pattern_matching::pattern_nested_constructor_rejected_neg]

Patterns MUST NOT contain sub-patterns. Each binding position in a constructor pattern MUST be a plain variable name — not another constructor pattern.

```clojure
;; NOT VALID: nested constructor pattern
(match val
  [(Some (Point x y)) (+ x y)])    ; compile-time error
```

Use nested `match` expressions as a workaround (see Section 6.7.6).

### 6.6.2 No Literal Patterns [Tested tests/spec_06_pattern_matching::pattern_int_match_with_wildcard (positive workaround); Neg owed S93 — literal-pattern rejection (FIXME 0433)]

Integer, float, string, and boolean literals MUST NOT appear as patterns. A
literal in pattern position is rejected at compile time (the implementation
reports `invalid pattern`).

```clojure
;; NOT VALID: literal pattern
(match n
  [0 "zero"
   1 "one"
   _ "other"])    ; compile-time error: invalid pattern
```

Use `if` expressions, `case`, or constructor-based wrappers instead. To match
on a scalar, bind it with a variable pattern and dispatch in the arm body (see
[§6.5.2](#652-non-adt-scrutinee-types)).

### 6.6.3 No Or-Patterns [Tested tests/spec_06_pattern_matching::pattern_first_match_wins]

A single pattern MUST NOT combine multiple alternatives.

```clojure
;; NOT VALID: or-pattern
(match color
  [(Red | Blue) "extreme"
   Green        "middle"])    ; compile-time error
```

### 6.6.4 No Guards [Tested tests/spec_06_pattern_matching::pattern_first_match_wins]

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

### 6.7.1 Matching on Option [Tested tests/spec_06_pattern_matching::match_enum_basic]

```clojure
(deftype (Option a) None (Some [:a val]))

(defn unwrap-or [:Int default :Option opt]
  (match opt
    [(Some x) x
     None     default]))

(unwrap-or 0 (Some 42))    ; -> 42
(unwrap-or 0 None)          ; -> 0
```

### 6.7.2 Matching on a Custom Sum Type [Tested tests/spec_06_pattern_matching::pattern_data_constructor_binds_fields]

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

### 6.7.3 Enum Matching [Tested tests/spec_06_pattern_matching::pattern_nullary_constructor]

```clojure
(deftype Color Red Green Blue)

(defn color-name [c]
  (match c
    [Red   "red"
     Green "green"
     Blue  "blue"]))

(color-name Green)    ; -> "green"
```

### 6.7.4 Variable Binding [Tested tests/spec_06_pattern_matching::pattern_variable_binds_value]

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

### 6.7.5 Wildcard Usage [Tested tests/spec_06_pattern_matching::pattern_wildcard_catchall]

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

### 6.7.6 Nested Match Workaround [Tested tests/spec_06_pattern_matching::nested_match_in_arm_body]

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

### 6.7.7 Product Type Destructuring [Tested tests/spec_06_pattern_matching::pattern_data_constructor_binds_fields]

Product types (single-constructor types) can be destructured like any other constructor:

```clojure
(deftype Point [:Int x :Int y])

(defn manhattan-distance [p]
  (match p
    [(Point x y) (+ x y)]))

(manhattan-distance (Point 3 4))    ; -> 7
```

Note: For product types, field accessor functions (e.g., `x`, `y`) are also available and may be more convenient than `match` when only one field is needed.

### 6.7.8 Match in Trait Implementations [Tested tests/spec_07_traits::trait_impl_on_enum_adt_with_match_over_all_constructors]

Pattern matching is commonly used in trait implementations for ADTs:

```clojure
(deftype (Option a) None (Some [:a val]))

(impl Display (Option :Display a)
  (defn show [self]
    (match self
      [None     "None"
       (Some x) (str-concat "(Some " (str-concat (show x) ")"))])))
```
