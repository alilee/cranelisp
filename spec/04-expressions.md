# 4. Expressions

This section defines the evaluation semantics for each expression form in Cranelisp. All expressions evaluate to a value of a statically known type. Cranelisp uses strict (eager) evaluation -- sub-expressions are fully evaluated before their results are used.

## Notation

Evaluation rules use the following notation:

- `E |- expr => v : T` means "in environment E, the expression `expr` evaluates to value `v` of type `T`"
- `E[x -> v]` means "environment E extended with binding `x` to value `v`"
- `->` denotes an evaluation step
- `;` separates sequenced steps (left-to-right)
- `E |- expr => v` is used when the type is clear from context

The environment `E` is a chain of lexical scopes: local bindings (from `let`, `fn`, `match`) shadow module-scope names.

## 4.1 Literals

Literal expressions evaluate to themselves. They carry no free variables and require no environment lookup.

### 4.1.1 Integer Literals

An integer literal evaluates to the corresponding signed 64-bit integer value.

```
E |- 42 => 42 : Int
E |- -7 => -7 : Int
E |- 0 => 0 : Int
```

```clojure
42      ; => 42
-7      ; => -7
```

### 4.1.2 Float Literals

A float literal evaluates to the corresponding IEEE 754 double-precision floating-point value.

```
E |- 3.14 => 3.14 : Float
E |- -0.5 => -0.5 : Float
```

```clojure
3.14    ; => 3.14
-0.5    ; => -0.5
```

### 4.1.3 Boolean Literals

The keywords `true` and `false` evaluate to their respective boolean values.

```
E |- true => true : Bool
E |- false => false : Bool
```

```clojure
true    ; => true
false   ; => false
```

### 4.1.4 String Literals

A string literal evaluates to the corresponding string value. Escape sequences are resolved during parsing (see [section 1.3.4](01-lexical.md#134-string-literals)).

```
E |- "hello" => "hello" : String
E |- "" => "" : String
```

```clojure
"hello"         ; => "hello"
"line1\nline2"  ; => a string containing a newline
```

## 4.2 Variable Reference

A variable reference looks up a name in the current lexical environment. Resolution follows the scope chain: local bindings (from `let`, `fn` parameters, `match` pattern bindings) are searched first, then module scope. An unbound name is a compile-time error.

```
E |- x => E(x)         when x is bound in E
E |- x => error         when x is not bound
```

```clojure
(let [x 42] x)         ; => 42, x resolves to the let binding
```

### 4.2.1 Constructor References

Constructor names are resolved through the module system like any other name.

**Nullary constructors** (constructors with no fields) evaluate directly to their integer tag value. No function call is involved:

```
E |- None => 0 : (Option a)
E |- Red => 0 : Color
E |- Green => 1 : Color
```

```clojure
None    ; => None (tag 0)
Red     ; => Red (tag 0)
Green   ; => Green (tag 1)
```

**Data constructors** (constructors with fields) evaluate to constructor functions. Referencing a data constructor by name produces a function value that, when called with the appropriate field arguments, allocates and returns the constructed value:

```
E |- Some => <constructor function> : (fn [a] (Option a))
E |- Cons => <constructor function> : (fn [a (List a)] (List a))
```

```clojure
Some        ; => constructor function (fn [val] ...)
(Some 42)   ; => (Some 42) : (Option Int)
```

### 4.2.2 Qualified and Dotted References

Qualified references (`module/name`) and dotted references (`Type.Constructor`, `Trait.method`) resolve through the module system. The resolution rules are defined in [section 8: Modules](08-modules.md).

```clojure
Option.Some         ; => constructor function for Some
Display.show        ; => trait method (resolved at call site)
math/sin            ; => function from the math module
```

## 4.3 Let Expression

```clojure
(let [x1 e1 x2 e2 ... xn en] body)
```

A `let` expression introduces a sequence of local bindings. Bindings are evaluated left-to-right. Each binding's value is computed in the environment extended by all preceding bindings. The body is evaluated in the environment extended by all bindings. The result of the `let` expression is the value of `body`.

```
E |- e1 => v1
E[x1 -> v1] |- e2 => v2
...
E[x1 -> v1, ..., xn -> vn] |- body => v
-----------------------------------------------
E |- (let [x1 e1 x2 e2 ... xn en] body) => v
```

Bindings go out of scope after `body` is evaluated. Any heap-allocated values bound by `let` that are not captured by a closure or returned from the body become eligible for deallocation.

**Sequential visibility**: Each binding can refer to previously bound names in the same `let`:

```clojure
(let [x 1 y (+ x 1)] y)    ; => 2, y's binding sees x
```

**Shadowing**: A binding MAY shadow an outer binding of the same name. The inner binding takes precedence within its scope:

```clojure
(let [x 10]
  (let [x 20] x))          ; => 20, inner x shadows outer x
```

**Single binding**:

```clojure
(let [x (+ 1 2)] (* x x))  ; => 9
```

**Multiple bindings**:

```clojure
(let [a 3
      b (+ a 1)
      c (* a b)]
  c)                        ; => 12
```

The binding list MUST contain an even number of forms -- alternating names and expressions. An odd number is a compile-time error.

## 4.4 If Expression

```clojure
(if cond then-expr else-expr)
```

An `if` expression evaluates a condition and selects one of two branches. Both branches are required -- there is no single-armed `if`.

The evaluation proceeds as follows:

1. Evaluate `cond` in the current environment. The result MUST be of type `Bool`.
2. If `cond` evaluates to `true`, evaluate `then-expr` and return its value.
3. If `cond` evaluates to `false`, evaluate `else-expr` and return its value.

```
E |- cond => true;  E |- then-expr => v
-----------------------------------------
E |- (if cond then-expr else-expr) => v

E |- cond => false;  E |- else-expr => v
-----------------------------------------
E |- (if cond then-expr else-expr) => v
```

**Short-circuit**: Only the selected branch is evaluated. The other branch is never executed. This is observable when branches contain side effects (IO operations).

**Type constraint**: Both branches MUST have the same type. This is enforced at compile time via unification. A type mismatch between branches is a compile-time error:

```clojure
; Valid: both branches have the same type
(if true 1 2)                ; => 1 : Int

; Valid: both branches return (IO Int)
(if (> x 0)
  (print (show x))
  (pure 0))

; ERROR: branch types differ (Int vs String)
(if true 1 "hello")
```

**Condition type**: The condition MUST be `Bool`. A non-`Bool` condition is a compile-time error:

```clojure
; ERROR: condition has type Int, expected Bool
(if 42 "yes" "no")
```

## 4.5 Lambda Expression

```clojure
(fn [param1 param2 ... paramN] body)
```

A lambda expression creates an anonymous function value (closure). The result is a first-class value that can be called, bound with `let`, passed as an argument, or returned from a function.

```
captures = free_vars(body) - {param1, ..., paramN} - globals
for each c_i in captures: E |- c_i => v_i
--------------------------------------------------------------
E |- (fn [params...] body) => <closure: code, [v_0, ..., v_k]>
```

The type of a lambda `(fn [p1 p2 ... pn] body)` where each `p_i` gets type `T_i` and `body` has type `R` is:

```
(fn [T1 T2 ... Tn] R)
```

### 4.5.1 Free Variable Capture

A lambda captures the values of all free variables referenced in its body -- variables that are neither parameters of the lambda nor top-level (global) definitions. Captured values are **copied** at the time the lambda is created. There is no shared mutable state between the lambda and the enclosing scope.

```clojure
(defn make-adder [n]
  (fn [x] (+ n x)))        ; captures n by value

(let [add5 (make-adder 5)]
  (add5 10))                ; => 15
```

Top-level function names and builtins are NOT captured -- they are accessed via direct calls or the global function table.

### 4.5.2 Parameter Type Annotations

Lambda parameters support optional type annotations using the `:Type name` syntax:

```clojure
(fn [:Int x :Bool y] (if y x 0))
```

Concrete annotations (`:Int`, `:String`, `:(Option Int)`) constrain the parameter to that exact type. Trait annotations (`:Num`, `:Display`) add trait constraints. Unannotated parameters receive fresh type variables and are inferred from usage.

### 4.5.3 Calling Convention

All lambda bodies are compiled with a closure calling convention: the closure pointer is passed as an implicit first argument, followed by the declared parameters. This allows the body to access captured values via offsets from the closure pointer. See [section 12.2: Calling Convention](12-runtime.md#122-calling-convention) for runtime details.

```clojure
; Lambda with no captures
(fn [x] (+ x 1))           ; closure: [code_ptr]

; Lambda with captures
(let [n 10]
  (fn [x] (+ n x)))        ; closure: [code_ptr, 10]
```

## 4.6 Function Application

```clojure
(callee arg1 arg2 ... argN)
```

A function application evaluates the callee and all arguments left-to-right, then applies the function to the arguments. The callee can be any expression that evaluates to a function -- a named function, a variable bound to a closure, a lambda expression, or a constructor.

```
E |- callee => f;  E |- arg1 => v1;  ...;  E |- argN => vN
f applied to (v1, ..., vN) => result
--------------------------------------------------------------
E |- (callee arg1 ... argN) => result
```

```clojure
(+ 1 2)                        ; => 3, direct call to trait method
(fact 10)                       ; => 3628800, direct call to named function
((fn [x] (* x x)) 7)           ; => 49, call lambda directly
(let [f (fn [x] (* x 2))]
  (f 5))                        ; => 10, call via variable
```

### 4.6.1 Direct Calls

When the callee is a known function name (symbol resolving to a top-level definition), the implementation emits a direct call. This avoids closure allocation and the closure calling convention overhead.

```clojure
(fact 10)                       ; direct call to 'fact'
(+ 1 2)                         ; direct call to resolved trait method '+$Int'
```

### 4.6.2 Indirect Calls

When the callee is an arbitrary expression (variable, lambda, function application result), the call goes through the closure calling convention: load the code pointer from offset 0 of the closure, then call it with the closure pointer as the first argument followed by the evaluated arguments.

```clojure
(let [f (fn [x] (+ x 1))]
  (f 5))                        ; indirect call through closure

(defn apply-fn [f x] (f x))
(apply-fn inc 5)                ; f is a closure; indirect call
```

### 4.6.3 Auto-Currying

When a function is called with fewer arguments than it declares parameters, the result is a **closure** capturing the applied arguments. This applies to both named functions and closures.

```
f : (fn [T1 T2 ... Tn] R)      where n > k
E |- arg1 => v1; ...; E |- argk => vk
----------------------------------------------------------
E |- (f arg1 ... argk) => <closure capturing v1..vk,
                            awaiting args of types Tk+1..Tn,
                            returning R>
```

The returned closure, when called with the remaining arguments, produces the same result as if all arguments had been supplied at once:

```clojure
(defn add [x y] (+ x y))
(let [add5 (add 5)]            ; auto-curry: returns (fn [y] (+ 5 y))
  (add5 10))                    ; => 15

(+ 1)                           ; => (fn [y] (+ 1 y)) : (fn [Int] Int)
((+ 1) 2)                       ; => 3
```

Auto-currying works at any depth -- supplying k of n arguments returns a function expecting the remaining n - k:

```clojure
(defn add3 [x y z] (+ x (+ y z)))
(let [f (add3 1)]               ; f : (fn [Int Int] Int)
  (let [g (f 2)]                ; g : (fn [Int] Int)
    (g 3)))                     ; => 6
```

**Multi-signature disambiguation**: For multi-signature functions (see section 4.7), auto-currying uses the expected return type arity to select the correct variant. If the call site expects a function of arity m, only variants with exactly k + m parameters are candidates.

**Restriction**: A multi-signature function name MUST NOT be used as a bare value (without any arguments). This is a compile-time error because the reference is ambiguous -- the compiler cannot determine which variant to reference. Use auto-curry with at least one argument, or wrap in a lambda.

## 4.7 Multi-Signature Dispatch

```clojure
(defn name
  ([params1...] body1)
  ([params2...] body2)
  ...)
```

A multi-signature function defines multiple variants of the same name, differing in parameter count, parameter types, or both. At each call site, the compiler selects the matching variant based on the concrete argument types after type inference.

### 4.7.1 Dispatch Rules

Dispatch proceeds as follows:

1. The compiler infers the types of all arguments at the call site.
2. Each variant's parameter types are compared against the argument types.
3. A variant matches if it has the same arity as the call and each parameter type unifies with the corresponding argument type.
4. Exactly one variant MUST match. Zero matches is an error (no applicable variant). Multiple matches is an error (ambiguous dispatch).

```
E |- arg1 => v1 : T1;  ...;  E |- argN => vN : TN
variant_i has params of types (S1, ..., SN) where each S_j unifies with T_j
---------------------------------------------------------------------------------
E |- (name arg1 ... argN) => apply variant_i's body with args (v1, ..., vN)
```

### 4.7.2 Name Mangling

Each variant is compiled as a separate function with a mangled name encoding its parameter types. The mangled name is `name$T1+T2+...+Tn` where each `Ti` is the short name of the concrete parameter type:

| Type | Mangled Name |
|---|---|
| `Int` | `Int` |
| `Bool` | `Bool` |
| `String` | `String` |
| `Float` | `Float` |
| `Fn(...)` | `Fn` |
| `ADT(name, ...)` | `name` (e.g., `Vec`, `List`, `Option`) |

Zero-parameter variants mangle as `name$`.

### 4.7.3 Examples

**Arity-based dispatch**:

```clojure
(defn add
  ([x y] (+ x y))
  ([x y z] (+ x (+ y z))))

(add 1 2)       ; => 3, dispatches to add$Int+Int
(add 1 2 3)     ; => 6, dispatches to add$Int+Int+Int
```

**Type-based dispatch**:

```clojure
(defn choose
  ([x y] (+ x y))          ; y : Int
  ([x y] (if y x 0)))      ; y : Bool

(choose 10 20)      ; => 30, dispatches to choose$Int+Int
(choose 5 true)     ; => 5, dispatches to choose$Int+Bool
```

**Collection dispatch** (the primary use case):

```clojure
(defn map
  ([f v] (lazy-map f (vec-to-seq 0 v)))    ; v : (Vec a)
  ([f l] (lazy-map f (list-to-seq l)))      ; l : (List a)
  ([f s] (lazy-map f s)))                   ; s : (Seq a)

(to-list (map inc [1 2 3]))           ; Vec dispatch -> (list 2 3 4)
(to-list (map inc (list 1 2 3)))      ; List dispatch -> (list 2 3 4)
```

### 4.7.4 Interaction with Auto-Currying

Multi-signature functions support auto-currying. When fewer arguments are supplied than any variant expects, the compiler narrows candidates by matching the expected return type arity against the remaining parameter count of each variant:

```clojure
(defn add
  ([x y] (+ x y))
  ([x y z] (+ x (+ y z))))

(let [f (add 10)] (f 5))       ; => 15, curries the 2-arg variant
```

## 4.8 Match Expression

```clojure
(match scrutinee [pattern1 body1 pattern2 body2 ...])
```

A `match` expression deconstructs a value by testing it against a sequence of patterns. The scrutinee is evaluated once, then patterns are tested top-to-bottom. The first matching pattern's body is evaluated and its value is the result of the `match` expression.

```
E |- scrutinee => v
pattern_i matches v, producing bindings {b1 -> w1, ...}
E[b1 -> w1, ...] |- body_i => result
-------------------------------------------------------------
E |- (match scrutinee [pattern_i body_i ...]) => result
```

### 4.8.1 Evaluation Order

1. The scrutinee is evaluated first, producing a value.
2. Patterns are tested top-to-bottom against the scrutinee value.
3. The first pattern that matches wins. Its body is evaluated in the current environment extended with any pattern bindings.
4. If no pattern matches, the program terminates with a runtime panic ("match failed").

Only the body of the matching arm is evaluated. Bodies of non-matching arms are never executed.

### 4.8.2 Pattern Bindings

Variables introduced by a pattern are in scope only within that arm's body. They are not visible in other arms or after the `match` expression.

```clojure
(match opt
  [(Some x) (+ x 1)]       ; x is bound only in this body
  [None 0])                 ; x is not in scope here
```

### 4.8.3 Type Constraint

All arm bodies MUST have the same type. This is enforced at compile time via unification:

```clojure
; Valid: all arms return Int
(match color
  [Red 0]
  [Green 1]
  [Blue 2])

; ERROR: arm types differ (Int vs String)
(match color
  [Red 0]
  [Green "green"])
```

### 4.8.4 Examples

**Simple ADT matching**:

```clojure
(match (Some 42)
  [(Some x) x]
  [None 0])                 ; => 42
```

**Nested expressions in bodies**:

```clojure
(defn describe [:Color c]
  (match c
    [Red "red"]
    [Green "green"]
    [Blue "blue"]))
```

**Wildcard and variable patterns**:

```clojure
(match x
  [0 "zero"]
  [_ "nonzero"])            ; _ matches anything, binds nothing
```

See [section 6: Pattern Matching](06-pattern-matching.md) for the complete pattern syntax, including constructor patterns, wildcard patterns, and variable patterns.

## 4.9 Type Annotation

```clojure
:Type expr
:(Applied Type) expr
```

A type annotation constrains the inferred type of an expression. The annotation is checked at compile time by unifying the annotation type with the expression's inferred type. If unification fails, it is a compile-time error. Annotations have no runtime effect -- they produce no code and do not change the value.

```
E |- expr => v : T
unify(T, Annotation) succeeds
-------------------------------
E |- :Annotation expr => v : T
```

### 4.9.1 Simple Annotations

```clojure
:Int 42                     ; => 42 : Int (redundant but valid)
:Bool true                  ; => true : Bool
```

### 4.9.2 Applied Type Annotations

For parameterized types, use the `:(Constructor Args...)` syntax:

```clojure
:(Option Int) None          ; => None : (Option Int)
:(List Int) Nil             ; => Nil : (List Int)
```

This is particularly useful for disambiguating polymorphic constructors. Without the annotation, `None` has type `(Option a)` with `a` unconstrained, which can cause ambiguity in type inference:

```clojure
; Without annotation: ambiguous type variable
None                        ; : (Option a) -- 'a' is unconstrained

; With annotation: concrete type
:(Option Int) None          ; : (Option Int)
```

### 4.9.3 Function Type Annotations

```clojure
:(fn [Int] Bool) f          ; constrain f to Int -> Bool
```

## 4.10 Vec Literal

```clojure
[e1 e2 ... eN]
```

A Vec literal evaluates its elements left-to-right and constructs a `Vec` containing the results. All elements MUST have the same type (enforced at compile time via unification).

```
E |- e1 => v1 : T;  E |- e2 => v2 : T;  ...;  E |- eN => vN : T
-------------------------------------------------------------------
E |- [e1 e2 ... eN] => <Vec [v1, v2, ..., vN]> : (Vec T)
```

```clojure
[1 2 3]                     ; => [1 2 3] : (Vec Int)
["a" "b" "c"]               ; => ["a" "b" "c"] : (Vec String)
[true false true]            ; => [true false true] : (Vec Bool)
```

**Element type uniformity**: All elements MUST unify to the same type:

```clojure
; ERROR: Int and String in the same Vec
[1 "hello"]
```

**Empty Vec**: An empty Vec literal `[]` has type `(Vec a)` with `a` unconstrained. A type annotation is needed when the surrounding context does not determine the element type:

```clojure
[]                          ; : (Vec a) -- element type unconstrained
:(Vec Int) []               ; : (Vec Int) -- disambiguated by annotation
(vec-push [] 1)             ; : (Vec Int) -- disambiguated by usage
```

**Nested Vecs**:

```clojure
[[1 2] [3 4]]               ; => [[1 2] [3 4]] : (Vec (Vec Int))
```

## 4.11 Evaluation Order Summary

Cranelisp uses **strict (eager) evaluation** throughout. All sub-expressions are fully evaluated before their results are consumed. The evaluation order within each expression form is:

| Form | Evaluation Order |
|---|---|
| Literal | Immediate -- no sub-expressions |
| Variable | Immediate -- environment lookup |
| `(let [x1 e1 ... xn en] body)` | `e1`, `e2`, ..., `en`, then `body` (left-to-right) |
| `(if cond then else)` | `cond`, then exactly one of `then` or `else` |
| `(fn [params] body)` | Captured values evaluated at closure creation; body deferred |
| `(f arg1 ... argN)` | `f`, then `arg1`, `arg2`, ..., `argN`, then apply (left-to-right) |
| `(match scrut [p1 b1 ...])` | `scrut`, then first matching `b_i` only |
| `:T expr` | `expr` only (annotation is compile-time) |
| `[e1 e2 ... eN]` | `e1`, `e2`, ..., `eN` (left-to-right) |

**Key properties**:

- Arguments are fully evaluated before the function body begins execution.
- Only one branch of `if` is evaluated.
- Only the body of the first matching `match` arm is evaluated.
- Lambda bodies are NOT evaluated at creation time -- only when the closure is called.
- The `Seq` type provides explicit opt-in laziness via thunks (zero-argument closures). This is a library-level construct, not a change to the evaluation model. See [section 12.4.2](12-runtime.md#1242-lazy-sequences).

## 4.12 Parallel Let Expression

```
(par-let [x1 e1 x2 e2 ... xn en] body)
```

`par-let` is a special form (not a macro) that evaluates all binding expressions in parallel, waits for all results, then evaluates `body` with the bindings in scope.

### 4.12.1 Semantics

Each binding expression `e1` through `en` is evaluated concurrently on a thread pool. The body `body` is evaluated only after all bindings have been resolved. The result of the `par-let` expression is the result of `body`.

Binding expressions MUST be independent — no expression `ei` may reference any name `xj` bound in the same `par-let`. This is enforced at compile time.

A `par-let` MUST have at least 2 bindings. A single binding offers no parallelism benefit.

### 4.12.2 Type Rules

Each binding expression `ei` is typed independently. The body `body` is typed in a context that includes all bindings `x1 : T1, ..., xn : Tn`. The result type is the type of `body`.

`par-let` applies to pure expressions only. For concurrent IO, the compiler automatically parallelises independent commutative effects in `bind!` chains — see [Section 10.12](10-io.md).

### 4.12.3 Evaluation Order

The order in which binding expressions complete is non-deterministic. However, since all expressions are pure (no side effects), this non-determinism is not observable — the result is always the same regardless of evaluation order.

```clojure
;; Both fib calls run concurrently
(par-let [a (fib 40)
          b (fib 39)]
  (+ a b))
```
