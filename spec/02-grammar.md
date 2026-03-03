# 2. Grammar

This section defines the syntactic grammar of Cranelisp -- how S-expression trees (as defined in [1. Lexical Structure](01-lexical.md)) are interpreted as language constructs. The lexical grammar produces a tree of forms (atoms, lists, brackets); the syntactic grammar assigns meaning to those trees.

Throughout this section, EBNF non-terminals in `UPPER_CASE` refer to lexical tokens from Section 1. Non-terminals in `lower_case` are syntactic grammar rules defined here. The notation `(...)` denotes a parenthesized list form, `[...]` denotes a bracket form.

## 2.1 Program Structure

A Cranelisp program is a sequence of top-level forms:

```ebnf
program      = top_level*
```

Top-level forms are processed in three phases:

1. **Module phase**: `mod`, `import`, `export`, and `platform` declarations are extracted and processed before any other compilation occurs.
2. **Macro phase**: `defmacro` and `defmacro-` forms are compiled and executed; macro calls are expanded. `begin` forms are flattened into the surrounding top-level sequence.
3. **AST phase**: The remaining forms (`defn`, `deftype`, `deftrait`, `impl`) are converted to abstract syntax tree nodes.

The implementation MUST process these phases in order: module declarations before macro expansion, and macro expansion before AST construction. Forms from one phase MUST NOT appear in a later phase -- for example, a `mod` or `import` form that survives to the AST phase is an error.

### Batch Mode

In batch mode (`--run`), the program MUST define a function named `main` that takes no parameters and returns a value of type `IO _`. Execution begins by calling `main`.

```clojure
(defn main []
  (print "hello world"))
```

### Interactive Mode

In interactive mode (REPL), top-level expressions are permitted in addition to definitions. Each expression is evaluated and its type and value are displayed. See [12. Runtime Model](12-runtime.md) for REPL semantics.

## 2.2 Top-Level Forms

```ebnf
top_level    = defn_form
             | deftype_form
             | deftrait_form
             | impl_form
             | defmacro_form      (* handled in macro phase *)
             | mod_form           (* handled in module phase *)
             | import_form        (* handled in module phase *)
             | export_form        (* handled in module phase *)
             | platform_form      (* handled in module phase *)
```

Note: `const`, `const-`, `def`, and `def-` are library macros defined in the prelude. They are not primitive syntactic forms and are not described here. See [Section 11.7](11-stdlib.md#117-prelude-macros) for their definition and expansion.

### 2.2.1 `defn` -- Function Definition

```ebnf
defn_form    = '(' defn_kw name docstring? single_sig ')'
             | '(' defn_kw name docstring? multi_sig ')'

defn_kw      = 'defn' | 'defn-'

single_sig   = param_list expr

multi_sig    = variant variant+

variant      = '(' param_list expr ')'
```

A `defn` form defines a named function. The `defn-` variant defines a module-private function (see Section 2.6).

**Single-signature form**: The parameter list is followed by a single body expression.

```clojure
(defn square [x] (* x x))

(defn greet [name]
  (str-concat "Hello, " name))
```

**Multi-signature form**: Multiple `(param_list body)` variants enable dispatch on argument count and types. When the first element after the name (or docstring) is a parenthesized list (not a bracket), the multi-signature form is assumed. There MUST be at least two variants.

```clojure
(defn add
  ([x y] (+ x y))
  ([x y z] (+ (+ x y) z)))
```

An optional docstring MAY appear between the name and the parameter list (single-sig) or the first variant (multi-sig). See Section 2.7.

```clojure
(defn inc "Increment by one" [:Int x] (+ x 1))

(defn add "Addition with 2 or 3 args"
  ([x y] (+ x y))
  ([x y z] (+ (+ x y) z)))
```

### 2.2.2 `deftype` -- Algebraic Data Type Definition

```ebnf
deftype_form = '(' deftype_kw type_head docstring? type_body ')'

deftype_kw   = 'deftype' | 'deftype-'

type_head    = TYPE_NAME
             | '(' TYPE_NAME type_param+ ')'

type_param   = SYMBOL                   (* lowercase *)

type_body    = product_body
             | sum_body

product_body = field_list

sum_body     = constructor_def+

constructor_def
             = CONSTRUCTOR_NAME                    (* nullary *)
             | '(' CONSTRUCTOR_NAME docstring? field_list? ')'

field_list   = '[' field_def* ']'

field_def    = annotation SYMBOL                  (* typed field *)
             | SYMBOL                              (* bare field -- inferred *)
```

The `deftype` form defines an algebraic data type (ADT). The `deftype-` variant makes it module-private.

The **type head** is either a bare type name (for monomorphic types) or a parenthesized name with type parameters (for polymorphic types). Type names MUST start with an uppercase letter. Type parameters MUST be lowercase symbols.

The **type body** takes one of two forms:

**Product type**: A single field list defines a product type. The type name is used as the sole constructor name.

```clojure
(deftype Point [:Int x :Int y])

(deftype (Pair a b) [:a first :b second])
```

**Sum type**: One or more constructor definitions define a sum type. Each constructor is either a bare uppercase symbol (nullary/enum variant) or a parenthesized form with an optional docstring and optional field list.

```clojure
;; Enum (all nullary)
(deftype Color Red Green Blue)

;; Sum with data constructors
(deftype (Option a)
  None
  (Some [:a val]))

;; Mixed nullary and data constructors
(deftype (Result a b)
  (Ok "Success value" [:a val])
  (Err "Error value" [:b err]))
```

**Shortcut syntax**: When a field in a field list has no type annotation (a bare symbol), the field is assigned a fresh type variable. The type variables are assigned alphabetically (`a`, `b`, `c`, ...) in first-appearance order across all constructors. This is equivalent to declaring explicit type parameters.

```clojure
;; These are equivalent:
(deftype Pair [first second])
(deftype (Pair a b) [:a first :b second])
```

An optional docstring MAY appear between the type head and the type body:

```clojure
(deftype (Option a) "A value that may or may not be present"
  None
  (Some [:a val]))
```

Constructors in a sum type MAY also have docstrings:

```clojure
(deftype (Result a b)
  (Ok "The success case" [:a val])
  (Err "The error case" [:b err]))
```

### 2.2.3 `deftrait` -- Trait Declaration

```ebnf
deftrait_form = '(' deftrait_kw trait_head docstring? method_sig* ')'

deftrait_kw   = 'deftrait' | 'deftrait-'

trait_head    = TRAIT_NAME
              | '(' TRAIT_NAME type_param+ ')'

method_sig    = '(' method_name docstring? '[' type_expr* ']' type_expr ')'
```

The `deftrait` form declares a trait -- a named collection of method signatures. The `deftrait-` variant makes it module-private.

The **trait head** is either a bare name (for simple traits) or a parenthesized name with type constructor parameters (for higher-kinded traits). Trait names MUST start with an uppercase letter.

**Simple traits**: The type parameter `Self` is implicit and refers to the implementing type.

```clojure
(deftrait Display
  (show [Self] String))

(deftrait Eq
  (= [Self Self] Bool))

(deftrait Ord
  (< [Self Self] Bool)
  (> [Self Self] Bool)
  (<= [Self Self] Bool)
  (>= [Self Self] Bool))
```

**Higher-kinded traits**: Explicit type constructor parameters enable abstraction over parameterized types. The lowercase parameters represent type constructors (e.g., `f` in `(Functor f)` ranges over `Option`, `List`, etc.).

```clojure
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
```

An optional docstring MAY appear between the trait head and the method signatures. Individual methods MAY also have docstrings:

```clojure
(deftrait Display "Convert a value to its string representation"
  (show "Return the string form of a value" [Self] String))
```

### 2.2.4 `impl` -- Trait Implementation

```ebnf
impl_form    = '(' 'impl' TRAIT_NAME impl_target impl_method* ')'

impl_target  = TYPE_NAME                              (* simple: Int, Bool *)
             | '(' TYPE_NAME impl_type_arg+ ')'       (* parameterized *)

impl_type_arg = TYPE_NAME                             (* concrete arg *)
              | SYMBOL                                 (* type variable *)
              | annotation SYMBOL                      (* constrained type var *)

impl_method  = '(' 'defn' name docstring? param_list expr ')'
```

The `impl` form provides method bodies for a trait on a specific type. There is no private variant of `impl` -- implementations are always public.

**Concrete implementations**: The target is a concrete type or a concrete instantiation of a parameterized type.

```clojure
(impl Display Int
  (defn show [x] (int-to-string x)))

(impl Display (Option Int)
  (defn show [opt]
    (match opt
      [None "None"
       (Some v) (str-concat "Some(" (str-concat (show v) ")"))])))
```

**Polymorphic implementations**: The target includes type variables, optionally with trait constraints. Polymorphic impl methods are constrained functions -- they are monomorphised at each call site.

```clojure
(impl Display (Option :Display a)
  (defn show [opt]
    (match opt
      [None "None"
       (Some v) (str-concat "Some(" (str-concat (show v) ")"))])))
```

**Higher-kinded trait implementations**: For HKT traits, the target is a bare type constructor name (without parameters):

```clojure
(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some v) (Some (f v))])))
```

Methods within an `impl` block MUST use the `defn` keyword (not `defn-`). They are always public. Each method's name MUST correspond to a method declared in the trait being implemented.

### 2.2.5 `defmacro` -- Macro Definition

```ebnf
defmacro_form = '(' defmacro_kw name docstring? macro_params expr ')'
              | '(' defmacro_kw name docstring? macro_clause+ ')'

defmacro_kw   = 'defmacro' | 'defmacro-'

macro_params  = '[' fixed_param* rest_clause? ']'

fixed_param   = SYMBOL

rest_clause   = '&' SYMBOL

macro_clause  = '(' macro_params expr ')'
```

The `defmacro` form defines a compile-time macro. The `defmacro-` variant makes it module-private.

The macro body receives its arguments as `Sexp` values and MUST return a value of type `Sexp`. A macro whose body has a different return type is a compile-time error.

**Fixed parameters**: Each fixed parameter binds to the corresponding argument's S-expression.

FIXME: this example is not great because it does have sound typing based on the int literal on the false side of if. it is also weird in a pure functional language.

```clojure
(defmacro when [cond body]
  `(if ~cond ~body 0))
```

**Rest parameters**: The `&` symbol before the last parameter captures all remaining arguments as an `(SList Sexp)`.

```clojure
(defmacro my-add [& args]
  `(+ ~@args))

(my-add 1 2 3)  ; expands to (+ 1 2 3)
```

**Zero-argument macros**: A macro with no parameters expands when referenced as a bare symbol (without parentheses).

```clojure
(defmacro always-one [] (SexpInt 1))
always-one  ; -> 1
```

An optional docstring MAY appear between the name and the parameter list:

FIXME: Same issue with example as when above

```clojure
(defmacro unless "Evaluate body when condition is false" [cond body]
  `(if ~cond 0 ~body))
```

Macros are expanded iteratively to a fixed point before AST construction. The body MAY use quasiquote (`` ` ``), unquote (`~`), and unquote-splicing (`~@`) as described in [1. Lexical Structure](01-lexical.md), Section 1.6.

### 2.2.6 `mod` -- Module Declaration

```ebnf
mod_form     = '(' 'mod' MODULE_NAME ')'
             | '(' 'mod-' MODULE_NAME ')'
```

The `mod` form declares a child module. `MODULE_NAME` MUST be a simple symbol (no dots, no qualifications). The child module's source is loaded from a file with the same name and a `.cl` extension, resolved relative to the current module's file. The `mod-` variant declares a private submodule accessible only within the declaring module's subtree.

```clojure
(mod math)        ; declares child module 'math', loaded from math.cl
(mod- internal)   ; declares private child module 'internal'
```

### 2.2.7 `import` -- Module Import

```ebnf
import_form  = '(' 'import' '[' import_spec+ ']' ')'

import_spec  = module_ref names_list

module_ref   = MODULE_PATH
             | '(' MODULE_PATH SYMBOL ')'           (* with alias *)

names_list   = '[' name+ ']'                         (* specific names *)
             | '[' '*' ']'                            (* glob import *)
             | '[' SYMBOL '.*' ']'                   (* member glob *)
             | '[' ']'                                (* alias-only *)
```

The `import` form brings names from other modules into the current scope. The body is a bracket containing pairs of module references and name lists.

**Module references**: A bare module path, or a parenthesized `(path alias)` pair that introduces a local alias.

**Name lists**:
- `[name1 name2]` -- import specific names
- `[*]` -- import all public names from the module
- `[Display.*]` -- import all members (methods/constructors) of a type or trait
- `[]` -- import nothing; used with aliases for qualified access

```clojure
(import [core.option [Some None Option]
         core.string [concat]
         (core.io io) [*]
         math []])
```

### 2.2.8 `export` -- Module Export

```ebnf
export_form  = '(' 'export' '[' export_spec+ ']' ')'

export_spec  = MODULE_PATH names_list
```

The `export` form re-exports names from child or imported modules as part of the current module's public interface. The syntax is the same as `import` but without aliases.

```clojure
(export [core.option [Some None Option]
         core.string [*]])
```

### 2.2.9 `platform` -- Platform Declaration

```ebnf
platform_form = '(' 'platform' SYMBOL ')'
```

The `platform` form declares which platform DLL provides IO operations for the program. It is **only valid in the entry module**. Library modules and non-entry modules MUST NOT use `platform`; they access platform functions via `import`:

```clojure
;; Entry module only:
(platform stdio)

;; Any module that needs platform functions:
(import [platform.stdio [*]])
```

`platform` is processed during the module loading phase. It is NOT an AST node.

## 2.3 Expression Forms

```ebnf
expr         = literal
             | var_ref
             | let_expr
             | if_expr
             | fn_expr
             | match_expr
             | annotate_expr
             | vec_lit
             | apply_expr
```

### 2.3.1 Literals

```ebnf
literal      = INTEGER
             | FLOAT
             | BOOLEAN
             | STRING
```

Literals evaluate to their corresponding values. See [1. Lexical Structure](01-lexical.md) for the lexical rules.

```clojure
42            ; Int
3.14          ; Float
true          ; Bool
"hello"       ; String
```

### 2.3.2 Variable Reference

```ebnf
var_ref      = SYMBOL
```

A symbol in expression position is a variable reference. The symbol is resolved through the name resolution rules described in [8. Modules](08-modules.md). The symbol MAY be simple (`foo`), qualified (`math/sin`), or dotted (`Option.Some`).

```clojure
x             ; local variable
inc           ; function reference
Option.Some   ; constructor reference
math/sin      ; qualified reference
```

### 2.3.3 `let` -- Local Bindings

```ebnf
let_expr     = '(' 'let' '[' binding+ ']' expr ')'

binding      = SYMBOL expr
```

The `let` form introduces local bindings. The binding list is a bracket containing pairs of names and value expressions. Bindings are evaluated left to right; each binding MAY reference earlier bindings in the same `let`. The body expression is evaluated in the scope of all bindings.

The binding list MUST contain an even number of elements (alternating names and values). The body MUST be exactly one expression.

```clojure
(let [x 1
      y (+ x 1)]
  (* x y))       ; -> 2
```

Binding values MAY include type annotations:

```clojure
(let [x :Int 42
      opt :(Option Int) None]
  x)
```

### 2.3.4 `if` -- Conditional

```ebnf
if_expr      = '(' 'if' expr expr expr ')'
```

The `if` form evaluates a condition, then evaluates exactly one of the two branches. The condition MUST have type `Bool`. Both branches are required and MUST have the same type.

```clojure
(if (> x 0)
  "positive"
  "non-positive")
```

### 2.3.5 `fn` -- Lambda Expression

```ebnf
fn_expr      = '(' 'fn' param_list expr ')'
```

The `fn` form creates an anonymous function (lambda). The parameter list uses the same syntax as `defn`. The body is a single expression. Lambdas capture variables from their enclosing scope (closures).

```clojure
(fn [x] (* x x))

(fn [:Int x :Int y] (+ x y))

(let [n 10]
  (fn [x] (+ x n)))      ; closure capturing n
```

### 2.3.6 Function Application

```ebnf
apply_expr   = '(' expr expr* ')'
```

A parenthesized list whose head is not a special-form keyword is a function application. The first element (callee) MUST evaluate to a function. The remaining elements are arguments. Arguments are evaluated left to right.

If the callee is a keyword (`let`, `if`, `fn`, `match`, `vec`), the form is parsed as the corresponding special form instead.

```clojure
(inc 5)                       ; named function call
((fn [x] (* x x)) 7)         ; lambda call
(f 1 2 3)                     ; variable call
```

**Auto-currying**: If a function is called with fewer arguments than its parameter count, the result is a closure that captures the applied arguments and accepts the remaining ones. This applies to all functions.

```clojure
(defn add [x y] (+ x y))
(let [inc (add 1)]           ; auto-curry: (add 1) -> (fn [y] (+ 1 y))
  (inc 5))                    ; -> 6
```

### 2.3.7 `match` -- Pattern Matching

```ebnf
match_expr   = '(' 'match' expr '[' match_arm+ ']' ')'

match_arm    = pattern expr
```

The `match` form inspects a scrutinee value against a sequence of patterns. Arms are tested in order; the body of the first matching arm is evaluated. See Section 2.5 for pattern syntax.

The arms bracket MUST contain an even number of elements (alternating patterns and bodies). All arm bodies MUST have the same type.

```clojure
(match opt
  [None "nothing"
   (Some v) (show v)])

(match color
  [Red "red"
   Green "green"
   Blue "blue"])
```

### 2.3.8 Type Annotation

```ebnf
annotate_expr = annotation expr
```

A type annotation constrains an expression's type. The annotation appears immediately before the expression it annotates. This form may appear at the top level of argument lists, binding values, and standalone expressions.

See Section 2.4 for the `annotation` grammar.

```clojure
:Int 42                       ; annotate literal
:(Option Int) None            ; annotate polymorphic constructor
:(Fn [Int] Bool) even?        ; annotate function reference
```

The annotation is checked at compile time -- the expression's inferred type MUST be compatible with the annotation. This is useful for disambiguating polymorphic constructors and constraining return types.

### 2.3.9 Vec Literal

```ebnf
vec_lit      = '[' expr* ']'
             | '(' 'vec' expr* ')'
```

A bracket form in expression position is a Vec literal. All elements MUST have the same type. An empty bracket `[]` creates an empty Vec (its element type is inferred from context).

The `(vec ...)` form is an alternative syntax with identical semantics.

```clojure
[1 2 3]                       ; Vec of Int
["a" "b" "c"]                 ; Vec of String
[]                            ; empty Vec (type inferred)
(vec 1 2 3)                   ; same as [1 2 3]
```

## 2.4 Type Expressions

Type expressions appear in annotations, parameter lists, field definitions, and trait method signatures.

```ebnf
type_expr    = named_type
             | type_var
             | self_type
             | applied_type
             | fn_type

named_type   = TYPE_NAME                  (* starts with uppercase *)

type_var     = SYMBOL                     (* starts with lowercase *)

self_type    = 'self'

applied_type = '(' TYPE_NAME type_expr+ ')'

fn_type      = '(' 'Fn' '[' type_expr* ']' type_expr ')'
```

### 2.4.1 Named Types

A symbol starting with an uppercase letter is a named type reference.

```clojure
Int                           ; 64-bit signed integer
Float                         ; 64-bit floating point
Bool                          ; boolean
String                        ; heap-allocated string
```

### 2.4.2 Type Variables

A symbol starting with a lowercase letter is a type variable, representing a polymorphic type parameter.

```clojure
a                             ; type variable
b                             ; type variable
```

### 2.4.3 Self Type

The keyword `self` refers to the implementing type within trait method signatures.

```clojure
(deftrait Eq
  (= [self self] Bool))      ; self = the implementing type
```

Note: `self` in type position is distinct from `Self` (which would be a named type). The trait method parameter list uses `self` (lowercase) to refer to the implementing type. When writing `[Self]` with uppercase, it is interpreted as a named type rather than the self-type of the trait.

### 2.4.4 Applied Types

A parenthesized type name followed by one or more type arguments creates a parameterized type application.

```clojure
(Option Int)                  ; Option applied to Int
(List String)                 ; List applied to String
(Result Int String)           ; Result with two type args
(IO Int)                      ; IO wrapping Int
```

### 2.4.5 Function Types

The `Fn` keyword followed by a bracketed parameter type list and a return type describes a function type.

```clojure
(Fn [Int] Bool)               ; Int -> Bool
(Fn [Int Int] Int)            ; (Int, Int) -> Int
(Fn [] String)                ; () -> String
(Fn [(Fn [a] b) (List a)] (List b))  ; higher-order
```

## 2.5 Pattern Syntax

Patterns appear in `match` arms. Each pattern is tested against the scrutinee value.

```ebnf
pattern      = constructor_pat
             | wildcard_pat
             | var_pat

constructor_pat = CONSTRUCTOR_NAME                    (* nullary *)
                | '(' CONSTRUCTOR_NAME SYMBOL* ')'    (* with bindings *)

wildcard_pat    = '_'

var_pat         = SYMBOL                              (* lowercase, not '_' *)
```

### 2.5.1 Constructor Pattern

A symbol starting with an uppercase letter is a constructor pattern. If bare, it matches a nullary constructor. If parenthesized, the trailing symbols bind the constructor's fields.

```clojure
None                          ; matches nullary None
(Some v)                      ; matches Some, binds field to v
(Cons h t)                    ; matches Cons, binds head to h, tail to t
Red                           ; matches nullary Red
```

The number of bindings MUST match the number of fields in the constructor.

### 2.5.2 Wildcard Pattern

The symbol `_` matches any value and binds nothing.

```clojure
(match x
  [0 "zero"
   _ "other"])
```

Note: An integer literal like `0` in a match arm is actually parsed as an expression, not a pattern. The example above is illustrative -- in practice, matching on integer values requires `if` chains or equality checks, not pattern matching. Pattern matching only works with ADT constructors, wildcards, and variable bindings.

### 2.5.3 Variable Pattern

A lowercase symbol (other than `_`) matches any value and binds it to the given name within the arm body.

```clojure
(match opt
  [None 0
   x (show x)])               ; x binds the entire Some value
```

### 2.5.4 Disambiguation

A symbol in pattern position is interpreted as follows:

- `_` -- wildcard pattern
- Starts with uppercase -- constructor pattern (nullary)
- Starts with lowercase (not `_`) -- variable binding pattern

There is no nested pattern matching -- constructor patterns bind field values to variables but do not recursively match on those fields.

## 2.6 Visibility

Definitions may be public (visible to importing modules) or private (visible only within the defining module). The visibility is indicated by a `-` suffix on the definition keyword:

| Public | Private | Description |
|---|---|---|
| `defn` | `defn-` | Function definition |
| `deftype` | `deftype-` | Type definition |
| `deftrait` | `deftrait-` | Trait declaration |
| `defmacro` | `defmacro-` | Macro definition |
| `mod` | `mod-` | Submodule declaration |

The following forms have no private variant:

| Form | Reason |
|---|---|
| `impl` | Trait implementations are always public |
| `import` | Imports affect only the current module's scope |
| `export` | Re-exports are inherently public |
| `platform` | Platform declarations are inherently public |

Library macros such as `const`/`const-` and `def`/`def-` follow `defmacro` visibility rules and are described in [Section 11.7](11-stdlib.md#117-prelude-macros).

By default (without the `-` suffix), all definitions are public. Private definitions MUST NOT be accessible to importing modules through `import` or `export`.

## 2.7 Docstrings

An optional docstring (a string literal) MAY appear between the name and the parameter list or body of a definition. Docstrings are preserved by the implementation and are available for introspection.

The following forms support docstrings:

| Form | Position |
|---|---|
| `defn` / `defn-` | Between name and param list / first variant |
| `deftype` / `deftype-` | Between type head and type body |
| `deftrait` / `deftrait-` | Between trait head and first method |
| `defmacro` / `defmacro-` | Between name and param list |
| Constructor definitions | Between constructor name and field list |
| Trait method signatures | Between method name and param types |

```clojure
(defn factorial "Compute n!" [:Int n]
  (if (= n 0)
    1
    (* n (factorial (- n 1)))))

(deftype (Option a) "A value that may or may not be present"
  (None "The absent case")
  (Some "The present case" [:a val]))

(deftrait Display "Convert values to strings"
  (show "Return the string representation" [Self] String))

(defmacro unless "Evaluate body when condition is false" [cond body]
  `(if ~cond 0 ~body))
```

A docstring MUST be a string literal. It MUST NOT be a variable reference or expression -- only a literal `"..."` form in the correct position is recognized as a docstring.

## 2.8 Common Grammar Elements

This section collects grammar elements referenced by multiple rules above.

### 2.8.1 Names

```ebnf
name              = SYMBOL                (* function/macro/value name *)

TYPE_NAME         = SYMBOL                (* starts with uppercase *)

CONSTRUCTOR_NAME  = SYMBOL                (* starts with uppercase *)

TRAIT_NAME        = SYMBOL                (* starts with uppercase *)

MODULE_NAME       = SYMBOL                (* simple symbol, no dots *)

MODULE_PATH       = SYMBOL                (* may contain dots: core.option *)
```

Function, macro, and value names may start with lowercase or be operator symbols. Type names, constructor names, and trait names MUST start with an uppercase letter. Module names in `mod` declarations MUST be simple symbols; module paths in `import` and `export` MAY contain dots.

### 2.8.2 Parameter Lists

```ebnf
param_list   = '[' annotated_param* ']'

annotated_param = annotation SYMBOL       (* typed parameter *)
                | SYMBOL                   (* untyped parameter *)

annotation   = ':' TYPE_NAME              (* :Int, :Bool *)
             | ':' SYMBOL                  (* :a, :Num -- type var or trait *)
             | ':' '(' type_expr+ ')'     (* :(Option Int), :(Fn [Int] Bool) *)
```

Parameters are listed in square brackets. Each parameter is a symbol, optionally preceded by a type annotation.

**Concrete annotations** (`:Int`, `:String`, `:(Option Int)`) constrain the parameter to a specific type.

**Trait annotations** (`:Num`, `:Display`) add a trait constraint to the parameter's type variable, producing a constrained polymorphic function.

**Type variable annotations** (`:a`) constrain the parameter to match other parameters with the same type variable.

```clojure
[x y]                         ; untyped
[:Int x :Int y]               ; concrete types
[:Num x :Num y]               ; trait constraints
[:(Option Int) opt]           ; applied type annotation
[:(Fn [Int] Bool) pred]       ; function type annotation
```

### 2.8.3 Annotation Syntax

The annotation syntax is used in parameter lists, field definitions, let bindings, and standalone type annotations:

```ebnf
annotation   = COLON_PREFIX               (* :Int, :a, :Num *)
             | ':' type_expr_list          (* : (Option Int) *)
```

Where `COLON_PREFIX` is a colon-prefixed symbol from the lexical grammar (e.g., `:Int`, `:a`), and `type_expr_list` is a parenthesized type expression (e.g., `(Option Int)`, `(Fn [Int] Bool)`).

The colon serves as the annotation introducer. A colon immediately followed by an uppercase letter is a named type annotation. A colon immediately followed by a lowercase letter is a type variable or trait constraint. A bare colon followed by a parenthesized form is a compound type annotation.
