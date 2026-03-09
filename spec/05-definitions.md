# 5. Definitions [Tested]

This section specifies the top-level definition forms in Cranelisp. All definitions appear at the top level of a source file or module. They introduce named functions, types, traits, macros, constants, and module structure into the program.

## 5.1 Function Definition (`defn` / `defn-`) [Tested]

### 5.1.1 Single-Signature [Tested tests/ring0::repl_define_and_call, tests/ring0::repl_multiple_params, tests/ring0::error_duplicate_param_names, tests/e2e::e2e_ring0_defn_and_call]

```ebnf
defn_form       = '(' ('defn' | 'defn-') name docstring? params body ')'
name            = symbol
docstring       = string
params          = '[' annotated_param* ']'
annotated_param = colon_prefix symbol   (* :Type name or :Trait name *)
                | symbol                (* bare name, type inferred *)
body            = expr
```

A function definition binds a name to a function value. The parameter list uses square brackets. Each parameter is optionally preceded by a colon-prefixed type annotation.

```clojure
(defn square [x] (* x x))

(defn add [:Int x :Int y] (+ x y))

(defn show-option [:Display a] (show a))

(defn inc "Increment by one" [:Int x] (+ x 1))
```

**Semantics:**

- The name MUST be a valid symbol.
- Parameters MUST be listed in square brackets.
- The body MUST be a single expression. Use `do` (a prelude macro) for sequencing multiple expressions.
- An optional docstring (string literal) MAY appear between the name and the parameter list.
- Parameter annotations take two forms:
  - **Concrete type**: `:Int`, `:String`, `:(Option Int)` -- constrains the parameter to that exact type.
  - **Trait constraint**: `:Num`, `:Display` -- constrains the parameter's type variable to types implementing that trait, producing a constrained polymorphic function (see [Section 7: Traits](07-traits.md)).
- When no annotation is provided, the parameter type is inferred via Hindley-Milner unification.
- The return type is always inferred; there is no return type annotation syntax.

### 5.1.2 Multi-Signature [Tested tests/ring2::neg_multi_sig_bare_value_errors, tests/repl_experience::defn_multi_param_reports_full_signature]

```ebnf
defn_multi_form = '(' ('defn' | 'defn-') name docstring? variant+ ')'
variant         = '(' params body ')'
```

A multi-signature function definition provides multiple variants with different parameter lists. The implementation dispatches to the appropriate variant based on the concrete argument types at each call site, determined after type inference.

```clojure
(defn size "Return the number of elements"
  ([:Vec v] (vec-len v))
  ([:List l] (list-len l)))
```

**Semantics:**

- All variants MUST share the same function name.
- Each variant is a parenthesized form containing a parameter list in square brackets and a body expression.
- An optional docstring MAY appear between the name and the first variant.
- Dispatch is resolved statically at compile time based on inferred argument types. If no variant matches the concrete types at a call site, it is a compile-time error.
- Variants MAY have different numbers of parameters.
- The mangled name for each variant is the function name followed by `$` and the parameter types joined by `+`. For example, `size` with a `Vec` parameter becomes `size$Vec`.

### 5.1.3 Auto-Currying [R3 S17]

When any function (single or multi-signature) is called with fewer arguments than it declares, the call returns a closure that captures the provided arguments and accepts the remaining ones. This is auto-currying.

```clojure
(defn add [x y] (+ x y))

(let [inc (add 1)]
  (inc 5))              ; -> 6
```

## 5.2 Type Definition (`deftype` / `deftype-`) [Tested]

```ebnf
deftype_form   = '(' ('deftype' | 'deftype-') type_head docstring? type_body ')'
type_head      = name                         (* monomorphic *)
               | '(' name type_var+ ')'       (* polymorphic *)
type_var       = symbol                        (* lowercase by convention *)
type_body      = field_list                    (* product type *)
               | constructor+                  (* sum type *)
field_list     = '[' field_def* ']'
field_def      = colon_prefix symbol           (* :Type fieldname *)
               | symbol                        (* bare fieldname, type inferred *)
constructor    = name                          (* nullary *)
               | '(' name docstring? field_list ')'   (* data constructor *)
               | '(' name docstring? ')'       (* nullary with docstring *)
```

A type definition introduces an algebraic data type (ADT) into scope. Three shapes are supported: product types, sum types, and enums.

### 5.2.1 Product Type (Single Constructor) [Tested tests/ring1::adt_product_construct_and_match, tests/ring1::adt_product_get_y, tests/ring1::adt_product_multi_field, tests/ring1::repl_adt_product, tests/e2e::e2e_ring1_adt_product]

When the type body is a bracketed field list, the type name doubles as the sole constructor.

```clojure
(deftype Point [:Int x :Int y])

(deftype (Pair a b) [:a first :b second])
```

- `Point` is both the type name and the constructor: `(Point 3 4)` constructs a value.
- Fields are alternating `:Type name` pairs within brackets.
- The constructor behaves as a function: `Point :: (Fn [Int Int] Point)`.

### 5.2.2 Sum Type (Multiple Constructors) [Tested tests/ring1::adt_sum_option_some, tests/ring1::adt_sum_option_none, tests/ring1::adt_either_type, tests/ring1::adt_enum_mixed_nullary_and_data, tests/e2e::e2e_ring1_adt_sum]

When the type body contains one or more constructor forms, each introduces a distinct variant.

```clojure
(deftype (Option a)
  None
  (Some [:a val]))

(deftype Shape
  (Circle [:Float radius])
  (Rect [:Float width :Float height]))
```

- **Nullary constructors** (no fields) are written as bare names: `None`, `Red`.
- **Data constructors** carry fields in a bracketed list: `(Some [:a val])`.
- Each constructor MAY have an optional docstring after its name.
- Nullary constructors are values: `None :: (Option a)`.
- Data constructors are functions: `Some :: (Fn [a] (Option a))`.

### 5.2.3 Enum (All Nullary) [Tested tests/ring0::repl_adt_enum, tests/ring0::repl_enum_definition_and_use, tests/repl_experience::multiple_enum_types_in_session, tests/repl_experience::enum_with_many_constructors, tests/examples::example_06_enums]

An enum is a sum type where all constructors are nullary.

```clojure
(deftype Color Red Green Blue)
```

This is syntactically a sum type with no field lists. Enum values are represented as bare integer tags at runtime (see [Section 12: Runtime Model](12-runtime.md)).

### 5.2.4 Shortcut Syntax -- Inferred Type Parameters [Tested tests/ring1::adt_shortcut_syntax]

When field brackets contain bare names (no `:Type` prefix), each unique bare name is assigned a fresh type variable. Type parameters on the type head are inferred and need not be written.

```clojure
;; Shortcut                              ;; Equivalent full form
(deftype Pair [first second])            (deftype (Pair a b) [:a first :b second])

(deftype Option                          (deftype (Option a)
  None                                     None
  (Some [unwrap]))                         (Some [:a unwrap]))

(deftype Result                          (deftype (Result a b)
  (Ok [ok])                                (Ok [:a ok])
  (Err [err]))                             (Err [:b err]))
```

**Rules:**

- A bare field name (no `:` prefix) is assigned a fresh type variable. Variables are allocated as `a`, `b`, `c`, ... in order of first appearance across all constructors.
- `:Type name` uses the explicit type; no inference occurs for that field.
- When all field types are inferred, the type parameter list on the head MAY be omitted.
- Mixing explicit and bare fields within one constructor is permitted:

```clojure
(deftype Named (Named [:String name value]))
;; name is :String (explicit), value gets fresh var 'a'
;; => (deftype (Named a) (Named [:String name :a value]))
```

### 5.2.5 Docstrings on Types and Constructors [Tested tests/ring2.rs::docstring_on_deftype]

An optional docstring MAY appear after the type head (before the body) and after each constructor name (before its field list).

```clojure
(deftype (Option a) "An optional value"
  (None "Represents absence")
  (Some "Wraps a present value" [:a val]))
```

### 5.2.6 Generated Accessors [Tested tests/ring1::adt_product_get_y]

For each named field in a type definition, an accessor function is automatically generated in the enclosing scope. The accessor's name is the field name.

**Product type accessors** are total -- they always succeed:

```clojure
(deftype Point [:Int x :Int y])

(x (Point 3 4))   ; -> 3
(y (Point 3 4))   ; -> 4
;; x :: (Fn [Point] Int)
;; y :: (Fn [Point] Int)
```

**Sum type accessors** are partial -- they succeed on the matching variant and panic on mismatched variants:

```clojure
(deftype (Option a) None (Some [:a unwrap]))

(unwrap (Some 42))   ; -> 42
(unwrap None)        ; -> runtime panic
;; unwrap :: (Fn [(Option a)] a)
```

Accessor functions are first-class values and can be passed as arguments or bound to variables.

### 5.2.7 Constructor Semantics [Tested tests/ring1::error_adt_constructor_wrong_arg_count, tests/ring1::error_adt_constructor_wrong_type]

- **Nullary constructors** are values, not functions. Entering a nullary constructor at the REPL displays its type.
- **Data constructors** are functions. They participate in auto-currying: `(let [f Some] (f 42))` works.
- Constructor names are conventionally capitalized, but this is not enforced.
- Constructor tags are assigned sequentially starting from 0 in definition order.

## 5.3 Trait Declaration (`deftrait` / `deftrait-`) [Tested]

```ebnf
deftrait_form  = '(' ('deftrait' | 'deftrait-') trait_head docstring? method_sig+ ')'
trait_head     = name                         (* simple trait *)
               | '(' name type_var+ ')'       (* higher-kinded trait *)
method_sig     = '(' name docstring? '[' type_expr* ']' type_expr ')'
type_expr      = 'Self'                       (* implementing type *)
               | symbol                        (* named type or type var *)
               | '(' 'Fn' '[' type_expr* ']' type_expr ')'   (* function type *)
               | '(' name type_expr+ ')'       (* applied type *)
```

A trait declaration introduces a named interface with one or more method signatures.

### 5.3.1 Simple Traits [Tested tests/ring2::user_trait_simple, tests/ring2::repl_user_trait, tests/repl_experience::ring2a_deftrait_in_repl]

```clojure
(deftrait Display "Convert a value to its string representation"
  (show "Return string form of value" [Self] String))

(deftrait Eq "Equality comparison"
  (eq [Self Self] Bool))
```

- Each method signature specifies the parameter types in square brackets and the return type.
- `Self` refers to the type that will implement the trait.
- An optional docstring MAY appear on the trait itself and on each method.

### 5.3.2 Higher-Kinded Traits [R3 S17]

When the trait head includes type parameters, the trait operates on type constructors rather than concrete types.

```clojure
(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container"
    [(Fn [a] b) (f a)] (f b)))
```

- The type parameter `f` represents a type constructor (e.g., `Option`, `List`).
- Method signatures MAY use the type parameter applied to type variables: `(f a)`.

### 5.3.3 Trait Semantics [Tested tests/ring2::trait_plus_int, tests/ring2::error_plus_bool]

- A trait declaration introduces method names into scope. These names cannot be used until at least one implementation is provided.
- Method signatures declare the type contract. Implementations MUST conform to the declared signature.
- Traits are the mechanism for operator overloading: `+`, `-`, `*`, `/` are methods of the `Num` trait; `=` is a method of `Eq`; `<`, `>`, `<=`, `>=` are methods of `Ord`.

## 5.4 Trait Implementation (`impl`) [Tested]

```ebnf
impl_form      = '(' 'impl' trait_name target_type method_defn+ ')'
trait_name     = symbol
target_type    = symbol                          (* monomorphic or bare constructor *)
               | '(' symbol type_arg+ ')'        (* applied type *)
type_arg       = symbol                          (* concrete type or type var *)
               | colon_prefix symbol             (* constrained type var *)
method_defn    = '(' 'defn' name params body ')' (* follows defn syntax *)
```

A trait implementation provides method bodies for a specific type.

### 5.4.1 Concrete Implementation [Tested tests/ring2::user_trait_simple, tests/ring2::user_trait_adt, tests/ring2::user_trait_multiple_impls]

```clojure
(impl Display Int
  (defn show [self] (int-to-string self)))

(impl Display Color
  (defn show [c]
    (match c
      [Red "Red"
       Green "Green"
       Blue "Blue"])))
```

### 5.4.2 Concrete ADT Instantiation [R2 S10]

```clojure
(impl Display (Option Int)
  (defn show [self]
    (match self
      [None "None"
       (Some x) (show x)])))
```

This implements Display for `(Option Int)` specifically. The `(show x)` call in the `Some` arm dispatches to the `Int` implementation.

### 5.4.3 Polymorphic Implementation [R2 S10]

```clojure
(impl Display (Option :Display a)
  (defn show [self]
    (match self
      [None "None"
       (Some x) (show x)])))
```

- `:Display a` constrains the type variable `a` to types that implement `Display`.
- The implementation methods become constrained polymorphic functions, monomorphised at each call site.
- `(show (Some 42))` generates a specialization `show$Option$Int`.

### 5.4.4 Higher-Kinded Implementation [R3 S17]

For HKT traits, the target is a bare type constructor name (not an applied type):

```clojure
(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some x) (Some (f x))])))
```

### 5.4.5 Implementation Semantics [Tested tests/ring2::user_trait_simple, tests/ring2::error_plus_bool]

- `impl` has no private variant. All trait implementations are visible wherever the trait and type are visible.
- Method definitions within `impl` follow `defn` syntax but MUST NOT include docstrings (the docstring comes from the trait declaration).
- The method parameter count and types MUST conform to the trait's declared signature.
- Method bodies are type-checked against the instantiated trait signature.

## 5.5 Macro Definition (`defmacro` / `defmacro-`) [Tested tests/macros::repl_defmacro_identity, tests/macros::repl_defmacro_quasiquote, tests/macros::repl_defmacro_multi_clause, tests/macros::batch_defmacro_simple]

```ebnf
defmacro_form  = '(' ('defmacro' | 'defmacro-') name docstring? macro_params body ')'
               | '(' ('defmacro' | 'defmacro-') name docstring? macro_clause+ ')'
macro_params   = '[' symbol* ('&' symbol)? ']'
macro_clause   = '(' macro_params body ')'
```

A macro definition introduces a compile-time transformation. The macro body is a Cranelisp function that receives its arguments as `Sexp` values and MUST return a `Sexp` value. Macros run during the macro expansion phase, before AST construction and type checking.

```clojure
(defmacro when "Execute body when condition is true" [cond body]
  `(if ~cond ~body 0))

(defmacro my-add [& args]
  `(+ ~@args))
```

**Semantics:**

- The macro body MUST have return type `Sexp`. A macro that returns a different type (e.g., `Int`) is a compile-time error.
- `&` before the last parameter captures remaining arguments as an `(SList Sexp)` value (variadic).
- Macro bodies are compiled with Cranelift and executed via JIT during expansion. They have access to the full language, including all functions and macros defined before them.
- Macros are expanded recursively: a macro may expand to forms containing other macro calls. An expansion limit (implementation-defined, at least 500 iterations) prevents infinite expansion.
- Quasiquote (`` ` ``), unquote (`~`), and unquote-splicing (`~@`) provide convenient syntax for constructing `Sexp` return values. See [Section 9: Macros](09-macros.md) for full expansion semantics.
- A `defmacro` MAY have multiple `([params] body)` clauses. Each clause is tried in order; the first whose parameter count and bracket-pattern constraints match the call site is selected. See [Section 9.2.6](09-macros.md#926-multi-clause-macros) for multi-clause macro semantics.

### 5.5.1 Zero-Argument Macros (Bare-Symbol Expansion)

A macro with zero parameters expands when referenced as a bare symbol, without parentheses:

```clojure
(defmacro always-one [] (SexpInt 1))

always-one   ; -> 1 (no parens needed)
```

### 5.5.2 Multi-Form Expansion (`begin`)

A macro MAY return `(begin form1 form2 ...)` to splice multiple top-level forms into the enclosing scope. `begin` is handled during macro expansion and is NOT valid in user source code.

```clojure
(defmacro def-pair [name a b]
  `(begin
    (defn ~(make-name1 name) [] ~a)
    (defn ~(make-name2 name) [] ~b)))
```

## 5.6 Constants (`const` / `const-`) [Tested tests/stdlib::macro_const_int_batch, tests/stdlib::macro_const_string_batch, tests/exemplar::exemplar_batch_const_macro]

```ebnf
const_form = '(' ('const' | 'const-') name expr ')'
```

A constant definition creates an inline substitution. Every reference to the constant name is replaced with the value expression at compile time.

```clojure
(const PI 3.14)
(const ANSWER 42)
(const GREETING "hello")

(* PI 2.0)   ; expands to (* 3.14 2.0)
```

**Semantics:**

- `const` is a prelude macro, not a built-in special form. It expands to a zero-argument `defmacro` that returns the quoted value.
- The value expression MUST be a literal or a form that can be quoted as `Sexp`. It is not evaluated -- it is substituted syntactically.
- `const-` creates a module-private constant.

## 5.7 Named Values (`def` / `def-`) [Tested tests/stdlib::macro_def_basic_batch, tests/stdlib::macro_def_expression_batch]

```ebnf
def_form = '(' ('def' | 'def-') name expr ')'
```

A named value definition evaluates its expression once and binds the result to a name.

```clojure
(def ten (+ 5 5))
(def pi 3.14)

(show ten)   ; -> "10"
```

**Semantics:**

- `def` is a prelude macro, not a built-in special form. It expands to a `begin` containing a zero-argument function definition and a zero-argument macro that calls it.
- The expression is evaluated once (as the body of a zero-argument function). References to the name expand to calls to that function.
- Unlike `const`, the value expression IS evaluated. This means `def` can bind computed values, not just literals.
- `def-` creates a module-private named value.

## 5.8 Module Declaration (`mod`) [Tested tests/ring2::single_file_via_run_project, tests/ring2::module_missing_file_error, tests/ring2::module_cycle_detection]

```ebnf
mod_form = '(' 'mod' module_name ')'
module_name = symbol
```

A module declaration introduces a submodule. It triggers module loading: if a source file with the corresponding name exists as a sibling of the current module's file, it is loaded; otherwise an empty file is created.

```clojure
(mod math)
(mod utils)
```

**Semantics:**

- `(mod name)` MUST contain exactly one module name argument.
- The module name MUST be a simple symbol (not qualified, not dotted).
- `mod` is processed during the module loading phase, before macro expansion and AST construction. It is NOT an AST node.
- `mod` does not switch into the child module. In a REPL, use `/mod name` to switch.
- `mod-` declares a private submodule. Other modules MUST NOT import from or reference names in a private submodule. See [Section 8.2.3](08-modules.md#823-private-submodule-declaration).

## 5.9 Import and Export [Tested tests/ring2.rs::import_specific_names, tests/ring2.rs::import_glob]

```ebnf
import_form = '(' 'import' import_body ')'
import_body = '[' import_spec+ ']'
import_spec = module_name '[' (name | '*')+ ']'

export_form = '(' 'export' export_body ')'
export_body = '[' export_spec+ ']'
export_spec = module_name '[' (name | '*')+ ']'
```

Imports bring names from other modules into the current scope. Exports re-export names from submodules through the current module.

```clojure
(import [math [sin cos] io [print read-line]])

(import [core.collections [*]])   ; import all public names

(export [math [sin] utils [*]])
```

**Semantics:**

- `import` and `export` are processed during the module loading phase, before macro expansion and AST construction. They are NOT AST nodes.
- `[*]` imports or exports all public names from the specified module.
- Imported names are available as bare (unqualified) symbols in the current module.
- Even without an explicit import, names from other modules can be referenced using qualified syntax: `math/sin`.
- All non-prelude modules receive an implicit `(import [prelude [*]])`. The prelude itself and the `primitives` module are exempt.
- See [Section 8: Modules](08-modules.md) for full module resolution semantics.

## 5.10 Platform Declaration [R4 S10]

```ebnf
platform_form = '(' 'platform' platform_name ')'
platform_name = symbol
```

A platform declaration specifies which platform DLL provides IO primitives for the program. It is **only valid in the entry module**.

```clojure
(platform stdio)
```

**Semantics:**

- The platform name MUST be a bare symbol (not a string literal).
- `platform` is only valid in the entry module. A `platform` form in any other module is a compile-time error.
- Non-entry modules that need platform functions MUST use `(import [platform.stdio [*]])` instead.
- `platform` is processed during the module loading phase, before macro expansion. It is NOT an AST node.
- See [Section 10: IO Model](10-io.md) for platform loading and IO semantics.

## 5.11 Visibility [Tested tests/ring2.rs::visibility_private_defn_not_importable, tests/ring2.rs::visibility_public_defn_importable, tests/ring2.rs::visibility_private_deftype_not_importable]

All definitions are **public by default**. A `-` suffix on the definition keyword makes the definition private to the defining module.

| Public | Private | Definition |
|---|---|---|
| `defn` | `defn-` | Function |
| `deftype` | `deftype-` | Type |
| `deftrait` | `deftrait-` | Trait |
| `defmacro` | `defmacro-` | Macro |
| `const` | `const-` | Constant |
| `def` | `def-` | Named value |
| `mod` | `mod-` | Submodule |

**Semantics:**

- Private names are accessible only within the defining module and its submodule subtree. They MUST NOT be imported by other modules.
- `impl` has no private variant. Trait implementations are always visible wherever both the trait and the type are in scope.
- `import`, `export`, and `platform` have no private variants.

## 5.12 Docstrings [Tested tests/ring2.rs::docstring_on_defn, tests/ring2.rs::docstring_on_deftype, tests/ring2.rs::docstring_on_deftrait]

Definitions MAY include an optional docstring -- a string literal placed between the name and the parameter list (or body).

| Form | Docstring position |
|---|---|
| `defn` | Between name and params: `(defn name "doc" [params] body)` |
| `deftype` | After type head: `(deftype Name "doc" ...)` |
| `deftrait` | After trait head: `(deftrait Name "doc" ...)` |
| Trait method | After method name: `(method "doc" [types] ret)` |
| Constructor | After constructor name: `(CtorName "doc" [:Type field])` |
| `defmacro` | Between name and params: `(defmacro name "doc" [params] body)` |

**Semantics:**

- Docstrings are stored in the compilation metadata and are available for introspection (e.g., via REPL `/doc` command).
- Docstrings have no effect on program semantics.
- `const`, `def`, `impl`, `mod`, `import`, `export`, and `platform` do not support docstrings.

## 5.13 Definition Ordering [Tested]

### 5.13.1 Functions, Types, Traits, and Implementations [Tested tests/ring0::forward_reference, tests/ring0::mutual_forward_references, tests/ring0::dual_mode_forward_reference]

Top-level definitions of functions, types, traits, and implementations MAY reference each other freely, including forward references. The implementation uses a two-pass approach:

1. **Pass 1 (Registration)**: All names are registered with their types or signatures.
2. **Pass 2 (Checking)**: All bodies are type-checked against the registered signatures.

This means a function may call another function defined later in the file, and a trait implementation may reference types or functions not yet defined at that point in the source.

```clojure
;; Forward reference: is-even calls is-odd before it is defined
(defn is-even [n]
  (if (= n 0) true (is-odd (- n 1))))

(defn is-odd [n]
  (if (= n 0) false (is-even (- n 1))))
```

### 5.13.2 Macros [Tested tests/ring3_repl::r3_neg_forward_reference_not_expanded, tests/macros::batch_defmacro_simple]

Macros MUST be defined before use. A macro cannot be forward-referenced. This is because macro expansion occurs in a single pass, and each `defmacro` is compiled immediately when encountered. A reference to a macro that has not yet been defined is an error.

```clojure
;; CORRECT: macro defined before use
(defmacro double [x] `(+ ~x ~x))
(defn f [x] (double x))

;; ERROR: macro used before definition
(defn f [x] (double x))
(defmacro double [x] `(+ ~x ~x))
```

### 5.13.3 Module-Phase Declarations [Tested tests/ring2.rs::module_phase_declarations_order_independent, crates/cranelisp-frontend/src/module_extract.rs::test_mixed_forms]

`mod`, `import`, `export`, and `platform` are extracted before any other processing. Their position in the source file relative to other definitions does not matter, though by convention they appear at the top.

## 5.14 Summary of Top-Level Forms [Tested]

| Form | Kind | Visibility | Phase |
|---|---|---|---|
| `defn` / `defn-` | Special form | Public / Private | AST building |
| `deftype` / `deftype-` | Special form | Public / Private | AST building |
| `deftrait` / `deftrait-` | Special form | Public / Private | AST building |
| `impl` | Special form | Always public | AST building |
| `defmacro` / `defmacro-` | Special form | Public / Private | Macro expansion |
| `const` / `const-` | Prelude macro | Public / Private | Macro expansion |
| `def` / `def-` | Prelude macro | Public / Private | Macro expansion |
| `mod` / `mod-` | Module declaration | Public / Private | Module loading |
| `import` | Module declaration | N/A | Module loading |
| `export` | Module declaration | N/A | Module loading |
| `platform` | Platform declaration | N/A | Module loading |
