# 5. Definitions [Tested]

This section specifies the top-level definition forms in Cranelisp. All definitions appear at the top level of a source file or module. They introduce named functions, types, traits, macros, constants, and module structure into the program.

## 5.1 Function Definition (`defn` / `defn-`) [Tested]

### 5.1.1 Single-Signature [Tested tests/spec_05_definitions::defn_define_and_call]

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
- Parameter names MUST be unique within a parameter list, with one exception: the name `_` (underscore) is a **discard parameter** and is exempt from the duplicate name check. Each `_` is an independent discard — the value is bound to a fresh, unreferenceable variable. Multiple `_` parameters MAY appear in the same parameter list. Referencing `_` in the function body is a compile-time error. [S52]

```clojure
(defn fold [f _ acc] (f acc))              ; one discard
(fn [acc _ _] acc)                         ; multiple discards -- each is independent
```

### 5.1.2 Multi-Signature [Tested tests/spec_05_definitions::defn_multi_clause_arity]

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

### 5.1.3 Auto-Currying [Tested tests/spec_05_definitions::defn_auto_curry_call_with_fewer_args]

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

### 5.2.1 Product Type (Single Constructor) [Tested crates/cranelisp-typecheck/src/adt.rs::test_register_product_type_with_fields]

When the type body is a bracketed field list, the type name doubles as the sole constructor.

```clojure
(deftype Point [:Int x :Int y])

(deftype (Pair a b) [:a first :b second])
```

- `Point` is both the type name and the constructor: `(Point 3 4)` constructs a value.
- Fields are alternating `:Type name` pairs within brackets.
- The constructor behaves as a function: `Point :: (Fn [Int Int] Point)`.

### 5.2.2 Sum Type (Multiple Constructors) [Tested tests/spec_05_definitions::data_constructor_arg_from_closure_call_result]

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

### 5.2.3 Enum (All Nullary) [Tested crates/cranelisp-typecheck/src/adt.rs::test_register_enum_type, tests/repl_introspection.rs::deftype_display_enum, tests/spec_05_definitions.rs::deftype_enum_construct_and_match, tests/examples.rs::every_example_runs_with_documented_exit]

An enum is a sum type where all constructors are nullary.

```clojure
(deftype Color Red Green Blue)
```

This is syntactically a sum type with no field lists. Enum values are represented as bare integer tags at runtime (see [Section 12: Runtime Model](12-runtime.md)).

### 5.2.4 Shortcut Syntax -- Inferred Type Parameters [Tested tests/spec_05_definitions::deftype_product_shortcut_field_names]

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

### 5.2.5 Docstrings on Types and Constructors [Tested tests/spec_05_definitions::deftype_with_docstring_does_not_affect_construct_or_match]

An optional docstring MAY appear after the type head (before the body) and after each constructor name (before its field list).

```clojure
(deftype (Option a) "An optional value"
  (None "Represents absence")
  (Some "Wraps a present value" [:a val]))
```

### 5.2.6 Generated Accessors [Tested+Neg tests/spec_05_definitions::generated_field_accessor_resolves_as_free_callable, tests/spec_05_definitions::accessor_cross_type_duplicate_field_name, tests/spec_field_accessor::bare_alias_resolves_when_field_unique, tests/spec_field_accessor::bare_alias_and_canonical_dispatch_equivalently, tests/spec_field_accessor::bare_alias_ambiguous_canonical_both_work]

For each named field in a type definition, an accessor function is automatically generated. **The canonical name of the accessor is the dotted form `Type.field`** — e.g. `Box.v`, `Point.x` — always available wherever `Type` is in bare scope (§8.5.2). This mirrors the language's qualified-display convention used everywhere else (`:primitives/Int`, `:(Fn [a] a) user/id`): the fully-qualified `Type.field` is the primary, displayed/reported name of the accessor (FIXME 0365/0439, settled S91).

The **bare field name** (`v`, `x`) is a **convenience alias** to the canonical accessor. It resolves to `Type.field` when exactly one in-scope type owns a field of that name. The bare form is the ordinary way to write an accessor in unambiguous code; it is not a separate function — it is shorthand for the canonical `Type.field`.

**Product type accessors** are total -- they always succeed:

```clojure
(deftype Point [:Int x :Int y])

(Point.x (Point 3 4))   ; -> 3   (canonical accessor)
(x (Point 3 4))         ; -> 3   (bare alias — unambiguous here)
;; Point.x :: (Fn [Point] Int)
;; Point.y :: (Fn [Point] Int)
```

**Sum type accessors** are partial -- they succeed on the matching variant and panic on mismatched variants:

```clojure
(deftype (Option a) None (Some [:a unwrap]))

(Option.unwrap (Some 42))   ; -> 42
(unwrap (Some 42))          ; -> 42  (bare alias)
(Option.unwrap None)        ; -> runtime panic
;; Option.unwrap :: (Fn [(Option a)] a)
```

Accessor functions are first-class values and can be passed as arguments or bound to variables. The canonical `Type.field` form is always first-class; the bare alias is first-class wherever it resolves unambiguously.

**Duplicate field names — the ambiguity lives in the bare alias, not the accessor.** Two type definitions MAY use the same field name (e.g. `(deftype Box [:Int v])` and `(deftype Cup [:Bool v])` both have a field `v`). The two canonical accessors `Box.v` and `Cup.v` are **distinct, always-valid functions** — there is no collision and no "poisoning" at the canonical level. What is contested is the single **bare alias** `v`: when two or more in-scope types own a field named `v`, the bare alias has no unique target, so any use of bare `v` is a **compile-time error that lists the canonical alternatives** (`Box.v`, `Cup.v`) under the §8.6.5 bare-name ambiguity rule. The compiler MUST NOT silently fold the alias into an argument-type-dispatched overload, and MUST NOT silently pick a winner.

The field stays reachable in every case — the contest never strands a field:
- via the canonical accessor `Box.v` / `Cup.v` (§8.5.2) — **always valid**, in both the unique and contested cases, same-module and cross-module. This is the primary form; it is never an "escape hatch" because it is the accessor's real name;
- via `match` (§6) — pattern destructuring is unaffected by alias contention and is always available;
- cross-module, via module-qualified names (§8.5.1) — `m/Box.v` (or the bare `m/v` where it resolves) reaches the module's accessor.

A field accessor can never be shadowed by a same-named trait method: a trait `impl` whose method name collides with an existing field-accessor name of the target type is rejected at impl time (§7.3.1), so the canonical `Type.field` always denotes exactly one thing.

Alias contention is scoped to the colliding bare name only: a bare field name **not** in contention still resolves uniquely to its canonical accessor and remains first-class (passable as an argument or bound to a variable). A contested bare alias has no single denotation (the coherence reason it cannot silently become an overload), but its canonical accessors each do.

### 5.2.7 Constructor Semantics [Tested tests/spec_05_definitions::deftype_product_constructor_arity_mismatch_neg]

- **Nullary constructors** are values, not functions. Entering a nullary constructor at the REPL displays its type.
- **Data constructors** are functions. They participate in auto-currying: `(let [f Some] (f 42))` works.
- Constructor names are conventionally capitalized, but this is not enforced.
- Constructor tags are assigned sequentially starting from 0 in definition order.

## 5.3 Trait Declaration (`deftrait` / `deftrait-`) [Tested]

```ebnf
deftrait_form  = '(' ('deftrait' | 'deftrait-') trait_head docstring? method_sig+ ')'
trait_head     = name                         (* simple trait *)
               | '(' name type_var+ ')'       (* higher-kinded trait *)
method_sig     = required_method | default_method
required_method = '(' name docstring? '[' param+ ']' type_expr ')'
default_method  = '(' name docstring? '[' param+ ']' body ')'
param          = ':' type_expr symbol          (* typed parameter *)
               | symbol                        (* bare -- implementing type *)
type_expr      = 'self'                       (* implementing type *)
               | symbol                        (* named type or type var *)
               | '(' 'Fn' '[' type_expr* ']' type_expr ')'   (* function type *)
               | '(' name type_expr+ ')'       (* applied type *)
```

A trait declaration introduces a named interface with one or more method signatures. All methods use named parameters in brackets. Required methods end with a return type; default methods end with a body expression.

### 5.3.1 Simple Traits [Tested tests/spec_07_traits::user_trait_simple, tests/spec_05_definitions::deftrait_impl_and_dispatch]

```clojure
(deftrait Display "Convert a value to its string representation"
  (show "Return string form of value" [x] String))

(deftrait Eq "Equality comparison"
  (= "Test equality" [a b] Bool))
```

- All methods use named parameters in brackets. Bare parameter names default to the implementing type.
- `self` (lowercase) in return type position refers to the implementing type.
- Required methods end with a return type expression; default methods end with a body expression.
- An optional docstring MAY appear on the trait itself and on each method.

### 5.3.2 Higher-Kinded Traits [Tested tests/spec_07_traits::hkt_deftrait_declaration_with_type_constructor_parameter_succeeds]

When the trait head includes type parameters, the trait operates on type constructors rather than concrete types.

```clojure
(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container"
    [:(Fn [a] b) f :(f a) x] (f b)))
```

- The type parameter `f` represents a type constructor (e.g., `Option`, `List`).
- Method signatures MAY use the type parameter applied to type variables: `(f a)`.
- HKT method parameters do not use bare names for `self`; instead, all parameters have explicit type annotations.

### 5.3.3 Trait Semantics [Tested tests/spec_05_definitions::deftrait_impl_and_dispatch, tests/spec_07_traits::trait_method_no_impl_then_recovery]

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

### 5.4.1 Concrete Implementation [Tested tests/spec_07_traits::user_trait_simple, tests/spec_07_traits::trait_impl_on_enum_adt_with_match_over_all_constructors, tests/spec_07_traits::trait_multiple_impls]

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

### 5.4.2 Concrete ADT Instantiation [Tested tests/spec_07_traits::polymorphic_impl_on_concrete_adt_instantiation]

```clojure
(impl Display (Option Int)
  (defn show [self]
    (match self
      [None "None"
       (Some x) (show x)])))
```

This implements Display for `(Option Int)` specifically. The `(show x)` call in the `Some` arm dispatches to the `Int` implementation.

### 5.4.3 Polymorphic Implementation [Tested tests/spec_07_traits::polymorphic_impl_on_concrete_adt_instantiation]

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

### 5.4.4 Higher-Kinded Implementation [Tested tests/spec_07_traits::hkt_impl_targets_bare_type_constructor_not_applied_form]

For HKT traits, the target is a bare type constructor name (not an applied type):

```clojure
(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some x) (Some (f x))])))
```

### 5.4.5 Implementation Semantics [Tested tests/spec_07_traits::user_trait_simple, tests/spec_07_traits::trait_method_no_impl_then_recovery]

- `impl` has no private variant. All trait implementations are visible wherever both the trait and type are visible — i.e., wherever both are reachable through the current module's transitive import closure. See [§5.11.1](#5111-impl-visibility--transitive-import-closure) for the full visibility rule and worked example, and [§7.11.1](07-traits.md#7111-impl-visibility--transitive-import-closure) for resolution-side consequences.
- Method definitions within `impl` follow `defn` syntax but MUST NOT include docstrings (the docstring comes from the trait declaration).
- The method parameter count and types MUST conform to the trait's declared signature.
- Method bodies are type-checked against the instantiated trait signature.

## 5.5 Macro Definition (`defmacro` / `defmacro-`) [Tested tests/spec_05_definitions::defmacro_registers_with_display]

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

A macro MAY return `(begin form1 form2 ...)` to splice multiple top-level forms into the enclosing scope. `begin` is handled by the macro expander. In batch (file) source code it is NOT valid as a user-authored top-level form (the file itself already provides the cluster scope per §5.13.1). At the REPL, `begin` IS valid as a user-authored cluster boundary -- see [§5.13.2](#5132-repl-input-boundary-and-begin-clusters).

```clojure
(defmacro def-pair [name a b]
  `(begin
    (defn ~(make-name1 name) [] ~a)
    (defn ~(make-name2 name) [] ~b)))
```

## 5.6 Constants (`const` / `const-`) [Tested tests/spec_11_stdlib::macro_const_int, tests/spec_11_stdlib::macro_const_string, tests/exemplar.rs::batch_const_macro_in_main]

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

## 5.7 Named Values (`def` / `def-`) [Tested tests/spec_11_stdlib::macro_def_basic, tests/spec_11_stdlib::macro_def_expression]

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

## 5.8 Module Declaration (`mod`) [Tested tests/spec_08_modules::synthetic_primitives_module_available, tests/spec_08_modules::qualified_ref_to_missing_module_errors_neg, tests/spec_08_modules::module_cycle_detection_neg]

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

## 5.9 Import and Export [Tested tests/spec_08_modules::import_specific_name_compiles_and_runs, tests/spec_08_modules::import_glob_brings_in_all_exports]

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
- The grammar above is a summary. The full grammar — including module aliases `(mod alias)`, symbol-rename pairs `(source local)`, member globs `Type.*`, and selective dotted members — is defined in [§8.3](08-modules.md#83-import) (import) and [§8.4](08-modules.md#84-export) (export). Renames and module aliases are symmetric across import and export.
- See [Section 8: Modules](08-modules.md) for full module resolution semantics.

## 5.10 Platform Declaration [S10]

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

## 5.11 Visibility [Tested tests/spec_05_definitions::private_defn_callable_in_module]

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
- `impl` has no private variant. Trait implementations are always visible wherever both the trait and the type are in scope. The phrase "in scope" means **reachable through the transitive import closure of the current module** — see §5.11.1 for the precise rule and worked example, and cross-references to [§7.11](07-traits.md#711-scope-and-visibility) (trait-side) and [§8.4.8](08-modules.md#848-implicit-impl-re-export) (module-side).
- `import`, `export`, and `platform` have no private variants.

### 5.11.1 Impl Visibility — Transitive Import Closure [S66]

A trait implementation `(impl Trait Type ...)` declared in module L is visible in module N when **both** the trait `Trait` and the type `Type` are reachable from N through the transitive closure of N's `import` declarations. An implementation MUST NOT require N to directly import L for the impl to be visible; if L's impl is reachable through any chain of imports (or re-exports — see §8.4.8) that brings `Trait` and `Type` into N's scope, the impl is in scope at N.

This matches the "instances are global within the import closure" semantics found in Haskell-family type-class systems: users do not enumerate impls in import or export lists; impls follow the trait and type wherever those names go.

**Worked example.** Three modules:

```clojure
;; --- l.cl ---
(deftype Color Red Green Blue)
(deftrait Display (show [self] String))
(impl Display Color
  (defn show [c] (match c [Red "Red" Green "Green" Blue "Blue"])))

;; --- m.cl ---
(import [l [Color Display Red Green Blue]])
(export [l [Color Display Red Green Blue]])

;; --- n.cl ---
(import [m [Color Display Red Green Blue]])
;; n.cl does NOT import l directly.
(defn describe [c] (show c))   ; OK -- (impl Display Color) from L is visible to N
```

N reaches `Display` and `Color` through M's re-export of L's names. The `(impl Display Color)` declared in L is therefore visible at N's call to `show`, and the call resolves to L's `Color` impl — even though N never wrote `(import [l ...])`. This applies symmetrically whether N reaches the trait/type via explicit re-export (`(export [l [...]])`), via a glob re-export (`(export [l [*]])`), or via direct import of L from a module that itself imports L.

**Visibility is a property of the trait + type pair, not the impl form.** An impl becomes invisible from N only when at least one of `Trait` or `Type` is unreachable from N. In particular, a private name (`defn-`, `deftype-`, `deftrait-`, see §5.11) breaks the chain: an impl declared in L for a private trait or type cannot reach beyond L's submodule subtree, because the names themselves cannot.

**Implementation note (non-normative).** The lookup mechanism — pre-computed per-module impl index, on-demand walk of `current_module.imports`, or another shape — is **implementation-defined**. The spec pins the visibility rule, not the algorithm.

## 5.12 Docstrings [Tested tests/spec_05_definitions::docstring_does_not_affect_call]

Definitions MAY include an optional docstring -- a string literal placed between the name and the parameter list (or body).

| Form | Docstring position |
|---|---|
| `defn` | Between name and params: `(defn name "doc" [params] body)` |
| `deftype` | After type head: `(deftype Name "doc" ...)` |
| `deftrait` | After trait head: `(deftrait Name "doc" ...)` |
| Trait method | After method name: `(method "doc" [params] ret_or_body)` |
| Constructor | After constructor name: `(CtorName "doc" [:Type field])` |
| `defmacro` | Between name and params: `(defmacro name "doc" [params] body)` |

**Semantics:**

- Docstrings are stored in the compilation metadata and are available for introspection (e.g., via REPL `/doc` command).
- Docstrings have no effect on program semantics.
- `const`, `def`, `impl`, `mod`, `import`, `export`, and `platform` do not support docstrings.

The **module-level** analogue of a docstring is the *module preamble* (§8.16) — a **leading `;;` comment block** at the head of a module file (file-header docs) that documents the module as a whole. The lexis is deliberately asymmetric to a docstring: a `defn` docstring is a leading *string literal* (anchored by the binding form), whereas the module preamble is a *comment block*. A module has no binding form to carry a leading string literal unambiguously, and file-header comments are where module documentation naturally lives — so the module preamble uses comment lexis (§8.16.6 explains the asymmetry in full). Like a docstring it is metadata-only, and it is read via the `/doc <module>` family.

## 5.13 Definition Ordering [Tested]

### 5.13.1 Functions, Types, Traits, and Implementations [Tested tests/spec_05_definitions::defns_mutual_forward_references]

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

### 5.13.2 REPL Input Boundary and `begin` Clusters [Tested tests/process_form_dispatch::process_form_dispatch_begin_cluster_resolves_mutual_forward_ref, tests/process_form_dispatch::process_form_dispatch_bare_forward_ref_errors_clearly]

In the REPL, **each input is a single top-level form**. Forward references to definitions defined in subsequent REPL inputs are NOT supported -- non-`begin`-grouped forms are processed in source order, one per eval. A reference in a REPL input to a name that has not yet been defined is an error, with the same diagnostic shape as a reference to a non-existent identifier.

**Incomplete form at end of input.** The REPL accumulates input across continuation lines until delimiters balance, then submits the form. If input ends (EOF — Ctrl-D, or the end of piped input) while a top-level form is still incomplete (unbalanced delimiters), the implementation MUST produce a parse error; the incomplete buffer MUST NOT be silently discarded. This mirrors the rule that a complete form at the prompt is submitted and executed: an incomplete form cannot be submitted, so its arrival at EOF is an error. [Tested tests/repl_negative.rs::parse_error_unclosed_paren_neg]

Mutual recursion in the REPL is expressed via `(begin form₁ form₂ ... formN)`, which the orchestrator processes as a single **cluster**: signatures of all forms register first (Pass 1), then bodies are type-checked (Pass 2), and the cluster commits atomically (all-or-nothing). Within a cluster, §5.13.1's MAY-reference-freely rule applies across the forms in that one cluster. This is the REPL analogue of the file-scope two-pass behaviour.

```clojure
;; REPL: forward reference within a single cluster -- OK
(begin
  (defn is-even [n] (if (= n 0) true (is-odd (- n 1))))
  (defn is-odd  [n] (if (= n 0) false (is-even (- n 1)))))

;; REPL: forward reference across separate inputs -- ERROR
(defn f [] (g 1))    ; ERROR: g is not defined
(defn g [x] x)       ; (defining g now does not retroactively repair f)
```

This forward-reference rule applies to non-macro top-level definitions: `defn`, `deftype`, `deftrait`, `impl`. **Macros are the exception** -- they follow the **defmacro-before-use** rule (§9.3.4) in both the REPL and batch: a macro MUST be defined before its first use in source order, and a use that appears textually before its `defmacro` is an ordinary reference (it passes through to the AST builder), not a macro call. A `defmacro` is part of the **compile-time layer** that runs *before* the cluster's non-macro forms are registered (the three-pass model, §9.12), so a forward reference to a macro is not resolvable as a macro even within a single cluster. Macro **expansion** may reference dependency-module definitions and same-module macros, never same-module non-macro definitions (§9.3.4). This is the same rule in the REPL and in batch — there is no REPL-vs-batch macro-availability divergence.

**Cluster atomicity**: If type checking fails for any form in the cluster, none of the forms are committed -- the REPL state is unchanged. On success, all forms commit together.

**Module-phase declarations** (`mod`, `import`, `export`, `platform`) MUST NOT appear inside a `begin` cluster. They are processed in the module phase (see §5.13.3 and §2.1), before macro expansion and clusters. A `begin` form in user code that contains a module-phase declaration is a compile-time error.

**Batch (file-level) non-macro semantics**: §5.13.1's MAY-reference-freely rule continues to apply across the file scope for `defn`/`deftype`/`deftrait`/`impl`. The orchestrator effectively treats a file's top-level non-macro definitions as one cluster (registered in Pass 2/3 of the three-pass model, §9.12). **Macros are the exception**: a `defmacro` is part of the compile-time layer (Pass 1) that runs *before* the cluster's non-macro forms are registered, so a macro is available only to forms that **follow** its `defmacro` in source order — the defmacro-before-use rule (§9.3.4), uniform across REPL and batch:

```clojure
;; Batch: defmacro precedes its use
(defmacro double [x] `(+ ~x ~x))
(defn f [x] (double x))

(defmacro triple [x] `(+ ~x ~x ~x))
(defn g [x] (triple x))
```

**Why explicit clustering?** This aligns Cranelisp with statically-typed REPL precedent. ML-family languages (OCaml, SML, F#) require explicit `let rec ... and ...` syntax for mutual recursion at any scope; Haskell-family languages (Haskell, Elm, PureScript) do automatic dependency analysis at module scope but treat each REPL input as a separate eval (with explicit grouping syntax such as `:{ ... :}` for multi-form input). Cranelisp matches Haskell-family at file scope (automatic via two-pass per §5.13.1) and ML-family at REPL scope (explicit `begin` cluster).

### 5.13.3 Module-Phase Declarations [Tested tests/spec_08_modules::import_below_use_still_available_before_definitions, crates/cranelisp-frontend/src/module_extract.rs::test_mixed_forms]

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
