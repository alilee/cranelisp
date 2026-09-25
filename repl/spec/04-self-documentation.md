> [REPL specification index](index.md)

## 4. Self-Documentation Contract

Every valid language construct entered at the REPL MUST produce useful feedback. This is the **self-documentation principle** from the project's design principles. All output reinforces the language syntax.

### 4.1 Symbol Lookup — Per-Class Specification

Entering a bare symbol name at the REPL MUST produce output following the universal format (§1.1). Every symbol class has a defined response. No valid name MUST produce an opaque error. If a name is unbound, the error MUST say so clearly. [Tested tests/repl_negative::unbound_symbol_clear_error] Colour styling of every introspection line here is governed by **§10.3** (the type annotation is R4 cyan, a `module/` name prefix R7 dim, the `; classification` and `; match:`/`; defn:`/`; impl:` drawers R6 dim).

#### 4.1.1 Functions (defn) [Tested tests/repl_introspection::bare_fn_lookup_after_defn_shows_defn_classification]

Primary line only. Classification `defn`. Docstring appended if present.

```
user> double
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2

user> id
:(Fn [a] a) user/id ; defn
```

Constrained functions show inline constraints per §1.4:

```
user> add
:(Fn [:Num a :a] a) user/add ; defn - Add two numbers
```

Overloaded functions show all variant signatures, one per line:

```
user> map
:(Fn [(Fn [a] b) (user/Vec a)] (user/Vec b)) user/map ; defn - Transform elements
:(Fn [(Fn [a] b) (user/List a)] (user/List b)) user/map
```

A variant that infers a trait bound MUST display that bound inline, exactly as a
single-signature constrained function does (§1.4) — the per-variant signature is a
signature and carries its own constraints. A multi-signature `defn` is inference-
equivalent to its clauses written as separate mutually-recursive functions (spec
§5.1.2), so a clause such as `([a b] (+ a b))` displays `:(Fn [:core.num/Num a :core.num/Num a] a)`,
never the constraint-stripped `:(Fn [a a] a)`. Dropping the constraint from a
variant's display is a §1.4 non-conformance even when the bound is still enforced.

| Requirement | Test |
|---|---|
| function shows type + name | [Tested tests/repl_introspection::bare_fn_lookup_after_defn_shows_defn_classification] |
| constrained fn shows constraints | [Tested tests/repl_introspection::bare_fn_lookup_after_defn_shows_defn_classification] |
| overloaded fn shows all variants | [Tested tests/repl_introspection::display_overloaded_fn_shows_all_variants] |

#### 4.1.2 Constructors [Tested tests/repl_introspection::nullary_constructor_bare_lookup_shows_deftype_and_qualified_home]

Primary line only. Classification `deftype` (constructors are created by `deftype`). Nullary constructors have no function type — just the ADT type.

```
user> Some
:(Fn [a] (user/Option a)) user/Option.Some ; deftype

user> Red
:user/Color user/Color.Red ; deftype
```

For single-constructor types where the constructor name matches the type name, the `Type.` prefix is suppressed:

```
user> Point
:(Fn [primitives/Int primitives/Int] user/Point) user/Point ; deftype
```

**Dotted-input parity — no type-segment doubling.** A constructor entered in its
dotted `Type.Ctor` form (e.g. `Color.Red`) MUST render the **same** canonical
qualified home as the bare form (`Red`):

```
user> Color.Red
:user/Color user/Color.Red ; deftype
```

never:

```
:user/Color user/Color.Color.Red ; deftype
```

The value slot carries the constructor's home exactly once (`module/Type.Ctor`);
the dotted-input path and the bare-input path render through one canonical home and MUST NOT diverge. [Tested tests/repl_introspection::dotted_nullary_constructor_input_does_not_double_type_segment]

#### 4.1.3 Types (deftype) [Tested tests/repl_introspection::bare_type_lookup_includes_match_section]

Primary line plus related symbols. Classification `deftype` for user types, `type` for builtin types. Related symbols show constructors under `match:` (the language construct used with them) and trait implementations under `impl:`.

```
user> Color
:user/Color ; deftype
; match:
;  Red Green Blue

user> Option
:user/Option ; deftype
; match:
;  None Some
; impl:
;  Display Eq

user> Int
:primitives/Int ; type
; impl:
;  Display Eq Num Ord
```

Constructor names under `match:` are unqualified bare names. Trait names under `impl:` are unqualified. Within `impl:`, locally-defined traits appear first, then imported traits.

| Requirement | Test |
|---|---|
| builtin types (Int, Bool, Float, String) | [Tested tests/repl_introspection::bare_type_lookup_includes_match_section] |
| user-defined type | [Tested tests/repl_introspection::bare_type_lookup_includes_match_section] |
| related constructors | [Tested tests/repl_introspection::bare_type_lookup_includes_match_section] |
| related trait impls | [Tested+Neg tests/repl_introspection::bare_type_lookup_includes_match_section] |

#### 4.1.4 Traits (deftrait) [Tested tests/repl_introspection::bare_trait_lookup_includes_defn_section]

Primary line plus related symbols. Classification `deftrait`. Related symbols show method names under `defn:` and implementing types under `impl:`.

```
user> Display
:core.str/Display ; deftrait - Format as string
; defn:
;  show
; impl:
;  Point
;  Bool Float Int List Vec

user> Num
:num.num/Num ; deftrait - Numeric operations
; defn:
;  + - * /
; impl:
;  Float Int
```

Within `impl:`, locally-defined types appear first, then imported types. Method names under `defn:` are unqualified.

#### 4.1.5 Special Forms [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting]

Primary line only. Classification `special form`. Special forms display a function-like type signature that teaches their syntax shape.

```
user> if
:(Fn [primitives/Bool a a] a) if ; special form - Conditional branch

user> let
:(Fn [bindings body] a) let ; special form - Local bindings

user> defn
:(Fn [name params body] function) defn ; special form - Define function

user> defmacro
:(Fn [name docstring? params body] macro) defmacro ; special form - Define macro
```

| Form | Test |
|---|---|
| `if` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `let` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `fn` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `defn` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `deftype` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `match` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |
| `defmacro` | [Tested tests/repl_introspection::special_forms_bare_lookup_fn_self_documenting] |

#### 4.1.6 Macros (defmacro) [Tested]

Each macro clause displays one compile-time transformation signature, in the
same one-line-per-arm layout as a multi-signature function. The first line has
classification `defmacro` and the optional docstring. A fixed parameter binds a
`macros/Sexp`; a top-level rest parameter binds the remaining forms as
`(macros/SList macros/Sexp)`; the result is always `macros/Sexp`. This describes
the macro transformation and MUST NOT expose the type of an expression produced
by expansion or imply that the macro is a runtime function value.

The `Fn` type cannot express a macro's bracket-destructuring or variadic call
pattern. When a clause uses either, the signature is followed by a `; pattern:`
line containing the authored parameter pattern. Simple fixed-position parameter
names add no information to the typed signature and are omitted.

```
user> twice
:(Fn [macros/Sexp] macros/Sexp) user/twice ; defmacro - Evaluate and double

user> my-add
:(Fn [macros/Sexp (macros/SList macros/Sexp)] macros/Sexp) user/my-add ; defmacro - Variadic addition
; pattern: [x & rest]
```

Zero-arg macros expand immediately — they do not reach the lookup path.

| Requirement | Test |
|---|---|
| macro shows transformation signatures | [Tested tests/repl_introspection::defmacro_display_single_clause] |
| multi-clause macro shows every signature | [Tested tests/repl_introspection::defmacro_display_multi_clause] |

#### 4.1.7 Primitive Functions [Tested+Neg tests/repl_introspection::bare_primitive_add_i64_at_prompt_displays_type_and_fqn, tests/repl_introspection::bare_primitive_lookup_not_empty_neg]

Primary line only. Classification `primitive` (distinguishes builtins from user-defined `defn`). Primitives are defined in the `primitives` module.

```
user> add-i64
:(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64 ; primitive - Add

user> str-concat
:(Fn [primitives/String primitives/String] primitives/String) primitives/str-concat ; primitive - Concatenate two strings
```

The classification word `primitive` (rather than `defn`) is intentional: it distinguishes host-implemented builtins from user-defined functions. The builtin's docstring (sourced from [Appendix A.5](../../spec/appendix-a-builtins.md#a5-docstrings-for-builtins-r1)) follows the classification in the same `; {classification} - {docstring}` dash form per §1.1.


#### 4.1.8 Trait Methods (including operators) [Tested tests/repl_introspection::operator_plus_bare_lookup_displays_signature]

Trait methods use `Trait.method` dot notation in the name position, fully qualified with the defining module. Classification `deftrait` (methods are declared by `deftrait`).

```
user> +
:(Fn [:core.num/Num a :a] a) core.num/Num.+ ; deftrait - Addition operator

user> show
:(Fn [:core.str/Display a] primitives/String) core.str/Display.show ; deftrait - Format as string

user> =
:(Fn [:core.cmp/Eq a :a] primitives/Bool) core.cmp/Eq.= ; deftrait
```

This applies to all trait methods, not just operators. The `Trait.method` notation is valid input syntax (per spec §1.4.4), reinforcing discoverability.

#### 4.1.9 Modules [R4]

Primary line plus related symbols. Classification `mod`. Related symbols show the module's public exports under `exports:`.

```
user> math
:math ; mod
; exports:
;  foo bar
```

Module lookup is Ring 4 scope.

#### 4.1.10 Unbound Names [Tested tests/repl_negative::unbound_symbol_clear_error]

An unbound name MUST produce a clear error message, not an opaque internal error. The session MUST continue.

```
user> xyz
error: unbound symbol 'xyz'
```

#### 4.1.11 Spellings With Several Candidates [Tested+Neg]

A bare spelling can denote several distinct canonical declarations in the
current module scope: the terminal-deduplicated candidate set of spec
`08-modules.md` §8.6.1 layer 2, §8.6.2 and §8.6.4. Bare lookup reports that
set in full.

Bare lookup MUST print the primary line or lines of every candidate, each
rendered by its own §4.1.x class rule with its fully-qualified name. It MUST
NOT omit a candidate, MUST NOT show one candidate chosen by local, import,
prelude or tier origin or by arrival order, and MUST NOT report the spelling
as unbound (§4.1.10). Candidates whose types coincide are still distinct
declarations and each MUST appear; lookup does not compare candidate types.

Lookup is introspection, not use: it MUST NOT report an ambiguity error or
warning for the candidate set. Selection — and the ambiguity rejection that
goes with it — belongs to an input that *uses* the spelling, which resolves
under spec `08-modules.md` §8.6.5 without relaxation.

Given imported functions `a/f` and `b/f`, both `(Fn [Int] Int)`, and
`c/f : (Fn [String] String)`:

```
user> f
:(Fn [primitives/Int] primitives/Int) a/f ; defn
:(Fn [primitives/Int] primitives/Int) b/f ; defn
:(Fn [primitives/String] primitives/String) c/f ; defn
```

`(f "x")` still selects `c/f`; `(f 1)` is still ambiguous between `a/f` and
`b/f` and the source must qualify one (§8.6.5).

`/sig`, `/info` and `/doc` on a bare name report every candidate, each in that
command's own format (§3.8, §3.6, §11.2.4). None of them substitutes an
ambiguity error for the listing.

| Requirement | Test |
|---|---|
| every candidate's primary line printed, fully qualified, by its own class rule | [Tested+Neg tests/repl_introspection::prelude_and_local_candidates_both_list_at_bare_lookup_and_sig, tests/repl_introspection::two_imported_candidates_both_list_at_bare_lookup_and_sig, tests/repl_introspection::nullary_ctor_and_function_candidates_both_list_at_bare_lookup, tests/repl_introspection::one_terminal_reached_two_ways_lists_once] |
| candidates whose types coincide are each listed; no type comparison at lookup | [Tested+Neg tests/repl_introspection::identically_typed_candidates_both_list_neg_no_ambiguity_at_lookup] |
| no candidate omitted or chosen by origin, tier or order; never reported unbound | [Tested+Neg tests/repl_introspection::prelude_and_local_candidates_both_list_at_bare_lookup_and_sig, tests/repl_introspection::two_imported_candidates_both_list_at_bare_lookup_and_sig] |
| no ambiguity error or warning at lookup; a use of the spelling still resolves under §8.6.5 | [Tested+Neg tests/repl_introspection::identically_typed_candidates_both_list_neg_no_ambiguity_at_lookup, tests/repl_introspection::identically_typed_candidates_ambiguous_use_still_rejected_neg_no_silent_selection] |
| `/sig`, `/info` and `/doc` list every candidate in their own format | [Tested+Neg tests/repl_introspection::prelude_and_local_candidates_both_list_at_bare_lookup_and_sig, tests/repl_introspection::info_lists_prelude_and_local_candidates, tests/repl_introspection::doc_lists_prelude_and_local_candidates, tests/repl_introspection::info_lists_identically_typed_candidates, tests/repl_introspection::doc_lists_identically_typed_candidates] |
