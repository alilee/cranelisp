# 5. Definitions [Tested]

This section specifies the top-level definition forms in Cranelisp. All definitions appear at the top level of a source file or module. They introduce named functions, types, traits, macros, constants, and module structure into the program.

**Declaration heads are binders. [S113]** Every definition form in this section binds a **new** name into the **current** module. A declaration head — the name a definition form introduces — is a **binder, not a reference**, and MUST be a **bare (unqualified) symbol**. This is the settled general principle (user ruling 2026-07-18, generalized to all binder heads; the veto window closed at S112 Phase 7): it holds for **every** binder head, not only the two forms the original ruling named. A **qualified** spelling in declaration-head position — `(defn fmt/foo [x] …)`, `(deftrait (fmt/Foo f) …)`, `(deftype fmt/Foo …)` — is a **compile-time error**, and so is a **dotted** one (`(defn a.foo [x] …)`, `(deftype A.B …)` — user ruling 2026-07-21, *Binder positions* below) [S115]: there is no mechanism for declaring a name into another module; a definition always binds into the module that contains it. This is the dual of the reference rules (§8.5): a **binder** introduces a name where it is written, so it carries no module qualifier; only a **reference** reaches across modules. (`impl` is not an exception — its slot 1 echoes a trait *reference*, not a fresh binder, [§7.3](07-traits.md#73-trait-implementation).)

The **native binder special forms** are `defn`/`defn-`, `deftype`/`deftype-`, `deftrait`/`deftrait-`, and `defmacro`/`defmacro-`, together with the **method definitions inside an `impl` body**, the **method-signature names inside a `deftrait`** (a `deftrait` introduces its method names into the current module, §5.3.3 — a method-signature name such as `show` in `(deftrait Foo (show [x] Int))` is a binder, so a qualified spelling `(deftrait Foo (fmt/show [x] Int))` is a compile-time error on this same principle), and the **variant-constructor names and field names introduced by `deftype`** (each variant constructor mints a module-level callable, §5.2.2; each field name mints a module-level accessor `Type.field`, §5.2.6 — both are binders, user ruling 2026-07-19). Each of these heads is a binder subject to the bare-symbol rule above. [S113]

**Binder positions — where the bare-symbol rule applies. [S113]** The user's principle (2026-07-19): **you can define a name only into the module — or lexical scope — that contains the definition; you can never define a name *into another module*, only *reference* one.** A binder therefore never carries a module qualifier (`/`, §1.4.3) or a dotted path (`.`, §1.4.4): those are **reference** syntax (§8.5). A qualified or dotted spelling in **any** binder position is a compile-time error, with the diagnostic span on the offending binder name. The table enumerates every name-introducing position in the language and states the rule for each; the dual — **reference** positions, where a name crosses modules and a qualifier is permitted — is listed last for contrast.

| Position | Form / § | Kind | Rule |
|---|---|---|---|
| `defn`/`defn-` head | §5.1 | binder | bare symbol; qualified/dotted rejects [S115] |
| `deftype`/`deftype-` head | §5.2 | binder | bare symbol; qualified/dotted rejects [S115] |
| `deftype` variant-constructor name | §5.2.2 | binder | bare **uppercase** symbol; qualified/dotted/lowercase rejects [S115] |
| `deftype` field name (mints `Type.field` accessor) | §5.2.6 | binder | bare symbol; qualified/dotted rejects [S115] |
| `deftype` type parameters | §5.2, §2.2.2 | binder (type var) | bare **lowercase** symbol; qualified/dotted rejects [S115] |
| `deftrait`/`deftrait-` head | §5.3, §7.1 | binder | bare uppercase symbol; qualified/dotted rejects [S115] |
| `deftrait` method-signature name | §5.3.3 | binder | bare symbol; qualified/dotted rejects [S115] |
| `deftrait` constructor variables (`con_var`) | §7.2 | binder (type var) | bare lowercase symbol; qualified/dotted rejects [S115] |
| `defmacro`/`defmacro-` head | §5.5 | binder | bare symbol; qualified/dotted rejects [S115] |
| `impl`-body method-defn head | §5.4, §7.3 | binder | bare symbol; qualified/dotted rejects [S115] |
| `const`/`const-`, `def`/`def-` head (stdlib macros) | §5.6, §5.7 | binder (post-expansion) | bare symbol; qualified/dotted rejects, **span at the written head** [S115] |
| `mod`/`mod-` name | §5.8 | binder (module) | simple symbol — not qualified, not dotted |
| `platform` name | §5.10 | binder (composes module path) | simple symbol — not qualified, not dotted |
| `defn`/`defmacro` parameters | §5.1, §5.5 | local binder | bare symbol; qualified/dotted rejects [S115] |
| `fn` (lambda) parameters | §4.5 | local binder | bare symbol; qualified/dotted rejects [S115] |
| `let` binding names | §4.3 | local binder | bare symbol; qualified/dotted rejects [S115] |
| `match` variable pattern | §6.2.4 | local binder | bare symbol; qualified/dotted rejects [S115] |
| `import`/`export` rename local-name, module alias, mount alias | §8.3.4, §8.4.4 | local binder (alias) | bare symbol; qualified/dotted rejects [S115] |
| **Reference (contrast):** `impl` slot-1 trait + slot-2 target | §7.3, §7.3.5 | reference | qualifier **permitted** — resolved by identity |
| **Reference (contrast):** `match` constructor-pattern head | §6.2.1 | reference | dotted canonical form **permitted** (`Maybe.Some`) |
| **Reference (contrast):** variable / call-head / type references | §2.3.2, §8.5 | reference | qualifier/dotted **permitted** |

All binder rows reject decisively — the principle admits no exceptions and no position carries open semantics (a binder that named another module would be defining into it, which the language does not do). The reject is a **binder-position constraint**, enforced at each binder site: a `/`-bearing (qualified, §1.4.3) or `.`-bearing (dotted, §1.4.4) token is not a legal binder, and naming one is a compile-time error with the diagnostic span on the offending name. The reader does **not** reject the token structurally — it produces a single plain symbol (`a/b`), and the qualified-vs-bare classification is applied afterward, at the binder site — so the constraint is stated and checked per-position; it is normative, not incidental to tokenization. (For the value-level local binders — `defn`/`fn` parameters, `let` names, `match` var-patterns — the check runs at the frontend build layer above the int expansion pass, per the S114 ruling on FIXME 0670.)

**Dotted binders reject exactly as qualified ones do — `.` is reserved for type/trait qualification. [S115]** The user ruled (2026-07-21) that a **dotted (`.`) spelling in ANY binder position is a compile-time error**, on the same footing as a `/`-qualified spelling: a **located** error with the diagnostic span on the offending binder name, never a silent bind. `(defn a.b [x] x)`, `(deftype A.B …)`, `(deftype P [:Int a.b])`, `(let [a.b 5] …)`, `(defn g [a.b] 1)` and `(match 1 [a.b a.b])` are all rejected. The ruling is a consequence of the binder principle above, not an addition to it: the language has no notion of defining a name into a nested path, so a dotted binder has no meaning to give. `.` in this language is **type/trait qualification syntax** (§1.4.4) — a *reference* device — and it is never a name-introducing device.

- **Reference positions are untouched.** `.` remains legal wherever a name is *referenced*: the dotted constructor-pattern head `(Maybe.Some x)` (§6.2.1), dotted field accessors `Type.field` (§5.2.6), dotted type/trait references (§8.5), and dotted module paths in `import`/`export` (§8.3, §8.4). Nothing here bans `.` generally — it bans `.` in the binder column only. The binder/reference line is exactly where the rule is drawn.
- **Rider — the qualified type-parameter cell is a clean reject too. [S115]** `(deftype (Pair prim/a b) …)` is a **located binder-reject with the span on the type parameter**, on the same diagnostic footing as every other row. It MUST NOT surface as an incidental downstream failure (e.g. a "module not found" resolution error at a degenerate zero-width span).
- **Scribe's note on the table above.** Before this ruling the table's per-row Rule column named only `/` on most rows while the prose two paragraphs up was already categorical over `/` **and** `.`. That divergence was a *mirror inside the spec* — the same defect class as the §7.1.4 duplicated-rule divergence: one requirement written twice, drifting on the copy nobody re-read. The table rows are now restated from the prose rather than maintained beside it; a future rule change edits the prose and the table together, or the table not at all.

The surface forms **`def`/`def-` and `const`/`const-` are stdlib macros** ([§5.7](#57-named-values-def--def-), [§5.6](#56-constants-const--const-), [§9.10](09-macros.md#910-example-prelude-macros); `stdlib/defs.cl`) — **there is no native `def` special form.** They **expand** to the native binder forms (`defn`/`defmacro`), so the binder rule reaches them **after expansion**: a qualified **or dotted** head such as `(def fmt/x 1)`, `(const fmt/PI 3.14)` or `(def a.x 1)` is rejected on the same principle. [S115] Because the rejection fires on the expanded `defn`/`defmacro`, the diagnostic span MUST point at the **user's written form** — the `def`/`const` head as typed — not the synthesized expansion. [S113]

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

- The name MUST be a valid **bare (unqualified)** symbol — a declaration head is a **binder**, not a reference (§5, *Declaration heads are binders*); a qualified **or dotted** spelling (`fmt/square`, `a.square`) is a compile-time error (§5, *Binder positions*). [S113] [S115]
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

### 5.1.2 Multi-Signature [Tested+Neg tests/spec_05_definitions::defn_multi_clause_arity, tests/multi_arity_clause_param_51_2::rp4_unannotated_backflow_accepted_and_runs, tests/multi_arity_clause_param_51_2::poly_clause_nonoverlapping_arity_accepted_both_dispatch, tests/multi_arity_clause_param_51_2::backflow_pinned_param_call_with_wrong_type_rejected_neg, tests/multi_arity_clause_param_51_2::f3_delegation_chain_backflow_accepted_and_runs, tests/multi_arity_clause_param_51_2::recursive_poly_clause_accepted_matches_standalone_twin, tests/spec_05_definitions::constrained_clause_nonoverlapping_arity_dispatches_two_instantiations — full matrix: plan/s112-0628-ic-wave.md §1] [S112 — one attributed-carry cell RED: cross-arity sibling self-call from a poly template clause, tests/multi_arity_clause_param_51_2::cross_arity_sibling_self_call_from_poly_clause_accepted_matches_standalone_twin (wrong-reject, owner /dev typecheck)]

```ebnf
defn_multi_form = '(' ('defn' | 'defn-') name docstring? variant+ ')'
variant         = '(' params body ')'
```

A multi-signature function definition provides multiple variants with different parameter lists. The implementation dispatches to the appropriate variant based on the concrete argument types at each call site, determined after type inference.

```clojure
(defn size "Return the number of elements"
  ([:(Vec Int) v] (vec-len v))
  ([:(List Int) l] (list-len l)))
```

Each clause's parameters are inferred exactly as for a single-signature `defn`
(§5.1.1). A parametric type still MUST supply its type argument where the
grammar requires it (`:(Vec Int)`, not bare `:Vec` — §5.2, §3). A clause
parameter MAY be left polymorphic on the same terms as a single-signature
`defn`: it is an ambiguous-type error **only when the equivalent standalone
function would also fail to infer it** (§3.11), never merely because it belongs
to a multi-signature form. Type flows across clauses through ordinary call
resolution — see **Inference** below.

**Semantics:**

- All variants MUST share the same function name.
- Each variant is a parenthesized form containing a parameter list in square brackets and a body expression.
- An optional docstring MAY appear between the name and the first variant.
- Dispatch is resolved statically at compile time based on inferred argument types. If no variant matches the concrete types at a call site, it is a compile-time error.
- Variants MAY have different numbers of parameters.
- The mangled name for each variant is the function name followed by `$` and the parameter types joined by `+`. For example, `size` with a `Vec` parameter becomes `size$Vec`.
- **The multi-variant form is available only for `defn`/`defn-`.** The anonymous `fn` ([§4.5](04-expressions.md#45-lambda-expression)) is single-arity — a lambda takes exactly one `[params] body`, and the parenthesised multi-arity clause form is a parse error for `fn`.
- **Clauses must be distinguishable for dispatch.** Two clauses of **different arity** always dispatch by argument count. Two clauses of the **same arity** dispatch by their concrete argument types (after inference, §7.4.4). Two same-arity clauses whose signatures **can unify** — such that one concrete argument tuple could match both — are a **dispatch-ambiguity compile-time error**, reported at the definition (both colliding clauses named), not silently resolved by clause order. **The unifiability judgment is made on the clause signatures *as written* — the pre-inference parameter annotations — never on the types inference later settles.** A same-arity pair whose *written* signatures can unify is a definition-time ambiguity error **even if** inference would later settle the two clauses disjoint (for example when an internal sibling self-call pins one clause to a concrete type). The program `(defn t ([x] x) ([:Int y] y) ([a b] (t "s")))` is rejected **by design**: the `[x]` clause's written signature (`x` unannotated) can unify with the `[:Int y]` clause's `[Int]`, so the two same-arity clauses are a definition-site ambiguity — notwithstanding that the internal `(t "s")` self-call would pin the `[x]` clause to `[String]` and thereby settle the two disjoint. The remedy is to **annotate the clause so the written signatures are disjoint** (here, `([:String x] x)`). This is precisely what §5.1.2 constrains: dispatch *ambiguity*, **not** the presence of polymorphism. A **genuinely-polymorphic** clause is admissible whenever it does not overlap a same-arity sibling (see **Inference** below). [Tested+Neg tests/spec_05_definitions::same_arity_unifiable_clauses_definition_site_error_neg, tests/spec_05_definitions::same_arity_unifiable_clauses_call_site_ambiguous_neg] [Settled 2026-07-18 (user ruling, M1): "can unify" is judged on the WRITTEN (pre-inference) clause signatures; the as-landed pre-drain check implements exactly this reading, and its rejection of the internal-pin program above is correct by design]

**Inference — clause-equivalent to separate mutually-recursive functions.**

A multi-signature `defn` is **inference-equivalent to its clauses written as
separate, mutually-recursive functions that happen to share one dispatched
name.** Each clause is type-checked per §5.1.1, under the two-pass
registration/checking discipline of §5.13.1 (all clause signatures register
first, then all bodies are checked). Type annotations on a clause parameter are
**descriptive, not rigidity-adding** — a written type variable does not add
rigidity of its own ([§3.3](03-types.md#33-type-variables); written ≡ unwritten,
[§3.3.1](03-types.md#331-a-bare-type-variable-is-an-inference-variable-with-a-name));
a parameter's type comes from usage.

A **self-call from one clause to a sibling clause is an ordinary call.** It
resolves (by arity, then — among same-arity clauses — by argument types,
§7.4.4) to a specific sibling clause and unifies the argument types with that
clause's parameter types, **exactly as a call to any other function does.**
There is no independence barrier: matching parameter identifiers across clauses
carry types across clauses precisely because a sibling self-call pins them
through the callee clause's signature, just as calling a separate function would.

```clojure
;; The 2-arg clause's self-call to the 3-arg clause pins p, rot : Int through
;; the 3-arg clause's inferred signature — exactly as calling a separate
;; function would. This MUST type-check.
(defn rp4
  ([p rot]     (let [q (rp4 p rot 0)] p))        ; => (Fn [Int Int] Int)
  ([p rot idx] (add-i64 p (add-i64 rot idx))))   ; => (Fn [Int Int Int] Int)
```

`add-i64` pins the 3-arg clause to `(Fn [Int Int Int] Int)`; the 2-arg clause's
`(rp4 p rot 0)` resolves to that clause and pins `p` and `rot` to `Int`. The
definition type-checks identically to the same logic written as two separate
mutually-recursive functions `rp4a`/`rp4b`.

A clause parameter is an **ambiguous-type compile-time error only when the
equivalent standalone function would also fail to infer it** — i.e. neither the
clause's own body nor any sibling self-call that reaches it pins the parameter's
type at a codegen-reaching position (genuine §5.1.1 / §3.11 ambiguity). A
parameter is **not** an error merely because a sibling clause was "not
consulted": no such barrier exists.

A clause left **genuinely polymorphic** — e.g. `([:a x] x)`, itself a valid
standalone function — is **admissible** in a multi-signature `defn`. The
separate-mutually-recursive-functions equivalence implies it directly, and
§5.1.2 constrains dispatch *ambiguity*, not the presence of polymorphism. Its
coexistence with a same-arity sibling is governed by the overlap rule above: it
is admitted when the two clauses' signatures **cannot** unify (both clauses
compile and dispatch), and is a dispatch-ambiguity error, reported at the
definition, when they **can** — the same rule that governs any two same-arity
clauses.

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

The `type_head` name is a **binder** (§5, *Declaration heads are binders*) — a **bare (unqualified)** symbol; a qualified **or dotted** head (`(deftype fmt/Point …)`, `(deftype (fmt/Pair a b) …)`, `(deftype A.B …)`) is a compile-time error (§5, *Binder positions*). The type parameters are binders on the same rule — `(deftype (Pair prim/a b) …)` is a **located** reject with the span on the parameter, not an incidental resolution failure. [S113] [S115]

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
- A constructor name is a **binder** (§5, *Declaration heads are binders*; user ruling 2026-07-19) — it mints a module-level callable, so it MUST be a **bare uppercase** symbol. A qualified **or dotted** spelling (`(deftype Shape (fmt/Circle …))`, `(deftype Shape (Shape.Circle …))`) is a compile-time error, with the diagnostic span on the constructor name: you can define a constructor only into the module that contains the `deftype`, never into another module. This holds in both constructor arms — the nullary bare-name arm and the parenthesized data-constructor arm. (Lowercase constructor names are separately rejected as ill-formed — a lowercase ctor would be callable but unmatchable, since a lowercase pattern symbol binds a variable, §6.2.4.) [S113]
- A **field name** is likewise a binder — it mints a module-level accessor `Type.field` (§5.2.6), so it MUST be a **bare** symbol; a qualified **or dotted** field name (`(deftype T [:Int fmt/r])`, `(deftype T [:Int a.r])`) is a compile-time error, span at the field name. [S113] [S115]

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
- Constructor names MUST be capitalized — a **bare uppercase** symbol; a lowercase constructor name is rejected as ill-formed, and a qualified **or dotted** spelling is a compile-time error (§5.2.2). [S115]
- Constructor tags are assigned sequentially starting from 0 in definition order.

## 5.3 Trait Declaration (`deftrait` / `deftrait-`) [Tested]

```ebnf
deftrait_form  = '(' ('deftrait' | 'deftrait-') trait_head docstring? method_sig+ ')'
trait_head     = name                         (* simple trait *)
               | '(' name type_var+ ')'       (* higher-kinded trait *)
method_sig     = required_method | default_method
required_method = '(' name docstring? '[' param* ']' type_expr ')'  (* param* — a return-type-dispatched method may take zero params, §7.1.1 *)
default_method  = '(' name docstring? '[' param+ ']' body ')'
param          = ':' type_expr symbol          (* typed parameter *)
               | symbol                        (* bare -- implementing type *)
type_expr      = 'self'                       (* implementing type *)
               | symbol                        (* named type or type var *)
               | '(' 'Fn' '[' type_expr* ']' type_expr ')'   (* function type *)
               | '(' name type_expr+ ')'       (* applied type *)
```

A trait declaration introduces a named interface with one or more method signatures. All methods use named parameters in brackets. Required methods end with a return type; default methods end with a body expression. The trait head (`name` in the grammar above) is a **binder** — a **bare (unqualified) uppercase symbol** (§5, *Declaration heads are binders*, and [§7.1](07-traits.md#71-trait-declaration)); a qualified **or dotted** head is a compile-time error (§5, *Binder positions*). [S113] [S115]

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

### 5.3.2 Higher-Kinded Traits [Tested+Neg tests/spec_07_traits::hkt_deftrait_declaration_with_type_constructor_parameter_succeeds, tests/spec_07_traits::deftrait_bare_return_convar_never_applied_rejected_neg, tests/spec_07_traits::deftrait_bare_arg_convar_never_applied_rejected_neg]

When the trait head includes type parameters, the trait operates on type constructors rather than concrete types.

```clojure
(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container"
    [:(Fn [a] b) f :(f a) x] (f b)))
```

- The type parameter `f` represents a type constructor (e.g., `Option`, `List`).
- Method signatures MAY use the type parameter applied to type variables: `(f a)`.
- HKT method parameters do not use bare names for `self`; instead, all parameters have explicit type annotations.
- **Kind is determined by usage.** A parenthesized head `(deftrait (X a) …)` is the higher-kinded form **only if** its head variable is **applied** (`(a b)`) somewhere in the method signatures. A parenthesized head whose variable is never applied is **malformed**; a conventional (kind-`*`) trait uses the bare-head form `(deftrait X …)` with `self`. See [§7.1](07-traits.md#71-trait-declaration) and [§7.2.1](07-traits.md#721-constructor-variables).

### 5.3.3 Trait Semantics [Tested tests/spec_05_definitions::deftrait_impl_and_dispatch, tests/spec_07_traits::trait_method_no_impl_then_recovery]

- A trait declaration introduces method names into scope. These names cannot be used until at least one implementation is provided. Each method-signature name is a **binder** (§5, *Declaration heads are binders*) — a **bare (unqualified)** symbol; a qualified **or dotted** method name (`(deftrait Foo (fmt/show [x] Int))`, `(deftrait Foo (Foo.show [x] Int))`) is a compile-time error (§5, *Binder positions*). [S113] [S115]
- Method signatures declare the type contract. Implementations MUST conform to the declared signature.
- Traits are the mechanism for operator overloading: `+`, `-`, `*`, `/` are methods of the `Num` trait; `=` is a method of `Eq`; `<`, `>`, `<=`, `>=` are methods of `Ord`.

## 5.4 Trait Implementation (`impl`) [Tested]

```ebnf
impl_form      = '(' 'impl' impl_head impl_target method_defn+ ')'
impl_head      = trait_name                       (* conventional trait — bare, as declared *)
               | '(' trait_name con_var ')'       (* higher-kinded trait head — echoed as declared *)
impl_target    = type_name                        (* conventional concrete:  Int *)
               | '(' type_name type_arg+ ')'      (* conventional applied:    (Option Int), (Option :Display a) *)
               | '(' trait_name con_target ')'    (* HK trait-constructor pairing: (Functor Option) *)
type_arg       = type_name                        (* concrete type or type var *)
               | colon_prefix symbol              (* inline constraint: :Display a *)
method_defn    = '(' 'defn' name params body ')'  (* follows defn syntax *)
```

A trait implementation provides method bodies for a specific type. Slot 1
**echoes the `deftrait` head as declared** — the bare trait name for a
conventional trait, the parenthesized `(Trait con_var)` head for a higher-kinded
trait — and slot 2 **names the target**: a **type** for a conventional trait
(`(impl Display Int …)`, `(impl Display (Option :Display a) …)`), a
**trait-constructor pairing** `(Trait Constructor)` for a higher-kinded trait
(`(impl (Functor f) (Functor Option) …)`). The authoritative grammar, examples,
and rationale live in [§7.3](07-traits.md#73-trait-implementation).

> **Kind-matching (settled).** The precise **impl-target kind-matching
> table** — exactly which targets are well-kinded for a given trait head, and
> which are rejected and with what diagnostic — is settled in
> [§7.3.5](07-traits.md#735-kind-checking-of-impl-targets): a conventional
> (kind-`*`) trait target MUST be a **type** (a bare/under-applied constructor
> is a kind-mismatch), and a higher-kinded trait target MUST be a bare
> constructor whose arity matches the con_var's usage-derived kind (a
> fully-applied type, a primitive, or a wrong-arity constructor is rejected).
> The `impl` *syntax* above (echo-the-head, slot-2 target shape) is likewise
> settled.

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

### 5.4.3 Polymorphic Implementation [S112 — pinned repro directed (plan/s112-0628-ic-wave.md §3.3a TB-24): the polymorphic/constrained impl target `(Option :Display a)` is a PRE-EXISTING wrong-reject on HEAD (`unknown type a` before the arity gate; owner /dev typecheck); the previous cite tests/spec_07_traits::polymorphic_impl_on_concrete_adt_instantiation exercises only the CONCRETE instantiation `(MyOpt Int)` — §5.4.2's cell, mis-pointed here; band corrected /qa 2026-07-18]

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

### 5.4.4 Higher-Kinded Implementation [Tested+Neg tests/spec_07_traits::hkt_impl_targets_bare_type_constructor_not_applied_form, tests/spec_07_traits::hkt_impl_on_user_well_kinded_adt_dispatches, tests/spec_07_traits::old_form_hkt_impl_bare_head_rejected_names_new_form_neg]

For HKT traits, the impl echoes the declared head `(Functor f)` in slot 1 and names a trait-constructor pairing `(Functor Option)` in slot 2 (the constructor named in the pairing is bare, never an applied type — see [§7.3.4](07-traits.md#734-higher-kinded-implementation)):

```clojure
(impl (Functor f) (Functor Option)
  (defn fmap [g x]
    (match x
      [None None
       (Some v) (Some (g v))])))
```

### 5.4.5 Implementation Semantics [Tested tests/spec_07_traits::user_trait_simple, tests/spec_07_traits::trait_method_no_impl_then_recovery]

- `impl` has no private variant. All trait implementations are visible wherever both the trait and type are visible — i.e., wherever both are reachable through the current module's transitive import closure. See [§5.11.1](#5111-impl-visibility--transitive-import-closure) for the full visibility rule and worked example, and [§7.11.1](07-traits.md#7111-impl-visibility--transitive-import-closure) for resolution-side consequences.
- Method definitions within `impl` follow `defn` syntax but MUST NOT include docstrings (the docstring comes from the trait declaration).
- The method parameter count and types MUST conform to the trait's declared signature.
- Method bodies are type-checked against the instantiated trait signature.
- **Redefinition is hot-reload.** [S115] Re-entering an `impl` for a (trait, target-type) pair that already has an implementation in a live session **replaces** the previous implementation: subsequent method dispatch (§7.4) for that (trait, type) pair uses the **new** method bodies, exactly as re-entering a `defn` hot-reloads a function definition (redefinition runtime semantics — dependent recompilation, broken symbols, the frozen world — are `repl/spec.md` §18; source round-trip is `repl/spec.md` §15.6). The re-`impl` carries the same-type constraint that governs `defn` redefinition — the new method bodies MUST conform to the trait's declared signature for the target type (the conformance rules above), so a re-`impl` whose methods do not type-check against that signature is rejected exactly as any other non-conforming impl; a conforming re-`impl` leaves each method's compiled signature unchanged and is therefore signature-preserving (`repl/spec.md` §18.1). An implementation MUST NOT silently ignore a re-`impl` — accepting the form and printing the ordinary confirmation while continuing to dispatch to the **first** implementation is a defect.

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

- The macro name is a **binder** (§5, *Declaration heads are binders*) — a **bare (unqualified)** symbol; a qualified **or dotted** head (`(defmacro fmt/when …)`, `(defmacro a.when …)`) is a compile-time error (§5, *Binder positions*). [S113] [S115]
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
- The `name` is a **binder** (§5, *Declaration heads are binders*) — a **bare (unqualified)** symbol; a qualified **or dotted** head (`(const fmt/PI 3.14)`, `(const a.PI 3.14)`) is a compile-time error (§5, *Binder positions*). [S115] Because `const` expands to a `defmacro`, the binder rule bites on that expansion, but the diagnostic span MUST point at the written `const` head, not the synthesized form (§5, macro-surface note). [S113]
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
- The `name` is a **binder** (§5, *Declaration heads are binders*) — a **bare (unqualified)** symbol; a qualified **or dotted** head (`(def fmt/x 1)`, `(def a.x 1)`) is a compile-time error (§5, *Binder positions*). [S115] Because `def` expands to a `defn`/`defmacro` pair, the binder rule bites on that expansion, but the diagnostic span MUST point at the written `def` head, not the synthesized form (§5, macro-surface note). [S113]
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

- The platform name MUST be a **simple symbol** — not a string literal, and **not qualified, not dotted** (the same constraint `mod` places on a module name, §5.8). The name is a binder that composes the synthetic module path `platform.<name>` and the DLL search path, so a qualified or dotted spelling (`(platform foo/stdio)`, `(platform std.io)`) would mint a bogus module path and is a compile-time error, span at the platform name. This is the module-phase analogue of the general binder rule (§5, *Binder positions*): you name a platform to load, you do not define a name into another module. [S113]
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

**A trait *method* is a sufficient trait-side entry point (D2, user ruling 2026-07-19). [S113]** The "reach `Trait`" leg above is satisfied by reaching **any of the trait's methods**: importing a method of `Trait` directly (`(import [home [m]])`, without importing the `Trait` name) brings `Trait`'s canonical home into N's import closure and suffices to **dispatch** `m` — the trait name need not separately be in scope. This governs dispatch only; **declaring** an impl of `Trait` still requires the trait head in scope (§7.3). See [§7.11.2](07-traits.md#7112-method-import-dispatch--a-method-reference-suffices) for the full ruling and its edge cells.

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
