> [REPL specification index](index.md)

## 1. Display Format

### 1.1 Universal Output Format [Tested+Neg tests/repl_introspection::bare_primitive_type_int_displays_type_info, tests/repl_introspection::display_defn_with_docstring_uses_dash_separator]

All REPL output uses a unified format that mirrors Cranelisp type annotation syntax. **Colour styling of this format is governed by §10.3, the single token/element styling authority** (the `:Type` annotation is R4 cyan, a literal value R2/R3, a `module/` name prefix R7 dim, the `; classification` comment R6 dim). The primary line is always:

```
:Type {value|name} ; {classification} - {docstring first line}
```

Where:
- `:Type` — the fully-qualified type (per §1.4), always present
- `{value|name}` — either a runtime value (for expression results) or a fully-qualified name (for definitions and lookups)
- `; {classification} - {docstring}` — optional comment suffix. The classification is the name of the defining special form (`defn`, `deftype`, `deftrait`, `defmacro`, `special form`, `impl`) or the symbol-class word `primitive` (used for builtins in the `primitives` module — see §4.1.7). The docstring is the first line of the symbol's documentation. If the symbol has no docstring, only the classification appears. If there is no classification (literal values), the comment is omitted entirely.

Builtins use the same dash form: `; {classification} - {docstring}` with classification `primitive` (e.g., `; primitive - Add`). The classification word `primitive` (rather than `defn`) is what distinguishes the host-implemented builtin from a user-defined function; the docstring suffix grammar is identical to `defn`/`deftype`/etc.

**Related symbols** appear as comment lines below the primary line. Each section names a relationship using language syntax, followed by unqualified symbol names (bare names, since these are in-scope symbols):

```
; {relationship}:
;  {symbol} {symbol} ...
```

Related symbol lists use the **same normative layout algorithm** as `/list` categories (§3.3 rules L0–L4); the layout MUST be byte-for-byte identical to `/list` for the same name set. [Tested repl/spec.md→tests/repl_introspection.rs::layout_cross_command_list_exports_byte_identical] Within each section, locally-defined symbols appear before imported symbols.

**Examples:**

```
user> 42
:primitives/Int 42

user> double
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2

user> Display
:core.str/Display ; deftrait - Format as string
; defn:
;  show
; impl:
;  Point
;  Bool Float Int List Vec

user> Color
:user/Color ; deftype
; match:
;  Red Green Blue

user> if
:(Fn [primitives/Bool a a] a) if ; special form - Conditional branch

user> +
:(Fn [:core.num/Num a :a] a) core.num/Num.+ ; deftrait - Addition operator
```

Not every symbol class has related symbols. Functions, constructors, literals, and primitives have only the primary line (plus optional docstring). Types, traits, macros, and modules have related symbol sections.

For a `defmacro`, the `:Type` position is its **compile-time transformation
signature**, not a runtime value type and not the type of any eventual expanded
expression. Each fixed macro argument contributes `macros/Sexp`; a rest binding
contributes a final `(macros/SList macros/Sexp)` parameter; every clause returns
`macros/Sexp`. Destructuring and variadic call syntax that cannot be expressed by
an ordinary `Fn` type is retained in a `; pattern:` metadata line (§4.1.6).

**The one canonical envelope — `:Type {subject} ; {metadata}` (S109).** This universal format is not
merely a shared *convention*; it is a **single canonical envelope** that every "what is this symbol,
and what is its type" surface renders through — **bare-symbol lookup** (§4.1), **`/sig`** (§3.8),
**`/info`** (§3.6), and eligible **`/search` result rows** (§17.19.2). These surfaces differ **only**
in verbosity — which drawers they expand (a `/search` row adds an originating-module column and
an import-how-to; `/info` adds the source form and code-size drawer; bare lookup and `/sig` show
the primary line plus the classification/related-symbol drawers) — **never** in the shape of the
`:Type {subject} ; {metadata}` primary line itself. They are **one envelope constructor with
different drawer sets**, not four independently-formatted renderers (FIXME 0572). This is the
experience contract; the mechanism is the shared envelope constructor of the E4 styling seam
(`design/arch/repl-styling-seam.md` §4 — "one envelope constructor that both route through"), so
the `:`-prefix, spacing, and metadata grammar are single-sourced. A `/search` row that grows its
own `name :: (Fn …)` primary-line shape is a conformance defect against this envelope, not a
stylistic variation. Macro declarations are outside `/search` rather than being forced into a
typed envelope (§17.19.2a). [S109]

### 1.2 Expression Results [S122]

An expression evaluation MUST display the result in the format:

```
:QualifiedType value
```

The type prefix is always fully qualified. The value portion uses the **canonical value display format** defined in [spec §12.9](../../spec/12-runtime.md#129-value-display-format). This includes elision rules for large values — the REPL MUST apply the same elision thresholds as all other contexts that use the canonical format.

Examples:

| Example | Test |
|---|---|
| `:primitives/Int 3` | [Tested tests/repl_introspection::display_int_result] |
| `:primitives/Bool true` | [Tested tests/repl_introspection::display_bool_true] |
| `:primitives/Float 3.14` | [Tested tests/repl_introspection::display_float_result] |
| `:user/Color Color.Red` | [Tested tests/repl_introspection::display_int_result] |
| `:(user/Option primitives/Int) (Option.Some 42)` | [Tested tests/repl_introspection::display_int_result] |
| `:(Fn [a] a) <closure>` (anonymous — no bound name) | [Tested tests/repl_introspection::display_int_result] |
| `:(Fn [(primitives/Vec a)] primitives/Int) primitives/vec-len` (name-bearing reference — a bare/qualified symbol resolving to a named function shows the FQ name, never `<closure>`; §1.5, 0572) | [Tested tests/repl_introspection::named_function_value_displays_fq_name_not_closure, tests/repl_introspection::fq_bare_display_parity_with_imported_introspection] |

**Ring 0**: `primitives/Int`, `primitives/Bool`, `primitives/Float`, nullary ADT constructors, non-capturing function values.
**Ring 1**: `primitives/String`, data ADT constructors, closures, `Vec`, `List`.

**Ring 4**: `IO` expressions are executed, not displayed as values (§1.2.1).

**Ring 4**: `Trace` — displayed using the standard ADT format per [spec §12.9](../../spec/12-runtime.md#129-value-display-format). The REPL does NOT auto-format trace trees — the raw ADT value is shown. Users who want a human-readable indented call tree SHOULD import `core.trace` and call `trace-show-tree`. [R4 S20]

### 1.2.1 IO Expression Results [Tested+Neg tests/spec_10_io.rs::repl_pure_int_result_prints_io_notice_then_payload, tests/spec_10_io.rs::repl_pure_string_result_prints_io_notice_then_payload, tests/spec_10_io.rs::repl_bind_pure_lambda_result_prints_io_notice_then_payload_without_double_free, tests/spec_10_io.rs::repl_io_notice_precedes_effect_output_neg_not_on_pure_defn_or_lookup_turns, tests/output_equivalence::output_equiv_single_print]

An expression whose type is `IO a` ([spec §10.1](../../spec/10-io.md#101-io-type)) is an IO action. The REPL MUST execute it automatically as part of evaluating the expression, and MUST present it in this order:

1. The notice line `Executing IO…`, printed before the action starts executing through the trampoline and platform.
2. The platform output the action produces.
3. The payload the action returns, in the §1.2 format under the payload's own fully-qualified type `a` — not `IO a`.

An expression whose type is not `IO` MUST NOT produce the notice. The notice is REPL output: batch output (§0.2, §0.2.1) never contains it.

```
user> (Pure 42)
Executing IO…
:primitives/Int 42

user> (print "hello")
Executing IO…
hello
:primitives/Int 0

user> (+ 1 2)
:primitives/Int 3
```

### 1.3 Definition Results [Tested]

When the user enters a definition form, the REPL confirms the definition using the universal format (§1.1). The response follows the same per-class rules as bare symbol lookup (§4.1) — a definition is immediately followed by its lookup display.

```
user> (defn double "Multiply by 2" [x] (* x 2))
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2

user> (deftype Color Red Green Blue)
:user/Color ; deftype
; match:
;  Red Green Blue

user> (deftrait Sizeable (size [x] Int))
:user/Sizeable ; deftrait
; defn:
;  size

user> (impl Sizeable Circle (defn size [c] ...))
impl user/Sizeable for user/Circle

user> (defmacro n [] (macros/SexpInt 42))
:(Fn [] macros/Sexp) user/n ; defmacro
```

**Canonical-home qualification.** In `impl Trait for Type`, the trait name and the target type MUST each be qualified by **its own canonical home module** — the module that defines it — not by the module in which the `impl` is written. In the example above both `Sizeable` and `Circle` are user-defined, so both read `user/`. When either name belongs to another module the qualifier follows it there: an impl of the prelude trait `Display` for a user type reads `impl text.display/Display for user/Widget`, and an impl of a user trait for a primitive reads `impl user/Foo for primitives/Int`. Stamping the writing module on a name whose home is elsewhere (`impl user/Display for user/Int`) is a defect — the qualifier is a fully-qualified name and MUST name the real home (the self-documenting-REPL principle; resolve each name's home once per Principle 24). [S113]

A function definition MUST NOT display `<closure>` — the user defined a *named* function, not an anonymous closure. `<closure>` is reserved for anonymous function *values* (§1.2, §1.5).

| Requirement | Test |
|---|---|
| defn shows type + qualified name | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| polymorphic defn shows type vars | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| deftype shows qualified type name | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| deftrait shows trait name | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| impl shows `impl Trait for Type` | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| impl qualifies trait + type by canonical home, not the writing module | [S113] |
| constrained fn shows inline constraints | [Tested tests/repl_introspection::defn_display_zero_arg_thunk] |
| overloaded fn shows all variants | [Tested tests/repl_introspection::display_overloaded_fn_shows_all_variants] |

**Ring 0**: function definitions, type definitions.
**Ring 2**: trait declarations, trait implementations, constrained functions.
**Ring 3**: macros.

### 1.4 Type Display [Tested]

Types MUST be displayed using Cranelisp type notation with fully-qualified names:

| Type | Display | Test |
|---|---|---|
| Primitive | `primitives/Int`, `primitives/Bool`, `primitives/Float`, `primitives/String` | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| Function | `(Fn [ParamType1 ParamType2] ReturnType)` | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| ADT (no args) | `user/Color` | [Tested tests/repl_negative::display_neg_type_always_qualified] | <!-- doc-check: literal reason="Illustrative language symbols" -->
| ADT (with args) | `(user/Option primitives/Int)` | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| Type variable | lowercase letter: `a`, `b`, `c`, ... | [Tested tests/repl_negative::display_neg_type_always_qualified] |
| Constrained variable | `:num.num/Num a` | [Tested+Neg tests/repl_introspection::constraint_trait_name_displays_canonical_home_neg_no_bare_trait, tests/repl_introspection::constraint_display_is_identical_across_definition_sig_and_bare_lookup] |

Type names MUST always be fully qualified with their module path. Type variables are bare lowercase — they are not module-scoped.

Polymorphic type schemes MUST display quantified variables as consecutive lowercase letters starting from `a`. Constraints MUST appear inline on first occurrence of the constrained variable.

```
:(Fn [a] a) user/id
:(Fn [:num.num/Num a :a] a) num.num/+
```

### 1.5 Value Display

Values are runtime results and have no module scope. They are displayed bare.

| Type | Display | Ring | Test |
|---|---|---|---|
| `Int` | decimal integer (e.g., `42`, `-7`) | 0 | [Tested tests/repl_introspection::display_int_result] |
| `Bool` | `true` or `false` | 0 | [Tested tests/repl_introspection::display_bool_true] |
| `Float` | decimal float (e.g., `3.14`) | 0 | [Tested tests/repl_introspection::display_float_result] |
| `String` | `"contents"` with escapes | 1 | [Tested tests/display_exact::display_exact_primitive_value_lines] |
| Nullary constructor | `Type.Ctor` (e.g., `Color.Red`, `Option.None`) | 0 | [Tested tests/display_exact::display_exact_nullary_and_single_level_adt_value_lines] |
| Data constructor (multi-ctor) | `(Type.Ctor field1 field2 ...)` (e.g., `(Option.Some 42)`) | 1 | [Tested tests/repl_introspection::data_constructor_applied_dot_notation_display] |
| Data constructor (single-ctor, name matches type) | `(Ctor field1 field2 ...)` (e.g., `(Point 3 4)`) | 1 | [Tested+Neg tests/repl_introspection::data_constructor_product_no_dot_notation_display] |

| Name-bearing function reference | its **fully-qualified name** (e.g. `primitives/vec-len`, `user/double`) — only when the *displayed expression is itself a name-bearing reference* (a bare/qualified symbol resolving to a named function); never `<closure>` | 1 | [Tested tests/repl_introspection::named_function_value_displays_fq_name_not_closure, tests/repl_introspection::fq_bare_display_parity_with_imported_introspection] | <!-- doc-check: literal reason="Illustrative language symbols" -->
| Function value with no recoverable name | `<closure>` — a literal `(fn …)`, a captured closure, or a named function that has passed through computation and lost its binding (`(id double)`, `(let [f double] f)`) | 1 | [Tested tests/repl_introspection::closure_value_display_shows_closure_token] |
| Vec | `[elem1 elem2 ...]` (empty: `[]`) | 1 | [Tested tests/display_exact::display_exact_vec_value_lines, tests/repl_introspection::vec_value_display_shows_element_content] |
| List | generic ADT recursive form (e.g., `(List.Cons 1 (List.Cons 2 List.Nil))`; empty: `List.Nil`) | 1 | [Tested tests/repl_introspection::display_user_list_value_shows_elements_and_nil, tests/display_exact::display_exact_user_list_recursive_form_whole_line] |
| Seq | generic ADT recursive form (e.g., `(Seq.SeqCons h <closure>)`); REPL MUST NOT force-evaluate the lazy tail | 2 | [Tested tests/repl_introspection::display_infinite_seq_value_does_not_hang] |

`Vec` is a compiler-seeded primitive type, so the REPL knows to render it as `[elem1 elem2 ...]`. `List` and `Seq` are stdlib types defined via `deftype`; the REPL renders them through the generic ADT recursive formatter (Type.Constructor + recursive field formatting). The MUST requirement for `Seq` is termination: the REPL displays the constructor and field shape without forcing the lazy tail thunk, so an infinite sequence does not hang the prompt.

**A name-bearing reference carries its qualified name; a value that lost its binding shows `<closure>` (S109 — 0572).**
The qualified-name rule applies to a **name-bearing reference expression** — a bare or qualified
symbol that resolves to a named function, evaluated as a value (e.g. entering `primitives/vec-len`
or `user/double` bare at the prompt). When the *displayed expression is itself* such a reference, the <!-- doc-check: literal reason="Illustrative language symbols" -->
value slot MUST show the value's **fully-qualified name** (`primitives/vec-len`), in the same
qualified form every other name-bearing display uses (§1.4, the self-documenting-REPL rule that names
are always fully qualified). The opaque token `<closure>` is a **placeholder for the absence of a
*recoverable* name**, and it is **correct — required** — for a function value that has no runtime name
identity: a literal `(fn [x] …)`, a captured closure, or a **named function that has passed through
computation and lost its binding** (`(id double)`, `(let [f double] f)` — the value genuinely has no
recoverable name, so `<closure>` is the honest display). The distinction is about the *displayed
expression*, not the value's origin: a name-bearing reference shows the name; a value that arrived by
computation shows `<closure>`. This is the value-display facet of the 0572 unification — a bare-symbol
value lookup and a `/search`/`/info` row of the same function agree on the qualified name because they
render through the one canonical envelope (§1.1). [Tested tests/repl_introspection::named_function_value_displays_fq_name_not_closure, tests/repl_introspection::fq_bare_display_parity_with_imported_introspection] [S109]

> **Aspirational** (not currently required): A future revision MAY render `List` and `Seq` in surface form, as `(list elem1 elem2 ...)` and `(seq elem1 elem2 ...)`. The render never forces a lazy `Seq` tail: it shows the already-evaluated elements and writes `+more` in place of the first unforced tail (`(seq elem1 elem2 ... +more)`), so the `Seq` termination MUST above still holds. The compiler recognises the built-in `List` and `Seq` internally; the language has no render annotation for types to opt in with. No such mechanism exists today, so the generic ADT form is normative. These forms become MUST only once the mechanism ([display protocol](../../design/arch/display-protocol.md)) lands; the obligation is [FIXME 0050](../../design/arch/fixmes/0050-promote-list-seq-pretty-printer-aspirational.md).


ADT fields MUST be recursively formatted according to this table.

**Representation-flattening is invisible to display (R5).** A single-constructor ADT whose
sole field is a scalar (`Int`, `Bool`, `Float`, or another such value) is **value-representation
flattened** by the compiler — the value is stored as a bare unboxed word, with no heap object
or tag word. This is a codegen optimisation (`design/arch/ownership-inference.md` §6.3 R5); it
MUST have **no effect on display**. Such a value MUST render as the ordinary single-ctor
constructor form `(Ctor value)` — identical to its non-flattened sibling — with the scalar
field formatted per its own row above. The display MUST NOT leak the flattened representation
(a raw `<tag:N>` sentinel is a non-conformance) and MUST NOT crash (a `Float` field's bit
pattern MUST NOT be dereferenced as a pointer). A flattened ADT nested as a field of an outer
ADT MUST likewise recurse to its constructor form.

| Value | Display | Ring | Test |
|---|---|---|---|
| Single-ctor single-scalar-field ADT (R5-flattened), `Int` field, e.g. `(Box 99)` | `(Box 99)` — never `<tag:99>` | 1 | [Tested tests/display_exact.rs::display_r5_value_layout_int_shows_constructor_form] |
| … `Bool` field, e.g. `(B true)` | `(B true)` — never `<tag:1>` | 1 | [Tested tests/display_exact.rs::display_r5_value_layout_bool_shows_constructor_form] |
| … `Float` field, e.g. `(F 3.14)` | `(F 3.14)` — MUST NOT crash | 1 | [Tested tests/display_exact.rs::display_r5_value_layout_float_does_not_crash] |
| R5-flattened ADT nested as a field of an outer ADT | recurses to `(Ctor value)`, e.g. `(Wrap (Box 5) 7)` | 1 | [Tested tests/display_exact.rs::display_r5_value_layout_nested_field_shows_constructor_form] |

Value semantics (construct / match / extract) are unaffected by flattening and were always
correct — this note pins the **display** invariant so the representation stays invisible
[Tested tests/display_exact.rs::r5_value_layout_construct_match_extract_is_sound].

### 1.5.1 Bare Polymorphic Values — Type Display via Introspection [Tested+Neg tests/repl_introspection::prelude_option_none_value_display_neg_definition_metadata]

A **result-only-polymorphic value** is a value whose finalised type is polymorphic with no concrete instantiation forced by the surrounding context — e.g. a bare `None` (type `∀a. (Option a)`) or a bare empty literal `[]` (type `∀a. (Vec a)`) entered alone at the prompt. Such a value has **no concrete runtime representation** to show: under the slot⟺concrete model it is *slot-less* (`UserFnState::Polymorphic`) — it has no GOT slot and is not compiled as a runtime value.

| Requirement | Test |
|---|---|
| A bare/unpinned polymorphic value entered at the REPL MUST display its **polymorphic type** in `:Type value` form — fully-qualified type, constructor/value form. It MUST NEVER be an opaque error. | [Tested tests/repl_introspection::prelude_option_none_value_display_neg_definition_metadata, tests/repl_introspection::display_empty_vec_value] |
| Bare `None` MUST display `:(prelude/Option a) Option.None` form — the `Option.None` value form prefixed by the polymorphic `(…/Option a)` type. | [Tested tests/repl_introspection::prelude_option_none_value_display_neg_definition_metadata] |
| Bare `[]` MUST display the `(primitives/Vec a)` type prefix and the `[]` value form. | [Tested tests/repl_introspection::display_empty_vec_value] |
| The display MUST NOT render the symbol's *definition* drawer (e.g. `; deftype`, a module-qualified constructor path `fn.option/…`) — this is a value-display, not a definition lookup. | [Tested tests/repl_introspection::prelude_option_none_value_display_neg_definition_metadata] |

This is the **self-documenting-REPL principle applied to polymorphic values** (root `CLAUDE.md` §"Design Principles": "No valid language construct should produce an opaque error"). Because there is no concrete runtime value to show, the useful feedback the REPL gives back is the **type** — read from the symbol-table scheme via introspection — in the same `:Type value` notation every other result uses.

**Served from introspection, never from a slot.** The display MUST be served by reading the polymorphic scheme from the symbol table (introspection over the type), NOT by compiling, slotting, or evaluating the value to a concrete runtime representation. This is the architectural reason the disposition works for a slot-less `UserFnState::Polymorphic` def: a result-only-polymorphic value has no GOT slot and never reaches codegen, so the REPL cannot read a runtime value — it reads the *scheme* instead and renders the polymorphic type. An implementation that tries to compile/slot the bare value to display it would either fail (no slot) or force a spurious concretisation; the conforming path is type-display-by-introspection.

**Distinct from the §3.11 codegen-forced ambiguity error.** The language spec (`spec/03-types.md` §3.11) rejects an *ambiguous* polymorphic type — an unconstrained type variable that remains after inference — as a **type error**. That rejection applies only to a polymorphic value in a position that **actually reaches codegen** and must be monomorphised (e.g. a top-level value expression whose concrete instance the program demands but cannot determine). It does **not** apply to this REPL bare-display path: displaying a bare `None`/`[]` is pure introspection over the symbol-table scheme and never requires the value to have a GOT slot or to be compiled. The two dispositions are complementary, not contradictory — §3.11 governs *codegen* (where a residual `Type::Var` is a bug); §1.5.1 governs *REPL display* (where a residual `Type::Var` is exactly the useful feedback to show).
