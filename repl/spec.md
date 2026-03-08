# REPL Experience Specification

Normative specification for the Cranelisp REPL user experience. A conforming REPL MUST satisfy all requirements tagged with the current ring or earlier.

While called repl, the repl experience encompasses the entire user experience from invoking the repl as well as its associated CLI invocation modes, exit codes, batch output format, and cache lifecycle.

<!-- FIXME(/repl): Specify CLI invocation modes (--run, --version, --help) -->

## Design Principle

> **The REPL reinforces the syntax of the language.** Every output teaches the user how to write Cranelisp.

Output uses the `:Type value` format — the same colon-prefixed type annotation syntax used in the language itself. Names are always fully qualified to teach the module system. Constructors use `Type.Constructor` dot notation (valid input syntax per §1.4.4 of the language spec).

## 1. Display Format

### 1.1 Output Categories [Tested]
<!-- All table rows below have [Tested] annotations -->

<!-- RESOLVED: Sprint 9 — bare type name lookup implemented. Type::from_name() check
     added to special_form_feedback() before symbol table lookup. Int, Bool, Float, String
     now produce `:primitives/{name}` output. Tests: e2e.rs::e2e_s1_1_bare_type_int,
     e2e_s1_1_bare_type_bool, e2e_s1_1_bare_type_float, e2e_s1_1_bare_type_string. -->

REPL output falls into three categories. The format mirrors Cranelisp type annotation syntax (`:Type expr`).

| Input kind | Format | Example | Test |
|---|---|---|---|
| Expression result | `:QualifiedType value` | `:primitives/Int 3` | [Tested tests/e2e::e2e_s1_2_int_display_qualified] |
| Function definition | `:TypeScheme qualified-name` | `:(Fn [a] primitives/Int) user/foo` | [Tested tests/e2e::e2e_s1_3_defn_shows_qualified_name] |
| Type definition | `:qualified/TypeName` | `:user/Color` | [Tested tests/e2e::e2e_s1_1_bare_type_user_defined] |
| Symbol lookup | `:TypeScheme qualified-name` | `:(Fn [a] a) user/id` | [Tested tests/e2e::e2e_s4_1_bare_symbol_lookup] |
| Constructor lookup | `:QualifiedType Type.Constructor` | `:user/Color user/Color.Red` | [Tested tests/e2e::e2e_s1_1_constructor_lookup] |
| Special form lookup | `:signature name` | `:(Fn [primitives/Bool a a] a) if` | [Tested tests/e2e::e2e_s4_2_special_form_feedback] |

### 1.2 Expression Results [Tested]

An expression evaluation MUST display the result in the format:

```
:QualifiedType value
```

Values are runtime results — they have no module scope. The type is always fully qualified.

Examples:

| Example | Test |
|---|---|
| `:primitives/Int 3` | [Tested tests/repl_experience::display_int_result] |
| `:primitives/Bool true` | [Tested tests/repl_experience::display_bool_true] |
| `:primitives/Float 3.14` | [Tested tests/repl_experience::display_float_result] |
| `:user/Color Color.Red` | [Tested tests/repl_experience::display_enum_adt] |
| `:(user/Option primitives/Int) (Option.Some 42)` | [Tested tests/repl_experience::r1_display_sum_adt_some] |
| `:(Fn [a] a) <closure>` | [Tested tests/repl_experience::r1_display_closure_format] |

**Ring 0**: `primitives/Int`, `primitives/Bool`, `primitives/Float`, nullary ADT constructors, non-capturing function values.
**Ring 1**: `primitives/String`, data ADT constructors, closures, `Vec`, `List`.


**Ring 4**: `IO` (trampoline executes; inner value displayed as `:primitives/IO inner_value`).

### 1.3 Definition Results [Tested]

A function definition MUST display its inferred type scheme and fully-qualified name. It MUST NOT display `<closure>` — the user defined a *named* function, not an anonymous closure:

```
:(Fn [a] a) user/id
:(Fn [primitives/Int] primitives/Int) user/double
```

Note: `<closure>` is reserved for anonymous function *values* (§1.2, §1.5). When the user writes `(defn double [x] (* x 2))`, the response shows the name `user/double`. Only `(fn [x] (* x 2))` evaluated as an expression produces `<closure>`.

| Requirement | Test |
|---|---|
| defn shows type + qualified name | [Tested tests/repl_experience::defn_reports_type_and_name] |
| polymorphic defn shows type vars | [Tested tests/repl_experience::defn_polymorphic_type_vars] |
| deftype shows qualified type name | [Tested tests/repl_experience::deftype_reports_adt_type] |
| deftrait shows trait name | [Tested tests/ring2::repl_deftrait_display] |
| impl shows `impl Trait for Type` | [Tested tests/ring2::repl_impl_display] |
| constrained fn shows inline constraints | [Tested tests/ring2::repl_constrained_fn_display] |
| overloaded fn shows all variants | [R3 S8] |

A type definition MUST display the fully-qualified type name:

```
:user/Color
:user/Option
```

A trait declaration MUST display the trait name:

```
:user/Sizeable
```

A trait implementation MUST confirm the trait and type:

```
impl user/Sizeable for user/Circle
```

A constrained function definition MUST display its constraints inline on the first occurrence of each constrained type variable:

```
:(Fn [:core.numerics/Num a :a] a) user/double
```

An overloaded function definition MUST display all variant signatures.

**Ring 0**: function definitions, type definitions.
**Ring 2**: trait declarations, trait implementations, constrained functions, overloaded functions.
**Ring 3**: macros.

### 1.4 Type Display [Tested]

Types MUST be displayed using Cranelisp type notation with fully-qualified names:

| Type | Display | Test |
|---|---|---|
| Primitive | `primitives/Int`, `primitives/Bool`, `primitives/Float`, `primitives/String` | [Tested tests/e2e::e2e_s1_2_int_display_qualified] |
| Function | `(Fn [ParamType1 ParamType2] ReturnType)` | [Tested tests/repl_experience::display_function_type] |
| ADT (no args) | `user/Color` | [Tested tests/e2e::e2e_s1_3_deftype_shows_qualified_name] |
| ADT (with args) | `(user/Option primitives/Int)` | [Tested tests/repl_experience::r1_display_polymorphic_adt_type] |
| Type variable | lowercase letter: `a`, `b`, `c`, ... | [Tested tests/repl_experience::r2a_polymorphic_fn_normalized_vars] |
| Constrained variable | `:core.numerics/Num a` | [Tested tests/ring2::repl_constrained_fn_display] |

Type names MUST always be fully qualified with their module path. Type variables are bare lowercase — they are not module-scoped.

Polymorphic type schemes MUST display quantified variables as consecutive lowercase letters starting from `a`. Constraints MUST appear inline on first occurrence of the constrained variable.

```
:(Fn [a] a) user/id
:(Fn [:core.numerics/Num a :a] a) core.numerics/+
```

### 1.5 Value Display [R3 S8]

Values are runtime results and have no module scope. They are displayed bare.

| Type | Display | Ring | Test |
|---|---|---|---|
| `Int` | decimal integer (e.g., `42`, `-7`) | 0 | [Tested tests/repl_experience::display_int_result] |
| `Bool` | `true` or `false` | 0 | [Tested tests/repl_experience::r0_bool_displays_as_word] |
| `Float` | decimal float (e.g., `3.14`) | 0 | [Tested tests/repl_experience::display_float_result] |
| `String` | `"contents"` with escapes | 1 | [Tested tests/repl_experience::r1_display_string_literal] |
| Nullary constructor | `Type.Ctor` (e.g., `Color.Red`, `Option.None`) | 0 | [Tested tests/e2e::e2e_s1_5_nullary_ctor_dot_notation] |
| Data constructor | `(Type.Ctor field1 field2 ...)` (e.g., `(Option.Some 42)`) | 1 | [Tested tests/e2e::e2e_s1_5_data_ctor_dot_notation] |
| Closure | `<closure>` | 1 | [Tested tests/repl_experience::r1_display_closure_format] |
| Vec | `[elem1 elem2 ...]` (empty: `[]`) | 1 | [Tested tests/repl_experience::r1_display_vec_int] |
| List | `(list elem1 elem2 ...)` (empty: `List.Nil`) | 1 | [R3 S8] |
| Seq | `(seq elem1 elem2 ... +more)` (forces up to 20) | 2 | [R3 S8] |

ADT fields MUST be recursively formatted according to this table.

## 2. Prompt [Tested]

### 2.1 Primary Prompt [Tested tests/e2e::e2e_s2_1_prompt_format]

The primary prompt MUST display:

```
{compile_ms}+{eval_ms}ms; {module}>
```

Where:
- `compile_ms` — JIT compilation time of the previous expression (integer milliseconds)
- `eval_ms` — evaluation time of the previous expression (integer milliseconds)
- `module` — current module name (default: `user`)

On startup (before any expression), the timing SHOULD be `0+0ms`.

**Ring 0**: timing and prompt display.
**Ring 2**: module name changes when `/mod` switches namespace.

### 2.2 Continuation Prompt [Tested tests/e2e::e2e_s2_2_continuation_prompt]

When multi-line input is in progress (unmatched parentheses or brackets), the continuation prompt MUST be:

```
{spaces}...
```

Where `{spaces}` aligns the `...` with the start of user input on the primary prompt line.

### 2.3 Empty and Comment-Only Input [Tested tests/repl_experience::empty_input_is_silent]

Blank lines (empty or whitespace-only) MUST silently re-prompt with no output. The REPL MUST NOT produce an error, evaluation result, or any visible output — it simply presents the next prompt.

Comment-only lines (lines where all non-whitespace content begins with `;`) MUST silently re-prompt with no output. Since `;` is the Cranelisp comment character, a line consisting entirely of comments carries no evaluable content.

This enables:
- Natural use of blank lines and comments as formatting in demo scripts and piped input
- Interactive users pressing Enter on an empty line without seeing an error
- Pasting code blocks that contain comment lines without spurious error output

**Ring 0**: empty and comment-only input handling.

## 3. Slash Commands

Slash commands provide introspection and navigation. All commands start with `/` and are NOT expressions — they are REPL-only features.

### 3.1 Command Inventory [R3 S10]

| Command | Aliases | Description | Ring | Test |
|---|---|---|---|---|
| `/help` | `/h` | Show available commands and usage | 0 | [Tested tests/e2e::e2e_s3_1_help] |
| `/sig <name>` | `/s` | Show signature with typed parameters | 0 | [Tested tests/e2e::e2e_s3_1_sig] |
| `/doc <name>` | `/d` | Show docstring | 0 | [R4 S10] |
| `/type <expr>` | `/t` | Show type without evaluating | 0 | [Tested tests/e2e::e2e_s3_1_type] |
| `/info <name>` | `/i` | Full details: type, classification, code size, compile time | 0 | [Tested tests/e2e::e2e_s3_4_info] |
| `/source <name>` | — | Show original source text | 0 | [R4 S10] |
| `/sexp <name>` | — | Show parsed S-expression | 0 | [R4 S10] |
| `/ast <name>` | — | Show AST | 0 | [R4 S10] |
| `/clif <name>` | — | Show Cranelift IR | 0 | [R4 S10] |
| `/disasm <name>` | — | Show disassembled native code | 0 | [R4 S10] |
| `/list [filter]` | `/l` | List symbols in current module | 0 | [Tested tests/e2e::e2e_s3_3_list] |
| `/time <expr>` | — | Evaluate with timing breakdown | 0 | [Tested tests/e2e::e2e_s3_1_time] |
| `/expand <form>` | `/e` | Macro-expand a form | 3 | [R3 S11 — tests/ring3_repl::r3_expand_single_macro IGNORED] |
| `/mod [name]` | — | Switch module namespace | 2 | [R4 S10] |
| `/imports` | — | Show imports in current module with source | 2 | [R3 S11 — tests/ring3_repl::r3_imports_empty IGNORED] |
| `/reload [name]` | `/r` | Reload module from file | 2 | [R4 S10] |
| `/mem [expr]` | `/m` | Show allocation statistics | 1 | [R4 S10] |
| `/run-tests` | — | Discover and run test functions | 4 | [R4 S10] |
| `/quit` | `/q` | Exit REPL | 0 | [Tested tests/e2e::e2e_s3_1_quit] |

### 3.2 `/help` Output [Tested tests/e2e::e2e_s3_1_help]

`/help` MUST list all available commands with a brief description. The output MUST be organized by category:

```
Available commands:
  /help (/h)        Show this help
  /sig (/s) <name>  Show signature
  /doc (/d) <name>  Show docstring
  ...
```

Commands not yet available (due to ring) SHOULD be omitted or marked as unavailable.

### 3.3 `/list` Categories [R4 S10]
<!-- Section-level: Modules and Imports categories not yet implemented -->

`/list` MUST organize symbols into categories. Names MUST be fully qualified.

| Category | Contents | Ring | Test |
|---|---|---|---|
| Types | User-defined types (`deftype`) | 0 | [Tested tests/e2e::e2e_s3_3_list] |
| Special forms | `if`, `let`, `fn`, `defn`, `deftype`, `match` | 0 | [Tested tests/e2e::e2e_s3_3_list_special_forms] |
| Functions | User-defined functions | 0 | [Tested tests/e2e::e2e_s3_3_list] |
| Traits | Trait declarations | 2 | [Tested tests/e2e::e2e_s3_3_list_traits] |
| Macros | Macro definitions | 3 | [Tested+Neg tests/ring3_repl::r3_list_macros_category_via_symbol_table, tests/ring3_repl::r3_neg_non_macros_absent_from_macros] |
| Modules | Declared submodules | 2 | [R4 S10] |
| Imports | Count of imported names by source module | 2 | [R3 S11] |

**`/list` scope rule:** `/list` MUST show only names **defined in** the current module. Imported names appear in the Imports category as a summary (count per source module), not individually mixed into other categories. Primitives (`add-i64`, `eq-i64`, etc.) are defined in the `primitives` module — they MUST NOT appear in `/list` when the current module is `user`. Trait methods (`+`, `show`, etc.) are either user-defined (appear under Functions) or imported (appear under Imports).

**`/list` Imports category format:**

```
Imports:
  primitives (3 names)
  math (2 names: foo, bar)
```

The Imports category shows which modules have been imported and how many names came from each. For small imports (≤5 names), the names are listed inline. For glob imports or large counts, only the count is shown. This gives the user a quick overview; `/imports` provides full detail.

**`/list` negative requirements** (what MUST NOT appear):

- Functions category MUST NOT contain names from other modules (primitives, imports)
- Types category MUST NOT contain types from other modules unless imported
- No category should contain compiler-internal symbols not in the spec
- In a fresh `user` session with no definitions, `/list` MUST show only Special forms (no Functions, no Types, no Traits — until the user defines them or loads a prelude)

**Filter argument:** `/list <text>` performs a case-insensitive substring match on symbol names across all categories, showing matching symbols with full type info (like `/sig`). `/list <module-name>` (when the argument matches a loaded module name) shows that module's public definitions. `/list <module-name> <text>` combines both: searches within a specific module.

**Large category display:** When a category contains 7 or more names, the display SHOULD use the following layout algorithm:

1. **Operators first, then mandatory break.** Non-alphabetic symbols (`+`, `-`, `*`, `!=`, etc.) are displayed first, wrapping at 6 per line. After all operators, a new line starts — operators never share a line with alphabetic names.

2. **Letter groups pack onto rows, breaking early to stay together.** Names are grouped by first letter (case-insensitive, sorted). Before adding a letter group to the current row, check: would `current_count + group_size > 6`? If so, flush the current row first. This ensures a letter group either fits entirely on the current row alongside previous groups, or starts a new row — it never splits across a row boundary (unless the group itself has 7+ names).

3. **Hard wrap at 6 within large groups.** If a single letter group has more than 6 names, it wraps at 6 per line within itself.

Categories with fewer than 7 names appear on a single line after the category label.

```
Fns:
  + - * / < > <= >= !=
  abs add ceil concat
  double drop
  empty? even? filter floor fold
  get
  ...
```

In this example: operators get their own line(s). Then A-group (abs, add) and C-group (ceil, concat) fit together on one row (4 items). D-group (double, drop) would push to 6+ so starts a new row. E-group (empty?, even?) and F-group (filter, floor, fold) fit together (5 items). G-group (get) starts a new row since adding it to the previous row would exceed 6.

### 3.4 `/imports` — Import Detail [R3 S11 — tests/ring3_repl::r3_imports_empty IGNORED]

`/imports` MUST show all imports active in the current module, grouped by source module, with the individual names listed. This is the detailed companion to `/list`'s summary Imports category.

```
user> /imports
From primitives:
  add-i64 :: (Fn [primitives/Int primitives/Int] primitives/Int)
  eq-i64  :: (Fn [primitives/Int primitives/Int] primitives/Bool)
  sub-i64 :: (Fn [primitives/Int primitives/Int] primitives/Int)
From math:
  bar :: (Fn [primitives/Int primitives/Int] primitives/Int)
  foo :: (Fn [primitives/Int] primitives/Int)
```

**Format:** Each imported name shows its type signature using fully-qualified type names (per §1.4). Names are grouped by **immediate source module** (the module named in the `import` form, not the ultimate origin) and sorted alphabetically within each group. Source modules are sorted alphabetically.

**Re-export provenance:** When the user writes `(import [prelude [*]])` and the prelude re-exports `+` from `core.numerics`, `/imports` shows `From prelude:` — because that is the module the user imported from. The user's mental model is "I imported from prelude." The ultimate origin is available via `/info +` (which shows the defining module per §3.5).

**Glob imports:** When `(import [mod [*]])` was used, `/imports` MUST show the individual names that were imported (the expansion of `*` at the time the import was evaluated), not just `*`.

**Implicit prelude import (Ring 3+):** The compiler injects an implicit `(import [prelude [*]])` for all non-prelude modules (spec §8.8.1). This implicit import IS visible in `/imports` — the user needs to discover what the prelude provides. `/imports prelude` filters to show only names from that source module (exact module name match).

**No imports:** In a fresh session with no explicit `(import ...)` and no prelude, `/imports` MUST show nothing (empty output, silent re-prompt). The `primitives` module's implicit availability is via the module resolution fallback, NOT via import — so it does not appear in `/imports` unless the user explicitly writes `(import [primitives [add-i64]])`.

**Filter argument:** `/imports <module-name>` filters to a single source module (exact match on the module name). This is useful when prelude imports are large — `/imports prelude` shows only prelude imports. `/imports` with no argument shows all imports.

**Error cases:**
- `/imports nonexistent` — no imports from that module; silent re-prompt (not an error)

### 3.5 `/info` Output [Tested tests/e2e::e2e_s3_4_info]

`/info <name>` MUST display multi-line details using the `:Type name` format:

```
:(Fn [primitives/Int] primitives/Int) user/double
  (defn double [x] (* x 2))
  48 bytes, 2ms
```

For overloaded functions, all variants MUST be listed. For constrained functions, specializations MUST be shown.

## 4. Self-Documentation Contract

Every valid language construct entered at the REPL MUST produce useful feedback. This is the **self-documentation principle** from the project's design principles. All output reinforces the language syntax.

### 4.1 Bare Symbol Lookup [R3 S10]

Entering a symbol name without arguments MUST produce its type and fully-qualified name:

| Symbol kind | Response | Test |
|---|---|---|
| Function | `:TypeScheme module/name` | [Tested tests/e2e::e2e_s4_1_bare_symbol_lookup] |
| Constructor | `:QualifiedType module/Type.Ctor` | [Tested tests/e2e::e2e_s1_1_constructor_lookup] |
| Type | Type definition display | [Tested tests/e2e::e2e_s1_1_bare_type_int, tests/e2e::e2e_s1_1_bare_type_bool, tests/e2e::e2e_s1_1_bare_type_float, tests/e2e::e2e_s1_1_bare_type_string] |
| Special form | `:signature name` | [Tested tests/e2e::e2e_s4_2_special_form_feedback] |
| Macro | Clause signatures | [R3 S11 — tests/ring3_repl::r3_bare_macro_lookup IGNORED] |
| Trait | Method signatures | [Tested tests/e2e::e2e_s4_1_bare_trait_lookup] |

If the symbol has a docstring (per spec §5.2), the **first line** of the docstring SHOULD be appended as a comment after the type display:

```
:TypeScheme module/name ; first line of docstring
```

This provides inline documentation without requiring a separate `/doc` command, reinforcing discoverability.

Examples:

```
0+0ms; user> id
:(Fn [a] a) user/id
0+0ms; user> double
:(Fn [primitives/Int] primitives/Int) user/double ; Multiply by 2
0+0ms; user> Red
:user/Color user/Color.Red
0+0ms; user> +
:(Fn [:core.numerics/Num a :a] a) core.numerics/+
```

No valid name MUST produce an opaque error. If a name is unbound, the error MUST say so clearly. [Tested tests/repl_experience::unbound_symbol_clear_error]

**Ring 0**: type + qualified name display.
**Ring 2**: docstring display (requires docstrings, which depend on the module system for stored metadata).

### 4.2 Special Form Feedback [R3 S9]

Special form keywords (`if`, `let`, `fn`, `defn`, `deftype`, `match`, `defmacro`) entered bare MUST produce a function-like type signature, NOT an opaque error. Special forms are not regular functions but displaying their shape teaches the user their syntax.

| Form | Test |
|---|---|
| `if` | [Tested tests/e2e::e2e_s4_2_special_form_feedback] |
| `let` | [Tested tests/e2e::e2e_s4_2_special_form_let] |
| `fn` | [Tested tests/e2e::e2e_s4_2_special_form_fn] |
| `defn` | [Tested tests/e2e::e2e_s4_2_special_form_defn] |
| `deftype` | [Tested tests/e2e::e2e_s4_2_special_form_deftype] |
| `match` | [Tested tests/e2e::e2e_s4_2_special_form_match] |
| `defmacro` | [R3 S11 — tests/ring3_repl::r3_special_form_defmacro IGNORED] |

Examples:

```
0+0ms; user> if
:(Fn [primitives/Bool a a] a) if
0+0ms; user> let
:(Fn [bindings body] a) let
0+0ms; user> defn
:(Fn [name params body] function) defn
```

### 4.3 Operator Feedback [Tested tests/e2e::e2e_s4_3_operator_plus_feedback]

Operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`) are stdlib functions, not builtins. Entering them bare MUST display their type scheme and fully-qualified name showing their stdlib home.

```
0+0ms; user> +
:(Fn [:core.numerics/Num a :a] a) core.numerics/+
0+0ms; user> =
:(Fn [:core.numerics/Eq a :a] primitives/Bool) core.numerics/=
```

In Ring 0 (before traits), the display SHOULD still show the operator's conceptual stdlib home. The implementation-level builtin is a temporary shortcut, not the truth.

## 5. Error Presentation [Tested]

### 5.1 Error Format [Tested]

All errors MUST display:

1. The error category (parse error, type error, etc.) [Tested tests/repl_experience::parse_error_category]
2. The source location (file/line/column or character span) [Tested tests/repl_experience::error_has_source_span]
3. A human-readable message [Tested tests/repl_experience::error_has_human_readable_message]

Errors MUST be written to stdout (as part of the REPL conversation flow, visible in piped output and the showcase). Stderr is reserved for traces and diagnostic output. Errors MUST NOT crash the REPL session — the user MUST be able to continue entering expressions after any error. [Tested tests/e2e::e2e_s5_1_errors_on_stdout]

### 5.2 Error Recovery [Tested]

After any error (parse, type, runtime), the REPL MUST:
- Display the error [Tested tests/e2e::e2e_s5_2_error_recovery]
- Reset input state (clear any partial multi-line input)
- Present the prompt for new input

The session state (defined functions, types, modules) MUST NOT be corrupted by an error in a subsequent expression. [Tested tests/repl_experience::type_error_does_not_corrupt_state]

### 5.3 Type Error Quality [Tested]

Type errors MUST include:
- The expected type (fully qualified) [Tested tests/repl_experience::type_error_mentions_expected_and_actual]
- The actual (inferred) type (fully qualified) [Tested tests/e2e::e2e_s5_3_type_error_shows_expected_actual]
- The source location of the mismatch [Tested tests/repl_experience::error_has_source_span]

Type errors SHOULD suggest common fixes when applicable.

## 6. Discoverability [Tested]

### 6.1 First Five Minutes [Tested tests/repl_experience::first_five_minutes_workflow]

A new user opening the REPL with no prior knowledge MUST be able to:

1. See that `/help` is available (mentioned in the startup banner or prompt)
2. Evaluate a simple expression and see a typed result: `(+ 1 2)` → `:primitives/Int 3`
3. Define a function and see its inferred type: `(defn id [x] x)` → `:(Fn [a] a) user/id`
4. Find available operators and functions via `/list`
5. Get help on any symbol via `/info` or `/sig`

### 6.2 Startup Banner [Tested tests/e2e::e2e_s6_2_startup_banner]

The REPL MUST display a startup banner including:
- The language name and version
- A hint about `/help`

The banner SHOULD be concise (3 lines or fewer).

### 6.3 First Session Journey [Tested tests/repl_experience::first_five_minutes_workflow]

The "first five minutes" (§6.1) lists capabilities. This section scripts the **narrative arc** — the sequence a new user follows from launch to confidence. Each step builds on the previous one; nothing requires prior knowledge. This journey defines the `first-session.demo` showcase script.

**Phase 1: Orientation** (banner → `/help`)

The user launches cranelisp and sees a banner with the language name and a `/help` hint. They type `/help`. The output shows them slash commands exist, organized by purpose. They now know there is a self-documentation system. *(Ring 0)*

**Phase 2: First evaluation** (expression → typed result)

The user types a simple expression. The result shows `:Type value` format — they learn that the REPL always shows types. They try a few more: booleans, arithmetic. Each result reinforces the `:Type value` pattern. *(Ring 0)*

**Phase 3: Defining things** (defn → type inference)

The user defines a function. The REPL shows the inferred type scheme and qualified name. They call it. They see that the REPL inferred the types without annotation. *(Ring 0)*

**Phase 4: Introspection** (`/sig`, `/list`, `/info`)

The user wants to see what they've defined. `/list` shows everything in scope. `/sig` shows a function's type. `/info` shows full details. They discover that the REPL knows about everything they've defined and can explain it. *(Ring 0)*

**Phase 5: Making mistakes** (error → recovery)

The user makes a type error. The error message names the expected and actual types. They continue typing — the session is intact. They learn the REPL is resilient. *(Ring 0)*

**Phase 6: Self-documentation** (bare symbols, special forms)

The user types a function name bare. The REPL shows its type. They type `if` bare. It shows the special form's shape. They learn that any name typed bare produces documentation, not an error. *(Ring 0)*

**Phase 7: Richer types** (strings, ADTs, Vecs)

The user creates a string, defines an ADT, pattern-matches on it. They create a Vec. Each value displays in a readable format that mirrors the language syntax. *(Ring 1)*

**Phase 8: Composition** (closures, higher-order, putting it together)

The user combines what they've learned: a closure over an ADT, applied via a higher-order function, stored in a Vec. The REPL handles it all. They feel confident. *(Ring 1)*

Later rings extend this journey with modules (`/mod`), traits, macros (`/expand`), and IO, but the core loop — evaluate, inspect, make mistakes, recover — is established by Ring 1.

### 6.4 Tab Completion [R4 S11]

The REPL SHOULD support tab completion for:
- Symbol names (functions, types, constructors)
- Slash commands
- Module names (after `/mod`)

This is a SHOULD, not a MUST, because it depends on the terminal library.

## 7. Performance Targets

### 7.1 Startup Time [Tested tests/e2e::e2e_s7_1_startup_under_500ms]

The REPL MUST start and display a prompt within **500ms** on a modern machine (defined as: Apple M-series or equivalent x86-64, SSD, 8GB+ RAM). This includes loading the prelude.

### 7.2 Expression Evaluation [Tested tests/repl_experience::simple_eval_under_50ms]

Simple expressions (arithmetic, boolean logic, small function calls) MUST evaluate and display within **50ms** of the user pressing Enter. This is the combined compile + eval time.

### 7.3 Prompt Responsiveness [R4 S10]

After displaying a result, the next prompt MUST appear within **10ms**. There MUST be no perceptible delay between result display and prompt readiness.

### 7.4 Large Output [R3 S8]

When displaying large values (e.g., a Vec with 1000 elements), the REPL SHOULD truncate output with an indication of the total size rather than flooding the terminal. The truncation threshold is implementation-defined but SHOULD be configurable.

## 8. Ring 2B Module Demo Scenarios [R4 S10]

When the module system is fully wired (Ring 2B), these 7 REPL scenarios validate the module experience. Each scenario has a concrete expected behavior.

**Scenario 1: `/mod math` switches namespace**
```
user> /mod math
math>
```
The prompt changes to reflect the active module. Definitions entered now belong to `math`.

**Scenario 2: `/mod user` switches back**
```
math> /mod user
user>
```
Switching back to `user` restores the default namespace. Previously defined `math` symbols remain accessible via qualified names.

**Scenario 3: `(import [math [foo]])` loads module**
```
user> (import [math [foo]])
```
After defining `foo` in the `math` module (via `/mod math` + `defn`), importing it makes `foo` available as a bare name in `user`.

**Scenario 4: Qualified access `math/foo`**
```
user> math/foo
:(Fn [primitives/Int] primitives/Int) math/foo
```
Without importing, any symbol can be accessed via its qualified path.

**Scenario 5: `/list` shows module symbols only**
```
math> /list
Functions:
  math/foo
```
The `/list` command in a module shows only that module's own definitions, not imported or global symbols. After switching back to `user` and importing:
```
user> (import [math [foo]])
user> /list
Special forms:
  defn, deftype, ...
Imports:
  math (1 name)
```
The imported `foo` appears under Imports (summary), not under Functions.

**Scenario 5b: `/imports` shows detail**
```
user> /imports
From math:
  foo :: (Fn [primitives/Int] primitives/Int)
```
The imported `foo` appears with its full type signature. The source module is `math` (the module named in the `import` form).
The `/imports` command shows exactly what was imported and from where. The user can see the type signature of each imported name.

**Scenario 6: `/mod` shows current module**
```
math> /mod
math
```
Bare `/mod` with no argument displays the name of the current module.

**Scenario 7: Unknown module gives clear error**
```
user> /mod nonexistent
Error: Module 'nonexistent' not found. Use /mod <name> to create a new module.
```
The error message is actionable — it tells the user what to do next.

## 10. Terminal Styling [R4 S11]

When connected to a colour-capable terminal (detected via `isatty()` and `TERM`/`NO_COLOR`), the REPL SHOULD apply ANSI colour to distinguish output categories. Styling MUST be suppressed in piped/batch mode and when `NO_COLOR` is set (per https://no-color.org).

### 10.1 Colour Palette [R4 S11]

| Element | Colour | ANSI | Rationale |
|---|---|---|---|
| Prompt (timing + module) | dim/grey | `\033[90m` | Recedes — not the focus |
| User input (typed text) | white/default | `\033[0m` | Primary focus — what the user is writing |
| Comment lines (`;`) | green | `\033[32m` | Familiar from editors; clearly non-code |
| Result type (`:Type`) | cyan | `\033[36m` | Distinct from value; teaches the type system |
| Result value | white/default | `\033[0m` | Primary content |
| Error messages | red | `\033[31m` | Immediately noticeable |
| Warnings | yellow | `\033[33m` | Less urgent than errors |
| Slash command output | default | `\033[0m` | Informational, no special emphasis |

### 10.2 Showcase Styling [R4 S11]

The showcase player (`repl/showcase`) MAY apply the same colour palette during replay. Comment section headers SHOULD use the same green as REPL comments. The `[paused]` indicator SHOULD use dim/grey.

### 10.3 Requirements [R4 S11]

- Colour MUST be opt-out, not opt-in (enabled by default on capable terminals)
- `NO_COLOR` environment variable MUST disable all colour output
- Piped output (`!isatty(stdout)`) MUST NOT contain ANSI escape sequences
- Colour choices SHOULD be legible on both light and dark terminal backgrounds
- The colour scheme SHOULD be consistent between the REPL and the showcase player

**Ring 4**: full terminal styling implementation.

## 9. Ring Testability Matrix

| Requirement | Ring 0 | Ring 1 | Ring 2 | Ring 3 | Ring 4 |
|---|---|---|---|---|---|
| `:Type value` display | Int, Bool, Float, enum ADT | + String, data ADT, Vec, List, closures | + Seq | | + IO |
| Definition display | function type + qualified name | | + constrained, overloaded | + macro | |
| Prompt with timing | yes | | + module name | | |
| `/help` | yes | | | | |
| `/sig`, `/doc`, `/type`, `/info` | yes | | | | |
| `/source`, `/sexp`, `/ast`, `/clif`, `/disasm` | yes | | | | |
| `/list` | Types, Special forms, Fns | | + Traits, Modules, Imports | + Macros | |
| `/time` | yes | | | | |
| `/expand` | | | | yes | |
| `/mod`, `/reload` | | | yes | | |
| `/mem` | | yes | | | |
| `/run-tests` | | | | | yes |
| Self-documentation | bare symbol, special forms, operators (qualified) | | + traits, modules | + macros | |
| Error recovery | yes | | | | |
| Startup < 500ms | yes | | | | |
| Eval < 50ms (simple) | yes | | | | |
| Fully-qualified names | all output | | | | |
| `Type.Constructor` notation | yes | | | | |

## 11. Ring 3 REPL Requirements [R3 S11]
<!-- Partial: §11.3 and §11.2.1-2 tested, §11.1/§11.4 not yet -->

Ring 3 introduces the macro system. The REPL MUST integrate macros into all existing introspection and display mechanisms so that macros are first-class citizens of the self-documentation experience.

### 11.1 `/expand` Command [R3 S11 — tests/ring3_repl::r3_expand_single_macro IGNORED]

The `/expand` (alias `/e`) command MUST accept a single S-expression form, perform recursive macro expansion to a fixed point (per spec Section 9.3.3), and display the fully expanded S-expression WITHOUT evaluating it.

```
user> /expand (double-list 1 2)
(Cons 1 (Cons 1 (Cons 2 (Cons 2 Nil))))
user> /expand (cond (> x 0) "pos" (= x 0) "zero" "neg")
(if (> x 0) "pos" (if (= x 0) "zero" "neg"))
user> /expand (+ 1 2)
(+ 1 2)
```

If the input form contains no macro calls, `/expand` MUST display it unchanged. If expansion fails (e.g., arity mismatch, expansion limit exceeded), `/expand` MUST display the error without corrupting session state.

The output MUST be a valid S-expression string. Fully-qualified constructor names generated by quasiquote expansion (e.g., `macros/SexpSym`) SHOULD be simplified to bare names when they are unambiguous in context.

### 11.2 Macro Introspection [R3 S11]

Macros MUST appear in existing REPL introspection commands alongside functions and types.

#### 11.2.1 `/list` — Macros Category [Tested+Neg tests/ring3_repl::r3_list_macros_category_via_symbol_table, tests/ring3_repl::r3_list_neg_macros_not_in_functions, tests/ring3_repl::r3_neg_non_macros_absent_from_macros]

`/list` MUST include a "Macros" category listing all macros defined or imported in the current module. Macros MUST be listed by their unqualified name within the current module scope.

```
user> /list
Macros: double-list, when
Fns: ...
Types: ...
```

#### 11.2.2 `/info` — Macro Details [Tested tests/ring3_repl::r3_info_macro_clause_count, tests/ring3_repl::r3_info_macro_docstring]

`/info <name>` for a macro MUST display:
- The macro's classification as `macro`
- The number of clauses (if multi-clause)
- The docstring (if present)

```
user> /info cond
cond :: macro (2 clauses)
  "Multi-way conditional with mandatory default"
user> /info when
when :: macro
```

#### 11.2.3 `/sig` — Macro Signature [Tested tests/ring3_repl::r3_sig_macro_params — variadic IGNORED]

`/sig <name>` for a macro MUST display the parameter signature of each clause, using `& rest` syntax for variadic parameters and bracket notation for bracket destructuring parameters.

```
user> /sig cond
cond :: macro
  [x]
  [x body & rest]
user> /sig bind!
bind! :: macro
  [[name expr & bindings] body]
```

For single-clause macros, the clause signature MAY be displayed on the same line:

```
user> /sig when
when :: macro [cond body]
```

#### 11.2.4 `/doc` — Macro Docstring [R3 S11 — tests/ring3_repl::r3_doc_macro_no_docstring IGNORED]

`/doc <name>` for a macro MUST display the macro's docstring. If the macro has no docstring, `/doc` MUST display a message indicating none is available.

```
user> /doc list
list: "Construct a list from elements"
user> /doc my-macro
my-macro: no docstring
```

### 11.3 `defmacro` Display [Tested tests/ring3_repl::r3_defmacro_display_single_clause, tests/ring3_repl::r3_defmacro_display_multi_clause, tests/macros::repl_defmacro_display_single_clause, tests/macros::repl_defmacro_display_multi_clause]

When the user defines a macro at the REPL, the display MUST confirm the definition using the format:

```
name :: macro
```

For multi-clause macros, the clause count SHOULD be shown:

```
name :: macro (N clauses)
```

Examples:

```
user> (defmacro double [x] `(+ ~x ~x))
double :: macro
user> (defmacro cond ([x] x) ([x body & rest] `(if ~x ~body (cond ~@rest))))
cond :: macro (2 clauses)
```

This mirrors the definition display pattern established for functions (Section 1.3) and types, keeping the REPL output self-documenting.

### 11.4 Bare Macro Lookup [R3 S11 — tests/ring3_repl::r3_bare_macro_lookup IGNORED]

Entering a macro name as a bare symbol (without arguments) MUST produce its clause signatures, consistent with the self-documentation contract (Section 4.1). Zero-argument macros are an exception: they expand immediately via bare-symbol expansion (spec Section 9.5) rather than displaying introspection.

```
user> double
double :: macro [x]
user> cond
cond :: macro
  [x]
  [x body & rest]
```

### 11.5 Sprint 11 Test Scenarios [R3 S11]

The following test scenarios validate the Ring 3 REPL macro experience. Each MUST have a corresponding test in `tests/`.

| # | Scenario | Expected Behavior | Spec Reference | Test |
|---|---|---|---|---|
| 1 | `/expand` with a single macro | Displays expanded form without evaluation | §11.1, §9.3.2 | [R3 S11 — tests/ring3_repl::r3_expand_single_macro IGNORED] |
| 2 | `/expand` with nested macros | Displays fully expanded form (recursive to fixed point) | §11.1, §9.3.3 | [R3 S11 — tests/ring3_repl::r3_expand_nested_macros IGNORED] |
| 3 | `/expand` with no macro calls | Displays input unchanged | §11.1 | [R3 S11 — tests/ring3_repl::r3_expand_no_macro IGNORED] |
| 4 | `/list` after `defmacro` | Macro appears under "Macros" category | §11.2.1, §3.3 | [Tested tests/ring3_repl::r3_list_macros_category_via_symbol_table] |
| 5 | `/info` on a multi-clause macro | Shows clause count and docstring | §11.2.2 | [Tested tests/ring3_repl::r3_info_macro_clause_count] |
| 6 | `/sig` on a variadic macro | Shows parameter signature with `& rest` | §11.2.3 | [Tested tests/ring3_repl::r3_sig_macro_params — variadic IGNORED] |
| 7 | `defmacro` display at REPL | Shows `name :: macro` confirmation | §11.3, §9.13 | [Tested tests/ring3_repl::r3_defmacro_display_single_clause] |
| 8 | Bare macro name lookup | Shows clause signatures (non-zero-arg macros) | §11.4, §4.1 | [R3 S11 — tests/ring3_repl::r3_bare_macro_lookup IGNORED] |
