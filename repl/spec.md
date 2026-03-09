# REPL Experience Specification

Normative specification for the Cranelisp REPL user experience. A conforming REPL MUST satisfy all requirements tagged with the current ring or earlier.

While called repl, the repl experience encompasses the entire user experience from invoking the repl as well as its associated CLI invocation modes, exit codes, batch output format, and cache lifecycle.

## 0. CLI Invocation Modes

The `cranelisp` binary supports the following invocation modes:

| Mode | Invocation | Description | Status |
|---|---|---|---|
| REPL | `cranelisp` | Start the interactive REPL | Implemented |
| Batch | `cranelisp --run <file.cl>` | Compile and execute a source file, print result, exit | Implemented |
| Version | `cranelisp --version` | Print version string and exit | Future work |
| Help | `cranelisp --help` | Print usage summary and exit | Future work |

### 0.1 REPL Mode (no arguments)

When invoked with no arguments, the binary MUST start the interactive REPL: display the startup banner (see Section 6.2), load the prelude, and present the primary prompt. The REPL runs until the user enters `/quit` or sends EOF (Ctrl-D).

### 0.2 Batch Mode (`--run <file>`)

`cranelisp --run <file.cl>` MUST compile and execute the named source file via the module graph pipeline. On success, the result value MUST be printed to stdout in the same `:Type value` format used by the REPL (Section 1.2). Warnings MUST be printed to stderr. On failure, the error MUST be printed to stderr and the process MUST exit with a non-zero status code.

If the file does not exist, the binary MUST print an error to stderr and exit with status code 1.

### 0.3 Error Handling

Invalid arguments (e.g., `cranelisp --run` without a file, or unknown flags) MUST print a usage hint to stderr and exit with status code 1. The usage hint MUST show the supported invocation forms.

### 0.4 Future: `--version` and `--help` [R4]

`cranelisp --version` SHOULD print the version string (format: `cranelisp <semver>`) to stdout and exit with status code 0.

`cranelisp --help` SHOULD print a usage summary listing all supported flags and their descriptions to stdout and exit with status code 0.

These are not yet implemented. When added, they MUST follow standard CLI conventions (GNU-style long flags, stdout for informational output, exit code 0 on success).

## Design Principle

> **The REPL reinforces the syntax of the language.** Every output teaches the user how to write Cranelisp.

Output uses the `:Type value` format — the same colon-prefixed type annotation syntax used in the language itself. Names are always fully qualified to teach the module system. Constructors use `Type.Constructor` dot notation (valid input syntax per §1.4.4 of the language spec).

## 1. Display Format

### 1.1 Universal Output Format [R3 S14]

All REPL output uses a unified format that mirrors Cranelisp type annotation syntax. The primary line is always:

```
:Type {value|name} ; {classification} - {docstring first line}
```

Where:
- `:Type` — the fully-qualified type (per §1.4), always present
- `{value|name}` — either a runtime value (for expression results) or a fully-qualified name (for definitions and lookups)
- `; {classification} - {docstring}` — optional comment suffix. The classification is the name of the defining special form (`defn`, `deftype`, `deftrait`, `defmacro`, `special form`, `impl`). The docstring is the first line of the symbol's documentation. If the symbol has no docstring, only the classification appears. If there is no classification (literal values), the comment is omitted entirely.

**Related symbols** appear as comment lines below the primary line. Each section names a relationship using language syntax, followed by unqualified symbol names (bare names, since these are in-scope symbols):

```
; {relationship}:
;  {symbol} {symbol} ...
```

Related symbol lists use the same line-breaking algorithm as `/list` categories (§3.3). Within each section, locally-defined symbols appear before imported symbols.

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

When the user enters a definition form, the REPL confirms the definition using the universal format (§1.1). The response follows the same per-class rules as bare symbol lookup (§4.1) — a definition is immediately followed by its lookup display.

```
user> (defn double "Multiply by 2" [x] (* x 2))
:(Fn [primitives/Int] primitives/Int) user/double ; defn - Multiply by 2

user> (deftype Color Red Green Blue)
:user/Color ; deftype
; match:
;  Red Green Blue

user> (deftrait (Sizeable a) (size [:a] :Int))
:user/Sizeable ; deftrait
; defn:
;  size

user> (impl Sizeable Circle (defn size [c] ...))
impl user/Sizeable for user/Circle
```

A function definition MUST NOT display `<closure>` — the user defined a *named* function, not an anonymous closure. `<closure>` is reserved for anonymous function *values* (§1.2, §1.5).

| Requirement | Test |
|---|---|
| defn shows type + qualified name | [Tested tests/repl_experience::defn_reports_type_and_name] |
| polymorphic defn shows type vars | [Tested tests/repl_experience::defn_polymorphic_type_vars] |
| deftype shows qualified type name | [Tested tests/repl_experience::deftype_reports_adt_type] |
| deftrait shows trait name | [Tested tests/ring2::repl_deftrait_display] |
| impl shows `impl Trait for Type` | [Tested tests/ring2::repl_impl_display] |
| constrained fn shows inline constraints | [Tested tests/ring2::repl_constrained_fn_display] |
| overloaded fn shows all variants | [R3 S14] |

**Ring 0**: function definitions, type definitions.
**Ring 2**: trait declarations, trait implementations, constrained functions.
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
| Data constructor (multi-ctor) | `(Type.Ctor field1 field2 ...)` (e.g., `(Option.Some 42)`) | 1 | [Tested tests/e2e::e2e_s1_5_data_ctor_dot_notation] |
| Data constructor (single-ctor, name matches type) | `(Ctor field1 field2 ...)` (e.g., `(Point 3 4)`) | 1 | [Tested tests/e2e::e2e_ring1_adt_product] |

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
| `/doc <name>` | `/d` | Show docstring (including builtins — see spec/appendix-a-builtins.md §A.5) | 0 | [R1] |
| `/type <expr>` | `/t` | Show type without evaluating | 0 | [Tested tests/e2e::e2e_s3_1_type] |
| `/info <name>` | `/i` | Full details: type, classification, code size, compile time | 0 | [Tested tests/e2e::e2e_s3_4_info] |
| `/source <name>` | — | Show original source text | 0 | [R4 S10] |
| `/sexp <name>` | — | Show parsed S-expression | 0 | [R4 S10] |
| `/ast <name>` | — | Show AST | 0 | [R4 S10] |
| `/clif <name>` | — | Show Cranelift IR | 0 | [R4 S10] |
| `/disasm <name>` | — | Show disassembled native code | 0 | [R4 S10] |
| `/list [prefix]` | `/l` | List definitions in current module | 0 | [Tested tests/e2e::e2e_s3_3_list] |
| `/time <expr>` | — | Evaluate with timing breakdown | 0 | [Tested tests/e2e::e2e_s3_1_time] |
| `/expand <form>` | `/e` | Macro-expand a form | 3 | [R3 S11 — tests/ring3_repl::r3_expand_single_macro IGNORED] |
| `/mod [name]` | — | Switch module namespace | 2 | [R4 S10] |
| `/imports [module]` | — | Show imports and special forms; filter by source module | 0 | [R3 S14] |
| `/exports <module>` | — | List a module's importable public symbols | 2 | [R3 S14] |
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

### 3.3 `/list` — Module Definitions [R4 S15]

`/list` shows symbols **defined in the current module** — the user's own work. It does NOT show imports or special forms (those belong on `/imports`). Constructors are included alongside other symbols alphabetically.

**Scope rule:** `/list` MUST show only names created by definitions in the current module: `defn`, `deftype`, `deftrait`, `impl` (trait method definitions), `defmacro`. Imported names MUST NOT appear. [Tested+Neg tests/e2e::e2e_s3_3_list_neg_no_imports] Special forms MUST NOT appear (they are always available and shown by `/imports`). [Tested+Neg tests/e2e::e2e_s3_3_list_neg_no_special_forms] Primitives (`add-i64`, etc.) MUST NOT appear when the current module is `user`. [Tested+Neg tests/e2e::e2e_s3_3_list_neg_no_imports]

**Categories:**

| Category | Contents | Ring | Test |
|---|---|---|---|
| Modules | Declared submodules | 2 | [R4 S15] |
| Macros | Macro definitions (`defmacro`) | 3 | [Tested+Neg tests/ring3_repl::r3_list_macros_category_via_symbol_table, tests/ring3_repl::r3_neg_non_macros_absent_from_macros] |
| Traits | Trait declarations (`deftrait`) | 2 | [Tested tests/e2e::e2e_s3_3_list_traits] |
| Types | User-defined types and constructors (`deftype`) | 0 | [Tested+Neg tests/e2e::e2e_s3_3_list_constructors_in_types, tests/e2e::e2e_s3_3_list_neg_ctors_not_in_fns] |
| Fns | User-defined functions and trait method implementations | 0 | [Tested tests/e2e::e2e_s3_3_list, tests/e2e::e2e_s3_3_list_fns_category_name] |

Category order: Modules, Macros, Traits, Types, Fns. Empty categories are omitted. [Tested+Neg tests/e2e::e2e_s3_3_list_neg_empty_categories_omitted]

**Empty module:** When no definitions exist in the current module, `/list` MUST print `(no definitions)`. [Tested tests/e2e::e2e_s3_3_list_empty_module] This distinguishes "command worked on empty module" from a failed command.

**Negative requirements** (what MUST NOT appear): [Tested+Neg]

- No category should contain imported names (those belong on `/imports`) [Tested+Neg tests/e2e::e2e_s3_3_list_neg_no_imports]
- No category should contain special forms (those belong on `/imports`) [Tested+Neg tests/e2e::e2e_s3_3_list_neg_no_special_forms]
- No category should contain compiler-internal symbols (`__macro_*`, `$`-mangled names) [R4 S15]
- Constructors MUST appear in Types, not in Fns [Tested+Neg tests/e2e::e2e_s3_3_list_constructors_in_types, tests/e2e::e2e_s3_3_list_neg_ctors_not_in_fns]

**Filter argument:** `/list <text>` performs a case-insensitive prefix match on symbol names across all categories, showing matching symbols with full type info. [Tested tests/e2e::e2e_s3_3_list_prefix_filter] `/list` with no argument shows all definitions. [Tested tests/e2e::e2e_s3_3_list]

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

### 3.4 `/imports` — Imports and Special Forms [R4 S15]

`/imports` shows everything available in the current module that was NOT defined here: imported names and language special forms. This is the complement of `/list` — together they cover all symbols in scope.

**Categories:**

| Category | Contents | Ring | Test |
|---|---|---|---|
| Special forms | `if`, `let`, `fn`, `defn`, `deftype`, `match`, etc. | 0 | [Tested tests/e2e::e2e_s3_4_imports_special_forms, tests/e2e::e2e_s3_4_imports_special_forms_always] |
| Macros | Imported macro definitions | 3 | [R4 S15] |
| Traits | Imported trait declarations | 2 | [R4 S15] |
| Types | Imported types and constructors | 0 | [R4 S15] |
| Fns | Imported functions and trait methods | 0 | [Tested tests/e2e::e2e_s3_4_imports_includes_imports] |

Category order: Special forms, Macros, Traits, Types, Fns. Empty categories are omitted (except Special forms, which are always present). [Tested tests/e2e::e2e_s3_4_imports_special_forms_always]

**Format:** Each category lists names using the same layout algorithm as `/list` (§3.3) — names only, no type signatures. Type the symbol name for more detail.

**Source module filter:** `/imports <module-name>` filters to show only imports from that source module (exact match). [Tested tests/e2e::e2e_s3_4_imports_filter_by_module, tests/e2e::e2e_s3_4_imports_filter_shows_from] Names are grouped under `From <module>:` and sorted alphabetically. Source modules sorted alphabetically.

```
user> /imports prelude
From prelude:
  + - * / < > <= >= != =
  case cond
  show str
  ...
```

**Unfiltered mode:** `/imports` with no argument shows all imports organized by category (not by source module). [Tested tests/e2e::e2e_s3_4_imports_after_import] This gives a quick overview of what's available. Use `/imports <module>` for per-module detail.

**Re-export provenance:** When the user writes `(import [prelude [*]])` and the prelude re-exports `+` from `core.numerics`, `/imports prelude` shows `+` under `From prelude:` — because that is the module the user imported from. The ultimate origin is available via `/info +` (§3.6).

**Reexport entries:** Both `Import` and `Reexport` module entries MUST be included. [Tested tests/e2e::e2e_s3_4_imports_includes_imports] A symbol re-exported through the prelude is still an import from the user's perspective.

**Glob imports:** When `(import [mod [*]])` was used, `/imports` MUST show the individual names that were imported (the expansion of `*` at the time the import was evaluated), not just `*`.

**Implicit prelude import (Ring 3+):** The compiler injects an implicit `(import [prelude [*]])` for all non-prelude modules (spec §8.8.1). This implicit import IS visible in `/imports` — the user needs to discover what the prelude provides.

**No imports:** In a fresh session with no explicit `(import ...)` and no prelude, `/imports` MUST show only Special forms. [Tested tests/e2e::e2e_s3_4_imports_empty] The `primitives` module's implicit availability is via the module resolution fallback, NOT via import — so primitives do not appear in `/imports` unless explicitly imported.

**Error cases:**
- `/imports nonexistent` — no imports from that module; silent re-prompt (not an error) [Tested+Neg tests/e2e::e2e_s3_4_neg_imports_nonexistent_not_error, tests/e2e::e2e_s3_4_neg_imports_nonexistent_silent]

### 3.5 `/exports <module>` — Module Public API [R4 S15]

`/exports <module>` resolves a module and lists its importable (public) symbols. This answers "what can I import from this module?" before writing an `(import ...)` form.

**Argument:** The module name is required. `/exports` with no argument MUST print a usage hint: `Usage: /exports <module-name>`. [Tested tests/e2e::e2e_s3_5_exports_no_arg_usage]

**Module resolution:** The argument is resolved using the same resolution logic as `(import [module [...]])` — submodule paths, root modules, and stdlib modules. If the module is not yet loaded, it SHOULD be resolved and loaded (same as an import would trigger). If the module cannot be found, print an error: `Module '<name>' not found`. [Tested tests/e2e::e2e_s3_5_exports_not_found]

**Output format:** Public symbols listed by category — names only, no type signatures. [Tested tests/e2e::e2e_s3_5_exports_lists_symbols] Type the symbol name for more detail.

```
user> /exports math
Module 'math':
Fns:
  bar foo
```

Categories follow the same order as `/list`: Modules, Macros, Traits, Types, Fns. Names sorted alphabetically within categories.

**What counts as public:** Definitions with public visibility — `Def`, `Constructor`, `TraitDecl`, `TypeDef`, `Macro`. Import and Reexport entries in the target module are NOT shown (those are the module's own imports, not its exports).

**Empty module:** If the module has no public symbols, print `Module '<name>' has no public symbols`. [R4 S15]

**Filter argument:** `/exports <module> <prefix>` performs a case-insensitive prefix match within the module's exports. [R4 S15]

### 3.6 `/info` Output [Tested tests/e2e::e2e_s3_4_info]

`/info <name>` MUST display multi-line details using the `:Type name` format:

```
:(Fn [primitives/Int] primitives/Int) user/double
  (defn double [x] (* x 2))
  48 bytes, 2ms
```

For overloaded functions, all variants MUST be listed. For constrained functions, specializations MUST be shown.

## 4. Self-Documentation Contract

Every valid language construct entered at the REPL MUST produce useful feedback. This is the **self-documentation principle** from the project's design principles. All output reinforces the language syntax.

### 4.1 Symbol Lookup — Per-Class Specification [R3 S14]

Entering a bare symbol name at the REPL MUST produce output following the universal format (§1.1). Every symbol class has a defined response. No valid name MUST produce an opaque error. If a name is unbound, the error MUST say so clearly. [Tested tests/repl_experience::unbound_symbol_clear_error]

#### 4.1.1 Functions (defn) [Tested tests/e2e::e2e_s4_1_bare_symbol_lookup]

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

| Requirement | Test |
|---|---|
| function shows type + name | [Tested tests/e2e::e2e_s4_1_bare_symbol_lookup] |
| constrained fn shows constraints | [Tested tests/ring2::repl_constrained_fn_display] |
| overloaded fn shows all variants | [R3 S14] |

#### 4.1.2 Constructors [Tested tests/e2e::e2e_s1_1_constructor_lookup]

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

#### 4.1.3 Types (deftype) [Tested tests/e2e::e2e_s1_1_bare_type_int]

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
| builtin types (Int, Bool, Float, String) | [Tested tests/e2e::e2e_s1_1_bare_type_int, tests/e2e::e2e_s1_1_bare_type_bool, tests/e2e::e2e_s1_1_bare_type_float, tests/e2e::e2e_s1_1_bare_type_string] |
| user-defined type | [Tested tests/e2e::e2e_s1_1_bare_type_user_defined] |
| related constructors | [R3 S14] |
| related trait impls | [R3 S14] |

#### 4.1.4 Traits (deftrait) [Tested tests/e2e::e2e_s4_1_bare_trait_lookup]

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
:core.numerics/Num ; deftrait - Numeric operations
; defn:
;  + - * /
; impl:
;  Float Int
```

Within `impl:`, locally-defined types appear first, then imported types. Method names under `defn:` are unqualified.

#### 4.1.5 Special Forms [Tested tests/e2e::e2e_s4_2_special_form_feedback]

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
| `if` | [Tested tests/e2e::e2e_s4_2_special_form_feedback] |
| `let` | [Tested tests/e2e::e2e_s4_2_special_form_let] |
| `fn` | [Tested tests/e2e::e2e_s4_2_special_form_fn] |
| `defn` | [Tested tests/e2e::e2e_s4_2_special_form_defn] |
| `deftype` | [Tested tests/e2e::e2e_s4_2_special_form_deftype] |
| `match` | [Tested tests/e2e::e2e_s4_2_special_form_match] |
| `defmacro` | [R3 S14 — tests/ring3_repl::r3_special_form_defmacro] |

#### 4.1.6 Macros (defmacro) [R3 S14]

Primary line plus clause signatures. Classification `defmacro`. Each clause shows its parameter list on a separate comment line.

```
user> twice
:user/twice ; defmacro - Evaluate and double
; [x] -> Sexp

user> my-add
:user/my-add ; defmacro - Variadic addition
; [x] -> Sexp
; [x y] -> Sexp
; [x y z] -> Sexp
```

Zero-arg macros expand immediately — they do not reach the lookup path.

| Requirement | Test |
|---|---|
| macro shows clause signatures | [R3 S14 — tests/ring3_repl::r3_bare_macro_lookup] |
| multi-clause macro | [R3 S14 — tests/ring3_repl::r3_bare_macro_lookup_multi_clause] |

#### 4.1.7 Primitive Functions [R3 S14]

Primary line only. Classification `defn` (primitives are functions). Primitives are defined in the `primitives` module.

```
user> add-i64
:(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64 ; defn

user> str-concat
:(Fn [primitives/String primitives/String] primitives/String) primitives/str-concat ; defn
```

**Current gap**: The implementation skips primitives (`DefKind::Primitive` returns `None`). They MUST be shown like any other function.

#### 4.1.8 Trait Methods (including operators) [Tested tests/e2e::e2e_s4_3_operator_plus_feedback]

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

#### 4.1.10 Unbound Names [Tested tests/repl_experience::unbound_symbol_clear_error]

An unbound name MUST produce a clear error message, not an opaque internal error. The session MUST continue.

```
user> xyz
error: unbound symbol 'xyz'
```

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

The user wants to see what they've defined. `/list` shows their definitions. `/imports` shows what's available from elsewhere (including special forms). `/sig` shows a function's type. `/info` shows full details. They discover that the REPL knows about everything and can explain it. *(Ring 0)*

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

**Scenario 5: `/list` shows only definitions**
```
math> /list
Fns:
  foo
```
The `/list` command shows only that module's own definitions — not imports, not special forms. Names are unqualified (they belong to the current module). After switching back to `user` with no definitions:
```
user> /list
(no definitions)
```
`/list` is empty because the user hasn't defined anything yet. Imports and special forms are on `/imports`.

**Scenario 5b: `/imports` shows imports and special forms**
```
user> (import [math [foo]])
user> /imports
Special forms:
  defn deftype fn if let match
Fns:
  foo
```
Special forms always appear in `/imports` (they're available but not user-defined). The imported `foo` appears under Fns. For detail on where imports came from:
```
user> /imports math
From math:
  foo
```
The source module filter groups names by source. Type `foo` for its type signature.

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

<!-- FIXME(/repl): Terminal styling is specced at Ring 4 but should be reconsidered
for earlier delivery. At minimum, prompt, comments, and output type annotations
should be visually distinct. The demos look flat and hard to parse without any
colour differentiation. Consider pulling basic ANSI colour (prompt dim, type cyan,
errors red) into Ring 3 scope — the full palette can remain Ring 4. -->

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
| `/list` | Types, Fns | | + Traits, Modules | + Macros | |
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

`/list` MUST include a "Macros" category listing all macros defined in the current module (per §3.3). Macros MUST be listed by their unqualified name.

```
user> /list
Macros:
  double-list when
Fns:
  ...
```

#### 11.2.2 `/info` — Macro Details [Tested tests/ring3_repl::r3_info_macro_clause_count, tests/ring3_repl::r3_info_macro_docstring]

`/info <name>` for a macro MUST display the universal format (§1.1) with classification `defmacro`, clause signatures, and docstring.

```
user> /info cond
:user/cond ; defmacro - Multi-way conditional with mandatory default
; [x] -> Sexp
; [x body & rest] -> Sexp
  2 clauses
user> /info when
:user/when ; defmacro
; [cond body] -> Sexp
```

#### 11.2.3 `/sig` — Macro Signature [Tested tests/ring3_repl::r3_sig_macro_params — variadic IGNORED]

`/sig <name>` for a macro MUST display the clause signatures using the universal format (§1.1, §4.1.6), with `& rest` syntax for variadic parameters and bracket notation for bracket destructuring.

```
user> /sig cond
:user/cond ; defmacro
; [x] -> Sexp
; [x body & rest] -> Sexp

user> /sig bind!
:prelude/bind! ; defmacro
; [[name expr & bindings] body] -> Sexp

user> /sig when
:user/when ; defmacro
; [cond body] -> Sexp
```

#### 11.2.4 `/doc` — Macro Docstring [R3 S11 — tests/ring3_repl::r3_doc_macro_no_docstring IGNORED]

`/doc <name>` for a macro MUST display the macro's docstring. If the macro has no docstring, `/doc` MUST display a message indicating none is available.

```
user> /doc list
:prelude/list ; defmacro - Construct a list from elements

user> /doc my-macro
:user/my-macro ; defmacro
  no docstring
```

### 11.3 `defmacro` Display [Tested tests/ring3_repl::r3_defmacro_display_single_clause, tests/ring3_repl::r3_defmacro_display_multi_clause, tests/macros::repl_defmacro_display_single_clause, tests/macros::repl_defmacro_display_multi_clause]

When the user defines a macro at the REPL, the display MUST confirm the definition using the universal format (§1.1, §4.1.6):

```
user> (defmacro double [x] `(+ ~x ~x))
:user/double ; defmacro
; [x] -> Sexp

user> (defmacro cond ([x] x) ([x body & rest] `(if ~x ~body (cond ~@rest))))
:user/cond ; defmacro
; [x] -> Sexp
; [x body & rest] -> Sexp
```

This mirrors the definition display pattern established for functions (Section 1.3) and types, keeping the REPL output self-documenting.

### 11.4 Bare Macro Lookup [R3 S11 — tests/ring3_repl::r3_bare_macro_lookup IGNORED]

Entering a macro name as a bare symbol (without arguments) MUST produce output per the universal format (§1.1, §4.1.6). Zero-argument macros are an exception: they expand immediately via bare-symbol expansion (spec Section 9.5) rather than displaying introspection.

```
user> double
:user/double ; defmacro
; [x] -> Sexp

user> cond
:prelude/cond ; defmacro
; [x] -> Sexp
; [x body & rest] -> Sexp
```

### 11.5 Sprint 11 Test Scenarios [R3 S11]

The following test scenarios validate the Ring 3 REPL macro experience. Each MUST have a corresponding test in `tests/`.

| # | Scenario | Expected Behavior | Spec Reference | Test |
|---|---|---|---|---|
| 1 | `/expand` with a single macro | Displays expanded form without evaluation | §11.1, §9.3.2 | [R3 S11 — tests/ring3_repl::r3_expand_single_macro IGNORED] |
| 2 | `/expand` with nested macros | Displays fully expanded form (recursive to fixed point) | §11.1, §9.3.3 | [R3 S11 — tests/ring3_repl::r3_expand_nested_macros IGNORED] |
| 3 | `/expand` with no macro calls | Displays input unchanged | §11.1 | [R3 S11 — tests/ring3_repl::r3_expand_no_macro IGNORED] |
| 4 | `/list` after `defmacro` | Macro appears under "Macros" category | §11.2.1, §3.3 | [Tested tests/ring3_repl::r3_list_macros_category_via_symbol_table] |
| 5 | `/info` on a multi-clause macro | Shows universal format with clause signatures and docstring | §11.2.2 | [Tested tests/ring3_repl::r3_info_macro_clause_count] |
| 6 | `/sig` on a variadic macro | Shows universal format with `& rest` clause signature | §11.2.3 | [Tested tests/ring3_repl::r3_sig_macro_params — variadic IGNORED] |
| 7 | `defmacro` display at REPL | Shows universal format `:module/name ; defmacro` with clause signatures | §11.3, §9.13 | [Tested tests/ring3_repl::r3_defmacro_display_single_clause] |
| 8 | Bare macro name lookup | Shows universal format with clause signatures (non-zero-arg macros) | §11.4, §4.1.6 | [R3 S11 — tests/ring3_repl::r3_bare_macro_lookup IGNORED] |
