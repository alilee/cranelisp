# REPL Experience Specification

Normative specification for the Cranelisp REPL user experience. A conforming REPL MUST satisfy all requirements tagged with the current ring or earlier.

<!-- FIXME(/repl): DEFERRED to Ring 4. CLI invocation modes (--run, --version, --help),
     exit codes, batch output format, and cache lifecycle are CLI-level concerns, not REPL
     experience concerns. They should be specified in a companion CLI spec (owned by /qa or /arch)
     once the REPL experience itself is stable. The REPL spec intentionally covers only the
     interactive session contract. -->

## Design Principle

> **The REPL reinforces the syntax of the language.** Every output teaches the user how to write Cranelisp.

Output uses the `:Type value` format — the same colon-prefixed type annotation syntax used in the language itself. Names are always fully qualified to teach the module system. Constructors use `Type.Constructor` dot notation (valid input syntax per §1.4.4 of the language spec).

## 1. Display Format

### 1.1 Output Categories [R2 S8]

<!-- FIXME(/qa): Bare type name lookup is untested. Typing `Int` at the REPL produces
     "undefined variable: Int" instead of `:primitives/Int`. The special_form_feedback()
     function only searches the current module's symbol table — primitive types like Int,
     Bool, Float, String live in the `primitives` module and aren't found. Need a test
     for each row of the §1.1 category table, and the bare symbol lookup needs to search
     imported modules (including primitives). -->

REPL output falls into three categories. The format mirrors Cranelisp type annotation syntax (`:Type expr`).

| Input kind | Format | Example | Test |
|---|---|---|---|
| Expression result | `:QualifiedType value` | `:primitives/Int 3` | [Tested tests/e2e::e2e_s1_2_int_display_qualified] |
| Function definition | `:TypeScheme qualified-name` | `:(Fn [a] primitives/Int) user/foo` | [Tested tests/e2e::e2e_s1_3_defn_shows_qualified_name] |
| Type definition | `:qualified/TypeName` | `:user/Color` | [Tested tests/e2e::e2e_s1_1_bare_type_user_defined] |
| Symbol lookup | `:TypeScheme qualified-name` | `:(Fn [a] a) user/id` | [Tested tests/e2e::e2e_s4_1_bare_symbol_lookup] |
| Constructor lookup | `:QualifiedType Type.Constructor` | `:user/Color user/Color.Red` | [R2 S8] |
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

<!-- FIXME(/qa): U1.6 — Polymorphic ADT type variables display as internal names (e.g. t1)
     instead of source-level names from deftype (e.g. a). REPL shows :(Option t1) None instead
     of :(Option a) None. format_result_value should normalize type vars to match source-level
     names from TypeDefInfo. Source: /docs. Severity: important. -->

<!-- FIXME(/qa): U1.9 — Polymorphic ADT fields with heap types display raw pointers instead of
     formatted values. (Some "hello") shows (Some 40383875776) instead of (Some "hello").
     format_adt_heap_value reads field types from TypeDefInfo as Type::Var(a) — needs to build
     substitution map from type_params to type_args before formatting fields. Source: /repl.
     Severity: important. -->
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

### 1.5 Value Display

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

### 3.1 Command Inventory

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
| `/expand <form>` | `/e` | Macro-expand a form | 3 | [R3 S9] |
| `/mod [name]` | — | Switch module namespace | 2 | [R2 S8] |
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

### 3.3 `/list` Categories [R2 S8]

`/list` MUST organize symbols into categories. Names MUST be fully qualified.

| Category | Contents | Ring | Test |
|---|---|---|---|
| Types | User-defined types (`deftype`) | 0 | [Tested tests/e2e::e2e_s3_3_list] |
| Special forms | `if`, `let`, `fn`, `defn`, `deftype`, `match` | 0 | [R2 S8] |
| Functions | User-defined functions | 0 | [Tested tests/e2e::e2e_s3_3_list] |
| Traits | Trait declarations | 2 | [R2 S8] |
| Macros | Macro definitions | 3 | [R3 S9] |
| Modules | Declared submodules | 2 | [R2 S8] |
| Imports | Imported names | 2 | [R2 S8] |

An optional filter argument narrows the listing (substring match on name).

### 3.4 `/info` Output [Tested tests/e2e::e2e_s3_4_info]

`/info <name>` MUST display multi-line details using the `:Type name` format:

```
:(Fn [primitives/Int] primitives/Int) user/double
  (defn double [x] (* x 2))
  48 bytes, 2ms
```

For overloaded functions, all variants MUST be listed. For constrained functions, specializations MUST be shown.

## 4. Self-Documentation Contract

Every valid language construct entered at the REPL MUST produce useful feedback. This is the **self-documentation principle** from the project's design principles. All output reinforces the language syntax.

### 4.1 Bare Symbol Lookup

Entering a symbol name without arguments MUST produce its type and fully-qualified name:

| Symbol kind | Response | Test |
|---|---|---|
| Function | `:TypeScheme module/name` | [Tested tests/e2e::e2e_s4_1_bare_symbol_lookup] |
| Constructor | `:QualifiedType module/Type.Ctor` | [R2 S8] |
| Type | Type definition display | [R2 S8 — tests/e2e::e2e_s1_1_bare_type_int IGNORED] |
| Special form | `:signature name` | [Tested tests/e2e::e2e_s4_2_special_form_feedback] |
| Macro | Clause signatures | [R3 S9] |
| Trait | Method signatures | [R2 S8] |

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

### 4.2 Special Form Feedback

Special form keywords (`if`, `let`, `fn`, `defn`, `deftype`, `match`, `defmacro`) entered bare MUST produce a function-like type signature, NOT an opaque error. Special forms are not regular functions but displaying their shape teaches the user their syntax.

| Form | Test |
|---|---|
| `if` | [Tested tests/e2e::e2e_s4_2_special_form_feedback] |
| `let` | [Tested tests/e2e::e2e_s4_2_special_form_let] |
| `fn` | [R2 S8] |
| `defn` | [R2 S8] |
| `deftype` | [R2 S8] |
| `match` | [R2 S8] |
| `defmacro` | [R3 S9] |

Examples:

```
0+0ms; user> if
:(Fn [primitives/Bool a a] a) if
0+0ms; user> let
:(Fn [bindings body] a) let
0+0ms; user> defn
:(Fn [name params body] function) defn
```

### 4.3 Operator Feedback [R2 S8]

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

## 8. Ring 2B Module Demo Scenarios [R2 S8]

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

**Scenario 5: `/list` shows module symbols**
```
math> /list
Fns: foo
```
The `/list` command in a module shows only that module's definitions, not the global scope.

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
