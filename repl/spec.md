# REPL Experience Specification

Normative specification for the Cranelisp REPL user experience. A conforming REPL MUST satisfy all requirements tagged with the current ring or earlier.

## Design Principle

> **The REPL reinforces the syntax of the language.** Every output teaches the user how to write Cranelisp.

Output uses the `:Type value` format — the same colon-prefixed type annotation syntax used in the language itself. Names are always fully qualified to teach the module system. Constructors use `Type.Constructor` dot notation (valid input syntax per §1.4.4 of the language spec).

## 1. Display Format

### 1.1 Output Categories

REPL output falls into three categories. The format mirrors Cranelisp type annotation syntax (`:Type expr`).

| Input kind | Format | Example |
|---|---|---|
| Expression result | `:QualifiedType value` | `:primitives/Int 3` |
| Function definition | `:TypeScheme qualified-name` | `:(Fn [a] primitives/Int) user/foo` |
| Type definition | `:qualified/TypeName` | `:user/Color` |
| Symbol lookup | `:TypeScheme qualified-name` | `:(Fn [a] a) user/id` |
| Constructor lookup | `:QualifiedType Type.Constructor` | `:user/Color user/Color.Red` |
| Special form lookup | `:signature name` | `:(Fn [primitives/Bool a a] a) if` |

### 1.2 Expression Results

An expression evaluation MUST display the result in the format:

```
:QualifiedType value
```

Values are runtime results — they have no module scope. The type is always fully qualified.

Examples:

```
:primitives/Int 3
:primitives/Bool true
:primitives/Float 3.14
:user/Color Color.Red
:(user/Option primitives/Int) (Option.Some 42)
:(Fn [a] a) <closure>
```

**Ring 0**: `primitives/Int`, `primitives/Bool`, `primitives/Float`, nullary ADT constructors, non-capturing function values.
**Ring 1**: `primitives/String`, data ADT constructors, closures, `Vec`, `List`.
**Ring 4**: `IO` (trampoline executes; inner value displayed as `:primitives/IO inner_value`).

### 1.3 Definition Results

A function definition MUST display its inferred type scheme and fully-qualified name:

```
:(Fn [a] a) user/id
:(Fn [primitives/Int] primitives/Int) user/double
```

A type definition MUST display the fully-qualified type name:

```
:user/Color
:user/Option
```

**Ring 0**: function definitions, type definitions.
**Ring 2**: constrained functions, overloaded functions.
**Ring 3**: macros.

### 1.4 Type Display

Types MUST be displayed using Cranelisp type notation with fully-qualified names:

| Type | Display |
|---|---|
| Primitive | `primitives/Int`, `primitives/Bool`, `primitives/Float`, `primitives/String` |
| Function | `(Fn [ParamType1 ParamType2] ReturnType)` |
| ADT (no args) | `user/Color` |
| ADT (with args) | `(user/Option primitives/Int)` |
| Type variable | lowercase letter: `a`, `b`, `c`, ... |
| Constrained variable | `:core.numerics/Num a` |

Type names MUST always be fully qualified with their module path. Type variables are bare lowercase — they are not module-scoped.

Polymorphic type schemes MUST display quantified variables as consecutive lowercase letters starting from `a`. Constraints MUST appear inline on first occurrence of the constrained variable.

```
:(Fn [a] a) user/id
:(Fn [:core.numerics/Num a :a] a) core.numerics/+
```

### 1.5 Value Display

Values are runtime results and have no module scope. They are displayed bare.

| Type | Display | Ring |
|---|---|---|
| `Int` | decimal integer (e.g., `42`, `-7`) | 0 |
| `Bool` | `true` or `false` | 0 |
| `Float` | decimal float (e.g., `3.14`) | 0 |
| `String` | `"contents"` with escapes | 1 |
| Nullary constructor | `Type.Ctor` (e.g., `Color.Red`, `Option.None`) | 0 |
| Data constructor | `(Type.Ctor field1 field2 ...)` (e.g., `(Option.Some 42)`) | 1 |
| Closure | `<closure>` | 1 |
| Vec | `[elem1 elem2 ...]` (empty: `[]`) | 1 |
| List | `(list elem1 elem2 ...)` (empty: `List.Nil`) | 1 |
| Seq | `(seq elem1 elem2 ... +more)` (forces up to 20) | 2 |

ADT fields MUST be recursively formatted according to this table.

## 2. Prompt

### 2.1 Primary Prompt

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

### 2.2 Continuation Prompt

When multi-line input is in progress (unmatched parentheses or brackets), the continuation prompt MUST be:

```
{spaces}...
```

Where `{spaces}` aligns the `...` with the start of user input on the primary prompt line.

## 3. Slash Commands

Slash commands provide introspection and navigation. All commands start with `/` and are NOT expressions — they are REPL-only features.

### 3.1 Command Inventory

| Command | Aliases | Description | Ring |
|---|---|---|---|
| `/help` | `/h` | Show available commands and usage | 0 |
| `/sig <name>` | `/s` | Show signature with typed parameters | 0 |
| `/doc <name>` | `/d` | Show docstring | 0 |
| `/type <expr>` | `/t` | Show type without evaluating | 0 |
| `/info <name>` | `/i` | Full details: type, classification, code size, compile time | 0 |
| `/source <name>` | — | Show original source text | 0 |
| `/sexp <name>` | — | Show parsed S-expression | 0 |
| `/ast <name>` | — | Show AST | 0 |
| `/clif <name>` | — | Show Cranelift IR | 0 |
| `/disasm <name>` | — | Show disassembled native code | 0 |
| `/list [filter]` | `/l` | List symbols in current module | 0 |
| `/time <expr>` | — | Evaluate with timing breakdown | 0 |
| `/expand <form>` | `/e` | Macro-expand a form | 3 |
| `/mod [name]` | — | Switch module namespace | 2 |
| `/reload [name]` | `/r` | Reload module from file | 2 |
| `/mem [expr]` | `/m` | Show allocation statistics | 1 |
| `/run-tests` | — | Discover and run test functions | 4 |
| `/quit` | `/q` | Exit REPL | 0 |

### 3.2 `/help` Output

`/help` MUST list all available commands with a brief description. The output MUST be organized by category:

```
Available commands:
  /help (/h)        Show this help
  /sig (/s) <name>  Show signature
  /doc (/d) <name>  Show docstring
  ...
```

Commands not yet available (due to ring) SHOULD be omitted or marked as unavailable.

### 3.3 `/list` Categories

`/list` MUST organize symbols into categories. Names MUST be fully qualified.

| Category | Contents | Ring |
|---|---|---|
| Types | User-defined types (`deftype`) | 0 |
| Special forms | `if`, `let`, `fn`, `defn`, `deftype`, `match` | 0 |
| Functions | User-defined functions | 0 |
| Traits | Trait declarations | 2 |
| Macros | Macro definitions | 3 |
| Modules | Declared submodules | 2 |
| Imports | Imported names | 2 |

An optional filter argument narrows the listing (substring match on name).

### 3.4 `/info` Output

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

| Symbol kind | Response |
|---|---|
| Function | `:TypeScheme module/name` |
| Constructor | `:QualifiedType module/Type.Ctor` |
| Type | Type definition display |
| Special form | `:signature name` |
| Macro | Clause signatures |
| Trait | Method signatures |

Examples:

```
0+0ms; user> id
:(Fn [a] a) user/id
0+0ms; user> Red
:user/Color user/Color.Red
0+0ms; user> +
:(Fn [:core.numerics/Num a :a] a) core.numerics/+
```

No valid name MUST produce an opaque error. If a name is unbound, the error MUST say so clearly.

### 4.2 Special Form Feedback

Special form keywords (`if`, `let`, `fn`, `defn`, `deftype`, `match`, `defmacro`) entered bare MUST produce a function-like type signature, NOT an opaque error. Special forms are not regular functions but displaying their shape teaches the user their syntax.

Examples:

```
0+0ms; user> if
:(Fn [primitives/Bool a a] a) if
0+0ms; user> let
:(Fn [bindings body] a) let
0+0ms; user> defn
:(Fn [name params body] function) defn
```

### 4.3 Operator Feedback

Operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`) are stdlib functions, not builtins. Entering them bare MUST display their type scheme and fully-qualified name showing their stdlib home.

```
0+0ms; user> +
:(Fn [:core.numerics/Num a :a] a) core.numerics/+
0+0ms; user> =
:(Fn [:core.numerics/Eq a :a] primitives/Bool) core.numerics/=
```

In Ring 0 (before traits), the display SHOULD still show the operator's conceptual stdlib home. The implementation-level builtin is a temporary shortcut, not the truth.

## 5. Error Presentation

### 5.1 Error Format

All errors MUST display:

1. The error category (parse error, type error, etc.)
2. The source location (file/line/column or character span)
3. A human-readable message

Errors MUST be written to stderr. They MUST NOT crash the REPL session — the user MUST be able to continue entering expressions after any error.

### 5.2 Error Recovery

After any error (parse, type, runtime), the REPL MUST:
- Display the error
- Reset input state (clear any partial multi-line input)
- Present the prompt for new input

The session state (defined functions, types, modules) MUST NOT be corrupted by an error in a subsequent expression.

### 5.3 Type Error Quality

Type errors MUST include:
- The expected type (fully qualified)
- The actual (inferred) type (fully qualified)
- The source location of the mismatch

Type errors SHOULD suggest common fixes when applicable.

## 6. Discoverability

### 6.1 First Five Minutes

A new user opening the REPL with no prior knowledge MUST be able to:

1. See that `/help` is available (mentioned in the startup banner or prompt)
2. Evaluate a simple expression and see a typed result: `(+ 1 2)` → `:primitives/Int 3`
3. Define a function and see its inferred type: `(defn id [x] x)` → `:(Fn [a] a) user/id`
4. Find available operators and functions via `/list`
5. Get help on any symbol via `/info` or `/sig`

### 6.2 Startup Banner

The REPL MUST display a startup banner including:
- The language name and version
- A hint about `/help`

The banner SHOULD be concise (3 lines or fewer).

### 6.3 Tab Completion

The REPL SHOULD support tab completion for:
- Symbol names (functions, types, constructors)
- Slash commands
- Module names (after `/mod`)

This is a SHOULD, not a MUST, because it depends on the terminal library.

## 7. Performance Targets

### 7.1 Startup Time

The REPL MUST start and display a prompt within **500ms** on a modern machine (defined as: Apple M-series or equivalent x86-64, SSD, 8GB+ RAM). This includes loading the prelude.

### 7.2 Expression Evaluation

Simple expressions (arithmetic, boolean logic, small function calls) MUST evaluate and display within **50ms** of the user pressing Enter. This is the combined compile + eval time.

### 7.3 Prompt Responsiveness

After displaying a result, the next prompt MUST appear within **10ms**. There MUST be no perceptible delay between result display and prompt readiness.

### 7.4 Large Output

When displaying large values (e.g., a Vec with 1000 elements), the REPL SHOULD truncate output with an indication of the total size rather than flooding the terminal. The truncation threshold is implementation-defined but SHOULD be configurable.

## 8. Ring Testability Matrix

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
