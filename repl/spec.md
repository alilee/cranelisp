# REPL Experience Specification

Normative specification for the Cranelisp REPL user experience. A conforming REPL MUST satisfy all requirements tagged with the current ring or earlier.

While called repl, the repl experience encompasses the entire user experience from invoking the repl as well as its associated CLI invocation modes, exit codes, batch output format, and cache lifecycle.

## 0. CLI Invocation Modes

The `cranelisp` binary supports the following invocation modes:

The general invocation form is:

```
cranelisp [target] [--run | --link] [--no-color] [--no-cache] [--priority-workers N] [--nice-workers N]
```

The optional positional `[target]` specifies the project root and entry module (see §0.5). The mode flags (`--run`, `--link`) and the modifier flags (`--no-color`, `--no-cache`) are boolean modifiers and take no parameter; `--priority-workers` and `--nice-workers` each take a numeric argument `N`. Flags modify the behaviour applied to the resolved entry module.

The modifier and worker flags (`--no-color`, `--no-cache`, `--priority-workers`, `--nice-workers`) are detailed in §0.6.

| Mode | Invocation | Description | Status |
|---|---|---|---|
| REPL | `cranelisp [target]` | Interactive REPL (default when no mode flag) | [Tested] |
| Run | `cranelisp [target] --run` | Compile and execute `main`, then exit | [Tested] |
| Link | `cranelisp [target] --link` | Compile and produce linkable object file | [Tested] |
| Version | `cranelisp --version` | Print version string and exit | Future — not implemented (errors `unknown flag` today); see §0.4 |
| Help | `cranelisp --help` | Print usage summary and exit | Future — not implemented (errors `unknown flag` today); see §0.4 |

> The synopsis above is the as-built CLI. There is **no** `--release` flag (it errors `unknown flag`), and `--version`/`--help` are not yet implemented (§0.4). The keep-this-consistent companion is `user/cli-reference.md` — the two MUST agree.

### 0.1 REPL Mode [Tested]

When invoked with no arguments, the binary MUST start the interactive REPL with cwd as the project root and `user` as the entry module: display the startup banner (see Section 6.2), load the prelude, and present the primary prompt. The REPL runs until the user enters `/quit` or sends EOF (Ctrl-D).

When invoked with a positional target (e.g. `cranelisp mymod`, `cranelisp dir/mymod`), the REPL MUST resolve the project root and entry module per §0.5 and start the REPL in that context. [R4 S52]

### 0.2 Run Mode (`--run`) [Tested+Neg tests/sprint23::batch_main_*]

`cranelisp [target] --run` MUST compile the module graph rooted at the resolved entry module, then call `main` in the entry module. The binary MUST NOT print any output itself — all output is produced by IO effects within the program. [R4 S52]

**Entry point resolution:**

1. The entry module MUST define a zero-argument function named `main`.
2. If `main` is not defined in the entry module, the binary MUST print an error to stderr and exit with status code 1. The error message MUST mention that `main` is required.

**Result handling by return type:**

| `main` return type | Behavior |
|---|---|
| `IO _` | Execute through the IO trampoline (side effects happen). The inner type determines the exit code per the exit code rules below. |
| `Int` | Use the value as the process exit code. |
| Any other type | Exit with status code 0. No output. |

**Exit code rules:**

- If the inner result type (after IO unwrapping) is `Int`, the value is used as the process exit code.
- For all other types, exit code is 0.

**Warnings** MUST be printed to stderr. On compilation failure, the error MUST be printed to stderr and the process MUST exit with a non-zero status code.

If the resolved entry module source file does not exist, the binary MUST print an error to stderr and exit with status code 1.

### 0.2.1 Link Mode (`--link`) [R4 S52]

`cranelisp [target] --link` MUST compile the module graph rooted at the resolved entry module and produce a linkable object file. It MUST NOT execute any code and MUST NOT produce output to stdout. [R4 S52]

`--run` and `--link` MUST NOT be used together. If both are present, the binary MUST print an error to stderr and exit with status code 1.

### 0.3 Error Handling

Invalid arguments (e.g., unknown flags, `--run` and `--link` together) MUST print a usage hint to stderr and exit with status code 1. The usage hint MUST show the supported invocation form including the positional target syntax.

### 0.4 Future: `--version` and `--help` [R4]

**Not yet implemented.** As built, `cranelisp --version` and `cranelisp --help` both error `unknown flag: --version` / `unknown flag: --help` (the usage hint to stderr) and exit with status code 1 — they are parsed like any other unrecognised flag (§0.3).

When implemented:

`cranelisp --version` SHOULD print the version string (format: `cranelisp <semver>`) to stdout and exit with status code 0.

`cranelisp --help` SHOULD print a usage summary listing all supported flags and their descriptions to stdout and exit with status code 0.

When added, they MUST follow standard CLI conventions (GNU-style long flags, stdout for informational output, exit code 0 on success).

### 0.5 Positional Target Resolution [R4 S52]

All invocation modes accept an optional positional `[target]` argument that specifies the **project root** and **entry module**. The target MUST be the last argument on the command line, after all flags.

#### 0.5.1 Resolution Rules

The target argument is resolved to a `(project_root, entry_module)` pair according to the following rules, applied in order:

1. **No target**: project root is cwd, entry module is `user`.
2. **Target has a directory component** (contains `/`): the directory portion is the project root, the final component is the entry module name. E.g. `dir/mymod` resolves to project root `dir/`, entry module `mymod`.
3. **Target is an existing directory** (no `/` but the name matches a directory in cwd): project root is that directory, entry module is `user`. E.g. if `myproject/` exists, `cranelisp myproject` resolves to project root `myproject/`, entry module `user`.
4. **Target is a bare name** (no `/`, not an existing directory): project root is cwd, entry module is the target name. E.g. `cranelisp mymod` resolves to project root `.`, entry module `mymod`.

The `.cl` extension MUST be optional in the target. `cranelisp user` and `cranelisp user.cl` MUST be equivalent. If the target ends in `.cl`, the extension MUST be stripped before deriving the entry module name.

The project root MUST be resolved to an absolute path. If a relative path is given, it MUST be resolved against cwd.

#### 0.5.2 Directory Component Detection

A target "has a directory component" when it contains at least one `/` separator. This includes:

- `dir/mymod` — project root `dir/`, entry module `mymod`
- `path/to/mymod` — project root `path/to/`, entry module `mymod`
- `./mymod` — project root `.` (cwd), entry module `mymod`
- `../other/mymod` — project root `../other/`, entry module `mymod`

A bare name like `mymod` does NOT have a directory component, even if a directory named `mymod` exists. The directory-existence check (rule 3) is a separate, lower-priority rule.

#### 0.5.3 Interaction with `--run` and `--link`

The `--run` and `--link` flags are boolean modifiers — they do not take parameters. The positional target is always resolved via §0.5.1 regardless of which mode flag is present. The target may appear before or after the flags: `cranelisp dir/mymod --run` and `cranelisp --run dir/mymod` MUST be equivalent.

#### 0.5.4 Examples [R4 S52]

| Invocation | Project root | Entry module | Notes |
|---|---|---|---|
| `cranelisp` | cwd | `user` | Default: REPL in current directory |
| `cranelisp user` | cwd | `user` | Explicit default module |
| `cranelisp user.cl` | cwd | `user` | `.cl` stripped |
| `cranelisp mymod` | cwd | `mymod` | Bare name, not a directory |
| `cranelisp myproject` | `myproject/` | `user` | `myproject/` is an existing directory |
| `cranelisp dir/mymod` | `dir/` | `mymod` | Directory component present |
| `cranelisp ./mymod` | cwd | `mymod` | Explicit cwd via `./` |
| `cranelisp ../other/app` | `../other/` | `app` | Relative parent path |
| `cranelisp --run` | cwd | `user` | Run mode, default target |
| `cranelisp mymod --run` | cwd | `mymod` | Run mode with target |
| `cranelisp dir/mymod --run` | `dir/` | `mymod` | Run mode with path |
| `cranelisp dir/mymod --link` | `dir/` | `mymod` | Link mode with path |

#### 0.5.5 Error Handling [R4 S52]

1. If the target contains a directory component and the directory does not exist, the binary MUST print an error to stderr naming the missing directory and exit with status code 1.
2. If the resolved entry module source file (`{project_root}/{entry_module}.cl`) does not exist:
   - In REPL mode: the binary SHOULD create an empty source file and proceed. This supports the common workflow of starting a new project from an empty directory.
   - In `--run` mode: the binary MUST print an error to stderr naming the missing file and exit with status code 1.
   - In `--link` mode: the binary MUST print an error to stderr naming the missing file and exit with status code 1.
3. If the target is ambiguous (e.g. both a file `mymod.cl` and a directory `mymod/` exist in cwd), the directory-existence check (rule 3 in §0.5.1) takes precedence — the target is treated as a project root directory. To force module interpretation, use `./mymod`.

#### 0.5.6 Dotted Module Paths [R4 S52]

The positional target supports only file-system paths (`/`-separated), not Cranelisp dotted module paths. To start the REPL in a submodule, use the file-system path:

| Intent | Correct | Incorrect |
|---|---|---|
| Module `app` in `myproject/` | `cranelisp myproject/app` | `cranelisp myproject.app` |
| Submodule `core.str` | `cranelisp core/str` | `cranelisp core.str` |

Dotted names (e.g. `core.str`) MUST be treated as a single module name, not as a path separator. If a user passes `core.str`, the binary resolves it as entry module `core.str` in cwd — which will fail if no file `core.str.cl` exists.

### 0.6 Modifier and Worker Flags

These flags modify behaviour but do not select a mode. They may appear in any mode (subject to the noted incompatibility) and in any position relative to the target.

| Flag | Argument | Effect | Default |
|---|---|---|---|
| `--no-color` | none | Disable ANSI colour in REPL and diagnostic output. | colour on |
| `--no-cache` | none | Bypass the on-disk module cache (recompile from source). **MUST error if combined with `--link`** (link mode relies on the object cache) — usage hint to stderr, exit code 1. | cache on |
| `--priority-workers` | `N` (numeric) | Number of priority compilation workers. A non-numeric `N` is an error (usage hint to stderr, exit code 1). | `1` |
| `--nice-workers` | `N` (numeric) | Number of background ("nice") compilation workers. A non-numeric `N` is an error. | `1` |

This table is kept consistent with `user/cli-reference.md`; the two MUST agree.

## Design Principle

> **The REPL reinforces the syntax of the language.** Every output teaches the user how to write Cranelisp.

Output uses the `:Type value` format — the same colon-prefixed type annotation syntax used in the language itself. Names are always fully qualified to teach the module system. Constructors use `Type.Constructor` dot notation (valid input syntax per §1.4.4 of the language spec).

## 1. Display Format

### 1.1 Universal Output Format [Tested+Neg tests/repl_experience::defn_reports_function_type, tests/wave6_demo_repros::display_defn_with_docstring_uses_dash_separator]

All REPL output uses a unified format that mirrors Cranelisp type annotation syntax. The primary line is always:

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

The type prefix is always fully qualified. The value portion uses the **canonical value display format** defined in [spec §12.9](../spec/12-runtime.md#129-value-display-format). This includes elision rules for large values — the REPL MUST apply the same elision thresholds as all other contexts that use the canonical format.

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

**Ring 4**: `IO` (trampoline executes the effect chain; result displayed as `:(IO InnerType) (IO.Pure inner_value)`, e.g. `:(IO primitives/Int) (IO.Pure 42)`). IO is an ADT and MUST follow the same `Type.Constructor` display format as all other ADTs per [spec §12.9](../spec/12-runtime.md#129-value-display-format).

**Ring 4**: `Trace` — displayed using the standard ADT format per [spec §12.9](../spec/12-runtime.md#129-value-display-format). The REPL does NOT auto-format trace trees — the raw ADT value is shown. Users who want a human-readable indented call tree SHOULD import `core.trace` and call `trace-show-tree`. [R4 S20]

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
| overloaded fn shows all variants | [Tested tests/repl_experience::display_overloaded_fn_shows_all_variants] |

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

### 1.5 Value Display

Values are runtime results and have no module scope. They are displayed bare.

| Type | Display | Ring | Test |
|---|---|---|---|
| `Int` | decimal integer (e.g., `42`, `-7`) | 0 | [Tested tests/repl_experience::display_int_result] |
| `Bool` | `true` or `false` | 0 | [Tested tests/repl_experience::display_bool_true] |
| `Float` | decimal float (e.g., `3.14`) | 0 | [Tested tests/repl_experience::display_float_result] |
| `String` | `"contents"` with escapes | 1 | [Tested tests/e2e::e2e_s1_2_string_display_qualified] |
| Nullary constructor | `Type.Ctor` (e.g., `Color.Red`, `Option.None`) | 0 | [Tested tests/e2e::e2e_s1_5_nullary_ctor_dot_notation] |
| Data constructor (multi-ctor) | `(Type.Ctor field1 field2 ...)` (e.g., `(Option.Some 42)`) | 1 | [Tested tests/e2e::e2e_s1_5_data_ctor_dot_notation] |
| Data constructor (single-ctor, name matches type) | `(Ctor field1 field2 ...)` (e.g., `(Point 3 4)`) | 1 | [Tested tests/ring1::adt_product_construct_and_match] |

| Closure | `<closure>` | 1 | [Tested tests/repl_experience::ring1_closure_display_format] |
| Vec | `[elem1 elem2 ...]` (empty: `[]`) | 1 | [Tested+Neg tests/repl_experience::display_vec_int, tests/repl_experience::display_vec_empty] |
| List | generic ADT recursive form (e.g., `(List.Cons 1 (List.Cons 2 List.Nil))`; empty: `List.Nil`) | 1 | [Tested+Neg tests/repl_experience::display_list_nil, tests/repl_experience::display_list_non_empty_no_truncation_for_small_list] |
| Seq | generic ADT recursive form (e.g., `(Seq.SeqCons h <closure>)`); REPL MUST NOT force-evaluate the lazy tail | 2 | [Tested tests/repl_experience::display_seq_infinite_does_not_hang] |

`Vec` is a compiler-seeded primitive type, so the REPL knows to render it as `[elem1 elem2 ...]`. `List` and `Seq` are stdlib types defined via `deftype`; the REPL renders them through the generic ADT recursive formatter (Type.Constructor + recursive field formatting). The MUST requirement for `Seq` is termination: the REPL displays the constructor and field shape without forcing the lazy tail thunk, so an infinite sequence does not hang the prompt.

> **Aspirational** (not currently required): A future revision MAY introduce a type-directed pretty-printer that recognises `List` and `Seq` and renders them as `(list elem1 elem2 ...)` and `(seq elem1 elem2 ... +more)` (forcing up to a small bound). This would require either (a) a display protocol/trait the stdlib opts into per type, or (b) compiler-seeded recognition of named types from a known stdlib path. No such protocol exists today, so the generic ADT form is normative. These forms are promoted to MUST only once the display-protocol mechanism lands — tracked by `design/arch/fixmes/0050-*.md` (owner `/int`, with `/arch` on the protocol and `/stdlib` on List/Seq opt-in).


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

Per-row annotations below indicate test coverage for each command. Ring 4 introspection commands (`/disasm`, `/time`, `/mod`, `/reload`) are legitimately pending. (`/mem` E2E coverage landed Sprint 58 Wave 5.)

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
| `/expand <form>` | `/e` | Macro-expand a form | 3 | [R3 S16] |
| `/mod [name]` | — | Switch module namespace | 2 | [R4 S10] |
| `/imports [module]` | — | Show imports and special forms; filter by source module | 0 | [Tested+Neg tests/e2e::e2e_s3_4_imports_special_forms, tests/e2e::e2e_s3_4_imports_empty, tests/e2e::e2e_s3_4_imports_empty_neg_no_primitives_leak] |
| `/exports <module>` | — | List a module's importable public symbols | 2 | [Tested tests/e2e::e2e_s3_5_exports_lists_symbols, tests/e2e::e2e_s3_5_exports_no_arg_usage] |
| `/mem [expr]` | `/m` | Show allocation statistics (see §3.7) | 4 | [Tested tests/e2e::mem_command_snapshot_emits_live_and_allocs, tests/e2e::mem_command_delta_runs_expr_and_shows_signed_deltas, tests/e2e::mem_command_baseline_counters_zero_at_start, tests/e2e::mem_command_alias_m_works] |
| `/run-tests [module]` | `/rt` | Discover and run test functions (see §16) | 4 | [R4] |
| `/run-all-tests` | — | Run all tests in project (see §16) | 4 | [R4] |
| `/sh <cmd>` | — | Run a shell command (see §13) | 4 | [R4 S52] |
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

**No imports:** In a fresh session with no explicit `(import ...)` and no prelude, `/imports` MUST show only Special forms. [Tested+Neg tests/e2e::e2e_s3_4_imports_empty, tests/e2e::e2e_s3_4_imports_empty_neg_no_primitives_leak] The `primitives` module's implicit availability is via the module resolution fallback, NOT via import — so primitives do not appear in `/imports` unless explicitly imported.

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

### 3.7 `/mem` — Allocation Statistics [Tested]

`/mem` reports the runtime allocation counters maintained by `cranelisp-runtime`: total allocations observed, total deallocations, and bytes currently live. The command has two shapes — a **snapshot** (no argument) and a **delta** (with an expression argument). Both are comment lines (`;`-prefixed), consistent with the self-documentation convention in §1.5.

**Snapshot — `/mem`** — MUST emit two comment lines:

```
user> /mem
; live: <bytes> bytes (<live-allocs> allocations)
; allocs: <total-allocs>  deallocs: <total-deallocs>
```

- `<bytes>` is `cranelisp_runtime::bytes_current()` — sum of currently-live heap allocations in bytes.
- `<live-allocs>` is `allocs - deallocs` — the number of allocations that have not been freed.
- `<total-allocs>` and `<total-deallocs>` are the cumulative counters since process start.

The two fields between `allocs:` and `deallocs:` are separated by two spaces. The `(<live-allocs> allocations)` group is singular or plural depending on count (the implementation MAY always use `allocations` for simplicity).

**Delta — `/mem <expr>`** — MUST evaluate the expression, print its formatted result on the first line (per §1.2), then emit one comment delta line:

```
user> /mem (list 1 2 3)
:(collections.list/List primitives/Int) (List.Cons 1 (List.Cons 2 (List.Cons 3 List.Nil)))
; delta: allocs +<d-allocs>  deallocs +<d-deallocs>  bytes <±d-bytes>  live <±d-live>
```

- `<d-allocs>`, `<d-deallocs>` are non-negative deltas (prefixed `+`).
- `<d-bytes>` and `<d-live>` are signed deltas (`+`/`-`) because rebinding `it` can release previously-live allocations, making the delta negative.
- Each field is separated from the next by two spaces.

Evaluation errors MUST still emit the delta line — observation is the point, and a failed allocation is itself interesting data. The header line in the error case uses the standard §5 error format.

`/mem` MUST NOT start the runtime; the counters are valid from process start. An empty runtime reports `; live: 0 bytes (0 allocations)` and `; allocs: 0  deallocs: 0`.

| Requirement | Test |
|---|---|
| snapshot emits live + totals | [Tested tests/e2e::mem_command_snapshot_emits_live_and_allocs] |
| delta prints result then delta line | [Tested tests/e2e::mem_command_delta_runs_expr_and_shows_signed_deltas] |
| signed `bytes` and `live` deltas | [Tested tests/e2e::mem_command_delta_runs_expr_and_shows_signed_deltas] |
| baseline counters at process start are zero | [Tested tests/e2e::mem_command_baseline_counters_zero_at_start] |
| `/m` short alias produces snapshot | [Tested tests/e2e::mem_command_alias_m_works] |

## 4. Self-Documentation Contract

Every valid language construct entered at the REPL MUST produce useful feedback. This is the **self-documentation principle** from the project's design principles. All output reinforces the language syntax.

### 4.1 Symbol Lookup — Per-Class Specification

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
| overloaded fn shows all variants | [Tested tests/repl_experience::display_overloaded_fn_shows_all_variants] |

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
| related constructors | [Tested tests/repl_experience::display_type_shows_related_constructors] |
| related trait impls | [Tested+Neg tests/repl_experience::display_type_shows_related_trait_impls, tests/repl_experience::display_type_no_impls_omits_impl_section] |

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
| `defmacro` | [Tested tests/ring3_repl::r3_special_form_defmacro, tests/e2e::e2e_s4_2_special_form_defmacro] |

#### 4.1.6 Macros (defmacro) [Tested]

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
| macro shows clause signatures | [Tested tests/ring3_repl::r3_bare_macro_lookup] |
| multi-clause macro | [Tested tests/ring3_repl::r3_bare_macro_lookup_multi_clause] |

#### 4.1.7 Primitive Functions [Tested+Neg tests/e2e.rs::e2e_s4_1_7_primitive_bare_symbol_lookup, tests/e2e.rs::e2e_s4_1_7_neg_primitive_lookup_not_empty]

Primary line only. Classification `primitive` (distinguishes builtins from user-defined `defn`). Primitives are defined in the `primitives` module.

```
user> add-i64
:(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64 ; primitive - Add

user> str-concat
:(Fn [primitives/String primitives/String] primitives/String) primitives/str-concat ; primitive - Concatenate two strings
```

The classification word `primitive` (rather than `defn`) is intentional: it distinguishes host-implemented builtins from user-defined functions. The builtin's docstring (sourced from [Appendix A.5](../spec/appendix-a-builtins.md#a5-docstrings-for-builtins-r1)) follows the classification in the same `; {classification} - {docstring}` dash form per §1.1.


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

Errors MUST be written to stdout (as part of the REPL conversation flow, visible in piped output and the showcase). Stderr is reserved for traces and diagnostic output. Errors MUST NOT crash the REPL session — the user MUST be able to continue entering expressions after any error. [Tested+Neg tests/e2e::e2e_s5_1_errors_on_stdout, tests/e2e::e2e_s5_1_errors_on_stdout_neg_stderr_empty]

### 5.2 Error Recovery [Tested]

After any error (parse, type, runtime), the REPL MUST:
- Display the error [Tested tests/e2e::e2e_s5_2_error_recovery]
- Reset input state (clear any partial multi-line input)
- Present the prompt for new input

The session state (defined functions, types, modules) MUST NOT be corrupted by an error in a subsequent expression. [Tested+Neg tests/repl_experience::type_error_does_not_corrupt_definitions, tests/repl_experience::type_error_does_not_corrupt_state_neg_failed_defn_absent]

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

Simple expressions (arithmetic, boolean logic, small function calls) MUST evaluate and display within **50ms** of the user pressing Enter. This is the combined compile + eval time. This budget holds regardless of background compilation: the scheduler's priority ladder ranks blocking REPL/typecheck work above non-blocking JIT codegen, so an in-flight prelude or module compile does not starve a trivial REPL submission. The tested 50ms bound (`tests/repl_experience::simple_eval_under_50ms`) is the normative guard; a dedicated REPL-priority work level is not required unless a regression pushes trivial-form latency past this budget under worker contention.

### 7.3 Prompt Responsiveness [R4 S10]

After displaying a result, the next prompt MUST appear within **10ms**. There MUST be no perceptible delay between result display and prompt readiness.

### 7.4 Large Output [Tested tests/e2e.rs::e2e_s7_4_large_vec_output_is_bounded]

When displaying large values (e.g., a Vec with 1000 elements), the REPL SHOULD truncate output with an indication of the total size rather than flooding the terminal. The truncation threshold is implementation-defined but SHOULD be configurable.

## 8. Ring 2B Module Demo Scenarios [R4 S10]

When the module system is fully wired (Ring 2B), these 7 REPL scenarios validate the module experience. Each scenario has a concrete expected behavior.

**Scenario 1: `/mod math` switches namespace**
```
user> /mod math
math>
```
The prompt changes to reflect the active module. Definitions entered now belong to `math`. The `/mod` command MUST NOT print a confirmation message — the prompt change is sufficient feedback.

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

**Scenario 6: `/mod` with no argument resets to `user`**
```
math> /mod
user>
```
Bare `/mod` with no argument switches back to the `user` module. The current module is always visible in the prompt, so a "show current" command is redundant. `/mod` is the quickest way home.

**Scenario 7: Unknown module gives clear error**
```
user> /mod nonexistent
Error: Module 'nonexistent' not found. Use /mod <name> to create a new module.
```
The error message is actionable — it tells the user what to do next.

## 10. Terminal Styling [R4 S22]

When connected to a colour-capable terminal, the REPL MUST apply ANSI styling to distinguish output categories. Styling makes the `:Type value` format scannable — the type prefix, the value, and the classification comment are visually distinct without requiring the user to parse punctuation.

### 10.1 TTY Detection and Suppression [R4 S22]

Colour MUST be enabled by default on capable terminals and suppressed otherwise. The detection logic, in priority order:

1. **`--no-color` flag**: If the `--no-color` CLI flag is present, all ANSI output MUST be suppressed. This flag MUST be accepted alongside other flags (e.g., `cranelisp --no-color`, `cranelisp --run file.cl --no-color`).
2. **`NO_COLOR` environment variable**: If `NO_COLOR` is set to any non-empty value, all ANSI output MUST be suppressed (per https://no-color.org). The value is irrelevant — `NO_COLOR=1`, `NO_COLOR=true`, and `NO_COLOR=` (empty) all suppress except the empty string case: `NO_COLOR=` (set but empty) does NOT suppress.
3. **TTY check**: If stdout is not a terminal (`!isatty(stdout)`), all ANSI output MUST be suppressed. This covers piped output (`cranelisp | less`), redirected output (`cranelisp > log.txt`), and batch mode (`--run`).
4. **Otherwise**: Colour is enabled.

There is no `--color=force` flag. If a user needs colour in piped output (e.g., for `less -R`), they can use a tool like `unbuffer` or `script`. Keeping the implementation simple is more important than covering this edge case.

### 10.2 SGR Escape Convention [R4 S22]

All styling uses ANSI SGR (Select Graphic Rendition) sequences only — no cursor movement, no alternate screen, no 256-colour or truecolor. The palette is restricted to the base 8 colours (30-37) plus bright variants (90-97) and attributes bold (1) and dim (2). This ensures legibility across all terminal emulators, including the macOS default Terminal.app which has limited truecolor support.

Every styled span MUST be terminated by a reset (`\033[0m`) before any newline or before transitioning to a differently-styled span. Unterminated escape sequences corrupt subsequent output and are a conformance failure.

Escape sequences MUST NOT appear inside the value portion of `:Type value` when that value is a String literal — the string content is user data and MUST be printed verbatim.

### 10.3 Colour Palette [R4 S22]

The palette assigns one colour per semantic role. There are no user-configurable themes — the defaults are chosen to work on both light and dark terminal backgrounds using the standard 16-colour ANSI palette.

| Element | Style | SGR Code | Reset | Rationale |
|---|---|---|---|---|
| Prompt (timing + module + `>`) | dim | `\033[2m` | `\033[0m` | Recedes from focus; always visible but never competing |
| Result type (`:Type` prefix) | cyan | `\033[36m` | `\033[0m` | Distinct from value; teaches the type system visually |
| Result value | default | — | — | Primary content; no styling needed |
| Classification comment (`; defn`, `; deftrait`, etc.) | dim | `\033[2m` | `\033[0m` | Metadata — present but subordinate to the type+value |
| Related-symbol comment lines (`; defn:`, `; impl:`, names) | dim | `\033[2m` | `\033[0m` | Secondary information following the primary line |
| Error keyword (`Error:`) | bold red | `\033[1;31m` | `\033[0m` | Immediately noticeable |
| Error detail (message body) | red | `\033[31m` | `\033[0m` | Contextually connected to the error keyword |
| Warning keyword (`Warning:`) | bold yellow | `\033[1;33m` | `\033[0m` | Less urgent than errors, still attention-getting |
| Warning detail | yellow | `\033[33m` | `\033[0m` | Contextually connected to the warning |
| Slash command category headers (`Fns:`, `Types:`, etc.) | bold | `\033[1m` | `\033[0m` | Anchors for scanning `/list`, `/imports`, `/exports` |
| Slash command body (symbol names, info lines) | default | — | — | Dense informational content; styling would add noise |
| Startup banner | dim | `\033[2m` | `\033[0m` | One-time context; should not dominate |

Notes on specific choices:

- **No green for comments.** The earlier draft used green for `;` comment lines. However, REPL output comment lines (`;`) carry structured information (classifications, related symbols) — they are not "comments" in the source-code sense. Dim is more appropriate: it creates a visual hierarchy (type = cyan, value = default, metadata = dim) without introducing a third saturated colour.
- **Bold for category headers only.** Bold is reserved for structural anchors (category names in `/list` output, error/warning keywords). Using bold elsewhere dilutes its signal.
- **No colour on user input.** The line editor controls input styling. The REPL MUST NOT emit escape sequences into the input buffer.

### 10.4 Styled Universal Output Format [R4 S22]

The universal output format (§1.1) with styling applied. Angle brackets show styled spans; actual output uses SGR codes, not brackets.

**Expression result:**
```
<cyan>:primitives/Int</cyan> 42
```

**Definition with classification and docstring:**
```
<cyan>:(Fn [primitives/Int] primitives/Int)</cyan> user/double <dim>; defn - Multiply by 2</dim>
```

**Type with related symbols:**
```
<cyan>:user/Color</cyan> <dim>; deftype</dim>
<dim>; match:</dim>
<dim>;  Red Green Blue</dim>
```

**Error:**
```
<bold-red>Error:</bold-red> <red>Unbound symbol 'foo'</red>
```

**Slash command `/list`:**
```
<bold>Types:</bold>
  Color Point
<bold>Fns:</bold>
  double area
```

The reset between the cyan type prefix and the default-styled value is the space character — no visible break, just a colour transition. The classification comment (everything from `; ` onward on the primary line) is a single dim span.

### 10.5 Batch Mode Output [R4 S22]

Batch mode (`--run`) writes to stdout which is typically not a TTY. Per §10.1, ANSI sequences MUST be suppressed. The `:Type value` format is emitted as plain text. Error messages to stderr MUST also be plain text in batch mode (stderr TTY status is checked independently — if stderr is a TTY but stdout is not, errors MAY be styled on stderr).

### 10.6 Showcase Player Styling [R4 S22]

The showcase player (`repl/showcase`) MAY apply the same colour palette during replay. Specifically:

- Prompt lines SHOULD use dim styling, matching the REPL prompt.
- Simulated user input SHOULD use default (no styling) — matching the visual weight of real typing.
- Output lines SHOULD be styled using the same rules as §10.3 (cyan for types, dim for comments, red for errors).
- The `[paused]` indicator SHOULD use dim styling.
- The showcase player MUST respect `NO_COLOR` and TTY detection using the same logic as the REPL (§10.1), minus the `--no-color` flag (the player has its own invocation interface).

### 10.7 Implementation Notes [R4 S22]

The styling layer SHOULD be implemented as a small module (e.g., `src/style.rs`) that provides a `Style` enum and a `styled(text, style) -> String` function. When colour is disabled, `styled` returns the text unchanged. All REPL output code calls `styled` — there are no raw `\033[` literals scattered through the codebase.

The TTY detection result SHOULD be computed once at startup and stored as a boolean. Checking `isatty()` on every line would be wasteful and could produce inconsistent output if stdout is redirected mid-session (which is not a supported scenario but should not cause crashes).

**Ring 4 Sprint 22**: Full terminal styling specification. Implementation targeted for a subsequent sprint.

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
| `/mod` | | | yes | | |
| Demo trampoline | | | | | yes |
| `/mem` | | yes | | | |
| `/run-tests`, `/run-all-tests` | | | | | yes |
| Shell escape (`/sh`) | | | | | yes |
| File watching | | | | | yes |
| Self-documentation | bare symbol, special forms, operators (qualified) | | + traits, modules | + macros | |
| Error recovery | yes | | | | |
| Startup < 500ms | yes | | | | |
| Eval < 50ms (simple) | yes | | | | |
| Fully-qualified names | all output | | | | |
| `Type.Constructor` notation | yes | | | | |

## 11. Ring 3 REPL Requirements [Tested tests/e2e.rs::e2e_s11_1_expand_single_macro]

Ring 3 introduces the macro system. The REPL MUST integrate macros into all existing introspection and display mechanisms so that macros are first-class citizens of the self-documentation experience.

### 11.1 `/expand` Command [Tested+Neg tests/e2e.rs::e2e_s11_1_expand_single_macro, tests/e2e.rs::e2e_s11_1_neg_expand_non_macro_unchanged]

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

### 11.2 Macro Introspection [Tested tests/ring3_repl::r3_list_macros_category_via_symbol_table]

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

#### 11.2.3 `/sig` — Macro Signature [Tested tests/ring3_repl::r3_sig_macro_params, tests/ring3_repl::r3_sig_macro_variadic]

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

#### 11.2.4 `/doc` — Macro Docstring [Tested tests/ring3_repl::r3_macro_no_docstring, tests/e2e::e2e_s11_2_4_doc_macro_no_docstring, tests/e2e::e2e_s11_2_4_doc_macro_with_docstring]

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

### 11.4 Bare Macro Lookup [Tested tests/ring3_repl::r3_bare_macro_lookup, tests/ring3_repl::r3_bare_macro_lookup_multi_clause]

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
| 1 | `/expand` with a single macro | Displays expanded form without evaluation | §11.1, §9.3.2 | [Tested tests/e2e.rs::e2e_s11_1_expand_single_macro] |
| 2 | `/expand` with nested macros | Displays fully expanded form (recursive to fixed point) | §11.1, §9.3.3 | [Tested tests/e2e.rs::e2e_s11_1_expand_nested_macros] |
| 3 | `/expand` with no macro calls | Displays input unchanged | §11.1 | [Tested+Neg tests/e2e.rs::e2e_s11_1_expand_no_macro, tests/e2e.rs::e2e_s11_1_neg_expand_non_macro_unchanged] |
| 4 | `/list` after `defmacro` | Macro appears under "Macros" category | §11.2.1, §3.3 | [Tested tests/ring3_repl::r3_list_macros_category_via_symbol_table] |
| 5 | `/info` on a multi-clause macro | Shows universal format with clause signatures and docstring | §11.2.2 | [Tested tests/ring3_repl::r3_info_macro_clause_count] |
| 6 | `/sig` on a variadic macro | Shows universal format with `& rest` clause signature | §11.2.3 | [Tested tests/ring3_repl::r3_sig_macro_variadic] |
| 7 | `defmacro` display at REPL | Shows universal format `:module/name ; defmacro` with clause signatures | §11.3, §9.13 | [Tested tests/ring3_repl::r3_defmacro_display_single_clause] |
| 8 | Bare macro name lookup | Shows universal format with clause signatures (non-zero-arg macros) | §11.4, §4.1.6 | [Tested tests/ring3_repl::r3_bare_macro_lookup] |

## 12. Demo Trampoline [R4 S23]

The demo player (§10.6) SHOULD support `/quit` within a demo script by restarting the REPL process and continuing with the remaining script lines. This allows demo scripts to demonstrate session restart naturally:

```
; Define something
(defn foo [] 42)
(foo)
; Restart and show it's gone
/quit
; New session starts here
foo
; error: undefined symbol 'foo'
```

When the demo player detects that the REPL process has exited (due to `/quit` or EOF), it SHOULD start a new REPL process and pipe the remaining demo lines into it. The demo ends when the script is exhausted, not when the first REPL exits.

## 13. Shell Escape [R4 S52]

The REPL supports a `/sh` slash command for running operating system commands without leaving the REPL session. This is useful for checking file contents, running external tools, or verifying output during iterative development.

### 13.1 Syntax [R4 S52]

The shell escape command is `/sh <command>`:

```
user> /sh ls -la
```

`/sh` follows the same slash-command convention as all other REPL commands (§3). Everything after `/sh` and optional whitespace is the shell command string.

### 13.2 Execution [R4 S52]

The command string (everything after `/sh` and optional whitespace) MUST be passed to the system shell for execution. On Unix-like systems, this means invoking `/bin/sh -c "<command>"`. The REPL MUST NOT attempt to parse or interpret the command itself.

The command runs synchronously — the REPL blocks until the command completes. The REPL prompt is not displayed until the command finishes.

### 13.3 Output Handling [R4 S52]

The command's stdout and stderr MUST be passed through directly to the terminal. The REPL does NOT capture, buffer, or reformat the output. The user sees exactly what the command produces, interleaved as the OS delivers it.

```
user> /sh echo "hello from shell"
hello from shell
0+0ms; user>
```

### 13.4 Exit Code Display [R4 S52]

If the command exits with a non-zero status, the REPL MUST display the exit code after the command output:

```
user> /sh false
exit status: 1
0+0ms; user>
```

If the command exits with status 0, no exit code is displayed — silence means success.

If the command is terminated by a signal (e.g., SIGKILL), the REPL SHOULD display the signal information:

```
user> /sh kill -9 $$
killed by signal: 9
0+0ms; user>
```

### 13.5 No REPL State Interaction [R4 S52]

Shell escape is a pure passthrough. The command MUST NOT affect REPL state in any way:
- No variables, definitions, or imports are modified.
- The current module is unchanged.
- The typechecker, code cache, and compilation state are untouched.
- Environment variables set by the command do NOT propagate back to the REPL process (the command runs in a child process).

### 13.6 Edge Cases [R4 S52]

**No arguments:** `/sh` with no command (or only whitespace) MUST print a usage hint: `Usage: /sh <command>`. [R4 S52]

```
user> /sh
Usage: /sh <command>
0+0ms; user>
```

**Command not found:** If the shell cannot find the command, the shell's own error message is passed through (since stdout/stderr are not captured). The exit code is displayed per §13.4.

```
user> /sh nonexistent-command
/bin/sh: nonexistent-command: command not found
exit status: 127
0+0ms; user>
```

**Multi-line:** Shell escape does NOT support continuation lines. Each `/sh` invocation is a self-contained command. For multi-statement commands, use shell syntax (e.g., `/sh echo a && echo b`).

**Timing:** The prompt after a shell escape MUST show `0+0ms` — shell commands are not Cranelisp evaluations and do not contribute to compile/eval timing.

### 13.7 `/help` Integration [R4 S52]

`/sh` MUST appear in `/help` output as:

```
  /sh <cmd>       Run a shell command
```

## 14. File Watching [R4 S23]

The REPL automatically detects when source files change on disk, eagerly recompiles the affected modules, and notifies the user of the result. The developer edits files in their editor, saves, and the REPL immediately recompiles — no manual reload command needed.

### 14.1 Watch Scope [R4 S23]

The file watcher MUST monitor directories that contain source files actually loaded during the current session. This includes:
- The project root directory (if one was determined at startup).
- Directories of modules loaded via `(import ...)` or `/mod`, and their transitive dependencies.

The watcher SHOULD use OS-level filesystem notification (e.g., `FSEvents` on macOS, `inotify` on Linux) rather than polling. This provides near-instant detection without CPU overhead.

New files in watched directories SHOULD be detected, but they do not trigger any action until they are referenced by an import or module load.

The watcher MUST NOT watch directories that have not been imported. Stdlib directories are watched only if the prelude or a user module actually imported from them.

### 14.2 Eager Recompilation [R4 S23]

When a `.cl` source file is modified (content change, not just metadata/timestamp), the watcher MUST:

1. **Identify the module.** Map the changed file path to its module identity in the module graph.
2. **Clear old module state.** Remove the module's previous definitions from the typechecker, trait registry, and symbol tables so that recompilation does not conflict with existing definitions.
3. **Recompile immediately.** Re-read, re-parse, re-typecheck, and re-compile the module. Update GOT entries so callers get the new code.
4. **Cascade to dependents.** Dependents of the changed module MUST also be recompiled in topological order.
5. **Notify the user of the result.** Display `[updated: <file>]` on success or `[errors: <file>]` on failure (see §14.3).

Recompilation is **eager** — it happens as soon as the change is detected (at the next poll opportunity, before the next prompt), not deferred until the module is accessed.

Content hash comparison MUST be used to skip metadata-only changes (e.g., `touch foo.cl`). The watcher records the content hash of each source file when it is first loaded and compares against it on each filesystem event. Only true content changes trigger recompilation.

### 14.3 Notification Format [R4 S23]

The recompilation result IS the notification. There is no separate `[changed: ...]` message.

**On success:**

```
0+0ms; user> (+ 1 2)
:primitives/Int 3
[updated: math.cl]
0+0ms; user>
```

The format is `[updated: <file>]` where `<file>` is the path relative to the project root. If multiple modules were recompiled (including cascade dependents), each gets its own notification line.

**On failure:**

```
0+0ms; user> (+ 1 2)
:primitives/Int 3
[errors: math.cl]
  math.cl:5:3 — type error: expected Int, got String
0+0ms; user>
```

The format is `[errors: <file>]` followed by the error details on indented lines. The error details use the standard error format (§5.1).

**Input preservation (nice-to-have):** If the user is mid-input when a notification arrives, the notification SHOULD print on a new line, then reinstate the partial input line so typing is uninterrupted. Implementation MAY use rustyline's `ExternalPrinter` API for this. As an interim approach, notifications MAY be deferred until the next prompt boundary (before the prompt is printed). Notifications MUST NOT corrupt the user's input.

### 14.4 Error Blocking [R4 S23]

When a module fails to recompile, the REPL MUST block further evaluation until the error is resolved:

1. The module is added to the session's error set.
2. Before evaluating any expression, the REPL checks the error set. If non-empty, it refuses evaluation with a message: `Cannot evaluate: module '<name>' has errors. Fix the source file and save.`
3. Slash commands (`/help`, `/quit`, etc.) remain available during error blocking — only expression evaluation is blocked.
4. When the source file is modified again (presumably with a fix), the watcher triggers another recompilation attempt. If recompilation succeeds, the module is removed from the error set, and evaluation resumes normally. If it fails again, the error set is updated with the new error.

There is **no last-known-good fallback**. Source code diverging from runtime behavior is dangerous — the user must see the error and fix it. The error blocking ensures they cannot accidentally evaluate code that depends on a broken module.

```
[errors: math.cl]
  math.cl:5:3 — type error: expected Int, got String
0+0ms; user> (+ 1 2)
Cannot evaluate: module 'math' has errors. Fix the source file and save.
0+0ms; user>
;; User fixes math.cl and saves...
[updated: math.cl]
0+0ms; user> (+ 1 2)
:primitives/Int 3
```

### 14.5 Module State on Error [R4 S23]

When a module fails to recompile:

1. The old module state has already been cleared (§14.2 step 2).
2. The module is in an error state — its definitions are unavailable.
3. The error set prevents evaluation from proceeding (§14.4).
4. The module remains watched. The next file modification triggers another recompilation attempt.

This "errors block" approach is preferable to "last-known-good" because it prevents the dangerous situation where the source file says one thing but the runtime does another. The user is forced to address the error before continuing.

### 14.6 Clearing Errors [R4 S23]

Error-locked modules (§14.4) are cleared when the offending file is fixed and saved — the watcher detects the change, recompiles successfully, and removes the module from the error set. The user can also restart the REPL (`/quit`) to clear all state.

### 14.7 Interaction with Object Cache [R4 S23]

File watching and the object cache work together:
- Recompilation invalidates and replaces cache entries for changed modules.
- Unchanged modules continue to use their cached `.o` files.
- Failed recompilations do NOT update the cache — the stale cache entry remains until a successful recompilation replaces it.

This means that after editing one file, only that file and its dependents are recompiled — unchanged modules load instantly from cache.

## 15. REPL Session Persistence [R4 S52]

### 15.1 Source Regeneration [R4 S52]

The REPL MUST persist interactive definitions to disk by maintaining a backing `.cl` file for the entry module (e.g. `user.cl`). When the user enters a definition that compiles successfully:

1. The definition MUST be compiled and installed in the session. [R4 S52]
2. The entry module's backing `.cl` file MUST be **regenerated** atomically from the module's current state. The regeneration is performed by the REPL after eval — it is not part of the compilation or `.o` caching pipeline. [R4 S52]

The regenerated source file MUST be valid, parseable Cranelisp source — loading it through the normal module graph pipeline MUST reproduce the same session state. [R4 S52]

Definitions that fail to compile MUST NOT trigger regeneration — the backing file reflects only the last successfully compiled state. [R4 S52]

### 15.2 Session Restore [R4 S52]

On REPL startup, the entry module's backing `.cl` file MUST be loaded through the normal module graph pipeline (with cache hit for fast restore). Definitions from the previous session MUST survive restart — the user resumes where they left off. [R4 S52]

If the backing file does not exist (first session, or user deleted it), the REPL MUST start with an empty module. [R4 S52]

### 15.3 Unified Development Model [R4 S52]

This design unifies interactive and file-based development:
- Interactive definitions are source files that happen to be managed by the REPL.
- File watching (§14) applies uniformly — external edits to the backing file MUST be picked up by the watcher and recompiled.
- The object cache (§14.7) accelerates both imported modules and the user's own work.

### 15.4 Regeneration Integrity [R4 S52]

The regenerated source file MUST satisfy the following invariants:

1. **Round-trip correctness:** Loading the regenerated file through the compiler MUST produce the same types, values, and module exports as the interactive session. [R4 S52]
2. **Authorship ordering:** Definitions MUST appear in the order they were registered with the session — file-loaded modules in source declaration order; REPL-introduced symbols appended in the order they were entered. Redefinition MUST NOT reorder; a redefined symbol keeps its original position. Cranelisp's cluster-atomic typecheck handles forward references natively, so dependency ordering is not a correctness requirement — the regenerated file reflects authorship intent. [R4 S52]
3. **Symbol qualification preservation:** The regenerated source MUST preserve the user's original qualification style. If the user wrote a fully-qualified reference (`core.option/Some`), it MUST remain fully-qualified. If the user wrote a bare name (`Some`) that was resolved via an import, it MUST remain bare. The regenerator MUST NOT rewrite bare names to qualified or vice versa. [R4 S52]
4. **Structural sections at top in fixed order:** Structural sections MUST appear at the top of the regenerated file in this fixed order: (a) platforms — `(declare-platform ...)` forms; (b) submodules — `(mod ...)` declarations; (c) exports — `(export ...)` forms; (d) imports — `(import ...)` forms. Within each section, items appear in authorship order (file parse order + REPL append). Definitions follow the four structural sections. [R4 S52]
5. **Comments:** The behaviour of comments in regenerated source is unspecified. The implementation MAY strip comments, preserve them, or handle them in any other way. [R4 S52]
6. **Source in cache metadata:** The `.meta.json` cache file MUST include all source text needed for regeneration, so that the REPL can restore the backing file from cache alone. [R4 S52]
7. **Authorship-intent rationale:** The regeneration invariants above (authorship ordering, fixed structural-section order, redef in place) collectively express a single intent — *principle of least surprise*. The regenerated file is a faithful record of what the user typed and when, not a derived form computed from compilation properties. The compiler's pipeline already handles forward references and dependency resolution; regeneration's job is authorship fidelity, not re-deriving correctness. [R4 S52]

### 15.5 File Watching Integration [R4 S52]

The file watcher (§14) MUST ignore writes triggered by the REPL's own source regeneration. Self-triggered writes MUST NOT cause a recompilation cycle. External edits to the backing file (e.g. from a text editor) MUST be detected and recompiled normally. [R4 S52]

### 15.6 Redefinition [R4 S52]

When the user redefines a name that already exists in the session, the regenerated source file MUST contain only the latest definition — the previous definition MUST be replaced, not duplicated. [R4 S52]

## 16. Test Discovery and Execution [R4]

The REPL provides commands for discovering and running test functions. Test infrastructure rests on two ordinary `primitives`-module entries — `discover-tests` and `catch-runtime-error` — plus the existing macro system. Both parse as plain applications, type by ordinary scheme resolution, and require import or FQ reference like any other `primitives` name (zero frontend and zero typecheck special-casing). Everything above them — selection, filtering, iteration, result interpretation, reporting, timing — is ordinary in-language code in the stdlib.

See `design/arch/test-discovery.md` (SETTLED, fourth convergence) for the full subsystem design.

### 16.1 Test Function Convention

A **test function** is any zero-argument function whose name begins with `test-` and whose return type is exactly `(Fn [] (Option String))`:

- `None` — the test passed
- `Some(reason)` — the test failed, with a human-readable reason string

There is no module naming requirement. Test functions may be defined in any module. A `test-`prefixed function whose scheme is not exactly `(Fn [] (Option String))` is **excluded from discovery and warned** at discovery time, so a mistyped test cannot silently masquerade as "no failures."

### 16.2 Slash Commands

#### 16.2.1 `/run-tests [module]` [R4]

Discover and run test functions. With no argument, searches the current module. With a module path argument, searches that module. The command is sugar over the in-language runner (§16.5).

```
user> /run-tests
  test-add ................................ ok
  test-div-zero .......................... FAILED: expected error

1 passed, 1 failed in 2.34ms
```

```
user> /run-tests user.math.test
  test-factorial ......................... ok

1 passed in 0.45ms
```

On failure, the trace tree for the failing test MUST be displayed after the failure reason (see §16.4).

#### 16.2.2 `/run-all-tests` [R4]

Discover and run all test functions in all loaded modules whose source files are under the project root. Library modules (discovered through the lib search path) are excluded.

```
user> /run-all-tests
  user/test-add .......................... ok
  user.math/test-factorial ............... ok
  user.io/test-read ...................... FAILED: file not found

2 passed, 1 failed in 5.67ms
```

### 16.3 The Primitives

`discover-tests` and `catch-runtime-error` are ordinary `primitives`-module symbols — imported (or FQ-referenced) like any other primitive, not special forms and not always-in-scope root names.

**`discover-tests`** — discovery primitive:

```
discover-tests              :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; current module
discover-tests "mod.path"   :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; named module (String arg)
discover-tests ["a" "b"]    :: (IO (Vec (Pair String (Fn [] (Option String)))))   ; union over a Vec of module paths
```

Returns one `(Pair name callable)` per eligible `test-*` function:

- **`name`** — the fully-qualified test name `"module/test-name"` as a `String`, for selection, sorting, and reporting.
- **`callable`** — a language fn value of type `(Fn [] (Option String))` that, when invoked, performs a **GOT-slot-indirect call** to the test. The wrapper closes over the test's GOT slot, not a baked code pointer, so a *redefined* test runs its current body.

**Freshness.** The callables are late-bound GOT-slot wrappers. Calling `discover-tests` again re-scans live state: a `test-*` defined after a previous call is included on the next call, and a redefined test runs its new body. Selection and reporting compose over these values and stay fresh by construction — freshness lives in the returned values, not in expansion timing. (This is why discovery returns callables, not a `(Vec String)` of names threaded through a macro runner, which would freeze the test set at the macro's expansion time. The macro-runner approach is retired.)

The three call shapes are one underlying extern taking `(Vec String)`; the no-arg form (current module) and single-`String` form are stdlib-macro sugar normalising to the `Vec` form. The module argument is an ordinary value — a `String` or a `(Vec String)`, not a bare module path.

`Pair` and `Result` are seeded as primitives bootstrap types (alongside `Option`), so both are available to discovery results and to `catch-runtime-error`.

**`catch-runtime-error`** — protected-call combinator:

```
catch-runtime-error :: forall a. (Fn [(Fn [] a)] (Result a String))
```

Promoted out of the test feature to a standalone `primitives` entry usable by any user code and by the stdlib — it is the language's only way to turn a runtime panic into a value. It invokes the thunk on the calling thread; if the thunk hit a language-level runtime error (match non-exhaustion, division by zero, vec out-of-bounds), it clears the error slot and returns `(Err message)`; otherwise it returns `(Ok result)`.

`TestResult`, `TestPass`, `TestFail`, and `run-test` are **retired**: a test's outcome is its own `(Option String)` (`None` = pass, `Some reason` = fail); the FQ name lives in the discovered `Pair`; timing comes from `trace`'s nanos.

### 16.4 Tracing Failures

The slash commands do NOT automatically trace failing tests. To trace a failing test, use `(trace (test-fn))` at the REPL:

```
user> /run-tests
  test-factorial ......................... FAILED: expected 120, got 0

0 passed, 1 failed in 1.23ms
user> (trace (test-factorial))
;; => Trace ADT with full call tree
```

Trace and test are independent, composable features — the user decides when tracing overhead is worthwhile.

### 16.5 Programmatic Use

The in-language runner is ordinary code — no macro. `discover-tests` returns `(name, callable)` pairs; `catch-runtime-error` brackets each callable; the runner folds a three-way outcome per test over the resulting `(Result (Option String) String)`:

- `(Err msg)` — the test panicked (match non-exhaustion, div-by-zero, …)
- `(Ok None)` — the test passed
- `(Ok (Some why))` — the test ran and reported an assertion failure

```clojure
(import [primitives [discover-tests catch-runtime-error]])

;; Run one discovered test: returns a human-readable line.
(defn run-one [pair]
  (match pair
    [(Pair name run)
     (match (catch-runtime-error run)
       [(Err msg)        (str-concat name " PANIC: " msg)]
       [(Ok None)        (str-concat name " ok")]
       [(Ok (Some why))  (str-concat name " FAIL: " why)])]))

;; Run every test in the current module.
(defn run-all []
  (map run-one (discover-tests)))

;; Run only the tests whose name contains a substring — selection is in-language,
;; over the SAME pairs, and stays fresh because the callables are late-bound.
(defn run-matching [substr]
  (map run-one
       (filter (fn [p] (match p [(Pair nm _) (contains? nm substr)])) (discover-tests))))
```

`catch-runtime-error` is usable by any code, not just tests:

```clojure
(import [primitives [catch-runtime-error]])

;; Try a risky computation; recover with a default on panic.
(defn safe-div [a b]
  (match (catch-runtime-error (fn [] (/ a b)))
    [(Ok q)   q]
    [(Err _)  0]))           ; division by zero panicked — recover with 0
```

Standard library convenience functions (e.g., `format-test-run`, `failures-only`, `test-passed?`) MAY be provided in a `core.testing` module but are not required by this specification.

### 16.6 `--link` Interim Behaviour

`discover-tests` is **REPL / `--run` only**. A `--link` build of a program that calls `discover-tests` is accepted at compile time, but the missing host symbol surfaces as an unresolved-symbol failure at link/load (the standalone executable has no live session to scan). This is documented interim behaviour — no friendly rejection yet; a future sprint may add a diagnostic.

`catch-runtime-error`, by contrast, **works in all modes including `--link`**: it is a self-contained intrinsic (it calls a closure already present in the linked program and constructs a `Result` heap value — no live session needed). Error capture is a pure runtime capability available everywhere; discovery is a dev-session capability.
