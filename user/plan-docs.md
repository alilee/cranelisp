# Documentation Plan

Plan for user-facing Cranelisp documentation. Produced by `/docs` during Sprint 0, updated after persona and tutorial design review.

## Persona

> **Sam** is 12 years old and curious about how computers work. They've played games and used apps but never written code. They're motivated — they want to make things, not just use things. They're comfortable with basic arithmetic and the idea of variables from math class. They don't know any programming terms: "function," "type," "expression," "recursion" are all new words. They don't know what a Lisp is. They learn best by doing, not reading. They need to see results immediately and feel progress.

This persona drives every documentation decision:
- Never assume prior programming knowledge
- Introduce terms before using them — "function" needs explanation, not just demonstration
- Parentheses-first syntax gets a positive framing in lesson 1: "everything is an expression, and expressions look like `(operation arguments)`"
- No "if you know X, this is like Y" — Sam doesn't know X
- Short sections, immediate feedback, sense of progression
- The REPL is the primary learning environment, not a document

## Design Principles

1. **Teach programming, not a programming language.** The tutorial teaches what computation, values, names, decisions, and abstraction *are* — using Cranelisp as the vehicle. It does not teach "how Cranelisp differs from X."
2. **The REPL is the classroom.** The tutorial is built into the REPL as an interactive `/learn` command. The student never leaves the environment where they experiment.
3. **Socratic method.** The REPL asks questions. The student answers by typing expressions. The REPL validates the result and advances. Learning happens through doing, not reading.
4. **Consistent output from day one.** REPL output always uses the full `:primitives/Int 3` format with qualified names. No simplified mode. The student absorbs the pattern before they understand it, and there is no surprise when modules are introduced later.
5. **Docstrings in output.** REPL responses include docstrings to aid comprehension. Typing `Int` shows `primitives/Int ; Integer numbers between -100 billion and 100 billion`. Every builtin, type, constructor, and special form has a docstring.
6. **Progressive disclosure.** Sections follow concept dependencies (what you must understand before the next thing), not language feature lists or ring order.

## The `/learn` System

> **FIXME**: This example is more verbose than we want. Really just want to ask a one-line or short question in a comment without any explanation, so the steps will need to be really small increments. Section metadata should include a list of forms or literals that can be used with `/learn +` or `/learn if` or `/learn deftype` to route to a section so no menu. Bare `/learn` should start or resume at the last unfinished section. 

### User Experience

```
user> /learn
Learn Cranelisp

  1. Int              ; whole numbers
  2. Float            ; decimal numbers
  3. Bool             ; true and false
  4. arithmetic       ; adding, subtracting, multiplying
  5. comparison       ; is this bigger than that?
  6. naming           ; giving names to values
  ...

Type /learn 1 to start, or /learn next for the next section.

user> /learn 1

── 1. Int ─────────────────────────────────────

Cranelisp knows about different kinds of values.
The simplest are whole numbers, called Int.

; what is 3?
user> 3
:primitives/Int 3
; the REPL shows two things:
;   primitives/Int — the kind of value (a whole number)
;   3              — the value itself
; what is -42?
user> -42
:primitives/Int -42
; what is Int?
user> Int
primitives/Int ; Integer numbers between -100 billion and 100 billion
; section Int complete!
; next section: Float
; what is 3.0?
user>
```

### Data Structure

Each tutorial step is a tuple:

```
section:  "Int"
prompt:   "; what is 3?"
trigger:  3           ; any expression producing this value advances
answer:   "3"         ; shown by /answer
```

- **section**: topic group name
- **prompt**: the question displayed to the student (prefixed with `;` so it looks like a comment)
- **trigger**: the value that means "correct" — any expression producing this value works. `(+ 1 2)` and `3` and `(- 5 2)` all satisfy trigger `3`. The student can be creative.
- **answer**: the intended expression, shown when the student types `/answer`

### Mechanism

- `/learn <section>` activates a section and displays the first prompt
- `/learn next` advances to the next recommended section
- `/learn` with no argument shows the section list with completion status
- `/answer` displays the answer, evaluates it (so the student sees the output), and advances to the next prompt
- `/skip` skips the current prompt without answering
- A **watch** on the REPL checks every evaluation result against the current trigger. Match → display success message and next prompt. No match → normal REPL output, student can try again.
- Between prompts, the student can type anything — the REPL works normally. The watch is passive.
- Progress is stored locally (e.g. `.cranelisp/learn-progress`) so the student can resume across sessions.

### Trigger Types

Most sections use value triggers (result equals a specific value). Later sections need richer triggers:

| Trigger kind | Checks | Example use |
|---|---|---|
| Value | Result equals expected value | "what is (+ 3 4)?" → trigger: `7` |
| Type | Result has expected type | "make a Float" → trigger: type is `Float` |
| Name | A name exists with expected type | "define a function called double" → trigger: `double` exists with type `(Fn [Int] Int)` |
| Match | Result matches a pattern | "make a list with 3 elements" → trigger: result is a 3-element Vec |

Value triggers cover the first ~15 sections. Richer triggers are introduced as needed.

### Ownership

- `/docs` owns the curriculum content (section definitions, prompts, triggers, answers) in `user/tutorial/`
- `/repl` owns the `/learn` experience specification (how the command works, display format, progress tracking) — added to `repl/spec.md`
- `/qa` owns the implementation (the watch mechanism, trigger evaluation, progress persistence in `src/repl/`)

## Curriculum

Sections are ordered by concept dependency — what you need to understand before the next thing. Ring constraints determine when content can be *implemented* (tested against a working compiler), but the pedagogical order is independent.

### Foundation (Ring 0)

| # | Section | Teaches | Questions |
|---|---|---|---|
| 1 | `Int` | Whole numbers exist, REPL shows their type | 3–4 |
| 2 | `Float` | Decimal numbers are a different kind | 3–4 |
| 3 | `Bool` | true/false, a third kind of value | 3–4 |
| 4 | `arithmetic` | `(+ 1 2)` — parentheses pattern, operations, nesting | 5–7 |
| 5 | `comparison` | `=`, `<`, `>` — comparing values, results are Bool | 4–5 |
| 6 | `naming` | `let` — giving names to values, using them | 5–7 |
| 7 | `choices` | `if` — doing different things based on a condition | 4–6 |
| 8 | `recipes` | `defn` — naming a computation you can reuse | 5–7 |
| 9 | `calling` | Calling functions, functions calling functions | 4–6 |
| 10 | `your-types` | `deftype` — making your own kinds of things (enums) | 5–7 |
| 11 | `matching` | `match` — looking at what kind of thing you have | 5–7 |
| 12 | `self-reference` | Recursion — a recipe that uses itself | 5–7 |
| 13 | `counting-down` | Recursive patterns: countdown, factorial | 4–6 |

### Data (Ring 1)

| # | Section | Teaches | Questions |
|---|---|---|---|
| 14 | `text` | Strings — values that hold text | 4–5 |
| 15 | `data-types` | Product types — things with parts (fields) | 5–7 |
| 16 | `sum-types` | Sum types — things that could be one of several shapes | 5–7 |
| 17 | `maybe` | `Option` — when something might not exist | 5–7 |
| 18 | `matching-data` | Pattern matching on data constructors (field access) | 5–7 |
| 19 | `collections` | `Vec` — a collection of many values | 5–7 |
| 20 | `lists` | `List` — another way to collect values | 4–6 |
| 21 | `functions-as-values` | Passing functions to other functions (`fn`, closures) | 5–7 |
| 22 | `map-filter-reduce` | Transforming collections with functions | 5–7 |

### Abstraction (Ring 2)

| # | Section | Teaches | Questions |
|---|---|---|---|
| 23 | `shared-behavior` | Traits — types that can do the same thing (`Display`) | 5–7 |
| 24 | `implementing` | `impl` — teaching a type how to do something | 5–7 |
| 25 | `generic-functions` | Constrained polymorphism — functions that work on any type with a trait | 4–6 |
| 26 | `organizing` | Modules — splitting code into files | 5–7 |
| 27 | `importing` | `import` — using code from other modules | 4–6 |

### Modules Detail (Ring 2) — Getting-Started Section Outline

Sections 26 and 27 of the curriculum ("organizing" and "importing") cover modules interactively. The getting-started guide needs a companion reference section. Outline:

#### 1. Creating Modules with `(mod name)`
- A module is a named container for definitions
- `(mod util)` in a file tells the compiler that `util.cl` exists alongside the current file
- REPL: `/mod math` switches the current namespace to `math`

#### 2. File Resolution Rules
- `(mod util)` looks for `util.cl` in the same directory as the declaring file
- Root modules resolve from the project root or `lib/` directory
- Submodules use directory nesting: `(mod core.math)` resolves to `core/math.cl`

#### 3. Importing with `(import [...])`
- `(import [util [double triple]])` — selective import of specific names
- `(import [util [*]])` — glob import of all exported names
- Imported names become available as bare names in the current scope

#### 4. Exporting with `(export [...])`
- `(export [double triple])` — only these names are visible to importers
- Without an explicit export, all public definitions are visible
- Controls the public API of a module

#### 5. Qualified Name Access
- Any name can be accessed via its module path: `util/double`, `core.math/sqrt`
- Qualified access works without importing — only requires the module to be loaded
- The REPL always displays fully-qualified names: `:(Fn [a] a) util/id`

#### 6. Private Definitions with `defn-`
- `(defn- helper [x] (+ x 1))` — private, not exported or accessible via qualified name
- Use for internal implementation details that callers should not depend on

### Meta (Ring 3)

| # | Section | Teaches | Questions |
|---|---|---|---|
| 28 | `code-as-data` | Macros — programs that write programs | 5–7 |
| 29 | `derive` | Automatic trait implementations | 3–5 |

### Effects (Ring 4)

| # | Section | Teaches | Questions |
|---|---|---|---|
| 30 | `outside-world` | IO — talking to the outside world | 5–7 |
| 31 | `sequencing` | `do`/`bind!` — doing IO steps in order | 5–7 |
| 32 | `programs` | `main`, batch mode, platforms | 4–6 |
| 33 | `testing` | Writing and running tests | 4–6 |

**~33 sections, ~160 questions total.** Each section takes 5–10 minutes. The full curriculum is ~4–6 hours of interactive learning.

## Docstrings

The REPL includes docstrings in output for types, builtins, constructors, and special forms. This is a REPL spec change (for `/repl` to add to `repl/spec.md`).

**Format**: docstring appears after a semicolon on the same line.

```
user> Int
primitives/Int ; Integer numbers between -100 billion and 100 billion

user> +
:(Fn [primitives/Int primitives/Int] primitives/Int) primitives/+ ; Add two numbers

user> if
:(Fn [primitives/Bool a a] a) if ; Choose between two values based on a condition

user> Color.Red
:user/Color user/Color.Red ; A Color value
```

This means every builtin type, primitive function, special form, and user-defined type/function needs a docstring. The `defn` form already supports docstrings: `(defn add "Add two numbers" [x y] (+ x y))`. Builtins and special forms need docstrings registered by the compiler.

<!-- FIXME(/repl): RESOLVED — docstring display is already specified in repl/spec.md §4.1 (bare symbol lookup appends first line of docstring as "; comment") and tagged Ring 2 at §4.1 line 286. No additional spec work needed. -->

<!-- FIXME(/arch): RESOLVED. The architecture already provides `docstring: Option<String>` on `ModuleEntry::Def` (interfaces.md line 635) and `description: String` on `DefKind::SpecialForm` (line 699). Populating these fields with actual docstring text during `register_builtins()` is an implementation task for `/typecheck` (primitives module seeding) and `/qa` (REPL display verification). No architectural change needed. -->

## Directory Structure

```
user/
  CLAUDE.md                     # ownership + writing conventions (exists)
  plan-docs.md                  # this file
  getting-started.md            # installation → run cranelisp → type /learn
  tutorial/
    CLAUDE.md                   # tutorial content conventions
    curriculum.md               # section/prompt/trigger/answer definitions (or .cl data file)
  guide/
    CLAUDE.md                   # guide conventions + section ordering
    lexical.md                  # tokens, comments, commas-as-whitespace
    types.md                    # type system overview, inference, annotations
    expressions.md              # all expression forms, evaluation rules
    definitions.md              # defn, deftype, deftrait, impl, defmacro
    pattern-matching.md         # match syntax, exhaustiveness
    traits.md                   # trait system, Display, Num, Eq, Ord, Functor
    modules.md                  # module system, imports, exports, visibility
    macros.md                   # macro system, Sexp model, expansion
    io.md                       # IO model, platforms, do, bind!
    collections.md              # Vec, List, Seq, unified API
    runtime.md                  # RC, heap layout, calling conventions
    repl.md                     # REPL usage, slash commands, introspection
    stdlib.md                   # prelude, core modules, naming conventions
  errors/
    CLAUDE.md                   # error catalog conventions
    parse-errors.md             # reader and grammar errors
    type-errors.md              # unification failures, constraint violations
    runtime-errors.md           # match exhaustion, index out of bounds, panics
```

### Rationale

- **`getting-started.md`** is short: install, start the REPL, type `/learn`. One page.
- **`tutorial/`** contains the curriculum data (section definitions with prompts, triggers, answers). This is content consumed by the REPL's `/learn` engine, not standalone reading material.
- **`guide/`** is reference documentation for practitioners who've completed the tutorial. 13 sections cover the full language surface. This serves the "second audience" — experienced programmers who want to look things up.
- **`errors/`** is an error message catalog. Three files cover parse, type, and runtime errors.

## Getting-Started Outline

### `user/getting-started.md`

Short. Gets Sam from zero to `/learn` in under 5 minutes.

#### 1. What is Cranelisp?

One paragraph, no jargon: "Cranelisp is a programming language. You type instructions, and the computer follows them. Cranelisp checks your instructions for mistakes before running them, so you find problems early."

#### 2. Installation

- Prerequisites: Rust toolchain
- Clone, build
- Verify: `cranelisp --version`

#### 3. Start the REPL

- Run: `cranelisp`
- "You'll see a prompt. This is where you type instructions."
- "Type `/learn` to start the interactive tutorial."

#### 4. What's Next

- `/learn` for the interactive tutorial
- `/help` to see all commands
- `user/guide/` for reference (when you're ready)

That's it. Everything else happens inside the REPL via `/learn`.

## Guide Section Plan

The guide serves a different audience from the tutorial: someone who has completed `/learn` (or is an experienced programmer) and wants reference documentation. 13 sections, each rewriting a spec area for users.

| Guide Section | Spec Source | Ring | Content Focus |
|---|---|---|---|
| `lexical.md` | 01 | 0 | Tokens, comments, commas, string escapes, operator symbols, dot notation |
| `types.md` | 03 | 0–2 | Type system overview, inference, annotations, type variables, constraints |
| `expressions.md` | 04 | 0–1 | All expression forms: literals, `let`, `if`, `fn`, application, `match` |
| `definitions.md` | 05 | 0–3 | `defn`, `deftype`, `deftrait`, `impl`, `defmacro`, `mod` |
| `pattern-matching.md` | 06 | 0–1 | Match syntax, pattern kinds, exhaustiveness rules, nested patterns |
| `traits.md` | 07 | 2 | Trait declarations, implementations, derive, method resolution |
| `modules.md` | 08 | 2 | File mapping, `mod`/`import`/`export`, search order, prelude |
| `macros.md` | 09 | 3 | Sexp model, defmacro, quasiquote, expansion rules |
| `io.md` | 10 | 4 | IO type, pure/bind/do, platform DLLs, auto IO scheduling |
| `collections.md` | 11 | 1–2 | Vec, List, Seq, unified API |
| `runtime.md` | 12 | 1+ | Value representation, RC semantics, calling conventions |
| `repl.md` | repl/spec | 0 | REPL usage, all slash commands, `/learn`, self-documentation |
| `stdlib.md` | 11 | 3–4 | Prelude contents, core modules, naming conventions |

## Error Catalog Plan

Three files covering all error categories. Each entry has:
- **Error message** (exact text)
- **When it occurs** (common cause, written for Sam — no jargon)
- **How to fix** (with example)
- **Example** (REPL transcript showing the error and fix)

### `errors/parse-errors.md`

| Error Category | Examples |
|---|---|
| Unmatched parentheses/brackets | `(+ 1 2`, `[1 2` |
| Invalid token | `@foo`, `#bar` |
| Invalid literal | unterminated string |
| Unexpected form | `(defn 42 ...)` |
| Missing required elements | `(defn)`, `(if true)` |

### `errors/type-errors.md`

| Error Category | Examples |
|---|---|
| Type mismatch | `(+ 1 true)`, `(if 42 ...)` |
| Unbound variable | `(+ x 1)` |
| Arity mismatch | `(+ 1 2 3)` |
| Occurs check failure | `(defn f [x] (x x))` |
| Missing trait implementation | `(+ "a" "b")` |
| Exhaustiveness failure | match missing arm |

### `errors/runtime-errors.md`

| Error Category | Examples |
|---|---|
| Match exhaustion (runtime) | non-exhaustive match at runtime |
| Index out of bounds | `(vec-get [1 2] 5)` |
| Integer overflow | arithmetic overflow |
| Stack overflow | unbounded recursion |

## Concept Inventory

Full inventory of concepts from `spec/` sections 01–12, mapped to tutorial sections and guide entries.

### Ring 0 Concepts (Core)

| Concept | Spec | Tutorial Section | Guide |
|---|---|---|---|
| Integer literals, arithmetic | 01, 04.1 | 1 (Int), 4 (arithmetic) | lexical, expressions |
| Float literals, arithmetic | 01, 04.1 | 2 (Float), 4 (arithmetic) | lexical, expressions |
| Boolean literals, `not` | 01, 04.1 | 3 (Bool) | lexical, expressions |
| Operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`) | A.3 | 4 (arithmetic), 5 (comparison) | expressions |
| `let` bindings | 04.3 | 6 (naming) | expressions |
| `if` conditional | 04.4 | 7 (choices) | expressions |
| `defn` / `defn-` | 05.1.1 | 8 (recipes) | definitions |
| Function application | 04.6 | 9 (calling) | expressions |
| `deftype` (enum) | 05.2 | 10 (your-types) | definitions |
| `match` (enum patterns) | 06 | 11 (matching) | pattern-matching |
| Recursion, TCO | 04.8 | 12–13 (self-reference, counting-down) | expressions |
| Type inference (HM) | 03.1–3.3 | passive (REPL output) | types |
| Comments | 01.2 | within prompts | lexical |

### Ring 1 Concepts (Heap)

| Concept | Spec | Tutorial Section | Guide |
|---|---|---|---|
| String literals | 01.3.4 | 14 (text) | lexical, expressions |
| `deftype` (product, sum) | 05.2 | 15–16 (data-types, sum-types) | definitions |
| `Option` type | 11 | 17 (maybe) | collections |
| `match` (data patterns) | 06.2 | 18 (matching-data) | pattern-matching |
| `Vec` type | 03.2.4, A.3 | 19 (collections) | collections |
| `List` type | 03.2, 11 | 20 (lists) | collections |
| Closures, `fn` | 04.5, 12.1.3 | 21 (functions-as-values) | expressions |
| Higher-order functions | 04.6 | 22 (map-filter-reduce) | expressions |
| Auto-currying | 04.7 | 22 | expressions |

### Ring 2 Concepts (Abstraction)

| Concept | Spec | Tutorial Section | Guide |
|---|---|---|---|
| `deftrait` | 07.1 | 23 (shared-behavior) | traits |
| `impl` | 07.3 | 24 (implementing) | traits |
| Constrained polymorphism | 03.5, 07.6 | 25 (generic-functions) | traits, types |
| Modules | 08 | 26–27 (organizing, importing) | modules |

### Ring 3 Concepts (Meta)

| Concept | Spec | Tutorial Section | Guide |
|---|---|---|---|
| `defmacro` | 09.2 | 28 (code-as-data) | macros |
| `derive` | 07.13 | 29 (derive) | traits |

### Ring 4 Concepts (Effects)

| Concept | Spec | Tutorial Section | Guide |
|---|---|---|---|
| IO type | 10.1 | 30 (outside-world) | io |
| `do`, `bind!` | 10.4, 10.5 | 31 (sequencing) | io |
| `main`, batch mode, platforms | 10.6, 10.7 | 32 (programs) | io |
| Testing | — | 33 (testing) | repl |

## Per-Ring Deliverables

### Ring 0

- `user/getting-started.md` — complete
- `user/tutorial/curriculum.md` — sections 1–13 (Foundation)
- `/learn` engine implemented by `/qa` (basic value triggers)

### Ring 1

- `user/tutorial/curriculum.md` — sections 14–22 (Data)
- Guide sections: `lexical.md`, `expressions.md`, `pattern-matching.md` (drafts)

### Ring 2

- `user/tutorial/curriculum.md` — sections 23–27 (Abstraction)
- Guide sections: `traits.md`, `modules.md`, `types.md` (drafts)

### Ring 3

- `user/tutorial/curriculum.md` — sections 28–29 (Meta)
- Guide sections: `macros.md`, `stdlib.md` (drafts)

### Ring 4

- `user/tutorial/curriculum.md` — sections 30–33 (Effects)
- All guide sections complete
- Error catalog complete
- Full curriculum polished and tested

## Writing Conventions

1. **Voice**: Second person ("you"), active voice, present tense
2. **Tone**: Friendly, encouraging, never condescending. Written for a motivated 12-year-old.
3. **No jargon without introduction**: The first time a term is used (function, type, recursion, etc.), explain it in plain language.
4. **No cross-language comparisons**: Never "if you know X, this is like Y." Sam doesn't know X.
5. **REPL prompts**: Tutorial prompts are prefixed with `;` (comment syntax). The student absorbs that `;` means "not code" naturally.
6. **Consistent output**: All examples use full `:primitives/Int 3` format with qualified names. No simplified mode.
7. **Error examples**: When an error naturally occurs in the curriculum, show it, explain it kindly, show the fix.

## Usability Findings (Pre-Ring 0)

Filed as FIXMEs on the relevant documents:

1. **Category**: Learning curve. **Severity**: Important. **Description**: The getting-started guide cannot show a "hello world" batch program at Ring 0 because batch mode requires IO (Ring 4). The `/learn` system makes this less painful — the student starts with `/learn` instead of "write a file and run it." But hello-world is a universal expectation. Consider whether a minimal batch mode that prints `main`'s return value could be available at Ring 0.

2. **Category**: REPL feature. **Severity**: Important. **Description**: The `/learn` system requires a REPL feature (watch mechanism, trigger evaluation, progress tracking). This is not just documentation content — it's REPL implementation work. `/qa` needs to plan this as a Ring 0 deliverable so the tutorial is available from the first release.

<!-- Finding 1 → FIXME(/arch) on design/arch/roadmap.md (U0.1). Finding 2 → FIXME(/qa) on tests/plan/ring0.md (U0.2). -->

## Dependencies and Coordination

| Dependency | From Skill | Needed For |
|---|---|---|
| `/learn` engine implementation | `/qa` | Tutorial must work in the REPL |
| `:Type value` display with docstrings | `/repl` | Tutorial comprehension |
| Builtin docstrings registered | `/arch` | REPL docstring display |
| Pipeline wired (`compile_unit()`) | `/qa` | Ring 0 tutorial sections must evaluate correctly |
| Example numbering and files | `/examples` | Tutorial section alignment |
| Stdlib function names | `/stdlib` | Later tutorial sections, guide stdlib section |
| Error message text | `/frontend`, `/typecheck`, `/backend` | Error catalog entries |

## Next Skills

- `/repl` — Add docstring display to REPL output spec. Add `/learn` command to REPL spec (experience specification for the interactive tutorial).
- `/qa` — Implement the `/learn` engine: watch mechanism, trigger evaluation, progress persistence. Plan this as a Ring 0 deliverable.
- `/arch` — Register docstrings for all builtin types, primitive functions, and special forms.
- `/examples` — Tutorial section alignment: the `/learn` curriculum may subsume or complement the standalone examples. Coordinate numbering.
- `/port` — The exemplar project is the capstone. See `exemplar/plan-exemplar.md`.
