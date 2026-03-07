# Ring 3 Macro Implementation Plan

Implementation plan for the Cranelisp macro system in the reimplementation. Covers 7 phases from synthetic module seeding through REPL polish. Implementation begins Sprint 10; this document is the Sprint 9 deliverable.

## Architecture Summary

The macro system adds a compile-time transformation layer between reading and AST building. Macro bodies are ordinary Cranelisp functions (`Sexp -> Sexp` or `(SList Sexp) -> Sexp`) compiled with the full pipeline (typecheck + backend) and invoked during expansion. The key architectural constraint is **dependency inversion**: the `MacroExpander` trait is defined in `cranelisp-types`, the AST builder in `cranelisp-frontend` consults it, and the binary crate (`cranelisp`) provides the real implementation that wires typecheck + backend.

```
Source text
  --> [Reader]           cranelisp-frontend/reader.rs
  --> Sexp tree
  --> [MacroExpander]    cranelisp (binary) -- CranelispExpander struct
  --> Expanded Sexp
  --> [AST Builder]      cranelisp-frontend/ast_builder.rs
  --> AST
  --> [TypeChecker]      cranelisp-typecheck
  --> [Backend]          cranelisp-backend
  --> Execute
```

**Critical constraint**: Macro bodies are compiled during sequential form processing in the pipeline orchestrator (binary crate), NOT during AST building. The `expand()` method only invokes already-compiled function pointers. The AST builder never triggers compilation -- it merely asks "is this a macro?" and "expand it."

## Sketch Reference

The sketch's macro system lives in `sketch/src/macro_expand.rs` (~1955 lines) and `sketch/src/marshal.rs` (~315 lines). Key functions to study:

| Function | Lines | Purpose |
|----------|-------|---------|
| `parse_defmacro` | 363-467 | Extract name, docstring, clauses from Sexp |
| `synthesize_macro_clause_defn` | 469-519 | Build a `Defn` with arg destructuring match chain |
| `build_macro_param_chain` | 522-655 | Nested match for SCons peeling + bracket destructure |
| `compile_macro` | 796-859 | Typecheck + compile each clause, verify return type |
| `expand_quasiquotes` | 1263-1299 | Top-level quasiquote desugaring |
| `expand_qq_template` | 1115-1202 | Recursive quasiquote template expansion |
| `expand_sexp` | 1300-1393 | Recursive macro call expansion with depth limit |
| `call_clause_fn` | 864-870 | Marshal args, invoke, unmarshal result |
| `clause_matches` | 873-908 | Arity + structural pattern checking |
| `dispatch_macro` | 911-926 | Try clauses in order, call first match |

The reimplementation should NOT copy the sketch. It should use the sketch to de-risk design decisions and inform requirements, then build from first principles against the spec and the reimplementation's crate architecture.

## Phase 1: Synthetic `macros` Module + Marshal Infrastructure

**Goal**: Seed the `macros` module with `SList` and `Sexp` ADTs at startup; implement marshal functions for converting between Rust `Sexp` values and runtime ADT representations.

### Files to Create

| File | Crate | Content |
|------|-------|---------|
| `crates/cranelisp-runtime/src/marshal.rs` | runtime | `sexp_to_runtime()`, `runtime_to_sexp()`, tag constants, `alloc_adt()`, `build_runtime_list()`, `read_runtime_list()` |

### Files to Modify

| File | Crate | Change |
|------|-------|--------|
| `crates/cranelisp-runtime/src/lib.rs` | runtime | Add `pub mod marshal` |
| `crates/cranelisp-typecheck/src/builtins.rs` | typecheck | Add `register_macros_module()` to seed `SList`/`Sexp` type defs and constructors in a synthetic `macros` module |
| `crates/cranelisp-types/src/module.rs` | types | Add `rest_param: Option<Symbol>` to `MacroClauseInfo` (per `/arch` design note) |

### Key Functions

- `register_macros_module(tc: &mut TypeChecker)` -- Register `SList` (SNil, SCons) and `Sexp` (7 variants) as type definitions in a synthetic `macros` module. Follows the same pattern as `register_primitives_module()`.
- `sexp_to_runtime(sexp: &Sexp) -> i64` -- Allocate heap `Sexp` ADT values from a Rust `Sexp` tree. Each node is a heap cell `[tag, field0, ...]`.
- `runtime_to_sexp(val: i64) -> Sexp` -- Read heap to reconstruct a Rust `Sexp` from a runtime ADT value. All output spans are `Span::SYNTHETIC`.
- `build_runtime_list(items: &[i64]) -> i64` -- Build an SList from a slice of i64 values (SNil = 0, SCons = heap `[1, head, tail]`).

### Tag Constants

```rust
// SList tags (SList is polymorphic, but at runtime tags are fixed)
pub const TAG_SNIL: i64 = 0;   // nullary constructor
pub const TAG_SCONS: i64 = 1;  // data constructor: [1, head, tail]

// Sexp tags (all data constructors, no nullary)
pub const TAG_SEXP_INT: i64 = 0;
pub const TAG_SEXP_FLOAT: i64 = 1;
pub const TAG_SEXP_BOOL: i64 = 2;
pub const TAG_SEXP_STR: i64 = 3;
pub const TAG_SEXP_SYM: i64 = 4;
pub const TAG_SEXP_LIST: i64 = 5;
pub const TAG_SEXP_BRACKET: i64 = 6;
```

Note: Tag assignment order MUST match the constructor order in the `deftype` registration. The spec lists `SexpInt` first (tag 0), but the sketch uses `SexpSym` as tag 0. The reimplementation should follow the spec's ordering (Section 9.1.2) to maintain consistency: `SexpInt=0, SexpFloat=1, SexpBool=2, SexpStr=3, SexpSym=4, SexpList=5, SexpBracket=6`.

### Dependencies

- `/typecheck`: Must expose the same `register_type_def()` / `register_constructor()` paths used for user `deftype`. The `macros` module must be registered AFTER `primitives` (it references `Int`, `Bool`, `Float`, `String` types).
- `/backend`: `alloc_with_rc()` from `cranelisp-runtime/src/alloc.rs` is needed for heap allocation in marshal. Also `alloc_string()` for `SexpSym`/`SexpStr` variants.

### Estimated Scope

~300 lines: marshal.rs (~180 lines), builtins.rs additions (~80 lines), module.rs changes (~20 lines), tests (~20 lines).

---

## Phase 2: Quasiquote Expansion Engine

**Goal**: Implement the quasiquote desugaring pass that transforms template syntax (`` ` ``, `~`, `~@`) into explicit `Sexp` constructor calls. This runs at the Sexp level, before AST building.

### Files to Create

| File | Crate | Content |
|------|-------|---------|
| `crates/cranelisp-frontend/src/quasiquote.rs` | frontend | `expand_quasiquotes()`, `expand_qq_template()`, `expand_quote_template()`, auto-gensym support |

### Files to Modify

| File | Crate | Change |
|------|-------|--------|
| `crates/cranelisp-frontend/src/lib.rs` | frontend | Add `pub mod quasiquote` and re-export `expand_quasiquotes` |

### Key Functions

- `expand_quasiquotes(sexp: &Sexp) -> Result<Sexp, CranelispError>` -- Top-level entry: walk a Sexp tree, recognizing `(quasiquote ...)` and `(quote ...)` forms, and desugar them into explicit constructor calls.
- `expand_qq_template(template: &Sexp, depth: usize, gensym_map: &mut HashMap<String, String>) -> Sexp` -- Recursive quasiquote template expansion. At depth 0, `(unquote x)` passes `x` through; `(unquote-splicing x)` produces `sconcat` calls. At depth > 0 (nested quasiquote), forms are structurally quoted.
- `expand_quote_template(template: &Sexp) -> Sexp` -- Pure structural quotation: every form becomes its `Sexp` constructor. No unquote handling.
- `make_gensym_name(base: &str) -> String` -- Generate unique symbol name using `SYNTHETIC_SPAN_COUNTER`.

### Quasiquote Expansion Rules

Per spec Section 9.4.2, within a quasiquoted form:

| Input | Output |
|-------|--------|
| `42` | `(macros/SexpInt 42)` |
| `3.14` | `(macros/SexpFloat 3.14)` |
| `true` | `(macros/SexpBool true)` |
| `"hello"` | `(macros/SexpStr "hello")` |
| `foo` | `(macros/SexpSym "foo")` |
| `~expr` | `expr` (passed through, must be `Sexp`) |
| `~@expr` | splice via `sconcat` (must be `(SList Sexp)`) |
| `(a b c)` | `(macros/SexpList (macros/SCons <a> (macros/SCons <b> (macros/SCons <c> macros/SNil))))` |
| `[a b c]` | `(macros/SexpBracket (macros/SCons <a> (macros/SCons <b> (macros/SCons <c> macros/SNil))))` |
| `x#` | auto-gensym: `(macros/SexpSym "x__auto_NNNN")` where NNNN is a unique counter |

Constructor references are module-qualified (`macros/SexpSym`, `macros/SCons`, etc.) so that quasiquote-based macros work without `(import [macros [*]])`.

### Auto-Gensym

Symbols ending in `#` inside quasiquote templates are auto-gensym. A per-quasiquote `HashMap<String, String>` tracks base -> generated name mappings. All occurrences of `x#` within one quasiquote expansion produce the same generated name. Different expansions produce different names.

### Synthetic Span Counter

A global `AtomicU32` counter starting at 1,000,000 ensures synthetic spans never collide with real source spans. Every node generated by quasiquote expansion gets a unique span from this counter.

### Dependencies

- Phase 1: Constructor names (`macros/SexpSym`, etc.) must be registered so the AST builder/typechecker can resolve them.
- Reader: Already parses `` ` ``, `~`, `~@` into `(quasiquote ...)`, `(unquote ...)`, `(unquote-splicing ...)` forms (confirmed in `reader.rs`).
- `sconcat`: The `~@` (unquote-splicing) operator generates calls to `sconcat`. This function must be available at expansion time. It lives in `lib/core/syntax.cl` and is re-exported through the prelude (spec Section 9.7.0).

### Estimated Scope

~350 lines: quasiquote.rs (~280 lines including helper constructors), tests (~70 lines).

---

## Phase 3: `defmacro` Parsing + Body Synthesis

**Goal**: Parse `defmacro` forms from Sexp, synthesize a `Defn` for each clause with argument destructuring via nested match expressions.

### Files to Create

| File | Crate | Content |
|------|-------|---------|
| `crates/cranelisp-frontend/src/defmacro.rs` | frontend | `is_defmacro()`, `parse_defmacro()`, `synthesize_macro_clause_defn()` |

### Files to Modify

| File | Crate | Change |
|------|-------|--------|
| `crates/cranelisp-frontend/src/lib.rs` | frontend | Add `pub mod defmacro` and re-exports |

### Key Types

```rust
/// Parsed defmacro info (before compilation).
pub struct DefmacroInfo {
    pub name: Symbol,
    pub is_private: bool,
    pub docstring: Option<String>,
    pub clauses: Vec<MacroClause>,
    pub span: Span,
}

/// A single parsed macro clause (params + body sexp).
pub struct MacroClause {
    pub fixed_params: Vec<MacroParam>,
    pub rest_param: Option<Symbol>,
    pub body_sexp: Sexp,
}
```

### Key Functions

- `is_defmacro(sexp: &Sexp) -> bool` -- Check if a Sexp is a `(defmacro ...)` or `(defmacro- ...)` form.
- `is_begin(sexp: &Sexp) -> bool` -- Check if a Sexp is a `(begin ...)` form.
- `flatten_begin(sexp: Sexp) -> Vec<Sexp>` -- Extract forms from a begin wrapper.
- `parse_defmacro(sexp: &Sexp) -> Result<DefmacroInfo, CranelispError>` -- Extract name, optional docstring, clause(s). Handles both single-clause shorthand `[params] body` and multi-clause `([params] body)+` syntax.
- `parse_macro_params(bracket: &Sexp) -> Result<(Vec<MacroParam>, Option<Symbol>), CranelispError>` -- Parse a parameter bracket, recognizing `&` for rest params and nested brackets for destructuring.
- `synthesize_macro_clause_defn(name: &str, clause_idx: usize, clause: &MacroClause, span: Span, expander: &mut dyn MacroExpander) -> Result<Defn, CranelispError>` -- Build a `Defn` node for one clause:
  1. Expand quasiquotes in the body Sexp
  2. Rewrite synthetic spans to unique values
  3. Build body `Expr` via `build_expr`
  4. Wrap in nested match for arg destructuring (`build_macro_param_chain`)
  5. Return a `Defn` with parameter type `:(macros/SList macros/Sexp)` and the wrapped body

### Arg Destructuring (build_macro_param_chain)

The macro function signature is `extern "C" fn(i64) -> i64` where the i64 argument is an `(SList Sexp)`. The synthesized body destructures this list via nested `match` expressions:

```
match __args__
  [(macros/SCons param1 __t2__)
    (match __t2__
      [(macros/SCons param2 __t1__)
        (match __t1__
          [(macros/SCons param3 rest_or_tail)
            <body>])])]
```

For bracket destructuring parameters, an additional inner match peels the `SexpBracket` and destructures its inner `SList`:

```
(match bracket_temp
  [(macros/SexpBracket __inner__)
    (match __inner__
      [(macros/SCons a (macros/SCons b rest))
        <continuation>])])
```

Key GOTCHA from sketch: Inner chain tail binding names (`__inner_t{N}__`) MUST be prefixed differently from outer chain bindings (`__t{N}__`) to avoid shadowing.

### Dependencies

- Phase 2: `expand_quasiquotes()` must be available for body preprocessing.
- `cranelisp-frontend/src/ast_builder.rs`: `build_expr()` is called to convert the body Sexp to an `Expr`. Currently this function takes `&mut dyn MacroExpander` -- the synthesizer passes it through so earlier macros in the body can be expanded.
- `cranelisp-types`: `MacroParam`, `MacroClauseInfo` types already exist.

### Estimated Scope

~450 lines: defmacro.rs (~350 lines), tests (~100 lines).

---

## Phase 4: MacroExpander Implementation (Binary Crate)

**Goal**: Implement the `CranelispExpander` struct in the binary crate that provides the real `MacroExpander` trait. This is where macro bodies are compiled and macro calls are dispatched.

### Files to Create

| File | Crate | Content |
|------|-------|---------|
| `src/expander.rs` | binary | `CranelispExpander` struct, `MacroExpander` impl, `compile_macro()`, clause dispatch, `MacroEnv` |

### Key Types

```rust
/// Compiled macro clause with function pointer.
struct MacroClauseEntry {
    func_ptr: *const u8,  // extern "C" fn(i64) -> i64
    fixed_params: Vec<MacroParam>,
    rest_param: Option<Symbol>,
    body_sexp: Option<Sexp>,
}

/// A registered macro with all its compiled clauses.
struct MacroEntry {
    name: Symbol,
    docstring: Option<String>,
    clauses: Vec<MacroClauseEntry>,
}

/// Macro environment: name -> compiled macro.
pub struct MacroEnv {
    macros: HashMap<Symbol, MacroEntry>,
}

/// The real MacroExpander implementation.
/// Owns the compiled macro registry.
pub struct CranelispExpander {
    env: MacroEnv,
}
```

### Key Functions

- `CranelispExpander::compile_macro(tc, jit, info, &self) -> Result<(), CranelispError>` -- For each clause in a `DefmacroInfo`:
  1. Expand earlier macros in the body Sexp (via `expand_sexp` with current env)
  2. Call `synthesize_macro_clause_defn()` to build a `Defn`
  3. Typecheck the `Defn` (verify return type is `Sexp`)
  4. Compile via backend, extract function pointer
  5. Register in `MacroEnv`

- `CranelispExpander::expand()` (MacroExpander trait) -- Given a macro name and args:
  1. Look up macro in `MacroEnv`
  2. Dispatch to matching clause (`clause_matches`)
  3. Marshal args: `sexp_to_runtime()` for each arg
  4. Build runtime SList from marshalled args
  5. Call function pointer: `extern "C" fn(i64) -> i64`
  6. Unmarshal result: `runtime_to_sexp()`
  7. Re-expand result (recursive, with depth limit)

- `expand_sexp(sexp: Sexp, env: &MacroEnv, depth: usize) -> Result<Sexp, CranelispError>` -- Recursively walk a Sexp tree, expanding macro calls. Handles:
  - List forms where head is a known macro -> dispatch and re-expand
  - Bare symbols that are zero-arg macros -> dispatch
  - `(begin ...)` splicing
  - Depth limit (100 iterations per spec recommendation)

- `clause_matches(clause: &MacroClauseEntry, args: &[Sexp]) -> bool` -- Check arity and structural patterns (bracket params must receive `Sexp::Bracket` with compatible element count).

### Ownership/Borrowing Design

The critical design question (flagged by `/arch`): how does `CranelispExpander` access the TypeChecker and Backend for macro body compilation while the AST builder holds `&mut dyn MacroExpander`?

**Solution**: The expander does NOT hold references to TypeChecker or Backend. Instead:

1. **Compilation** happens in the pipeline orchestrator (binary crate) BEFORE the AST builder runs. When processing forms sequentially, the orchestrator detects `defmacro` at the Sexp level (via `is_defmacro()`), compiles it using its own `&mut TypeChecker` and `&mut Jit`, and registers the result in the expander.

2. **Expansion** happens inside the AST builder via the `MacroExpander` trait. At this point, the expander only needs its `MacroEnv` (compiled function pointers) and the marshal functions. No TypeChecker or Backend access is needed.

This means `CranelispExpander` is a simple struct owning a `MacroEnv`. It borrows nothing. The pipeline orchestrator owns the TypeChecker, Backend, AND the expander, lending `&mut CranelispExpander` to the AST builder when needed.

```rust
// In pipeline orchestrator (simplified):
let mut tc = TypeChecker::new();
let mut jit = Jit::new()?;
let mut expander = CranelispExpander::new();

for sexp in sexps {
    if is_defmacro(&sexp) {
        let info = parse_defmacro(&sexp)?;
        expander.compile_macro(&mut tc, &mut jit, &info)?;
    } else {
        let expanded = expand_sexp(sexp, expander.env(), 0)?;
        let ast = build_top_level(&expanded, &mut expander)?;
        let check = tc.check_program(&[ast])?;
        // ... compile ...
    }
}
```

### Dependencies

- Phase 1: Marshal functions for arg/result conversion.
- Phase 2: `expand_quasiquotes()` for body preprocessing.
- Phase 3: `parse_defmacro()`, `synthesize_macro_clause_defn()` for parsing and synthesis.
- `/typecheck`: `check_defn()` for typechecking macro clause bodies.
- `/backend`: `compile_defn()` for JIT compilation of macro clause bodies.

### Estimated Scope

~400 lines: expander.rs (~300 lines), MacroEnv (~50 lines), tests (~50 lines).

---

## Phase 5: Pipeline Integration (Batch + REPL)

**Goal**: Replace `NoOpExpander` with `CranelispExpander` in both batch and REPL pipelines. Implement two-pass prelude loading.

### Files to Modify

| File | Crate | Change |
|------|-------|--------|
| `src/pipeline.rs` | binary | Replace `NoOpExpander` with `CranelispExpander` in `compile_and_run()` and `compile_module_graph()`. Add sequential form processing with defmacro interception. |
| `src/repl.rs` | binary | Replace `NoOpExpander` in `eval()`. Store `CranelispExpander` in `ReplSession`. Handle `defmacro` at REPL. |
| `src/lib.rs` | binary | Add `pub mod expander` |
| `crates/cranelisp-frontend/src/ast_builder.rs` | frontend | Remove `quote`/`quasiquote`/`unquote`/`unquote-splicing` rejection arms (currently Ring 3 gate errors). These are now handled by the expander. |

### Two-Pass Prelude Loading (spec Section 9.12)

The prelude (`lib/prelude.cl` and its submodules) is loaded with two passes:

**Pass 1 -- Type registration**: Scan all forms for `deftype`. Parse each to AST and register in the TypeChecker. This makes all constructors (including Sexp constructors from the `macros` module) available for use in macro bodies.

**Pass 2 -- Sequential compilation**: Process forms in source order:
1. `deftype` -> skip (already registered in Pass 1)
2. `defmacro` -> expand earlier macros in body, synthesize `Defn`, typecheck, compile, register in `MacroEnv`. The macro is immediately available for subsequent forms.
3. Everything else -> expand through `MacroEnv`, build AST, typecheck, compile.

This ordering ensures:
- Macro bodies can reference all type constructors (from Pass 1)
- Macro bodies can call helper functions defined earlier in the file
- Macro bodies can use earlier macros (e.g., `` ` `` uses qualified constructors, `slist` is a macro)
- User code can use all macros defined above it

### Batch Pipeline Changes

In `compile_module_graph()`, each module's forms are processed sequentially:

```rust
for sexp in remaining_sexps {
    if is_defmacro(&sexp) {
        let info = parse_defmacro(&sexp)?;
        expander.compile_macro(&mut tc, &mut jit, &info)?;
        // Register in module's symbol table as ModuleEntry::Macro
    } else if is_begin(&sexp) {
        // Flatten and process each sub-form recursively
    } else {
        let expanded = expand_sexp(sexp, expander.env(), 0)?;
        let ast = build_top_level(&expanded, &mut expander)?;
        // ... typecheck, compile ...
    }
}
```

### REPL Changes

`ReplSession` gains a `CranelispExpander` field. When the user enters a `defmacro`:

1. Parse the defmacro Sexp
2. Compile it (typecheck + backend) using the session's TypeChecker and Jit
3. Register in the session's `CranelispExpander`
4. Display: `name :: macro: (fn [Sexp Sexp ...] Sexp)` (per spec Section 9.13)

All subsequent REPL input is expanded through the updated macro environment before AST building.

### Import/Module Integration

When a module imports a macro from another module:
- `ModuleEntry::Macro` in the source module's symbol table stores `MacroClauseInfo` (params, rest_param)
- The importing module needs the compiled function pointers, not just the info
- The pipeline orchestrator must ensure the source module's macros are compiled before the importing module processes its forms
- Topological sort already guarantees this ordering

### Dependencies

- Phases 1-4: All prior phases must be complete.
- `/qa`: Integration tests for batch and REPL macro usage.

### Estimated Scope

~250 lines: pipeline.rs changes (~100 lines), repl.rs changes (~100 lines), ast_builder.rs gate removal (~20 lines), prelude loading (~30 lines).

---

## Phase 6: SList Helpers + Prelude Macros (stdlib scope)

**Goal**: Implement the SList helper functions and prelude macros. This phase is primarily `/stdlib` scope but is documented here for completeness and dependency tracking.

### Files to Create/Modify (stdlib)

| File | Owner | Content |
|------|-------|---------|
| `lib/core/syntax.cl` | /stdlib | `sfold`, `sreverse`, `sconcat`, `sempty?`, `slist` macro, `make-def-name`, `quote-sexp` |
| `lib/prelude.cl` | /stdlib | 10 prelude macros: `list`, `do`, `bind!`, `vec`, `cond`, `case`, `->`, `->>`, `str`, `when` |

### SList Helpers (spec Section 9.7)

These are ordinary Cranelisp functions operating on `(SList a)`:

| Function | Signature | Purpose |
|----------|-----------|---------|
| `sfold` | `(fn [(fn [b a] b) b (SList a)] b)` | Left fold |
| `sreverse` | `(fn [(SList a)] (SList a))` | Reverse |
| `sconcat` | `(fn [(SList a) (SList a)] (SList a))` | Concatenate |
| `sempty?` | `(fn [(SList a)] Bool)` | Empty check |
| `slist` | macro: `[& elems]` | Convenience constructor |

Per spec Section 9.7.0, only `sconcat` is re-exported through the prelude (used in quasiquote-generated code for `~@`). Others are available via explicit import from `core.syntax`.

### Prelude Macros (spec Section 9.10)

| Macro | Clauses | Features Used |
|-------|---------|---------------|
| `const` / `const-` | single | `quote-sexp`, bare-symbol expansion |
| `def` / `def-` | single | `begin`, `make-def-name`, `quote-sexp` |
| `list` | multi (0-arg, variadic) | `sfold`, `sreverse`, quasiquote |
| `do` | multi (1-arg, variadic) | quasiquote, `~@` |
| `bind!` | single (bracket destructure) | bracket pattern, quasiquote |
| `vec` | single (variadic) | `SexpBracket` constructor |
| `cond` | multi (1-arg, variadic) | recursive expansion, quasiquote |
| `case` | single (variadic) | manual Sexp constructors, `~` |
| `->` | single (variadic) | `sfold`, pattern matching |
| `->>` | single (variadic) | `sfold`, `sconcat` |
| `str` | multi (0-arg, 1-arg, variadic) | recursive expansion |
| `when` | single | quasiquote |

### Primitives for Macro Authors (spec Section 9.11)

| Primitive | Signature | Where |
|-----------|-----------|-------|
| `quote-sexp` | `(fn [Sexp] Sexp)` | Runtime intrinsic or inline |
| `str-concat` | `(fn [String String] String)` | Already exists |
| `make-def-name` | `(fn [Sexp] Sexp)` | stdlib helper in `core/syntax.cl` |

`quote-sexp` converts a runtime `Sexp` value into a `Sexp` that reproduces it when evaluated. This can be implemented as a runtime intrinsic (extern function) or as a Cranelisp function using pattern matching on Sexp variants.

### Dependencies

- Phases 1-5: Full macro pipeline must be operational.
- `/typecheck`: ADT type inference for `SList`/`Sexp` operations.
- `/backend`: Codegen for pattern matching on `SList`/`Sexp`.

### Estimated Scope

~400 lines of Cranelisp: syntax.cl helpers (~150 lines), prelude macros (~250 lines). Frontend changes minimal (primitive registration for `quote-sexp`).

---

## Phase 7: REPL Polish (`/expand`, introspection)

**Goal**: Implement `/expand` command, integrate macros into REPL introspection (`/list`, `/info`, `/sig`, `/doc`), and add the `defmacro-in-results` capability for macros that produce other macros.

### Files to Modify

| File | Crate | Change |
|------|-------|--------|
| `src/repl.rs` | binary | Handle `/expand` command; display macros in `/list` taxonomy; macro info in `/info`, `/sig`, `/doc` |

### `/expand` Command (spec Section 9.13)

```
user> /expand (double-list 1 2)
(list 1 1 2 2)
user> /expand (list 1 2 3)
(Cons 1 (Cons 2 (Cons 3 Nil)))
```

Implementation: parse the input Sexp, run it through `expand_sexp()` (recursive expansion to fixed point), format the result as a string, display WITHOUT evaluating.

### Macro Introspection

Macros appear in REPL introspection alongside functions and types:

- `/list` -- Macros appear under a "Macros" category
- `/info name` -- Shows `name :: macro: (fn [Sexp Sexp ...] Sexp)`, clause count, docstring
- `/sig name` -- Shows the macro's parameter signature
- `/doc name` -- Shows the macro's docstring

The `ModuleEntry::Macro` variant already stores `clauses`, `docstring`, and `visibility`. The REPL handlers need to match on this variant and produce appropriate output.

### `defmacro-in-results`

When a macro expansion produces a `(begin ...)` form containing `(defmacro ...)`, those inner `defmacro` forms must be compiled and registered. This is essential for `def`/`const` which expand to a `begin` containing a `defmacro`.

The pipeline orchestrator handles this: after expanding a form, if the result is a `(begin ...)`, flatten it, and process each sub-form -- including any `defmacro` forms -- sequentially.

### Dependencies

- Phases 1-6: Full macro system with prelude macros.
- The `/repl` skill owns the REPL experience spec and test scripts.

### Estimated Scope

~150 lines: REPL command handlers (~80 lines), `/expand` implementation (~40 lines), tests (~30 lines).

---

## Risk Assessment

### R1: Ownership/Borrowing During Compilation

**Risk**: The AST builder holds `&mut dyn MacroExpander` while macro compilation needs `&mut TypeChecker` and `&mut Jit`.

**Mitigation**: Resolved by architecture. Macro compilation happens in the pipeline orchestrator BEFORE the AST builder runs for that form. The expander only reads its `MacroEnv` during expansion -- no mutable access to TypeChecker or Backend needed. See Phase 4 for the detailed ownership design.

### R2: Synthetic Span Collisions

**Risk**: Multiple macro expansions could produce nodes with the same synthetic span, causing resolution map collisions in the typechecker and codegen.

**Mitigation**: Global `AtomicU32` counter starting at 1,000,000. Each node gets a unique span. The sketch uses this approach successfully. Additionally, `rewrite_spans()` in `synthesize_macro_clause_defn()` rewrites any `Span::SYNTHETIC` (0,0) spans to unique values, and clause index offsets prevent cross-clause collisions.

### R3: Marshal Safety

**Risk**: `sexp_to_runtime()` allocates heap memory; `runtime_to_sexp()` reads raw pointers. Invalid heap state could cause memory corruption.

**Mitigation**:
- Marshal functions are `unsafe` only in their pointer-reading portions (clearly documented).
- Tag constants are compile-time constants matching the registered ADT tags.
- Roundtrip tests verify correctness for all Sexp variants.
- RC is NOT tracked for marshalled macro args/results (they are temporary, freed after expansion). This matches the sketch's approach.
- `debug_assert!` on tag values to catch corruption early.

### R4: Two-Pass Loading

**Risk**: The two-pass prelude loading (types first, then sequential) could produce ordering errors if a type depends on a macro or vice versa.

**Mitigation**: The spec (Section 9.12) explicitly defines the ordering. Pass 1 only processes `deftype` forms (no macro references). Pass 2 processes everything sequentially, which naturally handles dependencies. The `macros` module types are seeded by the compiler before prelude loading begins (Phase 1), so they are always available.

### R5: `defmacro-in-results` (begin Splicing)

**Risk**: A macro can expand to `(begin (defmacro ...) ...)`, requiring the pipeline to compile new macros from expansion results.

**Mitigation**: The pipeline orchestrator checks for `(begin ...)` results after expansion and recursively processes sub-forms. This is a natural extension of sequential form processing. The sketch handles this successfully. Key constraint: `begin` is ONLY valid as a macro expansion result, never in user source.

### R6: Cross-Module Macro Availability

**Risk**: Macros imported from dependency modules must be compiled before the importing module processes its forms.

**Mitigation**: Topological sort guarantees dependencies are compiled first. When a module is compiled, its macros are registered in the expander. When the next module is processed, those macros are available. The `MacroEnv` accumulates across modules within a compilation session.

### R7: Recursive Macro Expansion

**Risk**: A macro that expands to another macro call (or itself) could loop infinitely.

**Mitigation**: Depth limit of 100 (configurable). The `expand_sexp()` function increments a depth counter on each recursive expansion. Exceeding the limit produces a compile-time error per spec Section 9.3.3.

---

## Summary

| Phase | New Files | Modified Files | Est. Lines | Key Deliverable |
|-------|-----------|----------------|------------|-----------------|
| 1. Synthetic module + marshal | 1 | 3 | ~300 | `macros` module seeded, `sexp_to_runtime`/`runtime_to_sexp` |
| 2. Quasiquote engine | 1 | 1 | ~350 | `expand_quasiquotes()`, auto-gensym |
| 3. defmacro parsing | 1 | 1 | ~450 | `parse_defmacro()`, `synthesize_macro_clause_defn()` |
| 4. MacroExpander impl | 1 | 0 | ~400 | `CranelispExpander`, `compile_macro()`, `expand_sexp()` |
| 5. Pipeline integration | 0 | 4 | ~250 | Two-pass prelude, batch + REPL wiring |
| 6. Prelude macros | 2 | 0 | ~400 | sfold/sconcat helpers, 12 prelude macros |
| 7. REPL polish | 0 | 1 | ~150 | `/expand`, macro introspection |
| **Total** | **6** | **10** | **~2300** | |

Phases 1-5 are `/frontend` + `/backend` scope. Phase 6 is primarily `/stdlib` scope. Phase 7 is `/repl` + `/qa` scope.

## Next Skills

- `/arch` -- Review this plan against the Ring 3 macro architecture design doc; confirm ownership model and `MacroClauseInfo.rest_param` addition
- `/typecheck` -- Confirm `register_macros_module()` approach for seeding synthetic types; confirm `check_defn()` path works for macro clause bodies
- `/backend` -- Confirm `compile_defn()` path works for macro clause bodies returning `Sexp` ADT values
- `/stdlib` -- Begin planning prelude macro implementations against Phase 6 dependency matrix
- `/qa` -- Begin planning Ring 3 integration tests against spec Section 9
