# Ring 3 Macro Pipeline Architecture

Design document for the macro mini-pipeline: how `defmacro` forms are compiled, how macro invocations are expanded, and how the system bootstraps. This document specifies the architecture; implementation details are owned by the relevant compiler skills.

## 1. Overview

The macro system requires a circular dependency: the frontend needs macros expanded during AST building, but macro expansion requires compiled function pointers produced by the backend. The reimplementation resolves this through **dependency inversion** (Decision 8).

`cranelisp-types` defines the `MacroExpander` trait. The frontend's AST builder accepts `&mut dyn MacroExpander` and calls `expand()` / `is_macro()` when it encounters a list form whose head names a registered macro. The binary crate provides the real implementation — `CraneliftExpander` — which holds a `MacroEnv` mapping macro names to compiled function pointers. The `expand()` method performs clause dispatch, argument marshalling, function pointer invocation, result unmarshalling, and span rewriting. It never re-borrows the typechecker or backend.

```
    cranelisp-types            cranelisp-frontend           cranelisp (binary)
  ┌──────────────────┐      ┌────────────────────┐      ┌───────────────────────┐
  │ trait MacroExpander│◄────│ ast_builder.rs      │      │ CraneliftExpander     │
  │   expand()        │      │  &mut dyn MacroExp. │      │   impl MacroExpander  │
  │   is_macro()      │      └────────────────────┘      │   MacroEnv            │
  └──────────────────┘                                    │   marshal.rs          │
                                                          └───────────────────────┘
```

The critical constraint: when `ast_builder` calls `expander.expand()`, the `CraneliftExpander` only invokes already-compiled functions. It does **not** access the typechecker or backend during expansion. Macro compilation happens earlier, in the pipeline orchestrator, before the form that uses the macro reaches the AST builder.

## 2. MacroExpander Implementation

### CraneliftExpander

A struct in the binary crate (`src/macro_expander.rs`) that implements `MacroExpander`:

```rust
/// Real macro expander for Ring 3+.
/// Holds compiled macro function pointers and performs expansion.
pub struct CraneliftExpander {
    /// Maps macro name -> compiled clause info + function pointers.
    macro_env: MacroEnv,
    /// Expansion iteration limit (default: 500).
    expansion_limit: usize,
}

/// Runtime macro environment: name -> list of compiled clauses.
pub struct MacroEnv {
    macros: HashMap<Symbol, Vec<MacroClauseEntry>>,
}

/// A compiled macro clause ready for invocation.
pub struct MacroClauseEntry {
    /// JIT-compiled function pointer: extern "C" fn(i64) -> i64
    func_ptr: *const u8,
    /// Fixed parameters (for clause matching).
    params: Vec<MacroParam>,
    /// Rest parameter name, if variadic.
    rest_param: Option<Symbol>,
    /// Original body sexp (for /expand display, optional).
    body_sexp: Option<Sexp>,
}
```

### expand() Method

The `expand()` implementation:

1. **Clause dispatch**: iterate clauses in definition order. For each clause, check whether the call-site argument count matches the clause's fixed parameter count (accounting for rest parameters) and whether any bracket patterns match the corresponding argument structure. First match wins.
2. **Marshal arguments**: convert each `Sexp` argument from the compiler's internal representation to a heap-allocated runtime `Sexp` ADT value via `sexp_to_runtime()`. For variadic clauses, collect remaining arguments into a runtime `(SList Sexp)` value.
3. **Invoke**: call the clause's `func_ptr` with the marshalled argument list packaged as a single `(SList Sexp)`. The function returns an `i64` representing a runtime `Sexp` value.
4. **Unmarshal result**: convert the runtime `Sexp` value back to the compiler's internal `Sexp` representation via `runtime_to_sexp()`.
5. **Rewrite spans**: replace all spans in the result tree with the call-site span, so error messages point to the macro invocation.
6. **Re-expand**: recursively expand the result until no macro calls remain (fixed point) or the iteration limit is reached.

### is_macro() Method

Returns `true` if `macro_env.macros.contains_key(name)`. This is called by the AST builder before treating a list head as a function application.

## 3. Macro Compilation Flow

When the pipeline orchestrator encounters a `defmacro` form (detected at the Sexp level by checking for a list whose head is `"defmacro"` or `"defmacro-"`), it intercepts the form **before** passing it to the AST builder. The compilation sequence:

```
defmacro Sexp
    │
    ▼
1. parse_defmacro()         → extract name, docstring, clauses (params + body sexps)
    │
    ▼
2. for each clause:
   a. expand macros in body  → use current MacroEnv (earlier macros available)
   b. expand quasiquotes     → desugar `, ~, ~@ to explicit Sexp constructor calls
   c. synthesize Defn        → wrap body in (defn __macro_clause_N [args] body)
      │                        with parameter destructuring match chain
      ▼
   d. typecheck              → verify return type is Sexp, body is well-typed
      │
      ▼
   e. compile                → Cranelift IR → JIT finalize → extract func_ptr
    │
    ▼
3. register in MacroEnv     → store func_ptr + params + rest_param per clause
4. register in SymbolTable  → ModuleEntry::Macro for module system visibility
```

### Defn Synthesis (Step 2c)

Each clause becomes a standalone function with signature `extern "C" fn(i64) -> i64`. The single `i64` parameter is a pointer to an `(SList Sexp)` containing all the macro's arguments (already marshalled by the caller).

The synthesized `Defn` body contains a nested match chain that destructures this SList:

- For each fixed `MacroParam::Name(n)`, peel one `SCons` and bind the head to `n`.
- For each `MacroParam::Bracket { fixed, rest }`, peel one `SCons`, match the head against `SexpBracket`, and destructure the inner `SList` to bind the fixed names and optional rest.
- If the clause has a `rest_param`, the remaining tail of the outer SList binds to the rest parameter name.
- The innermost expression is the macro body.

### Quasiquote Expansion (Step 2b)

Quasiquote templates are desugared to explicit `Sexp` constructor calls before typechecking. This is a Sexp-to-Sexp transformation in the frontend:

- Literal atoms become their corresponding `Sexp` constructor: `42` -> `(macros/SexpInt 42)`
- Symbols become `(macros/SexpSym "name")`
- Lists become `(macros/SexpList (macros/SCons <elem1> (macros/SCons <elem2> ... macros/SNil)))`
- Brackets become `(macros/SexpBracket ...)`
- `~expr` splices `expr` directly (must be of type `Sexp`)
- `~@expr` splices each element of `expr` (must be of type `(SList Sexp)`), concatenated with `sconcat`
- Auto-gensym: `x#` symbols within a single quasiquote expansion produce consistent unique names

Quasiquote expansion emits **qualified** constructor references (`macros/SexpSym`, `macros/SCons`, etc.) so user modules do not need `(import [macros [*]])` for quasiquote-based macros.

## 4. Macro Expansion Flow

When the AST builder encounters a list form `(name arg1 arg2 ...)`:

```
AST builder
    │
    ├── is_macro("name")?  ──no──>  treat as function application
    │
    yes
    │
    ▼
expander.expand("name", [arg1, arg2, ...], span)
    │
    ▼
CraneliftExpander::expand()
    │
    ├── 1. clause_dispatch(clauses, args)  → select matching clause
    │
    ├── 2. sexp_to_runtime(arg1), sexp_to_runtime(arg2), ...
    │      for variadic: collect rest into (SList Sexp) via runtime SCons/SNil
    │      package all args as (SList Sexp)
    │
    ├── 3. call func_ptr(args_slist_ptr) → result_i64
    │
    ├── 4. runtime_to_sexp(result_i64) → expanded Sexp
    │
    ├── 5. rewrite_spans(expanded, call_site_span)
    │
    └── 6. re-expand if result contains macro calls (up to limit)
           │
           ├── check for (begin ...) → splice into multiple top-level forms
           │
           └── return expanded Sexp to AST builder
```

### Bare-Symbol Expansion

When the AST builder encounters a bare symbol (not inside a list application), it also checks `is_macro()`. If the name is a zero-argument macro, it calls `expand(name, &[], span)` to produce the expansion. This enables `const`-style macros where a bare name expands to a value.

### begin Flattening

If a macro returns `(begin form1 form2 ... formN)`, the expander signals to the pipeline orchestrator that multiple top-level forms should be spliced in place of the macro call. The AST builder does not handle `begin` — the pipeline orchestrator detects it at the Sexp level and processes each form independently.

This is essential for macros like `def` that expand to both a `defn` and a nested `defmacro`.

## 5. Marshalling

### sexp_to_runtime

Converts a compiler-internal `Sexp` value to a heap-allocated runtime `Sexp` ADT value. Located in the binary crate (`src/marshal.rs`).

```rust
/// Convert compiler Sexp to runtime Sexp ADT (heap-allocated).
/// Returns an i64 representing the tagged ADT value.
pub fn sexp_to_runtime(sexp: &Sexp) -> i64
```

For each `Sexp` variant, allocates a heap cell with the appropriate constructor tag and fields:

| Compiler Sexp | Runtime constructor | Tag | Fields |
|---|---|---|---|
| `Sexp::Int(n, _)` | `SexpInt` | 0 | `[tag, n]` |
| `Sexp::Float(f, _)` | `SexpFloat` | 1 | `[tag, f_bits]` |
| `Sexp::Bool(b, _)` | `SexpBool` | 2 | `[tag, b]` |
| `Sexp::Str(s, _)` | `SexpStr` | 3 | `[tag, str_ptr]` |
| `Sexp::Symbol(s, _)` | `SexpSym` | 4 | `[tag, str_ptr]` |
| `Sexp::List(children, _)` | `SexpList` | 5 | `[tag, slist_ptr]` |
| `Sexp::Bracket(children, _)` | `SexpBracket` | 6 | `[tag, slist_ptr]` |

For `SexpList` and `SexpBracket`, the children are first converted to a runtime `(SList Sexp)` by recursively marshalling each child and building a chain of `SCons`/`SNil` cells.

### runtime_to_sexp

Reads a runtime `Sexp` ADT value from the heap and reconstructs a compiler-internal `Sexp`. Located in the binary crate (`src/marshal.rs`).

```rust
/// Convert runtime Sexp ADT (heap pointer or nullary tag) to compiler Sexp.
/// The span is set to Span::SYNTHETIC; the caller rewrites it.
pub fn runtime_to_sexp(val: i64) -> Sexp
```

Reads the tag from the heap cell, then reads fields according to the constructor layout. For `SexpList`/`SexpBracket`, walks the `SList` chain reading `SCons` heads recursively.

### Runtime Allocation Helpers

`cranelisp-runtime` provides low-level allocation functions used by the marshal code:

- `heap_alloc(size)` — allocate with RC header (existing)
- String allocation via existing string intrinsics

No new `marshal.rs` is needed in `cranelisp-runtime` — the binary crate's marshal code calls existing runtime allocation functions directly.

### RC Strategy for Marshalled Values

Marshalled values are allocated at compile time (during macro expansion) and are **leaked** — their reference counts are never decremented. This is acceptable because:

1. Macro expansion happens a bounded number of times during compilation.
2. The total memory used by marshalled Sexp trees is proportional to source code size, not runtime data size.
3. This matches the sketch's approach and avoids the complexity of tracking ownership across the marshal boundary.

The same strategy applies to both `sexp_to_runtime` (allocating input to the macro function) and the runtime `Sexp` values returned by the macro function (which are immediately unmarshalled and then abandoned).

## 6. Module Integration

### Synthetic macros Module

The `macros` module is compiler-seeded at startup (like the `primitives` module). It contains the `Sexp` and `SList` type definitions:

```clojure
;; Seeded by the compiler, not user-modifiable:
(deftype (SList a) SNil (SCons [:a shead :(SList a) stail]))
(deftype Sexp
  (SexpInt [:Int sval])
  (SexpFloat [:Float sval])
  (SexpBool [:Bool sval])
  (SexpStr [:String sval])
  (SexpSym [:String sname])
  (SexpList [:(SList Sexp) sitems])
  (SexpBracket [:(SList Sexp) sitems]))
```

These types are registered via the typechecker's normal `register_type_def` path during startup, before any user code is processed. Constructors (`SexpInt`, `SCons`, `SNil`, etc.) are available via qualified access (`macros/SexpSym`) without import.

### ModuleEntry::Macro

When a macro is compiled and registered, the pipeline orchestrator inserts a `ModuleEntry::Macro` into the current module's symbol table:

```rust
ModuleEntry::Macro {
    name: macro_name,
    clauses: clause_infos,  // Vec<MacroClauseInfo> — serializable metadata
    docstring: parsed_docstring,
    visibility: Public | Private,  // defmacro vs defmacro-
    sexp: Some(original_sexp),
    source: Some(source_text),
}
```

This makes macros visible to:

- **Cross-module import**: `(import [other-module [my-macro]])` makes `my-macro` available as a macro in the importing module. The pipeline orchestrator loads the macro's compiled function pointer from the exporting module's `MacroEnv`.
- **REPL introspection**: `/list` shows macros, `/info my-macro` shows clause signatures, `/sig` shows `macro: (fn [Sexp ...] Sexp)`, `/doc` shows the docstring.
- **Module caching**: `MacroClauseInfo` is serializable. When a cached module is loaded, the pipeline re-compiles macro bodies to obtain function pointers (macro function pointers cannot be serialized).

### Cross-Module Macro Visibility

When module A exports a macro and module B imports it:

1. Module A is compiled first (topological order).
2. During A's compilation, `defmacro` forms produce `MacroClauseEntry` values stored in A's `MacroEnv` slot.
3. Module A's symbol table contains `ModuleEntry::Macro` with `MacroClauseInfo` metadata.
4. When module B's import is processed, the pipeline orchestrator:
   a. Finds the `ModuleEntry::Macro` in A's symbol table.
   b. Looks up A's `MacroEnv` to obtain the function pointers.
   c. Registers the macro in B's `MacroEnv` slot (or in the shared `CraneliftExpander`).
5. During B's compilation, calls to the imported macro are expanded via the registered function pointers.

## 7. Bootstrapping

The prelude is the first non-trivial Cranelisp source that uses macros. It contains type definitions, helper functions, and macro definitions that depend on each other. Bootstrapping follows the two-pass strategy from spec section 9.12.

### Startup Sequence

```
1. register_primitives()       → Int, Bool, Float, String, Fn types + named primitives
2. register_core_traits()      → Num, Eq, Ord, Display (Decision 17 path)
3. seed_macros_module()        → register Sexp and SList types in synthetic macros module
4. load_prelude()              → two-pass prelude loading (below)
```

### Two-Pass Prelude Loading

**Pass 1 — Type registration**: Scan all Sexp forms in the prelude source for `deftype`. For each, parse to AST and register the type definition in the typechecker. This makes all constructors (e.g., `Cons`, `Nil`, `None`, `Some`) available for use in macro bodies during Pass 2.

**Pass 2 — Sequential form processing**: Process each Sexp form in source order:

- **`deftype`**: skip (already registered in Pass 1).
- **`defmacro`**: compile the macro body through the mini-pipeline (expand earlier macros in body, expand quasiquotes, synthesize Defn, typecheck, compile, extract func_ptr). Register in `MacroEnv`. The macro is immediately available for subsequent forms.
- **`defn` / `impl` / other**: expand through the current `MacroEnv`, then build AST, typecheck, and compile normally.

This ordering ensures:

- Macro bodies can reference all type constructors (from Pass 1).
- Macro bodies can call helper functions defined earlier in the file (compiled in Pass 2 before the macro).
- Macro bodies can use earlier macros (e.g., the `slist` convenience macro inside another macro's body).
- Regular code can use all macros defined above it in the file.

### begin and defmacro-in-results

When a macro expands to `(begin form1 form2 ...)`, the pipeline orchestrator must handle each spliced form individually during Pass 2. If one of the spliced forms is a `defmacro`, it must be compiled and registered immediately so that subsequent spliced forms (and subsequent top-level forms) can use it.

This is essential for the `def` macro, which expands to `(begin (defn name-def ...) (defmacro name ...))`.

### REPL Bootstrapping

The REPL session runs the same startup sequence. After bootstrapping, the `CraneliftExpander` holds all prelude macros. Each subsequent REPL input is expanded through the full `MacroEnv` before AST building.

When the user defines a new macro at the REPL, it follows the same compilation flow as during prelude loading: intercept the `defmacro` Sexp, compile through the mini-pipeline, register in `MacroEnv`, and register in the current module's symbol table.

## 8. Interface Changes

### MacroClauseInfo

Add `rest_param: Option<Symbol>` to `MacroClauseInfo` in `cranelisp-types/src/module.rs`:

```rust
/// Information about a single macro clause (for multi-clause defmacro).
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MacroClauseInfo {
    pub params: Vec<MacroParam>,
    pub rest_param: Option<Symbol>,  // NEW: variadic rest parameter name
    pub source: Option<String>,
}
```

This field is needed for:
- Clause dispatch: determining whether a clause can accept more arguments than its fixed parameter count.
- REPL introspection: displaying the full clause signature including `& rest`.

### MacroExpander Trait

No changes to the `MacroExpander` trait itself. The existing `expand()` and `is_macro()` methods are sufficient. The trait remains in `cranelisp-types/src/pipeline.rs`.

### NoOpExpander

The existing `NoOpExpander` remains as a fallback for tests and for any code path that does not need macro expansion. In Ring 3, the binary crate replaces `NoOpExpander` with `CraneliftExpander` at all pipeline entry points.

## 9. New Files

### Binary crate (`src/`)

| File | Purpose | Approx. lines |
|---|---|---|
| `src/macro_expander.rs` | `CraneliftExpander` struct, `MacroEnv`, `MacroClauseEntry`, `impl MacroExpander` | ~250 |
| `src/marshal.rs` | `sexp_to_runtime()`, `runtime_to_sexp()` — convert between compiler and runtime Sexp | ~200 |

### Frontend crate (`crates/cranelisp-frontend/src/`)

| File | Purpose | Approx. lines |
|---|---|---|
| `src/quasiquote.rs` | Quasiquote expansion: `expand_quasiquotes()`, `expand_qq_template()`, auto-gensym | ~200 |
| `src/defmacro_parse.rs` | `parse_defmacro()` — extract name, docstring, clauses from Sexp, synthesize Defn body | ~250 |

### Types crate (`crates/cranelisp-types/src/`)

No new files. One field addition to `MacroClauseInfo` in `module.rs`.

### Typecheck crate (`crates/cranelisp-typecheck/src/`)

No new files. The typechecker already handles all the types involved (ADTs, function types, `Sexp` as an ADT). The `macros` module is seeded via existing `register_type_def` infrastructure.

### Backend crate (`crates/cranelisp-backend/src/`)

No new files. Macro clause compilation uses the existing `compile_defn` / `compile_program` infrastructure.

### Runtime crate (`crates/cranelisp-runtime/src/`)

No new files. Marshal code in the binary crate calls existing `heap_alloc` and string allocation functions.

### Standard library (`stdlib/`)

| File | Purpose | Approx. lines |
|---|---|---|
| `stdlib/core/syntax.cl` | SList helpers (`sfold`, `sreverse`, `sconcat`, `sempty?`, `slist`), prelude macros (`list`, `do`, `bind!`, `cond`, `case`, `->`, `->>`, `vec`, `str`, `const`, `def`, `when`) | ~150 |

### Test files (`tests/`)

| File | Purpose | Approx. lines |
|---|---|---|
| `tests/macros.rs` | Macro integration tests: single-clause, multi-clause, bracket destructuring, quasiquote, bare-symbol, begin, cross-module | ~300 |
| `tests/prelude_macros.rs` | Prelude macro tests: `list`, `do`, `cond`, `case`, threading, `vec`, `str`, `const`, `def` | ~200 |

### Approximate total: ~1550 new lines across ~8 new files.

## 10. Risks

### R1: Ownership During Macro Body Compilation

**Risk**: The pipeline orchestrator needs `&mut TypeChecker` and `&mut Backend` to compile a macro body, but these may already be borrowed during module compilation.

**Mitigation**: Macro compilation happens at the top level of form processing — the same scope where `compile_and_run` or the REPL's `compile_unit` operates. The typechecker and backend are available as mutable borrows at this level. The key insight is that macro compilation completes before the AST builder is invoked for subsequent forms, so there is no overlapping borrow: the flow is sequential (compile macro → register → proceed to next form), not concurrent.

### R2: Synthetic Spans

**Risk**: Macro-expanded code carries synthetic spans. Error messages that point to synthetic spans are unhelpful.

**Mitigation**: The `rewrite_spans()` step in `expand()` replaces all spans in the expansion result with the macro call-site span. This means type errors, codegen errors, and runtime errors from expanded code all point to where the macro was invoked. The tradeoff is that errors in the macro body itself (as opposed to the expansion result) must be reported at `defmacro` time, not at call time. This is the same tradeoff the sketch makes (spec section 9.14, item 5).

### R3: Marshal Safety

**Risk**: `sexp_to_runtime` allocates heap cells and `runtime_to_sexp` reads raw heap memory. Incorrect tag values, dangling pointers, or layout mismatches cause undefined behavior.

**Mitigation**:
- Marshal code is centralized in one file (`src/marshal.rs`) with extensive assertions.
- The heap layout of marshalled values is identical to normal ADT values — the same `heap_alloc` and field offset constants are used.
- Marshal round-trip tests (`sexp_to_runtime` then `runtime_to_sexp`) verify that all seven Sexp variants survive the round trip.
- The leak-at-compile-time RC strategy avoids use-after-free from premature deallocation.

### R4: Two-Pass Prelude Loading

**Risk**: The two-pass approach adds complexity to the module loading pipeline. Pass 1 must reliably identify all `deftype` forms without expanding macros (since macros are not yet available).

**Mitigation**: Pass 1 only scans for top-level `(deftype ...)` forms — a purely syntactic check (is the first element of a list the symbol `"deftype"`?). No macro expansion is needed because `deftype` is a special form, never produced by macro expansion in the prelude itself. If a macro in user code expands to a `deftype`, the two-pass approach is not needed for user modules (only for the prelude, which has the circular dependency between types and macros).

### R5: Expansion Divergence

**Risk**: Recursive macros (e.g., `list`, `cond`) may produce infinite expansion if the base case is not reached.

**Mitigation**: The expansion limit (default 500 iterations) terminates divergent expansions with a clear error message naming the macro and the iteration count. This matches spec section 9.3.3.

### R6: Cross-Module Macro Re-compilation on Cache Load

**Risk**: When a cached module containing macros is loaded, the macro function pointers cannot be deserialized. The macro bodies must be re-compiled.

**Mitigation**: Module caching is Ring 4. By that point, the macro compilation pipeline will be mature. The cache loader will re-compile macro bodies using stored `MacroClauseInfo` metadata and the original source (stored in `ModuleEntry::Macro.source`). This is comparable to how the sketch handles macro reloading.
