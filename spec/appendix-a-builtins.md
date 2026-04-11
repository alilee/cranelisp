# Appendix A: Builtin Reference (Non-Normative)

> **This appendix is non-normative.** It documents the reference implementation's compiler-seeded types and primitive functions. Sections A.1–A.2 describe types that are language-level requirements (normatively specified in [Section 3](03-types.md) and [Section 8.9](08-modules.md#89-synthetic-modules)). Sections A.3–A.4 list primitive functions and special forms provided by the reference implementation.

## A.1 Primitive Types [Tested]

Registered in the `primitives` module. Available in all programs via `(import [primitives [*]])` or qualified reference.

| Type | Description | Value Domain |
|---|---|---|
| `Int` | Signed 64-bit integer | -2^63 to 2^63 - 1 | [Tested tests/ring0.rs::arithmetic_addition]
| `Bool` | Boolean | `true`, `false` | [Tested tests/ring0.rs::boolean_not_true]
| `String` | Immutable UTF-8 string | Heap-allocated byte sequence | [Tested tests/ring1.rs::string_concat]
| `Float` | IEEE 754 double-precision | 64-bit floating point | [Tested tests/ring0.rs::float_arithmetic]

## A.2 Built-in Compound Types [Tested tests/ring1.rs::vec_literal_int, tests/io.rs::io_pure_int_type, tests/macros.rs::macro_basic_repl]

Registered in the `primitives` and `macros` synthetic modules.

| Type | Module | Kind | Description |
|---|---|---|---|
| `(Vec a)` | `primitives` | Built-in | Resizable array, element access via extern primitives | [Tested tests/ring1.rs::vec_len_three]
| `(IO a)` | `primitives` | Compiler-seeded ADT | Effectful computation; constructors `Pure`, `Effect`, `Bind` | [R4 S9]
| `Trace` | `primitives` | Compiler-seeded ADT | Execution trace tree; single constructor `TraceCall` with fields `name` (String), `params` (SList String), `result` (String), `children` (SList Trace), `nanos` (Int). Not auto-imported; requires explicit import. | [Tested tests/ring4_trace.rs::trace_type_importable_from_primitives]
| `TestResult` | root | Compiler-seeded ADT | Test execution result; constructors `TestPass` (name, nanos), `TestFail` (name, nanos, reason), `TraceFail` (name, nanos, reason, trace). Root type — always in scope. | [R4]
| `Sexp` | `macros` | Compiler-seeded ADT | S-expression value for macro system | [Tested tests/macros.rs::macro_basic_repl]
| `(SList a)` | `macros` | Compiler-seeded ADT | Cons-list for S-expression manipulation | [Tested tests/macros.rs::macro_basic_repl]

## A.3 Primitive Functions (Host-Implemented) [Tested tests/ring0.rs::hello, tests/ring1.rs::str_concat, tests/ring1.rs::int_to_string]

Primitive functions are implemented in the host language and registered in the `primitives` module. They are the low-level substrate; standard library functions and trait implementations are built on top of them.

### Inline Primitives

Inline primitives compile to inline Cranelift IR instructions — no function call overhead.

**Integer arithmetic** — all `(Fn [Int Int] Int)`:

| Function | Description |
|---|---|
| `add-i64` | Add | [Tested tests/ring0.rs::arithmetic_addition]
| `sub-i64` | Subtract | [Tested tests/ring0.rs::arithmetic_subtraction]
| `mul-i64` | Multiply | [Tested tests/ring0.rs::arithmetic_multiplication]
| `div-i64` | Integer division | [Tested tests/ring0.rs::arithmetic_division]

**Integer comparison** — all `(Fn [Int Int] Bool)`:

| Function | Description |
|---|---|
| `eq-i64` | Equality | [Tested tests/ring0.rs::comparison_operators]
| `lt-i64` | Less than | [Tested tests/ring0.rs::comparison_operators]
| `gt-i64` | Greater than | [Tested tests/ring0.rs::comparison_operators]
| `le-i64` | Less than or equal | [Tested tests/ring0.rs::comparison_less_equal]
| `ge-i64` | Greater than or equal | [Tested tests/ring0.rs::comparison_greater_equal]

**Float arithmetic** — all `(Fn [Float Float] Float)`:

| Function | Description |
|---|---|
| `add-f64` | Add | [Tested tests/ring0.rs::float_arithmetic]
| `sub-f64` | Subtract | [Tested tests/ring0.rs::float_subtraction]
| `mul-f64` | Multiply | [Tested tests/ring0.rs::float_multiplication]
| `div-f64` | Division | [Tested tests/ring0.rs::float_division]

**Float comparison** — all `(Fn [Float Float] Bool)`:

| Function | Description |
|---|---|
| `eq-f64` | Equality | [Tested tests/repl_experience.rs::all_float_comparison_primitives_work_in_repl]
| `lt-f64` | Less than | [Tested tests/ring0.rs::float_comparison]
| `gt-f64` | Greater than | [Tested tests/repl_experience.rs::all_float_comparison_primitives_work_in_repl]
| `le-f64` | Less than or equal | [Tested tests/repl_experience.rs::all_float_comparison_primitives_work_in_repl]
| `ge-f64` | Greater than or equal | [Tested tests/repl_experience.rs::all_float_comparison_primitives_work_in_repl]

**Boolean** — `(Fn [Bool] Bool)`:

| Function | Description |
|---|---|
| `not` | Boolean negation | [Tested tests/ring0.rs::boolean_not_true]

### Extern Primitives

Extern primitives are called via the foreign function interface.

**Type conversion**:

| Function | Type | Description |
|---|---|---|
| `int-to-string` | `(Fn [Int] String)` | Convert integer to decimal string | [Tested tests/ring1.rs::string_int_to_string]
| `float-to-string` | `(Fn [Float] String)` | Convert float to string | [Tested tests/ring1.rs::string_float_to_string]
| `bool-to-string` | `(Fn [Bool] String)` | `"true"` or `"false"` | [Tested tests/ring1.rs::string_bool_to_string]
| `string-identity` | `(Fn [String] String)` | Identity for `String` (used by Display impl) | [Tested tests/ring1.rs::string_identity_returns_same]

**String operations**:

| Function | Type | Description |
|---|---|---|
| `str-concat` | `(Fn [String String] String)` | Concatenate two strings | [Tested tests/ring1.rs::string_concat]
| `str-eq` | `(Fn [String String] Bool)` | String equality (byte-wise) | [Tested tests/ring1.rs::string_eq_true]
| `str-len` | `(Fn [String] Int)` | String length in bytes | [Tested tests/ring1.rs::string_len]
| `parse-int` | `(Fn [String] (Option Int))` | Parse decimal integer; `None` on failure | [Tested tests/ring1.rs::parse_int_valid]
| `substring` | `(Fn [String Int Int] String)` | Extract substring from start (inclusive) to end (exclusive); clamps out-of-bounds indices | [R3 S14]
| `char-at` | `(Fn [String Int] String)` | Character at byte index as single-character string; empty string if out of bounds | [R3 S14]
| `split` | `(Fn [String String] (Vec String))` | Split string by separator | [R3 S14]
| `join` | `(Fn [String (Vec String)] String)` | Join strings with separator | [R3 S14]
| `replace` | `(Fn [String String String] String)` | Replace all occurrences of `from` with `to` | [R3 S14]
| `trim` | `(Fn [String] String)` | Trim leading and trailing whitespace | [R3 S14]
| `starts-with?` | `(Fn [String String] Bool)` | Test if string starts with prefix | [R3 S14]
| `ends-with?` | `(Fn [String String] Bool)` | Test if string ends with suffix | [R3 S14]
| `contains?` | `(Fn [String String] Bool)` | Test if string contains substring | [R3 S14]
| `to-upper` | `(Fn [String] String)` | Convert to uppercase | [R3 S14]
| `to-lower` | `(Fn [String] String)` | Convert to lowercase | [R3 S14]

**Macro support**:

| Function | Type | Description |
|---|---|---|
| `quote-sexp` | `(Fn [Sexp] Sexp)` | Convert a runtime `Sexp` value to constructor source code | [Tested tests/macros.rs::macro_quasiquote_repl]

**Vec operations**:

| Function | Type | Description |
|---|---|---|
| `vec-get` | `(Fn [(Vec a) Int] a)` | Index (bounds-checked; panics on out-of-bounds) | [Tested tests/ring1.rs::vec_get_first]
| `vec-set` | `(Fn [(Vec a) Int a] (Vec a))` | Return new Vec with element at index replaced | [Tested tests/ring1.rs::vec_set_element]
| `vec-push` | `(Fn [(Vec a) a] (Vec a))` | Return new Vec with element appended | [Tested tests/ring1.rs::vec_push_appends]
| `vec-len` | `(Fn [(Vec a)] Int)` | Number of elements | [Tested tests/ring1.rs::vec_len_three]
| `vec-map` | `(Fn [(Fn [a] b) (Vec a)] (Vec b))` | Map function over elements | [R3 S10]
| `vec-reduce` | `(Fn [(Fn [b a] b) b (Vec a)] b)` | Left fold over elements | [R3 S10]

`vec-set` and `vec-push` are semantically pure (return new values). The implementation MAY use copy-on-write when the reference count is 1.

## A.4 Special Forms [R3 S10]

Special forms are keywords processed directly by the compiler. They are not functions or macros and cannot be shadowed.

**Test infrastructure** — special forms, always in scope (see [repl/spec.md §16](../repl/spec.md#16-test-discovery-and-execution)):

| Form | Type | Description |
|---|---|---|
| `(discover-tests)` | `(IO (SList Sexp))` | Discover `test-*` function names in the current module. Returns `SexpSym` values. | [R4]
| `(discover-tests module)` | `(IO (SList Sexp))` | Discover `test-*` function names in the named module. `module` is a bare module path (e.g., `user.math`) — same syntax as `import`. Returns `SexpSym` values. | [R4]
| `(run-test name)` | `(IO TestResult)` | Run a single test without tracing (fast). Returns `TestPass` or `TestFail`. `name` is a bare qualified symbol (e.g., `user/test-add`) or a `Sexp` expression. | [R4]
| `(trace-test name)` | `(IO TestResult)` | Run a single test with GOT-swap tracing. Returns `TestPass` or `TraceFail`. `name` is a bare qualified symbol or a `Sexp` expression. | [R4]

## A.5 Docstrings for Builtins [R1]

All primitive functions (§A.3) and special forms (§A.4) MUST have docstrings available at runtime. The docstring for each builtin is the Description column text from the tables above (or an equivalent concise description). These docstrings MUST be accessible via the `/doc` REPL command and MUST appear in the `; classification - docstring` suffix of the universal output format (repl/spec.md §1.1) when the symbol is displayed.

| Form | Description |
|---|---|
| `defn` / `defn-` | Function definition (single or multi-sig); `defn-` is module-private | [Tested tests/ring0.rs::arithmetic_addition]
| `deftype` / `deftype-` | Algebraic data type definition; `deftype-` is module-private | [Tested tests/ring1.rs::parse_int_valid]
| `deftrait` / `deftrait-` | Trait declaration; `deftrait-` is module-private | [Tested tests/ring2.rs::user_trait_simple]
| `impl` | Trait implementation | [Tested tests/ring2.rs::trait_plus_int]
| `defmacro` / `defmacro-` | Macro definition; `defmacro-` is module-private | [Tested tests/ring3_repl::r3_defmacro_display_single_clause]
| `let` | Local bindings: `(let [x e1 y e2] body)` | [Tested tests/ring0.rs::nested_let]
| `if` | Conditional: `(if cond then else)` | [Tested tests/ring0.rs::comparison_operators]
| `fn` | Lambda expression: `(fn [params] body)` | [Tested tests/ring1.rs::closure_simple_capture]
| `match` | Pattern matching: `(match scrutinee [pat1 body1 ...])` | [Tested tests/ring1.rs::parse_int_valid]
| `mod` / `mod-` | Submodule declaration; `mod-` is module-private | [Tested tests/ring2.rs::single_file_via_run_project]
| `import` | Name import: `(import [module [names]])` | [Tested tests/ring2.rs::import_specific_names]
| `export` | Name re-export: `(export [module [names]])` | [Tested crates/cranelisp-frontend/src/module_extract.rs::test_export_specific]
| `platform` | Platform DLL declaration (entry module only): `(platform stdio)` | [R4 S9]
| `trace` | Execution trace: `(trace expr)` — evaluates `expr` with call instrumentation, returns `Trace` ADT | [R4 S20]
