# Frontend Plan — Ring 0 Reader and AST Builder

Produced by `/frontend` for Sprint 0, Task 5. This document plans the Ring 0 implementation of the `cranelisp-frontend` crate: the S-expression reader and the AST builder. No macros are included (Ring 3).

## 1. PEG Crate Choice

### Evaluation

| Crate | Style | Pros | Cons |
|---|---|---|---|
| `peg` 0.8 | PEG macro (`peg::parser!{}`) | Used by prototype; proven for this grammar; zero-copy position tracking; readable inline grammar; fast compile times | Proc macro grammar not separately testable as data; error messages can be opaque |
| `pest` | External `.pest` grammar file | Grammar in a separate file (reviewable); excellent error reporting; well-documented | Heavier dependency; grammar file is another asset to manage; pairs-based API requires more boilerplate to build Sexp |
| `nom` | Combinator functions | Maximum flexibility; pure Rust functions; easy to test individual parsers | Verbose for this grammar size; harder to read at a glance; more code to maintain |
| `winnow` | Fork of nom | Improved error handling over nom; streaming support | Same verbosity issues as nom; newer, smaller ecosystem |
| `chumsky` | Parser combinators with error recovery | Best-in-class error recovery; designed for programming languages | Heavy compile times; complex API; overkill for an S-expression grammar |
| Hand-written | Recursive descent | Full control; zero dependencies; best possible error messages | More code; more surface area for bugs; no grammar-as-specification benefit |

### Decision: `peg` 0.8

**Rationale**:

1. **Proven**: The prototype uses `peg` 0.8 and it handles the full Cranelisp grammar (58 KB of parser, ~400 lines of grammar rules, ~980 tests pass). The grammar is not novel -- it is an S-expression reader with a handful of reader macros. There is no risk that `peg` cannot handle it.

2. **Appropriate complexity**: S-expression grammars are simple. The token precedence (float before integer before operator, etc.) maps directly to PEG's ordered choice (`/`). A combinator library or hand-written parser would be more code for no benefit.

3. **Position tracking**: `peg` provides `position!()` for byte offsets. The prototype uses `(usize, usize)` spans; the reimplementation uses `Span { start: u32, end: u32 }`. The conversion is a cast at the grammar boundary.

4. **Compile time**: `peg` generates code at compile time via proc macro. It compiles fast and produces efficient parsers. No runtime grammar interpretation.

5. **Familiarity**: The prototype grammar is a tested reference. The reimplementation grammar will be structurally identical (same rules, same ordering), with two changes: `Span` struct instead of tuple, and `String` newtype conversions.

**Risk**: `peg` error messages on malformed input can be unhelpful (e.g., "expected one of: ..."). This is acceptable for Ring 0. If error quality becomes a blocking usability finding, we can add a post-parse error enhancement pass that maps common PEG failures to user-friendly messages. This is cheaper than switching parsers.

## 2. Ring 0 Grammar Rules

The reader must parse **all** lexical forms from spec `01-lexical.md` so that error messages are correct even for features not yet supported at the AST level. The AST builder then rejects non-Ring-0 forms with clear errors.

### 2.1 Whitespace and Comments

```
rule comment() = ";" [^ '\n']* ("\n" / ![_])
rule ws() = ([' ' | '\t' | '\n' | '\r' | ','] / comment())*
```

Comma is whitespace (Clojure convention, spec 1.2).

### 2.2 Atoms (Token Precedence)

The atom rule tries alternatives in the order specified by spec 1.7:

```
rule atom() -> Sexp
    = v:float()             { Sexp::Float(v.0, v.1) }     // 1. Float before integer
    / v:integer()           { Sexp::Int(v.0, v.1) }       // 2. Integer before operator
    / v:boolean()           { Sexp::Bool(v.0, v.1) }      // 3. Boolean
    / v:string_literal()    { Sexp::Str(v.0, v.1) }       // 4. String
    / v:colon_prefix()      { Sexp::Symbol(v.0, v.1) }    // 5. Colon-prefix (:Int, :a)
    / v:colon_bare()        { Sexp::Symbol(v.0, v.1) }    // 6. Bare colon (:)
    / v:ampersand()         { Sexp::Symbol(v.0, v.1) }    // 7. Ampersand (&)
    / v:qualified_symbol()  { Sexp::Symbol(v.0, v.1) }    // 8. Qualified (mod/name)
    / v:dotted_symbol()     { Sexp::Symbol(v.0, v.1) }    // 9. Dotted (Type.member)
    / v:gensym_symbol()     { Sexp::Symbol(v.0, v.1) }    // 10. Gensym (x#)
    / v:percent_param()     { Sexp::Symbol(v.0, v.1) }    // 11. Percent (%1, %)
    / v:operator_symbol()   { Sexp::Symbol(v.0, v.1) }    // 12. Operator (+, <=)
    / v:symbol()            { Sexp::Symbol(v.0, v.1) }    // 13. Simple symbol
```

### 2.3 Individual Token Rules

Each rule corresponds to a spec section:

| Rule | Spec | Ring 0 Notes |
|---|---|---|
| `float()` | 1.3.2 | `-?` digits `.` digits. Both parts required. |
| `integer()` | 1.3.1 | `+` digits OR `-?` digits. `+` variant tried first. |
| `boolean()` | 1.3.3 | `true`/`false` with negative lookahead `!symbol_char()` |
| `string_literal()` | 1.3.4 | Escape sequences: `\n`, `\t`, `\\`, `\"`. Parsed to `Sexp::Str`. |
| `colon_prefix()` | 1.4.5 | `:` followed by alpha/underscore + symbol_char*. |
| `colon_bare()` | 1.4.5 | `:` not followed by symbol_char. |
| `ampersand()` | 1.4.8 | `&` not followed by symbol_char. |
| `qualified_symbol()` | 1.4.3 | module_path `/` local_name. Module may contain dots. |
| `dotted_symbol()` | 1.4.4 | parent `.` member. Member may be symbol_chars or operator_chars. |
| `gensym_symbol()` | 1.4.6 | symbol `#`. (Ring 3, but reader must parse.) |
| `percent_param()` | 1.4.7 | `%` optionally followed by `1`-`9`. (Ring 3, but reader must parse.) |
| `operator_symbol()` | 1.4.2 | `operator_char()+` with `!digit` lookahead. |
| `symbol()` | 1.4.1 | Alpha/underscore start, then symbol_char*. |

### 2.4 Composite Forms

```
rule list()    -> Sexp = "(" ws() form()* ws() ")"
rule bracket() -> Sexp = "[" ws() form()* ws() "]"
```

### 2.5 Reader Macros

```
rule quote_reader()       = "'" form()        // -> (quote <form>)
rule quasiquote()         = "`" form()        // -> (quasiquote <form>)
rule unquote_splicing()   = "~@" form()       // -> (unquote-splicing <form>)
rule unquote()            = "~" form()        // -> (unquote <form>)
rule anon_fn()            = "#(" form()* ")"  // -> (fn [%1..%N] (body))
```

Ordering in the `form()` rule follows spec 1.6: `quote` before `quasiquote`, `unquote_splicing` before `unquote`, `anon_fn` before `list`.

### 2.6 Public Entry Points

```rust
pub fn parse_sexp(input: &str) -> Result<Sexp, CranelispError>;
pub fn parse_sexps(input: &str) -> Result<Vec<Sexp>, CranelispError>;
```

Error mapping: PEG's `ParseError` (offset + expected set) is converted to `CranelispError::ParseError { message, span }` at the public boundary.

### 2.7 `$` Reader Macro

The prototype has a `dollar_sym()` rule that expands `$name` to `(SexpSym name)`. This is used in macro bodies to construct `Sexp` values. Since macros are Ring 3, the reader should still parse `$` syntax from Ring 0 (so that error messages are correct for files that happen to contain it), but the AST builder need not handle it until Ring 3.

## 3. Sexp to Expr Mapping (Ring 0)

The AST builder transforms `Sexp` trees into `Expr` and `TopLevel` AST nodes. Ring 0 covers the following mappings.

### 3.1 Expression Forms

| Sexp shape | Expr variant | Ring | Spec |
|---|---|---|---|
| `Sexp::Int(v, span)` | `IntLit { value, span }` | 0 | 4.1 |
| `Sexp::Float(v, span)` | `FloatLit { value, span }` | 0 | 4.1 |
| `Sexp::Bool(v, span)` | `BoolLit { value, span }` | 0 | 4.1 |
| `Sexp::Str(v, span)` | **Rejected** in Ring 0 (clear error: "strings not yet supported") | 1 | 4.1 |
| `Sexp::Symbol(name, span)` | `Var { name, span }` | 0 | 4.2 |
| `(let [name val ...] body)` | `Let { bindings, body, span }` | 0 | 4.3 |
| `(if cond then else)` | `If { cond, then_branch, else_branch, span }` | 0 | 4.4 |
| `(fn [params] body)` | `Lambda { params, param_annotations, body, span }` | 0 | 4.5 |
| `(f arg1 arg2 ...)` | `Apply { callee, args, span }` | 0 | 4.6 |
| `(match scrut [pat body ...])` | `Match { scrutinee, arms, span, compiler_generated: false }` | 0 | 4.8 |
| `:Type expr` (annotation) | `Annotate { annotation, expr, span }` | 0 | 4.9 |
| `Sexp::Bracket(elems, span)` in expr position | **Rejected** in Ring 0 (clear error: "Vec literals not yet supported") | 1 | 4.10 |
| `(vec ...)` | **Rejected** in Ring 0 | 1 | 4.10 |
| `(trace ...)` | **Rejected** in Ring 0 | 4 | 12 |


### 3.2 Annotation Handling

Annotations appear as inline `Sexp` tokens that must be consumed greedily. The AST builder uses a `try_consume_annotation()` helper that examines items at a given position:

1. `:Name` (colon-prefix symbol, `s.len() > 1`) -- parses as `TypeExpr::Named` (uppercase) or `TypeExpr::TypeVar` (lowercase) or `TypeExpr::SelfType` ("self")
2. `:` `(Fn [...] ret)` or `(Name args...)` (bare colon followed by list) -- parses compound annotation via `build_type_expr()`

This helper is used in three contexts:
- **Parameter lists**: `[:Int x :a y]` -- annotation precedes parameter name
- **Let bindings**: `[x :Int 42]` -- annotation precedes binding value
- **Expression arguments**: `(f :Int 42)` -- annotation wraps argument as `Annotate`
- **Top-level REPL**: `:Int 42` -- two sexp forms combine into one `Annotate`

### 3.3 Pattern Building (Ring 0)

Patterns appear in `match` arms. The builder dispatches on Sexp variant:

| Sexp shape | Pattern variant | Ring 0 constraint |
|---|---|---|
| `Sexp::Symbol("_", span)` | `Wildcard { span }` | Fully exercised |
| `Sexp::Symbol(UpperName, span)` | `Constructor { name, bindings: [], span }` | Nullary only in Ring 0 |
| `Sexp::Symbol(lower, span)` | `Var { name, span }` | Fully exercised |
| `Sexp::List([UpperName, var1, var2, ...], span)` | `Constructor { name, bindings, span }` | Ring 1 (data constructors) |

Ring 0 constraint: `Constructor` patterns have empty `bindings` because only enum-only ADTs exist. The builder should accept the full syntax from Ring 0 (including `(Some x)` constructor patterns) so that error messages are correct; the **typechecker** is responsible for rejecting data constructors that do not exist.

### 3.4 TypeExpr Building

| Sexp shape | TypeExpr variant | Ring 0 |
|---|---|---|
| `Symbol(uppercase)` | `Named(TypeName)` | Yes |
| `Symbol("self")` | `SelfType` | Defined, Ring 2 |
| `Symbol(lowercase)` | `TypeVar(Symbol)` | Yes |
| `(Fn [types...] ret)` | `FnType(params, ret)` | Yes |
| `(Name args...)` | `Applied(TypeName, args)` | Defined, Ring 1+ |

### 3.5 TopLevel Forms

| Sexp shape | TopLevel variant | Ring 0 |
|---|---|---|
| `(defn name "doc"? [params] body)` | `Defn(Defn { ... })` | Yes |
| `(defn- name "doc"? [params] body)` | `Defn(Defn { visibility: Private, ... })` | Yes |
| `(defn name "doc"? (variant1) (variant2) ...)` | `DefnMulti { ... }` | Defined, Ring 2 |
| `(deftype Head "doc"? [fields])` | `TypeDef { ... }` (product) | Ring 1 (fields) |
| `(deftype Head "doc"? Ctor1 Ctor2 ...)` | `TypeDef { ... }` (sum/enum) | Yes (nullary only) |
| `(deftype- ...)` | `TypeDef { visibility: Private, ... }` | Yes |
| `(deftrait ...)` | `TraitDecl(...)` | Defined, Ring 2 |
| `(impl ...)` | `TraitImpl(...)` | Defined, Ring 2 |
| `(defmacro ...)` | **Error**: "should be handled before AST building" | Ring 3 |
| `(begin ...)` | **Error**: "should be handled before AST building" | Ring 3 |
| `(mod ...)` / `(import ...)` / `(export ...)` / `(platform ...)` | **Error**: "should be handled before AST building" | Ring 2 |

Detection of single vs. multi-signature `defn`: if the form after the name (and optional docstring) is a `Bracket`, it is single-sig; if it is a `List`, it is multi-sig.

### 3.6 ReplInput Forms

`ReplInput` wraps `TopLevel` plus bare expressions. The builder tries top-level forms first, then falls back to expression building. In Ring 0:

- `(defn ...)` / `(defn- ...)` -- `ReplInput::Defn`
- `(deftype ...)` / `(deftype- ...)` -- `ReplInput::TypeDef`
- Everything else -- `ReplInput::Expr`

Multi-sexp REPL input (e.g., `:Int 42` as two forms) is handled by `build_repl_input_from_sexps`, which calls `build_args_with_annotations` to combine annotation + value into a single `Annotate` expression.

### 3.7 `desugar_type_def`

The prototype's `ast.rs` contains a `desugar_type_def()` function that handles the shortcut syntax for bare field names. When a field has no type annotation, it is assigned `TypeExpr::TypeVar("")` (empty string sentinel). The desugaring pass:

1. Collects all bare fields across all constructors
2. Assigns type variables `a`, `b`, `c`, ... in first-appearance order
3. Replaces empty `TypeVar` with the assigned variable
4. Merges explicit type params with inferred ones

This function should live in `cranelisp-frontend` (it is a syntactic desugaring, not a type system operation). In Ring 0, it will only encounter the enum case (no fields), so it is exercised trivially. The implementation should be complete from the start so Ring 1 does not require rework.

## 4. Known Gotchas from the Prototype

### 4.1 `-3` Must Parse as Integer, Not Operator

The grammar must try `integer()` before `operator_symbol()` in the atom rule. The operator rule uses `!['0'..='9']` negative lookahead to prevent `-3` from matching as `-` followed by `3`. Spec 1.7 is explicit about this ordering.

### 4.2 Float Before Integer

`3.14` must parse as float, not integer `3` followed by `.14`. The atom rule tries `float()` before `integer()`. Spec 1.3.2 notes this.

### 4.3 Boolean Boundary: `trueness` is a Symbol

`true` and `false` must NOT be followed by a `symbol_char`. The prototype uses `!symbol_char()` negative lookahead: `"true" !symbol_char()`. Without this, `trueness` would parse as `true` + `ness`.

### 4.4 Qualified vs. Dotted vs. Simple Symbol Ordering

Qualified symbols (`mod/name`) must be tried before dotted symbols (`Type.method`) because qualified can contain a dot in the module path. Dotted must be tried before simple because `Type.method` is a longer match than `Type`. The prototype's ordering is: qualified -> dotted -> gensym -> percent -> operator -> simple. Spec 1.7 makes this ordering normative.

### 4.5 Operator `!digit` Lookahead

Operator symbols use `operator_char()+ !['0'..='9']` to prevent `-3` from being consumed as operator `-` followed by integer `3`. Without the digit lookahead, the ordered choice would greedily match `-` as an operator before `integer()` had a chance.

### 4.6 `+3` Explicit Positive Integer

The prototype supports `+3` as an explicit positive integer. The `integer()` rule has two alternatives: `"+" digits` and `-? digits`. The `+` variant must be tried first (it consumes the `+` sign that would otherwise match as an operator). Without this, `+3` would parse as `Apply(+, 3)` inside a list.

### 4.7 Annotation Greediness in Parameter Lists

The annotation consumer `try_consume_annotation()` must be greedy: when it sees `:Int`, it must check whether the next token is a parameter name (and consume both) or whether `:Int` stands alone. In parameter lists, `:Int x` means "x has type Int". In argument lists, `:Int 42` means `Annotate(Int, 42)`. The context is the same algorithm; the interpretation differs based on whether names vs. expressions follow.

### 4.8 Let Binding Annotations

Let bindings support annotations: `(let [x :Int 42] ...)`. The binding parser must call `build_one_expr_at()` which handles the annotation case. This produces `(x, Annotate(Int, 42))` as the binding.

### 4.9 Bare Colon vs. Colon-Prefix

`:Int` (colon immediately followed by uppercase) is a colon-prefix token. `: (Option Int)` (colon + space + list) is a bare colon followed by a list. The reader treats these as two separate tokens (`Sexp::Symbol(":", ...)` and `Sexp::List(...)`). The AST builder's `try_consume_annotation()` handles the bare-colon case by looking ahead to the next sexp.

### 4.10 Empty Application Error

`()` (empty list) is a valid Sexp but not a valid expression. The AST builder must produce a clear error ("empty application"). The reader does NOT reject it.

### 4.11 `defn` Name Can Be an Operator

`(defn + [x y] ...)` is valid -- the function name can be an operator symbol. The `get_defn_name()` helper accepts any symbol, not just identifiers.

### 4.12 Docstring Detection

Optional docstrings are detected by checking if `children[start]` is `Sexp::Str`. This means string literals in this position are always consumed as docstrings, not as body expressions. Since Ring 0 does not support strings, this is a non-issue at Ring 0. When strings are added (Ring 1), the docstring rule is unambiguous because `defn`/`deftype`/`deftrait` always have a structural element (param list, type head, method sig) after the docstring position.

### 4.13 Span Type Change: Tuple to Struct

The prototype uses `type Span = (usize, usize)`. The reimplementation uses `struct Span { start: u32, end: u32 }`. All reader code that constructs spans must use `Span::new(start as u32, end as u32)` instead of tuple construction. The PEG `position!()` macro returns `usize`; the cast to `u32` is safe for source files under 4 GB.

### 4.14 String Newtypes: `Symbol` Instead of `String`

The prototype stores all identifiers as bare `String`. The reimplementation uses `Symbol` (and `TypeName`, etc.). The reader produces `Sexp::Symbol(String, Span)` with a bare `String` (the raw text). The AST builder converts to `Symbol` at the Sexp-to-Expr boundary. This is the correct layering: the reader is format-agnostic, the AST builder is type-aware.

### 4.15 `$` (Dollar-Sign) Reader Macro

The prototype has a `dollar_sym()` rule for `$name` and `$(expr)` that expands to `(SexpSym ...)`. This is used in macro bodies (Ring 3). The reimplementation reader should include this rule from the start so that source files containing `$` syntax parse without error, even though the AST builder will not handle it until Ring 3.

### 4.16 `anon_fn` Body Wrapping

The `#(...)` reader macro wraps the entire body as a *list* (not just the forms): `#(+ %1 %2)` becomes `(fn [%1 %2] (+ %1 %2))`. The `build_anon_fn()` function collects percent params, normalizes bare `%` to `%1`, and builds the `(fn ...)` form. This is a reader-level transformation, not AST-level. It should be ported as-is.

## 5. Module Structure for `cranelisp-frontend`

### 5.1 Crate Dependencies

```toml
[dependencies]
cranelisp-types = { path = "../cranelisp-types" }
peg = "0.8"
```

No other dependencies. The frontend crate is self-contained.

### 5.2 Source Layout

```
cranelisp-frontend/
  src/
    lib.rs            # pub mod declarations, re-exports
    reader.rs         # PEG grammar, parse_sexp(), parse_sexps()
    ast_builder.rs    # Sexp -> Expr, TopLevel, ReplInput
    desugar.rs        # desugar_type_def() (type shortcut syntax)
    CLAUDE.md         # Frontend-specific conventions
```

**Rationale for flat structure**: The prototype uses `sexp.rs` and `ast_builder.rs` as flat files. The reimplementation grammar is structurally identical. There is no benefit to a directory structure (`reader/`, `ast_builder/`) for Ring 0. If the macro expander (Ring 3) grows large enough to need subdirectories, that restructuring happens at Ring 3.

### 5.3 Public API

```rust
// reader.rs
pub fn parse_sexp(input: &str) -> Result<Sexp, CranelispError>;
pub fn parse_sexps(input: &str) -> Result<Vec<Sexp>, CranelispError>;

// ast_builder.rs
pub fn build_program(sexps: &[Sexp]) -> Result<Program, CranelispError>;
pub fn build_repl_input(sexp: &Sexp) -> Result<ReplInput, CranelispError>;
pub fn build_repl_input_from_sexps(sexps: &[Sexp]) -> Result<ReplInput, CranelispError>;
pub fn build_expr(sexp: &Sexp) -> Result<Expr, CranelispError>;

// desugar.rs
pub fn desugar_type_def(
    type_name: &TypeName,
    explicit_params: &[Symbol],
    constructors: &[ConstructorDef],
) -> (Vec<Symbol>, Vec<ConstructorDef>);
```

Note: The prototype combines `parse_program()` (read + build in one call) and `parse_repl_input()`. The reimplementation should keep the two-phase API (`parse_sexps` then `build_program`) as the primary interface, with convenience wrappers if needed. This allows callers to inspect the intermediate `Sexp` (used for REPL `/sexp` command and `DefCodegen.sexp` storage).

### 5.4 `MacroExpander` Trait

The `MacroExpander` trait is defined in `cranelisp-frontend` (or `cranelisp-types`; per `interfaces.md` it is in frontend). The AST builder accepts an `&mut dyn MacroExpander` parameter. In Ring 0, the binary crate provides a `NoOpExpander` that always returns `false` for `is_macro()`. The AST builder calls `is_macro()` before treating any list head as a function application.

In Ring 0, the `build_program` and `build_repl_input` functions can omit the expander parameter entirely (no macro calls exist). When Ring 3 adds macros, the signatures change to accept `&mut dyn MacroExpander`. This is a clean extension point.

**Ring 0 approach**: Do NOT pass a `MacroExpander` to Ring 0 functions. The AST builder does not call any macro expansion. The safety-net errors for `defmacro`/`begin` are sufficient.

## 6. Interface Gaps and Observations

### 6.1 `Sexp::Symbol` Uses Bare `String`, Not `Symbol` Newtype

`interfaces.md` defines `Sexp::Symbol(String, Span)` -- the first field is a bare `String`, not a `Symbol` newtype. This is intentional: the reader does not know whether a symbol is a variable name, type name, module path, or operator. The semantic classification happens in the AST builder when converting to `Expr::Var { name: Symbol, ... }`, `TypeExpr::Named(TypeName)`, etc.

**No gap**: this is the correct design. The reader is syntactic; the AST builder is semantic.

### 6.2 `FieldDef.type_expr` Sentinel for Bare Fields

The prototype uses `TypeExpr::TypeVar(String::new())` (empty string) as a sentinel for bare field names in the shortcut syntax `(deftype Pair [first second])`. The `desugar_type_def` function replaces these with assigned type variables.

**Observation**: Using an empty string as a sentinel is fragile. Consider adding an explicit variant or using `Option<TypeExpr>` for field type expressions. However, since the spec explicitly defines bare fields as getting "a fresh type variable" (spec 2.2.2), and the empty-string sentinel is local to the frontend crate (not visible across the boundary), this is acceptable. The `FieldDef` in `cranelisp-types` always has a resolved `TypeExpr` after desugaring.

**No gap**: the sentinel is internal to the frontend.

### 6.3 `TraitImpl.type_args` Uses `Vec<Symbol>` Not `Vec<TypeExpr>`

The `TraitImpl` struct in `interfaces.md` stores `type_args: Vec<Symbol>` -- these are the type parameters in `(impl Display (Option a) ...)`. The prototype's `build_impl_target()` extracts these as strings. The reimplementation should use `Symbol` (which it does).

**No gap**: consistent with `interfaces.md`.

### 6.4 REPL Display Format Affects Frontend Minimally

The REPL spec (`repl/spec.md`) defines the `:Type value` output format. This does NOT affect the frontend -- the display formatting is done by the binary crate's REPL handler using type information from the typechecker. The frontend's job is to produce AST; display is downstream.

**No gap**: frontend is not responsible for display formatting.

### 6.5 `compiler_generated` Field on `Match`

The `Match` variant has a `compiler_generated: bool` field. The AST builder always sets this to `false` for user-written `match` expressions. The macro expander (Ring 3) may set it to `true` for compiler-generated matches (e.g., from `cond` or `case` macro expansion). Ring 0 can ignore this field (always `false`).

### 6.6 `Expr` Has No `Do` Variant

The spec mentions `do` (in the context of IO monads, spec 2.3.6 note). `do` is a prelude macro, not a special form. It does not appear in the `Expr` enum. The AST builder does not need to handle it. This is correct -- `do` expands to nested `bind` calls during macro expansion (Ring 3).

### 6.7 `par-let` Removed from Spec

The spec originally had `par-let` (spec 4.12), which has been removed. Lenient evaluation (spec 12.4.3) supersedes it. The `Expr` enum has no `ParLet` variant. The prototype's `build_par_let` should NOT be ported. If the user writes `(par-let ...)`, the AST builder should produce an error: "par-let is not supported; use let with lenient evaluation".

## 7. Testing Strategy

### 7.1 Reader Unit Tests

Port the prototype's reader tests (lines 420-599 in `sketch/src/sexp.rs`) with adaptations:
- `Span` struct instead of tuple
- Test every token rule from spec 1.7 ordering
- Test negative cases: malformed floats (`.5`, `3.`), unterminated strings, unmatched parens
- Test comma-as-whitespace

### 7.2 AST Builder Unit Tests

Port the prototype's AST builder tests (lines 1323+ in `sketch/src/ast_builder.rs`) with adaptations:
- `Symbol` newtype instead of bare `String`
- Test Ring 0 rejection of `Sexp::Str` with clear error message
- Test Ring 0 rejection of `VecLit` with clear error message
- Test all Ring 0 expression forms
- Test annotation handling in all contexts (params, let bindings, arguments, REPL)
- Test `defn` single-sig and `deftype` enum-only

### 7.3 Integration Boundary

Integration tests (owned by `/qa`) will exercise the full parse-then-build pipeline. The frontend's own tests should be pure unit tests that construct `Sexp` values directly (for AST builder) or parse strings (for reader), without needing the typechecker or backend.

## 8. Implementation Order

1. **`cranelisp-types` stubs** (by `/arch`): Ensure `Sexp`, `Span`, `Expr`, `TopLevel`, `Pattern`, `MatchArm`, `TypeExpr`, `FieldDef`, `ConstructorDef`, `Defn`, `DefnVariant`, `Visibility`, `Program`, `ReplInput`, `CranelispError` are defined.

2. **`reader.rs`**: Port the PEG grammar from `sketch/src/sexp.rs`. Change `Span` from tuple to struct. Add `parse_sexp()` and `parse_sexps()` public functions. Port and adapt unit tests.

3. **`desugar.rs`**: Port `desugar_type_def()` from `sketch/src/ast.rs`. Adapt for `Symbol`/`TypeName` newtypes.

4. **`ast_builder.rs`**: Port expression builders from `sketch/src/ast_builder.rs`. Add Ring 0 rejection errors for `Sexp::Str`, `VecLit`, `trace`, `par-let`. Port and adapt unit tests.

5. **Wiring**: Update `lib.rs` with public re-exports. Verify `cargo check` passes for the `cranelisp-frontend` crate in isolation.

## Next skills

- `/typecheck` -- Can begin Ring 0 inference implementation once the `Expr`/`TopLevel` types are populated by the frontend. The frontend produces the input; the typechecker is the next consumer.
- `/backend` -- Can begin Ring 0 codegen in parallel with typecheck, working from the same `Expr`/`TopLevel` types.
- `/qa` -- Can begin writing Ring 0 integration tests that exercise the full reader -> AST builder pipeline once the frontend crate compiles.
