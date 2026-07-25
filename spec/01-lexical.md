# 1. Lexical Structure [Tested]

This section defines the lexical grammar of Cranelisp — the rules for converting source text into tokens.

## 1.1 Source Encoding [Tested tests/spec_12_runtime::string_utf8_source_encoding_accepted]

Source text MUST be valid UTF-8.

## 1.2 Whitespace and Comments [Tested]

Whitespace separates tokens but is otherwise insignificant. The following are whitespace:

- Space (U+0020)
- Tab (U+0009)
- Newline (U+000A)
- Carriage return (U+000D)
- Comma (U+002C) — commas are whitespace, following Clojure convention [Tested crates/cranelisp-frontend/src/reader.rs::test_commas_are_whitespace]

```ebnf
ws        = (ws_char | comment)*
ws_char   = ' ' | '\t' | '\n' | '\r' | ','
comment   = ';' [^ '\n']* ('\n' | EOF)
```

Line comments begin with `;` and extend to the end of the line (or end of input). [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_with_comment]

```clojure
; this is a comment
(+ 1 2)   ; inline comment
[1, 2, 3] ; commas are whitespace, equivalent to [1 2 3]
```

> **Note (leading comment block — module preamble).** Comments are ordinarily insignificant. One position is an exception: a **contiguous `;;` comment block at the very top of a file**, running up to the first form, has the **module preamble** role (§8.16) — file-header documentation for the module as a whole. The reader does not discard it; it is preserved via `Sexp::Comment` (added Sprint 24) and surfaced so the frontend can associate the captured text with the module. A blank line breaks the leading block, and comments after the first form are ordinary comments. This is purely positional — the lexer treats the tokens as ordinary line comments; §8.16 assigns the role.

## 1.3 Literals [Tested]

### 1.3.1 Integer Literals [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_integer_literal]

```ebnf
integer   = '+' digit+
          | '-'? digit+
digit     = '0' | '1' | ... | '9'
```

Integer literals represent signed 64-bit integers. The range is -2^63 to 2^63 - 1. A leading `+` sign is permitted. A leading `-` sign indicates a negative value.

```clojure
42        ; positive integer
-7        ; negative integer
+3        ; explicit positive
0         ; zero
```

Note: The parser attempts integer before operator, so `-3` is parsed as the integer negative three, not the operator `-` followed by `3`.

### 1.3.2 Float Literals [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_float_literal]

```ebnf
float     = '-'? digit+ '.' digit+
```

Float literals represent IEEE 754 double-precision (64-bit) floating-point numbers. Both the integer and fractional parts are required — `.5` and `3.` are not valid.

```clojure
3.14      ; positive float
-0.5      ; negative float
0.0       ; zero as float
```

Note: The parser attempts float before integer, so `3.14` is parsed as a float, not the integer `3` followed by `.14`.

### 1.3.3 Boolean Literals [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_true]

```ebnf
boolean   = 'true' !symbol_char
          | 'false' !symbol_char
```

The keywords `true` and `false` are boolean literals. They MUST NOT be followed by a symbol character — `trueness` is a symbol, not a boolean. [Tested crates/cranelisp-frontend/src/reader.rs::test_true_prefix_is_symbol]

### 1.3.4 String Literals [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_string]

```ebnf
string    = '"' string_char* '"'
string_char = '\\n'             ; newline (U+000A)
            | '\\t'             ; tab (U+0009)
            | '\\\\'            ; backslash (U+005C)
            | '\\"'             ; double quote (U+0022)
            | [^ '"' | '\\']   ; any character except quote or backslash
```

String literals are enclosed in double quotes. The following escape sequences are recognized:

| Escape | Character |
|---|---|
| `\n` | Newline (U+000A) [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_string_escapes] |
| `\t` | Tab (U+0009) |
| `\\` | Backslash |
| `\"` | Double quote [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_string_escaped_quote] |

```clojure
"hello"           ; simple string
"line1\nline2"    ; string with newline
"she said \"hi\"" ; escaped quotes
""                ; empty string
```

> **Note (leading-string roles).** A bare string literal is lexically a single token wherever it appears; its *role* is positional. As the leading form of a definition it is a docstring (§5.12); elsewhere it is an ordinary string value. The lexer does not distinguish these — the position does. (The **module preamble** (§8.16) is *not* a leading string literal — it is the contiguous leading `;;` comment block at the head of a file; see the comment note in §1.2.)

## 1.4 Symbols [Tested]

### 1.4.1 Simple Symbols [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_simple_symbol, Tested crates/cranelisp-frontend/src/reader/tests.rs::test_parse_symbol_with_interior_arrow, crates/cranelisp-frontend/src/reader/tests.rs::test_parse_symbol_with_interior_arrow_minimal, crates/cranelisp-frontend/src/reader/tests.rs::test_parse_symbol_with_interior_le, tests/spec_05_definitions.rs::defn_name_with_arrow_in_symbol_parses]

```ebnf
symbol         = symbol_start (symbol_char | interior_op_run)*
symbol_start   = 'a'-'z' | 'A'-'Z' | '_'
symbol_char    = 'a'-'z' | 'A'-'Z' | '0'-'9' | '_' | '-' | '?' | '!'
interior_op    = '+' | '*' | '=' | '<' | '>'
interior_op_run = interior_op+ &symbol_char    (* absorbed only when followed by a symbol_char *)
```

Symbols are identifiers. They start with a letter or underscore, followed by any combination of letters, digits, underscores, hyphens, question marks, and exclamation marks.

```clojure
foo           ; simple symbol
my-func       ; hyphens allowed
empty?        ; question mark allowed
do!           ; exclamation mark allowed
_private      ; underscore start
Point         ; uppercase (typically types/constructors)
```

**Interior operator characters.** A symbol that has already started (with `symbol_start`) MAY contain a run of operator characters from the set `interior_op` (`+ * = < >`) **when that run is immediately followed by another `symbol_char`** — the run is then *interior* to the symbol and absorbed into the token. A run of operator characters at the **end** of an identifier (a *trailing* run, with no following `symbol_char`) is NOT absorbed: it is left for the operator reader and tokenizes as a separate operator symbol (§1.4.2). The hyphen, `?`, and `!` are already `symbol_char` and need no special treatment; the qualifier `/` (§1.4.3) and the dot `.` (§1.4.4) are structurally significant and are NEVER absorbed as interior operator characters.

```clojure
char->digit   ; ONE symbol — the interior `->` run is followed by `digit`
a->b          ; ONE symbol — minimal interior-operator form
clamp<=hi     ; ONE symbol — interior `<=` run followed by `hi`
(-> x f)      ; the head is the standalone `->` threading operator (§1.4.2),
              ;   not a symbol — `->` has no following symbol_char
a <= b        ; THREE tokens — `a`, the operator `<=`, and `b`
foo ->        ; TWO tokens — symbol `foo` then the trailing operator `->`
```

A token whose FIRST character is an operator character is an operator symbol (§1.4.2), never a simple symbol — interior absorption applies only after a `symbol_start` has begun the token.

### 1.4.2 Operator Symbols [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_operator_plus, Tested crates/cranelisp-frontend/src/reader/tests.rs::test_symbol_then_standalone_arrow_not_merged, crates/cranelisp-frontend/src/reader/tests.rs::test_threading_arrow_head_still_standalone]

```ebnf
operator_symbol = operator_char+ !digit
operator_char   = '+' | '-' | '*' | '/' | '=' | '<' | '>'
```

Operator symbols are sequences of operator characters. They MUST NOT be immediately followed by a digit — this prevents `-3` from being parsed as the operator `-` followed by `3`.

An operator run is a *standalone* operator symbol whenever it is not interior to an alphabetic-started identifier (see §1.4.1) — i.e. when it does not directly follow a `symbol_start`-begun token body, or when it is a trailing run not followed by a `symbol_char`. Thus `->` in `(-> x f)` is the threading operator, `<=` in `a <= b` is the comparison operator, and the trailing `->` in `foo ->` is a separate operator token, even though the same characters appear interior to `char->digit` and `clamp<=hi`.

```clojure
+             ; addition
<=            ; less-or-equal
->            ; arrow (used in threading macros)
->>           ; thread-last
**            ; user-defined operator
```

Note: Operators are ordinary symbols — they have no special syntactic status. They are trait methods resolved through the same dispatch as any other function.

### 1.4.3 Qualified Symbols [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_qualified_symbol]

```ebnf
qualified_symbol = module_path '/' local_name

module_path      = segment ('.' segment)*
segment          = symbol_start symbol_char*

local_name       = symbol_start symbol_char* '.' (symbol_char+ | operator_char+)
                 | symbol_start symbol_char*
                 | operator_char+
```

Qualified symbols reference a name in a specific module. The module path and local name are separated by `/`. A qualified symbol contains **exactly one** `/`; `module_path` is the dot-separated form on the left side of the `/`, and `local_name` is the single (possibly dotted or operator) symbol on the right.

```clojure
math/sin          ; function 'sin' in module 'math'
core.io/pure      ; function 'pure' in module 'core.io'
math/+            ; operator '+' in module 'math'
option/Option.Some ; dotted name in module 'option'
```

Module aliases (from aliased imports per §8.3.4 and module mounts on export per §8.4.4) substitute **within `module_path`** — i.e., on dot-separated segments to the left of the single `/`. There is no two-slash notation: writing `A/str/foo` to mean "module `A`'s `str` alias, name `foo`" is a syntax error. The correct form is `A.str/foo`, where `str` is a segment of `module_path` that the resolver replaces via `A`'s alias table during resolution (see §8.6.6).

### 1.4.4 Dotted Symbols [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_dotted_symbol]

```ebnf
dotted_symbol = symbol_start symbol_char* '.' (symbol_char+ | operator_char+)
```

Dotted symbols access a member of a type or trait.

```clojure
Option.Some       ; constructor 'Some' of type 'Option'
Display.show      ; method 'show' of trait 'Display'
Num.+             ; operator '+' of trait 'Num'
```

### 1.4.5 Colon-Prefixed Symbols [Uncovered S115 — was crates/cranelisp-frontend/src/reader.rs::test_parse_colon_prefix, tests/spec_08_modules.rs::annotation_binds_top_level_following_form, tests/spec_08_modules.rs::annotation_in_paren_is_application_of_annotated_element]

```ebnf
colon_prefix = ':' symbol_start symbol_char*
colon_bare   = ':' !symbol_char
```

Colon-prefixed symbols are used for type annotations. A bare colon `:` (not immediately followed by a symbol character) is the same annotation introducer whose type form follows either parenthesised (`:(Fn [a] a)`) or separated from the colon by whitespace (`: Int`, see the S114 note below). [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_bare_colon]

```clojure
:Int              ; type annotation
:Num              ; trait constraint
:Display          ; trait constraint
:                 ; bare colon — annotation introducer for a parenthesised or whitespace-separated type form
```

> **Normative note (annotation introducer).** A `colon_prefix` token (`:Int`) is an **annotation introducer**, not a variable reference. It is valid only as the head of an `annotate_expr` (§2.3.8), where it **binds the immediately-following form**. A `colon_prefix` is never a standalone atom or variable reference, and a `colon_prefix` with **no following form** is a parse error (`annotation missing expression`). This holds in every expression position, including as the leading element of a parenthesized list — there the `colon_prefix` annotates only the single following element, and the list is the application of that one annotated element. (Since the 2026-07-21 ruling below, "never a standalone atom" holds in **every** position, not only expression positions, and is structural: see the read-time-fold note.)

> **Normative note (`:` is a `^`-style reader macro; user ruling 2026-07-20). [S114]** The annotation `:` is a **reader macro in the manner of Clojure's `^` type hint**: it **binds the immediately-following form**, and — like `^`, whose reader recursively reads the next form — **whitespace between `:` and that form is permitted**. `: Int` ≡ `:Int`, and `: (Fn [a] a)` ≡ `:(Fn [a] a)`. The bound form **MUST be a type expression** (§2.4); `:` is **not** a keyword constructor (it does not mint a Clojure-style keyword value) and **not** a typed-racket-style `:` declaration form. A **dangling qualifier** in the bound form — `:foo/`, `:a.b/` (a module path with an empty local half, §8.5.1) — is a **located compile-time error** at the offending token; it does **not** silently degrade to `:foo` / `:a.b`. [S114]

> **Normative note (the fold happens at READ time; user ruling 2026-07-21). [S115]** `:Type <form>` is folded by the **reader**, not by a later pass: reading `:` and its two halves produces **one structural annotated node** in the read tree —
>
> ```ebnf
> annotated_form = (colon_prefix | colon_bare) type_form form
> ```
>
> — whose first child is the type form (the annotation half, with the colon itself **not** part of that child: `:Int` yields the plain symbol `Int`, `:(Fn [a] a)` yields the plain list) and whose second child is the annotated subject. Because the fold is a reader rule over the recursive read of a form, it applies in **every** position that reads forms, with no per-position exception:
>
> - expression positions (top level, list interiors, bracket interiors — `[:Int x :Int y]` reads as **two** annotated elements);
> - **macro-argument position** — a macro call's argument list is read like any other list, so `(def x :Int 5)` presents the macro **two** arguments (`x`, and the annotated `5`) and its arity matches what the user wrote (§9.1);
> - **quoted and quasiquoted data** — the fold precedes quote handling, so `'(:Int 5)` is a quotation of the annotated node, and a `~`-unquote may occupy either half.
>
> Consequences pinned by this ruling:
>
> - **"Never a standalone atom" now holds unconditionally.** There is no position — expression, quoted, or macro-argument — in which the annotation introducer survives as a bare atom. The invariant is structural, not a rule to be re-checked per position.
> - **Nesting is chaining.** `:A :B x` reads as the annotation `A` over the annotation `B` over `x` (stacked bounds, §3.9.3) — a nested chain, not a flat run.
> - **A trailing introducer is a located READER error** — an introducer with nothing to bind (at end of input, before a closing `)`/`]`, or as the sole remainder of a REPL line) is reported with the message **`annotation missing expression`** (wording unchanged from the parse-error formulation above; only the reporting site moves earlier).
> - **`~@` is not a legal half.** Unquote-splicing produces zero or more forms into a list context, while each half of the node is exactly one form; `~@` written directly as either half is a **located error**.
> - **The type-expression requirement is unchanged and is still checked after reading.** The reader folds structurally whatever follows the introducer; that the annotation half must be a type expression (§2.4) — so `:5 x` is rejected — remains a located error at the type-expression seam, not a reader error.
>
> The annotation is never carried as out-of-band metadata: an annotation **asserts** a type (§2.3.8), so it must be visible in the tree that macros and the type checker both see; a side-channel that could be silently dropped was explicitly rejected. Implementation contract: `design/arch/annotated-sexp-node.md`.

### 1.4.6 Gensym Symbols [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_gensym_shorthand]

```ebnf
gensym_symbol = symbol_start symbol_char* '#'
```

Symbols ending in `#` are auto-gensym symbols, used inside quasiquote templates to generate unique names. Within a single quasiquote, all occurrences of the same `x#` produce the same generated name. Different quasiquotes produce different names, preventing macro hygiene issues.

```clojure
`(let [x# 42] x#)  ; both x# expand to the same unique name
```

### 1.4.7 Percent Parameters [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_percent_param_bare]

```ebnf
percent_param = '%' ('1'-'9')?
```

Percent parameters (`%`, `%1`-`%9`) are used inside anonymous function shorthand `#(...)` to refer to positional arguments. Bare `%` is equivalent to `%1`.

### 1.4.8 Ampersand [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_ampersand]

```ebnf
ampersand = '&' !symbol_char
```

A standalone `&` (not followed by a symbol character) is used in macro parameter lists for variadic arguments.

## 1.5 Delimiters [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_bracket]

```ebnf
open_paren    = '('
close_paren   = ')'
open_bracket  = '['
close_bracket = ']'
```

Parentheses delimit lists (function calls, special forms). Square brackets delimit parameter lists, binding lists, match arms, field definitions, and vector literals.

## 1.6 Reader Macros [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_quote]

```ebnf
quote            = "'" form
quasiquote       = '`' form
unquote_splicing = '~@' form
unquote          = '~' form
anon_fn          = '#(' ws form* ws ')'
```

Reader macros are syntactic sugar processed during parsing:

- `'form` expands to `(quote form)` — produces an `Sexp` value at runtime [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_quote]
- `` `form `` expands to `(quasiquote form)` [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_quasiquote]
- `~form` expands to `(unquote form)` [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_unquote]
- `~@form` expands to `(unquote-splicing form)` [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_unquote_splicing]
- `#(body)` expands to `(fn [%1 %2 ... %N] (body))` — anonymous function shorthand [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_anon_fn]

The `quote` form converts its argument to an `Sexp` value. `'foo` produces `(SexpSym "foo")`, `'42` produces `(SexpInt 42)`, `'(+ 1 2)` produces `(SexpList ...)`.

The anonymous function `#(...)` scans the body for `%`, `%1`-`%9` references, normalizes bare `%` to `%1`, finds the maximum param index N, and wraps the body as `(fn [%1 %2 ... %N] (body))`. If no percent params are found, it produces a zero-arg function.

Note: Quote (`'`) MUST be tried before quasiquote (`` ` ``). Unquote-splicing (`~@`) MUST be tried before unquote (`~`). Anonymous function (`#(`) MUST be tried before list (`(`). These orderings resolve ambiguity for overlapping prefixes.

## 1.7 Token Precedence [Tested crates/cranelisp-frontend/src/reader.rs::test_negative_three_standalone]

When multiple token rules could match at a given position, the parser MUST try them in the following order:

1. Float literal (before integer, to capture the decimal point)
2. Integer literal (before operator, so `-3` is an integer) [Tested crates/cranelisp-frontend/src/reader.rs::test_negative_three_standalone]
3. Boolean literal
4. String literal
5. Colon-prefixed symbol
6. Bare colon
7. Ampersand
8. Qualified symbol (before dotted, since qualified contains `/`)
9. Dotted symbol (before simple symbol, since dotted is longer)
10. Gensym symbol (before simple symbol, since gensym includes trailing `#`)
11. Percent parameter (before operator, since `%` is not an operator char)
12. Operator symbol
13. Simple symbol

This ordering ensures that longer matches take priority and that ambiguous cases like `-3` (integer, not operator) and `true` (boolean, not symbol) are resolved correctly.

## 1.8 Forms [Tested+Neg crates/cranelisp-frontend/src/reader.rs::annotation_fold_is_recursive_and_stacks, crates/cranelisp-frontend/src/reader.rs::annotation_fold_rejects_dangling_delimiters_at_introducer, crates/cranelisp-frontend/src/reader.rs::annotation_fold_handles_compound_spaced_quoted_and_full_span_forms, crates/cranelisp-frontend/src/reader.rs::test_parse_multiple_forms]

A **form** is the basic unit of Cranelisp syntax:

```ebnf
form    = ws (quote | quasiquote | unquote_splicing | unquote
            | annotated_form
            | anon_fn | list | bracket | atom) ws

list    = '(' ws form* ws ')'
bracket = '[' ws form* ws ']'

(* the read-time annotation fold, §1.4.5 — the introducer and its two
   halves become ONE form; it is not an atom *)
annotated_form = (colon_prefix | colon_bare) ws form ws form

atom    = float | integer | boolean | string
        | ampersand
        | qualified_symbol | dotted_symbol
        | gensym_symbol | percent_param
        | operator_symbol | symbol

program = ws form* ws
```

A program is a sequence of zero or more forms separated by whitespace. Each form is either an atom (literal or symbol), a parenthesized list, a bracketed list, an annotated form, or a reader macro expansion. **`colon_prefix`/`colon_bare` are no longer `atom` alternatives [S115]** — a colon introducer only ever occurs as the head of an `annotated_form` (§1.4.5, the 2026-07-21 read-time-fold ruling), so "an annotation introducer is never a standalone atom" is a property of this grammar rather than a rule checked afterwards. In `annotated_form` the first `form` is the annotation half (required to be a type expression, §2.4, checked after reading) and the second is the annotated subject. [Tested crates/cranelisp-frontend/src/reader.rs::test_parse_multiple_forms]
