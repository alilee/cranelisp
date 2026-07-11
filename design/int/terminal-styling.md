# Terminal Styling and Pretty-Printer

Implementation design for `repl/spec.md` section 10 (Sprint 24).

## Sketch Comparison

The sketch has no terminal styling. All output is plain text with no ANSI escape sequences. The sketch's `format_sexp()` and `format_flat()` functions produce unstyled strings. There is nothing to follow or diverge from -- this is entirely new functionality.

## Architecture

Two layers, as specified in section 10.7:

```
Layer 1: src/style.rs    -- Style enum, styled() function, TTY detection
Layer 2: src/pretty.rs   -- S-expression pretty-printer (Sexp -> styled indented String)
```

Layer 1 is a leaf module with no dependencies on compiler internals. Layer 2 depends on Layer 1 and on `cranelisp_types::Sexp`. Both live in the binary crate (`src/`) because they are REPL presentation concerns, not library crate functionality.

### Why two layers

The pretty-printer handles S-expression formatting: indentation, syntax highlighting, head-position detection. But some output elements are not S-expressions (prompt, error messages, category headers). These use `styled()` directly from Layer 1. Separating the layers keeps the pretty-printer focused on Sexp tree-walking while giving non-Sexp output a clean styling API.

## Layer 1: `src/style.rs`

### Style Enum

```rust
/// ANSI style for a text span.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Style {
    /// Bold (SGR 1) -- head position atoms, category headers, error keyword
    Bold,
    /// Dim (SGR 2) -- prompt, banner
    Dim,
    /// Italic (SGR 3) -- comments
    Italic,
    /// Cyan (SGR 36) -- type annotations (:Type)
    Cyan,
    /// Yellow (SGR 33) -- integer, float, boolean literals; warning detail
    Yellow,
    /// Green (SGR 32) -- string literals
    Green,
    /// Red (SGR 31) -- error detail
    Red,
    /// Bold Red (SGR 1;31) -- error keyword
    BoldRed,
    /// Bold Yellow (SGR 1;33) -- warning keyword
    BoldYellow,
}
```

### `styled()` Function

```rust
/// Wrap text in ANSI escape sequences for the given style.
///
/// When colour is disabled (via TTY detection), returns text unchanged.
pub fn styled(text: &str, style: Style) -> String
```

Implementation: if `is_color_enabled()` is false, return `text.to_string()`. Otherwise, emit `\033[{code}m{text}\033[0m` where `{code}` is the SGR code for the style variant. Every styled span is self-contained with its own reset -- no reliance on nesting or state.

SGR code mapping:
- `Bold` -> `1`
- `Dim` -> `2`
- `Italic` -> `3`
- `Cyan` -> `36`
- `Yellow` -> `33`
- `Green` -> `32`
- `Red` -> `31`
- `BoldRed` -> `1;31`
- `BoldYellow` -> `1;33`

### TTY Detection

Computed once at startup, stored in a module-level `OnceLock<bool>`:

```rust
use std::sync::OnceLock;

static COLOR_ENABLED: OnceLock<bool> = OnceLock::new();

/// Initialize colour detection. Must be called once at startup
/// with the parsed --no-color flag value.
pub fn init_color(no_color_flag: bool) {
    let enabled = detect_color(no_color_flag);
    let _ = COLOR_ENABLED.set(enabled);
}

/// Query whether colour output is enabled.
pub fn is_color_enabled() -> bool {
    *COLOR_ENABLED.get().unwrap_or(&false)
}
```

Detection logic (section 10.1 priority order):

```rust
fn detect_color(no_color_flag: bool) -> bool {
    // 1. --no-color flag takes highest priority
    if no_color_flag {
        return false;
    }
    // 2. NO_COLOR env var (any non-empty value suppresses)
    if let Ok(val) = std::env::var("NO_COLOR") {
        if !val.is_empty() {
            return false;
        }
    }
    // 3. TTY check on stdout
    use std::io::IsTerminal;
    if !std::io::stdout().is_terminal() {
        return false;
    }
    // 4. Otherwise: enabled
    true
}
```

Uses `std::io::IsTerminal` (stable since Rust 1.70). No external crate needed.

### `--no-color` CLI Integration

Add `--no-color` to `parse_args()` in `src/main.rs`:

```rust
enum RunMode {
    Repl { no_color: bool },
    RunFile { path: String, no_cache: bool, no_color: bool },
    Link { path: String, no_color: bool },
    Error(String),
}
```

Each `RunMode` variant carries the flag. At the top of each mode handler (`run_repl()`, `run_file()`, `link_file()`), call `style::init_color(no_color)` before any output. The flag is accepted in any position alongside other flags.

Alternatively, call `init_color()` once in `main()` before dispatching, since the flag is parsed before mode selection. This is simpler:

```rust
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let (mode, no_color) = parse_args(&args);
    style::init_color(no_color);
    match mode { ... }
}
```

The second approach is preferred -- single initialization point, no flag threading through `RunMode`.

## Layer 2: `src/pretty.rs`

### Public API

```rust
/// Pretty-print and syntax-highlight a Sexp tree.
///
/// Returns a styled, indented string. When colour is disabled,
/// returns plain indented text (indentation always applies).
pub fn pretty_print(sexp: &Sexp) -> String

/// Pretty-print a string by parsing it to Sexp first.
///
/// If parsing fails, returns the input string unstyled.
/// Uses the comment-preserving reader mode.
pub fn pretty_print_str(source: &str) -> String
```

### Algorithm

`pretty_print` calls a recursive `pp(sexp, indent, in_head_position) -> String`:

1. **Atom nodes** (Symbol, Int, Float, Bool, Str):
   - Apply style based on node type and context:
     - If `in_head_position`: `Style::Bold`
     - If type annotation (symbol starts with `:`): `Style::Cyan`
     - If Int or Float: `Style::Yellow`
     - If Bool: `Style::Yellow`
     - If Str: `Style::Green`
     - Otherwise: no styling (default text)
   - Return the styled atom string.

2. **Comment nodes** (`Sexp::Comment` -- new variant, see below):
   - Style the entire comment text as `Style::Italic`.
   - Prefix with `; `.

3. **List nodes** (`Sexp::List`):
   - Compute flat representation (unstyled) to measure length.
   - If flat length <= 40 characters: emit single-line.
   - Otherwise: emit multi-line with indentation.
   - First child is in head position; remaining children are not.
   - When the list itself is in head position, its brackets are bold.

4. **Bracket nodes** (`Sexp::Bracket`):
   - Same short/long threshold as List.
   - No head-position bolding (section 10.3.3).

### Head Position Propagation

Head position is a boolean parameter passed recursively:

- `pretty_print(sexp)` calls `pp(sexp, 0, false)` -- top-level is NOT in head position.
- Inside a `Sexp::List`, the first child is rendered with `in_head_position = true`.
- If the first child of a list is itself a list, that sub-list's brackets are bold (because the sub-list is in head position) and its own first child is recursively in head position.
- `Sexp::Bracket` children are never in head position.

### Type Annotation Detection

A symbol starting with `:` is a type annotation. The entire annotation -- from the colon through any compound type -- gets `Style::Cyan`.

Detection:
- `Sexp::Symbol(name, _)` where `name.starts_with(':')` -> cyan.
- Compound type annotations like `:(Fn [Int] Int)` appear as `Sexp::List` where the first child is a `Sexp::Symbol` starting with `:`. When the pretty-printer encounters this pattern, the entire list (including all children) is rendered in cyan. Specifically: if the first child of a list is a colon-prefixed symbol, the list is a "type annotation list" and all its contents are styled cyan, overriding the normal head-position and literal rules (per section 10.3.4).

### Indentation Rules

For multi-line forms:

**Standard alignment** (default): head and first argument on line 1; subsequent arguments indented to align with the first argument.

```
(map (+ 1)
     my-long-list-name)
```

**Special-form indentation**: when the head is one of `defn`, `deftype`, `deftrait`, `impl`, `let`, `match`, `fn`, `if`, `do`, `defmacro`, use 2-space body indent instead of argument alignment:

```
(defn factorial [n]
  (if (= n 0)
    1
    (* n (factorial (- n 1)))))
```

The set of special forms is a compile-time constant:

```rust
const SPECIAL_FORM_INDENT: &[&str] = &[
    "defn", "deftype", "deftrait", "impl", "let", "match",
    "fn", "if", "do", "defmacro",
];
```

### Aligned `let`/`match` pair layout — FIXME 0554 (S107) [normative: `repl/spec.md` §3.11]

`let` binding lists and `match` arm lists are **pair-structured** vectors: the binding
`Sexp::Bracket` reads as consecutive `(left, right)` pairs — `[l0 r0 l1 r1 …]` → `(l0,r0)
(l1,r1) …`. Before S107 the printer sent that bracket through the generic `pp_bracket`
path, which smeared pairs across lines (the FIXME 0554 defect). S107 makes the layout a
**byte-reproducible MUST** (`repl/spec.md` §3.11 P0–P5, the byte-exact `rotate` fixture).

**Durability constraint (Phase-2, binding).** Pair-awareness is implemented as **structural
recognition on the `Sexp` tree**, *never* string post-processing. The printer recognises the
binding/arm `Sexp::Bracket` of a recognised head and lays it out from the tree. Recognised
heads for S107 are exactly **`let`** (the binding vector is its first `[...]` argument) and
**`match`** (the arm vector is the `[...]` following the scrutinee). This is a display
contract only — no language-semantics change, no other form's layout changes.

**Column model.** `repl/spec.md` §3.11's 1-based-looking "column N" values map directly onto
`pp`'s existing 0-based `indent` parameter (character offset from the left margin): the `let`
that "sits at column 2" is `pp(let_sexp, indent=2, …)`. So the pair layout reuses `pp`'s
existing absolute-column threading with **no new coordinate system**.

**Dispatch seam (`pp_list`).** The recognition sits at the **top of `pp_list`**, *before* the
`FLAT_THRESHOLD` measurement, because P0 forces multi-line whenever a recognised vector has
≥2 pairs even if the whole form would fit flat:

```
fn pp_list(children, indent, in_head):
    if empty { … }
    if is_type_annotation_list(children) { … }          // unchanged
    if let Some(s) = try_pp_pair_form(children, indent, in_head) { return s }  // NEW — let/match ≥2 pairs
    // unchanged flat/threshold path below (0/1-pair let/match fall through here)
    if flat.len() <= FLAT_THRESHOLD { return pp_list_flat(…) }
    return pp_list_multiline(…)
```

`try_pp_pair_form` returns `None` (→ existing layout) for any non-recognised head, a vector
not present at the expected position, **fewer than 2 pairs** (P0 — nothing to align), or an
**odd** element count (P5 graceful fallback — the pre-existing bracket layout, never a crash
or dropped element). It returns `Some(text)` only when it takes over the whole form.

**Head-line + pair-vector placement.** The recognised head keeps its pre-vector arguments on
the head line (rendered flat), which fixes the vector's `[` column:
- **`let`**: head line is `(let [`. The `[` column = `indent + len("(let ")` = `indent + 5`;
  the left-column start (first left-term char) = `[`col + 1 = `indent + 6`. The `let` **body**
  forms (everything after the binding vector) follow on new lines at the special-form body
  indent `indent + 2`, exactly as today.
- **`match`**: head line is `(match <scrutinee> [` — the arm vector stays **on the head line**
  after the scrutinee (this is the one deviation from the generic special-form arm, which
  would drop the second argument to a body line). The `[` column = `indent + len("(match ") +
  flatwidth(scrutinee) + 1`; left-column start = `[`col + 1. (The scrutinee is rendered flat
  on the head line — a bounded simplification; §3.11's contract is on the arm-vector
  alignment, and the fixtures use simple scrutinees.)

**The pair-vector formatter** (`pair_vector_layout`, a ≤~40-line helper — keeps `pp_list`
and `try_pp_pair_form` within the `src/CLAUDE.md` ~100-line budget):

```
pair_vector_layout(pairs: &[(&Sexp,&Sexp)], left_col: usize) -> String:
    W = max over pairs of pairs[i].left.format_flat().len()   // P3 — per-vector, unstyled widths
    right_col = left_col + W + 1                              // P3 — one min space after widest left
    out = "["
    for (i,(left,right)) in pairs.enumerate():
        if i > 0 { out += "\n" + " "*left_col }               // P1/P2 — one pair per line, left column
        left_flat = pp(left, 0, false)                        // rendered flat (styled); width via format_flat
        out += left_flat
        out += " " * (right_col - left_col - left.format_flat().len())   // P3 pad to right column
        out += pp(right, right_col, false)                    // P4 — right term as if opening AT right_col
    out += "]"                                                // attaches to the last right term's final line
```

Key points, each pinned to a §3.11 rule:
- **P2/P3 widths are unstyled** — `format_flat().len()`, matching the existing threshold-
  measurement discipline (ANSI never inflates a column count). Determinism (byte-exact
  colour-off) follows: padding is space runs computed from unstyled widths; colour-on only
  wraps the same characters in SGR at the same columns.
- **P4 recursion is free.** Passing `indent = right_col` into `pp(right, right_col, false)`
  makes the nested form compute *its* continuation indent relative to `right_col` — precisely
  "printed as if its opening column were the right-column start." A multi-line `if` value
  indents its body to `right_col + 2` (the ordinary special-form +2, delegated); a nested
  `match` value re-enters `try_pp_pair_form` with its own per-vector `W` (P0–P4 recurse).
- **The closing `]` attaches to the last line** of the last pair's right term (no newline
  before it) — reproducing the fixture's `new-pos)]`.
- **`as_pairs(bracket_children) -> Option<Vec<(&Sexp,&Sexp)>>`** is the tiny even-count
  splitter; `None` on an odd count routes P5 to the fallback.

This is verified against the byte-exact `rotate` fixture in `repl/spec.md` §3.11 (which `/qa`
pins as an e2e): the `let`'s three left terms `d`/`new-pos`/`final-pos` give `W=9`,
`right_col = 8+9+1 = 18`; the `d`-value nested `match` recurses with its own `W=5`,
`right_col = 28+5+1 = 34`. Because the same printer backs `/sexp`, `/source`, **and** the
agent's ```lisp fences (`design/int/agent.md` §14.5), all three inherit the aligned layout
with no extra wiring.

### Line Length Measurement

The 40-character threshold is measured on unstyled text. The pretty-printer computes `flat_len` by calling `Sexp::format_flat()` (existing method on Sexp) which produces unstyled text. Escape sequences are never counted toward line length.

### Comment Preservation

Section 10.3.6 requires a `Sexp::Comment(String, Span)` variant. This is a change to `cranelisp_types::Sexp` (owned by `/frontend`).

**Cross-skill coordination**: File `FIXME(/frontend)` on `crates/cranelisp-types/src/sexp.rs` requesting the `Comment` variant and a `preserve_comments: bool` flag on the reader. The default mode (used by the compiler pipeline) continues to strip comments. The pretty-printer uses the comment-preserving mode.

Until the `Comment` variant is available, `/source` output will be pretty-printed without comment styling. This is a graceful degradation -- the feature works, just without italic comments. No blocking dependency.

## Output Path Inventory

Every REPL output path that produces S-expression content, and how each gets wired to the pretty-printer.

### Paths that use the pretty-printer

| Output Path | Current Code Location | Current Mechanism | Migration |
|---|---|---|---|
| **Expression result** (`:Type value`) | `eval_and_display()` in `mod.rs` line 1544 | `format_result_value()` returns plain string | Re-parse the returned string via `pretty_print_str()` before `writeln!` |
| **Definition result** (`:Type name ; class`) | `eval_and_display()` in `mod.rs` line 1530 | `definition_display` field, plain string | Re-parse via `pretty_print_str()` |
| **IO result** | `eval_and_display()` in `mod.rs` line 1536 | `force_io_and_format()` returns plain string | Re-parse via `pretty_print_str()` |
| **`/source`** | `handle_source()` in `commands.rs` line 512 | `dc.source` printed verbatim | Re-parse stored source via `pretty_print_str()` (comment-preserving reader mode once available) |
| **`/expand`** | `handle_expand()` in `commands.rs` line 283 | `format_sexp(&expanded)` -- already has Sexp tree | Call `pretty_print(&expanded)` directly (no re-parsing needed) |
| **`/sig`** | `handle_sig()` in `commands.rs` line 39 | `format_entry_signature()` returns plain string | Re-parse via `pretty_print_str()` |
| **`/info`** line 1 | `handle_info()` in `commands.rs` line 144 | same as `/sig` | Re-parse via `pretty_print_str()` |
| **`/type`** | `handle_type()` in `commands.rs` line 101 | `format_type_qualified()` returns plain string | Re-parse via `pretty_print_str()` (just `:{type}`) |
| **`/time`** | `handle_time()` in `commands.rs` line 271 | `format_result_value()` plus timing suffix | Re-parse the result portion, append unstyled timing |
| **Bare symbol feedback** | `special_form_feedback()` in `commands.rs` line 813 | `format_entry_signature()` returns plain string | Re-parse via `pretty_print_str()` |

### Paths that do NOT use the pretty-printer

| Output Path | Current Code Location | Why Not |
|---|---|---|
| `/sexp` | `commands.rs` line 531 | Debug representation of Sexp structure, not pretty-printed source (section 10.3.7) |
| `/ast` | `commands.rs` line 548 | Rust Debug format of AST |
| `/clif` | `commands.rs` line 565 | CLIF IR text, not S-expression |
| `/disasm` | `commands.rs` line 582 | Disassembly text |
| `/list`, `/imports`, `/exports` body | `commands.rs` various | Plain name lists, not S-expression content |
| `/help` | `mod.rs` line 1415 | Plain text command list |
| `/doc` | `commands.rs` line 50 | Plain text docstring |
| Error messages | `mod.rs` line 1557 | Styled via non-formatter styling (section 10.4) |
| Prompt | `mod.rs` line 1446 | Styled via non-formatter styling |
| Banner | `mod.rs` line 1961 | Styled via non-formatter styling |

### Migration Strategy

The key insight from section 10.7: "The migration can be incremental -- individual output paths can be converted one at a time."

The simplest migration path is a wrapper: everywhere we currently `writeln!(stdout, "{display}")` for S-expression content, replace with `writeln!(stdout, "{}", pretty_print_str(&display))`. This re-parses the string through the reader and pretty-printer. For `/expand`, which already has the Sexp tree, call `pretty_print(&expanded)` directly.

This re-parsing approach has negligible cost (REPL output strings are short) and avoids restructuring the display functions. The existing `format_result_value()` / `format_entry_signature()` functions continue to produce plain strings; the pretty-printer adds styling and indentation on top.

**Future optimization**: If re-parsing becomes a concern, refactor display functions to return Sexp trees instead of strings. This is not needed for Sprint 24.

## Non-Formatter Styling

These chrome elements use `styled()` directly (section 10.4).

### Prompt

`format_prompt()` in `mod.rs` line 1439:

```rust
fn format_prompt(compile_ms: u64, eval_ms: u64, module: &str) -> String {
    styled(&format!("{compile_ms}+{eval_ms}ms; {module}> "), Style::Dim)
}
```

### Error Messages

`eval_and_display()` in `mod.rs` line 1557 and throughout:

```rust
// Before:
writeln!(stdout, "error: {e}")
// After:
writeln!(stdout, "{} {}", styled("Error:", Style::BoldRed), styled(&e.to_string(), Style::Red))
```

Similarly for `handle_info`, `handle_sig`, etc. error paths. The error keyword is bold red; the detail is red.

### Warning Messages

`eval_and_display()` in `mod.rs` line 1528:

```rust
writeln!(stdout, "{} {}", styled("Warning:", Style::BoldYellow), styled(&w.message, Style::Yellow))
```

### Category Headers

`print_name_category()` in `commands.rs` line 970:

```rust
writeln!(stdout, "{}:", styled(label, Style::Bold))
```

The body (symbol names) remains unstyled.

### Startup Banner

`run_repl()` in `mod.rs` line 1961:

```rust
writeln!(stdout, "{}", styled("Cranelisp v0.1.0", Style::Dim));
writeln!(stdout, "{}", styled("Type /help for commands, /quit to exit.", Style::Dim));
```

### `/info` Metadata Lines

The code size and compile duration line in `handle_info()` (commands.rs line 156) remains unstyled (it is informational body content, not a category header).

### File Watcher Notifications

`[updated: file]` and `[errors: file]` in `mod.rs` line 1698, 1702: these are informational chrome. Style `[errors: ...]` as red, `[updated: ...]` as default.

## Banner FIXME Fix

Section `mod.rs` line 1586-1591 has:

```rust
// FIXME(/int): This should be println!, not eprintln!.
if session.enable_persistence() {
    eprintln!("; Restored user.cl");
}
```

Fix: change `eprintln!` to `writeln!(stdout, ...)` (using the stdout handle already in scope in `run_repl()`). The banner and restore messages are user-visible status on stdout, not error diagnostics on stderr. Apply `Style::Dim` to match the banner styling.

This must happen inside `run_repl()` where `stdout` is available. Currently `create_repl_session()` calls `enable_persistence()` internally. Two options:

1. **Move persistence enablement into `run_repl()`** after `create_repl_session()` returns, so `stdout` is in scope. This is the cleaner option -- `create_repl_session()` returns the session, and the caller decides what to print.

2. **Pass `stdout` into `create_repl_session()`**. This adds an unnecessary parameter -- the function's job is session creation, not display.

Option 1 is preferred. Extract `enable_persistence()` call from `create_repl_session()` into `run_repl()`:

```rust
pub fn run_repl() {
    let mut session = create_repl_session();
    let mut stdout = io::stdout().lock();

    // Startup banner (dim).
    writeln!(stdout, "{}", styled("Cranelisp v0.1.0", Style::Dim));
    writeln!(stdout, "{}", styled("Type /help for commands, /quit to exit.", Style::Dim));

    // Session persistence (after banner, before prompt).
    if session.enable_persistence() {
        writeln!(stdout, "{}", styled("; Restored user.cl", Style::Dim));
    }
    // ... prompt and loop
}
```

## Testing Approach

### Unit Tests for `src/style.rs`

- `styled()` with colour enabled: verify SGR codes are emitted.
- `styled()` with colour disabled: verify plain text returned.
- Each `Style` variant maps to the correct SGR code.
- Styled spans are self-contained (start code + text + reset).

### Unit Tests for `src/pretty.rs`

- Short form (<= 40 chars): single line output.
- Long form (> 40 chars): multi-line with correct indentation.
- Head position: first element of list is bold.
- Nested head position: `((+ 1) 2)` -- inner `(` and `+` are bold.
- Type annotations: `:Int` is cyan, `:(Fn [Int] Int)` entirely cyan.
- Literals: integers yellow, strings green, booleans yellow.
- Special form indentation: `defn`, `let`, `if` get 2-space body indent.
- Bracket forms: no head-position bolding.
- Colour disabled: indentation still applies, no escape sequences.
- Mixed content: `:primitives/Int 42` -- type cyan, literal yellow.
- Comment nodes (once `Sexp::Comment` exists): italic styling.

### Integration Tests (via `/qa`)

- Eval `:Type value` display has correct ANSI codes when colour is enabled.
- `--no-color` flag suppresses all ANSI in output.
- `NO_COLOR=1` environment variable suppresses all ANSI.
- Piped output (`| cat`) suppresses ANSI (stdout not a TTY).
- `/source` output is indented and highlighted.
- `/expand` output is indented and highlighted.
- Error messages use red styling.
- Prompt uses dim styling.
- Category headers in `/list` are bold.

### Testing `is_color_enabled()`

The `OnceLock` design makes direct unit testing of detection logic straightforward: test `detect_color()` as a pure function (not `is_color_enabled()` which depends on global state). For integration tests, use `--no-color` to force colour off, since TTY status cannot be controlled in `cargo test` (test stdout is not a TTY).

## Implementation Order

1. `src/style.rs` -- Style enum, `styled()`, TTY detection, `init_color()`.
2. `--no-color` CLI flag in `src/main.rs`, call `init_color()` in `main()`.
3. `src/pretty.rs` -- Pretty-printer with indentation and syntax highlighting.
4. Wire expression result display through `pretty_print_str()`.
5. Wire definition result display through `pretty_print_str()`.
6. Wire `/source` through `pretty_print_str()`.
7. Wire `/expand` through `pretty_print(&sexp)`.
8. Wire `/sig`, `/info`, `/type` through `pretty_print_str()`.
9. Wire bare-symbol feedback through `pretty_print_str()`.
10. Non-formatter styling: prompt (dim), errors (red), warnings (yellow), headers (bold), banner (dim).
11. Banner FIXME fix (eprintln -> writeln, move persistence enablement).
12. File `FIXME(/frontend)` for `Sexp::Comment` variant.

Steps 1-3 are the foundation. Steps 4-9 are incremental output path conversions (each independently testable). Steps 10-11 are chrome styling. Step 12 is cross-skill coordination.

## Open Questions

None. The spec (section 10) is comprehensive. All design decisions follow directly from the spec requirements.
