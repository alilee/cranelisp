# Comment Preservation in the Reader

Design document for Sprint 24: preserving comments in the Sexp tree so the pretty-printer can render them.

## Problem

Comments are currently stripped during parsing. The `skip_whitespace_and_comments()` function in `reader.rs` consumes both whitespace and `;`-to-EOL comments as part of the same loop, discarding comment text entirely. This means downstream consumers (notably `/source` and the pretty-printer specified in repl/spec.md S10.3) cannot reconstruct or display comments that were present in the original source.

The REPL spec S10.3.6 requires the reader to support a comment-preserving mode so that:
- `/source <name>` re-parses stored source text and retains commentary
- Result display metadata lines (`; defn`, `; impl:`, `; match:`) are styled uniformly as italic by the pretty-printer
- User comments survive round-tripping through the reader

## Sexp::Comment Variant

A new variant is added to the `Sexp` enum in `cranelisp-types/src/sexp.rs`:

```rust
pub enum Sexp {
    // ... existing variants ...
    /// Comment: `; some text` — preserved only in comment-preserving reader mode
    Comment(String, Span),
}
```

**What is stored**: The text after the `;` delimiter, with the `;` itself removed and exactly one leading space stripped if present. A comment `; hello world` stores `"hello world"`. A comment `;no space` stores `"no space"`. A bare `;` with nothing after it (or only a newline) stores `""`. The trailing newline is never included.

**Span**: Covers from the `;` character through the last non-newline character of the comment (or just the `;` for empty comments). This allows error reporting and source mapping if needed.

**Serde**: The variant derives `Serialize`/`Deserialize` like all other variants (already derived on the enum).

## Reader Changes

### preserve_comments flag

Add a boolean field to the `Reader` struct:

```rust
struct Reader<'a> {
    src: &'a str,
    pos: usize,
    preserve_comments: bool,
}
```

Default: `false`. The existing `parse()` function continues to construct `Reader` with `preserve_comments: false`, preserving backward compatibility.

A new public entry point exposes the comment-preserving mode:

```rust
/// Parse source text, preserving comments as Sexp::Comment nodes.
pub fn parse_preserving_comments(source: &str) -> Result<Vec<Sexp>, CranelispError>
```

This constructs `Reader { src: source, pos: 0, preserve_comments: true }` and runs the same parse loop.

### Comment capture logic

When `preserve_comments` is true, `skip_whitespace_and_comments()` changes behavior. Instead of one function that silently consumes both whitespace and comments, the logic splits into two cooperating functions:

```
skip_whitespace(r)           -- consumes only whitespace (spaces, tabs, newlines, commas)
try_read_comment(r) -> Option<Sexp>  -- if at ';', reads comment text, returns Sexp::Comment
```

The parse loop and delimited-form readers (`read_list`, `read_bracket`) gain a pattern:

```
skip_ws_and_maybe_collect_comments(r, &mut children)
```

which calls `skip_whitespace`, then checks for a comment. If `preserve_comments` is true and a comment is found, it pushes `Sexp::Comment` into `children` and loops (there may be more whitespace/comments). If `preserve_comments` is false, the existing `skip_whitespace_and_comments` behavior applies — comments are consumed and discarded.

A clean implementation approach: keep `skip_whitespace_and_comments` as-is for the non-preserving path, and add a separate `skip_ws_collect_comments` that the preserving path uses. This avoids adding branches to the hot path of the compiler pipeline.

### Comment text extraction

When the reader encounters `;`:

1. Record `start = pos` (position of `;`)
2. Advance past `;`
3. If the next character is a space (` `), advance past it (strip one leading space)
4. Record the start of the text content
5. Advance until newline or EOF
6. The text is `src[text_start..pos_before_newline]`
7. If stopped at a newline, advance past it
8. Return `Sexp::Comment(text, Span::new(start, end))`

## Comment Positioning

Comment nodes appear in the Sexp tree at the position where they occur in source text. They are siblings alongside regular forms inside `List` and `Bracket` children vectors, and at the top level alongside other top-level forms.

Examples:

```lisp
; A helper function
(defn add [a b]    ; adds two numbers
  (+ a b))
```

With comment preservation, the top-level parse produces:

```
[
  Comment("A helper function", span),
  List([
    Symbol("defn", span),
    Symbol("add", span),
    Bracket([Symbol("a", span), Symbol("b", span)], span),
    Comment("adds two numbers", span),
    List([Symbol("+", span), Symbol("a", span), Symbol("b", span)], span),
  ], span),
]
```

The `; adds two numbers` comment becomes a child of the outer list, positioned between the parameter bracket and the body form — exactly where it appeared in the source.

**Standalone line comments** appear between forms at whatever nesting level they occupy.

**Inline comments** (after a form on the same line) appear after that form in the children vector. The reader does not distinguish between standalone and inline comments — they are both `Sexp::Comment` nodes positioned by their source location.

**End-of-file comments** appear as top-level `Sexp::Comment` nodes at the end of the result vector.

## Pipeline Isolation

The AST builder, typechecker, and backend MUST never encounter `Sexp::Comment` nodes. Two mechanisms ensure this:

### Primary mechanism: default off

The compiler pipeline uses `parse()`, which sets `preserve_comments: false`. No `Comment` nodes are produced, so downstream phases never see them. This is the zero-cost path — no filtering, no new match arms, no behavioral change.

### Secondary mechanism: filter on entry (defense in depth)

If any future code path accidentally feeds comment-preserving sexps into the compiler pipeline, the AST builder's `build_top_level` and `build_expr` functions should include a guard:

```rust
Sexp::Comment(_, _) => continue,  // skip comments silently
```

in any match arm that iterates over children (e.g., processing list elements). This is a defensive measure — it should never fire in practice but prevents a hard crash if it does. The `build_program` top-level loop should likewise skip `Comment` nodes.

This is preferable to a separate filtering pass because:
- It requires no allocation (no new `Vec` without comments)
- It co-locates the guard with the code that would otherwise fail on an unknown variant
- Adding the new variant to `Sexp` already forces exhaustive-match updates everywhere; adding `skip` arms is part of that work

### What NOT to do

Do not add `Comment` handling to the typechecker or backend. Those phases work with `Expr`/`TopLevel`/`Type` — they never see `Sexp` at all. The isolation boundary is at the Sexp-to-AST translation in the AST builder.

## Sexp Utility Updates

Adding a variant to `Sexp` requires updating all match arms. The affected methods:

### `span(&self) -> Span`

```rust
Sexp::Comment(_, s) => *s,
```

### `format_flat(&self) -> String`

```rust
Sexp::Comment(text, _) => {
    if text.is_empty() {
        ";".to_string()
    } else {
        format!("; {text}")
    }
}
```

Re-emits the canonical `; text` format with one space after the semicolon. This matches the input convention and ensures round-trip fidelity.

### `format_indented(&self, indent: usize) -> String`

Comments are always short (single line), so the flat format is returned directly — no indentation logic needed. The comment text never exceeds the 60-char threshold in practice, but even if it did, line-breaking a comment would be incorrect.

```rust
Sexp::Comment(_, _) => self.format_flat(),
```

When a `Comment` appears inside a `List` or `Bracket` being indented, the parent's indentation logic handles it: the comment is emitted on its own line with the same indentation as sibling forms.

### `Display` impl

No change needed — it delegates to `format_indented(0)`.

## Sketch Comparison

The sketch (`sketch/src/sexp.rs`) uses a PEG grammar where comments are consumed inside the `ws()` rule:

```peg
rule comment() = ";" [^ '\n']* ("\n" / ![_])
rule ws() = quiet!{([' ' | '\t' | '\n' | '\r' | ','] / comment())*}
```

The sketch's `Sexp` enum has no `Comment` variant. Comments are unconditionally stripped and cannot be recovered. The sketch never needed comment preservation because it had no pretty-printer or `/source` command that required it.

**Divergence**: The reimplementation adds `Sexp::Comment` and a dual-mode reader. This is a deliberate extension — the sketch never addressed this requirement. The approach is informed by common Lisp tooling (e.g., Clojure's `tools.reader` preserves comments as metadata) but uses a simpler in-tree model rather than metadata attachment, since Cranelisp's Sexp nodes don't have a metadata map.

## Testing Approach

### Unit tests in `cranelisp-frontend`

1. **Basic comment parsing**: `parse_preserving_comments("; hello")` produces `[Comment("hello", _)]`
2. **Comment text extraction**: verify `;` stripping, single leading space stripping, no-space case, empty comment
3. **Inline comment**: `parse_preserving_comments("42 ; note")` produces `[Int(42, _), Comment("note", _)]`
4. **Comment inside list**: `parse_preserving_comments("(a ; mid\n b)")` produces `List([Symbol("a"), Comment("mid"), Symbol("b")])`
5. **Multiple comments**: consecutive comment lines produce consecutive `Comment` nodes
6. **EOF comment**: comment at end of input without trailing newline
7. **Backward compatibility**: `parse("42 ; note")` still produces `[Int(42, _)]` — no `Comment` nodes
8. **Round-trip fidelity**: `parse_preserving_comments(text).format_flat()` reproduces the comment as `; text`

### Integration tests

9. **AST builder tolerance**: feeding `Comment` nodes into `build_program` does not crash (defense-in-depth guard)
10. **Pretty-printer**: comment nodes are styled as italic when styling is enabled (owned by `/int` or REPL layer)

### What not to test here

Typechecker and backend never see `Sexp` — no tests needed there. The pretty-printer styling is a downstream consumer tested separately.

## Delivery

- **Crate**: `cranelisp-types` (Sexp variant), `cranelisp-frontend` (reader changes)
- **Risk**: Low. The change is additive. The default code path is unchanged. The new variant forces exhaustive-match updates but each is a one-line addition.
- **Dependencies**: None. This is a leaf change with no upstream requirements.
- **Downstream consumers**: Pretty-printer (Sprint 24), `/source` command (Sprint 24)
