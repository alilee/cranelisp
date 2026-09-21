# Module Preamble Capture

Interior design for `crates/cranelisp-frontend/src/preamble.rs` — capturing the
leading comment-block module preamble. Normative source:
`spec/08-modules.md` §8.16 (the comment-block model). Storage:
`cranelisp-types::SymbolTable.module_preamble: Option<String>`, which the
frontend produces but does not own.

## 1. Scope and boundary

§8.16 spans three concerns; only the first is the frontend's.

| Concern | Owner |
|---|---|
| **Capture** — recognise the leading comment block, strip markers, join to `Option<String>` | frontend (§2–§4) |
| **Wiring** — thread the text onto `SymbolTable.module_preamble` at module load | int (§5) |
| **Re-emit** — emit the preamble verbatim on source regeneration | int (§6) |

The frontend's deliverable is a **pure function over a source string**. It
performs no symbol-table mutation and no I/O, which is what keeps it
unit-testable from a string with no session.

## 2. Capture mechanism

### 2.1 The boundary rule

The preamble is the contiguous block of line comments that **begins on the first
line of the file** and runs up to, but not including, the first form. Walking
from byte 0:

1. The block **starts at the first line**. If the first non-whitespace content is
   not a `;` comment, there is no preamble.
2. The block **accumulates** every contiguous comment line.
3. The block **terminates** at the first of: a **blank line** (comments below it
   are ordinary, never preamble), the **first non-comment form**, or **EOF** (a
   file that is only a comment block is entirely preamble — degenerate but
   valid).
4. Comments after the first form are never preamble.
5. There is **at most one** preamble per module.

### 2.2 Why the comment stream alone is not sufficient

`parse_preserving_comments` already surfaces leading comments as top-level
`Sexp::Comment` nodes in source order, which gets rules 1, 2, 4 and 5 for free —
the comment siblings already stop at the first real form.

The gap is rule 3's **blank-line break**. The reader consumes whitespace,
including blank lines, silently between comments, so two comment nodes separated
by a blank line are indistinguishable in the stream from two adjacent ones. The
span offsets do record the gap, but recovering "was there a blank line here?"
from spans means re-deriving lexical structure the reader already saw and
discarded — which is exactly the kind of inference that breaks when comment
positioning changes for an unrelated reason.

### 2.3 A head-of-source line scan

Capture is a self-contained line-oriented scan over the raw source, independent
of the parse: classify each physical line as blank, comment, or form-start, and
accumulate comment lines until a blank or form-start line — or EOF — terminates
the run. An empty run yields `None`.

This works in the same lexical units the spec's boundary rule is written in
(physical lines), so the blank-line rule is encoded where it is least error-prone,
and the capture cannot be perturbed by reader changes to comment positioning
inside forms.

### 2.4 Corner cases

| Source shape | Result | Rule |
|---|---|---|
| `;; doc` then `(mod m)` | `Some("doc")` | first form terminates |
| `;; line1` ⏎ `;; line2` ⏎ `(mod m)` | `Some("line1\nline2")` | contiguous run |
| `;; doc` ⏎ ⏎ `;; section` ⏎ `(mod m)` | `Some("doc")` | blank-line break; `section` is ordinary |
| `(defn f [] 0)` | `None` | not a comment first |
| `;; doc` ⏎ `;; more`, EOF | `Some("doc\nmore")` | EOF terminates |
| `;; a` ⏎ `(defn …)` ⏎ `;; b` | `Some("a")` | `b` is after the first form |
| empty file | `None` | no comment lines |
| blank line, then `;; doc`, then a form | `None` | see below |

**Leading blank lines yield `None`.** §8.16.1 says the block "begins on the first
line of the file", and the strict reading is that a blank first line means the
run does not begin on line 1. This is the safe default: it never mis-captures an
incidental comment as module documentation. Relaxing it is a one-line change to
the scan plus a spec clarification, and nothing here assumes it.

## 3. Text extraction

For each captured line:

1. Strip the comment marker — the maximal leading run of `;` that forms it, so
   `;;` if present, else a single `;`. The `;;` form is the idiomatic file header
   and the spec's own example uses it.
2. Strip **one** immediately-following space if present: `;; Sudoku` → `Sudoku`,
   `;;Sudoku` → `Sudoku`, a bare `;;` → `""`.
3. Strip nothing further. Interior alignment after that one space is content, and
   preserving it is what makes §6 round-trip byte-stable.

Join the stripped lines with a single `\n`, with no trailing newline.

The marker rule here is a **superset** of the reader's `Sexp::Comment` rule,
which strips a single `;` and one space. That is not a conflict: the preamble
scan does its own line stripping and does not route through comment capture, so
it owns the marker rule end to end.

## 4. Frontend surface

```rust
pub fn capture_module_preamble(source: &str) -> Option<String>
```

One pure function, re-exported at the crate root. No change to `Sexp`, to
`extract_module_declarations`, or to the `parse` entries.

**Why a standalone function rather than a field on `ExtractedDeclarations`.**
Declaration extraction iterates the *parsed*, comment-stripped form vector — the
pipeline uses `parse`, where comments are already gone. The preamble needs the
raw source head, for blank-line awareness and the `;;` marker. Bolting it on
would force `extract_module_declarations` to take the source string in addition
to the forms, widening a narrow, well-factored boundary for an orthogonal concern
(Principle 2). A sibling function the load seam calls alongside extraction is the
cleaner seam.

## 5. The frontend → int seam

The frontend hands off; int wires.

- At each module-load site, after parsing the source, int calls
  `capture_module_preamble` on the **same source string** and assigns the result
  to that module's `SymbolTable.module_preamble`. One call and one field
  assignment per site; no new control flow.
- The frontend's responsibility ends at returning the `Option<String>`. Threading
  it onto the right module, at the right sites, in every mode (`--run`, `--link`,
  REPL, cache restore) is int's orchestration concern — the same surface that owns
  the structural-declaration append and the module-load lifecycle.
- **Capture does not re-run on a cache hit.** `module_preamble` is a serialised
  field, so a cache-restored module carries its preamble through
  deserialisation; capture runs only on a fresh source parse, mirroring how
  structural declarations ride the cached table.

## 6. Regeneration round-trip

§8.16.5 requires the preamble to round-trip **byte-stably**: a module whose
preamble is unchanged across a regeneration emits a byte-identical leading
comment block — no reflow, re-wrap, re-indent or re-mark.

The split is capture (frontend, the input side) against re-emit (int's
regeneration printer, the output side). The contract the frontend's half fixes:

1. The preamble is emitted **before** the first section, at the file head, as the
   canonical leading comment block.
2. **Verbatim, no reflow.** The stored text is re-marked by prefixing each line
   with `;; ` and joining with `\n`. Because capture strips exactly
   marker-plus-one-space, re-emit with `;; ` reproduces the canonical form — the
   two rules are **inverse** on the canonical `;;`-and-one-space shape. An empty
   stored line becomes a bare `;;`.
3. Clearing the preamble emits no block and must leave the rest of the file
   byte-stable.

The inverse-pair property is the testable form of the whole contract: capture,
store, regenerate, re-parse, capture again yields the same text, and the head
bytes are byte-identical. That round trip crosses the frontend/int boundary, so
it is an integration-level assertion, not a frontend unit one.

## Cross-references

- `spec/08-modules.md` §8.16 — the normative comment-block model.
- `design/frontend/reader.md` — the comment-preserving reader mode and `Sexp::Comment`.
- `design/frontend/modules.md` §4 — the orthogonal structural-declaration boundary.
- `design/arch/repl-embedded-agent.md` §3.4 — why first-class module preambles are load-bearing.
