---
number: 0421
target: /spec
filed_by: /dev
filed_at: 2026-06-21
sprint_filed: 87
refers_to: spec/01-lexical.md §1.4.1, spec/01-lexical.md §1.4.2
status: open
---

# Lexical grammar omits interior operator chars in symbols (`char->digit`)

## Issue

The S87 D-name defect (`tests/spec_05_definitions.rs::defn_name_with_arrow_in_symbol_parses`)
required the reader to lex `char->digit` as a **single** symbol. The reader now
does so (`crates/cranelisp-frontend/src/reader.rs`: interior operator chars are
absorbed into an alphabetic symbol when followed by more symbol body).

This diverges from the spec's literal lexical grammar:

```ebnf
# §1.4.1
symbol_char  = 'a'-'z' | 'A'-'Z' | '0'-'9' | '_' | '-' | '?' | '!'
```

`symbol_char` does NOT include `>` `<` `=` `*` `+`. By the grammar as written,
`char->digit` lexes as three tokens (`char-`, `->`, `digit`) — which is exactly
the defect. The implemented (and now test-mandated) behaviour is that operator
characters interior to an alphabetic symbol are part of the symbol; a *standalone*
operator run (`->`, `<=`, `a <= b`) is still an operator symbol per §1.4.2.

## Proposed resolution

Reconcile §1.4.1 (and the relationship to §1.4.2) with the implemented rule:

- An alphabetic-started symbol MAY contain interior operator characters
  (`+ * = < >`) when they are followed by further symbol-char body. The arrow
  `->` inside `char->digit` is interior, not a token boundary.
- A symbol still MUST start with `symbol_start` (letter or `_`); a token that
  starts with an operator char remains an operator symbol per §1.4.2.
- `/` (qualified separator) and `.` (dotted member) are NOT absorbed — they keep
  their §1.4.3 / §1.4.4 structural meaning.

`/spec` decides the exact grammar phrasing and whether `!` (already a symbol_char)
and `-` need re-statement. The implementation excludes `-`/`?`/`!` from the
"interior operator" set because they are already `symbol_char`s, and excludes `/`
and `.` for the structural reason above.

## Operational implication / Context

Implemented this sprint to close the D-name guard. Guard tests:
- `tests/spec_05_definitions.rs::defn_name_with_arrow_in_symbol_parses` (+ control)
- `crates/cranelisp-frontend/src/reader.rs::test_parse_symbol_with_interior_arrow`
  (and siblings: interior `<=`, standalone-arrow-not-merged, threading-head intact)

The spec text is the only artefact now out of step; the FIXME exists so the
grammar is brought into line rather than left silently contradicting the reader.
