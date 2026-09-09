---
number: 0789
target: /arch
filed_by: /dev (src)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: crates/cranelisp-types/src/sexp.rs::quote_head;
  crates/cranelisp-frontend/src/quasiquote.rs (landed consumer);
  src/expander.rs::quote_head (remaining C6 tail)
status: open
---

# The shared reader-quote classifier has one remaining int-side duplicate

## Issue

The authoritative structural predicate is now
`cranelisp_types::quote_head(&[Sexp]) -> Option<QuoteHead>`, beside `Sexp`.
It recognizes exactly the four bare two-element reader forms — `quote`,
`quasiquote`, `unquote`, and `unquote-splicing` — as the closed exhaustive
`QuoteHead` sum.

**C1 delivered:** `cranelisp-types` publishes `QuoteHead` and `quote_head`,
with exact-head and arity controls. **C2 delivered:** frontend deleted its four
local predicates and every fold/template site consumes the shared classifier
with exhaustive matching. Do not recreate frontend-local
`is_quote`/`is_quasiquote`/`is_unquote`/`is_unquote_splicing` helpers; those
names no longer exist.

The filing remains open because `src/expander.rs` still defines its own local
`QuoteHead` and `quote_head`. Its two shield walks share that local function,
but it is still a second encoding of the types-owned rule and currently folds
`unquote` and `unquote-splicing` into one local variant. Divergence here could
double-desugar or mis-qualify a quoted subtree.

## Proposed resolution

C6 completes the already-planned consumer wash:

1. import `cranelisp_types::{QuoteHead, quote_head}` in `src/expander.rs`;
2. delete the int-local enum and classifier;
3. route both shield walks through the shared function, matching all four
   variants exhaustively and preserving the current treatment of
   `UnquoteSplicing` where it intentionally follows `Unquote`;
4. replace source comments that still name the deleted frontend predicates;
5. retain the existing expansion/qualification shield tests as the behavioural
   controls.

No frontend API work, new predicate, cache change, or language-behaviour
decision remains.

## Context

**Closure trigger:** C6 lands with no `QuoteHead` or `quote_head` definition in
`src/expander.rs`; both int shield walks call the types-owned classifier; no
source citation names the deleted frontend predicates; the quote-shield tests
remain green. Until then this filing stays `open`.
