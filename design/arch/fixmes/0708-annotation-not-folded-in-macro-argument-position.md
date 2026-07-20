---
number: 0708
target: /spec
retargeted_from: /qa (S114 Phase-6b disposition, 2026-07-20 — attribution done;
  the fork is language-normative; /spec frames it for the USER)
filed_by: /repl
filed_at: 2026-07-20
sprint_filed: 114
refers_to: spec §1.4.5 / §2.3.8 (`:`-annotation reader macro) vs macro-argument
  collection (frontend reader ↔ int macro-expansion seam)
status: open
---

## /qa S114 Phase-6b disposition (2026-07-20 — durable record: tests/plan/s114-test-plan.md §12 item 1)

**Reproduced free-standing at HEAD `9fda5f40`** (no stdlib): `(defmacro mydef
([name value] \`(defn ~name [] ~value)))` + `(mydef x :primitives/Int 5)` →
the same 3-vs-2 arity error. **Attribution confirmed (the layered shape):**
the reader emits `:primitives/Int` as ONE `Sexp::Symbol` with NO pairing
(`reader.rs::read_colon_prefix`); pairing lives exclusively in the AST builder
(`ast_builder.rs::try_consume_annotation` via `build_one_expr_at`); int's macro
expansion (`src/process_form/macro_resolution.rs::try_expand_sexp`) counts raw
Sexp children BEFORE AST build, so macro args see `:Int` standalone. The
visible arity diagnostic is int's; the missing fold is a frontend↔int
seam-ordering question.

**Why /spec:** the spec does not settle the fork. §1.4.5's "never a standalone
atom" (lexical) argues the fold must precede macro-arg collection; §2.3.8's
"every *expression* position" does not obviously cover an unevaluated macro
argument; and a sexp-level fold changes what every macro observably receives
(a synthetic annotation pair) — language surface. Frame for the user:
(a) fold before macro-arg collection (annotated macro args work uniformly;
`(def x :Int 5)` succeeds) vs (b) deliberate carve-out (spec wording amended
+ a located diagnostic naming the annotation-in-macro-arg situation). Under
EITHER ruling the current internal-sounding `returned malformed sexp … N
argument(s)` message is nonconforming — the polarity-safe pin is specified in
plan §12 item 1; /repl's diagnostic request is satisfied by both outcomes.
S115 scope input (not a trivial fix).

# `:Type` annotation does not bind the following form in macro-argument position

## Severity
Important (diagnostic quality + spec-conformance tension; needs attribution)

## Issue

Surfaced exercising the S114-rescribed `:` reader macro (§1.4.5, "binds the
immediately-following form ... in **every expression position**"). Annotation
folding is **inconsistent between function-call and macro-argument positions**:

Folds correctly (function application) — `:Type` binds the next form, one arg:
```
user> (defn one [a] a)
user> (one :primitives/Int 5)
:primitives/Int 5                      ; one arg — :Int folded onto 5
user> (defn two [a b] (+ a b))
user> (two :primitives/Int 5 7)
:primitives/Int 12                     ; two args — :Int folded onto 5, then 7
```

Does NOT fold (macro argument) — `:Type` and the following form are counted as
**two separate arguments**:
```
user> (def x :primitives/Int 5)
Error: macro error at 0..25: macro `defs/def` returned malformed sexp at 0..25:
  no matching clause for macro `defs/def` with 3 argument(s); clauses accept 2 argument(s)
```
`def` is `(def name value)` (`stdlib/defs.cl:24`, clause `[name value]`). With
folding, `(def x :Int 5)` is `(def x <annotate(5,Int)>)` = 2 args; the macro layer
instead sees `x`, `:primitives/Int`, `5` = 3 args.

Two problems:
1. **Spec tension.** §1.4.5/§2.3.8 assert the binding holds in "every expression
   position," and §1.4.5 says a `colon_prefix` is "never a standalone atom." In
   macro-argument position it effectively stands alone (the macro sees a bare
   `:Int` sexp). Either macro-argument position is a deliberate exception (then the
   spec's "every position" wording needs a carve-out) or the fold should apply
   before macro-argument collection.
2. **Diagnostic quality.** The user-visible error is internal-sounding ("returned
   malformed sexp ... N argument(s)") for a form a user reasonably expects to work
   or to be told clearly why it cannot. This violates the self-documenting-REPL
   principle (no valid-looking construct should produce an opaque error).

This is the "error signature masks a layered bug" shape (root `CLAUDE.md`): the
visible error is an int macro-expansion arity message, but the underlying question
is a frontend reader / expansion-seam ordering one. Attribution needed before a fix.

## Proposed resolution

`/qa` attributes (frontend reader annotation-fold vs int macro-argument collection
ordering) and requests a minimal repro from `/testing`. Then either (a) the fold is
made to apply before macro-argument collection so annotated macro args work
uniformly (and `(def x :Int 5)` succeeds), or (b) macro-argument position is
confirmed a deliberate reader exception — in which case `/spec` carves it out of
§1.4.5/§2.3.8's "every expression position" wording, and the diagnostic is improved
to name the annotation-in-macro-arg situation rather than emit a raw arity/malformed
message. `/repl` requests the outcome either way (the diagnostic must stop being
opaque).

## Context

`/repl` S114 Phase-6a assessment. Minimal repro is the two REPL transcripts above
(prelude loaded via `CRANELISP_LIB=stdlib`).
