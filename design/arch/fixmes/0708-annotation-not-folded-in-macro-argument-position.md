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

---

## /spec framing for the USER (S115 Phase 3 — OPEN normative question; /spec frames, does not rule)

**The one question.** When a `:Type` annotation appears in a **macro-call argument
list** — `(mydef x :primitives/Int 5)`, `(def x :primitives/Int 5)` — does the
annotation **fold onto the following form before the macro sees its arguments**
(so the macro receives two arguments: `x` and the annotated `5`), or is
macro-argument position a **deliberate carve-out** where `:Type` and the following
form are genuinely two separate arguments the macro must reckon with?

### Why the spec does not already settle it

The S114 ruling made `:` a **`^`-style reader macro** that "binds the
immediately-following form … in **every expression position**" (§1.4.5, §2.3.8),
and declared a `colon_prefix` "**never a standalone atom**." That wording reads two
ways at the macro-argument seam:

- §1.4.5's "never a standalone atom" and "every position" argue the fold is a
  read-level fact that must hold *before* a macro collects its arguments — a bare
  `:Int` sitting alone in a macro's argument list is exactly the standalone atom
  §1.4.5 forbids.
- §2.3.8's "every **expression** position" enumerates positions in the **built
  AST** (top-level, parenthesized, application argument, `let` value, `match`-arm
  body, `if`/`fn`/`let` body, vector element). A macro argument, at the moment the
  macro layer inspects it, is an **unevaluated `Sexp`** — not yet an expression —
  so §2.3.8's list does not obviously reach it.

As built, the two live on opposite sides of a layering seam: the reader emits
`:primitives/Int` as one `Sexp::Symbol` with **no** pairing
(`reader.rs::read_colon_prefix`); the fold that pairs `:Type` with the next form
into an annotation lives **later**, in the AST builder
(`ast_builder.rs::try_consume_annotation`); and macro expansion counts raw `Sexp`
children **before** the AST build
(`process_form/macro_resolution.rs::try_expand_sexp`). So a macro sees `:Int`
standalone, and a 2-clause macro handed `x`, `:Int`, `5` reports a 3-vs-2 arity
error. In function-**application** position the AST builder folds first, so
`(one :Int 5)` is correctly one argument.

### Reading A — fold before macro-argument collection (`:Type` is one unit everywhere the reader produces `Sexp`s)

`:Type <form>` is a single read-time unit in **every** position that carries
`Sexp`s, macro-argument lists included. `(mydef x :Int 5)` presents the macro two
arguments (`x`, and the annotated `5`); `(def x :Int 5)` succeeds by language
mechanism, no stdlib change.

- **User-visible behavior:** annotated macro arguments work uniformly; `(def x
  :Int 5)` binds `x` to a `5` constrained to `Int`. This is the most faithful
  realization of "reader macro **in the manner of Clojure's `^`**" — Clojure's `^`
  attaches at **read** time, before any macro sees the form.
- **But it changes what every macro observably receives.** A macro that today
  destructures/counts its arguments as raw `Sexp`s would now see a **synthetic
  folded annotation form** where it used to see two children. That is a
  language-surface change to the macro contract (§9).
- **Load-bearing sub-question this reading forces:** *what is the `Sexp` shape of
  the folded annotation a macro observes* — one that macros can quote, unquote, and
  destructure? §2.3.8 currently defines `annotate_expr` as an **AST node**, not an
  `Sexp` shape; Reading A needs a representable read-time form (e.g. a synthetic
  `(annotate Type form)` list, or a metadata-carrying token à la `^meta`).
- **Spec sections touched:** §1.4.5 + §2.3.8 (state the fold is read-time and that
  macros receive a folded annotation `Sexp`), §9 (macros — define the folded-`Sexp`
  shape macros observe), a new normative example. The folded-`Sexp` representation
  may additionally be a `cranelisp-types`/`Sexp` design question (flag to /arch),
  not pure scribing.

### Reading B — macro-argument position is a deliberate carve-out (`:Type` is a genuine standalone `Sexp` there)

The fold stays an AST-build operation (as built); a macro operates on raw `Sexp`s
before AST build, so `:Type` legitimately stands alone in a macro's argument list.
"Every expression position" means "every **built-AST** expression position," which
does **not** include unevaluated macro-argument position.

- **User-visible behavior:** annotated macro arguments do **not** auto-fold.
  `(def x :Int 5)` does **not** succeed by a language fold — for it to work at all,
  the `def` **macro** would have to accept the extra argument (its clause becomes
  something like `[name : type value]` or variadic), which is a **stdlib** change,
  not a language mechanism.
- **No change to what macros receive** — matches the as-built layering (reader →
  macro-expand over `Sexp`s → AST-build folds).
- **But two spec corrections fall out:** (1) §1.4.5's "**never a standalone atom**"
  must be qualified — a `colon_prefix` *can* stand alone in a pre-AST-build
  macro-argument list; (2) §2.3.8's "every expression position" needs an explicit
  carve-out naming macro-argument (pre-AST-build) position.
- **Spec sections touched:** §1.4.5 (qualify "never a standalone atom"), §2.3.8
  (carve "every expression position" → "every built-AST expression position"), plus
  a **diagnostic requirement** (below).

### Common to both rulings — the diagnostic is nonconforming today

Under **either** reading, the current user-visible error —

```
macro `defs/def` returned malformed sexp … no matching clause … with 3 argument(s); clauses accept 2 argument(s)
```

— is internal-sounding for a form a user reasonably expects to work or to be told
plainly why it cannot (the self-documenting-REPL principle: no valid-looking
construct produces an opaque error). Reading A makes the form **succeed**; Reading B
requires the message be **replaced** by a located diagnostic that names the
annotation-in-macro-argument situation. /repl's request is satisfied either way; the
polarity-safe pin is `tests/plan/s114-test-plan.md` §12 item 1.

### /spec's neutral consistency note (analysis, not a ruling)

The S114 ruling's **letter** was scribed as an `annotate_expr` **AST** production
whose "every expression position" list enumerates **built-AST** positions — that is
the Reading-B layering. The S114 ruling's **analogy** ("a reader macro **in the
manner of Clojure's `^`**") points the other way: `^` attaches at **read** time,
before macros run — Reading A. The two pull apart precisely at this seam, which is
why it is a genuine normative fork for the user and not resolvable by scribe. If the
user rules **A**, the `^`-analogy is honored but the macro contract gains a
folded-`Sexp` form (a §9 + likely design consequence); if the user rules **B**, the
as-built layering stands but §1.4.5/§2.3.8's "never standalone / every position"
wording is corrected to built-AST scope and the opaque diagnostic is replaced by a
located one.
