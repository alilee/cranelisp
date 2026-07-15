---
number: 0613
target: /dev
filed_by: /qa
filed_at: 2026-07-15
sprint_filed: 110
scheduled: S111 (default; /sprint MAY pull into the S110 W-SRC chain if slack — see §Fix-vs-carry)
refers_to: SG-1 attribution — the 0605 stdlib-compile gate's first catch
  (`tests/stdlib_conformance.rs::stdlib_all_public_modules_compile_and_run`,
  36/37 clean; `derive` fails). This is LAYER 1 of a layered finding; layer 2
  is FIXME 0614 (/stdlib). Attribution record
  `tests/plan/s110-attribution-sg1-sg2.md`.
status: open
---

# Quote/quasiquote never desugared outside macro-clause compilation — templates in ordinary `defn` bodies die as parse errors

## Minimal repro (mode-uniform: REPL ≡ `--run`; stdlib-free; verified 2026-07-15 on HEAD)

```clojure
(defn helper [x] `(if ~x 1 0))
;; => parse error: unexpected quasiquote form — should have been expanded
```

The whole reader-quote family is affected, in every non-`defmacro` position:
`'(1 2)` at top level and `(defn f [] '(1 2))` die identically
(`unexpected quote form — …`). REPL and `--run` produce the same error.

**Control (works):** the same template inside a `defmacro` clause body
compiles and expands correctly — `(defmacro m [x] `(if ~x 1 0))` +
`(m true)` expands fine.

This is exactly what the SG-1 gate hit: compiling `stdlib/derive.cl` fails at
byte 5306 = line 166, the FIRST quasiquote in a plain `defn-` body
(`build-eq-chain`) — no macro invocation anywhere in the probe
(`(import [derive [*]])` + trivial `main`).

## Mechanism / suspected locus

- The ONLY production caller of `cranelisp_frontend::expand_quasiquotes` is
  `src/process_form/macro_clause.rs:53` (macro-clause synthesis). No other
  form ever gets desugared.
- The stated contract says desugaring runs on EVERY form:
  - `crates/cranelisp-frontend/src/lib.rs:48` — "Quasiquote desugaring runs
    before `build_form`".
  - `design/frontend/frontend.md:127` — "It runs unconditionally on every
    form, before macro-call dispatch."
  - `design/frontend/s76-syntactic-only.md` (frontend.md-cascade row) —
    "quasiquote desugaring runs before `build_form`; macro expansion is
    performed by int/typecheck before the expanded forms reach `build_form`."
- `crates/cranelisp-frontend/src/ast_builder.rs:1171` is the backstop that
  fires ("should have been expanded" — the builder EXPECTS desugaring to have
  already happened; this is a wiring gap, not a deliberate rejection).
- Likely lost in the S76 W-Macro migration: when frontend `expand` was deleted
  and expansion moved to int's Pass-1 loop, the unconditional desugar step did
  not survive on the non-macro form path.

## Spec basis (why this is a defect, not a restriction)

- Spec §9.4.1: quasiquote is reader-level **"syntactic sugar"** desugared to
  `Sexp` constructor calls; nothing restricts it to macro bodies. §9.4.2:
  "Unquote `~expr` evaluates `expr` in the **current scope**" — general.
- The desugared equivalent (raw `SexpList`/`SCons` calls) compiles fine in
  `defn` bodies — `core.syntax` and derive.cl's raw-ctor helpers are
  gate-green.
- §9.3.4's own prescribed remedy for macro helpers — "a macro that needs a
  helper MUST place that helper in a **dependency module**" — presupposes
  Sexp-template construction in ordinary dependency-module `defn`s; without
  this fix every such helper must be hand-written in raw constructors.
- Even under a restrictive reading, the current diagnostic leaks an internal
  invariant — a violation of the self-documenting principle either way.

**One-line /spec confirmation requested at the next user gate** (via
`/sprint` → `/spec`): "quasiquote/quote are legal wherever an expression is
legal (desugar on every form)?" Default disposition is the fix below; if the
user instead rules macro-clause-only, the resolution flips to (a) a proper
diagnostic ("quasiquote is only valid inside defmacro") + (b) FIXME 0614's
raw-ctor rewrite becoming mandatory + (c) a spec §9.4 sidenote.

## Fix shape (seam question for /dev, small /arch touch)

Either int's single form chokepoint gains the `expand_quasiquotes` call
(restoring the stated contract), or desugaring folds INTO frontend
`build_form`/`build_expr` so no caller can forget (the single-codepath lever;
`macro_clause.rs:53` then becomes redundant/idempotent). Keep the
`ast_builder` rejection as the backstop invariant. The fix must cover the
family uniformly: `quote`, `quasiquote`/`unquote`, `unquote-splicing`.

## /testing request — committed narrow repro (before or with the fix)

Failing-not-ignored, joining the S110 RED set as the durable record:

- `quasiquote_in_defn_body_desugars` (the 1-liner above) + the `quote`
  sibling; a form × position matrix per the standing variants lens
  (positions: defmacro clause body [green control], `defn`/`defn-` body,
  top-level expr; forms: quote / quasiquote+unquote / unquote-splicing;
  modes: REPL + `--run`).
- `// spec: spec/09-macros.md §9.4` and
  `// defect: class=wrong-reject locus=src/process_form (missing pre-build_form desugar) found=S110 owner=/dev`.

## Fix-vs-carry

Default **carry to S111**: `derive` is uninvoked (nothing in the corpus
imports it), S110 is already broad, and the fix wants the seam ruling above.
The fix itself is small; if the W-SRC chain has slack, `/sprint` may pull it
in. Until fixed, the SG-1 gate stays RED tracing to THIS + 0614 —
**excluding `derive` from the gate is NOT acceptable** (recreates the
blindness 0605 exists to cure).
