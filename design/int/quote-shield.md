# Int quote shield — `expand_scoped` holds quoted data out of Pass-1 macro expansion

Scoped subordinate design doc (S111, FIXME 0613; `/arch` Phase-2 §3 correction).
Master: `int.md`. Code home: `src/expander.rs` (`expand_scoped`). Owner surface:
int (`/dev` implements in Phase 5). This doc is the design intent for the int leg
of the quasiquote-legal-everywhere wave; the frontend leg (folding
`expand_quasiquotes` into `build_forms`) is `design/frontend/`.

## 1. Why the shield exists — the hazard the fold unmasks

Sprint 111 rules 0613 **(A) legal everywhere**: quote/quasiquote desugar wherever
an expression is legal. The delivery folds `expand_quasiquotes` into frontend
`build_forms`, so every form is desugared before `build_form` dispatch.

int's Pass-1 macro expander runs **before** `build_forms` — i.e. before the fold's
desugar point. `expand_scoped` (`src/expander.rs:735`) recurses into **all**
sub-lists of a form, recognising and dispatching macro-call-shaped heads, with the
only verbatim shields today being the binding forms (`let`/`fn`/`lambda`/`defn`/
`defn-`/`match`, §8.6.3) and the `defmacro` name position (S102 CS-D1). There is
**zero quote/quasiquote handling** (verified: no `quote` reference anywhere in the
file).

Once quote is legal everywhere, that gap becomes a live corruption surface. A
macro-call-shaped list living inside quoted **data** would be macro-expanded before
the desugar ever sees it:

```clojure
(defn f [] '(m x))     ; m a registered macro
```

The quoted literal `(m x)` is data — it must reach `build_form` intact so the fold
turns it into `(macros/SexpList …)` constructor calls yielding the value
`(m x)`. But `expand_scoped` recursing into the `defn` body sees `(m x)` as a macro
call and rewrites it to `m`'s expansion — **silent data corruption**. Today this is
masked only because the quote dies at `build_form` first (0613's parse error); the
fold removes that mask, so the shield must land in the same logical wave (see §6).

## 2. Where the shield sits

Two guard clauses at the **top of the non-empty `Sexp::List` arm** of
`expand_scoped`, before the binding-form dispatch and before macro-head recognition
(step 2). A `quote`/`quasiquote`-headed list must short-circuit before any macro
recognition can fire on its head or descend into its body.

Placement relative to the binding-form check is immaterial for correctness (no
binding form is named `quote`/`quasiquote`), but placing the shield **first** is the
clearest statement of intent: a reader-quote head is handled by the shield and
nothing else.

## 3. The two rules

**Rule Q (`quote`): fully verbatim, no descent.** A `(quote X)` form is pure data.
Return the subtree unchanged — do **not** recurse into `X` at all. This mirrors the
frontend's `expand_quote_template`, which has no unquote handling: top-level quote
is pure structural quotation.

**Rule QQ (`quasiquote`): descend only into live unquotes, tracking depth.** A
`(quasiquote T)` template is mostly data, but `unquote`/`unquote-splicing` bodies at
the matching nesting depth are **ordinary expression positions** where macro calls
SHOULD expand (they evaluate in the current scope, §9.4.2). Walk the template
holding every node verbatim EXCEPT the body of a **live** unquote/unquote-splicing,
which is handed back to `expand_scoped` for normal expansion. Nested quasiquotes
raise the depth so their unquotes stay shielded until they reach their own live
level.

The depth convention **mirrors the frontend `expand_qq_template`/`expand_qq_list`
math exactly** (`quasiquote.rs:263–366`), so shield and fold agree on which unquotes
are live: the quasiquote body is walked at `qq_depth = 0`; `unquote`/
`unquote-splicing` are live at depth 0; a nested `(quasiquote …)` increments depth;
an `(unquote …)`/`(unquote-splicing …)` decrements it.

## 4. Algorithm (depth-tracking pseudo-logic)

`expand_scoped`, non-empty `Sexp::List(children, span)` arm — new prelude before the
existing binding-form / macro-head / default-recurse steps:

```
// SHIELD (reader-quote family) — matched STRUCTURALLY, no shadows consult (see §5).
if let Sexp::Symbol(head, _) = &children[0] {
    if head == "quote" && children.len() == 2 {
        // Rule Q — quoted data is never expanded. No descent.
        return Ok(Sexp::List(children, span));
    }
    if head == "quasiquote" && children.len() == 2 {
        // Rule QQ — body walked at qq_depth 0; only live unquotes expand.
        let inner = shield_qq(children.pop_body(), resolver, depth,
                             origin_span, shadows, /*qq_depth=*/0)?;
        return Ok(Sexp::List(vec![head_symbol, inner], span));
    }
}
// … existing: binding-form dispatch → macro-head recognition → default recurse
```

The template walker (new helper; its own `qq_depth`, distinct from the macro
`depth` expansion-limit counter):

```
fn shield_qq(node, resolver, depth, origin_span, shadows, qq_depth) -> Result<Sexp> {
  match node {
    Sexp::List(children, span) if !children.is_empty() => {
      if let Sexp::Symbol(h, _) = &children[0] {
        if (h == "unquote" || h == "unquote-splicing") && children.len() == 2 {
          if qq_depth == 0 {
            // LIVE unquote — ordinary expression position: expand macros here.
            let e = expand_scoped(body, resolver, depth, origin_span, shadows)?;
            return Ok(Sexp::List(vec![head, e], span));
          } else {
            // nested: decrement, stay shielded.
            let inner = shield_qq(body, …, qq_depth - 1)?;
            return Ok(Sexp::List(vec![head, inner], span));
          }
        }
        if h == "quasiquote" && children.len() == 2 {
          // nested quasiquote: increment depth, stay shielded.
          let inner = shield_qq(body, …, qq_depth + 1)?;
          return Ok(Sexp::List(vec![head, inner], span));
        }
      }
      // Ordinary list under quasiquote (INCLUDING a nested `(quote …)`, see §5.1):
      // recurse structurally at the SAME depth so inner live unquotes are found.
      let mapped = children.map(|c| shield_qq(c, …, qq_depth))?;
      Ok(Sexp::List(mapped, span))
    }
    Sexp::Bracket(children, span) => {
      // Brackets can't head an unquote but CAN contain live unquotes (`[~x ~y]`).
      let mapped = children.map(|c| shield_qq(c, …, qq_depth))?;
      Ok(Sexp::Bracket(mapped, span))
    }
    atom | Sexp::Comment(..) => Ok(node),  // verbatim
  }
}
```

Notes:
- `shield_qq` never errors on `unquote-splicing` at qq_depth 0 ("~@ not valid at top
  level of quasiquote" is the **fold's** diagnostic; the shield just expands the body
  and hands the tree on — the fold raises the error unchanged). Keeping unquote and
  unquote-splicing on the SAME arm keeps the shield minimal and defers the one
  error site to its single owner.
- No `depth`-limit change: `shield_qq` threads the macro `depth` untouched into the
  `expand_scoped` re-entry so the expansion-depth guard still fires for macros
  expanded inside a live unquote.

## 5. Currency invariant — shield and fold in lockstep, matched structurally

The shield holds verbatim **exactly** the subtrees the frontend fold will later
desugar. Both sides recognise the reader-quote family by the SAME structural test
the frontend uses: a two-element list whose head is the bare symbol `quote`/
`quasiquote`/`unquote`/`unquote-splicing` (`quasiquote.rs:53–68`). The shield
therefore does **not** consult `shadows` and does **not** consult the macro
resolver for these heads — neither does the fold. If the two tests ever diverge, a
subtree either gets double-desugared or expanded-then-desugared; keeping them
byte-identical (bare-symbol head + `len()==2`) is the durable coupling. This is the
BC §1/§6 currency claim in code form: **int's expander is quote-blind by shield,
not by accident** (the BC sentence itself is `/arch`'s to author per Phase-2 §3;
the `src/CLAUDE.md` §"Macro expansion" code-voice sentence is `/dev`'s at
implementation).

### 5.1 The subtle case — `quote` INSIDE an active quasiquote is NOT a boundary

At the **top level** (`expand_scoped`), `(quote X)` is fully verbatim (Rule Q). But a
`(quote …)` encountered **while shielding a quasiquote** is treated as an ordinary
list — `shield_qq` keeps walking its children at the same depth, so a live unquote
inside it is still found and expanded (`` `(quote ~x) `` — the `~x` is live). This
matches the frontend exactly: `expand_qq_list` special-cases only unquote/
unquote-splicing/quasiquote heads and lets `(quote …)` fall through to ordinary
child recursion at all depths. The asymmetry (top-level quote = verbatim boundary;
quote-under-active-quasiquote = ordinary list) is intentional and load-bearing —
do not add a `quote` short-circuit inside `shield_qq`.

## 6. Ordering note (binding on the Phase-4 wave plan)

Per `/arch` Phase-2 ordering constraint 2: **the int quote-shield lands ≤ the
frontend fold.**

- **Shield-only (before the fold) is inert-safe.** Quote still dies at `build_form`
  (0613's parse error is still live), so nothing reaches the shield's new arms in a
  way that changes observable behaviour — the shield is dormant until the fold makes
  quote legal. Landing it first (or in the same change-set) is always safe.
- **Fold-without-shield is NOT safe.** It opens the §1 corruption surface: a
  macro-call-shaped list inside quoted data gets macro-expanded before desugar. So
  the fold must never land ahead of the shield.

Two `/dev` surfaces (`cranelisp-frontend` fold + `src/` shield), **one logical
wave**; dispatch the int shield first or same-change-set, never after.

## 7. Size estimate

~40–55 lines in `src/expander.rs`: the two guard clauses in `expand_scoped`
(~10 lines) + the `shield_qq` template walker (~30 lines) + doc comments. (The
`/arch` §3 "~15-line" figure counts the guard-clause core; the honest total with the
depth-tracking walker and its rustdoc lands around 40–55.) Zero public-API impact
(binary — the e2e suite is the conformance gate). No new types, no cache/schema
touch, no new session state.

## 8. Testability — the interaction matrix `/testing` must cover

Principle 5 (testability is structural): the shield is a pure `Sexp → Sexp`
transform reachable through the REPL `/expand` command and end-to-end through any
`defn` body / top-level form, so it is directly exercisable without session state.

The 0613 form × position × mode matrix (`/qa`/`/testing` own the authoring) gains
the **macro-expansion interaction rows** — a registered macro `m` in
macro-call shape, placed in each quote context, at each position, must OR must-not
expand:

| # | Macro-call shape context | Position | Expected |
|---|---|---|---|
| 1 | under `quote` — `'(m x)` | `defn` body | **NOT expanded** (held verbatim → desugars to the literal `(m x)`) |
| 2 | under `quote` — `'(m x)` | top level | **NOT expanded** |
| 3 | under `quasiquote`, outside any unquote — `` `(m x) `` | `defn` body | **NOT expanded** (template data) |
| 4 | under `quasiquote`, outside any unquote — `` `(m x) `` | top level | **NOT expanded** |
| 5 | under live `unquote` — `` `(a ~(m x)) `` | `defn` body | **expanded** (ordinary expression position) |
| 6 | under live `unquote` — `` `(a ~(m x)) `` | top level | **expanded** |
| 7 | under live `unquote-splicing` — `` `(a ~@(m x)) `` | `defn` body | **expanded** |
| 8 | under live `unquote-splicing` — `` `(a ~@(m x)) `` | top level | **expanded** |

Rows 1–4 are the corruption guard (the reason the shield exists); rows 5–8 pin that
the shield does not over-shield (unquote bodies remain live). Both REPL and `--run`
modes (the fix is mode-uniform; the shield runs in the one shared Pass-1 loop).

**Depth guard (recommended addition to the matrix):** a nested quasiquote
`` `(a `(b ~(m x))) `` — the inner `~(m x)` is at qq_depth 1 for the OUTER
quasiquote, so it must **NOT** expand at the outer level (it is data for the outer
template); it becomes live only when the inner template is itself evaluated. This
pins the depth-tracking, distinguishing the shield from a naive "expand any unquote"
approach.

## 9. Cross-references / manifestation

- `design/arch/fixmes/0613-quasiquote-not-desugared-outside-macro-clauses.md` — the
  defect; `sprints/SPRINT.md` §"Architecture review (Phase 2)" §3 — the `/arch`
  ruling this doc implements.
- Frontend leg (the fold + backstop): `design/frontend/` + `crates/cranelisp-frontend`
  (`expand_quasiquotes`, `ast_builder.rs:1160+` rejection stays as the backstop).
- `src/CLAUDE.md` §"Macro expansion" — the code-voice sentence lands here at `/dev`
  implementation (quote-blind by shield).
- BC §1/§6 (frontend desugars; int expander quote-blind by shield) — `/arch`
  Phase-3 action.
- `macro-resolver-impl.md` — the sibling expander glue design; the shield is a new
  arm in the same `expand_scoped` walk.
