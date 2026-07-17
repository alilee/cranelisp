# Quasiquote/quote desugar fold into the AST chokepoint

> Subordinate topic doc, cited from `design/frontend/frontend.md` §4. Owned by
> `/design` (frontend). Authored S111 Phase 3 for FIXME 0613, against the
> `/arch` Phase-2 architecture-review ruling (SPRINT.md §"Architecture review
> (Phase 2)" §3). Pre-implementation; `/dev` implements in Phase 5.

## 0. The defect this closes (FIXME 0613)

Quote/quasiquote templates die as parse errors everywhere **except** inside a
`defmacro` clause body:

```clojure
(defn helper [x] `(if ~x 1 0))
;; => "unexpected quasiquote form — should have been expanded"
```

The whole reader-quote family (`'`/`` ` ``/`~`/`~@`) is affected in every
non-`defmacro` position (top-level expr, `defn`/`defn-` body). The mechanism:
the ONLY production caller of `cranelisp_frontend::expand_quasiquotes` is
`src/process_form/macro_clause.rs:67` (macro-clause synthesis). No other form is
ever desugared, so the ordinary-form path reaches the `ast_builder.rs:1167+`
backstop with the quote head still present.

**Ruled (A) by the user gate this sprint** (via `/sprint`→`/spec`):
quasiquote/quote are legal wherever an expression is legal (desugar on every
form). Spec basis: §9.4.1 (quasiquote is reader-level syntactic sugar, no
macro-body restriction), §9.4.2 (unquote evaluates in the current scope —
general), §9.3.4 (macro helpers presuppose Sexp-template construction in
ordinary dependency-module `defn`s).

## 1. The fold point — the single-codepath lever

Desugaring folds INTO the two frontend AST-entry chokepoints so **no caller can
forget it** (Principle 7 — single source of truth; Principle 18 — enforce
invariants structurally). The chokepoints, verified as the complete production
entry set:

| Chokepoint | `ast_builder.rs` | Production callers |
|---|---|---|
| `build_forms(sexps)` | :287 | `src/worker.rs::build_program_compat` → the **universal** path (REPL, `--run`, `--link`, `process_cluster`, agent, index_worker, save-regen slash) |
| `build_form(sexp)` | :180 | `src/save.rs:1881/1901` (persisted-source re-parse of a single top-level form) |

`build_expr` (`ast_builder.rs:1136`) has **zero production direct callers** — it
is the internal expression-recursion primitive and the `build_forms` bare-expr
branch (line 317). It therefore does **not** receive the fold; it trusts its
input is already desugared and keeps the backstop (§4) as the structural guard.
Folding at `build_expr` would re-walk each subtree O(depth) times per node — the
fold belongs at the two OUTER form boundaries only.

### 1.1 Placement within each chokepoint

Both chokepoints desugar the **whole** sexp tree they receive as their FIRST
step, before any head-shape dispatch or `:Type` pairing:

- **`build_forms`**: map `expand_quasiquotes` over the input slice once, up
  front, producing a desugared `Vec<Sexp>`; run the existing annotation-pairing
  + dispatch loop over the desugared vec. `expand_quasiquotes` preserves
  structure (a `:Type` annotation sexp `Sexp::Symbol(":Foo")` is untouched; the
  following quote/quasiquote form is rewritten in place, still one slice
  element), so the `:Type`-binds-following-form pairing (BC §1 invariant 9) is
  unaffected — desugar-then-pair is order-safe.
- **`build_form`**: desugar `sexp` once, then dispatch.

**Recommended shape (avoids a redundant second walk):** extract the current
`build_form` body into a private `build_form_inner(sexp)` that assumes a
desugared input; make the public `build_form = expand_quasiquotes then
build_form_inner`; have `build_forms`' internal dispatch (line 311) call
`build_form_inner`, not the public `build_form`, since `build_forms` already
desugared the slice. This keeps exactly ONE desugar pass per form. The naive
alternative (leave line 311 calling public `build_form`, which re-desugars) is
also **correct** by idempotence (§2) — the second pass is a structural no-op —
but costs one extra tree walk per top-level form; `/dev` may pick either, the
private-core split is preferred for cleanliness.

`build_expr` is unchanged apart from keeping its backstop.

## 2. Idempotence contract — the transform is a fixpoint

**Claim.** For every `Sexp s`,
`expand_quasiquotes(expand_quasiquotes(s)) ≡ expand_quasiquotes(s)` structurally,
**including spans and any minted gensyms**. One pass reaches the fixpoint: **no
`quote`/`quasiquote`/`unquote`/`unquote-splicing` head symbol in operator
position survives one pass.**

Why it holds (each grounds a `/testing` assertion):

1. `expand_quasiquotes` rewrites exactly the arity-2 list forms whose head
   `Sexp::Symbol` is `quote` or `quasiquote`, replacing them with
   `macros/Sexp*` constructor-call trees; every other node is structurally
   rebuilt by recursing into its children (`quasiquote.rs:193–226`).
2. Output constructor heads are `macros/SexpSym`, `macros/SexpList`,
   `macros/SexpInt`, `macros/SexpBracket`, `macros/SCons`, `sconcat`, … — none
   equal to `quote`/`quasiquote`. A quoted occurrence of the *word* becomes a
   **string literal**: `'quote` → `(macros/SexpSym "quote")` — the token is now
   inside a `Sexp::Str`, never a head `Sexp::Symbol`. So `is_quote`/`is_quasiquote`
   (which match a `Symbol` head) never fire on a second pass.
3. Auto-gensym (`x#`) and synthetic spans are minted **only** while rewriting a
   quasiquote template. A second pass finds no templates → mints nothing → the
   tree is bit-identical (span-stable, gensym-stable). This is what makes the
   fixpoint hold *including spans*, not just up to structure.
4. `unquote`/`unquote-splicing` are meaningful only inside a quasiquote
   template (handled depth-tracked by `expand_qq_list`). The depth-0 `(unquote
   e)` splices `e` verbatim, then `expand_quasiquotes` recurses into the whole
   result so any quasiquote nested inside `e` is also desugared — the re-descent
   is why nested templates reach the fixpoint in the same pass.

**Consequence for the existing `macro_clause.rs:67` caller — KEEP it.** Post-fold
its `expand_quasiquotes(&synth_sexp)` (step 2) desugars the synthesised clause
defn; step 3's `build_program_compat` → `build_forms` desugars it **again** — a
structural no-op by the fixpoint. The explicit call is now **redundant but
harmless**, and is retained deliberately (per the §3 ruling): it documents intent
at the one site that hand-builds a compiler-generated Sexp, and removing it is a
separate cleanup outside this scope. The idempotence contract is precisely what
makes the double-desugar safe — the fold does not require the caller to be
removed, and no other caller needs auditing for a pre-existing `expand_quasiquotes`.

## 3. Backstop invariant — a surviving quote head is a bug

The `ast_builder.rs:1167–1181` rejection in `build_list_expr`
(`quote`/`quasiquote`/`unquote`/`unquote-splicing` → "should have been
expanded") **stays**, as the structural enforcement that the fold ran
(Principle 18). Post-fold its semantics sharpen:

- A surviving **`quote`/`quasiquote`** head reaching `build_list_expr` is
  **always a compiler bug** — these are desugared wherever they appear in the
  tree, so their arrival means a NEW form-entry chokepoint was added that
  bypassed the fold. The backstop converts a silent mis-lowering into a loud
  diagnostic at exactly the seam that assumed desugaring.
- A surviving **`unquote`/`unquote-splicing`** head can also be a **genuine user
  error** — `~x`/`~@x` written outside any quasiquote template. `expand_quasiquotes`
  leaves such forms untouched (they are not under a quasiquote), so the backstop
  correctly rejects them. (The "should have been expanded" wording is slightly
  off for this user-error case; a friendlier "unquote outside quasiquote" message
  is a possible follow-up refinement, out of this scope — the rejection itself is
  correct.)

The backstop is NOT removed and NOT weakened. It is the invariant's fence, not a
feature gate.

## 4. Family covered uniformly

The reader (`reader.rs`) desugars the sigils at read time —
`'x`→`(quote x)`, `` `x ``→`(quasiquote x)`, `~x`→`(unquote x)`,
`~@x`→`(unquote-splicing x)` — so all four surface as list forms with these head
symbols. `expand_quasiquotes` covers the whole family in one walk:

- `quote` → `expand_quote_template` (pure structural quotation, no unquote).
- `quasiquote` → `expand_qq_template` (depth-tracked; `unquote`/`unquote-splicing`
  resolved inside at depth 0, structurally re-quoted at depth > 0).
- `unquote` / `unquote-splicing` → meaningful only inside a quasiquote;
  standalone occurrences fall through to the §3 backstop.

The fold is the family, not a subset — the mandate is uniform coverage
(`/qa`/`testing`'s 0613 matrix: forms {quote / quasiquote+unquote /
unquote-splicing} × positions {defmacro clause body [green control], `defn`/`defn-`
body, top-level expr} × modes {REPL, `--run`}).

## 5. Currency fix — `lib.rs:48`

The crate-root rustdoc claim (`crates/cranelisp-frontend/src/lib.rs:48`):

> "Quasiquote desugaring runs before `build_form`; macro expansion is performed
> by int/typecheck before the expanded forms reach `build_form`."

is **currently FALSE** — desugaring ran only in `macro_clause.rs`, not on the
general form path — and becomes **TRUE** with this fold (desugar is the first
step of `build_forms`/`build_form`). `/dev` keeps the claim and sharpens it in
the implementing change-set, e.g.: *"Quasiquote/quote desugaring is folded into
`build_forms`/`build_form` as their first step — the whole reader-quote family
(`quote`/`quasiquote`/`unquote`/`unquote-splicing`) is a fixpoint after one pass,
so no caller can bypass it and re-desugaring is a no-op. Macro expansion is
performed by int/typecheck before the expanded forms reach the fold."* The
edit is `/dev`'s (code rustdoc); this design pins the intent and the truth-flip.

`design/frontend/s76-syntactic-only.md:74` carries the same aspirational wording
("quasiquote desugaring runs before `build_form`"); it becomes literally accurate
post-fold and needs no rewrite (a pointer is added in frontend.md §9).

## 6. The pipeline chain, post-fold

```
reader (' ` ~ ~@ → (quote…)/(quasiquote…)/(unquote…)/(unquote-splicing…))
  → int Pass-1 macro expansion  [src/expander.rs::expand_scoped — QUOTE SHIELD, §7]
  → build_program_compat (flatten_begin)
  → build_forms  ── DESUGAR FOLD (expand_quasiquotes, §1) ──┐
       ├─ :Type pairing (BC §1 invariant 9)                  │ one fixpoint pass
       ├─ build_form_inner  (top-level forms)                │ over the whole tree
       └─ build_expr        (bare exprs; backstop §3 guards) ┘
```

Desugar runs **after** macro expansion and **before** per-form build. That
ordering is load-bearing for §7.

## 7. Named seam — int's quote shield (out of frontend's surface)

The `/arch` Phase-2 §3 correction: the moment quote is legal everywhere, a
second seam goes live. Int's Pass-1 macro expansion (`src/expander.rs::expand_scoped`
/ `expand_sexp_recursive`, ~715–829) recurses into all sub-lists with **no
quote/quasiquote handling** and runs BEFORE the fold. Without a shield, a
macro-call-shaped list inside quoted data — `(defn f [] '(m x))` with `m` a
registered macro — would have its quoted **literal** macro-expanded before the
desugar ever sees it: silent data corruption. Today that is masked only because
the quote dies at `build_form` first; the fold unmasks it.

**Frontend-side invariant (this design's surface):** frontend desugars the
reader-quote family **exactly once, at the `build_forms`/`build_form` boundary,
operating on the fully-macro-expanded sexp tree**. Frontend does NOT desugar
before macro expansion — therefore **macros receive raw `(quote …)`/`(quasiquote
…)` argument sexps** (the conservative semantics: a macro sees the sexp the user
wrote; desugar-before-expansion would change macro-arg representation observably).
Desugaring is exclusively frontend's, once, at the fold; the shield never
desugars.

**Complementary obligation (int's surface, a separate `/design`(int) dispatch
owns `src/expander.rs`):** Pass-1 macro expansion must not rewrite the interior
of quoted literals — hold `quote` subtrees fully verbatim; within `quasiquote`
descend ONLY into `unquote`/`unquote-splicing` bodies (ordinary expression
positions where macro calls SHOULD expand), tracking quasiquote nesting depth so
nested quasiquotes stay shielded. This is named here as the paired invariant, not
designed here. **Ordering constraint (SPRINT.md §3):** the int shield lands ≤ the
frontend fold — shield-only is inert-safe (quote still dies at `build_form`);
fold-without-shield opens the new data-corruption surface.

`/testing`'s 0613 matrix gains the interaction rows (per §3): {macro-call shape
inside quote / inside quasiquote outside unquote / under unquote / under
unquote-splicing} × {defn body, top level} — the first two must NOT expand, the
last two MUST.

## 8. Public-API / cross-crate impact

**Zero public-API diff** for the frontend crate:
`build_form`/`build_forms`/`build_expr` signatures are unchanged;
`expand_quasiquotes`/`expand_quote_template`/`next_synthetic_span` stay `pub`
(the standing quasiquote API — REPL `/expand`, user macros). No
`cranelisp-types` edit; no cache/schema impact (the fold is a pure Sexp→Sexp
rewrite before AST). No baseline regeneration is required by the frontend change
on its own; `/dev` confirms `public-api.txt` is unchanged at PR time.

## 9. Testability (Principle 5)

The fold is unit-testable at the frontend boundary with no session:

- **Positive**: `build_forms`/`build_form` on `(defn helper [x] \`(if ~x 1 0))`
  and the `quote`/`unquote-splicing` siblings succeed and produce the
  `macros/`-constructor AST (the FIXME 0613 repro, now green).
- **Idempotence**: `expand_quasiquotes(expand_quasiquotes(s)) ==
  expand_quasiquotes(s)` for representative `s` including `'quote`, `` `(m ~x) ``,
  nested quasiquotes — asserting span/gensym stability (§2).
- **Backstop preserved (negative)**: a hand-built `Sexp` with a surviving
  `(unquote x)` outside any quasiquote still errors at `build_expr`; and (bug
  guard) a raw `(quote x)` fed to `build_expr` directly still hits the backstop
  (build_expr does not fold).
- **Matrix**: the form × position × mode matrix (§4) is `/qa`/`testing`-owned
  e2e; the frontend unit tier pins the boundary behaviour.

Unit tests are `/dev`'s; e2e/matrix is `/qa`+`/testing`'s. This design authors no
tests.

## 10. Cross-references

- `design/frontend/frontend.md` §4 — form-classification + dispatch (master; the
  fold is named there in the chain).
- `crates/cranelisp-frontend/src/ast_builder.rs` :180 (`build_form`), :287
  (`build_forms`), :1167 (backstop) — fold + backstop sites.
- `crates/cranelisp-frontend/src/quasiquote.rs` — `expand_quasiquotes` (:193),
  `expand_quote_template` (:239), `expand_qq_template` (:268).
- `src/process_form/macro_clause.rs:67` — the pre-existing (now redundant/idempotent)
  caller, retained.
- `crates/cranelisp-frontend/src/lib.rs:48` — currency fix (§5).
- `src/expander.rs:715–829` — int's `expand_scoped` (the quote-shield seam, §7).
- `design/arch/fixmes/0613-quasiquote-not-desugared-outside-macro-clauses.md` —
  the defect record.
- SPRINT.md §"Architecture review (Phase 2)" §3 — the `/arch` ruling (fold point,
  int shield, ordering constraint).
