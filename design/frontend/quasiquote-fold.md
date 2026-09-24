# Quasiquote/Quote Desugaring and the AST-Entry Fold

Interior design for `crates/cranelisp-frontend/src/quasiquote.rs` and its fold
into the AST chokepoints. Spec: `spec/09-macros.md` §9.4.

Quote and quasiquote are legal **wherever an expression is legal** — a template
in an ordinary `defn` body or at top level is as valid as one in a `defmacro`
clause (user ruling, S111; spec §9.4.1 makes quasiquote reader-level sugar with
no macro-body restriction). Desugaring is therefore a property of every form, not
of one call site, and the design's whole job is to make that structural rather
than remembered.

## 1. The fold point

Desugaring folds into the two AST-entry chokepoints as their first step, so **no
caller can forget it** (Principle 7, Principle 18):

| Chokepoint | Production callers |
|---|---|
| `build_forms(sexps)` | int's universal build path — REPL, `--run`, `--link`, cluster processing, agent, index worker, save-regen |
| `build_form(sexp)` | int's persisted-source re-parse of a single top-level form |

`build_expr` has **no** production direct caller: it is the internal
expression-recursion primitive and the bare-expression branch of `build_forms`.
It does not fold. Folding there would re-walk each subtree once per level of
nesting; instead it trusts its input and keeps the backstop (§3) as the
structural guard.

### 1.1 Placement within each chokepoint

Both chokepoints desugar the **whole** tree they receive before any head-shape
dispatch or `:Type` pairing.

- `build_forms` maps the desugar over the input slice once, up front, then runs
  the pairing and dispatch loop over the desugared vector. `expand_quasiquotes`
  preserves structure — each slice element maps to exactly one element, and an
  `Sexp::Annotated` remains one node — so desugar-then-pair is order-safe and BC
  §1 invariant 9 is unaffected.
- `build_form` desugars its one form, then dispatches.

The public `build_form` is the desugar composed with a private
`build_form_inner` that assumes desugared input; `build_forms`' internal dispatch
calls the inner function, because it has already desugared the slice. That keeps
exactly one pass per form. Calling the public entry from the loop would also be
*correct* by idempotence, at the cost of one extra tree walk per top-level form.

## 2. Idempotence — the transform is a fixpoint

For every `Sexp s`, `expand_quasiquotes(expand_quasiquotes(s))` is structurally
identical to `expand_quasiquotes(s)`, **including spans and minted gensyms**. One
pass reaches the fixpoint: no quote-family head symbol in operator position
survives it.

Four facts hold it up, and each is worth an assertion:

1. The transform rewrites exactly the arity-2 list forms whose head symbol is
   `quote` or `quasiquote`, and structurally rebuilds every other node by
   recursing into its children.
2. Output heads are `macros/SexpSym`, `macros/SexpList`, `macros/SCons`,
   `sconcat` and their siblings — none of which is a quote head. A quoted
   occurrence of the *word* becomes a string: `'quote` → `(macros/SexpSym "quote")`,
   where the token now sits inside a `Sexp::Str` and can never again be a head
   symbol.
3. Auto-gensym (`x#`) and synthetic spans are minted **only** while rewriting a
   template. A second pass finds no template, mints nothing, and returns a
   bit-identical tree. This is what makes the fixpoint hold including spans
   rather than merely up to structure.
4. `unquote` and `unquote-splicing` are meaningful only inside a template. A
   depth-0 `(unquote e)` splices `e` verbatim and the walk then recurses into the
   result, so a template nested inside an unquote is desugared in the same pass.

The practical consequence: int's macro-clause synthesis path already calls
`expand_quasiquotes` on the tree it hand-builds, and the fold desugars it again.
That second pass is a structural no-op. The explicit call is retained
deliberately — it documents intent at the one site that constructs a
compiler-generated `Sexp` — and idempotence is precisely what makes keeping it
safe.

## 3. Backstop — a surviving quote head is a bug

`build_list_expr` rejects a surviving `quote`/`quasiquote`/`unquote`/
`unquote-splicing` head. The rejection **stays**, as the structural enforcement
that the fold ran. Post-fold its two cases mean different things:

- A surviving **`quote` or `quasiquote`** head is always a compiler bug: these are
  desugared wherever they appear, so arrival means a new form-entry chokepoint
  was added that bypassed the fold. The backstop converts a silent mis-lowering
  into a loud diagnostic at exactly the seam that assumed desugaring.
- A surviving **`unquote` or `unquote-splicing`** head may also be a genuine user
  error — `~x` written outside any template. The transform leaves such forms
  untouched, so rejecting them is correct.

The backstop is a fence, not a feature gate. It is not removed or weakened.

## 4. The family is covered uniformly

The reader lowers the sigils at read time (`'x` → `(quote x)`, `` `x `` →
`(quasiquote x)`, `~x` → `(unquote x)`, `~@x` → `(unquote-splicing x)`), so all
four reach the fold as list forms. One walk covers the family: `quote` routes to
pure structural quotation; `quasiquote` routes to the depth-tracked template
expansion, which resolves unquotes at depth 0 and re-quotes them structurally at
greater depth; standalone unquotes fall through to §3.

### 4.1 One classifier decides membership

Membership is decided once, by `cranelisp_types::quote_head`
(`design/arch/interfaces.md` §"Reader-quote structural predicate"). The frontend
carries **no** local notion of what a quote is; the four crate-private predicates
it once had are gone, and re-creating an `is_quote`/`is_quasiquote` helper here is
a review reject. Int's two scope-aware shields consume the same function, so the
fold and the shields cannot disagree about which subtree is data — the divergence
that would double-desugar or mis-qualify a quoted subtree is unrepresentable
rather than merely tested for.

**The exactness is a condition on the classifier, not an assumption about it.**
The classifier recognises a bare-symbol head with full string equality and
exactly two children, so a qualified spelling such as `macros/quote` is not a
quote head. If `cranelisp-types` ever widened recognition — a qualified head, a
suffix match, another arity — the fold would silently change meaning. That is the
standing falsifier, and it is why the unit tier keeps the equivalence pins.

Four sites consume the classifier, and two of them carry **negative** facts a
careless rewrite loses:

| Site | Decision | Must preserve |
|---|---|---|
| `expand_quasiquotes` list arm | `Quasiquote` → template expansion; `Quote` → structural quotation | `Unquote` and `UnquoteSplicing` **fall through to ordinary child recursion**; §3, not this arm, reports them |
| `expand_qq_list`, `macros/SexpList` branch | `Unquote` → depth-0 splice / depth-n re-quote; `UnquoteSplicing` → depth-0 error / depth-n re-quote; `Quasiquote` → depth increment | `Quote` is **not** tested here and must not become tested: a `(quote …)` inside a template is re-quoted structurally like any other list |
| `expand_qq_children` splice detection | `UnquoteSplicing` at depth 0 | the depth-0 guard stays outside the classifier |
| `expand_qq_spliced` segment loop | `UnquoteSplicing` at depth 0 | same |

The bracket branch keeps its own guard: special heads are recognised only under
`macros/SexpList`, because a bracket cannot carry one. That is a *position* rule
and stays in the fold; the classifier answers only "what head is this".

`QuoteHead` is a closed sum so that a new quote head fails to compile at every
walker. The frontend matches on it **without a `_` arm**: each site names all four
variants and `None`, grouping the ones it treats alike so the grouping is a
visible decision rather than an accident. A wildcard arm forfeits the point of the
closed sum.

## 5. The pipeline chain

```
reader (' ` ~ ~@ → (quote …)/(quasiquote …)/(unquote …)/(unquote-splicing …))
  → int Pass-1 macro expansion  [quote-shielded, §6]
  → build_forms / build_form  ── DESUGAR FOLD (§1) ──┐
       ├─ :Type pairing (BC §1 invariant 9)          │ one fixpoint pass
       ├─ build_form_inner  (top-level forms)        │ over the whole tree
       └─ build_expr        (bare exprs; §3 guards)  ┘
```

Desugar runs **after** macro expansion and **before** per-form build. That
ordering is load-bearing for §6.

## 6. The paired seam — int's quote shield

The frontend's side of the contract: it desugars the quote family **exactly once,
at the `build_forms`/`build_form` boundary, over the fully-macro-expanded tree**.
It does **not** desugar before macro expansion, so **macros receive raw
`(quote …)`/`(quasiquote …)` argument sexps** — the conservative semantics, where
a macro sees the sexp the user wrote. Desugaring before expansion would change
macro-argument representation observably.

The complementary obligation is int's and is named here, not designed here:
Pass-1 macro expansion must not rewrite the interior of quoted literals. It holds
`quote` subtrees verbatim and, within `quasiquote`, descends only into unquote
bodies — the ordinary expression positions where a macro call *should* expand —
tracking nesting depth so a nested quasiquote stays shielded. Without the shield,
a macro-call-shaped list inside quoted data would be expanded as code: silent data
corruption. `design/int/int.md` owns it.

Both halves recognise the family through the one classifier (§4.1), so "shield
and fold stay in lockstep" is a property of the code rather than a discipline.

## 7. Testability

The fold is unit-testable at the frontend boundary with no session, and four
classes of assertion discriminate different failures:

- **Positive** — a template in an ordinary `defn` body and at top level builds to
  the `macros/`-constructor AST, for each of the four family members.
- **Idempotence** — a second desugar is bit-identical for representative inputs
  including `'quote`, `` `(m ~x) `` and nested templates, asserting span and
  gensym stability (§2).
- **Backstop** — a hand-built surviving `(unquote x)` outside any template still
  errors at `build_expr`, and a raw `(quote x)` fed to `build_expr` directly still
  hits the backstop, because `build_expr` does not fold.
- **Classifier equivalence** — the two negative facts of §4.1 get their own pins,
  because a passing suite does not discriminate them: a `(quote …)` inside a
  template is re-quoted structurally rather than routed to structural quotation,
  and a standalone unquote still reaches the backstop. A wrong-arity control
  (`(quote a b)`) and a qualified-head control (`(macros/quote x)`) must both
  remain ordinary lists.

## Cross-references

- `spec/09-macros.md` §9.4 — quasiquote semantics and the expansion rules.
- `design/arch/interfaces.md` §"Reader-quote structural predicate" — the `QuoteHead`/`quote_head` contract.
- [Pass-1 quote shield](../int/int.md#66-pass-1-quote-shield) — the paired int-side obligation.
- `design/frontend/defmacro-synthesis.md` — the sibling synthetic surface.
