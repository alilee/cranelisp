# Frontend — Master Design

> Interior design for `crates/cranelisp-frontend/`. Owned by `design`, narrow-deployed to this surface.
>
> **Contract sources** (canonical, normative — this document does not restate them):
> - `design/arch/bounded-contexts.md` §1 — the Frontend bounded context and its invariants 1–10.
> - `crates/cranelisp-frontend/src/lib.rs` `//!` preamble and per-item rustdoc — the public surface. There is no separate facade document.
> - `crates/cranelisp-frontend/public-api.txt` — the as-built enumeration, gated at PR time.
>
> This document states HOW the crate fulfills that contract.

---

## 1. What the frontend is

The frontend is **purely syntactic**: source bytes → `Sexp` → AST. It owns three
operations and nothing else.

1. **Read** — source bytes → `Vec<Sexp>`, with an optional comment-preserving
   mode and the leading-comment-block preamble capture (`reader.rs`,
   `preamble.rs`).
2. **Quasiquote desugar** — `` ` `` / `~` / `~@` / `(quote …)` → `macros/`-qualified
   constructor applications (`quasiquote.rs`). Pure `Sexp → Sexp`, no execution.
3. **Build** — desugared `Sexp` → `ParsedEntry` / `Expr` / `TypeExpr`
   (`ast_builder.rs`), plus module-identity normalisation with `super` resolution
   (`module_extract.rs`).

It performs **no macro recognition and no macro execution** (BC §1 invariant 2).
Recognition is the `cranelisp_types::resolve_macro_head` primitive, driven by
typecheck's within-form descent and int's Pass-1 loop; execution is int's, behind
the `cranelisp_types::MacroExpander` callback. Quasiquote desugaring is the
entirety of the frontend's remaining macro-adjacent role, and it is syntactic.

The frontend is the only crate that touches raw source bytes, names no `Type`,
`Scheme` or `TypeId`, and depends only on `cranelisp-types` (Principle 3 —
dependency flows toward stability). Everything crossing the boundary is passed by
value; the sole `&` parameter on the surface is a read-only slice.

Because the crate is stateless apart from one atomic counter, every public
function is callable in isolation from a source string with no session — the
structural testability the REPL's `/expand`, `/sexp` and `/source` depend on
(Principle 5).

---

## 2. Public surface

The crate-root `//!` preamble is the canonical statement of the surface; the
table below records only where each item lives and which interior design covers
it.

| Surface item | Home | Interior design |
|---|---|---|
| `parse`, `parse_preserving_comments` | `lib.rs` → `reader.rs` | `reader.md` |
| `capture_module_preamble` | `preamble.rs` | `module-preamble.md` |
| `extract_module_declarations` → `ExtractedDeclarations` | `module_extract.rs` | `modules.md` |
| `build_form`, `build_forms`, `build_expr` | `ast_builder.rs` | `ast-builder.md` |
| `parse_type_expr` | `ast_builder.rs` | `ast-builder.md` §4 |
| `parse_defmacro`, `synthesize_macro_clause_defn`, `is_defmacro`, `is_begin`, `flatten_begin` | `defmacro.rs` | `defmacro-synthesis.md` |
| `expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span` | `quasiquote.rs` | `quasiquote-fold.md` |

`build_form` and `build_expr` are **mode-agnostic**: they take no
`CodegenBehaviour` and behave identically under REPL, `--run` and `--link`. A
mode-conditional rejection at the build layer would be a defect; `--link`'s
`(trace …)` refusal is the linker's natural missing-symbol detection.

The frontend originates no public type of its own. `ExtractedDeclarations` is its
one public DTO — structural sugar over `cranelisp-types` items, `#[non_exhaustive]`
so a new declaration category is additive. Nothing from `cranelisp-types` is
re-exported here; consumers import it directly (Principle 15).

### 2.1 Interior modules

| File | LOC | Responsibility |
|---|---|---|
| `lib.rs` | 397 | Public re-exports, the `parse` wrappers, and the surface narrative |
| `reader.rs` | 1059 | Hand-written recursive descent: bytes → `Vec<Sexp>`, spans, comment mode |
| `ast_builder.rs` | 2396 | `Sexp` → AST: head classification, form lowering, type expressions, patterns, traits and impls |
| `module_extract.rs` | 497 | Peels `mod`/`mod-`/`import`/`export`/`platform`; resolves `super` |
| `defmacro.rs` | 624 | `defmacro` shape parse → `DefmacroInfo`; per-clause `Defn` synthesis |
| `quasiquote.rs` | 424 | Quote-family desugaring; the monotonic synthetic-span counter |
| `preamble.rs` | 269 | Leading `;;` comment-block capture (spec §8.16) |
| `synth.rs` | 130 | `pub(crate)` synthetic-`Sexp` primitives shared by `quasiquote` and `defmacro` |

Counts verified at S122; the sibling `{module}/tests.rs` files are excluded.

`synth` is the single synthetic-`Sexp` construction kit: both `quasiquote` and
`defmacro` compose their module-specific shapes on top of its primitives rather
than re-deriving the `Sexp` + span pattern, so a change to how a synthetic form
is spanned is one edit (Principle 7). Every primitive draws from the one counter
behind `next_synthetic_span`, which is what makes BC §1 invariant 4 (synthetic
spans are unique) hold across threads.

### 2.2 The defmacro helper family is permanently public

`parse_defmacro`, `synthesize_macro_clause_defn`, `is_defmacro`, `is_begin` and
`flatten_begin` are internal-but-exposed: public at the crate root, not part of
the form-by-form boundary, and consumed directly by int's macro pipeline. They
stand on those consumers. **There is no "narrow back to `pub(crate)`"** — the
event the older rustdoc conditioned that on was the migration of `expand` into
this crate, and S76 deleted `expand` rather than migrating it, so the condition
can never occur.

---

## 3. Form classification and dispatch

The form-by-form scheduler (Decision 30) processes one source form at a time. The
frontend's contribution to each unit of source is:

1. **`parse` runs once per source unit** (a file load or one REPL submission),
   returning a flat, source-ordered `Vec<Sexp>`.
2. **`extract_module_declarations` runs once immediately after**, peeling the
   structural declarations, rewriting `super` against the parsing module's path,
   and returning the residual form vector. Structural extraction precedes macro
   expansion (spec §8.12.1), so a macro cannot expand into a `(mod …)` or
   `(import …)` — these are recognised syntactically. `modules.md` states the
   extraction and the append contract.
3. **`build_forms` / `build_form` lower the residual forms**, after int has run
   Pass-1 macro expansion over them. Quasiquote desugaring is the first step
   inside the chokepoints, so no caller can bypass it.

```
reader ── '/`/~/~@ lowered to (quote …)/(quasiquote …)/…
  → int Pass-1 macro expansion (quote-shielded)
  → build_forms / build_form  ── quasiquote desugar fold ──┐
       ├─ :Type pairing (BC §1 invariant 9)                │ one fixpoint pass
       ├─ build_form_inner  (top-level forms)              │ over the whole tree
       └─ build_expr        (bare expressions)             ┘
```

There is **no defmacro pre-pass**: a macro is available only to forms after its
own `defmacro`, in source order (BC §1 invariant 8;
[macro availability rule](../arch/macro-availability-model.md#1-the-rule)).

Four interior judgments elaborate this chain, each in its own document:

- **Annotation and declaration shape** — the read-time `Sexp::Annotated` fold,
  `deftype` explicit parameters and field types, constructor and field
  uniqueness, and the one §7.1 trait-method tail: `s116-syntax-and-annotation.md`.
- **Quasiquote fold** — the chokepoint set, the idempotence contract, the
  surviving-quote-head backstop, and the paired int quote shield:
  `quasiquote-fold.md`.
- **Binder heads** — the one shared reject for a qualified or dotted spelling in
  any binder position: `binder-head-reject.md`.
- **Operand-position and annotation lexing** — the one body seam and the reader's
  dangling-qualifier rejects: `enforcement-matrices.md`.

Two shapes carry their own documents because their grammar is settled
independently: `trait-impl-head-parse.md` (the echo-the-head `impl` slot-1 form)
and `defmacro-synthesis.md` (`defmacro` shape parse and clause synthesis).

---

## 4. Quality attributes

**Simplicity and blast radius.** A hand-written recursive-descent reader is
simpler than a parser library for a grammar this small, and it gives full control
over error messages and span tracking. The crate's one remaining structural
tension is that `ast_builder.rs` is a single ~2,400-line file carrying top-level
dispatch, expression lowering, type expressions, patterns, and trait/impl
lowering. The cost is accretion locality rather than algorithmic complexity —
every new language form lands in the same file — so it is a blast-radius concern,
not a defect. See §6.

**Observability.** The frontend produces error values and never logs. Every
`CranelispError` carries an `ErrorLocation` with `span` populated; parse errors
additionally populate `context` with surrounding lines, so they remain
self-contained after the source string drops. Post-parse errors leave `context`
empty and let the formatter resolve it through introspection (Decision 39). The
crate has no internal tracing surface and does not need one: debugging-time
observability is int's `CRANELISP_CODEGEN_TRACE` plus the REPL slash commands,
whose only requirement of the frontend is that its functions be callable in
isolation and return inspectable data.

**Concurrency.** The frontend has no internal concurrency and no shared mutable
state except the synthetic-span counter, which is a process-monotonic `AtomicU32`
based at 1,000,000 so synthetic spans never collide with real source offsets. All
public functions are pure transforms over owned or borrowed input, so any worker
may call them without synchronisation.

**Performance.** Cost is dominated by the reader's lexing and the AST builder's
tree walk, both linear in source size. Deeply nested quasiquote templates produce
wide synthetic trees with per-node allocation and no pooling, which is acceptable
while the macro footprint stays small. Re-parsing on REPL evaluation is int's
cost, not the frontend's — the frontend lexes once per source unit.

---

## 5. Decision register (frontend-relevant)

**Active.**

| # | Decision | Frontend takeaway |
|---|---|---|
| 30 | Form-by-form scheduler; mutual-import deadlock | The frontend produces no gaps and never blocks, because it is syntactic-only. Macro recognition, execution and the gap-orchestration retry belong to typecheck and int. |

**Legacy — embodied in the architecture.**

| # | Decision | Frontend takeaway |
|---|---|---|
| 1 | 7+1 crate DAG | One crate, depending only on `cranelisp-types` |
| 2 | `cranelisp-types` is data-only | Every AST and `Sexp` type lives there. `ExtractedDeclarations` is the allowed exception — the frontend's own DTO, named for a frontend call rather than a domain concept |
| 6 | `Type::from_name` / `type_name` | The frontend uses `TypeName` (syntactic) and never `Type`; the lift happens in typecheck |
| 21 | Typecheck-sourced call graph on `ModuleEntry` | The frontend extracts `MacroClauseInfo` shapes; it never computes callees |
| 23 | Uniform codegen; two-GOT model | Macro invocation runs through the GOT; the frontend never names `Jit` or `Linker` |
| 32 | `CodeStore` / `LinkerStore` marker traits | The frontend stays C/L-blind |
| 33 | Structural declarations as fields on `SymbolTable` | `extract_module_declarations` returns the bundle int appends directly onto those fields |
| 38 | `SharedState`; per-symbol mutability discipline | The frontend holds no scheduler or session reference |
| 39 | `ErrorLocation`; per-defn source on introspection | Spans are always populated; synthetic spans come from the monotonic allocator |

---

## 6. Potential extension

**Split `ast_builder.rs` by subsystem** into `ast/{top_level,expr,types,patterns,common}.rs`.
The trigger is accretion: every new language form lands in the same file, so the
blast radius of a form addition is the whole builder. The split removes existing
single-file policy concentration rather than budgeting for future complexity, and
it is bounded — the module seams already exist as function groups. It is
implementation work with no interface consequence; nothing in this design depends
on it landing, and no obligation schedules it.

---

## 7. Cross-references

- `design/arch/bounded-contexts.md` §1 — the bounded-context statement and invariants.
- `design/arch/interfaces.md` §"Reader Output" — the `Sexp` carrier, `Sexp::Annotated`, and the `QuoteHead`/`quote_head` classifier.
- `design/arch/macro-availability-model.md`, `design/arch/macro-expansion-ownership.md` — the recognition/execution split the frontend sits outside.
- `design/int/int.md` §6.2 — the cluster orchestration that drives `build_form`/`build_forms`.
- `design/arch/principles.md` — Principles 2, 3, 5, 6, 7, 15, 16, 18.
- `crates/cranelisp-frontend/CLAUDE.md` — the crate-local conventions and seam map (`dev`-owned).
