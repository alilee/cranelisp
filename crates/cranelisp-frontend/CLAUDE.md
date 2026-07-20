# cranelisp-frontend — local conventions

The voice of the code: API gotchas, invariants, and known asymmetries for the
reader, AST builder, module-decl extraction, quasiquote/quote desugaring,
defmacro shape-recognition, and preamble capture. Owned by `/dev` when
narrow-deployed here. Direction/target shape lives in `design/frontend/`; the
public surface is `lib.rs` rustdoc + `public-api.txt` — neither duplicated here.

The frontend is **purely syntactic** (post-S76 W-Macro): text → `Sexp` →
`TypeExpr`/`Expr`/`ParsedEntry`. It names no `Type`, no backend crate, and does
**no macro recognition or execution** — only quasiquote desugaring (`lib.rs` BC
invariants 1–2).

## Submodule seam map (+ where each `#[cfg(test)]` lives)

| Submodule | Concern | Tests live in |
|---|---|---|
| `reader.rs` | source text → `Vec<Sexp>` (hand-written recursive-descent) | `reader/tests.rs` |
| `ast_builder.rs` | `Sexp` → `Expr` / `ParsedEntry` / `TypeExpr`; per-form + form-sequence | `ast_builder/tests.rs` |
| `module_extract.rs` | peel `mod`/`import`/`export`/`platform` decls | `module_extract/tests.rs` |
| `quasiquote.rs` | `` ` ``/`~`/`~@`/`quote` → `macros/`-qualified ctor Sexps | `quasiquote/tests.rs` |
| `defmacro.rs` | defmacro shape-parse + per-clause defn synthesis | `defmacro/tests.rs` |
| `preamble.rs` | leading `;;` block capture (spec §8.16) | **inline** `mod tests` |

**Asymmetry**: `preamble.rs` keeps its tests inline; every other submodule uses a
sibling `{module}/tests.rs` file. Match the sibling convention for new submodules.

## Reader token disambiguation (spec §1.7) — `read_form` dispatch order is load-bearing

`read_form` (`reader.rs`) dispatches by first byte in a fixed precedence: float
before int (capture the decimal point), int/number before operator (so `-3`, `+3`
are numbers), boolean before symbol (`true`/`false` only at a symbol boundary).
Reorder these and literals mis-tokenize.

- **Interior operator absorption** (`is_interior_operator_char` = `+ * = < >`,
  and NOT `/` or `.`): a run of these chars is absorbed into a symbol token ONLY
  when immediately followed by another symbol char (`char->digit`, `lt<=fb`) —
  see `consume_symbol_chars` + the `interior_operator_run_then_symbol` lookahead.
  A *trailing* run is left for the operator reader (`->` standalone, `a <= b`).
  `/` and `.` are excluded because they are structurally significant (module
  qualifier / dotted member) and must not be silently swallowed.
- **`-`/`+` are number-or-operator** (`read_minus_or_number` / `read_plus_or_operator`):
  followed by a digit → number, else operator symbol. An operator symbol
  immediately followed by a digit is a hard error (spec §1.4.2).
- **`:`-prefix** (`read_colon_prefix`): `:Name`, `:mod/Name`, `:a.b/Name` read as
  ONE `Sexp::Symbol(":Name")`; bare `:` and `:(...)` read as `Sexp::Symbol(":")`
  (the AST builder pairs the following compound form). The `/`-split guard
  requires BOTH halves non-empty so a bare `/` division operator stays a bare
  name (Principle 16; FIXME 0328/0331 — the split itself lives in
  `cranelisp-types::resolve`, `/arch`-owned).
- Reader macros desugar at read time: `'x`→`(quote x)`, `` `x ``→`(quasiquote x)`,
  `~x`→`(unquote x)`, `~@x`→`(unquote-splicing x)`, `#(...)`→`(anon-fn (...))`.
  `%n`/`$name`/`&name`/`name#` produce plain symbols the AST builder later gates.

## `:Type` binds the FOLLOWING form, everywhere (BC invariant 9; spec §1.4.5/§2.3.8)

A `colon_prefix` token is an **annotation introducer, never a `Var`**. In
expression position `build_expr` errors `annotation missing expression` on a bare
`:Type` (`ast_builder.rs` ~L1131). The pairing is single-sourced through
`build_one_expr_at` + `try_consume_annotation`, called at EVERY position that can
carry an annotated operand: call head + args (`build_apply`), vec literals, `let`
values, `match` scrutinee (FIXME 0389 — grouping the scrutinee into one
`Expr::Annotate` is what keeps a positional arity guard honest), params, fields,
and the top-level form sequence (`build_forms`). When you add a new operand
position, route it through `build_one_expr_at` — a raw `build_expr` there silently
drops annotation support.

- **Stacked annotation runs** (`:Eq :Display a`) can only be trait bounds, so
  `annotation_run_carrier` (FIXME 0341/0346) folds a run of length >1 into
  `TypeExpr::Bounds([TraitRef..])`; a run of length 1 is left as the resolved
  `TypeExpr` for typecheck's try-type-then-trait disambiguation (spec §3.9.3).

## Qualified-name splitting (§8.5) — split at the LAST `/`, guard both halves

`type_ref_from_name` and `trait_ref_from_name` (`ast_builder.rs`) split a written
`module/Name` onto `Some(module)` only when both halves are non-empty; otherwise
`module: None`. Stuffing a whole slash-name into the bare-name slot re-roots it
under the current module (the **D-qual** defect class, S91). Every impl
trait-name / target / constraint / applied-head position routes through the
splitter (`build_impl_target`). See RED defects below.

`reject_qualified_binder_head` is the **dual** of these splitters: a reference
splits `module/Name` and reaches across modules; a declaration binder MUST be
bare, so a qualified spelling rejects (spec §5 binder-positions table, S113). It
uses the SAME both-halves-non-empty predicate — a bare `/` (division operator)
splits to empty halves and is NOT qualified (Principle 16).

**Landed binder-reject sites** (all see raw pre-int source, so the reject is
sound): the §5 native heads (defn / deftype-both-arms / deftrait-caller /
defmacro / method-sig / con_var); `deftype` **constructor names** (both arms) and
**field names** (both arms); `defmacro` **params** (`parse_param_items` +
`parse_bracket_pattern`); the `import`/`export` **module alias**
(`module_extract`). `mod`/`mod-` and `platform` names enforce their own
simple-symbol rule (reject `/` AND `.`) at `module_extract.rs` (spec §5.8/§5.10 —
module-phase decls).

**DEFERRED — value-level local binders** (`defn`/`fn` params, `let` names,
`match` var-patterns): the reject is NOT applied at their `build_form` seams
(`build_annotated_params`, `build_let_bindings`, `build_pattern` — see the NOTEs
there). Those seams run AFTER int's macro-expansion name-resolution, which itself
(mis-)qualifies a local binder whose name collides with an importable symbol
(`name` → `primitives/name`, only with a macro in scope). A build-layer reject
there fires on int's mangled output and breaks a VALID program
(`(defn f [name] (str … name))`). Enforcement is owed at the reader/raw layer or
via the paired int fix — **FIXME 0670** (`target: /arch`). Do not re-add a reject
at these three seams without that fix.

`type_expr_to_trait_ref` (the stacked-bounds `:Eq :Display a` reshaper) **does
NOT re-split** — it trusts the upstream split and only reshapes `TypeRef`→
`TraitRef`. Every name reaching it is already module-split (`Named`/`Applied`
names via `type_ref_from_name`; `parse_annotation_name` never mints a
slash-carrying `TypeVar` since FIXME 0589). A `debug_assert` enforces the
**splitter dual** — no *splittable* qualified spelling (two non-empty halves)
survives (a degenerate `foo/` is legitimately passed through, Principle 16). Its
former hand-rolled `rsplit_once` was downstream compensation for 0589's
slash-`TypeVar` and was retired at S113 (P7).

**Invariant: a `TypeVar` never carries a qualified (`module/name`) spelling**
(Principle 18, FIXME 0589), enforced at EVERY point where type-var-ness is
decided — a qualified-lowercase name (`mod/x`) is NOT a bare type var (spec §3.3)
and routes to `Named(type_ref_from_name(…))`, or (in a binder slot) rejects. The
decision points, each carrying its own routing/reject: `parse_annotation_name`
(simple `:name` annotations → Named), `build_type_expr` (compound type-expression
positions — `(Fn […])`/`(Option a)` args, return types → Named), and
`build_impl_target` (impl-target type args → Named; the `:Constraint var` arm
rejects a qualified constrained var as a binder, like con_var §3.1). The S109
typecheck mint guard (`!contains('/')`) stays as the downstream backstop; these
frontend legs make the routing correct where the decision is made. When you add a
new type-var/type-arg decision point, it enforces this same invariant — do not
re-list a count here, honor the invariant.

## Known open defects (RED guards — the test is the record, no FIXME file)

- **Trailing junk after a valid ctor field bracket is silently dropped.**
  `build_constructor_def` (`ast_builder.rs` ~L604) rejects a trailing *non-bracket*
  non-docstring form (S107 item 1), but `(deftype Box (Box [:Int n] extra))` still
  silently drops `extra`. Guard: `tests/spec_05_definitions.rs::
  deftype_ctor_trailing_form_after_field_bracket_rejected_neg` (RED, `// FIXME(/frontend)`).

## Intentional NYI gates in `build_expr` — not bugs

`reject_non_ring0_symbol` + `build_list_expr` reject `%param`, `$gensym`,
`&rest`, trailing-`#`, `anon-fn` (`#(...)`), and `par-let` with "not yet
supported (Ring N)" messages. These are deliberate gates on reader-accepted
syntax, not defects. `quote`/`quasiquote`/`unquote` reaching `build_list_expr`
is an error ("should have been expanded") — they must be desugared upstream.

## `reject_reserved_binder_name` — `trace` only, binder positions only

`RESERVED_BINDER_NAMES = ["trace"]` (`ast_builder.rs`). `trace` is a root special
form; it is rejected in binder/definition slots (defn/let/params/patterns/defmacro
names) but is legal in head/reference position `(trace expr)`. The set is
deliberately not widened (Principle 6) — other special forms can't reach a bound
name because the parser dispatches them in head position. Single-sourced across
all binder sites.

## Synthetic spans: one global atomic (BC invariant 4)

`quasiquote::SYNTHETIC_SPAN_COUNTER` (`AtomicU32`, starts at `1_000_000` above any
realistic source offset) is the ONE source of synthetic spans; `defmacro::next_span`
delegates to `quasiquote::next_synthetic_span`. `make_gensym_name` also draws from
it (`x#` → `x__auto_NNNN`). Never mint a second counter — uniqueness across a
session is the invariant. Auto-gensym in templates only fires at depth 0.

## Caller contracts (enforced with diagnostics, not silent)

- `build_form` rejects `begin` (flatten via `flatten_begin` first),
  `mod`/`import`/`export`/`platform` (peel via `extract_module_declarations`
  first), and returns `Vec<ParsedEntry>` because `deftype` yields a `TypeDef` plus
  one `Constructor` per variant (source order). Macros must be expanded first —
  an unexpanded macro call becomes a silent `Expr::Apply` and fails later.
- `build_forms` is the top-level `:Type`-pairing seam; it DROPS `ParsedEntry::Macro`
  and `::Constructor` (handled by the macro pipeline / ADT synthesis, not the
  `TopLevel` dispatch). A trailing `:Type` with nothing to bind is a parse error.
- `extract_module_declarations` requires `containing_module`: it rewrites `super`
  to the parent path (spec §8.3.7) so `ImportSpec.module_path` NEVER carries the
  literal `"super"` past the boundary (BC invariant 3). `super` in a root module
  is a compile-time error.

## deftype field desugaring

`build_field_list` stores a bare (unannotated) field name as
`TypeExpr::TypeVar("")` — the empty string is the "assign me a fresh var"
sentinel. `desugar_type_def` then maps each unique bare field to a sequential
letter (`a`, `b`, … via `sequential_type_var`), consistent across constructors,
and infers `type_params` only when none were declared on the head.

## Debugging

Everything here is a pure function (`&str`/`&Sexp` in, value out) — unit-testable
with no session (Principle 5). No frontend-specific env/trace flags exist; codegen
traces are the backend's. Render an offending `Sexp` in a diagnostic via
`Sexp::format_flat()`, never `{:?}` (the 0500 rendered-diagnostic class — `{:?}`
leaks `Span { .. }` dumps into user text). REPL `/expand` exercises quasiquote.
