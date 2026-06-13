---
number: 0329
target: /spec
filed_by: /dev (int)
filed_at: 2026-06-13
sprint_filed: 81
refers_to: design/arch/bounded-contexts.md §1 invariant 9 + §6 "Annotation-pairing is frontend-driven", design/arch/facades/int.md §"cranelisp-frontend" consumed surface, crates/cranelisp-frontend/src/ast_builder.rs (try_consume_annotation, build_one_expr_at, build_args_with_annotations — the annotation-pairing helpers + the non-pairing build_expr/build_list_expr sites), src/worker.rs (build_program_compat — per-sexp build_form/build_expr iteration), spec/03-types.md §3.1, spec/08-modules.md §8.9.1, repl/spec.md §"Output Format", tests/spec_08_modules.rs (bare_primitive_type_int_neg_*, bare_primitive_types_bool_float_string_neg_*)
status: open
---

# `:Type` is an annotation that binds the following form in EVERY position — frontend-owned pairing (the boundary ruling) + the missing top-level / sub-form pairing fix

## BOUNDARY RULED (S81 /arch, user-ratified 2026-06-13) — annotation-pairing is wholly frontend's

The approved fix: **`:Type` is a reader-macro-like type-unifying annotation that binds the
immediately-following form, in EVERY position** (never a standalone atom). `/spec` analysis
confirmed the grammar already makes `annotate_expr` a first-class `expr` and typecheck's
`infer_annotate` is already correct (resolve annotation type, then unify) — the *entire*
defect is that the frontend never builds the `Expr::Annotate` node in the divergent
positions (the single-sexp `build_expr`, the list-head dispatch, and the top-level form
sequence). `/arch` ruled the owning seam:

**ONE OWNING SEAM: THE FRONTEND.** The `:Type`-binds-following-form pairing is a
reading / AST-construction act (the leading `:Type` and the bound form lower together into
one `Expr::Annotate`), so it is frontend-owned wherever it occurs — list-head, sub-form,
AND top-level form sequence. int orchestrates the *sequence of forms*; the frontend decides
*what a form is*, and a `:Type`-prefixed pair is one form. Splitting the pairing across two
crates (pairing helper in frontend, top-level driving in int's per-sexp `build_program_compat`)
is exactly the half-implemented state this defect exposed — forbidden by Principle 7 (single
source of truth) and Principle 1 (decoupling over convenience). Canonical ruling:
`design/arch/bounded-contexts.md` §1 invariant 9 (+ §6 "Annotation-pairing is frontend-driven"
+ `facades/int.md` consumed-frontend line).

**Frontend API shape.** A new additive frontend boundary entry — a **form-sequence builder**
(e.g. `build_forms(sexps: &[Sexp]) -> Result<…, CranelispError>` and/or the bare-expression
`TopLevel::Expr` sibling int's `build_program_compat` needs) that lifts `build_one_expr_at`
to the top-level sequence: pair a leading `:Type` sexp with the following form into
`Expr::Annotate`, otherwise delegate per-sexp to `build_form`/`build_expr`. Also extend the
sub-form sites (`build_expr` single-sexp, `build_list_expr` head) so the SAME pairing helper
applies at every expression-building site, not just the comma-style argument sequences. A
bare leading `:Type` with nothing to bind is a parse error (`annotation missing expression`),
not a `Var`. The exact signature is `/dev`-on-frontend's to land in the lib.rs `///` rustdoc
+ regenerate `crates/cranelisp-frontend/public-api.txt` (two-update discipline). Baseline
impact: **one additive public free function** — no removal, no `cranelisp-types` change.

**What int becomes.** `src/worker.rs::build_program_compat`'s per-sexp `build_expr` driving
(for the bare-expression branch) is replaced by a call to the new frontend form-sequence
builder. int does NOT re-implement `try_consume_annotation`/`build_one_expr_at`; the only int
change is the call-site swap (and `is_top_level_form` / the per-sexp loop stop treating a bare
leading `:Type` as its own `TopLevel::Expr`). No new int boundary type; no `cranelisp-types`
change.

**No `cranelisp-types` / public-API impact** beyond the single new frontend entry (frontend
`public-api.txt` baseline gains one line; regenerate in the implementing change-set).

## RE-TARGET HISTORY (S81 bite-1 /dev-on-typecheck investigation, 2026-06-13)

Originally filed `target: /typecheck` on the hypothesis that bare `:Int` over-resolves
via a residual `primitives`-keyed shortcut in the type-name chokepoint. **That hypothesis
is FALSE.** Investigation (below) showed typecheck's type-resolution path already enforces
the §3.1/§8.9.1 reachability discipline correctly. Then re-targeted to `/spec` as an open
behaviour question; `/spec` has since ruled (position 1 above — `:Type` binds the following
form in every position). The boundary is now decided; this FIXME is the implementation
tracker for the ratified fix. The 2 tests stay failing-not-ignored until the fix lands.

## Investigation finding (evidence)

### Typecheck's type-name resolution is ALREADY correct

When `:Int` is a GENUINE type annotation (fn param — where the frontend pairs `:Type expr`
into `Expr::Annotate` via `build_one_expr_at`), typecheck rejects it without prelude and
accepts the FQ form, exactly per §3.1/§8.9.1:

```
$ printf '(defn f [:Int x] x)\n' | cranelisp        # no prelude, no import
Error: type error: unknown type `Int` (from module ``)       # CORRECT — bare rejected

$ printf '(defn g [:primitives/Int x] x)\n' | cranelisp
:(Fn [primitives/Int] primitives/Int) user/g ; defn          # CORRECT — FQ works
```

`resolve_type_expr_in_module` (`checker.rs` ~2093) roots at `module_path`, falls back to
`prelude` ONLY when the `PreludeFallback` bit is ON, and public-filters the prelude
terminal. With `PreludeVariant::None` the bit is OFF → bare `:Int` is unreachable → the
`unknown type Int` error the spec requires. No `primitives`-keyed shortcut exists. There is
nothing for typecheck to fix.

### The failing tests use TOP-LEVEL `:Int 42`, which never forms an annotation

`:Int 42` typed at the REPL (or as a `--run` file) is parsed by `cranelisp_frontend::parse`
into TWO top-level sexps — `Symbol(":Int")` and `Int(42)` — each processed independently by
`build_form` (`src/worker.rs::build_program_compat` iterates per-sexp). The `:Type expr`
annotation pairing (`try_consume_annotation` + `build_one_expr_at`) fires only inside a LIST
context (fn args / body), never across top-level forms. So at top level:

```
$ printf ':Int 42\n'   | cranelisp   # REPL, no prelude  → :primitives/Int 42 (value 42's type; :Int form's result discarded/last-wins)
$ printf ':Foo 1\n'    | cranelisp   # REPL              → :primitives/Int 1   (unknown Foo SILENTLY ignored — proves :Foo is not resolved as a type)
$ printf ':Int 42\n'   | cranelisp --run prog.cl         → error: undefined variable: :Int   (the :Int sexp builds as Expr::Var ":Int")
$ printf '(defn f [] (:Int 42))\n' | cranelisp           → error: undefined variable: :Int   (inside parens, head position → Apply callee ":Int")
```

The REPL display `:primitives/Int 42` is the **output format** (`repl/spec.md` §Output) for
the last form's VALUE (`42`), with the `:Int` token dropped/last-wins — NOT a resolution of
the type `Int`. The `:Foo 1 → :primitives/Int 1` case is the smoking gun: a genuinely-unknown
type name produces no error and the value-type is shown, proving the leading `:Name` is not
being resolved as a type at top level at all.

## Resolution (RULED — position 1 chosen)

**Top-level `:Int 42` parses as `Annotate{Int, 42}`** — consistent with the in-list pairing,
and `:Type` binds the following form in EVERY position. Bare `:Int` without prelude then
correctly errors `unknown type Int` (typecheck's already-correct resolution fires once the
node exists), and the 2 negatives pass. This also affects the POSITIVE REPL display path
(`:Int 42` with prelude shows the annotated/unified type). The §3.1/§8.9.1 reachability RULE
was never in question; it just needed the `Expr::Annotate` node to exist at top level / sub-form
positions for it to bite. (Rejected position 2 — "top-level `:Type value` is NOT an annotation"
— would have left a position-dependent surface inconsistency and mis-specified the 2 negatives.)

## Implementing skills + sequence

1. **`/spec`** — finalize the normative wording (`:Type` binds the immediately-following form
   in every position, never a standalone atom; the top-level / sub-form positions are
   annotations identical to in-list ones). Annotate `spec/03-types.md §3.1` / `spec/08-modules.md
   §8.9.1` / `repl/spec.md §"Output Format"` rows. *(`/spec` has substantively ruled; this step
   is the spec-text codification + traceability.)*
2. **`/dev`-on-frontend** — add the form-sequence builder (the new additive public entry) +
   extend `build_expr`/`build_list_expr` so the SAME annotation-pairing helper applies at every
   expression-building site; bare-leading-`:Type`-with-nothing-to-bind is a parse error.
   Regenerate `crates/cranelisp-frontend/public-api.txt` (one added line); update the lib.rs
   `///` + `//!` rustdoc (two-update discipline). Unit-test the pairing per position.
3. **`/dev`-on-int** — rework `src/worker.rs::build_program_compat` to call the frontend
   form-sequence builder for the bare-expression branch; stop treating a bare leading `:Type`
   as its own `TopLevel::Expr`. Call-site swap only; no int boundary-type change.
4. **`/qa`** — un-ignore / confirm the 2 negatives pass (`bare_primitive_type_int_neg_*`,
   `bare_primitive_types_bool_float_string_neg_*`); add positive coverage for top-level
   `:Type value` annotation behaviour (with prelude → unified type display) and for the
   sub-form pairing fix. The FQ positives already pass.

FIXME 0329 **closes when the fix lands** (do not delete until then) — it is the durable record
+ the regression guard while the 2 tests stay failing-not-ignored.

## Operational implication / Context

- NOT a typecheck defect — typecheck's type-resolution chokepoint
  (`resolve_type_expr_in_module`) already honours the prelude-fallback/import scoping for
  type names (sibling-correct with the value chokepoints). The S81 `resolve_with_fallback`
  migration did NOT cause this; bare type-annotation resolution is on a separate closure path
  that was already correct.
- 2 tests (`bare_primitive_type_int_neg_unknown_type_without_import`,
  `bare_primitive_types_bool_float_string_neg_unknown_without_import`) remain
  failing-not-ignored as the durable record until /spec rules + the owning skill actions.
- The complementary FQ positives (`fq_primitive_type_int_works_without_import`,
  `fq_primitive_type_int_neg_no_unknown_type_error`) PASS — consistent with the finding (FQ
  `:primitives/Int 42` displays `:primitives/Int 42` either way).
</content>
</invoke>
