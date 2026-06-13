---
number: 0329
target: /spec
filed_by: /dev (int)
filed_at: 2026-06-13
sprint_filed: 81
refers_to: crates/cranelisp-frontend/src/ast_builder.rs (try_consume_annotation, build_one_expr_at — top-level annotation pairing), src/worker.rs (build_program_compat — per-sexp build_form iteration), spec/03-types.md §3.1, spec/08-modules.md §8.9.1, repl/spec.md §"Output Format", tests/spec_08_modules.rs (bare_primitive_type_int_neg_*, bare_primitive_types_bool_float_string_neg_*)
status: open
---

# Bare primitive TYPE name at TOP LEVEL (`:Int 42`) is NOT a type annotation — the 0329 negatives test a parsing/REPL behaviour, NOT typecheck type resolution

## RE-TARGET (S81 bite-1 /dev-on-typecheck investigation, 2026-06-13)

Originally filed `target: /typecheck` on the hypothesis that bare `:Int` over-resolves
via a residual `primitives`-keyed shortcut in the type-name chokepoint. **That hypothesis
is FALSE.** Investigation (below) shows typecheck's type-resolution path already enforces
the §3.1/§8.9.1 reachability discipline correctly; the failing tests exercise an int /
frontend TOP-LEVEL form-sequencing behaviour, not typecheck. Re-targeted to `/spec` for a
behaviour ruling; once ruled, the implementation owner is `/dev`-on-frontend (annotation
pairing) and/or `/dev`-on-int (REPL line handling). The 2 tests stay failing-not-ignored.

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

## Open question for /spec

**Should top-level `:Type value` (REPL line or file form) be a type annotation?**

Two coherent positions:

1. **Top-level `:Int 42` SHOULD parse as `Annotate{Int, 42}`** (consistent with the in-list
   pairing). Then bare `:Int` without prelude correctly errors `unknown type Int`, and the 2
   negatives pass. Implementation: `/dev`-on-frontend extends top-level form-building to pair
   a leading `:Type` sexp with the following value sexp (the `build_one_expr_at` shape, lifted
   to the top-level sequence in `src/worker.rs`/`build_form` iteration). This also changes the
   POSITIVE REPL display path (`:Int 42` with prelude would show the annotated/unified type).

2. **Top-level `:Type value` is NOT an annotation** (current behaviour — leading `:Name` is a
   plain symbol/var). Then the 2 negative tests are mis-specified: they assert a typecheck
   "unknown type" error for a construct that is never a type annotation at top level. `/qa`
   should re-express them against a context where `:Int` IS an annotation (fn param / paren'd
   arg), where typecheck ALREADY produces the required error (proven above), or delete them as
   redundant with the fn-param coverage.

The §3.1/§8.9.1 reachability RULE is not in question and is correctly enforced for genuine
annotations; only the top-level *surface syntax* of `:Type value` needs a ruling.

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
