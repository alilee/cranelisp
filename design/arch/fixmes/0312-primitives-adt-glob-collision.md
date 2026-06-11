---
number: 0312
target: /design
filed_by: /dev
filed_at: 2026-06-11
sprint_filed: 78
refers_to: design/int/s78-entry-module.md §2.2 (item 3/4), §2.7.5, sprints/SPRINT.md Wave 4 /qa NARROWING
status: open
---

# `is_seeded` deletion surfaces a real `primitives`-seeded-ADT vs stdlib-ADT glob collision

## Issue

S78 Wave 4 §2 directs `/dev (src/)` to delete the `is_seeded` name-keyed
ambiguity-skip in `src/imports.rs::insert_detecting_ambiguity` (the `user`/
`primitives` arm), on the stated grounds that it was *solely* a bandage over the
prelude-flattening collision and that "primitives reach user code via prelude's
re-export chain-follow through the fallback, not a name-key" (§2.2 item 4; the
/qa NARROWING constraint).

Deleting it is spec-correct per §8.6.4 (two `import` forms bringing the same bare
name from different source modules MUST error). The prelude-fallback path (bit
ON) is unaffected — the §2 gate's `bare_primitive_resolves_via_prelude_reexport`
and the 3 import-shadow tests behave correctly.

**But the `primitives` arm was NOT solely a prelude-flattening bandage.** It also
suppressed a genuine collision that fires for modules that **explicitly** glob-
import `primitives` AND import a domain ADT module, with the prelude fallback bit
**OFF** (i.e. modules that refuse the prelude). Concretely, every stdlib module
shaped like `collections/list.cl` / `seq/lazy.cl`:

```clojure
(import [prelude []])                    ; refuses implicit prelude → fallback OFF
(import [primitives [*]])                ; glob → brings primitives/Option,Some,None,Pair (PUBLIC seeds)
(import [fn.option [Option Some None]])  ; specific → brings fn.option/Option,Some,None
```

`primitives` publicly seeds the `Option` ADT (`src/bootstrap.rs` Step 4,
`Visibility::Public`) because primitive signatures reference it (`parse-int ::
(Fn [String] (Option Int))`, `discover-tests :: ... (Option String)`) and the
no-stdlib REPL path needs a bare `Option`. The stdlib `fn.option` ALSO defines
`Option`. With `is_seeded` gone, the glob `primitives/Option` and the explicit
`fn.option/Option` collide → uniform `Ambiguous` → bare `None`/`Some`/`Option`
in the stdlib module poison to `undefined variable: None`.

This is NOT reachable via the prelude fallback (the module refuses prelude;
bit OFF), so §2.7.5's "primitives-via-prelude survives via the re-export
chain-follow" does not cover it. The §2 design reasoned only about bit-ON
prelude-fallback modules.

## Blast radius (confirmed by test run, `-j 2`)

The whole stdlib stops compiling. Cascading failures (all single root cause —
`undefined variable: None` in `collections.list`, then `+`/`/` undefined as the
chain unwinds):

- `tests/spec_08_modules.rs::null_import_module_resolves_all_names_via_explicit_imports`
- `tests/repl_introspection.rs::bare_primitive_two_hop_reexport_chain_lands_on_terminal_def`
- `tests/regression.rs::s60_run_tests_reduction_{1,2,3,4,5}_*`
- `tests/regression.rs::wave6_run_tests_batched_html_completes_without_crash`
- `tests/repl_persist_race.rs::repl_dep_load_no_race_with_persistent_workers`
- `tests/cache.rs::cache_repl_second_session_loads_prelude_from_cache`,
  `cache_repl_writer_survives_slash_reset`
  (`cache_repl_writes_manifest_on_prelude_load` is a SEPARATE pre-existing
  failure — it fails identically with `is_seeded` restored.)

Verified causal: restoring the `is_seeded` `primitives` arm makes
`null_import_*` and `s60_run_tests_reduction_2` pass again.

## Proposed resolution (for /design to decide — NOT enacted)

This is a cross-cutting decision the `/dev (src/)` lane cannot make unilaterally
(it risks the no-stdlib `Option` greens and the primitive-signature resolution).
Candidate dispositions, in rough order of cleanliness:

1. **Make the `primitives`-seeded ADTs (`Option`, `Some`, `None`, `Pair`, …)
   non-glob-exported** (`Visibility::Private` in `src/bootstrap.rs`, or an
   "internal seed" visibility), so `(import [primitives [*]])` does NOT pick them
   up, while qualified `primitives/Option` (for primitive sigs) and the prelude
   re-export path still resolve. Needs a check that the no-stdlib bare-`Option`
   path (tests + REPL) still works — those reach `Option` via the prelude
   re-export of `fn.option` (stdlib) OR via `primitives` re-export; if the latter,
   this breaks them. `/arch` owns `bootstrap.rs` visibility intent.

2. **Add a glob-vs-specific precedence rule**: a *specific* import shadows a
   *glob* import of the same name (no ambiguity) — the explicit/narrow import
   wins. This is a §8.6.4 spec amendment (the current text has no glob/specific
   exception) routed to `/spec`, plus threading the import-kind into
   `insert_detecting_ambiguity` (it currently sees only `ModuleEntry::Import`,
   the glob/specific distinction is already lost). Matches common language
   semantics (wildcard < explicit).

3. **Fix the stdlib** (`/stdlib`) to not glob-import `primitives` when it also
   imports domain ADTs — import the specific primitive *functions* it needs
   instead of `[primitives [*]]`. Narrowest blast radius if the stdlib is the
   only offender, but does not address the latent conflict for user code.

## Operational implication

Until resolved, the `is_seeded` deletion (correctly landed per the §2 contract)
leaves the workspace stdlib non-compiling, red-ing ~9 stdlib-dependent e2e tests.
The §2 prelude-as-outer-scope model itself is sound and green (15/15 logic on the
fixture-prelude `spec_08_prelude_outer_scope` suite — see the companion /qa FIXME
re: the 3 exit-code-1005 test-design defects). This FIXME isolates the ONE
remaining root cause that the §2 contract under-specified.
