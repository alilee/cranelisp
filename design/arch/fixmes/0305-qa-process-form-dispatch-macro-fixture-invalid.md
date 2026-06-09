---
number: 0305
target: /qa
filed_by: /dev (int)
filed_at: 2026-06-09
sprint_filed: 77
refers_to: tests/process_form_dispatch.rs::process_form_dispatch_macro_after_import_succeeds_in_one_eval, design/arch/fixmes/0299-int-macro-cross-mode-availability.md, spec/08-modules.md §8.2 + §8.4
status: open
---

# `process_form_dispatch_macro_after_import_succeeds_in_one_eval` fixture is invalid per spec

## Issue

The `helper.cl` fixture inside this test contains TWO constructs that the spec
forbids, causing the `helper` module to fail to compile — which surfaces as the
test's error, NOT a macro-availability bug:

```clojure
(mod helper)              ; defect 1
(export [my-double])      ; defect 2
(defmacro my-double [x] `(add-i64 ~x ~x))
```

Current error (with the W-MacroTrait int fixes in place):

```
module 'helper' failed: module error at 0..12:
    submodule 'helper.helper' not found (declared by 'helper')
```

**Defect 1 — `(mod helper)` inside `helper.cl`.** Per spec §8.2 (lines 16–18,
80–84) a module's identity is its file path; `(mod name)` does NOT self-declare
the module — it declares a **child submodule** and MUST resolve to the child
directory path `helper/helper.cl` only. Since no `helper/helper.cl` exists, this
is a spec-mandated compile-time error. A dependency `.cl` file loaded via import
must NOT carry a self-naming `(mod …)` line (compare the passing `spec_08_modules`
fixtures: `util.cl` is just `(defn helper [] 42)` with no `(mod util)`).

**Defect 2 — `(export [my-double])`.** Per spec §8.4, `export_entry = module_spec
names_list`; `export` re-exports names FROM imported modules and always requires
a module spec + names list. There is no bare-local-symbol export form, so
`(export [my-double])` is rejected ("export: missing names list after module
'my-double'"). A module's own `defmacro` is **public by default** — no `export`
is needed to make `my-double` importable.

## Proposed resolution

Replace the `helper.cl` fixture body with just the macro definition (drop the
`(mod helper)` and `(export …)` lines):

```clojure
(defmacro my-double [x] `(add-i64 ~x ~x))
```

I verified end-to-end against `target/debug/cranelisp` that with this corrected
fixture the test's REPL stdin
(`(import [primitives [*]])` + `(import [helper [my-double]])` + `(my-double 21)`)
produces `:primitives/Int 42` with empty stderr — i.e. the macro-after-import
orchestration is correct; only the fixture was malformed.

## Operational implication / Context

S77 W-MacroTrait (RT5). The two genuine int orchestration defects this test
cluster was filed against (FIXME 0299 #1/#2 — cross-module clause-in-memory on
cache restore; same-module macro persistence) are FIXED in `src/` and their two
tests (`mode_equiv_macro_user_defined`, `persist_bug_macro_usage_in_defn_…`)
now pass. This third test fails only because its fixture violates spec §8.2/§8.4
— a /qa fixture repair, not a compiler change. Per
`memory/feedback_validate_tests_against_spec`, the fix is to the test.
