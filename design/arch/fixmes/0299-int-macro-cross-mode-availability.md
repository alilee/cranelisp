---
number: 0299
target: /int
filed_by: /qa
filed_at: 2026-06-09
sprint_filed: 77
refers_to: tests/build_confidence.rs::mode_equiv_macro_user_defined (FAILING), tests/repl_persist.rs::persist_bug_macro_usage_in_defn_survives_session_restart (FAILING), tests/process_form_dispatch.rs::process_form_dispatch_macro_after_import_succeeds_in_one_eval (FAILING), sprints/SPRINT.md §"W3 / W-MacroTrait" (RT5), tests/plan/ledger.md (RT5)
status: open
---

# Macro cross-mode availability — clause/helper not in memory across REPL≢`--run` and cache restart

## Issue

Compiled macro clause pointers (and the helper fns macro bodies expand into)
are not reliably available at expansion time across all execution modes and
across cache restart. The macro-availability MODEL is LOCKED (per /arch Phase-2
Q3(b) — this is orchestration/Pass-1 clause-ptr availability + REPL/`--run`
parity, NOT a /spec or /arch decision). Three failing tests, three faces of the
same root:

1. **`mode_equiv_macro_user_defined`** — `(defmacro twice [x] ...) (defn main []
   (twice 21))` produces 42 in `repl_fresh`, `run_fresh`, `run_cached`,
   `link_fresh`, `link_cached`, but the **`repl_cached`** permutation fails:

   ```
   [repl_cached] observed=None exit=Some(1)
     stderr: user.cl:1:1: error: module error at 0..0: module 'user' failed:
             type error at 48..53: undefined variable: twice
   ```

   On a cached REPL restart the macro `twice` is not re-registered before the
   `(defn main ...)` body that uses it is checked.

2. **`persist_bug_macro_usage_in_defn_survives_session_restart`** — a macro
   whose body expands to a call into `macros/sconcat` (str macro) works in
   session 1, but session 2 (cache restart) fails:

   ```
   stderr=user.cl:1:1: error: module error at 0..0: module 'fn.threading'
          failed: codegen error at 0..0: unresolved symbol: sconcat
   ```

   The macro re-registers but the helper symbol it expands into
   (`sconcat`) is not in the codegen batch after restart.

3. **`process_form_dispatch_macro_after_import_succeeds_in_one_eval`** — the
   stderr is actually a cross-module RESOLUTION error (RT4-adjacent), masking
   the macro path:

   ```
   Error: module error at 0..0: module 'helper' failed: module error at 0..12:
          submodule 'helper.helper' not found (declared by 'helper')
   Error: type error at 1..10: undefined variable: my-double
   ```

   This test couples RT4 (module discovery) and RT5 (macro after import); the
   macro-availability fix may not fully clear it until RT4 (`(mod …)` discovery
   / cross-module search) is also resolved. Verify after the RT4/W-Module fix.

## Proposed resolution

- Ensure Pass-1 macro registration runs (and clause pointers / expansion-helper
  symbols are populated into the live symbol table + codegen batch) on a CACHED
  REPL restart, not just on a cold session — mirror the cold-start path.
- Ensure the symbols a macro body expands into (`sconcat` and friends in the
  `macros` module) are present in the codegen batch after cache restart.
- For #3, confirm the macro path is correct once RT4 (cross-module/`(mod …)`
  resolution — FIXME 0121 / W-Module) lands; if it still fails on `my-double`
  after RT4, the residual is this FIXME.

## Operational implication / Context

S77 W-MacroTrait (RT5). The three failing tests are the durable record + the
regression guard. The macro model is locked; this is an orchestration / cache-
restart parity gap, owner /dev int. Note the cross-coupling of #3 with RT4 —
resolve W-Module first or in tandem.
