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

## RESOLUTION (S77 W-MacroTrait, /dev int — 2026-06-09)

The int orchestration defects behind tests #1 and #2 are FIXED in `src/`
(`worker.rs`, `session_v4.rs`); both tests now PASS. Test #3 is a **/qa
test-design defect** (the fixture, not a compiler bug) — handed off via FIXME
0305. This FIXME stays `open` only because it `refers_to` test #3, which still
fails until /qa repairs its fixture; the int work is complete.

**Three distinct roots found (not one):**

1. **`mode_equiv_macro_user_defined` [repl_cached] + cross-module imported macro
   on cache restore** — root: a cross-module macro whose home module is restored
   from the disk cache is installed at `TypecheckDone` with `code: None` + empty
   GOT (its `.o` codegen is a deferred step), so at expansion the clause GOT slot
   is empty → "clause N is not in memory". The introspection-record recompile
   fallback also fails (cache-restored modules never populate introspection).
   **Fix** (`worker.rs::SymbolTableMacroResolver::recognize`, new Step 2a): when a
   recognised macro's clause is not in memory and its home module is registered-
   as-cached, drive `handle_cached_codegen` synchronously to link the `.o` and
   populate the GOT before the executor reads it. (This is the cross-module half
   of the disk-cache gap previously noted as a "Known limitation" in
   `src/CLAUDE.md`.)

2. **`mode_equiv_macro_user_defined` [repl_cached] same-module REPL macro on
   restart** — root: `register_macro_in_module` discarded the macro sexp (an old
   `FIXME(fire-B)`), so it was never written to the int `Introspection` record.
   Consequence: `regenerate_backing_file` (via `save::generate_module_source`)
   silently DROPPED every `defmacro` from the regenerated `user.cl`, so a cached
   REPL restart saw `(defn main [] (twice 21))` with no `twice` →
   `undefined variable: twice`. **Fix**: `register_macro_in_module` now records
   the macro sexp/source into `Introspection` (REPL mode), feeding BOTH the
   on-demand recompile path AND the backing-file regenerator.

3. **`persist_bug_macro_usage_in_defn_survives_session_restart`** — root: the
   cache-restore `Linker` (`worker.rs::load_cached_module_via_linker`) registers
   the intrinsics catalog but NOT user-callable primitive externs. The synthetic
   `macros`-module `sconcat` (and `quote-sexp`) are binary-exported symbols the
   fresh JIT resolves via its exported-symbol fallback; the cache Linker has no
   dlsym fallback → a cached stdlib `.o` referencing `sconcat` failed with
   `unresolved symbol: sconcat`. **Fix**: `register_binary_exported_primitives`
   resolves slot-less `DefKind::Primitive` symbols via `dlsym(RTLD_DEFAULT, …)`
   and registers them with the Linker, mirroring the JIT.

Unit tests added: `worker::tests::dlsym_host_symbol_resolves_exported_primitive`,
`worker::tests::dlsym_host_symbol_misses_unexported_name`.

---


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
