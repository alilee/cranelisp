---
number: 0009
target: /int
filed_by: /arch
filed_at: 2026-04-26
sprint_filed: 63
refers_to: design/arch/facades/int.md §"process_form — the gap-orchestration retry loop" + §"SharedState — the worker-shareable session subset" + §"Introspection", design/arch/sequences/concurrency-symbol-table-entry.mmd, design/arch/sequences/exec-flow-compilation.mmd, design/arch/CLAUDE.md Decisions 38 + 39
status: open
---

# `register_module` runs Phase 0 explicitly; `process_form` shifts from `entry().or_default()` to `get()`

## Issue

`facades/int.md` `process_form` (lines 397–423) currently does, per form:

```rust
let scope_table = self.symbol_tables.entry(scope.clone()).or_default();
let check_result = match cranelisp_typecheck::check_form(ast, &mut scope_table, &self.symbol_tables) {
    ...
};
```

This holds a DashMap entry write lock (`RefMut[SymbolTable]`) on the scope module **for the entire duration of `check_form`**. The lock blocks any other worker from acquiring shared shard access to the same module — a real cross-module read contention point (see FIXME 0008 §"Issue").

The fix on `/typecheck`'s side (FIXME 0008) reshapes `SymbolTable` so all post-setup mutation is per-entry via the inner DashMap. To realise that benefit, `/int`'s integration layer must:

1. Run a **Phase 0 setup step** in `register_module` that does the brief `&mut SymbolTable` work (`write_structural_decls`) before any form-by-form typecheck dispatches.
2. Switch `process_form` from `entry(&scope).or_default()` to a shared `get(&scope)` for the per-form typecheck loop.

Without these two changes, the `/typecheck` facade reshape (FIXME 0008) is wasted — the integration layer would still hold a per-form RefMut even after `check_form` no longer requires `&mut`.

## Proposed resolution

### Change 1 — `register_module` runs Phase 0 explicitly

Today's `register_module(module, source)` flow conceptually: store source, dispatch `PriorityWork::Typecheck(module)`. Restructure as:

```rust
pub fn register_module(&mut self, module: ModuleFullPath, source: Arc<str>) -> Result<(), CranelispError> {
    // Parse extracts BOTH forms AND structural decls (imports/exports/platforms/submodules).
    // The parser already produces ParseProduct { forms: Vec<Sexp>, structural: StructuralDecls } per
    // exec-flow-compilation.mmd line 54.
    let parse_product = cranelisp_frontend::parse(&source)?;

    // Phase 0 — brief &mut SymbolTable hold for structural decls.
    {
        let mut scope_table = self.symbol_tables.entry(module.clone()).or_default();
        scope_table.write_structural_decls(parse_product.structural);
        // RefMut drops here.
    }

    // From this point on, the SymbolTable is reachable only via shared .get() — no whole-module
    // write lock is ever taken again. Per-symbol mutation flows through &self methods
    // (insert_or_update, write_code) backed by the inner DashMap's per-key write locks.

    self.scheduler.register_module(module);    // dispatches PriorityWork::Typecheck(module) when ready
    Ok(())
}
```

The Phase 0 block is microsecond-scale. The RefMut drop **must** happen before `scheduler.register_module` so workers picking up `PriorityWork::Typecheck` find the SymbolTable reachable via shared `.get()` only.

### Change 2 — `process_form` uses shared `.get(&scope)`

```rust
pub fn process_form(&mut self, form: Sexp, scope: &ModuleFullPath) -> Result<ProcessedForm, CranelispError> {
    let mut sexp = form;
    loop {
        let expanded = match cranelisp_frontend::expand(sexp.clone(), &self.symbol_tables) {
            Ok(s) => s,
            Err(ExpansionError::Gap(gap)) => { self.handle_gap(gap)?; continue; }
            Err(other) => return Err(other.into()),
        };

        let ast = cranelisp_frontend::build_ast(expanded)?;

        // CHANGED: shared .get(), not .entry().or_default(). Phase 0 already created the SymbolTable.
        // The Ref is held only across check_form; per-entry mutations inside check_form acquire
        // the inner DashMap's per-key write locks briefly.
        let scope_table = self.symbol_tables.get(&scope)
            .expect("Phase 0 must run in register_module before process_form");

        let check_result = match cranelisp_typecheck::check_form(ast, &scope_table, &self.symbol_tables) {
            Ok(r) => r,
            Err(CheckError::Gap(gap)) => { self.handle_gap(gap)?; continue; }
            Err(other) => return Err(other.into()),
        };

        return Ok(ProcessedForm::from(check_result));
    }
}
```

Note `&scope_table` (shared) rather than `&mut scope_table`. The signature change is on `/typecheck`'s side via FIXME 0008.

### Change 3 — call-site updates for any other `&mut SymbolTable` usages

Audit `/int` for any other site that calls a `&mut SymbolTable` method on a `Sess.symbol_tables` value. The expected list after FIXME 0008 lands:

- `write_structural_decls` — only at Phase 0 in `register_module` (above).
- `append_defn_order(sym)` — per REPL eval that introduces a new defn (brief initiator-thread `&mut` hold, the same shape as Phase 0).
- Everything else (`insert_or_update`, `write_code`, `install_import_bindings`, `get`, `get_type`, `defined_symbols`, `public_symbols`, `all_symbols`, `allocate_got_slot`, `defn_order`) — `&self`, no RefMut needed.

Any remaining `&mut SymbolTable` site that's NOT in the Phase 0 block or per-eval `append_defn_order` is a regression from the design intent and should be migrated to the per-entry pattern.

### Change 4 — formalise `SharedState` and split from `CompilerSession` (per Decision 38)

Per `facades/int.md` §"SharedState — the worker-shareable session subset":

- Define `pub struct SharedState { symbol_tables, scheduler, cache, kept_dlls, introspection, settings, project_root, lib_dirs, platform_dirs }` in `src/session_v4.rs` (or `src/shared_state.rs`).
- `CompilerSession` shrinks to `{ shared: Arc<SharedState>, watcher, current_repl_module, repl_input_active, worker_pool, warnings }`.
- Worker loops change signature: `priority_worker_loop(shared: Arc<SharedState>)` and `nice_worker_loop(shared: Arc<SharedState>)` — receive their own Arc clone at spawn.
- `process_form` becomes a free function `worker::process_form(shared: &SharedState, form: Sexp, scope: &ModuleFullPath)` that workers invoke directly. `CompilerSession::process_form` becomes a thin delegating wrapper for REPL eval / initiator-side use cases.
- `handle_gap` and `ensure_registered` similarly become free functions taking `shared: &SharedState`.
- All worker-side `Sess.scheduler` / `Sess.symbol_tables` / `Sess.cache` references become `shared.scheduler` / `shared.symbol_tables` / `shared.cache`.

### Change 5 — populate `Introspection` at parse + codegen sites (per Decisions 38 + 39)

In `process_form` after parse + macro expansion, write per-defn `source` and `sexp`:

```rust
if let Some(intro) = shared.introspection.as_ref() {
    intro.insert(fq.clone(), Introspection {
        source: Some(file_arc[defn.span.start..defn.span.end].to_string()),  // for file-based; for REPL evals it's the eval text
        sexp: Some(expanded.clone()),
        ..Default::default()
    });
}
```

In the codegen worker after `compile_to_module` finalize, update with codegen artefacts:

```rust
if let Some(intro) = shared.introspection.as_ref() {
    if let Some(mut entry) = intro.get_mut(&fq) {
        entry.clif_ir = Some(ctx.captured_clif());            // when CRANELISP_CODEGEN_TRACE
        entry.disasm = Some(ctx.captured_disasm());           // when trace mode
        entry.code_size = Some(ctx.code_size());
        entry.compile_duration = Some(ctx.elapsed());
    }
}
```

The `as_ref()` check is the canonical mode discriminator — production batch (`shared.introspection == None`) skips both populate paths, paying zero per-symbol overhead.

### Change 6 — `regenerate_backing_file` rewrite (per Decision 39)

`Sess::regenerate_backing_file(&mut self, module: &ModuleFullPath)` walks `defn_order`, looks up each defn's source on `Introspection`, concatenates, writes to the .cl file:

```rust
pub fn regenerate_backing_file(&mut self, module: &ModuleFullPath) -> Result<(), CranelispError> {
    let st = self.shared.symbol_tables.get(module)
        .ok_or_else(|| /* error: module not registered */)?;
    let intro = self.shared.introspection.as_ref()
        .ok_or_else(|| /* error: introspection required for regenerate */)?;

    let mut text = String::new();
    for sym in st.defn_order() {
        let fq = FQSymbol::new(module.clone(), sym.clone());
        if let Some(info) = intro.get(&fq) {
            if let Some(src) = &info.source {
                text.push_str(src);
                text.push('\n');
            }
        }
    }
    std::fs::write(self.module_file_path(module), text)?;
    Ok(())
}
```

Old shape (slicing into `module_sources`) is deleted along with the `module_sources` field.

### Change 7 — error formatting (per Decision 39)

Add `Sess::format_error(&self, err: &CranelispError) -> String` that resolves `ErrorLocation` against the current mode:

- Inline `ctx` snippet present → use it directly (parser path).
- `fq` present + introspection enabled → look up `shared.introspection[fq].source`, slice using `line_col` for inline rich display.
- Neither → fallback to `file:line:col: error: message` style.

REPL display path calls this; production batch CLI display path also calls this. One formatter, mode-conditional input.

## Operational implication

- **Cross-module read contention disappears.** Worker reading m1 via `Sess.symbol_tables.get(&m1)` no longer blocks behind another worker's per-form RefMut on m1. Only the brief Phase 0 hold (microseconds) is exclusive — and Phase 0 happens once per module, before any cross-module dependents exist.

- **Per-symbol gap mechanism becomes mechanically sound.** Per FIXME 0008 §"Operational implication" — the `Gap(SymbolTypechecked)` / `wait_for_typecheck_symbol` / `notify_symbol_typechecked` round-trip in `handle_gap` works without the livelock risk it would have under per-form whole-module RefMut.

- **REPL upsert path unchanged in shape.** `register_defn_signature` (`crates/cranelisp-typecheck/src/program.rs:2184–2232`) carry-forward (Decision 31 + Decision 32 Clone bound) operates on the entry-level `Option<C>`; that's a per-entry write under the inner DashMap, no whole-module RefMut needed. The carry-forward fix the Wave-3b implementation outcome required remains correct.

- **Decision 30 single-worker-per-module reframes as ORDERING, not lock-safety.** The integration layer can keep dispatching at most one `PriorityWork::Typecheck(module)` at a time as a scheduler discipline (avoid per-module dispatch races, simplify form-by-form sequencing), but the lock layer no longer requires it.

- **Production batch carries zero per-symbol metadata overhead.** `shared.introspection: None` in `--run` non-trace and `--link` modes; introspection populate paths short-circuit on the `as_ref()` check. Only REPL mode and `CRANELISP_CODEGEN_TRACE=1` runs incur the per-defn metadata cost.

- **`module_sources` field is deleted.** No SharedState field tracks per-module source text — per Decision 39, source lives per-defn on `Introspection.source`. The watcher path reads files from disk on change events; nothing in SharedState keeps the file string alive.

- **Cache schema bump (per FIXME 0008 update).** `SymbolTable.defn_order: Vec<Symbol>` changes the serialised shape; the cache schema version constant in `crates/cranelisp-backend/src/cache/mod.rs` (per Decision 34) increments. Old caches reject as version-mismatch.

## Context

Surfaced during S63 W2 sequence-diagram authoring of `design/arch/sequences/concurrency-symbol-table-entry.mmd`. Earlier diagram drafts retained the per-form `entry().or_default()` shape and tried various wait-on-contention designs (per-symbol with retry; module-grained `wait_for_typecheck_module`); user direction at S63 W2 review selected per-symbol mutability with brief Phase 0 setup, motivating both this FIXME and FIXME 0008.

**Now formally specified by Decisions 38 + 39** (filed in `design/arch/CLAUDE.md` Sprint 63 alongside this FIXME revision). Decision 38 pins the formal `SharedState` shape + per-symbol mutability discipline + `Introspection` placement (Option-discriminated on `SharedState`). Decision 39 pins per-defn source on `Introspection.source` + `defn_order: Vec<Symbol>` on `SymbolTable` for canonical regeneration order + `ErrorLocation` carrying coordinate data with formatting downstream. This FIXME is the `/int` slice of those decisions — Phase 0 setup, worker shift to `Arc<SharedState>`, `process_form` shared-access pattern, introspection populate sites, `regenerate_backing_file` rewrite, `format_error` formatter.

Pairs with FIXME 0008 (the typecheck-facade counterpart — `check_form` signature drop `&mut`, `install_import_bindings` becomes `&self`, `defn_order` field added). Both should land together — `/int` cannot drop the per-form RefMut until `/typecheck` accepts `&SymbolTable` in `check_form`'s signature.
