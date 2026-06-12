# src/

Cross-cutting source conventions for the Cranelisp reimplementation. All compiler skills must follow these rules. Local `CLAUDE.md` files in subdirectories may add conventions but must not contradict these.

## Error Handling

- **No `unwrap()` in pipeline code.** Use `?` with `CranelispError`. `unwrap()` is permitted only in tests and in `main()`.
- **No `panic!()`** Use `unreachable!("invariant: <description>")` for true programmer errors (logic bugs that should never occur). Never `panic!` on user input.
- **No `expect()` in pipeline code.** If the value might be None/Err due to user input, return a proper error. If it's a programmer invariant, use `unreachable!`.
- **Every error carries a `Span`** for source location. Parse errors use byte offset converted to Span at the reader boundary.
- **Warnings are data, not side effects.** Accumulate `Vec<Warning>`, never `eprintln!`. Warnings flow to the caller and are displayed by the binary crate.

## Code Structure

- **Max ~100 lines per function.** If a function grows beyond this, decompose it into named helpers. Long functions are the prototype's primary structural debt.
- **Max 8 parameters.** Group related parameters into context structs. The prototype's `compile_function` had 21 parameters — this must not recur.
- **One dispatch method per Expr variant.** `infer_expr` and `compile_expr` dispatch to `infer_let`, `infer_apply`, `compile_let`, `compile_apply`, etc.
- **Named structs for multi-field returns.** No bare tuples `(Vec<Type>, Type, String)` — use `MonoDefn`, `OverloadVariant`, etc.

## Naming Conventions

- **String newtypes for all identifiers.** `Symbol`, `ModuleFullPath`, `FQSymbol`, `TraitName`, `TypeName`, `ModuleName`, `LinkerSymbol`. Never pass bare `String` or `&str` where a typed identifier is expected.
- **Named constants for magic numbers.** `GOT_TABLE_SIZE`, `NULLARY_TAG_THRESHOLD`, etc. No bare numeric literals in logic.
- **Rust naming conventions.** `snake_case` for functions and variables, `CamelCase` for types and enum variants, `SCREAMING_SNAKE` for constants.

### JIT Symbol Names

All symbols registered in the JIT share a single flat namespace. Names must be unambiguous across user code, primitives, trait impls, and runtime infrastructure. The naming scheme uses module-qualified paths (`module/name`) as the primary disambiguation mechanism, matching the language's own module system.

**Categories:**

| Category | JIT name format | Example | Visible to users? |
|----------|----------------|---------|-------------------|
| User function | `name` or `module/name` | `factorial`, `user/factorial` | Yes |
| Trait method impl | `Trait.method$Type` | `Display.show$Int` | Via trait dispatch |
| Multi-sig variant | `name$Params` | `add$Int+Int` | Via overload dispatch |
| ADT constructor | `name` or `module/name` | `Some`, `Cons`, `user/Point` | Yes — via module system |
| Extern primitive | `name` (kebab-case) | `str-concat`, `int-to-string` | Yes — in `primitives` module |
| Runtime infrastructure | `runtime/name` | `runtime/alloc`, `runtime/panic` | No |

**Rules:**

1. **User-visible primitives** use the spec name exactly (kebab-case, per `spec/appendix-a-builtins.md`). The Rust function implementing the primitive follows Rust `snake_case` conventions — the two names are independent.
2. **Runtime infrastructure** (allocator, dealloc, RC underflow check, etc.) uses the `runtime/` module prefix. These are internal — never callable from user code.
3. **Platform functions** loaded from DLLs use the platform's declared names, prefixed by the platform module path.
4. **No `cranelisp_` prefix.** The `cranelisp_` prefix used in the sketch added no information (everything is cranelisp) and made a name-change harder. Use module-qualified names instead.
5. **`#[unsafe(no_mangle)]` on runtime functions** is optional — symbols are registered by function pointer via `JITBuilder::symbol()`, not by linker symbol name. Use it only if stable names in debugger stack traces are desired.
6. **Rust function names** for extern primitives should match the spec name in `snake_case` (e.g., `int_to_string` for `int-to-string`). Do not prefix with `cranelisp_`.

## Scope Management

- **Scope stack (push/pop), not `env.clone()`.** The prototype cloned `local_env` (~70+ entries) at every scope boundary. Use a stack-based approach: push a scope frame, pop on exit.
- **Consuming calling convention.** Callee owns heap parameters. Caller emits inc for non-last-use, or transfers ownership for last-use.

## Heap Access

- **Representation containment.** Only emit helpers (`heap_load`, `heap_store`, `emit_*_alloc`, `emit_rc_inc`, `emit_rc_dec`) may import layout constants (`HEAP_HEADER_SIZE`, field offsets). No other codegen code references raw byte offsets. This confines layout assumptions to a single module.
- **Pointer-width documentation.** Every `heap_load` / `heap_store` call must include a comment stating the semantic field being accessed and its width. E.g., `heap_load(ptr, 16, 8) // tag: i64`.
- **Base-pointer convention.** Heap pointers point to offset 0 of the allocation. All field accesses use positive offsets. No interior pointers.

## Serialization

- **Serde derives on all cross-boundary types.** `#[derive(Serialize, Deserialize)]` on types in `cranelisp-types`.
- **`#[serde(skip)]` for runtime-only fields.** Function pointers, JIT handles, `Duration` — skip with sensible defaults.

## REPL display (S77 W-Repl)

- **Builtin docstrings live in `src/builtin_docs.rs`, sourced from Appendix A.5.** `cranelisp-primitives` registers primitive `ModuleEntry::Def`s with `docstring: None` (its `PrimitiveDef` carries no Description text, and that crate is outside the int boundary). `builtin_docs::builtin_docstring(name)` maps the spec primitive name → its §A.3 Description column. It is the single source consulted by both the bare-primitive value display (`format_def_entry` primitive arm) and `/doc` (`handle_doc`), satisfying the §A.5 MUST + the §1.1 `; primitive - <doc>` format (FIXME 0301). When §A.3 gains/renames a primitive, add the row; an uncatalogued name returns `None` (→ bare `; primitive`, no doc).
- **`/doc` follows the import chain.** `handle_doc` resolves the local entry through `resolve_entry_for_display` before reading the docstring — a bare re-exported primitive (`add-i64`) is an `Import` locally, not the `Def`.
- **Single-ctor product value display reads the ctor scheme off the `TypeDef` entry.** For `(deftype Point [:Int x :Int y])` the ctor name == type name, so the `Point` symbol-table key holds the `ModuleEntry::TypeDef` (not a separate `Def`); the ctor's scheme rides on `TypeDef.constructor_scheme`. `display::ctor_field_types` checks BOTH the `Def` arm and the `TypeDef { constructor_scheme }` arm — the `Def`-only lookup returned no fields, so `(Point 3 4)` rendered as the bare ctor `Point` (FIXME 0302).
- **EOF mid-form is a parse error, not a silent exit.** The REPL read loop in `main.rs` accumulates continuation lines until parens balance. At EOF with a pending unbalanced form, the leftover buffer is flushed through `eval` and the parser's `unclosed '('` diagnostic is written to stdout (§5.1) — a complete form submits, so an incomplete form at EOF MUST error (FIXME 0142; user ruling 2026-06-09; spec recording owed via FIXME 0307 /spec).

## Type System

- **Ring 0 defines the full `Type` enum.** All variants (`Int`, `Bool`, `String`, `Float`, `Fn`, `ADT`, `Var`, `TyConApp`) exist from the start. Rings exercise them incrementally.
- **`Type::from_name()` / `Type::type_name()`** centralize primitive name mapping. No scattered match blocks.
- **`TypeId` is `u32`.** Not `usize`. 4 billion type variables is sufficient.

## Synthetic-module mount + import installer (S76 W-Absorb)

- **`src/bootstrap.rs`** hosts `mount_synthetic_modules(symbol_tables, next_id)` — int's reconstruction of the deleted `cranelisp_typecheck::register_builtins` body (FIXME 0242, now resolved). It seeds, in bootstrap order: special forms at root `""` (`ModuleEntry::SpecialForm`); intrinsic type names + `Vec` in `primitives`; the synthetic `macros` module (`Sexp`/`SList` ADTs + `sconcat`); `Option`, `IO` (+ `bind`), `Trace` (ADT data only — bodies are in `cranelisp-intrinsics`, codegen in backend), and `TestResult` in `primitives`. Called from `CompilerSession::new` (after the `PRIMITIVES_TABLE` `into_concrete` mount) and from `platform.rs`'s test fixture. `Def` entries use `ModuleEntry::def(scheme, kind)` (the Tier-1 builder); non-`Def` entries (`SpecialForm`/`IntrinsicType`/`TypeDef`) use plain struct literals + `insert` (the broader `declare_*` vocabulary stays deferred — FIXME 0241). ADTs are reconstructed directly (TypeDef entry + per-ctor `Def { kind: DefKind::Constructor }` with a synthesised `Expr::ConstrADT` body), since typecheck's `register_type_def` is no longer reachable. Fresh type vars for the polymorphic ADTs/`bind` come from `next_id` (high-water advances monotonically).
- **`src/imports.rs`** hosts the int-side import/export installer (`install_imports` / `install_exports`) — replaces typecheck's struck `register_imports`/`register_exports` (BC §2 invariants 2+8). Writes per-symbol `ModuleEntry::Import { source, visibility }` bindings into the current module's table (visibility `Private` for `(import …)`, `Public` for `(export …)` re-export edges; the `Reexport` variant is retired) + module-path aliases into `SharedState.module_aliases` (keyed `<owner>.<alias>`). Resolution semantics (glob/specific/member-glob, visibility checks, ambiguity detection via `insert_detecting_ambiguity`) mirror the deleted typecheck bodies. typecheck reads `module_aliases` read-only; `ModuleCompiler` carries `module_aliases: &ModuleAliases` and threads it into `check_forms`.

## Prelude as an OUTER SCOPE (S78 §2 — NOT flattened)

The implicit prelude is an **outer scope resolved by a session-side fallback bit**, NOT materialised (flattened) into each module's symbol table (S78 §2.7; `design/int/s78-entry-module.md §2`). The model:

- **The bit.** `SharedState.prelude_fallback: cranelisp_typecheck::PreludeFallback` (= `DashMap<ModuleFullPath, bool>`), a companion map of identical shape to `module_aliases`, session-side and **unserialized** (recomputed per session from source, never cached). `module_path → true` ⇒ a bare-name inner-table miss in that module falls back to the `prelude` module's OWN table (chain-following prelude's `(export [primitives [*]])` re-exports to the canonical primitive entries). Absent/`false` ⇒ no fallback.
- **Who sets it.** `worker::inject_prelude_if_needed` is the single site: on its ON path (module neither IS `prelude` nor references it via `sexps_reference_prelude`) it does `ctx.prelude_fallback.insert(module.clone(), true)` — replacing the two former `install_imports([prelude_glob])` flatten calls. It still drives prelude *discovery/load* (`register_dep` / `register_module` / `block_for_typecheck`) so the fallback has a table to consult; only the flattening is gone. OFF paths (early returns) insert nothing — absence-is-OFF.
- **Who reads it.** typecheck reads it read-only via the `check_forms` 5th param (`prelude_fallback: &PreludeFallback`) carried on `TypeCheckEnv` beside `module_aliases`, at its two bare-name resolution chokepoints. int threads `&self.shared.prelude_fallback` at every site that threads `module_aliases`; `ModuleCompiler` carries `prelude_fallback: &'a PreludeFallback`. Platform FQ-sig checks pass an empty `PreludeFallback::default()` (FQ leaves never need the bare-name fallback).
- **`is_seeded` is DELETED.** The former `imports.rs` name-keyed skip (`user`/`primitives`-sourced imports bypass §8.6.4 ambiguity) was a bandage over the collision the *flattened* prelude created in the inner table. With no flattening, `insert_detecting_ambiguity` reverts to uniform `Ambiguous` for two indirect entries from different sources. Explicit-import shadowing of a prelude name is now automatic: prelude's name is no longer an `Import` entry in the inner table, so the explicit import is the sole entry and wins with NO ambiguity. **Do NOT re-introduce any name-keyed `"user"`/`"primitives"` exemption.**
- **Introspection reads the bit session-side** (no threading — these hold `&self.shared`): `describe_symbol` adds a prelude hop between current and root (so `/sig`/`/doc` on a prelude name resolve); `handle_imports` appends a distinct **"Prelude (implicit)"** group (via `prelude_implicit_names`) enumerating prelude's own public symbols when the bit is ON — explicit-import categories narrow to what the module actually imported, the group is absent when the bit is OFF (refusal). `/list`/`/exports` are unaffected.

## Cluster-Atomic Orchestration (Sprint 66 Wave 3a-β)

- **`src/cluster.rs`** hosts `ProcessedCluster` and the `process_cluster` / `insert_cluster` free functions per `design/arch/facades/int.md` §"process_cluster". Per Decision 44's 2026-05-13 third amendment, `ProcessedCluster` carries cluster-level cross-symbol bookkeeping directly (warnings, resolved-import bindings, introspection records) — there is no separate `ModuleCheckAccumulator` on either the typecheck side or the int side. The pre-S66 type is fully retired.
- A **cluster** is the unit of typecheck atomicity (Decision 44):
  - Non-`(begin)` REPL input = one-form cluster.
  - `(begin form₁ … formN)` REPL input = explicit multi-form cluster.
  - Batch file = one big cluster of the file's non-structural forms.
- `process_cluster` is the SOLE crate-crossing where `ResolutionGap` values become scheduler calls. Frontend and typecheck stay pure with respect to live state (return `Gap`, never call the scheduler).
- **Typecheck dispatch surface** collapsed to one call per cluster — `cranelisp_typecheck::check_forms(parsed, &mut ctx, symbol_tables)`. `worker::check_program_compat` is the int-side bridge that converts `Vec<TopLevel>` (the legacy program shape) into `Vec<ParsedEntry>` for `check_forms`, constructs `ClusterContext::Live`, and dispatches.
- **Build-form dispatch** uses `worker::build_program_compat` as a drop-in replacement for the retired `cranelisp_frontend::build_program`. Per-form `build_form` is the new boundary; structural decls (`mod`/`import`/`export`/`platform`) flow through `extract_module_declarations` peeling.
- **Status (Sprint 78 — in-call-stack restructure).** Cluster-mode staging is the live typecheck path (`process_cluster_with_staging`, `a2dcebd` — `check_program_compat` delegates to it unconditionally; commit-on-Ok / discard-on-Err). The S78 restructure retired the `process_module_forms` outer per-form loop and lifted Pass-0/1/2 + the in-call-stack dependency drive into `cluster::process_cluster` (the worker entry) + `worker::process_cluster_once` (the shared core: expand → Pass-0 structural peel → build → fresh-staging `check_forms`) + `worker::drive_module_dep` (register-edge only). `cluster::process_cluster` is now **the single live orchestration**; the `process_module_forms` worker loop is gone. The cross-thread `module_sexps` / `suspend_states` parking maps and the `eval_in_flight` guard are deleted — the cluster sexps ride the scheduler work packet (`PriorityWork::Typecheck { module, sexps }`, stored on `ModuleState`), and a worker that hits a dependency gap frees back to the pool while the scheduler requeues the blocked module (retry-from-top, no saved suspend state) when its dep completes. The block/notify/requeue/cycle-detect kernel is unchanged; "in-call-stack" describes the STATE (stack-local staging, dropped on a gap, rebuilt from the packet), not thread-blocking. FIXME 0176/0179 closed.
- **Entry-module single-orchestration (S78 §3 / B1).** The eval thread (REPL) is the SOLE orchestrator of the **entry module** once the REPL loop takes over. `CompilerSession::mark_entry_eval_owned` (called by `main.rs` after startup `wait_inmem_complete`) sets `ModuleState.eval_owned = true` on the entry module and clears its stored `sexps`. While `eval_owned`, `try_unblock_locked` early-returns WITHOUT requeuing the module onto the pool — so a pool worker can never re-typecheck the entry module's own sexps concurrently with the eval thread (the B1 dual-orchestration the restructure was meant to remove). The eval thread drives its OWN dep retries (`process_single_form` blocks on the *dependency* via `wait_module_inmem_complete_blocking`, then re-runs the cluster from the top). The flag is keyed on the module's orchestration **ROLE** carried as data on `ModuleState` — **NEVER** on the module name (`"user"` is only the entry module's default name; see §1 below). `--run`/`--link` entry modules and all dependency modules stay `eval_owned = false` (pool-driven; requeue is correct there). `eval_owned` is preserved across watcher-triggered re-register (`re_register_module`) — so post-reload dependency-completion requeues still skip the eval-owned module (`try_unblock_locked` early-return). The reload pass ITSELF is pool-driven but eval-synchronous: `re_register_module` resets the entry module to `pool: TypecheckFirst` + `sexps: Some` + pushes it onto `typecheck_first`, so a pool worker re-typechecks it, but the watcher reload runs synchronously on the eval thread (`poll_and_reload` / `reload_module`), blocking the eval loop — there is no concurrent eval claim, so the concurrent-B1 defect stays closed.
- **Entry module is ordinary; `"user"` is only the default name (S78 §1).** The entry module — the `main`-bearing module under `--run`/`--link`, or the REPL's initial target — is an ordinary module in every respect. Its name is the CLI target (`sudoku`, `myapp`), defaulting to `"user"` only when no target is given. `CompilerSession::new(settings, root, entry_module_name)` receives that name and seeds the REPL cursor (`current_repl_module`), the carry-forward `repl_check_state`, and `TestRunnerState.current_module` off it (NOT a hardcoded `"user"`); the entry module's table is created lazily by its real name via `ensure_module_exists` for pre-first-input introspection. `/mod` with no argument (`handle_mod("")`) returns the cursor to `self.entry_module` (the "home" module), and `run_test_by_name` defaults an unqualified test name to the current REPL module. The only legitimate `"user"` literal is `main.rs`'s CLI default when no target is given. No orchestration path keys on the module name.

## Macro expansion (S76 W-Macro, fire B) — recognition primitive + single executor

The macro **two-jobs split** (`design/arch/macro-expansion-ownership.md`) is landed on int's side:

- **Recognition is a `cranelisp-types` query, with a prelude OUTER-SCOPE fallback (S78 §2).** `src/expander.rs::recognize_macro_head` wraps `cranelisp_types::resolve_macro_head` over a committed first-hop (`View::single(live)` over the current module). It handles imports/reexports/aliases/visibility and returns the macro's canonical `FQSymbol`, `Ok(None)` for a non-macro or forward (pre-`defmacro`) reference, `Err` only for hard failures (private / unknown qualified module). **Since §2 made the prelude an outer scope (not flattened), prelude-provided macros (`cond`/`when`/`do`/`str`/`thread-first`/`case`/`vec`/…) are NOT in the current module's inner table** — so when the first-hop misses (`Ok(None)`) AND the module's `prelude_fallback` bit is ON (and current ≠ `prelude`; absence-is-OFF), recognition RETRIES `resolve_macro_head` against the `prelude` module's OWN view, rooted at `prelude` (chain-following prelude's `(export …)` re-exports). **Public-only (the I-1 lesson):** the prelude-retry hit is post-filtered on the canonical entry's `is_public()` (`prelude_macro_public`) — a PRIVATE prelude macro must NOT leak to a user module (reachability is judged relative to the original user module, never in prelude's subtree). The `prelude_fallback` bit is threaded as a param; both resolvers (`worker::SymbolTableMacroResolver`, `session_v4::ReadOnlyMacroResolver`) pass `&SharedState.prelude_fallback`. **Mostly zero int→typecheck dependency for recognition** — it is a types query (`macro-availability-model.md` §0.7) plus the session-side `PreludeFallback` companion-map read. The bespoke chain-walks are gone: `resolve_macro_definition` (worker) is replaced by `recognize_macro_head` + a direct `read_macro_meta` lookup on the resolved canonical entry. (NOTE: the parallel constructor-resolution chokepoints in `cranelisp-typecheck` — pattern-ctor + internal-ctor gate — also needed the §2 fallback and are tracked by FIXME 0317 `target: /typecheck`, outside the int boundary.)
- **Execution is the single `JitMacroExpander`.** `src/expander.rs::JitMacroExpander` implements `cranelisp_types::MacroExpander` over the surviving invocation core (`invoke_clause` + `invoke_jit_protected` signal-protected JIT call + `rewrite_spans` + `src/marshal.rs`). Given `(fq, args, span)` it reads `clauses_meta` from the canonical `DefKind::Macro` entry, selects the matching clause, loads the clause fn's GOT-slot code ptr (`__macro_{name}_clause_{idx}`), marshals/invokes/unmarshals, and rewrites spans. An absent clause-code GOT slot surfaces a clear `MacroInvokeError::Aborted` ("…not in memory…") rather than misbehaving. The shared `execute_matched_clause` is the **one** invocation core — there is no `MacroEntry`-based parallel executor (`MacroEntry`, `build_macro_entry_from_clauses`, `expand_macro_call_with_entry` all deleted).
- **The walk.** `expand_sexp_recursive` survives as the live driver (the Pass-1 expand loop with just-in-time dependency compilation — `macro-availability-model.md` §0.4). S78: it runs inside `worker::process_cluster_once`, the shared core that `cluster::process_cluster` (worker entry) and `process_single_form` (REPL) both drive. The walk's `MacroResolver` trait does recognition (`recognize`) + on-demand clause compilation only; execution flows through `JitMacroExpander` (it exposes `symbol_tables()` for the walk to build the expander).
- **Macro sexp for on-demand compile** is read back from `SharedState.introspection` (keyed by `FQSymbol`), not the symbol-table entry (the per-entry `sexp` field was retired, Decision 41) — `worker::resolve_macro_sexp_from`.
- **Deleted dead scaffolding.** `scheduler::block_for_macro_codegen` + its private helpers (`push_priority_entries_locked`, `wire_priority_edges_locked`) and `worker::collect_transitive_uncompiled_deps` are deleted — the locked decision forbids same-module non-macro clause callees (round-trip safety, §0.3), so there is no empty-slot case to pre-compile (`macro-availability-model.md` §0.7). The priority-codegen-queue subsystem (`PriorityEntry`, `take_priority_work`'s `BlockingJitCodegen` scan) was removed; `PriorityWork` carries only `Typecheck { module, sexps }` (S78 packet) + `JitCodegen` (cache-hit inmem load).

**FQ auto-loading + just-in-time dependency compile (S76 W3, FIXME 0268 resolved).** An FQ reference `mod/sym` (function OR macro) to a not-yet-loaded module is auto-loaded on demand (spec §8.5.4 / §9.3.6), in `--run`, `--link`-precompile, and REPL. The mechanism lives at the int boundary in `src/worker.rs`, NOT in typecheck (which stays pure — it surfaces a `ResolutionGap`, never loads):

- **Where the gap is caught.** Two surfacing sites, both inside `process_cluster_once` (S78 — formerly `process_module_forms`):
  1. *FQ macro* (`(mac/twice …)`): during Pass-2 expansion, `SymbolTableMacroResolver::recognize` detects a `/`-qualified head whose module is absent from `symbol_tables`, captures it on `blocked_on_fq_module`, and returns `Ok(None)` (the aborted walk treats the head as ordinary). `try_expand_sexp` surfaces it as `ExpandOutcome::BlockedOnFqModule`, `process_regular_form` returns the dep module, and `pass2_check_bodies_with_expansion` returns `Pass2Result::BlockedOnFqModule`.
  2. *FQ function / type* (`(mac/helper …)`): typecheck maps `QualifiedModuleUnknown` → `ResolutionGap::SymbolTypechecked` (checker.rs); `check_program_compat` returns `Ok(Some(gap))` instead of swallowing it; `finalize_cluster` maps the gap to its module and drives it. (In practice an FQ function head also contains `/`, so it usually blocks via the Pass-2 macro-recogniser path first — both routes converge on `drive_module_dep`.)
- **Drive + retry-from-top (S78).** `drive_module_dep` resolves the module file with the **same rules as `import`** (`pipeline::resolve_module_file`; no new search semantics), `register_dep` (parse → `Arc<[Sexp]>`) + `register_module(dep, sexps, true)` + `block_for_typecheck` (register-edge only — it does NOT wait). `process_cluster_once` returns `ClusterOnce::Gap { dep }`. The worker wrapper (`handle_typecheck_work_shared`) frees back to the pool — the scheduler requeues the blocked module when the dep completes (`notify_typecheck_done` → `try_unblock_locked`, reading the module's sexps off `ModuleState`); the REPL wrapper (`process_single_form`) blocks on `wait_module_inmem_complete_blocking(dep)` then loops. Either way the cluster re-runs from the top against now-larger live state (no saved index). Already-loaded / cache-hit deps use `block_for_typecheck` + `scheduler.unblock_module` (immediate re-queue — no future `notify_typecheck_done` sweep would fire).
- **Macro-vs-fn discrimination is orchestrator-owned and implicit in the retry-from-top:** only the dependency typecheck-and-compile is forced (the dep is registered + blocked on via `drive_module_dep`); functions are NOT speculatively JIT-pushed. A dep macro's clause code is JIT'd by the dep's own Pass-2 codegen, so the re-run expand finds it in memory. **Consequently the `priority_boost_jit` / `wait_for_inmem` priority-codegen subsystem was never needed and is deleted** (B5 disposition — see `src/scheduler.rs`).
- **Failure semantics:** module file not found → module-not-found error at the referencing span; a transitive cycle back to the referencing module → the scheduler's existing acyclicity rejection in `block_for_typecheck`.

**Cross-mode macro availability on cache restore (S77 W-MacroTrait, FIXME 0299 — RESOLVED).** The former "cross-module macro loaded from the disk cache fails with 'clause N is not in memory'" limitation is fixed by three coupled int-side changes (the macro model is LOCKED — these are orchestration, not model, changes):

- **Cache-restore clause materialisation.** `SymbolTableMacroResolver::recognize` (worker.rs) gained a Step 2a: when a recognised macro's clause GOT slot is empty AND its home module is registered-as-cached (`scheduler.cached_module_contains`), it drives `handle_cached_codegen` synchronously to link the home module's `.o` and populate the GOT before the executor reads the clause ptr. A cache-restored module is installed at `TypecheckDone` with `code: None` + empty GOT (its `.o` codegen is a *deferred* step), so the clause is not in memory at expansion until this drive runs; the introspection-record recompile fallback does not help because cache-restored modules never populate introspection.
- **Macro sexp into Introspection.** `register_macro_in_module` now records the macro's sexp + source into the int `Introspection` record (REPL mode only — the old `FIXME(fire-B)` discarded it). This single source feeds BOTH the on-demand clause recompile (`resolve_macro_sexp_from`) AND `save::generate_module_source`. Without it, `regenerate_backing_file` silently DROPPED every `defmacro` from the regenerated `user.cl`, so a cached REPL restart of a same-module macro hit `undefined variable: <macro>`.
- **Binary-exported primitive externs for the cache Linker.** `load_cached_module_via_linker` calls `register_binary_exported_primitives`, which resolves slot-less `DefKind::Primitive` symbols (the synthetic `macros`-module `sconcat`/`quote-sexp`) via `dlsym(RTLD_DEFAULT, name)` (`dlsym_host_symbol`) and registers them with the cache `Linker`. These are `#[unsafe(export_name="…")]` symbols in `cranelisp-primitives` (statically linked into the host); the fresh JIT resolves them through its exported-symbol fallback, but the cache `Linker` has none — so a cached stdlib `.o` referencing `sconcat` failed `unresolved symbol: sconcat`. Ring primitives (in the `primitives` module GOT) are still registered by the GOT-pointer walk; only the slot-less synthetic-module externs need dlsym.

**Closed (S78 — FIXME 0176/0179):** `cluster::process_cluster` IS the live orchestration; `worker::process_cluster_once` is its shared Pass-0/1/2 core (staging-mode `check_program_compat` activated). There is no longer a separate `process_module_forms` worker loop or a zero-caller scaffold. Same-module non-macro definitions are still NOT available at expansion (the §9.3.4 rejection; its diagnostic-message quality is FIXME 0262, `/typecheck`).

**`(mod X)` short-name alias + entry-file precedence (S77 W-Module, FIXME 0121 resolved).** Two coupled int-side fixes make a `(mod child)`-declaring entry project compile in `--run`/`--link`/cache:

- **Entry-file precedence in `main.rs::resolve_target_from`.** Per spec §8.11.1 the project root is the directory *containing the entry file*. A `<name>.cl` file passed as the target IS the entry; a same-named `<name>/` directory is its submodule directory (§8.2.5). Rule 3 (directory-as-project) now fires ONLY when `<target>/` exists AND `<target>.cl` does NOT — otherwise an entry file declaring `(mod child)` (which needs a sibling `<entry>/` directory to hold `<entry>/child.cl`) was misread as a directory target and the compiler hunted a non-existent `<entry>/user.cl`. `resolve_target` delegates to `resolve_target_from(target, cwd)` so the rules are unit-testable off-cwd (`main.rs` `#[cfg(test)]`).
- **`(mod X)` registers a module-path alias** `X → <parent>.X` (`worker.rs::register_submodule_alias`, called from `handle_mod`) so a bare qualified ref `X/sym` resolves to the loaded submodule `<parent>.X` (spec §8.2.6 / §8.5.1 — the loaded module's identity is its FULL path per §8.1; no module literally named `X` exists). Keyed by the bare short name so typecheck's §8.6.6 longest-prefix substitution (`cranelisp_types::resolve::substitute_module_alias`) matches the `module_part`; `Visibility::Private`. The int FQ-autoload boundary (`SymbolTableMacroResolver::recognize`) must apply the SAME substitution before computing the dep module to load — `worker.rs::resolve_module_alias` mirrors the (crate-private) types longest-prefix fn, because the autoload boundary runs before typecheck. Without it the recogniser took `mod_part` verbatim and tried to load `X` (→ "module 'X' referenced by 'X/...' not found"). NOTE: import-alias bare qualified refs (`(import [(util u) …])` → bare `u/helper`) are still owner-scoped-keyed (`<owner>.alias`) and so resolve only via `<owner>.alias/...`; the spec §8.3.4 `str/split` bare form is a separate, pre-existing gap NOT in W-Module scope.

## Test discovery — `discover-tests` host-promised extern (S76 W-Collapse / Wave 4b)

Test discovery is mounted by `bootstrap.rs` as two `primitives` entries, not by a
`(run-tests ...)` special form:

| Symbol | `DefKind` | Body |
|---|---|---|
| `discover-tests` | `PrimitiveExtern` | `discover_tests_extern` in `src/session_v4.rs`, host-promised at session init |
| `catch-runtime-error` | `Primitive` | `cranelisp-intrinsics::panic`, resolved from the intrinsics archive |

`discover-tests :: (Fn [(Vec String)] (Vec (Pair String (Fn [] (Option String)))))`
reads the live typed session state (it needs `Code`, which `cranelisp-intrinsics`
cannot name — Principle 18), so its body lives in int. `Jit::new` has no extension
point for it; int promises it via the additive `Jit::define_symbol` escape hatch in
`worker::build_session_jit` (`jit.define_symbol("discover-tests", discover_tests_extern)`;
test-discovery.md §6). `catch-runtime-error` needs no `define_symbol` — JIT name = ABI
name and it resolves from `intrinsics_table()`.

`TestResult` and `run-test` are **RETIRED** (test-discovery.md, fourth convergence) —
the old `(run-tests ...)` special form path, `run_test_extern`, `int_intrinsics()`,
and the SList/IO/TestResult marshalling are all gone. The REPL `/run-tests` command
(`handle_run_tests`) drives discovery through the same core as `discover_tests_extern`.

(S76 trace ruling 2026-06-04: the trace family — `cranelisp_trace_format` + the 12
`cranelisp_trace_*` bodies — also LEFT int. It lives in `cranelisp_intrinsics::trace`,
published via `intrinsics_table()`, registered by `Jit::new`. `src/trace.rs` is deleted.)

**No syntactic gating.** Do not re-introduce per-program scans that gate intrinsic registration — the pre-S66 `program_uses_test_forms` / `program_needs_trace` / `any_compiled_defn_uses_test_forms` helpers were deleted in Wave 3a-γ. See FIXME 0178 for the architectural rationale (forbidden-patterns clause to land on `facades/intrinsics.md`).

The thread-local state `discover_tests_extern` dereferences (`TestRunnerState`) is set just-in-time before invoking compiled code. `TestRunnerState` lives on `SharedState` (built once in `CompilerSession::new`, stable for session lifetime); the REPL `/mod` command updates only its `current_module` field through its `Mutex`. The intrinsic null-checks the pointer and returns harmless defaults when no eval is active. (`TraceDisplayState` was deleted with the trace family in S76 — see above.)

## Known regressions from the Wave 3a-β collapse

The Wave 3a-β typecheck-collapse refactor regressed several test categories where the pre-S66 multi-call shape carried cross-form state across separate `check_form` invocations. The new single-call shape rebuilds that state per `check_forms` call, which exposes accumulator-fragmentation issues on:

- **Constrained polymorphism across multiple REPL inputs** — e.g., `(defn id [x] x)\n(id 7)\n`. The second-form mono dispatch interacts pathologically with the per-call typecheck state; investigation in flight via FIXME `target: /typecheck`.
- **Multi-clause macro compilation through `compile_macro_clause_inline`** — the legacy threading of `&mut CheckState` + `&mut ModuleCheckAccumulator` is now no-op (the accumulator is local to `check_forms`). Some macro-clause flows expect cross-form context that the new shape doesn't surface.

These will be addressed in the FIXME 0176 follow-up that lifts `ClusterContext::Cluster` + staging into `process_cluster` proper.

## Testing

- **Every module gets `#[cfg(test)] mod tests`.** Unit tests live next to the code they test.
- **Integration tests in `tests/`.** Owned by `/qa`, organized by ring.
- **Test names describe the behavior, not the implementation.** `test_let_polymorphism_infers_identity` not `test_case_47`.

## Dependencies Between Crates

- `cranelisp-types`: no dependencies (except `serde`, `std`)
- `cranelisp-frontend`: depends on `cranelisp-types`
- `cranelisp-typecheck`: depends on `cranelisp-types`
- `cranelisp-backend`: depends on `cranelisp-types`, `cranelisp-runtime`
- `cranelisp-runtime`: depends on `cranelisp-platform`, `cranelisp-types`
- `cranelisp-platform`: no dependencies (except `std`)
- `cranelisp` (binary): depends on all above

No circular dependencies. Cargo enforces this at build time.

## Debugging Cross-Crate Failures

When an integration test fails and the root cause could be in any crate, follow the isolation process in `tests/CLAUDE.md` §"Isolating Cross-Crate Failures". The key principle: write a crate-level unit test that asserts the expected state at the crate boundary. If it passes, the bug is in the integration wiring. If it fails, fix the crate.
