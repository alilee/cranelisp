# src/

Cross-cutting source conventions for the Cranelisp binary/int surface. All compiler skills must follow these rules. Local `CLAUDE.md` files in subdirectories may add conventions but must not contradict these.

The as-designed int surface is defined by `design/arch/bounded-contexts.md` §6 (Binary / int) plus the crate/binary rustdoc and the `design/int/` design docs. The retired `design/arch/facades/*.md` facade-spec set is not a live reference (the directory holds only the s69/s70 audit records).

## Error Handling

- **No `unwrap()` in pipeline code.** Use `?` with `CranelispError`. `unwrap()` is permitted only in tests and in `main()`.
- **No `panic!()`.** Use `unreachable!("invariant: <description>")` for true programmer errors (logic bugs that should never occur). Never `panic!` on user input.
- **No `expect()` in pipeline code.** If the value might be None/Err due to user input, return a proper error. If it's a programmer invariant, use `unreachable!`.
- **Every error carries a `Span`** for source location. Parse errors use byte offset converted to Span at the reader boundary.
- **Warnings are data, not side effects.** Accumulate `Vec<Warning>`, never `eprintln!`. Warnings flow to the caller and are displayed by the binary crate.

## Code Structure

- **Max ~100 lines per function.** If a function grows beyond this, decompose it into named helpers.
- **Max 8 parameters.** Group related parameters into context structs.
- **One dispatch method per Expr variant.** `infer_expr` and `compile_expr` dispatch to `infer_let`, `infer_apply`, `compile_let`, `compile_apply`, etc.
- **Named structs for multi-field returns.** No bare tuples `(Vec<Type>, Type, String)` — use `MonoDefn`, `OverloadVariant`, etc.

## Naming Conventions

- **String newtypes for all identifiers.** `Symbol`, `ModuleFullPath`, `FQSymbol`, `TraitName`, `TypeName`, `ModuleName`, `LinkerSymbol`. Never pass bare `String` or `&str` where a typed identifier is expected.
- **Named constants for magic numbers.** `GOT_TABLE_SIZE`, `NULLARY_TAG_THRESHOLD`, etc. No bare numeric literals in logic.
- **Rust naming conventions.** `snake_case` for functions and variables, `CamelCase` for types and enum variants, `SCREAMING_SNAKE` for constants.

### JIT Symbol Names

All symbols registered in the JIT share a single flat namespace. Names must be unambiguous across user code, primitives, trait impls, and runtime infrastructure. Module-qualified paths (`module/name`) are the primary disambiguation mechanism, matching the language's own module system.

| Category | JIT name format | Example | Visible to users? |
|----------|----------------|---------|-------------------|
| User function | `name` or `module/name` | `factorial`, `user/factorial` | Yes |
| Trait method impl | `Trait.method$Type` | `Display.show$Int` | Via trait dispatch |
| Multi-sig variant | `name$Params` | `add$Int+Int` | Via overload dispatch |
| ADT constructor | `name` or `module/name` | `Some`, `Cons`, `user/Point` | Yes — via module system |
| Extern primitive | `name` (kebab-case) | `str-concat`, `int-to-string` | Yes — in `primitives` module |
| Runtime infrastructure | `runtime/name` | `runtime/alloc`, `runtime/panic` | No |

Rules:

1. **User-visible primitives** use the spec name exactly (kebab-case, per `spec/appendix-a-builtins.md`). The Rust function implementing the primitive follows Rust `snake_case` — the two names are independent.
2. **Runtime infrastructure** (allocator, dealloc, RC underflow check, etc.) uses the `runtime/` prefix. Internal — never callable from user code.
3. **Platform functions** loaded from DLLs use the platform's declared names, prefixed by the platform module path.
4. **No `cranelisp_` prefix.** Use module-qualified names instead.
5. **`#[unsafe(no_mangle)]` on runtime functions** is optional — symbols are registered by function pointer via `JITBuilder::symbol()`, not by linker symbol name. Use it only for stable debugger stack traces.
6. **Rust function names** for extern primitives should match the spec name in `snake_case` (e.g., `int_to_string` for `int-to-string`).

## Scope Management

- **Scope stack (push/pop), not `env.clone()`.** Push a scope frame, pop on exit — never clone the whole `local_env` at a scope boundary.
- **Consuming calling convention.** Callee owns heap parameters. Caller emits inc for non-last-use, or transfers ownership for last-use.

## Heap Access

- **Representation containment.** Only emit helpers (`heap_load`, `heap_store`, `emit_*_alloc`, `emit_rc_inc`, `emit_rc_dec`) may import layout constants (`HEAP_HEADER_SIZE`, field offsets). No other codegen code references raw byte offsets — layout assumptions are confined to a single module.
- **Pointer-width documentation.** Every `heap_load` / `heap_store` call must include a comment stating the semantic field and its width. E.g., `heap_load(ptr, 16, 8) // tag: i64`.
- **Base-pointer convention.** Heap pointers point to offset 0 of the allocation. All field accesses use positive offsets. No interior pointers.

## Serialization

- **Serde derives on all cross-boundary types.** `#[derive(Serialize, Deserialize)]` on types in `cranelisp-types`.
- **`#[serde(skip)]` for runtime-only fields.** Function pointers, JIT handles, `Duration` — skip with sensible defaults.

## Type System

- **The full `Type` enum exists from the start.** All variants (`Int`, `Bool`, `String`, `Float`, `Fn`, `ADT`, `Var`, `TyConApp`) are defined up front.
- **`Type::from_name()` / `Type::type_name()`** centralize primitive name mapping. No scattered match blocks.
- **`TypeId` is `u32`.** Not `usize`.

## Session/REPL module map

`CompilerSession` (`session_v4.rs`) is decomposed along the `design/int/int.md` §3.3 module map. Sibling modules hold `impl CompilerSession` blocks, so the private fields and helpers they reach are widened to `pub(crate)`.

| Module | Responsibility |
|---|---|
| `session_v4.rs` | `CompilerSession` struct + lifecycle (`new`, register/re-register module, link/entry-module, trampoline, watcher reload, `shutdown`/`Drop`); `SharedState`; worker-pool spawn/join; symbol-table + introspection accessors; `discover-tests` extern + `TestRunnerState`. |
| `eval.rs` | REPL eval form-chain — `eval` (cluster boundary + `:Type` grouping), `eval_one_form`, `process_single_form`/`process_form_cluster` (eval-thread dep-retry trampoline), `codegen_and_execute`, bare-symbol introspection, dep registration. |
| `repl/` | The REPL command/display surface, decomposed S110 (FIXME 0606) from the former `repl.rs` god-file. `repl/mod.rs` = slash dispatch (`dispatch_command`), prompt/banner/line-editor, input classification, and the **shared bottom-layer toolbox** (resolution glue `lookup_with_prelude_fallback*`/`resolve_*_arg`/`get_introspection` + the referer-scan family `body_references`/`sexp_references`/…) that all siblings depend on; it re-exports the shared externals as `pub(crate) use` and hosts the shared `#[cfg(test)] mod test_support` helpers. `QUIT_SENTINEL`/`ReplCommand` live here (`QUIT_SENTINEL` re-exported from `session_v4`). `repl/format.rs` = the **value/echo** half of the formatter family (`describe_symbol`, `collect_related*`, `format_eval_result*`, the `format_def_entry*` per-kind dispatcher, `format_sexp`/`indent_source_block`, the `push_*`/`code_block_doc`/`classification_metadata` span primitives, and the name-layout subfamily). `repl/format_type.rs` = the **per-kind definition-display leaves** — the `*_display`/`*_display_doc` builders for a named definition (`format_type_display`/`format_trait_display`/`format_builtin_type_display`/`format_special_form_display`/`format_macro_display`/`format_overloaded_variants`, `impls_for_type_in_view`) plus the `; defn:`/`; impl:`/`; match:` related-section builders (`format_related_section_doc`, `format_trait_related_sections*`) they share; `format_def_entry_doc` (in `format.rs`) routes to these leaves — a one-way `format.rs` → `format_type.rs` edge. `repl/search.rs` = the `/search` UI subsystem (`handle_search`, `render_search_row*`, settle/scheme/referer scan). `repl/commands.rs` = the `handle_*` slash-command battery. So the five-file layout is `mod`/`search`/`format`/`format_type`/`commands`. Cross-file free fns are `pub(crate)`; siblings reach the residual toolbox via `use super::*` and the externals via mod.rs's `pub(crate) use` re-exports. The format.rs A-split (FIXME 0627, `repl-decomposition.md` §1.6.1) landed all four split-able files under the ~1,500 guideline; `commands.rs` is ratified ≤ ~1,700. |
| `process_form.rs` | The shared gap-orchestration form chain. |
| `redefine.rs` | The dependent-recompilation session transaction (`design/int/session-transaction.md`): `AbiSurface` summary-diff, `RedefKind` classification, on-demand `ReverseIndex` from `Def.callees`, affected-set closure + SCC reverse-topo walk, `run_transaction`, `mark_broken`, `TransactionReport`. |

**redefine invariants (load-bearing).** A BROKEN entry's `code` field holds the trap stub's `Code` handle — a `code: None` + `ast: Some` entry would be silently RECOMPILED against the new-world callee by `derive_codegen_batch`'s synth-def sweep (the unsoundness the trap closes). The retention pool (`SharedState.retained_code`) is append-only to session end and pairs each trap stub with the provenance buffer its baked address reads. `__expr`/`__macro_*` are gate-exempt (fresh-slot churn every turn would exhaust the 1024-slot GOT). A slot-less staged Def displacing a slotted prior with compiled code must route the prior `Code` through the pool at the commit gate (`RetainedCode::frozen`) — dropping it is a UAF through the still-embedded GOT slot (FIXME 0479).

**Single-implementation discipline.** `process_form::compile_macro_clause_core` is the sole macro-clause compiler; it takes a `MacroClauseEnv` of the threaded refs, and the two callers (`compile_macro_with_state`, the resolver on-demand path, and `compile_macro_clause_inline`, the `&mut ModuleCompiler` Pass-2 path) each build the env from their own reference sources. Do not re-introduce a byte-identical mirror.

**Degraded startup load** (`repl/spec.md` §18.8). A REPL startup failure on the entry module does not exit — `main.rs` catches it and `recover_startup_failure` re-drives the backing source form-by-form through the eval path (green forms commit; failures retained as `FailedForm` on `CompilerSession.failed_forms`). While a module's failed set is non-empty it sits in `error_modules`: `process_commands` refuses expressions but ACCEPTS definition turns (the repair), and `regenerate_backing_file` re-emits each failed form verbatim so regen never drops a broken definition. Regeneration is source-text-first (`save::generate_fns_and_macros` emits the record's verbatim `Introspection.source` when it re-parses to the recorded sexp, via the consistency-gated `process_form::verbatim_source_slice`); macro-expansion-produced definitions record the turn's ORIGINAL outer form as the regen authority. Never author a second regen-source channel.

## REPL display

- **One styling authority — the `styled::render` seam (`repl/spec.md` §10.3).** ALL token-styled REPL output builds a `StyledDoc` of role-tagged spans (`src/styled.rs` — the `Role` vocabulary is the single code manifestation of the §10.3 R1–R15 table) and is emitted through `styled::render`, the SOLE site that applies the §10.3 style table. **`style::styled` is NEVER called outside `styled::render`** and the sanctioned `src/agent/render.rs` agent frame (markdown/gutter) — a second `style::styled` call site in a formatter is a mirror (Principle 7 drift; `/review` watches for it). A producer emits roles at construction and NEVER re-parses its own output to re-discover them. Shared line builders are single-sourced: `style::error_line` (R8/R9 `Error:` line), `style::repl_metadata_line` (R6 `;` lifecycle/watcher note), `repl::push_warning_line` (R6+R11 `; warning:`), `display::envelope` (`:Type value`). **Data-serialization is not display**: persisted `.cl` source / `FailedForm.text` / introspection `source` fallbacks use `pretty::pretty_print_plain` (the colour-free `.text()` of the doc), NEVER `pretty::pretty_print` — a colour-ON session that serialized through the display path would embed SGR into stored source and break re-parse (§10.2). The live TTY prompt (R13) is a **documented deferral** — left plain because rustyline prompt width + `continuation_prompt_string` length math have no e2e guard (§10.8); see `prompt_string`'s doc comment.
- **Builtin docstrings live on `PrimitiveDef.docstring` in `cranelisp-primitives`** (the canonical home — no parallel int-side table). Both the bare-primitive value display (`format_def_entry`) and `/doc` (`handle_doc`) read `entry.docstring.as_deref()` directly, satisfying the §A.5 MUST + §1.1 `; primitive - <doc>` format.
- **`/doc` follows the import chain.** `handle_doc` resolves the local entry through `resolve_entry_for_display` before reading the docstring — a bare re-exported primitive (`add-i64`) is an `Import` locally, not the `Def`.
- **EOF mid-form is a parse error, not a silent exit.** The `main.rs` read loop accumulates continuation lines until parens balance; at EOF with a pending unbalanced form the leftover buffer is flushed through `eval` and the parser's `unclosed '('` diagnostic is written to stdout (§5.1).
- **REPL input abstraction — `src/repl_input.rs`** (`repl/spec.md` §10.8). The read loop reads through one `ReplInput`, gated on `IsTerminal` for stdin. **TTY** = a `rustyline` editor (history recall + inline editing + per-project history, cap 1000, graceful-degrade). **Non-TTY** (piped/redirected — the e2e harness) = `rustyline` is NEVER instantiated; the loop reads fd 0 directly, one byte up to the newline, **no read-ahead**, and the prompt is written verbatim so output stays **byte-identical** (the `non_tty_repl_line_editor_off` golden guards this). No-read-ahead is load-bearing: the poll-shape `read-line` platform leaf shares fd 0 with the host, so a read-ahead `BufReader` would swallow a line a later `read-line` turn should consume. `WouldBlock`/`EINTR` are retried, not treated as EOF. The agent write-consent read (§15.2) goes through the SAME `ReplInput` (`read_consent_line`).

## Bootstrap and imports

- **`src/bootstrap.rs`** hosts `mount_synthetic_modules(symbol_tables, next_id)` — int's reconstruction of typecheck's former `register_builtins`. It seeds, in bootstrap order: special forms at root `""`; intrinsic type names + `Vec` in `primitives`; the synthetic `macros` module (`Sexp`/`SList` ADTs + `sconcat`); `Option`, `IO` (+ `bind`), `Trace`, and `TestResult` in `primitives`. Called from `CompilerSession::new`. ADTs are registered directly (TypeDef entry + per-ctor `Def { kind: Constructor }`); `register_synth_adt` mirrors typecheck's `register_type_def_with_ctor_infos` (computes `is_product` and attaches the type facet to the lone product ctor, else a separate `TypeDef`). Only `Pair` is a seeded product; `Option`/`Result`/`IO` are sums.
- **`src/imports.rs`** hosts the int-side import/export installer (`install_imports`/`install_exports`). Writes per-symbol `ModuleEntry::Import { source, visibility }` bindings (`Private` for `import`, `Public` for `export` re-export edges) + module-path aliases into `SharedState.module_aliases`. typecheck reads `module_aliases` read-only.
  - **`export` brings the name into the exporting module's OWN bare scope** (§8.4.0): `import`/`export` is the same bring-into-scope operation, visibility apart.
  - **§8.6.4 definition-over-(import|export|prelude) rejection** (FIXME 0514 — the no-exception ruling) lives at the **shared typecheck seam** `cranelisp_typecheck::check_forms` Pass-1 (`reject_def_over_binding`, checker.rs) — the single mode-uniform chokepoint both REPL/Additive and batch/Replace traverse, and the only place that sees the prelude OUTER scope. The int-side Pass-0 installer keeps only §8.6.5 ambiguity detection, including the distinct-terminal prelude-overlap poison (`insert_detecting_ambiguity` takes `prelude_fallback`). A pure-REPL import over an existing local def in a separate later cluster is a residual companion gap, not covered by the current matrix.

## Prelude as a resolution FALLBACK (not flattened, not an "outer scope")

The implicit prelude is resolved by a session-side **fallback mechanism**, NOT materialised into each module's symbol table (`design/int/s78-entry-module.md` §2). This is a resolution-mechanism detail with **zero semantic weight** (spec §8.8.1, `design/arch/prelude-import-convergence.md` §1): the implicit prelude is just `(import [prelude [*]])`, a prelude-provided name is in scope on **identical terms to an explicit import**, and there is **no "outer scope" as a language concept** — only the fallback. Consequently a definition over a prelude-provided name is a §8.6.4 conflict (never a shadow), rejected through the same `cranelisp_types::reject_def_over_binding` seam every definition form routes through (int's `defmacro` gate in `process_form/form_dispatch.rs` calls it directly; §Macro expansion below). The mechanism itself:

- **The bit.** `SharedState.prelude_fallback: PreludeFallback` (= `DashMap<ModuleFullPath, bool>`), session-side and **unserialized** (recomputed per session). `module_path → true` ⇒ a bare-name inner-table miss in that module falls back to the `prelude` module's OWN table (chain-following prelude's `(export [primitives [*]])`). Absent/`false` ⇒ no fallback (absence-is-OFF).
- **Who sets it.** `worker::inject_prelude_if_needed` is the single site. It still drives prelude discovery/load so the fallback has a table to consult; only the flattening is gone.
- **Who reads it.** typecheck reads it read-only via the `check_forms` `prelude_fallback` param (on `TypeCheckEnv`). int threads `&self.shared.prelude_fallback` everywhere it threads `module_aliases`. Platform FQ-sig checks pass an empty `PreludeFallback::default()`.
- **No name-key exemption.** Explicit-import shadowing of a prelude name is automatic (prelude's name is no longer an inner-table `Import` entry, so the explicit import is the sole entry and wins with NO ambiguity). **Do NOT re-introduce any name-keyed `"user"`/`"primitives"` exemption.**
- **Introspection reads the bit session-side** (`describe_symbol` adds a prelude hop; `handle_imports` appends a "Prelude (implicit)" group when the bit is ON).

## Cluster-atomic orchestration

- **`src/cluster.rs`** hosts `ProcessedCluster` and the `process_cluster`/`insert_cluster` free functions. `ProcessedCluster` carries cluster-level cross-symbol bookkeeping directly (warnings, resolved-import bindings, introspection records) — there is no separate `ModuleCheckAccumulator`.
- A **cluster** is the unit of typecheck atomicity: a non-`(begin)` REPL input = one-form cluster; `(begin …)` = explicit multi-form cluster; a batch file = one big cluster.
- **`process_cluster` is the SOLE crate-crossing where `ResolutionGap` values become scheduler calls.** Frontend and typecheck stay pure with respect to live state (return `Gap`, never call the scheduler). Typecheck dispatch is one call per cluster — `cranelisp_typecheck::check_forms(parsed, &mut ctx, symbol_tables)`; `worker::check_program_compat` is the int-side bridge. `cluster::process_cluster` (worker entry) + `worker::process_cluster_once` (shared Pass-0/1/2 core: expand → structural peel → build → fresh-staging `check_forms`) + `worker::drive_module_dep` (register-edge only) are the single live orchestration. "In-call-stack" describes the STATE (stack-local staging, dropped on a gap, rebuilt from the scheduler work packet `PriorityWork::Typecheck { module, sexps }`), not thread-blocking.
- **Entry-module single-orchestration is STRUCTURAL** (Invariant SW). The eval thread is the SOLE orchestrator of the entry module by construction, not a role flag: after startup the entry sits in its terminal pool (`TypecheckDone`), NOT in any typecheck queue, so no pool worker can re-claim it. The eval path (`ModuleCompiler.eval_driven == true`) NEVER moves the entry to `TypecheckBlocked`; on a dependency gap it records a cycle-check edge (`register_dep_edge_for_cycle_check`), waits on the dependency itself (`register_dep_for_eval`), and re-runs the cluster from the top. Watcher reload is pool-driven but eval-synchronous.
- **Signature barrier at the body boundary** (Invariant PP; FIXME 0452). `process_cluster_once` computes the cluster's static import closure once and gates the body (Pass-1/2) on the barrier: no body is admitted until every forward closure module has published its signatures — i.e. reached a terminal typecheck pool. **The terminal pool transition IS the publication edge** (`notify_typecheck_done` runs post-`finalize_cluster`, so `pool → TypecheckDone` happens-after the Defs are installed); there is NO separate `signatures_ready` bit. The worker path is a **single atomic check-and-block** (`block_on_first_unready_closure_member`): under one state-lock it scans for the first unready member AND registers `module` as its waiter — this closes the lost-wakeup that a two-call scan-then-register shape had. On a gap the worker frees back to the pool (requeue-when-ready); the eval thread — the one genuine waiter — blocks in `await_signature_barrier`. The root and its ancestors are excluded before the scheduler call. Per-cluster closure memo (`ModuleState.static_closure_memo`) runs the walk once per cluster, not once per retry.
- **Entry module is ordinary; `"user"` is only the default name.** The entry module (the `main`-bearing module under `--run`/`--link`, or the REPL's initial target) is ordinary in every respect. Its name is the CLI target, defaulting to `"user"` only when no target is given. No orchestration path keys on the module name; the only legitimate `"user"` literal is `main.rs`'s CLI default.

## Macro expansion — recognition primitive + single executor

The macro two-jobs split (`design/arch/macro-expansion-ownership.md`) is landed on int's side:

- **Recognition is a `cranelisp-types` query with a prelude outer-scope fallback.** `src/expander.rs::recognize_macro_head` wraps `cranelisp_types::resolve_macro_head` over a committed first-hop; it returns the macro's canonical `FQSymbol`, `Ok(None)` for a non-macro/forward reference, `Err` only for hard failures. When the first-hop misses AND the module's `prelude_fallback` bit is ON (current ≠ `prelude`), recognition RETRIES against the `prelude` module's OWN view. The prelude-retry hit is post-filtered on the canonical entry's `is_public()` (a PRIVATE prelude macro must NOT leak).
- **Execution is the single `JitMacroExpander`** (`src/expander.rs`) over the invocation core (`invoke_clause` + `invoke_jit_protected` + `rewrite_spans` + `src/marshal.rs`). It reads `clauses_meta` from the canonical `DefKind::Macro` entry, loads the clause fn's GOT-slot code ptr (`__macro_{name}_clause_{idx}`), marshals/invokes/unmarshals. An absent clause-code GOT slot surfaces a clear `MacroInvokeError::Aborted` rather than misbehaving. There is no `MacroEntry`-based parallel executor.
- **The walk.** `expand_sexp_recursive` is the live driver (Pass-1 expand loop with just-in-time dependency compilation), running inside `worker::process_cluster_once`. Macro sexp for on-demand compile is read back from `SharedState.introspection` (keyed by `FQSymbol`), not the symbol-table entry.

**FQ auto-loading + just-in-time dependency compile.** An FQ reference `mod/sym` (function OR macro) to a not-yet-loaded module is auto-loaded on demand (spec §8.5.4 / §9.3.6) in `--run`, `--link`-precompile, and REPL. The mechanism lives at the int boundary in `src/worker.rs`, NOT in typecheck (which stays pure — it surfaces a `ResolutionGap`, never loads). Two surfacing sites inside `process_cluster_once`: an FQ macro blocks via `SymbolTableMacroResolver::recognize` (`blocked_on_fq_module` → `ExpandOutcome::BlockedOnFqModule`); an FQ function/type maps `QualifiedModuleUnknown` → `ResolutionGap::SymbolTypechecked`. Both converge on `drive_module_dep`, which resolves the module file with the same rules as `import` (`pipeline::resolve_module_file`), registers + blocks on the dep, and returns `ClusterOnce::Gap { dep }` for retry-from-top against now-larger live state. Macro-vs-fn discrimination is implicit in the retry (only the dependency typecheck-and-compile is forced; functions are NOT speculatively JIT-pushed). Failure semantics: module not found → error at the referencing span; a transitive cycle back → the scheduler's acyclicity rejection in `block_for_typecheck`.

**`(mod X)` short-name alias + entry-file precedence** (spec §8.2.5/§8.2.6). `main.rs::resolve_target_from`: a `<name>.cl` file passed as target IS the entry; the directory-as-project rule fires ONLY when `<target>/` exists AND `<target>.cl` does NOT. `(mod X)` registers a module-path alias `X → <parent>.X` (`worker.rs::register_submodule_alias`) so a bare qualified ref `X/sym` resolves; the int FQ-autoload boundary applies the same `cranelisp_types::substitute_module_alias` before computing the dep to load. Import-alias bare qualified refs (`(import [(util u) …])`) are still owner-scoped-keyed and resolve only via `<owner>.alias/...`.

## Test discovery — `discover-tests` host-promised extern

Test discovery is mounted by `bootstrap.rs` as `primitives` entries, not by a special form:

| Symbol | `DefKind` | Body |
|---|---|---|
| `discover-tests` | `PrimitiveExtern` | `discover_tests_extern` in `src/session_v4.rs`, host-promised at session init |
| `catch-runtime-error` | `Primitive` | `cranelisp-intrinsics::panic`, resolved from the intrinsics archive |

`discover-tests` reads the live typed session state (it needs `Code`, which `cranelisp-intrinsics` cannot name — Principle 18), so its body lives in int and is promised via `jit.define_symbol("discover-tests", …)` in `worker::build_session_jit`. `catch-runtime-error` needs no `define_symbol` (JIT name = ABI name). The REPL `/run-tests` command drives discovery through the same core as `discover_tests_extern`. `TestRunnerState` lives on `SharedState`; the intrinsic null-checks the pointer and returns harmless defaults when no eval is active.

**No syntactic gating.** Do not re-introduce per-program scans that gate intrinsic registration (the pre-S66 `program_uses_test_forms` / `program_needs_trace` helpers were deleted). The trace family lives in `cranelisp_intrinsics::trace`, registered by `Jit::new`.

## Embedded agent (`src/agent/`)

The embedded LLM advisor lives entirely in `src/agent/`, fully `#[cfg(feature = "agent")]` — **feature-off the module does not exist and the default `cargo build` / `cargo nextest run` never compile rig**, so the standard build stays agent-free (full-suite timing baseline is in root `CLAUDE.md` §Testing). `design/int/agent.md` is the design.

- **Feature + deps.** `agent = ["dep:rig-core", "dep:tokio", …]` (root `Cargo.toml`). `rig-core` is optional, `default-features = false`, with the smallest transport set that compiles the completion API + the anthropic/ollama providers. **native-tls, NOT rustls:** the rustls path pulls `aws-lc-rs` (a heavy C TLS backend, ~30 MB + a C toolchain); native-tls links the system OpenSSL. tokio is current-thread only.
- **The `AgentModel` membrane.** rig's `CompletionModel` is NOT object-safe in 0.39.0, so a thin object-safe internal trait `AgentModel` (`agent/types.rs`) is the handle; rig's `CompletionModel` is the wire boundary one layer below, inside `provider.rs`. The lib name is `rig_core` (imports are `use rig_core::…`).
- **Module map.** `types.rs` (neutral vocabulary + `AgentModel` + `AgentState`); `provider.rs` (runtime provider selection by `CRANELISP_AGENT_PROVIDER` + the rig membrane + tokio bridge); `request.rs` (the one place coupled to rig's request/message/tool-call shapes); `harvest.rs` (push-context assembler); `primer.rs` + `primer.txt` (always-on language primer, `include_str!`); `pull.rs` (pull-as-visible-commands + the read-only allowlist consent gate); `stub.rs` (the deterministic test `AgentModel`); `mod.rs` (the classifier + `agent_turn` model↔tool loop).
- **Wiring.** `CompilerSession.agent: Option<AgentState>` (`#[cfg]`-gated, zero bytes feature-off). `main.rs` threads the resolved `--agent` flag into `s.enable_agent(…)` in the REPL arm only (agent is REPL-only). Dormant (no reachable provider) ⇒ `/ask` renders the U6 notice.
- **Testing.** The stub is selected e2e by `CRANELISP_AGENT_PROVIDER=stub` + `CRANELISP_AGENT_STUB_SCRIPT=<fixture>` (a line DSL). Lane A e2e lives in `tests/agent.rs` (`--features agent`); request-content assertions are `#[cfg(test)]` unit tests in `agent/mod.rs`. Run: `cargo nextest run --features agent --test agent` (e2e) + `… --lib 'agent::'` (unit).

## Testing

- **Every module gets `#[cfg(test)] mod tests`.** Unit tests live next to the code they test.
- **Integration tests in `tests/`** are owned by `/qa` + `/testing`, not by `/dev`.
- **Test names describe the behavior, not the implementation.** `test_let_polymorphism_infers_identity`, not `test_case_47`.

## Dependencies Between Crates

- `cranelisp-types`: no dependencies (except `serde`, `std`)
- `cranelisp-frontend`: depends on `cranelisp-types`
- `cranelisp-typecheck`: depends on `cranelisp-types`
- `cranelisp-backend`: depends on `cranelisp-types`, `cranelisp-intrinsics` (+ `cranelisp-primitives`, transitive)
- `cranelisp-intrinsics` + `cranelisp-primitives` (the D43 split of the former `cranelisp-runtime`): depend on `cranelisp-platform`, `cranelisp-types`
- `cranelisp-platform`: no dependencies (except `std`)
- `cranelisp` (binary): depends on all above

No circular dependencies. Cargo enforces this at build time.

## Debugging Cross-Crate Failures

When an integration test fails and the root cause could be in any crate, follow the isolation process in `tests/CLAUDE.md` §"Isolating Cross-Crate Failures". The key principle: write a crate-level unit test that asserts the expected state at the crate boundary. If it passes, the bug is in the integration wiring. If it fails, fix the crate.
