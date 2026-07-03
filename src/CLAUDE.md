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

## Session/REPL module decomposition (FIXME 0109 §3.3, Waves C+D)

The former `session_v4.rs` god-file is decomposed along the `design/int/int.md`
§3.3 module map. All four are `pub(crate) mod` in `lib.rs`:

| Module | Responsibility |
|---|---|
| `session_v4.rs` (residual) | `CompilerSession` struct + lifecycle (`new`, `register_module`/`re_register_module`, `link_by_name`/`register_entry_module`, `trampoline`, watcher reload, `shutdown`/`Drop`); `SharedState` construction; worker-pool spawn/join; symbol-table accessors + `symbol_*` introspection getters; the `discover-tests` extern + `TestRunnerState`. |
| `eval.rs` | REPL eval form-chain — `eval` (cluster boundary + `:Type` grouping), `eval_one_form`, `process_single_form` / `process_form_cluster` (the eval-thread dep-retry trampoline over `process_form::process_cluster_once`), `codegen_and_execute`, `check_bare_symbol_introspection`, `register_dep_for_eval`. |
| `repl.rs` | Slash-command dispatch (`process_commands` / `dispatch_command` / `parse_slash_command` / all `handle_*`), prompt/banner/line-editor (`print_banner`, `write_prompt`, `pretty_print`, `parens_balanced`), and the introspection-display helpers (`describe_symbol`/`collect_related[_for]`, `format_eval_result`, `format_def_entry`, `resolve_entry_for_display`, the `format_*` free fns, `ReplCommand`/`ImportClass`). |
| `process_form.rs` | The shared gap-orchestration form chain (Wave C). |
| `redefine.rs` | The S101 dependent-recompilation session transaction (`design/int/session-transaction.md`): `AbiSurface` summary-diff comparand + `RedefKind` classification (consumed by the commit gate in `worker::commit_staging_to_live` — the single slot-policy authority), on-demand `ReverseIndex` from `Def.callees`, affected-set closure + SCC reverse-topo walk with the §4.1 slot-less pass-through, `run_transaction` (eval-thread-synchronous), `mark_broken` (trap-stub patch + retention pool + `SharedState.broken` registry), `TransactionReport` (`repl/spec.md` §18.3 rendering). Key invariants: a BROKEN entry's `code` field holds the trap stub's `Code` handle (a `code: None` + `ast: Some` entry would be silently RECOMPILED against the new-world callee by `derive_codegen_batch`'s synth-def sweep — the exact unsoundness the trap closes); the retention pool (`SharedState.retained_code`) is append-only to session end and pairs each trap stub with the provenance buffer its baked address reads; `__expr`/`__macro_*` are gate-exempt (fresh-slot churn on every expression turn would exhaust the 1024-slot GOT); a SLOT-LESS staged Def displacing a slotted prior with compiled code (concrete fn redefined as polymorphic/overloaded — the T1 shape) must route the prior `Code` through the pool at the commit gate (`RetainedCode::frozen`, the shared displace-to-pool constructor) — dropping it is a UAF through the still-embedded GOT slot (FIXME 0479; the T1 *semantic* cure is FIXME 0477). |

**Degraded startup load (S102 CS-0489, `repl/spec.md` §18.8).** A REPL
startup failure on the entry module no longer exits — `main.rs` catches it and
`lifecycle.rs::recover_startup_failure` re-drives the backing source
form-by-form through the eval path (green forms commit; failures retained as
`FailedForm` on `CompilerSession.failed_forms`, keyed by module). While a
module's failed set is non-empty it sits in `error_modules`: `process_commands`
refuses expressions with the §14.4 message but ACCEPTS definition turns
(`is_repair_definition_turn` — they are the repair), `eval` clears repaired
symbols (`clear_repaired_failed_form`), and `regenerate_backing_file` re-emits
each failed form's verbatim text (`append_failed_forms`) so regen never
silently drops a broken definition. The loader drains
`pending_cascade_reports` (startup is a load, not a user redefinition turn —
no `stale:` prints at startup). Regeneration itself is **source-text-first**
(S102 CS-D2): `save::generate_fns_and_macros` emits the record's verbatim
`Introspection.source` when it re-parses to the recorded sexp
(`sexp_matches_source`, reader-desugar-aware) and carries the live docstring;
all introspection source capture goes through the consistency-gated
`process_form::verbatim_source_slice`. Macro-expansion-produced definitions
record the turn's ORIGINAL outer form as the regen authority (S102 CS-D1;
the expanded `(defmacro …)` artifact stays on `.expanded` + `macro_sexp`),
and regen dedupes by authored-form identity — never author a second
regen-source channel.

**Module-scoped field privacy.** The `eval.rs`/`repl.rs` methods are
`impl CompilerSession` blocks in sibling modules, so the `CompilerSession`
private fields they reach were widened to `pub(crate)`
(`worker_pool`, `current_repl_module`, `repl_check_state`, `repl_input_active`,
`warnings`, `entry_module`) — and the session-resident helpers they call
(`current_module_path`, `current_symbol_table`, `set_current_module`,
`get_introspection`, the `discover_*`/`run_test_by_name` test helpers,
`ReadOnlyMacroResolver`, `TestOutcome`, etc.) are `pub(crate)`. `QUIT_SENTINEL`
lives in `repl.rs`, re-exported from `session_v4` to preserve its former path.

**Macro-clause single implementation.** `process_form::compile_macro_clause_core`
is the sole macro-clause compiler; `compile_macro_clause_with_state` (resolver
path, raw refs) and `compile_macro_clause_inline` (`&mut ModuleCompiler` path)
are thin adapters that source the references from their callers. The two former
byte-identical bodies (a post-Decision-44 convergence) are collapsed.
`inline_jit_codegen_for_module` / `_for_names` is already a thin-wrapper-over-core
pair (module derives the batch + notifies; names is the shared core), not a mirror.

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

- **Builtin docstrings live on `PrimitiveDef.docstring` in `cranelisp-primitives` (FIXME 0308).** Primitive `ModuleEntry::Def`s now carry their Appendix A.5 Description text on the `docstring` field (populated in `cranelisp-primitives`, the canonical home — no parallel int-side table). Both the bare-primitive value display (`format_def_entry` primitive arm) and `/doc` (`handle_doc`) read `entry.docstring.as_deref()` directly, satisfying the §A.5 MUST + the §1.1 `; primitive - <doc>` format. The former `src/builtin_docs.rs` parallel table is retired (it duplicated §A.3 with no structural coupling — Principle 7).
- **`/doc` follows the import chain.** `handle_doc` resolves the local entry through `resolve_entry_for_display` before reading the docstring — a bare re-exported primitive (`add-i64`) is an `Import` locally, not the `Def`.
- **Single-ctor product ctors are dual-facet `Def`s (S79 Option 3a, FIXME 0319).** For `(deftype Point [:Int x :Int y])` the ctor name == type name, so the type and its sole constructor collide on the `"Point"` symbol-table key. The surviving entry is the **got-slotted ctor `Def`** (exactly like a sum ctor) carrying a **type facet**: `DefKind::Constructor { type_def: Some(Box<TypeDefInfo>), .. }`. The ctor's scheme lives on its own `Def.scheme`, its field names on `Def.param_names`. The retired `ModuleEntry::TypeDef.constructor_scheme` smuggling field (and the FIXME-0302 product-fallback leg in `display::ctor_field_types`) are gone — `ctor_field_types` reads the single `Def` arm for products and sum ctors alike. Because the product ctor is now a `Def { ast: Some(..) }`, it flows through `SymbolTable::defined_symbols()` and got-slots + codegens like any other ctor (product ctors are no longer special — Principle 16). `bootstrap.rs::register_synth_adt` mirrors `typecheck::register_type_def_with_ctor_infos`: it computes `is_product` (`ctors.len()==1 && ctor-name==type-name`) and either attaches the facet to the lone ctor `Def` (product, no separate `TypeDef`) OR registers a separate `TypeDef` with `type_def: None` ctors (sum/enum). Only `Pair` is a seeded product; `Option`/`Result`/`IO` are sums.
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
- **Entry-module single-orchestration — STRUCTURAL exclusive claim (S93 §7 step 5 / Invariant SW; supersedes the S78 `eval_owned` flag).** The eval thread (REPL) is the SOLE orchestrator of the **entry module** by *construction*, not by a role flag. The retired `eval_owned` field + its `try_unblock_locked` early-return are GONE. The mechanism: after startup the entry module sits in its terminal pool (`TypecheckDone`) — NOT in any typecheck queue — so no pool worker can re-claim it for typecheck (`take_priority_work` only pops `typecheck_first`/`typecheck_next`). The eval path (`ModuleCompiler.eval_driven == true`, set only in `eval.rs`/`repl.rs`) NEVER moves the entry to `TypecheckBlocked`: on a dependency gap it records a cycle-check edge via `scheduler.register_dep_edge_for_cycle_check` (the `block_dep` helper in `process_form/dependency.rs` routes eval→cycle-edge vs pool→`block_for_typecheck`), then the eval thread waits on the *dependency* itself (`register_dep_for_eval` → `wait_module_inmem_complete_blocking`) and re-runs the cluster from the top, clearing the edge after the wait (`clear_dep_edge`). Because the entry never enters `TypecheckBlocked`, `try_unblock_locked`'s existing `pool != TypecheckBlocked` guard already makes a stray requeue impossible — there is no second orchestrator to suppress, so no flag (claimable XOR owned, by construction). `CompilerSession::mark_entry_eval_owned` now only drops the entry's startup sexps (`scheduler.release_entry_sexps`). The cycle-check edge stays visible to the REVERSE-direction check (a dep that imports the entry back is rejected by `block_for_typecheck`'s acyclicity scan), so REPL import-cycle diagnosis is preserved without blocking the entry. Watcher reload is **pool-driven but eval-synchronous**: `re_register_module` resets the entry to `TypecheckFirst` + `sexps: Some` and a pool worker re-typechecks it with the UNIFORM block/requeue discipline (`eval_driven == false` on the Replace path), while the eval thread blocks in `wait_inmem_complete_blocking` — no concurrent eval claim, so B1 stays closed and no role-keyed reload path remains.
- **Signature barrier at the body boundary (S93 §7 step 4 / Invariant PP; BC §6 ruling B; Wave-2c hardening — FIXME 0452).** `process_cluster_once` computes the cluster's STATIC import closure once (`dependency::static_import_closure`, reused for the cycle-error gate) and, after Pass-0, gates the body (Pass-1/Pass-2) on the closure barrier (`gate_body_on_signature_barrier`): no body is admitted until every FORWARD closure module has **published its signatures** — i.e. reached a terminal typecheck pool (`TypecheckDone`/`Complete`). **The terminal pool transition IS the publication edge (/arch ruling, option i):** `notify_typecheck_done` runs post-`finalize_cluster`, so `pool → TypecheckDone` happens-after the cluster's Defs are installed in `symbol_tables[module]`. There is therefore **no separate `signatures_ready` bit** — the live-dead bit + its explicit `register_module_signatures` driver + the `SignatureBarrierRegister` trace tag were REMOVED; the barrier predicate (`signatures_ready_locked`) reads pool-terminal state directly. **The worker path is a SINGLE ATOMIC check-and-block** (`scheduler.block_on_first_unready_closure_member`): under ONE state-lock acquisition it scans for the first unready closure member AND registers `module` as its `"*"` waiter (the `block_for_typecheck` requeue-kernel transition: TypecheckBlocked + `blocked_on` edge + acyclicity check). This closes the lost-wakeup Blocker the former two-call shape (`first_unready_closure_member` lock/scan/release THEN `block_dep` re-lock/register — now removed) had: if a member reached `notify_typecheck_done` between the two locks, its waiter-sweep ran before the waiter registered → `module` stranded in TypecheckBlocked on an already-terminal member → permanent hang. With one lock the scan and registration cannot interleave with the sweep. On `Some(member)` the worker surfaces a `Gap` and frees back to the pool (requeue-when-ready, never parks a pool thread); the eval thread — the one genuine waiter, consuming no pool slot — blocks in `scheduler.await_signature_barrier`. The root and its **ancestors** are excluded by `gate_body_on_signature_barrier` before the scheduler call: an ancestor reached by a `super` import commits its signatures BEFORE driving the child submodule (`drive_submodules` runs after the parent's `finalize_cluster`), so the parent is intentionally mid-flight (blocked on the child) and is NOT a forward dependency — gating on it would false-deadlock and trip a false parent⇄child cycle. **Per-cluster closure memo (Task-3, perf):** the static-closure walk (`fs::read_to_string` + `parse` per transitively-imported module) is memoised on `ModuleState.static_closure_memo` keyed by a cheap fingerprint of the cluster's DIRECT import paths (`scheduler.cached_static_closure`/`cache_static_closure`), so the walk runs ONCE per cluster instead of once per retry-from-top attempt (O(retries × closure-size) IO removed); `re_register_module` resets the memo on a source change. **One readiness kernel** (`notify_typecheck_done` terminal transition + the `block_for_typecheck`/atomic-barrier requeue) gated at two points (Pass-0 per-direct-import discovery+load; body-boundary per-closure transitive barrier) — NOT two protocols.
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
- **`(mod X)` registers a module-path alias** `X → <parent>.X` (`worker.rs::register_submodule_alias`, called from `handle_mod`) so a bare qualified ref `X/sym` resolves to the loaded submodule `<parent>.X` (spec §8.2.6 / §8.5.1 — the loaded module's identity is its FULL path per §8.1; no module literally named `X` exists). Keyed by the bare short name so typecheck's §8.6.6 longest-prefix substitution (`cranelisp_types::substitute_module_alias`) matches the `module_part`; `Visibility::Private`. The int FQ-autoload boundary (`SymbolTableMacroResolver::recognize`, `process_form.rs`) applies the SAME substitution before computing the dep module to load — it calls the now-public `cranelisp_types::substitute_module_alias` directly (S81 W-G item 0303 promoted it to the types public surface and deleted the former int-side `resolve_module_alias` byte-identical re-impl — Principle 7 single-source-of-truth). The autoload boundary runs before typecheck, so it must alias-resolve itself; without it the recogniser took `mod_part` verbatim and tried to load `X` (→ "module 'X' referenced by 'X/...' not found"). NOTE: import-alias bare qualified refs (`(import [(util u) …])` → bare `u/helper`) are still owner-scoped-keyed (`<owner>.alias`) and so resolve only via `<owner>.alias/...`; the spec §8.3.4 `str/split` bare form is a separate, pre-existing gap NOT in W-Module scope.

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

## Embedded agent (`src/agent/`, S88 Phase 5 Wave 3 — Advisor MVP core)

The embedded LLM advisor lives entirely in `src/agent/`, fully
`#[cfg(feature = "agent")]` — **feature-off the module does not exist and the
default `cargo build` / `cargo nextest run` never compile rig** (the ~9s suite
stays agent-free). `design/int/agent.md` is the design.

- **Feature + deps.** `agent = ["dep:rig-core", "dep:tokio", "dep:serde_json"]`
  (root `Cargo.toml`). `rig-core` is `optional`, `default-features = false`,
  `features = ["reqwest", "native-tls"]` — the smallest set that compiles the
  completion API + the anthropic/ollama providers. **native-tls, NOT rustls:**
  the rustls path pulls `aws-lc-rs` (a heavy C TLS backend, ~30 MB of build
  artifacts + a C toolchain); native-tls links the system OpenSSL — a far
  lighter agent footprint. tokio is a current-thread runtime only (`rt` +
  `macros`) — `agent_turn` `block_on`s one async rig completion per loop step.
- **The `AgentModel` membrane (object-safety).** The design names the model
  handle `Box<dyn rig::completion::CompletionModel>`, but rig's `CompletionModel`
  is **NOT object-safe** in 0.39.0 (associated types + `Clone` bound + async
  methods). We preserve the §6 intent with a thin object-safe internal trait
  `AgentModel` (`agent/types.rs`): the stub and each rig-backed provider
  implement it; rig's `CompletionModel` is still the wire boundary, one layer
  below, inside `provider.rs`. The lib name is `rig_core` (not `rig`) — imports
  are `use rig_core::...`. Correction filed as FIXME 0427 `target: /design`.
- **Module map.** `types.rs` (neutral vocabulary + `AgentModel` + `AgentState`);
  `provider.rs` (runtime provider selection — anthropic/ollama/stub by
  `CRANELISP_AGENT_PROVIDER`; the rig membrane impl + tokio bridge);
  `request.rs` (the one place coupled to rig's `CompletionRequest`/`Message`/
  tool-call shapes); `harvest.rs` (the push-context assembler, §5 ladder);
  `primer.rs` + `primer.txt` (the always-on language primer, `include_str!`);
  `pull.rs` (pull-as-visible-commands + the read-only allowlist consent gate);
  `stub.rs` (the deterministic test `AgentModel`, the testing linchpin);
  `mod.rs` (the classifier + the real `agent_turn` model↔tool loop).
- **Wiring.** `CompilerSession.agent: Option<AgentState>` (`#[cfg]`-gated, zero
  bytes feature-off). `main.rs` threads the resolved `--agent` flag
  (`agent_enabled`) into `s.enable_agent(...)` in the REPL arm only (agent is
  REPL-only). Dormant (no reachable provider) ⇒ `/ask` renders the U6 notice.
- **Testing.** The stub is selected e2e by `CRANELISP_AGENT_PROVIDER=stub` +
  `CRANELISP_AGENT_STUB_SCRIPT=<fixture>` (a line DSL: `tool: <name> <arg>` /
  `done: <prose>`). Lane A e2e lives in `tests/agent.rs` (`--features agent`);
  request-content assertions are `#[cfg(test)]` unit tests in `agent/mod.rs`
  (the stub captures every `AgentRequest`). Run: `cargo nextest run --features
  agent --test agent` (e2e) + `... --lib 'agent::'` (unit).
- **DEFERRED (R5 release valve, → S89/3b).** Spec-grep retrieval
  (`agent/spec_grep.rs`) and the telemetry skeleton (`agent/telemetry.rs`) are
  NOT built — the MVP acceptance holds without them (primer + harvest carry the
  grounding). Build/Document write modes + the validator are S89.

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
- `cranelisp-backend`: depends on `cranelisp-types`, `cranelisp-intrinsics` (+ `cranelisp-primitives`, transitive) — the backend-emitted runtime library
- `cranelisp-intrinsics` + `cranelisp-primitives` (the former `cranelisp-runtime`, split at D43): depend on `cranelisp-platform`, `cranelisp-types`
- `cranelisp-platform`: no dependencies (except `std`)
- `cranelisp` (binary): depends on all above

No circular dependencies. Cargo enforces this at build time.

## Debugging Cross-Crate Failures

When an integration test fails and the root cause could be in any crate, follow the isolation process in `tests/CLAUDE.md` §"Isolating Cross-Crate Failures". The key principle: write a crate-level unit test that asserts the expected state at the crate boundary. If it passes, the bug is in the integration wiring. If it fails, fix the crate.
