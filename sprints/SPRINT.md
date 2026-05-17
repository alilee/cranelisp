# Sprint 67: Edge settlement — facade definition + implementation reconciled

**Status**: PHASE 5 LANGUAGE (ACTIVE)

**Goal**: Settle the facade definition AND the implementation at every crate/component edge — completely and with confidence — by reconciling every facade↔`cargo public-api` drift identified in the post-S66 audit. After this sprint, edges are a frozen contract enforced by `cargo public-api` baselines; interior uplift can proceed without surprise at the seams.

## Scope

### In scope

For each of the 7 crates + the `int` binary, drive facade↔pub-api drift to **zero**, where each item is dispositioned in exactly one of two directions:

- **Pull facade to reality** (PFR): the implementation is correct; the facade text is updated to match. Used for cosmetic renames, intentional internal surface, and post-Decision implementation refinements that the facade didn't catch up with.
- **Push implementation to facade** (PIF): the facade-stated intent is correct; the implementation is moved to match. Used for Decision close-outs, forbidden-pattern residues, and surface that should never have been exposed.

Every disposition is explicit, recorded in the per-crate audit row, and signed off by `/arch` in Phase 2.

**Substantive gaps (PIF candidates)**:
- `Code` enum relocation from `src/code.rs` → `cranelisp-backend` (Decision 41 close-out)
- Typed `CompilationError` + `LinkerError` migration; `Linker::load_object` returns `LinkerArtefact`; `compile_to_object` as free function (Decision 37/41 close-out). DTOs land in `cranelisp-backend` (not types) per REV-4 — Principle 15 single-consumer placement.
- Delete `backend::primitives_inline::primitive_for_trait_method(TraitName, Symbol, TypeName)` — D43 `facades/backend.md` §Non-goals explicitly forbids this pattern; residue from S66 close
- **`operators.rs` full retirement + trait-keyed dispatch full removal** (FIXME 0150 close-out, D43 full close) — table row 7 pulled in per user direction "no further facade deferral"
- **`ops::cranelisp_op_*` (10 fns) retirement from intrinsics** (table row 31) — D43 retirement candidates; consumer audit (REV-5) precedes deletion
- `TypeCheckEnv` **full narrowing 30→2** — facade prescribes 2 methods, implementation exposes ~30; FIXME 0172 short-name fallback chains in `defining_module_for` / `fqtn_for_bare_type_name` resolved as part of this. No two-phase split — REV-2 reversed per user direction.
- Int `describe_symbol` / `list_user_definitions` / `module_imports` / `module_exports` / `symbol_source` / `symbol_sexp` / `symbol_clif` / `symbol_disasm` family — read-side-only against `shared.symbol_tables` + `shared.introspection` (REV-3); SharedState interior split remains genuinely interior (not facade-deferred).
- **`io_trace::*` relocation from `cranelisp-intrinsics` → `int`** (table row 30, Decision 40 close, FIXME 0103 io_trace half) — table row pulled in per user direction
- **`trace::cranelisp_trace_*` + observer relocation from `cranelisp-intrinsics` → `int`** (table row 33, Decision 40 close, FIXME 0103 trace half) — table row pulled in per user direction
- Primitives string/vec physical relocation from intrinsics (FIXME 0180 — Cargo cycle dissolved post-runtime retirement)
- Primitives `PRIMITIVES_TABLE: LazyLock<SymbolTable>` static (FIXME 0159) — facade prescribes one public item; pub-api shows 21 extern fns
- `PlatformError` adoption final residue; `CLType::from_repr` if facade-required
- `re_register_module` forwarding method on `CompilerSession` (table row 45) — trivial PIF

**Backend cache sub-facade** (REV-1 reversed per user direction): full `facades/backend-cache.md` authoring AND per-row absorption land in S67. Volume handled by dedicated cache wave; see Waves §Wave 4.

**FQTypeName binding migration (FIXME 0151).** `facades/types.md §232` lifted FQTypeName from aspirational → binding in S65 W2; source has not been migrated. Multi-crate: every API past frontend's resolution stage that names a type uses `FQTypeName` (exceptions: frontend syntactic-stage; receiver-pinned `SymbolTable::get_type`; reverse-lookup `Type::from_name`/`type_name`). Closes FIXME 0151.

**SharedState facade alignment (FIXME 0176 broader scope reclassified).** `facades/int.md` line 119 prescribes an 8-field `SharedState`; `src/session_v4.rs:573` has ~13+ fields (`module_sexps`, `suspend_states`, `cache_dir`, `compiled_o_paths`, `promote_nice_workers`, `cached_modules`, `file_to_module`, `cache_state`, `kept_dlls` typed mismatch, plus more). Per-field PFR/PIF disposition by /arch in Phase 3 Wave 0; PIF-prefer (narrow impl to facade) for items that are truly per-form runtime state and don't belong in worker-shared subset; PFR (widen facade) only where current shape is correct. `worker.rs` file decomposition remains genuinely interior (FIXME 0109, no `pub` surface change).

**Cosmetic drifts (PFR candidates — facade rewrite)**:
- Frontend: `StructuralDecls` → `ExtractedDeclarations` rename; `parse_defmacro` pub-at-root vs `pub(crate)`; `expand_quote_template`; `EXPANSION_DEPTH_LIMIT` const documented
- Typecheck: `View<'_, C, L>` → `ClusterRead<'_, C, L>` / `ClusterWrite<'_, C, L>` naming; `register_builtins` signature (`&DashMap<...>` + `&AtomicU32`); `CheckResult` shape pared to `display`+`warnings`
- Backend: `cache::{manifest, object, serialize}` submodule given a facade footprint (or absorbed into a `backend-cache.md` sub-facade); `jit::Jit` method-set pared or facade widened; `compiler::FnCompiler` / `CompileContext` / `resolve_func_arity` / `resolve_got_target` / `got_data_symbol_name` / `TracedFnInfo` / `MatchContext` etc. dispositioned per item; `exe::generate_startup_object` named
- Intrinsics: `consume_sexp` / `consume_slist` / `consume_closure` / `consume_vec_of_string` / `consume_vec_with` / `consume_trace_call` dispositioned (per-type drop helpers); `io_trace::*` named or moved per Decision 40 status
- Platform: `PlatformFn` field set documented (manifest extensions); `OwnedPlatformFnDescriptor.param_names` documented; `manifest_to_descriptors` return tuple documented; `STRING_HEADER_BYTES` / `HEAP_HEADER_SIZE` const list updated
- Int: `wait_for_*_codegen` → `wait_*_complete` rename; `process_cluster` / `insert_cluster` location named (lives in `cluster.rs`)
- Types: pass — facade matches; record verification

**Enforcement mechanism**:
- Per-crate `public-api.txt` baselines confirmed current; `public_api_check_runs_against_all_seven_crates` test remains tight
- Author a facade-compliance test (or document the manual process) that asserts every `pub` item in each `public-api.txt` is named in the corresponding facade, and every facade-cited name appears in pub-api
- `design/arch/CLAUDE.md` updated with the disposition discipline: future edge changes require explicit baseline diff + facade update in the same change-set

### Out of scope (deferred)

- **Interior uplift** of any crate — that is the explicit S68+ purpose. This sprint settles edges only.
- **0098 ResolutionGap / CheckError / ExpansionError residual** — Phase 4 carries; not edge-settlement.
- **0099 GotObserver consumer-half** — int consumer-side; not edge-shape question.
- **0109 int decomposition** (split `session_v4.rs` + `worker.rs`) — genuinely interior structural; no `pub` surface change. (SharedState shape alignment IS in scope per above — that is edge; file decomposition is not.)
- **`worker.rs` file decomposition + `session_v4.rs` file split + broader file relocations beyond what edge alignment requires** — interior structural; no facade-cited file boundary changes.
- **HostCallbacks fuller shape (Decision 31 callback support)** — facade explicitly conditions on `Fn a b` ABI landing; not a deferral of the current facade.
- **0181 cross-module macro stack overflow** — typecheck interior bug; doesn't touch edges.
- **0121 / 0142 / 0145 / 0148** S64 baseline carries — independent of facade work.
- **0116–0149 harvest** — `tests/legacy/` relocation; methodology arc, S68+.
- **Cosmetic facade rename pass beyond what edge settlement requires** — anything not driven by an audit row is curatorial polish, not settlement.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0096 | /design (backend) | open | Stale subordinate doc archival — folds into backend facade refresh |
| 0099 | /dev (int) | open | GotObserver consumer-half — deferred to S68; flagged as interior |
| 0100 | /dev (multi) | open | Single-consumer type relocation — verify edge-clean during disposition |
| 0102 | /dev (runtime — retired) | open | Re-target or close: runtime crate gone; may dissolve |
| 0106 | /design (arch) | open | Archive PlatformRegistry removal — folds into platform facade refresh |
| 0107 | /dev (platform) | open | `OwnedPlatformFnDescriptor` `#[non_exhaustive]` — verify and close |
| 0151 | /arch | open | FQTypeName implementation — deferred S68+ |
| 0159 | /dev (primitives, int) | open | `PRIMITIVES_TABLE: LazyLock<SymbolTable>` static — in scope |
| 0162 | /dev (int) | open | Per-crate doc drift from S66 fn_ptr rollback (int side) |
| 0163 | /dev (backend) | open | Per-crate doc drift from S66 fn_ptr rollback (backend side) |
| 0164 | /dev (typecheck) | open | Per-crate doc drift from S66 fn_ptr rollback (typecheck side) |
| 0172 | /dev (typecheck) | open | Short-name fallback chains in checker.rs — closes via `TypeCheckEnv` narrowing |
| 0173 | /dev (typecheck) | open | Remove `CheckPass` and relocate accumulator — verify whether edge-clean |
| 0175 | /arch (frontend) | open | `expand` invocation gap — folds into frontend facade refresh |
| 0176 | /dev (int) | open | Partial close: `describe_symbol` family only; SharedState split deferred S68+ |
| 0177 | /dev (typecheck) | open | check_forms cross-form state regression — verify edge-clean |
| 0178 | /arch (intrinsics) | open | Intrinsics inventory + forbid conditional registration — folds into intrinsics facade refresh |
| 0179 | /dev (typecheck) | open | Cluster read-union staging — verify edge-clean |
| 0180 | /dev (primitives) | open | String/vec physical relocation — in scope |

## Architecture review (Phase 2)

**Verdict**: PASS-WITH-REVISIONS — 2026-05-15 — `/arch` (Opus 4.7 1M)

The audit's substantive structure stands; verification surfaces five corrections + revisions that must be applied before Phase 3 fires.

### Audit verification summary — corrections + missing findings

**Types** — confirmed clean at edge. `View<'a, C, L>` present at pub-api.txt:1866 with `single` + `union` constructors; `SymbolTable<C, L>`, `FQSymbol`, `FQTypeName`, `ModuleFullPath`, `ResolutionGap`, `PlatformError`, `ErrorLocation`, `ParsedEntry`, `DefmacroInfo` all present. No drift. **Add `LinkerError`** — the typecheck/types facade names it as types-hosted (per FIXME 0154 resolution); a `grep` of `public-api.txt` for `LinkerError` returns zero — **MISSING FINDING** in prior audit. Either: (a) facade text changes to remove the "lives in `cranelisp-types`" claim and relocates `LinkerError` to `cranelisp-backend` (where the Linker is); or (b) Wave 0 authors `LinkerError` in `cranelisp-types`. Both directions defensible; user permits SPLIT.

**Frontend** — audit correct on `ExtractedDeclarations` rename, `parse_defmacro` pub-at-root, `expand_quote_template`, `EXPANSION_DEPTH_LIMIT`. **Additional cosmetic drift**: `synthesize_macro_clause_defn`, `flatten_begin`, `is_begin`, `is_defmacro`, `next_synthetic_span` all pub at root — facade silent. PFR cluster.

**Typecheck** — audit correct on shape but **mis-stated precision**: `ClusterContext::current_symbol_table*` return `ClusterRead`/`ClusterWrite` newtypes that wrap (Cluster vs Live cases) + provide `.view()` and `Deref` respectively. Facade `typecheck.md` §"Cluster check scaffolding" lines 59–60 prescribe **direct** `View<'_, C, L>` / `&mut SymbolTable<C, L>` return. The wrapper layer is real surface drift (PFR — wrapper is intentional locality-correctness machinery; facade widens to admit it). **Confirmed substantive**: `TypeCheckEnv` exposes 30+ methods (pub-api.txt:163–202); facade prescribes `new` + `next_type_id` only — PIF target. `CheckResult` has `{display, warnings}` only at pub-api.txt:121–123 vs facade comment "/* annotated_ast, scheme, callees, method_resolutions, type_defs, mono_defns */" — but per Decision 44 third amendment, side products land on staging Def fields, not on CheckResult. **The facade is correct as a direction**; the comment is stale. PFR (rewrite the explanatory comment) or PIF-cosmetic. `register_builtins(modules: &DashMap, next_id: &AtomicU32)` vs facade `(table: &mut SymbolTable)` — facade text reflects pre-cluster-atomic shape; PFR.

**Backend** — audit substantively correct + **understated**. Confirmed: `compile_to_module` returns `Result<CompilationResult, CranelispError>` (pub-api.txt:end) not facade's `Result<(), CompilationError>`; no `LinkerArtefact`/`ObjectArtefact`/`CompilationError`/`LinkerError`/`load_object` (free fn)/`compile_to_object`/`Code` enum at the backend boundary. `Code` lives at `src/code.rs:72` (verified). `Linker::get_symbol` returns `Option<*const u8>` (pub-api.txt for `linker.rs`) — D37 violation. `primitive_for_trait_method(TraitName, Symbol, TypeName) -> Option<&'static str>` present at pub-api.txt for `primitives_inline` — D43 forbidden pattern. cache submodule footprint: ~30 items across `cache::{linker,manifest,object,serialize}` AND a root-level `cache::` re-export layer that duplicates each submodule item — **doubled**, not 30. **Additional finding**: `CompileContext`, `FnCompiler`, `TracedFnInfo`, `MatchContext`, `MATCH_EXHAUSTION_TRAP`, `resolve_func_arity`, `resolve_got_target`, `got_data_symbol_name` (in two places — `compiler::` and `cache::`), `CodeFinalizer` trait + impls on `JITModule`/`ObjectModule`, `intrinsic_symbols()`, `jit_free_memory_call_count()`, `CompileArtifacts`, `IntrinsicFuncIds`, `IntrinsicIds`, `IntrinsicSymbol`, `FunctionArtifacts`, `CompilationResult`, `declare_intrinsics_generic`, `Jit::*` (10+ methods) — every one a PFR or PIF call. Backend cache submodule is the **largest single facade gap** in the workspace; absorption into one facade in a single sprint is **infeasible**.

**Primitives** — audit correct that `PRIMITIVES_TABLE` does not exist (pub-api.txt has zero `LazyLock<SymbolTable>`). **Re-export situation amended**: `string::` and `vec::` submodules in `cranelisp-primitives` (pub-api.txt:53–70) re-export from intrinsics — these are at-root re-exports (lines 2–17). Audit said "Cargo cycle dissolved post-runtime retirement"; verified — `crates/cranelisp-primitives/Cargo.toml:8` shows `cranelisp-intrinsics = { path = ... }` plain dep, no cycle. Physical relocation now structurally possible (FIXME 0180 close path is clear). **21 extern fns is correct** (verified: 16 ring0 + 4 conversion + sconcat). Two PIF candidates remain: `PRIMITIVES_TABLE` static; string/vec physical relocation from intrinsics.

**Intrinsics** — audit substantively correct. `io_trace::*` (`IoTracePayload`, `IoTraceTag`, `IoTraceEvent`, `FlushGuard`, `format_event_line`, `record_event`, `install_panic_hook`, `flush_to_stderr`, `dump_*_buffer`, `publish_thread_buffer`, `trace_instant_anchor`, `IO_TRACE_BUFFER_CAPACITY`) present at pub-api.txt:111–249. Per Decision 40, these belong in `int` not intrinsics — but D40 has FIXME 0103 tracking and was **explicitly deferred from S67 scope** by FIXME 0178 wording (intrinsics inventory + forbid conditional registration). Disposition: **DEFER** io_trace relocation; PFR-document its current intrinsics residence + cite D40 as the future destination. `consume_*` drop helpers (pub-api.txt:15–23) are Rust-callable, not extern; facade says backend emits drop glue. PFR (facade widens to admit per-type Rust drop helpers as a separate surface from backend-emitted drop glue). `ops::cranelisp_op_*` (pub-api.txt:255–264) — D43 retirement candidates per FIXME 0150; **add to PIF list**.

**Platform** — audit correct. `CLType::from_repr` missing from pub-api.txt (only `to_raw` present); facade prescribes both. **PFR**: from_repr was never required by host-side code; facade narrows. `PlatformFn` field bloat (12 fields vs facade's 7) — PFR documents the manifest-extension fields. `manifest_to_descriptors` returns `(String, String, Vec<...>)` tuple — facade says `Vec<OwnedPlatformFnDescriptor>` plain. The two leading strings are platform-name + version; PFR documents. `STRING_HEADER_BYTES`/`HEAP_HEADER_SIZE` consts present at pub-api.txt:222/228 but facade only lists `ABI_VERSION`/`IO_TAG_*` — PFR. `OwnedPlatformFnDescriptor::param_names` field present; PFR.

**Int (binary)** — audit substantively correct. `describe_symbol`, `list_user_definitions`, `module_imports`, `module_exports`, `symbol_source`, `symbol_sexp`, `symbol_clif`, `symbol_disasm`, `format_command_result`, `current_repl_module`, `set_current_repl_module`, `set_repl_input_active` all absent from `src/` (grep returns zero). `format_error` is a free function at `main.rs:90`, not a `CompilerSession` method. `process_cluster`/`insert_cluster` live in `src/cluster.rs:177/248`, not `session_v4.rs`. `wait_inmem_complete`/`wait_object_complete` are the actual names (pub at `scheduler.rs:930/1021` AND `session_v4.rs:3228/3238`). All confirmed substantive PIF (describe_symbol family) or PFR (location, naming) per audit. **`re_register_module`** present at `scheduler.rs:412` but as `CompileScheduler` method, not `CompilerSession` — partial PIF.

### Per-row disposition table

| # | Item | Facade location | Pub-api / src location | Dir | Owning skill | Notes |
|---|---|---|---|---|---|---|
| 1 | `Code` enum | `backend.md` §"`Code`" | `src/code.rs:72` | PIF | /dev (backend) | D41 close-out; physical relocation; ripple check item below |
| 2 | `compile_to_module` return | `backend.md` §"Free functions" | backend pub-api `CompilationResult` + `CranelispError` | PIF | /dev (backend) | Add `CompilationError` enum; remove `CompilationResult` (or rename to private); D37+D41 |
| 3 | `load_object` free fn + `LinkerArtefact` | `backend.md` §"Free functions" + §"Return shapes" | backend pub-api `Linker::load_object` returns `Result<(), CranelispError>` | PIF | /dev (backend) | D41 + D37 |
| 4 | `compile_to_object` free fn + `ObjectArtefact` | `backend.md` §"Free functions" | absent from backend pub-api | PIF | /dev (backend) | D41 |
| 5 | `LinkerError` location + `Linker::get_symbol` return | `backend.md` §"Errors" + types.md | backend `linker.rs` `Option<*const u8>`; absent from types pub-api | SPLIT | /arch + /dev (backend) | Author in types (Wave 0) OR relocate to backend; facade currently claims types; **/arch decides Wave 0** |
| 6 | `primitive_for_trait_method` | `backend.md` §"Operator special-casing is forbidden" | `cranelisp-backend::primitives_inline::primitive_for_trait_method` | PIF | /dev (backend) | D43 forbidden pattern; delete |
| 7 | `operators.rs` deletion residue | `backend.md` §"Forbidden patterns" | `primitives_inline.rs` present (renamed) | PFR | /design (backend) | Confirm renamed; rest of D43 still owed per FIXME 0150 — DEFER to S68 |
| 8 | backend cache submodule footprint | `backend.md` (silent) | pub-api.txt:1–end of cache section, ~60 items doubled | PFR (sub-facade) | /design (backend) | **Author `facades/backend-cache.md` sub-facade THIS sprint**; full row absorption defers to S68 — see scope revision below |
| 9 | `jit::Jit` method-set | `backend.md` §"`Jit`" | backend pub-api `Jit::*` (10+ methods) | PFR | /design (backend) | Facade widens to admit current method-set OR mark methods `pub(crate)`; PFR-only sufficient |
| 10 | `compiler::FnCompiler`, `CompileContext`, `MatchContext`, `TracedFnInfo` | absent from facade | backend pub-api | PFR | /design (backend) | Facade documents as internal-but-exposed (tests use them) |
| 11 | `resolve_func_arity`, `resolve_got_target`, `got_data_symbol_name`, `MATCH_EXHAUSTION_TRAP` | absent | backend pub-api | PFR | /design (backend) | Either mark internal-exposed OR `pub(crate)`-narrow |
| 12 | `exe::generate_startup_object` | absent | backend pub-api | PFR | /design (backend) | Document as link-orchestration assist |
| 13 | `CodeFinalizer` trait + impls on JITModule/ObjectModule | absent | backend pub-api | PFR | /design (backend) | Decision 38 surface — document |
| 14 | GOT-observer (`register_got_observer`, `GotEvent*`) | `backend.md` §"GOT-population observation" | present at pub-api `got_observer::*` | PFR | /design (backend) | Already aligned; confirm name correspondence |
| 15 | `IntrinsicSymbol`, `IntrinsicFuncIds`, `IntrinsicIds`, `intrinsic_symbols()`, `declare_intrinsics_generic` | absent | backend pub-api jit module | PFR | /design (backend) | Backend-internal helpers; document |
| 16 | `ExtractedDeclarations` (rename from `StructuralDecls`) | `frontend.md` (presumed `StructuralDecls`) | `module_extract::ExtractedDeclarations` | PFR | /design (frontend) | Rename in facade |
| 17 | `parse_defmacro`, `is_defmacro`, `is_begin`, `flatten_begin`, `synthesize_macro_clause_defn`, `next_synthetic_span`, `expand_quote_template`, `EXPANSION_DEPTH_LIMIT` | facade silent or `pub(crate)` | frontend pub-api root + defmacro module | PFR | /design (frontend) | Document as macro-resolver helpers |
| 18 | `DefmacroInfo`, `MacroClause` re-exports at root | facade silent | frontend pub-api:2–3,9–10 | PFR | /design (frontend) | Document re-export policy |
| 19 | `check_forms` signature | `typecheck.md` §"Free function" | typecheck pub-api:210 | — | — | Match; no drift |
| 20 | `ClusterContext`, `ClusterRead`, `ClusterWrite` shape | `typecheck.md` §"Cluster check scaffolding" line 59–60 | typecheck pub-api:50–99 | PFR | /design (typecheck) | Facade widens: `current_symbol_table()` returns `ClusterRead`, which `.view()`s to `View`; `current_symbol_table_mut()` returns `ClusterWrite` which derefs to `&mut SymbolTable`. Document the wrapper layer. |
| 21 | `TypeCheckEnv` 30+ methods | `typecheck.md` §"Cluster check scaffolding" prescribes 2 | typecheck pub-api:162–209 | PIF | /dev (typecheck) | FIXME 0172 short-name fallback chains close; narrow to facade — but verify with /design typecheck first whether the methods serve real test/REPL access patterns. **Scope check**: 30→2 in one sprint may be too aggressive. Recommend PFR-document-then-PIF-narrow split across S67 (document + remove dead methods) + S68 (algorithmic consolidation). |
| 22 | `CheckResult` shape stale comment | `typecheck.md` line 107 | typecheck pub-api:121–123 | PFR | /design (typecheck) | Replace stale comment with D44 third-amendment shape |
| 23 | `register_builtins` signature | `typecheck.md` §"Builtin registration" line 80 | typecheck pub-api:5 / 212 | PFR | /design (typecheck) | Facade reflects pre-cluster-atomic shape; update to `(modules: &DashMap, next_id: &AtomicU32)` per Decision 38 |
| 24 | `SymbolTableEnsureOutcome`, `install_symbol_table_ensure_hook`, `emit_symbol_table_ensure`, `SymbolTableEnsureHook` | `typecheck.md` §"Trace hooks" | typecheck pub-api:6–30, 100–120 | PFR | /design (typecheck) | Document |
| 25 | `ReplSnapshot` shape | `typecheck.md` (used in invariant 7) | typecheck pub-api:146–161 | PFR | /design (typecheck) | Document fields |
| 26 | `PRIMITIVES_TABLE: LazyLock<SymbolTable>` | `primitives.md` §"Public surface" | absent (21 extern fns instead) | PIF | /dev (primitives) + /dev (int) | FIXME 0159; introduce static, demote extern fns to `pub(crate)` |
| 27 | string/vec re-exports from intrinsics | `primitives.md` (silent on re-exports) | primitives pub-api:53–70 + 2–17 | PIF | /dev (primitives) | FIXME 0180; physical relocation now structurally possible |
| 28 | `ring0_jit_symbols()` free fn | absent from facade | primitives pub-api:50, 76 | PFR | /design (primitives) | Document or `pub(crate)` (used by int session init) |
| 29 | `consume_sexp/slist/closure/vec_of_string/vec_with/trace_call/io_tree` | intrinsics.md §"Drop glue" says backend-emitted | intrinsics pub-api:15–23 | PFR | /design (intrinsics) | Facade widens: per-type Rust drop helpers ARE intrinsics; "backend-emitted" applies to user-defn drop glue only |
| 30 | `io_trace::*` (15+ items) | intrinsics.md §"IO observation" — should be int per D40 | intrinsics pub-api:111–249 | DEFER (S68) | /dev (int) + /design (intrinsics) | FIXME 0103 tracking; **explicitly out of S67 scope** per SPRINT.md "Out of scope" amend |
| 31 | `ops::cranelisp_op_*` (10 fns) | intrinsics.md (silent — these are pre-D43 residue) | intrinsics pub-api:255–264, 427–436 | PIF | /dev (backend?) — see notes | D43 retirement per FIXME 0150; these duplicate `primitives::ring0::*` operations under different names. **/arch flags**: whose deletion? Backend was the consumer pre-D43; post-D43 backend uses primitives::ring0. /design + /dev backend confirm consumer-free, then /dev (intrinsics) deletes. |
| 32 | `take_runtime_error`, `trace_anchor`, `is_rc_trace_enabled`, `consume_io_tree`, `consume_shallow`, `rc_trace`, `dec_shallow_io`, `dealloc`, `is_live`, `bytes_*`, `alloc_count`, `dealloc_count`, `reset_counts`, `alloc_with_rc`, `alloc_string`, `read_string_as_str` | intrinsics.md §"RC primitives" §"Stats accessors" §"Drop glue" §"Panic helper" | intrinsics pub-api | PFR | /design (intrinsics) | All present; confirm facade enumerates each |
| 33 | `trace::cranelisp_trace_*` (10 fns), `trace_anchor` | absent | intrinsics pub-api:307–319 | DEFER (S68) | /dev (int) | FIXME 0103 — trace observer relocation to int |
| 34 | `IoEvent/IoEventTag/IoObserver/register_io_observer/emit/trace_anchor` | intrinsics.md §"IO observation" | intrinsics pub-api:27–110 | PFR | /design (intrinsics) | Already aligned; confirm |
| 35 | `CLType::from_repr` | platform.md §"CLType" line 21 | absent from platform pub-api | PFR | /design (platform) | Facade narrows; host-side never used `from_repr`, only `to_raw` |
| 36 | `PlatformFn` field set (12 fields vs facade 7) | platform.md §"Platform manifest" | platform pub-api:184–198 | PFR | /design (platform) | Document `jit_name_len`, `name_len`, `docstring_len`, `param_name_count`, `param_names`, `param_name_lens`, `type_sig_len` |
| 37 | `manifest_to_descriptors` tuple return | platform.md §"Host-side descriptors" line 119 | platform pub-api:253 returns `(String, String, Vec<...>)` | PFR | /design (platform) | Document name + version leading strings |
| 38 | `OwnedPlatformFnDescriptor::param_names` | platform.md §"Host-side descriptors" silent | platform pub-api:173 | PFR | /design (platform) | Document field |
| 39 | `STRING_HEADER_BYTES`, `HEAP_HEADER_SIZE` consts | platform.md §"Public consts" silent | platform pub-api:222, 228 | PFR | /design (platform) | Document |
| 40 | `call_effect_thunk`, `derive_jit_name` free fns | platform.md §"manifest" prescribes `derive_jit_name`; `call_effect_thunk` silent | platform pub-api:251–252 | PFR | /design (platform) | Document `call_effect_thunk` |
| 41 | `HostContext`, `HostCallbacks` shape | platform.md §"Host context" prescribes both; `HostCallbacks` fuller than current | platform pub-api:146–166 (HostCallbacks has only `alloc` field) | PFR | /design (platform) | Narrow facade OR widen impl per Decision 31 callback support — DEFER fuller HostCallbacks to whenever `Fn a b` ABI lands; document the `alloc` minimum |
| 42 | `describe_symbol`, `list_user_definitions`, `module_imports`, `module_exports`, `symbol_source`, `symbol_sexp`, `symbol_clif`, `symbol_disasm`, `current_repl_module`, `set_current_repl_module`, `set_repl_input_active`, `format_command_result`, `format_error` (as method) | `int.md` §"Introspection accessors" + §"CompilerSession" lines 70–94 | absent from `src/` | PIF | /dev (int) | FIXME 0176 partial close — `describe_symbol` family only; SharedState split (`worker.rs` split) DEFERRED S68. **Scope check below**. |
| 43 | `process_cluster`/`insert_cluster` location | `int.md` says `CompilerSession` methods | live in `src/cluster.rs:177/248` as free fns taking `&mut CompilerSession` | PFR | /design (int) | Document as free-fn-with-session shape OR PIF-relocate as methods; both serve. PFR cheaper. |
| 44 | `wait_for_inmem_codegen`/`wait_for_object_codegen` naming | `int.md` lines 61–62 | `wait_inmem_complete`/`wait_object_complete` at `session_v4.rs:3228/3238` | PFR | /design (int) | Update facade naming |
| 45 | `re_register_module` location | `int.md` line 36 as `CompilerSession` method | `scheduler.rs:412` as `CompileScheduler` method only | PIF (small) | /dev (int) | Add thin `CompilerSession` forward; trivial |

### Decision close-out plan

- **Decision 37 (CompilationError typing)** — closes in S67 via rows 2–5. Add `CompilationError` enum to `cranelisp-backend`; remove `CranelispError::CodegenError { message: ... }` strings at the backend boundary; verify `Linker::get_symbol` returns `Result<*const u8, LinkerError>` (row 5).
- **Decision 41 (Code enum + LinkerArtefact + per-symbol JIT direct writes)** — closes in S67 via rows 1–4, 13. Code relocates; LinkerArtefact + ObjectArtefact land; CodeFinalizer documented. **/arch authors close-out amendment** to `decisions/0041-*.md` adding "status: closed" pointer post-S67 close.
- **Decision 43 (runtime split + trait-keyed dispatch forbidden)** — partial close in S67 via row 6 (`primitive_for_trait_method` delete) + row 31 (`ops::cranelisp_op_*` retirement). **Operators.rs deletion + full trait-dispatch retirement (FIXME 0150) remains open** with target S68. **/arch amends D43 §Non-goals** with "primitive_for_trait_method removed S67; full operators.rs retirement S68".
- **Decision 35 (Code enum location)** — already closed in spirit by D41; row 1 lands the physical move. **/arch confirms `decisions/0035-*.md` "amended Sprint 67 — physical move landed" pointer**.
- **Decision 40 (trace/io_trace relocate to int)** — REMAINS OPEN, S68+ target via FIXME 0103. Row 30 + 33 explicitly DEFER. No /arch action this sprint.
- **Decision 44 (cluster-atomic typecheck)** — already in source post-S66 W3a. Rows 19–25 are facade-text-catch-up (PFR). No Decision amendment needed; the W3a-β trace implementations are downstream interior.

### Cross-crate interface authoring (Wave 0)

`/arch` Phase 3 Wave 0 authors in `crates/cranelisp-types/`:

1. **`CompilationError` enum** — variants per `facades/backend.md` §"Errors" (SymbolNotCompilable, CodegenFailed, ModuleError) — **OR** /arch decides this lives in `cranelisp-backend` (Principle 15 — single-consumer per error type; backend is constructor; `int` matches). **Recommendation: author in `cranelisp-backend/src/error.rs`** because `int` is the only matcher and backend is the only constructor — no multi-consumer pull. Update facade text accordingly (PFR).
2. **`LinkerError` enum** — row 5 SPLIT. **Recommendation: author in `cranelisp-backend`** for the same reason. The facade text in `backend.md` §"Errors" already enumerates the variants; types.md needs the §"Errors and warnings" entry deleted.
3. **`LinkerArtefact`, `ObjectArtefact`** — author in `cranelisp-backend` (constructor + returner). Backend.

No new `cranelisp-types` types required. /arch does the facade-text reconciliation (deleting the types.md §"Errors and warnings" `LinkerError` entry; documenting the backend-local location) in Phase 3 Wave 0.

### Scope adjustment recommendations

Three revisions required before Phase 3 fires:

**REV-1 (backend cache submodule)**: SPRINT.md "In scope" line 31 calls for facade absorption "or absorbed into a `backend-cache.md` sub-facade". The verification surfaces ~60 items (doubled across `cache::` root + submodules). **Sub-facade authoring in S67 is the only tractable path**; full row-by-row absorption defers to S68. **Add to SPRINT.md "In scope"**: "Author `facades/backend-cache.md` THIS sprint — names every cache pub item, dispositions PFR/PIF; per-row text refinement defers to S68." **Add to "Out of scope"**: "Per-row backend cache disposition beyond sub-facade authoring."

**REV-2 (TypeCheckEnv narrowing)**: SPRINT.md line 22 prescribes "30→2" narrowing in S67. Verification shows the 30 methods serve REPL introspection (`all_type_defs`, `lookup_constructor_type`, `module_table`, etc.) — not all dead code. **Recommend two-phase**: S67 = PFR-document each method + remove confirmed-dead ones (10–15); S68 = algorithmic consolidation (e.g., FIXME 0172 short-name fallback chains; merging `module_table` + `module_table_cloned`). **Amend SPRINT.md line 22**: "TypeCheckEnv narrowing — PFR-document current 30, identify + remove confirmed-dead (target ~15 remaining); algorithmic narrowing to facade-prescribed 2 defers to S68 via /dev (typecheck) decomposition."

**REV-3 (int describe_symbol family)**: SPRINT.md line 23 + FIXME 0176 close-out. Verification shows the family has hidden dependencies on the SharedState split (`worker.rs` decomposition, `session_v4.rs` interior structure) that are explicitly deferred S68 (FIXME 0109, FIXME 0176). **`describe_symbol` family CAN land as `CompilerSession` methods that read from `shared.symbol_tables` + `shared.introspection`** without touching the SharedState interior split — it's a read-side accessor surface. **Confirm with /design (int) Phase 3 that the implementation lands inside `session_v4.rs`'s impl block** (read accessors only, no SharedState restructure); if /design objects, defer the family to S68. Mark SPRINT.md line 23 with "/dev (int) confirms read-side-only access pattern; SharedState interior decomposition stays S68."

### Required revisions (PASS-WITH-REVISIONS)

1. **REV-1 backend-cache sub-facade scope expansion** — author `facades/backend-cache.md` in Wave 2; defer per-row absorption to S68.
2. **REV-2 typecheck narrowing two-phase** — S67 documents + dead-removes; S68 consolidates.
3. **REV-3 int describe_symbol read-side-only scope** — /design (int) Phase 3 confirms; else defer family to S68.
4. **REV-4 LinkerError location** — /arch Wave 0 authors `CompilationError` + `LinkerError` + `LinkerArtefact` + `ObjectArtefact` in `cranelisp-backend` (not types); update both facade docs PFR-style; remove types.md §"Errors and warnings" LinkerError entry.
5. **REV-5 ops::cranelisp_op_* (row 31) consumer audit** — /design (backend) Wave 2 confirms zero current consumers of `cranelisp_op_*` fn names in backend codegen; /dev (intrinsics) Wave 3 deletes once cleared.
6. **REV-6 add missing FIXMEs to Phase 2 acknowledgement** — FIXMEs 0096, 0100, 0106, 0107, 0173, 0177, 0178, 0179 are in scope per "FIXME debt" table; their Phase 3 ownership maps to /design refresh per crate. Phase 3 wave order should fire /design Wave 2 BEFORE /dev Wave 3 — confirmed in current draft. No SPRINT.md edit; flag for /sprint Phase 3 plan author.

Once these six revisions are applied to SPRINT.md (REV-1, REV-2, REV-3 directly; REV-4 + REV-5 as a "Wave 0 / Wave 2 prep" note; REV-6 as a phasing note), `/arch` is satisfied that Phase 3 may proceed.

**Principle 8 check (interim architecture risk)**: zero interim shapes land. Every PIF moves toward target; every PFR documents reality. The two-phase narrowing in REV-2 is not an interim shape — S67's "PFR-document + dead-remove" is a stable subset of the S68 target. Same for REV-1 (sub-facade is a permanent organisational layer, not a stepping stone).

**Cross-crate dependency check**: no new types in `cranelisp-types`; all four DTOs (CompilationError, LinkerError, LinkerArtefact, ObjectArtefact) land in `cranelisp-backend`. Acyclic; Principle 3 holds.

### Scope amendments applied (2026-05-15) — user direction

User direction received post-/arch verdict: **"I don't want to defer realising the final facade any further. Add waves if we need to break up the volume."**

Revisions reversed (volume absorbed by additional waves, see Waves §):

- **REV-1 reversed**: backend cache sub-facade **AND** per-row absorption both land in S67. Dedicated Wave 4 absorbs the volume.
- **REV-2 reversed**: `TypeCheckEnv` narrows **fully 30→2** in S67. FIXME 0172 closes completely. No two-phase split.
- Table-row DEFERs pulled into scope:
  - **Row 7** — `operators.rs` full retirement (D43 full close, FIXME 0150 close)
  - **Row 30** — `io_trace::*` relocation from intrinsics → int (D40 close half, FIXME 0103 io_trace half)
  - **Row 33** — `trace::cranelisp_trace_*` + observer relocation from intrinsics → int (D40 close half, FIXME 0103 trace half)

Revisions applied as drafted:

- **REV-3 kept**: `describe_symbol` family lands as read-side-only `CompilerSession` accessors against `shared.symbol_tables` + `shared.introspection`. This satisfies the facade (which prescribes methods, not interior shape). SharedState field-by-field decomposition is genuinely interior (not facade) and remains S68+.
- **REV-4 applied**: all four DTOs (`CompilationError`, `LinkerError`, `LinkerArtefact`, `ObjectArtefact`) land in `cranelisp-backend`; `types.md` §"Errors and warnings" `LinkerError` entry removed.
- **REV-5 applied**: `/design (backend)` Wave 1 confirms zero current consumers of `cranelisp_op_*` fn names in backend codegen before `/dev (intrinsics)` Wave 2 deletes.
- **REV-6 applied**: /design Wave 1 fires before /dev Wave 2/3/4 (phasing baked into wave plan).

Decision close-outs updated:

- **Decision 40 (trace/io_trace relocation to int)** — closes in S67 via table rows 30 + 33; FIXME 0103 closes both halves.
- **Decision 43 (trait-keyed dispatch forbidden)** — **full close** in S67 via row 6 (`primitive_for_trait_method` delete) + row 7 (`operators.rs` retirement) + row 31 (`ops::cranelisp_op_*` retirement). FIXME 0150 closes completely.
- Decisions 35, 37, 41, 44 close as previously named.

### Second user challenge applied (2026-05-15) — facade-drift deferrals reclassified

User challenge: "how do those deferrals not break the premise?" — surfaced two items the original deferral list mis-classified as interior:

- **FQTypeName binding (FIXME 0151)** — `facades/types.md §232` says binding; source has not migrated. This IS edge drift, not interior. **Pulled into S67 scope.** Multi-crate PIF: typecheck, backend, intrinsics, primitives, platform, int. Receiver-pinned exception + frontend syntactic-stage + reverse-lookup `Type::from_name` exceptions preserved.
- **SharedState facade shape (FIXME 0176 broader scope reclassified)** — `facades/int.md` 8 fields vs `src/session_v4.rs:573` ~13+ fields. `pub struct SharedState` IS at edge. **Pulled into S67 scope.** Per-field PFR/PIF disposition by /arch in Wave 0; preference is PIF (narrow impl) where field is per-form transient and shouldn't be on worker-shared subset; PFR (widen facade) only where current shape is structurally correct.

Items confirmed genuinely interior (no `pub` surface change, no facade-cited shape):
- 0181 cross-module macro stack overflow (runtime bug, typecheck recursion)
- S64 baseline carries 0121/0142/0145/0148 (runtime bugs in independent code paths)
- 0116–0149 test harvest (tests/legacy/ → owning crates; test organization)
- `worker.rs` / `session_v4.rs` file decomposition (FIXME 0109) — file split with no `pub` surface change

These properly stay deferred.

Sprint envelope expanded further. FQTypeName migration adds multi-crate PIF work (Wave 3 expanded). SharedState alignment adds /arch Wave 0 per-field disposition + Wave 3 int-side narrowing. /review (typecheck/backend/intrinsics/primitives/platform/int) Wave 5 scope widens to verify FQTypeName threading.

Sprint envelope expanded from 5 waves to 7 (Wave 0 + Waves 1–6). Volume in Wave 4 (backend cache absorption) is the largest single delta; Wave 3 carries the typecheck full narrowing.

**Verdict status**: scope amendments applied; awaiting user confirmation of revised scope before Phase 3 fires. /arch verdict re-affirmed as **PASS** under the amended scope (all interim-architecture-risk checks still clear; new in-scope rows are full closes of named Decisions, not interim shapes).

## Skill plans (Phase 3)

_To be filled after /arch Phase 2 sign-off._

### /arch

- **Task**: Per-row PFR/PIF disposition table for every audit finding; sign off on facade text updates; commit to baseline-diff discipline in `design/arch/CLAUDE.md`
- **Acceptance**: Disposition table complete; no row marked "TBD"; CLAUDE.md edit drafted

### /design (per crate, narrow)

One invocation per crate: types, frontend, typecheck, backend, primitives, intrinsics, platform; one for int.
- **Task**: Reconcile the facade text against the agreed disposition; ensure every pub-api item is either named in the facade or explicitly marked as internal-but-exposed (with reason)
- **Acceptance**: `facades/{crate}.md` matches `crates/cranelisp-{crate}/public-api.txt` at the granularity of "named or rationalised"

### /dev (per crate, narrow)

One invocation per crate where PIF items exist: backend (Code relocation, typed errors, primitive_for_trait_method delete), typecheck (TypeCheckEnv narrow), int (describe_symbol family), primitives (PRIMITIVES_TABLE static, string/vec relocate). Frontend / intrinsics / platform / types: likely PFR-only.
- **Task**: Implement PIF items; update baselines; verify facade compliance test passes
- **Acceptance**: PIF items landed; `public-api.txt` regenerated; facade compliance test green

### /review (per crate, narrow)

Per-crate after /dev: confirm edge is settled.
- **Acceptance**: No Blocker findings; Important findings either resolved or filed as FIXME with S68+ target

### /qa

**Wave 0 deliverables landed (2026-05-15)**:

- `tests/facade_compliance.rs` — single failing-not-ignored test that
  walks every pub-api item across the 7 crate baselines (8 facade
  files including the backend-cache sub-facade) and grep-asserts the
  item name appears in the corresponding facade. Failing at S67 W0
  open with **281 orphans** across the 7 crates:
    - cranelisp-types: orphans heavily weighted toward newtype derives + view shapes
    - cranelisp-frontend: 14 orphan helper fns (PFR-target Wave 1)
    - cranelisp-typecheck: 25+ TypeCheckEnv method orphans (PIF-target row 21 / Wave 3)
    - cranelisp-backend: ~80 orphans across cache submodule + JIT helpers (PFR sub-facade authoring + Wave 1, PIF rows 1–7 Wave 3)
    - cranelisp-primitives: 8 orphans (PIF rows 26–27 Wave 3)
    - cranelisp-intrinsics: 50+ io_trace/trace/ops orphans (Wave 4 relocations)
    - cranelisp-platform: 12 orphans (PFR Wave 1)
- `tests/facade_pif_rows.rs` — 16 failing-not-ignored tests, one
  per substantive PIF row cluster:

| Row(s) | Test | Owning /dev wave |
|---|---|---|
| 1 | `row_01_code_enum_named_in_backend_pub_api` | backend W3 |
| 2–3 | `rows_02_03_compilation_error_enum_named_in_backend_pub_api` | backend W3 |
| 3–4 | `rows_03_04_linker_and_object_artefact_named_in_backend_pub_api` | backend W3 |
| 5 | `row_05_linker_error_enum_named_in_backend_pub_api` | backend W3 |
| 6 | `row_06_primitive_for_trait_method_absent_from_backend_pub_api` | backend W3 |
| 7 | `row_07_operators_module_retired_from_backend` | backend W3 (D43 full close) |
| 21 | `row_21_typecheck_env_narrowed_to_facade_two_methods` | typecheck W3 (FIXME 0172) |
| 26 | `row_26_primitives_table_static_named_in_primitives_pub_api` | primitives W3 (FIXME 0159) |
| 27 | `row_27_primitives_string_vec_physically_owned_by_primitives_not_reexported` | primitives W3 (FIXME 0180) |
| 30 | `row_30_io_trace_absent_from_intrinsics_pub_api` | int W4 + intrinsics post-W4 (D40 close half) |
| 31 | `row_31_cranelisp_op_extern_fns_deleted_from_intrinsics` | intrinsics W2 (D43 close) |
| 33 | `row_33_trace_observer_absent_from_intrinsics_pub_api` | int W4 + intrinsics post-W4 (D40 close half) |
| 42 | `row_42_describe_symbol_family_methods_exist_on_compiler_session` | int W3 (FIXME 0176 partial) |
| 45 | `row_45_re_register_module_callable_on_compiler_session` | int W3 |
| FQTypeName (D47) | `fqtypename_binding_resolved_stage_apis_use_fqtypename_not_bare_typename` | typecheck W3 (FIXME 0151) |
| SharedState | `shared_state_field_count_matches_facade_after_pif` | int W3 (FIXME 0176 broader scope) |

- `tests/plan/baseline.md` — baseline regeneration discipline
  statement (50 lines) cross-linked to
  `design/arch/CLAUDE.md §"Baseline-diff discipline"`. Codifies the
  two-update rule, the regeneration command, the per-skill
  responsibility split (`/dev` regenerates, `/design` updates
  facade, `/review` confirms both in same diff, `/qa` owns the
  enforcement tests).

**Failure-count expectation at S67 W0**:
- `facade_compliance.rs` — 1 test, FAILS with **281 orphans** across 7
  crates (the orphan total is the sprint progress metric; → 0 at W6
  close).
- `facade_pif_rows.rs` — 17 tests, **16 fail / 1 passes** at W0.

**Test already green (passing today — flagged for review)**:

- `rev3_describe_symbol_resolves_primitive_via_facade_method` — passes
  because `/info add-i64` already classifies as primitive via existing
  slash-command paths (the cranelisp REPL already produces the
  facade-prescribed universal-display format through the pre-S67 code
  path). Test is durable: when row 42 lands the describe_symbol
  family, the e2e signal stays green by construction; the test
  continues to assert the user-visible contract. The two listed
  passing tests in the original draft (`row_42_describe_symbol_family_powers_slash_info`,
  `rev3_describe_symbol_resolves_primitive_via_facade_method`)
  collapsed into one after `row_42_*` was strengthened to check for
  the named methods in `src/` (which do NOT exist today — test now
  fails correctly).

**Wave-flip expectations** (when each test becomes green):

| Wave | Tests flipping green |
|---|---|
| W2 | row 31 (intrinsics: ops::cranelisp_op_*) |
| W3 | rows 1–7 (backend); row 21 (typecheck TypeCheckEnv); rows 26–27 (primitives); rows 42, 45 (int describe_symbol family + re_register_module); FQTypeName test; SharedState test |
| W4 | rows 30, 33 (intrinsics: io_trace + trace relocation) |
| W4–W6 | `facade_compliance.rs` orphan count → 0 as /design Wave 1 + /dev Waves 2–4 + /design facade updates land |

**Acceptance at Wave 6 close**: every test in `facade_compliance.rs`
and `facade_pif_rows.rs` passes; `tests/plan/baseline.md` records
the regeneration discipline.

**Discipline pointers**:
- `memory/feedback_failing_not_ignored.md` — failing tests are
  coverage assets; never `#[ignore]`'d.
- `memory/project_test_strategy.md` — these tests live in `tests/`
  (e2e + integration shape); unit tests stay with `/dev` inside
  crates.
- `design/arch/CLAUDE.md §"Baseline-diff discipline"` — the
  architectural side of the two-update rule.

## Waves (Phase 4)

Seven waves (0–6) to absorb the volume of full facade realisation per user direction.

### Wave 0 — /arch authoring (sequential, gates everything)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /arch | cranelisp-backend | Author 4 DTOs: `CompilationError`, `LinkerError`, `LinkerArtefact`, `ObjectArtefact` (DTOs land in backend per REV-4, not types) | pending |
| /arch | design/arch | Author `facades/backend-cache.md` sub-facade with full per-row dispositions | pending |
| /arch | design/arch | Per-field PFR/PIF disposition for SharedState (~13+ impl fields vs 8 facade fields); produce alignment plan | pending |
| /arch | design/arch | FQTypeName migration plan: enumerate every resolved-stage boundary API in typecheck/backend/intrinsics/primitives/platform/int that currently takes bare `TypeName`; classify against exception list (frontend syntactic, receiver-pinned, reverse-lookup) | pending |
| /arch | design/arch | Amend Decisions 35, 37, 40, 41, 43, 44 with S67 close-out pointers; add Decision close for FQTypeName binding S67 landing | pending |
| /arch | cranelisp-types | Remove `LinkerError` entry from `types.md` §"Errors and warnings" | pending |
| /arch | design/arch | Update `design/arch/CLAUDE.md` with baseline-diff discipline (edge change requires explicit pub-api diff + facade update in same change-set) | pending |
| /qa | tests/ | Scaffold facade-compliance test (every pub-api line named in facade or marked internal-but-exposed) in parallel with /arch | pending |

### Wave 1 — /design refresh per crate (parallel after Wave 0)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /design | cranelisp-types | Verify clean; record edge state; integrate REV-4 DTO removal | pending |
| /design | cranelisp-frontend | PFR rows 16–18 (ExtractedDeclarations rename, helper documentation) | pending |
| /design | cranelisp-typecheck | PFR rows 20, 22–25 (ClusterRead/Write wrapper, stale comments, builtin signature, trace hooks, ReplSnapshot); prep PIF row 21 narrowing | pending |
| /design | cranelisp-backend | PFR rows 7, 9–15 (operators.rs renamed, Jit method-set, compiler helpers, exe helpers, CodeFinalizer, IntrinsicIds); confirm row 31 consumer audit (REV-5) | pending |
| /design | cranelisp-backend-cache | Per-row backend cache disposition under sub-facade authored Wave 0 | pending |
| /design | cranelisp-primitives | Prep PIF rows 26–28 (PRIMITIVES_TABLE static, string/vec relocation, ring0_jit_symbols) | pending |
| /design | cranelisp-intrinsics | PFR rows 29, 32, 34 (drop helpers, RC primitives, IO observer); prep PIF row 31 + DEFER-pulled-in rows 30, 33 (io_trace + trace relocation) | pending |
| /design | cranelisp-platform | PFR rows 35–41 (CLType narrow, manifest fields, descriptor fields, consts, callbacks) | pending |
| /design | int | PFR rows 43–44 (location, naming); confirm REV-3 read-side-only path for rows 42 + 45 PIF | pending |

### Wave 2 — /dev PFR + small PIF (parallel after Wave 1)

**Wave 1 finding (FIXME 0183)**: REV-5 audit NOT clear — 20 backend consumers of `cranelisp_op_*` exist at `jit.rs:150-159` and `compiler/literals.rs:325-339`. `/dev (intrinsics)` ops retirement moves from Wave 2 → Wave 4 (post-backend-migration). Remaining Wave 2 work proceeds.

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-frontend | PFR completions per design row 16–18 (parse_defmacro disposition, helper internal-but-exposed, ExtractedDeclarations rename verified) | pending |
| /dev | cranelisp-platform | FIXME 0107 close (`OwnedPlatformFnDescriptor` `#[non_exhaustive]`); minor PFR-text-driven impl alignment if any | pending |
| /dev | cranelisp-types | Remove LinkerError export sites (post Wave 0 facade edit) | pending |
| ~~/dev~~ | ~~cranelisp-intrinsics~~ | ~~Delete `ops::cranelisp_op_*`~~ — **MOVED TO WAVE 4** per FIXME 0183 (backend migration must land first) | deferred |

### Wave 3 — /dev substantive PIF cluster A (parallel where independent, after Wave 2)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | **First (clears FIXME 0183)**: migrate `cranelisp_op_*` consumers (`jit.rs:150-159` + `compiler/literals.rs:325-339`) to GOT-indirect resolution against primitives-module slots. Then: `Code` enum relocation (row 1), typed errors migration (rows 2–5), `primitive_for_trait_method` delete (row 6), `operators.rs` full retirement (row 7, FIXME 0150 close, D43 close) | pending |
| /dev | cranelisp-typecheck | `TypeCheckEnv` full narrow 30→2 (row 21, FIXME 0172 close) — no two-phase split | pending |
| /dev | cranelisp-primitives | `PRIMITIVES_TABLE: LazyLock<SymbolTable>` static (row 26, FIXME 0159), string/vec physical relocation from intrinsics (row 27, FIXME 0180) | pending |
| /dev | int | `describe_symbol` family + read-side accessors (row 42), `re_register_module` forward (row 45); SharedState field-by-field alignment per Wave-0 disposition plan | pending |
| /dev | cranelisp-typecheck | FQTypeName migration: typecheck-side resolved-stage boundary lifts per Wave-0 plan | pending |
| /dev | cranelisp-backend | FQTypeName migration: backend-side boundary lifts | pending |
| /dev | cranelisp-intrinsics | FQTypeName migration: intrinsics-side boundary lifts (if any past D40/D43 cleanup) | pending |
| /dev | cranelisp-primitives | FQTypeName migration: primitives-side boundary lifts | pending |
| /dev | cranelisp-platform | FQTypeName migration: platform-side boundary lifts (`wait_for_typecheck_type` etc.) | pending |
| /dev | int | FQTypeName migration: int-side boundary lifts (REPL display, slash commands, scheduler API surfaces) | pending |

### Wave 4 — /dev cache absorption + relocations + ops retirement (after Wave 3)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | Full per-row backend cache submodule absorption per `facades/backend-cache.md` (25 root re-exports → `pub(crate)`; `Linker::get_symbol` return-type lift; PFR/PIF per row) | pending |
| /dev | int | Host `io_trace::*` relocated from intrinsics (row 30, D40 close half); target file `src/io_trace.rs` already exists per /design (int) Wave 1 | pending |
| /dev | int | Host `trace::cranelisp_trace_*` + observer relocated from intrinsics (row 33, D40 close half, FIXME 0103 close); target file `src/trace.rs` proposed per /design (int) Wave 1 | pending |
| /dev | cranelisp-intrinsics | **Now unblocked** (post-backend Wave 3): delete `ops::cranelisp_op_*` (10 fns, row 31, FIXME 0183 close); remove `io_trace::*` and `trace::*` after int hosting confirmed | pending |

### Wave 5 — /review per crate (parallel after Wave 4)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /review | cranelisp-types | Confirm edge settled | pending |
| /review | cranelisp-frontend | Confirm edge settled | pending |
| /review | cranelisp-typecheck | Confirm edge settled + FIXME 0172 closure | pending |
| /review | cranelisp-backend | Confirm edge settled + D37/D41/D43 closures + cache absorption | pending |
| /review | cranelisp-primitives | Confirm edge settled + FIXME 0159/0180 closures | pending |
| /review | cranelisp-intrinsics | Confirm edge settled + trace relocation cleanup | pending |
| /review | cranelisp-platform | Confirm edge settled | pending |
| /review | int | Confirm edge settled + describe_symbol family + trace hosting | pending |

### Wave 6 — final compliance + close prep

| Skill | Crate | Task | Status |
|---|---|---|---|
| /qa | tests/ | Final facade-compliance test pass; baseline regeneration discipline documented | pending |
| /arch | design/arch | Final `design/arch/CLAUDE.md` baseline-diff discipline edit | pending |
| /sprint | sprints/ | Phase 7 close prep | pending |

## Notes

### Phase 3 close summary (2026-05-15)

**/arch Wave 0 outputs**:
- 4 DTOs landed in `cranelisp-backend` (`CompilationError`, `LinkerError`, `LinkerArtefact`, `ObjectArtefact`)
- `design/arch/facades/backend-cache.md` sub-facade authored (~260 lines)
- SharedState alignment plan in `facades/int.md` (~21 fields, per-field PFR/PIF/rehome/merge)
- FQTypeName migration plan in `facades/types.md` (per-crate target lists; typecheck bulk, primitives/intrinsics zero hits, platform/int 0 changes)
- Decisions 35, 37, 40, 41, 43, 44 amended with S67 close-out pointers
- Decision 47 (new) — formalises FQTypeName binding + the 3 exception classes
- `facades/types.md` LinkerError entry removed (cross-ref pointer to backend installed)
- `design/arch/CLAUDE.md` baseline-diff discipline section added

**/qa Wave 0 outputs**:
- `tests/facade_compliance.rs` — single failing test grep-asserting every pub-api item appears in its facade
- `tests/facade_pif_rows.rs` — 17 failing-not-ignored tests, one per substantive PIF row cluster
- `tests/plan/baseline.md` — baseline regeneration discipline section
- Initial orphan count: **281** across all crates (sprint progress metric)
- 16/17 PIF row tests fail at W0 (intended state); 1 passes coincidentally (`rev3_describe_symbol_resolves_primitive_via_facade_method`)

**Wave 1 /design × 9 outputs**:
- All 9 facades refined; **net orphan count: 0 across all 7 crates** (`facade_compliance` test now passes)
- 2 new FIXMEs filed:
  - **0182** — `/dev (primitives, int)` Wave 3 narrows or deletes `ring0_jit_symbols` post-PRIMITIVES_TABLE migration
  - **0183** — `/dev (backend)` Wave 3 migrates `cranelisp_op_*` consumers to GOT-indirect BEFORE `/dev (intrinsics)` deletes the source
- FIXME 0107 confirmed still open (`OwnedPlatformFnDescriptor` not yet `#[non_exhaustive]`) — moves to Wave 2 /dev (platform)
- 2 structural drifts surfaced for /arch follow-up: View enum-vs-struct (cranelisp-types); CranelispError variant drift (CranelispError facade body)

### Wave resequencing (2026-05-15) per FIXME 0183

- `/dev (intrinsics)` `ops::cranelisp_op_*` deletion: **Wave 2 → Wave 4** (post-backend-migration)
- `/dev (backend)` Wave 3: **prepended** `cranelisp_op_*` consumer migration to GOT-indirect (clears FIXME 0183 before downstream deletes)
- All other waves unchanged

### /dev (int) hack-back close (2026-05-16) — partial landing

Wave 3 /dev (int) re-fire under FIXMEs 0192 + 0193 (TypeCheckEnv 13-method disposition + Principle 17 amendment). FIXMEs deleted at fire close.

**Landed**:
- Principle 17 amendment: root `""` is special-form metadata home; `user` not architecturally special
- Special-form registration shifted to `""` for 9 syntactic forms (`trace` retained in `primitives` per stdlib re-export)
- `cranelisp-types` gained `ensure_module_exists`/`install_module`/`EnsureOutcome` primitives
- `ensure_module_exists` on TypeCheckEnv reduced to thin shim
- `register_imports`/`register_exports` refactored to free fns; 8 cross-crate caller sites migrated
- `CompilerSession::introduce_module_blank` shim landed

**Punted** (silently — FIXMEs deleted despite incomplete work):
- Methods 1, 2, 3, 4, 5, 6, 7, 11 relocations to cranelisp-types (8 of 13 disposition rows)
- Full 4-branch `introduce_module(x)` consolidation
- Public-api baselines not regenerated
- `DefKind::SpecialForm` consumer migration partial — **known regression**: bare-special-form input at REPL no longer surfaces description metadata (consumers still probe current_module, not `""`)

**State**: Partial close accepted on user direction "press forward." No new FIXMEs filed despite the punts. Phase G consumer migration + remaining TypeCheckEnv relocations carry as unrecorded debt into S68.

### /dev (int) hack-back re-fire (2026-05-16) — substantive landing

Second re-fire under restored FIXME 0192 + user direction "hammer in the complete new facade." All four Residual Tasks delivered:

- 8 method dispositions executed (methods 1–7, 11): deletions + relocations to `cranelisp-types`
- `CompilerSession::introduce_module` 4-branch lifecycle landed at `src/session_v4.rs:1174-1208` (present / cache-hit / source-hit / blank)
- REPL regression fixed: bare special-form input at REPL again surfaces description metadata; consumers now probe root `""`
- Bonus: `/imports` slash command enumerates special forms from root `""`
- Baselines regenerated: types 3714→3772 (+58 — new chain-follow fns + `EnsureOutcome`); typecheck 190→184 (-6)

FIXME 0192 deleted on legitimate close.

### Sibling-wave breakage — `cranelisp-exe-bundle` (2026-05-16)

Wave 4b (Sprint 66) retired `cranelisp_intrinsics::ops` and moved Ring 0 ops to `cranelisp_primitives::ring0` (23 `#[export_name]` symbols). `cranelisp-exe-bundle/src/lib.rs` still referenced the retired `intrinsics::ops` module → `cargo check --workspace` broke. Two-line patch: drop `pub use cranelisp_intrinsics::ops`, add `pub use cranelisp_primitives::ring0`. Workspace check green.

**Descope note**: `cranelisp-exe-bundle` is NOT a 9th facaded surface. It is a force-link manifest for `crate-type = ["staticlib"]` — its `pub use` lines exist solely to retain `#[no_mangle]` / `#[export_name]` symbols in the produced `.a`. No caller-facing API; no facade authored. Treat as an `/int` implementation detail (binary-production support), audited by `/dev (int)` when intrinsics/primitives submodule shape changes. Sprint 67 facade-coverage count remains 7 lib crates + `int` binary = 8 surfaces.

S66 close-out audit (delegated to research subagent 2026-05-15) identified:
- 7 crates + int = 8 facade↔pub-api comparisons
- 5 substantive gaps (PIF candidates), ~20 cosmetic drifts (PFR candidates) across the surface
- Verdict per crate: types ✅; frontend ⚠️ cosmetic; typecheck ❌ substantive; backend ❌ substantive (largest); primitives ⚠️ in-flight (FIXMEs 0159/0180); intrinsics ⚠️ cosmetic; platform ⚠️ cosmetic; int ❌ substantive

## Outcome (Phase 7)

_To be filled at close._
