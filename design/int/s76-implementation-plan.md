# Int — S76 implementation plan (facade-arc wash-through + parallel-JIT collapse + W-Macro)

Owner: `/design (int)`. Phase-3 implementation plan for the S76 int scope, subordinate to `design/int/int.md` (master) and bound by `design/arch/facades/int.md` (LIVE — retirement is a separate late-phase capstone, NOT in this plan) + `design/arch/bounded-contexts.md` §6.

**This is DESIGN ONLY.** No `src/` edits. The plan names the files touched, the order, the inseparable-wave constraints, the deletions, the acceptance per workstream, the seams needing an `/arch` ruling (all already settled by the S76 Phase-2 review + W-Macro LOCKED decision — none re-opened here), and where int unit tests land.

Grounded against the actual source (measured 2026-06-03): `cargo check -p cranelisp` = **173 errors**; `src/` = 25,399 LOC across 28 files. The master design doc (`int.md`) is S64-era and substantially stale w.r.t. the as-built (`cluster.rs`, `cache.rs`, `got_trace.rs`, `trace.rs`, `io_trace.rs`, `display.rs` have all since landed in `src/`; many of its §14/§16 FIXMEs are resolved). This plan supersedes the master for S76 sequencing; the master's §15 doc-triage and §13 Decision-register are not S76 concerns.

---

## 0. Workstream map + the one hard ordering constraint

| WS | Name | Touches | Sequencing |
|---|---|---|---|
| **A** | W-Absorb — streamlined-type cascade | the wide cascade across `worker.rs`, `session_v4.rs`, `pipeline.rs`, `cluster.rs`, `expander.rs`, `save.rs`, `pretty.rs`, `display.rs`, `platform.rs`, `code.rs` | First. Everything else sequences behind it. |
| **B** | W-Collapse — delete the parallel JIT pipeline | `worker.rs` (worker path), `pipeline.rs` (delete expr-eval path) | After A. **Two inseparable parts (a)+(b) in ONE wave** (Principle 11). |
| **C** | W-Macro — three-pass expand loop (LOCKED) | `cluster.rs` (Pass-1 loop), `worker.rs` (delete walk), `expander.rs` (keep core, delete walk), `marshal.rs` | After A; shares the `process_cluster`/`worker.rs` boundary with B — co-schedule with or just after B. |
| **D** | W-Enablement — ctor batch + `Jit::new` + `INTRINSICS_TABLE` + `into_concrete` + startup-object relocation | `worker.rs`, `exe.rs`, the primitives mount site | The `Jit::new(symbol_tables)` part is the SAME edit as B's worker realign (co-edit). Ctor-batch + `into_concrete` ride A. |
| **E** | Host-wiring (int's parts) — host ADT marshal, `parse_type_sig` removal, platform-as-module | `platform.rs`, `marshal.rs` | A dedicated wave AFTER A defines the host surface (0229/0233). |

**The single non-negotiable ordering constraint (Principle 11, BC §3 "Watch item"):** W-Collapse part (a) [worker realign to S75 5-arg `compile_to_module`] and part (b) [delete `pipeline.rs`'s hand-rolled expr-eval path] land in the **same wave**, together with the `Jit::new(symbol_tables)` construction (D). Doing any one without the others leaves int with one foot in each pipeline — the dual-pipeline defect Principle 11 exists to prevent. There is no intermediate green state where only the worker path is realigned; the expr-eval path and the `Jit::new` collapse are the same structural move.

---

## 1. W-Absorb — the streamlined-type cascade (173 → green)

Facade-first migration discipline ([[feedback_facade_first_migration]]): push int to the target shapes; do NOT negotiate the seven streamlined crates back. The cascade is mechanical once the mapping is known. Per-cluster mapping (grounded in the measured error histogram):

### 1.1 `ModuleEntry` variant collapse (~41 errors)

The pre-S70 `ModuleEntry` enum had `Macro`, `Reexport`, `Constructor`, `SpecialForm`, `TraitDecl.decl`, `TraitImpl.target_type` variants/fields int still matches on. The streamlined types crate collapsed these:

| Old int match | New shape (target) | Sites |
|---|---|---|
| `ModuleEntry::Macro { clauses, .. }` | `ModuleEntry::Def { kind: DefKind::Macro { clauses_meta, sexp, source }, .. }` | 15 — `worker.rs::separate_macros`, `SymbolTableMacroResolver`, `/list`/`/info` describe paths in `session_v4.rs` |
| `ModuleEntry::Reexport { .. }` | per-symbol `ModuleEntry::Import { source, visibility: Public }` (BC §7 "Visibility is per-entry"; Reexport retired) | 11 — import/export display + `module_exports` |
| `ModuleEntry::Constructor { .. }` | `ModuleEntry::Def { kind: DefKind::Constructor, ast, code, got_slot, .. }` (+ `CtorMeta` for metadata) | 9 — ADT introspection in `pretty.rs`/`display.rs`/`session_v4.rs` |
| `DefKind::SpecialForm` | retired variant — special forms are `ModuleEntry::SpecialForm` (entry-level, not a `DefKind`); read description from there | 11 — `/imports` special-form category, `describe_symbol` |
| `TraitDecl.decl` field | `TraitDecl { info: TraitDeclInfo, visibility, docstring }` (slimmed; `decl` AST no longer embedded) | 5 |
| `TraitImpl.target_type` | read via the slimmed `TraitImpl` shape (consult `cranelisp-types` baseline for the field) | 1 |

**Approach:** every `match entry { ModuleEntry::Macro {..} => …, ModuleEntry::Constructor {..} => … }` arm becomes a `ModuleEntry::Def { kind, .. }` arm with an inner `match kind { DefKind::Macro {..} => …, DefKind::Constructor => …, DefKind::UserFn {..} => … }`. The REPL `SymbolCategory` mapping (`SymbolInfo.category`) reads from `DefKind` + entry variant uniformly. This is the bulk of the `session_v4.rs` introspection-accessor + `pretty.rs`/`display.rs` ADT-formatting churn.

### 1.2 `DefKind` reshape + primitive-ness (~17 errors)

`DefKind::Primitive { primitive_kind, jit_name }` lost its fields (D0048 A2 reversal — `Code::Primitive` marker dropped; primitive-ness is read from `kind: DefKind::Primitive` alone, entry carries `code: None`). `PrimitiveKind` import retires. The 3 `PrimitiveKind` import sites + 3 field-access sites in `worker.rs`/`session_v4.rs` drop to a bare `DefKind::Primitive` discriminant check.

### 1.3 `Code` / `CompilationArtifacts` reshape (~11 errors)

`Code::ptr` (9 sites) and `CompilationArtifacts.code_ptrs`/`.artifacts` (2 sites) — GOT is the single source of callable addresses (D0041/D0035 post-rollback canonical: no per-entry ptr). Every `code.ptr()` call site changes to read the address from `symbol_tables[m].got().slot(got_slot)`. **These sites are mostly in the worker JIT path and `pipeline.rs`** — they are subsumed by W-Collapse (§2), so resolve them THERE rather than patching `Code::ptr` to limp along. The non-collapse `code.ptr()` sites (cache-hit `Linker::register_symbol` at `worker.rs:3582`) read the Linker-resolved address differently — those migrate with §2's cache-hit touch.

### 1.4 typecheck-surface cluster (~14 errors)

- `register_imports` / `register_exports` (7 sites) — struck from typecheck (BC §2 + §7: import/export registration is an int-side / frontend-StructuralDecl alias-installer concern, NOT typecheck). int's call sites in `worker.rs`/`session_v4.rs`/`cluster.rs` are replaced by the **int-side alias installer** writing into `SharedState.module_aliases` + per-entry `Import` bindings at parse-time (Phase 0 / `process_cluster` pre-`check_forms`). This is the `module_aliases` SharedState field the S67 alignment plan named; the installer is the producer. typecheck reads `module_aliases` read-only.
- `Type::from_name` (5 sites) / `io_inner_type` (2 sites) — narrowed typecheck helpers. Re-point to the streamlined equivalents (consult `crates/cranelisp-typecheck` baseline; likely `Type::adt`/explicit construction + an IO-type accessor). FIXME 0187 is subsumed here.
- `ClusterContext` import (1) + `ReplSnapshot` import (1) + `TypeCheckEnv::snapshot`/`restore` (2) + `Scheme.vars` (1) — `ClusterContext` renamed to `SymbolTableAccess` (D0044 amendment); the snapshot/restore REPL error-recovery primitives moved or renamed (consult typecheck baseline — the `repl_check_state` `tc_snapshot`/`tc_restore` pair). `Scheme.vars` → the streamlined field name.

### 1.5 `DefnVariant` / `Lambda` / `Expr` narrows (~14 errors)

- `param_annotations` on `DefnVariant`/`Lambda`/`Expr::Lambda` (7+2) — S70 narrowed these off the AST. int reads param types from `scheme` / `param_names` instead. Sites are in `pipeline.rs` (wrapper-defn construction) + macro-clause building in `worker.rs`.
- `DefnVariant.name` / `Symbol.name` / `Symbol.tag` / `Symbol.fields` (7) — `Symbol` is now a newtype over the string (Deref to `str`); `.name` field access becomes `.as_ref()`/`Deref`; `DefnVariant.name` moved or the variant restructured (consult baseline). The `Symbol.fields`/`.tag` accesses (5) are likely on an ADT-pattern path mis-typed as `Symbol`.

### 1.6 `ModDecl.visibility` / `is_private` (~14 errors)

`ModDecl` carries `visibility: Visibility` per spec §5.2 (not `is_private: bool`). Every `mod_decl.is_private` read becomes `mod_decl.visibility == Visibility::Private`; pattern matches mentioning the field add `visibility`. Sites in `cluster.rs`/`worker.rs` submodule handling + `save.rs` regeneration.

### 1.7 Acceptance (W-Absorb)

`cargo check -p cranelisp` advances monotonically to **0 errors** (W-Green). No `pub(crate)` backend reach-around is "fixed" by re-publishing — the 23 backend-privacy errors (cluster 7) are LEFT for W-Collapse, which resolves them by int *not calling*. (If A is landed before B, the backend-privacy errors remain; A's "green" milestone is therefore reached only after B lands. Sequence A's type-cascade edits first, but W-Green is the A+B+D joint milestone.)

---

## 2. W-Collapse — delete int's parallel JIT pipeline (the bulk simplification)

Two inseparable parts, ONE wave (Principle 11). int produces GOT entries and calls the ONE entry (`compile_to_module`), as backend designed; backend privates STAY private ([[feedback_callee_api_for_caller_only]]).

### 2.1 Part (a) — realign the worker path

`src/worker.rs::inline_jit_codegen_for_names` (line 3229) is the canonical per-symbol JIT path. It is red against S75 backend: it calls the **4-arg** `compile_to_module(module, names, tc_modules, jit.jit_module())` and reads `result.code_ptrs` / constructs `Code::Jit { ptr }` (the pre-D41 shape S75 retired).

Realign to the S75 shape (BC §3 invariant 3):
- Call the **5-arg** `compile_to_module(scope, &[sym], &symbol_tables, introspection.as_ref(), module)` (consult backend baseline for the exact arg order — the 5th arg is the `Module` instance per `compile-to-module.md`).
- It returns `CompilationArtifacts` (introspection contributions: `clif_ir`, `code_size`, `compile_duration`) and writes the **GOT slot internally** (D41 #2 — backend's own write).
- **int composes `Code::Jit` from its owned `Arc<Jit>`** (D41 #1, S75 W2 Finding-A — backend only borrows `&mut M`, never owns the `Arc<Jit>`) and installs via `SymbolTable::write_code(sym, Code::Jit(arc_jit.clone()))`. `Code::Jit` is now `Code::Jit(Arc<Jit>)` (lifecycle-owner only, no `ptr`).
- Retain the `CompilationArtifacts` introspection into `shared.introspection` (conditional on `is_some()`).

### 2.2 Part (b) — delete `pipeline.rs`'s hand-rolled expr-eval path

`src/pipeline.rs` (459 LOC) hand-rolls the JIT for REPL expression eval: `declare_intrinsics → declare_functions → build_compile_context → compile_defn → finalize_and_get_ptr` (lines 138-169 and 277-306, two copies). **DELETE this path.** Route REPL expression eval through the unified worker entry:
- Wrap the expression in the `__repl_expr__` synthetic `Def` (a zero-arg fn body), insert into the symbol table, and call the SAME `compile_to_module`-based path part (a) realigns.
- The eval-result trampoline (per `int.md` §5.3 "Eval lifetime") drives the `Arc<Jit>`-reclaim-on-value-consumed via `Code::Jit`'s `Drop`.

**Deletion inventory (W-Collapse):**
- `src/pipeline.rs` — the two hand-rolled expr-eval functions (the reusable `wrapper_defn` construction may survive if reused by the synthetic-Def path; the `declare_*`/`compile_defn`/`finalize_and_get_ptr` calls all delete). Likely the whole file collapses to a thin synthetic-Def builder, or folds into `cluster.rs`/`worker.rs`.
- `src/worker.rs` — the hand-assembled flat-symbol JIT setup: `collect_jit_setup` (2954), `collect_jit_setup_public` (3017), `got_data_defs` assembly (2959/3005), the already-compiled-fn-ptr sweep, `inline_jit_codegen_for_module` (3173) if it duplicates the per-names path. The `Jit::new_with_symbols(&extra)` call (3296) is REPLACED by `Jit::new(symbol_tables)` (D, §4.2).
- int stops calling the 9 backend `pub(crate)` reach-arounds: `declare_intrinsics`, `declare_functions`, `compile_defn`, `build_compile_context`, `finalize_and_get_ptr`, `intrinsic_symbols`, (`ensure_module_exists` is types-pub — no change), `generate_startup_object` (relocates, §4.4), `got_data_symbol_name` (now types-pub — read from there).

### 2.3 Acceptance (W-Collapse)

- All 23 backend-privacy errors (cluster 7) resolve to "int no longer references the symbol."
- There is exactly ONE `compile_to_module` call site shape in int (the worker per-symbol path); REPL expr eval and module-defn codegen both flow through it.
- `cargo check -p cranelisp` green (joint A+B+D milestone).
- An int **unit test** in `src/worker.rs` `#[cfg(test)]` (the existing `inline_jit_codegen_for_names_compiles_single_defn` at 4193 — realign it, do not delete) asserts a single-defn compiles + is GOT-callable through the unified path.

---

## 3. W-Macro — the three-pass expand loop (DECISION LOCKED 2026-06-03)

Authoritative: `macro-availability-model.md` §0 (LOCKED) + `macro-expansion-ownership.md` §4.3 PINNED box + BC §6 int bullet. **No public-API delta** beyond the already-authored-and-baselined `cranelisp_types::{MacroExpander, MacroInvokeError, resolve, resolve_macro_head, Resolved, ResolveError}`. The locked rule: a macro's expansion references only **dependency modules** (typechecked-before, JIT-compiled just-in-time) + **macros** (incl. same-module); **same-module non-macro defs are NOT available at expansion** (enforced structurally by pass ordering); **defmacro-before-use is normative**.

### 3.1 int owns the Pass-1 expand loop in `process_cluster`

`src/cluster.rs::process_cluster` (line 177) currently expands each form (gap-retry) then builds `Vec<ParsedEntry>` then makes one `check_forms` call. The S76 shape makes the expand step the explicit **Pass-1 expand loop**:

1. For each form, walk for macro heads. **Recognition** is via `cranelisp_types::resolve_macro_head` over the **committed** symbol tables — `View::single(live)` first-hop (no staging exists during Pass 1). Zero int→typecheck dependency for recognition (it's a types query).
2. On a recognized macro head, execute via int's `MacroExpander` impl (§3.2).
3. `build_form` the raw-`Sexp` result into `ParsedEntry`s (keeping `build_form` in int, out of typecheck — `macro-expansion-ownership.md` §4.3 "second/cleaner shape").
4. Re-enter the loop on the spliced entries (nested macros + structural re-classification: `def` → `(begin (defn …)(defmacro …))`) until no macro heads remain (fixpoint, bounded by `EXPANSION_DEPTH_LIMIT`).
5. **Dependency-module forms a clause needs are typechecked-and-compiled just-in-time** during Pass 1 (pause-and-fetch — the same scheduler gap mechanism as cross-module value/type refs, Decision 0030).
6. Feed the fully-expanded `Vec<ParsedEntry>` to ONE `check_forms` call = Passes 2+3 (no `MacroExpander` param; it never triggers macro execution).

### 3.2 int implements `cranelisp_types::MacroExpander`

A new type in int (e.g. `src/expander.rs`) implementing the trait over the **surviving** invocation core:
- `src/expander.rs::invoke_clause` (119), `find_matching_clause` (107), `invoke_jit_protected` (170), `rewrite_spans` (322) — these SURVIVE, wrapped by `MacroExpander::invoke(&self, fq, args, call_span) -> Result<Sexp, MacroInvokeError>`.
- `src/marshal.rs` — Sexp↔heap marshalling survives (it's the execution-side marshal, BC §4b/int-owned).
- int constructs the `&dyn MacroExpander` and threads it into the Pass-1 loop. (It is NOT passed to `check_forms` — recognition+execution happen in the expand loop, before `check_forms`.)

### 3.3 Deletion inventory (W-Macro)

- `src/worker.rs::SymbolTableMacroResolver` (442) + `impl MacroResolver` (465) + `resolve_macro_definition` (521) — the free-standing chain-walk. **DELETE** — recognition is now `cranelisp_types::resolve_macro_head`.
- `src/expander.rs::expand_sexp_recursive` (354) + `expand_macro_call_with_entry` (409) + `trait MacroResolver` (49) — the free-standing walk. **DELETE** — the walk moved to the `process_cluster` Pass-1 loop driving `resolve_macro_head`.
- `src/worker.rs` line 748-760 (the `SymbolTableMacroResolver` + `expand_sexp_recursive` driver) — **DELETE**.
- `src/worker.rs::block_for_macro_codegen` reference + the dead `collect_transitive_uncompiled_deps` macro-clause-callee machinery (2413-2501, `compile_macro_clause_inline` 2510) — **DELETE, NOT WIRED** (the locked decision forbids same-module non-macro clause callees, so there is no empty-slot case; `macro-availability-model.md` §0.7). The `scheduler.rs:669` dead `block_for_macro_codegen` can be dropped (coordinate with `/dev (int)` on scheduler; it's int-owned).
- `worker.rs` macro-clause-with-state path: `compile_macro_clause_with_state` (609) — assess; if it duplicates the `MacroExpander` JIT invocation, fold; the just-in-time dependency-compile of Pass 1 replaces the inline clause-callee compile.

### 3.4 Acceptance (W-Macro)

- `process_cluster` runs the three-pass shape; `check_forms` receives fully-expanded `Vec<ParsedEntry>` and is never passed a `MacroExpander`.
- The free-standing walk (`expand_sexp_recursive`, `SymbolTableMacroResolver`, `MacroResolver` trait, `block_for_macro_codegen`) is gone.
- e2e: macro-using programs (REPL + batch) expand correctly; the LOCKED rejected-program shape (`helper → m → f`, same-module `defn` called by a macro clause) produces a **clear diagnostic** (`macro-availability-model.md` §0.8), NOT silent expansion. (`/qa` authors the narrow integration test; int unit-tests the `resolve_macro_head` recognition + `MacroExpander::invoke` marshalling in `src/`.)
- int unit tests in `src/expander.rs` `#[cfg(test)]`: `MacroExpander::invoke` round-trips a known clause; `resolve_macro_head` over a committed table recognizes a `DefKind::Macro` head and returns `Ok(None)` for a forward (pre-defmacro) reference.

---

## 4. W-Enablement — ctor batch + JIT-setup collapse + relocations

### 4.1 `derive_codegen_batch` enumerates synthesised ctor `Def`s (0249-b)

int's `derive_codegen_batch` (the function that builds the `names` batch handed to `compile_to_module`) enumerates each `TypeDef`'s synthesised constructor `Def` names into the batch, so their `Expr::ConstrADT` bodies are lowered and GOT slots populated. **Requires 0249-a (typecheck got-slots `DefKind::Constructor` entries in `register_constructors`) to land FIRST** — if int enumerates a `got_slot: None` ctor, `compile_to_module` has no slot to write. This is a cross-crate ordering: 0249-a (typecheck /dev) before 0249-b (int /dev). Mirror of the Decision 0048 primitives got-slotting. Acceptance: `(map Some xs)` reaches the constructor via its GOT slot (the roadmap's pending real-pipeline e2e test).

### 4.2 `Jit::new(symbol_tables)` + `INTRINSICS_TABLE` consumption (co-edit with W-Collapse §2.1)

This is the SAME edit as the worker realign (BC §3 sequence point 2): the hand-assembly loop (`worker.rs:3242-3296`) is **replaced by** `Jit::new(symbol_tables)`. int:
- Calls the new backend `Jit::new(symbol_tables)` (authored by `/dev (backend)` this sprint) — it derives the whole JIT symbol set from `symbol_tables` (GOT data symbols via `cranelisp_types::got_data_symbol_name`, intrinsic Import targets from `cranelisp_intrinsics::INTRINSICS_TABLE`).
- **int assembles nothing** — delete `collect_jit_setup`, `got_data_defs` assembly, the flat symbol vector.
- The cache-hit `Linker::register_symbol` sites in `worker.rs` (3545 `intrinsic_symbols()`, 3570/3582/3591) migrate: intrinsic registration reads `cranelisp_intrinsics::INTRINSICS_TABLE` instead of backend's `intrinsic_symbols()`; the GOT-base registration reads `got_data_symbol_name` from types.

**Cross-crate dependency:** `INTRINSICS_TABLE` (intrinsics /dev) + `Jit::new(symbol_tables)` (backend /dev) must land with or just before int's consumption. Sequence: intrinsics publishes → backend consumes in `Jit::new` → int's two readers switch.

### 4.3 `into_concrete::<Code, ()>()` at the `PRIMITIVES_TABLE` mount (0242-i)

The int primary-mount site (`session_v4.rs`, where `PRIMITIVES_TABLE` is cloned and inserted at `ModuleFullPath::primitives()`) still spells the static as `<Code,()>` + bare `.clone()` — stale to the S73 `<(),()>` shape. Adopt `cranelisp_primitives::PRIMITIVES_TABLE` (now `SymbolTable<(),()>`) + `.into_concrete::<Code, ()>()` at the mount (BC §4a "Session-integration contract"; 0242 mount-comment). This closes 0242-(i); 0242-(ii) host ADT marshaling is WS-E.

### 4.4 `generate_startup_object` body relocation to `src/exe.rs` (SEAM — /arch RULED)

The S76 Phase-2 review RULED (Q1): **int owns startup-object emission** (BC §3 invariant 7 — the `--link` `_main` alias is int's link-orchestration, not a backend boundary). Relocate the body from backend `pub(crate) generate_startup_object` into `src/exe.rs` — it uses `cranelift_object` directly (int already depends on it transitively); no codegen-from-`symbol_tables` logic, so it does NOT belong behind `compile_to_module`. int deletes its broken `pub use cranelisp_backend::exe::generate_startup_object` re-export. Backend deletes its `pub(crate)` stub in a future backend streamline (acceptable to leave the dead stub one sprint). **No /arch ruling pending — this was settled in Phase 2.**

### 4.5 Acceptance (W-Enablement)

- `(map Some xs)` works e2e (constructor-as-value).
- int assembles zero JIT symbols by hand; `Jit::new(symbol_tables)` is the only construction site.
- primitives mount uses `into_concrete::<Code,()>()`; one shared `Arc<GotTable>`.
- `--link` startup-object emission lives in `src/exe.rs`; `link.rs` e2e passes (gated also on backend 0122).

---

## 5. WS-E — Host-wiring (int's parts: 0229 + 0233)

A dedicated wave AFTER A defines the host surface. int's parts (the platform host-wiring set 0229-0235 spans several skills; these two are int's):
- **0229** host-side ADT marshaling for platform round-trip — `src/marshal.rs` / `src/platform.rs` gain host↔language ADT marshalling for platform call args/returns. Gates `spec_platforms.rs`. Depends on upstream 0230 (`parse_type_expr` named API, /frontend) + 0231 (platform sig typecheck entry, /typecheck).
- **0233** `parse_type_sig` removal + platform-as-module — `src/platform.rs::parse_type_sig` (the stringly-typed sig parser) is removed in favour of the typed `parse_type_expr` API; platform module introduction flows through the existing `ensure_module_exists` path against the `platform.<name>` key (BC §4a/SharedState `kept_dlls` rationale + spec §8.9.3). `load_platform_dll` constructs structured `PlatformError` per Decision 42 (the old `int.md` §9 FIXME 0104 work); `Sess::format_error` adds the `Platform` arm.

Acceptance: `spec_platforms.rs` + `platform_errors.rs` + `spec_08_modules.rs` platform paths pass. Round-trip DLL integration tests (0235, /qa) green.

---

## 6. W-e2e → unit (user's primary directive)

Once green, run the active e2e suite (34 files, all modes). For **every** failure, two mandatory outputs ([[feedback_unit_tests_with_dev]] + [[feedback_repros_join_suite]]):
- (a) a fix, OR a tracked defect FIXME + failing-not-ignored repro;
- (b) an explicit **assessment** recorded per-failure: "would an int `src/` unit test have caught this before e2e?" If no, close the gap with a new `#[cfg(test)]` unit test in the owning `src/` module.

int unit tests land **inside `src/`** per the test strategy ([[project_test_strategy]]) — `#[cfg(test)] mod tests` in the relevant file (`worker.rs`, `expander.rs`, `cluster.rs`, `platform.rs`). `/qa` owns the e2e harness in `tests/`. The s68 sentinels (`s68_primitives_uniform.rs`, 2 `#[ignore]`'d cases, 0221/0191) un-ignore once W-Green lands.

---

## 7. Seams needing an /arch ruling

**None open.** All four S76 seams were settled in the Phase-2 /arch review + the W-Macro LOCKED decision:
- Pipeline-collapse seam — fully specified (BC §3); no new backend public surface; `got_data_symbol_name` → types (authored, baselined), `generate_startup_object` body → int (ruled §4.4).
- 0249 sequencing — resolved (0249-a before 0249-b).
- `Jit::new(symbol_tables)` + `INTRINSICS_TABLE` — approved as target-stated; authored by backend/intrinsics /dev this sprint.
- W-Macro three-pass + resolution-primitive placement — LOCKED; types surface authored + baselined.

If implementation surfaces a genuine new cross-crate gap, `/dev (int)` files FIXME `target: /arch` per protocol (do not edit `cranelisp-types` or `design/arch/`).

---

## 8. Wave / ordering summary (feeds Phase 4 wave-org)

1. **W-Absorb type cascade** (§1) — first; the wide mechanical edit. Lands NOT-green (backend-privacy cluster left for B).
2. **W-Collapse (a)+(b) + Jit::new co-edit + into_concrete** (§2 + §4.2 + §4.3) — ONE inseparable wave (Principle 11). Cross-crate gated on backend `Jit::new` + intrinsics `INTRINSICS_TABLE`. This is the W-Green milestone.
3. **W-Macro three-pass** (§3) — shares the `cluster.rs`/`worker.rs`/`expander.rs` boundary with wave 2; co-schedule or immediately after. Gated on the spec change (FIXMEs 0005/0006/0007, `/spec`, already routed) being committed.
4. **W-Enablement ctor batch** (§4.1) — gated on typecheck 0249-a; can ride wave 2 if 0249-a lands first.
5. **W-e2e → unit** (§6) — after W-Green.
6. **WS-E host-wiring** (§5) — dedicated wave after A; gated on /frontend 0230 + /typecheck 0231.

This plan feeds **Phase 4 wave-org** (`/sprint`) and **Phase 5 `/dev (int)`** (implementation against this plan + `/qa`'s sprint-wide failing tests). The int facade stays **LIVE** through Phases 3-5; W-Retire is the separate late-phase capstone, NOT in this plan.
