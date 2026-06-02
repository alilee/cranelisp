# Bounded Contexts — per-surface target shape

`/arch` commits to six crate-shaped surfaces plus the cross-crate types crate. Each is a **bounded context**: the stable demarcation of what the crate is responsible for. The triad (`/design`, `/dev`, `/review`) narrow-deploys to one surface per invocation; the surface's bounded context is what the triad reads to do its work.

This file is the canonical home for the per-surface full statements. The skill def (`.claude/commands/arch.md` §The crate-shaped surfaces) carries the one-line summaries and points here. The facade specs (`design/arch/facades/{crate}.md`) cite this file rather than restate the bounded context.

This document is conceptual. Each section answers: *what is this crate's responsibility, why does the boundary lie here, what crosses it.* It does not specify *how* responsibilities are implemented (per-crate design carries that) or *which decisions bind* the implementation (the boundary itself is the decision; cross-cutting principles live in `principles.md`).

Each section: bounded context (essence + why); in-scope (responsibilities, conceptually); out-of-scope (what belongs elsewhere by responsibility); what crosses the boundary (value-passing surfaces and, where applicable, window types). The int section additionally enumerates internal cadences and inter-cadence handoffs.

---

## 1. Frontend — `crates/cranelisp-frontend/`

**Bounded context.** Source text becomes structured data. The frontend reads source bytes into S-expressions, expands macros, and builds the AST. It is purely structural: it does not know types, code, or semantics — only shape. This narrows the contract the rest of the pipeline depends on: every downstream stage consumes the same well-formed tree shape, regardless of whether the input came from a file, the REPL, or another macro.

**In-scope.**
- Lexing and parsing source into S-expression trees
- Macro expansion (multi-clause defmacro and quasiquote desugaring)
- AST construction from expanded S-expressions
- Module-identity normalisation (super resolution, structural-declaration extraction)
- Synthetic-span allocation for macro-generated forms

**Out of scope.**
- Type inference (typecheck)
- Code generation (backend)
- Module loading orchestration (int)
- Spec definition (`/spec`)

**What crosses the boundary.**
- **Inputs**: source text; the session-level `SymbolTables<C, L>` + `ModuleAliases` for macro lookup (read-only — see invariant 6).
- **Outputs**: AST values (expression trees, top-level forms, structural declarations) defined in `cranelisp-types`; per-form `ParsedEntry` transients; `ExtractedDeclarations` bundles; `Sexp` values from macro expansion.
- **Window types**: none.

**Public surface (canonical enumeration).** The crate-root rustdoc (`crates/cranelisp-frontend/src/lib.rs` //! preamble) is the single source of truth for the frontend's as-designed public boundary; `crates/cranelisp-frontend/public-api.txt` is the authoritative as-built enumeration, gated at PR time per the baseline-diff discipline (see `design/arch/CLAUDE.md` §"Baseline-diff discipline"). Per-item rustdoc on each public item (`pub fn expand`, `pub fn parse`, `pub struct ExtractedDeclarations`, `pub enum ExpansionError`, etc.) carries the per-item contract — visit them with `cargo doc -p cranelisp-frontend --no-deps`.

The four free-function form-by-form boundary — `parse`, `extract_module_declarations`, `build_form`, `build_expr`, plus `expand` for macro expansion — is the operative public-API summary; see the lib.rs preamble §"Public surface — the form-by-form boundary" for signatures and the rationale for the shape (per-form, no AST union enum).

**Bounded-context invariants.** These hold across sprints — the contract `cranelisp-frontend` makes with the rest of the workspace:

1. **No type inference.** Types in the frontend are `TypeExpr` (syntactic), not `Type` (resolved). Type resolution is `cranelisp-typecheck`'s job. The frontend never names `Type`, `Scheme`, or `TypeId`.
2. **No code generation.** Macro bodies are AST nodes that `int` compiles via the backend; the frontend never invokes Cranelift and never names `cranelisp-backend`, `cranelisp-primitives`, or `cranelisp-intrinsics`.
3. **`super` resolved at frontend.** Per `design/arch/super-import-arbitration.md`: `ImportSpec.module_path` NEVER contains the literal `"super"` past `parse` (specifically past `parse_import_sexp`). All `super`-resolution happens at parse time against the parsing module's own path.
4. **Synthetic spans are unique.** `next_synthetic_span` issues monotonically increasing spans for compiler-generated forms. No two synthetic spans collide within a session.
5. **`expand` is re-entrant.** May invoke registered macros which may themselves expand further. Whether the implementation imposes a defensive depth limit (and what value) is the implementing crate's call — not a BC concern; the published `EXPANSION_DEPTH_LIMIT` is an operational safeguard, not a contract.
6. **`expand` is side-effect-free for dependency resolution.** When an FQ ref's target isn't ready, expand returns `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` — never calls the scheduler, never registers modules, never blocks. The frontend has no `Sess` / `CompileScheduler` dependency (Principle 3). The orchestrator (`int::process_form`) handles dispatch + retry.
7. **`#[non_exhaustive]` DTOs include all error types.** `ExpansionError` is `#[non_exhaustive]` so adding new gap kinds or genuine error variants is non-breaking.
8. **Form-by-form, not pre-pass.** Per FIXME `sprints/fixmes/0005-spec-macro-availability-form-by-form.md`: there is NO defmacro pre-pass extraction. Each form is processed in source order; macros become available to subsequent forms only after their `defmacro` form is itself processed. The "module-wide availability" model in `spec/09-macros.md` §9.3.4 is to be revised — until then, the frontend does not implement it.

**FIXME 0175 — marshal-deps gap on `expand` invocation.** The `expand` function performs the structural traversal (children recursion, macro-head detection, depth-limit enforcement, quasiquote expansion) but does NOT call into the JIT'd macro body — it returns `Err(ExpansionError::Gap(ResolutionGap::MacroInMem(fq)))` for every macro head encountered. The live invocation path remains in `src/expander.rs` until `/arch` resolves FIXME 0175 (`design/arch/fixmes/0175-arch-frontend-expand-invocation-gap.md`): `cranelisp_runtime::heap_alloc` + signal handling cannot be reached from `cranelisp-frontend` under the current BC §1 dep-allowance, and the target invocation requires them. Likely resolution: a new `cranelisp-marshal` crate. When resolved, `expand` gains the body call and the `src/expander.rs` implementation deletes; the signature and uniform-Gap contract above stand and need no revision.

**Relationship to consumer crates.** Frontend's outputs are consumed by `cranelisp-typecheck` (`ParsedEntry` vectors fed into `check_forms` — see §2 + Decision 44) and by the integration layer (`src/cluster.rs::process_cluster` consumes per-clause `Defn`s built via `synthesize_macro_clause_defn` per Decision 21). Macro-resolver helpers (`parse_defmacro`, `synthesize_macro_clause_defn`, et al.) are pub-at-root for these two consumers and narrow back at FIXME 0098 Phase 2 close; the quasiquote helpers (`expand_quasiquotes`, `expand_quote_template`, `next_synthetic_span`) remain pub at root as the standing public quasiquote API used by user-authored macros and REPL `/expand`. See the lib.rs preamble §"Macro-resolver helpers — internal-but-exposed" for the disposition history.

**Per-surface documentation.** Like `cranelisp-types` (§7), this surface has no separate `facades/frontend.md` document — the source-side rustdoc (crate-root `//!` narrative in `crates/cranelisp-frontend/src/lib.rs` plus per-item `///` comments) IS the facade. Retired in S70 Phase B group B3-C following the S69 Sub 42 precedent per Principle 7 (single source of truth) and lived-experience cost of dual-maintenance. The `public-api.txt` baseline gates the surface at PR time; rustdoc-coverage is the source-side equivalent of the per-crate facade-compliance test for the other crates.

---

## 2. Typecheck — `crates/cranelisp-typecheck/`

**Bounded context.** Untyped AST becomes typed AST plus populated symbol tables. Typecheck infers types, resolves traits, classifies polymorphism, and analyses match exhaustiveness. Its results land in two places: directly on AST nodes (each node carries its inferred type and resolution choices), and in the per-module symbol-table view supplied by the caller. The crate carries no shared session state and no cadence; it is invoked synchronously, one form at a time, by the integration layer.

**In-scope.**
- Type inference (Hindley-Milner) over every AST variant
- Trait declaration, impl recording, method resolution
- Constrained-polymorphism detection and monomorphisation analysis
- ADT exhaustiveness checking
- Per-symbol callee extraction (writes into the symbol table for downstream scheduling)

**Out of scope.**
- AST construction (frontend)
- Code generation (backend)
- Pipeline scheduling, module loading, REPL session (int)
- Runtime helpers (intrinsics — §4b)

**What crosses the boundary.**
- **Inputs**: the full cluster's `ParsedEntry` list (produced by repeated `cranelisp_frontend::build_form` calls, accumulated by the orchestrator); a symbol-table-access window (`SymbolTableAccess`) supplied by the caller, abstracting staging-vs-live; read-only `SymbolTables` (all other modules' tables) and the session-level `ModuleAliases` table.
- **Outputs**: in-place AST annotations and per-symbol Pass-2 side products written onto staging `ModuleEntry::Def` fields; a `CheckResult` (last-form display info + cluster-scope warnings) on success; a `CheckError` (recoverable `Gap`, or non-recoverable `TypeError`) on failure.
- **Window types**: typecheck consumes a symbol-table-access window passed by the caller (`SymbolTableAccess`, with `SymbolTableRead` / `SymbolTableMut` borrow guards and the unioned `View` read surface). It exposes no windows of its own.

**Cluster-atomic entry surface.** The typecheck entry surface is **one** free function per cluster — `check_forms(parsed: Vec<ParsedEntry>, ctx: &mut SymbolTableAccess, symbol_tables: &SymbolTables, module_aliases: &ModuleAliases) -> Result<(), CheckError>` — per Decision 44 (amended FIXME 0167 for Approach B + `SymbolTableAccess`; 2026-05-13 third amendment collapsing the prior two-pass facade split into a single function). A **cluster** is the unit of typecheck atomicity: one form (a non-`begin` REPL input), the contents of `(begin form₁ … formN)` (an explicit REPL cluster), or a file's non-structural forms (batch). The internal two-pass discipline (Pass 1 register signatures into staging, then Pass 2 check bodies against the unioned staging+live view — spec §5.13.1, supporting forward references / mutual recursion) is preserved as an implementation-phase ordering **inside** `check_forms`; it does not cross the boundary. There is no public pass discriminator and no public accumulator type — Pass-1-to-Pass-2 working state (`defn_type_vars`, default-method-defn deferrals, generalisation inputs) lives inside the one stack frame and is dropped when the call returns, closing the state-threading hole by construction (no working state crosses the facade because there is only one call). See the `check_forms` per-item `///` rustdoc in `crates/cranelisp-typecheck/src/lib.rs` (post-S72 W5 canonical; `facades/typecheck.md` retired) for the per-item contract and Decision 44 for the rationale + rejected alternatives.

**Staging-vs-live abstraction (`SymbolTableAccess`).** The orchestrator (`int::process_cluster`) hands typecheck a `SymbolTableAccess` window. In `Cluster` mode the read accessor returns a `View` unioning an orchestrator-owned transient staging table over live (staging-first); the write accessor returns the staging table. In `Live` mode (REPL introspection, fine-grained drivers) both accessors hit the live per-module table directly. Typecheck calls these accessors uniformly — the ~91 register-call sites and ~51 read-access sites in the crate are unchanged; the staging-vs-live surgery is absorbed entirely in the accessors, so typecheck cannot distinguish staging from live. There is a **single pair** of read+write borrow guards crossing or touching the surface — `SymbolTableRead` / `SymbolTableMut` — returned by both the orchestrator-side `SymbolTableAccess` accessors and the interior `TypeCheckEnv` accessors; no parallel `pub(crate)` pair exists (S72 W2 /review I-2; user-arbitrated unification under the `SymbolTable*` names — the type names *what* is accessed, not the access mode). The `View` read surface lives in `cranelisp-types` (multi-consumer); the `SymbolTableAccess` enum and the two borrow guards are typecheck-interior types per Principle 15 (single implementation-crate consumer, `int`).

**Public surface (canonical enumeration).** The crate-root rustdoc (`crates/cranelisp-typecheck/src/lib.rs` `//!` preamble) is the single source of truth for the as-designed public boundary; `crates/cranelisp-typecheck/public-api.txt` is the authoritative as-built enumeration, gated at PR time per the baseline-diff discipline (see `design/arch/CLAUDE.md` §"Baseline-diff discipline"). Per-item rustdoc carries the per-item contract (`pub fn check_forms`, `pub struct CheckState`, `pub enum SymbolTableAccess`, `pub enum CheckError`, the `trace` module, `pub fn advance_next_id_past_table`, etc.) — visit them with `cargo doc -p cranelisp-typecheck --no-deps`. `TypeCheckEnv` narrows to two public methods (`new`, `next_type_id`); per-symbol lookups, module-table accessors, and the cluster-introspection helpers become `pub(crate)` callee-side helpers (all callers are inside `check_forms`'s frame). `register_builtins`, `register_imports`, and `register_exports` are **struck** from the surface entirely (not demoted): synthetic-module assembly is `int`'s session-init concern (FIXME 0242), and import/export registration is frontend's StructuralDecl concern processed before typecheck runs — `ParsedEntry` has no `Import`/`Export` variant, so typecheck never receives one.

**Types originated here.** Per Principle 15's placement heuristic, `CheckResult`, `CheckError`, `CheckState`, `TypeCheckEnv`, `SymbolTableAccess`, `SymbolTableRead`, and `SymbolTableMut` live in `cranelisp-typecheck` (referenced by `int` only). `ResolutionGap` is the cross-cutting exception — referenced by both the frontend facade (`ExpansionError::Gap`) and typecheck (`CheckError::Gap`) — so it lives in `cranelisp-types` per the multi-consumer rule; `View` likewise. `CheckResult` is pared to the two cross-cluster items the orchestrator surfaces to the REPL display layer (`display: Option<DisplayInfo>`, `warnings: Vec<Warning>`); per-symbol Pass-2 side products land on staging `ModuleEntry::Def` fields, not on `CheckResult` (invariant 3a). Multi-consumer dependency types (`Scheme`, `Subst`, `Type`, `TypeId`, `ResolvedCall`, `MethodResolutions`, `TypeDefInfo`, `DisplayInfo`, `MonoDefn`, `Warning`, `TraitDecl`, …) live in `cranelisp-types` because backend codegen also consumes them. No crate-root re-exports of `cranelisp-types` items (the legacy `CranelispError` / `TopLevel` convenience re-exports were removed S73 per Principle 15).

**FQTypeName binding at typecheck boundaries.** Per Decision 0047 + §7 ("FQTypeName binding"), every resolved-stage API on the typecheck surface that names a type uses `FQTypeName`; bare `TypeName` is reserved for the two exception classes (syntactic-lift sites at `check_form`; receiver-pinned helpers where `&self` IS the module context). Typecheck carries the largest /dev burden of the six crates' migration (~7 PIF conversions + ~3 syntactic-lift keeps + ~5 receiver-pinned keeps), but most of those APIs become `pub(crate)` under the `TypeCheckEnv` narrowing and stop crossing the boundary entirely.

**Bounded-context invariants.** These hold across sprints — the contract `cranelisp-typecheck` makes with the rest of the workspace:

1. **No code generation.** Typecheck never invokes Cranelift, never produces JIT or object output. Its product is annotated AST + symbol-table entries.
2. **No commits to live `SymbolTable` from `check_forms`.** Per FIXME 0160 + Decision 44 — `check_forms` is pure with respect to **live state**: it does not mutate the live `SymbolTable` nor any state visible outside the cluster. It MAY mutate the orchestrator-handed staging `SymbolTable` via the same accessor API used in committed-mode (`ctx.current_symbol_table_mut()`); typecheck cannot distinguish staging from live because the accessor abstracts the difference. Cluster atomicity is preserved because staging is orchestrator-local and is committed (drained into live) only on whole-cluster `Ok`. The orchestrator drops staging on the floor on any `Err`; on `Err(Gap)` it dispatches and **retries the whole `check_forms` call** against a fresh staging frame (no sub-cluster granularity). The live table is byte-identical to its pre-cluster state across any failure — preserving Decision 44's Principle 1 (decoupling) + Principle 7 (single durable source of truth) intent without inverting every register-call site. Resolved import bindings are installed by `int` (post-cluster-`Ok` arm), not by typecheck.
3. **Single source of truth via `defined_symbols()`.** Per Decision 22 — the codegen-compilable predicate is `SymbolTable::defined_symbols()`. Typecheck writes entries that satisfy or fail this predicate; it does not maintain a parallel store.

   3a. **Per-symbol Pass-2 side products land on staging `ModuleEntry::Def` fields; Pass-1-to-Pass-2 working state is internal to `check_forms`.** Two intra-pass data categories must be distinguished (their conflation produced the state-threading hole that triggered Decision 44's third amendment): (i) **per-symbol Pass-2 side products** — the data that survives the cluster and is consumed downstream (codegen, call graph, REPL display) — are written into the staging `Def` entry's existing fields during Pass 2 (call-graph edges into `Def.callees` per Decision 21; expr-type annotations onto `Def.ast` per Decision 22; mono entries staged as additional mangled-name `Def` entries; per-form `method_resolutions` / `expr_types` / `mono_defns` / `callees`). The orchestrator's drain into live carries these with each entry. (ii) **Pass-1-to-Pass-2 working state and cluster-scoped algorithmic intermediaries** (`defn_type_vars`, default-method-defn deferrals, generalisation inputs, multi-sig variant accumulation, the deferred-resolutions working set) are internal to `check_forms`'s stack frame — no `&mut ModuleCheckAccumulator` parameter, no public accumulator type — constructed on entry, consumed across the Pass 1 → Pass 2 boundary internally, dropped on return. Cross-symbol bookkeeping the orchestrator itself collects (warnings, resolved-import bindings, introspection records) is `int`-side data surfaced via the cluster return shape — see `facades/int.md` §"Cluster orchestration result".
4. **TC-sourced call graph.** Per Decision 21 — call-graph edges are extracted during typechecking from method resolutions. The per-symbol `callees: Vec<FQSymbol>` is the call graph; the rich `CallGraph` (with tail-position info) is for within-module codegen analysis.
5. **Trait method dispatch via `ResolvedCall::TraitMethod`.** Typecheck always emits `TraitMethod` for trait-dispatched operators; backend handles lowering. Typecheck stays clean of backend-specific concerns. The prior `(TraitName, Symbol, TypeName) → primitive` collusion-table approach in backend is retired per Decision 43 — backend has no trait knowledge; primitive emission goes through `cranelisp-primitives` + `cranelisp-intrinsics` directly.
6. **Constraint propagation in `generalize`.** Per Decision 19 — `Scheme.constraints` is populated by collecting trait constraints from active type variables during generalisation. Non-empty constraints mark a constrained polymorphic function (monomorphised at call sites).
7. **TC error rollback via cluster-atomic staging-drop.** `check_forms` allocates type vars within `CheckState`; on `Err` the orchestrator-owned transient staging table (Decision 44) is dropped and the live table is byte-identical to its pre-cluster state — that staging-drop IS the typecheck-state rollback. There is **no** caller-driven snapshot/restore: the `snapshot`/`restore` primitive and the `ReplSnapshot` type were deleted as dead code in S73 (purge Wave 3), superseded by this mechanism. The type-var pool (`next_id`) is monotonic and intentionally NOT rolled back across the retry boundary — fresh vars from a failed attempt are abandoned (allocation is cheap; monotonicity preserves the TypeId-consistency invariant).
8. **FQ resolution surfaces via `CheckError::Gap` — the ONLY legitimate cross-module concern typecheck has.** When `check_forms` encounters an FQ symbol or FQ type reference whose target module is absent from `symbol_tables` (not yet typechecked), it returns `Err(CheckError::Gap(ResolutionGap::SymbolTypechecked(fq)))` or `Err(CheckError::Gap(ResolutionGap::Type(fqt)))`. This Gap return is the **replacement** for the struck import/export-registration machinery (see the struck `register_imports`/`register_exports` above): typecheck does not reach across to another module by registering imports — it surfaces the missing dependency as a `Gap` and lets the orchestrator load and typecheck that module, then resumes. Typecheck does NOT block, does NOT call the scheduler, does NOT register modules — it surfaces the dependency to `int::process_cluster`, which catches the gap, loads + typechecks `fq.module`, and retries the whole `check_forms` call (via `handle_gap`). It asks for `ResolutionGap::SymbolTypechecked` (not `SymbolInMemory`) for value references because typecheck needs only the entry's `Scheme`, not its compiled code (macros are already expanded by the time `check_forms` runs). While following an FQ reference, typecheck consults the read-only `module_aliases` parameter to substitute import/export aliases for a `module_path` prefix per §8.6.6 — it follows aliases, it does not populate them.
9. **No `Sess` / `CompileScheduler` dependency.** Same as frontend — typecheck stays a pure function from inputs (`ParsedEntry`, `SymbolTableAccess`, `SymbolTables`, `ModuleAliases`) to outputs (`CheckResult` or `CheckError`). Principle 3.
10. **Module locality — typecheck never iterates the universe of modules.** Per Principle 17, every cross-module access fits one of four principled shapes; unbounded scans of the module set for short-name resolution, impl resolution, or method-of-type aggregation are forbidden. The four shapes: (1) **unqualified short-name lookup** — current module's view only (staging ∪ live); if the entry is `ModuleEntry::Import { source }`, chain-follow `source.module` one edge at a time to the canonical entry — never iterate the module set; (2) **qualified (FQ) lookup** — direct, single named module; (3) **impl resolution** — chain-follow the trait reference back to its defining module (shape 1) and probe that one module for `impl$FQTypeName$FQTraitName` (storage placement is the trait's defining module per Decision 0045 — no closure walk, no cycle detection); (4) **bulk introspection** — current module only; multi-module aggregation is composed at the orchestrator (session/REPL) layer, not inside `check_forms`. Mutating writes always go through `ctx.current_symbol_table_mut()`; a typecheck pass MUST NOT mutate a foreign module's table directly. `ModuleEntry::TraitImpl` writes target the trait's defining module (Decision 0045) — the orchestrator selects the target table by chain-following the trait reference at write time, identically to the read side (Decision 0046 retargeting). This invariant is the **structural prerequisite** for invariant 2's cluster-atomic guarantee: the `SymbolTableAccess` accessor surgery only delivers atomicity if every read and write actually flows through it; the absence of orphaned direct-module pierces is what makes that the case. Compliance with Principle 17 and compliance with Decision 44 are the same property viewed from two angles.

**Module-locality rationale (Principle 17 + Decisions 0044/0045).** The "search every module for a short name" pattern is module-system-shaped wrong: the language's visibility rules (spec §5.11, §8.3) already decide which names are reachable from the current module, and an unbounded scan disregards them. The prototype carried 40+ direct module-set accesses across the typecheck crate — short-name lookups iterating every loaded module, `find_impl_for_type` scanning the whole module set, cross-module mutating writes — each violating the spec's visibility rule and blurring the cluster-atomic surface. The remediation encodes the visibility rule in the access pattern: a name is reachable from the current module iff it is local, imported, or imported transitively, and typecheck walks that bounded set via per-symbol point-to-point chain-follow (one edge at a time, terminating at the canonical non-`Import` entry; no closure walk, no cycle detection) rather than the universe. `Import` covers both private (`(import …)`-form) and public (`(export [foreign-sym])`-form, formerly `Reexport`) edges — visibility is a per-entry orthogonal axis, not a separate variant (see §7 "Visibility is per-entry"). Synthetic modules (`primitives`, `macros`) have empty `imports`/`exports` by construction and reference cross-module symbols fully-qualified at registration time, not via short-name resolution. This is why the boundary lies at module-locality: it is the structural prerequisite that makes Decision 44's cluster-atomic shape actually atomic — the `SymbolTableAccess` choke point only buys atomicity if no read or write bypasses it.

**Per-surface documentation.** Like `cranelisp-types` (§7), `cranelisp-frontend` (§1), and `cranelisp-platform` (§5), this surface has no separate `facades/typecheck.md` document as a permanent record — the source-side rustdoc (crate-root `//!` narrative in `crates/cranelisp-typecheck/src/lib.rs` plus per-item `///` comments) IS the facade. Retired in S72 Wave 5 following the S69 Sub 42 / S70 Phase B / S71 Wave 4 precedents per Principle 7 (single source of truth) and the lived-experience cost of dual-maintenance — the 4th data point of the facade-retirement pattern. The cross-surface narrative (this section), invariants 1–10, and the module-locality rationale live here in BC §2; the per-item contracts, "types originated here" placements, and per-public-item invariants live in the source rustdoc. The `public-api.txt` baseline gates the surface at PR time per the baseline-diff discipline; rustdoc-coverage is the source-side equivalent of the per-crate facade-compliance test for the other crates.

---

## 3. Backend — `crates/cranelisp-backend/`

**Bounded context.** Typed AST becomes executable code. The backend translates symbol-table entries into Cranelift IR and produces compilation artefacts: in-memory machine code for direct execution, object files for linking, and the cache pair (metadata + object) for re-use across sessions. There is one compilation entry point regardless of mode; mode (in-memory vs object) is a property of the Cranelift module supplied by the caller, not a parameter on the entry point. The crate has no cadence; multiple compilations may run concurrently with disjoint inputs.

**In-scope.**
- IR emission for every spec-defined construct
- RC discipline at the call boundary (callee owns its heap parameters)
- In-memory artefact production with reclaim on drop
- Object-file production
- Cache read and write
- Per-module link binding for cross-module call indirection

**Out of scope.**
- Type inference (typecheck)
- Macro expansion (frontend)
- Pipeline scheduling (int)
- Runtime helpers (intrinsics — backend declares them as imports; §4b) and user-callable primitives (primitives — §4a)

**What crosses the boundary.**
- **Inputs**: a symbol-table view; a Cranelift module to emit into.
- **Outputs**: for JIT mode (per Decision 41 per-symbol cardinality — typecheck cluster commit followed by N parallel backend workers, each calling `compile_to_module` for one assigned symbol), a **per-symbol GOT-slot write** (`got().store_slot(slot, ptr)` — D41 #2, backend's own write) plus a value-returned `CompilationArtifacts` carrying the always-created introspection contributions (`clif_ir`, `code_size`, `compile_duration`) for the caller to retain or drop; on-demand disassembly via the separate `produce_disasm(fq, code_size, symbol_tables)` free function with a caller-supplied `code_size` (S75 W2 Finding-C). The **caller composes the `Code` lifecycle owner** (`Code::Jit` from its owned `Arc<Jit>`, `Code::Linker` from the `LinkerArtefact`) and installs it via `SymbolTable::write_code` — backend never constructs `Code` (it only borrows `&mut M` and never owns the `Arc<Jit>`; S75 W2 Finding-A — symmetric with the cache-hit path). Backend does not name the integration-layer `Introspection` type at its boundary; the value-returned artefact replaces what would have been a third direct-write that inverted the DAG. For object mode (per-module), the object artefact and the cache pair.
- **Window types**: none.

**`symbol_tables` is the single codegen source; object mode is a finalize-time difference only.** `compile_to_module<M>` makes every codegen decision from `symbol_tables` (+ `module_aliases`): callee resolution + `got_slot`, arity from `entry.scheme`, dispatch shape from `entry.kind` (user / primitive → GOT-indirect against `__cranelisp_got_{M}`; intrinsic → `Linkage::Import` by name), `DefKind::Constructor` metadata. The emitted CLIF is byte-identical across JIT and object (invariants 1 & 6); object mode differs only at finalize — it emits the `__cranelisp_got_{M}` data symbol with relocations + the `.meta.json` sidecar (§"Object file contract" in the backend facade) — and **fn pointers are a resolution-time concern** (JIT finalize / cache `Linker` / system `ld`), never a codegen concern.

**Minimal JIT-setup boundary (S75 — `Jit` shrinks to construct + handoff + reclaim).** In the converged design, `compile_to_module` drives declare → compile → finalize **internally**; the caller (int) only constructs the `Jit`, hands off `jit.jit_module()`, and holds `Arc<Jit>` for reclaim. The boundary `Jit` surface is therefore minimal: the constructor(s), the `jit_module()` handoff accessor, and `Drop`. The JIT-orchestration methods (`declare_intrinsics`, `declare_functions{_prefixed}`, `declare_imported_functions`, `compile_defn`, `finalize{_and_get_ptr}`, `build_compile_context`, `build_shared_isa`) + the module-level `intrinsic_symbols` / `build_isa` / `declare_intrinsics_generic` + the JIT-setup DTOs (`IntrinsicSymbol`, `IntrinsicFuncIds`, `IntrinsicIds`, `CompileArtifacts`) are **internal (`pub(crate)`)** — they are exercised only by int's PARALLEL hand-rolled REPL path (`src/pipeline.rs`), which collapses into `compile_to_module` in S77. **Target (S77):** a single `Jit::new(symbol_tables)` derives the entire JIT symbol set from the same `symbol_tables` that feeds codegen — GOT data symbols from `symbol_tables[M].got().base_ptr()` (including the `primitives` synthetic module, preserving the Decision-0048 dep-ban: backend reaches primitives only through the type-erased mount), and intrinsic `Import` targets from the intrinsics-published `cranelisp_intrinsics::INTRINSICS_TABLE` (the Decision-0048-for-intrinsics forward commitment; see §4b). int assembles nothing. `CodeFinalizer` stays `pub` — it is the `compile_to_module<M: Module + CodeFinalizer>` generic bound, named in the entry's own signature. The S77 target collapse assumes constructor `Def`s are got-slotted callable (`(map Some list)` reaching the ctor via its `got_slot`) — the typecheck + int enablement for that is tracked by **FIXME 0249** (mirrors the primitives Decision 0048 got-slotting precedent; see `design/backend/compile-to-module.md` §2.6.5).

**What crosses the boundary (cross-surface summary).** Backend is driven by the integration layer (`int`) and observed/relied-upon by it; nothing downstream of backend exists in the workspace. The surfaces that cross:

- **The three codegen entries** — `compile_to_module<M: Module + CodeFinalizer>` (the sole CLIF emission path, generic over the `Module` instance the caller supplies — `JITModule` per-symbol or `ObjectModule` per-module), `load_object` (the JIT-mode cache-hit entry returning a `LinkerArtefact`), and `produce_disasm` (on-demand machine-code disassembly with a caller-supplied `code_size`). Plus the ISA constructor `build_isa`. There is no separate object-compile entry — the object path is `compile_to_module::<ObjectModule>` + caller `finish().emit()`.
- **The lifecycle types `Code` / `Jit` / `Linker`** — backend *names* `Code` (its variants wrap backend-owned `Jit`/`Linker`) but the **caller composes** both `Code::Jit` (from its owned `Arc<Jit>`) and `Code::Linker` (from the `LinkerArtefact`); backend only borrows `&mut M` and writes the GOT slot. `Jit`/`Linker` are opaque retention newtypes (custom `Drop` reclaims executable pages / mmap).
- **The cache contract a driver drives** — backend exposes cache read/write and `.o`/sidecar pairing through the `cache` submodule (an internal implementation mechanism, NOT a separate boundary surface — see "Per-surface documentation" below); the integration layer's nice workers + cache-hit path drive it. The cache's own internal invariants live in the cache submodule rustdoc, not here.
- **The GOT-population observer** — `register_got_observer` + `GotEvent`/`GotEventTag`/`GotProvenance`/`GotObserver`: an extension point (not diagnostics) in the same shape as intrinsics' `IoObserver`; events fire from `compile_to_module`'s GOT-slot-store site and `load_object`'s slot population. Observer state lives in int.
- **The heap-layout ABI** — backend reads the runtime heap layout through intrinsics' named extern functions and the blessed layout-ABI consts (§4b invariant 2); it emits offset-keyed loads/stores against the same `#[repr(C)]` contract intrinsics owns. This is a value-passing ABI, not a Rust-type surface.

**Bounded-context invariants.** These hold across sprints — the contract `cranelisp-backend` makes with the rest of the workspace (folded from the retired `facades/backend.md` §"Bounded-context invariants" at S75 W5b; per-item contracts + the object-file contract + the codegen-entry signatures live in the `crates/cranelisp-backend/src/lib.rs` `//!` + per-item `///` rustdoc, which is the canonical surface):

1. **Single compilation entry point per mode (Decision 23).** `compile_to_module<M: Module + CodeFinalizer>` is the sole CLIF emission path. Object vs JIT differs only in the `Module` instance the integration layer supplies; CLIF emission is byte-identical. Mode is NOT a function parameter.

2. **Uniform consuming calling convention (Decision 24).** Every call site emits identically for RC management. Caller transfers ownership of heap-typed args (inc-before-call for non-last-use, direct transfer for last-use); callee owns heap params. Data constructors, user fns, trait methods, builtins, and externs all follow the same rule. There is no "borrowing" classification.

3. **Compiled-code lifecycle owner lives on `ModuleEntry::Def.code`; fn ptr lives in `SymbolTable.got()` indexed by `got_slot` (Decisions 25 + 41).** Backend writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(slot, ptr)` (D41 #2). The **caller** composes the `Code` lifecycle owner and stores it (D41 #1): `Code::Jit(Arc<Jit>)` from the `Arc<Jit>` it owns after a `compile_to_module` call, `Code::Linker(Arc<Linker>)` from the `LinkerArtefact` `load_object` returns. Backend cannot construct `Code::Jit` — it only borrows `&mut M` and never owns the `Arc<Jit>` (symmetric with the cache-hit path; S75 W2 Finding-A). The GOT is the **single source of truth** for callable addresses; `Code` carries lifecycle ownership only (no per-variant `ptr`). There is no separate `compile_to_object` backend free function (the object caller finalises the `ObjectModule`); no `JitArtefact` return shape.

4. **`defined_symbols()` is the codegen-compilable predicate (Decision 22).** `compile_to_module` trusts the contract: a `names` entry that `defined_symbols()` would not include errors (typed `CompilationError`) rather than synthesising. One filter, exposed on `SymbolTable`, consumed identically by callers and the backend's internal loop.

5. **Per-symbol reclaim safety (Decision 41 §"Safety invariant").** Custom `Drop for Jit` calls `unsafe JITModule::free_memory()`. The "no derived fn pointer reachable at refcount 0" invariant is upheld by int's discipline — every derivative pointer lives behind an `Arc` on `ModuleEntry::Def.code`; GOT slots are atomic-swapped on REPL redefinition before the old `Arc` drops; language-level fn values are heap closures that dispatch through the GOT, not raw code pointers. Backend relies on this discipline; it does not enforce it.

6. **Two-GOT model, one CLIF (Decision 23).** The same `Linkage::Import` reference against `__cranelisp_got_{M}` appears in every CLIF emission. JIT mode resolves via int's `JITBuilder::symbol_lookup_fn` returning `SymbolTable[M].got.base_ptr()`; `--link` mode resolves via the `.o` data-section GOT defined as `Linkage::Export` (Decision 36). Backend does not branch on mode; the `Module` impl supplied at finalize determines resolution.

7. **Bare-name + Local linkage uniformly (Decision 36).** Every user function is `Linkage::Local` with a bare-name symbol. No `user`/`main` special case. The `--link` mode `_main` alias is int's job, not backend's.

**Per-surface documentation.** Like `cranelisp-types` (§7), `cranelisp-frontend` (§1), `cranelisp-platform` (§5), `cranelisp-typecheck` (§2), `cranelisp-intrinsics` (§4b), and `cranelisp-primitives` (§4a), this surface has no separate `facades/backend.md` document — the source-side rustdoc (crate-root `//!` narrative in `crates/cranelisp-backend/src/lib.rs` plus per-item `///` comments) IS the facade. Retired in S75 Wave 5b (7th data point of the facade-retirement pattern) per Principle 7 (single source of truth) and the lived-experience cost of dual-maintenance. The cross-surface narrative (this section §3), the "what crosses the boundary" summary, and invariants 1–7 live here in BC §3; the per-item contracts (the three codegen entries, `Code`/`Jit`/`Linker`, errors, the GOT-observer extension point, heap classification, the object-file contract) live in the source rustdoc. The `public-api.txt` baseline gates the surface at PR time per the baseline-diff discipline; rustdoc-coverage is the source-side equivalent of the per-crate facade-compliance test for the other crates.

The cache submodule (`cranelisp_backend::cache`) was the 8th retirement data point (one crate, two facade files — `facades/backend-cache.md` retired alongside `facades/backend.md` at S75 W5b). **The cache is an implementation detail of the backend bounded context, NOT a separate bounded context** — there is no §3a and no BC-level cache entry. Its 5 internal implementation invariants (`Linker` is the only mmap-holder; `CacheManifest` is the single index; cache-validity checked at every hit attempt; `CACHE_FORMAT_VERSION`/`CACHE_SCHEMA_VERSION` independence; no re-codegen on cache-hit) and the four-submodule shape (`linker`/`manifest`/`object`/`serialize`) live in the cache submodule rustdoc (`crates/cranelisp-backend/src/cache/mod.rs` `//!` + per-submodule `//!` + per-item `///`), where a reader of the cache mechanism expects to find them — they are not contracts the rest of the workspace reasons about at the bounded-context boundary.

---

## 4a. Primitives — `crates/cranelisp-primitives/`

**Bounded context.** Spec-defined operations callable from user code via the `primitives/<name>` module path. Primitives are language-level: they appear in the symbol table, they have GOT slots, they are addressable as values (`(let [f +] (f 1 2))` reads a fn pointer from the GOT slot and indirect-calls it). Backend MAY substitute inline CLIF at known direct call sites via a name-keyed substitution table; the named fn pointer is a legitimate fallback for indirect call sites. The crate has no trait knowledge; trait dispatch resolves at typecheck/stdlib level, and the resolved target — an impl body — calls primitives by name. Per Decision 43 the previous combined `cranelisp-runtime` BC retires; this section and §4b replace it.

**Internal cadence.** None. The crate is a leaf — extern fns called from JIT-emitted code or from user code via GOT-indirect call. No state machine; no scheduling.

**In-scope.**
- Integer / float / bool primitive operations (arithmetic, comparison, logical)
- Primitive type conversions (`int_to_string`, `parse_int`, `float_to_string`, `bool_to_string`, …)
- The named `extern "C"` form is *the* addressable backing for each primitive; no `cranelisp_op_*` parallel form (per Decision 43's Phase 4 deletion)

**Out of scope.**
- Code generation (backend)
- Backend-emitted-call targets (intrinsics — §4b)
- Trait dispatch knowledge (typecheck + stdlib)
- Session mount + concretization (int — int clones `cranelisp_primitives::PRIMITIVES_TABLE` and calls `into_concrete::<Code, ()>()` at session init; the `()`-flavoured static is owned here, the `<Code, ()>` concretization is int's)

**What crosses the boundary.**
- **Outward**: the static `PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>>` (the synthetic `primitives` module's symbol table + the shared `Arc<GotTable>`); behind it, an `extern "C"` symbol surface — primitives by their kebab-case symbol name, reachable only via GOT slots.
- **Inward**: identifier newtypes + `SymbolTable`/`ModuleEntry`/`DefKind` etc. from `cranelisp-types` (boundary); the runtime substrate from `cranelisp-intrinsics` — the allocator and the blessed **heap-layout-ABI consts** (`HeapString::{LEN_OFFSET, DATA_OFFSET}`, `vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}`) plus drop/RC/panic helpers (FIXME 0245). **Nothing from `cranelisp-backend`** — `primitives ⟂ backend` (S73 sever; FIXME 0244 made every entry `code: None`, so primitives never names `Code`).
- **Window types**: none.

**Evolution driver.** Spec-driven — new primitives appear when the spec requires them.

**Session-integration contract (asserted-live).** `CompilerSession` startup holds a `SymbolTables<Code, ()>` map, so it concretizes the `()`-flavoured static `PRIMITIVES_TABLE` to `<Code, ()>` before inserting it at `ModuleFullPath::primitives()`. It does so via `SymbolTable::into_concrete::<Code, ()>()` — the same `cranelisp-types` bridge the cache-restore path uses (`crates/cranelisp-types/src/module.rs`). `into_concrete` maps each entry's `code: Option<()>` to `None::<Code>` (every primitives entry is already `code: None`) and carries `got: self.got` through verbatim, so the inner `Arc<GotTable>` is reference-count-shared with the static-memory backing — one and only one `GotTable` for primitives in the process. This `<(),()>`→`<Code, ()>` bridge is an **exercised contract today, not forward work** (Ruling 1, S74 Phase 2): the cache-restore hot path calls `into_concrete::<Code, ()>()` explicitly (`session_v4.rs`, `worker.rs`) and `into_concrete` is defined and tested in `cranelisp-types`. The distinct seam FIXME 0242 defers is the typecheck-side `register_builtins` synthetic-module assembly, NOT the primitives `into_concrete` bridge. The reconciliation of the `int`-side primary-mount comment/call (which still spells the static as `<Code,()>` + bare `.clone()`, stale to the S73 `<(),()>` shape) is **int's to own** — folded into FIXME 0242's brief (same call site); the rustdoc assertion holds regardless, since both spellings produce the shared-`Arc<GotTable>` `<Code, ()>` table. From session-init onward, primitives dispatch is functionally equivalent to any other module via the standard cross-module GOT-indirect call sequence; backend's `symbol_lookup_fn` carries no primitives-specific branch.

**Bounded-context invariants.** These hold across sprints — the contract `cranelisp-primitives` makes with the rest of the workspace (folded from the retired `facades/primitives.md` §"Bounded-context invariants" at S74 W3; per-item contracts + the static-init contract live in the `crates/cranelisp-primitives/src/lib.rs` `//!` + per-item `///` rustdoc, which is the canonical surface):

1. **User-callable surface.** Every fn populated into `PRIMITIVES_TABLE` is reachable from user code via the `primitives/<name>` module path. Adding a new primitive is a spec change; deleting or renaming one is a breaking change. Spec-driven evolution.

2. **Symbol-table addressable.** Every primitive has an entry in the synthetic `primitives` module's symbol table at `ModuleFullPath::primitives()`. Session init Arc-clones the static; entries are visible identically from every concurrent session. The entry's `got_slot: Some(N)` indexes the address — `(let [f +] (f 1 2))` resolves to the fn ptr at that slot.

3. **Uniform dispatch (Decision 0048).** From session-init onward, every primitive call from JIT-emitted code follows the standard cross-module GOT-indirect call sequence. Backend's `symbol_lookup_fn` carries no primitives-specific branch. `JITBuilder::symbol(name, ptr)` direct registration is reserved exclusively for intrinsics. **Structurally enforced** (Decision 0048 §"Structural invariant — backend dep-ban"): `cranelisp-backend` does not depend on `cranelisp-primitives`, so backend physically cannot name a primitive's extern fn — the GOT-indirect path is the only path available to it.

4. **No trait knowledge.** Per Decision 43 — backend's name-keyed substitution table maps `Symbol → cranelift_op` (e.g., `add-i64 → iadd`), never `(TraitName, method, TypeName) → Symbol`. Trait dispatch resolves at typecheck level; the resolved target is the impl body, which calls primitives by name; backend substitutes from the resolved name.

5. **Inline-substitution is optional.** Backend MAY substitute a primitive call with inline CLIF (e.g., `add-i64 → iadd`) at a known direct call site. It MAY NOT be required to do so — the named fn ptr in `PRIMITIVES_TABLE.got()` is a legitimate fallback for indirect calls (operator-as-value, GOT-indirect cross-module calls before linker resolution). Implementation choices live in `cranelisp-backend/src/primitives_inline.rs`.

6. **Process-static lifecycle.** `PRIMITIVES_TABLE` and its inner `Arc<GotTable>` are constructed once per process at `LazyLock` first-access; never reallocated; never invalidated. Each entry carries `code: None` (post-A2-reversal, FIXME 0244) — primitives have no per-entry reclaimable `Code` resource (the `LazyLock` owns the static fn addresses); the lifecycle category is *not* recorded as a `code` marker variant, it follows from `kind: DefKind::Primitive`. Decision 31's per-batch `JITModule` lifecycle does not apply — primitives are the **named exception**. Cache-hit reload (Decision 30) similarly carves primitives out — primitives are never cached (no `.meta.json`, no `.o`); the static is always present at session start.

7. **Spec-driven evolution.** New primitives appear when the spec requires them. The crate does not accrete primitives for backend convenience; that is what `cranelisp-intrinsics` is for. The categorical line (user-callable vs backend-emitted-call target) is the load-bearing distinction Decision 43 formalised and Decision 0048 makes operational.

8. **Consuming convention at extern boundary (Decision 24).** Every `pub(crate) extern "C"` fn MUST consume its heap-typed arguments — dec any heap arg it does not return. Internal Rust helpers may use any local convention; the extern boundary enforces consuming so backend's call sites can emit uniformly.

**Per-surface documentation.** Like `cranelisp-types` (§7), `cranelisp-frontend` (§1), `cranelisp-platform` (§5), `cranelisp-typecheck` (§2), and `cranelisp-intrinsics` (§4b), this surface has no separate `facades/primitives.md` document — the source-side rustdoc (crate-root `//!` narrative in `crates/cranelisp-primitives/src/lib.rs` plus per-item `///` comments) IS the facade. Retired in S74 Wave 3 (6th data point of the facade-retirement pattern; doc-only — primitives' source was aligned in S73) per Principle 7 (single source of truth). The cross-surface narrative (this section §4a), the asserted-live session-integration mount, and invariants 1–8 live here in BC §4a; the single-`pub static` shape, the static-init contract, the primitives inventory, the `code: None` lifecycle, the backend severance, and the Option-2 DCE-survival wording live in the source rustdoc. The `public-api.txt` baseline (nine lines — `PRIMITIVES_TABLE` + seven `pub mod` + crate root) gates the surface at PR time; the semantic surface (which primitives exist + their signatures) is governed by spec-conformance tests, not the Rust baseline.

---

## 4b. Intrinsics — `crates/cranelisp-intrinsics/`

**Bounded context.** Backend-emitted-call targets — runtime support code with stable ABI contracts called by JIT-emitted code or by the IO trampoline. Intrinsics are NOT callable from user code; not in any symbol table; not in any GOT. The ABI is tightly coupled to backend's codegen choices. The crate has no knowledge of compilation, scheduling, REPL, or development tooling; its job is to provide the language's runtime semantics in a way that depends only on the running program — not on how that program was loaded, who is observing it, or what process structure surrounds it. Diagnostic and observability surfaces are explicitly out: those are development concerns, not part of running a program. Per Decision 43 the previous combined `cranelisp-runtime` BC retires; this section and §4a replace it.

**Internal cadence.** Intrinsics hosts the **runtime cadence** — atomic RC operations interleaved with normal execution; fork-join scopes during parallel evaluation. This cadence is invisible outside the running program; it produces no handoffs to compilation or REPL.

**In-scope.**
- Heap memory model (allocation, layout — base-pointer convention per Decision 11)
- Reference counting primitives
- Drop glue helpers (consume_shallow, consume_io_tree, dec_shallow_io)
- String and vector runtime
- IO trampoline
- Fork-join evaluation cells (IVar)
- Marshal between language Sexp values and host Rust values
- Panic intrinsic for match exhaustiveness failure
- IO observer registration API (per Decision 40 — the registration site lives here; observer state lives in int)

**Out of scope.**
- Code generation (backend)
- User-callable primitives (primitives — §4a)
- Diagnostics, tracing, observability state (int — development concerns) — per Decision 40, the historical `trace.rs` and `io_trace.rs` modules relocate from runtime/intrinsics to int via the `IoObserver` callback contract. Intrinsics keeps only a ~50-line extension-point API parallel to `register_alloc_callback`.
- Platform DLL loading and lifecycle (int)
- Pipeline state (int)

**What crosses the boundary.**
- **Outward**: an `extern "C"` symbol surface plus a small set of host-callback structures used for inversions of control (e.g., when platform DLLs need runtime services); plus the `IoObserver` registration API. **Plus the published flat catalog `INTRINSICS_TABLE` (TARGET-STATED; implementation S77).** See invariant 11 below.
- **Inward**: layout constants and identifier newtypes from `cranelisp-types`; the `IO_TAG_*` consts and `HostContext` from `cranelisp-platform` (consumed by the IO trampoline).
- **Window types**: write-once evaluation cells (IVar) held by the runtime cadence. The C-ABI surface itself is value-passing — heap pointers cross as integers, opaque to the consumer.

**Evolution driver.** Backend-driven — new intrinsics appear when backend codegen needs them; existing intrinsics evolve in lock-step with backend's emitted-call shapes.

**Cross-crate dependency edges (post-D43, S73-corrected).**

- **`cranelisp-primitives` depends on exactly two workspace crates**: `cranelisp-types` (boundary) and `cranelisp-intrinsics` (runtime substrate — the allocator + blessed heap-layout-ABI consts + drop/RC/panic helpers, FIXME 0245). It does **NOT** depend on `cranelisp-backend`: `primitives ⟂ backend` is a **bidirectional severance** (S73 — FIXME 0244 made every primitives entry `code: None`, so primitives never constructs or names a `Code` value, so it drops `cranelisp-backend` from its `Cargo.toml`; the reverse `backend → primitives` edge was already banned by Decision 0048 §"Structural invariant — backend dep-ban"). The previously-"permitted" `primitives → backend` edge (for the now-deleted `Code::Primitive` / the `Code` type-parameter mention) retires.
- **`cranelisp-intrinsics`** imports from `cranelisp-types` and `cranelisp-platform` only; it does NOT depend on primitives (the consumption is the other way — primitives is intrinsics' in-tree Rust consumer).
- **Backend's own dependency edges** (its current `cranelisp_primitives::*` Rust-path references in `intrinsic_symbols()` and the resulting `cranelisp-primitives` line in `crates/cranelisp-backend/Cargo.toml`) are stale residue of the pre-S73 model and are scheduled for deletion in a **future backend sprint** (deferred per the S73 re-scope; FIXME 0191). Until that lands, backend's manifest is red against the dep-ban; this is a known, sequenced carry, not a fresh defect. `int` depends on primitives (clone + `into_concrete` at session mount), intrinsics (JIT registration of fn ptrs + the trace/io_trace consumer side post-FIXME 0103), and backend.

**Bounded-context invariants.** These hold across sprints — the contract `cranelisp-intrinsics` makes with the rest of the workspace (folded from the retired `facades/intrinsics.md` §"Bounded-context invariants" at S74 W3; per-item contracts live in the `crates/cranelisp-intrinsics/src/lib.rs` `//!` + per-item `///` rustdoc, which is the canonical surface):

1. **Backend-emitted-call targets only.** Per Decision 43 — every fn in this crate is called by JIT-emitted code or by the IO trampoline; nothing here is callable from user code. Not in any symbol table; not in any GOT. Adding an intrinsic is a backend + intrinsics co-design; deleting one requires backend co-evolution.

2. **Representation containment.** Per `src/CLAUDE.md` "Heap Access" — within intrinsics, only `alloc.rs`, `heap_string.rs`, `vec_runtime.rs` define the layout constants (`HEAP_HEADER_SIZE`, field offsets). **Backend** reads the layout through the named extern functions, never by hard-coding offsets. **`cranelisp-primitives`** reads it through the blessed layout-ABI consts (`HeapString::{LEN_OFFSET, DATA_OFFSET}`, `vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}`) — the one sanctioned cross-crate reader of the offsets (FIXME 0245), and only via those single-source consts, never by re-deriving them.

3. **Atomic RC discipline (Decision 13).** RC inc/dec emit `atomic_rmw` at all rings, even Ring 1 single-threaded. Acquire fence on the free path before drop_glue reads object fields. Avoids an ABI break when concurrency arrives at Ring 4.

4. **Strings opaque to backend (Decision 12).** `HeapString` layout is intrinsics-owned. All string operations go through extern functions. Enables future rope upgrade.

5. **Embedded `drop_glue_ptr` in closures (Decision 11).** Closures carry their drop fn at offset 24 — `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`. The drop glue function is per-lambda generated by backend; null for closures with no heap captures. Cross-module closures self-describe; no side-table lookup required.

6. **Consuming convention at extern boundary (Decision 24).** Every `#[no_mangle]` extern function MUST consume its heap-typed arguments — dec any heap arg it does not return. Internal Rust helpers may use any local convention; the extern boundary enforces consuming so backend's call sites can emit uniformly.

7. **IO trampoline shallow dec (Decision 29).** `cranelisp_run_io` reduces IO trees node-by-node, consuming each outer allocation via `dec_shallow_io` — a distinct primitive from transitive `consume_io_tree` because field pointers are already re-owned by other holders during the walk.

8. **No state across sessions.** Stats accessors (`alloc_count`, etc.) are process-global — `int`'s `reset_counts` should be called at session start in test contexts. Production runs do not call `reset_counts`.

9. **Backend-driven evolution + dispatch asymmetry (Decision 0048).** Intrinsics changes are typically driven by backend codegen choices (a new RC inlining strategy, a new IO node, a new trampoline shape). The crate does not accrete intrinsics for spec convenience; spec-defined operations live in `cranelisp-primitives`. The categorical line is the load-bearing distinction Decision 43 formalised — and Decision 0048 reinforces post-S68 by binding the **dispatch asymmetry**: intrinsics use `JITBuilder::symbol` direct registration; primitives use the standard GOT-indirect path against `cranelisp_primitives::PRIMITIVES_TABLE`. This asymmetry is **intentional and load-bearing, not residual** (the §"Asymmetry justification" prose from the retired facade): primitives are a module (the synthetic `primitives` module, with a `SymbolTable` + GOT slots), so they ride the uniform GOT-indirect path; intrinsics are genuinely runtime-special — not a module, no `SymbolTable` entries, no GOT slots, called by emitted IR via extern-name relocation only. Forcing intrinsics through a synthetic GOT would introduce a categorical fiction (a module with no user-visible surface) for no semantic gain. The dispatch shape is the runtime embodiment of the categorical line; drifting either side toward the other reopens the BC overlap Decision 43 closed.

10. **No `FQTypeName` at the intrinsics public surface.** Per `/arch` Sprint 67 Phase 3 Wave 0 verification — zero pub-api items on this crate name `FQTypeName` or `TypeName`. Intrinsics operates on raw heap pointers + marshaling tags (Sexp tags, IO tags) drawn from `cranelisp-types`; types are never named at the surface. This holds across the FQTypeName-migration sweep (FIXME 0151); no boundary lifts on this crate.

11. **`INTRINSICS_TABLE` is the published flat Import-catalog (Decision-0048-for-intrinsics — TARGET-STATED; implementation S77).** Intrinsics self-publishes its catalog, applying the `primitives::PRIMITIVES_TABLE` precedent (Decision 0048) to intrinsics: `cranelisp_intrinsics::INTRINSICS_TABLE` is a **published flat catalog** `name → (signature, ptr)` that `cranelisp-intrinsics` owns. **CRUCIAL ASYMMETRY — `INTRINSICS_TABLE` is a flat catalog, NOT a mounted GOT-module like primitives.** Intrinsics are **Import-dispatched, not GOT-dispatched** (invariant 9 — intrinsics are not a module, have no `SymbolTable`, no GOT slots; backend emits `Linkage::Import` against the intrinsic name and the relocation resolves to the registered fn ptr). `PRIMITIVES_TABLE` is a `SymbolTable` + `Arc<GotTable>` mounted into the session's `SymbolTables` map because primitives ride the uniform GOT-indirect path; `INTRINSICS_TABLE` is a flat `name → (signature, ptr)` table consumed at **three resolution points, never at codegen**: (a) **JIT construct** — `JITBuilder::symbol(name, ptr)` registration at `Jit::new(symbol_tables)` setup (target S77; today backend's `pub(crate)` `intrinsic_symbols()` enumerates by Rust path); (b) **cache-hit load** — `Linker::register_symbol(name, ptr)` (`src/worker.rs:3545` today reads `intrinsic_symbols()`); (c) **`--link`** — the exe-bundle resolves the same names against the `cranelisp-intrinsics` archive. Backend's `intrinsic_symbols()` (now `pub(crate)`) is the transitional reader; the target reads `INTRINSICS_TABLE`. `backend::IntrinsicSymbol` retires as a *public* concept — the catalog's home moves to intrinsics. **`INTRINSICS_TABLE` does not exist in source today**; creating it in the intrinsics crate is **S77** (paired with the backend `Jit::new(symbol_tables)` collapse). This is the intrinsics-side forward commitment; backend's consumer side is captured in the backend facade §"Consumed surface". The §6 emitted-call ABI invariant (the by-string ABI) is **unchanged** — the catalog publishes the same names backend already emits; only the *enumeration source* moves (Rust-path → published table).

**Per-surface documentation.** Like `cranelisp-types` (§7), `cranelisp-frontend` (§1), `cranelisp-platform` (§5), and `cranelisp-typecheck` (§2), this surface has no separate `facades/intrinsics.md` document — the source-side rustdoc (crate-root `//!` narrative in `crates/cranelisp-intrinsics/src/lib.rs` plus per-item `///` comments) IS the facade. Retired in S74 Wave 3 (5th data point of the facade-retirement pattern) per Principle 7 (single source of truth) and the lived-experience cost of dual-maintenance. The cross-surface narrative (this section §4b), invariants 1–10, the cross-crate dependency edges, and the §"What crosses the boundary" 0245 contract live here in BC §4b; the per-item contracts (allocator family, drop helpers, IO trampoline, IVar, panic, IO-observation extension point, `HeapString`/`vec_runtime` layout-ABI consts), the forbidden-patterns rule, the `JITBuilder::symbol`-narrowing, and the Option-2 DCE-survival wording live in the source rustdoc. The `public-api.txt` baseline gates the surface at PR time per the baseline-diff discipline; rustdoc-coverage is the source-side equivalent of the per-crate facade-compliance test for the other crates.

---

## 5. Platform — `crates/cranelisp-platform/`

**Bounded context.** The shared interface contract between the cranelisp host binary and platform DLLs. Both the host and every platform DLL link against this crate; that is its purpose. It defines the C-ABI types, the wrappers that present those types safely in Rust, the layout constants both sides must agree on, and the macro DLLs use to publish their manifests. The crate owns no runtime state and no cadence.

**External audience — Principle 15 exception.** `cranelisp-platform` is the only implementation crate with an explicitly external audience: out-of-tree DLL authors (`cranelisp-stdio`, `cranelisp-fs`, etc.) depend only on this crate and would not otherwise see `cranelisp-types`. Per Principle 15's external-audience exception, the facade lives with the source rustdoc — Sprint 71 retired the standalone `design/arch/facades/platform.md` and folded its narrative into the crate-root `//!` preamble + per-item `///` docs (3rd data point of the facade-retirement pattern after `types.md` S69 + `frontend.md` S70). Audit F9 (S69) verified the exception's scope health: `SchedulingClass` and `PlatformError` are the only re-exports, both grounded in named multi-consumer + external-audience criteria.

**In-scope.**
- C-ABI contract types (`PlatformManifest`, `PlatformFn`, `HostCallbacks`) — all `#[repr(C)]`, layout-governed by `ABI_VERSION` per Principle 14
- Safe wrappers over the C-ABI representation (`CLInt`/`CLBool`/`CLFloat`/`CLString`/`CLIO`/`CLAdt`/`CLOwned`) — all `#[repr(transparent)]` over `i64`
- Layout constants shared between host and DLL (`ABI_VERSION`, `HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`, `IO_TAG_*`, `IO_EFFECT_RESOURCE_OFFSET`)
- The DLL manifest macro (`declare_platform!`) — the DLL-author entry point
- Host-side conversion of manifests into safe Rust descriptors (`manifest_to_descriptors`, `OwnedPlatformFnDescriptor`)
- Schema parser + marker-type pattern (Sprint 71) — `Schema`, `SchemaParseError`, `CLAdtType`, `AnyAdt`, `GetSchema`; the `declare_platform!` `schema:` arm auto-emits one marker type per declared ADT plus a `LazyLock<Schema>` static parsed once per DLL

**Out of scope.**
- DLL session lifecycle and retention (int — see §6)
- IO trampoline implementation (intrinsics — §4b)
- Per-DLL platform implementations (separate downstream crates)
- Spec definition of IO semantics (`/spec`)
- Type-signature parsing (`int`-side because it requires `cranelisp-typecheck` vocabulary that platform must not depend on per Principle 3 + FIXME 0155)
- Sig grammar routed through frontend+typecheck — Sprint 71 deferred; tracked by FIXMEs 0230 + 0231 + 0233
- Platform-as-module registration (each loaded platform getting its own `SymbolTable`+`GotTable`) — Sprint 71 deferred; tracked by FIXME 0233
- `.meta.json` schema for platform symbol-table caching — Sprint 71 deferred; tracked by FIXME 0232
- `/abi <TypeName>` REPL command — Sprint 71 deferred; tracked by FIXME 0234

**What crosses the boundary.**
- **Outward**: the C-ABI types, wrappers, constants, and macro to both host and DLL consumers.
- **Inward**: a small set of layout types from `cranelisp-types` — `SchedulingClass`, `PlatformError`, `Symbol`, `Span`, `ErrorLocation`, `HeapHeader`.
- **Window types**: none.

### Cross-cutting RC discipline

All heap CL types (`CLString`, `CLAdt<T>`, `CLIO<T>`) store **alloc base pointers** (the address of the `[total_size: i64][rc: i64][...]` heap allocation), NOT payload pointers. This matches the compiler's convention (Decision 0013); JIT-emitted code, the `CLString::from(&str)` builder, and the `CLAdt::from_raw` constructor all agree on what an `i64` "heap reference" means. `inc_rc` / `dec_rc` (per `CLHeap`; method-name asymmetry preserved per audit F5 R3) use `Ordering::SeqCst` to match Cranelift's `atomic_rmw` semantics — `Relaxed` is unsound for both directions (allows reordering relative to field reads, producing potential read-after-free).

`CLOwned<T>` is the host-side RAII wrapper for cross-callback RC discipline; the consuming variant `CLHeap::into_owned_consuming` is the consuming calling convention per Decision 0024 (used by platform externs that capture a heap parameter into an Effect closure — see `design/backend/ring2-rc.md` §10.4).

### Schema mechanism + marker-type pattern (Sprint 71 — layer 1)

`declare_platform!`'s optional `schema:` arm accepts a cranelisp-S-expression literal declaring ADT shapes. The macro auto-emits one zero-sized marker type per declared type (implementing `CLAdtType` with `const TYPE_NAME: &'static str = "..."`) plus a `LazyLock<Schema>` static parsed once at first access. DLL function signatures use `CLAdt<MarkerType>` for typed parameters; field access is `r.read_field::<CLInt>("w")` — the type-name comes from the marker via `T::TYPE_NAME`.

Layer 1 (the current sprint's scope) settles the schema format, marker-type pattern, `Schema` parser, `CLAdt<T>` wrapper, and the four field-access methods (`read_tag`, `read_field`, `own_field`, `construct`). **Layer 2** (deferred) is whatever ergonomic surface DLL authors get on top of layer 1 — a typed-newtype proc-macro generator, a `match-on-tag` macro, or stay-with-layer-1 if measurement shows the verbosity is acceptable. All three layer-2 options consume the same layer-1 schema this sprint settles.

### ABI versioning rationale

`ABI_VERSION: u32` is the single layout-discipline gate between host and DLL (Principle 14). Any layout-affecting change to a `#[repr(C)]` struct (`PlatformManifest`, `PlatformFn`, `HostCallbacks`) or a const the DLL reads by hard-coded offset (`HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`, `IO_TAG_*`, `IO_EFFECT_RESOURCE_OFFSET`, new `CL_TYPE_TAG_*` values) bumps the version. The host validates `abi_version` at DLL load and refuses mismatched DLLs with `PlatformError::AbiVersionMismatch`. Adding a method on `CLAdt` (no new `HostCallbacks` field, no new const) does NOT bump; adding a new pub `CL<T>` wrapper variant alone does NOT bump (Principle 14's `#[repr(transparent)]` exemption — the wrapper is a host-side typing convenience over an `i64`; the ABI is the `i64`). See `crates/cranelisp-platform/src/lib.rs` `ABI_VERSION` rustdoc for the full bump-rule enumeration.

Sprint 71 bumped `ABI_VERSION` from 1 to 2: `HostCallbacks` grew by `alloc_with_tag` + `validate_schema` for the ADT-marshaling surface.

### Future host-wiring story (forward-looking commitment)

Sprint 71 lands the platform-side API but defers the host-side wiring of `alloc_with_tag` / `validate_schema` callbacks. `HostCallbacks` is initialised with the in-crate **named-null callbacks** (`null_alloc_with_tag` panics with FIXME 0229 message; `null_validate_schema` returns 0). The construction path (`CLAdt::construct`) gates on the alloc callback via R1 wired-or-panic; read paths are callback-free (DLL-local schema lookup + transmute) and fully functional.

The host-wiring sprint (tracked as **FIXMEs 0229–0235**) lands:

- **0229** (`/int`) — populate `alloc_with_tag` + `validate_schema` callbacks; removes the R1 named-null-callback gates
- **0230** (`/frontend`) — expose `parse_type_expr` as a named API for platform sig parsing
- **0231** (`/typecheck`) — sig typechecking entry point against the importing platform's resolution context
- **0232** (`/backend`) — `.meta.json` schema extensions for platform module symbol-table caching
- **0233** (`/int`) — replace `parse_type_sig` with the frontend+typecheck path; register platforms as normal modules with their own `SymbolTable` + `GotTable`
- **0234** (`/repl`) — `/abi <TypeName>` emitter implementation against the schema DSL spec
- **0235** (`/qa`) — round-trip integration tests once host-side wiring lands

When `Fn a b` lands on the spec §10.10.1 platform-ABI permitted-types list (currently future work; not in this sprint's scope), `HostCallbacks` widens further with `rc_inc` / `rc_dec` / `invoke_closure` per Decision 0031's "Callback support (forward commitment)". The widening is a binary-incompatible ABI bump.

### Conformance triad coverage holes (audit C1–C5)

The S69 audit identified five conformance coverage holes the current triad (compile-time check + `cargo-public-api` baseline + facade compliance test) does not catch:

- **C1** — `CLHeap` method receiver/arity drift
- **C2** — `#[non_exhaustive]` annotation appearance/removal
- **C3** — `declare_platform!` macro arm drift (the F6 category, generalised; partially mitigated S71 Wave 2 by the new schema:-arm compile-fixture tests T17–T21)
- **C4** — `#[repr(C)]` struct field-order changes
- **C5** — `unsafe impl Send/Sync` removal on `PlatformFn` (the F3 category)

All five are tracked by FIXMEs 0224–0228 (`target: /qa`, deferred to a future conformance-triad-enhancement sprint).

### Bounded-context invariants

These hold across sprints — the contract `cranelisp-platform` makes with the rest of the workspace:

1. **Platform fn pointers live in `SymbolTable.got()`, indexed by `ModuleEntry::Def.got_slot`** (Decision 0026, S66 amendment + rollback `1dc57ae` — GOT is the single source of truth for callable addresses). Per spec §8.9.3, `(platform <name>)` registers a synthetic module at `symbol_tables["platform.<name>"]`; per-fn `ModuleEntry::Def` entries (with `kind: DefKind::PlatformEffect { scheduling_class }` distinguishing the platform origin) live in that synthetic module's `symbols`. The DLL handle is the lifecycle owner, retained on the platform module's own `SymbolTable.dll: Option<D>` field (per `crates/cranelisp-types/src/module.rs` `SymbolTable` rustdoc — `D: DllStore` generic). Drop semantics: dropping the platform module's SymbolTable drops the DLL. `scheduling_class` lives inside `DefKind::PlatformEffect { scheduling_class }` — a `DefKind` sibling variant promoted from the retired `PrimitiveKind` sub-discriminator (S69 Submission 36); ill-formed states ("a user fn with a scheduling class") unrepresentable.

2. **Stable C ABI at the DLL boundary.** `PlatformManifest`, `PlatformFn`, `HostCallbacks` are `#[repr(C)]`. Layout changes require an `ABI_VERSION` bump. `load_manifest` (int-side) validates the version on load and refuses mismatched DLLs with `PlatformError::AbiVersionMismatch`.

3. **Heap closures via GOT, not raw code pointers (Decision 0031 callback support — forward commitment).** When `Fn a b` is added to spec §10.10.1 (currently future work), platform fn arguments of fn type will pass as the heap closure address (Decision 0011 layout: `[header | code_ptr | drop_glue_ptr | captures...]`), NOT raw code pointers. Platforms will invoke retained closures via `HostCallbacks::invoke_closure` which dispatches through the GOT — so REPL redefinition retargets future invocations transparently. Retention requires `rc_inc` on storage, `rc_dec` on release.

4. **Marshaling tags shared with intrinsics.** The `CLType` impls use the same `i64` layout the intrinsics helpers expect. `CLString.0` is an alloc-base pointer to an intrinsics-allocated `HeapString` (Decision 0012 — string layout owned by `cranelisp-intrinsics`; Decision 0043 — intrinsics is the post-runtime-split host); `CLOwned<CLString>` participates in RC via `HostCallbacks.alloc` and the intrinsics-side dec path. There is one `i64` representation per CLType, agreed between platform and intrinsics via this crate's documented layout.

5. **`HostContext` initialised once per session.** `int` constructs `HostCallbacks` (with fn pointers into `cranelisp_intrinsics`) at `CompilerSession::new` and calls `HostContext::init` exactly once. Subsequent platform fn calls see the same callbacks for the session's lifetime. `HostContext` is `Send + Sync` by auto-derivation (`AtomicPtr<HostCallbacks>` is `Send + Sync`); `HostCallbacks` auto-projects `!Send + !Sync` (extern "C" fn pointers + raw allocations); `OwnedPlatformFnDescriptor` auto-projects `!Send + !Sync` (raw `ptr: *const u8`); `PlatformFn` carries explicit `unsafe impl Send + Sync` because the IO trampoline reads descriptors from multiple threads when dispatching Effect nodes (safety justified by BC §5 invariant 6 — no DLL unloading mid-session).

6. **No DLL unloading mid-session.** Once a platform DLL is loaded via `load_manifest`, it stays loaded until session shutdown. This is what makes the per-symbol GOT-slot pointer valid for the session — DLL pages are not unmapped while symbols reference them. Bounded leaks in `declare_platform!`'s `Box::leak` for `jit_name` bytes + per-fn parallel-array allocations are bounded by this invariant.

7. **`scheduling_class` declared by the DLL, consumed by the IO trampoline.** Per Decision 0026 — the IO trampoline reads `scheduling_class` off the destructured `DefKind::PlatformEffect` variant when it dispatches an Effect, and uses it to decide whether to spawn the work on the IO thread pool, the CPU thread pool, etc. Platform authors choose the class statically per fn via the `scheduling:` arm of `declare_platform!`.

8. **FQTypeName migration: zero-hit (Decision 0047).** Per Decision 0047 + §7 ("FQTypeName binding"), `cranelisp-platform` has zero public-surface changes and zero in-crate hits under the FQTypeName binding migration. The platform-DLL ABI uses S-expression type-signature strings (`PlatformFn.type_sig`) rather than resolved-stage type identifiers; resolution happens int-side downstream of `manifest_to_descriptors`. Migration disposition: no-op.

---

## 6. Binary / int — `src/` + `crates/cranelisp-exe-bundle/`

**Bounded context.** The integration layer wires the other surfaces into a deployable artefact and into a working REPL. It hosts three internal cadences with distinct execution shapes — compilation, REPL, watcher — coordinates the typed handoffs between them, owns all development tooling (slash commands, tracing, observability, introspection), and is the only crate that knows the concrete carrier of compiled code. The two crate paths (`src/` and `cranelisp-exe-bundle`) are one surface for triad purposes: a change touching both is one design/development/review cycle.

### 6.1 Internal cadences

**Compilation cadence.** Workers consume work packets off internal queues. Each worker claims a packet, processes it, publishes results into compilation-cadence windows, and notifies the scheduler. Closed-loop within the compilation subsystem; no external clock.

**REPL cadence.** Turn-based, synchronous to user input. One prompt → one parse → one submission to the compilation cadence → wait for result → display. Owns input handling, slash-command dispatch, prompt formatting, display, and the diagnostic surface (tracing, observability, introspection). Does not own compilation state — interacts with compilation only through handoffs.

**Watcher cadence.** OS file-change notifications arrive on a callback thread; the watcher captures them. The cadence is open-loop — its timing is dictated by the operating system. Captured changes do not act directly on compilation; they cross to the REPL cadence at a poll point and from there to the compilation cadence as re-register requests.

### 6.2 Inter-cadence handoffs

Handoffs are how cadences communicate. The pattern matters; the int facade pins the typed objects. Three patterns suffice:

- **REPL → compilation**: the REPL submits work (an evaluation, a module load) and waits. Compilation signals when ready.
- **Compilation → REPL**: each evaluation completes with either a displayable result or an error. The REPL formats and prints.
- **Watcher → REPL → compilation**: file-change events do not flow directly into compilation. They are polled by the REPL at prompt boundaries (avoiding mid-input interleave) and become re-register requests.

The runtime cadence (inside running programs) produces no handoffs to other cadences.

### 6.3 Within-cadence access

Each cadence accesses shared state only through typed handles owned by the cadence-relevant subsystem. There is no ambient session-state god-handle that any consumer can reach into; the access primitive is the window, and the windows are partitioned along cadence lines so that REPL state, compilation state, and watcher state cannot cross-contaminate. The int facade enumerates the windows; this document fixes the partitioning principle.

### In-scope

- The three cadences and their handoffs
- The compiler-shared state (symbol tables, code-pointer carriers, retention roots) decomposed into cadence-scoped windows
- Scheduler and worker subsystem (one ownership boundary, both priority and background work)
- REPL session, slash-command dispatch, prompt formatting, display
- Development tooling: tracing, observability, introspection
- Module loading orchestration; cache writer; save/regenerate
- File watcher
- DLL session lifecycle (handles retained for the session)
- The integration-layer concrete code carrier (the only crate that names it)
- CLI argument parsing
- Exe-bundle: link-target re-exports and the standalone-binary startup stub

### Out of scope

- Source parsing (frontend)
- Type inference (typecheck)
- Code emission (backend)
- Runtime helpers (intrinsics — §4b) and user-callable primitives (primitives — §4a)
- Platform ABI contract (platform)

### What crosses the boundary

- **Inward**: the public surfaces of all five other crates.
- **Outward**: nothing for other crates — the integration layer is the application root. The exe-bundle exposes a startup stub used only by the system linker.
- **Window types**: cadence-scoped. Not exposed to other crates.

### Known architectural constraints

- **Mutual-import deadlock**: two modules that import from each other deadlock the scheduler under the current scheduling strategy. A test-scaffolding workaround exists for the common case; lifting the constraint is module-system work and is out-of-scope here.

---

## 7. Cross-crate types — `crates/cranelisp-types/`

**Bounded context.** The single home for everything that crosses crate boundaries. The crate is *data and contract*: data types that flow by ownership across the workspace, and trait contracts that downstream crates implement to participate in cross-crate generic shapes. It depends on nothing within the workspace, and nothing outside is allowed to invert that direction. The crate is `/arch`'s own; consumers file `target: /arch` to add or change shapes.

**In-scope (catalog by family).**
- AST: expression trees, top-level forms, definitions, patterns, type expressions, trait declarations and impls, visibility
- Types: type representation, schemes, substitutions, identifiers
- Sexp: the s-expression value type and its marshal tag constants
- Symbol table: per-module symbol tables (generic over per-symbol code carrier and per-module link carrier), entry variants, definition kinds, primitive classifications, structural declarations, import/export specifications, macro clause information
- Heap layout: header type, heap classification
- GOT runtime memory: per-module code-pointer table
- Operator catalog: descriptor type and registry for the named primitive functions the language exposes
- Marshal: tag constants
- Scheduling: scheduling-class enum
- Identifier newtypes: symbols, type names, trait names, module names, fully-qualified variants
- Span and error: source spans, error and warning types
- Constants: shared sizes and thresholds

**Visibility is per-entry.** `Visibility` lives once, on the entry. Every `ModuleEntry` variant carries `visibility: Visibility`; there is no parallel exports-set sidecar (the prior `Reexport` variant retired — public re-export edges are `Import { source, visibility: Public }`). Cross-module slot lookups consult the per-entry visibility field directly. The visibility-bearing entry NEVER duplicates `visibility` inside an embedded payload: `ModuleEntry::Def` carries direct `visibility` (the outer `Defn` AST wrapper retired from the runtime model) and `ModuleEntry::TraitDecl` carries direct `visibility` + a slimmed `info: TraitDeclInfo` payload (S72 Phase B — the embedded AST `TraitDecl`'s own `visibility` was a duplicate and is no longer embedded). Same pattern at adjacent layers: `ModuleAliasEntry`, form-level `Defn` / `TraitDecl` (the frontend AST node, which keeps its own source-recorded `visibility`/`docstring`/`span`) / `ModDecl` / `ImportSpec` / `ExportSpec`.

**Docstring is a direct entry field.** Symmetric with visibility: every introspection-bearing `ModuleEntry` variant — `Def`, `SpecialForm`, `TypeDef`, `TraitDecl`, `IntrinsicType` — carries `docstring: Option<String>` as a **direct top-level field**, never nested in an embedded payload struct (single source of truth, Principle 7). S72 Phase B un-nested two cases: `TypeDef` (docstring moved out of `TypeDefInfo` — which now carries only structural metadata: name, type-param binders, constructor names) and `TraitDecl` (docstring moved out of the embedded AST `TraitDecl` — the entry carries `TraitDeclInfo` with only `name`/`type_params`/`methods`). `IntrinsicType` gained a direct `docstring` it previously lacked, so intrinsic scalar types (`Int`, `Bool`, `Float`, `String`) are introspectable like any other symbol. The slimmed `*Info` payloads parallel the `Def`-narrows-`Defn` precedent: the entry owns the canonical metadata; the payload carries only what the symbol table structurally needs.

**Two complementary stores, two purposes** — the form-record on `SymbolTable.{imports,exports}` is NOT the same thing as per-entry `visibility` on `ModuleEntry`:

- **`SymbolTable.imports: Vec<ImportSpec>` and `SymbolTable.exports: Vec<ExportSpec>`** are **form-records**: append-only, source-order, only user-authored forms. They are the source-of-truth for `.cl` regeneration (`repl/spec.md` §15.4), duplicate-form warnings, and form-by-form parse-time classification. The form-record records *what the user wrote*.
- **Per-entry `visibility: Visibility` on `ModuleEntry`** is the source-of-truth for visibility decisions: used by cross-module resolution's visibility-filter step and by the `/exports M` REPL command. Per-entry visibility records *the effect on each symbol* — one symbol per `ModuleEntry` slot, with its own visibility.

Both are load-bearing; neither retires the other. A `(export [a b c])` form persists one `ExportSpec` row in the form-record and toggles `visibility = Public` on the three corresponding `ModuleEntry` slots; a `(import …)` form similarly persists an `ImportSpec` row and installs per-entry `Import { visibility: Private, .. }` bindings. The two stores stay structurally consistent by parse-time installer convention.

**Module aliases live at session level**, not on `SymbolTable`. `SymbolTable` holds a single per-key store — `symbols: DashMap<Symbol, ModuleEntry<C>>` for value/type/trait bindings. The module-path-namespace aliases introduced by spec §8.3.4 (import alias) and §8.4.4 (export mount) live in a **parallel session-level table** `ModuleAliases = DashMap<ModuleFullPath, ModuleAliasEntry>`, keyed by the alias's **full path**. Aliases are not symbols (they name parts of a module path, not value bindings); keying by full path lets §8.6.6 qualified-name resolution do a single-table longest-prefix-match against the queried `module_path` rather than segmenting and walking per-module alias sub-tables. The owning module of any alias entry is **derived from the key** (strip the last dot-separated segment, e.g., key `m.n.str` → owner `m.n`); it is not stored on `ModuleAliasEntry`. Three keying domains — `ModuleFullPath` (module / alias path), `Symbol` (in-module binding), `TypeName` (receiver-pinned ADT lookup) — three newtypes, no conflation.

**Per-namespace insertion-time conflict enforcement** (spec §8.6.4). Three conflict cases — two within-table, one cross-table:

- **Rename collision** (within `SymbolTable.symbols`) — two import/export entries producing the same local `Symbol` collide on insertion; structurally detected by a second `symbols.insert(sym, …)` for an already-occupied key.
- **Mount collision** (within session-level `ModuleAliases`) — two mounts at the same alias **inside the same owner module** collide; different owner modules mounting the same local alias name land at different `ModuleFullPath` keys and do not collide.
- **Mount-vs-submodule cross-namespace collision** (cross-table — `ModuleAliases` vs `SymbolTables`) — an alias path in `ModuleAliases` clashes with a real loaded module path in `SymbolTables`. NOT structural via the type system; the parse-time installer MUST perform an atomic cross-table check at insert time.

**Multi-legged authoring.** Some declarations author multiple `Def` entries from a single source form. The parent metadata `Def` carries the authored form (`sexp`, `source`); synthesized sub-entries derive from it. Pattern:

| Source form | Parent metadata `Def` | Synthesized sub-entries |
|---|---|---|
| `(defn name ([sig-1] body-1) ([sig-2] body-2))` (multi-sig) | `Def { kind: Overloaded { variants, sexp, source } }` | One `Def { kind: UserFn, ast, code }` per variant, mangled name (e.g., `add$Int+Int`) |
| `(defmacro name [pat-0] body-0 [pat-1] body-1)` | `Def { kind: Macro { clauses_meta, sexp, source } }` | One `Def { kind: UserFn, ast, code }` per clause body, mangled name `{name}$clause-{N}` |
| `(deftype (Name a) Ctor-0 Ctor-1)` | `Def { kind: TypeDef { … } }` | One `Def { kind: Constructor, ast, code }` per constructor (D49) |
| `(deftrait Name methods…)` | `Def { kind: Trait { … } }` | Methods stored per D45 (TraitImpl placement) |

The `sexp` + `source` fields live on the parent metadata `DefKind` variant, not on synthesized sub-entries. REPL `/source name` resolves through the parent metadata if a sub-entry is named (e.g., `/source thread-first$clause-0` resolves to the parent `thread-first`'s form). `ast` and `code` are sub-entry concerns — each clause body, constructor body, or multi-sig variant body has its own.

**Macros are Defs.** Macro clause bodies are stored as `Def { kind: UserFn { … } }` entries with mangled names `{macro-name}$clause-{N}`, dispatched via the normal GOT mechanism — uniform with multi-sig fn variants. Macro parent entries are `Def { kind: Macro { clauses_meta, sexp, source } }` carrying **metadata only**. Expansion-time dispatch walks `clauses_meta` to pattern-match the call sexp, then GOT-dispatches to the matched clause's mangled-variant Def. No sidecar `MacroEnv` table exists — clause-body lookup is the same GOT-dispatch path as any other callable.

**Trait-method addressing convention.** Trait methods are addressed by composite `Symbol` within the trait's defining module. For a trait method `Display.show` declared in module `core`: the canonical `ModuleEntry::Def` for the method lives in `core` keyed by `Symbol::from("Display.show")`. Per-method `ModuleEntry::Import` bindings injected by the prelude into user modules carry `source: FQSymbol { module: ModuleFullPath::from("core"), symbol: Symbol::from("Display.show") }`. Bare-name use sites (`(show 42)`) install the local Import binding under the bare `Symbol::from("show")`. The trait is **not** a distinct module namespace — `FQSymbol` remains two-component; any `FQSymbol` whose `symbol` field contains a `.` is a trait-method reference.

**TraitImpl storage.** Per Decision 0045, `(impl Trait Type method-defns…)` lands in the **trait's defining module** keyed by the synthetic name `impl$FQTypeName$FQTraitName`. Importers discover impls by chain-following the trait reference back to its defining module and probing for that synthetic key. No closure walk; no cycle detection; per-symbol point-to-point navigation only (Principle 17).

**FQTypeName binding** (Decision 0047). FQTypeName is binding as the cross-crate boundary type for resolved-stage type identifiers; two narrow exceptions — syntactic-lift sites (`check_form` resolving `TypeRef` → `FQTypeName`) and receiver-pinned helpers (e.g., `SymbolTable::get_type(name: &TypeName)` where `&self` IS the module context). Syntactic-stage qualification is captured structurally by `TraitRef` and `TypeRef` (both carrying `Option<ModuleFullPath>`) rather than letting a "bare name slip through" the AST.

**Field-level access on state types is discouraged outside the types crate.** State types (`ModuleEntry`, `DefKind`, `SymbolTable`) expose method-level accessors as their public contract — e.g., `ModuleEntry::arity()` (delegating to `Type::fn_arity()` on `scheme.ty`), `SymbolTable::get` / `get_type` / `defined_symbols` / `public_symbols`. Direct field access remains permitted on **data-record DTOs** (`NamedImport`, `ImportSpec`, `ExportSpec`, `ModDecl`, `PlatformSpec`, `Span`, `FQSymbol`, `FQTypeName`, `FQTraitName`, `TypeDefInfo`, `TraitDeclInfo`, `MethodResolutions`) where the field set IS the contract and serde round-trips structurally.

**`Def` entry construction — the builder (Tier 1, production).** `ModuleEntry::Def` carries ~11 fields, six of which are construction-time defaults at every static-table / mount call site (`callees`, `got_slot`, `trait_origin`, `seq`, `ast`, `code`). Enum variants cannot use `..Default::default()`, so hand-rolled `ModuleEntry::Def { … }` struct literals spell out all 11 fields even where only three matter. `ModuleEntry::def(scheme, kind) -> DefBuilder<C>` is the single production constructor for `Def` entries: chainable setters for the construction-time concerns (`visibility` — defaulting to `Public`, `docstring`, `param_names`, `got_slot`, `trait_origin`, `seq`, `ast`), terminated by `.build()` (or the `From<DefBuilder<C>>` conversion). `callees` and `code` are deliberately *not* settable — they are runtime-state fields written downstream (callees by typecheck's `finalize_check_result`, code by backend after `compile_to_module`); the builder is construction-time-only, keeping the runtime-state single-source-of-truth invariants intact (Principle 7). The builder is the multi-consumer Tier-1 piece shared by `cranelisp-primitives` static-table assembly, `int`'s synthetic-module mount (FIXME 0242), and the Tier-2 test helpers. It realizes the `declare_def` helper deferred by FIXME 0241; the broader `declare_adt` / `declare_special_form` / `declare_trait` vocabulary remains deferred (minimum mechanism — only the `Def` constructor has two real production consumers today).

**Test-support symbol-table construction (Tier 2, feature-gated, NOT in the production baseline).** `cranelisp_types::test_support` (compiled only under `#[cfg(any(test, feature = "test-support"))]`) hosts `SymbolTableBuilder<C, L>` — a **generic, content-agnostic** convenience for building a single populated `SymbolTable<C, L>` from declared entries, for use by OTHER crates' test suites (typecheck's unit suite). It shares only the Tier-1 `ModuleEntry::def` constructor with production; it carries no specific module's content (no Option/IO/primitive schemes — that domain content is typecheck-owned Tier 3). The boundary is deliberate: the builder covers per-`SymbolTable` construction only; the multi-module `SymbolTables` DashMap, the session-level type-id allocator, and bootstrap ordering between synthetic modules are typecheck's Tier-3 concern (content- and bootstrap-aware). Pure `#[cfg(test)]` would be crate-local and invisible to downstream test builds, hence the `test-support` Cargo feature is the visibility mechanism. The `public-api.txt` baseline is generated WITHOUT `--features test-support`, so `test_support` never enters the production contract — that delineation is what makes the test-only boundary enforceable. See FIXME 0239 (the broader "instantiate a symbol table from a source" generalization, deferred) and FIXME 0241.

**Trait contracts (marker traits for cross-crate windows).** The crate hosts empty marker traits that downstream crates implement to supply concrete types where the boundary is generic. Concrete window types live in the owning crate, not here, so this crate stays ignorant of backend and runtime concrete state.

**Out of scope.**
- Anything that would invert the dependency graph (Cranelift types, JIT/linker types, the integration-layer code carrier)
- Pipeline orchestration (int)
- Runtime intrinsics (intrinsics — §4b)
- Per-form transient typecheck-internal state

**What crosses the boundary.**
- Every type in this crate is a boundary type by definition. The crate IS its surface. The full enumeration is at `crates/cranelisp-types/public-api.txt` (auto-generated by `cargo public-api`); per-item rustdoc lives on the items themselves and can be browsed via `cargo doc -p cranelisp-types --no-deps`.

**Per-surface documentation.** Unlike the other crate-shaped surfaces, `cranelisp-types` has no separate `facades/types.md` document — the source-side rustdoc (crate-root `//!` narrative in `crates/cranelisp-types/src/lib.rs` plus per-item `///` comments) IS the facade. Decision retired the facade as a permanent record in S69 Submission 42 per Principle 7 (single source of truth) and lived-experience cost of dual-maintenance. The `public-api.txt` baseline gates the surface at PR time per the baseline-diff discipline (see `design/arch/CLAUDE.md` §"Baseline-diff discipline"); rustdoc-coverage is the source-side equivalent of the per-crate facade-compliance test for the other crates.

---

## Cross-references

- `principles.md` — architectural principles
- `facades/{crate}.md` — per-surface facade specs (as-designed public surface)
- `interfaces.md` — narrative companion to `crates/cranelisp-types/`
- `spec/` — language definition
