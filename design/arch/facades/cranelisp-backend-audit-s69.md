# cranelisp-backend — Sprint 69 facade audit (per-item analysis, re-authored 2026-05-19)

**Audit triple**: `crates/cranelisp-backend/src/lib.rs` (declared surface, 4941 LOC) + `crates/cranelisp-backend/src/{code,primitives_inline,got_observer,error,artefact,jit,cache}.rs` and submodules × `design/arch/facades/backend.md` (460 LOC, parent) + `design/arch/facades/backend-cache.md` (376 LOC, sub-facade) × `crates/cranelisp-backend/public-api.txt` (2008 LOC, live boundary).

**Date**: 2026-05-19 (S69 Phase 3 Wave 1 — re-authored a second time).
**Auditor**: /design (cranelisp-backend narrow deployment).
**Inputs frozen at**: current commit on `main` (post-S68 close `9516dfc`).

**Discipline**: per `memory/feedback_audit_per_item_analysis.md` (2026-05-18 user direction). Each finding gets **five** blocks — facade expects / source does / **design intent (grounding citation)** / difference implies / disposition. The grounding block names the Decision(s), Principle(s), and/or FIXME(s) that authorise the facade's prescription. **Without the grounding block, "facade-moves vs source-moves" defaults to whichever side is settled — that is the prior-audit failure mode this version corrects.**

**What changed since the prior version of this audit (2026-05-19 morning).** The prior version dispositioned 22 findings without reading Decisions 31, 35, 41, 43, 48, Principles 7, 17, 18, or `design/backend/{compile-to-module,per-module-got}.md`. Because the binding intent was not loaded, two arbitration briefs (A-1 = `Code::Jit { ptr }` retention; A-2 = `compile_to_module` generic parameters) were filed for /arch resolution when the architectural configuration already grounds both: Decision 31 S66 amendment + Decision 35 §"Canonical post-rollback shape" + Decision 48 §"Relationship — Decision 35" all assert "GOT is the single source of truth for callable addresses; no per-entry pointer field" as the **landed** post-rollback canonical statement (not a target); Decision 41 §"Three coordinated changes" line 3 spells `compile_to_module<M: Module>(... SymbolTable<Code, ()>, ...)` monomorphic on `Code` as the binding signature. **F-1 and the former A-1 flip from arbitration to source-moves. F-2 and the former A-2 flip from "may need arbitration" to source-moves (Decision 41 PIF Row 2, on backlog).** Eight further per-finding grounding blocks are tightened. The findings overview table now carries a "Grounding" column citing the specific Decision/Principle/FIXME that grounds each disposition; no row's disposition stands without a citation.

---

## 0. Summary up front

Backend is the workspace's largest single facade — a 460-line parent (`backend.md`) plus a 376-line sub-facade (`backend-cache.md`) describing a 2008-line public-api surface across `~/code`, `~/error`, `~/artefact`, `~/jit`, `~/cache::{linker,manifest,object,serialize}`, `~/got_observer`, `~/heap`, `~/compiler`, `~/exe`, and `~/primitives_inline`. The S67 close substantially reduced the gap between as-built and as-designed; the residual drift is grounded in the Decision 41 close-out work (Row 2/3/4 PIF carries already on backlog) plus the Decision 35 post-rollback variant-slim that the rollback commit `1dc57ae` did not extend into the variant-internal `ptr` field.

**Substantive corrections vs the prior version.**

1. **F-1 (Code::Jit ptr retention) — flips from arbitration to source-moves.** Decision 31 §"Amendment (Sprint 66 — fn_ptr unification + rollback)" + Decision 35 §"Canonical post-rollback shape" + Decision 48 §"Relationship to other Decisions / Decision 35" all assert as **landed canonical** the statement "GOT is the single source of truth for callable addresses; `ModuleEntry::Def.got_slot: Option<usize>` indexes into `SymbolTable.got()`; there is no separate `fn_ptr` / `platform_fn_ptr` / `primitive_fn_ptr` field." The variant-slim `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` shape is the target. Source's two-field `Code::Jit { jit, ptr }` carrying `*const u8` alongside `Arc<Jit>` AND the `Code::ptr()` accessor are un-migrated. Disposition: **source moves**, not arbitration. The migration is one bundled work item with F-2's Decision 41 close, because the per-symbol direct-write rewrite in `compile_to_module` is the site that constructs the variants.

2. **F-2 (compile_to_module signature) — flips from "may need arbitration (A-2)" to unambiguous source-moves.** Decision 41 §"3. Backend writes directly..." spells the binding signature verbatim:
   ```rust
   pub fn compile_to_module<M: Module>(
       scope: &ModuleFullPath,
       names: &[Symbol],
       symbol_tables: &DashMap<ModuleFullPath, SymbolTable<Code, ()>>,
       introspection: Option<&DashMap<FQSymbol, Introspection>>,
       module: M,
   ) -> Result<(), CompilationError>;
   ```
   The generic `<C, L>` parameters that today's source carries are pre-Decision-41 batch-return shape, not "as-designed parametric retention." Decision 32's `CodeStore`/`LinkerStore` empty-marker trait remains operative for typecheck and frontend (which stay on `<(), ()>`); but the backend codegen entry monomorphises on `Code` per Decision 41. The audit's prior "(b) Facade moves — accept the live generic shape" disposition was a re-derivation from source rather than from configuration — the wrong direction per Principle 13.

3. **F-7 (primitives_inline.rs retirement reframe) — grounding strengthened; disposition unchanged.** Decision 43 §"Status pointer — Sprint 67 FULL CLOSE" + facade §"Operator special-casing is forbidden" point 3 jointly authorise the name-keyed inline-substitution pattern. The prior reframe (the file's `is_known_builtin` + `try_emit_inline_primitive` remain as a name-keyed shortcut over the standard GOT-indirect path) is correct. The grounding block now cites Decision 43's status pointer verbatim ("the surviving substitution table inside `primitives_inline.rs` is name-keyed only ... Symbol-only, never `(TraitName, Symbol, TypeName)` triples"); the reframe stands.

4. **F-19 (Decision 48 dep-ban) — grounding strengthened; disposition unchanged.** Principle 18 §"Worked example — primitives dispatch" makes Decision 48 §"Structural invariant — backend dep-ban" the canonical worked example of structural enforcement. The /qa test refinement note remains.

Disposition class counts (over **22 findings**: F-1 through F-22), revised:

| Class | Count | Meaning |
|---|---:|---|
| Source-moves | 9 | Facade is target-stating per cited Decision/Principle; source has drifted / never landed. Includes the seven backlog-tracked PIF carries + F-1 (now grounded by Decisions 31+35+48) + F-2 (grounded by Decision 41). |
| Both-move | 2 | F-3 (param name + Linker doubling); F-7 (facade D43 close mark-as-landed + reframe Sprint 69 row 7). |
| Facade-moves | 4 | F-5 (stale "pending Wave 3" comment on a landed lift); F-13 (root-level re-exports not in §"Public surface"); F-14 (method signatures not enumerated); F-15 (impl placement not noted). |
| No action (informational / structural-already-enforced) | 7 | Auto-trait projection noise (F-18) + tombstone confirmations (F-6, F-10, F-22) + private helpers (F-17) + landed extension points (F-11) + consumer-site-enforced auto-traits on a transitional type (F-16, bundled with F-12). |
| Requires /arch arbitration | 0 | **Zero.** Both prior arbitration briefs (A-1, A-2) are dispositioned by the configuration. The §"Arbitration briefs" section below is retained as a record of what was *previously* in arbitration and why it is now grounded. |

The audit cannot resolve no items alone — the configuration suffices. The findings overview table at the bottom carries the per-row Grounding column.

---

## Findings

### Finding F-1 — `Code::Jit { ptr }` variant-internal `ptr` field

**Facade expects.** `facades/backend.md` §"`Code` — the per-symbol lifecycle owner (moved here from `src/` per Decision 41; slimmed per S66 — variant slim preserved through the same-day fn_ptr-unification rollback)" prescribes:

```rust
pub enum Code {
    Jit(Arc<Jit>),                                             // fresh-build code; Arc<Jit> is the Decision-31 reclaim primitive
    Linker(Arc<Linker>),                                       // cache-hit code mapped from .o via load_object
    Primitive,                                                 // process-static lifecycle marker (Decision 0048 A2, revised S68 Phase 3); no payload; GOT slot holds the *const u8 per Decision 35
}
```

§"`Code`" body line 78: "To extract the fn ptr from a callable entry, **read the GOT slot**: `symbol_table.got().load_slot(entry.got_slot.unwrap())`. Do NOT match on `Code` variants for ptr access. The variant-uniform `Code::ptr()` accessor that previously lived here is removed — there is no ptr inside `Code` to accessor over."

**Source does.** `crates/cranelisp-backend/src/code.rs:72-99` declares:

```rust
#[non_exhaustive]
#[derive(Clone)]
pub enum Code {
    Jit  { jit: Arc<Jit>,    ptr: *const u8 },
    Linker { linker: Arc<Linker>, ptr: *const u8 },
    Primitive,
}
```

Pub-api lines 781-785 confirm the two-field variants. `Code::jit(jit, ptr)`, `Code::linker(linker, ptr)` constructors and the `Code::ptr()` accessor (`code.rs:148-153`, pub-api 788-790) are all live.

**Design intent — grounded.** **Three Decisions and one Principle** explicitly target-state the slim shape as **landed canonical**, not as a future commitment:

- **Decision 31 §"Amendment (Sprint 66 — fn_ptr unification + rollback, 2026-05-09)"** — quote: "Post-rollback the call address lives at `symbol_table.got().load_slot(slot)`, indexed by `ModuleEntry::Def.got_slot`. `Code::Jit(Arc<Jit>)` continues to be the reclaim primitive."
- **Decision 35 §"Amendment (Sprint 66 — rollback, 2026-05-09)"** — quote: "The unified `fn_ptr` field is retracted. ... The variant slim from the previous amendment is preserved — `Code` stays tuple-shaped (`Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)`), carrying lifecycle ownership only. The difference vs. the previous amendment is purely *where* the call address lives: GOT slot, not sibling field." The previous amendment's tuple shape is preserved through the rollback — the rollback's scope was the sibling field's removal, but the variant shape it slimmed to had **already** retired the per-variant `ptr` payload.
- **Decision 48 §"Relationship to other Decisions / Decision 35"** — quote: "Aligned (invariant preserved). Primitives store fn ptrs in `GotTable` slots indexed by `ModuleEntry::Def.got_slot`, exactly as Decision 35's post-rollback canonical statement prescribes. No sibling `fn_ptr` field is introduced." The Decision 48 §"Shape" S68 Phase 3 amendment treats Decision 35's "GOT is the single source of truth for callable addresses; no per-entry pointer field" invariant as the **working** invariant, building Decision 48 (Code::Primitive marker) on top of it. If the variant-internal `ptr` field were still authoritative, Decision 48's framing of `Code::Primitive` as "no payload — Decision 35's 'no per-entry pointer field' invariant is preserved" would be incoherent — but it is coherent, which means Decision 48 treats the variant-slim as already-landed.
- **Principle 7 (Single source of truth)** — explicit in the Principle's "Consequence" paragraph: "Parallel stores (... `SharedState.kept_jits`/`kept_linkers`, ...) are architectural defects whether or not they happen to be 'fast paths' — they re-introduce divergence by construction." A `*const u8` in `Code::Jit` alongside the same `*const u8` in `symbol_table.got().load_slot(slot)` is exactly the parallel-store shape Principle 7 forbids.

The rollback commit `1dc57ae` removed a **sibling** `ModuleEntry::Def.fn_ptr` field that was introduced in `b09ec76` AND was supposed to also retire the variant-internal `ptr` (which is the same conceptual placement viewed from inside vs alongside the variant). The rollback's `git revert` actually undid only the sibling field. **The variant-slim was a separate edit that landed in `b09ec76` and was NOT reverted by `1dc57ae`** — and yet the current source retains the variant-internal `ptr` because the S66 work did not get to the second commit. The facade text + Decision 31/35/48 narrate the target — slim variants — and treat it as canonical. The audit's prior framing ("rollback's intent was sibling-only; facade is target-stating beyond what shipped") was a wrong reading of the rollback's scope.

**What the difference implies.** Three downstream consequences:

- Every `Code::jit(arc_jit, ptr)` call site (in `compile_to_module`'s finalize phase post-Decision-41 — today the equivalent code lives in `int`'s post-loop reconstruction at `worker.rs:2860-3018`; in tests in `code.rs`) carries a `ptr` alongside the `Arc<Jit>` that duplicates `got().load_slot(slot)`.
- `Code::ptr()` callers (tests in `code.rs:174, 211`; one prospective caller — none on the production path today, because the production read path already routes through GOT per Decision 35 §"Canonical post-rollback shape" §"Backend's `compile_to_module` writes the address via `got().store_slot(slot, ptr)`") would migrate to `st.got().load_slot(entry.got_slot.unwrap())`.
- The Decision 35 single-source-of-truth invariant is currently structurally-uphold-able only by call-order discipline (backend writes to both `Code.{Jit,Linker}.ptr` AND `got().store_slot()` and trusts they stay in sync). The migration converts the invariant to structurally-enforced.

**Disposition.** **Source moves.** Bundled with F-2 (Decision 41 close) as a single migration in the Sprint 69 Row 2 wave: when `compile_to_module` rewrites for per-symbol direct-writes per Decision 41, it constructs `Code::Jit(Arc<Jit>)` (not `Code::Jit { jit, ptr }`) and writes the ptr via `got().store_slot(slot, ptr)`. The `Code::jit(jit, ptr)` and `Code::linker(linker, ptr)` constructors retire; replacements are `Code::jit(jit)` and `Code::linker(linker)`. The `Code::ptr()` accessor retires. Tests at `code.rs:174, 211` rewrite to read the GOT instead of the variant. Pub-api shrinks by 4 lines (`Jit::ptr`, `Linker::ptr`, `Code::ptr()`, and one of the constructor signatures).

**Closes** the prior version's arbitration brief A-1. No /arch arbitration required — Decisions 31, 35, 48 jointly disposition it.

---

### Finding F-2 — `compile_to_module` return shape and generic parameters

**Facade expects.** `facades/backend.md` §"Free functions" lines 16-22 (verbatim):

```rust
pub fn compile_to_module<M: Module>(
    scope: &ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<Code, ()>>,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module: M,
) -> Result<(), CompilationError>;
```

§"Return shapes" line 46: "`compile_to_module` returns `Result<(), CompilationError>` — no artefact struct. Backend writes Code and Introspection directly into the passed-in stores per Decision 41."

**Source does.** `crates/cranelisp-backend/src/lib.rs:437-456`:

```rust
pub fn compile_to_module<M, C, L>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module: &mut M,
) -> Result<CompilationResult, CompilationError>
where
    M: Module + CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
```

Five drifts in one signature: borrowed-vs-owned `scope`/`module_path`; by-value-vs-by-mut-ref `module`; missing `introspection` parameter; `Result<CompilationResult, _>` vs `Result<(), _>`; `<M, C, L>` generic vs `<M: Module>` monomorphic on `SymbolTable<Code, ()>`.

`CompilationResult` (lib.rs:128-170) carries `func_ids`, `code_ptrs: HashMap<Symbol, *const u8>`, `artifacts: HashMap<Symbol, FunctionArtifacts>`, `entry_func_id`, `func_arities`, `warnings`. The doc comment confirms its transitional role per Decision 35 Layer 2 Option B.

**Design intent — grounded.** **Decision 41 is the binding citation**, verbatim from §"3. Backend writes directly to symbol tables and introspection; returns `Result<(), CompilationError>`":

> Final signature:
>
> ```rust
> pub fn compile_to_module<M: Module>(
>     scope: &ModuleFullPath,
>     names: &[Symbol],
>     symbol_tables: &DashMap<ModuleFullPath, SymbolTable<Code, ()>>,
>     introspection: Option<&DashMap<FQSymbol, Introspection>>,
>     module: M,
> ) -> Result<(), CompilationError>;
>
> Backend writes each compiled symbol's `Code::Jit { jit, ptr }` into its entry via `symbol_tables.get(scope).unwrap().write_code(sym, Code::Jit { jit, ptr })` (Decision 38's `write_code(&self, …)` — interior mutable, no `&mut` flow needed). Backend also stores the GOT slot pointer via the entry's already-existing GOT path.

Decision 41 §"S66 amendment + rollback" updates the `Code::Jit { jit, ptr }` text to `Code::Jit(Arc<Jit>)` per the variant slim — but the signature lines (the five above) are unchanged. Decision 41 §"Status pointer — Sprint 67 close" notes "Decision 41 closes substantively at S67 close" with the Wave 3 dispatch — i.e., the rewrite is on the close-out track, with the binding signature already named.

**Decision 32 unchanged for typecheck/frontend.** Decision 41 §"Cross-references and amendments" line 4: "Decision 32 unchanged. The empty-marker `CodeStore` trait still serves: `()` for non-codegen crates, `Code` for backend + int." The generic shape is preserved at the SymbolTable type definition site (`cranelisp-types`); backend's codegen entry-point monomorphises on `Code` because backend is the consumer for which the empty-marker `CodeStore` trait was authored.

**The audit's prior framing** (arbitration brief A-2: "whether the generic shape is the intended preservation of Decision 32 parametric SymbolTable") **was a re-derivation from source.** Decision 41 names the binding monomorphic signature directly; the source's `<C: CodeStore, L: LinkerStore>` parameters are pre-Decision-41 batch-return shape that the close-out work eliminates.

**Principle 2 (narrow interfaces).** Decision 41 §"Rationale" line 2: "Principle 2 (narrow interfaces) — five parameters, no return tuple to unpack." The source's 4-parameter `<M, C, L>` shape with the `CompilationResult` return-tuple is wider than the facade's 5-parameter direct-write shape (the introspection map is an explicit parameter rather than a marshalled artefact map).

**What the difference implies.** The caller (`int`'s priority worker) must today post-process `CompilationResult` into `Code::Jit { jit, ptr }` per symbol and write the GOT slots — exactly the per-symbol direct-write Decision 41 wants to eliminate. The introspection bookkeeping (CLIF IR, disasm, code size) flows through `CompilationResult.artifacts` rather than directly into an `int`-owned `DashMap<FQSymbol, Introspection>`. Two structural costs: (a) duplicated state-threading discipline at the boundary; (b) `CompilationResult` and `FunctionArtifacts` are transitional public surfaces that should not exist.

The migration is bounded:
1. Rewrite `compile_to_module_impl` to write `Code::Jit(Arc<Jit>)` (post-F-1) into `symbol_tables[scope].symbols[name].code` per symbol immediately after finalize, AND write GOT via `got().store_slot(slot, ptr)`.
2. Add the `introspection: Option<&DashMap<FQSymbol, Introspection>>` parameter; on `is_some()`, write per-symbol `Introspection { clif_ir, disasm, code_size, compile_duration }`.
3. Delete `CompilationResult` and `FunctionArtifacts` types entirely (they retire from the public surface — closes F-12).
4. Migrate `int`'s priority-worker caller in `src/worker.rs:2860-3018` (per Decision 41 §"Consequences" line 4) to call `compile_to_module` per-symbol and skip the post-loop reconstruction.
5. Drop the `<C, L>` generics from the function signature; monomorphise on `<Code, ()>` at the backend entry.

**Disposition.** **Source moves.** Decision 41 PIF Row 2 work, already on the Sprint 69 backlog. Bundled with F-1 (variant slim is constructed at the same call sites), F-8 (introspection parameter is the same five-parameter target shape), F-12 (`CompilationResult` + `FunctionArtifacts` retire), and F-16 (`unsafe impl Send/Sync` retires with the type).

**Closes** the prior version's arbitration brief A-2. No /arch arbitration required — Decision 41 dispositions it directly.

---

### Finding F-3 — `load_object` free-function shape

**Facade expects.** §"Free functions" lines 24-28:

```rust
pub fn load_object(
    module: &ModuleFullPath,
    object: &[u8],
    symbol_tables: &SymbolTables,
) -> Result<LinkerArtefact, CranelispError>;
```

**Source does.** `crates/cranelisp-backend/src/lib.rs:772-805`:

```rust
pub fn load_object<C, L>(
    module: &ModuleFullPath,
    object_bytes: &[u8],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Result<artefact::LinkerArtefact, CranelispError>
where C: cranelisp_types::CodeStore, L: cranelisp_types::LinkerStore,
```

Three drifts: parameter name `object`/`object_bytes`; generic `<C, L>` vs facade's `SymbolTables` newtype; `Linker::load_object` method exists alongside the free function.

The free-fn body (lines 781-804) is a scaffold; production callers use `cache::linker::Linker::load_object` directly.

**Design intent — grounded.** Facade §"PIF prep" Row 3 (line 305): "Target: a free function `cranelisp_backend::load_object(module, object, symbol_tables) -> Result<LinkerArtefact, CranelispError>` that owns Linker construction and returns the artefact. The `Linker::load_object` method becomes `pub(crate)`."

The §"PIF prep" rows in the parent facade are the close-out commitments for the Decision 41 wave (S67 close); the parent facade's §"Status pointer" + Decision 41's status pointer treat them as on-track work, not arbitration items. The `SymbolTables` newtype is shorthand for the same `DashMap<ModuleFullPath, SymbolTable<Code, ()>>` shape spelled in F-2's grounded Decision 41 signature; the abstraction is at the facade boundary so the audit treats the underlying concrete shape as the binding one.

The `<C, L>` parameters on the free fn are the same pre-Decision-41 generic carry F-2 identified. **Principle 2 (narrow interfaces) + Decision 41 §"Rationale"** ground the monomorphisation.

**What the difference implies.** Doubled-`pub` surface (the method AND the free fn) is the documented PIF Row 3 work; on-backlog narrowing of the method to `pub(crate)`. The parameter-name drift (`object` vs `object_bytes`) is trivial.

**Disposition.** **Both move.**
- **Facade moves** — rename parameter `object` → `object_bytes` to match source (one-line edit; either name is fine, but the source name is more descriptive).
- **Source moves** — Row 3 PIF carry: migrate production callers from `Linker::load_object` method to the free function; narrow the method to `pub(crate)`; drop the `<C, L>` generics from the free fn (monomorphise on `<Code, ()>` per F-2 grounding).

Closes F-3; on-backlog at Sprint 69 Row 3.

---

### Finding F-4 — `compile_to_object` shape + body

**Facade expects.** §"Free functions" lines 30-34:

```rust
pub fn compile_to_object(
    module: &ModuleFullPath,
    symbol_tables: &SymbolTables,
) -> Result<ObjectArtefact, CranelispError>;
```

**Source does.** `crates/cranelisp-backend/src/lib.rs:821-842`. Body returns `Err` unconditionally with a message naming FIXME 0184. `_symbol_tables` underscore-prefix marks the parameter as unused.

**Design intent — grounded.** **Decision 41 §"3. Backend writes directly..."** — `compile_to_module` is the JIT-mode codegen entry; `compile_to_object` is the dual for the nice-worker object-codegen path (per facade §"Free functions" line 30-34 and §"`load_object`/`compile_to_object`" paragraphs). The two entries together are the binding boundary. **FIXME 0184** is the implementation tracker for the nice-worker orchestration migration into backend.

**Principle 11 (single pipeline, mode parameters)** — Decision 23's "mode is a Module property" + Decision 41's per-symbol cardinality for JIT vs per-module cardinality for object — `compile_to_module` and `compile_to_object` are the two cardinality-flavoured entries of the same conceptual codegen surface.

**What the difference implies.** A reader of the facade alone would believe `compile_to_object` is the canonical nice-worker entry; a reader of source would see a placeholder. The placeholder is acceptable as a Wave 0 scaffold (the artefact types exist; the entry compiles; the boundary is reserved); production migration is Wave 3 work (Row 4).

**Disposition.** **Source moves.** Row 4 PIF carry on backlog:
1. Migrate the nice-worker orchestration body from `int`'s `cache_writer.rs` into `compile_to_object`'s body: instantiate `ObjectModule` with appropriate `TargetIsa`; drive `compile_to_module` against it; emit `.o` bytes via `ObjectModule::finish().emit()`; build the sidecar `SymbolTable<(), ()>` from the typecheck product; return `ObjectArtefact { object, sidecar }`.
2. Remove the FIXME 0184 reference from the placeholder; the migration closes that FIXME.
3. Re-point `int`'s caller to the free function; delete the migrated orchestration code from `int`.

Closes F-4; on-backlog at Sprint 69 Row 4.

---

### Finding F-5 — `Linker::get_symbol` return type — sub-facade lag on landed lift

**Facade expects.** `facades/backend-cache.md` §"`cache::linker`" line 36:

```rust
pub fn get_symbol(&self, name: &str) -> Result<*const u8, LinkerError>;       // Decision 36 bare-name lookup — RETURN TYPE CHANGE pending Wave 3 (currently Option<*const u8>)
```

**Source does.** Pub-api line 82 — the return type is **already** `Result<*const u8, LinkerError>`. The lift has landed.

**Design intent — grounded.** Decision 37 + the parent facade §"Errors" — `LinkerError` is the typed cache-side error variant family. The sub-facade prescribes the lift; the close-out happened at S67 W4 (per Decision 41 §"Status pointer — Sprint 67 close" Wave 3 row enumeration: "`Linker::get_symbol` returns `Result<*const u8, LinkerError>` (post-S58 silent-NULL regression closure)"). The sub-facade lags on the celebration.

**Principle 13 (`interfaces.md` is auditable)** — `cargo-public-api` baselines are the audit-of-record; the sub-facade should match the baseline state.

**What the difference implies.** Documentation lag on a landed feature. Readers consulting only the sub-facade would believe the lift is still future work; readers consulting only source would believe (correctly) that consumers can already match on `LinkerError` variants.

**Disposition.** **Facade moves.** Two-spot edit on `facades/backend-cache.md`:
1. §"`cache::linker`" line 36 — remove the "RETURN TYPE CHANGE pending Wave 3 (currently Option<*const u8>)" comment; the signature is the landed shape.
2. §"Disposition decisions" table row — change "PFR — return-type lift Wave 3" to "PFR — return-type lift **landed S67 W4**".
3. §"Wave 4 checklist" row — remove or tombstone under a "landed in S67" subsection.

Closes F-5.

---

### Finding F-6 — `primitives_inline::primitive_for_trait_method` tombstone

**Facade expects.** `facades/backend.md` §"`primitives_inline`" line 287: "`primitives_inline::primitive_for_trait_method(TraitName, Symbol, TypeName) -> Option<&'static str>` — **DELETED (S67 W4 close).**"

**Source does.** Verified absent. `grep -n "primitive_for_trait_method" crates/cranelisp-backend/src/primitives_inline.rs` returns no hits; pub-api carries no entry.

**Design intent — grounded.** **Decision 43 §"Status pointer — Sprint 67 FULL CLOSE"** — quote: "`primitive_for_trait_method(TraitName, Symbol, TypeName) -> Option<&'static str>` — DELETED from `crates/cranelisp-backend/src/primitives_inline.rs` per Wave 3 row 6." Plus the facade §"Operator special-casing is forbidden" forbidding `(TraitName, Symbol, TypeName)` triple keys. The deletion is the binding intent; source matches.

**What the difference implies.** None.

**Disposition.** **No action.** Tombstone correctly reflects deleted-fn state.

---

### Finding F-7 — `primitives_inline.rs` retirement reframe

**Facade expects.** Two facade passages are load-bearing here, in tension with each other:

(a) `facades/backend.md` §"`primitives_inline.rs` retirement narrative" (lines 289-294):

> `primitives_inline.rs` itself is the post-rename successor to the deleted `operators.rs` (S66 rename confirmed). Per D43 full close, the file retires fully once every Ring 0 primitive is reachable through the standard GOT-indirect call path ... The inline substitution that lives in `primitives_inline.rs` today is the code-size + dispatch-cost optimisation; it remains a legitimate substitution but must be reframed as a name-keyed shortcut over the standard path (not a parallel dispatch).

(b) §"Non-goals / forbidden patterns" → "Operator special-casing is forbidden" point 3 (lines 338-339):

> Inline-substitution at the codegen site (the legitimate optimisation) is keyed on Symbol ONLY (never on `(TraitName, Symbol, TypeName)` triples — backend has no trait knowledge), and is a substitution applied to the same call shape, not a parallel dispatch path. ... The substitution is OPTIONAL — the named primitive fn ptr in the synthetic `primitives` module's GOT is always a legitimate target for indirect calls.

**Source does.** `crates/cranelisp-backend/src/primitives_inline.rs` (366 lines) contains:
1. `pub fn is_known_builtin(name: &str) -> bool` (line 117) — `matches!` predicate over 23 Ring 0 entries.
2. `pub fn try_emit_inline_primitive<M: Module>(builder, name, args, span, module, panic_func_id) -> Option<Result<Value, CranelispError>>` (line 54). Contract: `Some(Ok)` matched + emitted; `Some(Err)` matched + emit failed; **`None` not in table — caller MUST fall through to GOT-indirect.**
3. Seven private emit helpers.

Two active call sites in backend codegen (`compiler/apply.rs:222,240`; `compiler/control_flow.rs:1365-1366`) follow the gate-then-fall-through pattern.

**Design intent — grounded.** **Decision 43 §"Statement"** — quote: "Backend MAY substitute CLIF inline at direct call sites via a name-keyed substitution table." Plus §"Status pointer — Sprint 67 FULL CLOSE": "the surviving substitution table inside `primitives_inline.rs` is name-keyed only (`add-i64 → iadd`, etc. — Symbol-only, never `(TraitName, Symbol, TypeName)` triples)." Plus **Principle 17 (uniform dispatch — every callable goes through the GOT)** as cited in Decision 43's status pointer.

**Decision 48 §"Shape"** — primitives now have `code = Some(Code::Primitive)` with GOT slots populated from the static `PRIMITIVES_TABLE`. Every primitive IS reachable via the standard GOT-indirect path per Decision 23's two-GOT model. The "fall through to GOT-indirect" contract on `try_emit_inline_primitive`'s `None` arm is **structurally satisfiable** post-S68 (it was not pre-S68; the inline substitution was load-bearing because the GOT path did not yet exist for some primitives).

The facade's §"primitives_inline.rs retirement narrative" point that the substitution "becomes an optional optimisation that can be retired without breaking call sites" is now the **landed** structural property, not future work. The closure-criterion for D43 is not file deletion but: (P1) `try_emit_inline_primitive` returns `Option<...>` so unmatched names fall through; (P2) every call site falls through to GOT-indirect on `None`.

**The prior reframe is correct and grounded.** The prior audit version flagged this and expanded it; the grounding citations (Decision 43 §"Status pointer" + Decision 48 §"Shape" + Principle 17) make explicit *why* the reframe is correct.

**What the difference implies.** A Sprint 69 Wave 3 row 7 brief that names "delete `primitives_inline.rs`" as the closure criterion (per the prior backlog framing) encodes both a factual error (the file's only forbidden inhabitant is already gone — F-6) AND a structural mismatch with Decision 43's authorised pattern. The correct closure criterion is the two structural properties P1+P2 named above.

**Disposition.** **Both move (with reframe).**
- **Source: NO action required** beyond what has landed. The remaining file content is the legitimate inline-substitution optimisation per facade §"Operator special-casing is forbidden" point 3 + Decision 43 §"Statement". No file deletion.
- **Facade moves** — `backend.md` §"`primitives_inline.rs` retirement narrative" marks D43 full close as **landed** rather than as "Wave 3 closes FIXME 0150" pending. The narrative text: the file's role is narrowed to its legitimate inline-substitution optimisation (name-keyed shortcut over the standard GOT-indirect path, not a parallel dispatch); the parallel-dispatch role retired with `primitive_for_trait_method`'s deletion at S67 W4. The PIF test is P1+P2 above.
- **Sprint 69 backlog row 7 brief**: re-author from "retire `primitives_inline.rs`" to "verify D43 full close: assert P1 (return type is `Option<...>`) and P2 (every call site falls through to GOT-indirect on `None`); update facade narrative to mark D43 full close landed; close FIXME 0150." This is a `/sprint` reframing at the Wave 2 user-checkpoint.

Closes F-7. The reframe is grounded by Decisions 43 + 48 + Principle 17; the prior version of this finding had the right direction but cited none of these.

---

### Finding F-8 — `compile_to_module` introspection parameter

**Facade expects.** §"Free functions" signature (per F-2 grounding citation, Decision 41 §"3.") names `introspection: Option<&DashMap<FQSymbol, Introspection>>` as a parameter. §"Free functions" body (line 38): "Backend also writes `Introspection { clif_ir, disasm, code_size, compile_duration }` into the introspection map iff `introspection.is_some()` — the `Option`'s `is_some()` IS Decision 38's mode discriminator, reaching backend directly via the parameter."

**Source does.** No `introspection` parameter on `compile_to_module` (lib.rs:437-446). Introspection bookkeeping is carried in `CompilationResult.artifacts` per F-2.

**Design intent — grounded.** **Decision 41 §"3."** — explicit in the binding signature (quoted in F-2). **Decision 38** — the mode-discriminator pattern (`Option::is_some()` IS the mode flag, not a separate `enum Mode { Jit, Object, ... }` parameter). **Principle 11 (single pipeline, mode parameters)** — mode reaches backend through the `Option`'s shape, not through a discriminated enum that backend would have to match against.

**What the difference implies.** Today's mode discriminator is implicit (priority worker always wants introspection; nice worker discards artifacts after writing the sidecar) and lives in `int`'s call-site logic. Bundled with F-2 (the introspection parameter is part of the same Decision-41 close).

**Disposition.** **Source moves** (bundled with F-2 in Row 2). The migration adds the parameter to the signature; on `is_some()`, per-symbol writes happen inline in the codegen loop rather than being marshalled through a return-tuple artefact map.

---

### Finding F-9 — `Linker::load_object` method retention

**Facade expects.** §"PIF prep" Row 3 (line 305): "The `Linker::load_object` method becomes `pub(crate)`."

**Source does.** Pub-api line 83: `pub fn cranelisp_backend::cache::linker::Linker::load_object(&mut self, module_name: &str, bytes: &[u8]) -> Result<(), CranelispError>`. The method remains `pub`.

**Design intent — grounded.** **Facade §"PIF prep" Row 3** + the parent facade narrative — `load_object` is at the boundary as a free function (F-3); the method retires to `pub(crate)` once production callers migrate. **Principle 13 (`interfaces.md` is auditable)** — having two `pub` entries for the same operation widens the public surface visible to `cargo-public-api` baselines; narrowing closes the doubling.

**What the difference implies.** Doubled `pub` surface; documented transitional state per Row 3.

**Disposition.** **Source moves** (Row 3 PIF carry, on backlog; bundled with F-3).

---

### Finding F-10 — `Code::Primitive` marker variant

**Facade expects.** §"`Code`" lines 65-78 names `Primitive` as a no-payload variant; Decision 0048 §"Shape" S68 Phase 3 amendment.

**Source does.** `crates/cranelisp-backend/src/code.rs:88-98` declares the `Primitive` variant. Pub-api line 786 confirms. Unit test `code_primitive_marker_variant_constructible_and_distinct` validates construction, pattern-matching, distinctness.

**Design intent — grounded.** **Decision 0048 §"Shape" (S68 Phase 3 amendment, 2026-05-17)** — variant added per user direction for grep-ability at every `Code` match site. **Decision 35 §"Canonical post-rollback shape"** preserved — variant carries no payload; the `*const u8` lives in the GOT slot.

**What the difference implies.** None. Variant is landed per Decision 0048 §"Shape" amendment.

**Disposition.** **No action.** S68 Phase 3 amendment landed correctly.

---

### Finding F-11 — `GotObserver` extension point + `register_got_observer`

**Facade expects.** §"GOT-population observation (extension point)" lines 175-199 prescribes:

```rust
pub enum GotEventTag { JitWrite, LinkerWrite, Redefinition, /* … */ }
pub struct GotEvent { ... }
pub type GotObserver = fn(GotEventTag, &GotEvent);
pub fn register_got_observer(observer: Option<GotObserver>);
```

**Source does.** Submodule `cranelisp_backend::got_observer` carries `register_got_observer` (pub), `emit` (pub, observer-side dispatch), and the three types. Acquire/Release atomic discipline per `got_observer.rs:26`.

**Design intent — grounded.** **Facade §"GOT-population observation"** — extension point for observability; the structural contract is "callers do not reason about Acquire/Release." **Principle 5 (testability is structural)** — `/qa` and `/repl` can register observers to test GOT-population invariants without behavioral CLIF inspection. The pub surface matches the facade's prescription.

**What the difference implies.** None at the structural level. The variant set placeholder (`/* … */`) is intentional facade abstraction.

**Disposition.** **No action.** Optional Wave 2 cosmetic improvement (replace the placeholder with the actual variant set for completeness); not required.

---

### Finding F-12 — `CompilationResult` + `FunctionArtifacts` transitional types

**Facade expects.** §"`CompilationResult` + `FunctionArtifacts` (Rows 2 + 15 transitional)" explicitly names these as **transitional** internal-but-exposed types slated for deletion per the Decision 41 close.

**Source does.** Both live at `lib.rs:128-170` and are `pub`. `CompilationResult` is `compile_to_module`'s return.

**Design intent — grounded.** **Decision 41 §"Final signature"** — quoted in F-2. The return shape eliminates these types. **Principle 7 (single source of truth)** — `code_ptrs: HashMap<Symbol, *const u8>` AND `artifacts: HashMap<Symbol, FunctionArtifacts>` AND `func_arities: HashMap<Symbol, usize>` are per-symbol slices of state that the per-symbol direct-write pattern eliminates entirely (state lives where the symbol lives — on its `ModuleEntry::Def`).

**What the difference implies.** No drift — facade acknowledges; source carries. Compliance test recognises these as known internal exposures.

**Disposition.** **Source moves** (bundled with F-2 in Row 2). When the per-symbol direct-write rewrite lands, both types delete; the introspection bookkeeping moves directly into the caller-supplied `DashMap<FQSymbol, Introspection>`.

---

### Finding F-13 — Root-level re-exports of third-party crates + `build_isa`

**Facade expects.** §"Types originated here" closing paragraph (line 403): "Third-party re-exports (`cranelift_module`, `cranelift_object`, `cranelift::codegen::isa::TargetIsa`, `build_isa`) are out of scope of Principle 15 — they expose backend's chosen codegen toolchain; tracked separately if encapsulation becomes warranted."

**Source does.** `lib.rs:11-17` re-exports all four at the crate root. Pub-api lines 2-4 confirm.

**Design intent — grounded.** **Principle 15 (facade types live with behavior)** — the re-exports are an explicit carve-out per the facade's own closing-paragraph statement. **Principle 13 (`interfaces.md` is auditable)** — the re-exports are part of the audited public surface; the §"Public surface" enumeration should include them so `cargo-public-api` baselines and the facade match line-for-line.

**What the difference implies.** Asymmetric placement — closing-paragraph disclaimer but not in §"Public surface" enumeration. A reader of just §"Public surface" misses them.

**Disposition.** **Facade moves.** Parent facade §"Public surface" gets a new §"Root-level re-exports" subsection naming the four items as part of the as-designed boundary. The closing-paragraph disclaimer remains for the Principle-15 carve-out.

Closes F-13.

---

### Finding F-14 — `CodeFinalizer` trait method enumeration

**Facade expects.** §"`CodeFinalizer` trait + impls (Row 13)" names the three methods (`define_module_got_data`, `finalize_for_code_read`, `try_get_finalized_function`) without showing full signatures.

**Source does.** `lib.rs:200-258` declares the trait with full signatures; impls at lib.rs:260-303+.

**Design intent — grounded.** **Principle 13 (`interfaces.md` is auditable)** — a facade whose mechanical name-substring compliance test cannot catch a signature regression is incomplete. **Decision 41 §"3."** — `compile_to_module` calls these methods via the `M: Module + CodeFinalizer` bound; the bound's contract MUST be auditable at the facade level.

**What the difference implies.** A regression on `define_module_got_data`'s signature (e.g., `slot_funcs: &[(usize, FuncId)]` → `HashMap<usize, FuncId>`) is structurally invisible to the facade as written; the compliance test catches names but not signatures.

**Disposition.** **Facade moves.** Parent facade §"`CodeFinalizer` trait + impls" enumerates the three method signatures verbatim in a fenced block. Closes F-14.

---

### Finding F-15 — `CodeFinalizer` impls live at crate root, not in submodules

**Facade expects.** Same passage as F-14; silent on physical placement.

**Source does.** Both impls at `crates/cranelisp-backend/src/lib.rs:260-303+` (crate root).

**Design intent — grounded.** **Rust's coherence rule** — impls on foreign target types (`JITModule`, `ObjectModule`) must live with the trait (here, `CodeFinalizer` in backend). **Principle 5 (testability is structural)** — `/review`'s per-PR audit relies on knowing where to look for impls; silent placement makes audit work harder than it needs to be.

**What the difference implies.** Reviewers searching `find . -path '*jit*' -name '*.rs' | xargs grep CodeFinalizer` would miss the impl. Documentation gap, not a structural defect.

**Disposition.** **Facade moves (small).** Add one sentence to §"`CodeFinalizer` trait + impls" noting the crate-root placement and the coherence rationale. Closes F-15.

---

### Finding F-16 — `unsafe impl Send/Sync for CompilationResult`

**Facade expects.** Not named.

**Source does.** `lib.rs:179-180`: `unsafe impl Send for CompilationResult {}` + `Sync`. Justified at lines 171-178 with a SAFETY comment.

**Design intent — grounded.** **`CompilationResult` is transitional per F-12 grounded by Decision 41.** The impls retire with the type. **Principle 14 (FFI layout discipline)** — raw pointer fields require deliberate `Send`/`Sync` reasoning; the SAFETY comment is the right discipline for the type's transitional lifespan.

**What the difference implies.** Regression on either impl would not break a compliance test (auto-detected by use, not by name-substring); it would manifest as a build failure in `int`'s worker code (structural enforcement at the consumer site).

**Disposition.** **No action.** Structural enforcement at the consumer site (the workers' send patterns are the regression detector). Since `CompilationResult` is itself slated for deletion in Row 2 (F-2/F-12), enumerating its `Send/Sync` impls in the facade would add work that retires with the type.

---

### Finding F-17 — Private CLIF dump helpers `clif_dump_matches` + `write_clif_dump`

**Facade expects.** Not named. The CLIF dump observability (`CRANELISP_CODEGEN_DUMP`) is an internal observability hook.

**Source does.** `lib.rs:92-118`. Both `fn` (not `pub fn`).

**Design intent — grounded.** **Principle 2 (narrow interfaces)** — internal observability helpers are not part of the public surface. The `CRANELISP_CODEGEN_DUMP` env-var contract IS the public observability surface; the helper functions implementing it are not.

**What the difference implies.** None — private helpers; not part of the boundary.

**Disposition.** **No action.** Private helpers; not part of the public surface.

---

### Finding F-18 — Auto-trait projection noise (ALIGN / Output / Owned)

**Facade expects.** Not named.

**Source does.** Pub-api lines like 34, 41 etc. — auto-projections from `crossbeam_epoch::atomic::Pointable`, `typenum::type_operators::Same`, etc.

**Design intent — grounded.** **Principle 13 (`interfaces.md` is auditable)** + the /arch watch item authorising the /qa Category D1 filter at `tests/facade_compliance.rs` — auto-trait projections from third-party blanket impls are not part of the architectural public surface. They are filtered at the compliance test, not enumerated at the facade.

**What the difference implies.** None at the architectural level — these are auto-derived projections, not real boundary items.

**Disposition.** **No action.** /qa Category D1 filter IS the audit.

---

### Finding F-19 — Decision 0048 §"Structural invariant — backend dep-ban" verification

**Facade expects.** `facades/backend.md` §"Consumed surface" (line 424): "`cranelisp-primitives` — **DEP-BANNED post-S68 Phase 3** (Decision 0048 §'Structural invariant — backend dep-ban', user-arbitrated 2026-05-17)."

**Source does.** Three structural evidence points verify the dep-ban:
1. `crates/cranelisp-backend/Cargo.toml` — `[dependencies]` lists `cranelisp-types`, `cranelisp-intrinsics`, Cranelift etc.; `cranelisp-primitives` is absent. Explicit comment block names Decision 0048 + the no-dep contract.
2. `crates/cranelisp-backend/tests/no_primitives_dep.rs` exists (66 lines). Test asserts `!cargo_toml.contains("cranelisp-primitives")` — currently substring-trips on the comment-block mention; assertion needs scoping to `[dependencies]` and `[dev-dependencies]` sections only.
3. No `use cranelisp_primitives::*` lines in backend source.

**Design intent — grounded.** **Decision 0048 §"Structural invariant — backend dep-ban" (S68 Phase 3, 2026-05-17)** — quote: "`cranelisp-backend` MUST NOT depend on `cranelisp-primitives`. ... With no Rust-path visibility into primitives' fns, backend physically cannot emit a direct-call instruction targeting one." **Principle 18 (Enforce architectural invariants structurally where possible)** — Principle 18's own §"Worked example — primitives dispatch" cites Decision 0048's dep-ban as the canonical example of converting a behavioral invariant ("backend reaches primitives via the GOT, never via direct extern") to a structural property of the workspace DAG.

**What the difference implies.** Structural invariant holds. The GOT-dispatch invariant for primitives is a property of the workspace DAG, not of behavioral tests. Re-adding the dep edge would fail the integration test on next run; re-adding `use cranelisp_primitives::*` in source would compile only after re-adding the Cargo.toml dep — the two would have to break together.

**Disposition.** **No action.** The dep-ban is structurally enforced; the facade text matches the source state. /qa follow-up flagged (not a backend audit finding): refine `no_primitives_dep.rs` to scan only the `[dependencies]` and `[dev-dependencies]` sections so the deliberate comment-block mention does not trip the substring test.

---

### Finding F-20 — `cache::CachedModule` field visibility

**Facade expects.** `facades/backend-cache.md` §"`cache::*` (root)" (lines 186-198):

```rust
#[non_exhaustive]
pub struct CachedModule {
    pub metadata: CacheMetadata,
    pub meta_path: PathBuf,
    pub object_path: PathBuf,
    pub has_object: bool,
}
impl CachedModule {
    pub fn symbol_table(&self) -> &SymbolTable;
    pub fn imported_modules(&self) -> HashSet<ModuleFullPath>;
}
```

**Source does.** Pub-api lines 720-723 verify all four fields ARE `pub`:
```
pub cranelisp_backend::cache::CachedModule::has_object: bool
pub cranelisp_backend::cache::CachedModule::meta_path: std::path::PathBuf
pub cranelisp_backend::cache::CachedModule::metadata: cranelisp_backend::cache::serialize::CacheMetadata
pub cranelisp_backend::cache::CachedModule::object_path: std::path::PathBuf
```
Plus `symbol_table()` and `imported_modules()` methods (lines 725-726).

**Design intent — grounded.** **Principle 13 (`interfaces.md` is auditable)** — the facade matches the live shape. The fields ARE `pub`; the prior audit's unverified concern dissolves on pub-api inspection.

**What the difference implies.** None — facade matches source.

**Disposition.** **No action.** Verified — fields are `pub` per the facade.

---

### Finding F-21 — Sub-facade root re-export layer narrow-to-`pub(crate)` (Wave 4 PIF)

**Facade expects.** `facades/backend-cache.md` §"Wave 4 checklist" enumerates ~25 root-level `cache::*` re-exports each labelled "PIF-narrow | Mark `pub(crate)`; callers use `cache::{submod}::{name}`."

**Source does.** All 25+ re-export rows live as `pub` at `cache::` root.

**Design intent — grounded.** **Principle 2 (narrow interfaces)** — doubled-pub surface where each item has a canonical submodule-qualified path. **Principle 13 (`interfaces.md` is auditable)** — narrowing reduces baseline line count by 25 and removes the doubled enumeration.

**What the difference implies.** Documented Wave 4 PIF gap; mechanical caller migration (`grep cranelisp_backend::cache::` reveals every call site).

**Disposition.** **Source moves** (Wave 4 carry on backlog). Acceptance: post-Wave-4 `cargo public-api -p cranelisp-backend` produces a 25-line shorter `public-api.txt`; facade compliance stays green; `int` builds clean against the narrowed surface.

---

### Finding F-22 — `intrinsic_symbols()` body shrinkage post-S68

**Facade expects.** §"`jit` shape DTOs" (line 258): "**Signature unchanged at S68; body shrinks.**" Lists genuinely-intrinsic targets (heap alloc/dealloc/panic/RC underflow, heap-string alloc/read, vec runtime support, IO entry, IVar create/spark/force). Deletion targets named: every `cranelisp_primitives::*` Rust-path reference inside `intrinsic_symbols()`.

**Source does.** Cargo.toml dep-line removed (F-19). No `use cranelisp_primitives::*` in backend source (F-19). The `ring0_jit_symbols()` call + ~22 individual extern fn references in `intrinsic_symbols()` are deleted (structurally enforced by F-19 dep-ban).

**Design intent — grounded.** **Decision 0048 §"Phase 5 Wave 4 implementation consequence"** — "Backend's current `intrinsic_symbols()` body has direct Rust-path references to `cranelisp_primitives::ring0::ring0_jit_symbols()` plus the ~22 individual extern fns. All such references are deleted in Wave 4; the `cranelisp-primitives` line in `crates/cranelisp-backend/Cargo.toml` then comes out." **Decision 43 §"Bounded-context shift" §4b** — intrinsics' bounded context is "backend-emitted-call targets; runtime support code"; primitives are excluded (they reach via GOT-indirect dispatch from §4a). **Principle 17 (uniform dispatch — every callable goes through the GOT)** — primitives are callables, route through the GOT; intrinsics are non-callables, route via `JITBuilder::symbol(name, ptr)`.

**What the difference implies.** Wave 4 deletion target has landed structurally. Facade text describes the post-shrinkage state; source matches.

**Disposition.** **No action.** Deletion has landed and is structurally enforced (per F-19).

---

## Findings overview (with Grounding column)

| ID | Finding | Disposition | Grounding citation |
|---|---|---|---|
| F-1 | `Code::Jit { ptr }` variant-internal `ptr` field | Source moves (bundled with F-2 Row 2) | Decisions 31 §"Amendment (S66 rollback)" + 35 §"Canonical post-rollback shape" + 48 §"Relationship — Decision 35"; Principle 7 |
| F-2 | `compile_to_module` return shape + generics | Source moves (Row 2 PIF, backlog) | Decision 41 §"3. Backend writes directly..."; Principle 2 |
| F-3 | `load_object` free fn — `object` param name + Linker method coexistence | Both move (Row 3 PIF, backlog) | Facade §"PIF prep" Row 3 + Decision 41 §"Rationale" |
| F-4 | `compile_to_object` body is `Err` stub | Source moves (Row 4 PIF, backlog) | Decision 41 §"3." + FIXME 0184; Principle 11 |
| F-5 | `Linker::get_symbol` return type lift — sub-facade stale | Facade moves | Decision 41 §"Status pointer — S67 close" Wave 3 row; Decision 37 |
| F-6 | `primitive_for_trait_method` deletion tombstone | No action (verified) | Decision 43 §"Status pointer — S67 FULL CLOSE" |
| F-7 | `primitives_inline.rs` retirement reframe | Both move (reframe Row 7 + facade D43 close) | Decision 43 §"Statement" + §"Status pointer"; Decision 48 §"Shape"; Principle 17 |
| F-8 | `compile_to_module` introspection parameter | Source moves (bundled F-2) | Decision 41 §"3." + Decision 38; Principle 11 |
| F-9 | `Linker::load_object` method `pub` → `pub(crate)` | Source moves (bundled F-3) | Facade §"PIF prep" Row 3; Principle 13 |
| F-10 | `Code::Primitive` marker variant | No action (landed) | Decision 0048 §"Shape" (S68 Phase 3 amendment) + Decision 35 |
| F-11 | `GotObserver` extension point + `register_got_observer` | No action (landed); optional facade variant enumeration | Facade §"GOT-population observation"; Principle 5 |
| F-12 | `CompilationResult` + `FunctionArtifacts` transitional types | Source moves (bundled F-2) | Decision 41 §"Final signature"; Principle 7 |
| F-13 | Root-level re-exports (`build_isa`, `TargetIsa`, `cranelift_module`, `cranelift_object`) | Facade moves | Principle 13 + Principle 15 carve-out |
| F-14 | `CodeFinalizer` trait method enumeration | Facade moves | Principle 13; Decision 41 §"3." |
| F-15 | `CodeFinalizer` impls at crate root, not submodules | Facade moves (small) | Rust coherence rule; Principle 5 |
| F-16 | `unsafe impl Send/Sync for CompilationResult` | No action (consumer-site enforced; retires with F-12) | Decision 41; Principle 14 |
| F-17 | Private CLIF dump helpers | No action (private) | Principle 2 |
| F-18 | Auto-trait projection noise (ALIGN / Output / Owned) | No action (/qa Category D1 filter) | Principle 13 + /arch watch item |
| F-19 | Decision 0048 §"Structural invariant — backend dep-ban" verification | No action (structurally enforced); /qa follow-up flagged | Decision 0048 §"Structural invariant"; Principle 18 §"Worked example" |
| F-20 | `cache::CachedModule` field visibility | No action (verified — fields are `pub`) | Principle 13; pub-api 720-723 |
| F-21 | Sub-facade root re-export layer narrow-to-`pub(crate)` (Wave 4) | Source moves (Wave 4 PIF, backlog) | Principle 2 + Principle 13 |
| F-22 | `intrinsic_symbols()` body shrinkage post-S68 | No action (landed; verified F-19) | Decision 0048 §"Phase 5 Wave 4"; Decision 43 §4b; Principle 17 |

**Class counts.** 9 source-moves + 2 both-move + 4 facade-moves + 7 no-action + 0 arbitration = 22 findings.

---

## Calibration — prior dispositions flipped

Prior dispositions (from the 2026-05-19-morning version of this audit) and the re-authored dispositions:

| ID | Prior disposition | Re-authored disposition | Reason for flip / strengthening |
|---|---|---|---|
| F-1 | Requires /arch arbitration (Brief A-1) | Source moves (bundled with F-2 Row 2) | **FLIP.** Decisions 31 §"Amendment (S66 rollback)" + 35 §"Canonical post-rollback shape" + 48 §"Relationship — Decision 35" jointly target-state the slim variants as **landed canonical** statement. The prior framing of "incomplete rollback / pending /arch decision" mis-read the rollback's scope and treated the Decisions as ambiguous. Principle 7 forbids the parallel-store shape source carries. |
| F-2 | Source moves (Row 2 PIF, backlog) — but A-2 framed the generic-vs-monomorphic question as "may need arbitration" | Source moves (Row 2 PIF, backlog) | **STRENGTHENED + sub-flip on A-2.** Decision 41 §"3. Final signature" spells the monomorphic `<M: Module> ... SymbolTable<Code, ()>` shape verbatim. The prior A-2 brief ("may be Decision 32 preservation") was a re-derivation from source; Decision 32 §"Cross-references and amendments" in Decision 41 itself confirms backend monomorphises on `Code` while typecheck stays on `()`. |
| F-3 | Both move (Row 3 PIF, backlog) | Both move (Row 3 PIF, backlog) | Unchanged disposition; grounding strengthened (added Decision 41 §"Rationale" + Principle 2). |
| F-4 | Source moves (Row 4 PIF, backlog) | Source moves (Row 4 PIF, backlog) | Unchanged disposition; grounding strengthened (Decision 41 §"3." + FIXME 0184 + Principle 11). |
| F-5 | Facade moves | Facade moves | Unchanged; grounding strengthened (Decision 41 §"Status pointer" Wave 3 row makes the lift's S67-W4 landing the citation). |
| F-6 | No action (verified) | No action (verified) | Unchanged; grounding citation is Decision 43 §"Status pointer — S67 FULL CLOSE" verbatim. |
| F-7 | Both move (reframe row 7 + facade D43 close) | Both move (reframe row 7 + facade D43 close) | Unchanged direction; grounding strengthened (Decision 43 §"Statement" authorises name-keyed substitution; Decision 48 §"Shape" makes the GOT-indirect fall-through structurally satisfiable; Principle 17 names the uniform-dispatch invariant). The prior reframe lacked these citations. |
| F-8 | Source moves (bundled F-2) | Source moves (bundled F-2) | Unchanged; Decision 38 grounding made explicit. |
| F-9 | Source moves (bundled F-3) | Source moves (bundled F-3) | Unchanged. |
| F-10 | No action (landed) | No action (landed) | Unchanged. |
| F-11 | No action (landed) | No action (landed) | Unchanged. |
| F-12 | Source moves (bundled F-2) | Source moves (bundled F-2) | Unchanged; Principle 7 grounding made explicit. |
| F-13 | Facade moves | Facade moves | Unchanged. |
| F-14 | Facade moves | Facade moves | Unchanged. |
| F-15 | Facade moves (small) | Facade moves (small) | Unchanged. |
| F-16 | No action (consumer-site enforced; bundled F-12) | No action (consumer-site enforced; retires with F-12) | Unchanged; Principle 14 grounding made explicit. |
| F-17 | No action (private) | No action (private) | Unchanged. |
| F-18 | No action (/qa Category D1 filter) | No action (/qa Category D1 filter) | Unchanged. |
| F-19 | No action (structurally enforced); /qa follow-up flagged | No action; /qa follow-up flagged | Unchanged; Principle 18 §"Worked example" cited as the grounding-of-record. |
| F-20 | Facade moves (small, verify-and-align) | **No action** (verified — fields are `pub`) | **FLIP (small).** Pub-api lines 720-723 verify all four fields ARE `pub`. The prior "verify-and-align" disposition assumed the fields might be private with `pub` accessors; verification shows they are `pub` as the facade prescribes. |
| F-21 | Source moves (Wave 4 PIF, backlog) | Source moves (Wave 4 PIF, backlog) | Unchanged. |
| F-22 | No action (landed; verified F-19) | No action (landed; verified F-19) | Unchanged. |

**Dispositions flipped: 3 (F-1, F-2/A-2, F-20).**

Three most consequential flips:

1. **F-1 (arbitration → source moves).** Eliminates a phantom /arch arbitration brief. The slim variants `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)` are landed canonical per Decisions 31+35+48; source's two-field shape is un-migrated. The migration is bundled with F-2 Row 2 — a single change-set covering both Decision 35 variant slim + Decision 41 per-symbol direct-writes.
2. **F-2 / A-2 (arbitration-flavoured concern → unambiguous source moves).** Decision 41's binding signature is monomorphic on `SymbolTable<Code, ()>`; the generic `<C, L>` source carries is pre-Decision-41 shape, not "as-designed Decision 32 preservation." Principle 2 (narrow interfaces) makes the case structurally.
3. **F-20 (facade-moves verify-and-align → no action).** Pub-api verification shows the facade matches source — a finding that the prior audit raised without checking the live boundary. This is a small flip but a representative one: the prior audit dispositioned without the verification it should have done.

---

## Arbitration briefs — A-N

**None.** The configuration grounds every finding. The prior audit's A-1 (`Code::Jit { ptr }`) and A-2 (`compile_to_module` generic vs monomorphic) are dispositioned by Decisions 31+35+48 (A-1) and Decision 41 (A-2). No items remain genuinely unsourced in the architectural configuration.

This section is retained as a record of what was *previously* in arbitration and why it is now grounded — future audits that hit the same surface should recognise that what *looks* like an arbitration question may be a configuration reading the audit has not yet done.

---

**Audit memo committed as durable per-crate artefact per Sprint 69 Category 0 brief. The re-authoring discipline (read the architectural configuration BEFORE dispositioning, cite Decision/Principle/FIXME per finding) is the standing protocol; future sprints re-run this triple (lib.rs + parent facade + sub-facade + pub-api.txt) against this baseline with the discipline as the audit's shape constraint.**
