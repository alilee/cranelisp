# W5 retirement fold mapping — `facades/backend.md` + `facades/backend-cache.md`

**Sprint 75 W5a. Authored by `/design (backend)`.** This document is the
mechanical fold map for retiring the two backend facade files (the 7th
retirement data point — one crate, two facade files). It tells:

- **`/dev (backend)`** (W5a-dev) exactly which rustdoc home each facade section
  folds to (`lib.rs //!`, per-item `///`, cache submodule `//!`/`///`), and
  which facade text is **phantom/stale and must be DROPPED** (not folded).
- **`/arch`** (W5b) exactly which **bounded-context invariants** belong in
  `bounded-contexts.md §3` (backend), and confirms **nothing** from
  `backend-cache.md` goes to BC (it is an implementation detail).

It documents **post-W4 current source reality**, validated against
`crates/cranelisp-backend/src/{lib,code,artefact,error,jit,compiler/apply,
compiler/literals,cache/*}.rs` and `crates/cranelisp-backend/public-api.txt`
(584-line baseline). Where the facade target-states ahead of source, the fold
records it as a **forward note**, never a current-state claim.

---

## The governing distinction (user-confirmed — held)

- **`backend` is a BOUNDED CONTEXT.** `backend.md` folds to `lib.rs //!` (the
  boundary narrative) + per-item `///` on the boundary surface; its
  cross-surface narrative + **bounded-context invariants** go to
  `bounded-contexts.md §3` (/arch's W5b — this doc maps what goes there).
- **`backend-cache` is an IMPLEMENTATION DETAIL of backend** — the persistence
  half, a submodule. `backend-cache.md` folds **ONLY** to the cache submodule
  rustdoc (`cache/mod.rs //!` + per-submodule `//!` + per-item `///`). Its 5
  invariants are **internal implementation invariants** documented in the cache
  rustdoc — **NOT** promoted to `bounded-contexts.md`. **No §3a, no BC-level
  cache entry.** The bounded-context-vs-implementation-detail line is held.

---

## Part 0 — Source-validated reality (the conformed boundary)

The backend public boundary, as it exists in source post-W4 (baseline-confirmed):

### Codegen boundary — three free functions (`lib.rs` root)

```rust
pub fn compile_to_module<M, C, L>(
    module_path: ModuleFullPath,                                 // BY VALUE (not &)
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,   // raw DashMap, generic <C,L>
    module_aliases: &ModuleAliases,
    module: &mut M,                                               // &mut M (borrow only)
) -> Result<CompilationArtifacts, CompilationError>
where M: Module + CodeFinalizer, C: CodeStore, L: LinkerStore;

pub fn load_object<C, L>(
    module: &ModuleFullPath,
    object_bytes: &[u8],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,   // NO module_aliases param
) -> Result<LinkerArtefact, CranelispError>
where C: CodeStore, L: LinkerStore;

pub fn produce_disasm<C, L>(
    fq: &FQSymbol,
    code_size: usize,                                            // caller-supplied
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
) -> Result<String, CompilationError>
where C: CodeStore, L: LinkerStore;

pub fn build_isa(is_pic: bool) -> Result<Arc<dyn TargetIsa>, CranelispError>;  // re-export of cache::object::build_isa
```

**Source differs from facade pre-W5 text:** generic over `<M, C, L>` (NOT
`<M>` pinned to `Code`); `module_path` by value; raw `&DashMap<…, SymbolTable<C,L>>`
(NOT `&SymbolTables<Code, ()>`); `load_object` takes **3** args (no
`module_aliases`) and returns `CranelispError` (not `CompilationError`). **Fold
the source signatures.**

### Boundary types (`lib.rs` root + sibling modules)

- `CompilationArtifacts { clif_ir: String, code_size: usize, compile_duration: Duration }` — `#[non_exhaustive]`, `lib.rs`.
- `CompilationError { SymbolNotCompilable, CodegenFailed, ModuleError }` — `#[non_exhaustive]`, `error.rs`. Bidirectional `From` bridge with `CranelispError`.
- `LinkerError { SymbolNotFound, RelocationFailed }` — `#[non_exhaustive]`, `error.rs`.
- `Code { Jit(Arc<Jit>), Linker(Arc<Linker>) }` — `#[non_exhaustive]`, `code.rs`. **No `Primitive` variant, no `ptr` field.** Carries lifecycle owner ONLY. Offers `Code::jit(Arc<Jit>)` + `Code::linker(Arc<Linker>)` constructor associated fns + manual `Debug` + `unsafe Send/Sync`.
- `LinkerArtefact { linker: Arc<Linker>, ptrs: HashMap<Symbol, *const u8> }` — `#[non_exhaustive]`, `artefact.rs`.
- `ObjectArtefact { object: Vec<u8>, sidecar: SymbolTable<(),()> }` — `#[non_exhaustive]`, `artefact.rs`. **PHANTOM: constructed nowhere** (no producer in source; `compile_to_object` was retracted/deleted). See DROP list.
- `Jit` (opaque) — `jit.rs`. Public surface: `new`/`new_with_symbols`/`new_with_isa` (3 ctors — S77 target collapses to `Jit::new(symbol_tables)`), `jit_module(&mut self) -> &mut JITModule`, `Drop`, free fn `jit_free_memory_call_count()`. All orchestration methods are `pub(crate)` (W4 narrowing **done**).
- `CodeFinalizer` trait (3 methods: `finalize_for_code_read`, `try_get_finalized_function`, `define_module_got_data`) + impls on `JITModule`/`ObjectModule` — `lib.rs`. STAYS `pub` (named in `compile_to_module`'s `M: Module + CodeFinalizer` bound).
- `GotEvent`/`GotEventTag`/`GotProvenance`/`GotObserver` + `register_got_observer` + `emit` — `got_observer.rs`.
- `HeapCategory` + `classify` — `heap.rs`.

### Constructor codegen (`compiler/apply.rs`, `pub(crate)`)

- `compile_constr_adt(tag, fields, span)` + `emit_adt_construct(tag, field_vals, span)` — the two-path model EXISTS (nullary → `iconst tag`; data → `emit_alloc`+tag+stores). Closure-as-value path **deleted** (no `compile_data_constructor_*` in source — confirmed).
- **PARTIAL:** `nullary_constructor_tag` + `data_constructor_info` STILL EXIST in `compiler/literals.rs` (lines 166, 179, `pub(crate)`). The facade's "single handler replacing … `nullary_constructor_tag`, `data_constructor_info` family / ~200 LOC removed" is only partially realised. Fold as current-state with a forward note (see DROP/forward list).

---

## Part 1 — `backend.md` → rustdoc-home mapping (condensed)

Legend: **LIB** = `lib.rs //!`; **ITEM** = per-item `///` on the named item;
**BC** = `bounded-contexts.md §3` (for /arch); **DROP** = phantom/stale, do not
fold (reason given); **FWD** = fold as forward note (`// target (S77):` /
forward section), not a current claim.

| `backend.md` section | Home | Notes |
|---|---|---|
| Header "Bounded context citation" | **BC** + **LIB** (1-line) | Typed AST → CLIF → executable; owns codegen/RC/JIT/caching/linking; paired with runtime. The full BC statement is /arch's; LIB carries a 1-line crate purpose. |
| "This spec is target-stating / drift detection" | **DROP** | Facade-mechanics meta; not a source fact. The baseline + compiler IS the contract post-retirement (per `feedback_retired_facade_drops_compliance`). |
| §"Free functions — three codegen entry points" (intro + 3 signatures) | **LIB** + **ITEM** (`compile_to_module`/`load_object`/`produce_disasm`) | Fold the **source** signatures (Part 0), NOT the facade's `<M>`/`&SymbolTables<Code,()>` text. LIB states "codegen boundary is exactly three free functions". |
| `compile_to_module` mode-agnostic / generic-over-M / cardinality-by-`names` narrative | **ITEM** (`compile_to_module ///`) + **BC inv 1** | "Single compilation entry per mode; mode is the `Module` instance, not a param" is BC inv 1. The `symbol_tables`-is-single-source detail → ITEM. |
| "`symbol_tables` is the single source for every codegen decision" para | **ITEM** (`compile_to_module`) | Long para — condense to: callee/GOT-target via `resolve_got_target`, arity via `resolve_func_arity`, `entry.kind` → dispatch shape, ctor metadata, per-module GOT. |
| "There is no separate object-compile entry" + §2.5 caller-finalize | **ITEM** (`compile_to_module`) + **BC inv 3** | Object path = `compile_to_module::<ObjectModule>` + caller `finish().emit()`. Real. |
| **Tombstone — `compile_to_object` retracted** | **DROP** (as standing text) → one-line **ITEM** note | Already enacted in source (deleted; `lib.rs:957` NOTE block exists). Keep only a terse `///` line on `compile_to_module`: "object path is `compile_to_module::<ObjectModule>` + caller finalize; no separate object entry." The historical tombstone narrative is git history, not rustdoc. |
| D41 #2 GOT-slot-write / #1 caller-composes-`Code` paragraphs | **ITEM** (`compile_to_module` + `Code`) + **BC inv 3** | Real (confirmed in `lib.rs` Step 5 + `code.rs`). Backend writes `got().store_slot`; caller composes `Code`. State honestly: backend OFFERS `Code::jit`/`Code::linker` ctors but `compile_to_module` itself does not call them. |
| "Who constructs `Code` — the caller, both variants" para | **ITEM** (`Code`) + **BC inv 3** | Real. Symmetric Jit/Linker rule. |
| `produce_disasm` on-demand / caller-supplies-`code_size` / capstone para | **ITEM** (`produce_disasm`) | Real (`lib.rs:850`, capstone in `disasm_host`). |
| `load_object` cache-hit entry para | **ITEM** (`load_object`) | Real. Note 3-arg source shape. |
| nice-worker object-codegen path para | **ITEM** (`compile_to_module`) + cache `object` `//!` | Cross-ref; object packet detail lives in cache rustdoc. |
| §"Return shapes" — `CompilationArtifacts` + doc | **ITEM** (`CompilationArtifacts`) | Real. Already has good `///` in `lib.rs:145-174`; fold the always-created rationale. |
| §"Return shapes" — `LinkerArtefact` | **ITEM** (`LinkerArtefact`) | Real. Already documented in `artefact.rs`. |
| §"Return shapes" — `ObjectArtefact` | **DROP from boundary narrative** → **ITEM** flagged | PHANTOM: no producer in source. Fold a `///` that states it honestly: "sidecar+`.o` pair shape; **not currently produced** — the object path returns bytes via caller `finish().emit()` + sidecar via cache `serialize`. Retained as a typed shape for a future single-call object entry; delete candidate." Flag to /dev: consider deleting the type. |
| §"`Code` — per-symbol lifecycle owner" (enum + slim narrative) | **ITEM** (`Code` enum + module `//!` in `code.rs`) + **BC inv 3** | Real. `code.rs //!` already carries the full reclaim/safety narrative; fold any missing facade nuance there. |
| "read the GOT slot, do NOT match on `Code` for ptr" para | **ITEM** (`Code`) | Real. |
| "Per-symbol redefinition reclaim preserved" para | **ITEM** (`Code` / `Jit`) + **BC inv 5** | Real (`jit.rs` Drop + counter). |
| §"Errors" — `CompilationError` + `LinkerError` + paras | **ITEM** (both enums in `error.rs`) | Real. `error.rs` already documents both; fold the §2.7 typed-signal rationale. |
| §"`Jit` — JIT retention newtype" (struct + Drop + Send/Sync) | **ITEM** (`Jit` + `jit.rs //!`) | Real. Fold the Cranelift-evidence reclaim rationale onto `Jit::drop` / struct (already largely present `jit.rs:206-283`). |
| §"`Linker` — cache-load retention newtype" | cache `linker` `//!` + **ITEM** (`Linker`) | `Linker` lives in `cache::linker`; its retention-newtype role is cache-submodule rustdoc. Parent `backend.md` only names it as a boundary type carried by `Code::Linker`/`LinkerArtefact` → one cross-ref line in `code.rs`/`artefact.rs`. |
| §"Cache submodule" (pointer to backend-cache.md) | **DROP** | Pure cross-facade pointer; superseded by the cache rustdoc itself. |
| §"GOT-population observation" (extension point + types + `register_got_observer`) | **ITEM** (`got_observer` module `//!` + each item) | Real. Fold the "third observability instance / IoObserver-shaped" narrative onto `got_observer.rs //!`. |
| §"Public consts: None" | **DROP** | Trivial. |
| §"Internal-but-exposed surface" intro + S75 reclassification | **DROP** (as facade-mechanics) → distilled into **ITEM** `pub(crate)` rustdoc | The "why pub" rationale per item is better expressed as the existing `pub(crate)` + `#[allow(dead_code)]` FIXME notes already in `jit.rs`. No boundary content. |
| §"Codegen-orchestration internals (Row 10)" (`FnCompiler`/`CompileContext`/`MatchContext`/`TracedFnInfo`/`MATCH_EXHAUSTION_TRAP`) | **ITEM** (`compiler` module `//!` + items) | These are `pub` internal codegen primitives; document at `compiler/*` rustdoc as internal-but-exposed (test instantiation). Not boundary. |
| §"Compiler submodules (Row 10 expanded)" | **ITEM** (`compiler` `//!`) | Submodule organisation note → `compiler/mod.rs //!`. |
| §"GOT-target resolution helpers (Row 11)" (`resolve_func_arity`/`resolve_got_target`/`got_data_symbol_name`/`MATCH_EXHAUSTION_TRAP`) | **ITEM** (each item `///`) | Real internal primitives. Document at item. |
| §"Module/submodule re-exports (Row 7/14)" (`codegen_types`/`got`/`got_observer`/`heap`/`exe::generate_startup_object`) | **ITEM** (each module `//!`) | Document each `pub` submodule's role at its `//!`. |
| §"Heap classification" (`HeapCategory` + `classify` + pending cascades) | **ITEM** (`heap.rs //!` + `HeapCategory`/`classify`) | Real. Fold the two-mode-`Option<&tables>` contract + the 3 pending structural cascades as `// FIXME`/forward notes already partially in `heap.rs`. |
| §"`jit::Jit` boundary + orchestration method-set (Row 9)" | **ITEM** (`Jit` items, `pub(crate)`) + **FWD** | The `pub`/`pub(crate)` rulings are **already enacted** in source (W4 done). Fold the minimal-boundary statement (3 ctors + `jit_module` + Drop public; orchestration `pub(crate)`) onto `jit.rs //!`. **FWD:** `Jit::new(symbol_tables)` collapse + `INTRINSICS_TABLE` read = S77 — mark as `// target (S77):` notes (already present at `jit.rs:96-101,285-291`). |
| §"`jit` shape DTOs (Row 15)" (`IntrinsicSymbol`/`IntrinsicFuncIds`/`IntrinsicIds`/`CompileArtifacts`) | **ITEM** (each DTO, `pub(crate)`) | Real (`pub(crate)` in source). Document at item; note S77 home-shift for `IntrinsicSymbol`. |
| §"`CodeFinalizer` trait + impls (Row 13)" | **ITEM** (`CodeFinalizer` trait + impls — already richly documented `lib.rs:176-372`) | Real, STAYS `pub`. Boundary (named in generic bound). |
| §"`CompilationResult` + `FunctionArtifacts` (transitional)" | **DROP** | STALE: `CompilationResult` does not exist in source; `FunctionArtifacts` IS `pub(crate)` (`lib.rs:137`, not the facade's transitional-public claim). Fold only `FunctionArtifacts`'s existing `pub(crate) ///`. No `CompilationResult`. |
| §"`primitives_inline` (Rows 7+6)" + retirement narrative | **ITEM** (`primitives_inline.rs //!` + items) | `is_known_builtin`/`try_emit_inline_primitive` real (`pub`). `primitive_for_trait_method` DELETED — DROP the tombstone (git history). Fold name-keyed-shortcut role onto `//!`. |
| §"PIF prep — Wave 3 targets" (Rows 1-8) | **DROP** | All resolved/enacted (Code in backend; return shape landed; `load_object` free fn exists; `compile_to_object` retracted; `get_symbol` typed; `primitive_for_trait_method` deleted). Facade-process bookkeeping, not boundary content. |
| §"REV-5 audit (cranelisp_op_*)" tombstone | **DROP** | CLOSED; git history. |
| §"Non-goals / Operator special-casing forbidden" | **ITEM** (`primitives_inline.rs //!` + `compiler` `//!`) | Fold the "every primitive goes through the same GOT-indirect path; inline substitution is name-keyed-only, never `(trait,method,type)` triples" rule as a forbidden-pattern note. `operators.rs` is **gone** (confirmed — file does not exist); DROP the "scheduled for deletion" text. |
| §"Object file contract" (format / naming+linkage / GOT data symbol / sidecar / `--link` exception / pairing invariant) | **ITEM** (`compile_to_module ///` + `CodeFinalizer::define_module_got_data ///`) + **BC inv 6,7** | Real and load-bearing. Two-GOT model + bare-Local linkage = BC inv 6+7. The `.o` emission detail → `define_module_got_data` `///` (already richly documented `lib.rs:212-251`). Sidecar → cache `serialize` `//!`. |
| §"Types originated here" | **ITEM** (each type's `///`) + **DROP** the FQTypeName/transitional rows | Principle-15 origination note per type. The "moves here at Wave 3 / legacy duplicate" rows are DONE — DROP. |
| §"Consumed surface" (cranelisp-types / intrinsics / primitives dep-ban / Cranelift / capstone) | **LIB** + **FWD** | LIB carries the dependency narrative (what backend imports, the primitives dep-ban, capstone-direct). **FWD:** `INTRINSICS_TABLE` read = S77 — `// target (S77):` note on `intrinsic_symbols()` (already at `jit.rs:96-101`). |
| §"Sealed traits: None" | **LIB** (1 line) | Trivially fold. |
| §"`#[non_exhaustive]` DTOs" | **DROP** | Mechanical; the attributes are on the types themselves. |
| §"Bounded-context invariants" (1-7) | **BC** | The 7 invariants → `bounded-contexts.md §3` (see Part 3). |
| §"Constructor codegen" (`compile_constr_adt`/`emit_adt_construct`/two-path/deletion targets) | **ITEM** (`compile_constr_adt` + `emit_adt_construct ///`) + **FWD** | Real two-path model (already documented `apply.rs:569-621`). **FWD/honest:** `nullary_constructor_tag` + `data_constructor_info` still exist in `literals.rs` — fold "single-handler / ~200 LOC removed" as a **forward** cleanup note, NOT a done claim. GOT-entry-as-callable ctor is S77 (int-produced). |

---

## Part 2 — `backend-cache.md` → cache-submodule rustdoc mapping (condensed)

**Confirming: NOTHING from `backend-cache.md` goes to `bounded-contexts.md`.**
Cache is an implementation detail; its rustdoc home is the cache submodule tree.

Legend: **MOD** = `cache/mod.rs //!`; **SUB** = per-submodule `//!`
(`linker`/`manifest`/`object`/`serialize`); **ITEM** = per-item `///`; **DROP**.

| `backend-cache.md` section | Home | Notes |
|---|---|---|
| Header "Parent facade / largest facade gap" | **DROP** | Facade-mechanics. |
| Header "Bounded context citation" (cache = persistence half) | **MOD** | Fold as the cache `//!` opening: "cache is backend's persistence half — serialises typecheck+codegen products, validates hits, reads back at session start. Lives in backend because `Linker` mediates ELF/Mach-O loading (Cranelift-adjacent, Principle 3)." Implementation-detail framing, NOT a BC entry. |
| "This spec is target-stating / drift" | **DROP** | The doubled re-export layer it cites as "largest drift" is **already retired** (`cache/mod.rs` comment confirms W4 done). |
| §"Architectural shape" (4-submodule table) | **MOD** | Fold the 4-submodule responsibility table onto `cache/mod.rs //!` (already partially present `mod.rs:1-37`). |
| "doubled root re-export layer narrows" para | **DROP** | DONE in source. `mod.rs:16-37` already documents the retirement + canonical submodule paths. Keep that source comment; DROP the facade's target-stating version. |
| §"`cache::linker`" (struct + 4 methods) | **SUB** (`linker //!`) + **ITEM** | **Stale:** facade lists `Linker::load_object` as public PFR — source has it `pub(crate)` (NOT in baseline). Public surface is `new`/`get_symbol`/`register_symbol`. `get_symbol` returns `Result<*const u8, LinkerError>` (typed — **done**, not "pending Wave 3"). Fold source reality. |
| §"`cache::manifest`" (CacheManifest/CachedModuleRef/CacheInvalidReason + methods + free fns) | **SUB** (`manifest //!`) + **ITEM** | Real, matches baseline. Fold each struct/enum/fn `///`. |
| §"`cache::object`" (CacheWritePacket/ObjectCompileInput/ProcessedPacket/FnSlotInfo/IntrinsicTable/IntrinsicEntry + free fns) | **SUB** (`object //!`) + **ITEM** | Real, matches baseline. `build_isa(is_pic: bool)` is the canonical home (re-exported at root). Fold field-level `///` (DTOs cross backend↔int). |
| §"`cache::serialize`" (CacheMetadata/CacheStale + free fns) | **SUB** (`serialize //!`) + **ITEM** | Real, matches baseline. Fold the 6 `CacheStale` variants + `reason()` telemetry note. Sidecar shape = Decision 25. |
| §"`cache::*` (root)" (CachedModule + consts + orchestration fns) | **MOD** + **ITEM** | Real. **Stale:** facade says `try_load_cached_module -> Result<CachedModule, CacheStale>` and `load_cached_object -> Result<(), CranelispError>`; source returns `Result<Option<CachedModule>, CranelispError>` and `Result<HashMap<String,*const u8>, CranelispError>` respectively. Fold source signatures. |
| §"Disposition decisions — per item" (PFR/PIF tables) | **DROP** | Facade-audit bookkeeping. The dispositions are enacted (re-export layer gone, `get_symbol` typed). No rustdoc value. |
| §"`cache::*` root re-export layer (~30 items)" + Wave 4 narrowing | **DROP** | DONE. `mod.rs:16-37` source comment is the durable record. |
| §"Items that should move OUT" (None) | **DROP** | Audit note; the `CacheStale`-hoist-rejected rationale is git/design history, not rustdoc. |
| §"Forbidden patterns" (no cross-submodule unhomed pub / no bare `Option<*const u8>` / no serde change without version bump) | **SUB** (`serialize //!` for the version-bump rule; `mod.rs //!` for the homing rule) | Fold as forbidden-pattern notes — these ARE durable contracts worth keeping in rustdoc. `CACHE_SCHEMA_VERSION` bump rule already documented at `mod.rs:54`. |
| §"Bounded-context invariants" (5 cache invariants) | **MOD** / **SUB** (internal-impl) | **STAY in cache rustdoc as implementation invariants. NOT to BC §3.** See Part 4. |
| §"Wave 4 checklist" + acceptance signal | **DROP** | DONE. |
| §"Cross-references" | **DROP** | Decision pointers; folded inline where load-bearing. |

---

## Part 3 — Bounded-context invariants for `bounded-contexts.md §3` (for /arch)

These are **backend's** invariants (from `backend.md` §"Bounded-context
invariants"). They are cross-surface contracts → `bounded-contexts.md §3`:

1. **Single compilation entry point per mode** (Decision 23) — `compile_to_module<M>` is the sole CLIF emission path; object vs JIT differs only in the `Module` instance; CLIF byte-identical; mode is NOT a parameter.
2. **Uniform consuming calling convention** (Decision 24) — every call site emits identically for RC; caller transfers ownership of heap args; callee owns heap params; no "borrowing" classification.
3. **Compiled-code lifecycle owner lives on `ModuleEntry::Def.code`; fn ptr lives in `SymbolTable.got()` indexed by `got_slot`** (Decisions 25+41) — backend writes the GOT slot via `got().store_slot`; the **caller** composes `Code` (`Code::Jit` from owned `Arc<Jit>`; `Code::Linker` from `LinkerArtefact`); backend cannot construct `Code::Jit` (only borrows `&mut M`). GOT is the single source of truth; `Code` carries lifecycle ownership only. No separate `compile_to_object` entry. No `JitArtefact`.
4. **`defined_symbols()` is the codegen-compilable predicate** (Decision 22) — `compile_to_module` trusts the contract; a `names` entry not in `defined_symbols()` errors rather than synthesises.
5. **Per-symbol reclaim safety** (Decision 41 §"Safety invariant") — custom `Drop for Jit` calls `unsafe JITModule::free_memory()`; the "no derived fn pointer reachable at refcount 0" invariant is upheld by int's discipline (Arc on `.code`, atomic GOT swap on redefinition, fn-values dispatch through GOT).
6. **Two-GOT model, one CLIF** (Decision 23) — same `Linkage::Import` against `__cranelisp_got_{M}` in every CLIF; JIT resolves via `JITBuilder::symbol_lookup_fn`; `--link` resolves via `.o` `Linkage::Export` GOT; backend does not branch on mode.
7. **Bare-name + Local linkage uniformly** (Decision 36) — every user fn is `Linkage::Local` bare-name; no `user`/`main` special case; the `--link` `_main` alias is int's job.

These 7 are the BC §3 payload. (Backend's overall bounded-context statement —
"Typed AST → CLIF → executable; owns codegen, RC, JIT lifecycle, caching,
linking; paired with runtime" — is the §3 header, already present.)

---

## Part 4 — The 5 cache invariants STAY in cache rustdoc (NOT BC)

From `backend-cache.md` §"Bounded-context invariants". These are
**internal implementation invariants** of the cache submodule — they fold to
`cache/mod.rs //!` (or the relevant submodule `//!`), **NOT** to
`bounded-contexts.md`. **No §3a; no BC-level cache entry.**

1. **`Linker` is the only mmap-holder.** Per-symbol retention via `Arc<Linker>`. → `cache/linker //!` + `cache/mod.rs //!`.
2. **`CacheManifest` is the single index.** Per-module sidecars + objects referenced via `modules`, pair-invariantly. → `cache/manifest //!`.
3. **Cache-validity checked at every cache-hit attempt.** `check_manifest` before any `try_load_cached_module`; stale → `CacheStale`; no "use stale anyway". → `cache/manifest //!` + `cache/serialize //!`.
4. **`CACHE_FORMAT_VERSION` and `CACHE_SCHEMA_VERSION` are independent.** Format = `CacheManifest` shape; schema = `SymbolTable` serialised shape. → `cache/mod.rs //!` (consts already there).
5. **No re-codegen on cache-hit.** Cache-hit modules skip `compile_to_module`; read `.o` via `Linker::load_object`; `.o` bytes authoritative. → `cache/mod.rs //!` + `cache/linker //!`.

The line held: these describe how the cache submodule behaves internally; they
are not contracts the rest of the workspace reasons about at the bounded-context
boundary. `/arch` adds **nothing** to BC for the cache.

---

## Part 5 — Phantom/stale facade text to DROP (not fold)

`/dev (backend)` must NOT carry these into rustdoc — they contradict source:

1. **`ObjectArtefact` as a live return shape.** No producer in source; `compile_to_object` deleted. Fold ONLY an honest "not currently produced / delete-candidate" `///`; flag to /dev for possible deletion.
2. **`compile_to_module` signature `<M>` over `&SymbolTables<Code,()>` / `&ModuleFullPath`.** Source is `<M,C,L>` over `ModuleFullPath` (value) + `&DashMap<…,SymbolTable<C,L>>`. Fold source.
3. **`load_object` 4-arg shape with `module_aliases`.** Source is 3-arg, no `module_aliases`. Fold source.
4. **`CompilationResult` (transitional return tuple).** Does not exist in source. DROP entirely.
5. **`FunctionArtifacts` as transitional-public.** Source is `pub(crate)`. Fold its existing `pub(crate)` rustdoc only.
6. **`Linker::load_object` as public PFR method.** Source has it `pub(crate)` (not in baseline). Public Linker surface = `new`/`get_symbol`/`register_symbol`.
7. **`Linker::get_symbol` "return-type lift pending Wave 3" (`Option<*const u8>`).** Already `Result<*const u8, LinkerError>` in source. DROP "pending".
8. **`try_load_cached_module -> Result<CachedModule, CacheStale>`** / **`load_cached_object -> Result<(), CranelispError>`.** Source: `Result<Option<CachedModule>, CranelispError>` / `Result<HashMap<String,*const u8>, CranelispError>`. Fold source.
9. **Doubled root re-export layer "narrows in Wave 4".** Already retired (`cache/mod.rs:16-37`). DROP target-stating text.
10. **`operators.rs` "scheduled for deletion in Wave 4".** File does not exist in source (gone). DROP.
11. **`primitive_for_trait_method` tombstone, REV-5 `cranelisp_op_*` tombstone, all PIF Row 1-8 / Wave-4-checklist process bookkeeping.** Resolved/enacted; git history, not rustdoc.
12. **`Code::Primitive` variant + `ptr` field references.** Source `Code` has neither (FIXME 0244 reversal enacted). Any facade text implying them → DROP.
13. **"~200 LOC removed / single handler replaces the constructor family"** as a DONE claim — partially false (`nullary_constructor_tag`/`data_constructor_info` remain). Fold as FORWARD cleanup note (Part 6).
14. **artefact.rs stale header doc-comment** (`lib.rs`-adjacent block at `artefact.rs:1-27,70-80`) describing `compile_to_module -> Result<(),CompilationError>` and `compile_to_object -> ObjectArtefact`. `/dev` must REWRITE this header to current reality during the fold.

---

## Part 6 — S77-forward items (mark as forward, never current-state)

Fold these as `// target (S77):` rustdoc notes or a clearly-labelled forward
section — the canonical rustdoc must never claim a not-yet-true state. Most are
**already** marked in source (cited); the fold preserves the forward framing.

1. **`Jit::new(symbol_tables)` collapse** — current is `new`/`new_with_symbols`/`new_with_isa` (3 ctors). S77 collapses to one. Already FWD-noted at `jit.rs:285-291`. Fold as `// target (S77):`.
2. **`intrinsics::INTRINSICS_TABLE` read** — backend currently reads intrinsics by Rust path in `intrinsic_symbols()` (`jit.rs:148`). `INTRINSICS_TABLE` does NOT exist yet (intrinsics-source change is S77). Already FWD-noted at `jit.rs:96-101`. Fold as `// target (S77):` on `intrinsic_symbols()` / `IntrinsicSymbol`.
3. **Constructor GOT-entry-as-callable (int-produced)** — S77. The first-class-use `(map Some list)` via ctor `Def`'s `got_slot` is the target; fold as forward on `compile_constr_adt`/`emit_adt_construct`.
4. **Constructor old-family full deletion** — `nullary_constructor_tag` + `data_constructor_info` (`literals.rs:166,179`) still exist. Fold "single-handler consolidation / LOC reduction" as a forward cleanup note, not done.
5. **`int`'s parallel `pipeline.rs` JIT path collapse into `compile_to_module`** — the reason the `pub(crate)` orchestration methods + DTOs carry `#[allow(dead_code)]`. S77. Already noted at `jit.rs:28-32,236-241,285-291`.

---

## Hand-off

- **`/dev (backend)` (W5a-dev):** write the rustdoc per Parts 1, 2, 5, 6. Edit-only-source. The two facade files are NOT yet deleted (that is /arch W5b after rustdoc lands). Rewrite the stale `artefact.rs` header (Part 5 #14). Decide `ObjectArtefact` delete-vs-keep (Part 5 #1).
- **`/arch` (W5b):** write `bounded-contexts.md §3` from Part 3 (7 backend invariants); confirm **nothing** cache-related enters BC (Part 4); then `git rm design/arch/facades/backend.md design/arch/facades/backend-cache.md` and update the §"Canonical documents" facade-retirement tally (7th data point) + the baseline-diff discipline note (`facades/backend-cache.md` reference).
- Post-retirement, per `feedback_retired_facade_drops_compliance`: the crate's surface IS the source (baseline + compiler = definition; rustdoc = rationale). Drop `backend` + `backend-cache` from facade-compliance testing; do NOT substitute a rustdoc self-documentation check.
