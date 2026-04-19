# Symbol-Table Generics Activation (Step 5c)

Strategy doc for the call-site sweep that activates the `SymbolTable<C: CodeStore, L: LinkerStore>` parameterisation, places `Arc<Jit>` on `ModuleEntry::Def.code`, and dissolves `SharedState.kept_jits` for Jit retention. This closes G12 and completes Decision 31 Scenario 2 (per-redefinition JIT reclaim).

Spec anchor: `pipeline-v4.md` §9.1 (parameterised `SymbolTable`). Decisions 25 (compiled code on entry), 31 (one `JITModule` per compile batch; `Arc<Jit>` on `ModuleEntry::Def.code`), 32 (`CodeStore` / `LinkerStore` empty marker traits), 35 (`Code` enum location + Layer 2 Option B + `kept_jits` / `kept_linkers` dissolution).

## Wave 3b implementation outcome (Sprint 58)

**Landed**:

1. `Code` enum at `src/code.rs` per Decision 35:
   - Variants: `Code::Jit { jit: Arc<cranelisp_backend::jit::Jit>, ptr: *const u8 }`,
     `Code::Linker { linker: Arc<cranelisp_backend::cache::Linker>, ptr: *const u8 }`.
   - `pub fn ptr(&self) -> *const u8` accessor — uniform across both variants.
   - Manual `Debug` impl (Jit/Linker don't impl Debug); auto-derived `Clone`; `unsafe impl Send + Sync`.
   - `pub type SessionSymbolTable = SymbolTable<Code, ()>` and `pub type SessionModuleEntry = ModuleEntry<Code>` aliases.

2. `pub mod code` removed from `cranelisp-types/src/lib.rs`; the old pointer-only `cranelisp_types::Code` struct deleted (Decision 35: integration layer owns `Code`).

3. `compile_to_module<M, C, L>` parameterised over the symbol-table flavour. Per Decision 35 Layer 2 Option B, the function returns `CompilationResult.code_ptrs: HashMap<Symbol, *const u8>`; the integration-layer `inline_jit_codegen_for_names` (in `src/worker.rs`) constructs `Code::Jit { jit, ptr }` per-entry from the returned pointers. Backend itself never names `Code`.

4. `SharedState.kept_jits` and `SharedState.kept_linkers` deleted. Per-entry `Code::Jit { jit: Arc::clone(&jit_arc), ptr }` (cache-hit: `Code::Linker { linker: Arc::clone(&linker_arc), ptr }`) is the new retention root; `Arc::strong_count` drops as entries evict, and the underlying `Jit::Drop` (calling `unsafe JITModule::free_memory()`) fires when the last clone drops. `kept_dlls` (platform DLLs) is unchanged — orthogonal to Step 5c.

5. `register_defn_signature` (in `cranelisp-typecheck/src/program.rs`) extended to preserve the `code` field on REPL-redefinition upsert. Pre-Wave-3b, replacing the entry with `code: None` was harmless because the `Arc<Jit>` lived in the session-level `kept_jits` pool. Post-Wave-3b, the same replacement would drop the Arc and free the JIT pages mid-typecheck — leaving the GOT slot pointing at freed memory if the redefinition then fails. Carrying the existing `code` forward through registration preserves the Arc; on success, codegen overwrites with the new `Code::Jit`; on failure, snapshot/restore keeps the carried-forward (original) code, and the GOT slot remains valid.

6. **Out-of-scope addendum**: typecheck and types crates *were* touched, contrary to the original CLAUDE-prompt expectation that they should "already work via default propagation". The widespread `TypeCheckEnv<'_>` → `TypeCheckEnv<'_, C, L>` parameterisation, `CompileContext<'a, C, L>`, and helper-function generic propagation (`HeapCategory::classify`, `is_mixed_adt`, `display::*`, etc.) was necessary because the typecheck crate's accessors and helpers are pinned to `<()>` by default; passing the integration layer's `<Code, ()>` flavour required generics-through-the-stack. The `CodeStore` and `LinkerStore` traits gained a `Clone` super-bound to enable the `code.clone()` carry-forward in `register_defn_signature` and the `serialise_meta`/`write_meta` cache-write path. `SymbolTable<C, L>` gained a generic `new_with_params(path)` constructor for callers that need `<Code, ()>` directly. `SymbolTable<()>` gained an `into_concrete<C, L>()` conversion for the cache-restore path (deserialise yields `<()>`, install needs `<Code, ()>`).

7. **Test count delta**: 1717 total, 1712 pass, 5 fail (the same pre-existing baseline as Wave 2 close). Newly-introduced unit tests in `src/code.rs` cover (a) Arc reclaim via `Arc::strong_count` drop chain (Decision 31 Scenario 2 reclaim primitive), (b) `Code::Linker` constructibility, (c) `SessionSymbolTable` concrete-type choice (compile-time `_requires_code_store::<Code>()` assertion), (d) mixed-lineage table (both `Code::Jit` and `Code::Linker` coexist), (e) regression-guard scanning `src/session_v4.rs` for residual `kept_jits`/`kept_linkers` references.

The Layer 1/2 sweep counts in §3 below are *pre-implementation estimates*; the actual sweep was wider than estimated for typecheck (~30 sites parameterised) but matched expectations elsewhere.

## 1. Problem Statement

Decision 31's Scenario 2 (defn redefinition reclaims the JIT pages of the prior definition) is the headline behavioural payoff of this sprint, but it cannot fire until `Arc<Jit>` lives directly on `ModuleEntry::Def.code`. As of Sprint 57, the type-checker crate `cranelisp-types` cannot name `cranelift_jit::JITModule` without inverting the dependency graph (Principle 3 violation). The `SymbolTable<C, L>` generics — empty marker traits that the integration layer instantiates with concrete code/linker types — are the DAG-compatible mechanism that lets `cranelisp-types` stay ignorant of Cranelift while letting the integration layer place `Arc<Jit>` exactly where it belongs.

The activation is mechanically simple but broad. ~182 call sites name `SymbolTable` directly; once it gains generics, every site must either parameterise or pin to `SymbolTable<(), ()>`. Most sites pin (typecheck/frontend/the bulk of backend operate on the typecheck-product flavour) — the generics' default of `()` keeps those signatures unchanged. The integration layer is the sole site that names a concrete `C` other than `()`.

The work is bounded but ordering matters: building too aggressively at the top of the call graph leaves the build red for hours. The plan below sequences the migration so each stage is independently buildable.

## 2. Key Design Decisions

### 2.1 Concrete `C` choice for the integration layer

The integration layer chooses **`C = Code`** where `Code` is an enum unifying fresh-build (JIT-backed) and cache-hit (Linker-backed) compiled code:

```rust
// In src/session_v4.rs (or src/code.rs if extracted).
pub enum Code {
    Jit { jit: Arc<cranelisp_backend::jit::Jit>, ptr: *const u8 },
    Linker { linker: Arc<cranelisp_backend::cache::Linker>, ptr: *const u8 },
}
```

Rationale for the enum (vs `C = Arc<Jit>` directly):

- A real session mixes fresh-build and cache-hit modules. The same `SymbolTable<C, _>` shape must accommodate both. An enum allows the variant to carry the appropriate retention root.
- Decision 31 Scenario 2's reclaim primitive is "drop the `Arc<Jit>` to free the pages." That works inside `Code::Jit` exactly the same way it would work as the bare `C` — the Arc still hits refcount 0 when the last `Code::Jit` referencing it drops.
- Cache-hit modules need `Arc<Linker>` retention with the same drop-when-last-eviction semantics. Folding both into `Code` keeps the pattern uniform.
- The ptr-only access path (every JIT-emitted call site reads `code.ptr`) treats both variants identically.

Rejected alternatives:

- **`C = Arc<Jit>` and a parallel `cache_code: Option<*const u8>` field on `Def`**: re-introduces the splay between fresh-build and cache-hit storage that Decision 25 closed. Two fields, two retention disciplines, two reclaim paths.
- **`C = Box<dyn CodeStore>`**: gives up monomorphisation and adds vtable dispatch on every `code.ptr` access. Decision 32 already rejected `dyn` for this reason.
- **Two separate sessions, one per backing kind**: violates Principle 11 (single pipeline).

### 2.2 Concrete `L` choice for the integration layer

**`L = ()`** — no per-module linker store. The `Linker` lives inside `Code::Linker.linker` per-symbol via `Arc`. There is no per-module `linker` field that needs retention separately.

Rationale: the `.o`-mapped pages are already kept alive by every `Code::Linker { linker, .. }` that points into them — when the last `Def.code = Some(Code::Linker { ... })` referencing a given Linker drops, the `Arc<Linker>` refcount hits 0 and the pages can be reclaimed. There is no scenario where you need to keep the Linker around without keeping any code derived from it.

If a future need emerges (e.g., a Linker holds metadata used for symbol resolution beyond the immediate code), `L` can be re-introduced without further generics churn — the parameter is already there.

### 2.3 `kept_jits` dissolution

**Disposition**: `SharedState.kept_jits` deletes outright as part of the Step 5c sweep. The retention root for every `Arc<Jit>` becomes the `ModuleEntry::Def.code: Some(Code::Jit { jit, ptr })` field (or its clone in another entry produced by the same compile batch).

Current callers of `SharedState.kept_jits.lock().push(...)` (in `src/session_v4.rs` lines around 2503 and the priority worker code at 2497) are rewritten to populate `Code::Jit` on each `Def.code` from the batch. The `Arc<Jit>` is cloned per entry; reclaim happens automatically when the last clone drops. This is precisely Decision 31 Scenario 2.

**Test path**: `/qa` Wave 5 verification — REPL `(defn f [x] x)` then `(defn f [x] (+ x 1))` then `/mem` shows live-bytes drop on the redefinition (current behaviour: the drop only fires at session teardown).

`SharedState.kept_linkers` follows the same logic: every `Code::Linker` carries the `Arc<Linker>` it needs; the parallel pool dissolves. (If a cache-hit module loads `.o`-mapped code but no symbol from it ever ends up on a `Def.code`, the Linker is reclaimable immediately — which is correct behaviour.)

`SharedState.kept_dlls` (platform DLL retention) is *not* affected by Step 5c — DLLs are session-scoped resources that platforms call into through fn pointers stored on `Def.platform_fn_ptr`, but the `.platform_fn_ptr` field is `*const u8` (not Arc-wrapped) and points into pages owned by `kept_dlls`. The `kept_dlls` retention pool is the existing answer.

## 3. Sweep Strategy: Migration Order

The 182 call sites partition into four layers by their relationship to the parameterisation:

### Layer 0: Foundation (`crates/cranelisp-types/src/module.rs`)

Single file. Lands first. Gate-keeps everything else.

- Define `pub trait CodeStore: Send + Sync + 'static {}` + blanket impl.
- Define `pub trait LinkerStore: Send + Sync + 'static {}` + blanket impl.
- Add `<C: CodeStore = (), L: LinkerStore = ()>` to `SymbolTable`.
- Add `<C: CodeStore = ()>` to `ModuleEntry`.
- Change `Def.code: Option<Code>` to `Def.code: Option<C>` (the existing `Code` symbol in `cranelisp-types/src/lib.rs` deletes — replaced by the integration layer's `Code` enum).
- Add `pub linker: Option<L>` (Decision 33 placeholder; `L = ()` for typecheck-flavour tables).

After this, `cranelisp-types` builds standalone if all dependents either pin to `()` defaults or compile against the unparameterised paths — but every dependent crate breaks until they're updated. Don't merge Layer 0 alone; it must land bundled with Layer 1 in the same commit.

### Layer 1: Default-pinned crates (typecheck, frontend, runtime, platform)

Sites in these crates that name `SymbolTable` or `ModuleEntry` get `<(), ()>` (or `<()>`) appended where the type appears in a signature. The default makes most sites work with no change at all — explicit `<()>` is needed only where the compiler can't infer.

Order within Layer 1:

1. **`cranelisp-typecheck`** — owns `cranelisp-types/src/module.rs` per Decision 33; the largest call-site cluster. ~80 sites by rough estimate. Most are method receivers on `SymbolTable` — these continue to work as `impl<C: CodeStore, L: LinkerStore> SymbolTable<C, L>` blocks. Free-function signatures that take `&SymbolTable` get `&SymbolTable` (no change — `()` defaults). Iteration over `ModuleEntry` works through `()`-defaulted variants. Friction zone: any `match entry { ModuleEntry::Def { code, .. } => ... }` that references the `code` field needs to handle `Option<()>` (which is `Option<()>` — a meaningless tag). For typecheck, `code` is never read; the matches all use `..`.
2. **`cranelisp-frontend`** — small footprint (<10 sites). Mostly threading `&SymbolTable` through resolver helpers.
3. **`cranelisp-runtime`** — no SymbolTable references (runtime is pure data).
4. **`cranelisp-platform`** — no SymbolTable references.

Verification at each crate close: `cargo check -p <crate>` clean. Move to the next crate only after the current one builds.

### Layer 2: `cranelisp-backend` (mostly default-pinned, one exception)

~50 sites. Most operate on the typecheck-product flavour and pin to `()`.

The exception is `compile_to_module` — its return path is the producer of compiled code. Today it returns code in a separate result type; Step 3b had it write `Code` into `Def.code` directly via the symbol table. Step 5c rewrites that to write `C` (the chosen integration-layer concrete) into `Def.code`. Two options:

**Option A (preferred)**: `compile_to_module` becomes generic over `C: CodeStore + From<RawCode>`, where `RawCode` is a backend-internal type carrying `Arc<Jit>` + `*const u8`. The integration layer's `Code` enum implements `From<RawCode>` (returning `Code::Jit { ... }`). This keeps `cranelisp-backend` ignorant of the integration layer's `Code` enum.

**Option B**: `compile_to_module` returns the raw `(Arc<Jit>, HashMap<Symbol, *const u8>)` tuple and the priority worker (in `/int`) writes the `Code::Jit { ... }` entries onto each `Def.code`. This pushes the responsibility outward — backend stays simple, integration layer absorbs the conversion.

Option B is preferred — it keeps the `compile_to_module` signature symmetric across JIT and Object module backings (the `ObjectModule` path already returns bytes, not codestore wrapping), and avoids forcing `cranelisp-backend` to invent a `RawCode` type. Decision deferred to `/backend` review of `compile-to-module.md` minor update.

### Layer 3: `src/` (the integration layer; the only crate that names a concrete `C`)

~50 sites. The instantiation site is `src/session_v4.rs::SharedState.symbol_tables: DashMap<ModuleFullPath, SymbolTable<Code, ()>>`. Cascades from there:

- `ReplSession` and the worker types reference `SymbolTable<Code, ()>` everywhere — refactor by introducing a `pub type SessionSymbolTable = SymbolTable<Code, ()>;` alias near the `Code` enum and using the alias throughout. One alias, ~50 site touches all become `SessionSymbolTable` references, then inference kicks in.
- The `Code` enum lands as part of this layer (with `From` impls for the backend's raw types per Layer 2 Option B).
- `kept_jits` and `kept_linkers` deletion lands here; the priority worker's compile-finalise path rewrites to populate `Code::Jit` on each `Def.code`.
- `try_cache_hit_load` rewrites to populate `Code::Linker` on each `Def.code` after the linker resolves the symbol → addr map.
- `format_def_entry` and other introspection paths read `code.is_some()` to determine "is compiled?" — works uniformly across `Code::Jit` and `Code::Linker`.

Order within Layer 3:

1. Define `Code` enum + `SessionSymbolTable` alias near the top of `src/session_v4.rs`.
2. Update `SharedState.symbol_tables` field type.
3. Sweep `src/worker.rs`, `src/session_v4.rs` other call sites with the alias.
4. Delete `kept_jits` / `kept_linkers`. Compile errors will now point to every site that pushed; rewrite each to populate `Code::Jit` / `Code::Linker` on the appropriate `Def.code`.
5. Verify `/qa` Wave 5 reclaim test passes.

### Layer 4: `tests/`

Small footprint; tests that construct `SymbolTable` directly use `SymbolTable::new(path)` which infers `<(), ()>`. Tests that reach into `Def.code` (rare) need to handle `Option<()>` or `Option<Code>` depending on whether they touch fresh-build state. Most tests don't care.

## 4. Migration Order Summary

| Stage | Crate(s) | Sites (rough) | Ordering | Build-green checkpoint |
|---|---|---|---|---|
| 1 | `cranelisp-types` (Layer 0) + `cranelisp-typecheck` (Layer 1) | ~80 | Bundle in one commit; the type changes break `cranelisp-typecheck` until updated. | `cargo check -p cranelisp-types && cargo check -p cranelisp-typecheck` |
| 2 | `cranelisp-frontend` | <10 | Independent of stage 1; can run in parallel. | `cargo check -p cranelisp-frontend` |
| 3 | `cranelisp-backend` | ~50 | After stages 1–2. | `cargo check -p cranelisp-backend` |
| 4 | `src/` integration layer (`SessionSymbolTable` alias, `Code` enum, `kept_jits` dissolution) | ~50 | After stage 3. | `cargo check -p cranelisp` and full `cargo nextest run` |
| 5 | `tests/` adjustments | <10 | After stage 4; only if any tests break. | `cargo nextest run` |

The hot path (fresh build of a single module) exercises stages 3 and 4 together; if stage 4 lands without stage 3's option-B `compile_to_module` shape decided, a transient `Code::from(raw)` shim suffices for Wave 2 and gets reabsorbed in Wave 3 — but the preferred path is decide Layer 2 first, then sweep.

## 5. Edge Cases & Invariants

- **`format_def_entry` and other introspection that displays `code.is_some()`**. Today reads "yes/no compiled". Step 5c keeps this — `Some(Code::Jit { .. })` and `Some(Code::Linker { .. })` both indicate compiled state. Display tests should not need updating.
- **`debug_assert!`s on GOT slot consistency**. The GOT base address comes from `SymbolTable.got` (unchanged); `Def.code.ptr` is what got written into the slot at codegen time. Cross-checks remain valid.
- **Cache-hit + redefinition**. A REPL user who types `(defn f [x] x)` (cache-hit from prior session) then `(defn f [x] (+ x 1))`: the prior `Def.code = Some(Code::Linker { linker, ptr })` drops; if no other entry held a clone of that `Arc<Linker>`, the linker pages can reclaim. The new `Def.code = Some(Code::Jit { ... })` carries the fresh JIT batch's Arc. Mixed lineage is fine.
- **Macro clause Defs**. `__macro_{name}_clause_{i}` Defs follow the same `code` lifecycle as user fns. Their `Code::Jit { jit, .. }` shares the `Arc<Jit>` with sibling user fns from the same compile batch — they reclaim together, atomically.
- **`Send + Sync` of `SymbolTable<Code, _>`**. `Code` carries `Arc<Jit>` and `Arc<Linker>` and a `*const u8`. The Arc parts are `Send + Sync` (by Arc's semantics); the raw pointer needs an `unsafe impl Send + Sync` on the `Code` enum (analogous to today's `unsafe impl Send + Sync for ModuleEntry` at `crates/cranelisp-types/src/module.rs:239`, with the same safety reasoning — the pointer is an integer handle into pages that the Arc keeps alive).
- **Parallel worker access**. The worker holds a `&Arc<SharedState>`; reading `symbol_tables[m].get(name).code.as_ref()` returns `&Option<Code>`. Cloning `Code` is cheap (Arc bumps); workers can clone without contention.
- **`Option<C>` deserialise**. `code` is `#[serde(skip)]`; on deserialise the field comes back as `None` regardless of `C`. The cache-hit path (Step 5b) populates `Some(Code::Linker { ... })` after the Linker resolves the addr. Order matters: install symbol table → drive linker → populate `code` → notify scheduler typecheck-done.

## 6. Cross-Skill Coordination

| Skill | Coordination point |
|---|---|
| `/typecheck` | Owns `cranelisp-types/src/module.rs` (per Decision 33). Lands the trait definitions + parameterisation in one commit alongside the typecheck-side sweep. |
| `/backend` | Owns `compile_to_module` signature. Decides Layer 2 Option A vs B. Updates `compile-to-module.md` minor. |
| `/platform` | No direct touch; `kept_dlls` and `platform_fn_ptr` are out of Step 5c scope. Confirms in addendum to `platform-registry-removal.md`. |
| `/qa` | Wave 5 reclaim test (Decision 31 Scenario 2) is the headline verification. Without the test, the Step 5c claim is unverified. |
| `/repl` | New demo vignette: redefine + `/mem` showing live-bytes drop. |

## 7. Sketch Comparison

The sketch did not have parameterised symbol tables. Its `CompiledModule` carried a concrete `JitModule` reference (the prototype's wrapper around `cranelift_jit::JITModule`) inline, with `serde(skip)` on the field. This worked because the sketch was a single-pipeline monolith (`CompiledModule` lived in the binary crate, not in a stable types crate); the `cranelisp-types` → `cranelisp-backend` direction the reimplementation forbids was implicit-but-violated in the sketch's structure (Architecture Principle 3).

The reimplementation diverges in three ways:

1. **Generics rather than concrete types in the stable crate**. `cranelisp-types` cannot name `Jit`; the generics keep it ignorant. The integration layer chooses the concrete. The sketch's structure-by-monolith approach is unavailable to us by design.
2. **One enum per integration layer (`Code`), not a per-module storage strategy**. The sketch had several different lifetime stories for code (JIT pages, cached `.o` pages, intrinsic functions) and no unified abstraction. The `Code` enum gives them all one shape.
3. **Reclaim semantics are explicit and tested**. The sketch never reclaimed JIT pages — it leaked them per redefinition. Decision 31 + Step 5c make reclaim a first-class behaviour with a specific test (Scenario 2). This is genuinely new; no sketch precedent exists.

The sketch's lifetime story for cached `.o` was: load through `linker.rs`, hold pages alive via `mmap`, never reclaim until process exit. The reimplementation matches this for cache-hit (Linker pages live as long as any `Code::Linker { linker, .. }` references them; reclamation on the last drop is new). For fresh-build JIT pages, the sketch leaked; the reimplementation reclaims per Decision 31.

## 8. Open Questions

- **Layer 2 Option A vs Option B for `compile_to_module` shape**. `/backend` decides during Wave 1 review of `compile-to-module.md` minor update. `/int`'s sweep accommodates either; B is preferred per §3 Layer 2.
- **Does `kept_linkers` truly dissolve, or does it persist in narrowed form?** Hinges on whether any Linker holds metadata used outside the per-symbol code path. Current evidence: no — `Linker` in `crates/cranelisp-backend/src/cache/` is purely a code-pages-and-symbol-table wrapper. Deletion is the default plan; revisit if Wave 2 surfaces a reason.
- **Eager `Arc<Jit>` clone on every entry vs lazy share via `OnceLock`**. The plan above clones the Arc per `Def.code` from the batch. For batches with ~100 functions this is ~100 atomic increments at compile-finalise time — negligible. If profiling shows a cost we can introduce a per-batch `Arc<OnceLock<Jit>>` shim, but premature.

## 9. Next Skills

- `/typecheck` — `ast-annotation.md` §12 (generics shape, read-only from typecheck POV) lands before Wave 2.
- `/backend` — `compile-to-module.md` minor update with Layer 2 option resolution; `module-caching.md` cross-references for the Linker shape.
- `/qa` — Decision 31 Scenario 2 reclaim test (Wave 5).
- `/repl` — `ring4p.demo` vignette for the headline behaviour.
