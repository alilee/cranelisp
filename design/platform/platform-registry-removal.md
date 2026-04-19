# Platform Registry Removal — Platform-side Design (G8)

**Sprint**: 57 (Pipeline v4 Convergence, Phase 4 Step 4a — G8)
**Author**: `/platform`
**Co-author**: `/int` (see also `design/int/platform-registry-removal.md` when it lands)
**Status**: Phase 3a (Design) — Wave 1 input
**Cross-reference**: `/arch` Decisions 25, 26; `design/arch/interfaces.md` §Module Entries; `design/int/step8-platform-registry.md` (superseded by this document for the G8 consolidation step)

## 1. Background

`PlatformRegistry` was introduced in Sprint 45 (Step 8) to consolidate two previously scattered stores — `platform_symbols: Vec<(String, *const u8)>` and `scheduling_registry: HashMap<Symbol, SchedulingClass>` — into a single `HashMap<FQSymbol, PlatformFunction>` on `CompilerSession`. At Sprint 56 close the DashMap-vs-entry split (Decisions 25, 26) identified this registry as a pre-v4 accretion: the "one store on `SymbolTable`" invariant (Principle 11) requires that platform function pointers and their scheduling class live on `ModuleEntry::Def.platform_fn_ptr`, not on a side map.

Sprint 57 G8 deletes `PlatformRegistry` and migrates those two fields onto `ModuleEntry::Def` directly. The DLL loader, bind-chain analysis, and the JIT symbol collection all become symbol-table reads.

## 2. Current `PlatformFunction` Struct

**Location**: `src/platform_registry.rs` lines 18-25.

```rust
pub struct PlatformFunction {
    pub jit_name: JitSymbol,
    pub fn_ptr: *const u8,
    pub scheduling_class: SchedulingClass,
}
```

Only three fields. Relevant observations for the placement question (§3 below):

- **`jit_name: JitSymbol`** — already persisted on the `ModuleEntry::Def` via `kind: DefKind::Primitive { jit_name: Some(JitSymbol), .. }` (see `src/platform.rs:261`). The registry copy is redundant.
- **`fn_ptr: *const u8`** — runtime-only, non-serializable. `#[serde(skip)]` target. This is the field that Decision 26 moves to `ModuleEntry::Def.platform_fn_ptr: Option<*const u8>`.
- **`scheduling_class: SchedulingClass`** — read by `bind_chain_analysis::classify_expr`. Also runtime-ish in the sense that it never changes for a given platform-function entry, but it is derivable from the DLL manifest at load time (not expensive enough to cache separately if rebuilding is required; but conceptually part of the "what kind of primitive is this?" metadata).

No other fields exist — no arity (it is on `param_names`), no type signature (it is on `scheme`), no bind-chain analysis state (the analysis is purely over `Expr`, reading only `scheduling_class`). This is a strict three-field struct; all three fields are duplicated or derivable from the owning `ModuleEntry::Def`.

**Construction site**: `src/worker.rs::handle_platform` lines 1454-1493 — loads the DLL, calls `manifest_to_descriptors`, and for each descriptor registers a `PlatformFunction` on `ctx.platform_registry`. The `ModuleEntry::Def` for the same descriptor was already inserted by `load_and_register_platform` in `src/platform.rs:246-268`.

**Reader sites** (three distinct consumers):

1. **JIT symbol collection** — `src/worker.rs::collect_jit_setup` (lines 2113-2157) walks the current module's symbol table, finds `DefKind::Primitive { primitive_kind: PlatformEffect, jit_name: Some(_), .. }` entries (and the equivalent `ModuleEntry::Import` chains back to them), looks each `jit_name` up in `platform_registry.fn_ptr_by_jit_name()` to get the `*const u8`, and assembles `Vec<(String, *const u8)>` for `JITBuilder::symbol()`.
2. **IO trampoline** — at runtime, the trampoline (`crates/cranelisp-runtime/src/io.rs`) does not currently read the registry directly; it calls `cranelisp_platform::call_effect_thunk`, whose thunk was constructed inside the platform DLL at effect-creation time. The DLL's `extern "C"` function was located via the JIT linker (point 1). So the runtime trampoline has no registry dependency today. **G8 does not change this** — the runtime path is unchanged; only the JIT-symbol-collection path moves to reading from `ModuleEntry::Def.platform_fn_ptr`.
3. **Bind-chain analysis** — `src/bind_chain_analysis.rs::classify_expr` (lines 137-155) calls `registry.scheduling_class(&symbol)` with a `Symbol` (the bare callee name from an `Apply` expression). It expects `Option<SchedulingClass>`. The lookup currently does a linear scan of all registry entries matching `fq.symbol == symbol`, plus a qualified-name fallback stripping `module/` prefix.

## 3. Position on `scheduling_class` Placement (Decision 26)

### Options as stated by /arch

- **Option A**: Field on `ModuleEntry::Def` directly — `ModuleEntry::Def { …, scheduling_class: Option<SchedulingClass> }`.
- **Option B**: Variant-internal — `PrimitiveKind::PlatformEffect { scheduling_class: SchedulingClass }`.

### Platform-side pros and cons

| Dimension | Option A (sibling field) | Option B (variant-internal) |
|---|---|---|
| Fit with existing `DefKind` | `DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect, jit_name }` already discriminates by `PrimitiveKind` enum. Adding a sibling means carrying `Option<SchedulingClass>` on every `ModuleEntry::Def`, including user functions, constructors, special forms, imports, re-exports, macros' inner defns, etc. That is dead state in >99% of entries. | Fits exactly the existing pattern. `jit_name` already lives *inside* `DefKind::Primitive`; `scheduling_class` belongs alongside it because it is metadata about how the primitive behaves. |
| Encapsulation | `scheduling_class` is readable on any `ModuleEntry::Def` without pattern-matching — ostensibly convenient. But every reader needs to know that the field is only meaningful when `kind` matches `PlatformEffect`, so the Option discipline leaks. Worse, the type signature permits buggy writes (e.g., setting `scheduling_class` on a user fn would compile and silently do nothing). | The field is literally unreachable except after matching `DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class }, … }`. Miswrites are impossible; misreads require an explicit pattern match that the type-checker enforces. |
| Reader boilerplate | `entry.scheduling_class.unwrap_or(Sequential)` at each call site. One line. | `let sc = match entry.kind.as_ref() { DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class }, .. } => *scheduling_class, _ => Sequential };` or the equivalent `if let` pattern. Three lines. |
| Alignment with Decision 26's sibling field (`platform_fn_ptr`) | Consistent — both `platform_fn_ptr` and `scheduling_class` are siblings on `ModuleEntry::Def`, both `Option<…>` with `Some` only for `PlatformEffect` entries. | Inconsistent — `platform_fn_ptr` stays a sibling (per Decision 26 as written: "`Some` only when `kind == DefKind::Primitive { primitive_kind: PlatformEffect, .. }`"). If `scheduling_class` goes inside `PrimitiveKind::PlatformEffect`, one `PlatformEffect` datum is on the sibling and one is on the variant — split state. |
| Serialization | `scheduling_class` is a cheap `Copy` enum; it can round-trip through serde. Could be retained on cache-load without re-reading the manifest. | Same — either location serializes. |
| Re-derivation on cache hit | Requires re-reading the manifest to rediscover `scheduling_class` if it is not serialized. If it IS serialized, both options are equivalent here. | Same. |
| Principle 7 (single source of truth) | OK — each field has one home. | OK — each field has one home. |
| Principle 8 (no interim shapes) | The final state matches Decision 26's sibling pattern. | The final state is slightly different from Decision 26's stated shape for `platform_fn_ptr`. |

### Decision: **Option B — variant-internal `PrimitiveKind::PlatformEffect { scheduling_class }`**

Rationale:

1. **Encapsulation dominates boilerplate.** The pattern-match cost (three lines vs one) is trivially small compared to the cost of dead `Option<SchedulingClass>` state on every non-platform `ModuleEntry::Def` in every `SymbolTable`. Every user-defined function in a program would carry `scheduling_class: None`. That is exactly the kind of "field on a variant where it does not apply" anti-pattern Principle 6 (complexity budget) rejects.

2. **The type system makes mistakes impossible.** With Option B, nobody can write `scheduling_class` to a non-platform entry, because the variant is not `PlatformEffect`. With Option A, miswrites compile and silently lose information. For a field that is the load-bearing input to auto-parallelisation, silent miswrites are a latent class of scheduling bugs.

3. **`jit_name` is already inside `PrimitiveKind::PlatformEffect` (via `DefKind::Primitive { jit_name }`).** `scheduling_class` is the same category of metadata — "what does this primitive do at runtime?". The two fields belong together.

4. **`/arch` prefers Option B** per Decision 26, and `/platform` sees no platform-side objection.

### Note on `platform_fn_ptr` (not `scheduling_class`)

Decision 26 as currently written puts `platform_fn_ptr` on the sibling field (not on the variant). `/platform` observes the same reasoning above applies — `platform_fn_ptr` is also meaningful only for `PlatformEffect` entries, and also carries dead `Option<…>` state on every other `ModuleEntry::Def`. However, **`platform_fn_ptr` is `#[serde(skip)]` runtime state**: the cost is one null pointer word per entry (not a typed `Option` discriminant on serialized output), and the access pattern is different — the JIT symbol collector wants a fast enumeration without matching on `kind`. `/platform` defers to `/int`'s implementation call for `platform_fn_ptr` placement.

**If /int chooses to move `platform_fn_ptr` inside the variant for symmetry with `scheduling_class`**, the variant becomes `PrimitiveKind::PlatformEffect { scheduling_class: SchedulingClass, fn_ptr: Option<*const u8> }` with `fn_ptr` not serde-skipped at the variant-member level but the entire `DefKind` enum's serde discipline is handled at the variant; a custom skip may be needed. The author flags this as a minor serde wart of Option B extended to `fn_ptr`.

**Recommendation**: `scheduling_class` inside `PrimitiveKind::PlatformEffect` (Option B). `platform_fn_ptr` stays on the sibling with `#[serde(skip)]` per Decision 26 as written, unless `/int` sees a compelling reason for symmetry.

### Required changes on the `Module` resolution path (Option B)

When the IO trampoline's scheduling-class check needs `SchedulingClass` for a given callee name during bind-chain analysis (`src/bind_chain_analysis.rs::classify_expr`):

```rust
fn scheduling_class_of(
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    current_module: &ModuleFullPath,
    name: &Symbol,
) -> SchedulingClass {
    // Walk imports and look up the defining entry.
    let Some(table) = symbol_tables.get(current_module) else {
        return SchedulingClass::Sequential;
    };
    let entry = match table.get(name.as_ref()) {
        Some(ModuleEntry::Def { kind, .. }) => Some(kind.as_ref()),
        Some(ModuleEntry::Import { source }) => {
            // Follow Import to defining module.
            symbol_tables.get(&source.module).and_then(|src| {
                match src.get(source.symbol.as_ref()) {
                    Some(ModuleEntry::Def { kind, .. }) => Some(kind.as_ref().clone()),
                    _ => None,
                }
            }).as_ref().map(|k| k.clone()); // slightly awkward through DashMap; /int will shape this
            // In practice use helpers in SymbolTable::resolve_chain
            None
        }
        _ => None,
    };
    match entry {
        Some(DefKind::Primitive {
            primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class },
            ..
        }) => *scheduling_class,
        _ => SchedulingClass::Sequential,
    }
}
```

The qualified-name fallback (`name.rfind('/')`) that `registry.scheduling_class()` currently does becomes the Import chain walk. This is a natural fit — the symbol table already knows about imports; the registry had no awareness and needed a string-prefix heuristic.

`/int`'s Wave 2 design doc owns the exact `SymbolTable` helper signature (e.g., `resolve_entry_chain(module, name) -> Option<(FQSymbol, &ModuleEntry)>`). `/platform` asks only that the helper exists and returns the defining entry after walking Import chains. This helper is already needed for many other G8/G6 read paths.

## 4. `crates/cranelisp-platform/` Impact under G8

The `crates/cranelisp-platform/` crate itself is **unchanged** by G8. `/arch` Decision 26 explicitly states `PlatformRegistry` is deleted — but `PlatformRegistry` lives in `src/platform_registry.rs` (the binary crate), NOT in `crates/cranelisp-platform/`.

### What survives in `crates/cranelisp-platform/`

- **`PlatformManifest`, `PlatformFn`, `HostCallbacks`** — the C-ABI contract types. Required by every platform DLL.
- **`ABI_VERSION`, `IO_TAG_*`, `HEAP_HEADER_SIZE`** — ABI constants.
- **`SchedulingClass` enum** — still needed; becomes a field of `PrimitiveKind::PlatformEffect` per §3 above.
- **`CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLOwned<T>`, `CLType`, `CLHeap`** — safe wrapper types for platform authors.
- **`HostContext`, `GLOBAL_ALLOC`** — platform DLL initialization.
- **`OwnedPlatformFnDescriptor` + `manifest_to_descriptors()`** — safe-Rust descriptor conversion used by the host loader.
- **`call_effect_thunk`** — called by the runtime IO trampoline to force `Effect` nodes.
- **`declare_platform!` macro** — platform authors use this unchanged.

### What changes

Nothing in `crates/cranelisp-platform/` itself. The crate is a stable ABI surface.

### What deletes

Nothing in `crates/cranelisp-platform/`. Deletion is confined to the binary crate:

| Path | Disposition |
|---|---|
| `src/platform_registry.rs` (entire file — ~183 lines including tests) | **DELETE** at G8 close |
| `PlatformRegistry` struct | Deleted with the file. |
| `PlatformFunction` struct | Deleted with the file. The three fields it held are now: `jit_name` already on `DefKind::Primitive.jit_name`; `fn_ptr` moves to `ModuleEntry::Def.platform_fn_ptr`; `scheduling_class` moves into `PrimitiveKind::PlatformEffect { scheduling_class }`. |

### `(platform …)` form semantics confirmation (spec/08-modules.md §8.9.3)

The `(platform …)` form per spec creates a synthetic module `platform.<name>` containing the functions exported by the DLL. Each function becomes a `ModuleEntry::Def` in that synthetic module with:

- `scheme` — the type signature parsed from the manifest's `type_sig` string (`parse_platform_type_sig` in `src/platform.rs`).
- `kind: DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect { scheduling_class }, jit_name: Some(JitSymbol) }` (post-G8).
- `ast: None` — platform fns have no Cranelisp body.
- `code: None` — same; their body is the DLL fn_ptr.
- `platform_fn_ptr: Some(ptr)` (post-G8) — written during `handle_platform` immediately after module-entry insertion.

This matches spec §8.9.3 exactly. Spec text does not need to change; the implementation moves the runtime data onto the symbol-table entry it already creates.

The DLL manifest loader fills `platform_fn_ptr` after `dlopen`+`dlsym` succeeds. On cache-hit load, `platform_fn_ptr` starts `None` (serde-skipped) and is re-filled by re-executing the platform-loading path against the manifest. The `PlatformDecl` entry in the owning module (`src/worker.rs` already persists this in the symbol table as a distinct `ModuleEntry::PlatformDecl`) records the DLL path; the reloader follows it.

## 5. G6 (Code on SymbolTable) and G9 (Persistent Workers) — platform-side impact

### G6 — `code: Option<Code>` on `ModuleEntry::Def`

Platform fns never have Cranelisp-compiled `Code`. Their `ModuleEntry::Def.code` is permanently `None`. The introspection story for platform entries is unchanged: `/sig`, `/doc`, `/info` continue to show the type signature, docstring, and (where relevant) a "primitive: PlatformEffect" indicator. `/clif` and `/disasm` would report "no CLIF / no disasm" for platform entries (they should never have been meaningful — the DLL's machine code is not our CLIF output). This is a correctness tightening; no behavioural regression.

**Confirmation**: platform entries appear in symbol-table introspection via the same code path as every other `ModuleEntry::Def`. No platform-specific introspection path exists.

### G9 — persistent priority workers

The platform DLL loader runs on whichever worker handles the `(platform …)` form — today via `handle_platform` inside `worker.rs`. Persistent workers don't change the semantics of DLL loading; what changes is the worker lifecycle. Key invariants to preserve:

1. **DLL leak is still process-lifetime.** `handle_platform` leaks the `LoadedLibrary` (per existing comment at `worker.rs:1491`). Persistent workers do not shorten this lifetime — the DLLs stay mapped until the process exits.

2. **Platform-fn-ptr writes must be visible to later workers.** Today `ctx.platform_registry.register(…)` mutates a `PlatformRegistry` field on the session. Post-G8, the write is `table.get_mut(&module).and_modify(|t| t.insert(symbol, entry_with_fn_ptr))` on the per-module `SymbolTable` in the session's `DashMap<ModuleFullPath, SymbolTable>`. DashMap entries are `RwLock`-guarded, so a write from one worker is observable by later symbol-table reads on any worker. No additional locking is needed for the platform path specifically.

3. **Race in principle, not in practice.** A theoretical race exists if worker A is loading platform P while worker B compiles a module that imports from `platform.P`. Today, the scheduler sequences platform loading before any compilation that depends on it (via the module-graph dependency edge on `ModuleEntry::PlatformDecl`). Persistent workers keep that sequencing; the scheduler still edges through the graph. No new race.

4. **No `thread::scope` interaction.** Platform loading doesn't spawn worker-scoped threads; `dlopen` is blocking on the calling thread. G9 removes `thread::scope` from the *worker pool* lifecycle, not from DLL loading.

**Confirmation requested of /int**: when `design/int/persistent-workers.md` lands, `/platform` reviews it for these three invariants. Expected: clean. If a platform-DLL-ordering regression shows up, flag via FIXME(/platform).

## 6. v4_platform test failures — triage

`tests/v4_pipeline.rs` contains five tests listed under "Platform Registry tests (Sprint 45 Step 8)":

| Test | Line | Assertion | Expected G8 effect |
|---|---|---|---|
| `v4_platform_stdio_print` | 751 | Clean stderr on `(platform stdio)` + `(print "…")` program. | **Flip to passing.** Current failure is likely one of two root causes: (a) the `collect_jit_setup` walker emits the `jit_name→fn_ptr` pair from the registry; after migration it reads `entry.platform_fn_ptr` directly. If either path has a stale/missing entry, the JIT linker fails with `unknown symbol: cranelisp_print` which shows on stderr. Moving the ptr onto the entry eliminates the two-store sync question — whoever walks the symbol table for JIT setup sees the ptr in the same place it reads every other entry field. (b) Cross-module resolution: `(import [platform.stdio [print]])` makes `main` module entry for `print` a `ModuleEntry::Import { source: platform.stdio/print }`. `collect_jit_setup` handles this case (worker.rs:2134) but the follow-through to the source table is an extra DashMap round-trip that the registry short-circuited by keying on FQSymbol directly. Either way, G8 reduces the surface where these two paths can disagree. |
| `v4_platform_io_trampoline` | 773 | stdout contains `"trampoline works"`. | **Flip to passing** iff `v4_platform_stdio_print` flips — the trampoline executes only if the JIT resolved `cranelisp_print` and the compiled `main` actually ran. |
| `v4_platform_import_and_use` | 797 | Clean stderr on explicit import from `platform.stdio`. | **Flip to passing** — same failure/fix path as A-1. |
| `v4_platform_empty_registry` | 819 | No-platform program exits 44 (300 mod 256). | **Already passing** or should be — this test has no `(platform …)` form. If it is in the 5 baseline failures, it points to a different defect. Hypothesis: the 5 may not all be platform-*semantic* failures; some may be shared-crate compilation failures triggered by residual stale `platform_symbols` field references. Worth verifying with `/int` which 5 v4_platform-named tests are in the 14-failure baseline. |
| `v4_platform_multiple_calls` | 835 | Clean stderr on two sequenced `print` calls. | **Flip to passing** — same root cause as A-1. |

**Out-of-G8 failures** (if any): `v4_platform_empty_registry` — if currently failing, the fix is not in G8's scope; the defect is elsewhere in the single-module compile path. File FIXME(/int) if it remains failing after G8 lands.

**Expected outcome**: four tests flip to passing under G8 (A-1, A-2, A-3, A-5). `v4_platform_empty_registry` (A-4) either was already passing or needs non-G8 investigation. `/platform` expects the 5 v4_platform failures in the baseline to be A-1, A-2, A-3, A-5, and one of: A-4, or a sixth test (e.g., `v4_platform_form` at line 560, which is structurally identical to A-1 and is likely also failing).

`/platform` asks `/qa` to record the precise five test names in `tests/plan/ring4.md` during Wave 1 so the G8 acceptance criterion is unambiguous.

## 7. Sketch Comparison

### How the sketch handles platform fn-ptr resolution

The sketch does **not** use a central registry. Platform fn ptrs are stored inside the JIT module itself via `JITBuilder::symbol_lookup_fn`:

```rust
// sketch/src/jit.rs:672-676
let dynamic_symbols = Arc::new(Mutex::new(HashMap::<String, SendPtr>::new()));
let syms = dynamic_symbols.clone();
builder.symbol_lookup_fn(Box::new(move |name| {
    syms.lock().unwrap().get(name).map(|sp| sp.0)
}));
```

Platform loading pushes entries into the `dynamic_symbols` map (via `Jit::load_platform` — not shown). Cranelift's linker, when it encounters an undeclared symbol name, calls the closure and gets a raw pointer back.

Scheduling class lives on the TypeChecker in `sketch/src/typechecker/primitives.rs`:

```rust
// sketch/src/typechecker/primitives.rs:977-979 (inside register_platform)
self.platform_scheduling
    .insert(desc.name.clone(), desc.scheduling_class);
```

(`platform_scheduling: HashMap<String, SchedulingClass>` on the `TypeChecker`.) Bind-chain analysis calls `tc.scheduling_of(name)` (lines 985-992) to read it.

**Two observations on the sketch**:

1. **Two stores, not one.** The sketch has exactly the pre-v4 split that the reimplementation's `PlatformRegistry` was introduced to consolidate. The JIT's `dynamic_symbols` holds `(jit_name, fn_ptr)` pairs; the TypeChecker's `platform_scheduling` holds `(name, SchedulingClass)` pairs. These are populated from the same manifest but stored separately.

2. **The sketch's `platform_scheduling` is a `HashMap<String, SchedulingClass>` keyed by bare name (not qualified).** Two platforms exporting the same name would collide. The reimplementation's pre-G8 `PlatformRegistry` addressed this with `FQSymbol` keys; G8 addresses it by making the scheduling class a field of the qualified `ModuleEntry::Def` itself.

### Reimplementation divergence

**The reimplementation diverges from the sketch**, by G8, in three ways:

1. **Consolidate fn_ptr + scheduling_class onto the symbol-table entry** (not onto separate session stores). The sketch has two stores; the reimplementation at Sprint 45 had one (`PlatformRegistry`); at Sprint 57 G8 has zero — both data items live on `ModuleEntry::Def` where they naturally belong.

2. **Use the symbol-table Import chain to resolve cross-module platform references**, rather than the sketch's bare-name lookup with no module awareness. This aligns platform functions with every other cross-module symbol — they are resolved uniformly.

3. **`fn_ptr` is resolved at finalize time via `JITBuilder::symbol()`** (not via `symbol_lookup_fn` closure). This matches `/arch` Decision 23 (Uniform codegen: JIT vs Object mode differs only in finalize-time symbol resolution): the JIT `Module` implementation is handed the list of `(jit_name, fn_ptr)` pairs at `finalize_definitions` time, via the list `collect_jit_setup` assembles from the symbol-table scan.

### Rationale for divergence

The sketch's approach encodes the dual-pipeline defect described in `design/arch/archive/pipeline-convergence-review.md`: scattered state across pipeline stages, lookup-by-string with no module awareness, and bidirectional-dependency shaped data flows. Every audit finding category (`audits/module.md`, `audits/typechecker.md`) calls out this kind of scatter as Principle 7 (single source of truth) violation.

G8 closes the divergence by putting both fields on the `ModuleEntry::Def` that typecheck already creates during `(platform …)` form processing. There is no second store to keep in sync. Bind-chain analysis and JIT symbol collection read from the same table via the same `get()`/Import-chain walk. `FQSymbol` keying is implicit — each module's `SymbolTable` already indexes by local `Symbol`, and the `ModuleFullPath` that contains it is the module qualifier.

## 8. Open Questions / /int Coordination

1. **`SymbolTable` helper for Import-chain walk**: /platform expects a helper like `resolve_chain(&self, name: &Symbol) -> Option<(FQSymbol, &ModuleEntry)>` that follows `ModuleEntry::Import` to the defining `ModuleEntry::Def`. If one doesn't already exist in `cranelisp-types`, /int's Wave 2 work should add it. /platform's bind-chain-analysis reader uses this.

2. **`platform_fn_ptr` vs `PrimitiveKind::PlatformEffect { fn_ptr }`**: /platform supports /arch's Decision 26 as written (sibling field, `#[serde(skip)]`). If /int proposes moving `fn_ptr` inside the variant for symmetry with `scheduling_class`, /platform is OK with it — the pattern-match cost is the same three lines as for `scheduling_class`, and the symmetry is mild but nice.

3. **Five-failing-test identification**: /qa to record which exact five `v4_platform` tests are in the 14-failure baseline. The tests in `tests/v4_pipeline.rs` that begin with `v4_platform_` total six (`v4_platform_form` at 560, plus A-1 through A-5). The 14-failure baseline may include `v4_platform_form` and A-1 through A-4, excluding A-5; or some other subset.

4. **Spec text check**: `spec/08-modules.md §8.9.3` is unchanged by G8 — the spec describes the `(platform …)` form's module-creation semantics, not the implementation detail of where fn_ptr lives. Confirmed no FIXME(/spec) needed.

## 9. Acceptance Checklist for G8 Close

- [ ] `src/platform_registry.rs` deleted (entire file).
- [ ] `PlatformFunction` struct removed from all sites.
- [ ] `ModuleEntry::Def` has `platform_fn_ptr: Option<*const u8>` field, `#[serde(skip)]`.
- [ ] `PrimitiveKind::PlatformEffect { scheduling_class: SchedulingClass }` is the shape.
- [ ] `handle_platform` in `src/worker.rs` writes both `platform_fn_ptr` and the `PrimitiveKind::PlatformEffect { scheduling_class }` onto the `ModuleEntry::Def` during symbol-table insert (not onto a side registry).
- [ ] `bind_chain_analysis.rs::classify_expr` reads `scheduling_class` via symbol-table Import-chain walk.
- [ ] `collect_jit_setup` reads `platform_fn_ptr` directly from the entry (no `fn_ptr_by_jit_name`).
- [ ] `cargo clippy -p cranelisp` clean (introduces no new warnings).
- [ ] 5 `v4_platform` tests flip to green (per §6 triage — four definite, one open).
- [ ] No regression on existing platform tests (stdio platform test suite).
- [ ] IO trampoline RC-leak fix (FIXME on `crates/cranelisp-runtime/src/io.rs:58`) coordinated with `/backend` in the same Wave per Sprint 57 §Architecture Review condition 6.

## Next skills

- `/int` — complete `design/int/platform-registry-removal.md` with the per-site migration plan; confirm /platform's §3 decision on `scheduling_class` placement and lock it into a minor update to Decision 26 if needed.
- `/arch` — review §3 and update Decision 26 to note that `scheduling_class` lives on `PrimitiveKind::PlatformEffect`, while `platform_fn_ptr` stays as the sibling `#[serde(skip)]` field (Option B for scheduling_class, sibling field for fn_ptr — /platform's recommendation).
- `/backend` — `run_io_trampoline` RC-leak fix lands in Wave 3 alongside G8 per Sprint 57 conditions.
- `/qa` — in Wave 1, record the exact five `v4_platform` tests in the 14-failure baseline so G8's acceptance is unambiguous.
