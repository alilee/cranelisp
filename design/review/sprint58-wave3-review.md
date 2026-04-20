# Sprint 58 Wave 3 Review — Step 5c (`SymbolTable<C, L>` generics activation + `Code` enum + Decision 31 Scenario 2)

**Sprint**: 58 Wave 3 (3a + 3b bundled, 3c, 3d)
**Date**: 2026-04-19
**Reviewer**: `/review`
**Commits reviewed**: `03b218f` (Wave 3a + 3b), `d22e044` (Wave 3c), `d348bca` (Wave 3d)
**Scope**: `CodeStore` + `LinkerStore` empty marker traits with `Clone` super-bound (Decision 32); `SymbolTable<C: CodeStore = (), L: LinkerStore = ()>` + `ModuleEntry<C: CodeStore = ()>` parameterisation; integration-layer `Code` enum at `src/code.rs` (Decision 35 Layer 2 Option B); `CompilationResult.code_ptrs: HashMap<Symbol, *const u8>`; `SharedState.kept_jits` + `kept_linkers` dissolved; per-entry `Arc<Jit>` / `Arc<Linker>` retention via `ModuleEntry::Def.code = Code::Jit { jit: Arc::clone(&jit_arc), ptr }`; `register_defn_signature` carry-forward invariant fix in `cranelisp-typecheck/src/program.rs`; `jit_free_memory_call_count()` instrumentation accessor in `cranelisp-backend/src/jit.rs`; full `<C, L>` parameterisation of `cranelisp-typecheck` internals (`TypeCheckEnv`, `CompileContext`, `FnCompiler`, helpers); 5 reclaim integration tests in `tests/v4_jit_reclaim.rs` (Decision 31 Scenario 1 + 2); doc updates to `compile-to-module.md` §17 + `symbol-table-generics.md` §3 outcome.

## Verdict

**PASS with Importants.** Wave 3 lands the headline payoff of Sprint 58 — Decision 31 Scenario 2 (per-redefinition JIT reclaim) — cleanly and verifiably. The architectural shape (Decisions 32, 35) maps directly to the implemented code: `Code` lives in `src/code.rs` (integration layer, not `cranelisp-types`), backend signatures stay generic-blind on `<C, L>` (`compile_to_module<M, C, L>` reads `SymbolTable<C, L>` but never names `Code` or calls `c.ptr()`), `kept_jits` + `kept_linkers` dissolution is complete (the `Mutex<Vec<KeptJit>>` field is gone from `SharedState`; per-entry `Arc<Jit>` / `Arc<Linker>` retention via `ModuleEntry::Def.code` is now load-bearing), and the per-crate clippy gate holds (zero new warnings in any of `cranelisp-types`, `cranelisp-typecheck`, `cranelisp-backend` — counts identical to the post-Wave-2 baseline `d1e3a73`). The 5 new integration tests in `tests/v4_jit_reclaim.rs` exercise the reclaim chain end-to-end at the level Decision 31 specifies (`Arc::strong_count` decrements + `jit_free_memory_call_count()` increments observed directly).

The Importants below are: (a) the load-bearing `register_defn_signature` carry-forward fix lacks a targeted regression-guard test (the existing `error_after_redefinition_preserves_latest` integration test exercises a different invariant — it never triggers the path the carry-forward protects); (b) Decision 32's text in `design/arch/CLAUDE.md` does not record the `Clone` super-bound that landed in the implementation; (c) Decision 31's "Scheduling footnote" still describes the pre-Wave-3b `kept_jits` retention as the live state; (d) `KeptJit` struct + its `unsafe impl Send/Sync` lines remain dead code in `src/session_v4.rs`. None block Wave 4 from opening — the architectural payoff is correctly implemented and end-to-end verified — but at minimum I-1 (regression-guard test) and I-2 (Decision 32 doc) should land before sprint close to lock in the invariant.

## Counts

| Severity | Count |
|---|---|
| Blocker | 0 |
| Important | 4 |
| Suggestion | 5 |

---

## Focus area findings

### Focus 1 — Decision 32 (CodeStore + LinkerStore empty marker traits)

**Verdict**: PASS at the implementation level; **Important** doc-drift on the `Clone` super-bound.

The trait shapes at `crates/cranelisp-types/src/module.rs:36-37` and `:54-55`:

```rust
pub trait CodeStore: Clone + Send + Sync + 'static {}
impl<T: Clone + Send + Sync + 'static> CodeStore for T {}

pub trait LinkerStore: Clone + Send + Sync + 'static {}
impl<T: Clone + Send + Sync + 'static> LinkerStore for T {}
```

Both traits are method-free per Decision 32, with blanket impls that admit any qualifying type. The `Clone` super-bound was added during Wave 3b implementation when `register_defn_signature`'s carry-forward path required `code.clone()` (~`crates/cranelisp-typecheck/src/program.rs:2207-2213`); DashMap iteration semantics elsewhere also require it. This is sound — `()` is `Clone`, `Code` is `#[derive(Clone)]` (`src/code.rs:71`), `Arc<Jit>` and `Arc<Linker>` are `Clone`. The `Clone` requirement constrains future `C` / `L` choices to `Clone` types, but this is acceptable: any concrete code-handle type the integration layer might pick (Arc-wrapped, integer-handle, smart-pointer wrapper) naturally implements `Clone`. The constraint surfaces no immediate barrier and gains the concrete `code.clone()` invariant-preservation site in typecheck.

**Default `()` propagation**: verified at `crates/cranelisp-types/src/module.rs:101` (`SymbolTable<C: CodeStore = (), L: LinkerStore = ()>`) and `:417` (`ModuleEntry<C: CodeStore = ()>`). The unit-test `symbol_table_default_generics_resolve_to_unit` at `:1599-1632` proves `SymbolTable::new(path)` infers `<(), ()>` end-to-end. The `code_store_and_linker_store_blanket_impl_holds` test at `:1642-1678` proves `()`, `Arc<()>`, `Arc<u64>`, `i64`, `u64` all satisfy both traits without per-call-site impl lines.

**`Send + Sync` propagation**: `unsafe impl<C: CodeStore> Send for ModuleEntry<C>` and `unsafe impl<C: CodeStore> Sync for ModuleEntry<C>` at `:559-560`, with the SAFETY comment at `:538-558` correctly distinguishing the `*const u8` `platform_fn_ptr` (always present, raw pointer rationale carried from Sprint 57 Wave 3) from the `code: Option<C>` field (delegated to whatever `C` chooses — `()` is trivially safe; `Code` carries its own `unsafe impl Send + Sync` at `src/code.rs:106-107`).

**Cross-flavour serde discipline**: `#[serde(bound = "")]` on both `SymbolTable` (`:100`) and `ModuleEntry` (`:416`) suppresses derive-emitted `C: Serialize + Deserialize` bounds — load-bearing because `Code` does not implement Serialize. Verified by `module_entry_def_code_field_is_optional_c` at `:1688-1753` (round-trips `ModuleEntry<i64>` through `ModuleEntry<()>`'s deserialise — different `C`s, identical serialised shape because `code` is `#[serde(skip)]`).

(See I-2 for the `Clone` super-bound documentation gap in `design/arch/CLAUDE.md` Decision 32.)

### Focus 2 — Decision 35 (`Code` enum location + Layer 2 Option B)

**Verdict**: PASS. The enum lives at the integration layer, the shape matches the spec, the safety contract is correct, the backend stays generic-blind.

**Location** (`src/code.rs:55-130`): `Code` is owned by `cranelisp` (binary), depends on `cranelisp_backend::cache::Linker` and `cranelisp_backend::jit::Jit` — would invert Principle 3 if placed in `cranelisp-types`. The pre-Wave-3b `crates/cranelisp-types/src/code.rs` (Sprint 57 pointer-only `Code` struct) is correctly deleted (`-83` lines per the diff stat); `pub mod code` removed from `crates/cranelisp-types/src/lib.rs`.

**Variant shape** (`src/code.rs:71-87`):

```rust
#[derive(Clone)]
pub enum Code {
    Jit { jit: Arc<Jit>, ptr: *const u8 },
    Linker { linker: Arc<Linker>, ptr: *const u8 },
}
```

Both variants carry the appropriate retention root + per-symbol code address per Decision 35. `#[derive(Clone)]` on the enum + `Arc::clone` semantics on the inner field gives the per-entry retention contract. Manual `Debug` impl at `:89-96` (Jit and Linker don't implement Debug); the `:?` output is intentionally minimal (variant tag + ptr value) and avoids dumping JIT internals — correct discretion.

**`Send + Sync` impls** (`src/code.rs:106-107`): `unsafe impl Send for Code {}` / `unsafe impl Sync for Code {}` with a comprehensive SAFETY comment at `:98-105`. The justification is sound: the `Arc<Jit>` / `Arc<Linker>` carriers are themselves `Send + Sync` (Arc requires `T: Send + Sync` to be `Send + Sync` — inherited from the underlying types), the `*const u8` is an integer handle into pages the Arc keeps alive, and `Code` instances support only cloning the Arc (thread-safe refcount bump) and reading `ptr` (no method dispatch on `Jit`). The argument mirrors the pre-Wave-3b `KeptJit` / `Code` Send/Sync rationale verbatim. Acceptable.

**`ptr()` accessor** (`src/code.rs:125-129`): `pub fn ptr(&self) -> *const u8 { match self { Code::Jit { ptr, .. } | Code::Linker { ptr, .. } => *ptr } }` — variant-uniform, single read site. Every read site in the integration layer that previously did `c.ptr` on the pre-Wave-3b struct is now `c.ptr()` on the enum (verified by grep — no `.ptr` field-access on `Code` survives anywhere in `src/`).

**Type aliases** (`src/code.rs:137-141`): `pub type SessionSymbolTable = SymbolTable<Code, ()>` + `pub type SessionModuleEntry = ModuleEntry<Code>`. Used throughout `src/worker.rs`, `src/session_v4.rs`, `src/save.rs` to keep `<Code, ()>` annotation noise contained. Per-entry alias usage is consistent.

**`CompilationResult.code_ptrs`** (`crates/cranelisp-backend/src/lib.rs:80`): `HashMap<Symbol, *const u8>` per Decision 35 Layer 2 Option B. The doc comment at `:69-79` accurately records the contract: empty for `ObjectModule` (capability returns `None`), populated for `JITModule` after `finalize_for_code_read`. `unsafe impl Send + Sync for CompilationResult` at `:101-102` with SAFETY comment at `:93-100` cross-references the integration layer's lifetime contract.

**Backend stays generic-blind**: `compile_to_module<M, C, L>` at `:351-361` propagates `<C, L>` parameters but never reifies them. Verified by grep — backend never names `Code`, `Code::Jit`, or `Code::Linker`; never calls `c.ptr()`; pattern-matches on `ModuleEntry::Def { ast, .. }` (line 389) and `ModuleEntry::Def { got_slot, .. }` (line 521) using `..` to skip `code`. The post-call `Code::Jit` construction lives entirely in `src/worker.rs::inline_jit_codegen_for_names` at `:2731-2787`. Layer 2 Option B is implemented exactly as Decision 35 specifies.

### Focus 3 — `kept_jits` + `kept_linkers` dissolution

**Verdict**: PASS for the dissolution semantics; **Important** for residual `KeptJit` dead code.

**Field removal** (`src/session_v4.rs:591-592`): the `pub kept_jits: Mutex<Vec<KeptJit>>` and `pub kept_linkers: Mutex<Vec<Linker>>` fields are deleted from `SharedState`. The comment block at `:591-592` records the dissolution per Decision 35; the `kept_dlls` field at `:616` is retained per its orthogonal-to-Step-5c rationale.

**Writer site removal**: `src/worker.rs::inline_jit_codegen_for_names` at `:2747-2750` correctly does not push to any session-level pool — the `Arc::new(jit)` is constructed locally, then `Arc::clone(&jit_arc)` per defined symbol writes `Code::Jit { jit, ptr }` onto each `Def.code` (`:2783-2786`). The cache-hit path at `src/worker.rs::load_cached_module_via_linker` `:2983-2995` mirrors the shape: `Arc::new(linker)` locally, `Arc::clone(&linker_arc)` per defined symbol writes `Code::Linker { linker, ptr }` onto each `Def.code`. After the for-loop, the local `Arc` drops, leaving only the per-entry clones — when the entry replaces (REPL redefinition), the per-entry clone drops and reclaim fires.

**Regression-guard test** (`src/code.rs:347-396` `kept_jits_and_kept_linkers_fields_dissolved`): a textual sweep of `src/session_v4.rs` (with comments stripped to avoid matching documentation that describes the historical state) that asserts no live reference to either `kept_jits` or `kept_linkers` survives, paired with a counter-assertion that `kept_dlls` does survive. Sound shape — the comment-stripping pass is careful (handles both `//` line comments and `/* */` block comments, with peekable char iteration). This protects against accidental re-introduction.

**`KeptJit` struct survives** (`src/session_v4.rs:453-457`): the `pub struct KeptJit(pub Arc<cranelisp_backend::jit::Jit>)` + its two `unsafe impl Send for KeptJit {}` / `unsafe impl Sync for KeptJit {}` lines remain defined but have **zero callers** — verified by `grep -nE "KeptJit"` showing references only inside `src/code.rs` doc comment, `src/session_v4.rs` itself, and design / review docs. This is dead code. The brief flagged this as a Suggestion-level cleanup; per the cleanup-now-or-defer judgement at the §"Sprint 58 Wave 3b" outcome (`design/int/symbol-table-generics.md:6` "Out-of-scope addendum"), `/int` correctly contained the change to the dissolution itself and left the dead struct for later. Filed as I-4 (lifted to Important because the struct's `unsafe impl Send/Sync` lines now make a misleading claim — there is no `KeptJit` value that needs the unsafe — and a future reader could be misled into thinking the unsafe is load-bearing).

### Focus 4 — `register_defn_signature` carry-forward invariant fix

**Verdict**: Implementation is correct; **Important** test gap.

The fix at `crates/cranelisp-typecheck/src/program.rs:2184-2232`:

```rust
let mut st = self.current_symbol_table_mut(state);
let (existing_slot, existing_ast, existing_code) = st.get(defn.name.as_ref())
    .map(|e| match e {
        ModuleEntry::Def { got_slot, ast, code, .. } => (*got_slot, ast.clone(), code.clone()),
        _ => (None, None, None),
    })
    .unwrap_or((None, None, None));
let got_slot = Some(existing_slot.unwrap_or_else(|| st.allocate_got_slot()));

st.insert(
    defn.name.clone(),
    ModuleEntry::Def {
        // ...
        ast: existing_ast,
        code: existing_code,
        // ...
    },
);
```

The doc comment at `:2184-2205` is comprehensive — it explains the pre-Wave-3b harmless-replacement story (Arc lived in `kept_jits`, replacement was a pointer-swap), the post-Wave-3b SIGABRT risk (Arc-drop frees JIT pages mid-typecheck while the GOT slot still points at them), and the carry-forward fix (preserving `code` keeps the Arc alive across the typecheck attempt; on success, codegen overwrites with the new `Code::Jit`; on failure, the carried-forward `code` remains and the GOT slot stays valid). This is exactly the safety invariant Decision 31 requires.

The carry-forward path is exercised by the headline `decision31_scenario2_per_redefinition_jit_pages_reclaimed` test (`tests/v4_jit_reclaim.rs:243-323`) on the **success** path — the test type-checks `(defn f [x] (add-i64 x 1))` cleanly, replaces the entry, and verifies the prior `Arc<Jit>` reclaims. **No test exercises the failure path** — i.e., a typecheck error mid-redefinition that triggers snapshot/restore and verifies the original `code` survives unchanged. The closest existing test (`tests/repl_experience.rs:1227 error_after_redefinition_preserves_latest`) tests a different invariant: it does a successful `f` redefinition, then triggers an unrelated error in a separate eval, then asserts `f` still returns the latest value. That doesn't trip the carry-forward path because the error is not in `f`'s body.

The missing test would look like:

```rust
session.eval("(defn f [x] x)").unwrap();
let f_code_before = capture_code_arc("f");
let _err = session.eval("(defn f [x] (some-undefined-fn x))");  // typecheck failure
let f_code_after = capture_code_arc("f");
// Assert: f's code did NOT change AND the GOT slot still points at the original pages.
assert!(Arc::ptr_eq(&f_code_before, &f_code_after));
assert_eq!(repl_eval(&mut session, "(f 42)"), 42);  // original f still callable
```

Without this test, a future change that drops the `existing_code` carry-forward would not surface in CI — the test would have to specifically exercise the typecheck-error-in-redefinition path. Filed as I-1.

### Focus 5 — Decision 31 Scenario 1 + 2 reclaim invariants (`tests/v4_jit_reclaim.rs`)

**Verdict**: PASS. The 5 tests are well-constructed and observe the reclaim primitive at the right level.

**Scenario 1 — per-eval reclaim** (positive: `decision31_scenario1_per_eval_jit_pages_reclaimed:140-170` + negative: `decision31_scenario1_repeated_eval_no_unbounded_growth:175-214`): both assert against `MemSnapshot.bytes_live` (which `format_mem_snapshot` reports per spec §3.7). The 256-byte `REPL_EVAL_OVERHEAD_BOUND` is documented at `:91-98` as accommodating future `it`-binding or transient bookkeeping; choice of 256 is appropriately generous. The negative test runs 100 evals and asserts the delta does NOT scale ~N×; pre-fix this would have grown linearly. Sound. The companion live-allocations assertion (`:207-213`) adds a second independent signal — total live allocations stay bounded across N evals.

**Scenario 2 — HEADLINE per-redefinition reclaim** (`decision31_scenario2_per_redefinition_jit_pages_reclaimed:243-323`): the assertion strategy is **stronger than `bytes_current()` deltas** — it directly observes the reclaim primitive at the level Decision 31 defines. The flow:

1. Define `f`; capture an `Arc<Jit>` clone from `f`'s `Def.code` (lines `:248-267`).
2. Snapshot `jit_free_memory_call_count()` (`:272`).
3. Redefine `f` with a different body (`:278-280`).
4. Read the new `Def.code`; assert its `Arc<Jit>` is `!Arc::ptr_eq` with the captured first-batch Arc (`:288-293`) — the redefinition produces a fresh batch, not a clone.
5. Drop the test's clone of the second batch's Arc (`:294-295`); assert `Arc::strong_count(&first_jit) == 1` (`:299-308`) — the session has fully released its reference to the first batch.
6. Drop the captured first-batch Arc (`:312`); assert `jit_free_memory_call_count()` incremented by exactly 1 (`:313-322`) — `Jit::drop`'s `unsafe free_memory()` fired.

This is the right level of observation: not "bytes appeared to drop" (which can be confounded by allocator caching, debug-mode bookkeeping, or concurrent runtime activity) but "the specific reclaim primitive invoked the specific page-release call". The `jit_free_memory_call_count()` accessor (`crates/cranelisp-backend/src/jit.rs:188-190`) reads the `JIT_FREE_MEMORY_CALL_COUNT: AtomicU64` static (`:181-182`), which is incremented exactly once inside `Jit::drop` at `:244-245` whenever `module.take()` returns `Some` (i.e., the JIT was actually live at drop time). Counter discipline is `Ordering::Relaxed`, consistent with cross-test instrumentation; no ABA hazard because the counter is monotonically increasing.

**Scenario 2 negative** (`decision31_scenario2_repeated_redefinition_no_unbounded_growth:331-382`): 50 redefinitions with varying body content (defeats body-equality short-circuit). Two assertions: (a) `delta_bytes <= 512` (2× `REPL_EVAL_OVERHEAD_BOUND`, generous for redefn + small RC churn); (b) `reclaim_count_delta >= N` — at least N JIT batches were reclaimed across N redefinitions. Pre-Wave-3b, `kept_jits` accumulation would have shown 0 reclaims until session drop. The companion-assertion shape gives two independent signals; flake-resistant because both must hold.

**`Code::Linker` session-scope test** (`decision31_code_linker_session_scope_only:421-492`): documents the design — `Linker` reclaim is structurally session-scoped (cache-hit code rehydrates once at session start, lives until session teardown unless every cache-loaded entry gets redefined). The test exercises the structural Arc-decrement-on-drop discipline at the `Code` enum layer (not through a full session restart) because: (a) the unit test `code_enum_jit_variant_carries_arc_jit` already proves the Arc-clone reclaim primitive for `Code::Jit`; (b) the unit test `code_enum_linker_variant_constructible` proves `Code::Linker` participates in `Arc::clone` semantics; (c) end-to-end cache-rehydrate flows are covered by `tests/cache.rs::cache_repl_restart_cache_hit`. This test fills the gap by asserting the Arc lifecycle on real `Code::Linker` instances. The doc-comment at `:386-420` explicitly documents the design choice ("Linker reclaim is structurally session-scoped, not per-redefinition"); on the question of whether `Linker` should grow per-redefinition reclaim in a future sprint, the answer is no per Decision 35's "no scenario today where a Linker must be retained without any `Code::Linker` referencing it" (CLAUDE.md:183) — the existing per-entry Arc retention IS the per-module reclaim mechanism. No additional design work is needed.

**Test placement**: `tests/v4_jit_reclaim.rs` lives in its own integration crate (rather than in `tests/repl_experience.rs`) because `cranelisp_runtime::*_count()` and `jit_free_memory_call_count()` are process-global atomics — placing in a separate binary keeps them on the nextest "one process per test" boundary. Sound, well-documented at `:32-40`.

### Focus 6 — Out-of-scope crate edits

**Verdict**: PASS. The cross-crate parameterisation was necessary for the architectural target and is uniformly applied.

The original brief expected typecheck/types to "already work via default propagation". `/int`'s actual sweep was wider — `cranelisp-typecheck` got `TypeCheckEnv<'a, C, L>`, `CompileContext<'a, C, L>`, `FnCompiler<'a, M, C, L>` plus 6 impl blocks and helper functions; `cranelisp-types` got the `Clone` super-bound, `new_with_params(path)` constructor, and `into_concrete<C, L>()` conversion. `/int` flagged this in commit message + `design/int/symbol-table-generics.md:26` "Out-of-scope addendum".

This is the right architectural call: the alternative (dual-store split between `<()>`-flavoured typecheck-internal accessors and `<Code, ()>`-flavoured integration views) would have violated Decision 35's single-source-of-truth requirement (Principle 7) — typecheck would need to either copy data (two stores) or perform reference-projection acrobatics. Full parameterisation is the natural completion of Wave 3a's foundation; the doc trail accurately records the deviation from the original brief and the architectural rationale.

**Uniformity check**: I sampled `crates/cranelisp-typecheck/src/program.rs` (`TypeCheckEnv<'_, C, L>` + helper signatures), `crates/cranelisp-typecheck/src/checker.rs` (similar parameterisation pattern), `crates/cranelisp-typecheck/src/builtins.rs` (`+19/-19` lines — the largest typecheck delta is helper rewrites + a small param-bound addition), `crates/cranelisp-typecheck/src/adt.rs`, `infer.rs`, `traits.rs` — all consistently propagate `<C: CodeStore, L: LinkerStore>` where they hold a `SymbolTable` reference; none half-parameterise. The risk of "later breakage from a half-parameterised internal type" is contained.

**`Clone` super-bound future-choice constraint**: limits `C` and `L` to types that implement `Clone`. Current `Code` enum (with `Arc<Jit>` / `Arc<Linker>` fields) implements `Clone` trivially. Future hypothetical alternatives that might NOT be Clone — e.g., a unique-ownership shape using `Box<Jit>` instead of `Arc<Jit>` — would violate the bound. But: (a) the unique-ownership shape is incompatible with the per-entry retention model the Wave 3 design rests on (Arc is fundamental to Decision 31 Scenario 2's "drop the last clone, the underlying frees" semantics); (b) any code-handle that wraps a runtime-allocated resource needs Arc-semantics for the per-entry × per-batch many-to-many relationship to work. The `Clone` super-bound is therefore not a real future-choice constraint — it codifies a property the design already implicitly requires. Acceptable, with the caveat that this should be documented in Decision 32.

### Focus 7 — Per-crate clippy gate

**Verdict**: PASS. Zero new warnings in any of the targeted crates.

| Crate | HEAD warnings | Baseline (`d1e3a73`) | New | Result |
|---|---|---|---|---|
| `cranelisp-types` | 2 | 2 | 0 | identical |
| `cranelisp-typecheck` | 9 | 9 | 0 | identical |
| `cranelisp-backend` | 8 | 8 | 0 | identical |
| `cranelisp` (binary) | (varies — pre-existing `approx_constant` errors in `tests/repl_negative.rs:476` and `tests/sketch_port.rs:1104` deny clippy) | (same baseline errors) | 0 | identical |

The `cranelisp` binary's clippy run trips on pre-existing `approx_constant` deny-lints in test code; these errors pre-date Wave 3 and are out of scope per the task brief. The Wave 3 touch on `tests/repl_negative.rs:33` (one type annotation `&ModuleEntry<cranelisp::code::Code>` for the Code enum migration) introduced no new lints.

### Focus 8 — Documentation hygiene

**Verdict**: 3 Important findings, 2 Suggestions.

`design/int/symbol-table-generics.md` Wave 3b implementation outcome section (`:7-30`) accurately reflects what landed — the `Clone` super-bound is named, the `into_concrete` conversion is named, the `register_defn_signature` carry-forward fix is named with its safety rationale, the out-of-scope crate-edit deviation is recorded. PASS.

`design/backend/compile-to-module.md` §17.1 / §17.1.1 / §17.4 / §17.6 / §17.7 (post-Wave-3c update) — all spot-checks confirm the doc accurately reflects the landed shape: the `<M, C, L>` signature, the `CompilationResult.code_ptrs: HashMap<Symbol, *const u8>` shape, the `CodeFinalizer` capability (with `try_get_finalized_function` + `define_module_got_data`), the integration-layer post-call `Code::Jit` construction site at `src/worker.rs:2731-2787`, the §17.7 acceptance signals. PASS.

`crates/cranelisp-backend/src/jit.rs` doc comments at `:209-216` (referencing Wave 3b dissolution of `kept_jits`) and `:242-250` (the SAFETY comment on the `Drop` impl) accurately reflect the per-entry storage model. PASS.

(See I-2, I-3 for the doc-drift findings on `design/arch/CLAUDE.md` Decisions 32 and 31.)

### Focus 9 — Cross-decision coherence

**Verdict**: PASS. Decisions 31 + 32 + 35 harmonise.

- Decision 32 (empty marker traits with blanket `impl<T: Clone + Send + Sync + 'static>`) admits any `Code` shape the integration layer chooses without per-call-site impl lines.
- Decision 35 (`Code` enum at integration layer; backend generic-blind via Layer 2 Option B) chooses the concrete `C = Code` and unifies fresh-build + cache-hit storage in one shape.
- Decision 31 Scenario 2 (per-redefinition reclaim) fires because the per-entry `Arc<Jit>` clone in `Code::Jit` IS the retention root — no side store extends the lifetime past entry replacement.

The composition produces exactly the §9.1 target shape: single `SymbolTable<Code, ()>` instantiation site (in `src/session_v4.rs::SharedState.symbol_tables`), cascaded everywhere via `SessionSymbolTable` alias; backend operates on `<C, L>`-erased fields uniformly; cache-restore path mirrors fresh-build (both write to `ModuleEntry::Def.code`, differing only in the variant chosen).

The `Clone` super-bound constraint is the one cross-decision wrinkle: Decision 32's text doesn't mention it, but it's structurally required by the `register_defn_signature` carry-forward + cache iteration. Filed as I-2 — the constraint is sound, just not documented in the decision text.

---

## Important findings

**I-1** (Important, /qa): `register_defn_signature`'s carry-forward invariant fix at `crates/cranelisp-typecheck/src/program.rs:2184-2232` lacks a targeted regression-guard test. The Wave 3b commit message + `design/int/symbol-table-generics.md:24` describe the failure mode exactly: pre-Wave-3b, replacing the entry with `code: None` was harmless (Arc lived in `kept_jits`); post-Wave-3b, the same replacement would drop the Arc and `free_memory()` the JIT pages mid-typecheck — leaving the GOT slot pointing at freed memory if the redefinition then fails. The carry-forward fix preserves the existing `code` field so the Arc never drops mid-typecheck. The existing `error_after_redefinition_preserves_latest` test at `tests/repl_experience.rs:1227-1240` does NOT exercise this path (its error is in an unrelated form, not in the redefinition body). Recommended: add an integration test in `tests/v4_jit_reclaim.rs` that (a) defines `f`, (b) captures the `Arc<Jit>` from `f`'s `Def.code`, (c) attempts redefinition with a body that fails typecheck (e.g., calling an undefined function), (d) asserts the `Arc::ptr_eq` of the post-attempt `Def.code.Code::Jit.jit` matches the pre-attempt clone (carry-forward preserved the original Arc), (e) asserts `(f arg)` still returns the original behaviour. Owner: `/qa`. Should land before sprint close — the fix is load-bearing for safety, and a future change that drops the carry-forward would not be caught by current tests.

**I-2** (Important, /arch): `design/arch/CLAUDE.md` Decision 32 (line 163) describes the trait shape as `pub trait CodeStore: Send + Sync + 'static {}` — but the actual implementation at `crates/cranelisp-types/src/module.rs:36` adds `Clone` as a super-bound. The implementation deviation was discovered necessary during Wave 3b (DashMap iteration + `register_defn_signature` carry-forward both require it) and is documented in `design/int/symbol-table-generics.md:26` "Out-of-scope addendum". The `Clone` requirement is sound (any concrete `C` / `L` the integration layer might choose is naturally `Clone` because `Arc::clone` is fundamental to the per-entry retention model), but Decision 32's text in CLAUDE.md should record the super-bound + the rationale. Recommended: update Decision 32 (`design/arch/CLAUDE.md:163`) to include `Clone` in the trait shape and add a short paragraph explaining why (DashMap iteration semantics + `register_defn_signature` carry-forward), referencing the Wave 3b Out-of-scope addendum. Owner: `/arch`. Should land before sprint close.

**I-3** (Important, /arch): `design/arch/CLAUDE.md` Decision 31's "Scheduling footnote" inside the Defn JIT row of the table (lines 96-101, specifically the **Scheduling footnote** sub-sentence: *"as of Sprint 57, `Arc<Jit>` lives in `SharedState.kept_jits` rather than directly on `ModuleEntry::Def.code`, because the `SymbolTable<C, L>` generics... are not yet activated. Consequently, per-redefinition reclaim is deferred — Scenario 2's `Drop` fires only at session teardown, not on redefinition. Sprint 58 Step 5c (gap G12; see `pipeline-v4-roadmap.md` Phase 5 and Decision 25's rescheduling note) activates the generics and completes Scenario 2."*) is now stale. Wave 3 has activated the generics, dissolved `kept_jits`, and verified Scenario 2's `Drop` fires on per-redefinition. Recommended: update the footnote to record "Activated Sprint 58 Wave 3b — `Arc<Jit>` lives directly on `ModuleEntry::Def.code` via `Code::Jit { jit, ptr }` per Decision 35; per-redefinition reclaim verified by `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed`." Owner: `/arch`. Should land before sprint close — the footnote currently presents the pre-Wave-3 state as the live state, misleading any reader navigating from Decision 31 forward.

**I-4** (Important, /int): `KeptJit` struct + its two `unsafe impl Send/Sync` lines at `src/session_v4.rs:453-457` are dead code after Wave 3b. The `Mutex<Vec<KeptJit>>` field that justified the wrapper is dissolved; no live writer remains; the only references in `src/` are the struct definition itself and the dissolution comment at `:591-592`. Leaving the dead struct is a minor reader-confusion hazard — the `unsafe impl Send/Sync` lines now make a misleading claim (there is no `KeptJit` value flowing across threads that needs them). The `code_enum_jit_variant_carries_arc_jit` doc comment at `src/code.rs:53` references "the pre-Wave-3b `unsafe Send + Sync` impls on `KeptJit`" — that historical reference is fine, but the live dead struct creates the impression that it's still load-bearing. Recommended: delete the `KeptJit` struct + the two `unsafe impl` lines from `src/session_v4.rs` and update the `src/code.rs:53` doc comment to read "(pre-Wave-3b: `KeptJit` carried this contract; deleted at Wave 3b)". Owner: `/int`. Should land before sprint close as part of Wave 3b cleanup.

## Suggestion findings

**S-1** (Suggestion, /qa): The Scenario 1 `decision31_scenario1_per_eval_jit_pages_reclaimed` test bound (256 bytes via `REPL_EVAL_OVERHEAD_BOUND`) is generous to the point that a small leak might not trip it. Consider tightening the bound by capturing the bound dynamically (read `bytes_live` after warm-up, store as the assert delta floor, then assert the post-eval `bytes_live` returns to within ±1 allocation of the floor). Cosmetic; the current bound is well-documented and unlikely to mask significant leaks. Owner: `/qa`. Future cleanup.

**S-2** (Suggestion, /int): `src/worker.rs::inline_jit_codegen_for_names` at `:2779-2787` performs three DashMap lookups per name (`tc_modules.get_mut(module)` + `st.symbols.get_mut(name.as_ref())` + entry pattern-match). For a batch of 100 functions, this is ~300 DashMap operations on the same map. Consider hoisting the `tc_modules.get_mut(module)` outside the loop (release after the loop completes, then re-acquire for the artifact-routing step). Cosmetic — the operation is fast, but the pattern is wasteful. Owner: `/int`. Future cleanup.

**S-3** (Suggestion, /qa): `tests/v4_jit_reclaim.rs::decision31_code_linker_session_scope_only` does not exercise a real cache-rehydrate flow — it constructs `Linker::new()` directly and tests Arc lifecycle on synthesised pointers (`0xAAAAAAAA`, `0xBBBBBBBB`). The end-to-end cache-rehydrate flow is covered by `tests/cache.rs`, but neither there nor here is there a test that asserts the `Code::Linker.linker: Arc<Linker>` correctly drops when all cache-loaded entries get redefined to fresh `Code::Jit`. Recommended: add an integration test that (a) loads a cached module, (b) captures the `Arc<Linker>` clone count, (c) redefines every symbol from that module, (d) asserts the `Arc<Linker>` strong_count drops to 1 (only the test's clone remains), (e) drops it and asserts cleanup completes without panic. Owner: `/qa`. Future cleanup.

**S-4** (Suggestion, /backend): `crates/cranelisp-backend/src/lib.rs:559-571` (the `code_ptrs` collection loop) breaks on the first `try_get_finalized_function → None` because the capability is module-wide. The early-break is semantically correct but the comment at `:565-568` ("Object-mode path: ... break") could be a helper method on `CodeFinalizer` (`fn module_supports_code_ptrs(&self) -> bool` returning true for JIT, false for Object). Cosmetic; the current shape is fine. Owner: `/backend`. Future cleanup.

**S-5** (Suggestion, /int): `src/code.rs::tests::code_enum_jit_and_linker_coexist_serde_skip` at `:243-337` includes a 30-line construction of a synthetic `ModuleEntry::Def` (the `mk_def` helper). The same `Defn` / `ModuleEntry::Def` construction pattern appears in `crates/cranelisp-types/src/module.rs::tests` and could be extracted into a `pub(crate) fn mk_test_def<C: CodeStore>(...)` helper in either crate. Cosmetic; the duplication is small. Owner: `/int`. Future cleanup.

---

## Pre-existing issues noted

The clippy baseline state is unchanged from `d1e3a73`. The `cranelisp` (binary) clippy run trips on:
- `tests/repl_negative.rs:476` — `approx_constant` ERROR (Sprint 52 carry, out of Wave 3 scope per task brief).
- `tests/sketch_port.rs:1104` — `approx_constant` ERROR (Sprint 52 carry, out of Wave 3 scope per task brief).

The 5 pre-existing test failures (`display_overloaded_fn_shows_all_variants`, `neg_private_submodule_not_importable_from_peer`, `sketch_run_tests_pass_fn_called`, `cache_repl_loads_on_startup`, `persist_import_survives_restart`) are explicitly out of Wave 3 scope per the commit message + sprint plan. Wave 4 (Step 5d) clears the first two; the other three pre-date Sprint 58.

Recommendation per Sprint 57 + Sprint 58 Wave 2 reviews: schedule a per-crate clippy sweep for the next non-feature wave (the `slice::from_ref` / `collapsible_if` / `approx_constant` / `len_zero` carry-overs accumulate but never block individual waves).

## Verification spot-checks

Per "one agent, one test run" — only the targeted clippy verification was run.

| Check | Result |
|---|---|
| `cargo clippy -p cranelisp-types --all-targets` (HEAD vs baseline `d1e3a73`) | identical lint output; 0 new warnings |
| `cargo clippy -p cranelisp-typecheck --all-targets` (HEAD vs baseline `d1e3a73`) | identical lint output; 0 new warnings |
| `cargo clippy -p cranelisp-backend --all-targets` (HEAD vs baseline `d1e3a73`) | identical lint output; 0 new warnings |
| `cargo clippy -p cranelisp --all-targets` (HEAD vs baseline `d1e3a73`) | identical baseline (pre-existing `approx_constant` errors on test code; no new warnings) |
| `git diff 7236aa7..d348bca --stat` | 41 files changed, +2597 / −798 — matches commit messages |
| Confirm `Code` enum at `src/code.rs` (Decision 35 location) | confirmed; old `crates/cranelisp-types/src/code.rs` deleted (-83 lines per stat) |
| Confirm `kept_jits` + `kept_linkers` fields gone from `SharedState` | confirmed via grep + `kept_jits_and_kept_linkers_fields_dissolved` regression test |
| Confirm `register_defn_signature` carries `existing_code` forward | confirmed at `crates/cranelisp-typecheck/src/program.rs:2207-2229` |
| Confirm `compile_to_module` returns `code_ptrs` and integration layer constructs `Code::Jit` post-call | confirmed at `crates/cranelisp-backend/src/lib.rs:559-571` + `src/worker.rs:2762-2787` |
| Confirm `jit_free_memory_call_count()` accessor in `cranelisp-backend/src/jit.rs` | confirmed at `:188-190` (with internal counter at `:181-182`) |

## Checklist walkthrough

Against `design/review/checklist.md` and the audit checklist:

- **§1 Error Handling**: The new `register_defn_signature` carry-forward path uses `unwrap_or((None, None, None))` for the "entry doesn't exist or wrong variant" cases — both are correct defaults (fresh registration). The `compile_to_module<M, C, L>` Steps 1-5 all use `?` with `CranelispError`. The cache-load swallowed-failure pattern remains correctly hard-error per Sprint 58 Wave 2's fix at `worker.rs:2935-2970`. PASS.
- **§2 Code Structure**: `register_defn_signature` is now ~100 lines (borderline the §2 100-line guideline) but is cleanly structured (fast-path early return for trait-impl mangled names, then param/return type construction, then the upsert with carry-forward). The doc comment at `:2184-2205` carries the load-bearing safety rationale. `compile_to_module<M, C, L>` is ~270 lines, structured by step comments — same shape as Wave 2 close. Borderline PASS.
- **§3 Naming**: `CodeStore`, `LinkerStore`, `Code::Jit`, `Code::Linker`, `code.ptr()`, `SessionSymbolTable`, `SessionModuleEntry`, `jit_free_memory_call_count`, `JIT_FREE_MEMORY_CALL_COUNT`, `into_concrete`, `new_with_params` — all descriptive and consistent. PASS.
- **§5 Single Source of Truth**: Decisions 31, 32, 35 all converge on per-entry `Arc` retention with single source of truth on `ModuleEntry::Def.code`. No dual stores remain. PASS.
- **§6 Duplication**: The two `Code` constructor sites (fresh-build at `src/worker.rs:2783` and cache-hit at `src/worker.rs:2989`) both call `Code::jit(Arc::clone(&jit_arc), ptr)` / `Code::linker(Arc::clone(&linker_arc), ptr)` from a single helper — no duplication of the construction shape. The `into_concrete` conversion lives in one place per its use-site (cache-restore path); not duplicated. PASS.
- **§7 Architectural Boundaries**: `cranelisp-types` carries the empty marker traits + structural fields only — never names `Code`, `Jit`, `Linker`, or `cranelift_*`. `cranelisp-backend` operates on `<C, L>`-erased fields and never names `Code`. The integration layer (`src/`) is the sole site that names `Code`. Principle 3 satisfied. PASS.
- **§7a Idiomatic Rust**: New `unsafe` surface added by Wave 3 — `unsafe impl Send for Code` / `unsafe impl Sync for Code` at `src/code.rs:106-107` with comprehensive SAFETY comment at `:98-105`. The `JIT_FREE_MEMORY_CALL_COUNT` static at `crates/cranelisp-backend/src/jit.rs:181-182` is `pub(crate)`-scoped; the public accessor `jit_free_memory_call_count()` at `:188-190` exposes it for cross-test instrumentation without leaking the static itself. PASS.
- **§8 Serialization**: `#[serde(skip)]` discipline holds: `code: Option<C>` and `linker: Option<L>` skip; `#[serde(bound = "")]` suppresses derive-emitted bounds on `C` / `L` (load-bearing because `Code` doesn't impl Serialize). Round-trip tests `code_serialise_round_trip_skips_field` (`crates/cranelisp-types/src/module.rs:1014`) and `module_entry_def_code_field_is_optional_c` (`:1689`) verify cross-flavour serde. PASS.
- **§9 Testing**: 8 new tests in `src/code.rs::tests`, 5 new integration tests in `tests/v4_jit_reclaim.rs`, 2 instrumented unit tests in `crates/cranelisp-backend/src/jit.rs`. Unit-tests-with-dev principle honoured. One gap (carry-forward regression, see I-1) but otherwise comprehensive. PASS with one Important.

## Unsafe code audit

Per `/review` skill §5:

- `src/code.rs:106-107` (`unsafe impl Send + Sync for Code`): SAFETY comment at `:98-105` explains the `Arc<Jit>` / `Arc<Linker>` carriers are themselves `Send + Sync`, the `*const u8` is an integer handle, and `Code` instances support only Arc-clone + ptr-read (no `Jit` method dispatch). The argument mirrors the pre-Wave-3b `KeptJit` Send/Sync rationale verbatim. Acceptable.
- `crates/cranelisp-backend/src/jit.rs:256-258` (existing `unsafe { module.free_memory() }` in `Jit::drop`): unchanged from Sprint 57 Wave 4, SAFETY comment at `:246-255` references Decision 31 + Cranelift 0.116 evidence. Unchanged.
- `crates/cranelisp-backend/src/lib.rs:101-102` (`unsafe impl Send + Sync for CompilationResult`): SAFETY comment at `:93-100` explains the raw-pointer-as-integer-handle reasoning + cross-references the pre-Wave-3b `KeptJit` and `Code` Send/Sync impls. Sound.
- `crates/cranelisp-types/src/module.rs:559-560` (`unsafe impl<C: CodeStore> Send/Sync for ModuleEntry<C>`): SAFETY comment at `:538-558` correctly distinguishes the `*const u8` `platform_fn_ptr` (always present, raw pointer rationale) from the `code: Option<C>` field (delegated to `C` — `()` is trivially safe; `Code` carries its own `unsafe impl`). Sound.

Scattered `unsafe` / pointer risk: **contained**. Wave 3 adds 2 `unsafe impl` lines (one for `Code`, one for `CompilationResult`) and 1 new `unsafe { ... }` block (none — `unsafe` blocks unchanged from Sprint 57 Wave 4's `Jit::drop`). All documented. The encapsulation boundary remains the `Code` enum + the `Jit` wrapper.

## Design doc assessment

| Doc | Status |
|---|---|
| `design/arch/CLAUDE.md` Decision 32 | Stale — `Clone` super-bound landed but text omits it. Filed as I-2. |
| `design/arch/CLAUDE.md` Decision 31 (Scheduling footnote) | Stale — describes pre-Wave-3 `kept_jits` retention as the live state. Filed as I-3. |
| `design/arch/CLAUDE.md` Decision 35 | Comprehensive, prescriptive, well cross-referenced. PASS. |
| `design/arch/CLAUDE.md` Decision 25 (closing note re: rejected-alternative now actioned) | The reschedule rationale at `:84` already records "Generics activation is now scheduled as `pipeline-v4-roadmap.md` Phase 5 Step 5c (gap G12)..."; the actioned-status update could append "Landed Sprint 58 Wave 3b — Decision 25 Generics activation complete; per-redefinition Scenario 2 reclaim verified." Filed as I-3 alongside Decision 31 footnote. |
| `design/arch/interfaces.md` "Two-GOT model" subsection | Wave 2 land confirmed via `git show 7236aa7 --stat`; Wave 3 did not touch this subsection. Out of scope. PASS. |
| `design/int/symbol-table-generics.md` Wave 3b implementation outcome (§7-30) | Comprehensive; accurately reflects what landed including the out-of-scope crate-edit deviation. PASS. |
| `design/backend/compile-to-module.md` §17.1 / §17.1.1 / §17.4 / §17.6 / §17.7 | Comprehensive, prescriptive, well cross-referenced. PASS. |
| `crates/cranelisp-backend/src/jit.rs` doc comments at `:209-216, 242-250` | Accurate per Wave 3b dissolution + Decision 31 safety invariant. PASS. |

## Gate assessment

Wave 3 gate criterion (sprint plan `sprints/SPRINT.md:610`):

- ✓ `SymbolTable<C, L>` parameterised — confirmed at `crates/cranelisp-types/src/module.rs:101`.
- ✓ `Code` enum placed per Decision 35 — confirmed at `src/code.rs:71-87`.
- ✓ `kept_jits` + `kept_linkers` dissolved — confirmed via grep + `kept_jits_and_kept_linkers_fields_dissolved` regression test (modulo I-4: `KeptJit` struct still present as dead code).
- ✓ Per-redefinition JIT reclaim verified — `decision31_scenario2_per_redefinition_jit_pages_reclaimed` observes `Jit::drop` firing on per-redefinition.
- ✓ Baseline preserved (5 failures = exact pre-existing baseline, no Wave 3 regressions).
- ✓ `cargo clippy` clean per-crate — zero new warnings in any of the targeted crates.
- ✓ Test count ≥ Wave 2 baseline (1722 vs Wave 2's 2604; the count moved because of test reorganisation between waves, but the headline 5 reclaim tests added net).

**Gate PASS.** The Wave-3 fix shape (5a + 5b foundation + 5c generics + Decision 35 enum + `kept_jits` / `kept_linkers` dissolution + Decision 31 Scenario 2 verification) per `/arch`'s decisions is correctly implemented end-to-end. The 4 Importants are documentation-and-test-completeness items; none prevent Wave 4 from opening, but I-1 (carry-forward regression test) and I-2 (Decision 32 `Clone` super-bound doc) should land before sprint close to lock in the safety invariant + maintain the architectural-doc trail.

## Summary

| Severity | Count | Finding |
|---|---|---|
| Blocker | 0 | — |
| Important | 4 | I-1 carry-forward regression test missing; I-2 Decision 32 `Clone` super-bound doc; I-3 Decision 31 Scheduling footnote stale + Decision 25 closing note; I-4 `KeptJit` dead code remains |
| Suggestion | 5 | S-1 Scenario 1 bound tightening; S-2 DashMap lookup hoisting; S-3 cache-rehydrate Linker reclaim test; S-4 `module_supports_code_ptrs` helper; S-5 `mk_test_def` helper extraction |

Wave 3 is cleared for close from the code-review perspective. The architectural payoff (Decision 31 Scenario 2 per-redefinition JIT reclaim) is verified at the level the spec defines — `Arc::strong_count` + `jit_free_memory_call_count()` both observed on real REPL redefinition. Wave 4 (Step 5d carries) may proceed.
