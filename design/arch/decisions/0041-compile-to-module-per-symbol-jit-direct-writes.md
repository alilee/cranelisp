---
number: 0041
title: `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes shared state directly; returns `CompilationArtifacts`; `produce_disasm` is a separate on-demand backend function
status: operative
---

# 0041 — `compile_to_module` per-symbol JIT cardinality; `Code` moves to `cranelisp-backend`; backend writes the GOT slot, the caller composes `Code`; returns `CompilationArtifacts`; `produce_disasm` is a separate on-demand backend function

> **D1 partial reversal (S80 Wave 2D, 2026-06-13).** D41's settlement that macro
> `sexp`/`source` lives on the int-layer `Introspection` record (not on the
> symbol-table entry) is **reversed for the macro `sexp` *compile-path* field only**.
> The user ruling: introspection is REPL-slash-command-only and MUST be populated
> only in REPL mode; any data the *compile* pipeline reads belongs on the symbol
> table. The on-demand macro-clause recompile (`resolve_macro_sexp_from`) was a
> compile-path read sourced from `introspection`, which forced S78 to populate
> introspection unconditionally and broke the REPL-vs-batch discriminator. Macro
> source now lives on `DefKind::Macro.macro_sexp` (serialized — survives cache
> restore); introspection reverts to REPL-only; the run-mode signal is an explicit
> `RunMode` carrier on `SharedState`, not `introspection.is_some()`. D41's *symmetry*
> rationale still holds for every OTHER Def kind and for the introspection *display*
> readers. Canonical: `design/arch/d1-introspection-repl-only.md` (+ BC §6 + the
> `DefKind::Macro` rustdoc).

> **S75 W2 correction + drain pointer (2026-06-02, user-approved; manifestation site repointed S75 W5b).** Two parts of this Decision were corrected because they target-stated something not embodiable crate-narrow, and the corrected substance now lives at its manifestation site. **`facades/backend.md` was retired S75 W5b** (7th facade-retirement data point); the canonical home is now `bounded-contexts.md` §3 (backend — invariant 3 + "Who composes `Code`") + the `crates/cranelisp-backend/src/{lib,code}.rs` source rustdoc (per `design/arch/CLAUDE.md` §"Where a commitment manifests" — no separate Decision log). This Decision file is in the drain backlog (`design/arch/CLAUDE.md`); the corrected statements below are kept consistent with BC §3 + the source rustdoc so no contradicting copy remains until the file drains. (Below, the historical `facades/backend.md §...` citations are retained as the pre-retirement narrative trail — read them as "BC §3 + the backend source rustdoc".)
> 1. **#1 — `Code` construction is the CALLER's, not backend's.** `compile_to_module<M>` is generic over `M` and only borrows `&mut M`, so it never owns the `Arc<Jit>` needed to build `Code::Jit` (int wraps `Arc::new(jit)` *after* the call). This is symmetric with the cache-hit path (`load_object` returns `LinkerArtefact { Arc<Linker> }`; the caller composes `Code::Linker`). The embodiable rule, uniform across both modes: **backend writes the GOT slot (#2); the caller composes the `Code` lifecycle owner.** There is no `SymbolTable::write_code` requirement at backend's boundary. See `facades/backend.md` §"Free functions" ("Who constructs `Code`") + §"`Code`" + BC §3 invariant 3.
> 2. **`produce_disasm` is real, with a caller-supplied `code_size`.** Signature is `produce_disasm(fq, code_size, symbol_tables)` — the caller passes back the `code_size` it received in `CompilationArtifacts` (backend never reads it from persisted entry metadata; `ModuleEntry::Def` does not carry it). Body: resolve `fq` → GOT ptr → read `ptr..ptr+code_size` → capstone-disassemble (capstone is /arch-blessed as a direct backend dep, already in the tree via cranelift's `disas` feature). See `facades/backend.md` §"Free functions" (`produce_disasm` prose) + §"Consumed surface" (capstone).
>
> The §"S70 Phase B amendment", §3, §3b, and #4 text below predates these corrections; read them as superseded on the two points above (Code-construction-is-caller's; `produce_disasm` takes `code_size`). The corrected canonical statement is the facade.

`compile_to_module` is per-symbol-arity for JIT mode and per-module-arity for object mode (caller controls via `names` length). `Code` enum moves from `src/code.rs` to `cranelisp-backend/src/code.rs` (Decision 35 Layer 2 Option B retracts in the sense that int is no longer the sole crate to *name* `Code` — backend names it in its own signatures; Principle 3 protected — `Code` does NOT enter `cranelisp-types`). Backend writes the resulting fn pointer to the entry's GOT slot via `got().store_slot` (#2); the **caller** composes the `Code` lifecycle owner (`Code::Jit` from its owned `Arc<Jit>`, `Code::Linker` from the `LinkerArtefact`) and installs it via Decision 38's `write_code(&self, sym, code)` (#1 — the caller's, not backend's; see the S75 correction box above). Backend returns the **always-created** introspection artefacts (`clif_ir`, `code_size`, `compile_duration`) by value as `CompilationArtifacts`; the caller decides whether to retain or discard them. The **on-demand** disassembly is produced by a separate backend function `produce_disasm(&fq, code_size, &symbol_tables)` invoked lazily (e.g., when the `/disasm` REPL command fires), operating on the persistent post-compile machine code located via the GOT and bounded by the caller-supplied `code_size`. `Introspection` stays in the integration layer (no DAG inversion; backend never names it). Per-symbol JIT cardinality enables true per-redefinition reclaim; Decision 31 amends from per-batch to per-symbol cardinality.

## S70 Phase B amendment — direct-write of `Introspection` retracted (2026-05-26)

The pre-amendment `compile_to_module` signature carried `introspection: Option<&DashMap<FQSymbol, Introspection>>` as a parameter so backend could direct-write the per-symbol introspection record. That third direct-write is **retracted**.

**Why retract.** `Introspection` is an integration-layer (`int`) type — defined in `src/session_v4.rs` and target-stated by `facades/int.md` §"Introspection". For backend to accept `Option<&DashMap<FQSymbol, Introspection>>` at its public boundary, `Introspection` would have to live where `cranelisp-backend` can reach it. It does not — and putting it there inverts the DAG (Principle 3: `cranelisp-backend` does not depend on the `int` binary crate). This DAG inversion was surfaced by the Sprint 70 Phase B configuration → source completeness sweep, 5th audit lens (memo at `design/arch/cranelisp-types-settled-verdict-s70.md`). FIXME 0221 captured the question; this amendment resolves it.

**New shape — categorize by always-created vs on-demand.** The user-arbitrated direction: "for those things that are always created, no harm in passing those back to the caller and having the caller discard them if not required. for those created as needed, could there be a separate call?" Applied to backend's per-symbol introspection contributions:

- **Always-created** (returned in `CompilationArtifacts` by value): `clif_ir`, `code_size`, `compile_duration`. CLIF IR lives in memory during `compile_to_module`'s normal flow — Cranelift's `Function` IR is consumed by the codegen pipeline, so its capture must happen during compile or not at all; string serialization is ~tens of μs, dominated by codegen cost. Code size and compile duration are free byproducts of finalization. Always returning these in the artefact (and letting the caller drop them in production-batch mode) is cheaper than the conditional-branch + double-pointer DashMap insert the retracted shape required.
- **Created-on-demand** (separate backend function): `disasm`. Disassembly operates on the persistent post-compile machine code — `FQSymbol → SymbolTable.got().load_slot(slot) → ptr`, plus the entry's `code_size`. Both are reachable from the integration layer at any time after `compile_to_module` returns, so the disassembly call can fire lazily when a REPL `/disasm` request arrives, not eagerly per-compile.

**New canonical signatures:**

```rust
pub fn compile_to_module<M: Module>(
    scope: &ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &SymbolTables<Code, ()>,
    module_aliases: &ModuleAliases,
    module: M,
) -> Result<CompilationArtifacts, CompilationError>;

#[non_exhaustive]
pub struct CompilationArtifacts {
    /// CLIF IR text. Always captured during codegen; caller decides whether
    /// to retain it (REPL/trace mode) or drop it (production batch).
    pub clif_ir: String,
    /// Native code size in bytes. Reported by Cranelift finalize.
    pub code_size: usize,
    /// Wall-clock duration of the codegen step (parse-IR → finalized code).
    pub compile_duration: std::time::Duration,
}

pub fn produce_disasm(
    fq: &FQSymbol,
    symbol_tables: &SymbolTables<Code, ()>,
) -> Result<String, CompilationError>;
```

**Caller integration shape** (illustrative; the int-side cascade will action this when its wave fires):

```rust
let artifacts = backend::compile_to_module(scope, &[sym], st, ma, jit)?;
if shared.introspection.is_some() {
    shared.introspection.as_ref().unwrap().insert(fq, Introspection {
        source: ...,           // populated at parse time
        sexp: ...,             // populated at parse + expansion
        expanded: ...,         // (if surfaced)
        ast: ...,              // (if surfaced)
        clif_ir: Some(artifacts.clif_ir),
        code_size: Some(artifacts.code_size),
        compile_duration: Some(artifacts.compile_duration),
        disasm: None,          // produced lazily by /disasm REPL command
    });
}
// Later, on `/disasm <fn>`: let d = backend::produce_disasm(&fq, &shared.symbol_tables)?;
```

**Architectural properties this lands.**

1. **Zero DAG inversion.** Backend never names `Introspection`. The integration-layer type stays in the integration-layer crate; backend's public surface stays within its bounded context.
2. **No mode discriminator at `compile_to_module`.** Work performed by `compile_to_module` is uniform regardless of whether the caller is in REPL/trace mode or production batch. The caller controls retention by holding (or dropping) the returned `CompilationArtifacts`. The pre-amendment `Option<&DashMap<...>>::is_some()` doubling as a mode discriminator is gone.
3. **Principle 7 — minimum mechanism.** `Introspection` lives one place (int crate). Single source of truth for the composite per-symbol metadata record; no parallel backend-side DTO + merge step.
4. **D41 #1 (Code direct-write) and #2 (GOT slot direct-write) preserved unchanged.** Both still target types-crate types (`SymbolTable<Code, ()>`, `GotTable`); both still flow through interior-mutable `&self` methods.

**Operational implication / Context.** The pre-amendment `crates/cranelisp-backend/src/` source still carries the pre-amendment signature (or, depending on which row of the Wave 3 PIF list has fired, the older `Result<CompilationResult, CranelispError>` per-batch shape). Rotating backend source to the new amendment shape (`Result<CompilationArtifacts, CompilationError>` + the new `produce_disasm` free function) is **owed work for a future sprint** — parallel to typecheck/int wave-3 cascades, where every consumer crate needs rotation. This amendment doc names the new signature shape; the source cascade lands separately. Out of S70's frontend-focused remaining scope.

## Three coordinated changes (post-amendment shape — §3 is the value-returning + on-demand pair; the retracted #3 direct-write of `Introspection` is documented as §3b below)

### 1. Per-symbol JIT cardinality

Each `compile_to_module` call for JIT mode receives `&[symbol]` — one symbol per call. Backend creates one `JITModule`, defines one function, finalises, hands back. Object mode is unchanged: `compile_to_module` receives `&[full module's defined symbols]` and produces a `.o` containing all of them.

Cardinality is determined by the `names` arity at the caller, NOT by mode at the function signature — Decision 23's "mode is a Module property" remains intact. JIT call sites now look like:

```rust
for sym in defined_symbols(&shared.symbol_tables[scope]) {
    let jit = Jit::new_with_symbols(&extra)?;
    let artifacts = compile_to_module(scope, &[sym], &shared.symbol_tables, &shared.module_aliases, jit.jit_module())?;
    // Caller writes Introspection here if shared.introspection.is_some(); see §3 / §"S70 amendment" for the integration shape.
}
```

Per-redefinition reclaim becomes truly per-symbol: redefine one defn → its `Code::Jit` clone in the table drops → the `Arc<Jit>` hits 0 → custom `Drop` calls `unsafe free_memory()` for that one defn's pages, immediately. Cost: per-symbol `JITModule::new` invocations (~50 intrinsic registrations each per `register_intrinsics` in `jit.rs:166`). Cache-hit `Linker` cardinality is unchanged: one Linker holds many symbols (the `.o` is per-module, not per-symbol).

### 2. `Code` enum moves from `src/code.rs` to `cranelisp-backend/src/code.rs`

Backend already owns `Jit` and `Linker`; it's the natural home for the type that wraps both. Decision 35's "Code lives in `src/`" rationale was Principle 3 — `cranelisp-types` cannot import `Code` because `Code` references backend types. That rationale stands intact — `Code` does NOT move to `cranelisp-types`; it moves to `cranelisp-backend`.

`SymbolTable<C, L>` stays generic in `cranelisp-types`; backend instantiates `SymbolTable<Code, ()>` for its own signatures; frontend/typecheck stay on `SymbolTable<(), ()>` (no `Code` import for them either — the `C` generic continues to serve its purpose). Decision 35 Layer 2 Option B retracts: backend is no longer generic-blind; it knows about and constructs `Code`. The "integration layer is the sole crate that names `Code`" claim from Decision 35 relaxes — int still names `Code` at the session-boundary instantiation, but backend now also names it (in its own crate).

### 3. Backend writes directly to symbol tables; returns `Result<CompilationArtifacts, CompilationError>`; `produce_disasm` is a separate on-demand function

Canonical signatures (S70 Phase B amendment):

```rust
pub fn compile_to_module<M: Module>(
    scope: &ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &SymbolTables<Code, ()>,
    module_aliases: &ModuleAliases,
    module: M,
) -> Result<CompilationArtifacts, CompilationError>;

#[non_exhaustive]
pub struct CompilationArtifacts {
    pub clif_ir: String,
    pub code_size: usize,
    pub compile_duration: std::time::Duration,
}

pub fn produce_disasm(
    fq: &FQSymbol,
    symbol_tables: &SymbolTables<Code, ()>,
) -> Result<String, CompilationError>;
```

Backend writes each compiled symbol's `Code::Jit(Arc<Jit>)` into its entry via `symbol_tables.get(scope).unwrap().write_code(sym, Code::Jit(Arc<Jit>))` (Decision 38's `write_code(&self, …)` — interior mutable, no `&mut` flow needed). Backend also stores the GOT slot pointer via `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)`. Backend then returns the always-created introspection artefacts (`clif_ir`, `code_size`, `compile_duration`) packaged as `CompilationArtifacts`; the caller decides whether to retain (REPL/trace mode → write into `Introspection`) or drop (production batch → fall off the stack).

Decision 37's "no swallowed failures" rule lands as a single `?` inside `compile_to_module` — the per-step cascade collapses; backend errors out at the first invariant breach with a typed `CompilationError` variant.

### 3b. Why the direct-write of `Introspection` was retracted

The pre-amendment shape passed `introspection: Option<&DashMap<FQSymbol, Introspection>>` as a third direct-write parameter, paralleling #1 (Code) and #2 (GOT slot). That third direct-write inverted the dependency DAG: `Introspection` is an integration-layer (`int`) type and putting it on backend's public boundary would require `cranelisp-backend → int` (forbidden by Principle 3). The retraction substitutes:

- Backend returns `CompilationArtifacts` by value (always-created fields). Caller does the `Introspection` write itself, in its own crate, with full visibility into the integration-layer composite type.
- `disasm` (the on-demand field) becomes a separate backend function `produce_disasm(fq, symbol_tables)` invoked when the REPL `/disasm` command fires, not eagerly per-compile.

Net result: D41 #1 + #2 (direct-writes to types-crate types — `Code` into `SymbolTable<Code, ()>`, ptr into `GotTable`) survive. D41 #3 (direct-write to int-crate type `Introspection`) is gone, replaced by the value-returning artefact + on-demand call shape above. The full rationale and architectural properties are in §"S70 Phase B amendment" at the top of this Decision.

## Consequences

- `crates/cranelisp-backend/src/code.rs` new (moved from `src/code.rs`); backend exports `pub enum Code { Jit { jit: Arc<Jit>, ptr: *const u8 }, Linker { linker: Arc<Linker>, ptr: *const u8 } }`.
- `src/code.rs` deleted; int imports `cranelisp_backend::Code` for session-boundary instantiation of `SymbolTable<Code, ()>`.
- `crates/cranelisp-backend/src/lib.rs` `compile_to_module` signature updated per §3 above; old `(Arc<Jit>, code_ptrs)` return removed.
- `src/worker.rs:2860-3018` post-loop deleted (the iterate-over-names + GOT-store + `Code::Jit`-construct + three error cascades collapse into the per-symbol call-site loop above).
- `Jit::compile_defn` (audit HIGH-1) confirmed deprecated — paired pin: `Jit` exposes only `new` / `module` / finalize accessors; per-function compilation is via `compile_to_module` only — there is no public `compile_defn`.
- `facades/backend.md` §"Public surface": `compile_to_module` signature spelled per §3 — `Result<CompilationArtifacts, CompilationError>`; the `CompilationResult` / return-tuple (pre-amendment) gone; `CompilationArtifacts` DTO added; `produce_disasm` free function added; `Code` enum surface added; no `Introspection` parameter.
- `facades/int.md` §"SharedState — code carrier construction": post-loop description deleted; `Code` import path updates from `src/code.rs` to `cranelisp_backend::Code`; `Introspection` struct unchanged; population narrative rotates to "caller writes the artefact-derived fields into `Introspection`" per the S70 amendment.
- `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed` re-verified against per-symbol cardinality — the test's "redefine X, observe pages reclaimed" assertion strengthens (reclaim is now per-symbol-immediate rather than batch-coalesced).

## S66 amendment + rollback — GOT is single source of truth (2026-05-09)

**Phase 1 (commit `b09ec76` + `6f47008`, superseded same day):** The ptr embedded in `Code` variants was migrated to a unified `fn_ptr: Option<*const u8>` field on `ModuleEntry::Def` (which also subsumed the previously-separate `platform_fn_ptr` and superseded the briefly-planned `primitive_fn_ptr`). `Code` variants slimmed to lifecycle owner only:

```rust
pub enum Code {
    Jit(Arc<Jit>),
    Linker(Arc<Linker>),
}
```

**Phase 2 (commit `1dc57ae`, rollback — same day):** The unified `fn_ptr` field was identified as redundant with the per-module `GotTable` already populated at registration. Removed. The variant slim is preserved; the call address now has its single home in the GOT.

**Canonical post-rollback statement:**

> **GOT is the single source of truth for callable addresses.** `ModuleEntry::Def.got_slot: Option<usize>` indexes into `SymbolTable.got()` (a `GotTable` — see `crates/cranelisp-types/src/got.rs`); the runtime address lives at `symbol_table.got().load_slot(slot)`. There is no separate `fn_ptr` / `platform_fn_ptr` / `primitive_fn_ptr` field. Origin (JIT-compiled / linker-loaded / platform DLL / primitive) is encoded by `kind: DefKind`.

Decision 41's substance is unchanged: per-symbol JIT cardinality, `Code` lives in `cranelisp-backend`, backend writes shared state directly, returns `Result<(), CompilationError>`. The post-rollback write pattern is:

1. Backend calls `jit.get_finalized_function(func_id)` to obtain the code ptr.
2. Backend calls `symbol_table.got().store_slot(slot, ptr)` to publish the address (Release; visible to JIT-emitted GOT loads).
3. Backend calls `SymbolTable::write_code(&self, sym, Code::Jit(Arc<Jit>))` to install the lifecycle owner (Decision 38's interior-mutable signature).
4. The entry's `got_slot: Some(slot)` was already allocated at registration; no field-level ptr write occurs.

Decision 31 Scenario 2 reclaim semantics are preserved (lifecycle ownership stays inside `Code::Jit(Arc<Jit>)`; `Drop` chain unchanged; the GOT slot's stored ptr becomes invalid the instant `JITModule::free_memory()` runs). See `design/arch/sprint-66-types-authoring-plan.md` §1.7-revised + §1.8 and `design/arch/facades/{types,backend,primitives,platform}.md` for the as-designed shape.

## Cranelift evidence (why custom `Drop` is required)

The per-symbol reclaim model above is enabled by — and depends on — Cranelift 0.116's JIT-memory contract. The evidence that motivates the `Arc<Jit>`-with-custom-`Drop` shape (originally captured by retired Decision 31):

1. `Memory::drop` leaks on purpose (`cranelift-jit-0.116.1/src/memory.rs:269-276`):
   ```rust
   impl Drop for Memory {
       fn drop(&mut self) {
           // leak memory to guarantee validity of function pointers
           mem::replace(&mut self.allocations, Vec::new())
               .into_iter()
               .for_each(mem::forget);
       }
   }
   ```
   So the default drop of a `JITModule` (or our `Jit` wrapper that owns one) reclaims nothing.
2. `JITModule::free_memory` is `unsafe` and frees everything (`cranelift-jit-0.116.1/src/backend.rs:219`):
   ```rust
   /// corresponding module, it should only be used when none of the functions
   /// from that module are currently executing and none of the `fn` pointers
   /// are called afterwards.
   pub unsafe fn free_memory(mut self) { … }
   ```
   The safety contract is exactly what the per-symbol invariant below upholds — `Arc<Jit>` refcount zero means "no fn pointer reachable from this JIT".
3. `prepare_for_function_redefine` does NOT reclaim (`cranelift-jit-0.116.1/src/backend.rs:575-596`):
   ```rust
   pub fn prepare_for_function_redefine(&mut self, func_id: FuncId) -> ModuleResult<()> {
       assert!(self.hotswap_enabled, "Hotswap support is not enabled");
       …
       self.compiled_functions[func_id] = None;
       // FIXME return some kind of handle that allows for deallocating the function
       Ok(())
   }
   ```
   Cranelift's own author flags the missing dealloc; we cannot reclaim per-function inside a shared JIT. Reclaim is necessarily per-`JITModule`. Per-symbol cardinality (this Decision) makes per-`JITModule` reclaim equivalent to per-symbol reclaim.

**Safety invariant** for the `unsafe free_memory()` call: when an `Arc<Jit>` refcount reaches 0, no function pointer derived from that JIT is reachable. Upheld by:

- Every derivative pointer lives on a `ModuleEntry::Def.code = Some(Code::Jit(Arc<Jit>))` (refcount > 0 while the entry holds it), OR is ephemeral (stack-local during compile/call, drops before return), OR is a GOT slot that is atomically swapped to the new code *before* the old `Arc<Jit>` can drop.
- **REPL redefinition is the sole event that mutates GOT slots** (defn-of-existing-name at the REPL prompt). Between REPL evals the system is still: batch compiles append fresh GOT slots but never retarget existing ones, and the concurrent evaluation machinery (spec §12.4.3 lenient evaluation, §10.12 auto IO scheduling) is strictly fork-join, so no in-flight call outlives the prompt that issued it. On redefinition, the GOT slot is atomically swapped before the old `Arc<Jit>` drop; callers reaching the site after the swap dispatch to the new code, and no new caller can observe the old entry.
- Language-level invariant: function values returned from user code are heap closures that call into the GOT, not raw code pointers. Eval cannot leak `__expr`'s fn pointer into the returned value.

## Callback support (forward commitment)

> **SUPERSEDED (S98, 2026-07-01) — do NOT migrate this section into the canonical set.**
> The S98 platform-effect-boundary ruling (`effect-concurrency.md` §12.1; canonical
> statement at `bounded-contexts.md` §5 invariant 3 + the two-pointer-`HostCallbacks`
> paragraph) retires this forward commitment: the platform-effect boundary is **poll-in
> / wake-out only**, there is **no closure-callback-into-cranelisp capability**, and
> `HostCallbacks` will NOT gain `invoke_closure`/`rc_inc`/`rc_dec`. A cranelisp closure
> never crosses the DLL boundary. The heap-closure GOT-dispatch safety machinery below
> remains valid ONLY as the *in-process* cranelisp-to-cranelisp model (e.g.
> `io::call_continuation` inside `cranelisp-intrinsics`); it is not a DLL-ABI
> capability. This section drains to nothing — the retirement, not the commitment, is
> the durable record.

The safety invariant above assumes platforms do not retain fn pointers across calls. The current platform calling convention (spec §10.10.1) permits only `Int`, `Bool`, `String`, and `IO a` as argument types — there is no `Fn a b` row in the `i64` interpretation table, so platforms cannot today receive or retain user function values. When that row is eventually added, the rules below MUST hold so that the safety invariant survives verbatim:

1. The `i64` passed for a fn-typed argument is the address of the **heap closure struct** (Decision 11 layout: `[header | code_ptr | drop_glue_ptr | captures...]`), NOT the raw code pointer the closure would dispatch to. Platforms never see raw JIT addresses.
2. Platforms invoke the closure via a **host callback** (added to `HostCallbacks` alongside the existing `alloc` callback — spec §10.10.3 — when the feature lands; e.g., `invoke_closure(closure_addr, args...) -> i64`). The callback performs GOT-indirect dispatch through the closure's `code_ptr` slot, so every invocation hits the currently-defined code — redefinition is transparent to retained closures.
3. Platforms that **retain** a closure beyond the dynamic extent of the call (store it for later invocation) MUST inc the heap closure on storage and dec on release via host callbacks (e.g., `rc_inc`/`rc_dec`, following the §10.10.3 host-callback pattern). Retention without refcount participation is a platform contract violation.
4. Under these rules, REPL redefinition remains safe: the GOT swap retargets future callbacks to the new code; the old `Arc<Jit>` reaches refcount 0 only once no `ModuleEntry::Def.code` references it AND no live heap closure targets a GOT slot backed by it; `unsafe free_memory()` fires without dangling the platform's retained closure, because the retained closure calls through the GOT rather than into the freed JIT.

The exact host-callback names and signatures are out of scope for this forward commitment — they will be specified by `/platform` and `/spec` when the `Fn a b` row is added to §10.10.1.

## Cross-references and amendments

**Decision 31 retracted (S69 Phase 3).** D31's substance was fully amended into this Decision at Sprint 64; the residual file existed only as a confusion source (its title still said "per batch" while the body's amendment paragraph + D41's cross-references established per-symbol cardinality as operative). The Cranelift evidence + callback-support forward commitment that D31 was the canonical home for relocate verbatim into this Decision (§"Cranelift evidence" + §"Callback support" above). Per-symbol JIT cardinality is the operative model — both for `compile_to_module` JIT calls and for per-redefinition reclaim semantics. Per-batch cardinality retains only for object mode (one `ObjectModule` per `.o`).

**Decision 35 amends.** Layer 2 Option B retracts; `Code` location moves from `src/` to `cranelisp-backend`; "the integration layer is the sole crate that names `Code`" relaxes (int names it at the session boundary; backend names it in its own crate). The Principle 3 protection (no `cranelisp-types → cranelisp-backend` dep) survives intact.

**Decision 32 unchanged.** The empty-marker `CodeStore` trait still serves: `()` for non-codegen crates, `Code` for backend + int. The `Clone` super-bound stays — `Code` derives `Clone` (Arc clones are cheap).

Sprint 63 substance-scoping resolution §1.2.

## Rationale

- Principle 1 (decoupling) — int no longer duplicates backend's iteration.
- Principle 2 (narrow interfaces) — five parameters, no return tuple to unpack.
- Principle 7 (single source of truth) — backend writes the entry it produced.
- Principle 11 (single pipeline, mode parameters) — same function for JIT and object, mode driven by `Module` impl per Decision 23.

## Canonical location

`crates/cranelisp-backend/src/lib.rs` (`compile_to_module` signature); `crates/cranelisp-backend/src/code.rs` (`Code` enum, post-move). Owner: `/arch` files Decision and authors amended Decision 31 + Decision 35 cross-amendment notes; `/arch` updates `facades/backend.md` and `facades/int.md`. `/dev` (backend) executes the `Code` move and signature refactor; `/dev` (int) deletes the post-loop and refactors call sites.

## Status pointer — Sprint 67 close

S67 close — all four close-out items land in Waves 0+3+4:

- **Wave 0** — `CompilationError` enum + `LinkerError` enum +
  `LinkerArtefact` + `ObjectArtefact` authored in
  `crates/cranelisp-backend/src/{error,artefact}.rs` per REV-4
  (single-consumer placement, not `cranelisp-types`). Verified
  `cargo check -p cranelisp-backend` passes with the new types
  (no consumer wiring at Wave 0).
- **Wave 3** (`/dev (backend)`) — `Code` enum physically relocates
  from `src/code.rs` → `crates/cranelisp-backend/src/code.rs`;
  `compile_to_module` signature lifts to `Result<CompilationArtifacts, CompilationError>`
  (S70 Phase B amendment — `Result<(), CompilationError>` was the
  pre-amendment target; the value-returning artefact replaces the third
  direct-write per §"S70 Phase B amendment") + direct per-symbol writes
  via Decision 38's `write_code` + `got().store_slot`; on-demand
  `produce_disasm(fq, symbol_tables)` is a separate free function;
  `load_object` becomes a free function returning
  `LinkerArtefact`; `compile_to_object` becomes a free function
  returning `ObjectArtefact`; `Linker::get_symbol` returns
  `Result<*const u8, LinkerError>` (post-S58 silent-NULL regression
  closure).
- **Wave 4** (`/dev (int)`) — call sites in `worker.rs` /
  `pipeline.rs` collapse to per-symbol pattern; the previous
  multi-step post-loop dissolves.

Decision 41 closes substantively at S67 close.
