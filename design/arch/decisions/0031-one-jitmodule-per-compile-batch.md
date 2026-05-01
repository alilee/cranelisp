---
number: 0031
title: One `JITModule` per compile batch; `Arc<Jit>` on `ModuleEntry::Def.code`; custom `Drop` calls `unsafe free_memory()`
status: operative
---

# 0031 — One `JITModule` per compile batch; `Arc<Jit>` on `ModuleEntry::Def.code`; custom `Drop` calls `unsafe free_memory()`

The JIT-lifetime story unifies across three scenarios under one primitive:

| Scenario | Module | Lifetime | Reclaim |
|---|---|---|---|
| REPL eval | Fresh `JITModule` containing the synthetic `__expr` (or equivalent one-shot) | Per-eval | Custom `Drop` on our `Jit` wrapper calls `unsafe free_memory()` after the result is consumed |
| Defn JIT | Fresh `JITModule` per `compile_to_module` call | `Arc<Jit>` on every `ModuleEntry::Def.code` produced by that batch | Custom `Drop` → `unsafe free_memory()` fires when the Arc refcount hits 0 (all entries evicted/redefined). **Scheduling footnote (Scenario 2 ACTIVE since Sprint 58 Wave 3)**: Sprint 58 Wave 3 (Step 5c) activated the `SymbolTable<C, L>` generics (per Decision 32) and selected the integration-layer `Code` enum as the concrete `C` (per Decision 35). `Arc<Jit>` lives directly on `ModuleEntry::Def.code = Some(Code::Jit { jit, ptr })`; `SharedState.kept_jits` is dissolved. Per-redefinition reclaim fires when the old `Def` entry is replaced and the replaced entry's `Arc<Jit>` clone drops, triggering the `Jit` wrapper's custom `Drop::drop()` → `unsafe free_memory()` (`crates/cranelisp-backend/src/jit.rs:244-258`). **Verified by `tests/v4_jit_reclaim.rs::decision31_scenario2_per_redefinition_jit_pages_reclaimed`** — the test directly observes (a) `Arc::ptr_eq` mismatch between the pre- and post-redefinition `Arc<Jit>`, (b) `Arc::strong_count(&first_jit) == 1` after the session releases its reference, and (c) `jit_free_memory_call_count()` increment by exactly 1 when the test-captured `first_jit` clone drops. **Carry-forward invariant (Wave 3b discovery)**: the upsert at `crates/cranelisp-typecheck/src/program.rs:2184-2232` clones the existing `code: Option<C>` forward into the rebuilt entry. Without that clone, REPL upsert would drop the prior `Arc<Jit>` mid-typecheck, calling `free_memory()` on JIT pages still referenced by the GOT slot before the new code address is written. The carry-forward keeps the carrier `Arc<Jit>` alive across the typecheck attempt; on success, codegen overwrites with the new `Code::Jit`; on failure, the carried-forward `code` remains and the GOT slot stays valid. This is the fix that required `C: Clone` on `CodeStore` — see Decision 32's `Clone` super-bound rationale. |
| Object | `ObjectModule` | Per compile batch | Plain `Drop`; no executable memory to reclaim |

**Safety invariant** for the `unsafe free_memory()` call (required by Cranelift 0.116 `cranelift-jit/src/backend.rs:219` — "none of the `fn` pointers are called afterwards"): when the Arc refcount reaches 0, no function pointer derived from that JIT is reachable. Held by:
- Every derivative pointer lives on a `ModuleEntry::Def.code` (which holds the `Arc<Jit>` — refcount > 0 while any such pointer is reachable), OR is ephemeral (stack-local during compile/call, drops before return), OR is a GOT slot.
- **REPL redefinition is the sole event that mutates GOT slots** (defn-of-existing-name at the REPL prompt). Between REPL evals the system is still: batch compiles append fresh GOT slots but never retarget existing ones, and the concurrent evaluation machinery (spec §12.4.3 lenient evaluation, §10.12 auto IO scheduling) is strictly fork-join, so no in-flight call outlives the prompt that issued it. On redefinition, the GOT slot is atomically swapped to point at the new code *before* the old `Arc<Jit>` can drop; callers reaching the site after the swap dispatch to the new code, and no new caller can observe the old entry.
- Language-level invariant: function values returned from user code are heap closures that call into the GOT, not raw code pointers. Eval cannot leak `__expr`'s fn pointer into the returned value.
- **Prospective concern — callback platforms.** The invariant above assumes platforms do not retain fn pointers across calls. The current platform ABI (spec §10.10.1) has no `Fn a b` row and therefore cannot retain callbacks. When callback support lands, the "Callback support (forward commitment)" sub-section below specifies the rules that preserve this invariant.

**Cranelift 0.116 evidence** (why a custom `Drop` is required):
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
   The safety contract is exactly what the invariant above upholds — Arc-refcount-zero means "no fn pointer reachable".
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
   Cranelift's own author flags the missing dealloc; we cannot reclaim per-function. Reclaim is necessarily per-JIT (per compile batch).

**Consequences**:
- Retracts Decision 28 (per-worker persistent JIT): long-lived per-worker JIT coalesces batches and defeats scenario-2 reclaim. Per-batch is the target.
- Strikes `pipeline-v4.md` §6.2 "persistent eval JIT": eval is a fresh-JIT-per-call with drop-to-reclaim.
- Inverts `pipeline-v4-roadmap.md` G10 row: "Fresh JIT per REPL expression" is the correct target direction, not a gap.
- The Wave 4+1 "JIT rotation" FIXME on `design/int/persistent-workers.md:206` disappears — rotation is unnecessary under the batch model.
- Decisions 25 (code on `ModuleEntry`), 27 (G8→G9 sequencing), and 29 (`rc::dec_shallow_io`) are orthogonal and unchanged.

**Callback support (forward commitment).** The current platform calling convention (spec §10.10.1) permits only `Int`, `Bool`, `String`, and `IO a` as argument types — there is no `Fn a b` row in the `i64` interpretation table, so platforms cannot today receive or retain user function values. When that row is eventually added, the rules below MUST hold so that the safety invariant survives verbatim:

1. The `i64` passed for a fn-typed argument is the address of the **heap closure struct** (Decision 11 layout: `[header | code_ptr | drop_glue_ptr | captures...]`), NOT the raw code pointer the closure would dispatch to. Platforms never see raw JIT addresses.
2. Platforms invoke the closure via a **host callback** (added to `HostCallbacks` alongside the existing `alloc` callback — spec §10.10.3 — when the feature lands; e.g., `invoke_closure(closure_addr, args...) -> i64`). The callback performs GOT-indirect dispatch through the closure's `code_ptr` slot, so every invocation hits the currently-defined code — redefinition is transparent to retained closures.
3. Platforms that **retain** a closure beyond the dynamic extent of the call (store it for later invocation) MUST inc the heap closure on storage and dec on release via host callbacks (e.g., `rc_inc`/`rc_dec`, following the §10.10.3 host-callback pattern). Retention without refcount participation is a platform contract violation.
4. Under these rules, REPL redefinition remains safe: the GOT swap retargets future callbacks to the new code; the old `Arc<Jit>` reaches refcount 0 only once no `ModuleEntry::Def.code` references it AND no live heap closure targets a GOT slot backed by it; `unsafe free_memory()` fires without dangling the platform's retained closure, because the retained closure calls through the GOT rather than into the freed JIT.

The exact host-callback names and signatures are out of scope for this forward commitment — they will be specified by `/platform` and `/spec` when the `Fn a b` row is added to §10.10.1.

Canonical locations: `crates/cranelisp-backend/src/jit.rs` (the `Jit` wrapper + `Drop` impl — owned by `/backend`), `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def.code` (serde-skip `Arc<Jit>`). Rationale: Principle 11 (single pipeline; one reclaim primitive across JIT and REPL) + Principle 7 (single source of truth — one rule, applied everywhere) + Principle 8 (per-batch IS the target; no interim persistent-worker JIT).
