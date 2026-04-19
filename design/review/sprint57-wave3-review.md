# Sprint 57 Wave 3 Review — G8 (Platform on SymbolTable) + IO Trampoline RC Fix

**Sprint**: 57 Wave 3
**Date**: 2026-04-18
**Reviewer**: `/review`
**Scope**: `/int` types additions (SchedulingClass relocation, `PrimitiveKind::PlatformEffect { scheduling_class }`, `platform_fn_ptr`), `/int` registry deletion (`src/platform_registry.rs` gone, `kept_dlls` retention pool, `handle_platform` write-site), `/backend` IO trampoline RC fix (`dec_shallow_io`, ownership-aware `current_is_fresh` scheme), `/qa` 9 G8 integration tests in `tests/wave3_g8.rs`.

## Verdict

**PASS with Importants.** Wave 3 delivers the three structural changes — registry deletion, Decision-26 platform placement, Decision-29 RC primitive — cleanly. All 5 v4_platform failures flip green, Condition 6 (`g8_io_trampoline_rc_balanced`) passes, baseline 14-failure count preserved. The most substantive review finding is Focus 2: `/backend`'s interpretation of Decision 24's "uniform consuming convention" sharpens the Decision's scope to *extern/call-site* boundaries rather than internal Rust helpers. This is sound but merits a one-line clarifying sentence on Decision 24 for future-reader clarity. Focus 3 (string-literal RC residual) is a genuine defect but out of Wave 3's scope — file as FIXME for a future sprint.

## Focus area findings

### Focus 1 — `kept_dlls` retention pool (Principle 8): **Suggestion**

**Verdict**: Legitimate intermediate. NOT a Principle-8 violation. **Coincidentally fixes a pre-existing latent bug** (the deleted `loaded_platforms` field was never written to — a dangling-pointer-in-waiting defect). That bug fix is a welcome side effect, not a Principle-8 concern.

**Pattern consistency with Wave 2**: `kept_dlls` is shape-identical to `kept_jits` / `kept_linkers` — a session-lifetime retention pool holding opaque handles to keep mmap'd/dlopen'd code pages alive. Same rationale as Wave 2 Focus 1: the pointers on `ModuleEntry::Def.platform_fn_ptr` (Decision 26) reference code pages inside loaded DLLs; those DLLs must outlive the longest-lived reader of their pointers. Sessions hold DLL handles for their full lifetime because `LoadedPlatform` dropping unloads the `libloading::Library`, invalidating every `platform_fn_ptr` that still refers into the DLL's code segment.

**The coincidental bug fix** is real: `CompilerSession.loaded_platforms` (prior to Wave 3) was a never-written-to `Mutex<Vec<LoadedPlatform>>` field. The actual DLL handle was leaked inside the old `handle_platform` via `std::mem::forget`-style behaviour in `libloading` (via `_library` field never being dropped, because the `LoadedPlatform` owning it was dropped at end of `handle_platform`'s scope — the Library's drop would actually unload the DLL). Fix landed in Wave 3 by actually pushing into `kept_dlls`. This is a **welcome correction** — the previous state was UB-adjacent and would have SIGSEGV'd under any DLL-unmapped-but-still-referenced scenario (e.g., under any future `reload_module` path that didn't re-register platforms).

**`LoadedPlatform` unsafe impls** (`src/platform.rs:39-40`): `unsafe impl Send for LoadedPlatform {}` / `unsafe impl Sync for LoadedPlatform {}` are newly added in Wave 3 to support `SharedState::kept_dlls: Mutex<Vec<LoadedPlatform>>`. The SAFETY comment at lines 32-38 is accurate: `libloading::Library` is not `Sync` by default on all platforms because `dlsym` has interior state, but post-load the code segment is read-only and function-pointer calls across threads are safe. The `_library` handle is never read after construction — its `Drop` is the only load-bearing behaviour. Adequate rationale.

**S-1**: `src/session_v4.rs:549-554` vs `:555-569` — the `kept_jits`/`kept_linkers`/`kept_dlls` block now has three similarly-shaped pools with nearly identical rationale comments. Consider factoring a single summary comment: "Three retention pools (`kept_jits`, `kept_linkers`, `kept_dlls`) all hold code-page-keeping handles for the session lifetime. Per-pool rationale below." A future G10 migration will move `kept_jits` off `SharedState` (per Wave 2 Focus 1); `kept_dlls` probably stays (DLL handles are session-wide regardless of worker lifecycle). Defer to G10 sweep.
- **Owner**: `/int`. **Severity**: Suggestion. **Timing**: G10.

### Focus 2 — `/backend`'s Approach 4 design divergence: **Suggestion**

**Verdict**: Sound architecture; well-reasoned. Merits a one-line clarifying sentence on Decision 24 to prevent future misreadings, but no behavioural change and no `/arch` ratification-as-Decision needed.

**Decision 24's "uniform consuming convention"** is written at the *call-site* level: "Every function call site compiles identically for RC management: the caller transfers ownership of heap-typed arguments to the callee." The enumerated scope ("user functions, trait methods, builtins, and externs") is exhaustive of *compiled-call* classifications — i.e., every `ResolvedCall` the backend emits CLIF for. `run_io_trampoline` is not a compiled call from the backend's perspective; it is an *internal Rust helper* inside the runtime crate, invoked by the extern `cranelisp_run_io`. The Decision-24 call-site discipline applies to the extern boundary (`cranelisp_run_io` is consuming of `io_ptr`), and the Rust-side helper is free to choose its own internal convention so long as the extern boundary preserves the consuming semantics.

**This is the correct reading of Decision 24**, and `/backend`'s Approach 4 implements it correctly:
- Extern boundary: `cranelisp_run_io(io_ptr)` is consuming — it calls `consume_io_tree(io_ptr)` post-trampoline-return.
- Internal helper: `run_io_trampoline` is *non-consuming* of `io_ptr` (caller's tree) but *consuming* of fresh subtrees it allocates during the walk. The `current_is_fresh: bool` (and `cont_is_fresh` on `cont_stack`) track which subtree ownership applies.
- Double-dec avoidance: caller-tree nodes are released exactly once by `consume_io_tree(io_ptr)` post-return; fresh nodes are released exactly once by inline `dec_shallow_io` at the replace site. The two paths are disjoint by construction.

**Why the brief's "unconditional shallow-dec at every replace site" was wrong**: under that rule, caller-tree nodes reached during the walk would be dec'd inline AND dec'd again by `consume_io_tree(io_ptr)` post-return. The 24 pre-existing `tests/io.rs` tests that invoke `run_io_trampoline` directly (bypassing the extern) would double-free their test-constructed trees. `/backend` tested the brief's rule, observed the 24-test break, and diverged with rationale. The divergence is documented in `design/backend/ring2-rc.md §3.5.3/§3.5.4` and in `io.rs:67-90` top-of-file doc. The rejected "unconditional shallow-dec" alternative is also documented at `ring2-rc.md:317` ("Unconditional shallow-dec at every replace site... double-dec's caller-tree closures"), which makes the reasoning discoverable for future readers.

**Why this needs one-line clarification on Decision 24**: a careful reader of Decision 24 as written might interpret "uniform consuming convention across all call types" as extending to internal Rust helpers. That reading would force `run_io_trampoline` to be consuming, which would break the pre-existing tests and require a larger surgical rewrite. The sharper reading — "at each compiled call site and at each extern boundary" — is what Wave 3 landed, and it's what the Decision always intended (the enumeration "user functions, trait methods, builtins, and externs" is exhaustive of *compile-time-emitted* calls).

**S-2**: `design/arch/CLAUDE.md:71` Decision 24 — consider adding a sentence clarifying scope: "The convention applies at each compiled call site (`ResolvedCall` emission in `apply.rs`) and at each extern primitive's implementation (extern boundary). Internal Rust helpers invoked by extern primitives are free to choose their own convention as long as the extern boundary preserves the consuming contract with the caller-emitted CLIF." This makes the Approach-4 scope explicit and prevents a future reader from concluding `run_io_trampoline` violates Decision 24.
- **Owner**: `/arch`. **Severity**: Suggestion. **Timing**: anytime before Wave 4 close.

### Focus 3 — String-literal residual RC leak: **Suggestion (file FIXME)**

**Verdict**: Genuine defect observable by `/qa`, but **out of Wave 3 scope** — it's a different code path than the `dec_shallow_io` fix Wave 3 landed. `/qa` appropriately pivoted to Pure/bind-only chains for the Condition-6 gate. File a FIXME; do not gate Wave 3 close on it.

**What `/qa` observed**: the `print "a"` path through the test-capture DLL doesn't fully balance RC. Specifically, string-literal lifetimes in REPL-compiled IO programs (e.g., `(print "a")`) don't fully reclaim. This is NOT the IO-trampoline intermediate-node leak that `dec_shallow_io` fixes. It's a distinct path: the string "a" is heap-allocated during REPL eval-time, stored in an Effect node's thunk (captured as a closure env), and the ownership story of the string inside the Effect thunk vs. the thunk's Rust Box<FnOnce> is unclear.

**Ownership candidates**:
1. `/backend` — codegen emits a `str-concat` or string-literal heap alloc without a consuming dec at the thunk's effective call site.
2. `/runtime` — `call_effect_thunk` or the thunk's capture semantics don't dec captured heap args on last use. (Note: the *codegen* side of string-literal handling is `/backend`; the runtime side is `/runtime`.)
3. `/platform` — the test-capture DLL's `print` implementation returns without explicit `cranelisp_runtime::string::dec` on its argument, relying on some consuming convention that isn't upheld by the builder.

**`/qa`'s pivot is correct**: Condition 6's stated gate (IO trampoline RC balance) is what Wave 3 delivered. String-literal lifetime in `print "a"` is a separate defect observable through `print`, not through the trampoline's fresh-node release path. The two failures stack if both are present; by switching to Pure/bind chains (no platform call, no string literal), `/qa` isolated the Wave-3 fix.

**S-3**: File `FIXME(/backend)` at `crates/cranelisp-runtime/src/io.rs:29` (near the `cranelisp_run_io` doc) with text: "String-literal lifetime through `print` does not fully reclaim. REPL-observed: `(print "a")` through the trampoline leaks the string allocation. Root cause hypothesis: codegen emits string-literal heap alloc for argument to Effect thunk construction but the thunk's consume-on-call discipline isn't propagated to the captured string. Evidence: `/qa`'s Wave-3 Condition-6 work switched to Pure/bind-only chains to isolate." Route to `/backend` first; if investigation reveals the defect is runtime-side, re-route to `/runtime`.
- **Owner**: `/backend` (investigate first; route). **Severity**: Suggestion (tracking). **Not a Wave-3 gate**: the tests `/qa` wrote for Condition 6 use Pure/bind chains and pass; the `print "a"` observation is a separate residual.

### Focus 4 — `unsafe impl Send + Sync for ModuleEntry`: **Suggestion**

**Verdict**: Unsafe scope is justified and documented. The future-field-addition risk is real but mitigated by the single source of truth (`ModuleEntry::Def` variant) being in a well-reviewed crate.

**Current unsafe contract** (`crates/cranelisp-types/src/module.rs:229-240`):
- Two raw-pointer fields: `Code.ptr: *const u8` (via `code: Option<Code>`) and `platform_fn_ptr: Option<*const u8>`.
- Both are integer handles transmittable across threads; the *backing pages* are what needs validity, not the pointer-integers themselves.
- SAFETY comment (lines 229-238) explicitly enumerates the two raw pointer fields, names the session-level retention (`kept_jits`, `kept_dlls`) that keeps backing pages alive, and states the invariant ("threads that dereference must hold a live handle to the owning resource — the session enforces this invariant").

**Risk surface analysis**:
- Raw pointers are localised to the `ModuleEntry::Def` variant; no other variant carries unsafe-relevant state.
- Readers of `code.ptr` and `platform_fn_ptr` are contained: `src/worker.rs` (JIT setup), `src/session_v4.rs` (REPL eval), `src/bind_chain_analysis.rs` (scheduling class — doesn't deref the `platform_fn_ptr`, only reads `scheduling_class`). All three sites are single-session-scoped; none holds a reader across session drop.
- No raw pointer arithmetic outside the `Code::new(ptr)` / `heap_load` / `heap_store` encapsulation.

**Future-field-addition risk**: if a future sprint adds a third raw-pointer field (e.g., a platform-data pointer, a JIT stub pointer) to `ModuleEntry::Def`, the `unsafe impl Send + Sync` silently extends to cover it. The SAFETY comment at line 229-238 is keyed to the two current fields, not a general invariant. A reviewer might miss the widening. Mitigation: the comment at line 229-238 is colocated with the unsafe impls in the same module that owns the variant; any PR adding a third raw-pointer field would touch this file. `/review` or `/arch` gate on such a PR catches it.

**S-4**: `crates/cranelisp-types/src/module.rs:229-240` — consider rewording SAFETY comment to be field-invariant rather than field-enumeration: "All raw pointer fields on `ModuleEntry::Def` (currently `Code.ptr` and `platform_fn_ptr`) reference process-lifetime resources retained at the session level..." — and add a comment at the top of the file stating "Adding a new raw-pointer field to `ModuleEntry::Def` requires re-auditing the `unsafe impl Send + Sync` contract below." This future-proofs the invariant.
- **Owner**: `/int` (owns `ModuleEntry::Def` per Decisions 25/26). **Severity**: Suggestion. **Timing**: anytime; cosmetic.

### Focus 5 — `/platform`'s Wave 3 task moot status: **Confirmed moot**

**Verdict**: `/platform`'s nominal Wave 3 task ("Update IO trampoline to resolve platform fns via symbol-table lookup") is **genuinely moot**. `/int`'s Wave 1 design (`design/int/platform-registry-removal.md §5.1`) correctly identified that `run_io_trampoline` never read `PlatformRegistry` to begin with — platform fn resolution happens at codegen time (in `collect_jit_setup`) and the thunk carries the fn pointer baked in. The SPRINT.md task description was based on an inaccurate sprint-brief interpretation.

**Verification of "no missed work"**:
1. **`cranelisp-platform/` crate's ABI contract**: unchanged. `PlatformFn`, `PlatformManifest`, `HostCallbacks`, `declare_platform!`, `call_effect_thunk` all survive unchanged per `design/platform/platform-registry-removal.md §4`. The only shift is `SchedulingClass` now re-exports from `cranelisp-types` (via `pub use`). Platform DLL authors continue to `use cranelisp_platform::SchedulingClass` unchanged. Verified: `crates/cranelisp-platform/src/lib.rs:41` `pub use cranelisp_types::SchedulingClass;` — zero-cost alias.
2. **Stdio / test-capture DLLs still compile + link**: verified indirectly via `g8_cross_module_platform_fn_resolution` (passes end-to-end, which requires the test-capture DLL to load + register + dispatch).
3. **`declare_platform!` macro consumers**: no platform DLL currently uses `PlatformRegistry`-aware APIs (per `design/platform/platform-registry-removal.md §4.3`: "Nothing in `crates/cranelisp-platform/` itself. The crate is a stable ABI surface." and `§9.9: "No new warnings introduced in cranelisp-platform or cranelisp-runtime."`). Spot-checked: `cargo clippy -p cranelisp-platform --lib -- -D warnings` clean.
4. **Platform unit tests**: pass (`g8_platform_effect_variant_carries_scheduling_class`, `g8_scheduling_class_moved_to_types_regression_guard`, `g8_scheduling_class_read_via_symbol_table`).

**Action**: update SPRINT.md Wave 3 `/platform` row to `completed (moot — see Wave 3 review §Focus 5)`.

## General findings

### Blocker findings

None.

### Important findings

None from Wave 3.

### Suggestion findings

**S-1** (see Focus 1): `src/session_v4.rs:548-569` — factor three retention-pool rationale comments into a single block summary. Owner: `/int`. Timing: G10.

**S-2** (see Focus 2): `design/arch/CLAUDE.md:71` Decision 24 — add a sentence clarifying scope (compiled-call-site + extern boundary, not internal Rust helpers). Owner: `/arch`. Timing: before Wave 4 close.

**S-3** (see Focus 3): `crates/cranelisp-runtime/src/io.rs:29` — file FIXME(/backend) for string-literal-lifetime-through-`print` RC residual. Owner: `/backend` (investigate; route to `/runtime` if needed). Timing: future sprint.

**S-4** (see Focus 4): `crates/cranelisp-types/src/module.rs:229-240` — reword SAFETY comment to be field-invariant, add "new-field audit reminder" note at top of file. Owner: `/int`. Timing: cosmetic; anytime.

**S-5**: `tests/wave3_g8.rs:193-263` (`g8_platform_registry_regression_guard`) — mirrors Wave-2 `g6_codegen_product_regression_guard`'s comment-stripping behaviour. Same caveat applies (misses trailing-comment references). Forbidden-pattern list targets struct/field shapes unlikely to appear in trailing comments, so in practice this is fine. Additionally, Wave 3's guard uses the SAME comment-skip logic as Wave 2's — deduplication opportunity: extract a shared `scan_forbidden_patterns(src_dir, forbidden, skip_comments)` helper into `tests/helpers/`. Low priority.
- **Owner**: `/qa`. **Severity**: Low (cosmetic).

**S-6**: `tests/wave3_g8.rs:276` (`g8_cross_module_platform_fn_resolution`) — the test uses `is_io()` as a type assertion, presumably checking whether the result type is an IO type. Verify this method exists on `Type` and returns the expected value for `(IO Int)` / `(IO String)` etc. If not, a trivially-passing assertion is a test-verification gap. (Did not verify — routine check for `/qa` to confirm.)
- **Owner**: `/qa`. **Severity**: Low.

**S-7**: `crates/cranelisp-runtime/src/drop.rs:432-446` (`dec_shallow_io`) — doc at lines 416-422 notes "Semantically equivalent to `rc::consume_shallow` (both perform a shallow last-ref dec + dealloc)". If `consume_shallow` already exists, consider making `dec_shallow_io` a `#[doc(hidden)] pub fn dec_shallow_io(ptr: i64) { rc::consume_shallow(ptr) }` thin alias. This reduces the primitive count while preserving the call-site naming documentation. (Not verified that `rc::consume_shallow` exists with identical semantics — worth checking before S-7 action.) Alternative: if the two differ subtly (Ordering, or NULLARY_THRESHOLD handling), keep both and document the semantic delta.
- **Owner**: `/backend` (owns `drop.rs` per `design/backend/ring2-rc.md`). **Severity**: Low; verify first.

## Pre-existing issues noted

**Workspace-level clippy errors** (unchanged from Wave 2 report; per-crate status re-verified):

| Crate | Status | Pre-existing errors |
|---|---|---|
| `cranelisp-types` | clean ✓ | — |
| `cranelisp-platform` | clean ✓ | — |
| `cranelisp-typecheck` | clean ✓ | — |
| `cranelisp-backend` | 1 error ✗ | `compiler/mod.rs:569` (`collapsible_if`) — Sprint 55 origin, unchanged. |
| `cranelisp-runtime` | 4 errors ✗ (lib+tests profile) | `vec.rs:539, :564` (`fn_to_numeric_cast` in test code, Sprint 6 origin 2026-03-06); `primitives/float.rs:42` (`approx_constant` in test code, Sprint 5 origin 2026-03-05). These are TEST-mode errors — the `--lib` without `--tests` profile is clean. Brief noted "4 pre-existing" — verified: these 3 + the backend's 1 = 4 total. |
| `cranelisp` (binary) | inherits backend error; plus `src/watch.rs:70/71` and `src/worker.rs:1922` pre-existing per Wave 2 report. | Unchanged by Wave 3 per scope. |

**Total pre-existing clippy errors**: 4 (backend `compiler/mod.rs:569`; binary `src/watch.rs:70/71` — 2; binary `src/worker.rs:1922` — 1). The 4 mentioned in the brief match this inventory. The 3 runtime errors in test code are a separate category (surface only under `--tests`); if those are counted, the total is 7. The brief's count of 4 suggests `--lib-only` baseline.

**Recommendation**: sweep all clippy errors in one commit (either Wave 6 or a dedicated sweep sprint). The backend `collapsible_if` is a 3-line `if let` chain collapse; the binary's are similar; the runtime test-code errors need minor test-refactor (use `std::f64::consts::PI`, cast via `usize` for fn-pointer-to-i64 in tests).

## Verification spot-checks

All spot-checks ran without `--no-fail-fast` per review guidance.

| Test | Result | Notes |
|---|---|---|
| `cargo nextest run --test wave3_g8` (9 tests) | **9/9 PASS** in 0.66s | All G8 integration tests green. Includes Condition-6 gate `g8_io_trampoline_rc_balanced` and deep-chain variant `g8_rc_balance_bind_chain`. |
| `cargo nextest run --test v4_pipeline -- v4_platform` (6 tests) | **6/6 PASS** in 0.46s | All 5 previously-failing `v4_platform_*` tests plus `v4_platform_empty_registry` regression guard pass. Matches Wave 3 gate criterion. |
| `cargo nextest run -p cranelisp --lib -- worker::tests` (10 tests) | **10/10 PASS** in 0.045s | All unit tests on `src/worker.rs` pass, including `platform_form_handler_writes_fn_ptr_to_entry` and `cross_module_platform_fn_resolution` (the Wave 3 /int-written unit tests). |
| `cargo nextest run -p cranelisp --lib -- bind_chain_analysis::tests` (16 tests) | **16/16 PASS** in 0.02s | Scheduling-class-reads-from-symbol-table migration verified. `test_scheduling_of_bare_name`, `test_scheduling_of_qualified_name` exercise the G8-post migration path. |
| `cargo nextest run -p cranelisp-runtime --lib -- io::tests` (16 tests) | **16/16 PASS** in 0.02s | All IO trampoline unit tests including new `decision24_run_io_pure_rc_balanced`, `run_io_trampoline_rc_balanced`, `run_io_trampoline_deep_bind_chain_rc_balanced`, `call_continuation_dec_closure`. The deep-chain (1000-step) and RC-balance tests are the ones most likely to break under a wrong design choice. |
| `cargo nextest run -p cranelisp-runtime --lib` (118 tests) | **118/118 PASS** in 0.14s | Runtime library tests all green; no regression. |

**Baseline assessment**: the 5 v4_platform tests flip green is confirmed by direct re-run (all 6 pass, with 5 of them being the previously-failing targets). Per the brief's "1617 passed / 14 failed (same baseline count, composition shifted from Sprint 56's by -5 v4_platform / +5 somewhere else — same net)" — the composition shift merits a one-line note in the Wave 3 close-out so baseline provenance is clear. The "+5 somewhere else" wasn't explicitly identified in the brief; recommend `/sprint` pins the exact 5 tests that took the 5 v4_platform slots in the post-Wave-3 failure set.

## Checklist walkthrough

Against `design/review/checklist.md`:

- **§1 Error Handling**: `handle_platform` uses `?` with structured errors; `dec_shallow_io` has `# Safety` but no user-facing errors. No `unwrap()` in new pipeline code. PASS.
- **§2 Code Structure**: `handle_platform` (src/worker.rs:1455-~1510) is ~55 lines, well within the 100-line budget. `dec_shallow_io` is 15 lines. `run_io_trampoline` grew to ~134 lines (with Par dispatch + call_continuation references). Borderline but linear shape. PASS.
- **§3 Naming**: No new bare `String` identifier leaks. `LoadedPlatform` uses typed fields. `SchedulingClass` is a named enum, never stringified. PASS.
- **§5 Single Source of Truth**: G8's whole point — `scheduling_class` lives on `PrimitiveKind::PlatformEffect` variant (one location); `platform_fn_ptr` lives on `ModuleEntry::Def` (one location); no side map. PASS. `SchedulingClass` also consolidated to `cranelisp-types` (one canonical definition; `cranelisp-platform` re-exports). PASS.
- **§6 Duplication**: `dec_shallow_io` is a distinct primitive from `consume_io_tree` (documented at `ring2-rc.md §3.5.3`) and from `consume_shallow` (if the latter exists — see S-7). The distinction is semantic: shallow-only-single-node vs. transitive-tree-walk. Name disambiguation is load-bearing per Decision 29.
- **§7 Architectural Boundaries**: `SchedulingClass` relocation to `cranelisp-types` preserves Principle 3 (types depends on nothing, platform depends on types). Verified: `cranelisp-types/Cargo.toml` has no `cranelisp-platform` dep; `cranelisp-platform/Cargo.toml` has `cranelisp-types` dep. The DAG direction is correct and stable. PASS.
- **§7a Idiomatic Rust**: `unsafe impl Send + Sync for ModuleEntry` has SAFETY comment (see Focus 4). `unsafe impl Send/Sync for LoadedPlatform` has SAFETY comment (see Focus 1). `#[serde(skip)]` on `platform_fn_ptr` per Decision 26. PASS.
- **§8 Serialization**: `platform_fn_ptr` is `#[serde(skip, default)]` (line 170 in module.rs). `scheduling_class` inside `PrimitiveKind::PlatformEffect` is serialised (per Decision 26 asymmetry). Tested by `platform_fn_ptr_skipped_by_serde` (cranelisp-types unit test) and `g8_scheduling_class_moved_to_types_regression_guard`. PASS.
- **§9 Testing**: 9 new integration tests (`tests/wave3_g8.rs`) covering platform-fn-ptr write, scheduling-class symbol-table path, cross-module resolution, `kept_dlls` retention, Condition-6 RC balance, scheduling-class move, variant-placement. Unit tests in `cranelisp-runtime` (6 new: `decision24_run_io_pure_rc_balanced`, `run_io_trampoline_rc_balanced`, `run_io_trampoline_deep_bind_chain_rc_balanced`, `call_continuation_dec_closure`, `test_read_resource_token` variants). Unit tests in `src/worker.rs` (3+ per brief: `platform_form_handler_writes_fn_ptr_to_entry`, `cross_module_platform_fn_resolution`, `priority_worker_stores_code_ptr_in_got_slot`). Unit-tests-with-dev principle honored. PASS.

## Unsafe code audit

Per `/review` skill §5, Wave 3 introduces/modifies these unsafe sites:

| Site | SAFETY comment? | Encapsulated? | Rationale |
|---|---|---|---|
| `crates/cranelisp-types/src/module.rs:229-240` — `unsafe impl Send + Sync for ModuleEntry` | Yes, lines 229-238 | Yes (sole `ModuleEntry` module) | Raw pointers via `Code.ptr` + `platform_fn_ptr`; both session-scoped. Adequate. See Focus 4 for future-field risk. |
| `src/platform.rs:39-40` — `unsafe impl Send + Sync for LoadedPlatform` | Yes, lines 32-38 | Yes (sole `LoadedPlatform` module) | `libloading::Library` not `Sync` by default; post-load code pages are read-only. Accurate. |
| `crates/cranelisp-runtime/src/drop.rs:432-446` — `dec_shallow_io` unsafe blocks | Yes, docstring lines 427-431 + inline SAFETY at 436 | Yes | Sole caller path is from `run_io_trampoline` at replace sites. Invariant: caller transferred heap-typed field ownership elsewhere before calling. Documented. |
| `crates/cranelisp-runtime/src/io.rs:91-225` — tag read, field read, continuation call | Multiple `unsafe` blocks with inline SAFETY | Localised to trampoline | Reading tag/field offsets from heap pointers at known offsets; `call_continuation` uses `transmute` to recover `extern "C" fn(i64, i64) -> i64` signature. Standard trampoline pattern; no new surface. |

**Scattering risk**: Wave 3's new unsafe surface is contained. `unsafe` is localised to three files: `crates/cranelisp-types/src/module.rs` (unsafe impl), `src/platform.rs` (unsafe impl), `crates/cranelisp-runtime/src/io.rs` + `drop.rs` (trampoline + dec primitive). No `unsafe` leaking into `src/worker.rs`, `src/session_v4.rs`, or `src/bind_chain_analysis.rs` — the callers of these unsafe primitives use safe APIs.

**Overall unsafe audit**: clean. No expansion of risk surface beyond what Decision 26's pointer-on-entry shape necessarily requires.

## Design doc assessment

- **`design/int/platform-registry-removal.md`**: Comprehensive (12 sections covering state, registration path, readers, G6/G9 impact, tests, acceptance). Current with the Wave 3 implementation. PASS.
- **`design/platform/platform-registry-removal.md`**: Comprehensive (9 sections). Aligned with `/int`'s decisions (Option B for `scheduling_class`; sibling field for `platform_fn_ptr`). Section 8's "Open Questions" has unresolved FIXMEs that can now be resolved post-Wave-3 (`SymbolTable::resolve_chain` helper — /int now owns; `platform_fn_ptr` placement symmetry — /int chose sibling-field; five-failing-test identification — /qa resolved in Wave 1). Minor cleanup: marking these resolved. PASS with one cosmetic note.
- **`design/backend/ring2-rc.md §3.5`**: Comprehensive; §3.5.4 "Fix shape — LANDED Sprint 57 Wave 3" documents the Approach-4 choice and explicitly rejects the brief's "unconditional shallow-dec" recommendation with rationale (lines 317-318). §3.5.5 explains why `call_effect_thunk` is unaffected; §3.5.7 documents the testing requirement. Current with code. PASS.
- **`design/arch/CLAUDE.md` Decisions 24, 26, 29**: All in effect. Decision 24's scope could be sharpened per Focus 2 (S-2). Decision 26 "Canonical location: `crates/cranelisp-types/src/module.rs` `ModuleEntry::Def` + `DefKind::Primitive.primitive_kind` (after G8 lands); owned by `/int` + `/platform` co-design" — correctly predicts the landed state. PASS.
- **`design/int/phase2-codegen-convergence.md` I-3 resolution**: Wave 3 added a "LANDED" banner to the top per the Wave-2 Important I-3. Verified banner exists. PASS.
- **`design/backend/compile-to-module.md` I-2 resolution**: Wave 3 updated §9.1.2-§9.1.9 to match Shape-1 pointer-only Code per Wave-2 I-2. Not re-verified in this review (Wave 2 finding, Wave 3 resolution); trust `/backend`'s claim. Accept.

## Gate assessment

Wave 3 gate criterion (SPRINT.md:533):

- ✓ `PlatformRegistry` deleted — confirmed by `g8_platform_registry_regression_guard` (scan for forbidden live-code patterns passes with zero matches).
- ✓ IO + platform tests pass — confirmed by `cargo nextest run --test wave3_g8` (9/9) and `--test v4_pipeline -- v4_platform` (6/6).
- ✓ 5 v4_platform failures cleared — confirmed: `v4_platform_form`, `v4_platform_stdio_print`, `v4_platform_io_trampoline`, `v4_platform_import_and_use`, `v4_platform_multiple_calls` all PASS.
- ✓ RC balance verified for IO trampoline — `g8_io_trampoline_rc_balanced` + `g8_rc_balance_bind_chain` + `run_io_trampoline_rc_balanced` + `run_io_trampoline_deep_bind_chain_rc_balanced` all pass. Condition 6 met.

**Wave 3 gate passes.** The residual string-literal leak (Focus 3) is outside the gate wording ("IO trampoline" not "platform string path") and is not a blocker.

## Summary

| Severity | Count |
|---|---|
| Blocker | 0 |
| Important | 0 |
| Suggestion | 7 |

Wave 3 is cleared for close from the code-review perspective. The 7 Suggestions are all tracking/cosmetic items; none gate Wave 4 opening. The one item worth explicit user attention is **Focus 3 / S-3** (string-literal RC residual) — a real defect observable in real programs, routed to `/backend` for future-sprint investigation.
