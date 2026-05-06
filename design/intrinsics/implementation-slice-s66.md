# Sprint 66 implementation slice — `cranelisp-intrinsics` (NEW crate)

**Status.** draft

**Author.** `/design (intrinsics)`, 2026-05-06

**Reads.** `design/arch/facades/intrinsics.md` (W1 + W2.5 + commits `f00a405`, `b93b34f` — final-state); `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md`; `design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md`; `design/arch/decisions/0011-embedded-drop-glue-ptr-in-closures.md`; `design/arch/decisions/0010-base-pointer-abi.md`; `design/arch/legacy/substance-scoping.md` §1.7; `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md`; `design/arch/fixmes/0103-dev-runtime-int-trace-io-trace-relocation-and-io-observer.md`; `design/runtime/runtime.md` (master design — current shape, retiring); `design/arch/bounded-contexts.md` §4 → §4b.

**Crate state.** `crates/cranelisp-intrinsics/` does NOT yet exist. This slice is for the **creation** of the crate per Decision 43, populated by migration from `crates/cranelisp-runtime/src/`. It is one half of the D43 split (the sibling slice is `design/primitives/implementation-slice-s66.md`); the third coordinate is `design/runtime/implementation-slice-s66-retiring.md` which describes the wind-down of `cranelisp-runtime` once both child crates absorb its surface.

---

## 1. Scope from facade

The facade at `design/arch/facades/intrinsics.md` enumerates the as-designed public surface. The current source for every facade item is `crates/cranelisp-runtime/src/{rc,drop,alloc,string,io,ivar,marshal,panic}.rs` plus the (yet-unauthored) `io_observer.rs` extension-point per Decision 40. The delta is dominated by file moves under workspace-skeleton creation; secondary deltas are small wording / re-export adjustments and a single delete (the IoObserver registration site has no current source — it is greenfield).

| Delta | Source location(s) | FIXME closed | Acceptance |
|---|---|---|---|
| **D1 — Crate skeleton.** Create `crates/cranelisp-intrinsics/` (Cargo.toml + `src/lib.rs`); workspace `Cargo.toml` adds member; depends on `cranelisp-types` (boundary types) + `cranelisp-platform` (consumes `IO_TAG_*` consts + `HostContext` for IO trampoline Effect dispatch). NO dep on `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-backend`, `cranelisp-primitives`. | new — `crates/cranelisp-intrinsics/Cargo.toml`, `src/lib.rs` | 0150 (Phase 1 partial — sibling slices land the parallel skeletons) | `cargo check -p cranelisp-intrinsics` green; workspace builds; dep graph matches facade §"Consumed surface". |
| **D2 — Allocator migration.** Move `cranelisp_alloc`, `heap_alloc_payload`, `heap_dealloc`, `alloc_with_rc`, `alloc_count`, `dealloc_count`, `bytes_allocated`, `bytes_current`, `bytes_peak`, `reset_counts`, `is_live`. Decision 10 base-pointer layout (`offset 0: total_size`, `offset 8: rc`, `offset 16: payload`) preserved verbatim. | `cranelisp-runtime/src/alloc.rs` (304 LOC) → `cranelisp-intrinsics/src/alloc.rs` | 0150 (Phase 2 row "Allocator") | All extern symbols still resolve at link/JIT time with identical signatures; allocation counters return same values; `LIVE_ALLOCS` debug set still functional. |
| **D3 — RC primitives migration.** Move `rc_inc`, `rc_dec`, `rc_underflow_check`, `is_rc_trace_enabled`. `consume_shallow` (atomic dec helper) moves with `drop.rs` (D4) per current runtime master design §3 — it lives in `rc.rs`; clarify allocation in implementation. Atomic discipline (Decision 13: `atomic_rmw add 1` Relaxed for inc; `atomic_rmw sub 1` Release for dec; Acquire fence on free) preserved. | `cranelisp-runtime/src/rc.rs` (199 LOC) → `cranelisp-intrinsics/src/rc.rs` | 0150 (Phase 2 row "rc.rs") | `CRANELISP_RC_TRACE=1` still emits trace; `rc_underflow_check` still callable in debug; backend's emitted-`atomic_rmw` continues to land at runtime targets; tests in `rc.rs::tests` follow. |
| **D4 — Drop glue migration.** Move `consume_slist`, `consume_sexp`, `consume_vec_of_heap`, `consume_io_tree`, `consume_closure`, and the IO-trampoline-only shallow `dec_shallow_io` (Decision 29). `consume_trace_call` is **vestigial under D40 + D43**: trace.rs leaves runtime entirely (per FIXME 0103); `consume_trace_call`'s sole consumer is the trace-ADT walk in `cranelisp-runtime/src/trace.rs` (relocating to `src/trace/` in int per D40). Decision: `consume_trace_call` follows `trace.rs` to `src/` (int), NOT to intrinsics. | `cranelisp-runtime/src/drop.rs` (864 LOC) → `cranelisp-intrinsics/src/drop.rs`; `consume_trace_call` extracts to `src/trace/drop_helper.rs` (or similar — `/design (int)` slice owns the destination) | 0150 (Phase 2 row "drop.rs"); coordinates with 0103 (the trace-ADT consume helper carries with `trace.rs`) | All extern symbols backend names (`consume_*`, `dec_shallow_io`) resolve in intrinsics; `consume_trace_call` resolves wherever int parks it; Decision 24 consuming-convention tests still pass. |
| **D5 — String runtime migration.** Move `HeapString` layout type + `heap_alloc_string`, `string_read`, `alloc_string`, `read_string_as_str`, plus the ~15 string ops (`str_concat`, `str_eq`, `str_len`, `str_substring`, `str_split`, `str_join`, `str_replace`, `str_trim`, `str_starts_with`, `str_ends_with`, `str_contains`, `str_to_upper`, `str_to_lower`, etc. per current `string.rs`). Layout opaque to backend per Decision 12 — no facade change; HeapString is `#[non_exhaustive]` per facade §"String primitives". `cranelisp-platform`'s `CLString` is `#[repr(transparent)]` over `*const HeapString` and reaches bytes via this crate's `read_string_as_str`. | `cranelisp-runtime/src/string.rs` (717 LOC) → `cranelisp-intrinsics/src/string.rs` | 0150 (Phase 2 — implicit; string.rs not in current FIXME table but is a Cat 2 intrinsic per D43 §"Migration scope") | `CLString::as_str` (in platform) continues to resolve `HeapString` bytes; user-callable string-conversion primitives in `cranelisp-primitives` (`int_to_string` etc.) reach `alloc_string` via this crate's public Rust API. |
| **D6 — Vec primitives migration.** Move `vec_new`, `vec_len`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow`, `vec_drop`. COW discipline preserved (last-use → in place; else copy). Two-allocation Vec layout (`[header(16) | len | cap | data_ptr]` + plain `cap*8` data buffer) per current `vec.rs`. | `cranelisp-runtime/src/vec.rs` (666 LOC) → `cranelisp-intrinsics/src/vec.rs` | 0150 (implicit — Cat 2 intrinsic per D43) | All `vec_*` extern symbols resolve in intrinsics; backend's pre-compiled-args codegen pattern (per memory) continues to call through. |
| **D7 — IO trampoline migration.** Move `cranelisp_run_io`, `run_io_trampoline`, `io_run`. Iterative state machine (`Pure | Effect | Bind | Par`) preserved verbatim. Rayon Par dispatch + resource-token serialisation preserved. Per-cont `is_fresh` flag for RC discipline preserved. **Cross-crate dep:** intrinsics depends on `cranelisp-platform` for the `IO_TAG_*` consts and `HostContext` (per facade §"Consumed surface" — not redeclared here). | `cranelisp-runtime/src/io.rs` (966 LOC) → `cranelisp-intrinsics/src/io.rs` | 0150 (Phase 2 row "io.rs") | The trampoline reduces IO trees correctly; Decision 24 consuming-convention end-to-end test pass; Decision 29 `dec_shallow_io` per-node dec pattern preserved. Coordinates with D8 below: the in-line `io_trace::record_event` calls in `io.rs` swap to invoke the registered `IoObserver`. |
| **D8 — IoObserver extension-point API (greenfield).** Author `cranelisp-intrinsics/src/io_observer.rs` per facade §"IO observation": `IoEventTag` (`#[non_exhaustive]`), `IoEvent` (`#[non_exhaustive]`), `IoObserver = fn(IoEventTag, &IoEvent)`, `register_io_observer(observer: Option<IoObserver>)`, `trace_anchor() -> &'static Instant`. Concurrency contract per facade (W3 follow-up `b93b34f`): "thread-safe from any thread; last write wins under happens-before ordering"; the API commits to the contract internally — callers don't reason about Acquire/Release. **No current source for this module** — it is greenfield. The facade design is locked. Wire `io.rs`'s ~17 inline `io_trace::record_event` call sites to invoke the registered observer (relaxed-load null check; no-op if unregistered) per D40. | new — `cranelisp-intrinsics/src/io_observer.rs` (~50 LOC); `cranelisp-intrinsics/src/io.rs` call-site swap | 0150 (Phase 2 row "IoObserver"); 0103 (Phase 1 step 1 — but the registration HOST is intrinsics post-D43, NOT runtime) | `cranelisp-intrinsics::register_io_observer` callable; `int`'s session startup (slice `int`) registers `io_trace::record` and observer fires for every IO state transition. Production batch (no observer registered) pays one relaxed null-check load per call site. |
| **D9 — IVar primitives migration.** Move `ivar_create`, `ivar_spark`, `ivar_force`. Decision 13 atomic discipline (PENDING → EVALUATING → RESOLVED CAS) preserved. Rayon `spawn` for sparked thunks. | `cranelisp-runtime/src/ivar.rs` (314 LOC) → `cranelisp-intrinsics/src/ivar.rs` | 0150 (implicit — Cat 2 intrinsic per D43) | `ivar_force` blocks correctly; lenient-evaluation tests pass. |
| **D10 — Sexp marshaling migration.** Move `quote_sexp`, `sconcat`. Tag constants (`TAG_SEXP_*`, `TAG_SCONS`, `TAG_SNIL`) continue to import from `cranelisp-types` per facade §"Consumed surface" — Principle 15 (no re-export ceremony). | `cranelisp-runtime/src/marshal.rs` (389 LOC) → `cranelisp-intrinsics/src/marshal.rs` | 0150 (implicit — Cat 2 intrinsic per D43) | `quote_sexp` produces the same heap layout; `sconcat` preserves SList semantics for unquote-splicing; macro tests pass. |
| **D11 — Panic helper migration.** Move `runtime_panic`, `take_runtime_error`. Sentinel-pattern preserved (per spec §12.7.2 and `runtime_panic` §2.10 — bare-message contract; no `ErrorLocation` enrichment, distinct from D42's PlatformError). | `cranelisp-runtime/src/panic.rs` (95 LOC) → `cranelisp-intrinsics/src/panic.rs` | 0150 (Phase 2 row "panic.rs") | `take_runtime_error()` polled by host after every JIT entry; match-exhaustiveness panics surface as program exit signal. |
| **D12 — `lib.rs` authoring.** Author `cranelisp-intrinsics/src/lib.rs`: `pub mod` declarations for `alloc`, `rc`, `drop`, `string`, `vec`, `io`, `io_observer`, `ivar`, `marshal`, `panic`. NO `pub use cranelisp_types::*` ceremony per Principle 15. Crate doc comment cites BC §4b + Decision 43 + the "backend-emitted-call targets only" invariant. | new — `cranelisp-intrinsics/src/lib.rs` | 0150 (Phase 5 row "facade authored from D43 categorisation") | `cargo public-api` baseline file authored for the new crate (S66 task per FIXME 0150 Phase 5; mentioned for traceability — actual `cargo public-api` infrastructure is `/qa`'s test-plan slice). |
| **D13 — Backend extern-call resolution.** Backend's `IntrinsicSymbol` array in `crates/cranelisp-backend/src/jit.rs` updates the registration source from `cranelisp_runtime::*` to `cranelisp_intrinsics::*` for every Cat-2 symbol named here. Backend's Cargo.toml gains `cranelisp-intrinsics` dep, drops `cranelisp-runtime` dep. **This delta is owned by the `/design (backend)` slice** — listed here for cross-crate completeness. | `cranelisp-backend/Cargo.toml`, `cranelisp-backend/src/jit.rs` `IntrinsicSymbol` array | 0150 (Phase 3 step 5) | Backend slice |
| **D14 — Int registers intrinsics with the JIT.** `int`'s session init resolves intrinsic names to fn ptrs and registers them via `JITBuilder::symbol`; `int`'s session startup calls `cranelisp_intrinsics::register_io_observer(Some(int::io_trace::record))` when REPL/trace mode or `CRANELISP_IO_TRACE=1`. Cargo dep on `cranelisp-intrinsics`. **Owned by the `/design (int)` slice** — listed here for cross-crate completeness. | `src/Cargo.toml`, `src/{session,startup}.rs`, `src/io_trace/mod.rs` | 0150 (Phase 1 dep updates); 0103 (registration site) | int slice |
| **D15 — Platform's CLString continues to wrap HeapString.** `cranelisp-platform`'s `CLString` (`#[repr(transparent)]` `i64` newtype over `*const HeapString`) reaches bytes via `cranelisp-intrinsics::read_string_as_str`. Cargo dep on `cranelisp-intrinsics` (replacing dep on `cranelisp-runtime`). **Owned by the `/design (platform)` slice** — listed here for cross-crate completeness. | `cranelisp-platform/Cargo.toml`, `cranelisp-platform/src/string.rs` | 0150 (implicit dep update) | platform slice |
| **D16 — Retire `cranelisp-runtime`.** Once D2–D11 land and source files have moved, delete `crates/cranelisp-runtime/`. Workspace `Cargo.toml` removes the member. Coordinate ordering: per FIXME 0150 Phase 1, the new crates can re-export from runtime initially to keep deps stable; the retirement is the final step (Phase 5). **This delta is owned by the `/design (runtime-retiring)` slice** — listed here for cross-crate completeness. | `crates/cranelisp-runtime/` (full delete); workspace `Cargo.toml` | 0150 (Phase 5 step 1) | runtime-retiring slice |

**Action-class breakdown (D1–D12, intrinsics-owned only):**

- **MOVE** (relocate + minor adjustments, no behaviour change): D2, D3, D4, D5, D6, D7, D9, D10, D11 — 9 deltas.
- **NEW** (greenfield authoring): D1 (crate skeleton), D8 (IoObserver), D12 (`lib.rs`) — 3 deltas.
- **DELETE** (this slice): 0 — no deletes within intrinsics' boundary; runtime-side deletes are owned by the runtime-retiring slice.

D13–D16 are cross-crate dependencies surfaced for bilateral completeness (count: 4) and live in sibling slices.

---

## 2. Ordering within the slice

The slice is largely one logical unit (the crate creation). Internal ordering within S66's wave plan:

1. **D1 first** — crate skeleton must exist before sources can move into it. Workspace `Cargo.toml` membership lands first; `cargo check -p cranelisp-intrinsics` green at empty state.
2. **D2 (alloc) + D3 (rc) + D4 (drop) + D5 (string) + D6 (vec) + D9 (ivar) + D10 (marshal) + D11 (panic)** — move in any order *internally*, but as one batch. Each is a clean file move with `Cargo.toml` re-export adjustments. Per FIXME 0150 Phase 1, the new crate can re-export from runtime initially (transient compatibility shim) to keep dependent crates green during migration; the shim deletes when D13 + D14 + D15 land.
3. **D7 (io) + D8 (IoObserver)** — paired sub-batch. The `io.rs` migration AND the IoObserver authoring must land together: D8's purpose is to be the sink for `io.rs`'s ~17 inline `record_event` call-site swaps. Authoring D8 separately would leave `io.rs` calling into a non-existent module; landing D7 alone would force `io.rs` to retain its `io_trace::*` direct dependency, blocking FIXME 0103.
4. **D12 (lib.rs)** — incrementally extends as each module lands; final-state `lib.rs` is authored once D2–D11 are in place.
5. **D13 + D14 + D15** — owned by sibling slices (backend, int, platform); land in S66 alongside this slice. Cross-crate timing handled by the wave plan.
6. **D16 (runtime retirement)** — owned by the runtime-retiring slice; final step.

**No internal blocking dependencies between D2–D11**: each file move is independent, gated only on D1 (skeleton) being present. The pair D7+D8 is the only tight internal coupling.

---

## 3. Estimated effort

Single sprint wave for the intrinsics-owned deltas (D1–D12). Sizing breakdown:

- **D1 (skeleton)**: 30 minutes — workspace Cargo.toml + empty crate scaffolding.
- **D2–D6, D9–D11 (8 file moves)**: ~3–4 hours total — each is a `git mv` + path update + re-export adjustment + `cargo check`. Includes following-tests (each file's `mod tests` carries with).
- **D7 (io trampoline move)**: ~1 hour standalone — single file, but the largest (~966 LOC) and needs the call-site swap pattern thought through alongside D8.
- **D8 (IoObserver greenfield)**: ~2 hours — ~50 LOC of authoring + 17 call-site swaps in `io.rs` + integration test that the relaxed-load null-check pattern produces zero overhead when no observer is registered.
- **D12 (lib.rs)**: 30 minutes — module declarations + crate-doc comment; no behaviour.

**Total intrinsics-owned slice: ~7–8 hours** — a single triad cycle. **Cross-crate co-ordination overhead** (waiting on or unblocking the backend, int, platform, runtime-retiring slices) NOT included; that lives in the wave plan.

This sizing assumes **the FIXME 0150 Phase 1 transient compat shim** (new crates re-export from runtime initially) is used. Without the shim, D2–D11 must land in lockstep with D13 + D14 + D15 (no intermediate green state), inflating to a multi-day coordinated migration. **Recommend wave plan adopt the shim approach** per FIXME 0150 Phase 1.

---

## 4. Dependencies on other crates' slices

| This slice's item | Depends on | In the other crate's slice |
|---|---|---|
| D1 (workspace Cargo.toml) | sibling — `/design (primitives)` slice | `design/primitives/implementation-slice-s66.md` D-equivalent (workspace Cargo.toml lands both new crates atomically) |
| D7 + D8 (io trampoline + IoObserver) | `/design (platform)` slice for `IO_TAG_*` consts + `HostContext` final shape | `design/platform/implementation-slice-s66.md` (verifies platform's IO_TAG consts + HostContext are stable; per facade `25fa73a`, R9 truth-telling already landed — should be no churn) |
| D7 (io trampoline) | `/design (runtime-retiring)` slice for `io.rs` extraction (`cranelisp-runtime` source removal) | `design/runtime/implementation-slice-s66-retiring.md` |
| D4 (drop) — `consume_trace_call` extraction | `/design (int)` slice for trace-ADT walk relocation per FIXME 0103 | `design/int/implementation-slice-s66.md` (the `src/trace/` module that absorbs the relocated trace orchestration owns the destination for `consume_trace_call`) |
| D8 (IoObserver) | `/design (int)` slice for the observer registration site (`int::io_trace::record`) | `design/int/implementation-slice-s66.md` (per FIXME 0103 Phase 2; the `src/io_trace/` module + session startup registration call) |
| D13 (backend dep update + `IntrinsicSymbol` array) | `/design (backend)` slice — sibling | `design/backend/implementation-slice-s66.md` D-equivalent |
| D14 (int dep update + JIT registration) | `/design (int)` slice — sibling | `design/int/implementation-slice-s66.md` D-equivalent |
| D15 (platform dep update + CLString routes through intrinsics) | `/design (platform)` slice — sibling | `design/platform/implementation-slice-s66.md` D-equivalent |
| D16 (runtime crate retirement) | `/design (runtime-retiring)` slice — sibling | `design/runtime/implementation-slice-s66-retiring.md` |

**Bilateral check**: every cross-crate touch in this slice's table is named with the destination slice; the destination slices are expected to carry the reciprocal entry. `/arch`'s W4b cross-cutting check (per `sprint-65-reshape-phase-2-review.md` §3.3) verifies bilaterality across all 9 W4a slices.

**Total cross-crate dependencies: 9 entries spanning 5 sibling slices** (primitives, platform, runtime-retiring, int, backend).

---

## 5. Test surface impact

**No new spec-level user-visible behaviour.** D43 is a refactor: the language semantics, RC discipline, IO trampoline reduction order, panic propagation contract — all preserved. Test impact concentrates on:

- **Per-module unit tests follow their files** (per `feedback_unit_tests_with_dev.md`). Each `crates/cranelisp-runtime/src/{file}.rs::tests` module migrates with its file: `alloc::tests` → `cranelisp-intrinsics::alloc::tests`, etc. Test count unchanged; test-import paths in the test bodies update.
- **Integration tests in `tests/`** that currently link against `cranelisp-runtime` for fn-pointer access (rare — most go through the JIT'd code path) update their `Cargo.toml` deps to `cranelisp-intrinsics`. Per `project_test_strategy.md`, integration tests run e2e via the cranelisp exe; only a small handful might touch runtime types directly. **Owned by `/qa`'s S66 test plan slice.**
- **D8 (IoObserver) needs new unit tests** in `cranelisp-intrinsics::io_observer::tests`:
  1. `register_io_observer(Some(f))` then trampoline reduces an IO tree → observer fires with expected event sequence;
  2. `register_io_observer(None)` then trampoline reduces → zero observer calls (relaxed-load null check pays one branch);
  3. Concurrency: two threads register different observers; "last write wins under happens-before ordering" — assert the most-recently-registered observer is the one called by a subsequent reduction (per facade `b93b34f`).
- **End-to-end IO-trace test** validates the full chain (D8 + int's `src/io_trace/` registration + ring buffer + flush) — owned by the `/design (int)` slice and `/qa`'s test plan slice.

**No `[Tested]` annotation moves required in `spec/`** — D43 is below spec level. **No `#[ignore]`'d tests created.**

If `/qa`'s S66 test plan slice does not enumerate the D8 unit tests above, file FIXME `target: /qa` from this slice. (At authoring time `/qa`'s slice is co-authoring in W4a — bilaterality to be verified at W4b cross-cutting check.)

---

## 6. Open questions

The facade is locked (W1 + W2.5 + `f00a405` + `5b25663` + `b93b34f`). No interface-level questions surfaced during slice authoring. Three sub-questions exist where the facade does not pin and the answer is delegable to implementation:

1. **`consume_trace_call` destination naming.** Facade and decisions confirm `consume_trace_call` goes to int (not intrinsics) because trace.rs leaves runtime entirely per FIXME 0103. The exact module path within `src/trace/` is `/design (int)`'s call. **Not an `/arch` FIXME** — int's slice resolves at authoring time.

2. **Re-export shim duration.** FIXME 0150 Phase 1 proposes the new crates re-export from runtime initially (transient compat). Wave plan decides how many phases the shim survives. **Wave-plan decision, not facade**; deferred to `/sprint`.

3. **Crate-public Rust API vs `extern "C"` API distinction in `lib.rs`.** Facade lists both shapes for several primitives (e.g., `alloc_with_rc` vs `cranelisp_alloc`). The `lib.rs` re-export wall must mark both; the conventional pattern (`pub use alloc::{cranelisp_alloc, alloc_with_rc, ...}`) suffices. **No `/arch` question** — implementation pattern matches the existing `cranelisp-runtime/src/lib.rs` model.

**No FIXMEs filed against `/arch` from this slice.**

---

## Cross-references

- `design/arch/facades/intrinsics.md` — the facade this slice implements
- `design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md` — the binding decision
- `design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md` — IoObserver registration host moved here from runtime
- `design/arch/fixmes/0150-runtime-split-primitives-intrinsics.md` — implementation tracker (this slice is its W4a expression for intrinsics)
- `design/arch/fixmes/0103-dev-runtime-int-trace-io-trace-relocation-and-io-observer.md` — coordinates with this slice on the io.rs call-site swap + observer registration site
- `design/runtime/runtime.md` — current as-built shape (the source side of this migration)
- `design/primitives/implementation-slice-s66.md` — sibling slice (the other half of D43)
- `design/runtime/implementation-slice-s66-retiring.md` — sibling slice (the runtime wind-down)
- `design/backend/implementation-slice-s66.md`, `design/int/implementation-slice-s66.md`, `design/platform/implementation-slice-s66.md` — sibling slices that consume intrinsics post-migration
- `design/qa/test-plan-slice-s66.md` (or `tests/plan/implementation-slice-s66.md`) — `/qa`'s S66 test plan that this slice's D8 unit tests feed into
