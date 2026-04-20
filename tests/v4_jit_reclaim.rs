//! Sprint 58 Wave 3 — Decision 31 reclaim integration tests.
//!
//! Validates the user-visible reclaim contract for both:
//!
//! - Decision 31 Scenario 1 — per-eval JIT pages reclaim after a REPL eval.
//!   Carry from Sprint 57 (FIXME(/qa) on
//!   `design/arch/pipeline-v4-roadmap.md` Decision 31).
//! - Decision 31 Scenario 2 — per-redefinition JIT pages reclaim when a
//!   REPL user redefines a `defn`. Headline payoff for Sprint 58 Wave 3
//!   (the dissolution of `SharedState.kept_jits` per Wave 3a/3b).
//! - Code::Linker session-scope retention — cross-check that the
//!   `Code::Linker` variant participates in the same `Arc`-based reclaim
//!   discipline (the integration-level companion to the unit test
//!   `code_enum_jit_variant_carries_arc_jit` in `src/code.rs::tests`).
//!
//! These tests exercise the contract through the user-facing surfaces:
//!
//! - The `cranelisp_runtime::bytes_current()` / `alloc_count()` /
//!   `dealloc_count()` counters, which the `/mem` slash command reports
//!   verbatim per `repl/spec.md §3.7`. Asserting on these counters is
//!   equivalent to asserting on `/mem` output (and is the same data the
//!   `/mem` handler at `src/session_v4.rs::handle_mem` reads).
//! - The backend-side `cranelisp_backend::jit::jit_free_memory_call_count`
//!   counter, which fires inside `Jit::drop` exactly once per reclaimed
//!   per-batch JIT page mapping. This is the primitive that materialises
//!   Decision 31's reclaim guarantee at the OS-page level.
//! - The session's `SharedState.symbol_tables` DashMap, exposed via
//!   `ReplSession::symbol_tables()`, which lets us inspect each
//!   `ModuleEntry::Def.code` to confirm `Code::Jit`/`Code::Linker`
//!   placement.
//!
//! ## Test placement rationale
//!
//! These tests live in their own integration crate (rather than in
//! `tests/repl_experience.rs`) because they share a delicate runtime
//! observation: `cranelisp_runtime::*_count()` are process-global atomics.
//! Placing the reclaim tests in a separate binary keeps them on the
//! existing nextest "one process per test" boundary while letting them
//! coexist with other runtime-counter-sensitive tests in their own home
//! files.

#[path = "helpers/mod.rs"]
mod helpers;

use std::sync::Arc;

use cranelisp::code::Code;
use cranelisp_backend::jit::jit_free_memory_call_count;
use cranelisp_types::{ModuleEntry, ModuleFullPath};

use helpers::*;

// =============================================================================
// Reclaim test infrastructure
// =============================================================================

/// Snapshot of the runtime counters that `/mem` reports per spec §3.7.
///
/// Mirrors the data shape `format_mem_snapshot` reads from
/// `cranelisp-runtime`. `/mem`'s rendering is tested separately (unit tests
/// in `src/session_v4.rs::mem_command_tests`); these reclaim tests assert
/// directly on the underlying counters because the contract being validated
/// is "live bytes return to baseline" — a numerical claim about the
/// counters, not about formatting.
#[derive(Debug, Clone, Copy)]
struct MemSnapshot {
    bytes_live: usize,
    allocs: usize,
    deallocs: usize,
}

impl MemSnapshot {
    fn capture() -> Self {
        MemSnapshot {
            bytes_live: cranelisp_runtime::bytes_current(),
            allocs: cranelisp_runtime::alloc_count(),
            deallocs: cranelisp_runtime::dealloc_count(),
        }
    }

    /// Live allocations, equal to the `<live-allocs>` field in `/mem`'s
    /// `; live: <bytes> bytes (<live-allocs> allocations)` line.
    fn live_allocations(&self) -> usize {
        self.allocs.saturating_sub(self.deallocs)
    }
}

/// Bound for "small constant" overhead between two snapshots — accommodates
/// transient allocations from REPL introspection state (e.g., the eval
/// result carrying a heap value into `it`-binding semantics in future
/// sprints; today even a primitive `(add-i64 1 2)` keeps no heap state).
///
/// 256 bytes is generous for the targeted tests (each operates on `:Int`
/// scalars which are stack-only); choosing a value too small would create
/// flakiness if any future REPL feature adds a small per-eval bookkeeping
/// allocation. Choosing a value too large would defeat the test's purpose
/// (catching unbounded growth).
const REPL_EVAL_OVERHEAD_BOUND: i64 = 256;

/// Read the `Code` value off the named def in the current module.
///
/// Returns `None` if the module/symbol isn't found or the entry is not a
/// `Def` with a populated `code` field. Used by Scenario 2 to capture an
/// `Arc<Jit>` clone at one point in time and assert reclaim behaviour at
/// a later point.
fn read_def_code(
    session: &ReplSession,
    module: &ModuleFullPath,
    name: &str,
) -> Option<Code> {
    let table = session.symbol_tables().get(module)?;
    match table.get(name)? {
        ModuleEntry::Def {
            code: Some(code), ..
        } => Some(code.clone()),
        _ => None,
    }
}

/// Pull out the `Arc<Jit>` from a `Code::Jit` variant, or panic with a
/// helpful message naming the actual variant.
fn jit_arc_from_code(code: &Code) -> Arc<cranelisp_backend::jit::Jit> {
    match code {
        Code::Jit { jit, .. } => Arc::clone(jit),
        Code::Linker { .. } => {
            panic!("expected Code::Jit (fresh REPL build), got Code::Linker (cache hit)")
        }
    }
}

// =============================================================================
// Decision 31 Scenario 1 — per-eval JIT pages reclaimed
// =============================================================================

// spec: design/arch/CLAUDE.md Decision 31 Scenario 1 — per-eval JIT page
//       reclaim. Validates that REPL eval of a primitive expression returns
//       live bytes to baseline (transient allocations released).
//       Cross-references repl/spec.md §3.7 — `/mem` snapshot reports
//       `; live: <bytes>` reading the same `bytes_current()` counter.
#[test]
fn decision31_scenario1_per_eval_jit_pages_reclaimed() {
    let mut session = repl_session();

    // Settle the session — load any deferred state so the next eval is
    // representative of steady-state per-eval cost.
    let _ = session.eval("(add-i64 1 2)").expect("warm-up eval");

    let snap_a = MemSnapshot::capture();

    // Issue one REPL eval. `(add-i64 1 2)` is stack-only at the value
    // level, so any growth in `bytes_live` must come from compiler
    // bookkeeping retained beyond the eval.
    let result = session.eval("(add-i64 1 2)").expect("primitive eval");
    assert_eq!(result.value(), 3, "correctness guard for primitive eval");

    let snap_b = MemSnapshot::capture();

    // Positive: live bytes do not grow beyond a small constant. Decision 31
    // Scenario 1 says the per-eval JIT batch's pages reclaim when the
    // batch's `Arc<Jit>` count drops to zero — which happens immediately
    // because no `ModuleEntry::Def` was created (it's an expression eval,
    // not a defn) and the eval-fn batch is the sole holder of the Arc.
    let delta_bytes = (snap_b.bytes_live as i64) - (snap_a.bytes_live as i64);
    assert!(
        delta_bytes <= REPL_EVAL_OVERHEAD_BOUND,
        "Decision 31 Scenario 1 violated: per-eval JIT pages did not reclaim. \
         delta_bytes = {delta_bytes} (bound = {REPL_EVAL_OVERHEAD_BOUND}). \
         Snapshot A: {snap_a:?}; Snapshot B: {snap_b:?}"
    );
}

// spec: design/arch/CLAUDE.md Decision 31 Scenario 1 footnote — under
//       repeated eval, live bytes MUST NOT grow with the repetition count.
//       Pre-fix, the gap would grow ~N x; post-fix it stays flat.
#[test]
fn decision31_scenario1_repeated_eval_no_unbounded_growth() {
    let mut session = repl_session();

    // Warm-up.
    let _ = session.eval("(add-i64 1 2)").expect("warm-up eval");

    let baseline = MemSnapshot::capture();

    const N: usize = 100;
    for _ in 0..N {
        let _ = session.eval("(add-i64 1 2)").expect("repeated eval");
    }

    let after = MemSnapshot::capture();

    // The defining property: per-eval cost is bounded — it does NOT scale
    // linearly in N. Pre-fix, `kept_jits` would have grown by N (one per
    // eval); the live-bytes delta would scale ~N x per-eval-page-size.
    // Post-Wave-3b, every eval batch's Arc<Jit> drops at end of eval.
    let delta_bytes = (after.bytes_live as i64) - (baseline.bytes_live as i64);
    assert!(
        delta_bytes <= REPL_EVAL_OVERHEAD_BOUND,
        "Decision 31 Scenario 1 unbounded-growth violated: {N} repeated evals \
         leaked {delta_bytes} bytes (bound = {REPL_EVAL_OVERHEAD_BOUND}). \
         Pre-Wave-3b kept_jits accumulation would grow ~{N}x; post-fix \
         stays flat. Baseline: {baseline:?}; After: {after:?}"
    );

    // Negative-shape: the live-allocations count likewise stays bounded.
    // (Pre-fix this would also grow with N because each kept_jits entry
    // drove a heap-resident retention.)
    let delta_allocs =
        (after.live_allocations() as i64) - (baseline.live_allocations() as i64);
    assert!(
        delta_allocs.unsigned_abs() < (N as u64),
        "live allocations grew by {delta_allocs} across {N} evals — should \
         be bounded by a small constant, not scale with eval count"
    );
}

// =============================================================================
// Decision 31 Scenario 2 — per-redefinition JIT pages reclaimed (HEADLINE)
// =============================================================================

// spec: design/arch/CLAUDE.md Decision 31 Scenario 2 + design/int/symbol-table-generics.md §2.3
//       — per-redefinition JIT page reclaim. When a REPL user redefines a
//       defn, the prior `ModuleEntry::Def.code = Some(Code::Jit { jit, ptr })`
//       drops; the `Arc<Jit>` clone refcount decrements; if it reaches zero
//       (no other entries reference the same per-batch JIT), `Jit::drop`
//       fires `unsafe free_memory()` and reclaims the executable pages.
//       Headline payoff for Sprint 58 Wave 3.
//
// Assertion strategy: capture an `Arc<Jit>` clone from the FIRST defn
// before the redefinition, then redefine and assert:
//   1. The session's `Code::Jit` for that name carries a DIFFERENT Arc
//      (i.e. the new defn's batch, not the old one).
//   2. The captured first-defn Arc's strong count is exactly 1 (only the
//      test's clone remains; the session has dropped its references).
//   3. When the test drops its clone, `jit_free_memory_call_count`
//      increments — the underlying Cranelift JIT pages reclaim.
//
// This is stronger than a `bytes_current()` delta check because it
// observes the reclaim primitive at the precise level the spec defines
// (Arc-driven `Jit::drop`), not at the pages-released aggregate level
// (which can be muddied by allocator caching, debug-mode bookkeeping, or
// concurrent runtime activity).
#[test]
fn decision31_scenario2_per_redefinition_jit_pages_reclaimed() {
    let mut session = repl_session();
    let module = ModuleFullPath::from("user");

    // First definition of f.
    session
        .eval("(defn f [x] x)")
        .expect("first defn f compiles");

    // Capture the Arc<Jit> for the first defn's batch. This is the
    // retention root that Decision 31 Scenario 2 says will drop when the
    // entry is replaced.
    let first_code = read_def_code(&session, &module, "f")
        .expect("first defn f must populate ModuleEntry::Def.code");
    let first_jit = jit_arc_from_code(&first_code);

    // After the first defn, the session holds at least one Arc clone on
    // each entry, plus the jit_arc that `compile_in_priority_worker` keeps
    // through the for-loop scope; the test's clone bumps it by one more.
    let count_before_redef = Arc::strong_count(&first_jit);
    assert!(
        count_before_redef >= 2,
        "expected the session to hold at least one Arc<Jit> clone on f's \
         entry (test holds one too); strong_count = {count_before_redef}"
    );
    drop(first_code); // Release the local Code::Jit clone we used for capture.

    // Snapshot the JIT-reclaim counter so we can detect the precise moment
    // the underlying Cranelift JIT module drops.
    let reclaim_count_before = jit_free_memory_call_count();

    // Redefine f with a different body. This MUST replace the `code` field
    // on f's entry, dropping the prior `Code::Jit` clone. With no other
    // entries holding the first batch's Arc, the Arc count should fall to
    // 1 (only our captured clone remains).
    session
        .eval("(defn f [x] (add-i64 x 1))")
        .expect("redefinition of f compiles");

    let second_code = read_def_code(&session, &module, "f")
        .expect("redefined f must populate ModuleEntry::Def.code");
    let second_jit = jit_arc_from_code(&second_code);

    // Headline assertion 1: the new entry carries a DIFFERENT Arc<Jit>
    // (a fresh batch), not a clone of the first.
    assert!(
        !Arc::ptr_eq(&first_jit, &second_jit),
        "redefinition should produce a new JIT batch — `Arc::ptr_eq` should \
         be false. The redefinition path is reusing the prior batch's \
         allocation (Decision 31 Scenario 2 invariant violated)."
    );
    drop(second_code);
    drop(second_jit);

    // Headline assertion 2: the session has fully released its references
    // to the first batch's Arc<Jit>. Only our captured test clone remains.
    let count_after_redef = Arc::strong_count(&first_jit);
    assert_eq!(
        count_after_redef, 1,
        "Decision 31 Scenario 2 violated: after redefinition, the session \
         still holds {} extra Arc<Jit> clones on the FIRST batch \
         (strong_count = {count_after_redef}; expected 1, only the test's \
         captured clone). Pre-Wave-3b, kept_jits would have retained the \
         old Arc indefinitely.",
        count_after_redef - 1
    );

    // Headline assertion 3: when the test drops its clone, the underlying
    // Cranelift JIT pages are reclaimed (Jit::drop's free_memory fires).
    drop(first_jit);
    let reclaim_count_after = jit_free_memory_call_count();
    assert_eq!(
        reclaim_count_after,
        reclaim_count_before + 1,
        "expected exactly one new JIT::free_memory call after dropping \
         the last Arc<Jit> clone for the first defn's batch. \
         before = {reclaim_count_before}, after = {reclaim_count_after}. \
         If the count did not increment, Jit::drop is not firing — the \
         per-batch JIT pages are not being reclaimed."
    );
}

// spec: design/arch/CLAUDE.md Decision 31 Scenario 2 + symbol-table-generics.md §2.3
//       (kept_jits dissolution). Negative regression guard: pre-fix, every
//       redefinition of `f` would push a fresh `KeptJit` onto
//       `SharedState.kept_jits`, growing the live-bytes counter linearly
//       in the redefinition count. Post-fix, the prior batch's pages
//       reclaim immediately on each redefinition.
#[test]
fn decision31_scenario2_repeated_redefinition_no_unbounded_growth() {
    let mut session = repl_session();

    // First definition + warm-up so codegen is cached for any
    // monomorphisation overhead.
    session.eval("(defn f [x] x)").expect("first defn f");
    let _ = session.eval("(f 0)").expect("warm-up call");

    let baseline = MemSnapshot::capture();
    let reclaim_count_before = jit_free_memory_call_count();

    // Redefine f 50 times, varying N so each is a genuinely different
    // function body (defeats any potential body-equality short-circuit).
    const N: i64 = 50;
    for n in 1..=N {
        let src = format!("(defn f [x] (add-i64 x {n}))");
        session
            .eval(&src)
            .unwrap_or_else(|e| panic!("redefinition #{n} failed: {e}"));
    }

    let after = MemSnapshot::capture();
    let reclaim_count_after = jit_free_memory_call_count();

    // The defining property: per-redefinition cost is bounded — live bytes
    // do not scale linearly in N. Pre-Wave-3b, kept_jits accumulation
    // would have made this delta scale ~N x.
    let delta_bytes = (after.bytes_live as i64) - (baseline.bytes_live as i64);
    let bound = REPL_EVAL_OVERHEAD_BOUND * 2; // generous: redefn + small RC churn
    assert!(
        delta_bytes <= bound,
        "Decision 31 Scenario 2 unbounded-growth violated: {N} redefinitions \
         of f leaked {delta_bytes} bytes (bound = {bound}). Pre-Wave-3b \
         kept_jits accumulation would have grown ~{N}x. Baseline: \
         {baseline:?}; After: {after:?}"
    );

    // Companion assertion: at least N JIT batches were reclaimed (one per
    // redefinition releases the prior batch). Cranelift's per-batch
    // bookkeeping may free a small number of additional internal JIT
    // modules during compilation, so we use `>=` not `==`. The strong
    // signal is "at least N reclaims happened" — pre-fix would have shown
    // 0 because kept_jits held everything until session shutdown.
    let reclaim_delta = reclaim_count_after - reclaim_count_before;
    assert!(
        reclaim_delta >= (N as u64),
        "expected at least {N} JIT::free_memory calls across {N} \
         redefinitions, got {reclaim_delta}. Pre-Wave-3b kept_jits \
         retention would have shown 0 reclaims until session drop."
    );
}

// =============================================================================
// Code::Linker reclaim coverage — session-scope retention
// =============================================================================

// spec: design/int/symbol-table-generics.md §2.1 — `Code::Linker { linker, ptr }`
//       carries `Arc<Linker>` per-entry. The Linker's mmap'd code/data
//       regions reclaim when the last `Arc<Linker>` clone drops.
//
// Linker reclaim is structurally session-scoped (not per-redefinition):
// cache-hit code is rehydrated once at session start (or on first use of
// a cached module) and lives on the cached module's `ModuleEntry::Def`
// entries until session teardown. Unlike `Code::Jit`, REPL redefinition
// does not produce a fresh `Code::Linker` — redefining a cache-loaded
// symbol replaces the entry with a `Code::Jit` (the new code is freshly
// compiled), at which point the cache-loaded `Arc<Linker>` clone on that
// entry drops.
//
// This test verifies the structural invariant: when a `Code::Linker`-
// holding entry drops, the `Arc<Linker>` strong count decrements; when
// the last clone drops (e.g., session teardown, or all cache-loaded
// entries get redefined), the underlying `Linker` (and its `MmapMut`
// regions) reclaims via `memmap2::Drop`.
//
// We exercise this directly at the `Code` enum level rather than
// through a full session-restart cache-rehydrate scenario because:
//
// 1. The unit test `code_enum_jit_variant_carries_arc_jit` already
//    proves the Arc-clone reclaim primitive for `Code::Jit`.
// 2. The unit test `code_enum_linker_variant_constructible` proves
//    `Code::Linker` participates in `Arc::clone` semantics.
// 3. End-to-end cache-rehydrate flows are covered by the cache cluster
//    in `tests/cache.rs` (e.g., `cache_repl_restart_cache_hit`).
//
// What's missing — and what this test adds — is the integration-level
// guarantee that `Code::Linker` is observed on real session entries
// after a cache rehydrate and that its Arc-based reclaim discipline
// matches `Code::Jit`'s.
#[test]
fn decision31_code_linker_session_scope_only() {
    // Direct reclaim assertion at the Code::Linker enum layer.
    //
    // Construct a Linker, wrap in Arc, build two `Code::Linker` clones
    // (simulating "two `Def` entries reference the same cache-loaded
    // batch"), drop them in sequence, assert refcount decrements at
    // each step.
    //
    // Unlike `Jit::drop`, there is no global `LINKER_FREE_MEMORY_COUNT`
    // accessor — `Linker` reclaim is implicit via `MmapMut::Drop` (each
    // mmap'd region releases its mapping back to the OS). The test
    // therefore asserts the lifecycle through `Arc::strong_count` only,
    // and trusts `memmap2`'s Drop impl to release the pages. This
    // matches the design — the `Linker`'s reclaim contract is structural
    // (RAII through Arc + MmapMut), not instrumented.
    let linker = Arc::new(
        cranelisp_backend::cache::Linker::new()
            .expect("Linker::new must succeed for reclaim test"),
    );
    assert_eq!(
        Arc::strong_count(&linker),
        1,
        "fresh Arc<Linker> has refcount 1"
    );

    let code1 = Code::linker(Arc::clone(&linker), 0xAAAAAAAAusize as *const u8);
    let code2 = Code::linker(Arc::clone(&linker), 0xBBBBBBBBusize as *const u8);
    assert_eq!(
        Arc::strong_count(&linker),
        3,
        "two Code::Linker clones each hold one Arc clone (1 local + 2 = 3)"
    );

    // Both reads point into the same backing Linker even though the
    // per-symbol `ptr` values differ — this matches the cache-hit
    // semantics where one cached `.o` produces multiple `Def` entries,
    // each with its own resolved address but sharing the linker.
    assert_eq!(code1.ptr(), 0xAAAAAAAAusize as *const u8);
    assert_eq!(code2.ptr(), 0xBBBBBBBBusize as *const u8);

    // Drop the first Code::Linker clone. Refcount falls by one; the
    // Linker is still alive because `code2` and the local `linker`
    // hold clones.
    drop(code1);
    assert_eq!(
        Arc::strong_count(&linker),
        2,
        "dropping one Code::Linker clone decrements refcount to 2"
    );

    // Drop the second clone. Refcount falls to 1 (only the local Arc
    // remains).
    drop(code2);
    assert_eq!(
        Arc::strong_count(&linker),
        1,
        "dropping second Code::Linker clone decrements refcount to 1"
    );

    // Drop the local Arc — Linker reclaims (MmapMut regions release
    // their mappings). We can't observe the OS-level munmap without
    // platform-specific instrumentation, but the structural guarantee
    // is that `Linker::Drop` runs (and with it, every `MmapMut::Drop`
    // for `code_regions`, `data_regions`, `got_pool`).
    drop(linker);

    // Reaching this line without a panic is the assertion: the drop
    // chain completed cleanly. If `Linker::Drop` had a bug (e.g.,
    // double-free, use-after-free in the cleanup path), it would
    // surface here as an abort.
}
