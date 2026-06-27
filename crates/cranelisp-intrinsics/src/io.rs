//! IO trampoline — iterative evaluation of IO task trees.
//!
//! The IO model is a deferred-execution system. User code builds IO trees
//! by calling constructors (Pure, Effect) and the `bind` primitive. The
//! trampoline walks the tree iteratively with an explicit continuation
//! stack, avoiding stack overflow for arbitrarily deep bind chains.
//!
//! See `design/backend/io-trampoline.md` for the full design.

use cranelisp_platform::{IO_TAG_BIND, IO_TAG_EFFECT, IO_TAG_PAR, IO_TAG_PURE};
use cranelisp_types::HeapHeader;

use crate::alloc::alloc_with_rc;
use crate::io_observer::{self, IoEvent, IoEventTag};

/// Byte offset of the tag field from the base pointer.
const TAG_OFFSET: isize = HeapHeader::SIZE as isize; // 16

/// Byte offset of the first field from the base pointer.
const FIELD_0_OFFSET: isize = TAG_OFFSET + 8; // 24

/// Byte offset of the second field from the base pointer.
const FIELD_1_OFFSET: isize = FIELD_0_OFFSET + 8; // 32

/// Byte offset of the third field from the base pointer.
///
/// On an `IO_TAG_EFFECT` node this is the baked fn-name handle (the fourth
/// `i64` of the payload, ABI v4 — the node-widen from 24 → 32 bytes, FIXME
/// 0327, the dispatch funnel). The DLL's `CLIO::effect*` reserves it as null;
/// the backend stamps the statically-known fn-name handle here after the
/// platform-fn call returns (step 2). The fault guard reads it (step 3) so a
/// fault in foreign code can surface `PlatformError::DispatchError { fn_name }`.
/// A null handle ⇒ `fn_name: "<unknown>"`. Step 1 (the node-widen) leaves this
/// field reserved-but-unread; it is named here so steps 2/3 read it
/// consistently.
///
/// Derived from the named constants (NOT hard-coded 40): the node base is the
/// `HeapHeader`, and `cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET` is the
/// field's offset within the payload.
const FIELD_2_OFFSET: isize =
    HeapHeader::SIZE as isize + cranelisp_platform::IO_EFFECT_FN_NAME_OFFSET as isize; // 16 + 24 = 40

/// Byte offset of the code pointer within a closure from the base pointer.
/// Closure layout: [header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]
const CLOSURE_CODE_PTR_OFFSET: isize = HeapHeader::SIZE as isize; // 16

/// Force an IO task tree to completion (extern "C" entry point).
///
/// Takes a base pointer to a heap-allocated IO node (Pure/Effect/Bind/Par).
/// Returns the final result value (i64).
///
/// Decision 24 (Sprint 56 Step 2c): consuming convention — the top-level IO
/// tree handed to `cranelisp_run_io` is released via
/// `crate::drop::consume_io_tree` after evaluation. The trampoline itself
/// is non-consuming of its input tree (`io_ptr`); it walks the caller's
/// tree read-only. Any IO ADT node produced INSIDE the trampoline by a
/// continuation (Sprint 57 Wave 3 fix per `design/backend/ring2-rc.md`
/// §3.5) is shallow-dec'd inline via `drop::dec_shallow_io`, so continuation
/// intermediates do not leak. Closures reached via the caller's tree are
/// left alone — `consume_io_tree` walks and dec's them transitively.
/// Closures produced INSIDE the trampoline by a continuation (continuation
/// returns a Bind whose cont field is fresh) are also inline-dec'd by the
/// trampoline.
///
/// # Safety
/// `io_ptr` must be a valid base pointer to an IO node with rc > 0.
/// The IO tree must remain live for the duration of this call.
///
/// Linker symbol is `_cranelisp_run_io` (default Rust name via no_mangle) —
/// the standalone startup stub (`__startup.o`) calls into this directly by
/// the Rust function name to drive the IO trampoline, so the export_name
/// MUST remain the unaliased Rust name. JIT side registers it under
/// `runtime/run_io` via function pointer (not linker name).
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_run_io(io_ptr: i64) -> i64 {
    let result = drive_io(io_ptr);
    // Decision 24: release the caller's tree. `consume_io_tree` transitively
    // walks Pure/Effect/Bind/Par and dec's every heap-typed sub-ref
    // (including continuation closures still owned by Bind nodes).
    // Intermediate nodes produced by the trampoline have already been
    // released by `run_io_trampoline` itself — `io_ptr` is untouched by
    // the trampoline, so this dec is not a double-free.
    crate::drop::consume_io_tree(io_ptr);
    result
}

/// Drive an IO tree to its result value — the cfg-split between the sync
/// trampoline (the default / `--link` path) and the async-substrate executor.
///
/// **Feature off (the default, byte-identical):** today's synchronous
/// [`run_io_trampoline`] — unchanged. The exe-bundle / `--link` build never
/// enables `concurrency-runtime`, so a linked binary links no executor.
///
/// **Feature on:** the async trampoline twin is `block_on`'d on the host
/// reactor's single-future executor ([`crate::reactor::block_on_reactor`]). The
/// `Pure` / `Bind` / thunk-`Effect` / `Par` node walk is the proven sync stepper
/// (result-equivalent — thunk effects force synchronously, they do not suspend);
/// the genuine await boundary ([`crate::reactor::EffectPoll`]) + the `Par`-async
/// overlap ([`crate::reactor::join_io_leaves`]) are exercised by the hand-written
/// demo leaves (App. B "Demo leaf"). Wiring real poll-shape effect *nodes*
/// through the await boundary is the deferred backend slice (the
/// `declare_platform!` poll-emission), so the minimal twin's node walk stays
/// synchronous while the executor + reactor + await-boundary mechanism are live
/// and demonstrated.
#[cfg(not(feature = "concurrency-runtime"))]
#[inline]
fn drive_io(io_ptr: i64) -> i64 {
    run_io_trampoline(io_ptr)
}

#[cfg(feature = "concurrency-runtime")]
fn drive_io(io_ptr: i64) -> i64 {
    crate::reactor::block_on_reactor(async |_host| run_io_trampoline_inner_async(io_ptr).await)
        .expect("reactor init failed")
}

/// The async twin of [`run_io_trampoline`] (App. B step 2c). An `async fn` so it
/// is driven on the reactor executor.
///
/// In the minimal slice the body is fully synchronous (the node walk delegates to
/// the proven sync stepper; poll-shape await nodes are a later backend slice), so
/// it delegates to [`run_io_trampoline`] outright — reusing its
/// `TrampolineEnter`/`TrampolineExit` bookend rather than re-emitting an identical
/// one (I3 / Principle 7 — single source of truth; the IO trace stays identical
/// across the cfg-split because it IS the same bookend). When the `.await` Effect
/// arm lands, this regains a real async body around that same shared bookend.
#[cfg(feature = "concurrency-runtime")]
async fn run_io_trampoline_inner_async(io_ptr: i64) -> i64 {
    run_io_trampoline(io_ptr)
}

/// Core trampoline implementation. Separate from the extern "C" wrapper
/// so that panics (on invalid tags) can unwind normally in tests.
///
/// The trampoline is iterative with an explicit continuation stack.
///
/// ## RC balance (Sprint 57 Wave 3; §3.5)
///
/// The trampoline is non-consuming of its input `io_ptr`: nodes reachable
/// through the caller's tree (Bind spine, sub-branches, sub-continuations)
/// are left untouched. The caller (`cranelisp_run_io`, or a Rust-level
/// direct caller) owns the tree and is responsible for releasing it via
/// `drop::consume_io_tree` (or equivalent).
///
/// However, the trampoline IS consuming of any IO ADT node it produces
/// during the walk — specifically, nodes allocated by a continuation's
/// body. A continuation `(fn [x] (pure (+ x 1)))` allocates a fresh Pure
/// when invoked. That Pure becomes the new `current` and, as the
/// trampoline steps further, is replaced — at which point it is
/// shallow-dec'd. Without this inline dec the continuation-produced nodes
/// would leak (O(N) for N Bind steps).
///
/// A `current_is_fresh` flag tracks whether the current node belongs to
/// the caller's tree (initially) or to a continuation-produced subtree
/// (after the first `call_continuation`). It never flips back to false:
/// once we step into a continuation-produced subtree, its sub-nodes
/// (reached via Bind's inner field, Par's branch fields, etc.) are also
/// owned by this trampoline. Closures popped from `cont_stack` that were
/// captured from a fresh Bind are consumed; closures from the caller's
/// tree are left alone.
pub fn run_io_trampoline(io_ptr: i64) -> i64 {
    io_observer::emit(
        IoEventTag::TrampolineEnter,
        &IoEvent::TrampolineEnter { io_ptr },
    );
    let result = run_io_trampoline_inner(io_ptr);
    io_observer::emit(
        IoEventTag::TrampolineExit,
        &IoEvent::TrampolineExit { result },
    );
    result
}

/// The walk position after a `Pure`/`Effect`/`Par` arm has produced a result
/// value and consulted the continuation stack.
enum Step {
    /// The result was fed to a popped continuation; resume the loop on the
    /// continuation-produced node (always a fresh subtree).
    Advance(i64),
    /// The continuation stack was empty; the walk is complete with this value.
    Finish(i64),
}

/// Read the `i64` tag field of an IO node at `node`.
///
/// # Safety
/// `node` must be a valid IO-node base pointer (rc > 0).
#[inline]
unsafe fn read_node_tag(node: i64) -> i64 {
    unsafe { crate::heap_access::read_i64(node, TAG_OFFSET) }
}

/// Read the `i64` field at `field_offset` of an IO node at `node`.
///
/// # Safety
/// `node` must be a valid IO-node base pointer with the given field present.
#[inline]
unsafe fn read_node_field(node: i64, field_offset: isize) -> i64 {
    unsafe { crate::heap_access::read_i64(node, field_offset) }
}

/// Feed `value` (the result a `Pure`/`Effect`/`Par` arm just produced) to the
/// next continuation, or finish the walk.
///
/// Shared by the three value-producing arms — the "pop a continuation; release
/// the just-finished node if it was fresh; either invoke the continuation or
/// return" sequence that was open-coded identically three times. Returns
/// [`Step::Advance`] with the continuation-produced node (now a fresh subtree)
/// or [`Step::Finish`] with `value` when no continuation remains.
fn feed_continuation(
    cont_stack: &mut Vec<(i64, bool)>,
    current: i64,
    current_is_fresh: bool,
    value: i64,
) -> Step {
    match cont_stack.pop() {
        Some((cont_ptr, cont_is_fresh)) => {
            io_observer::emit(
                IoEventTag::ContPop,
                &IoEvent::Cont {
                    cont_ptr,
                    is_fresh: cont_is_fresh,
                    new_depth: cont_stack.len() as u32,
                },
            );
            // Releasing the just-finished node: shallow-dec it if we produced
            // it ourselves (fresh subtree). A caller-tree node is left for the
            // caller's post-return `consume_io_tree`.
            if current_is_fresh {
                crate::drop::dec_shallow_io(current);
            }
            // Same rule for the closure we're about to invoke: consume it only
            // if it was part of a fresh Bind.
            let new_io = call_continuation(cont_ptr, value, cont_is_fresh);
            io_observer::emit(
                IoEventTag::BindExit,
                &IoEvent::BindExit { new_current: new_io },
            );
            Step::Advance(new_io)
        }
        None => {
            // Final node; shallow-dec only if fresh.
            if current_is_fresh {
                crate::drop::dec_shallow_io(current);
            }
            Step::Finish(value)
        }
    }
}

/// Outcome of forcing an `IO_TAG_EFFECT` node under the fault guard.
enum EffectStep {
    /// The thunk produced this value; proceed to the continuation.
    Value(i64),
    /// A fault was captured in the dispatch-fault slot; abort the trampoline
    /// with the sentinel (int reads the slot, not the return value).
    Aborted,
}

/// Force an `IO_TAG_EFFECT` node's thunk under the platform fault guard
/// (FIXME 0327, step 3 — the dispatch funnel).
///
/// Reads the thunk + resource token + baked fn-name from the node, emits the
/// `PlatformEffect` event, then forces the thunk via
/// `io_guard::force_effect_thunk_protected`. A fault in foreign platform code
/// (Rust panic or SIGFPE/SIGILL/SIGBUS/SIGSEGV) is captured into the
/// dispatch-fault slot (paired with the fn-name) for int to compose into
/// `PlatformError::DispatchError`. The happy path is identical to the former
/// unguarded `call_effect_thunk(thunk_ptr)`.
fn force_effect_node(node: i64) -> EffectStep {
    // SAFETY: `node` is the live `current` Effect node base pointer; its
    // thunk/token fields are within its payload.
    let thunk_ptr = unsafe { read_node_field(node, FIELD_0_OFFSET) };
    let resource_token = unsafe { read_node_field(node, FIELD_1_OFFSET) };
    // Scheduling class is not currently stored on Effect nodes at runtime — the
    // class attaches to platform symbols at registration time (see
    // `cranelisp-platform::SchedulingClass` and `PlatformFn.scheduling_class`).
    // At the trampoline site we do not have a back-reference to the symbol. Emit
    // 0 as a placeholder; Slice 4 can either plumb the class through Effect
    // construction or consume it via /int's scheduler trace.
    //
    // FIXME(/backend): consider threading SchedulingClass into the Effect node
    // payload (extra field) so trampoline events carry the real class without
    // needing a cross-trace correlation. Deferred pending Slice 4 evidence.
    io_observer::emit(
        IoEventTag::PlatformEffect,
        &IoEvent::PlatformEffect {
            thunk_ptr,
            resource_token,
            scheduling_class: 0,
        },
    );
    let fn_name = read_effect_fn_name(node);
    // SAFETY: `thunk_ptr` is the Effect node's field-0 — a valid not-yet-forced
    // double-boxed thunk produced by `CLIO::effect*`.
    match unsafe { crate::io_guard::force_effect_thunk_protected(thunk_ptr, &fn_name) } {
        crate::io_guard::ForceOutcome::Value(v) => EffectStep::Value(v),
        crate::io_guard::ForceOutcome::Faulted => EffectStep::Aborted,
    }
}

/// Read a `Par` node's `count` and branch IO pointers.
///
/// Par node layout: `[header(16) | tag(8) | count(8) | branch_0(8) | …]`.
///
/// # Safety
/// `node` must be a valid `IO_TAG_PAR` node base pointer.
unsafe fn read_par_branches(node: i64) -> Vec<i64> {
    let count = unsafe { read_node_field(node, FIELD_0_OFFSET) } as usize;
    (0..count)
        .map(|i| unsafe { read_node_field(node, FIELD_1_OFFSET + (i as isize) * 8) })
        .collect()
}

/// Run a `Par` node's branches, marshal their results into a fresh heap results
/// buffer, and return its base pointer (the value fed to the continuation).
///
/// Each branch recursion is itself a non-consuming trampoline run on a
/// caller-tree or fresh-tree branch — it dec's only its own fresh intermediates.
/// The branches themselves are left live for later `consume_io_tree` (caller
/// tree) or shallow-dec'd at the enclosing Par level (§3.5.6 detail unchanged).
fn run_par_node(parent_ptr: i64) -> i64 {
    // SAFETY: `parent_ptr` is the live `current` Par node base pointer.
    let branch_ptrs = unsafe { read_par_branches(parent_ptr) };
    let count = branch_ptrs.len();
    let results = dispatch_par_branches_with_trace(&branch_ptrs, parent_ptr);
    io_observer::emit(
        IoEventTag::ParJoin,
        &IoEvent::ParJoin {
            parent_ptr,
            count: count as u32,
        },
    );

    // Allocate results buffer via alloc_with_rc so the continuation can dec it
    // when done. Results stored at FIELD_0_OFFSET + i*8 (offsets 24, 32, 40, …)
    // matching HeapAdt::field_offset(i).
    let results_buf = alloc_with_rc(8 + count * 8) as i64; // payload: padding(8) + N*8
    for (i, &val) in results.iter().enumerate() {
        // SAFETY: `results_buf` was just allocated with `count` field slots.
        unsafe { crate::heap_access::write_i64(results_buf, FIELD_0_OFFSET + (i as isize) * 8, val) };
    }
    results_buf
}

/// Inner loop — all state-machine instrumentation lives here; the outer
/// `run_io_trampoline` wraps it solely to emit enter/exit bookends. Each node
/// arm delegates to a named helper (`force_effect_node`, `run_par_node`) and the
/// shared `feed_continuation` step; the loop body is the dispatcher.
fn run_io_trampoline_inner(io_ptr: i64) -> i64 {
    let mut cont_stack: Vec<(i64, bool)> = Vec::new(); // (cont_ptr, is_fresh)
    let mut current: i64 = io_ptr;
    let mut current_is_fresh: bool = false;

    loop {
        let tag = unsafe { read_node_tag(current) };

        // The value a Pure/Effect/Par arm produces, ready to feed to the next
        // continuation via the shared `feed_continuation` step. Bind descends
        // in-place and `continue`s without producing a value.
        let produced: i64 = match tag {
            t if t == IO_TAG_PURE => {
                let val = unsafe { read_node_field(current, FIELD_0_OFFSET) };
                io_observer::emit(
                    IoEventTag::PureStep,
                    &IoEvent::PureStep { value: val, is_fresh: current_is_fresh },
                );
                val
            }
            t if t == IO_TAG_EFFECT => match force_effect_node(current) {
                EffectStep::Value(v) => v,
                // Abort: the fault is in the dispatch-fault slot. Return the
                // sentinel (0), mirroring the `runtime_panic` convention.
                EffectStep::Aborted => return 0,
            },
            t if t == IO_TAG_BIND => {
                let inner = unsafe { read_node_field(current, FIELD_0_OFFSET) };
                let cont = unsafe { read_node_field(current, FIELD_1_OFFSET) };
                io_observer::emit(
                    IoEventTag::BindEnter,
                    &IoEvent::BindEnter {
                        inner_ptr: inner,
                        cont_ptr: cont,
                        is_fresh: current_is_fresh,
                    },
                );
                // The Bind's cont pointer inherits the freshness of the Bind
                // node: caller-tree Binds hold caller-tree conts; fresh Binds
                // (produced by an outer continuation) hold fresh conts.
                cont_stack.push((cont, current_is_fresh));
                io_observer::emit(
                    IoEventTag::ContPush,
                    &IoEvent::Cont {
                        cont_ptr: cont,
                        is_fresh: current_is_fresh,
                        new_depth: cont_stack.len() as u32,
                    },
                );
                if current_is_fresh {
                    // Fresh Bind: shallow-dec the outer Bind alloc; inner
                    // ownership transfers to `current` and remains fresh.
                    crate::drop::dec_shallow_io(current);
                }
                // current_is_fresh stays as-is: if we were fresh, the inner
                // (allocated by the same continuation) is also fresh; if we
                // were not, we're still descending the caller's tree.
                current = inner;
                continue;
            }
            t if t == IO_TAG_PAR => run_par_node(current),
            _ => panic!("cranelisp_run_io: unknown IO tag {tag}"),
        };

        match feed_continuation(&mut cont_stack, current, current_is_fresh, produced) {
            Step::Advance(new_io) => {
                // The continuation just ran user code (`call_continuation`). If
                // that user code raised a runtime error (e.g. div-by-zero via
                // `runtime_panic`) or a platform-dispatch fault, the closure
                // returned the panic-path sentinel `0` — `new_io` is NOT a valid
                // IO node. Stop the walk and return the sentinel WITHOUT
                // dereferencing `new_io` (which would `read_node_tag(0)` →
                // null-deref → SIGSEGV). The slot is left SET (peeked, not
                // taken) so the HOST surfaces it — the trampoline is not the
                // surfacing point (FIXME 0401). Mirrors the
                // `EffectStep::Aborted => return 0` convention above.
                if crate::panic::has_runtime_error() || crate::panic::has_dispatch_fault() {
                    return 0;
                }
                current = new_io;
                current_is_fresh = true;
            }
            Step::Finish(value) => return value,
        }
    }
}

/// Call a continuation closure with a value, returning the new IO tree pointer.
///
/// Continuations are Cranelisp closures with standard HeapClosure layout:
/// `[header(16) | code_ptr(8) | drop_glue_ptr(8) | captures...]`
///
/// The code_ptr has signature `extern "C" fn(env_ptr: i64, val: i64) -> i64`.
/// The closure pointer itself is passed as the first argument (env_ptr).
///
/// If `cont_is_fresh` is true (the closure belonged to a fresh, trampoline-
/// produced Bind), the closure is consumed after invocation via
/// `drop::consume_closure` so the continuation's one-shot allocation does
/// not leak. If false, the closure is part of the caller's tree and left
/// alone — the caller's post-return `consume_io_tree` walk will release it.
fn call_continuation(cont_ptr: i64, val: i64, cont_is_fresh: bool) -> i64 {
    let code_ptr = unsafe { crate::heap_access::read_i64(cont_ptr, CLOSURE_CODE_PTR_OFFSET) };
    let call: extern "C" fn(i64, i64) -> i64 =
        unsafe { std::mem::transmute(code_ptr as *const ()) };
    let new_io = call(cont_ptr, val);
    if cont_is_fresh {
        // Continuation-owned closure: release it now. `consume_closure`
        // invokes the embedded drop glue on last-ref and deallocs.
        crate::drop::consume_closure(cont_ptr);
    }
    new_io
}

// --- Par dispatch with resource token serialization ---

/// Read the resource token from an IO node.
///
/// Effect nodes store the token at FIELD_1_OFFSET (offset 32).
/// Non-Effect nodes (Pure, Bind, Par) return 0 (unrestricted).
fn read_resource_token(io_ptr: i64) -> i64 {
    let tag = unsafe { crate::heap_access::read_i64(io_ptr, TAG_OFFSET) };
    if tag == IO_TAG_EFFECT {
        unsafe { crate::heap_access::read_i64(io_ptr, FIELD_1_OFFSET) }
    } else {
        0
    }
}

/// Read the baked platform fn-name from an `IO_TAG_EFFECT` node's fourth field
/// (FIELD_2_OFFSET, ABI v4 — FIXME 0327 the dispatch funnel).
///
/// The backend stamps field-3 with a pointer to a NUL-terminated UTF-8 C-string
/// (the `exe.rs::define_cstr_data` convention — read without a length channel)
/// after the platform-fn call returns (step 2). A node the backend did not
/// stamp (a fresh node, or one built by an out-of-tree DLL) keeps field-3 null,
/// and we degrade to `"<unknown>"` — never crash.
fn read_effect_fn_name(io_ptr: i64) -> String {
    // SAFETY: `io_ptr` is the live `current` Effect node base pointer; field-3
    // is within its 32-byte payload (ABI v4).
    let handle = unsafe { crate::heap_access::read_i64(io_ptr, FIELD_2_OFFSET) };
    if handle == 0 {
        return "<unknown>".to_string();
    }
    // SAFETY: a non-null handle is a backend-baked pointer to a NUL-terminated
    // UTF-8 C-string with program lifetime (a `.rodata`/leaked data symbol).
    let cstr = unsafe { std::ffi::CStr::from_ptr(handle as *const libc::c_char) };
    cstr.to_str()
        .map(|s| s.to_string())
        .unwrap_or_else(|_| "<unknown>".to_string())
}

/// Result of running one Par work item: the branch results placed at their
/// original indices, plus the first runtime panic ferried off the worker thread
/// (the fork-join error-slot ferry, test-discovery.md §6).
struct ItemResult {
    positioned: Vec<(usize, i64)>,
    error: Option<String>,
}

/// Work item for Par dispatch.
enum WorkItem {
    /// A single branch to run independently (token=0).
    Single(usize, i64),
    /// A group of branches to run sequentially (same non-zero resource token).
    SerialGroup(Vec<(usize, i64)>),
}

/// Dispatch Par branches with resource token serialization.
///
/// - Token=0 branches: each dispatched independently to rayon
/// - Same non-zero token: grouped and run sequentially as a single work item
/// - Results are placed in original binding order
///
/// See design/backend/io-scheduling.md §5.2 for the algorithm.
///
/// This `_with_trace` variant — used by the trampoline — emits `ParSpark` /
/// `ParSerialGroupEnter` events at dispatch time. (A no-trace
/// `dispatch_par_branches` wrapper forwarding `parent_ptr = 0` existed but was
/// dead — zero callers — and was deleted; LOW-1, FIXME 0370. Pass `0` directly
/// if an untraced dispatch is ever needed.)
fn dispatch_par_branches_with_trace(branch_ptrs: &[i64], parent_ptr: i64) -> Vec<i64> {
    use rayon::prelude::*;
    use std::collections::HashMap;

    // Group branches by resource token.
    let mut token_groups: HashMap<i64, Vec<(usize, i64)>> = HashMap::new();
    for (i, &io_ptr) in branch_ptrs.iter().enumerate() {
        let token = read_resource_token(io_ptr);
        token_groups.entry(token).or_default().push((i, io_ptr));
    }

    // Build work items.
    let mut work_items: Vec<WorkItem> = Vec::new();
    for (&token, entries) in &token_groups {
        if token == 0 {
            // Each unrestricted branch is independent.
            for &(idx, io_ptr) in entries {
                io_observer::emit(
                    IoEventTag::ParSpark,
                    &IoEvent::ParSpark {
                        parent_ptr,
                        branch_idx: idx as u32,
                        token,
                    },
                );
                work_items.push(WorkItem::Single(idx, io_ptr));
            }
        } else {
            // Same non-zero token: run sequentially as one work item.
            io_observer::emit(
                IoEventTag::ParSerialGroupEnter,
                &IoEvent::ParSerialGroupEnter {
                    token,
                    branch_count: entries.len() as u32,
                },
            );
            for &(idx, _io_ptr) in entries {
                io_observer::emit(
                    IoEventTag::ParSpark,
                    &IoEvent::ParSpark {
                        parent_ptr,
                        branch_idx: idx as u32,
                        token,
                    },
                );
            }
            work_items.push(WorkItem::SerialGroup(entries.clone()));
        }
    }

    // Dispatch via rayon and collect results. Each work item also ferries any
    // runtime panic raised on the worker thread back to the join site — the
    // worker's `take_runtime_error()` slot is a *different* thread-local than the
    // joining thread reads, so without this the panic is silently swallowed
    // (test-discovery.md §6 — the fork-join error-slot ferry, first-error-wins).
    let item_results: Vec<ItemResult> = work_items
        .into_par_iter()
        .map(|item| match item {
            WorkItem::Single(idx, io_ptr) => {
                let result = run_io_trampoline(io_ptr);
                // Worker-side: capture and clear this thread's slot so it does
                // not pollute later rayon work on the same thread.
                let err = crate::panic::take_runtime_error();
                ItemResult { positioned: vec![(idx, result)], error: err }
            }
            WorkItem::SerialGroup(entries) => {
                let mut positioned = Vec::with_capacity(entries.len());
                let mut error: Option<String> = None;
                for (idx, io_ptr) in entries {
                    let result = run_io_trampoline(io_ptr);
                    if let Some(e) = crate::panic::take_runtime_error()
                        && error.is_none()
                    {
                        error = Some(e);
                    }
                    positioned.push((idx, result));
                }
                ItemResult { positioned, error }
            }
        })
        .collect();

    // Place results in correct positions; re-raise the first ferried error into
    // the joining thread's slot (first-error-wins matches sequential semantics).
    let mut results = vec![0i64; branch_ptrs.len()];
    for item in item_results {
        for (idx, val) in item.positioned {
            results[idx] = val;
        }
        if let Some(msg) = item.error {
            crate::panic::set_runtime_error(msg);
        }
    }

    results
}

#[cfg(test)]
mod tests;
