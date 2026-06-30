//! IO trampoline — iterative evaluation of IO task trees.
//!
//! The IO model is a deferred-execution system. User code builds IO trees
//! by calling constructors (Pure, Effect) and the `bind` primitive. The
//! trampoline walks the tree iteratively with an explicit continuation
//! stack, avoiding stack overflow for arbitrarily deep bind chains.
//!
//! See `design/backend/io-trampoline.md` for the full design.

use cranelisp_platform::{
    IO_TAG_BIND, IO_TAG_EFFECT, IO_TAG_EFFECT_POLL, IO_TAG_LAUNCH, IO_TAG_PAR, IO_TAG_PURE,
    IO_TAG_SELECT,
};
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

/// Byte offset of a closure's first env slot (its captures) from the base
/// pointer — past the header, code_ptr, and drop_glue_ptr. For a poll-shape
/// effect's state-closure this is the env base the trampoline passes to the
/// poll-fn as `state` (its first i64 is the reserved result slot). (S94 R1.)
const CLOSURE_ENV_OFFSET: i64 = HeapHeader::SIZE as i64 + 16; // 32

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

/// Drive an IO tree to its result value — the SINGLE (async) trampoline.
///
/// Single-trampoline cutover (`design/arch/platform-interface.md` §6.8.0a): the
/// former `#[cfg]` split between a synchronous off-build stepper and the async
/// on-build executor is **deleted**. There is now ONE body: the async trampoline
/// twin `block_on`'d on the host reactor's single-future executor
/// ([`crate::reactor::block_on_reactor`]). A pure-blocking tree
/// (`Pure`/`Bind`/blocking-`Effect`) never returns `Pending` — thunk effects
/// force synchronously via `force_effect_node` — so the first `poll` returns
/// `Ready` and the reactor's `turn()` is never reached. The synchronous
/// [`run_io_trampoline`] is RETAINED as the rayon-worker per-branch driver (the
/// blocking-`Par` partition), NOT as a second top-level trampoline.
///
/// Stage-2 status (`design/arch/platform-interface.md` §6.8.0a): the reactor is
/// currently built **eager-cheap** ([`crate::reactor::Reactor::new`] = 2 syscalls
/// per drive: `epoll_create` + an eventfd) — the blessed fallback, a permanently
/// valid behaviour, not an interim. The truly-lazy `Poll` (a pure-blocking program
/// constructs NO mio `Poll`) is the follow-up refinement; its lost-wake soundness
/// on the capacity-park-release path needs the careful treatment deferred here.
pub(crate) fn drive_io(io_ptr: i64) -> i64 {
    // Same `TrampolineEnter`/`TrampolineExit` bookend as `run_io_trampoline`
    // (Principle 7 — the IO trace stays identical for the synchronous node kinds;
    // poll nodes add suspend/resume strand events only).
    io_observer::emit(
        IoEventTag::TrampolineEnter,
        &IoEvent::TrampolineEnter { io_ptr },
    );
    let result = crate::reactor::block_on_reactor(async |env| {
        run_io_trampoline_inner_async(io_ptr, env, crate::strand::StrandId::ROOT).await
    })
    .expect("reactor init failed");
    io_observer::emit(
        IoEventTag::TrampolineExit,
        &IoEvent::TrampolineExit { result },
    );
    result
}

/// The cancellation drop-guard for the async trampoline loop (§2.15.1) — the one
/// genuinely-new RC piece Chunk C introduces. It OWNS the loop's in-flight,
/// **trampoline-produced** manual-RC pointers: the live `current` node + the
/// un-popped `cont_stack` continuations. On a **drop-before-`Step::Finish`** (a
/// cancelled branch — a race loser, a shutdown-cleared strand: the future is
/// dropped mid-`.await`) its `Drop` frees them; on normal finish (and every early
/// return) it is **disarmed** (`armed = false`), so its drop is a no-op — the
/// `Option`-take / "consumed exactly once" discipline §2.9 uses for the permit
/// (Principle 20).
///
/// **Scope (C2 foundations).** The guard frees only the **fresh** (continuation-
/// produced) in-flight pointers — nodes/closures the trampoline produced and that
/// have **no other owner**, so freeing them on cancel is a pure leak-fix with no
/// double-free risk. The **non-fresh** root of a moved-out branch sub-tree (the
/// race/select loser's own tree, transferred by the C3 move-out) is freed by its
/// owner, NOT here — that per-branch root ownership + the `consume_io_tree` balance
/// of a partially-stepped non-fresh tree is the **/design-backend-coordinated seam
/// C3 pins** (§2.15.1: "not a settled mechanism" until the move-out contract is
/// fixed). C2 lands the guard + the fresh-portion release; C3 wires the non-fresh
/// root into it alongside the `IO_TAG_SELECT` node bake.
struct TrampolineFrame {
    /// The live node the loop is positioned on (mirrors the loop's `current`).
    current: i64,
    /// `true` iff `current` is a fresh (trampoline-produced) node this guard owns.
    current_is_fresh: bool,
    /// The continuation stack `(cont_ptr, is_fresh)` — fresh entries are owned here.
    cont_stack: Vec<(i64, bool)>,
    /// `true` while in-flight; set `false` before every return (normal finish /
    /// early abort) so a completed walk's frame-drop is a no-op.
    armed: bool,
}

impl Drop for TrampolineFrame {
    fn drop(&mut self) {
        if !self.armed {
            return; // walk completed / aborted normally — already balanced.
        }
        // Free the FRESH in-flight node (continuation-produced, no other owner).
        if self.current_is_fresh && self.current != 0 {
            crate::drop::consume_io_tree(self.current);
        }
        // Free each un-popped FRESH continuation closure (a fresh Bind's cont,
        // already dec_shallow_io'd at push, so this is its sole remaining owner). A
        // non-fresh cont belongs to the caller's/owner's tree — left for its
        // consume_io_tree.
        for (cont_ptr, is_fresh) in self.cont_stack.drain(..) {
            if is_fresh {
                crate::drop::consume_closure(cont_ptr);
            }
        }
    }
}

/// The async twin of [`run_io_trampoline_inner`] (App. B step 2c; S94 R1 — the
/// real async Effect arm, FIXME 0457). Its loop is the sync body **verbatim
/// except the Effect arm**, reusing the shared `feed_continuation` /
/// `force_effect_node` helpers (Principle 7):
///
/// - `IO_TAG_EFFECT_POLL` (a real poll-shape effect node, host-built by the
///   backend's poll-construction arm) ⇒ `.await` an [`crate::reactor::EffectPoll`]
///   over the node's state-closure — the leaf suspends/resumes on the reactor.
/// - `IO_TAG_EFFECT` (the v6 blocking thunk) ⇒ the synchronous force, exactly as
///   the sync stepper. The feature-off sync stepper only ever sees this kind.
/// - `IO_TAG_PAR` ⇒ [`run_par_node_async`] (`join_all` of the branches on the ONE
///   reactor — concurrent I/O leaves overlap in ≈max not sum), vs the sync
///   stepper's rayon dispatch.
///
/// Returns a boxed future so the `IO_TAG_PAR` arm can recurse per branch (async
/// recursion). The `strand` charges this walk's effect events; `IO_TAG_PAR` mints
/// a fresh child strand per branch so concurrent leaves are distinguishable.
///
/// Two lifetimes: `'a` is the borrow of `env` (the returned future's lifetime),
/// `'h` is the reactor-host lifetime carried by `ReactorEnv` (`'h: 'a`). A
/// supervised detached strand (`reactor::supervised`) OWNS a `ReactorEnv<'h>`
/// clone and calls this with a SHORTER borrow `&'a` of that owned env — so the
/// borrow and the host lifetime must be allowed to differ.
///
/// `pub(crate)`: the supervisor (`reactor::supervised`) drives a launched sub-tree
/// through this same trampoline body, so it is reachable from `reactor.rs`.
pub(crate) fn run_io_trampoline_inner_async<'a, 'h: 'a>(
    io_ptr: i64,
    env: &'a crate::reactor::ReactorEnv<'h>,
    strand: crate::strand::StrandId,
) -> std::pin::Pin<Box<dyn std::future::Future<Output = i64> + 'a>> {
    Box::pin(async move {
        // The cancellation drop-guard (§2.15.1) OWNS the loop's in-flight pointers —
        // see [`TrampolineFrame`]. It frees the fresh in-flight subtree if the future
        // is dropped before finishing (a cancelled race/select loser); it is disarmed
        // before every return so a completed walk's drop is a no-op.
        let mut frame = TrampolineFrame {
            current: io_ptr,
            current_is_fresh: false,
            cont_stack: Vec::new(),
            armed: true,
        };

        loop {
            let current = frame.current;
            let current_is_fresh = frame.current_is_fresh;
            let tag = unsafe { read_node_tag(current) };

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
                    EffectStep::Aborted => {
                        frame.armed = false;
                        return 0;
                    }
                },
                // S94 R1 — the real async Effect arm: a poll-shape effect node
                // suspends/resumes on the reactor via `EffectPoll`. S96 (§2.9):
                // `await_poll_node` is the single admission gate — it reads the
                // live `(token, capacity)`, acquires the permit, and hands it to
                // the `EffectPoll` (which owns it across the arc), so it needs the
                // full `ReactorEnv` (pool + host), not just `env.host`.
                t if t == IO_TAG_EFFECT_POLL => {
                    await_poll_node(current, env, strand).await
                }
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
                    frame.cont_stack.push((cont, current_is_fresh));
                    io_observer::emit(
                        IoEventTag::ContPush,
                        &IoEvent::Cont {
                            cont_ptr: cont,
                            is_fresh: current_is_fresh,
                            new_depth: frame.cont_stack.len() as u32,
                        },
                    );
                    if current_is_fresh {
                        crate::drop::dec_shallow_io(current);
                    }
                    frame.current = inner;
                    // freshness unchanged: descending the inner of a (non-)fresh Bind.
                    continue;
                }
                t if t == IO_TAG_PAR => run_par_node_async(current, env).await,
                // S96 Chunk B — launch-and-continue (§2.11): detach the launched
                // sub-tree into a supervised strand and yield `Pure Unit` so the
                // continuation runs WITHOUT awaiting it (fire-and-forget).
                t if t == IO_TAG_LAUNCH => launch_continue(current, env, strand).await,
                // S96 Chunk C — race/select (§2.15): run all branch sub-trees
                // concurrently on the reactor, yield the first-ready winner's
                // value, and DROP the losers (cancellation = future-drop, which
                // releases their permits + reactor interest via the RAII drop
                // paths). The node is NOT moved-out — it owns the branch Vec for
                // the tree lifetime; `consume_io_tree` reclaims every branch.
                t if t == IO_TAG_SELECT => run_select_node(current, env, strand).await,
                _ => panic!("cranelisp_run_io: unknown IO tag {tag}"),
            };

            match feed_continuation(&mut frame.cont_stack, current, current_is_fresh, produced) {
                Step::Advance(new_io) => {
                    if crate::panic::has_runtime_error() || crate::panic::has_dispatch_fault() {
                        frame.armed = false;
                        return 0;
                    }
                    frame.current = new_io;
                    frame.current_is_fresh = true;
                }
                Step::Finish(value) => {
                    frame.armed = false;
                    return value;
                }
            }
        }
    })
}

/// Await a single `IO_TAG_EFFECT_POLL` node on the reactor — the **single
/// admission gate** for the poll carrier (§2.9 acquire-around-poll). Reads the
/// **live** `(token, capacity)` off the node (token @ abs 32 via
/// [`read_resource_token`]; capacity @ abs 40 via [`read_capacity`] /
/// `POLL_CAPACITY_ABS_OFFSET`), **acquires** the token's permit BEFORE the leaf
/// establishes (`token == 0` ⇒ an inert no-op permit — unrestricted overlap),
/// then reads the state-closure (field-0), bakes an [`crate::reactor::EffectPoll`]
/// over the GOT-loaded poll-fn (`closure + 16`) and the env base (`closure + 32`)
/// **owning that permit**, and `.await`s it. The poll-fn writes its result into
/// the env's reserved result slot (env offset 0), which `EffectPoll` reads on
/// `Ready` (the generic env-offset read); the `EffectPoll` releases the permit on
/// `Ready` (eager) or on drop (the cancellation path) — the A→C contract.
///
/// This is where S96 moved the admission gate **down** from the S95 branch-level
/// no-op acquire in [`run_poll_partition`]: the permit must live on the future
/// whose drop releases it. A poll leaf reached any way (a top-level poll effect,
/// a poll leaf mid-`Bind`-chain, or a `Par` poll branch) acquires here exactly
/// once — there is no double-acquire (`run_poll_partition` no longer acquires).
async fn await_poll_node(
    node: i64,
    env: &crate::reactor::ReactorEnv<'_>,
    strand: crate::strand::StrandId,
) -> i64 {
    // v9 ctx-vtable (`reactor.md §7.5`): `await_poll_node` is **scheduling-blind**.
    // It reads NO `(token, capacity)`/`role` off the node and takes NO pre-poll
    // acquire — the *platform poll-fn* projects its token from the handle it holds and
    // calls `ctx.acquire` itself; the host keys held permits by this leaf's identity
    // and releases them on `Ready`/cancel (the `EffectPoll`'s release-guard). The node
    // is the v8-uniform shape; the v8 token/capacity admission slots are inert.
    //
    // The state-closure pointer (the node's only payload field this trampoline reads).
    let clo = unsafe { read_node_field(node, FIELD_0_OFFSET) };
    // code_ptr = the GOT-loaded poll-fn (closure offset 16).
    let poll_fn_ptr = unsafe { crate::heap_access::read_i64(clo, CLOSURE_CODE_PTR_OFFSET) };
    // SAFETY: `poll_fn_ptr` is a code pointer the backend's poll-construction arm
    // baked as the state-closure's `code_ptr` (`compile_poll_effect`,
    // `io-trampoline.md §12.3`): it is `emit_got_slot_load`'d from
    // `__cranelisp_got_platform_<name>`, whose slot the platform loader populated
    // at DLL load with a `declare_platform!`-exported poll-shape function of the
    // `PollFn` C-ABI (`unsafe extern "C" fn(*mut c_void, *const HostCtx,
    // *const Waker) -> Poll`). So it is non-null (a populated GOT slot), points at
    // finalized code (the DLL is mapped for the session — BC §5 invariant 6), and
    // has exactly the `PollFn` ABI we transmute to. This is the same "read a code
    // pointer out of a heap closure and transmute to its known ABI" pattern as
    // `call_continuation` (which transmutes the continuation's `code_ptr` to
    // `extern "C" fn(i64,i64) -> i64`).
    let poll_fn: cranelisp_platform::PollFn =
        unsafe { std::mem::transmute::<*const (), cranelisp_platform::PollFn>(poll_fn_ptr as *const ()) };
    // The state env base is `closure + 32` (past header + code_ptr + drop_glue);
    // the reserved result slot is its first i64 (env offset 0). (Named
    // `state_env` to not shadow the `env: &ReactorEnv` admission handle above.)
    let state_env = (clo + CLOSURE_ENV_OFFSET) as *mut core::ffi::c_void;
    // Construct the EffectPoll scheduling-blind (no permit) — the platform poll-fn
    // acquires via `ctx.acquire`; the host releases by identity on `Ready`/drop.
    // SAFETY: `state_env` points at the backend-built env (result slot + i64
    // args); `poll_fn` obeys the v9 poll-fn contract.
    let leaf = unsafe {
        crate::reactor::EffectPoll::new(state_env, poll_fn, env.host, strand)
    };
    leaf.await
}

/// Interpret an `IO_TAG_LAUNCH` node — the launch-and-continue detach (§2.11).
/// Fire-and-forget: the launched sub-tree (field 0) becomes a **supervised
/// detached strand** that the continuation does **not** await; the node yields
/// `Pure Unit` (`0`) immediately so the continuation runs at once.
///
/// Steps (`design/int/reactor.md §2.11` / `io-trampoline.md §15`):
/// 1. **Acquire a global-budget permit** for the new strand (§2.13). A free
///    global slot ⇒ proceed; an exhausted budget PARKS here (`.await`) — parking
///    the accept loop itself until an in-flight strand completes (backpressure).
/// 2. **Mint a child strand id** and emit `StrandLaunched { strand, parent }`.
/// 3. **Move the sub-tree out** of the node (read field 0, write the `0` sentinel
///    back) so the node's null-guarded drop glue (`drop.rs` IO_TAG_LAUNCH arm) is
///    a no-op — the strand now owns the sub-tree, no double-consume (§15.5).
/// 4. **Spawn the supervised strand** owning the sub-tree + the global `Permit`
///    (RAII-released on completion/drop) + a cloned `ReactorEnv`.
/// 5. **Yield `Pure Unit`** — the launch never awaits the strand.
async fn launch_continue(
    node: i64,
    env: &crate::reactor::ReactorEnv<'_>,
    parent: crate::strand::StrandId,
) -> i64 {
    // 1. Global admission gate (parks the accept loop if the budget is full).
    let global_permit = env.acquire_global(parent).await;

    // 2. Mint the child strand + record the launch (parent ties it to the loop).
    let child = crate::strand::next_strand();
    crate::strand::emit_strand_event(crate::strand::StrandEvent::StrandLaunched {
        strand: child,
        parent,
    });

    // 3. Move the sub-tree out: read field 0, then write the `0` sentinel back so
    //    the node's drop glue (consume_io_tree IO_TAG_LAUNCH arm) does NOT also
    //    free it — ownership transfers to the strand (the move-out contract,
    //    io-trampoline.md §15.5).
    let sub_tree = unsafe { read_node_field(node, FIELD_0_OFFSET) };
    // SAFETY: `node` is the live current IO_TAG_LAUNCH node; field 0 is its only
    // payload slot. Writing the `0` sentinel is the backend↔intrinsics move-out
    // contract (§15.5) — without it node-drop would double-free the sub-tree.
    unsafe { crate::heap_access::write_i64(node, FIELD_0_OFFSET, 0) };

    // 4. Hand ownership of the sub-tree + the global permit to a supervised strand
    //    (it `consume_io_tree`s the sub-tree + releases the permit on end, §2.12).
    env.supervisor
        .spawn(sub_tree, env.clone(), child, global_permit);

    // 5. The launch's value is always Unit — the continuation proceeds at once.
    0
}

/// Read the N branch IO-tree pointers out of an `IO_TAG_SELECT` node's field-0
/// `Vec (IO a)` carrier (`io-trampoline.md §16`). The Vec is read **by raw
/// pointer with NO RC** (§16.5): the branches stay owned by the Vec (owned by the
/// node) and are reclaimed uniformly by `consume_io_tree`'s `IO_TAG_SELECT` arm —
/// the same liveness model `read_par_branches` uses for a `Par` node.
///
/// # Safety
/// `node` is the live `IO_TAG_SELECT` node base pointer; field 0 is a valid
/// `Vec (IO a)` (header + len@16 + cap@24 + data_ptr@32, `vec_runtime.rs`).
unsafe fn read_select_branches(node: i64) -> Vec<i64> {
    // Vec struct field offsets (absolute from the Vec base) — `vec_runtime.rs`
    // (`VEC_LEN_OFFSET = 16`, `VEC_DATA_PTR_OFFSET = 32`). The Select node owns the
    // Vec at its own field 0.
    const VEC_LEN_OFFSET: isize = 16;
    const VEC_DATA_PTR_OFFSET: isize = 32;
    let vec_ptr = unsafe { read_node_field(node, FIELD_0_OFFSET) };
    if vec_ptr == 0 {
        return Vec::new();
    }
    let len = unsafe { crate::heap_access::read_i64(vec_ptr, VEC_LEN_OFFSET) } as usize;
    let data_ptr = unsafe { crate::heap_access::read_i64(vec_ptr, VEC_DATA_PTR_OFFSET) };
    if data_ptr == 0 {
        return Vec::new();
    }
    (0..len)
        .map(|i| unsafe { crate::heap_access::read_i64(data_ptr, (i as isize) * 8) })
        .collect()
}

/// Interpret an `IO_TAG_SELECT` node — the race/select combinator (§2.15).
///
/// Runs all N branch sub-trees concurrently on the ONE reactor thread, yields the
/// **first-ready** winner's value, and **drops the losers** — and the drop IS the
/// cancellation (§9: "cancel is the consequence of losing a race"). Steps
/// (`design/int/reactor.md §2.15` / `io-trampoline.md §16`):
/// 1. **Read the branches by raw pointer** off the field-0 `Vec (IO a)` — NO
///    move-out, NO RC: the node owns the Vec for the tree lifetime; `consume_io_tree`
///    reclaims every branch (winner + losers) uniformly at the end (§16.5).
/// 2. **Mint a child strand per branch** (`next_strand`) so the `/strand` dump shows
///    the fan-out, and **build one branch future** per sub-tree — each wrapped in the
///    §2.15.1 `TrampolineFrame` drop-guard (it frees only the FRESH continuation-
///    produced nodes a cancelled branch was mid-flight on; the non-fresh branch root
///    stays for `consume_io_tree`, so the C2 fresh-only guard is correct verbatim for
///    the no-move-out list-carrier model — see the §2.15 reconciliation note).
/// 3. **Race them** with `futures::future::select_all` (first-ready-wins; it re-polls
///    ALL pending branches each turn — the re-poll-all property that, together with
///    the permit-forwarding `Drop for AcquirePermit`, keeps a token-contended sibling
///    from being stranded).
/// 4. **Drop the losers** — `select_all` returns the un-resolved futures, which are
///    dropped after emitting `StrandCancelled { reason: RaceLost }`. Each loser
///    drop releases its permit (§2.9), deregisters its reactor interest (§2.16),
///    removes any parked-acquire waker / forwards its permit (§2.17 + the C3 fix),
///    and frees its unconsumed FRESH sub-tree (§2.15.1).
/// 5. **Return the winner's value** as the node's result (the surrounding `Bind`'s
///    continuation runs with it — the §5.1 "inner yields a value" contract).
async fn run_select_node(
    node: i64,
    env: &crate::reactor::ReactorEnv<'_>,
    _strand: crate::strand::StrandId,
) -> i64 {
    // SAFETY: `node` is the live `current` IO_TAG_SELECT node base pointer.
    let branches = unsafe { read_select_branches(node) };
    if branches.is_empty() {
        // Degenerate `(select [])` — no branch can win. Yield Unit (`0`); there is
        // nothing to race or cancel.
        return 0;
    }

    let mut futures = Vec::with_capacity(branches.len());
    let mut strands = Vec::with_capacity(branches.len());
    for branch in branches {
        let child = crate::strand::next_strand();
        strands.push(child);
        futures.push(run_io_trampoline_inner_async(branch, env, child));
    }

    // Race on the ONE reactor thread: first-ready wins, `winner_idx` indexes the
    // original `strands`/`futures`, `remaining` are the still-pending losers.
    let (winner_val, winner_idx, remaining) = futures::future::select_all(futures).await;

    // Cancel the losers: emit `StrandCancelled` for each, THEN drop their futures
    // (the drop is the cancellation — RAII permit/interest release). Emit before the
    // drop so the `/strand` stream shows the loser cancelled.
    for (i, &child) in strands.iter().enumerate() {
        if i != winner_idx {
            crate::strand::emit_strand_event(crate::strand::StrandEvent::StrandCancelled {
                strand: child,
                reason: crate::strand::CancelReason::RaceLost,
            });
        }
    }
    drop(remaining);

    winner_val
}

/// The async `Par` overlap arm — the **two-pool join** (slice 6) wrapping the
/// **token-capacity admission** gate (slice 3), per `design/int/reactor.md` §2.6
/// / §2.8.
///
/// Branches are **partitioned by node tag** (gate (c) — the tag is already on the
/// node; no descriptor, no symbol back-ref): `IO_TAG_EFFECT_POLL`-rooted branches
/// route to the **reactor** partition (`join_all` of `EffectPoll` leaves on the
/// ONE reactor thread); everything else (`IO_TAG_EFFECT` blocking, `Bind`,
/// `Pure`, nested `Par`) routes to the **rayon** partition (run-to-completion on
/// a worker thread). Original binding indices ride along so results re-merge in
/// source/binding order — the same buffer shape the sync `run_par_node` produces.
///
/// **Both partitions run concurrently** (`futures::join!`) and **both wrap the
/// §2.8 admission gate**: each branch acquires its node-read `(token, capacity)`
/// permit before dispatch and releases on completion (`token == 0` ⇒ no acquire).
/// The blocking partition is how capacity-N is realized this sprint — a blocking
/// branch is admitted on the reactor thread, then `rayon::spawn`'d across a
/// **wakeable rayon→reactor bridge** (a `futures` `oneshot` woken via the
/// executor's mio-backed waker — never `block_on(rayon_join)` on the reactor
/// thread, the load-bearing Principle-8 constraint that keeps the blocking branch
/// from starving the reactor). The dispatcher's bespoke `SerialGroup`
/// token-grouping **dissolves into** this uniform per-branch permit-acquire (arch
/// §8); the rayon-spawn + worker→join error-ferry plumbing is what carries over.
/// Poll branches read the sentinel token 0 this sprint (poll-shape capacity-N is
/// S96), so their acquire is an inert no-op — admission still wraps both
/// partitions structurally.
async fn run_par_node_async(parent_ptr: i64, env: &crate::reactor::ReactorEnv<'_>) -> i64 {
    // SAFETY: `parent_ptr` is the live `current` Par node base pointer.
    let branch_ptrs = unsafe { read_par_branches(parent_ptr) };
    let count = branch_ptrs.len();

    // Partition by reachable effect-leaf tag (minimal slice = root tag; the
    // auto-IO independence analysis yields effect-rooted branches). Poll-shape →
    // reactor; everything else → rayon. Indices ride along for in-order merge.
    let mut blocking: Vec<(usize, i64)> = Vec::new();
    let mut pollshape: Vec<(usize, i64)> = Vec::new();
    for (i, &b) in branch_ptrs.iter().enumerate() {
        // SAFETY: `b` is a live branch base pointer from `read_par_branches`.
        let tag = unsafe { read_node_tag(b) };
        if tag == IO_TAG_EFFECT_POLL {
            pollshape.push((i, b));
        } else {
            blocking.push((i, b));
        }
    }

    // Drive both pools CONCURRENTLY on the reactor thread (the wakeable bridge
    // frees the reactor while rayon runs, so the poll partition progresses).
    let (blocking_results, poll_results) = futures::join!(
        run_blocking_partition(blocking, env),
        run_poll_partition(pollshape, env),
    );

    io_observer::emit(
        IoEventTag::ParJoin,
        &IoEvent::ParJoin {
            parent_ptr,
            count: count as u32,
        },
    );

    // Merge by original binding index into the single results buffer.
    let mut merged = vec![0i64; count];
    for (idx, val) in blocking_results.into_iter().chain(poll_results) {
        merged[idx] = val;
    }
    let results_buf = alloc_with_rc(8 + count * 8) as i64; // payload: padding(8) + N*8
    for (i, &val) in merged.iter().enumerate() {
        // SAFETY: `results_buf` was just allocated with `count` field slots.
        unsafe { crate::heap_access::write_i64(results_buf, FIELD_0_OFFSET + (i as isize) * 8, val) };
    }
    results_buf
}

/// The blocking partition of the two-pool join: each branch acquires its
/// `(token, capacity)` permit on the reactor thread, then runs to completion on
/// rayon across the wakeable bridge, then releases. `join_all` on the reactor
/// thread so capacity-N branches overlap (the first N acquire + spawn; the
/// (N+1)th parks on the token's `Semaphore` until a permit frees).
async fn run_blocking_partition(
    branches: Vec<(usize, i64)>,
    env: &crate::reactor::ReactorEnv<'_>,
) -> Vec<(usize, i64)> {
    let futs = branches
        .into_iter()
        .map(|(idx, b)| run_blocking_branch(idx, b, env));
    futures::future::join_all(futs).await
}

/// One blocking branch: admit → `rayon::spawn` run-to-completion → await the
/// wakeable `oneshot` → ferry any worker-thread runtime error → release the
/// permit (waking the front parked waiter). The permit is **held across the
/// bridge** (acquired before the spawn, released after completion), which is what
/// bounds same-token concurrency to the pool's capacity.
async fn run_blocking_branch(
    idx: usize,
    branch: i64,
    env: &crate::reactor::ReactorEnv<'_>,
) -> (usize, i64) {
    let token = read_resource_token(branch) as u64;
    let capacity = read_capacity(branch).max(1) as u32;
    let strand = crate::strand::next_strand();

    // 1. Admit on the reactor thread (capacity-N parking; capacity-1 FIFO =
    //    source order). `token == 0` ⇒ inert no-op permit.
    let permit = env.acquire(token, capacity, strand).await;

    // 2. Offload run-to-completion to rayon across the wakeable bridge. The
    //    reactor thread is freed while the worker runs; the `oneshot` send wakes
    //    the reactor through the executor's mio-backed waker (NOT block_on).
    let (tx, rx) = futures::channel::oneshot::channel::<(i64, Option<String>)>();
    env.pending_bridges.set(env.pending_bridges.get() + 1);
    rayon::spawn(move || {
        // Non-consuming run on the worker (the Par node owns the branch; freed
        // later by `consume_io_tree`) — the same model as the sync dispatcher.
        let result = run_io_trampoline(branch);
        // Worker-side: capture + clear this thread's runtime-error slot (a
        // different thread-local than the reactor thread reads) so it can be
        // ferried back — the fork-join error-slot ferry (test-discovery.md §6).
        let err = crate::panic::take_runtime_error();
        let _ = tx.send((result, err));
    });

    // 3. Await completion (reactor thread parks here, freed for the poll
    //    partition). A dropped sender (rayon panic) yields the sentinel 0.
    let (result, err) = rx.await.unwrap_or((0, None));
    env.pending_bridges.set(env.pending_bridges.get() - 1);

    // 4. Re-raise the ferried error into the reactor thread's slot. This is
    //    first-to-*complete*-wins: across distinct-token concurrent blocking
    //    branches the winner is whichever rayon worker resolves first (NOT source
    //    order) — inherently racy, the same as the sync path for concurrent work.
    //    It is deterministic only for same-token capacity-1 branches, which run
    //    serial+ordered (the permit holds them to source order).
    if let Some(msg) = err
        && !crate::panic::has_runtime_error()
    {
        crate::panic::set_runtime_error(msg);
    }

    // 5. Release the permit (drop) — increments the pool + wakes the FRONT
    //    (FIFO) parked waiter, which re-polls and acquires.
    drop(permit);
    (idx, result)
}

/// The poll-shape partition of the two-pool join: each poll leaf is awaited on
/// the reactor via the async trampoline. `join_all` so distinct-token poll leaves
/// overlap on the ONE reactor thread (≈max not sum).
///
/// **S96 (§2.9): the admission gate moved DOWN onto the leaf.** S95 placed a
/// branch-level no-op acquire here (sentinel token 0). S96 removes it — the single
/// admission gate is now [`await_poll_node`] at the leaf's establishment, where it
/// reads the LIVE `(token, capacity)` and hands the resulting `Permit` to the
/// `EffectPoll` that structurally owns it (the A→C drop-release contract requires
/// the permit live on the future whose drop releases it). Acquiring here too would
/// double-acquire, so this partition no longer touches the pool.
async fn run_poll_partition(
    branches: Vec<(usize, i64)>,
    env: &crate::reactor::ReactorEnv<'_>,
) -> Vec<(usize, i64)> {
    let futs = branches.into_iter().map(|(idx, b)| async move {
        let strand = crate::strand::next_strand();
        let result = run_io_trampoline_inner_async(b, env, strand).await;
        (idx, result)
    });
    futures::future::join_all(futs).await
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

/// Read the resource token from an IO node — tag-agnostic over the two effect
/// kinds (§2.6 / §13.4): BOTH `IO_TAG_EFFECT` (blocking) and `IO_TAG_EFFECT_POLL`
/// (poll-shape) store the token at FIELD_1_OFFSET (abs offset 32). Non-effect
/// nodes (Pure, Bind, Par) return 0 (unrestricted). **S96**: the poll node now
/// carries a LIVE token here (the backend bakes it at offset 32; `await_poll_node`
/// reads it to gate the acquire-around-poll permit) — no longer the S95 sentinel.
fn read_resource_token(io_ptr: i64) -> i64 {
    let tag = unsafe { crate::heap_access::read_i64(io_ptr, TAG_OFFSET) };
    // Both effect tags carry the token at FIELD_1 (§2.6 / §13.4).
    let is_effect = tag == IO_TAG_EFFECT || tag == IO_TAG_EFFECT_POLL;
    if is_effect {
        unsafe { crate::heap_access::read_i64(io_ptr, FIELD_1_OFFSET) }
    } else {
        0
    }
}

/// Absolute byte offset of the **blocking** `IO_TAG_EFFECT` node's `capacity`
/// field — appended (append-only) at payload offset 32 by the platform
/// constructor `effect_on_resource_with_capacity` (`io-trampoline.md` §13.2). Abs
/// = header(16) + payload-offset(32) = 48.
const IO_EFFECT_CAPACITY_ABS_OFFSET: isize =
    HeapHeader::SIZE as isize + cranelisp_platform::IO_EFFECT_CAPACITY_OFFSET as isize; // 16 + 32 = 48

/// Absolute byte offset of the **poll** `IO_TAG_EFFECT_POLL` node's `capacity`
/// field — the symmetric reserved slot the backend bakes at `field_offset(2)`
/// (`io-trampoline.md` §13.3). Abs = FIELD_1_OFFSET + 8 = 40.
const POLL_CAPACITY_ABS_OFFSET: isize = FIELD_1_OFFSET + 8; // 32 + 8 = 40

/// Read the token-pool `capacity` from an IO node — **tag-branched** (§2.6 /
/// §13.4): `IO_TAG_EFFECT` (blocking) reads payload offset 32 (abs 48);
/// `IO_TAG_EFFECT_POLL` (poll-shape) reads `field_offset(2)` (abs 40). Non-effect
/// nodes default to capacity 1 (they carry no pool). **S96**: the poll node now
/// carries a LIVE capacity here (the backend bakes it at offset 40;
/// `await_poll_node` reads it to size the token's `Semaphore`) — no longer the S95
/// sentinel 1.
fn read_capacity(io_ptr: i64) -> i64 {
    let tag = unsafe { crate::heap_access::read_i64(io_ptr, TAG_OFFSET) };
    if tag == IO_TAG_EFFECT {
        unsafe { crate::heap_access::read_i64(io_ptr, IO_EFFECT_CAPACITY_ABS_OFFSET) }
    } else if tag == IO_TAG_EFFECT_POLL {
        unsafe { crate::heap_access::read_i64(io_ptr, POLL_CAPACITY_ABS_OFFSET) }
    } else {
        1
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
