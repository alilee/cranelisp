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

use crate::handle::{Borrowed, Owned};

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

/// A compiler-provided callback that consumes one owned language value.
/// Zero denotes a representation with no heap ownership.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ResultDisposer(i64);

impl ResultDisposer {
    pub(crate) const NONE: Self = Self(0);

    pub(crate) fn from_raw(raw: i64) -> Self {
        Self(raw)
    }

    #[cfg(test)]
    fn from_fn(dispose: extern "C" fn(i64)) -> Self {
        Self(dispose as *const () as i64)
    }

    pub(crate) fn dispose(self, value: i64) {
        if self.0 == 0 {
            return;
        }
        // SAFETY: non-zero result-disposer words are emitted by the backend as
        // canonical `(i64) -> ()` drop-glue addresses.
        let dispose: extern "C" fn(i64) = unsafe { std::mem::transmute(self.0 as *const ()) };
        dispose(value);
    }
}

/// A trampoline either transfers a produced value or stops without one.
/// Keeping the outcomes distinct prevents cancellation and fault sentinels
/// from acquiring value-disposal authority.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum TrampolineOutcome {
    Completed(i64),
    Stopped,
}

impl TrampolineOutcome {
    fn into_raw(self) -> i64 {
        match self {
            Self::Completed(value) => value,
            Self::Stopped => 0,
        }
    }

    fn map_completed<T>(self, map: impl FnOnce(i64) -> T) -> Option<T> {
        match self {
            Self::Completed(value) => Some(map(value)),
            Self::Stopped => None,
        }
    }
}

/// Owns a result between production and its next language-level handoff.
/// Transfer is explicit; every other exit discharges the value.
struct ProducedValue {
    value: i64,
    ownership: Option<ResultOwnership>,
}

enum ResultOwnership {
    Value(ResultDisposer),
    ParBuffer(Vec<ResultDisposer>),
}

impl ProducedValue {
    fn with_disposer(value: i64, disposer: ResultDisposer) -> Self {
        Self {
            value,
            ownership: Some(ResultOwnership::Value(disposer)),
        }
    }

    fn par_buffer(value: i64, disposers: Vec<ResultDisposer>) -> Self {
        Self {
            value,
            ownership: Some(ResultOwnership::ParBuffer(disposers)),
        }
    }

    fn transfer(mut self) -> i64 {
        self.ownership = None;
        self.value
    }
}

impl Drop for ProducedValue {
    fn drop(&mut self) {
        match self.ownership.take() {
            Some(ResultOwnership::Value(disposer)) => disposer.dispose(self.value),
            Some(ResultOwnership::ParBuffer(disposers)) => {
                for (index, disposer) in disposers.into_iter().enumerate() {
                    // SAFETY: a Par result buffer has one initialized value slot
                    // per disposer, beginning at the ordinary ADT field offset.
                    let value = unsafe {
                        crate::heap_access::read_i64(
                            self.value,
                            FIELD_0_OFFSET + (index as isize) * 8,
                        )
                    };
                    disposer.dispose(value);
                }
                // SAFETY: the armed Par buffer is owned by this guard.
                crate::rc::consume_shallow(unsafe { Owned::from_abi(self.value) });
            }
            None => {}
        }
    }
}

struct ContinuationFrame {
    ptr: i64,
    is_fresh: bool,
    input_disposer: ResultDisposer,
}

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
/// tree read-only. Fresh-node release follows
/// `design/intrinsics/ownership-and-disposal.md` §7: fresh Bind descent
/// releases the parent structurally after acquiring its fields; finished
/// fresh nodes use `drop::dec_shallow_io`. Closures reached via the caller's tree are
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
    // SAFETY: the consuming trampoline entry received this tree by transfer.
    crate::drop::consume_io_tree(unsafe { Owned::from_abi(io_ptr) });
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
/// Every drive constructs its reactor **eagerly**
/// ([`crate::reactor::Reactor::new`] = 2 syscalls: `epoll_create` + an eventfd),
/// including for a pure-blocking program. Lazy construction is a workload-triggered
/// refinement (`design/arch/effect-concurrency.md` §6); it must preserve the
/// capacity-park-release wake path.
pub(crate) fn drive_io(io_ptr: i64) -> i64 {
    // Same `TrampolineEnter`/`TrampolineExit` bookend as `run_io_trampoline`
    // (Principle 7 — the IO trace stays identical for the synchronous node kinds;
    // poll nodes add suspend/resume strand events only).
    io_observer::emit(
        IoEventTag::TrampolineEnter,
        &IoEvent::TrampolineEnter { io_ptr },
    );
    let outcome = crate::reactor::block_on_reactor(async |env| {
        run_io_trampoline_inner_async(
            io_ptr,
            env,
            crate::strand::StrandId::ROOT,
            ResultDisposer::NONE,
        )
        .await
    })
    .expect("reactor init failed");
    let result = outcome.into_raw();
    io_observer::emit(
        IoEventTag::TrampolineExit,
        &IoEvent::TrampolineExit { result },
    );
    result
}

/// The cancellation drop-guard for the async trampoline loop (§2.15.1). It OWNS
/// the loop's in-flight,
/// **trampoline-produced** manual-RC pointers: the live `current` node + the
/// un-popped `cont_stack` continuations. On a **drop-before-`Step::Finish`** (a
/// cancelled branch — a race loser, a shutdown-cleared strand: the future is
/// dropped mid-`.await`) its `Drop` frees them; on normal finish (and every early
/// return) it is **disarmed** (`armed = false`), so its drop is a no-op — the
/// `Option`-take / "consumed exactly once" discipline §2.9 uses for the permit
/// (Principle 20).
///
/// **Scope.** The guard frees only the frame's references to **fresh**
/// (continuation-produced) in-flight pointers. Other structural owners may retain
/// their own references. A **non-fresh** root is never freed here: a race/select
/// branch is not moved out of its `IO_TAG_SELECT` node, so the node's owner
/// reclaims every branch through `consume_io_tree`.
struct TrampolineFrame {
    /// The live node the loop is positioned on (mirrors the loop's `current`).
    current: i64,
    /// `true` iff `current` is a fresh (trampoline-produced) node this guard owns.
    current_is_fresh: bool,
    /// Continuations plus the disposer for the value each one accepts.
    cont_stack: Vec<ContinuationFrame>,
    /// `true` while in-flight; set `false` before every return (normal finish /
    /// early abort) so a completed walk's frame-drop is a no-op.
    armed: bool,
}

impl Drop for TrampolineFrame {
    fn drop(&mut self) {
        if !self.armed {
            return; // walk completed / aborted normally — already balanced.
        }
        // Release the frame's reference to the FRESH in-flight node.
        if self.current_is_fresh && self.current != 0 {
            // SAFETY: `current_is_fresh` marks the frame-owned reference.
            crate::drop::consume_io_tree(unsafe { Owned::from_abi(self.current) });
        }
        // Release the frame's reference to each un-popped FRESH continuation.
        // That reference was acquired before the fresh Bind parent was consumed;
        // another retained parent may still own a separate reference. A non-fresh
        // cont belongs to the caller's/owner's tree — left for its consume_io_tree.
        for cont in self.cont_stack.drain(..) {
            if cont.is_fresh {
                // SAFETY: `is_fresh` marks the frame-owned continuation.
                crate::drop::consume_closure(unsafe { Owned::from_abi(cont.ptr) });
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
    terminal_disposer: ResultDisposer,
) -> std::pin::Pin<Box<dyn std::future::Future<Output = TrampolineOutcome> + 'a>> {
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

            let edge_disposer = frame
                .cont_stack
                .last()
                .map_or(terminal_disposer, |cont| cont.input_disposer);

            let produced = match tag {
                t if t == IO_TAG_PURE => ProducedValue::with_disposer(
                    force_pure_node(current, current_is_fresh),
                    edge_disposer,
                ),
                t if t == IO_TAG_EFFECT => match force_effect_node(current) {
                    EffectStep::Value(value) => ProducedValue::with_disposer(value, edge_disposer),
                    EffectStep::Aborted => {
                        frame.armed = false;
                        return TrampolineOutcome::Stopped;
                    }
                },
                // A poll-shape effect node suspends/resumes on the reactor via
                // `EffectPoll`. Admission is the platform poll-fn's `ctx.acquire`
                // (`reactor.md` §7), not a read of the node.
                t if t == IO_TAG_EFFECT_POLL => ProducedValue::with_disposer(
                    await_poll_node(current, env, strand).await,
                    edge_disposer,
                ),
                t if t == IO_TAG_BIND => {
                    let (inner, cont, input_disposer) =
                        read_bind_transition(current, current_is_fresh);
                    io_observer::emit(
                        IoEventTag::BindEnter,
                        &IoEvent::BindEnter {
                            inner_ptr: inner,
                            cont_ptr: cont,
                            is_fresh: current_is_fresh,
                        },
                    );
                    frame.cont_stack.push(ContinuationFrame {
                        ptr: cont,
                        is_fresh: current_is_fresh,
                        input_disposer,
                    });
                    io_observer::emit(
                        IoEventTag::ContPush,
                        &IoEvent::Cont {
                            cont_ptr: cont,
                            is_fresh: current_is_fresh,
                            new_depth: frame.cont_stack.len() as u32,
                        },
                    );
                    frame.current = inner;
                    // freshness unchanged: descending the inner of a (non-)fresh Bind.
                    continue;
                }
                t if t == IO_TAG_PAR => match run_par_node_async(current, env).await {
                    Some(value) => value,
                    None => {
                        frame.armed = false;
                        return TrampolineOutcome::Stopped;
                    }
                },
                // S96 Chunk B — launch-and-continue (§2.11): detach the launched
                // sub-tree into a supervised strand and yield `Pure Unit` so the
                // continuation runs WITHOUT awaiting it (fire-and-forget).
                t if t == IO_TAG_LAUNCH => ProducedValue::with_disposer(
                    launch_continue(current, env, strand).await,
                    edge_disposer,
                ),
                // S96 Chunk C — race/select (§2.15): run all branch sub-trees
                // concurrently on the reactor, yield the first-ready winner's
                // value, and DROP the losers (cancellation = future-drop, which
                // releases their permits + reactor interest via the RAII drop
                // paths). The node is NOT moved-out — it owns the branch Vec for
                // the tree lifetime; `consume_io_tree` reclaims every branch.
                t if t == IO_TAG_SELECT => match run_select_node(current, env, strand).await {
                    TrampolineOutcome::Completed(value) => {
                        ProducedValue::with_disposer(value, edge_disposer)
                    }
                    TrampolineOutcome::Stopped => {
                        frame.armed = false;
                        return TrampolineOutcome::Stopped;
                    }
                },
                _ => panic!("cranelisp_run_io: unknown IO tag {tag}"),
            };

            // A combinator arm may have raised a runtime error while producing a
            // sentinel (e.g. an empty `(select [])` → "select over empty
            // collection", FIXME 0475). Abort BEFORE feeding the continuation so the
            // sentinel `0` is never applied — at a heap-typed `a` the `0` is an
            // unsound null the continuation would dereference. Mirrors the
            // `IO_TAG_EFFECT` `EffectStep::Aborted` early-return; int reads the slot
            // at the trampoline boundary (or a `catch-runtime-error` bracket drains
            // it) — not the return value.
            if crate::panic::has_runtime_error() || crate::panic::has_dispatch_fault() {
                frame.armed = false;
                return TrampolineOutcome::Stopped;
            }

            match feed_continuation(
                &mut frame.cont_stack,
                current,
                current_is_fresh,
                produced,
                CancellationProbe::Never,
            ) {
                Step::Advance(new_io) => {
                    if crate::panic::has_runtime_error() || crate::panic::has_dispatch_fault() {
                        frame.armed = false;
                        return TrampolineOutcome::Stopped;
                    }
                    frame.current = new_io;
                    frame.current_is_fresh = true;
                }
                Step::Finish(value) => {
                    frame.armed = false;
                    return TrampolineOutcome::Completed(value);
                }
                Step::Cancelled => return TrampolineOutcome::Stopped,
            }
        }
    })
}

/// Await a single `IO_TAG_EFFECT_POLL` node on the reactor. Reads only the
/// state-closure (field 0), bakes an [`crate::reactor::EffectPoll`] over the
/// GOT-loaded poll-fn (`closure + 16`) and the env base (`closure + 32`), and
/// `.await`s it. The poll-fn writes its result into the env's reserved result
/// slot (env offset 0), which `EffectPoll` reads on `Ready`.
///
/// Admission is not taken here: the platform poll-fn calls `ctx.acquire` for the
/// token it projects from its handle, and the reactor releases every permit held
/// by this leaf on `Ready` or on cancel-drop (`reactor.md` §2.9, §7). The node's
/// token and capacity slots are not read.
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
    let poll_fn: cranelisp_platform::PollFn = unsafe {
        std::mem::transmute::<*const (), cranelisp_platform::PollFn>(poll_fn_ptr as *const ())
    };
    // The state env base is `closure + 32` (past header + code_ptr + drop_glue);
    // the reserved result slot is its first i64 (env offset 0). (Named
    // `state_env` to not shadow the `env: &ReactorEnv` admission handle above.)
    let state_env = (clo + CLOSURE_ENV_OFFSET) as *mut core::ffi::c_void;
    // Keep-alive across suspension (`bounded-contexts.md §4b` invariant 15; FIXME
    // 0486 bug #2). A reactor-deferred poll effect's baked heap args (captured in
    // the state-closure) must stay LIVE from establish until the reactor resolves
    // the effect — but the enclosing IO sub-tree can be torn down first (a launched
    // strand's `consume_io_tree` runs to completion while the terminal `send-conn`
    // is still reactor-deferred). That teardown's tag-4 arm (`drop.rs`) would run
    // the state-closure's drop glue and free the baked args out from under the
    // pending poll-fn → use-after-free (RC-balanced; a UAF, not a miscount →
    // SIGABRT).
    //
    // Fix = **net-zero-inc** (the RC-trace-decided variant, FIXME 0486): take ONE
    // extra RC ref on the state-closure at establish and hand it to the
    // `EffectPoll`, which releases it (via `consume_closure`) exactly once at
    // resolve — on `Poll::Ready` OR on cancel-drop, keyed to the SAME two-path the
    // permit release already rides. The node's field-0 is left UNTOUCHED (no
    // sentinel), so the sub-tree's own tag-4 reclamation still dec's its ref
    // exactly as before; the closure is now freed at the LATER of {node-release,
    // effect-resolve} — i.e. at true rc→0. On the normal path resolve precedes
    // node-release, so free-timing/ownership is byte-identical to pre-fix; on the
    // launched path the extra ref survives the early teardown and the deferred send
    // reads the live args, resolve then frees. This is runtime-owned keep-alive;
    // the backend's state-closure + drop-glue obligation is unchanged (invariant
    // 15). (The move-out-with-sentinel alternative was rejected on measurement: it
    // eager-frees EVERY poll effect's closure on `Ready`, including the `accept`
    // effect's closure that captures the LISTENER — freeing it early wedges the
    // accept loop, so the server hangs and the launched vec-render never runs enough
    // to trip the bug. That is a false-green — the SIGABRT guard sees "no signal" but
    // the server is dead — and it reliably breaks the real serve path. Net-zero-inc
    // preserves the pre-fix closure free-timing, so listener/conn lifetime is
    // correct and the server keeps serving. See FIXME 0486.)
    // SAFETY: `clo` is the live state-closure base (rc > 0) — `rc_inc` takes the
    // keep-alive ref the `EffectPoll` owns.
    crate::rc::rc_inc(clo);
    // Construct the EffectPoll scheduling-blind (no permit) — the platform poll-fn
    // acquires via `ctx.acquire`; the host releases by identity on `Ready`/drop.
    // The `EffectPoll` now owns the keep-alive ref on `clo` and releases it exactly
    // once at resolve (invariant 15).
    // SAFETY: `state_env` points at the backend-built env (result slot + i64 args)
    // INSIDE `clo` (valid for the future's whole lifetime — the keep-alive ref keeps
    // `clo` alive at least until the EffectPoll releases it at resolve, after
    // reading the result slot); `poll_fn` obeys the v9 poll-fn contract; `clo` is
    // the live state-closure base carrying the keep-alive ref.
    let leaf = unsafe {
        crate::reactor::EffectPoll::new_owning(state_env, poll_fn, env.host, strand, clo)
    };
    leaf.await
}

/// Interpret an `IO_TAG_LAUNCH` node — the launch-and-continue detach (§2.11).
/// Fire-and-forget: the launched sub-tree (field 0) becomes a **supervised
/// detached strand** that the continuation does **not** await; the node yields
/// `Pure Unit` (`0`) immediately so the continuation runs at once.
///
/// Steps (`design/intrinsics/reactor.md §2.11` / `io-trampoline.md §15`):
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
    let result_disposer =
        ResultDisposer::from_raw(unsafe { read_node_field(node, FIELD_1_OFFSET) });
    // SAFETY: `node` is the live current IO_TAG_LAUNCH node; field 0 is its only
    // payload slot. Writing the `0` sentinel is the backend↔intrinsics move-out
    // contract (§15.5) — without it node-drop would double-free the sub-tree.
    unsafe { crate::heap_access::write_i64(node, FIELD_0_OFFSET, 0) };

    // 4. Hand ownership of the sub-tree + the global permit to a supervised strand
    //    (it `consume_io_tree`s the sub-tree + releases the permit on end, §2.12).
    env.supervisor
        .spawn(sub_tree, result_disposer, env.clone(), child, global_permit);

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
/// (`design/intrinsics/reactor.md §2.15` / `io-trampoline.md §16`):
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
) -> TrampolineOutcome {
    // SAFETY: `node` is the live `current` IO_TAG_SELECT node base pointer.
    let branches = unsafe { read_select_branches(node) };
    let branch_disposer =
        ResultDisposer::from_raw(unsafe { read_node_field(node, FIELD_1_OFFSET) });
    if branches.is_empty() {
        // Degenerate `(select [])` — no branch can win and there is no value to
        // return (FIXME 0475 / `reactor.md §9`; `spec/10-io.md §10.12.8`). Raise a
        // recoverable runtime error through the standard runtime-error slot — the
        // same §12.7.2 class as match-non-exhaustion / div-by-zero — instead of
        // returning a synthesised Unit `0` (an unsound null at a heap-typed `a`
        // that the continuation would dereference) and instead of hanging. Returning
        // the sentinel `0` here is safe: the trampoline's post-arm error-slot check
        // (`run_io_trampoline_inner_async`) aborts BEFORE feeding the continuation,
        // so the `0` is never applied.
        crate::panic::set_runtime_error("select over empty collection".to_string());
        return TrampolineOutcome::Stopped;
    }

    let mut futures = Vec::with_capacity(branches.len());
    let mut strands = Vec::with_capacity(branches.len());
    for branch in branches {
        let child = crate::strand::next_strand();
        strands.push(child);
        futures.push(run_io_trampoline_inner_async(
            branch,
            env,
            child,
            branch_disposer,
        ));
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
/// **token-capacity admission** gate (slice 3), per `design/intrinsics/reactor.md` §2.6
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
/// **Both partitions run concurrently** (`futures::join!`). Admission differs by
/// partition (§2.8):
///
/// - a **blocking** branch acquires its node-read `(token, capacity)` permit on
///   the reactor thread (`token == 0` ⇒ inert permit), then is `rayon::spawn`'d
///   across a **wakeable rayon→reactor bridge** (a `futures` `oneshot` woken via
///   the executor's mio-backed waker — never `block_on(rayon_join)` on the
///   reactor thread, the Principle-8 constraint that keeps the blocking branch
///   from starving the reactor); this per-branch permit replaces the synchronous
///   dispatcher's `SerialGroup` token-grouping on this path;
/// - a **poll** branch takes no branch-level permit; its leaf's platform poll-fn
///   acquires through `ctx.acquire` (see [`await_poll_node`]).
async fn run_par_node_async(
    parent_ptr: i64,
    env: &crate::reactor::ReactorEnv<'_>,
) -> Option<ProducedValue> {
    // SAFETY: `parent_ptr` is the live `current` Par node base pointer.
    let branch_ptrs = unsafe { read_par_branches(parent_ptr) };
    let count = branch_ptrs.len();

    // Partition by reachable effect-leaf tag (minimal slice = root tag; the
    // auto-IO independence analysis yields effect-rooted branches). Poll-shape →
    // reactor; everything else → rayon. Indices ride along for in-order merge.
    let mut blocking: Vec<(usize, ParBranch)> = Vec::new();
    let mut pollshape: Vec<(usize, ParBranch)> = Vec::new();
    for (i, &branch) in branch_ptrs.iter().enumerate() {
        // SAFETY: `branch.io` is a live branch base pointer from `read_par_branches`.
        let tag = unsafe { read_node_tag(branch.io) };
        if tag == IO_TAG_EFFECT_POLL {
            pollshape.push((i, branch));
        } else {
            blocking.push((i, branch));
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
    let mut merged: Vec<Option<ProducedValue>> = (0..count).map(|_| None).collect();
    for (idx, value) in blocking_results.into_iter().chain(poll_results) {
        merged[idx] = value;
    }
    let results = merged.into_iter().collect::<Option<Vec<_>>>()?;
    Some(par_results_buffer(&branch_ptrs, results))
}

/// The blocking partition of the two-pool join: each branch acquires its
/// `(token, capacity)` permit on the reactor thread, then runs to completion on
/// rayon across the wakeable bridge, then releases. `join_all` on the reactor
/// thread so capacity-N branches overlap (the first N acquire + spawn; the
/// (N+1)th parks on the token's `Semaphore` until a permit frees).
async fn run_blocking_partition(
    branches: Vec<(usize, ParBranch)>,
    env: &crate::reactor::ReactorEnv<'_>,
) -> Vec<(usize, Option<ProducedValue>)> {
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
    branch: ParBranch,
    env: &crate::reactor::ReactorEnv<'_>,
) -> (usize, Option<ProducedValue>) {
    let token = read_resource_token(branch.io) as u64;
    let capacity = read_capacity(branch.io).max(1) as u32;
    let strand = crate::strand::next_strand();

    // 1. Admit on the reactor thread (capacity-N parking; capacity-1 FIFO =
    //    source order). `token == 0` ⇒ inert no-op permit.
    let permit = env.acquire(token, capacity, strand).await;
    // A capacity-1 sibling may have failed while this branch was parked. It has
    // not started yet, so sequential left-to-right semantics require aborting
    // before the worker is spawned. Dropping the acquired permit wakes the next
    // waiter without performing this branch's effect.
    if crate::panic::has_runtime_error() || crate::panic::has_dispatch_fault() {
        return (idx, None);
    }

    // 2. Offload run-to-completion to rayon across the wakeable bridge. The
    //    reactor thread is freed while the worker runs; the `oneshot` send wakes
    //    the reactor through the executor's mio-backed waker (NOT block_on).
    let (tx, rx) = futures::channel::oneshot::channel::<(Option<ProducedValue>, Option<String>)>();
    let (lease, ticket) = env.bridge_join.start_bridge();
    let mut cancel_guard = crate::reactor::CancelBridgeGuard::new(ticket, Some(permit));
    rayon::spawn(move || {
        // Non-consuming run on the worker (the Par node owns the branch; freed
        // later by `consume_io_tree`) — the same model as the sync dispatcher.
        let outcome = run_io_trampoline_with_bridge(branch.io, &lease, strand, branch.disposer);
        // The nested trampoline transfers its terminal value out as a raw word.
        // Re-arm it immediately, before any fault/cancellation policy can choose
        // to abandon the completion.
        let produced =
            outcome.map_completed(|value| ProducedValue::with_disposer(value, branch.disposer));
        // Worker-side: capture + clear this thread's runtime-error slot (a
        // different thread-local than the reactor thread reads) so it can be
        // ferried back — the fork-join error-slot ferry (test-discovery.md §6).
        let err = crate::panic::take_runtime_error();
        if !lease.is_cancelled() {
            let published = tx.send((produced, err)).is_ok();
            #[cfg(test)]
            if published {
                ready_handoff_test_barrier(branch.io);
            }
            #[cfg(not(test))]
            let _ = published;
        }
    });

    // 3. Await completion (reactor thread parks here, freed for the poll
    //    partition). A dropped sender (rayon panic) yields the sentinel 0.
    let (result, err) = rx.await.unwrap_or((None, None));
    cancel_guard.complete();

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

    // 5. The guard released the permit after disarming cancellation — this
    //    increments the pool and wakes the front parked waiter.
    (idx, result)
}

#[cfg(test)]
#[derive(Default)]
struct ReadyHandoffBarrierState {
    published: bool,
    release: bool,
    finished: bool,
}

#[cfg(test)]
struct ReadyHandoffBarrier {
    state: std::sync::Mutex<ReadyHandoffBarrierState>,
    changed: std::sync::Condvar,
}

#[cfg(test)]
impl ReadyHandoffBarrier {
    fn new() -> Self {
        Self {
            state: std::sync::Mutex::new(ReadyHandoffBarrierState::default()),
            changed: std::sync::Condvar::new(),
        }
    }

    fn wait_until_published(&self) {
        let mut state = self.state.lock().unwrap();
        while !state.published {
            state = self.changed.wait(state).unwrap();
        }
    }

    fn release_and_wait_until_finished(&self) {
        let mut state = self.state.lock().unwrap();
        state.release = true;
        self.changed.notify_all();
        while !state.finished {
            state = self.changed.wait(state).unwrap();
        }
    }

    fn release(&self) {
        let mut state = self.state.lock().unwrap();
        state.release = true;
        self.changed.notify_all();
    }
}

#[cfg(test)]
struct ReadyHandoffBarrierGuard {
    branch: i64,
    barrier: std::sync::Arc<ReadyHandoffBarrier>,
}

#[cfg(test)]
impl ReadyHandoffBarrierGuard {
    fn wait_until_published(&self) {
        self.barrier.wait_until_published();
    }

    fn release_and_wait_until_finished(&self) {
        self.barrier.release_and_wait_until_finished();
    }
}

#[cfg(test)]
impl Drop for ReadyHandoffBarrierGuard {
    fn drop(&mut self) {
        self.barrier.release();
        let mut hook = READY_HANDOFF_TEST_HOOK.lock().unwrap();
        if hook
            .as_ref()
            .is_some_and(|(branch, _)| *branch == self.branch)
        {
            hook.take();
        }
    }
}

#[cfg(test)]
static READY_HANDOFF_TEST_HOOK: std::sync::LazyLock<
    std::sync::Mutex<Option<(i64, std::sync::Arc<ReadyHandoffBarrier>)>>,
> = std::sync::LazyLock::new(|| std::sync::Mutex::new(None));

#[cfg(test)]
fn install_ready_handoff_test_barrier(branch: i64) -> ReadyHandoffBarrierGuard {
    let barrier = std::sync::Arc::new(ReadyHandoffBarrier::new());
    let mut hook = READY_HANDOFF_TEST_HOOK.lock().unwrap();
    assert!(
        hook.is_none(),
        "only one ready-handoff barrier may be armed"
    );
    *hook = Some((branch, barrier.clone()));
    ReadyHandoffBarrierGuard { branch, barrier }
}

#[cfg(test)]
fn ready_handoff_test_barrier(branch: i64) {
    let barrier = READY_HANDOFF_TEST_HOOK
        .lock()
        .unwrap()
        .as_ref()
        .filter(|(armed_branch, _)| *armed_branch == branch)
        .map(|(_, barrier)| barrier.clone());
    let Some(barrier) = barrier else {
        return;
    };
    let mut state = barrier.state.lock().unwrap();
    state.published = true;
    barrier.changed.notify_all();
    while !state.release {
        state = barrier.changed.wait(state).unwrap();
    }
    state.finished = true;
    barrier.changed.notify_all();
}

/// The poll-shape partition of the two-pool join: each poll leaf is awaited on
/// the reactor via the async trampoline. `join_all` so distinct-token poll leaves
/// overlap on the ONE reactor thread (≈max not sum).
///
/// This partition takes no permit: the leaf's platform poll-fn acquires through
/// `ctx.acquire` and the reactor releases on `Ready` or cancel-drop
/// ([`await_poll_node`]). A branch-level acquire here would double-admit.
async fn run_poll_partition(
    branches: Vec<(usize, ParBranch)>,
    env: &crate::reactor::ReactorEnv<'_>,
) -> Vec<(usize, Option<ProducedValue>)> {
    let futs = branches.into_iter().map(|(idx, branch)| async move {
        let strand = crate::strand::next_strand();
        let outcome = run_io_trampoline_inner_async(branch.io, env, strand, branch.disposer).await;
        // A completed nested trampoline has transferred the raw value. Restore
        // its owner before consulting shared fault state; returning `None` then
        // drops the armed value rather than leaking it.
        let produced =
            outcome.map_completed(|value| ProducedValue::with_disposer(value, branch.disposer));
        let produced = if !crate::panic::has_runtime_error() && !crate::panic::has_dispatch_fault()
        {
            produced
        } else {
            None
        };
        (idx, produced)
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
/// trampoline steps further, is replaced — at which point the frame releases
/// its reference. Fresh Bind nodes are structurally consumed after the frame
/// acquires its own references to the inner node and continuation. Without these
/// releases the continuation-produced nodes would leak (O(N) for N Bind steps).
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
    run_io_trampoline_controlled(
        io_ptr,
        CancellationProbe::Never,
        crate::strand::StrandId::ROOT,
        ResultDisposer::NONE,
    )
    .into_raw()
}

fn run_io_trampoline_with_bridge(
    io_ptr: i64,
    lease: &crate::reactor::WorkerBridgeLease,
    strand: crate::strand::StrandId,
    terminal_disposer: ResultDisposer,
) -> TrampolineOutcome {
    run_io_trampoline_controlled(
        io_ptr,
        CancellationProbe::Bridge(lease),
        strand,
        terminal_disposer,
    )
}

fn run_io_trampoline_controlled(
    io_ptr: i64,
    cancellation: CancellationProbe<'_>,
    strand: crate::strand::StrandId,
    terminal_disposer: ResultDisposer,
) -> TrampolineOutcome {
    io_observer::emit(
        IoEventTag::TrampolineEnter,
        &IoEvent::TrampolineEnter { io_ptr },
    );
    let outcome = run_io_trampoline_inner(io_ptr, cancellation, strand, terminal_disposer);
    let result = match outcome {
        TrampolineOutcome::Completed(value) => value,
        TrampolineOutcome::Stopped => 0,
    };
    io_observer::emit(
        IoEventTag::TrampolineExit,
        &IoEvent::TrampolineExit { result },
    );
    outcome
}

/// The walk position after a `Pure`/`Effect`/`Par` arm has produced a result
/// value and consulted the continuation stack.
enum Step {
    /// The result was fed to a popped continuation; resume the loop on the
    /// continuation-produced node (always a fresh subtree).
    Advance(i64),
    /// The continuation stack was empty; the walk is complete with this value.
    Finish(i64),
    /// A bridge loser was cancelled before its next continuation call.
    Cancelled,
}

#[derive(Clone, Copy)]
enum CancellationProbe<'a> {
    Never,
    Bridge(&'a crate::reactor::WorkerBridgeLease),
}

impl CancellationProbe<'_> {
    fn is_cancelled(self) -> bool {
        match self {
            Self::Never => false,
            Self::Bridge(lease) => lease.is_cancelled(),
        }
    }
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

/// Project a child borrow through the lifetime of its live IO parent.
fn borrowed_io_field<'a>(parent: Borrowed<'a>, field_offset: isize) -> Borrowed<'a> {
    // SAFETY: `parent` brands the live node for this call. The caller selects a
    // field present in that node's closed IO layout, and the returned borrow is
    // narrowed to the parent's lifetime by this function's signature.
    unsafe { Borrowed::from_abi(read_node_field(parent.raw_for_read(), field_offset)) }
}

/// Read one Bind transition. A fresh parent is a frame-owned counted
/// reference, so acquire independent child references before structurally
/// releasing it. Caller-tree parents remain borrowed and untouched.
fn read_bind_transition(current: i64, current_is_fresh: bool) -> (i64, i64, ResultDisposer) {
    if !current_is_fresh {
        return (
            unsafe { read_node_field(current, FIELD_0_OFFSET) },
            unsafe { read_node_field(current, FIELD_1_OFFSET) },
            ResultDisposer(unsafe { read_node_field(current, FIELD_2_OFFSET) }),
        );
    }

    // SAFETY: `current_is_fresh` means the trampoline frame owns exactly the
    // continuation-produced reference represented by `current`.
    let parent = unsafe { Owned::from_abi(current) };
    let borrowed = parent.as_borrowed();
    let inner = borrowed_io_field(borrowed, FIELD_0_OFFSET).to_owned();
    let cont = borrowed_io_field(borrowed, FIELD_1_OFFSET).to_owned();
    let input_disposer =
        ResultDisposer(unsafe { read_node_field(parent.raw_for_read(), FIELD_2_OFFSET) });
    crate::drop::consume_io_tree(parent);
    (inner.into_raw(), cont.into_raw(), input_disposer)
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
    cont_stack: &mut Vec<ContinuationFrame>,
    current: i64,
    current_is_fresh: bool,
    value: ProducedValue,
    cancellation: CancellationProbe<'_>,
) -> Step {
    if cancellation.is_cancelled() {
        return Step::Cancelled;
    }
    match cont_stack.pop() {
        Some(cont) => {
            io_observer::emit(
                IoEventTag::ContPop,
                &IoEvent::Cont {
                    cont_ptr: cont.ptr,
                    is_fresh: cont.is_fresh,
                    new_depth: cont_stack.len() as u32,
                },
            );
            // Releasing the just-finished node: shallow-dec it if we produced
            // it ourselves (fresh subtree). A caller-tree node is left for the
            // caller's post-return `consume_io_tree`.
            if current_is_fresh {
                // SAFETY: a fresh completed current is owned by this frame.
                crate::drop::dec_shallow_io(unsafe { Owned::from_abi(current) });
            }
            // Same rule for the closure we're about to invoke: consume it only
            // if it was part of a fresh Bind.
            let new_io = call_continuation(cont.ptr, value.transfer(), cont.is_fresh);
            io_observer::emit(
                IoEventTag::BindExit,
                &IoEvent::BindExit {
                    new_current: new_io,
                },
            );
            Step::Advance(new_io)
        }
        None => {
            // Final node; shallow-dec only if fresh.
            if current_is_fresh {
                // SAFETY: a fresh final current is owned by this frame.
                crate::drop::dec_shallow_io(unsafe { Owned::from_abi(current) });
            }
            Step::Finish(value.transfer())
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

/// Force a `Pure` node, minting the consumer's reference where the node owns one
/// so the node keeps its own for later forces and its teardown
/// (`ownership-and-disposal.md` §6.1).
fn force_pure_node(node: i64, is_fresh: bool) -> i64 {
    // SAFETY: callers select this helper only after reading `IO_TAG_PURE`, so
    // ABI 10 guarantees the payload word and the witness word after it.
    let value = unsafe { read_node_field(node, FIELD_0_OFFSET) };
    // SAFETY: same ABI-10 shape; the witness is written only before publication.
    if let crate::drop::PurePayloadWitness::Owned(_) =
        unsafe { crate::drop::pure_payload_witness(node) }
    {
        crate::rc::rc_inc(value);
    }
    io_observer::emit(IoEventTag::PureStep, &IoEvent::PureStep { value, is_fresh });
    value
}

/// Force an `IO_TAG_EFFECT` node's thunk under the platform fault guard
/// (FIXME 0327, step 3 — the dispatch funnel).
///
/// Reads the thunk + resource token + baked fn-name from the node, emits the
/// `PlatformEffect` event, then forces the thunk via
/// `io_guard::force_effect_thunk_protected`. A fault in foreign platform code
/// (Rust panic or SIGFPE/SIGILL/SIGBUS/SIGSEGV) is captured into the
/// dispatch-fault slot (paired with the fn-name) for int to compose into
/// `PlatformError::DispatchError`. The thunk is borrowed: the node keeps it for
/// later forces and discharges it at teardown (`ownership-and-disposal.md` §6.2).
fn force_effect_node(node: i64) -> EffectStep {
    // SAFETY: `node` is the live `current` Effect node base pointer; its
    // thunk/token fields are within its payload.
    let thunk_ptr = unsafe { read_node_field(node, FIELD_0_OFFSET) };
    let resource_token = unsafe { read_node_field(node, FIELD_1_OFFSET) };
    // `scheduling_class: 0` is deliberate, not a placeholder. The class attaches
    // to platform symbols at registration time — `cranelisp_platform::SchedulingClass`,
    // derived onto `OwnedPlatformFnDescriptor.scheduling_class` from
    // `PlatformFn.concurrency` — and the trampoline has no back-reference to the
    // symbol. Extending the Effect node payload to carry it was considered and
    // rejected: `design/backend/io-scheduling.md` §"Scheduling class in trampoline
    // trace events" (resolution (b)). Consumers recover the class by correlating
    // this event with the originating `ParBind` classification trace.
    io_observer::emit(
        IoEventTag::PlatformEffect,
        &IoEvent::PlatformEffect {
            thunk_ptr,
            resource_token,
            scheduling_class: 0,
        },
    );
    let fn_name = read_effect_fn_name(node);
    // SAFETY: `thunk_ptr` is the Effect node's field 0, a live `CLIO::effect*`
    // thunk; the caller holds a counted reference to `node`, so teardown cannot
    // discharge it during this force.
    match unsafe { crate::io_guard::force_effect_thunk_protected(thunk_ptr, &fn_name) } {
        crate::io_guard::ForceOutcome::Value(v) => EffectStep::Value(v),
        crate::io_guard::ForceOutcome::Faulted => EffectStep::Aborted,
    }
}

/// A test `Effect` node built by the platform constructor, as a platform DLL
/// builds one, with the host allocator wired to this crate's. Its thunk returns
/// `value()`; its fn-name field is unstamped. A test frees it through the IO
/// teardown tail, which discharges the thunk.
#[cfg(test)]
pub(crate) fn test_effect_node(
    token: i64,
    capacity: i64,
    value: impl Fn() -> i64 + Send + Sync + 'static,
) -> i64 {
    static HOST: cranelisp_platform::HostContext = cranelisp_platform::HostContext::new();
    static WIRED: std::sync::Once = std::sync::Once::new();
    WIRED.call_once(|| {
        let callbacks = crate::host_callbacks();
        // SAFETY: `init` copies the callbacks out of the live local.
        unsafe { HOST.init(&callbacks) };
    });
    cranelisp_platform::CLIO::effect_on_resource_with_capacity(token, capacity, move || {
        cranelisp_platform::CLInt::from(value())
    })
    .into()
}

#[derive(Clone, Copy)]
struct ParBranch {
    io: i64,
    disposer: ResultDisposer,
}

/// Read a `Par` node's `count` and branch IO/disposer descriptors.
///
/// Par node layout: `[header | tag | count | io_0 | disposer_0 | …]`.
///
/// # Safety
/// `node` must be a valid `IO_TAG_PAR` node base pointer.
unsafe fn read_par_branches(node: i64) -> Vec<ParBranch> {
    let count = unsafe { read_node_field(node, FIELD_0_OFFSET) } as usize;
    (0..count)
        .map(|i| {
            let offset = FIELD_1_OFFSET + (i as isize) * 16;
            ParBranch {
                io: unsafe { read_node_field(node, offset) },
                disposer: ResultDisposer::from_raw(unsafe { read_node_field(node, offset + 8) }),
            }
        })
        .collect()
}

fn par_results_buffer(branches: &[ParBranch], results: Vec<ProducedValue>) -> ProducedValue {
    debug_assert_eq!(branches.len(), results.len());
    let results_buf = alloc_with_rc(8 + results.len() * 8) as i64;
    for (index, result) in results.into_iter().enumerate() {
        // SAFETY: the buffer was allocated with exactly one slot per result.
        unsafe {
            crate::heap_access::write_i64(
                results_buf,
                FIELD_0_OFFSET + (index as isize) * 8,
                result.transfer(),
            )
        };
    }
    ProducedValue::par_buffer(
        results_buf,
        branches.iter().map(|branch| branch.disposer).collect(),
    )
}

/// Run a `Par` node's branches, marshal their results into a fresh heap results
/// buffer, and return its base pointer (the value fed to the continuation).
///
/// Each branch recursion is itself a non-consuming trampoline run on a
/// caller-tree or fresh-tree branch — it dec's only its own fresh intermediates.
/// The branches themselves are left live for later `consume_io_tree` (caller
/// tree) or shallow-dec'd at the enclosing Par level (§3.5.6 detail unchanged).
fn run_par_node(
    parent_ptr: i64,
    cancellation: CancellationProbe<'_>,
    strand: crate::strand::StrandId,
) -> Option<ProducedValue> {
    // SAFETY: `parent_ptr` is the live `current` Par node base pointer.
    let branch_ptrs = unsafe { read_par_branches(parent_ptr) };
    let count = branch_ptrs.len();
    let results = dispatch_par_branches_with_trace(&branch_ptrs, parent_ptr, cancellation, strand)?;
    io_observer::emit(
        IoEventTag::ParJoin,
        &IoEvent::ParJoin {
            parent_ptr,
            count: count as u32,
        },
    );

    Some(par_results_buffer(&branch_ptrs, results))
}

/// Inner loop — all state-machine instrumentation lives here; the outer
/// `run_io_trampoline` wraps it solely to emit enter/exit bookends. Each node
/// arm delegates to a named helper (`force_effect_node`, `run_par_node`) and the
/// shared `feed_continuation` step; the loop body is the dispatcher.
fn run_io_trampoline_inner(
    io_ptr: i64,
    cancellation: CancellationProbe<'_>,
    strand: crate::strand::StrandId,
    terminal_disposer: ResultDisposer,
) -> TrampolineOutcome {
    let mut frame = TrampolineFrame {
        current: io_ptr,
        current_is_fresh: false,
        cont_stack: Vec::new(),
        armed: true,
    };

    loop {
        if cancellation.is_cancelled() {
            return TrampolineOutcome::Stopped;
        }
        let current = frame.current;
        let current_is_fresh = frame.current_is_fresh;
        let tag = unsafe { read_node_tag(current) };

        let edge_disposer = frame
            .cont_stack
            .last()
            .map_or(terminal_disposer, |cont| cont.input_disposer);

        // The value a Pure/Effect/Par arm produces, ready to feed to the next
        // continuation via the shared `feed_continuation` step. Bind descends
        // in-place and `continue`s without producing a value.
        let produced = match tag {
            t if t == IO_TAG_PURE => ProducedValue::with_disposer(
                force_pure_node(current, current_is_fresh),
                edge_disposer,
            ),
            t if t == IO_TAG_EFFECT => match force_effect_node(current) {
                EffectStep::Value(value) => ProducedValue::with_disposer(value, edge_disposer),
                // Abort: the fault is in the dispatch-fault slot. Return the
                // sentinel (0), mirroring the `runtime_panic` convention.
                EffectStep::Aborted => {
                    frame.armed = false;
                    return TrampolineOutcome::Stopped;
                }
            },
            t if t == IO_TAG_BIND => {
                let (inner, cont, input_disposer) = read_bind_transition(current, current_is_fresh);
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
                frame.cont_stack.push(ContinuationFrame {
                    ptr: cont,
                    is_fresh: current_is_fresh,
                    input_disposer,
                });
                io_observer::emit(
                    IoEventTag::ContPush,
                    &IoEvent::Cont {
                        cont_ptr: cont,
                        is_fresh: current_is_fresh,
                        new_depth: frame.cont_stack.len() as u32,
                    },
                );
                // current_is_fresh stays as-is: if we were fresh, the inner
                // (allocated by the same continuation) is also fresh; if we
                // were not, we're still descending the caller's tree.
                frame.current = inner;
                continue;
            }
            t if t == IO_TAG_PAR => match run_par_node(current, cancellation, strand) {
                Some(value) => value,
                None => return TrampolineOutcome::Stopped,
            },
            _ => panic!("cranelisp_run_io: unknown IO tag {tag}"),
        };

        match feed_continuation(
            &mut frame.cont_stack,
            current,
            current_is_fresh,
            produced,
            cancellation,
        ) {
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
                    frame.armed = false;
                    return TrampolineOutcome::Stopped;
                }
                frame.current = new_io;
                frame.current_is_fresh = true;
            }
            Step::Finish(value) => {
                frame.armed = false;
                return TrampolineOutcome::Completed(value);
            }
            Step::Cancelled => return TrampolineOutcome::Stopped,
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
        // SAFETY: a fresh continuation transfers its closure owner here.
        crate::drop::consume_closure(unsafe { Owned::from_abi(cont_ptr) });
    }
    new_io
}

// --- Par dispatch with resource token serialization ---

/// Read the resource token from an IO node — tag-agnostic over the two effect
/// kinds (§2.6 / §13.4): BOTH `IO_TAG_EFFECT` (blocking) and `IO_TAG_EFFECT_POLL`
/// (poll-shape) store the token at FIELD_1_OFFSET (abs offset 32). Non-effect
/// nodes (Pure, Bind, Par) return 0 (unrestricted). Production callers are the Par
/// admission paths (`run_blocking_branch`, `dispatch_par_branches_with_trace`);
/// a poll leaf's own admission does not read this slot ([`await_poll_node`]).
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
/// nodes default to capacity 1 (they carry no pool). The production caller is
/// `run_blocking_branch`; a poll leaf's own admission does not read this slot
/// ([`await_poll_node`]).
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
/// (int's `src/exe.rs::define_cstr_data` convention — read without a length channel)
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
    positioned: Vec<(usize, ProducedValue)>,
    error: Option<String>,
    cancelled: bool,
}

/// Work item for Par dispatch.
enum WorkItem {
    /// A single branch to run independently (token=0).
    Single(usize, ParBranch),
    /// A group of branches to run sequentially (same non-zero resource token).
    SerialGroup(Vec<(usize, ParBranch)>),
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
fn dispatch_par_branches_with_trace(
    branches: &[ParBranch],
    parent_ptr: i64,
    cancellation: CancellationProbe<'_>,
    strand: crate::strand::StrandId,
) -> Option<Vec<ProducedValue>> {
    use rayon::prelude::*;
    use std::collections::HashMap;

    // Group branches by resource token.
    let mut token_groups: HashMap<i64, Vec<(usize, ParBranch)>> = HashMap::new();
    for (i, &branch) in branches.iter().enumerate() {
        let token = read_resource_token(branch.io);
        token_groups.entry(token).or_default().push((i, branch));
    }

    // Build work items.
    let mut work_items: Vec<WorkItem> = Vec::new();
    for (&token, entries) in &token_groups {
        if token == 0 {
            // Each unrestricted branch is independent.
            for &(idx, branch) in entries {
                io_observer::emit(
                    IoEventTag::ParSpark,
                    &IoEvent::ParSpark {
                        parent_ptr,
                        branch_idx: idx as u32,
                        token,
                    },
                );
                work_items.push(WorkItem::Single(idx, branch));
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
            WorkItem::Single(idx, branch) => {
                let result = if cancellation.is_cancelled() {
                    None
                } else {
                    let outcome = run_io_trampoline_controlled(
                        branch.io,
                        cancellation,
                        strand,
                        branch.disposer,
                    );
                    let produced = outcome.map_completed(|value| {
                        ProducedValue::with_disposer(value, branch.disposer)
                    });
                    if cancellation.is_cancelled() {
                        None
                    } else {
                        produced
                    }
                };
                // Worker-side: capture and clear this thread's slot so it does
                // not pollute later rayon work on the same thread.
                let err = crate::panic::take_runtime_error();
                ItemResult {
                    positioned: result.into_iter().map(|value| (idx, value)).collect(),
                    error: err,
                    cancelled: cancellation.is_cancelled(),
                }
            }
            WorkItem::SerialGroup(entries) => {
                let mut positioned = Vec::with_capacity(entries.len());
                let mut error: Option<String> = None;
                let mut cancelled = false;
                for (idx, branch) in entries {
                    if cancellation.is_cancelled() {
                        cancelled = true;
                        break;
                    }
                    let outcome = run_io_trampoline_controlled(
                        branch.io,
                        cancellation,
                        strand,
                        branch.disposer,
                    );
                    // Re-arm immediately after the nested trampoline transfers
                    // its terminal raw value. Any following error/cancellation
                    // branch then disposes it by dropping `produced`.
                    let produced = outcome.map_completed(|value| {
                        ProducedValue::with_disposer(value, branch.disposer)
                    });
                    if let Some(e) = crate::panic::take_runtime_error() {
                        error = Some(e);
                        // A capacity-1 token group is observably sequential in
                        // source order. Once this entry fails, later entries
                        // have not started and the enclosing structured join
                        // aborts as-if ordinary left-to-right evaluation.
                        break;
                    }
                    if cancellation.is_cancelled() {
                        cancelled = true;
                        break;
                    }
                    if error.is_none()
                        && let Some(value) = produced
                    {
                        positioned.push((idx, value));
                    }
                }
                ItemResult {
                    positioned,
                    error,
                    cancelled,
                }
            }
        })
        .collect();

    // Place results in correct positions; re-raise the first ferried error into
    // the joining thread's slot (first-error-wins matches sequential semantics).
    let mut results: Vec<Option<ProducedValue>> = (0..branches.len()).map(|_| None).collect();
    let mut cancelled = cancellation.is_cancelled();
    for item in item_results {
        cancelled |= item.cancelled;
        for (idx, val) in item.positioned {
            results[idx] = Some(val);
        }
        if let Some(msg) = item.error {
            crate::panic::set_runtime_error(msg);
        }
    }

    if cancelled {
        return None;
    }
    results.into_iter().collect()
}

#[cfg(test)]
mod tests;
