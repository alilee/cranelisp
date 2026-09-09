# `poll_support` + the web/stdio v7 adoption — Solution Design

**Sprint 96, Chunk A (the substrate-adoption keystone). Pre-implementation —
evidence-first.** Subordinate to `design/platform/platform.md` (the master);
elaborates the new `concurrency`-gated `poll_support` module and how the two
in-tree model platforms (`web`, `stdio`) adopt the ABI-v7 poll-shape async-leaf
model. The cross-crate seams it rides on are owned elsewhere and only *referenced*
here:

- the **acquire-around-poll lifecycle** + the RAII `Permit` drop-guard + the
  token-capacity `Semaphore` pool — `design/intrinsics/reactor.md` §2.6 / §2.8 (sibling
  `/design` int);
- the **poll-node bake** (`IO_TAG_EFFECT_POLL` + the host-built state-closure env
  layout) — `design/backend/io-trampoline.md` §12 (sibling `/design` backend);
- the async-leaf C-ABI contract types (`HostCtx`, `Waker`, `WakerVTable`, `PollFn`,
  `ConcurrencyDescriptor`) — `crates/cranelisp-platform/
  src/concurrency.rs`, `design/arch/effect-concurrency.md` §12 (**`/arch`-owned —
  read-only**), `design/arch/platform-interface.md` §6.8. (The dual-channel
  `ConcurrentPlatformFn` / `ConcurrentPlatformManifest` named in this Chunk-A
  doc were **deleted** in the later single-ABI cutover — see the banners below;
  the types are now core/ungated, absorbed into the unified `PlatformFn` /
  `PlatformManifest`.)

> **Evidence-first ordering — this design is the *target the hand-rewrite
> converges to*, not a speculative pre-abstraction (Principle 8; Phase-2 scope
> item 2; /arch sign-off "(1) evidence-first extraction").** The Chunk-A `/dev`
> work order is: (a) hand-rewrite the simplest poll leaf (`stdio` `read_line`)
> against the **raw** R1 state-closure env layout + the **raw** `HostCtx`/`Waker`
> vtable; (b) hand-rewrite `web`'s `accept`/`read` over a connection token, with
> the idiom pain surfacing; (c) **then** extract `poll_support` from the repeated
> idiom — the typed env accessor, the fd/timer scaffold, the `PollState` phase
> scaffold. The macro convergence (§4) is a parallel, independent cleanup. This
> doc records what the extracted suite **should** contain (anticipated from the
> two-platform shape below) so the hand-rewrite has a target to converge on; it is
> a **net subtraction** (it retires the ~105-line `declare_concurrent_platform!`
> mirror), not a new layer. **Nothing in `poll_support` is built before the
> evidence exists.**

> **S96 Chunk-B v8 update (FIXME 0465 resolution).** This doc was authored in
> Chunk A against the v6/v7 *coexistence* envelope (`#[cfg(feature =
> "concurrency")]`, ABI-v7, the two-macro `declare_platform!` /
> `declare_concurrent_platform!` split). The S96 **single-ABI v8 cutover**
> (SPRINT.md §"Single-ABI cutover"; `platform-interface.md` §6.8.0) superseded that:
> ONE `declare_platform!` macro (per-fn `descriptor:` = poll / `scheduling:` =
> blocking), the ABI types are **core/ungated**, and the reactor is **always
> present** (one async trampoline; the `concurrency` / `concurrency-runtime`
> features are retired). Read §2's `#[cfg(feature = "concurrency")]` gates as
> *retired* and §4's two-arm macro convergence as **superseded** (one macro needs no
> convergence — §4 banner). The **scaffolds (§2), the value-source rule (§3.4), and
> the web connection model (§3.2 / §3.4.5) stand** — only the gating/macro envelope
> changed. **§3.5 (new) makes the web connection-handle cranelisp interface concrete
> on v8 — the ADTs, the poll-leaf signatures, the destructuring wrappers, and the
> serve-loop reshape — resolving FIXME 0465** (the Chunk-B keystone; co-designed with
> the slice-5 server demo).

> **S97 MODEL PIVOT — the callback-`ctx`-vtable handle model SUPERSEDES the v9
> descriptor cut (user-ratified + `/arch`-ratified 2026-06-30; `effect-concurrency.md`
> §4.1.1, `platform-interface.md` §6.8.0b, `bounded-contexts.md` §5, `interfaces.md`
> §"Resource scheduling").** The descriptor-as-representation-overhead model in the
> banner immediately below (a fixed-offset `ResourceDesc {token, capacity}` **header
> slot** on resource-handle ADTs, a `desc_out` out-param on `PollFn`, the trampoline
> stamp/read) is **RETIRED**. It hit a structural blocker at Wave-2 implementation: an
> opaque zero-field `Connection []` minted *inside the DLL* (`CLAdt::construct` → a
> 24-byte object) had no room for a 16-byte header slot stamped at `value+24` (heap
> overrun), and reserving that slot at the DLL-mint→host-alloc boundary was an
> undesigned cross-crate interface. The ratified replacement is **simpler and dissolves
> the blocker** — scheduling state never touches the value at all:
> - **NO header slot, NO `desc_out`, NO `ResourceDesc` type, NO `AsRawFd`-style trait.**
>   `PollFn` / `Poll` are **UNCHANGED** (`poll(state, *HostCtx, *Waker) -> Poll`).
> - **Handles are opaque ADTs carrying the platform's `r`/`fd` in a GENUINE field** —
>   `(deftype Connection [...])` with a real opaque field (web: `r == fd`); the platform
>   built the handle and reads `r` back out of its own field; the trampoline never
>   introspects it. Because the field is real, `CLAdt::construct` mints a normal
>   N-field object — the Wave-2 24-vs-40-byte overrun cannot arise.
> - **All runtime scheduling flows through a trampoline-owned `ctx` vtable** (the
>   generalized `HostCtx`) the poll-fn calls: `acquire(token, cap, waker) → Acquired |
>   Parked`, `register_{readable,writable,timer}(source, waker)`, `retire(token)`.
>   **Release is trampoline-owned** (fired on `Ready`/cancel, keyed by effect identity;
>   cancel never re-enters the poll-fn) — NOT a vtable call.
> - **The leaf's `role`** (`None`/`Produce`/`Consume`/`Retire`, on
>   `ConcurrencyDescriptor.role`) is a **compile-time-only manifest fact** grounding
>   inference E2 + codegen; the trampoline does NOT branch on it at runtime.
>
> **What this re-cascades in THIS doc** (Wave 0, S97; `platform-interface.md` §6.8.0b
> cascade list): **§3.5** (web) is rewritten — `Connection` is an opaque ADT with a
> genuine `fd` field (not the dead `[]` + header slot); the leaf sigs lose every
> `desc_out`/header carrier. **§3.6** is rewritten — the leaf-authoring contract is the
> **ctx-vtable poll-fn skeleton** (acquire/register/retire + tramp-owned release), NOT
> the `desc_out` env contract; the four leaf roles incl. **Retire** are documented.
> **§3.1** (stdio) re-expresses the singleton stdin token (0471, carried) as the poll-fn
> calling `acquire(STDIN_TOKEN, 1, waker)`. The §2 scaffolds stand, with two pivots: the
> `desc_of`/`set_desc` `PollEnv` helpers the descriptor cut added are **deleted**, and
> the `Reactor` scaffold (§2.2) grows `acquire`/`retire` wrappers over the new vtable
> entries. The two-module `web.cl`/`serve.cl` split (FIXME 0469) + the load-order rule
> (§3.6.3) + the singleton stdin token (FIXME 0471) **carry forward UNCHANGED**.
> **Everything below the "S97 ABI v8→v9 update" banner that describes a header slot,
> `desc_out`, `ResourceDesc`, or `Connection []` is SUPERSEDED** — read it for
> provenance only.

> **[SUPERSEDED by the MODEL PIVOT banner above.] S97 ABI v8→v9 update (FIXME 0482;
> /arch Phase-2 RATIFIED, `platform-interface.md`
> §6.8.0b + `effect-concurrency.md` §4.1.1 + BC §3/§5/§6 + `interfaces.md`
> §"Resource descriptor").** This doc was authored against the **v8 leading-pair**
> convention — the per-connection `(token, capacity)` rode into user source as the two
> leading positional leaf args, the backend baked them from positional operands
> (`inject_poll_leading_pair`, §3.4), and `web/Connection` was `[token capacity fd]`.
> **v9 deletes that mechanism.** The resource descriptor `(token, capacity)` becomes
> **trampoline-owned representation overhead — like the RC/heap header — type-invisible,
> never a leaf argument, never part of an ADT's logical shape.** Three carriers (the
> /arch ruling, adjusted from 0482's literal "widen `Poll::Ready`"):
> - **Storage** — a fixed-offset `ResourceDesc {token, capacity}` **header slot** on
>   resource-handle ADTs (uniform across types; the trampoline reads it with no per-ADT
>   "token is field N" knowledge). `interfaces.md` §"Resource descriptor" owns the layout.
> - **Produce carry** — a produce leaf writes `*desc_out` (a new `PollFn` out-param
>   `poll(state, host, waker, desc_out) -> Poll`); the trampoline **stamps** it into the
>   produced value's header. `Poll` stays single-register `#[repr(i32)]`; the value still
>   flows through `set_result` (the descriptor is the ONLY new return-side channel).
> - **Consume read** — before polling a consume leaf the trampoline **reads** the
>   descriptor off the consumed handle's header (acquire-around-poll). The consume leaf
>   takes **no `desc_out` and no leading-pair args**.
> - **Role** (`None`/`Produce`/`Consume`) is a **per-effect static manifest fact** on
>   `ConcurrencyDescriptor.role`, NOT a per-value descriptor field — "Produce" is a fact
>   about the *leaf*, not the connection.
>
> **What this supersedes in THIS doc:** read **§3.4** (the v8 `inject_poll_leading_pair`
> value-source derivation) as **SUPERSEDED for resource leaves** (the §3.4 banner) — the
> positional bake is deleted; the descriptor no longer flows as cranelisp operands. **§3.5
> is rewritten for v9** below: `Connection` is **fully opaque** (web recovers `fd` from
> `token == fd` in the header), leaf sigs slim to `read-conn : (Fn [Connection] (IO
> Request))`, and the wrapper-placement / load-order question (FIXME 0469) + the singleton
> stdin token (FIXME 0471, §3.1) are resolved here. **§3.6 (new)** is the general
> `desc_out` Produce/Consume leaf-authoring contract + the load-order platform-authoring
> rule. The §2 scaffolds stand; `PollEnv` grows one descriptor-reader helper (§3.6). The
> v9 cut lands as **ONE atomic change-set** across `cranelisp-types`, `cranelisp-platform`,
> backend, int, and every in-tree platform DLL (`ABI_VERSION` 8 → 9; "no users").

---

## 1. Why a `poll_support` module at all

The C-ABI poll contract (`concurrency.rs`; introduced at ABI v7, core/ungated since the v8 single-ABI cutover — current stamp v9) gives a platform author the raw C-ABI: a
`PollFn = unsafe extern "C" fn(state: *mut c_void, host: *const HostCtx, waker:
*const Waker) -> Poll`. Three things are repeated, error-prone, and `unsafe` in
every poll leaf, and S95's synthetic `async-demo` / `timer_write_pollfn` leaves
already paid the cost by hand:

1. **Reading args / writing the result out of `state`.** The `state: *mut c_void`
   *is* the host-built state-closure env (io-trampoline §12.2): a result slot at a
   fixed offset, then the marshaled i64 args, then leaf scratch. Every poll-fn
   does raw pointer arithmetic against that R1 convention — exactly the kind of
   hand-rolled offset math that drifts (the same class of bug the `schema.rs`
   field-by-name parser exists to prevent on the ADT side).
2. **Registering fd/timer readiness on `WouldBlock`.** Every leaf calls
   `(*host).register_readable(host_data, fd, waker)` (or `_writable` /
   `_timer`) through the vtable, with the `*const Waker` plumbing and the
   `WouldBlock`-vs-error branch repeated each time.
3. **Distinguishing first-poll setup from re-poll resume.** The host re-polls the
   same `PollFn` after each wake. The leaf must remember "have I opened the fd
   yet?" across polls — phase state that lives in the env scratch and is
   hand-encoded as a sentinel today.

`poll_support` codifies these three into a small, total helper layer (authored
`concurrency`-gated; core/ungated since the v8 single-ABI cutover) so a leaf
author writes intent (`"try the syscall; if it'd block,
tell the host to wake me"`), not offset math. The **descriptor** (the trust
assertion — token/capacity/blocking), the **syscall** (the platform's domain),
and the **result interpretation** (what the i64 means) stay hand-written — those
are the irreducible per-platform parts.

*(Historical — Chunk-A authoring state.)* The module was `#[cfg(feature =
"concurrency")]` throughout, entering neither the default build nor the frozen
`public-api.txt` edge — the `_neg` frozen-edge guard
(`tests/facade_pif_rows.rs::concurrency_descriptor_absent_from_default_public_api_neg`)
kept it off the default surface byte-identical-when-off, exactly as the v7
contract types were. The v8 single-ABI cutover **retired the `concurrency`
feature**: `poll_support` and the contract types are core/ungated, on the default
`public-api.txt` edge (top banner).

---

## 2. The three scaffolds (the extraction target)

### 2.1 Typed env accessor — `PollEnv` (codifies the R1 env-layout convention in one place)

The single home for the host-built state-closure env layout. Today every poll-fn
re-derives the offsets from io-trampoline §12.2 by hand:

```
state (= env base) →
  +0   result_slot : i64   (poll-fn writes its i64 result here — the FIXED, descriptor-independent offset)
  +8   arg_0 : i64         (marshaled effect arg 0)
  +16  arg_1 : i64
  ...                      (one slot per effect arg)
  +N   scratch...          (leaf-private)
```

> **Offset note.** io-trampoline §12.2 places the result slot at **closure**
> offset 32 (`base + header(16) + code_ptr(8) + drop_glue(8)`). The poll-fn
> receives `state` = the env base = the closure's first env slot, i.e. the result
> slot at `state + 0`, args at `state + 8 + 8*i`. `PollEnv` is constructed from the
> `state: *mut c_void` the host passes, and is the **single place** that encodes
> this relationship — if the backend's env layout ever moves a slot, this is the
> one edit, not every leaf. (The result-slot-first recommendation from
> io-trampoline §12.2 is what makes the accessor's `result()` a fixed `state + 0`
> read — coordinate any change with `/design` backend, who owns the bake.)

Shape (illustrative — the surface the hand-rewrite converges to):

```rust
#[cfg(feature = "concurrency")]
pub struct PollEnv { base: *mut i64 }   // = state as *mut i64

impl PollEnv {
    /// SAFETY: `state` is the host-built state-closure env (io-trampoline §12.2).
    pub unsafe fn new(state: *mut c_void) -> Self { … }

    /// Marshaled effect arg `i` (i64 — scalar value or heap base pointer).
    pub fn arg(&self, i: usize) -> i64 { … }          // *(base + 1 + i)
    /// Arg `i` reinterpreted as a `CL*` wrapper (the marshaling layer).
    pub fn arg_as<T: CLType>(&self, i: usize) -> T { … }

    /// Write the single i64 result the generalized `EffectPoll` reads on Ready.
    pub fn set_result(&self, v: i64) { … }            // *(base + 0) = v
    pub fn set_result_cl<T: CLType>(&self, v: T) { self.set_result(v.to_raw()) }

    /// Leaf-private scratch slot `j` (after the args) — the phase scaffold (§2.3)
    /// is built on top of this.
    pub fn scratch(&self, j: usize) -> *mut i64 { … }
}
```

`arg_as`/`set_result_cl` reuse the existing `CLType::to_raw` marshaling — the
accessor adds *no new marshaling*, only the offset discipline. Reading a heap
arg that the leaf retains across a `Pending` boundary still uses the existing
`CLOwned`/`into_owned_consuming` capture-RC protocol (master §"Capture-RC
Protocol") — the env accessor does not change RC ownership, it only locates the
i64.

### 2.2 fd-readiness / timer poll scaffold — over the host/waker vtable

A thin, safe wrapper over the three `HostCtx` `register_*` callbacks + the
`*const Waker`, turning the raw vtable call into a one-liner the leaf calls on
`WouldBlock`:

```rust
#[cfg(feature = "concurrency")]
pub struct Reactor<'h> { host: *const HostCtx, waker: *const Waker }

impl<'h> Reactor<'h> {
    pub unsafe fn new(host: *const HostCtx, waker: *const Waker) -> Self { … }

    /// Ask the host reactor to re-poll this effect when `fd` is readable.
    pub fn wake_on_readable(&self, fd: RawFd) { /* (*host).register_readable(host_data, fd, waker) */ }
    pub fn wake_on_writable(&self, fd: RawFd) { … }
    pub fn wake_on_timer(&self, deadline_nanos: u64) { … }

    // --- v9 ctx-vtable: the token-permit half (the leaf calls these itself) ---

    /// Acquire a permit on `token`'s capacity-`N` pool. `Acquired` ⇒ hold a permit and
    /// proceed; `Parked` ⇒ no permit free — the host enqueued `waker` on the token's
    /// permit-wait queue, so the leaf returns `Pending` (backpressure, §3.6.1).
    /// Idempotent per in-flight effect (the host keys held permits by the waker's data
    /// identity), so a re-poll re-calls it without double-counting — no "already
    /// acquired?" flag on the leaf. Release is **trampoline-owned** (on `Ready`/cancel);
    /// `Reactor` has no `release`.
    pub fn acquire(&self, token: u64, capacity: u32) -> Acquire { /* (*host).acquire(host_data, token, capacity, waker) */ }

    /// A Retire/`close` leaf ends the resource's scheduling identity after `close(r)`.
    /// Idempotent; wakes any token-parked waiters to observe the gone resource.
    pub fn retire(&self, token: u64) { /* (*host).retire(host_data, token) */ }
}
```

It exists to (a) hide the `(*host).vtable_fn(host_data, …)` indirection and the
`host`/`waker`-handle threading, and (b) give the leaf a single, named verb per
readiness kind **and per token-permit op**. It owns **no reactor state** — the host
owns the *when* and the permit pool (§12 A2 model + §4.1.1 ctx-vtable); this is purely
the platform-side projection of "register interest" / "ask for a permit." Cancellation
needs no leaf cooperation: the host ceases to poll, drops the node, and **releases the
permit it holds** (trampoline-owned, keyed by effect identity, never re-entering the
poll-fn); `Reactor` registers and acquires, it never blocks and never releases.

### 2.3 first-poll / re-poll phase scaffold — `PollState`

The host re-invokes the same `PollFn` after every wake, so a leaf must carry
"which phase am I in" across polls. `PollState` (the type that **lost its S95
consumer to the blocking-carrier decision** — Phase-2 scope item 2) is that phase
discriminator, stored in an env scratch slot (§2.1) so it survives across
`Pending` returns and is torn down by the state-closure `drop_glue_ptr`:

```rust
#[cfg(feature = "concurrency")]
#[repr(i64)]
pub enum PollPhase { Unstarted = 0, Established = 1, /* leaf-defined ≥ 2 */ }

pub struct PollState<'e> { slot: *mut i64 }   // a PollEnv scratch slot

impl<'e> PollState<'e> {
    pub fn phase(&self) -> i64 { … }
    pub fn set_phase(&self, p: i64) { … }
    /// The idiom: run `setup` exactly once (first poll), then `resume` each poll.
    /// Returns `Poll::Pending` from `setup` if the first syscall would block.
    pub fn drive(
        &self,
        setup:  impl FnOnce() -> PollStep,   // open fd, first non-blocking syscall
        resume: impl FnOnce() -> PollStep,   // re-attempt after a wake
    ) -> Poll { … }
}

/// What a phase step decided: done with a result, or parked on a readiness.
pub enum PollStep { Ready(i64), Park }
```

`drive` encodes the first-poll-vs-re-poll branch once (the env scratch sentinel is
`Unstarted` on the host-built node's zero-initialized scratch — io-trampoline §12.2
inits the env, so `0 = Unstarted` falls out for free). `PollStep::Park` is the
leaf saying "I registered a readiness via §2.2; wake me." `PollStep::Ready(v)`
writes through `PollEnv::set_result` and returns `Poll::Ready`. **No leaf re-enters
admission** (gate (a) requirement 2 — see §3.2): `drive` is pure phase logic over
the scratch slot, it never dispatches another effect.

### 2.4 What `poll_support` deliberately does NOT own

- **The descriptor.** Token/capacity/blocking are the platform's trust assertion;
  the leaf author writes the `ConcurrencyDescriptor` literal in the
  `declare_platform!` invocation (the per-fn `descriptor:` key). `poll_support`
  never synthesizes one.
- **The syscall + result meaning.** `TcpListener::accept`, `read`, the i64 the
  result slot carries — all hand-written. The scaffold locates and registers; it
  does not interpret.
- **The reactor / the permit pool / release.** All host-side (reactor.md). The platform
  *expresses intent* via the `ctx` vtable (`acquire`/`register_*`/`retire`) but **never
  sees a `Semaphore`, never holds a permit object, and never releases** — it calls
  `acquire`, returns `Poll`, and the host owns the permit pool + the tramp-owned release
  (on `Ready`/cancel). This is the thin-platform thesis (§12 / §4.1.1): platforms own the
  *what* + *which token*, the host owns the *when* + the permit *lifecycle*.
- **The token derivation, but NOT a codegen operand.** Under v9 (ctx-vtable model)
  there is **no codegen operand injection at all** — the `inject_poll_leading_pair`
  pass and the positional leading-pair are **deleted** (the §3.4 banner; backend's only
  v9 delta is the deletion). The leaf **computes the token from the handle it holds**
  (web: `token == fd`, read from `Connection`'s genuine `fd` field) and calls
  `ctx.acquire(token, capacity, waker)` *itself* in the poll-fn — `poll_support` exposes
  the `Reactor::acquire` wrapper (§2.2), but the *value* (which token, what capacity) is
  the platform's trust assertion, hand-written. `poll_support` never derives the token
  and never places an operand; it only wraps the vtable call.

---

## 3. web + stdio v7 adoption

### 3.1 `stdio` — the "simple platform ports cleanly" ergonomics check

`stdio` has two effects (master §"cranelisp-stdio Design"):

- **`print` stays blocking v6.** It is `SchedulingClass::Sequential`,
  ordering-critical (output must appear in program order), and never blocks long
  enough to matter — the poll model buys it nothing. It remains a
  `declare_platform!` (v6) `CLIO::effect` thunk, **untouched**. This is the
  byte-identical-off witness: a platform can mix v6 blocking + v7 poll effects, and
  the default (no-`concurrency`) host sees only the v6 shape.
- **`read_line` is the poll candidate.** It blocks on stdin readiness — the
  textbook poll leaf. Rewritten as a `PollFn`: first poll registers
  `wake_on_readable(STDIN_FILENO)` and parks; on wake, a non-blocking read either
  completes (write the `CLString` result via `PollEnv::set_result_cl`) or re-parks.

  **v9 (ctx-vtable) — the manifest-static serial token (resolves FIXME 0471
  STRUCTURALLY; CARRIES from the descriptor cut, re-expressed in ctx-vtable terms).**
  `read-line : (Fn [] (IO String))` takes **no operands** and produces **no per-value
  handle**: stdin is a *process singleton*, not a resource minted per value. So there
  is **no handle to project a token from** — and (under the ctx-vtable model) no header
  slot and no `desc_out` either. v9 gives the singleton a clean home: a **manifest-static
  serial token** declared on the effect —
  `read-line : { token: STDIN_TOKEN != 0, capacity: 1, role: Consume }`. **The poll-fn
  itself** calls `acquire(STDIN_TOKEN, 1, waker)` on that **constant** at the start of
  each poll — the token is read from the effect's `ConcurrencyDescriptor` (a process
  constant baked into the leaf), **not off any value** and **not from an operand**. On
  `Acquired` it does the non-blocking read: completes ⇒ `PollEnv::set_result_cl` the
  `CLString` + `Ready`; would-block ⇒ `register_readable(STDIN_FILENO, waker)` + `Pending`.
  On `Parked` (the only way to hit it is a *second* concurrent `read-line`) it returns
  `Pending` *before* the read; the host re-polls it when the first releases. The host
  **releases** the STDIN permit on `Ready`/cancel (trampoline-owned). Because the token
  is a fixed non-zero singleton at **capacity 1**, admission permits **at most one
  in-flight `read-line`** — single-in-flight stdin is enforced **by construction**, not
  by the v6 host `STDIN_BUF` `Mutex` + serial-use convention (FIXME 0471's latent gap: a
  `Commutative`, `token == 0` leaf acquires no permit, so nothing structurally barred
  two concurrent reads racing `STDIN_BUF`). It is a `/platform`-owned descriptor edit (the
  `read-line` manifest entry in `platforms/stdio`); **no backend/trampoline change** —
  there is no positional injection (deleted at v9) and no header to stamp, the leaf calls
  `acquire` itself. This is the canonical "serial resource with no handle object" case of
  the uniform poll-fn skeleton (§3.6.1).

`stdio` is the ergonomics check: if porting *one trivial blocking read* to a poll
leaf is more than "register readiness; resume on wake; set result," `poll_support`
is missing a scaffold. It is the smallest evidence input and the first thing `/dev`
hand-rewrites (§"implement first").

### 3.2 `web` — the connection-token model (the gate-(a) non-re-entry property)

`web` is the reference workload. The v6 platform (master / `exemplar/platforms/web`)
is a single-stream blocking `listen`/`accept`/`send` (one accepted `TcpStream`
held in a process-global `Mutex` between `accept` and `send`). The v7 rewrite turns
the connection lifecycle into poll-shape leaves over a **per-connection token**:

| Effect | v6 (then-current, at S96 authoring) | v7 (target) |
|---|---|---|
| `listen` | blocking `bind`, store listener | stays simple: a one-shot poll (or v6 blocking) that binds the listener. Mints **nothing** per-call; the listener is the long-lived resource. |
| `accept` | blocking `accept()`, hold stream | **poll-shape**: park on the listener fd's readable readiness; on wake, `accept()` a connection and **mint a FRESH connection token** for it; return a `web/Request`-bearing value (or a connection handle) carrying that token. |
| `read` (was internal `read_request`) | inline inside `accept` | **poll-shape**, **rides the connection token from `accept`**: park on the connection fd readable; on wake, read+parse one HTTP request. |
| `send` | blocking write+close | **poll-shape (or blocking)**, **rides the same connection token**: park on the connection fd writable; on wake, write the response and close. |

**The non-re-entry property gate (a) relies on (and this design guarantees):**

1. **`accept` mints a *fresh* connection token; `read`/`send` ride it.** The
   listener has its own token (the accept loop's admission point); each accepted
   connection gets a **distinct** token. So the pool's "distinct token ⇒
   independent capacity" rule (arch §5) makes different connections concurrent **by
   construction**, with no annotation in the handler — the launch-and-continue
   fan-out (Chunk B) over `accept` produces a stream of distinct-token connections,
   each handled independently. This is exactly the property reactor.md §2.8 and
   arch §4 (token disjointness) require.
2. **A poll-fn never re-enters admission on its own token (gate (a) req. 2).** The
   acquire-around-poll permit (reactor.md §2.8, Chunk-A int work) wraps the whole
   establish→ready arc of *one* `EffectPoll` at the trampoline's single admission
   gate. The web leaves are sound by construction: `accept`'s poll-fn does not
   dispatch another effect on the listener token; `read`/`send` poll-fns do not
   dispatch another effect on their connection token. `poll_support`'s `PollState::
   drive` is pure phase logic over scratch — it has **no path that dispatches an
   effect**, so a leaf *cannot* self-deadlock by re-entering admission on its
   exhausted token. (The §2.3 prose states this constraint normatively; the `/dev`
   leaf must not call back into the effect machinery from a poll-fn.)

**The reactor connection pool — the real capacity-on-poll consumer.** Each accepted
connection draws a **fresh per-connection token** (the accepted socket fd) at
**capacity 1** — serial *within* one connection (read→send are dataflow-ordered,
§8.2). The in-flight-**connection-COUNT** ceiling `N` is **not** a per-connection
capacity (this corrects the loose "capacity N per connection" wording here and in
§3.4.5, to match arch §16): `N` lives on the `Listener` handle and bounds the
**Chunk-B launch-and-continue fan-out** via the slice-4 global admission budget
(arch §16's "backpressure on accept"), composing `min(capacity, degree)`. The
capacity-**N** *per-token pool* mechanism is the DB-pool / `poll-pool`-test-leaf
case (§3.4.6), **not** web connections.

> **SUPERSEDED (top banner — ctx-vtable model).** The remainder of this paragraph
> describes the v8 leading-pair carrier (the `.cl` wrapper places `(token, capacity)` as
> two leading operands; the backend `inject_poll_leading_pair` pass bakes them to node
> offsets 32/40). Under the ratified v9 **ctx-vtable** model the `(token, capacity)` is
> **neither a cranelisp operand nor a value-header slot** — the **leaf computes the token
> from its handle** (web: `token == fd`, off `Connection`'s genuine `fd` field) and calls
> `ctx.acquire(token, capacity, waker)` itself; nothing is baked onto the node and the
> backend's only v9 delta is **deleting** the bake. The **fresh-per-connection-token
> model + the gate-(a) non-re-entry property above STAND** (they are about the *model*,
> not the carrier); both the leading-pair carrier below AND the intermediate
> header-slot/`desc_out` carrier are retired. See §3.5 (web concrete) + §3.6 (the
> ctx-vtable leaf-authoring contract).

On the v8 poll carrier the `(token, capacity)`
are **runtime operands** the `.cl` wrapper (§3.5.3) places as the two leading args of
the call (token = the connection fd, capacity = 1); the **backend `inject_poll_leading_pair`
pass** (NOT `poll_support`) is the codegen lowering that delivers them to
`compile_poll_effect`, which bakes them into the `IO_TAG_EFFECT_POLL` node's
reserved slots (token @ abs 32, capacity @ abs 40; io-trampoline §14 / reactor.md
§2.9). The full derivation — the injection-point-vs-value-source split (resolving
FIXME 0463), the `scheduling_class` discriminator, and the connection lifecycle —
is **§3.4**. `poll_support` itself never places codegen operands. The
acquire-around-poll lifecycle (the permit held across the `EffectPoll`
establish→ready arc, released on Ready **and on drop** via the RAII `Permit`) is
the Chunk-A int deliverable; this design only requires that the web leaves **park
cleanly** (return `Poll::Pending`, holding only the permit slot while freeing the
reactor thread) so the acquire-around-poll permit wraps every web leaf and parked
leaves overlap on the one reactor thread. The capacity-N "(N+1)th parks" analogue of
S95's blocking-carrier test is exercised by the `poll-pool` test leaf (§3.4.6, a
shared token); for web the in-flight-**connection-count** ceiling `N` is the
**Chunk-B** global-admission-budget concern (§3.5.6), not a per-connection capacity
(reactor.md §2.9).

**Request/Response ADTs are unchanged.** `web/Request` / `web/Response` stay
ordinary `.cl` ADTs marshaled via `CLAdt<T>` + the embedded `web.platform-schema`
(master §, `adt.rs`) — the poll rewrite changes *when* the effect completes
(poll vs block), not *what* crosses the boundary. The `accept` poll-fn still
`CLAdt::<Request>::construct`s on the read-complete phase; `send`'s poll-fn still
`read_field`s the `Response`. The capture-RC protocol applies as today to any heap
value the leaf retains across a `Pending` boundary (e.g. the in-flight `Response`
between `send`'s park and write) — `CLOwned` it.

**The serial serve loop survives (Chunk A is a permanent baseline).** Chunk A
ships the poll-shape web platform under the *existing serial* serve loop (one
`accept`→handle→`send` at a time); the fan-out (many concurrent handlers bounded
by admission) is **Chunk B**. So this design must not assume launch-and-continue;
the leaves must be correct under a single in-flight connection (capacity-1 token)
AND ready to overlap under capacity-N when Chunk B fans out. The connection-token
model above satisfies both: at capacity 1 it is today's behavior; at capacity N it
overlaps — same mechanism (arch §8, "distinct token ⇒ independent capacity; shared
token ⇒ shared pool").

### 3.3 Consistency with the sibling seams (referenced, not duplicated)

- **acquire-around-poll + RAII `Permit`** — `design/intrinsics/reactor.md` §2.6/§2.8.
  This doc requires only that web/stdio leaves return `Poll::Pending` on park and
  never block; the permit lifecycle, the pool, and the A→C cancellation-releases-
  permit contract are int's. **No contradiction found** — the platform side is
  permit-agnostic (it never sees one), which is exactly what the lock-free
  reactor-thread admission (reactor.md §2.8) needs.
- **poll-node bake + env layout** — `design/backend/io-trampoline.md` §12. The
  `PollEnv` accessor (§2.1) is the *consumer* of the env layout the backend bakes;
  the result-slot-first-at-`state+0` relationship is the one coordination point.
  **No contradiction found** — §2.1's offset note adopts io-trampoline §12.2's
  recommendation verbatim. If `/design` backend moves the result slot off
  first-env-slot, `PollEnv::set_result` is the single platform-side edit (flagged
  here so the seam stays single-sited).

### 3.4 Live `(token, capacity)` derivation — the A4 generalization (resolves FIXME 0463)

> **SUPERSEDED for resource leaves by ABI v9 (top banner; `platform-interface.md`
> §6.8.0b).** §3.4 designs the **v8 leading-pair** value-source: the platform's
> `.cl`/`poll_support` wrapper places `(token, capacity)` as the two leading cranelisp
> operands and the backend `inject_poll_leading_pair` pass bakes them from those
> positional args into the poll node's offset-32/40 slots. **v9 deletes this entire
> mechanism for resource leaves** — `(token, capacity)` is no longer a cranelisp value,
> no longer a leaf argument, and the backend stops baking from positional args. Under the
> ratified v9 **ctx-vtable** model the `(token, capacity)` is **not stored anywhere on a
> value** (neither operand nor header slot) — **the leaf computes the token from the
> handle it holds and calls `ctx.acquire(token, capacity, waker)` itself** in the poll-fn.
> The §3.4.2 `scheduling_class`-keyed inject-vs-leave-alone branch, the §3.4.3
> token-as-positional-arg derivation, the §3.4.4 capacity-as-operand choice, and the
> §3.4.5 web leading-pair lifecycle are all **retired**; their v9 replacements are §3.5
> (web concrete) + §3.6 (the ctx-vtable leaf-authoring contract). §3.4 is retained as the
> historical v8 design record (the model the v8 server shipped on); read it for
> provenance, not as the live contract. **The §3.4.6 `poll-pool` G1 test leaf survives as
> a v9 leaf** — its poll-fn `acquire`s the `(token, capacity)` from its own explicit args
> via the ctx vtable instead of carrying them as a baked leading pair; `/qa` re-pins the
> rows against the ctx-vtable carrier.

This is the load-bearing A4 refinement: how the S95 `(0, 1)` sentinel pass
(`cranelisp_backend::inject_poll_leading_pair`, landed A2b) GENERALIZES to LIVE
`(token, capacity)` for real resource leaves — **without a `cranelisp-types` touch
and without an `ABI_VERSION` bump** (Phase-2 public-API ruling, SPRINT.md
Architecture review).

#### 3.4.1 The injection POINT vs the value SOURCE (FIXME 0463 reconciliation)

Two roles, two owners — kept distinct (FIXME 0463 is filed because earlier prose,
incl. io-trampoline §14.2's SEAM note, attributed the *injection* to `poll_support`,
which is not realizable — a runtime-Rust helper layer inside a poll-fn cannot place
codegen operands at a cranelisp call site):

- **The injection POINT is the backend `MonoExpr` pass** `inject_poll_leading_pair`
  (`compile_to_module_impl`, the production `codegen_view` path). It is the *single*
  lowering site that makes a poll-shape call reach `compile_poll_effect` in the
  strict-peel form `arg_vals = [token, capacity, leaf_0, …]`. This is **codegen**, not
  platform Rust. The leading-pair operand convention + the bake offsets (token @ abs 32,
  capacity @ abs 40) are **stable** (io-trampoline §14, the /arch RESOLVED ruling);
  A4 changes only the *value source*, never the point or the convention.
- **`poll_support` (and the platform's `.cl` surface) is the value SOURCE for resource
  leaves** — it defines HOW the live `(token, capacity)` are *derived* (token = the
  resource handle; capacity = the pool ceiling) and *placed as explicit leading
  operands of the cranelisp call* so the backend peel finds them. `poll_support` never
  injects codegen operands; it shapes the source-level call (the same way the blocking
  `pool-demo` leaf makes `(token, capacity)` explicit cranelisp args — S95). The
  `(0, 1)` tokenless constants are the degenerate case this generalizes.

So A4 **SUBSUMES** `inject_poll_leading_pair` (not adds alongside it): the one pass
learns a per-leaf rule for what the leading pair is. It must not blindly prepend
`(0, 1)` ahead of a leaf that already carries a live pair, or it would clobber the
real `(token, capacity)`.

#### 3.4.2 The per-leaf rule — keyed on `scheduling_class` (the no-types-touch discriminator)

The pass must distinguish, per poll-shape effect, "this leaf carries an explicit live
`(token, capacity)`" from "this leaf is tokenless — synthesize the sentinel." The
discriminator is **`scheduling_class`**, which **already rides
`DefKind::PlatformEffect { scheduling_class, poll_shape, got_slot }`** (a long-standing
field; the v7 loader derives it from the descriptor via
`ConcurrencyDescriptor::nearest_scheduling_class`). Reading it is a **backend-internal**
change: `resolve_poll_effect_target` (which already returns `(module, got_slot,
param_types)`) is extended to also surface the already-destructured `scheduling_class`.
**No `cranelisp-types` edge, no new field, no ABI bump** — exactly the constraint the
Phase-2 ruling fixes.

| Poll leaf (`poll_shape: true`) | `scheduling_class` | What the backend pass does | `(token, capacity)` source |
|---|---|---|---|
| **Tokenless** (bare timer; `stdio read_line`; `async-demo async-read`) | `Commutative` (descriptor `token 0, cardinality 0`) | **INJECT** the constants `(0, 1)` ahead of the natural args (the A2b behaviour, now *gated* on `Commutative`) | synthesized constants — `token 0` ⇒ no-acquire / unrestricted, `capacity 1` ⇒ serial |
| **Resource / pool** (`web accept`/`read`/`send`; the `poll-pool` G1 test leaf) | `ResourceSerial` (descriptor `token 0, cardinality 1`) | **DO NOT inject** — the source/wrapper already supplies `[token, capacity, leaf_0, …]`; the existing A2 strict peel bakes them live | the cranelisp call's two leading operands (explicit args for the test leaf; the `.cl`/`poll_support` wrapper for web) |

This **reuses the convention S95 already established** for the blocking carrier:
`pool-demo` declares `ResourceSerial` and carries `(token, capacity)` as its two
leading cranelisp args (`pool-read : (Int token, Int capacity, Int ms) -> IO Int`).
The poll carrier is symmetric — only the dispatch (reactor vs rayon) differs.

> **Why the backend pass needs no "which arg is the resource handle" logic.** For a
> `ResourceSerial` leaf the SOURCE has already placed `token` (= the resource handle,
> or a value derived from it) at operand 0, `capacity` at operand 1, and **re-passed
> the handle as `leaf_0`** (operand 2 → env `capture(1)` → the poll-fn's fd at
> `state+8`, `PollEnv::arg(0)`). The pass peels positionally; it identifies nothing.
> The "resource handle = `leaf_0` re-passed" half of the /arch convention is honored
> by the wrapper/source, not the codegen pass. `poll_shape: bool` stays the SOLE
> *bake* discriminator (the peel is one uniform path); `scheduling_class` gates only
> the *producer* decision inject-vs-leave-alone — not a second node discriminator, and
> not a bake-side branch. (`Sequential` poll leaves — rare — inject `(1, 1)`:
> global-serial token 1, capacity 1; documented for completeness.)

#### 3.4.3 Token derivation — the resource handle is a RUNTIME value

The token is the **resource handle the effect operates on** — a runtime i64, not a
compile-time constant:

- For the **G1 `poll-pool` test leaf** and any leaf whose admission coordinate is
  *separate from* its work args (the `pool-demo` shape), `token` is an **explicit
  cranelisp argument** the caller passes. No handle re-pass — the leaf has no fd; the
  leaf args are operands `2..`. The test source dials the per-row token/capacity
  literally (mirrors S95 `POOL_*`).
- For a **resource leaf that also needs the handle as its syscall fd** (`web read`/
  `send` over a connection; `accept` over the listener), the `.cl`/`poll_support`
  wrapper places the handle BOTH as `token` (operand 0) AND re-passed as `leaf_0`
  (operand 2). The poll-fn then finds its fd in the env at `state+8` exactly as today
  — the leading-pair peel does not shift any arg the poll-fn relies on (io-trampoline
  §14.2).

A **tokenless** leaf stays `(0, …)` because it is `Commutative` ⇒ the pass injects
`token = 0` (the `async-demo` timer, `stdio read_line` — neither operates on a pooled
resource; `read_line`'s serial-stdin discipline is a capacity-1 concern the host
imposes, not a token the leaf carries).

#### 3.4.4 Capacity derivation — a runtime operand, NOT a static field (option chosen + rejected)

Capacity is a per-**resource** ceiling (the pool size). The three options evaluated
(SPRINT.md A4 brief):

- **(a) ride the descriptor / manifest the backend reads — REJECTED.** The static
  `ConcurrencyDescriptor.cardinality` is NOT lifted onto `DefKind::PlatformEffect` (the
  loader lifts only `scheduling_class` + `poll_shape`); reading a live capacity-N this
  way would require **adding a field to `DefKind::PlatformEffect`** = a forbidden
  `cranelisp-types` touch. It also contradicts the ratified model: capacity is "per
  resource, platform-supplied **dynamically** at the effect site, **not** a `DefKind`
  field" (effect-concurrency.md §5/§8.1). The static `cardinality` stays *documentation
  + the v6 bridge*, never the live value.
- **(b) a value the platform's `.cl`/`poll_support` wrapper supplies at the effect
  site — CHOSEN.** Capacity is an **ordinary runtime i64 operand** the source places at
  operand 1, exactly like the token. For the G1 test leaf it is an explicit arg. For
  web it is supplied by the wrapper (Chunk A: the constant `1` — serial within a
  connection under the serial serve loop; the genuinely dynamic pool size `N` is
  carried in the connection handle and destructured by the wrapper when Chunk B fans
  out, §3.4.5). This satisfies io-trampoline §14.1 (capacity must be on the node BEFORE
  the first poll, because acquire precedes establish) — it is a Value at the effect
  site that the backend bakes at construction; **no reactor-narrows-at-first-poll**.
- **(c) bundle capacity in the resource handle — the Chunk-B/dynamic-pool refinement,
  a special case of (b).** When a pool's size is a runtime config (`(listen addr :pool
  N)`), the handle minted by `accept` encodes `(token, N)` and the wrapper destructures
  it into the two leading operands. Still option (b) at the codegen seam (two runtime
  operands the backend peels); only the *provenance* of the capacity operand is the
  handle rather than a literal.

**Confirmation: no `cranelisp-types` touch, no ABI bump.** token/capacity are i64
operands; the discriminator is the existing `scheduling_class`; the node layout is the
S95 48-byte 3-field shape (only the *values stored* change). If a future slice needs a
capacity that genuinely cannot be expressed as a source operand — i.e. it must ride a
new `DefKind`/descriptor field the backend reads — that is an `/arch` interface
decision and MUST be escalated via FIXME; **A4 does not need it.**

#### 3.4.5 The web connection pool lifecycle (the real capacity-on-poll consumer)

Walking §3.2's connection-token model with the live values pinned:

1. **`(listen addr :pool N)`** binds the listener (a one-shot poll or v6 blocking
   leaf). It mints **nothing per-connection**; the long-lived **listener handle**
   records the pool ceiling `N`.
2. **`accept`** is a `ResourceSerial` poll leaf on the **listener token**. Its wrapper
   supplies `(listener_token, accept_capacity, listener_handle)`. On the read-ready
   phase it `accept()`s a connection and **mints a FRESH connection token** for it,
   returning a connection value that carries `(fresh_token, 1, fd)` — a fresh
   per-connection token (= the accepted fd) at **capacity 1** (serial within the
   connection, §8.2; the pool ceiling `N` lives on the `Listener`, not the connection
   — §3.5). The fresh token makes distinct connections concurrent **by construction**
   (arch §5 "distinct token ⇒ independent capacity") — the gate-(a) non-re-entry
   property (§3.2): `accept`'s poll-fn never re-enters admission on the listener token.
3. **`read`/`send`** are `ResourceSerial` poll leaves **riding the connection token**.
   Their wrapper destructures the connection value: `(conn_token, conn_capacity,
   conn_handle)` — token from the connection, capacity **1** (serial within the
   connection, §8.2), handle re-passed as `leaf_0` (the connection fd at `state+8`). The
   in-flight-**connection-count** ceiling `N` is enforced at the **Chunk-B
   launch-and-continue fan-out** by the slice-4 global admission budget (read off the
   `Listener`), **not** by a per-connection capacity-N — arch §16; see §3.5.
4. **The per-connection capacity is `1`** (serial within a connection); the
   connection-**count** ceiling `N` is set on the `Listener` at `listen` time and
   consumed by the Chunk-B fan-out admission (arch §16) — distinct from the per-token
   capacity the node carries. Both are runtime operands the wrapper places and the
   backend peels — no static field, no `DefKind` capacity (effect-concurrency.md §8.1).

#### 3.4.6 The G1 `poll-pool` test leaf (authored WITH /dev, Gap G1)

The 4 RED `concurrency_poll_capacity.rs` rows expect a **poll-shape analogue of the
blocking `pool-demo`** — a `poll-pool` platform whose effects declare `(token,
capacity)` at the effect site and route to the **reactor** (suspend/resume on an armed
timer), not rayon. Shape (mirrors `pool-demo`, flips green when A2+A3+the live carrier
land):

- `poll-read  : (Int token, Int capacity, Int ms) -> IO Int` — poll-shape armed-timer
  leaf; suspend/resume on the reactor; capacity-pooled; returns `ms`.
- `poll-write : (Int token, Int capacity, Int ms) -> IO Int` — a DISTINCT poll effect
  on the **same** token (the token-sharing case); returns `ms`.
- `poll-log   : (Int token, Int capacity, Int ms, String tag) -> IO Int` — poll-shape;
  prints `tag` to real stdout (the within-token source-order witness); returns `ms`.

Declared via `declare_platform!` (each effect's per-fn `descriptor:` = poll) with each
effect's descriptor mapping to
`ResourceSerial` (`token 0, cardinality 1, blocking 0`) so the backend pass leaves the
source-supplied leading pair intact and the A2 peel bakes the live `(token, capacity)`.
token/capacity/ms are explicit cranelisp args (no handle re-pass — the timer leaf has
no fd; leaf args are operands `2..`). Add it to `tests/scripts/build-link-prereqs.sh`.
It is a **platform effect** (not stdlib), preserving the free-standing-test rule.

---

### 3.5 The web connection-handle cranelisp interface (v9 ctx-vtable — opaque Connection with a genuine `fd` field; resolves FIXME 0465 + 0469)

> **Rewritten for the ctx-vtable model (top banner; `platform-interface.md` §6.8.0b,
> `effect-concurrency.md` §4.1.1).** Two prior shapes are superseded: the v8
> `web/Connection [token capacity fd]` (leading pair destructured into every leaf call)
> AND the intermediate v9-descriptor `Connection []` (fully empty, scheduling in a hidden
> header slot stamped via `desc_out`). The ratified model is between them: `Connection`
> is **opaque but carries a GENUINE `fd` field** holding the platform's `r` (`r == fd`)
> — a real ADT field the platform reads back, NOT a hidden header slot. The leaf computes
> the token from that field and calls the `ctx` vtable itself. §3.6 is the general
> ctx-vtable leaf-authoring rule this section instantiates for web.

§3.2 / §3.4.5 describe the web connection-token *model*; this section pins the
**concrete v9 cranelisp surface** — the connection-handle ADTs (opaque, with a genuine
`fd` field), the platform poll-leaf signatures (the leaf projects the token from the
handle's `fd` field + calls `ctx.acquire`/`register_*`; no leading pair, no `desc_out`),
the **two-module** wrapper placement (FIXME 0469), and the serial serve-loop reshape.
`/port` owns the `.cl` files (`exemplar/web.cl`, `exemplar/serve.cl`,
`exemplar/main.cl`); `/platform` owns the poll-fns
(`exemplar/platforms/web/src/lib.rs`); this section is the **interface both implement
against** (Phase-5 D/D/R). It is the **SERIAL** serve loop (the permanent baseline).
The launch-and-continue fan-out (sibling `/design` intrinsics — `effect-concurrency.md`
§10, `reactor.md` §5) is *referenced* (§3.5.5), not designed here; the connection
threading below is shaped so the fan-out drops in without touching the leaves or
wrappers.

#### 3.5.1 The handle ADTs (`exemplar/web.cl`, /port-owned) — Connection is tramp-opaque (user-readable) with a genuine `fd` field

`web/Request` / `web/Response` are unchanged (§3.2 — platforms still do not declare
ADTs; the backend regenerates `web.platform-schema`). The two handle ADTs:

```clojure
;; web/Listener — the bound TCP listener. ORDINARY ADT, not a per-poll resource handle:
;; nothing acquires a "listener token" around a poll (accept is structurally serial in
;; the serve loop, §3.5.5).
;;   fd   : listener socket fd — a GENUINE field; accept reads it to poll on
;;          listener-readable and to accept() the next connection.
;;   pool : N, the in-flight-CONNECTION-COUNT ceiling — consumed by the
;;          launch-and-continue fan-out (slice-4 global admission budget, arch §16),
;;          NOT a per-connection capacity. A genuine field.
(deftype Listener [:primitives/Int fd :primitives/Int pool])

;; web/Connection — one accepted HTTP connection. TRAMP-OPAQUE handle (user-readable)
;; carrying a GENUINE `fd` field. For web `r == fd`, so the connection fd lives in an
;; ordinary ADT field the PLATFORM reads back (it built the handle); the TRAMPOLINE never
;; introspects it. It is NOT opaque to the user — user code may destructure/`match` it open
;; to read the fd (it is the program's own connection); the opacity is toward the trampoline.
;; The token is PROJECTED from this fd by the poll-fn (token == fd) — it is NOT stored
;; (no header slot, no desc_out, no ResourceDesc). The value is a normal 1-field object
;; = HeapHeader(16) + tag(8) + fd(8); `CLAdt::construct` mints it directly.
(deftype Connection [:primitives/Int fd])
```

**Opacity — it is toward the TRAMPOLINE, not the user (per `/arch`'s ruling — BC §5 /
`interfaces.md` §"Resource scheduling" / `effect-concurrency.md` §4.1.1).** `Connection` is
**tramp-opaque, user-readable**. The load-bearing invariant is **tramp-opacity**: the
*trampoline* never introspects the handle — it threads the value from `accept` to
`read`/`send`/`close` without ever reading its fields — and only the *platform* (which built
the handle via `CLAdt::construct`) reads `r`/`fd` back out of the field (`CLAdt`/schema,
§3.5.4). That is what lets **all** scheduling live in the `ctx` vtable with zero
value-carried scheduling state; the handle is scheduling-invisible.

It is **NOT opaque to the user**. `Connection` is an ordinary 1-field ADT: user code CAN
read the genuine field by ordinary destructuring / `match` — `(match c [(Connection fd) fd])`
typechecks and yields the real fd. It is the program's own connection, so reading its own
datum is expected. There is no language mechanism that makes an ADT non-user-destructurable,
and none is invented here — the analogy is `std`'s `TcpStream` *with `as_raw_fd()` available*,
not a `RawFd` no user can reach. (The retired "present but not user-destructurable" / "does
not export a user destructuring path" framing wrongly attributed a non-invariant to `/arch`;
it is dropped.)

**Fabrication is a platform-IO concern, not a host-soundness one.** User *construction* of a
`Connection` (forging an fd) does not threaten host soundness: the OS syscall is the capability
checkpoint, so a bad or unowned fd fails safely as an `EBADF`-class IO error — recoverable at
`catch-runtime-error` — never host UB. See `/arch`'s full ruling in `effect-concurrency.md`
§4.1.1 ("Handle fabrication is a platform-IO concern…").

**Why `Connection` carries a genuine `fd` field, not the dead `[]`+header-slot shape.**
For web the connection's only datum is its fd, and the platform's internal choice is
`token == fd`. The fd is a **real opaque ADT field the platform reads back**, NOT a
type-invisible header slot the trampoline stamps — so `CLAdt::construct` mints a normal
1-field object and the Wave-2 24-vs-40-byte overrun (the descriptor cut's blocker) never
arises. The live OS resources (`TcpListener`, accepted `TcpStream`) stay in
platform-internal maps keyed by fd — only the i64 fd crosses the boundary (the standard
fd-as-handle pattern), now in a genuine field. This retires the process-global
`Mutex<ServerState>` of the v6 platform.

> **The escape hatch — multiple genuine fields compose normally.** If a future platform
> needs more handle data than the syscall fd — e.g. `token != fd` (a virtual / NAT'd /
> multiplexed fd, where the admission token is a pool id distinct from the syscall fd) —
> it simply adds more opaque fields (`(deftype Connection [:primitives/Int fd
> :primitives/Int pool-id])`) and projects the token from whichever field(s) it chooses
> in its poll-fn. There is no header slot to coordinate with — the handle is an ordinary
> opaque ADT, and the token is always a *projection the platform computes*, never a
> stored datum. Web simply has one genuine field (`fd`) and projects `token == fd`.

#### 3.5.2 The platform poll-leaf signatures (`exemplar/platforms/web`, /platform-owned)

Four effects in ONE `declare_platform!` manifest (mixed blocking + poll). The sigs
**slim** — no leading `(token, capacity)` pair; the handle IS the leaf argument:

| effect | role (`ConcurrencyDescriptor.role`) | FQ signature | how scheduling is driven |
|---|---|---|---|
| `bind-listener` | blocking (`scheduling: Sequential`; role `None`) | `(Fn [Int Int] (IO web/Listener))` | none — `Listener` is not a per-poll resource handle |
| `accept-conn` | poll, **Produce** | `(Fn [web/Listener] (IO web/Connection))` | drives acquire/register on the listener fd; at `Ready` mints `Connection{fd: new_fd}` carrying the fresh `r` |
| `read-conn` | poll, **Consume** | `(Fn [web/Connection] (IO web/Request))` | reads `fd` off the `Connection` field; `acquire(read_tok(fd), 1, waker)` itself; parks on readable |
| `send-conn` | poll, **Consume** | `(Fn [web/Connection web/Response] (IO Int))` | reads `fd` off arg 0; `acquire(write_tok(fd), 1, waker)`; parks on writable; `Response` is arg 1 |

- **`bind-listener`** is a plain blocking `CLIO::effect` (a bind is fast; no poll-fn).
  It binds the listener, chooses `N`, and `CLAdt::<Listener>::construct`s
  `(listener_fd, N)` — both **genuine fields**. Role `None`: nothing acquires a listener
  token. Blocking + poll effects coexist in one manifest exactly as stdio's mixed
  manifest does.
- **`accept-conn`** is `role: Produce`. Its `Listener` arg arrives in the env at
  `PollEnv::arg(0)` (the ADT base ptr); the poll-fn reads `Listener.fd` (a genuine field,
  via `CLAdt`/schema). During establishment there is **no program handle yet**, so the
  Produce leaf drives acquire/register on the **listener fd** it is establishing on:
  `register_readable(listener_fd, waker)` + `Pending` until readable, then on wake
  `accept()`s a new fd. It then `CLAdt::<Connection>::construct`s `Connection{fd: new_fd}`
  carrying the fresh `r` and `Ready`s it through `set_result`. The handle **materializes
  only at the `Ready` edge** — no header stamp, no `desc_out` (both deleted). `accept` is
  **structurally serial** in the serve loop (§3.5.5), so role `Produce` (not `Consume`)
  is correct: it produces a handle, it does not consume a prior handle's admission.
- **`read-conn` / `send-conn`** are `role: Consume`. Their `Connection` arg arrives at
  `PollEnv::arg(0)`; the poll-fn reads `fd` off the `Connection`'s genuine field
  (§3.5.4), **projects the per-direction token** (`read` ⇒ `read_tok(fd)`, `send` ⇒
  `write_tok(fd)` — distinct, so read/write on one connection do not serialize against
  each other, §3.6.1 full-duplex), and **calls `acquire(token, 1, waker)` itself** at the
  start of each poll. On `Acquired` it parks on the connection fd's readable/writable
  readiness; on wake it reads/writes. The host **releases** the permit on `Ready`/cancel.
  `send-conn`'s `Response` is `PollEnv::arg(1)`.

**Env layout under v9** (no leading-pair peel, no `desc_out` slot — `PollFn` is
unchanged): the result slot @ `state+0`; the **handle** (`Listener` for accept,
`Connection` for read/send) @ `state+8` = `PollEnv::arg(0)`; `Response` ADT base ptr
(`send-conn` only) @ `state+16` = `PollEnv::arg(1)`. The poll-fn computes the token from
the handle's `fd` field and supplies `capacity` (the platform's trust assertion: `1` per
connection) directly to `acquire` — both are the *platform's* values, never baked onto a
value or read off a header.

#### 3.5.3 Wrapper placement — the TWO-MODULE split (resolves FIXME 0469)

Under v9 (ctx-vtable) the friendly verbs are near-trivial pass-throughs — the
destructuring is **gone** (no leading pair to thread; no descriptor to read or write):

```clojure
;; exemplar/serve.cl  (NOT web.cl — see the load-order constraint below)
(import [web [Listener Connection]])              ; the sig-referenced ADT module
(import [platform.web [bind-listener accept-conn read-conn send-conn]])

(defn listen [port n] (bind-listener port n))     ; blocking; returns Listener
(defn accept [listener] (accept-conn listener))   ; Produce; mints opaque Connection
(defn read   [conn]     (read-conn conn))         ; Consume; token projected from conn.fd
(defn send   [conn resp] (send-conn conn resp))   ; Consume
```

**The 0469 load-order constraint — why these wrappers CANNOT live in `web.cl`.** FIXME
0469 (confirmed empirically S96 Chunk B) found that putting these wrappers in
`web.cl` — the module that **declares the handle ADTs** — does not compile. The cause
is the platform-load pre-resolve (`platform-interface.md` §7.2, `src/platform.rs::
referenced_sig_modules`): loading the `web` platform DLL **resolves + compiles the
`.cl` type-modules its sigs reference BEFORE the platform is registered**. The web sigs
reference `web/Listener`/`web/Connection`/`web/Request`/`web/Response`, so `(platform
web)` fully loads + typechecks the `web` module **first**. If `web.cl` carried
`(import [platform.web …])`, that import would resolve against a platform **not yet
registered** → a hard `ModuleError` (`module 'platform.web' not found (imported by
'web')`). An FQ `platform.web/…` call has the same defect (FQ auto-load would try to
load `platform.web` as a `.cl` module mid-platform-load — the same cycle).

So the resolution splits the placement across **two `/port`-owned modules** (the
interface — ADTs, sigs, ctx-vtable scheduling model — is unchanged; only *where the
wrappers live* moves):

| module | contents | imports | loaded |
|---|---|---|---|
| `exemplar/web.cl` | the `web/*` **deftypes ONLY** (`Listener`, `Connection`, `Request`, `Response`) — **no platform import, no wrappers** | none (or other ADT modules) | by the platform-load pre-resolve (it is sig-referenced) — must stay platform-import-free |
| `exemplar/serve.cl` (the wrapper module) | the `listen`/`accept`/`read`/`send` wrappers | `[web [Listener Connection]]` + `[platform.web […]]` | only when `main.cl` imports it — **after** `(platform web)` — breaking the cycle |
| `exemplar/main.cl` | the serve loop | `[serve [listen accept read send]]` + `[web [Request Response]]` | by the program | the program |

The "plumbing out of `main.cl`" intent (the v8 §3.5.3 goal) is preserved — the
plumbing lives in `serve.cl`, just not in `web.cl`. **The general platform-authoring
rule this constraint generalizes to is §3.6.3** (`/arch` flagged it as model-independent
and worth stating regardless — it governs *any* platform whose sigs reference `.cl`
ADTs, not just web). `accept-conn`'s poll-fn mints the fresh `Connection{fd: new_fd}`
(an opaque value carrying the new `r` in its genuine field) and `set_result`s it — no
header stamp, no `desc_out`.

#### 3.5.4 poll_support consumption — web is the 3rd consumer; NO new env helper, `Reactor` grows acquire/retire

The three §2 scaffolds serve the web leaves with **no new `PollEnv` helper** — the
ctx-vtable model adds nothing to the env layout (no header slot, no `desc_out`). The
*only* §2 change is on the `Reactor` scaffold (§2.2), which grows the `acquire`/`retire`
wrappers over the new vtable entries. The descriptor cut's `desc_of`/`set_desc` PollEnv
helpers are **deleted** (there is no descriptor slot to read or write):

- **`PollEnv`** (§2.1) — reads `arg(0)` = the handle ADT base ptr (`Listener` /
  `Connection`), `arg(1)` = `Response` ptr; writes the result via `set_result` /
  `set_result_cl`. The leaf reads the connection `fd` as an **ordinary opaque ADT field**
  off `arg(0)` via the existing `CLAdt` / `web.platform-schema` path (`Connection.fd`) —
  the same accessor it uses for `Listener.fd`; **no descriptor-offset helper.**
- **`Reactor`** (§2.2) — `wake_on_readable(listener_fd)` (accept, fd from `Listener.fd`),
  `acquire(read_tok(conn_fd), 1)` + `wake_on_readable(conn_fd)` (read, fd from
  `Connection.fd`), `acquire(write_tok(conn_fd), 1)` + `wake_on_writable(conn_fd)` (send).
  The leaf computes the token from the fd field and calls `acquire`/`register_*` itself.
- **`PollState::drive`** (§2.3) — first poll `acquire`s + registers readiness + parks;
  resume re-`acquire`s (idempotent) + re-attempts the syscall; `Ready(result)` on
  completion (the host releases the permit).

Two web-specific parts stay **hand-written** (§2.4 "what `poll_support` does NOT own"):
(a) the **ADT construct/read on the ready phase** — `accept-conn` constructs
`Connection{fd: new_fd}` (a normal 1-field object via `CLAdt::construct`) + reads
`Listener.fd`; `read-conn` constructs a `Request`; `send-conn` reads a `Response` — via
the existing `CLAdt` / `web.platform-schema` path; (b) the **capture-RC** of the
`Response` retained across `send-conn`'s park→write boundary (`CLOwned` it). The token
projection (`fd` → `read_tok`/`write_tok`) is the platform's trust assertion (§3.6.1),
hand-written; `poll_support` only wraps the `acquire`/`register_*` calls — no scaffold
beyond `Reactor::acquire`/`retire`.

#### 3.5.5 The serial serve loop + the fan-out seam (`exemplar/main.cl`)

Structurally **unchanged from the v8 §3.5.5** — the connection still threads
accept→read→send via ordinary binding, and `Connection` is still a self-contained
handle (self-contained *because* it carries its `fd` in its own genuine opaque field,
from which the platform projects the token). The serial loop:

```clojure
(import [serve [listen accept read send]])
(import [web [Request Response]])

(defn port [] 8080)
(defn pool-size [] 64)      ; N — the fan-out in-flight ceiling (inert under the serial loop)

(defn serve-loop [listener]
  :(primitives/IO primitives/Int)
  (bind (accept listener)
    (fn [conn]
      (bind (read conn)
        (fn [req]
          (bind (send conn (handle req))
            (fn [_] (serve-loop listener))))))))

(defn main []
  (bind (listen (port) (pool-size))
    (fn [listener] (serve-loop listener))))
```

`handle` (the pure router) is **unchanged**. The fan-out factors `handle-conn` and
detaches it (`(do (handle-conn conn) (serve-loop listener))`) — and because the
`Connection` is a self-contained handle (it carries its `fd`, from which the platform
projects the token), `handle-conn` is a pure function of `conn`; the fan-out wraps it
without re-plumbing. The ctx-vtable cut **strengthens** this property: at v8 the
self-containment depended on the wrapper having threaded the `(token, capacity, fd)`
triple correctly; now the connection carries only its genuine `fd`, and the token is a
projection the poll-fn recomputes each poll (never threaded, never stored), so a
mis-threaded leading pair is no longer even expressible.

#### 3.5.6 How scheduling reaches the trampoline — the leaf-driven acquire/register lights up

Under the ctx-vtable model **the leaf drives scheduling itself** (no cranelisp operand,
no header slot, no `desc_out`); the trampoline only supplies the `*HostCtx` + `*Waker`
and owns *release*:

- **Produce (`accept-conn`):** there is **no program handle during establishment**, so
  the poll-fn drives `register_readable(listener_fd, waker)` on the *listener* fd it is
  establishing on (an `accept` does not contend on a connection token — it is structurally
  serial in the serve loop). At `Ready` it mints `Connection{fd: new_fd}` carrying the
  fresh `r` and `set_result`s it — no stamp, no `desc_out`.
- **Consume (`read-conn` / `send-conn`):** the poll-fn **reads `fd` off the `Connection`
  arg's genuine field**, projects the per-direction token (`read_tok`/`write_tok`), and
  calls `acquire(token, 1, waker)` **itself** at the start of each poll — taking the
  per-token permit. The host **holds** that permit across the establish→park→ready arc
  and **releases** it on `Ready`/cancel (trampoline-owned, keyed by the effect's identity;
  cancel never re-enters the poll-fn). So every consume leaf is admission-wrapped — **the
  leaf-driven acquire is lit up by the web consume leaves**.

What the permit gates, per granularity (honest, arch §16-faithful):

- **Per connection (capacity 1, per direction):** `read`/`send` on one connection draw
  **distinct per-direction tokens** (`read_tok(fd)` ≠ `write_tok(fd)`), so they do NOT
  serialize against each other (full-duplex, §3.6.1); within a direction, capacity 1
  serializes — dataflow already orders read→send, so the permit is
  correct-but-uncontended.
- **Across connections (distinct fds):** independent — different connections carry
  **distinct `fd`s**, so the projected tokens are distinct and the per-token permit does
  not serialize them (arch §8.2). Each connection's token is recomputed from its own `fd`
  each poll.
- **The in-flight-CONNECTION-COUNT ceiling N:** enforced under the fan-out by the
  **slice-4 global admission budget** (reading `N` off the `Listener`'s `pool` field),
  composing `min(capacity, degree)` over the same permit machinery (arch §8.1 / §16).
  **Not** a per-connection capacity-N.

**Rejected alternative — a SHARED connection-pool token of capacity N** (so the per-token
permit alone bounds the count, without the slice-4 global budget): **rejected** for the
same three reasons as v8 — (a) contradicts arch §16 (web uses fresh per-connection
tokens; capacity-N pools are the DB/SQL case, count is bounded by *backpressure*); (b)
serializes all connections through one token's §8.2 ordering; (c) the capacity-N
per-token pool mechanism is proven elsewhere (the `poll-pool` test leaf, §3.4.6), web
need not re-prove it.

> **Coordination note for `/sprint`.** The "N concurrent connections; the (N+1)th parks"
> server-demo witness is a fan-out property (the slice-4 global admission budget the
> sibling `/design` intrinsics agent owns), NOT a per-token-permit property. The
> ctx-vtable cut does not change this split: the interface uses only the ratified `ctx`
> vtable (`acquire`/`register_*`/`retire`) + ordinary opaque `.cl` ADTs — and the
> `cranelisp-types`/`cranelisp-platform` ABI changes (`ResourceRole`,
> `ConcurrencyDescriptor.role`, `Acquire`, `HostCtx.{acquire,retire}`; `PollFn` UNCHANGED)
> are the /arch-ruled v9 cutover surface (§6.8.0b), already manifested — no NEW cross-crate
> convention is introduced by this design pass.

#### 3.5.7 /dev + /port web implements, in this order (v9 ctx-vtable)

1. **`/port` — the handle ADTs** (`exemplar/web.cl`, §3.5.1): `web/Listener [fd pool]`
   (ordinary) + `web/Connection [fd]` (opaque, genuine `fd` field — NOT `[]`). **No
   platform import in `web.cl`** (§3.5.3 / §3.6.3). Keep `Request`/`Response`.
2. **`/port` — the wrapper module** (`exemplar/serve.cl`, §3.5.3): the trivial
   `listen`/`accept`/`read`/`send` pass-throughs; imports `[web [Listener Connection]]`
   + `[platform.web […]]`. Export them.
3. **`/platform` — the v9 platform poll leaves** (`exemplar/platforms/web/src/lib.rs`,
   §3.5.2): one `declare_platform!` with `bind-listener` (blocking, role `None`),
   `accept-conn` (poll, **Produce** — drives acquire/register on the listener fd, mints
   `Connection{fd}` at `Ready`), `read-conn` / `send-conn` (poll, **Consume** — read `fd`
   off the `Connection` field, `acquire(read_tok/write_tok, 1, waker)` themselves). Keep
   the pure `parse_http_request` / `format_http_response` halves; fd-keyed internal maps
   replace `Mutex<ServerState>`. Each rides `poll_support` (§3.5.4) — `PollEnv` +
   `Reactor::{wake_on_*,acquire,retire}` + `PollState::drive`. No `desc_out`/`desc_of`.
4. **`/platform` (or `/int`) — regenerate `web.platform-schema`** for the new ADT shapes
   (opaque `Connection`) + slimmed signatures (`/platform-schema web`).
5. **`/port` — reshape the serve loop** (`exemplar/main.cl`, §3.5.5): import `serve`;
   thread `Connection` through `read` → `handle` → `send`; keep `handle` pure +
   tail-recursion intact.
6. **`/qa` — the web e2e rows** + the v9 user-visible-signature guards (the slim
   `read-conn : (Fn [Connection] (IO Request))` sig; the opaque-`Connection` layout).
   `--run exemplar/main.cl` on the default binary serves (single trampoline, always
   present).
7. **Fan-out co-land** (sibling `/design` intrinsics + `/dev`): factor `handle-conn`,
   launch-and-continue + supervisor — the connection threading from steps 2/5 drops in
   unchanged; the slice-4 global budget reads `N` off the `Listener`.

---

### 3.6 The ctx-vtable leaf-authoring contract — the uniform poll-fn skeleton + the four roles (the general v9 rule)

§3.5 instantiates v9 for web; this section is the **platform-agnostic leaf-authoring
contract** every poll leaf follows under the ctx-vtable model. It is the §2.4 "what
`poll_support` does NOT own" boundary: `poll_support` wraps the `ctx` vtable calls
(`Reactor::{wake_on_*,acquire,retire}`, §2.2) and the env/phase scaffolds; the leaf
author declares the **role** (a manifest fact) and decides the **token/capacity values**
+ **token projection** from the handle (the trust assertion).

**The uniform poll-fn skeleton** (`effect-concurrency.md` §4.1.1; every poll-shape leaf
has this shape):

```
poll(state, ctx, waker):
    token = project_token(state.handle)            # platform computes from its handle
    if token != 0:
        if ctx.acquire(token, capacity, waker) == Parked:
            return Pending                          # backpressure: no op without a permit
    r = state.syscall(NONBLOCK)                      # the platform's `what`
    if would_block(r):
        ctx.register_<interest>(state.fd, waker)     # the host's `when`
        return Pending
    set_result(state, value_from(r))
    return Ready                                      # host releases the permit
```

- `acquire` returning **`Parked`** returns `Pending` **before** the syscall — an op is
  never started without a permit (backpressure / pool bound, arch §8).
- `acquire` is **idempotent per in-flight effect** (the host keys held permits by the
  waker's data identity), so a re-poll re-`acquire`s without consuming a second permit —
  the skeleton needs **no "have I already acquired?" flag** on `state`.
- A **commutative** leaf (`token == 0`) omits `acquire` entirely — the token never
  appears, no permit is taken.
- A **one-shot** leaf (`sleep`) is the degenerate case: no handle, no token, no acquire —
  just `register_timer(deadline, waker) → Pending → Ready`.
- **Release is trampoline-owned** — the host releases the held permit on the effect's
  `Ready` **or** cancel; cancel never re-enters the poll-fn (so a leaf never frees a
  permit it cannot soundly free on a cancel it never sees).

#### 3.6.1 The four roles and what each leaf author writes

The leaf's **role** is a **per-effect static fact** declared on the manifest
`ConcurrencyDescriptor.role` (`ResourceRole { None, Produce, Consume, Retire }`) — NOT a
per-value field (`platform-interface.md` §6.8.0b; "Produce" is a fact about the *leaf*,
not the connection). The trampoline **does NOT branch on role at runtime** — role grounds
inference E2 + documents the leaf; the poll-fn does *all* scheduling via the `ctx` vtable.
`PollFn` is **UNCHANGED** (`poll(state, *HostCtx, *Waker) -> Poll`) — no `desc_out`; the
value flows through `set_result` as today.

| role | when to declare it | what the poll-fn does (via `ctx`) | what the trampoline does |
|---|---|---|---|
| **`None`** | the effect neither produces nor consumes a scheduling resource (a tokenless/`Commutative` leaf — a bare timer; a fire-and-forget log; `bind-listener`; `sleep` one-shot) | **no `acquire`** (token 0 / no token); `register_timer` only if it waits | nothing scheduling-specific |
| **`Produce`** | the effect **mints** a resource handle whose later use must be admission-controlled (`accept`/`connect`/`open`) | drives `acquire`/`register_*` on the **establishment** resource (the listener fd / a fresh socket fd it minted — there is no program handle yet); at `Ready` **mints the handle ADT carrying the new `r`** in a genuine field and `set_result`s it | releases the establishment permit on `Ready`/cancel; hands the minted value onward (no stamp) |
| **`Consume`** | the effect **operates on** a previously-produced handle and must serialize within that resource (`read`/`write`/`send`; a DB `query` over a pooled connection) | reads `r` off the handle arg's **genuine field**, projects the (per-direction) token, calls `acquire(token, capacity, waker)` itself, then the I/O syscall + `register_*` on `WouldBlock` | releases the permit on `Ready`/cancel (keyed by effect identity) |
| **`Retire`** | the effect **ends** a resource's scheduling identity (`close`) | `acquire(token, …)` (idempotent), `close(r)` syscall, then `ctx.retire(token)` for **each** of the resource's tokens (full-duplex: `retire(read_tok)` + `retire(write_tok)`) | releases the permit on `Ready`; the `retire` drops the token's pool + wakes any token-parked waiters |

**The asymmetry is the load-bearing subtlety.** Every leaf does its *own* scheduling
through the vtable — there is no writer/reader split over a shared descriptor (that was
the dead model). A `Produce` leaf drives admission on the resource it is *establishing*
and mints the handle at `Ready`; a `Consume` leaf projects the token from the handle it
*holds*; a `Retire` leaf ends the identity; a `None` leaf touches neither. A leaf is
never both Produce and Consume — if an effect both mints a new handle and rides a prior
one (rare), it declares `Produce` and the prior handle's admission is the *caller's*
concern (for web, `accept` is structurally serial in the serve loop, so it needs no
listener-side contention — §3.5.2).

**Singleton resources (no produced handle) — the manifest-static token.** A resource
that is **not minted per value** (stdin, a global rate-limiter) has no handle to project
a token from. It declares a **manifest-static** serial token on the effect — a fixed
non-zero `token` + `capacity` + `role: Consume` — and the poll-fn calls
`acquire(STATIC_TOKEN, capacity, waker)` on that **constant** (read from the effect's
`ConcurrencyDescriptor`, not off any value). `read-line`'s `{token: STDIN_TOKEN != 0,
capacity: 1, role: Consume}` (§3.1) is the canonical case; it structurally enforces
single-in-flight with no value, no header, no special case. This is the v9 home for "a
serial resource with no handle object."

#### 3.6.2 The `poll_support` scaffold (no descriptor helper — the vtable is the only new idiom)

The ctx-vtable model adds **nothing to the env layout** (no header slot, no `desc_out`),
so there is **no `PollEnv` descriptor helper** — the descriptor cut's `desc_of`/`set_desc`
are **deleted**. The new idiom is purely the *vtable call*, codified once on the
`Reactor` scaffold (§2.2):

```rust
#[cfg(feature = "concurrency")]
impl Reactor<'_> {
    /// Token-permit acquire (the leaf computes `token` + `capacity` itself). Idempotent
    /// per in-flight effect; `Parked` ⇒ the leaf returns `Pending`. Release is
    /// trampoline-owned — there is NO `release` here.
    pub fn acquire(&self, token: u64, capacity: u32) -> Acquire { /* (*host).acquire(...) */ }
    /// End a token's scheduling identity (a Retire/`close` leaf), after `close(r)`.
    pub fn retire(&self, token: u64) { /* (*host).retire(...) */ }
    // wake_on_readable / wake_on_writable / wake_on_timer — §2.2, unchanged.
}
```

A leaf reads its handle's `r`/`fd` as an **ordinary opaque ADT field** off `PollEnv::arg(0)`
via the existing `CLAdt` / platform-schema path (the same accessor it uses for any ADT
field) — **not** through a descriptor-offset helper. It then projects the token
(`token == fd` for web; per-direction for full-duplex) and calls `Reactor::acquire`. The
**only** new offset-discipline question the descriptor cut raised (where does the
descriptor slot live?) **disappears** — there is no slot. The env-layout single-siting of
§2.1 (`PollEnv`) and the vtable single-siting of §2.2 (`Reactor`) are the two homes; no
third helper is added.

#### 3.6.3 General platform-authoring rule — a sig-referenced type-module cannot import its own platform

> **v9-independent (so stated regardless — `/arch` Phase-2 caveat on FIXME 0469).** This
> rule predates and outlives the descriptor cut; it governs *any* platform whose sigs
> reference `.cl` ADTs.

**Rule.** When a platform's effect signatures reference `.cl` ADTs declared in a module
`M` (so `M` is a *sig-referenced type-module*), `M` is loaded and typechecked by the
platform-load **pre-resolve** (`platform-interface.md` §7.2,
`src/platform.rs::referenced_sig_modules`) **before the platform is registered**.
Therefore **`M` MUST NOT import that platform** — neither via `(import [platform.<name>
…])` nor via an FQ `platform.<name>/…` call (FQ auto-load triggers the same mid-load
cycle). Both produce a hard `ModuleError` (`module 'platform.<name>' not found (imported
by '<M>')`).

**Consequence for platform authors.** Any **wrapper / convenience function that calls
the platform's own effects** must live in a **different module** than the ADTs the
platform's sigs reference. The pattern is the §3.5.3 two-module split:

1. the **type module** (`M`, e.g. `web.cl`) — declares the ADTs the sigs reference;
   **platform-import-free**; loaded by the pre-resolve.
2. the **wrapper module** (e.g. `serve.cl`) — imports both `M`'s ADTs and the platform
   effects; loaded only when the program imports it, **after** the platform is
   registered.

This is a structural constraint, not a web quirk — the next platform that wants
convenience wrappers over its own ADTs follows the same two-module pattern. (The
ctx-vtable cut *reduces* the wrappers to near-trivial pass-throughs — there is no leading
pair and no descriptor to thread — but the placement rule is unchanged: the wrapper still
imports the platform, so it still cannot be `M`.)

---

## 4. The converged macro skeleton — honoring gate (c) exactly

> **SUPERSEDED by the v8 single-ABI cutover (top banner).** With ONE
> `declare_platform!` macro there is no two-macro mirror to converge — the per-fn
> `descriptor:` (poll) / `scheduling:` (blocking) key choice in the single macro
> replaces the convergence (SPRINT.md §"Single-ABI cutover": "A4 step 5 is thus
> SUPERSEDED, not merely deferred"). §4 is retained as the historical Chunk-A design
> record; the web platform (§3.5.2) uses the single v8 macro directly.

### 4.1 The problem the convergence solves

`declare_concurrent_platform!` (`declare.rs:461`, ~105 lines) is today a **full
mirror** of `__declare_platform_body!`: it re-emits the GOT static, the GOT
population loop, the `host.init`, and the param-name parallel-array plumbing —
*identical token-for-token* to the v6 body — and then diverges only at the manifest
entry type (`ConcurrentPlatformFn` vs `PlatformFn`), the manifest type
(`ConcurrentPlatformManifest` vs `PlatformManifest`), the export symbol
(`cranelisp_concurrent_manifest` vs `cranelisp_platform_manifest_<name>`), and the
per-fn metadata field (`descriptor:` vs `scheduling:`). `/review` flagged the mirror
in S94. The convergence retires the duplicated spine.

### 4.2 The two-arm + shared-helper shape (gate (c) ruling, verbatim)

Per the Phase-2 gate-(c) ruling, the converged skeleton is a
**field-shape-parameterized shared inner helper** delegated to from **two separate
`macro_rules!` arms**:

- **Arm 1 — `declare_platform!` (v6, ungated).** Unchanged author surface;
  emits the `PlatformFn` shape. Stays exactly as today (two arms: with/without
  `schema:`), now delegating its shape-neutral spine to the shared helper.
- **Arm 2 — `declare_concurrent_platform!` (v7, gated).** Author surface
  unchanged (the `descriptor:` per-fn key, the `cranelisp_concurrent_manifest`
  export); emits the `ConcurrentPlatformFn` shape. Only this arm is reachable from
  a `concurrency`-feature-enabled platform crate.

Both delegate to a **shared `@emit-*` helper** that takes **only shape-neutral
tokens** and emits the spine that is byte-identical between v6 and v7:

```
__declare_platform_shared! {
    @spine
    name: $platform_name:literal,
    host: $host:ident,
    fns: [ $( $fn_ident:ident { params: [ $($param:ident),* ] } ),* ]
}
```

What the `@spine` helper emits (the retired mirror — all **type-name-neutral**):

1. **The exported GOT static** `__cranelisp_got_platform_<name>` —
   `[MacroAtomicPtr<u8>; GOT_TABLE_SIZE]` (identical symbol + shape in both ABIs;
   the host dlsyms it by name regardless of v6/v7).
2. **The GOT population loop** — `slot i ← $fn_ident as *const u8 as *mut u8`
   (the cast is `*const u8`, type-neutral; works for both a blocking `extern "C"`
   fn and a `PollFn` — both coerce to `*const u8`).
3. **The `$host.init(callbacks)` call.**
4. **The per-fn param-name plumbing** — `param_names_vec` / `name_ptrs` /
   `name_lens` / `param_count` / the `Box::leak`'d parallel arrays + the
   null-when-zero branch. Pure shape-neutral metadata.

What stays **in each arm** (the field-shape-divergent part — **v7 type names
appear ONLY in the gated v7 arm**):

| Per-arm (NOT in the shared helper) | v6 arm | v7 arm (gated) |
|---|---|---|
| manifest entry type + fields | `PlatformFn { ptr, …, scheduling_class }` | `ConcurrentPlatformFn { poll, drop_state, …, concurrency }` |
| manifest type | `PlatformManifest` | `ConcurrentPlatformManifest` |
| export symbol | `cranelisp_platform_manifest_<name>` | `cranelisp_concurrent_manifest` |
| per-fn metadata key | `scheduling: SchedulingClass` | `descriptor: ConcurrencyDescriptor` |
| `schema:` embed arm + `__cranelisp_layout_hash_<name>` | yes | n/a (poll leaves marshal via the same `.cl`/schema path if needed, but the schema arm is v6-shaped — keep it on the v6 arm; a v7 platform that marshals ADTs composes v6 `declare_platform!` for those + `declare_concurrent_platform!` for poll leaves, OR the v7 arm grows its own `schema:` sub-arm in a later slice) |

The shared helper **never names** `ConcurrentPlatformFn`, `ConcurrencyDescriptor`,
`drop_state`, `PollFn`, or `ConcurrentPlatformManifest`. Each `@spine` invocation
expands to the same tokens irrespective of caller, and the caller arm then
constructs its own typed manifest array + manifest struct + export inline (the
~20 divergent lines that genuinely differ, vs the ~85 mirrored lines now shared).

### 4.3 Why the two-arm shape is the safe one (the hazard gate (c) names)

The hazard gate (c) calls out: **a single arm with a `#[cfg]`-stripped v7-type
reference is unsound** — the v6 expansion may still need the type in scope, but
`#[cfg]` would strip it. The two-arm + shared-helper shape avoids this
structurally: **separate non-matching `macro_rules!` arms do not expand.** A v6
platform crate (no `concurrency` feature) invokes only `declare_platform!`; that
arm's expansion references only v6 types (`PlatformFn` etc.) and delegates the
spine to `@spine` (type-neutral). The v7 arm (`declare_concurrent_platform!`)
references `ConcurrentPlatformFn` etc. — but **it is never invoked by a v6 crate**,
and `macro_rules!` bodies are type-checked only on expansion, so those names are
never tokenized into a default build. There is no `#[cfg]`-inside-one-arm anywhere;
the gate is the *separation*, not a feature-strip.

### 4.4 The `_neg` frozen-edge guard is the review gate — and how the shape keeps it green

The enforcement is the **existing `_neg` guard**
(`tests/facade_pif_rows.rs::concurrency_descriptor_absent_from_default_public_api_neg`):
it asserts the v7 dormant types (`ConcurrencyDescriptor`, `ConcurrentPlatformFn`,
`ConcurrentPlatformManifest`, `HostCtx`, `Waker`, `WakerVTable`, `PollFn`,
`drop_state`) are **ABSENT from the default (feature-off) `public-api.txt` edge** —
i.e. the v6 expansion path (the default build) is free of v7 names. The converged
shape keeps it green by construction:

- the shared `@spine` helper is type-neutral, so it contributes no v7 name to *any*
  build;
- the v7 names live only in the `declare_concurrent_platform!` arm, which is gated
  (`$crate::ConcurrentPlatformFn` resolves only under `concurrency`) and invoked
  only by a `concurrency`-enabled crate;
- `poll_support` (§2) is `#[cfg(feature = "concurrency")]` throughout.

So the default `public-api.txt` is byte-identical-when-off, and the `_neg` guard
flips RED only if the convergence accidentally leaks a v7 name onto the default
edge (e.g. a v7 type referenced from the shared helper, or `poll_support` un-gated)
— which is precisely the regression the gate exists to catch. **`/review`
(platform) walks this guard on the change-set; it MUST stay green.** No platform
`public-api.txt` touch is expected (gate (c) public-API ruling) — all helpers name
already-gated types, and the macro spine names none.

---

## 5. Quality attributes (this chunk)

| Attribute | Assessment |
|---|---|
| **Simplicity** | Net subtraction (Principle 6): retires the ~105-line `declare_concurrent_platform!` mirror; `poll_support` is extracted from real evidence, not speculated. The three scaffolds each codify one repeated idiom (env offsets, vtable calls, phase sentinel) — no scaffold without a witnessed pain point. |
| **Maintainability** | The R1 env-layout convention lives in **one place** (`PollEnv`, §2.1) instead of replicated offset math per leaf — bounded blast radius if the backend bake moves a slot (one edit). The macro spine is single-sited (Principle 7) — a GOT/manifest mechanism change touches the shared helper, not two mirrors. |
| **Observability** | Out-of-pass for the platform crate (the strand event stream is intrinsics/reactor-side, reactor.md §3). `poll_support` emits nothing — the acquire/park/release events are emitted by the host when it services the vtable calls + releases the permit on `Ready`/cancel, not by the leaf. Noted as non-impact. |
| **Concurrency-safety** | The platform side stays single-threaded-per-leaf and **release-agnostic**: a poll-fn calls `acquire`/`register_*`/`retire` through the `ctx` vtable and returns `Poll`, but never blocks (`acquire` returns `Parked` immediately) and never dispatches another effect (gate (a) req. 2, §3.2). **Release is trampoline-owned** — the platform never releases a permit (so it cannot mis-release on a cancel it never sees). The lock-free reactor-thread permit map (reactor.md §2.8) is the host's; the platform only *calls into* it via the vtable. `PollState` lives in env scratch torn down by the host-built `drop_glue_ptr` (RC + drop for free, io-trampoline §12.2). |
| **Testability** | `PollEnv`/`Reactor`/`PollState` are unit-testable in-crate over a fixture env + a stub `HostCtx`/`Waker` (the `async_read_pollfn`/`timer_write_pollfn` precedent, reactor.md §2.7 — `concurrency`-gated unit tests); the stub `HostCtx` now also records `acquire`/`retire` calls. The macro skeleton is pinned by `tests/macro_expansion.rs` (GOT/manifest shape) + the `_neg` frozen-edge guard. e2e (distinct-token overlap, capacity-N poll parking, full-duplex non-serialization) is `/qa`'s plan over the rewritten web/stdio. |

---

## 6. Cross-references

- **ABI v9 ctx-vtable (the authoritative /arch rulings this doc conforms to — read-only):**
  `design/arch/platform-interface.md` §6.8.0b (the `ctx` vtable ABI — `HostCtx.{acquire,
  retire}` + the `Acquire` enum + `ConcurrencyDescriptor.role`; `PollFn` UNCHANGED, no
  `desc_out`); `design/arch/effect-concurrency.md` §4.1.1 (the canonical model — the
  uniform poll-fn skeleton, the four leaf roles, the full open/read/write/close trace,
  the singleton manifest-static token; §8.1/§8.2 permit + ordering); `design/arch/
  interfaces.md` §"Resource scheduling" (the `ResourceRole`/`Acquire`/`HostCtx` shapes —
  NO `ResourceDesc`, NO header slot); `design/arch/bounded-contexts.md` §5 (platform ABI
  v9 surface) / §3 (backend: delete the bake) / §6 (int: ctx-vtable host impl + tramp-owned
  release). The v9 sections here (§3.5 / §3.6 / §3.1) are the platform/leaf-authoring half
  of the cascade these rulings own.
- `design/platform/platform.md` — master (this is subordinate; cited from §"Subordinate docs")
- `design/intrinsics/reactor.md` §2.6/§2.8/§2.9 — acquire-around-poll, the token-capacity pool, RAII `Permit`, the testability seams (sibling `/design` int)
- `design/backend/io-trampoline.md` §12 — `IO_TAG_EFFECT_POLL` node + state-closure env layout (the `PollEnv` consumer's contract; sibling `/design` backend)
- `design/backend/io-trampoline.md` §14 — the poll-node live `(token, capacity)` bake + the leading-pair operand convention the `inject_poll_leading_pair` pass produces (sibling `/design` backend; §3.4 here is the platform-side value-source half)
- `crates/cranelisp-backend/src/lib.rs::inject_poll_leading_pair` — the backend `MonoExpr` injection POINT A4 generalizes (§3.4.1); `crates/cranelisp-backend/src/compiler/resolution.rs::resolve_poll_effect_target` — extended to surface `scheduling_class` (the no-types-touch discriminator, §3.4.2)
- `platforms/pool-demo/src/lib.rs` — the S95 BLOCKING capacity leaf whose `ResourceSerial` + explicit-`(token, capacity)`-args convention the poll carrier mirrors (§3.4.2/§3.4.6)
- `design/arch/effect-concurrency.md` §5/§8/§12 — descriptor, token-capacity carrier, A2 host-reactor model (**`/arch`-owned, read-only**); §8.2 within-token ordering + §10 supervisor + §16 the web/DB reference workload (the fresh-per-connection-token + backpressure model §3.5 is faithful to)
- `design/platform/poll-support.md §3.5` — the concrete web connection-handle cranelisp interface (resolves FIXME 0465); the Chunk-B keystone the slice-5 server demo exercises
- `exemplar/web.cl`, `exemplar/main.cl` — the `/port`-owned `.cl` surface §3.5.1/§3.5.3/§3.5.5 specifies (handle ADTs + wrappers + serve loop)
- `design/arch/platform-interface.md` §6.8 — the ABI-v4 cascade / numeric `ABI_VERSION` 6→7 (**`/arch`-owned**)
- `crates/cranelisp-platform/src/concurrency.rs` — the (now core/ungated) async-leaf C-ABI contract types (`HostCtx`/`Waker`/`WakerVTable`/`PollFn`; the dual-channel `ConcurrentPlatformFn`/`ConcurrentPlatformManifest` were **deleted** in the single-ABI cutover)
- `crates/cranelisp-platform/src/declare.rs` — `declare_platform!` / `__declare_platform_body!` (the single unified macro; `declare_concurrent_platform!` was **deleted** in the single-ABI cutover, its poll-shape arm folded into `declare_platform!`)
- `tests/facade_pif_rows.rs::concurrency_descriptor_absent_from_default_public_api_neg` — the `_neg` frozen-edge guard (gate (c) enforcement)
- `exemplar/platforms/web/src/lib.rs`, `platforms/stdio/src/lib.rs` — the rewrite targets

---

## /dev A4 implements, in this order:

> **SUPERSEDED by the ctx-vtable cutover (top banner; SPRINT.md Wave 2).** Steps 0/3
> below are the v8 `inject_poll_leading_pair` work; under the ctx-vtable model the backend's
> only delta is **DELETING** `inject_poll_leading_pair` + the positional peel (no
> `scheduling_class`-keyed branch, no leading pair to bake), and the platform leaves move to
> the uniform poll-fn skeleton (§3.6) — the live web impl order is **§3.5.7**. This list is
> retained for the evidence-first / extract-after sequencing rationale (Principle 8), which
> still governs how `poll_support` is extracted; read steps 0/3's carrier mechanics for
> provenance only.

Hand-rewrite first, extract after (Principle 8 — the suite is the target the
rewrite converges to, not a speculated pre-abstraction). The backend
discriminator change (step 0) is tiny and unblocks the live carrier; everything
after it is the evidence-first platform work.

0. **Backend: generalize `inject_poll_leading_pair` to be `scheduling_class`-keyed
   (§3.4.2).** Extend `resolve_poll_effect_target` to also return the
   already-destructured `scheduling_class` (reading an existing
   `DefKind::PlatformEffect` field — **no `cranelisp-types` touch, no ABI bump**).
   Branch the pass: `Commutative` ⇒ inject `(0, 1)` (the A2b behaviour, now gated);
   `ResourceSerial`/`Sequential` ⇒ do NOT inject (the source supplies the live
   leading pair; the A2 peel bakes it). This SUBSUMES A2b — no second pass (FIXME
   0463 §3.4.1). Pin at the seam with the existing `poll_codegen_tests` style:
   a `ResourceSerial` poll `Apply` is left untouched (no `(0,1)` prepend); a
   `Commutative` one still gets `(0,1)`.

1. **Hand-rewrite `stdio read_line`** as the first poll-shape leaf (`Commutative`
   ⇒ `(0,1)` injected) against the **raw** state-closure env layout (io-trampoline
   §12.2) + the **raw** `HostCtx`/`Waker` vtable — keeping `print` as untouched v6
   blocking (the byte-identical-off witness). Smallest evidence input; surfaces the
   env-accessor + fd-readiness + first-poll/re-poll idiom pain before web's
   complexity.

2. **Author the `poll-pool` G1 test leaf** (§3.4.6) — `poll-read`/`poll-write`/
   `poll-log`, each `ResourceSerial`, explicit `(token, capacity, …)` cranelisp
   args, reactor-routed armed-timer. Add to
   `tests/scripts/build-link-prereqs.sh`. This flips the 4 RED
   `concurrency_poll_capacity.rs` rows green (with A2's live bake + A3's
   acquire-around-poll already landed) — the smallest leaf that proves the live
   carrier end-to-end, before web's connection lifecycle. (Authored WITH this
   wave per the QA plan.)

3. **Hand-rewrite `web accept`/`read`/`send`** over a fresh connection token
   (§3.2 + §3.4.5). **MOVED to Chunk B** (user decision 2026-06-29) — it needed a
   concrete connection-handle cranelisp interface (FIXME 0465) that co-designs with
   the slice-5 server demo. **That interface is now pinned in §3.5** (the handle
   ADTs, the v8 poll-leaf signatures, the destructuring wrappers, the serve-loop
   reshape); the ordered Chunk-B impl list is **§3.5.7**. (Chunk A landed steps 0/2/4;
   the stdio mixed-manifest proof carried the "real poll platform" evidence in A's
   absence of web.)

4. **Extract `poll_support` from the two-platform evidence** (§2) — `PollEnv`
   (typed env accessor), `Reactor` (fd/timer scaffold), `PollState`/`drive` (phase
   scaffold). Refactor stdio `read_line` + web leaves onto it. Net subtraction.

5. **Macro convergence** (§4) — the two-arm + shared `@spine` helper, retiring the
   ~85-line mirror. Parallel/independent; land whenever, gated by a green `_neg`
   frozen-edge guard.

Each step's `/review` walks the `_neg` guard; none touches `cranelisp-types`,
`public-api.txt`, or `ABI_VERSION` (§3.4.4). If any step appears to require a new
`DefKind`/descriptor field the backend must read for capacity, STOP and file a
FIXME `target: /arch` — A4 as designed does not need it.
