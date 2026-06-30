# `poll_support` + the web/stdio v7 adoption — Solution Design

**Sprint 96, Chunk A (the substrate-adoption keystone). Pre-implementation —
evidence-first.** Subordinate to `design/platform/platform.md` (the master);
elaborates the new `concurrency`-gated `poll_support` module and how the two
in-tree model platforms (`web`, `stdio`) adopt the ABI-v7 poll-shape async-leaf
model. The cross-crate seams it rides on are owned elsewhere and only *referenced*
here:

- the **acquire-around-poll lifecycle** + the RAII `Permit` drop-guard + the
  token-capacity `Semaphore` pool — `design/int/reactor.md` §2.6 / §2.8 (sibling
  `/design` int);
- the **poll-node bake** (`IO_TAG_EFFECT_POLL` + the host-built state-closure env
  layout) — `design/backend/io-trampoline.md` §12 (sibling `/design` backend);
- the v7 C-ABI contract types (`HostCtx`, `Waker`, `WakerVTable`, `PollFn`,
  `ConcurrentPlatformFn`, `ConcurrencyDescriptor`) — `crates/cranelisp-platform/
  src/concurrency.rs`, `design/arch/effect-concurrency.md` §12 (**`/arch`-owned —
  read-only**), `design/arch/platform-interface.md` §6.8.

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

---

## 1. Why a `poll_support` module at all

The ABI-v7 contract (`concurrency.rs`) gives a platform author the raw C-ABI: a
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

`poll_support` codifies these three into a small, total, `concurrency`-gated
helper layer so a leaf author writes intent (`"try the syscall; if it'd block,
tell the host to wake me"`), not offset math. The **descriptor** (the trust
assertion — token/capacity/blocking), the **syscall** (the platform's domain),
and the **result interpretation** (what the i64 means) stay hand-written — those
are the irreducible per-platform parts.

The module is `#[cfg(feature = "concurrency")]` throughout, so it enters neither
the default build nor the frozen `public-api.txt` edge — the `_neg` frozen-edge
guard (`tests/facade_pif_rows.rs::concurrency_descriptor_absent_from_default_public_api_neg`)
keeps it off the default surface byte-identical-when-off, exactly as the v7
contract types already are.

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
}
```

It exists to (a) hide the `(*host).vtable_fn(host_data, …)` indirection and the
`host`-handle threading, and (b) give the leaf a single, named verb per readiness
kind. It owns **no reactor state** — the host owns the *when* (§12 A2 model);
this is purely the platform-side projection of "register interest." Cancellation
needs no leaf cooperation here: the host simply ceases to poll and drops the node
(the RAII `Permit` releases — reactor.md §2.8); `Reactor` registers, it never
blocks.

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
  `declare_concurrent_platform!` invocation (§4). `poll_support` never synthesizes
  one.
- **The syscall + result meaning.** `TcpListener::accept`, `read`, the i64 the
  result slot carries — all hand-written. The scaffold locates and registers; it
  does not interpret.
- **The reactor / the pool / the Permit.** All intrinsics-side (reactor.md). The
  platform never sees a `Semaphore`, a permit, or the acquire-around-poll arc — it
  only `register_*`s and returns `Poll`. This is the thin-platform thesis (§12):
  platforms own the *what*, the host owns the *when*.
- **The codegen operand injection.** Placing the live `(token, capacity)` as the
  two leading operands of a poll-shape call is a compile-time `MonoExpr` concern,
  owned by the **backend** pass `inject_poll_leading_pair` (§3.4.1). `poll_support`
  (a runtime-Rust helper inside the poll-fn) cannot place codegen operands; its
  role is the *value SOURCE* — deriving token/capacity and shaping the source-level
  call so the backend peel finds them (FIXME 0463 reconciliation, §3.4).

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
  It carries `token = 0` capacity-irrelevant **or** a serial stdin token of
  capacity 1 (stdin is a serial resource — the §8.2 within-token ordering case);
  the descriptor literal asserts it.

`stdio` is the ergonomics check: if porting *one trivial blocking read* to a poll
leaf is more than "register readiness; resume on wake; set result," `poll_support`
is missing a scaffold. It is the smallest evidence input and the first thing `/dev`
hand-rewrites (§"implement first").

### 3.2 `web` — the connection-token model (the gate-(a) non-re-entry property)

`web` is the reference workload. The v6 platform (master / `exemplar/platforms/web`)
is a single-stream blocking `listen`/`accept`/`send` (one accepted `TcpStream`
held in a process-global `Mutex` between `accept` and `send`). The v7 rewrite turns
the connection lifecycle into poll-shape leaves over a **per-connection token**:

| Effect | v6 (today) | v7 (target) |
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
case (§3.4.6), **not** web connections. On the poll carrier the `(token, capacity)`
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

- **acquire-around-poll + RAII `Permit`** — `design/int/reactor.md` §2.6/§2.8.
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

Declared via `declare_concurrent_platform!` with each effect's descriptor mapping to
`ResourceSerial` (`token 0, cardinality 1, blocking 0`) so the backend pass leaves the
source-supplied leading pair intact and the A2 peel bakes the live `(token, capacity)`.
token/capacity/ms are explicit cranelisp args (no handle re-pass — the timer leaf has
no fd; leaf args are operands `2..`). Add it to `tests/scripts/build-link-prereqs.sh`.
It is a **platform effect** (not stdlib), preserving the free-standing-test rule. (On
v8 this is one unified `declare_platform!` with each effect's `descriptor:` poll —
§4 banner.)

---

### 3.5 The web connection-handle cranelisp interface (resolves FIXME 0465)

§3.2 / §3.4.5 describe the web connection-token *model*; this section pins the
**concrete cranelisp surface** that did not exist — the connection-handle ADTs, the
platform poll-leaf signatures honoring the leading-pair convention, the destructuring
wrappers, and the serial serve-loop reshape. `/port` owns the `.cl` files
(`exemplar/web.cl`, `exemplar/main.cl`); `/platform` owns the poll-fns
(`exemplar/platforms/web/src/lib.rs`); this section is the **interface both implement
against** (Phase-5 D/D/R, Chunk B). It is the **SERIAL** serve loop (Chunk A's
permanent baseline). The Chunk-B launch-and-continue fan-out (sibling `/design`
intrinsics — `effect-concurrency.md` §10, `reactor.md` §5) is *referenced* (§3.5.5),
not designed here; the connection threading below is shaped so the fan-out drops in
without touching the leaves or wrappers.

#### 3.5.1 The handle ADTs (`exemplar/web.cl`, /port-owned)

Two new ordinary `.cl` ADTs join the unchanged `web/Request` / `web/Response` (§3.2 —
platforms still do not declare ADTs; the backend regenerates `web.platform-schema`):

```clojure
;; web/Listener — the bound TCP listener.
;;   fd   : listener socket fd (accept rides this as its serial admission token)
;;   pool : N, the in-flight-CONNECTION-COUNT ceiling — consumed by the Chunk-B
;;          launch-and-continue fan-out (slice-4 global admission budget, arch §16),
;;          NOT a per-connection capacity.
(deftype Listener [:primitives/Int fd :primitives/Int pool])

;; web/Connection — one accepted HTTP connection.
;;   token    : per-connection admission token (= fd; fresh per accept ⇒ distinct
;;              connections concurrent by construction, arch §8.2)
;;   capacity : 1 — serial WITHIN the connection (read→send are dataflow-ordered)
;;   fd       : connection socket fd (the syscall handle; re-passed as leaf_0)
(deftype Connection [:primitives/Int token :primitives/Int capacity :primitives/Int fd])
```

`token == fd` and `capacity == 1` in this slice; the three fields stay distinct so
(a) the leading-pair convention reads positionally and (b) a future `token ≠ fd`
split (a virtual/NAT'd fd) needs no ADT change. The live OS resources (`TcpListener`,
accepted `TcpStream`) stay in platform-internal maps keyed by fd — only the i64
fd/token/capacity cross the boundary (the standard fd-as-handle pattern; no
`TcpStream` value in cranelisp). This retires the process-global
`Mutex<ServerState>` of the v6 platform (the connection now threads through cranelisp,
not a hidden global).

#### 3.5.2 The platform poll-leaf signatures (`exemplar/platforms/web`, /platform-owned)

Four effects in ONE v8 `declare_platform!` manifest (mixed blocking + poll — the
shape stdio's `print`+`read_line` already proved in Chunk A):

| effect | descriptor | FQ signature | leading pair → leaf args |
|---|---|---|---|
| `bind-listener` | **blocking** (`scheduling: Sequential`) | `(Fn [Int Int] (IO web/Listener))` | none (blocking); args `(port, N)` |
| `accept-conn` | **poll** `ResourceSerial` | `(Fn [Int Int Int] (IO web/Connection))` | `[listener_fd, 1, listener_fd]` (leaf_0 = listener_fd) |
| `read-conn` | **poll** `ResourceSerial` | `(Fn [Int Int Int] (IO web/Request))` | `[conn_token, 1, conn_fd]` (leaf_0 = conn_fd) |
| `send-conn` | **poll** `ResourceSerial` | `(Fn [Int Int Int web/Response] (IO Int))` | `[conn_token, 1, conn_fd, resp]` (leaf_0 = conn_fd, leaf_1 = resp) |

- **`bind-listener`** is a plain blocking `CLIO::effect` (a bind is fast; no poll-fn).
  It binds the listener, chooses `N`, and `CLAdt::<Listener>::construct`s
  `(listener_fd, N)`. Blocking and poll effects coexist in one v8 manifest exactly as
  stdio's mixed manifest does (Chunk A).
- **`accept-conn` / `read-conn` / `send-conn`** are `ResourceSerial` poll leaves ⇒ the
  backend `inject_poll_leading_pair` pass leaves them **untouched** (§3.4.2); the
  SOURCE (the wrapper, §3.5.3) supplies the leading `(token, capacity)` pair. They ride
  `poll_support` verbatim (§3.5.4).

**Env layout under the leading-pair peel** (the /arch ruling, SPRINT.md Phase-3): the
result slot @ `state+0`; `leaf_0` (the re-passed fd) @ `state+8` = `PollEnv::arg(0)`;
`leaf_1` (the `Response` ADT base ptr, `send-conn` only) @ `state+16` =
`PollEnv::arg(1)`. token/capacity are baked to **node** offsets 32/40 and are NOT in
the env — the poll-fn never sees capacity (it is admission-only, read by
`await_poll_node`, reactor.md §2.9).

#### 3.5.3 The destructuring wrappers (`exemplar/web.cl`) — the cranelisp value SOURCE

The raw effects take an explicit leading pair; the friendly verbs `main.cl` calls
destructure the handle ADT and supply it. These wrappers **ARE** the `.cl` half of the
"value source" §3.4.1 names — they place `(token, capacity)` as the call's leading
operands and re-pass the fd as `leaf_0`, keeping the leading-pair plumbing OUT of
`main.cl`:

```clojure
(import [platform.web [bind-listener accept-conn read-conn send-conn]])

(defn listen [port n] (bind-listener port n))      ; blocking; returns Listener

(defn accept [listener]
  (match listener
    [(Listener fd pool)
       (accept-conn fd 1 fd)]))                     ; ride listener fd, serial; mints Connection

(defn read [conn]
  (match conn
    [(Connection token capacity fd)
       (read-conn token capacity fd)]))             ; ride conn token, cap 1; fd re-passed

(defn send [conn resp]
  (match conn
    [(Connection token capacity fd)
       (send-conn token capacity fd resp)]))        ; ride conn token; fd + resp as leaf args
```

`accept-conn`'s poll-fn mints the fresh `Connection`: on listener-readable it
`accept()`s a new fd and `CLAdt::<Connection>::construct`s `(new_fd, 1, new_fd)`.
`accept` / `read` / `send` / `listen` are exported from the `web` module; `main.cl`
imports them by name (so the serve loop reads in handle terms — arch §16 shape).

#### 3.5.4 poll_support consumption — web is the 3rd consumer, NO new scaffold

The three §2 scaffolds serve the web leaves unchanged (after `async-demo` + `stdio`):

- **`PollEnv`** (§2.1) — reads `arg(0)` = fd, `arg(1)` = `Response` ptr; writes the
  result (the constructed ADT base ptr / the `Int`) via `set_result` / `set_result_cl`.
- **`Reactor`** (§2.2) — `wake_on_readable(listener_fd)` (accept),
  `wake_on_readable(conn_fd)` (read), `wake_on_writable(conn_fd)` (send).
- **`PollState::drive`** (§2.3) — first poll registers readiness + parks; resume
  re-attempts the syscall; `Ready(result)` on completion.

Two web-specific parts stay **hand-written** (the §2.4 "what `poll_support` does NOT
own"): (a) the **ADT construct/read on the ready phase** — `accept-conn` constructs a
`Connection`, `read-conn` a `Request`, `send-conn` reads a `Response` — via the
existing `CLAdt` / `web.platform-schema` path (unchanged from today's blocking
`accept`/`send`); (b) the **capture-RC** of the `Response` retained across
`send-conn`'s park→write boundary (`CLOwned` it — §3.2, master "Capture-RC Protocol").
**No `poll_support` refinement is needed** — web confirms the Chunk-A suite is
complete (3rd consumer, zero new scaffold).

#### 3.5.5 The serial serve loop + the Chunk-B fan-out seam (`exemplar/main.cl`)

The Chunk-A serial loop threads the connection through read→handle→send,
tail-recursive (the connection token flows accept→read→send via ordinary binding):

```clojure
(import [web [listen accept read send Listener Connection Request Response]])

(defn port [] 8080)
(defn pool-size [] 64)      ; N — the Chunk-B in-flight ceiling (inert under the serial loop)

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

`handle` (the pure router, today's `main.cl`) is **unchanged**. The only reshape vs
today: `accept` yields a `Connection` (not a bare `Request`); a distinct `read` effect
rides that connection; `send` takes the connection + the response.

**The Chunk-B fan-out drops in WITHOUT touching the leaves or wrappers** (the sibling
`/design` intrinsics agent owns the supervisor + launch-and-continue seam). It factors
the per-connection work into `handle-conn` and detaches it:

```clojure
(defn handle-conn [conn]                ; the per-connection strand
  (bind (read conn)
    (fn [req] (send conn (handle req)))))

(defn serve-loop [listener]             ; Chunk-B shape (sibling-owned)
  (bind (accept listener)
    (fn [conn]
      ;; launch-and-continue: handle-conn detached + supervised; the in-flight COUNT
      ;; is bounded at N (= (pool-size), read off the Listener) by the slice-4 global
      ;; admission budget. No `spawn` in source. (sibling seam — referenced)
      (do (handle-conn conn)
          (serve-loop listener)))))
```

Because the `Connection` is a self-contained handle (carrying its own
token/capacity/fd), `handle-conn` is a pure function of `conn` — the fan-out wraps it
without re-plumbing. Serial loop = `(bind (handle-conn conn) (fn [_] (serve-loop
listener)))`; fan-out = `(do (handle-conn conn) (serve-loop listener))` — **same
connection threading, detached continuation.** This is the cleanly-drops-in property
the keystone requires.

#### 3.5.6 How `(token, capacity)` reaches the poll node — the A3 permit lights up

The wrapper (§3.5.3) places `(token, capacity)` as the leading operands ⇒ the backend
strict-peel bakes them to node offsets 32/40 (io-trampoline §14) ⇒ `await_poll_node`
reads them (reactor.md §2.9 step 1) ⇒ **`env.acquire(token, capacity, strand)` takes
the per-token permit BEFORE the poll-fn establishes**, holds it across the
establish→park→ready arc, and releases on `Ready` / drop (the RAII `Permit`). So every
web `accept-conn` / `read-conn` / `send-conn` is admission-wrapped — **the A3
acquire-around-poll permit is lit up by the web leaves**, the real consumer Chunk A
built it for.

What the permit gates, per granularity (honest, arch §16-faithful):

- **Per connection (capacity 1):** read→send on one connection serialize + order
  (§8.2 capacity-1 group) — dataflow already orders them, so the permit is
  correct-but-uncontended here.
- **Across connections (distinct tokens):** independent — different connections draw
  different tokens, so the per-token permit does NOT serialize them (arch §8.2
  "concurrent HTTP GETs draw distinct connection tokens → run concurrently").
- **The in-flight-CONNECTION-COUNT ceiling N:** enforced under Chunk-B fan-out by the
  **slice-4 global admission budget** (one reactor-thread `Semaphore`, reading `N` off
  the `Listener`), composing `min(capacity, degree)` over the *same* permit machinery
  (arch §8.1 / §16). It is **not** a per-connection capacity-N.

**Rejected alternative — a SHARED connection-pool token of capacity N** (so the
per-token permit alone bounds the count in Chunk A, without the slice-4 global budget).
Superficially closer to "the permit gates connection concurrency," but **rejected**:
(a) it contradicts arch §16 (web uses fresh per-connection tokens; the capacity-N pool
is the DB/SQL case, and connection count is bounded by *backpressure*); (b) it would
serialize all connections through one token's §8.2 ordering (unless capacity ≥ 2, which
erases the ordering anyway); (c) the capacity-N per-token pool mechanism is **already**
proven by the `poll-pool` test leaf (§3.4.6) — web need not re-prove it. The faithful
split (per-connection token capacity 1 + Chunk-B global budget for the count) keeps web
aligned with the ratified §16 model and still lights up the A3 permit on every leaf.

> **Coordination note for `/sprint` (not a blocker, no contradiction with the sibling
> seam).** The "N concurrent connections; the (N+1)th parks" acceptance witness for the
> *server demo* is a **Chunk-B** property (the slice-4 global admission budget the
> sibling `/design` intrinsics agent owns), NOT a Chunk-A per-token-permit property.
> Chunk A lights the permit up on every web leaf (admission-wrapped); Chunk B's global
> budget supplies the count ceiling. The capacity-N *per-token* parking witness already
> exists (the `poll-pool` leaf). No FIXME to `/arch` is warranted: the interface uses
> only the ratified §8.1 leading-pair carrier + ordinary `.cl` ADTs — no
> `cranelisp-types` change and no new cross-crate convention.

#### 3.5.7 /dev + /port Chunk-B web implements, in this order

1. **`/port` — the handle ADTs + wrappers** (`exemplar/web.cl`, §3.5.1/§3.5.3): add
   `web/Listener` + `web/Connection` deftypes; add the `listen`/`accept`/`read`/`send`
   destructuring wrappers over the (not-yet-built) raw effects. Export them from `web`.
2. **`/platform` — the v8 platform poll leaves** (`exemplar/platforms/web/src/lib.rs`,
   §3.5.2): one unified `declare_platform!` with `bind-listener` (blocking) +
   `accept-conn` / `read-conn` / `send-conn` (poll `ResourceSerial`), each over
   `poll_support` (§3.5.4); keep the pure `parse_http_request` / `format_http_response`
   halves; fd-keyed internal maps replace the `Mutex<ServerState>`.
3. **`/platform` (or `/int`) — regenerate `web.platform-schema`** for the new
   `Listener`/`Connection` ADTs + the new signatures (`/platform-schema web`).
4. **`/port` — reshape the serve loop** (`exemplar/main.cl`, §3.5.5): `accept` →
   `Connection`; thread it through `read` → `handle` → `send`; keep `handle` pure and
   tail-recursion intact.
5. **`/qa` — the web e2e rows** (deferred §3A web-roundtrip + §3C-web byte-identical;
   Gap G4 port-parametrizable fixture so 8080 does not collide in shared lanes). The
   reactor is always present on v8 (single trampoline) ⇒ `--run exemplar/main.cl` on the
   **default** binary serves; no concurrency-lane gating needed.
6. **Chunk-B fan-out co-land** (sibling `/design` intrinsics + `/dev`): factor
   `handle-conn`, launch-and-continue + supervisor (§3.5.5) — the connection threading
   from steps 1/4 drops in unchanged; the slice-4 global budget reads `N` off the
   `Listener` for the in-flight ceiling.

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
| **Observability** | Out-of-pass for the platform crate (the strand event stream is intrinsics/reactor-side, reactor.md §3). `poll_support` emits nothing — park/acquire/release events are stamped by the reactor when it drives the `EffectPoll`, not by the leaf. Noted as non-impact. |
| **Concurrency-safety** | The platform side stays single-threaded-per-leaf and permit-agnostic: a poll-fn registers readiness and returns `Poll`, never blocks, never re-enters admission (gate (a) req. 2, §3.2). The lock-free reactor-thread admission invariant (reactor.md §2.8) holds verbatim because the platform never touches the permit map. `PollState` lives in env scratch torn down by the host-built `drop_glue_ptr` (RC + drop for free, io-trampoline §12.2). |
| **Testability** | `PollEnv`/`Reactor`/`PollState` are unit-testable in-crate over a fixture env + a stub `HostCtx`/`Waker` (the `async_read_pollfn`/`timer_write_pollfn` precedent, reactor.md §2.7 — `concurrency`-gated unit tests). The macro convergence is pinned by `tests/macro_expansion.rs` (v7 GOT/manifest shape) + the `_neg` frozen-edge guard. e2e (distinct-token overlap, capacity-N poll parking) is `/qa`'s Chunk-A plan over the rewritten web/stdio. |

---

## 6. Cross-references

- `design/platform/platform.md` — master (this is subordinate; cited from §"Subordinate docs")
- `design/int/reactor.md` §2.6/§2.8/§2.9 — acquire-around-poll, the token-capacity pool, RAII `Permit`, the testability seams (sibling `/design` int)
- `design/backend/io-trampoline.md` §12 — `IO_TAG_EFFECT_POLL` node + state-closure env layout (the `PollEnv` consumer's contract; sibling `/design` backend)
- `design/backend/io-trampoline.md` §14 — the poll-node live `(token, capacity)` bake + the leading-pair operand convention the `inject_poll_leading_pair` pass produces (sibling `/design` backend; §3.4 here is the platform-side value-source half)
- `crates/cranelisp-backend/src/lib.rs::inject_poll_leading_pair` — the backend `MonoExpr` injection POINT A4 generalizes (§3.4.1); `crates/cranelisp-backend/src/compiler/resolution.rs::resolve_poll_effect_target` — extended to surface `scheduling_class` (the no-types-touch discriminator, §3.4.2)
- `platforms/pool-demo/src/lib.rs` — the S95 BLOCKING capacity leaf whose `ResourceSerial` + explicit-`(token, capacity)`-args convention the poll carrier mirrors (§3.4.2/§3.4.6)
- `design/arch/effect-concurrency.md` §5/§8/§12 — descriptor, token-capacity carrier, A2 host-reactor model (**`/arch`-owned, read-only**); §8.2 within-token ordering + §10 supervisor + §16 the web/DB reference workload (the fresh-per-connection-token + backpressure model §3.5 is faithful to)
- `design/platform/poll-support.md §3.5` — the concrete web connection-handle cranelisp interface (resolves FIXME 0465); the Chunk-B keystone the slice-5 server demo exercises
- `exemplar/web.cl`, `exemplar/main.cl` — the `/port`-owned `.cl` surface §3.5.1/§3.5.3/§3.5.5 specifies (handle ADTs + wrappers + serve loop)
- `design/arch/platform-interface.md` §6.8 — the ABI-v4 cascade / numeric `ABI_VERSION` 6→7 (**`/arch`-owned**)
- `crates/cranelisp-platform/src/concurrency.rs` — the v7 C-ABI contract types
- `crates/cranelisp-platform/src/declare.rs` — `declare_platform!` / `__declare_platform_body!` / `declare_concurrent_platform!` (the macro pair the convergence reshapes)
- `tests/facade_pif_rows.rs::concurrency_descriptor_absent_from_default_public_api_neg` — the `_neg` frozen-edge guard (gate (c) enforcement)
- `exemplar/platforms/web/src/lib.rs`, `platforms/stdio/src/lib.rs` — the rewrite targets

---

## /dev A4 implements, in this order:

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
