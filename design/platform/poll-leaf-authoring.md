# Poll-leaf authoring — the ctx-vtable contract

**Status:** current design. Subordinate to `platform.md`.

How a platform DLL author writes a poll-shape async leaf, and what
`crates/cranelisp-platform/src/poll_support.rs` supplies to make that cheap.
This is the *platform side* of the boundary; the reactor, the permit pool and
the trampoline cadence are owned elsewhere (`design/intrinsics/reactor.md`,
`design/backend/io-trampoline.md`) and are referenced here, never redescribed.

---

## 1. What a poll leaf is

A platform effect is either **blocking** — an `extern "C"` fn returning
`CLIO<T>`, whose thunk the trampoline forces on a worker — or **poll-shape**:

```rust
type PollFn = unsafe extern "C" fn(
    state: *mut c_void,
    host:  *const HostCtx,
    waker: *const Waker,
) -> Poll;
```

The choice is per effect, declared in the one manifest
(`concurrency.blocking == 0` ⇒ poll-shape), and both may appear in one platform.

**The division of labour is the whole design.** The platform owns the *what* —
it performs the non-blocking syscall. The host owns the *when* — on `WouldBlock`
the leaf registers interest through the `HostCtx` vtable and returns `Pending`;
the host's single reactor re-polls when the fd or timer fires. The platform
carries no runtime, spawns no thread, and never learns an async concept.

`state` is the host-built state-closure env, not a DLL allocation. The DLL
neither allocates nor frees it; the optional `drop_state:` manifest hook is the
only teardown the DLL contributes.

---

## 2. The uniform skeleton

Every poll leaf has this shape. Nothing about it is per-platform.

```
poll(state, ctx, waker):
    token = project_token(state.handle)          # the platform computes this
    if token != 0:
        if ctx.acquire(token, capacity, waker) == Parked:
            return Pending                        # no operation without a permit
    r = state.syscall(NONBLOCK)                   # the platform's `what`
    if would_block(r):
        ctx.register_<interest>(state.fd, waker)  # the host's `when`
        return Pending
    set_result(state, value_from(r))
    return Ready                                  # the host releases the permit
```

Four properties an author must be able to rely on:

- **`Parked` returns before the syscall.** An operation is never started without
  a permit; that is what makes the pool a bound rather than a hint.
- **`acquire` is idempotent per in-flight effect.** The host keys held permits by
  the waker's data identity, so a re-poll re-`acquire`s without consuming a
  second permit. The skeleton therefore needs **no "have I already acquired?"
  flag** on `state` — a flag would be a second, divergent record of a fact the
  host already holds.
- **Release is trampoline-owned.** There is no `release` in the vtable. The host
  releases on `Ready` *or* on cancel, and **cancel never re-enters the poll-fn**,
  so a leaf is never asked to free a permit on an event it cannot observe.
- **A commutative leaf omits `acquire` entirely** (`token == 0`). A one-shot
  timer leaf is the degenerate case: no handle, no token, no acquire — just
  `register_timer` → `Pending` → `Ready`.

---

## 3. The four roles

A leaf's **role** is a per-effect static fact on the manifest's
`ConcurrencyDescriptor.role` (`ResourceRole { None, Produce, Consume, Retire }`)
— a fact about the *leaf*, never a field on a value. **The trampoline does not
branch on role at runtime**: role grounds inference and documents the leaf; all
scheduling flows through the vtable calls the poll-fn makes itself.

| Role | Declare it when | The poll-fn does | The trampoline does |
|---|---|---|---|
| **`None`** | the effect neither produces nor consumes a scheduling resource — a bare timer, a fire-and-forget log, a bind, a one-shot sleep | no `acquire`; `register_timer` only if it waits | nothing scheduling-specific |
| **`Produce`** | the effect **mints** a resource handle whose later use must be admission-controlled (`accept`, `connect`, `open`) | drives `acquire`/`register_*` on the **establishment** resource — the listener fd, or a fresh fd it minted; there is no program handle yet. At `Ready` it mints the handle ADT carrying the new resource in a genuine field and `set_result`s it | releases the establishment permit on `Ready`/cancel; passes the minted value onward unstamped |
| **`Consume`** | the effect **operates on** a previously produced handle and must serialize within that resource (`read`, `write`, `send`; a query over a pooled connection) | reads the resource off the handle argument's genuine field, projects the (per-direction) token, calls `acquire` itself, then the syscall and `register_*` on `WouldBlock` | releases the permit on `Ready`/cancel, keyed by effect identity |
| **`Retire`** | the effect **ends** a resource's scheduling identity (`close`) | `acquire` (idempotent), the `close` syscall, then `ctx.retire(token)` for **each** of the resource's tokens — a full-duplex resource retires both directions | releases the permit on `Ready`; the retire drops the token's pool and wakes any token-parked waiter |

**The asymmetry is the load-bearing subtlety.** Every leaf performs its own
scheduling through the vtable; there is no writer/reader split over a shared
descriptor. A `Produce` leaf drives admission on the resource it is
*establishing*; a `Consume` leaf projects the token from the handle it *holds*.
A leaf is never both: if an effect both mints a handle and rides a prior one, it
declares `Produce`, and admission on the prior handle is the caller's concern.

**Singleton resources.** A resource that is not minted per value — stdin, a
global rate limiter — has no handle to project a token from. It declares a
**manifest-static** serial token on the effect (`token != 0`, `capacity: 1`,
`role: Consume`) and the poll-fn acquires on that constant, read from the
effect's own descriptor rather than off any value. `stdio`'s `read-line` is the
canonical case; it enforces single-in-flight structurally, with no value, no
header slot and no special case.

---

## 4. Resource handles

A resource handle is an **ordinary `.cl` ADT** carrying the platform's own
descriptor in a genuine field — for example
`(deftype Connection [:primitives/Int fd])`.

- **Opaque to the trampoline**, which never introspects it.
- **Not opaque to the user program**, which destructures it like any ADT.
- The leaf reads the field through the ordinary `CLAdt` / platform-schema path
  off `PollEnv::arg(0)` — the same accessor it uses for any ADT field. There is
  no descriptor-offset helper, no header admission slot, and no `desc_out`
  out-parameter; the v8 shapes that had them are retired.
- Token projection is the platform's own function of the handle's contents
  (`token == fd` for a simple case; per-direction tokens for full duplex). The
  token is never stored on the value.

**The opacity is toward the trampoline, not the user.** The trampoline threads
the handle from the producing leaf to the consuming ones without ever reading a
field; only the platform, which built it, reads the descriptor back out. That is
what lets all scheduling live in the ctx vtable with no value-carried scheduling
state. User code may still destructure the handle — it is the program's own
resource, and no language mechanism makes an ADT non-destructurable. The analogy
is a `TcpStream` that exposes `as_raw_fd()`, not a descriptor the program cannot
reach.

Fabrication of a handle is a platform-IO concern: the OS syscall is the
capability checkpoint, not the ADT. A forged or unowned descriptor fails as an
ordinary recoverable IO error, never as host undefined behaviour.

**More handle data composes normally.** A platform whose admission token is not
the syscall descriptor — a multiplexed or pooled resource — adds further genuine
fields and projects the token from whichever it chooses. There is no header slot
to coordinate with, because the token is always a projection the platform
computes rather than a stored datum.

---

## 5. What `poll_support` supplies

Three scaffolds, each the single home for one repeated, error-prone, `unsafe`
idiom. All are **core/ungated** — the `concurrency` feature was retired at the
single-ABI cutover and the crate has no `[features]`.

| Scaffold | Single-sites |
|---|---|
| **`PollEnv`** | the state-closure env layout: the result slot at `state + 0`, marshaled `i64` leaf args at `state + 8 + 8*i`. The offsets are derived here once instead of by hand in every leaf. |
| **`Reactor`** | the `HostCtx` vtable calls: `wake_on_readable` / `wake_on_writable` / `wake_on_timer`, plus `acquire(token, capacity) -> Acquire` and `retire(token)`. There is deliberately **no `release`** — release is trampoline-owned. |
| **`PollState` / `PollStep`** | the first-poll / re-poll phase distinction, so a leaf expresses "establish once, then re-check" without an ad-hoc discriminant in its own state. |

`poll_support` deliberately does **not** own: the reactor itself, the permit
pool, the poll-node construction, any codegen operand placement, or any
scheduling decision. It is leaf-author ergonomics over contracts owned
elsewhere. Adding a fourth scaffold that reaches into any of those is the
boundary violation to watch for.

---

## 6. The two-module rule for platforms with typed handles

> Structural, and independent of the vtable model.

When a platform's effect signatures reference `.cl` ADTs declared in a module
`M`, `M` is loaded and typechecked by the platform-load **pre-resolve**, *before
the platform is registered*. Therefore **`M` must not import that platform** —
neither by `(import [platform.<name> …])` nor by a fully-qualified
`platform.<name>/…` call, since FQ auto-load triggers the same mid-load cycle.
Both produce a hard module error.

The consequence for authors is a two-module split:

1. **The type module** (`M`) declares the ADTs the signatures reference. It is
   platform-import-free and is loaded by the pre-resolve.
2. **The wrapper module** imports both `M`'s ADTs and the platform's effects,
   and is loaded only when a program imports it — after registration.

This is a general rule, not a quirk of any one platform: the next platform that
wants convenience wrappers over its own ADTs follows the same split.

---

## 7. Worked references

| Platform | What it demonstrates |
|---|---|
| `platforms/async-demo` | the minimum leaf — one poll fn, `role: None`, no token |
| `platforms/poll-pool` | eight leaves across `Produce`/`Consume` roles with self-`acquire`, plus fault, block and no-interest paths — the in-tree exercise of the general seam |
| `platforms/stdio` | one blocking effect and one poll leaf in one manifest, with the singleton-resource manifest-static token |
| `exemplar/platforms/web` | the full shape: typed handles across poll leaves, `Produce` establishment and `Consume` operation, an embedded schema — built entirely on this contract with no platform-crate extension |

**The web reference in full**, because it is the one in-tree platform that
exercises every part of §3 and §4 at once. Four effects in one manifest, mixing
blocking and poll:

| Effect | Shape and role | Signature | How scheduling is driven |
|---|---|---|---|
| `bind-listener` | blocking, `Sequential`, role `None` | `(Fn [Int Int] (IO web/Listener))` | none — a bind is fast, and a `Listener` is not a per-poll resource |
| `accept-conn` | poll, `Produce` | `(Fn [web/Listener] (IO web/Connection))` | registers on the **listener** descriptor it is establishing on; at `Ready` mints a `Connection` carrying the fresh descriptor |
| `read-conn` | poll, `Consume` | `(Fn [web/Connection] (IO web/Request))` | reads the descriptor off the handle, acquires the **read** token, parks on readable |
| `send-conn` | poll, `Consume` | `(Fn [web/Connection web/Response] (IO Int))` | same, on the **write** token — distinct from the read token, so the two directions do not serialize against each other |

The handle types are ordinary `.cl` ADTs in `exemplar/web.cl`
(`(deftype Connection [:primitives/Int fd])`), not platform declarations. The
manifest signatures are fully qualified, as every manifest signature must be
(`platform.md` §5, invariant 8). Per-effect truth — the descriptors, the
parameter names and the leaf bodies — is the platform crate's own source and its
crate-root rustdoc.

---

## 8. Cross-references

- `platform.md` — the master design; the ABI and node layouts
- `crates/cranelisp-platform/src/{concurrency,poll_support}.rs` — the contract
  types and the scaffolds; per-item truth is their rustdoc
- `design/arch/effect-concurrency.md` §4.1.1 — the ctx-vtable model
- `design/arch/platform-interface.md` §6.8.0b — the v9 handle model
- `design/intrinsics/reactor.md` — the reactor, the permit pool, acquire-around-poll
- `design/backend/io-trampoline.md` §12 — the poll-node bake and the env layout
