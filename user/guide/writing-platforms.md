# Writing a platform — poll-shape effect leaves

A **platform** is how cranelisp reaches the outside world: files, sockets, stdin,
a database, a clock. The core language has no built-in I/O — every effect a program
performs is provided by a platform it declares with `(platform <name>)`. `stdio` and
`web` ship in-tree; this guide is for authoring your own.

This is the *platform author's* view. If you only want to **use** concurrency and I/O
from cranelisp, you are on the wrong page — read
[concurrency.md](concurrency.md) (the control combinators and inferred fan-out) and
[getting-started § Platforms and IO](../getting-started.md#platforms-and-io) instead.
Nothing on this page — tokens, capacity, poll functions, the reactor vtable — is
visible to a program author, by design.

Platforms are written in **Rust** and compiled to a binary (a `cdylib` for
REPL/`--run`, an `rlib` for `--link`) that ships alongside bundled `.cl` modules on
the platform search path. Authoring one needs a Rust toolchain; a *user* of your
platform needs none. The exact Rust API surface is normative in the design docs cited
throughout — this guide gives you the model and the shape so those docs read as
elaboration rather than first contact.

> **Status.** The poll-shape / `ctx`-vtable model described here is the shipped model
> for the in-tree `web` platform (see `exemplar/platforms/web/` and `exemplar/web.cl`).
> The canonical, normative sources are
> [`design/arch/effect-concurrency.md`](../../design/arch/effect-concurrency.md) §4.1.1
> and §12, [`design/platform/poll-support.md`](../../design/platform/poll-support.md),
> and [`design/intrinsics/reactor.md`](../../design/intrinsics/reactor.md). Where this
> guide and those disagree, the design docs win.

---

## The boundary: poll-in / wake-out only

The single most important fact about the platform boundary: **exactly two functions
cross it, and a cranelisp closure is not one of them.**

- **poll-in** — the host calls your platform's **poll function**. You try your
  non-blocking syscall and return either `Ready(result)` (you have a value) or
  `Pending` (it would block; you asked to be woken later). This is the *what*: your
  domain, your protocol.
- **wake-out** — when your syscall would block, you tell the host reactor to re-poll
  you later by registering interest (fd-readable, fd-writable, or a timer) through a
  host-provided vtable, handing it a **waker**. This is the *when*: the host's single
  reactor owns it.

That is the whole boundary. **A platform never calls back into a cranelisp closure.**
There is no host-mediated "invoke this cranelisp handler" capability — a continuation
is the trampoline's own suspended state, held host-side; it is never a handle your
platform holds and calls. Your platform returns `Ready`/`Pending` and signals a
waker, and the host resumes the continuation. This is a firm architectural ruling
([`effect-concurrency.md §12.1`](../../design/arch/effect-concurrency.md), S98), and it
is what keeps every platform a thin, stateless C-ABI leaf:

- A platform owns only its domain protocol and holds **no** cranelisp state — no RC,
  no error-slot ferrying, no scheduling logic pushed down into it.
- The one case that *looks* like it needs a callback — a C library that demands a
  synchronous callback (a `qsort` comparator, a GUI `run()` loop) — is served by
  writing that callback **in Rust, inside your platform**, and exposing only a
  poll-shaped effect to cranelisp. The re-entrant callback never becomes a
  cranelisp-closure-across-the-C-ABI contract.

Because you never block (you return `Pending` instead), **cancellation is free**: the
host simply stops polling you and drops the suspended state. Nothing is ever stuck
inside a syscall waiting to be interrupted.

---

## The poll function

Each async-capable effect is a **poll function** with a uniform signature (C-ABI):

```
poll(state, ctx, waker) -> Ready | Pending
```

- `state` is the effect's marshalled arguments plus a result slot and private
  scratch, laid out by the host (`poll_support`'s typed `PollEnv` accessor locates
  the fields for you — see [`poll-support.md §2.1`](../../design/platform/poll-support.md)).
- `ctx` is the host reactor's vtable (below).
- `waker` is the token you hand back to the reactor so it can re-poll you.

The host **re-invokes the same poll function** after each wake, so it must be able to
resume: first poll opens the fd and tries the syscall; later polls re-attempt after a
readiness fires. `poll_support`'s `PollState` scaffold encodes the
first-poll-vs-re-poll phase for you.

Every poll-shape leaf has the **same skeleton**
([`effect-concurrency.md §4.1.1`](../../design/arch/effect-concurrency.md)):

```
poll(state, ctx, waker):
    token = project_token(state.handle)          # you compute it from your handle
    if token != 0:
        if ctx.acquire(token, capacity, waker) == Parked:
            return Pending                        # backpressure: no op without a permit
    r = state.syscall(NONBLOCK)                   # your `what`
    if would_block(r):
        ctx.register_<interest>(state.fd, waker)  # the host's `when`
        return Pending
    set_result(state, value_from(r))
    return Ready
```

Sync / non-blocking effects just fall straight through to `Ready`. A blocking-style
effect (e.g. `stdio`'s ordering-critical `print`) can stay a plain blocking leaf —
blocking and poll-shape effects coexist in one platform, and a host that never
activates concurrency sees only the blocking shape.

---

## The `ctx` vtable — the host reactor

The host owns a single reactor. Your poll function talks to it through the `ctx`
vtable ([`effect-concurrency.md §4.1.1`](../../design/arch/effect-concurrency.md),
[`reactor.md §2.3`](../../design/intrinsics/reactor.md)). `poll_support`'s `Reactor`
wrapper ([`poll-support.md §2.2`](../../design/platform/poll-support.md)) turns each
vtable call into a one-liner:

| Verb | You call it to… | Returns |
|---|---|---|
| `register_readable(fd, waker)` | ask to be re-polled when `fd` becomes readable | — |
| `register_writable(fd, waker)` | …when `fd` becomes writable | — |
| `register_timer(deadline, waker)` | …when a deadline passes | — |
| `acquire(token, capacity, waker)` | ask for a permit on a resource's pool | `Acquired` \| `Parked` |
| `retire(token)` | end a resource's scheduling identity (after `close`) | — |

Two rules matter:

- **`acquire` is idempotent per in-flight effect.** A re-poll calls it again; the
  host keys held permits by the effect's identity (the waker's data pointer) and
  returns `Acquired` without double-counting. So your skeleton needs no "have I
  already acquired?" flag. On `Parked`, return `Pending` **before** the syscall — an
  op must never start without a permit (that is the backpressure / pool bound).
- **Release is host-owned. There is no `release`.** The host releases a held permit
  automatically when the poll completes (`Ready`) *or* when the effect is cancelled
  (its future drops) — and **cancel never re-enters your poll function**. You express
  *intent* (`acquire`); the host owns *lifecycle*. You could not soundly release on a
  cancel you never see, which is exactly why `release` is absent from the vtable.

---

## The handle model — scheduling state never rides on a value

When a platform mints a resource (a socket, a file, a DB connection), it hands the
program a **handle**: an ordinary cranelisp ADT. Two properties define the model
([`effect-concurrency.md §4.1.1`](../../design/arch/effect-concurrency.md)):

1. **The handle is tramp-opaque but user-readable.** "Opaque" means *the trampoline
   never introspects it* — there is no per-ADT "the token is field N" knowledge
   anywhere in the host, no reserved slot, no hidden header. It is **not** opaque to
   the user: it is *their* connection, carrying genuine program data (the fd, a peer
   address) in real ADT fields the program can `match` open. Model it on
   `std::net::TcpStream` with `as_raw_fd()` *available* — not a sealed newtype.

   ```clojure
   ;; the web Connection: a slim opaque handle carrying only the platform's fd
   (deftype Connection [:primitives/Int fd])
   ```

2. **Scheduling state never touches the value.** There is no `token` field, no
   `capacity` field, no header slot, no descriptor stamped onto the handle. The
   `(token, capacity)` a resource schedules on is **not** stored on the value at all.
   Instead your poll function **projects the token from the handle each poll** — for
   `web`, `token == fd`, read straight out of the `Connection`'s `fd` field — and
   calls `ctx.acquire(token, …)` itself. Because you recompute the token, the host
   keeps no handle→token scoreboard; its only scheduling state is a permit map per
   token and the reactor's interest table.

   > Full-duplex resources project **distinct** tokens per direction (`read_tok` /
   > `write_tok`) off one handle, so reads and writes do not serialize against each
   > other. `token == 0` means commutative — no acquire at all.

This model deliberately replaced an earlier one that carried a descriptor on the
value's heap header; that hit a blocker when an opaque DLL-minted handle had no room
for the slot. Carrying nothing on the value dissolved it. A consequence worth knowing:
because the handle carries no scheduling state and the host never reads it, a program
that *fabricates* a handle (`(Connection 999)` with an arbitrary fd) cannot corrupt
host state — the OS is the capability checkpoint, and a bad fd just returns `EBADF` as
an ordinary, recoverable I/O error.

---

## The four leaf roles

Each effect declares a **role** in its manifest — a compile-time fact that grounds the
inferred-launch analysis and documents the leaf. The trampoline does **not** branch on
role at runtime; every leaf does its own scheduling through the `ctx` vtable
([`effect-concurrency.md §4.1.1`](../../design/arch/effect-concurrency.md),
[`poll-support.md §3.6.1`](../../design/platform/poll-support.md)):

| Role | Examples | What the poll function does |
|---|---|---|
| **Produce** | `open` / `accept` / `connect` | Drives `acquire` / `register_*` on the *establishment* resource (the listener fd for `accept`; a fresh socket for `connect`). There is no program handle yet — at `Ready` it **mints the handle ADT** carrying the new `r` and returns it. |
| **Consume** | `read` / `write` / `send` / DB `query` | `state.handle` **is** the handle; reads `r` off its genuine field, projects the (per-direction) token, `acquire`s, does the I/O syscall. |
| **Retire** | `close` | `close(r)` syscall, then `ctx.retire(token)` for each of the resource's tokens (full-duplex: both). Ends the scheduling identity. |
| **None** | a commutative GET, `sleep` | No token (or token 0); no acquire. |

A leaf is never both Produce and Consume. **Singleton resources with no per-value
handle** (stdin, a global rate-limiter) declare a **manifest-static** token — e.g.
`read-line : {token: STDIN_TOKEN, capacity: 1, role: Consume}` — and the poll function
`acquire`s that constant. Capacity 1 then enforces single-in-flight stdin *by
construction*, with no value and no special case.

---

## The concurrency descriptor — the trust boundary

Each effect declares a **concurrency descriptor** in the manifest — the finite,
declarative statement of how it schedules
([`effect-concurrency.md §5`](../../design/arch/effect-concurrency.md)):

| Field | Meaning | Who owns it |
|---|---|---|
| **token** | what the effect conflicts on = the resource identity (`0` = unrestricted) | platform (computed dynamically, per poll) |
| **capacity** | the resource's safe-concurrency *ceiling* — "this token correctly sustains ≤ N concurrent ops" | platform (**trust** — you assert it) |
| **degree** | the *program's* chosen in-flight throttle, always ≤ capacity | program (policy) |
| **blocking?** | does it block, or yield on `WouldBlock`? — selects the worker pool | platform |

**Capacity is per-resource (per-token), not per-effect** — this is the central case,
not an edge. A DB pool of N connections backs *distinct* effects (`query`, `execute`,
`begin`) that all draw from the **same** pool: sum in flight ≤ N. So capacity attaches
to the token, and effects reference the token. Distinct token ⇒ independent capacity;
shared token ⇒ shared pool — one mechanism.

The descriptor is a **trust boundary**, continuous with the existing one: the compiler
does not verify that a `Commutative` effect truly has no shared state, nor that an
asserted capacity is the resource's true ceiling. You assert safety; the language takes
it on faith. That assertion is your platform's `unsafe`.

Capacity rides *with* the token, supplied dynamically at the effect site (a pool's
size is a runtime config known only when the pool opens), not baked statically per
effect kind. The static descriptor fields are defaults + documentation.

---

## Packaging: the manifest and the two-module rule

A platform ships as a directory on the platform search path containing the binary plus
bundled `.cl` modules, and exports three things the loader reads
([`design/arch/platform-interface.md`](../../design/arch/platform-interface.md)):

- the **GOT** — the linker-fixed-up table of effect function pointers (your poll
  functions), dispatched indirectly;
- the **manifest** — the declarative block the host builds a symbol table from: per
  effect, its fully-qualified name, type signature, concurrency descriptor, role, and
  poll-shape flag;
- the **schema + layout-hash** — a compiler-generated artifact describing the layout of
  the ADTs your signatures reference, gate-checked at load.

You declare effects with the `declare_platform!` macro (each effect names its
descriptor / role / poll-vs-blocking); the macro emits the GOT and manifest together in
one declared order. Platforms **do not declare ADTs** — the types your signatures
reference are ordinary importable `.cl` modules, and the backend generates the schema
from them.

**The two-module rule.** When a platform's effect signatures reference `.cl` ADTs in a
module `M`, the loader typechecks `M` *before* registering the platform. Therefore `M`
**must not import that platform**. Any convenience wrapper that *calls* the platform's
own effects must live in a **different** module
([`poll-support.md §3.6.3`](../../design/platform/poll-support.md)). The `web` pattern:

1. the **type module** (`web.cl`) — declares the handle/request/response ADTs; imports
   no platform; loaded by the pre-resolve.
2. the **wrapper module** (`serve.cl`) — imports both `web.cl`'s ADTs and the platform
   effects; loaded only when a program imports it, after registration. Under the
   `ctx`-vtable model these wrappers are near-trivial pass-throughs (no token/capacity
   pair to thread, no descriptor to read):

   ```clojure
   ;; serve.cl — wrappers over the raw platform effects
   (defn read [conn]      (read-conn conn))
   (defn send [conn resp] (send-conn conn resp))
   ```

---

## See also

- [concurrency.md](concurrency.md) — the *user* side: the control combinators
  (`race` / `select` / `timeout` / `sleep`), structured cancellation, and the inferred
  fan-out your poll leaves make possible.
- [`design/arch/effect-concurrency.md`](../../design/arch/effect-concurrency.md) — the
  ratified architecture: §4.1.1 (the `ctx`-vtable handle model, roles, the poll-fn
  skeleton), §5 (the concurrency descriptor), §12 / §12.1 (the C-ABI-async boundary and
  the poll-in / wake-out ruling).
- [`design/platform/poll-support.md`](../../design/platform/poll-support.md) — the
  `poll_support` scaffolds (`PollEnv`, `Reactor`, `PollState`), the four-role
  leaf-authoring contract (§3.6), and the `web` / `stdio` worked adoptions.
- [`design/intrinsics/reactor.md`](../../design/intrinsics/reactor.md) — the host
  reactor interior: the mio loop, the C-ABI waker projection, the `HostCtx` vtable, the
  token-capacity permit pool.
- [`design/arch/platform-interface.md`](../../design/arch/platform-interface.md) — the
  three-exports deployment model (GOT + manifest + schema), the loader, and `ABI_VERSION`.
- `exemplar/web.cl`, `exemplar/serve.cl`, `exemplar/platforms/web/` — the in-tree
  worked platform.
