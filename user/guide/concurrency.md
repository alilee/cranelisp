# Concurrency — throughput is free, control is explicit

Cranelisp's concurrency model has **two complementary halves** — peers, not a
primary feature with a footnote:

- **The inferred half (throughput).** The compiler extracts concurrency from the
  *dataflow independence* of your program automatically. You write ordinary
  direct-style code with **zero concurrency primitives** — no `spawn`, no `go`, no
  `async`, no threads, no locks — and the runtime overlaps independent work for you.
  The result is provably identical to running everything sequentially. This is
  *concurrency written by nobody*.
- **The explicit-control half (timing).** Everything that branches on completion
  *timing* — races, deadlines, cancellation — is a small set of in-language
  combinators (`sleep`, `race`, `select`, and the derived `timeout`). Dataflow can
  say "B's value depends on A's value"; it can never say "give up after 200ms" or
  "cancel the loser". That is irreducible, so it is a handful of ordinary typed
  functions you call explicitly.

The two halves build on the same foundation as the IO model
([getting-started § Platforms and IO](../getting-started.md#platforms-and-io)):
a single serializing interpreter (the *trampoline*) folds all effects into one
coherent order. Concurrency is permitted only over work that is provably
independent, which is what makes the inferred half's "identical to sequential"
promise hold. The full architecture is specified in
[`design/arch/effect-concurrency.md`](../../design/arch/effect-concurrency.md) and
the normative rules live in [`spec/10-io.md`](../../spec/10-io.md) §10.12.

> **Writing your own platform?** This page is about *using* concurrency from
> cranelisp. If you are authoring a platform DLL — poll-shape effect leaves, the
> reactor boundary, the connection/handle model — see the companion
> [**writing-platforms.md**](writing-platforms.md). Everything on *this* page is
> what a program author sees; none of the platform-side scheduling machinery
> (tokens, pools, poll functions) is visible here, by design.

---

## The inferred half — concurrency written by nobody

Two independent effects with no shared data may run at the same time. The classic
case is a server: a loop that accepts a connection, handles it, and loops to accept
the next. Because each connection is independent of the next, the handlers overlap
**with no `spawn` in the source**.

### The server with no `spawn`

This is the shape the showcase web server uses (from
[`exemplar/main.cl`](../../exemplar/main.cl), validated by `tests/exemplar_web.rs`):

```clojure
;; accept one connection, launch its handler, immediately accept the next
(defn serve-loop [listener]
  (bind (accept listener)
    (fn [conn]
      (do
        ;; the per-connection handler: read → (optional delay) → send.
        ;; Its result is DISCARDED (the `do`), and its work touches only
        ;; this freshly-accepted `conn` — so the runtime LAUNCHES it and does
        ;; not wait for it to finish.
        (bind (read-conn conn)
          (fn [req]
            (bind (sleep (slow-ms req))
              (fn [_] (send-conn conn (safe-handle req))))))
        ;; the continuation: accept the next connection right away
        (serve-loop listener)))))
```

There is no `spawn`, `go`, or `async` anywhere. The compiler infers the fan-out
because the handler's result is unused and its effects act only on the
freshly-accepted connection — so launching it and moving on changes nothing about
what the program computes. `K` concurrent slow requests overlap (finishing in
roughly the time of *one*) instead of serializing.

### The discipline that makes it fire

The inference is **conservative**: it only launches a handler when it can prove,
locally, that doing so is safe. In practice this means every effect inside the
handler must be a **direct leaf** over connection-local values:

- A platform effect on the freshly-bound connection (here `read-conn` / `send-conn`),
  or the resource-free `sleep` timer — these are direct, inspectable leaves.
- A **user function that returns IO**, placed in an effect position, is an *opaque
  footprint* the analysis cannot see into, so it **refuses to launch** and the
  server silently falls back to serial. Keep pure helpers pure: in the example
  above, `slow-ms : Request -> Int` and `safe-handle : Request -> Response` compute
  the *arguments* to the direct `sleep` / `send-conn` leaves — they are never
  themselves placed in an effect position.

You do not annotate any of this; you write the handler inline over the connection
and the launch falls out. The eligibility rule is specified in
[`design/arch/effect-concurrency.md §4.1`](../../design/arch/effect-concurrency.md)
and [`spec/10-io.md §10.12.7`](../../spec/10-io.md).

This is the IO-effect sibling of the **pure-compute** parallelism documented in
[automatic parallelism](../getting-started.md#automatic-parallelism) and
[parallel collections](parallel-collections.md). Both extract concurrency from
independence; they run on different substrates (the reactor for I/O, rayon for CPU).

### Connections are ordinary values you can read

`accept` hands your program a **connection handle** — an ordinary value. It is
*your* connection: you can `match` it open to read its fields exactly like any
other data type. A minimal web `Connection` carries the socket descriptor:

```clojure
(deftype Connection [:primitives/Int fd])

(defn conn-fd [c]
  (match c [(Connection fd) fd]))     ;; reads the real fd — typechecks and works
```

There is **no hidden scheduling state** on the value — no tokens, no pool
bookkeeping, nothing the runtime stamps in. A handle is just data your program
owns; how many connections may run at once is the platform's concern, decided
platform-side, and never something you thread through your code. (How the platform
does that is the subject of [writing-platforms.md](writing-platforms.md).)

### Honest scope: shared resources are bounded

Independent IO effects overlap — **but effects that share one resource are bounded
by that resource.** The canonical case is a database connection pool: many `query`
effects can be in flight at once, but the number in flight is capped by the pool,
and one more **parks** (waits) until a slot frees, which you observe as latency.
Effects on *distinct* resources are independent and overlap freely; effects on a
strictly-serial resource run one at a time in source order.

You never choose the limit and never write pool code — the platform decides it and
the runtime enforces it. From your side this is invisible except as
throughput/latency. The observable contract is
[`spec/10-io.md §10.12`](../../spec/10-io.md).

---

## The explicit-control half — timing combinators

When the outcome depends on *timing* — racing two operations, bounding work by a
deadline, cancelling a loser — you reach for explicit combinators. They are
**ordinary typed functions**, not special forms: each takes IO value(s) and builds a
new IO value describing the concurrent composition. Building the IO runs nothing;
the composed effect runs only when it is sequenced into the program.

| Combinator | Type | Behaviour |
|---|---|---|
| `sleep` | `(Fn [Int] (IO Int))` | Park for *d* milliseconds, then resume with `0`. |
| `race` | `(Fn [(IO a) (IO a)] (IO a))` | Run both; the first to complete wins, the **loser is cancelled**. |
| `select` | `(Fn [(Vec (IO a))] (IO a))` | N-ary race over a non-empty `Vec`; first to finish wins, all losers cancelled. An **empty** `Vec` raises a fatal error (see below). |
| `timeout` | `(Fn [Int (IO a)] (IO (Option a)))` | Stdlib: `(Some v)` if the work wins, `None` if the *d*-ms timer fires first (cancelling the work). |

`sleep`, `race`, and `select` are `primitives` builtins — no platform DLL, no
environment variable needed. Import them by name:

```clojure
(import [primitives [Pure bind sleep race select]])
```

### `race` — the faster branch wins

Define each branch as a named helper so it reads as a self-contained unit of work
(this is also the supported shape — see [rough edges](#known-rough-edges)):

```clojure
(import [primitives [Pure bind sleep race]])

(defn fast [] (bind (sleep 50)  (fn [_] (Pure 111))))   ;; ready after ~50ms
(defn slow [] (bind (sleep 300) (fn [_] (Pure 222))))   ;; ready after ~300ms

(defn main []
  (bind (race (fast) (slow))
    (fn [r] (Pure r))))                                 ;; -> 111
```

```
cranelisp --run race.cl   # exit code 111 — fast won; slow was cancelled
```

The whole race completes in ~50ms, not ~300ms: cancellation means the loser is not
left running with its result discarded — its future is dropped and its remaining
effects never happen.

### `select` — n-ary race over a Vec

`select` generalises `race` to a `Vec` of branches. It takes a Vec literal `[..]`,
never a List:

```clojure
(import [primitives [Pure bind sleep select]])

(defn fast [] (bind (sleep 50)  (fn [_] (Pure 7))))
(defn slow [] (bind (sleep 300) (fn [_] (Pure 9))))

(defn main []
  (bind (select [(slow) (fast) (slow)])
    (fn [r] (Pure r))))                                 ;; -> 7 (the fast branch)
```

```
cranelisp --run select.cl   # exit code 7
```

**Empty `select` is a fatal error.** `(select [])` over an empty `Vec` has no branch
that can win and no value to return, so it **raises a runtime error** rather than
returning a value or hanging. This raise happens when the effect *runs*, which is
outside any `catch-runtime-error` bracket — so it is **fatal and NOT catchable**:
it terminates the process in batch mode and aborts the expression in the REPL.
Wrapping the `select` in a thunk does not help; it only defers the raise. Always
give `select` a **non-empty** Vec. This is the honest general rule for *every*
run-time effect error, not a `select` special case (spec
[§10.12.8](../../spec/10-io.md) — the empty-`select` ruling).

### `timeout` — bound work by a deadline

`timeout` is a **standard-library** function, derived as `timeout d io = race io
(sleep d)` with each arm mapped into `Option`. It returns `(IO (Option a))`: `(Some
v)` if the work completes in time, `None` if the deadline fires (cancelling the
work). Because it lives in `core.io`, it is available to programs that use the
standard library (run with `CRANELISP_LIB=stdlib`):

```clojure
(import [core.io [timeout]])
(import [primitives [Pure bind sleep Some None]])

(defn main []
  (bind (timeout 10 (sleep 1000))     ;; 10ms deadline vs 1000ms of work
    (fn [r]
      (match r
        [(Some v) (Pure 1)            ;; work won
         None     (Pure 0)]))))       ;; deadline fired -> None
```

```
CRANELISP_LIB=stdlib cranelisp --run timeout.cl   # exit code 0 — the timer fired
```

If the work wins instead — `(timeout 1000 (Pure 42))` — the result is `(Some 42)`.

#### Free-standing code writes the pattern inline

`timeout` requires the standard library. **Free-standing code** (anything not using
stdlib — including the `examples/` and `tests/`) writes the timeout *pattern* inline:
race the work against a `sleep` deadline branch, using a sentinel value to mark which
won.

```clojure
(import [primitives [Pure bind sleep race]])

(defn work     [] (bind (sleep 300) (fn [_] (Pure 7))))    ;; the real work
(defn deadline [] (bind (sleep 50)  (fn [_] (Pure 99))))   ;; 99 = "timed out"

(defn main []
  (bind (race (work) (deadline))
    (fn [r] (Pure r))))                                    ;; -> 99 (deadline won)
```

```
cranelisp --run timeout-inline.cl   # exit code 99 — work overran, was cancelled
```

The worked teaching example is
[`examples/32-concurrency-combinators.cl`](../../examples/32-concurrency-combinators.cl).

---

## Structured cancellation — a consequence, not a primitive

There is **no `cancel` primitive**. Cancellation happens *structurally*, as the
consequence of three situations:

- **losing a `race` / `select`** — the slower branches are cancelled when the winner
  completes;
- **a `timeout` firing** — the bounded work is cancelled when the deadline wins;
- **a scope exiting** — outstanding work owned by a scope is cancelled when the scope
  ends.

A cancelled computation's effects **do not complete**: its future is dropped, its
remaining side effects never run, and its resources are released. This is
observable. The following stdio program races a slow `print "LATE"` against a 10ms
deadline; only `EARLY` is printed — `LATE` never happens because the slow branch is
cancelled:

```clojure
(platform stdio)
(import [core.io [timeout >>]])
(import [primitives [Pure bind sleep Some None]])
(import [platform.stdio [print]])

(defn slow-print []
  (>> (sleep 1000) (print "LATE")))     ;; would print after 1s

(defn main []
  (>> (print "EARLY")
      (bind (timeout 10 (slow-print))   ;; cancelled after 10ms
        (fn [_] (Pure 0)))))
```

```
CRANELISP_LIB=stdlib CRANELISP_PLATFORM_PATH=target/debug cranelisp --run cancel.cl
EARLY
```

`LATE` is absent — the cancelled loser's side effect genuinely did not run. The
normative cancellation semantics are
[`spec/10-io.md §10.12.9`](../../spec/10-io.md).

### Reference patterns

These compositions are the vocabulary for an uncooperative I/O boundary (work that
overruns, callers that vanish, load that floods):

- **Per-request timeout** — `(timeout d work)` bounds each request's handler in time
  and cancels it cleanly when it overruns.
- **Cancel-on-disconnect** — `race` the handler against a disconnect-watch branch; if
  the client vanishes first, the handler is cancelled.
- **Graceful shutdown** — stop accepting new work and let outstanding work drain (or
  cancel it on a deadline) when a scope exits.

The reference patterns are specified in
[`spec/10-io.md §10.12.10`](../../spec/10-io.md).

---

## Honest scope — current limitations

Cranelisp's concurrency works as described above, but there are real edges. The docs
state them plainly rather than imply production-unattended readiness.

- **`timeout` is stdlib, not a primitive.** It is available to programs run with
  `CRANELISP_LIB=stdlib` (the exemplar and production binaries). Free-standing code
  writes the `race`/`sleep` pattern inline (above).
- **An idle server stays up but does not self-exit.** A long-running `accept` loop
  with no traffic now stays alive indefinitely (the earlier ~30-second no-progress
  watchdog was retired). The flip side: a foreground `cranelisp --run` of a server
  will **not exit on its own** — it is waiting for the next connection. Run it under
  a process manager, or drive it from a test harness that kills it on completion (as
  `tests/exemplar_web.rs` does), rather than expecting it to return.

### Known rough edges

A few shapes currently miscompile or are unsound — avoid them, and use the supported
shape instead. The snippets above all sidestep these on purpose:

- **`race` with an *inline* `bind`-lambda argument miscompiles** under the default
  lenient evaluation. Use **named-helper branches** (as every snippet above does)
  rather than passing an inline `(bind …)` expression directly to `race`. `select` is
  unaffected.

---

## See also

- [`writing-platforms.md`](writing-platforms.md) — the companion guide for authoring
  a platform DLL: poll-shape leaves, the poll-in / wake-out reactor boundary, the
  connection/handle model. Everything the runtime does *behind* this page.
- [`examples/32-concurrency-combinators.cl`](../../examples/32-concurrency-combinators.cl)
  — the free-standing teaching example for `sleep` / `race` / `select` + the inline
  timeout pattern.
- [`exemplar/main.cl`](../../exemplar/main.cl) — the showcase web server with no
  `spawn` (the inferred fan-out).
- [Automatic parallelism](../getting-started.md#automatic-parallelism) and
  [parallel collections](parallel-collections.md) — the pure-compute sibling of the
  inferred half.
- [`spec/10-io.md §10.12`](../../spec/10-io.md) — the normative IO concurrency model:
  combinators (§10.12.8), structured cancellation (§10.12.9), reference patterns
  (§10.12.10).
- [`design/arch/effect-concurrency.md`](../../design/arch/effect-concurrency.md) — the
  ratified architecture: the two-peers thesis, the inferred-launch eligibility
  predicate (§4.1), the trampoline.
