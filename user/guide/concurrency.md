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
      (match conn
        [(Connection token capacity fd)
           (do
             ;; the per-connection handler: read → (optional delay) → send.
             ;; Its result is DISCARDED (the `do`), and its work touches only
             ;; this fresh connection — so the runtime LAUNCHES it and does not
             ;; wait for it to finish.
             (bind (read-conn token capacity fd)
               (fn [req]
                 (bind (sleep (slow-ms req))
                   (fn [_] (send-conn token capacity fd (safe-handle req))))))
             ;; the continuation: accept the next connection right away
             (serve-loop listener))]))))
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

### Honest scope: per-resource capacity

Independent IO effects overlap — **but effects that share one resource are bounded
by that resource's capacity, a ceiling the platform declares, not the program.** The
canonical case is a database connection pool of *N* connections: many `query`
effects can be in flight, but the sum in flight is capped at *N*, and the (N+1)th
**parks** until one frees (observable as wall-clock latency). Distinct resources
(distinct connection tokens) are independent and overlap freely; capacity-1 resources
serialize in source order.

You never choose *N* and never write pool code — the platform author declares the
capacity, and the runtime enforces it. The normative rule is
[`spec/10-io.md §10.12.4.1`](../../spec/10-io.md) (Resource Capacity — Token Pools).

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
| `select` | `(Fn [(Vec (IO a))] (IO a))` | N-ary race over a `Vec`; first to finish wins, all losers cancelled. |
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
remaining side effects never run, and its resources (permits, reactor interest) are
released. This is observable. The following stdio program races a slow `print "LATE"`
against a 10ms deadline; only `EARLY` is printed — `LATE` never happens because the
slow branch is cancelled:

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
- **A long-running server cannot yet idle unattended past ~30s with no traffic.** The
  reactor watchdog currently aborts a parked `accept` loop after about 30 seconds of
  no progress. A server under continuous traffic is fine; an idle server waiting for
  its first connection for more than 30s is not yet supported. (Tracked as a known
  limitation; a no-progress watchdog / server-mode opt-out is the fix.)

### Known rough edges

A few shapes currently miscompile or are unsound — avoid them, and use the supported
shape instead. The snippets above all sidestep these on purpose:

- **A bare ADT constructor used as a first-class function value crashes.** Wrap it in
  a lambda: write `(fn [x] (Some x))`, not a bare `Some`, when passing a constructor
  to a higher-order function. (This is why `timeout`'s definition wraps `Some`.)
- **`(select [])` over an empty Vec is unsound** — `select` is documented to never
  complete on an empty Vec; a program must not rely on it. Always give `select` a
  non-empty Vec.
- **`race` with an *inline* `bind`-lambda argument miscompiles** under the default
  lenient evaluation. Use **named-helper branches** (as every snippet above does)
  rather than passing an inline `(bind …)` expression directly to `race`. `select` is
  unaffected.

---

## See also

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
  (§10.12.10), resource capacity (§10.12.4.1).
- [`design/arch/effect-concurrency.md`](../../design/arch/effect-concurrency.md) — the
  ratified architecture: the two-peers thesis, the inferred-launch eligibility
  predicate (§4.1), the trampoline.
