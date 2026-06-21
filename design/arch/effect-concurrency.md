# Effect concurrency — thin platforms, scheduler-trampoline, inferred concurrency

**Status: TARGET STATE / THEORY.** Ratified in an `/arch` design conversation
(S87, 2026-06-21). **Pre-implementation.** This document captures the target
*language-level* concurrency architecture so the conversation survives. It describes
a trampoline ("the magic trampoline") more capable than the as-built one; §8 states
the honest as-is/target gap.

**Sequencing (user direction, 2026-06-21).** This is scheduled as its **own track**,
**after** the embedded-REPL-agent track (`design/arch/repl-embedded-agent.md`) and
**before** Phase H (the `--release` efficiency tier). The placement is filed to
`/sprint` as FIXME 0427. The concurrency→`--release` edge is a **dependency**, not a
priority: Phase H's non-atomic RC, escape→stack/region, Perceus reuse and RC-fusion
are sound only relative to a settled concurrency model (it determines which values
cross threads — atomic RC exists *because* of lenient/Par parallelism). The
"after agentic-repl" edge is a priority choice (the two are independent). See FIXME
0427 for the full rationale.

**Scope — which concurrency.** Cranelisp has two concurrency axes that share almost
no mechanism. This document is about the **language-level** axis: how a *program*
gets concurrency over effects. The **compiler-internal** axis (how the compiler
schedules its own typecheck/codegen work — scheduler, worker pool, `SharedState`)
is a different subject, inventoried in `design/int/concurrency-architecture.md` and
tracked as debt by FIXME 0425. Do not conflate them.

---

## 1. Thesis — state is the problem; confine it to one interpreter

In a pure functional language a value has no state, so **concurrency over values is
free** — independent computations parallelize with no coordination, and the result
is identical to sequential evaluation (the §12.4.3 observational-equivalence
promise holds by construction). The moment *state* enters, concurrency stops being
free, because state is exactly "a thing whose observed value depends on *when* you
look."

The organizing principle:

> **All state-mutation in a pure language must funnel through a single serializing
> interpreter. Concurrency is permitted only over the state-free part, or across
> provably-disjoint pieces of state.**

`IO a` is morally `World → (a, World)`; `bind!` threads `World` sequentially. The
**trampoline is that single interpreter** — it folds effects into one coherent
world-state in a defined order. Everything below is a corollary.

## 2. The Roc anti-pattern (what we are deliberately NOT building)

There is a tempting wrong turn: let a platform own its event loop and call back
into pure handlers (the exemplar's "Model B" `serve port handler`; FIXME 0407).
Down that road, a platform author must understand cranelisp's RC discipline,
error-slot ferry, and threading contract to write a *correct* platform — so the
interesting engineering **migrates out of cranelisp into every platform**. The
language degenerates into "a DSL on top of a platform written in a real language"
(the critique levelled at Roc). N platform authors each re-solve concurrency,
independently, badly.

We reject that equilibrium. **The complexity budget for concurrency is spent once,
in the language runtime, not repeatedly in every platform.** That is the defining
bet of "cranelisp is a programming language, not a DSL."

## 3. The model — thin platforms, smart trampoline, state as a pure fold

Three commitments, each the inverse of Model B:

- **Thin platforms.** A platform is a *stateless vocabulary of effects* —
  `accept`, `query`, `send` — each a plain, possibly-blocking function that does
  one thing and returns a result. It knows **nothing** about concurrency, fibers,
  scheduling, or application state. It MAY be naive synchronous blocking code; the
  trampoline supplies the concurrency by running blocking effects on worker threads
  and suspending the calling fiber. A platform author never learns an async concept.

- **State as the pure fold.** Application state never lives in a platform. It is the
  accumulator threaded through pure continuations — the trampoline's "fold effects
  into a consistent state." OS/library handles (a socket fd, a SQL connection) are
  **opaque tokens** the pure world holds and passes back; the platform performs an
  operation *on* a token but does not own it as mutable state.

- **Smart trampoline (a concurrent effect scheduler).** Concurrency lives in the
  interpreter. The trampoline is promoted from a per-`main` linear driver with
  lexical `Par` blocks into a **fiber/task runtime**: each in-flight computation is
  a suspended pure continuation; the scheduler drives many of them, dispatches their
  effects to thin platforms, and resumes continuations as results arrive.

## 4. How concurrency is *extracted* (no explicit primitives on the throughput path)

The pure program emits effects ordered **only by data dependencies**. The trampoline
extracts concurrency from three facts:

1. **Dataflow independence** — two effects with no shared free variable may run
   concurrently (the existing auto-IO independence analysis, §10.12.1).
2. **Token disjointness** — effects on different resource tokens run concurrently;
   effects sharing a token serialize (the existing `ResourceSerial` mechanism,
   §10.12.4). An accept loop yields a stream of *distinct* connection tokens, so
   different requests are concurrent **by construction**, with no annotation in the
   handler.
3. **Pool cardinality** — a resource exposes N tokens; the (N+1)th effect parks
   until one frees. **A connection pool bound is simply the token count** — there is
   no pool code in the platform.

Two consequences make the classic server fall out with **no `spawn`**:

- **Launch-and-continue is inferable.** In `(do (handle-conn conn) (serve listener))`,
  `handle-conn` returns `IO Unit` — its *result is unused* and its tokens are
  disjoint from the continuation. An effect whose result is discarded and whose
  tokens do not conflict with what follows may be launched and **not joined**. The
  accept loop fans out automatically; the recursion is TCO'd (§12.5).
- **Backpressure is a scheduler policy, not a language feature.** "Saturate but do
  not oversaturate under load" depends on dynamic resource availability — exactly the
  state the pure world correctly refuses to hold. But the trampoline *is* the
  scheduler and holds that state: it simply does not dispatch the next `accept` until
  a worker / token is free, parameterized by platform-declared cardinalities and a
  global budget. The pure loop emits `accept` eagerly and unboundedly; the scheduler
  throttles execution.

**Core saturation with responses *and* DB calls.** Blocking effects (the DB call)
run on a blocking worker pool — many in flight, consuming no core while waiting —
while pure rendering fills the CPU cores via lenient-eval sparks. The
blocking-vs-CPU split is itself inferable (effects are potentially-blocking; pure
values are CPU). Balancing the two pools to fill the cores is the scheduler's job,
given the metadata — and none of it touches the pure source.

## 5. The concurrency descriptor (a finite generalization of scheduling classes)

Today a platform declares per-effect `Sequential` / `Commutative` / `ResourceSerial`
+ a resource token (§10.12.2/§10.12.4). Generalize that into a per-effect
**concurrency descriptor**:

- **token** — what the effect conflicts on (0 = unrestricted, as today).
- **cardinality** — how many tokens exist for this resource = the safe parallelism
  / pool size. (New; today cardinality is implicitly 1 per distinct token value.)
- **global budget** — optional cap on total in-flight effects of this kind
  (the backpressure threshold). (New.)
- **blocking?** — whether the effect blocks an OS thread (selects the worker pool).
  Defaults to "yes" for effects; inferable.

This is the platform's entire concurrency contract. It is declarative, finite, and
evolutionary from the auto-IO machinery — not a new subsystem. It is also a **trust
boundary**, continuous with the existing one: the compiler does not verify that an
effect declared `Commutative` truly has no shared state, exactly as it does not
verify a `ResourceSerial` token is correct. The platform author asserts safety; the
language takes it on faith (the platform's `unsafe`).

## 6. The combinator boundary — the one thing dataflow cannot express

The precise statement that answers "why would the pure side ever need explicit
concurrency primitives?":

> **Dataflow dependency + token/cardinality metadata expresses every concurrency
> pattern where program control flow does NOT branch on completion *timing*.
> Explicit combinators are needed exactly and only where it does.**

Dataflow can say "B's *value* depends on A's value." It can never say "B's
*existence* depends on A *finishing first*." Therefore:

- **`race` / `select` / `timeout` / `cancel`** are irreducible — they branch on
  *when* something completes and cancel the loser. Cancellation is removing a node
  from the graph based on runtime timing; there is no dataflow encoding of it.
- A server's **throughput path never branches on timing** (each request independent;
  just run them all) → fully inferable, zero primitives.
- A server's **robustness path** (request timeouts, cancel-on-client-disconnect,
  graceful shutdown) *does* branch on timing → this is the only place explicit
  surface becomes unavoidable.

So the architecture is **one inferred contract** (effects ordered by data deps +
platform-declared safety; scheduler extracts max concurrency and applies
backpressure) **plus a separable, opt-in cancellation/choice layer** deferrable
until someone needs latency SLOs. When that layer arrives, the combinators are
**in-language IO primitives interpreted by the trampoline** — *not* platform
capabilities — so even the explicit surface keeps complexity in cranelisp and
platforms thin. (This is the algebraic-effects / effect-handler shape: direct-style
code; concurrency as a property of how the interpreter runs the effect tree.)

## 7. The new obligation this creates — supervisor error semantics

Fire-and-forget has a cost that must be designed, not discovered. **An un-joined
effect has no join point for its error to ferry to.** Structured fork-join re-raises
a worker panic at the join (the standing ferry obligation — `test-discovery.md`,
FIXME 0407 cross-ref). A launched-and-abandoned request handler that panics has
nowhere to re-raise.

So "launch-and-continue" forces the error story to grow from *join-point re-raise*
into **supervisor semantics**: a panicked handler becomes a 500 + log + drop-that-
request — **not** a silent strand, and **not** a whole-server abort. This is a
per-effect-kind *default policy* (platform- or scheduler-declared), so it still
stays out of the pure language — but it is the substantive new design work this
model introduces, and it makes the fork-join error-slot ferry contract richer rather
than optional. The ferry verification we flagged (spec §12.4.3 ¶4 MUST-propagate vs.
the as-built panic→`EVALUATING`→spin caveat) is a prerequisite to this layer.

## 8. As-is vs target (the honest gap)

**Exists today** (the building blocks): auto-IO independence analysis + `Par` nodes
(§10.12); resource tokens (§10.12.4); IVars / completion cells
(`crates/cranelisp-runtime/src/ivar.rs`); a rayon worker pool + `Par` dispatch
(`crates/cranelisp-intrinsics/src/io.rs`); `bind!`-compiled continuations; lenient
sparks over pure values (§12.4.3).

**Needed for the target** (not built): unstructured **launch-and-continue** (today's
`Par` is strictly lexical fork-join); a **runtime token-cardinality pool scheduler**
(today cardinality is implicitly 1 per token value); **backpressure** as a scheduler
policy; the **blocking/CPU two-pool split** with inferred routing; **supervisor error
semantics** (§7); and eventually the **cancellation/choice combinator layer** (§6).
A general parallel `map` / sparked apply-arguments (FIXME 0424) is a step on the
inferred-concurrency path. The lenient-eval showcase (FIXME 0408) exercises the
pure-value half.

A **concurrency-scheduler sequence diagram** under `design/arch/sequences/` is
warranted when this moves from theory to design — flagged sequence-diagram-pending;
not drawn while pre-implementation.

## 9. Manifestation sites when implemented

This is a target; nothing in the canonical set changes yet. When built, the
substance manifests at:

- **`bounded-contexts.md` §3 (backend)** — the trampoline-as-scheduler; launch-and-
  continue codegen; two-pool routing.
- **`bounded-contexts.md` §5 (platform)** — the concurrency descriptor (token +
  cardinality + budget + blocking) as the platform's declared contract; the
  "platforms stay thin / own no state" statement.
- **`bounded-contexts.md` §6 (int)** — the scheduler policy: backpressure,
  supervisor error semantics, pool sizing.
- **spec cascade** — §10.12 (descriptor generalization; launch-and-continue
  semantics) and §12 (supervisor error model; the eventual combinator layer), filed
  `target: /spec`.
- **A new principle** is a candidate: *"confine mutable-state concurrency to the
  interpreter; platforms are thin stateless effect vocabularies"* — if/when this is
  ratified as binding, file per `design/arch/principles/CLAUDE.md`.

## 10. Code sketch — the pure side of a web/DB API (assuming the magic trampoline)

Indicative cranelisp; the point is the **dataflow shape and where concurrency
emerges**, not exact record sugar. The programmer writes **zero concurrency
primitives**. Every comment marked `⟂` notes a place the trampoline extracts
concurrency on its own.

```clojure
;; ── Thin platforms (declared, not shown) ───────────────────────────────────
;; web : listen, accept, read-request, respond
;;   accept  — ResourceSerial on the listener token; yields a FRESH conn token
;;   respond — ResourceSerial on the *connection* token
;; sql : query, execute
;;   both    — ResourceSerial on a connection-pool token of cardinality N
;;             (pool size IS the token count; the platform has no pool code)
;; Neither platform knows anything about concurrency. The descriptors above
;; (§5) are all the metadata the scheduler needs.

(deftype Method [GET POST PUT DELETE])
(deftype Req  [Req Method String String])   ; (Req method path body)
(deftype Resp [Resp Int String])            ; (Resp status body)

;; ── Per-request handler: data in, effects-described out ─────────────────────
(defn handle [req]
  (match req
    (Req GET  path _)    (handle-get path)
    (Req POST _    body) (handle-post body)
    _                    (pure (Resp 405 "method not allowed"))))

(defn handle-get [path]
  (let [id (path-param path "id")]
    ;; ⟂ `user` and `orders` are data-independent and draw two DIFFERENT pool
    ;;   tokens (cardinality N ≥ 2) → the two queries run concurrently.
    ;;   No annotation; the scheduler reads it off the dataflow + tokens.
    (bind! [user   (query "SELECT * FROM users  WHERE id = ?" id)
            orders (query "SELECT * FROM orders WHERE user-id = ?" id)]
      ;; ⟂ pure CPU render → eligible for lenient sparks, fills cores.
      (pure (render-user-page user orders)))))

(defn handle-post [body]
  (match (parse-user body)                     ; pure validation → Result
    (Err msg) (pure (Resp 400 msg))
    (Ok  u)   (bind! [_ (execute "INSERT INTO users (name) VALUES (?)"
                                 (user-name u))]
                (pure (Resp 201 "created")))))

;; ── Accept loop: TCO self-recursion; the trampoline fans out ────────────────
(defn handle-conn [conn]
  (bind! [req  (read-request conn)
          resp (handle req)]
    (respond conn resp)))                       ; ResourceSerial on conn token

(defn serve [listener]
  (bind! [conn (accept listener)]               ; one accept at a time (serial)
    ;; ⟂ (handle-conn conn) returns IO Unit, result unused, tokens disjoint from
    ;;   the next accept → LAUNCH-AND-CONTINUE. The loop keeps accepting; the
    ;;   scheduler throttles in-flight handlers by free-token / free-worker
    ;;   availability (backpressure). No `spawn`.
    (do (handle-conn conn)
        (serve listener))))                     ; tail call → next accept

(defn main []
  (bind! [listener (listen 8080)]
    (serve listener)))
```

What the programmer expressed: a straight-line request/response and an accept loop.
What the runtime does for free, from dataflow + the platforms' concurrency
descriptors: runs the two queries in parallel, sparks the pure render across cores,
overlaps many requests, bounds the DB pool at N, and applies backpressure on accept
under load. The robustness path (a per-request timeout, cancel-on-disconnect) is the
*only* thing that would later require an explicit `timeout`/`race` combinator (§6) —
and even that is an in-language primitive the trampoline interprets, never a platform
capability.
