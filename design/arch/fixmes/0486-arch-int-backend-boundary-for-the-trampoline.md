---
number: 0486
target: /arch
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: design/arch/effect-concurrency.md §6 (async substrate / reified-IO-as-data), design/arch/bounded-contexts.md §3 (backend) + §4b (intrinsics) + §6 (int), design/backend/io-trampoline.md, design/int/reactor.md §7, crates/cranelisp-intrinsics/src/{io.rs (consume_io_tree/feed_continuation), reactor.rs}, tests/launch_grid_corrupt.rs
status: open
---

# Is "runtime" underspecified? — the /int ↔ intrinsics ↔ /backend boundary for the trampoline (and does intrinsics belong to /int at all?)

**For /arch review NEXT sprint** (not S97 — S97 ships the tactical fix; this is the boundary question the fix exposed). User-raised (S97, 2026-07-01) after a launched-effect use-after-free (bug #2) fell in the /int↔/backend crack.

## The core question — "runtime" is doing too much work

The word **"runtime"** conflates two things that should be separated:
- **Orchestration** — driving the REPL + the compiler pipeline, CLI, prelude, session lifecycle. This is genuinely **`/int`**.
- **The IO/RC runtime *library*** — the trampoline, reactor, `consume_io_tree`, `alloc_with_rc`. This is a **callee**: the thing `/backend` *emits calls into* (the analog of a language's GC / async executor — a library the compiled program invokes, not the orchestrator).

Today these are fused: `/int` owns `src/` AND is treated as owner of `cranelisp-intrinsics`, so the reactor sits "as an `/int` thing" next to the REPL. **User's thesis:** how IO is managed is an implementation detail that should be **encapsulated in `cranelisp-intrinsics`, which `/backend` emits calls to — NOT called directly from `/int`**; the only legitimate `/int`↔intrinsics contact is `/int` as a **client** (constructs the `HostCtx`, invokes `block_on_reactor` for `--run`/REPL). The tramp/reactor internals (lifetime discipline, poll deferral, `consume_io_tree`) are runtime-library guts `/int` should neither own nor need to understand. **So the boundary question is really two:**
1. Is `cranelisp-intrinsics` an **`/int` concern at all**, or is it a `/backend`-emitted (or standalone) runtime library with `/int` reduced to pure orchestration + a thin client seam?
2. Given (1): where does the trampoline's **lifetime guarantee** live (the sub-question bug #2 exposed, below)?

Current split (the thing under review): the **executor** (reactor: mio `Poll`, reactor thread, fd/timer registration, permit pools, launch supervision, `Par`/`select` joins) AND the **IO-tree interpreter** (`consume_io_tree`/`feed_continuation`) both live in `cranelisp-intrinsics`, owned/edited by `/int`; `/backend` emits the reified IO *data* + the RC/drop codegen; the runtime *interprets* it.

**Diagnostic the user proposed (worth capturing as evidence):** watch *how much `/int` has to learn about IO/tramp/reactor internals* to fix a tramp bug. The S97 bug-#2 fix is the live test — a skill labelled `/int` fixing a *reactor UAF* down in `reactor.rs`/`io.rs`. If the fix is mostly reactor/tramp internals (not orchestration), that ratio is direct evidence the encapsulation is wrong and intrinsics is mis-owned. Record the /int fix's internals-vs-orchestration split when it lands.

## Why the question arose — a seam bug that escaped /backend (bug #2)

S97 bug #2: a launched per-connection handler whose terminal `send-conn` (a Consume leaf marshaling a `Response` ADT to the web DLL) is **reactor-polled AFTER the launched frame is torn down**; the frame's scope-cleanup frees the baked `Response` buffer before the deferred send reads it; allocation churn recycles the freed buffer → heap-metadata overrun → SIGABRT. Deterministic repro `tests/launch_grid_corrupt.rs` (+ the smaller `redA` shape: launch + send-conn + churned string body, no grids/vec).

Why it escaped `/backend`: the emitted RC/drop discipline is **locally correct for a synchronous lifetime model** (args live until the effect runs, drop at scope exit) — and `/backend`'s tests (CLIF, RC counts) verify exactly that. The bug exists only because the **runtime defers** the poll across a frame teardown — a runtime-scheduling fact `/backend`'s model never captures. **The arg-lifetime-across-suspension contract was never written down at the boundary.** Correct-in-isolation codegen met a runtime deferral its model didn't include. (First triage even mis-attributed it to `/backend` borrowed-Var RC; a 6-point reduction refuted that — RC trace is balanced, it's a UAF, not a miscount.)

## What is DIRECTING intrinsics/reactor to /int? (evidence — the canonical ownership already disagrees)

The mis-ownership is **doc placement + a host-client blur, not a considered decision** — and it contradicts the canonical BC statement:
- **BC already says backend-emitted, NOT /int.** `bounded-contexts.md §4b`: *"Runtime helpers (intrinsics — **backend declares them as imports**)"*; §4b: *"primitive emission goes through `cranelisp-primitives` + `cranelisp-intrinsics` **directly**"* (backend has no trait knowledge); §4b invariant 2: *"backend reads the runtime heap layout through intrinsics' named extern functions … **intrinsics owns**."* The canonical ownership matches the user's model.
- **The crate-surface mapping is STALE, not a directive.** `.claude/commands/sprint.md` + `METHOD.md` still name the pre-split **`cranelisp-runtime`** as a surface *"(paired with backend)"*; the S73 Decision-43 split into `primitives` + `intrinsics` was never re-mapped. No live assignment sends intrinsics to /int.
- **The operative directive is DOC PLACEMENT.** The reactor/trampoline/IO-runtime design docs live under **`design/int/`** (`reactor.md`, `io-integration.md`, `bind-chain-analysis.md`) — so /sprint dispatched `/int` for the S97 reactor UAF by following `design/int/reactor.md §7`. That placement contradicts BC §4b.
- **Why they landed under /int (the blur):** (1) `/int` is the *host* — constructs `HostCtx`, drives `block_on_reactor` for `--run`/REPL (a legitimate client seam) — which blurred into "int owns the reactor"; `reactor.md` frames it *"int-owns-policy / intrinsics-hosts-mechanism."* (2) `design/int/` legitimately holds the **compiler-internal scheduler** (`concurrency-architecture.md` — the dependency-service orchestrating the compile pipeline, genuinely /int), and the **language-level IO runtime** reactor got filed right next to it — two different "concurrency" concerns, one directory. (3) A genuinely-int-owned handful exists (`int_intrinsics()`: `discover-tests`/`run-test`/trace externs) but those **physically live in `src/`**, and `INTRINSICS_TABLE` is *"the `cranelisp-intrinsics` crate's catalog only"* — so even that distinction supports backend-runtime ownership of the crate.

**Candidate resolution (concrete):** relocate the IO-runtime design out of `design/int/` (→ `design/backend/` or a new `design/runtime/`); affirm `cranelisp-intrinsics` (+ `primitives`) as the backend-emitted runtime library (per BC §4b); reduce `/int` to the thin **host-client seam** (construct `HostCtx`, invoke `block_on_reactor`, wire the pipeline/REPL) with nothing reaching into reactor/`consume_io_tree` internals; keep the genuinely-int externs (`int_intrinsics()` in `src/`) as the only int-side runtime surface; refresh the stale `/sprint`/`METHOD` crate-surface list to the post-D43 split.

## The architectural fork (what /arch should weigh)

**The reified-IO-as-data trade.** `effect-concurrency.md §6` deliberately chose **reified-IO-as-data + one generic Rust `async fn` interpreter** *over* hand-rolled fibers / per-program state machines, to keep the trampoline a simple awaiting Rust function. The trade that made: **lifetime-across-suspension became a runtime discipline instead of a compile-time guarantee.** Bug #2 is the bill for that trade.

**The Rust-async contrast.** A compiler-generated state machine holds captured locals across every `.await` **by construction** — "the frame freed the value before the await resumed" is structurally impossible. If `/backend` co-generated the IO execution that way (a per-program state machine owning each suspended effect's args across its suspend points), this bug *class* would be a `/backend` concern, caught by backend's own lifetime discipline. Caveat: even then the split doesn't fully collapse — the **executor** (reactor owning OS handles + DLL calls) is always a runtime library; what *could* move to `/backend` is the **interpreter/lifetime half** (the state-machine transform). So the reachable target is "the *lifetime* part of the tramp is a backend-guaranteed detail," not "tramp entirely backend."

## Proposed resolution (two levels — /arch decides scope)

1. **Minimal (pin the contract):** write the deferred/launched-effect **arg-lifetime contract** as an explicit `/backend`↔runtime interface — "a launched or reactor-deferred effect's baked arguments are live until the reactor resolves it; keep-alive is [emitted / runtime-owned]." Whichever side owns keep-alive, state it so the next deferred-effect codegen can't re-trip it. This is another instance of [[0483]] (make the functions between actors explicit — the boundary was implicit).
2. **Bigger (revisit the split):** evaluate whether the interpreter/lifetime half of the trampoline should move from a generic runtime interpreter (`consume_io_tree`) toward `/backend`-generated per-program execution (Rust-async-style), so lifetime-across-suspension is a compile-time guarantee. This reopens the `effect-concurrency.md §6` reified-data choice — only worth it if this bug class recurs; named here so the decision is deliberate, not defaulted.

## The concrete instance to fix WITH this boundary — bug #2 (deferred here, S97)

Bug #2 (the launched-send-terminal arg-lifetime UAF) **is** this boundary defect in the flesh: there is no owned contract for "a launched/reactor-deferred effect's baked args stay alive until the reactor resolves it." S97 chased it through repro→/backend-gate-refute→/int, and the /int fix stalled mid-edit (a `HashMap` keep-alive registry in `alloc.rs`) and was reverted for consolidation. **Its fix is deferred to be done AS PART OF resolving this boundary** — once, by the right owner, not patched by whichever skill happens to be pointed at the reactor. The durable record already exists: **deterministic guard `tests/launch_grid_corrupt.rs::launched_strand_grid_get_assoc_does_not_corrupt_heap_neg`** (RED, committed `3b9364d`), the quarantined `exemplar_web`, and the characterization above. So the boundary ruling here should also **specify + land the arg-lifetime fix** (whoever owns keep-alive) and flip that guard green + un-quarantine `exemplar_web`.

## Operational implication / Context

- S97 does NOT ship the bug-#2 fix — it ships the deterministic guard + this boundary FIXME. The fix lands with the boundary resolution next sprint.
- Manifestation once ruled: `bounded-contexts.md §3/§4b/§6` (the backend↔intrinsics↔int contract), `io-trampoline.md` / `reactor.md` (the lifetime contract), and — if the bigger option is taken — `effect-concurrency.md §6`.
