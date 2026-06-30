# Sprint 96 — Effect-concurrency: platform-model completion + the server demo — Failing-test PLAN

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests land in
**Phase 5 Stage 1** (QA-first, per chunk, before that chunk's per-crate D/D/R cycle). This
document enumerates the row-by-row test surface so `/sprint` + the user can review coverage
before implementation waves are allocated.

> **CHUNK-DELIMITED.** S96 is driven **chunk-by-chunk** (`SPRINT.md` Phase-2 partition:
> A substrate → B fan-out/control → C combinators). **This plan currently covers CHUNK A
> ONLY** (items 1–3: web+stdio v7 rewrites, the `poll_support` ergonomics suite, poll-shape
> live capacity + acquire-around-poll). The Chunk B rows (launch-and-continue + supervisor +
> backpressure / the "server with no `spawn`") and Chunk C rows (`race`/`select`/`timeout` +
> structured cancellation) are **out of this chunk** — they are sketched terse in §8
> "Out-of-chunk (B / C) — NOT planned here" and get full row tables when those chunks open.
> The A→C **RAII-Permit-release-on-drop** contract is *built* in Chunk A (§2 below) and
> *exercised* in Chunk C — §2B is the load-bearing row that contract leans on.

---

## Scope source + contracts of record (Chunk A)

**Scope source:** `sprints/SPRINT.md` S96 items 1–3 + the Phase-2 **Architecture review**
(the **Chunk A** partition entry's **Witnessable** bullet) + gate rulings **(a)**
acquire-around-poll (the RAII `Permit` drop-guard, non-re-entrant admission) and **(c)**
poll_support macro convergence (the `_neg` frozen-edge guard is the enforcement).

**Contract of record:**
- `design/arch/effect-concurrency.md` **§8** (resource-token model under async) / **§8.1**
  (the `(token, capacity)`-dynamic-on-the-node carrier + first-writer-wins reconciliation) /
  **§8.2** (within-token source ordering) / **§7** (two-pool model + the permanent wakeable
  bridge) / §5 (FIXME-0442 ruling — `min(capacity, degree)`, Chunk B).
- `design/int/reactor.md` **§2.8** (the token-capacity `Semaphore` pool — carrier-agnostic;
  S95 proved it on the BLOCKING carrier, **Chunk A lights up the POLL carrier**) / **§2.9**
  (testability seams — the AcquirePermit / Permit-on-drop / parking seams) / **§5** (the S96
  acquire-around-poll lifecycle: the permit wraps the `EffectPoll` establish→ready arc).
- `design/backend/io-trampoline.md` §13 (the poll-node `(token, capacity)` slot reservation
  baked at sentinel in S95 — Chunk A wires the live read; the in-process backend↔intrinsics
  node convention; **0461 platform-doc drift drains here**).

**Spec of record:** **NONE NEW for Chunk A.** The substrate is language-invisible
(`spec/10-io.md` §10.12.4.1 "Resource Capacity — Token Pools" already normative from S95 —
the capacity-N pool / (N+1)th-parks observable applies verbatim to the poll carrier; FIXME
0447's S94 re-affirmation: the poll carrier is an interior mechanism, not a source surface).
The §10.12.4.1 anchor is reused. (Chunk B/C carry the §10.12/§12 control-layer spec via 0447.)

**Public-api / ABI of record:** **ZERO new edges, NO ABI bump, v7 stays UNFROZEN** (Phase-2
public-api ruling). Poll-shape live capacity rides the **node `(token, capacity)` slots
reserved at sentinel in S95** (in-process backend↔intrinsics convention — no new public
constructor on the default edge). poll_support is `concurrency`-gated; the macro convergence
names only already-gated types. The `_neg`/frozen-edge guard stays green. web/stdio are
**in-tree** (rebuilt with the compiler) so the reserve-now-no-`ABI_VERSION`-bump latitude
persists.

**Test-leaf fixture (Chunk A's Gap G1 — see §7):** the S95 capacity leaf (`pool-demo`) was
**BLOCKING**; Chunk A needs the **poll-shape analogue** — a poll-carrier capacity leaf
(intended `poll-pool` platform, poll-shape effects declaring `(token, capacity)`). `/platform`
+ `/dev` author it WITH the Phase-5 /dev wave (it uses the live poll-node carrier).

## Baseline (Phase-3 sanity, `/qa` 2026-06-28 — not re-run this Phase; carried from S95 close)

The named lanes a genuine regression is measured against:

- **Default `cargo nt`** (feature-OFF, release gate) — **GREEN** (S95 close: 1700 passed /
  1 skipped / 0 failed). The skipped = the S94-demoted CPU-floor benchmark (Parallelism axis,
  unrelated).
- **`nt-reactor-e2e`** (`cargo nextest run -p cranelisp --features concurrency-runtime`) —
  **1708 / 1 skipped** at S95 close; the 5 new S95 capacity/two-pool e2e rows + the 3 named
  two-pool guards are GREEN on the **blocking** carrier.
- **`nt-concurrency-runtime`** (`-p cranelisp-intrinsics --features
  cranelisp-intrinsics/concurrency-runtime`) — **180/180**.

Source-of-truth checks done this Phase: the poll node **reserves** `(token, capacity)` slots
at the sentinel (S95 Wave-3 backend: token @abs 32 symmetric, capacity @abs 40) but the
trampoline does **NOT yet read them on the poll path** — the poll `EffectPoll` runs at
sentinel capacity 1 with no acquire-around-poll. `PollState` does **NOT** exist in
`crates/cranelisp-platform/src/concurrency.rs` (moved out of S95 to the S96 `poll_support`
suite — `/platform` deliverable). The `poll-pool` poll-shape capacity leaf does **NOT** exist
(Gap G1). The web platform (`exemplar/platforms/web/`) `accept`/`read_request` are **v6
blocking** `Sequential` effects (the Chunk A rewrite makes them poll-shape leaves). The stdio
`read_line` is **v6 blocking** (Chunk A makes it the poll candidate; `print` stays blocking).
The `declare_concurrent_platform!` ~105-line mirror still exists (gate (c) retires it via the
converged skeleton). **Any RED after this point is in-scope Chunk-A work.**

## Conventions / legend

- **Lane** (the four canonical invocations — unchanged from S95):
  - `nt` — `cargo nextest run` (feature-OFF, the release gate; the byte-identical-when-off floor).
  - `nt-concurrency` — `-p cranelisp-types -p cranelisp-platform -p cranelisp-intrinsics
    --features cranelisp-intrinsics/concurrency` (ABI-v7 layout/edge unit guards + the
    `PollState` helper + the converged-macro skeleton unit).
  - `nt-concurrency-runtime` — `-p cranelisp-intrinsics
    --features cranelisp-intrinsics/concurrency-runtime` (the reactor impl — the
    AcquirePermit-around-poll lifecycle + Permit-on-drop + the strand sink; unit-tier).
  - `nt-reactor-e2e` — `cargo nextest run -p cranelisp --features concurrency-runtime` (the
    whole `cranelisp` suite WITH the reactor on — a compiled-from-source program drives
    `cranelisp_run_io` through the real reactor + the live poll-carrier capacity pool).
- **Tier**: `unit` (`/dev`- or `/platform`-authored, `#[cfg(test)]` in the owning crate,
  named here for surface completeness + the mandatory-unit-test-per-fix discipline) or `e2e`
  (`/qa`-authored, `tests/*.rs`, subprocess via the `Cranelisp` builder, or the raw-process
  pattern for the infinite web server — see §3A). No middle tier.
- **Posture**: `RED-first` = a failing guard the fix flips green; `regression-replay` = an
  existing guard that must stay green; `stays-green` = a feature-off / frozen-edge invariant.
- **P/N**: positive (correct behaviour appears) / negative (wrong behaviour absent).

> **Why the headline splits unit ↔ e2e (the S94/S95 reconciliation, carried).** The
> acquire-around-poll lifecycle + the Permit-on-drop release live in `cranelisp-intrinsics`,
> compiled only with `concurrency-runtime` ON; the default / `--link` binary **never** enables
> it (the deployment invariant, `reactor.md` §1). The poll-carrier capacity *observable*
> (overlap / parking / wall-clock) is reachable from outside the crate ONLY through the
> `nt-reactor-e2e` binary (§1B/§1C/§1D e2e). The **drop-release** mechanism (§2) is **NOT
> subprocess-observable in Chunk A** — there is no source-level cancellation until Chunk C,
> so the future-drop path is an **intrinsics-unit** seam this chunk (it gets its e2e exercise
> in Chunk C via `timeout`/cancel-on-disconnect). The strand park/resume events are likewise
> in-memory-sink (unit), per S95.

---

## §1 — Poll-shape live capacity (the poll-carrier analogues of S95's blocking-carrier rows)

**Model (Chunk A — light up the POLL carrier).** S95 proved the `Semaphore`-per-token pool on
the **blocking** carrier and reserved the symmetric `(token, capacity)` slots on the
`IO_TAG_EFFECT_POLL` node at the sentinel (capacity 1). Chunk A makes the trampoline **read
those live slots on the poll path** and wraps the **whole `EffectPoll` establish→ready arc**
in the permit (the acquire-around-poll lifecycle, `reactor.md` §5 / §2.8) — the deferred
complexity, because the acquire must span the suspend/resume, not a one-shot dispatch.
**Capacity attaches to the resource (token): distinct token ⇒ independent; shared token ⇒
shared pool.** `token == 0` ⇒ no acquire; the (capacity+1)th poll **parks**; capacity-1
preserves source order. The pool mechanism (`RefCell<HashMap<token, TokenSlot>>`, FIFO
`AcquirePermit`, first-writer-wins) is **the S95 as-built**, reused verbatim — Chunk A changes
only *who acquires* (the poll partition now does, around the arc) and *the carrier the value
is read from* (the live poll node, not the sentinel).

Acceptance (`SPRINT.md` Chunk A Witnessable): poll `accept`/`read` leaves suspend/resume on
the reactor; poll-shape capacity-N — N overlap, the (N+1)th parks; capacity-1 poll
serial+ordered; distinct tokens independent / shared token shares the pool; first-writer-wins
+ `TokenCapacityMismatch` on the poll carrier. Spec anchor: `spec/10-io.md` §10.12.4.1
(items 1–5, reused — poll carrier is mechanism-neutral to the spec).

### 1A — the LIVE poll-node `(token, capacity)` read + acquire-around-poll wiring (unit)

The trampoline reads `(token, capacity)` off the **`IO_TAG_EFFECT_POLL`** node (S95-reserved
slots, now live) and wraps the `EffectPoll` arc in an `AcquirePermit` from the **same**
`HashMap<token, Semaphore>` the blocking carrier uses — distinct + shared semantics fall out
of the shared pool. **No new public edge, no ABI bump** (in-process node convention).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `poll_node_token_capacity_read_live_not_sentinel` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | the trampoline reads `(token, capacity)` off the **live** `IO_TAG_EFFECT_POLL` node (a poll node built declaring `T`,`N` reads back `token == T` / `capacity == N`, not the sentinel `1`); the read uses the **same** offsets the backend reserved in S95 (offset-agreement with `io-trampoline.md §13`) | P | RED-first (poll path reads sentinel today) |
| `acquire_around_poll_permit_spans_establish_to_ready` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | a poll-shape effect on `token T`, capacity N acquires its permit **before** the `EffectPoll` first establishes (registers fd/timer interest) and holds it across `Pending` → wake → `Ready` (the whole arc — `reactor.md §5`), NOT a one-shot acquire/release around a single dispatch; the permit map shows the slot held while the future is parked-on-readiness | P | RED-first (no poll-side acquire today) |
| `poll_effects_sharing_one_token_draw_from_one_pool` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | two distinct poll-shape effect kinds on the **same** token of capacity N acquire from ONE `Semaphore(N)` (the poll analogue of S95 §1F — capacity attaches to the token, not the effect kind); `token == 0` ⇒ no acquire on the poll path | P | RED-first |

### 1B — same-token capacity-N POLL: N concurrent, the (N+1)th parks (e2e)

The poll analogue of S95 §1C (blocking). `spec/10-io.md` §10.12.4.1 item 2 — the (N+1)th MUST
NOT begin until a permit frees — now demonstrated on the **reactor/poll** carrier (the permit
wraps the establish→ready arc, so the (N+1)th poll does not even *register interest* until a
permit frees).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `same_token_capacity_n_poll_admits_n_concurrent_nplus1_parks` | e2e | `nt-reactor-e2e` | (N+1) **poll-shape** effects (via the `poll-pool` leaf declaring `(token, capacity)`, each a `D`-ms armed-timer poll) on **one** token of capacity **N** (N=2, 3 effects): the first N suspend/overlap on the reactor, the (N+1)th **parks** on the token's `Semaphore` until a permit frees ⇒ wall-clock ≈ **2·D** (two waves), distinguishable from unbounded (~1·D, the slice-2 distinct-token overlap) AND from serial (~3·D); summed exit proves all ran. Two-sided window `> 1.5·D` AND `< 2.5·D` (D=60, best-of-N min — the S95 §1C jitter discipline). The (N+1)th-parks-on-the-poll-arc is the load-bearing assertion | P+N | **A1-LANDED** RED-first (`tests/concurrency_poll_capacity.rs`; RED on HEAD: `platform 'poll-pool' not found`) |

> **Pick N, D as S95 §1C.** N=2, D=60 ms: unbounded ≈ 60, capacity-2 ≈ 120, serial ≈ 180.
> Assert `> 1.5·D` (≈ 90 — the 3rd parked, did not overlap freely) AND `< 2.5·D` (≈ 150 —
> the first two DID overlap). Two-sided, wide on both edges; timing-flakiness is a banned
> disposition. Best-of-N min (contention can only slow, never speed, the true wall-clock).

### 1C — same-token capacity-1 POLL: serial AND source-ordered (e2e)

The poll analogue of S95 §1D. §10.12.4.1 item 3 / §8.2 — capacity 1 on the poll carrier is
exclusion *and* source order. The ordering half is the negative face: a bare `Semaphore(1)`
gives exclusion but not order; the poll `join_all` first-poll-in-source-order + the
acquire-as-first-action (`reactor.md §2.8`) is what carries order.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `same_token_capacity_1_poll_serial_and_source_ordered` | e2e | `nt-reactor-e2e` | three **poll-shape** effects on **one** token of capacity **1**, each delay D, serialise (wall-clock ≈ 3·D, `> 2.5·D`, not overlapped) **AND** complete in **source order** (observable via the leaf's ordered stdout tags `a`<`b`<`c`, or an order-encoding result) — proving exclusion did not reorder on the poll arc | P+N | **A1-LANDED** RED-first (`tests/concurrency_poll_capacity.rs`) |

### 1D — distinct-token POLL independent vs shared-token POLL shares the pool (e2e)

The poll-carrier sharpening of S95 §1B (distinct-token overlap, unchanged slice-2 mechanism —
GREEN at S95) PLUS the **shared-token** bound (the S95 §1F DB-pool case, now on the poll
carrier). Two rows: the independence floor (overlap) and the sharing ceiling (the 3rd parks).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `n_distinct_token_poll_capacity_leaves_overlap_max_not_sum` | e2e | `nt-reactor-e2e` | N (≥3) **distinct-token** poll leaves (each capacity ≥1, different tokens) overlap on ONE reactor thread — wall-clock ≈ **max**(D) not N·D; no cross-token permit dependency (the independence floor — distinct tokens never share a pool). The slice-2 overlap mechanism, re-asserted on the capacity-carrying poll leaf | P | **A1-LANDED** RED-first (`tests/concurrency_poll_capacity.rs`; **RENAMED** from plan `n_distinct_token_poll_leaves_overlap_max_not_sum` to disambiguate from the S95 bare-`async-demo` test of that exact name in `concurrency_capacity.rs`, which is GREEN — this is the capacity-leaf re-assertion) |
| `distinct_poll_effects_sharing_one_token_share_one_pool_nplus1_parks` | e2e | `nt-reactor-e2e` | TWO distinct **poll-shape** effect kinds (e.g. `poll-read` + `poll-write`) declaring the **same** token of capacity **N** draw from ONE shared `Semaphore(N)`: with N=2, 3 mixed-kind polls, at most 2 overlap and the 3rd parks regardless of kind (sum-in-flight ≤ N across both). The shared-pool bound is load-bearing — a per-effect-kind pool would let each run N concurrently (≈1·D) and fail the lower bound. Two-sided window as §1B | P+N | **A1-LANDED** RED-first (`tests/concurrency_poll_capacity.rs`) |

### 1E — first-writer-wins reconciliation on the POLL carrier (unit)

The poll analogue of S95 §1G. §8.1 reconciliation: two poll effects on one token declaring
different capacities ⇒ the first writer sizes the semaphore (never resized, never silent-max,
never abort), and a `TokenCapacityMismatch` strand event records the disagreement. NOT
subprocess-observable (in-memory sink) ⇒ intrinsics-unit.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `poll_same_token_conflicting_capacity_first_writer_wins_and_records_event` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | two **poll-shape** effects on one token declaring different capacities (2 then 5): the token's `Semaphore` is sized by the **first** writer (2 — never the larger), a second writer does NOT resize, AND a `TokenCapacityMismatch` strand event records the disagreement. Reuses the S95 pool's reconciliation code on the poll carrier (asserts no divergence between carriers) | P+N | RED-first (poll carrier has no live acquire today) |

---

## §2 — acquire-around-poll + the RAII `Permit` drop-guard (gate (a); the A→C contract)

**Gate (a) — TWO structural requirements.** (1) The `Permit` MUST be an **RAII drop-guard
owned by the `EffectPoll` future**, released on `Poll::Ready` **AND on future-drop** — a
race-lost / timed-out / disconnected poll that leaks its permit is how a capacity-N pool
bleeds to deadlock. **Chunk A BUILDS the drop-release path; Chunk C EXERCISES it** (the named
A→C contract — co-review the two for the Permit-on-drop path). (2) Acquire is
**non-re-entrant on its own token** — the platform poll-fn cannot re-enter admission, so it
cannot self-deadlock dispatching another effect on its own exhausted token. Admission stays
reactor-thread single-threaded (`reactor.md §2.8` lock-free permit map). Authority:
`reactor.md §2.9` (the AcquirePermit / Permit-on-drop seams) + §5.

### 2A — Permit released on `Poll::Ready` (the success path, unit)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `poll_ready_releases_permit_next_waiter_proceeds` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | over a fixture capacity-N pool: N `EffectPoll` futures hold permits; when one resolves `Poll::Ready` its `Permit` drops, `permits` increments, and the **front** FIFO waiter is woken and acquires (`Pending` → `Ready`). The (N+1)th, parked, proceeds only after a `Ready` frees a slot | P | RED-first (no poll-side permit today) |

### 2B — Permit released on FUTURE-DROP (the A→C contract — the load-bearing row)

The row Chunk C leans on. Drop / abandon an `EffectPoll` **mid-flight** (before `Ready`, while
it holds a permit and is parked-on-readiness) and assert the next waiter on that token
proceeds — i.e. a dropped poll does **not** leak its permit. NOT subprocess-observable in
Chunk A (no source-level cancellation until C) ⇒ intrinsics-unit; Chunk C adds the e2e
exercise via `timeout`/cancel-on-disconnect.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `dropping_inflight_poll_releases_permit_next_waiter_proceeds` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | a capacity-1 (or capacity-N, N in flight) token: one `EffectPoll` holds the permit and is **parked on readiness** (returned `Pending`, registered interest, NOT yet `Ready`); **drop the future** without resolving it ⇒ its RAII `Permit` releases (`permits` increments + front waiter woken); the next `AcquirePermit` waiter on that **same token** transitions `Pending` → `Ready` and runs. A leaked permit (drop without release) would leave the next waiter parked forever — the deadlock this guards | P+N | RED-first (the RAII drop-guard is the Chunk-A build) |
| `dropping_inflight_poll_deregisters_reactor_interest_neg` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | dropping a parked `EffectPoll` mid-flight also removes its fd/timer entry from the reactor `fd_waiters` map (no dangling waker fires into a dropped future); the permit AND the reactor interest both clean up on drop — the negative face: no orphaned waker, no double-free of the slot | N | RED-first |

### 2C — admission is non-re-entrant on its own token (gate (a) requirement 2, unit)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `poll_fn_cannot_re_enter_admission_on_own_token_neg` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | the acquire is the trampoline's single admission gate wrapping the whole establish→ready arc; a platform poll-fn invoked **inside** the arc does NOT re-enter admission (cannot dispatch another effect that re-acquires its own exhausted token) — so a capacity-1 poll-fn cannot self-deadlock. Structural assertion on the single-gate placement (`reactor.md §2.8`) | N | RED-first |

> **Web soundness by construction (gate (a)).** `accept` mints a *fresh* connection token;
> `read`/`send` ride that token — never a re-entry on the listener/pool token. §3A's web
> roundtrip is the observable confirmation that the acquire-around-poll arc does not deadlock
> the serial serve loop.

---

## §3 — web + stdio v7 adoption (item 1)

**Scope (Chunk A): a single SERIAL roundtrip per platform.** The full "server with no
`spawn`" (fan-out, supervisor, backpressure) is **Chunk B** — Chunk A proves only that the
rewritten poll-shape `accept`/`read` leaves serve **one** request under the **existing serial
serve loop** (a permanent baseline Chunk B accretes on). Both platforms stay byte-identical
when the feature is OFF (v6 blocking leaves coexist permanently via the slice-6 rayon route).

### 3A — web serves a single serial roundtrip via poll-shape `accept`/`read` (e2e)

The web platform's `accept` / internal `read_request` become **poll-shape** leaves over a
connection token; `send` may stay blocking. Under the existing serial `(accept) → handle →
(send) → recur` loop, one request round-trips. **Uses the raw-process pattern** (the
`Cranelisp` builder runs to completion; the web server is an infinite loop — `tests/
exemplar_web.rs` documents this exception: spawn → poll-until-listening → HTTP roundtrip →
kill via an RAII `ServerGuard`).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `web_poll_accept_read_serves_one_roundtrip_serial` | e2e (raw-process) | `nt-reactor-e2e` | a `--run` web server built with `concurrency-runtime` ON, using the **poll-shape** `accept`/`read` leaves, serves ONE HTTP roundtrip under the serial serve loop: the client GET gets the expected response body; the accept/read suspended on the reactor and resumed (the poll arc drove the request). The serial loop is unchanged (no fan-out) — this is the Chunk-A baseline, not the Chunk-B fan-out | P | **DEFERRED → A4** (see Wave-A1 record §"web rows deferred"): cannot be true-RED-first on the v6 single roundtrip (the v6 exemplar serves it fine → false-green), and binds the un-editable exemplar port 8080 → collides with `exemplar_web.rs` under the shared `nt-reactor-e2e` lane. Co-lands with the A4 poll-shape web rewrite + a port-parametrized poll-shape web fixture (G4) |

> **Reuse `exemplar_web.rs` machinery.** Mirror its `spawn_server` / `ServerGuard` / readiness
> poll / `http_request` helpers (or factor a shared module). Scope to a single GET roundtrip
> (the form-render path) — NOT the full Sudoku solve matrix (that is the existing
> `exemplar_web_server_serves_form_solution_and_not_found_over_http`, which stays GREEN on the
> v6 path feature-off). Pin a non-conflicting / ephemeral port to avoid the documented 8080
> collision.

### 3B — stdio `read_line` poll candidate works; `print` stays blocking (e2e)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `stdio_read_line_poll_candidate_round_trips` | e2e | `nt-reactor-e2e` | a `--run` program built `concurrency-runtime` ON that `read_line`s from piped stdin (the poll candidate — suspends on stdin readiness, resumes) and echoes via `print` (which stays blocking): the line round-trips correctly. The "simple platform ports cleanly" ergonomics check | P | **A1-LANDED** (`tests/concurrency_stdio_v7.rs`); **GREEN on HEAD — NOT RED-first**: piped+closed stdin is ready up-front so a poll-shape `read_line` never suspends → observationally identical to v6. Authored as an honest verify / stays-green pin (regression guard once A4 lands). See Wave-A1 record §"stdio rows are verify pins" |
| `stdio_print_stays_blocking_neg` | e2e | `nt-reactor-e2e` | `print` is NOT converted to a poll leaf — it lowers to the blocking `IO_TAG_EFFECT` carrier (verified observably: output ordering / no reactor suspend for `print`). The negative face: the rewrite did NOT over-convert blocking effects to poll-shape | N | **A1-LANDED** (`tests/concurrency_stdio_v7.rs`); GREEN on HEAD (stays-green — source-ordered sequential `print`s) |

### 3C — both platforms byte-identical when the feature is OFF (e2e, the floor)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `web_default_build_output_byte_identical_off` | e2e (raw-process) | `nt` | the web server built feature-OFF (the production default) serves the SAME roundtrip byte-identically — the poll-shape rewrite is invisible feature-off (v6 blocking `accept`/`read` via the rayon route). The existing `exemplar_web_server_serves_form_solution_and_not_found_over_http` covers the full matrix; this is the named byte-identical floor for the rewrite | P | **DEFERRED → A4** (port-8080 collision with `exemplar_web.rs` in the default lane; the existing `exemplar_web_server_serves_form_solution_and_not_found_over_http` is the de-facto byte-identical-off floor today). Co-lands with the A4 web rewrite + port-safe fixture |
| `stdio_default_build_output_byte_identical_off` | e2e | `nt` | a stdio `read_line`/`print` program is byte-identical through the default (feature-off) binary — the poll-candidate rewrite is invisible feature-off | P | **A1-LANDED** (`tests/concurrency_stdio_v7.rs`); GREEN on HEAD (stays-green, runs in `nt`) |

---

## §4 — the `poll_support` ergonomics suite (item 2 — evidence-first extraction)

**Extracted from real evidence** (rewrite §3 by hand against a minimal env accessor, let the
idiom pain surface, then extract). Four pieces (`SPRINT.md` item 2): the typed env accessor
(`PollState`), the fd-readiness/timer poll scaffold over the host/waker vtable, the
first-poll/re-poll phase scaffold (`PollState` phase — lost its S95 consumer to the
blocking-carrier decision), and the **converged macro skeleton**. `concurrency`-gated.

### 4A — `PollState` typed env accessor (unit) — the S95-deferred helper, now with a consumer

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `poll_state_env_accessor_arg_scratch_set_result_round_trip` | unit (`cranelisp-platform`) | `nt-concurrency` | `PollState::arg(i)` reads the i-th marshaled i64 arg, `scratch(i)` reads/writes leaf scratch, `set_result(v)` writes the host-known result slot — at the R1 env offsets (`[header \| code_ptr \| drop_glue_ptr \| env = result-slot + i64 args + scratch]`); a write-then-read round-trip pins the offset convention so the §3 web/stdio poll leaves + the §1 `poll-pool` capacity leaf are offset-safe. (Moved from S95 §4 — now has its real consumers: the web/stdio rewrites + the poll capacity leaf.) | P | RED-first (`PollState` absent on HEAD) |

### 4B — the fd-readiness / timer poll scaffold + first-poll/re-poll phase (unit)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `poll_support_fd_readiness_timer_scaffold_over_waker_vtable` | unit (`cranelisp-platform`) | `nt-concurrency` | the extracted fd-readiness/timer poll scaffold registers interest via the host/`WakerVTable` and returns `Pending`/`Ready` correctly against a fixture host ctx — codifying the idiom the hand-rewrite surfaced (the EWOULDBLOCK ⇒ register ⇒ Pending, wake ⇒ Ready loop) in one place | P | RED-first |
| `poll_state_phase_first_poll_then_re_poll` | unit (`cranelisp-platform`) | `nt-concurrency` | `PollState`'s first-poll/re-poll phase scaffold distinguishes the establish step (first poll: arm/register) from the resume step (re-poll: read-result) — the phase machine the poll leaves need (regained its consumer in Chunk A) | P | RED-first |

### 4C — the converged macro skeleton (gate (c) — retire the ~105-line mirror)

The converged skeleton retires `declare_concurrent_platform!` via a **field-shape-parameterized
shared inner helper**: v6 `declare_platform!` and the gated v7 path are **separate
`macro_rules!` arms** delegating to a common `@emit-*` helper taking only **shape-neutral
tokens** (manifest-entry construction, GOT export, fn-name handles). v7 type names
(`ConcurrentPlatformFn`, `ConcurrencyDescriptor`, `drop_state`, …) appear **only in the v7
arm** (itself gated) — never in the shared helper, never in an arm the v6 caller tokenizes.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `declare_platform_v6_and_v7_share_emit_helper_compile` | unit (`cranelisp-platform`) | `nt` + `nt-concurrency` | a v6 `declare_platform!` invocation compiles and produces the same manifest/GOT shape as before the convergence (feature-OFF — proving the shared `@emit-*` helper is shape-neutral), AND a v7 invocation compiles feature-ON producing the `ConcurrentPlatformFn` array via the v7 arm. The `declare_concurrent_platform!` mirror is gone (its callers route through the converged arm) | P | RED-first (mirror present today) |

### 5 — macro convergence `_neg` guard (gate (c) — the enforcement, MUST stay green)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `concurrency_descriptor_absent_from_default_public_api_neg` (EXISTS, `tests/facade_pif_rows.rs`) | e2e | `nt` | the v7 dormant types (`ConcurrencyDescriptor`, `ConcurrentPlatformFn`, `HostCtx`, `WakerVTable`, `Poll*`, `StrandId`/`StrandEvent`) stay ABSENT from every default-build `public-api.txt` — the macro convergence names only already-gated types, so the converged v6 arm's expansion stays free of v7 names | N | **A1-CONFIRMED** regression-replay — verified GREEN on HEAD (`tests/facade_pif_rows.rs:871`); MUST stay green (this chunk's review gate per gate (c)) |
| `declare_platform_v6_expansion_free_of_v7_type_names_neg` | unit (`cranelisp-platform`) | `nt` | a v6 `declare_platform!` invocation compiled WITHOUT the `concurrency` feature produces an expansion containing **no** v7 type-name tokens (`ConcurrentPlatformFn`/`ConcurrencyDescriptor`/`drop_state`/`Poll`/`Waker`) — the structural proof that the two-arm + shared-helper shape did not leak a `#[cfg]`-stripped v7-type reference into the v6 path (the exact hazard gate (c) names). NEW assertion warranted: the existing `_neg` guards the public-api edge; this guards the *macro expansion* directly | N | **A4 CO-LANDING UNIT** (`/dev`/`/platform`, `cranelisp-platform` `#[cfg(test)]`, authored WITH the converged macro — depends on the A4 macro shape per Gap G3) |

> **Why the new §5 macro-expansion row is warranted (per the task's "if a new assertion is
> warranted").** The existing `concurrency_descriptor_absent_from_default_public_api_neg`
> guards the *public-api baseline* (a type leaking onto the frozen edge). Gate (c)'s actual
> hazard is finer: a `#[cfg]`-stripped v7-type reference inside an arm the **v6 caller still
> tokenizes** — which would fail to *compile* the v6 stdio/web platforms feature-off, a
> failure the public-api guard does not directly name. The direct macro-expansion `_neg` pins
> that seam. (If `/dev`/`/platform` find the structural two-arm shape makes this
> unconstructable-by-construction — the v6 arm simply never mentions v7 tokens — the row may
> collapse into "v6 platforms compile feature-off", already covered by `nt` building the
> stdio/web crates; `/qa` authors to whichever the convergence lands, flagged Gap G3.)

---

## §6 — Regression guards / invariants (Chunk A must not perturb the floor)

Chunk A must not perturb the production default (`concurrency-runtime` OFF) NOR the S95
blocking-carrier capacity proof. The live poll-carrier acquire path is constructed ONLY
feature-on; feature-off the poll node's `(token, capacity)` slots ride as inert sentinel data;
`--link` links no executor.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `real_io_program_default_build_output_unchanged` (EXISTS, S94) | e2e | `nt` | a real-IO `--run` program's stdout/exit is byte-identical through the default binary — Chunk-A poll-carrier changes are invisible feature-off | P | regression-replay |
| `same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks` (EXISTS, S95) | e2e | `nt-reactor-e2e` | the S95 **blocking**-carrier capacity-N park stays GREEN — Chunk A's poll-carrier work does not regress the blocking carrier (the shared pool is reused, not forked) | P | regression-replay |
| `same_token_capacity_1_blocking_serial_and_source_ordered` (EXISTS, S95) | e2e | `nt-reactor-e2e` | the S95 blocking capacity-1 serial+ordered stays GREEN | P | regression-replay |
| `distinct_blocking_effects_sharing_one_token_share_one_pool_nplus1_parks` (EXISTS, S95) | e2e | `nt-reactor-e2e` | the S95 blocking DB-pool sharing stays GREEN | P | regression-replay |
| the 3 named two-pool guards (EXISTS, S95) | e2e | `nt-reactor-e2e` | `resource_serial_diff_token_parallelizes` / `auto_io_independent_diff_token_parallelizes_e2e` / `auto_io_par_grouping_uniform_across_modes` stay GREEN — two-pool routing unaffected by the poll-carrier acquire | P | regression-replay |
| `link_io_program_runs_without_executor` (EXISTS, S94) | e2e | `nt` | a small IO program `--link`ed then RUN succeeds (exit 0) — the linked binary works with no reactor/executor present | P | regression-replay |
| `link_path_does_not_enable_concurrency_runtime_neg` (EXISTS, S94) | unit (`src/`) | `nt` | the exe-bundle / `--link` build path never enables `concurrency-runtime` — the deployment invariant the poll-carrier work must preserve | N | regression-replay |
| `poll_carrier_default_build_constructs_no_acquire_path_neg` | unit (`cranelisp-backend`/`cranelisp-intrinsics`) | `nt` | a default (feature-off) build constructs **no** poll-carrier acquire path — the poll node's `(token, capacity)` slots ride as inert sentinel data (no `AcquirePermit` site reachable feature-off); poll effects lower to the unchanged feature-off path | N | RED-first if the gating leaks; else stays-green |
| `no_new_public_api_edge_or_abi_bump_chunk_a_neg` | e2e | `nt` | the `cranelisp-platform` / `cranelisp-types` `public-api.txt` baselines gain **no** new default-edge line from Chunk A (poll capacity rides the reserved in-process node slots; poll_support is gated); `ABI_VERSION` is unchanged (v7 stays unfrozen, in-tree platforms) | N | **A1-LANDED** (`tests/concurrency_poll_edge_guards.rs`); GREEN on HEAD (stays-green: no poll-ctor on the default edge, `ABI_VERSION == 7`). Flips RED if a Chunk-A wave leaks an edge/ABI bump |

---

## §7 — Flagged gaps shaping Stage-1 authoring

- **G1 — the poll-shape capacity test leaf (`target: /platform` + `/dev`).** The S95 capacity
  leaf (`pool-demo`) was **BLOCKING**; Chunk A needs the **poll-shape analogue** — the intended
  `poll-pool` platform with poll-shape effects declaring `(token, capacity)` at the effect site
  and routing to the **reactor** (not rayon):
  - `poll-read  : (Int token, Int capacity, Int ms) -> IO Int` — poll-shape armed-timer leaf,
    suspend/resume on the reactor, capacity-pooled; return `ms` (§1B/§1C/§1D/§2).
  - `poll-write : (Int token, Int capacity, Int ms) -> IO Int` — a DISTINCT poll effect kind
    on the same token (the §1D sharing case).
  - `poll-log   : (Int token, Int capacity, Int ms, String tag) -> IO Int` — poll-shape, print
    `tag` to real stdout (the §1C source-order witness).

  The leaf is a **platform effect** (zero `stdlib/` dependency — free-standing-test rule
  holds), written against `PollState` (§4A). It does NOT exist yet ⇒ the §1B/§1C/§1D e2e rows
  reference the intended surface via consts (mirror the S94 `ASYNC_LEAF_PLATFORM`/
  `ASYNC_LEAF_EFFECT` + S95 `POOL_*` pattern). **The fixture is authored WITH the Phase-5 /dev
  wave** (it uses the live poll-node carrier the wave lands — not a Wave-1/QA-first artefact).
  Does NOT block authoring the e2e rows RED-first (an absent platform is a clean runtime-RED;
  a non-compiling fixture crate would break the workspace build — do NOT add the crate in the
  QA-first wave). Flag to `/sprint` to sequence the `poll-pool` leaf + the live poll-carrier
  read early in the chunk so the acceptance rows have a real leaf to consume.

- **G2 — the strand event kinds for poll park/resume + drop-release (`target: /dev`
  intrinsics).** Whether §1E (capacity-disagreement) and the §2 drop-release path assert
  `TokenCapacityMismatch` / `TokenParked`/`TokenResumed` / a new drop-release event depends on
  `/dev`'s choice (`StrandEvent` is `#[non_exhaustive]`, reused from S95). Minor — affects only
  the event name in the unit assertions; `/qa` authors to whichever `/dev` lands.

- **G3 — the macro-convergence `_neg` shape (`target: /platform` + `/dev`).** Whether §5's
  direct macro-expansion `_neg` row is a distinct test or collapses into "v6 stdio/web
  platforms compile feature-off" (the structural by-construction proof) depends on the
  converged skeleton's exact shape (see the §5 note). `/qa` authors to whichever lands; the
  existing `concurrency_descriptor_absent_from_default_public_api_neg` MUST stay green
  regardless (this chunk's review gate per gate (c)).

- **G4 — the web roundtrip harness (`target: /qa`, self-resolved Phase 5).** §3A needs the raw-
  process server pattern (the `Cranelisp` builder cannot drive an infinite server). Factor or
  mirror `tests/exemplar_web.rs`'s `spawn_server`/`ServerGuard`/`http_request`; pin a
  non-conflicting port. Self-resolved by `/qa` at Stage-1 authoring — noted here for surface
  completeness.

These are surfaced here (not filed as FIXMEs) per the Phase-3 constraint (edit only
`tests/plan/`); `/sprint` routes G1/G2/G3 to `/platform` + `/dev` at the Phase-4 wave gate.

---

## §8 — Out-of-chunk (B / C) — NOT planned here (named for the partition gate)

Per the `SPRINT.md` chunk partition, these get full row tables when their chunks open. Named
so the chunk gate sees they are deliberately deferred, not missed:

- **Chunk B — launch-and-continue + supervisor + backpressure** (items 5 + 4, co-landed). The
  **"server with no `spawn`"** acceptance: accept-loop fan-out bounded by the admission budget
  (saturate-not-oversaturate); a **panicking handler → 500 + log + drop, server lives**;
  `min(capacity, degree)` on the §8.1 pool + a global reactor-thread admission `Semaphore`.
  Spec: 0447 first half (§10.12/§12 launch-and-continue + supervisor policy). **Depends on
  Chunk A** (fans out real poll `accept`/`read` leaves; bounded fan-out needs A's acquire-
  around-poll). FIXME 0460 (set-doc honest-failure e2e) is an opportunistic drain candidate
  here.
- **Chunk C — cancellation + combinator layer** (item 6). `race`/`select`/`timeout` (new gated
  IO node tags + `timeout = race io (sleep d)` `.cl`) + structured cancellation. **Exercises
  the A→C RAII Permit-release-on-drop contract** (§2B above is its load-bearing predecessor):
  per-request timeout fires and cancels the loser **releasing its permit**; cancel-on-
  disconnect; graceful shutdown. Spec: 0447 second half (§12 combinator typing/semantics).
  No public-api/ABI change.

---

## §9 — Phase-3 (Chunk A) exit gate confirmation

`/qa` confirms it has enough from the ratified contracts (`effect-concurrency.md`
§7/§8/§8.1/§8.2 + the Phase-2 gate rulings (a)/(c) + `reactor.md` §2.8/§2.9/§5 +
`io-trampoline.md` §13 + the reused `spec/10-io.md` §10.12.4.1) to draft the Phase-5 (Chunk-A)
Stage-1 failing tests:

- **§1 Poll-shape live capacity** — 3 unit (live poll-node read; acquire-spans-arc; shared
  pool) + 4 e2e (`nt-reactor-e2e`: capacity-N park §1B; capacity-1 serial+ordered §1C;
  distinct-token overlap + shared-token sharing §1D ×2) + 1 unit (first-writer-wins §1E).
  Anchor: §8.1 + §10.12.4.1.
- **§2 acquire-around-poll + RAII drop-guard** — 4 unit (`nt-concurrency-runtime`:
  Ready-releases §2A; **drop-releases §2B** + drop-deregisters-interest; non-re-entrant §2C).
  Anchor: gate (a) + `reactor.md` §2.9/§5. **§2B is the named A→C contract row.**
- **§3 web + stdio v7 adoption** — 2 e2e feature-on (`nt-reactor-e2e`: web serial roundtrip
  §3A; stdio read_line poll §3B) + 1 `_neg` (print stays blocking) + 2 e2e byte-identical-off
  (`nt`: web §3C, stdio §3C). Anchor: `SPRINT.md` item 1 Witnessable.
- **§4 poll_support suite** — 1 unit `PollState` round-trip (§4A) + 2 unit scaffold/phase
  (§4B) + 1 unit converged-macro compile (§4C). Anchor: `SPRINT.md` item 2.
- **§5 macro `_neg`** — 1 existing regression-replay (`concurrency_descriptor_absent…`, MUST
  stay green) + 1 new direct macro-expansion `_neg`. Anchor: gate (c).
- **§6 regression guards / invariants** — 6 existing regression-replays (byte-identical-off,
  4 S95 blocking-carrier capacity + the 3 two-pool guards collapsed to one row, link-no-
  executor, link-path-neg) + 2 new `_neg` (no-acquire-path-off; no-edge/ABI-bump). Anchor:
  App-B + `reactor.md` §1.

**Counts (Chunk A): 28 planned rows** —
- **e2e (`/qa`-authored): 11** — RED-first: §1B, §1C, §1D×2, §3A, §3B, §3B-neg, §3C×2 (9
  RED-first, 2 of them byte-identical-off that may be stays-green); regression-replay: 6 named
  in §6 (the S95 blocking + two-pool + link guards + byte-identical-off). *(The §6 "3 named
  two-pool guards" collapse to one ledger row; counted as one.)*
- **unit (`/dev`-/`/platform`-authored, named for surface completeness + mandatory-unit-per-
  fix): 14** — §1A×3, §1E×1, §2A/§2B×2/§2C×1 (4), §4A/§4B×2/§4C (4), §5 macro-expansion-neg
  ×1, §6 no-acquire-path-neg ×1. Plus the existing `concurrency_descriptor_absent…` (§5,
  e2e-tier in `facade_pif_rows.rs`) + `no_new_public_api_edge…` (§6) as edge guards.
- **Of the 28:** ~17 RED-first (the Chunk-A build surface) + ~9 regression-replay/stays-green
  carries + 2 edge/`_neg` guards. The new file/extend target: a new `tests/concurrency_poll_
  capacity.rs` (gated `#![cfg(feature="concurrency-runtime")]`, mirroring `concurrency_
  capacity.rs`) for §1B/§1C/§1D; extend / mirror `tests/exemplar_web.rs` for §3A/§3C web; a
  `tests/concurrency_stdio_v7.rs` or extend `spec_platforms` for §3B/§3C stdio. The unit rows
  land in `cranelisp-intrinsics` / `cranelisp-platform` `#[cfg(test)]` with the /dev waves.

### Open verdict for `/sprint` + user

The Chunk-A Stage-1 surface is **draftable now** for §1–§6. The `nt-reactor-e2e` /
`nt-concurrency` / `nt-concurrency-runtime` lanes + the `src/` passthrough **all already
exist** (S94/S95) — there is **no lane blocker**. The sequencing dependencies are:

1. **Gap G1** (the `poll-pool` poll-shape capacity leaf + `PollState`): the §1B/§1C/§1D e2e
   rows are draftable RED-first immediately (they reference the intended leaf shape; RED =
   "poll leaf does not yet declare capacity / the poll path does not yet acquire"), and flip
   GREEN once `/platform` + `/dev` land the leaf + the live poll-carrier read + the acquire-
   around-poll lifecycle. **Recommend `/sprint` sequence the `poll-pool` leaf + `PollState`
   (§4A) + the live poll-node read + the AcquirePermit-around-poll arc early in the chunk** so
   the acceptance rows have a real leaf before `/dev` claims the chunk green.
2. **§2B is the A→C contract row** — co-review it with Chunk C's cancellation work (the
   Permit-release-on-drop path A builds, C exercises). It is an intrinsics-unit row this chunk
   (no source-level cancellation until C) — its e2e exercise is a named **Chunk C** row.
3. **§5's `concurrency_descriptor_absent…` MUST stay green** — it is this chunk's review gate
   (gate (c)); `/review` (platform) walks it on the change-set.

## Wave-A1 landing record (Phase-5 Chunk-A Stage-1, `/qa` 2026-06-28 — ACTUAL)

This is the as-landed record of the QA-first wave. Test files authored this wave (no
`#[ignore]`; every test carries a `// spec:`/`// design:` ref):

### A1-LANDED — e2e files (`/qa`)

- **`tests/concurrency_poll_capacity.rs`** — gated `#![cfg(feature="concurrency-runtime")]`
  (compiles to nothing in default `nt`). 4 RED-first rows, all RED on HEAD with the clean
  runtime signal `platform 'poll-pool' not found` (the Gap-G1 fixture is an A4 deliverable):
  - §1B `same_token_capacity_n_poll_admits_n_concurrent_nplus1_parks`
  - §1C `same_token_capacity_1_poll_serial_and_source_ordered`
  - §1D `n_distinct_token_poll_capacity_leaves_overlap_max_not_sum` (**RENAMED** from the plan's
    `n_distinct_token_poll_leaves_overlap_max_not_sum` — that exact name already exists in
    `concurrency_capacity.rs` (S95 async-demo overlap, GREEN); the rename disambiguates the
    capacity-leaf re-assertion from the bare-leaf one).
  - §1D `distinct_poll_effects_sharing_one_token_share_one_pool_nplus1_parks`
- **`tests/concurrency_stdio_v7.rs`** — §3B/§3B-neg gated `#[cfg(feature="concurrency-runtime")]`,
  §3C-stdio UNGATED (`nt`). All 3 **GREEN on HEAD (verify / stays-green, NOT RED-first)** — see
  the §"stdio rows are verify pins" finding below.
- **`tests/concurrency_poll_edge_guards.rs`** — UNGATED (`nt`). `no_new_public_api_edge_or_abi_
  bump_chunk_a_neg` — GREEN on HEAD (no poll-ctor on the default platform edge; `ABI_VERSION
  == 7`). The §6 no-edge/no-ABI-bump floor.
- **§5 existing guard confirmed**: `concurrency_descriptor_absent_from_default_public_api_neg`
  (`tests/facade_pif_rows.rs:871`) verified GREEN on HEAD — this chunk's review gate (gate (c)).

### A1-DEFERRED → A4 co-landing (e2e rows the plan listed, not authorable cleanly in A1)

- **web rows deferred** — §3A `web_poll_accept_read_serves_one_roundtrip_serial` and §3C-web
  `web_default_build_output_byte_identical_off`. Two blockers /qa cannot resolve in the QA-first
  wave: (1) **no true-RED on the v6 single roundtrip** — the v6 exemplar serves a single serial
  GET fine, so a roundtrip assertion would be FALSE-GREEN today, not RED-first (it only becomes
  a real signal against the A4 poll-shape web server); (2) **port-8080 collision** — the
  exemplar hard-codes `(defn port [] 8080)` (un-editable by `/qa`), so any new web-server test
  collides with `exemplar_web.rs` in BOTH shared lanes (`nt-reactor-e2e` runs the whole
  `cranelisp` suite incl. `exemplar_web.rs`). Resolution: co-land both web rows with A4, which
  provides a **port-parametrized poll-shape web fixture** (Gap G4) — `/dev`/`/platform` author
  the fixture + the rewrite, `/qa` then adds the two web e2e against the port-safe fixture
  (and serialises them with `exemplar_web.rs` via a nextest `web-serve` test-group if 8080 is
  still shared). The existing `exemplar_web_server_serves_form_solution_and_not_found_over_http`
  is the de-facto byte-identical-off floor until then.

### stdio rows are verify pins (Wave-A1 finding)

The stdio `read_line` correctness round-trip is **observationally equivalent** to v6 through
the subprocess harness: piped stdin is closed up-front, so a poll-shape `read_line` finds data
ready and never suspends → byte-identical to the v6 blocking read. The harness has no
controllable mid-run stdin timing and no observable poll-vs-block distinction on instant I/O.
So §3B/§3B-neg/§3C-stdio are authored as **honest verify / stays-green pins** (regression
guards once A4 lands), NOT RED-first — the genuine RED-first poll-carrier acceptance lives in
`concurrency_poll_capacity.rs` (the §1 capacity rows, which require the acquire-around-poll
machinery). This is faithful to failing-not-ignored: a genuinely-passing pin is not a hidden
failure; none are `#[ignore]`'d.

### Co-landing UNIT rows owned by later /dev waves (named for surface completeness)

These reference types/fields that do not exist on HEAD (e.g. `EffectPoll.permit: Option<Permit>`,
the live poll-node bake helpers, the `poll-pool` fixture constructors, `PollState`); writing
them now would break the `cargo nextest` build. They co-land `#[cfg(test)]` in the owning crate
WITH the /dev wave that lands the type (the S95 precedent):

- **A2 (backend bake, `cranelisp-backend`)**: §6 `poll_carrier_default_build_constructs_no_
  acquire_path_neg` (partly backend); the poll-node live `(token, capacity)` bake unit tests.
- **A3 (intrinsics acquire-around-poll, `cranelisp-intrinsics`)**: §1A ×3 (live poll-node read;
  acquire-spans-arc; shared pool), §1E (first-writer-wins + `TokenCapacityMismatch`), §2A
  (Ready-releases), **§2B (drop-releases — the load-bearing A→C contract)** + §2B
  (drop-deregisters-interest-neg), §2C (non-re-entrant-neg). The A→C RAII Permit-release-on-drop
  path is BUILT + unit-verified in A3; its e2e exercise is a named **Chunk-C** row.
- **A4 (platform + web/stdio rewrite + fixture)**: §4A `PollState` round-trip, §4B ×2 (fd/timer
  scaffold; first-poll/re-poll phase), §4C converged-macro compile, §5
  `declare_platform_v6_expansion_free_of_v7_type_names_neg` (depends on the converged macro
  shape — Gap G3), AND the **Gap-G1 `poll-pool` poll-shape capacity test leaf** that flips the
  4 A1 `concurrency_poll_capacity.rs` rows GREEN (add it to `tests/scripts/build-link-prereqs.sh`
  so the e2e resolves it), plus the deferred web rows (above).

### Measured suite state (Wave-A1 close)

- **Default `nt`** (release gate, feature-OFF): **1702 passed / 1 skipped / 0 failed** (+2 vs
  the S95-close 1700: the two A1 ungated rows `stdio_default_build_output_byte_identical_off`
  + `no_new_public_api_edge_or_abi_bump_chunk_a_neg`). The 1 skip = the S94-demoted CPU-floor
  benchmark. The gated poll files compile OUT — no collateral RED. **No regression.**
- **`nt-reactor-e2e`** (`-p cranelisp --features concurrency-runtime`, `--no-fail-fast`):
  **1716 run / 1711 passed / 5 failed / 1 skipped.** The 5 RED = the **4 intended A1 poll-
  capacity rows** (`platform 'poll-pool' not found`) + **1 pre-existing known intermittent**
  `repl_introspection::imports_filter_neg_nonexistent_module_not_error` (FAIL at **30.021 s** =
  the 30 s harness cap — the documented cold-start REPL-cap / H5-H7 heisenbug residue noted in
  `.config/nextest.toml` and the S95 close; NOT Chunk-A-caused). The S95 blocking-carrier
  capacity guards (`same_token_capacity_n_blocking…`, `same_token_capacity_1_blocking…`,
  `distinct_blocking_effects_sharing…`), the two-pool guards, the S95 async-demo overlap, and
  `mixed_blocking_and_poll_par_overlaps_on_both_pools` all stay GREEN. **No regression beyond
  the named set.**

> A `tests/plan/ledger.md` entry mirroring this record will be added at Chunk-A Stage-1 close
> proper (after the A2–A5 /dev waves flip the RED set green).

<!-- ========================================================================= -->
<!-- ============================ CHUNK B ==================================== -->
<!-- ========================================================================= -->

# CHUNK B — Launch-and-continue + supervisor + backpressure (the fan-out / control-flow chunk; the reference-workload headline)

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests land in
**Phase 5 Chunk-B Stage 1** (QA-first, before the per-crate D/D/R waves). This section
extends the Chunk-A plan above (same row-per-requirement format) with the Chunk-B surface.

> **CHUNK-DELIMITED.** This section covers **CHUNK B ONLY** — slice 5 (launch-and-continue +
> supervisor: the "server with no `spawn`" + panic→500-server-lives) and slice 4
> (backpressure / admission budget: saturate-not-oversaturate, bounded in-flight), plus the
> **web poll rewrite** carried from Chunk A (the deferred §3A/§3C-web rows + the
> connection-token model of FIXME 0465 + the Gap-G4 port-parametrized web fixture). **Chunk C
> (cancellation + combinators — `race`/`select`/`timeout`) is LATER and NOT planned here.** The
> A→C RAII-Permit-release-on-drop contract was *built* in Chunk A (§2/§2B above) and is
> *exercised* by Chunk C — out of this chunk.

---

## Scope source + contracts of record (Chunk B)

**Scope source:** `sprints/SPRINT.md` S96 items 4 (backpressure) + 5 (launch-and-continue +
supervisor) — **co-landed** (Phase-2 gate (b): supervisor is co-requisite with
launch-and-continue, and fan-out must be bounded by admission, §14 step 4) — the **Chunk B**
partition entry's **Witnessable** bullet ("the *server with no `spawn`*"), plus the web poll
rewrite + FIXME 0465 carried from Chunk A close.

**Contract of record:**
- `design/arch/effect-concurrency.md` **§4** (launch-and-continue is *inferable* — an effect
  whose result is discarded and whose tokens are disjoint may be launched and not joined; the
  accept loop fans out automatically, TCO'd; backpressure is a scheduler policy) / **§5** (the
  *degree* program-throttle, `effective permits = min(capacity, degree)` + the FIXME-0442
  ruling: TWO substrate-bound mechanisms, ONE concept — I/O effect over-budget **admission-
  parks**) / **§9** (the control half — separable-but-committed) / **§10** (supervisor
  semantics: **500 + log + drop-the-request**, never a silent strand, never a whole-server
  abort; the reused worker-side capture; the honest "no first-error for detached strands"
  caveat) / **§11** (observability: supervisor drops vanish without a sink — the strand event
  is the trace) / **§16** (the worked pure-side server sketch — the `serve`/`handle-conn`
  shape the demo realizes).
- `design/int/reactor.md` **§5** (forward-looking: backpressure / *degree* generalizes the
  S92 CPU spark-budget counter into the reactor's I/O dimension via the inert `global_budget`
  field; supervisor = launch-and-continue + 500/log/drop for detached strands) / **§2.8** (the
  lock-free single-reactor-thread permit map the *degree* throttle parameterizes + the global
  admission `Semaphore` reuses) / **§3** (the `StrandEvent` sink the supervisor-action +
  admission-park events emit into). **NOTE:** the Chunk-B supervisor + backpressure interior
  is being authored by the sibling `/design` int agent THIS Phase — these rows cite the
  reactor.md §5 forward-looking anchors + the §10 architectural acceptance; the concrete
  `JoinSet` handle / global-Semaphore seam names are folded in at Stage-1 authoring (Gap G6).
- `design/platform/poll-support.md` **§3.2** (the web connection-token model — `accept` mints
  a FRESH connection token; `read`/`send` ride it: the gate-(a) non-re-entry property the
  fan-out leans on) / **§3.4.5** (the reactor connection-pool lifecycle — the real
  capacity-on-poll consumer). **FIXME 0465** (the concrete cranelisp connection-handle
  interface — `web/Connection` ADT + token-carrying `read`/`send` + serve-loop reshape) is the
  keystone the web rows + the slice-5 fan-out depend on; being resolved by the sibling
  `/design` platform + `/port` agents THIS Phase.

**Spec of record (0447 first half — `/spec` actioning THIS Phase):** `spec/10-io.md` **§10.12**
(launch-and-continue semantics: the un-joined detached strand; the TCO / observational-
equivalence interaction; the *degree*-budget user-facing surface) + **§12** (the supervisor-
policy note). The sibling `/spec` agent is authoring the §10.12/§12 control-layer surface this
Phase; these rows cite the §10.12/§12 anchors **provisionally** (Gap G5) and the `// spec:`
back-trace is pinned to the as-landed anchor at Stage-1 authoring. The Chunk-A §10.12.4.1
capacity anchor is **reused unchanged** for the *degree*-over-capacity composition rows (degree
composes on the same §8.1 pool capacity proves).

**Public-api / ABI of record (post-single-ABI-cutover):** the `concurrency` /
`concurrency-runtime` features are **RETIRED** (the cutover collapsed them — `Cargo.toml`
§6.8.0a). There is **ONE collapsed test lane**: `cargo nextest run` (the reactor is always
present via the eager-cheap fallback). Chunk-B tests are **un-gated** (no `#![cfg(feature=…)]`)
and run in that single lane. Per gate (d)/0442: *degree* + the global admission budget ride the
**already-core** `ConcurrencyDescriptor.global_budget` (no new edge line) + a reactor-
construction knob (int-internal); the supervisor reuses the S95 worker-side capture +
`StrandEvent` (`#[non_exhaustive]`); the launch-and-continue fan-out is an in-process trampoline
behaviour. **Expected Chunk-B public-api delta: ZERO new `cranelisp-types` / `cranelisp-platform`
edge lines, NO `ABI_VERSION` bump** (the web connection-handle interface of 0465 is `.cl` ADT +
in-process node operands, not a new ABI field). §B7 carries the no-new-edge guard.

## Conventions / legend (Chunk B)

- **Lane** — `nt` (the single collapsed `cargo nextest run`; reactor always present). Unit rows
  run via `-p cranelisp-intrinsics` (still inside `nt`). There is NO `nt-reactor-e2e` lane any
  more — the cutover collapsed it; Chunk-A rows that named it now run in `nt` (the doc-comment
  lane references in `tests/concurrency_*.rs` are stale and slated for the A4d doc sweep).
- **Tier** — `e2e` (`/qa`-authored, subprocess; **raw-process** for the infinite web server per
  `tests/exemplar_web.rs`, or the `Cranelisp`-builder run-to-completion pattern for synthetic
  poll-pool programs) / `unit` (`/dev`-authored `#[cfg(test)]` in the owning crate, named here
  for surface completeness + the mandatory-unit-per-fix discipline).
- **Posture** — `RED-first` (a failing guard the /dev wave flips green; an absent fixture leaf /
  unrealized capability is a clean runtime-RED, not a compile break) / `co-landing` (authored
  WITH the /dev wave that lands the fixture — referencing types/programs that do not exist on
  HEAD would break the workspace build, so these are authored in-wave, the S95 + Chunk-A-web
  precedent) / `verify` (a genuinely-passing pin — failing-not-ignored-faithful, none
  `#[ignore]`'d) / `regression-replay` (an existing guard that must stay green).
- **P/N** — positive (correct behaviour appears) / negative (wrong behaviour absent).

> **The e2e ↔ unit ↔ synthetic-vs-web split (the Chunk-B sequencing).** The Chunk-A precedent
> stands: **e2e first (QA-first, black-box), units co-land with their /dev crate wave, keep the
> build compilable.** Chunk B has THREE e2e flavours: (1) **synthetic RED-first** rows that
> witness launch-and-continue / backpressure / detached-fault-isolation through an extended
> `poll-pool`-style leaf + a launch loop — clean runtime-RED on HEAD (the capability/fixture is
> absent), authorable QA-first in Stage-1 Wave-1; (2) **web co-landing** rows that witness the
> SAME behaviours through the real "server with no `spawn`" — these need the FIXME-0465 web
> rewrite + the Gap-G4 port-parametrized fixture, so (exactly like the deferred Chunk-A web
> rows) they co-land with the /dev web wave (`/qa` adds them against the port-safe fixture); and
> (3) **unit** rows (supervisor `JoinSet`, the global-`Semaphore` / `min(capacity,degree)`
> composition, the no-ferry semantics) co-landing in `cranelisp-intrinsics` with the /dev
> supervisor+backpressure wave. The synthetic rows are the QA-first acceptance the per-crate
> triads make green; the web rows are the headline-workload confirmation.

---

## §B1 — The "server with no `spawn`" reference workload (the headline e2e)

**Acceptance (`SPRINT.md` Chunk B Witnessable + arch §4/§16).** A web server `accept`s
connections and fans out per-connection handlers via **launch-and-continue** — `(do (handle-conn
conn) (serve listener))`, where `handle-conn` returns `IO Unit`, its result is unused, and its
connection token is disjoint from the next `accept` — so the accept loop keeps accepting while
many handlers run concurrently. **There is NO user-level `spawn` primitive** (the fan-out is
inferred). Witness: concurrent requests overlap; a single roundtrip works under the reshaped
fan-out loop. These ride the FIXME-0465 connection-handle interface + the Gap-G4 port-param
fixture ⇒ **web co-landing** (raw-process, per `tests/exemplar_web.rs`).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `web_server_fans_out_concurrent_requests_overlap` | e2e (raw-process) | `nt` | the reshaped fan-out server (poll `accept`/`read`/`send` + launch-and-continue) serves **K concurrent slow requests** (K client connections opened back-to-back, each hitting a deliberately-slow handler route of ≈D ms) with **wall-clock ≈ max not sum** — the handlers OVERLAP (the accept loop did not serialise behind each handler). Two-sided window vs serial (≈K·D) and vs unbounded — the launch-and-continue fan-out is the load-bearing assertion. Best-of-N min (the §1B jitter discipline) | P | **co-landing** (FIXME-0465 web rewrite + Gap-G4 port-param fixture + a slow-handler route) |
| `web_server_serves_single_roundtrip_under_fanout_loop` | e2e (raw-process) | `nt` | one GET round-trips correctly through the **reshaped fan-out serve loop** (the demo is correct at K=1 — the fan-out path degenerates to a single in-flight handler and still produces the right response body). The Chunk-A §3A serial-roundtrip row is SUBSUMED here (the serial loop is replaced by the fan-out loop in Chunk B) | P | **co-landing** (subsumes the deferred §3A; see §B5a for the poll-`accept`/`read` mechanism assertion) |
| `web_server_no_user_spawn_primitive_neg` | e2e | `nt` | the language exposes **no `spawn`** (nor `go`/`async`/`thread`) primitive: a `--run`/REPL probe of `spawn` reports unbound, AND the server source (the fixture `main.cl`) contains **zero** concurrency primitives — the fan-out is purely inferred from dataflow (arch §1/§4). The negative face of "concurrency written by nobody" | N | **B1-LANDED verify** (`tests/concurrency_fanout.rs`; GREEN on HEAD — bare-REPL probes of `spawn`/`go`/`async`/`thread` all report `undefined variable`; failing-not-ignored-faithful, not `#[ignore]`'d. Scoped to the language-level probe; the "fixture `main.cl` contains zero primitives" half co-lands with the B5 web fixture) |

---

## §B2 — Supervisor: panic → 500, server lives (the load-bearing chunk-B row)

**Acceptance (arch §10 + gate (b)).** A handler that **faults** produces a **500 (or the error
response) for THAT request** while the server **keeps accepting + serving subsequent requests**
— the supervising context survives. The §10 policy is **500 + log + drop-the-request**, never a
silent strand, never a whole-server abort. Gate (b): the S95 worker-side capture is **reused
verbatim**; the join-side re-raise is **NOT** what detached strands need — new machinery is a
**supervisor handle** (`JoinSet`-equivalent on the reactor) that owns each detached strand
future, catches its outcome, and applies the policy, never re-raising into the (nonexistent)
parent. The fault **does NOT propagate to kill the accept loop** (the `_neg`, load-bearing).

### B2-syn — synthetic RED-first (the detached-fault-isolation + loop-lives core, no web)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `detached_faulting_effect_does_not_abort_the_launch_loop` | e2e (synthetic) | `nt` | a loop that **launches a faulting poll effect each iteration** (a `poll-pool` `poll-fault` leaf that panics/returns a runtime error, launched-and-not-joined per arch §4) still **completes all iterations** and exits cleanly (the supervisor catches + drops each faulted strand; the loop lives) — the synthetic core of "panic → drop, server lives", with no web/HTTP machinery. A non-supervised detached panic would abort the program (non-zero/signal exit) — the deadlock/abort this guards | P+N | **B1-LANDED RED-first** (`tests/concurrency_fanout.rs`; RED on HEAD with the clean runtime signal `'poll-fault' not found in module 'platform.poll-pool'` — the Gap-G6 leaf + supervisor are co-landing B2/B3 /dev deliverables. Uses `bind`-with-unused-binder, not the prelude `do` macro, per the free-standing-test rule) |

### B2-web — the headline supervisor acceptance (web co-landing)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `web_handler_fault_yields_error_response_for_that_request` | e2e (raw-process) | `nt` | a request to a **fault-injecting route** (a handler that deliberately faults) gets a **500 / error response** for that request (status 500 or the documented error body) — the supervisor turned the panic into a response, not a hang/crash | P | **co-landing** (FIXME-0465 web rewrite + a fault-injecting handler route, Gap G6) |
| `web_server_survives_handler_fault_continues_serving` | e2e (raw-process) | `nt` | **after** a faulting request, a subsequent normal GET on a fresh connection **still succeeds** (the expected body) — the accept loop + supervising context outlived the fault; the server keeps serving | P | **co-landing** |
| `web_handler_fault_does_not_kill_accept_loop_neg` | e2e (raw-process) | `nt` | the handler fault does **NOT** propagate to abort the accept loop / crash the server process — the child stays alive (still `try_wait() == None` / still accepting) after the fault; the fault did not exit/signal the process. **The load-bearing `_neg`** — a fault that ferried up to the accept loop would kill the server | N | **co-landing** (load-bearing) |

### B2-unit — supervisor machinery (intrinsics co-landing)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `supervisor_owns_detached_strand_catches_panic_applies_policy_and_records_event` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | the supervisor handle (`JoinSet`-equivalent) **owns** a detached strand future, **catches** its panic/error outcome (reusing the S95 worker-side `take_runtime_error()` capture), applies the **drop-the-request** policy **without re-raising into any parent**, and **records a `StrandEvent` supervisor-action** (§10 + §11 — the drop is logged, not silent). The negative face: the captured error is NOT `set_runtime_error()`-re-raised (the detached path diverges from the structured ferry — gate (b)) | P+N | **co-landing** (the supervisor `JoinSet` seam — Gap G6; depends on the /dev supervisor wave) |
| `supervised_drop_is_not_silent_neg` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | a supervised strand drop emits an observability event into the `StrandEvent` sink — it does **NOT** vanish silently (§11 reason 2: supervisor drops vanish without a sink; the policy + the sink are coupled). Asserts the sink received a supervisor-action event for the dropped strand | N | **co-landing** |

---

## §B3 — Backpressure / admission budget (slice 4)

**Acceptance (arch §4/§5 + gate (d)/0442 + reactor.md §5).** With a program-chosen **`degree`**
set, **at most `degree` handlers are in flight** (saturate-but-do-not-oversaturate); the
(degree+1)th admission **PARKS** (observable as bounded in-flight / bounded latency growth, NOT
unbounded memory growth). *degree* composes with the per-resource S95 capacity as **`min(capacity,
degree)`** on the existing §8.1 token-permit map, **plus** one **global** reactor-thread admission
`Semaphore` that bounds total in-flight detached strands (the launch-and-continue fan-out memory
bound). The over-budget action is **admission-park** (not the CPU-spark inline-fold — 0442's two-
mechanisms-one-concept ruling).

### B3-syn — synthetic RED-first (degree parking via a launch loop, no web)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `degree_n_bounds_inflight_launched_effects_nplus1_parks` | e2e (synthetic) | `nt` | a loop that **launches M independent slow poll effects** (`poll-pool`, distinct/fresh tokens so capacity does not bound them) under a configured **`degree = N` (N < M)**: at most **N** overlap, the (N+1)th **admission-parks** until one frees ⇒ wall-clock ≈ ⌈M/N⌉·D (waves), distinguishable from unbounded (≈1·D — all M overlapped, degree not enforced) AND from serial (≈M·D). Two-sided window; best-of-N min. **Saturate-not-oversaturate is the load-bearing assertion** — the lower bound proves the (N+1)th parked, the upper bound proves N DID overlap | P+N | **B1-LANDED RED-first** (`tests/concurrency_fanout.rs`; M=4, N=2, distinct tokens 1-4. RED on HEAD: validated ~180ms ≈ 1·D against the stale binary — degree unenforced, all 4 overlap ⇒ < the 225ms lower bound. The `CRANELISP_DEGREE` env knob is the provisional degree surface (§10.12.4.2: degree is implementation-defined config, not a language form), reconcile at the /dev backpressure wave, Gap G6) |

### B3-unit — the composition + the global bound (intrinsics co-landing)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `effective_permits_is_min_capacity_degree_both_directions` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | the effective in-flight ceiling on a token is **`min(capacity, degree)`**: with `degree < capacity` the *degree* wins (fewer admitted than the resource ceiling); with `degree > capacity` the *capacity* wins (the program throttle never raises past the resource's safe ceiling, arch §5). Both directions — the negative face is "degree never exceeds capacity" | P+N | **co-landing** (the §8.1 permit-map `min`-threading — Gap G6) |
| `global_admission_semaphore_bounds_total_inflight_detached_strands` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | the **global** reactor-thread admission `Semaphore` (reusing the §2.8 `AcquirePermit`/`TokenSlot`) caps **total** in-flight detached strands across ALL tokens — so an unbounded accept-loop fan-out cannot exhaust memory even with all-distinct connection tokens (the §14-step-4 memory bound the supervisor co-requires). The (global+1)th detached launch parks on the global gate | P | **co-landing** |

### B3-web — bounded in-flight under flood (web co-landing)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `web_server_bounded_inflight_under_request_flood_neg` | e2e (raw-process) | `nt` | under a **flood** (many fast-arriving client connections to a slow-handler route), the server's in-flight handler count stays **bounded** (observed as bounded concurrency / bounded latency-growth — the (degree+1)th request's response is *delayed* until a slot frees, not refused and not unbounded), NOT unbounded growth. The `_neg`: oversaturation does not occur — handlers in flight never exceed the budget. **Caveat:** direct memory-bound assertion is not subprocess-observable; this row uses the **parking/latency proxy** (a flood completes in ≈⌈flood/degree⌉ waves, not all-at-once), the same proxy as B3-syn | N | **co-landing** (depends on B3-syn's admission + the web fixture + a slow-handler route) |

---

## §B4 — Launch-and-continue semantics

**Acceptance (arch §4 + gate (b) + §10 caveat).** A **launched** effect runs **concurrently**;
the **launcher continues without awaiting** it (its result is discarded; its tokens are disjoint
from the continuation). Critically, the launched effect's **fault does NOT ferry into the
launcher** — contrast the structured `Par`/IVar fork-join, which DOES capture + re-raise the
first error inside the dynamic extent (the join-side re-raise has a parent to land on; the
detached strand does not). This asymmetry is gate (b)'s ruling and the §10 honest caveat
("no first-error ordering for detached strands").

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `launch_and_continue_runs_concurrently_launcher_does_not_await` | e2e (synthetic) | `nt` | `(do (slow-effect) (fast-continuation))` where `slow-effect` is a launched poll effect (result discarded, token disjoint): the **launcher proceeds to and completes `fast-continuation` without joining** `slow-effect` (wall-clock of the continuation ≪ the slow effect's D — the launcher did not block on it), AND `slow-effect` still **runs** (its observable side effect — a stdout tag — appears). Launch-and-continue overlap, not serial sequencing | P | **B1-LANDED RED-first** (`tests/concurrency_fanout.rs`; realized as the canonical **tail-recursive accept-loop** `(bind (poll-read n …) (fn [r] (fanout-loop (- n 1))))` launching K=5 slow effects — NOT a flat `(do slow fast)`, which structured auto-IO-parallel would overlap too and could not distinguish from launch-and-continue. RED on HEAD: validated ~789ms ≈ 5·D serial against the stale binary — each `bind` awaits, no fan-out ⇒ > the 450ms upper bound. Two-sided window also pins drain-at-exit, lower bound 0.5·D) |
| `detached_strand_fault_does_not_ferry_into_launcher_neg` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | a **launched (detached)** effect that faults does **NOT** re-raise into the launcher: the launcher's own outcome is unaffected (it returns its normal value, no `set_runtime_error` pollution from the detached fault) — the join-side re-raise has nowhere to land (gate (b)). The captured fault goes to the supervisor (§B2), not the launcher. **The load-bearing negative-semantics row** | N | **co-landing** (the detached-vs-structured branch — Gap G6) |
| `structured_par_first_error_still_re_raises_contrast` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | the **contrast**: the structured `Par`/IVar fork-join STILL ferries the worker-side capture + re-raises the first error into the joining frame (the S95 as-built ferry, `ivar.rs`/`io.rs`) — confirming Chunk B did NOT regress the structured path while adding the detached path. The two paths are deliberately divergent (gate (b)) | P | **regression-replay** (assert the existing structured ferry still re-raises; pair it with the `_neg` above so the divergence is pinned, not accidental) |

---

## §B5 — The deferred web e2e rows (the §3A/§3C-web carry) + Gap G4

**Carried from Chunk A close.** Chunk A deferred §3A (web serial roundtrip via poll `accept`/`read`)
and §3C-web (byte-equivalence) because (1) no true-RED on the v6 single roundtrip and (2) the
exemplar hard-codes `(defn port [] 8080)` → collides with `tests/exemplar_web.rs` in the shared
lane. The web poll rewrite lands in Chunk B (FIXME 0465), so these **co-land** here against the
**Gap-G4 port-parametrized poll-shape web fixture**. (Post-cutover the "byte-identical-OFF" framing
is retired → "reactor-free-off"; with one always-present reactor there is no off-state to compare,
so §3C-web is reframed as **serve-equivalence to the known-good rendered HTML**, not a feature-off
byte diff.)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `web_poll_accept_read_serves_one_roundtrip` | e2e (raw-process) | `nt` | the **poll-shape** `accept` (parks on the listener fd, mints a FRESH connection token) + `read` (rides that token, parks on the connection fd) leaves serve ONE HTTP roundtrip: the GET gets the expected body; the accept/read **suspended on the reactor and resumed** (the poll arc drove the request) — the §3A mechanism assertion, now realizable against the FIXME-0465 connection-handle interface. The non-re-entry property (gate (a)): `accept` mints, `read`/`send` ride — no listener-token re-entry | P | **co-landing** (FIXME-0465 + Gap-G4 fixture) |
| `web_poll_server_serves_response_equivalent_to_reference` | e2e (raw-process) | `nt` | the poll-shape web server serves the **same rendered HTML** the reference path serves (the full GET-form / POST-solve / 404 matrix the existing `exemplar_web_server_serves_form_solution_and_not_found_over_http` asserts) — the poll rewrite changed *when* the effect completes (poll vs block), not *what* crosses the boundary (`poll-support.md §3.2`). The `_neg` face: no garbling / no truncation / no field-shuffle from the connection-token rewrite | P+N | **co-landing** |

**Gap G4 — the port-parametrized poll-shape web fixture (fixture work, `target: /qa` self-resolved
+ /dev/`/port` co-land).** The exemplar's `main.cl` hard-codes port 8080 (un-editable by `/qa`);
the deferred + new web rows need a port-parametrized (env or arg-configured) poll-shape web server
fixture so multiple web e2e can run without colliding on 8080 — with each other AND with
`tests/exemplar_web.rs`. Two parts: (i) the **fixture** (a port-configurable poll-shape `main.cl`
+ the connection-handle `.cl` surface of FIXME 0465) co-lands with the /dev web wave (`/port` +
`/platform`); (ii) the **raw-process harness** (`/qa`-authored: mirror/factor `exemplar_web.rs`'s
`spawn_server`/`ServerGuard`/`http_request`, parametrized on port). If 8080 is still shared,
serialise the web suites via a nextest `web-serve` test-group (`max-threads = 1`) so concurrent
binds don't race. The existing `exemplar_web_server_serves_form_solution_and_not_found_over_http`
is the de-facto serve floor until the rewrite lands; §B7 keeps it green (or names its disposition
if the rewrite reshapes `main.cl`).

---

## §B6 — The read-line-concurrency precondition (A4d review Important I1)

**The precondition (carried from A4d /review, SPRINT.md §A4d close).** stdio `read-line` is a
`Commutative` `token-0` poll leaf → it takes the **no-admission** path, so nothing structurally
enforces the "at most one in-flight `read-line`" invariant its **process-global `STDIN_BUF` +
globally-`O_NONBLOCK`'d fd 0** assume. Correct under Chunk-A's serial serve loop (single in-flight);
at Chunk-B fan-out, two concurrently-admitted `read-line` strands would race on the shared buffer
(line-stealing/interleaving — the `Mutex` prevents UB, not the logical race). **The headline server
demo uses `web`, NOT concurrent stdin** — so this race is **NOT exercised** by the §B1–§B5 server
workload. The disposition is a /design-vs-/dev verdict:

- **IF `/design` corrects the `poll-support.md §3.1` claim** ("stdin's serial discipline is a host
  concern") to acknowledge token-0 imposes no admission → **documentation closure, NO test** (a
  usability finding, not a defect; the server demo never makes `read-line` concurrent).
- **IF `/dev` gives `read-line` a capacity-1 serial-stdin token** (`{token != 0, cardinality 1}`)
  so admission enforces the serial discipline → a **guard is warranted**:

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `read_line_serial_stdin_token_serialises_concurrent_reads` | e2e (synthetic) OR unit (`cranelisp-intrinsics`) | `nt` | IF `read-line` carries a capacity-1 serial-stdin token: two concurrently-admitted `read-line` strands **serialise** on that token (no `STDIN_BUF` interleaving / no line-stealing) — admission enforces the single-reader discipline. Authored ONLY under the /dev token-choice verdict | P+N | **conditional** (Gap G7 — depends on the /design-vs-/dev verdict; if the §3.1-doc-correction path is taken, this row is dropped and the finding closes by documentation) |

**Flag to `/sprint`:** route the I1 verdict (correct §3.1 [/design] vs serial-stdin token [/dev])
at the Chunk-B wave gate; `/qa` authors this row only if the token path is chosen. Either way the
server demo (web) is unaffected — this is a `read-line`-specific Chunk-B-reachability precondition,
not a server-demo gate.

---

## §B7 — Regression guards / invariants (Chunk B must not perturb the floor)

Chunk B adds fan-out + supervision + admission on top of the Chunk-A substrate; it must not
regress the Chunk-A green rows, the S95 blocking-carrier proofs, or the single-lane suite.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| the 4 `poll-pool` capacity rows (EXISTS, Chunk A: `same_token_capacity_n_poll…` / `…capacity_1_poll…` / `n_distinct_token_poll_capacity…` / `distinct_poll_effects_sharing_one_token…`) | e2e | `nt` | the Chunk-A poll-carrier capacity proofs stay GREEN — the *degree* throttle composes ON the §8.1 capacity pool (`min(capacity, degree)`), it does not replace or regress it | P | regression-replay |
| the 5 `concurrency_reactor.rs` rows (EXISTS, S94) | e2e | `nt` | the real-leaf reactor suspend/resume + overlap proofs stay GREEN — supervisor/admission do not perturb the await boundary | P | regression-replay |
| `stdio` mixed manifest (EXISTS, A4d: `concurrency_stdio_v7.rs` — `print` blocking + `read_line` poll in one v8 manifest) | e2e | `nt` | the mixed-platform cutover proof stays GREEN — Chunk B does not touch the stdio manifest | P | regression-replay |
| `exemplar_web_server_serves_form_solution_and_not_found_over_http` (EXISTS, S86) | e2e (raw-process) | `nt` | the full web serve matrix stays GREEN — **OR**, if the FIXME-0465 rewrite reshapes `exemplar/main.cl`, its disposition is named (rewritten in-place to the poll-shape fan-out server, still GREEN; `/port`-owned). The serve floor must not silently break | P | regression-replay (disposition-flagged) |
| the S95 blocking-carrier capacity guards (EXISTS, S95: `same_token_capacity_n_blocking…` / `…capacity_1_blocking…` / `distinct_blocking_effects_sharing…`) + the 3 two-pool guards | e2e | `nt` | the blocking-carrier capacity + two-pool routing proofs stay GREEN — Chunk B reuses the permit machinery, does not fork it | P | regression-replay |
| `chunk_b_no_new_public_api_edge_or_abi_bump_neg` | e2e | `nt` | Chunk B adds **no** new `cranelisp-types` / `cranelisp-platform` `public-api.txt` edge line and **no** `ABI_VERSION` bump: *degree*/global-budget ride the already-core `ConcurrencyDescriptor.global_budget`; the supervisor reuses `StrandEvent` (`#[non_exhaustive]`); the web connection-handle is `.cl` ADT + in-process node operands (FIXME 0465). Mirrors the Chunk-A `no_new_public_api_edge…` guard (`tests/concurrency_poll_edge_guards.rs`), extended to the Chunk-B surface | N | RED-first if a wave leaks an edge/ABI bump; else stays-green |
| single collapsed lane stays green | e2e + unit | `nt` | `cargo nextest run` (the one post-cutover lane) stays green beyond the named RED-first set — a genuine regression is any RED beyond the §B Stage-1 RED-first rows + the 1 known cold-start intermittent (`repl_introspection::imports_filter_neg_nonexistent_module_not_error`, the documented 30 s harness-cap heisenbug, NOT Chunk-B-caused) | P | regression-replay |

---

## §B8 — Flagged gaps shaping Chunk-B Stage-1 authoring

- **G5 — the §10.12/§12 spec anchors (`target: /spec`, in flight THIS Phase).** The launch-and-
  continue + supervisor + *degree* spec surface (0447 first half) is being authored by the sibling
  `/spec` agent now. The §B rows cite §10.12/§12 **provisionally**; `/qa` pins each `// spec:`
  back-trace to the as-landed anchor at Stage-1 authoring. The §10.12.4.1 capacity anchor is reused
  unchanged for the `min(capacity, degree)` composition rows.
- **G6 — the supervisor + backpressure interior seams (`target: /design` int + `/dev`).** The
  concrete `JoinSet`-handle / global-`Semaphore` / `min`-threading / `poll-fault` fixture-leaf
  names depend on the sibling `/design` int agent's Chunk-B reactor.md elaboration (in flight) +
  the /dev wave. The unit rows (§B2-unit, §B3-unit, §B4 `_neg`) + the `poll-fault` extended
  `poll-pool` leaf co-land WITH that wave; `/qa` authors to whichever seam lands (the `StrandEvent`
  supervisor-action variant name is a `#[non_exhaustive]` add — minor, /qa authors to the landed
  kind, the Chunk-A G2 precedent).
- **G7 — the read-line precondition verdict (`target: /sprint` to route; /design or /dev to
  resolve).** §B6: correct `poll-support.md §3.1` [/design, doc closure] vs give `read-line` a
  capacity-1 serial-stdin token [/dev, + a guard row]. `/qa` authors the §B6 row only under the
  token verdict. Not a server-demo gate (the demo uses web).
- **G4 — the port-parametrized web fixture (`target: /qa` self-resolved + /dev/`/port` co-land).**
  Restated from §B5 for the gate: the fixture is /dev/`/port`'s (the poll-shape port-configurable
  `main.cl` + the 0465 connection-handle `.cl` surface); the raw-process harness is `/qa`'s. The
  web rows co-land against it.

These are surfaced here (not filed as FIXMEs) per the Phase-3 constraint (edit only
`tests/plan/`); `/sprint` routes G5 to `/spec`, G6 to `/design` int + `/dev`, G7 to the wave gate,
G4 to `/qa` + /dev/`/port` at the Chunk-B wave gate.

---

## §B9 — Phase-3 (Chunk B) exit gate confirmation

`/qa` confirms it has enough from the ratified contracts (`effect-concurrency.md` §4/§5/§9/§10/§16
+ the Phase-2 gate rulings (b)/(d)/0442 + `reactor.md` §5/§2.8/§3 + `poll-support.md` §3.2/§3.4.5 +
FIXME 0465 + the reused `spec/10-io.md` §10.12.4.1 and the in-flight §10.12/§12) to draft the
Phase-5 (Chunk-B) Stage-1 failing tests. The sibling `/spec` (§10.12/§12) and `/design` (reactor
supervisor/backpressure + 0465 web interface) agents are authoring the remaining anchors THIS
Phase — the provisional-cite gaps (G5/G6) close at Stage-1 authoring.

**Counts (Chunk B): 19 functional rows + 7 §B7 regression guards = 26 rows** —
- **§B1 server-with-no-`spawn`** — 3 e2e (2 web co-landing P + 1 verify `_neg`).
- **§B2 supervisor** — 1 synthetic e2e RED-first (P+N) + 3 web co-landing e2e (2 P + 1 load-bearing
  `_neg`) + 2 intrinsics units (supervisor `JoinSet`+event P+N; not-silent `_neg`) = 6.
- **§B3 backpressure** — 1 synthetic e2e RED-first (degree-park P+N) + 2 intrinsics units
  (`min(capacity,degree)` P+N; global-Semaphore P) + 1 web co-landing e2e (`_neg` flood proxy) = 4.
- **§B4 launch-and-continue** — 1 synthetic e2e RED-first (overlap P) + 1 intrinsics unit
  (no-ferry `_neg`, load-bearing) + 1 intrinsics unit (structured-Par contrast, regression-replay) = 3.
- **§B5 deferred web** — 2 web co-landing e2e (poll accept/read roundtrip P; serve-equivalence P+N)
  + the Gap-G4 port-param fixture (fixture work, not a row).
- **§B6 read-line precondition** — 1 conditional row (authored only under the /dev token verdict).
- **§B7 regression guards** — 7 named (4 poll-pool collapsed + 5 reactor + stdio mixed +
  exemplar_web + S95 blocking collapsed + no-new-edge `_neg` + single-lane-green).

**e2e ↔ unit split (of the 19 functional rows):**
- **e2e (`/qa`-authored): 12** — **3 synthetic RED-first** (B2-syn, B3-syn, B4-overlap — writable
  QA-first Stage-1 Wave-1 against the extended `poll-pool`/launch fixtures) + **8 web co-landing**
  (B1a, B1b, B2a, B2b, B2c, B3-web, B5a, B5b — authored WITH the /dev web fixture wave, the
  deferred-Chunk-A-web precedent) + **1 verify pin** (B1c no-`spawn`).
- **unit (`/dev`/intrinsics-authored, named for surface completeness + mandatory-unit-per-fix): 6**
  — B2d (supervisor JoinSet+event), B2e (not-silent), B3b (`min(capacity,degree)`), B3c
  (global-Semaphore), B4b (no-ferry), B4c (structured-Par contrast). Co-land in
  `cranelisp-intrinsics` `#[cfg(test)]` with the /dev supervisor+backpressure wave.
- **conditional: 1** (B6a, /dev-token-verdict-gated).

### Open verdict for `/sprint` + user

The Chunk-B Stage-1 surface is **draftable now** for §B2-syn / §B3-syn / §B4-overlap (the 3
synthetic RED-first rows, QA-first against an extended `poll-pool` + launch-loop fixture) + B1c
(the no-`spawn` verify pin). The remaining e2e (the 8 web rows) + the 6 units + B6a **co-land**
with their /dev waves (the deferred-Chunk-A-web + S95-unit precedents), because they reference the
FIXME-0465 web interface / the supervisor+backpressure seams / the /dev read-line token-choice that
do not exist on HEAD — writing them now would break the single-lane build. Sequencing dependencies:

1. **Chunk B depends on Chunk A** (the demo fans out real poll `accept`/`read` leaves; the
   supervisor wraps real handler strands; bounded fan-out needs A's acquire-around-poll). Chunk A
   is COMPLETE — no substrate blocker.
2. **FIXME 0465 is the keystone** — the web connection-handle interface gates ALL §B1/§B2-web/§B5
   web rows + the Gap-G4 fixture. **Recommend `/sprint` sequence the 0465 /design (+/port +/platform)
   resolution + the port-param web fixture EARLY in the chunk** so the web acceptance rows have a
   real fan-out server to consume before /dev claims the chunk green (the Chunk-A Gap-G1 precedent:
   the synthetic rows are RED-first immediately; the headline-workload rows need the fixture).
3. **§B6 (read-line precondition)** needs the /sprint-routed I1 verdict (G7) before /qa knows
   whether to author the row (token path) or close by documentation (§3.1-correction path).
4. **The single collapsed lane** is the only lane post-cutover — no lane-blocker, no lane migration
   (the `concurrency-runtime` feature is gone; the reactor is always present).

## Phase-3 (Chunk B) plan record (`/qa` 2026-06-29)

Plan authored against the Chunk-B contracts above; the sibling `/spec` (0447 first half §10.12/§12)
and `/design` (reactor supervisor/backpressure + FIXME-0465 web interface) agents are authoring the
co-requisite anchors in parallel THIS Phase — the provisional-cite gaps (G5/G6) close at Stage-1.
No test code yet (Phase 5). A `tests/plan/ledger.md` entry mirroring the Chunk-B RED-first set will
be added at Chunk-B Stage-1 close.

## Wave-B1 landing record (Phase-5 Chunk-B Stage-1, `/qa` 2026-06-29 — ACTUAL)

The as-landed record of the QA-first wave. Per the Chunk-A precedent + the task constraint
("keep the build COMPILABLE + suite RUNNABLE after B1"), Wave-B1 authors ONLY the black-box e2e
rows that compile as Rust and run RED today; the unit rows + web rows co-land with their /dev
crate waves. No `#[ignore]`; every test carries a `// spec:` ref.

### B1-LANDED — e2e file (`/qa`): `tests/concurrency_fanout.rs` (un-gated, runs in `nt`)

The single new file, the post-cutover single-lane `nt`. 4 rows; the 3 synthetic RED-first rows
were validated against the stale `target/debug/cranelisp` (the Chunk-A-complete / Chunk-B-not-
started binary — see the build-blocker note below) since the workspace currently does not compile:

- §B1c `web_server_no_user_spawn_primitive_neg` — **GREEN verify pin** (bare-REPL probes of
  `spawn`/`go`/`async`/`thread` all → `undefined variable`; failing-not-ignored-faithful).
- §B2-syn `detached_faulting_effect_does_not_abort_the_launch_loop` — **RED-first**, clean runtime
  signal `'poll-fault' not found in module 'platform.poll-pool'` (Gap-G6 leaf + supervisor are
  co-landing /dev deliverables).
- §B3-syn `degree_n_bounds_inflight_launched_effects_nplus1_parks` — **RED-first**; M=4/N=2
  distinct tokens; ~180ms ≈ 1·D measured (degree unenforced ⇒ all overlap ⇒ < 225ms lower bound).
  `CRANELISP_DEGREE` is the provisional degree surface (Gap G6; §10.12.4.2 — degree is
  implementation-defined config, reconcile at the /dev backpressure wave).
- §B4 `launch_and_continue_runs_concurrently_launcher_does_not_await` — **RED-first**; the
  canonical **tail-recursive accept-loop** shape (K=5 launches), NOT a flat `(do slow fast)`
  (which structured auto-IO-parallel would overlap too — false-green). ~789ms ≈ 5·D serial
  measured (each `bind` awaits, no fan-out ⇒ > 450ms upper bound).

> **Free-standing-test note.** The prelude `do` macro is NOT available to free-standing tests
> (root `CLAUDE.md` §"Stdlib separation"); the launch-and-continue / supervisor candidate shape
> is therefore expressed with `bind` + an unused continuation binder — exactly what `do`
> desugars to, and what `concurrency_poll_capacity.rs` already uses.

### Co-landing rows owned by later /dev waves (named for surface completeness)

Reference types/programs absent on HEAD (the FIXME-0465 web interface, the supervisor `JoinSet`
seam, the `poll-fault` fixture leaf, the port-param web fixture); authoring them now would break
the single-lane build. They co-land WITH their /dev wave (the deferred-Chunk-A-web + S95-unit
precedents):

- **B-web co-landing** (the FIXME-0465 web rewrite + Gap-G4 port-param fixture): §B1a
  `web_server_fans_out_concurrent_requests_overlap`, §B1b
  `web_server_serves_single_roundtrip_under_fanout_loop`, §B2-web ×3
  (`web_handler_fault_yields_error_response_for_that_request`,
  `web_server_survives_handler_fault_continues_serving`,
  `web_handler_fault_does_not_kill_accept_loop_neg`), §B3-web
  `web_server_bounded_inflight_under_request_flood_neg`, §B5 ×2
  (`web_poll_accept_read_serves_one_roundtrip`,
  `web_poll_server_serves_response_equivalent_to_reference`). `/qa` adds these against the
  port-safe fixture once the web wave lands (serialise with `exemplar_web.rs` via a `web-serve`
  nextest group if 8080 is still shared).
- **B-intrinsics co-landing** (`cranelisp-intrinsics` `#[cfg(test)]`, the supervisor +
  backpressure /dev wave): §B2-unit ×2 (`supervisor_owns_detached_strand_catches_panic…`,
  `supervised_drop_is_not_silent_neg`), §B3-unit ×2 (`effective_permits_is_min_capacity_degree…`,
  `global_admission_semaphore_bounds_total_inflight_detached_strands`), §B4-unit ×2 (`detached_
  strand_fault_does_not_ferry_into_launcher_neg` — the load-bearing no-ferry `_neg`;
  `structured_par_first_error_still_re_raises_contrast` — regression-replay). These are
  **NOT** authored in B1 per the task ("Do NOT write unit rows referencing types/fns that don't
  exist yet").
- **§B6 conditional** `read_line_serial_stdin_token_serialises_concurrent_reads` — authored only
  under the /dev serial-stdin-token verdict (Gap G7, /sprint-routed).

### Ratifications (`/qa` Wave-B1)

- **A4d timing-window recalibration RATIFIED** (`tests/concurrency_poll_capacity.rs`, D_MS 60→150,
  exit 180→194). Verified each assertion's discriminating intent survives: at D=150 the three
  regimes are 180/330/480ms with windows 1.5·D=225 / 2.5·D=375 — §1B overlap ~330 ∈ (225,375),
  §1C serial ~480 > 375, §1D distinct ~180 < 225, §1D shared ~330 ∈ (225,375); the ~30ms fixed
  poll-carrier overhead sits comfortably inside every window (was ~50% of one D at D=60, flaking
  the §1B ceiling). exit 194 = 3·150 & 0xFF, arithmetic. A `// qa-ratified S96 B1:` note is in the
  file at the `D_MS` tuning block. **Verdict: RATIFIED — no window collapse.**
- **`ensure_platform_cdylibs_built()` neutralization RATIFIED** (`tests/examples.rs` +
  `tests/platform_errors.rs`). No coverage hole: the platforms the helper formerly built per-test
  (`stdio`, `test-capture`) are both in `tests/scripts/build-link-prereqs.sh`'s single
  `cargo build -p …` (9 platforms), so the IO examples (21-24) + the platform-error tests still
  resolve their DLLs; the call sites are preserved (inert). The retired per-test `cargo build` was
  the forbidden band-aid that broke parallel `--link` with mismatched crate disambiguators under
  the single-ABI cutover. A `// qa-ratified S96 B1:` note is at each helper. **Verdict: RATIFIED.**

### BUILD BLOCKER (flag to `/sprint` — NOT caused by the B1 rows)

`cargo nextest run` **could not be run** at Wave-B1 close: the workspace does not compile. The
shared tree carries **in-flight /dev Chunk-B work** that added `MonoExpr::LaunchContinue`
(`crates/cranelisp-types/src/mono_expr.rs`) and `Expr::LaunchContinue`
(`crates/cranelisp-types/src/ast.rs`) but left consuming `match` sites **non-exhaustive** in
`cranelisp-typecheck` (3 sites) and `cranelisp-backend` (5 sites: `compiler/control_flow/
free_vars.rs:27`, `compiler/fn_compiler.rs:411`, `heap.rs:628`, `lib.rs:720`, `lib.rs:804`) ⇒
`error[E0004]: non-exhaustive patterns`. This is **NOT** caused by `/qa`'s B1 changes (a new e2e
test binary + comments cannot cause a lib `match` error); it is the partially-applied
launch-and-continue /dev lowering. Until `/dev` completes those arms the suite cannot build or
run, so the B1 RED/green postures above were verified against the **stale `target/debug/cranelisp`
binary** (built 2026-06-29 05:51, pre-LaunchContinue = the Chunk-A-complete baseline the RED-first
rows target). **Action: `/sprint` route the build-fix to `/dev` (cranelisp-typecheck +
cranelisp-backend); re-run `cargo nextest run` once green to confirm the B1 postures + the
Chunk-A 1716 baseline.** `/qa` did not edit `crates/src/` (ownership boundary).

### Measured suite state (Wave-B1 close)

- **`cargo nextest run`** — **UNAVAILABLE** (workspace non-compiling, see the BUILD BLOCKER). The
  expected post-fix state: the 1 GREEN verify pin + the Chunk-A 1716 baseline stay green; the 3
  new synthetic RED-first rows fail (validated RED against the stale binary). A `tests/plan/
  ledger.md` entry will be added once the build is restored and the suite re-run confirms it.

<!-- ========================================================================= -->
<!-- ============================ CHUNK C ==================================== -->
<!-- ========================================================================= -->

# CHUNK C — Cancellation + combinator layer (`race`/`select`/`timeout` + structured cancellation — the explicit control surface)

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests land in
**Phase 5 Chunk-C Stage 1** (QA-first, before the per-crate D/D/R waves). This section
extends the Chunk-A + Chunk-B plans above (same row-per-requirement format) with the Chunk-C
surface.

> **CHUNK-DELIMITED.** This section covers **CHUNK C ONLY** — slice 7: the user-facing control
> combinators `race`/`select`/`timeout` + **structured cancellation**. Chunk C **exercises the
> A→C RAII-Permit-release-on-drop contract** that Chunk A *built* (§2/§2B above — `dropping_
> inflight_poll_releases_permit_next_waiter_proceeds` is its load-bearing intrinsics-unit
> predecessor; Chunk C adds the source-level-cancellation e2e exercise) and lands the **two A3-
> review Chunk-C prerequisites** (the findings the chunk is gated on — see "Chunk-C
> prerequisites" below). Chunk A+B are **COMPLETE** (substrate + supervisor + backpressure +
> the v8 web platform; suite **1726/1726 / 1 skip**). The Chunk-B **concurrent per-connection
> fan-out** is **WALLED on FIXME 0470** (interprocedural launch analysis — `handle-conn` is a
> user fn `classify_expr` treats as `Sequential`); the cancel-on-disconnect + graceful-shutdown
> **web-e2e** rows depend on that fan-out and are therefore **deferred with 0470** (§C5 below) —
> the **synthetic / direct-effect** cancellation rows (§C1–§C4 + §C5a) carry the Chunk-C
> acceptance WITHOUT the fan-out.

---

## The two Chunk-C prerequisites (the A3 adversarial-review findings the chunk is gated on)

The A3 `/review` (`SPRINT.md` §"A3 review", 2026-06-29) accepted the Chunk-A acquire-around-poll
+ RAII `Permit` drop-guard as Chunk-A-correct but surfaced **two Important findings that are
load-bearing for Chunk C** — both latent in the S95 pool machinery A3 deliberately left
unchanged: memory-safe and benign for one-shot `--run`/REPL, but they **bite under Chunk C's
deliberate, high-volume cancellation in a long-running reactor** (`SPRINT.md` §"Chunk-C design
prerequisites"). **The §C4 cancellation rows are exactly the rows that prove these two findings
neither leak nor lost-wake at volume:**

- **Finding #3 — active reactor-interest deregistration on `EffectPoll` drop.** On HEAD a
  dropped-mid-flight `EffectPoll` that armed **real fd/timer interest** leaves its `fd_waiters`
  / `timer_waiters` entry + live `mio` registration + `OwnedCWaker` clone in place **until that
  fd next readies** (or for the whole drive, if it never does). Memory-safe (the stored waker is
  the executor task waker, not a pointer into the future — a stale `turn()` fire just re-polls
  the top future), and it does **not** deadlock (`block_on_reactor` returns on the TOP future's
  completion, not `has_waiters()`) — but it is a **within-drive resource leak** that is bounded
  for a one-shot drive and **unbounded under Chunk C's per-request cancellation in a never-ending
  server loop**. Chunk C requires an `EffectPoll`-owned reactor-registration handle whose `Drop`
  **actively removes** the `fd_waiters`/`timer_waiters` entry + mio-deregisters (the literal
  active-deregistration the §2B plan row named; §2.9 to record the Chunk-A→Chunk-C handoff).
- **Finding #4 — `AcquirePermit` cancellation stale-waker lost-wakeup.** There is **no `Drop for
  AcquirePermit`** on HEAD (only `Drop for OwnedCWaker` and `Drop for Permit`). A future cancelled
  **while parked awaiting a permit** (Chunk C cancels a future that is waiting *for* a permit,
  before it acquires) leaves a **stale waker in the FIFO**; a later `Drop for Permit` does
  `pop_front()` + wakes that **dead** waker (no-op) while the freed permit goes **unclaimed** and
  the **next live** waiter is never woken ⇒ **lost-wakeup / a free permit nobody can take**.
  Unreachable in Chunk A (no cancellation); Chunk C hits it. Chunk C needs either `Drop for
  AcquirePermit` (remove own waker from the FIFO on cancel) or **pop-until-live** release
  semantics (skip dropped / `will_wake`-stale wakers).

Per the reviewer these are **Chunk-C-prerequisites, not A3 reworks** — folded into Chunk C's
`/design` int (reactor) pass, NOT standalone FIXMEs (the crates were mid-flight). **§C4b pins
finding #3; §C4d pins finding #4; §C4c / §C4e are their volume (e2e) faces.**

## Scope source + contracts of record (Chunk C)

**Scope source:** `sprints/SPRINT.md` S96 item 6 (slice 7 — `race`/`select`/`timeout` +
structured cancellation) + the **Chunk C** partition entry's **Witnessable** bullet ("per-request
**timeout** fires and cancels the loser (releasing its permit); `race`/`select` pick the winner;
**cancel-on-disconnect** + **graceful shutdown**") + the Phase-2 **gate (a)** ruling (the A→C
RAII-Permit-release-on-drop contract is **verified here**) + the A3-review findings #3/#4 (above).

**Contract of record:**
- `design/arch/effect-concurrency.md` **§9** (the control half — the combinators are **ordinary
  typed functions that construct trampoline-interpreted IO-ADT nodes**, the same class as `Par`;
  NOT special forms, NOT platform effects — platforms never see them; the irreducible primitive
  set is **`race`/`select` + structured cancellation**, everything else derived: `timeout d io =
  race io (sleep d)` is stdlib-derivable; `cancel` is **not** a standalone combinator — it is the
  *consequence* of losing a race / exiting a scope = **drop the future**; indicative signatures
  `race : IO a -> IO a -> IO a`, `timeout : Duration -> IO a -> IO (Option a)`, `select : List
  (IO a) -> IO a`; "separable but **committed**" — per-request timeout / cancel-on-disconnect /
  graceful shutdown are what let a server survive an uncooperative open-internet boundary) /
  **§10** (supervisor — the §C5 reference patterns) / **§11** (observability — the **cancellation**
  event: "race loser / timeout fired → what was cancelled" — the strand-sink trace).
- `design/int/reactor.md` — the Chunk-C cancellation interior, **being authored by the sibling
  `/design` int agent THIS Phase** (Gap G9): **finding #3** (the `EffectPoll`-owned reactor-
  registration handle whose `Drop` deregisters `fd_waiters`/`timer_waiters` + mio) + **finding #4**
  (`Drop for AcquirePermit` / pop-until-live release) folded into the Chunk-C design pass, plus
  the `race`/`select` IO-node-tag cancellation semantics (first-Ready ⇒ drop the loser future(s)
  ⇒ their RAII `Permit`s + reactor-interest handles release). The §2.8 lock-free single-reactor-
  thread permit-map invariant holds verbatim under cancellation (all drop/release events are
  reactor-thread events). §2.9 records the Chunk-A→Chunk-C handoff (Chunk A: permit-only release;
  Chunk C: active reactor-interest deregistration + `AcquirePermit` cancel-safety).
- `design/backend/io-trampoline.md` — the **combinator node codegen** (the new `race`/`select`
  IO node tags — in-process backend↔intrinsics node convention, the `IO_TAG_EFFECT_POLL` /
  `Par`-node precedent; pinned-const node tags, off the default public edge), being authored THIS
  Phase (Gap G9).

**Spec of record (0447 second half — `/spec` actioning THIS Phase):** the typed control-
combinator layer is the **only** remaining open half of FIXME **0447** (the §12 launch-and-
continue / supervisor / degree first half landed in Chunk B → §10.12.7 / §10.12.4.2 / §12.7.9).
`spec/10-io.md` **§10.12.6 item 3** already names it "a **committed but not-yet-specified**…
typed control-combinator layer (`race`/`select`, structured cancellation, and a derived
`timeout`)… specified **when it surfaces**, not before. Until then no program may rely on the
combinator surface." Chunk C IS that surfacing ⇒ the sibling `/spec` agent authors the
`race`/`select`/`timeout` typing + **structured-cancellation** semantics this Phase. The §C rows
cite the combinator/cancellation anchors **provisionally** (Gap G8 — provisional anchors
`spec/10-io.md §10.12.8` "Control Combinators" + `spec/12-runtime.md §12.7.10` "Structured
Cancellation"; `/qa` pins each `// spec:` back-trace to the as-landed anchor at Stage-1
authoring, the Chunk-B G5 precedent). The §10.12.4.1 capacity anchor + §10.12.7 detached-strand
anchor are **reused unchanged** for the permit-release-on-cancel + graceful-shutdown rows.

**Public-api / ABI of record (post-single-ABI-cutover):** per the Phase-2 ruling and the cutover,
**NO new `cranelisp-types` / `cranelisp-platform` `public-api.txt` edge line, NO `ABI_VERSION`
bump**. `race`/`select` are **new in-process IO node tags** (backend↔intrinsics convention,
pinned consts off the default edge — the `IO_TAG_EFFECT_POLL` precedent); `timeout` is **derived
`.cl`** (`race io (sleep d)`); cancellation **lights up the already-reserved `drop_state`**
(landed S94) + the future-drop RAII path Chunk A built — no new constructor on any default edge.
Combinators are **runtime-internal** (platforms never see them — §9), so there is **no platform-
ABI surface at all**. §C6 carries the no-new-edge guard.

## Conventions / legend (Chunk C)

- **Lane** — `nt` (the single collapsed `cargo nextest run`; the reactor is always present post-
  cutover via the eager-cheap fallback — the `concurrency`/`concurrency-runtime` features are
  retired). Unit rows run via `-p cranelisp-intrinsics` (still inside `nt`). Chunk-C rows are
  **un-gated** (no `#![cfg(feature = …)]`), the Chunk-B precedent.
- **Tier** — `e2e` (`/qa`-authored, subprocess via the `Cranelisp` builder run-to-completion for
  synthetic combinator programs; **raw-process** per `tests/exemplar_web.rs` for the deferred web
  rows) / `unit` (`/dev`-authored `#[cfg(test)]` in the owning crate, named here for surface
  completeness + the mandatory-unit-per-fix discipline).
- **Posture** — `RED-first` (a failing guard the /dev wave flips green; an absent combinator /
  capability / fixture leaf is a clean **runtime-RED** on HEAD — `--run` errors "undefined:
  race" / "`poll-block` not found", NOT a compile break, since e2e shell out to the binary) /
  `co-landing` (authored WITH the /dev wave that lands the type/leaf — referencing types/fns
  absent on HEAD would break the workspace build, so these are authored in-wave, the S95 + Chunk-A
  + Chunk-B precedent) / `deferred` (a row whose acceptance needs the FIXME-0470 fan-out — named,
  not authored, until 0470 unblocks) / `regression-replay` (an existing guard that must stay
  green).
- **P/N** — positive (correct behaviour appears) / negative (wrong behaviour absent).

> **The e2e ↔ unit ↔ synthetic-vs-web split (the Chunk-C sequencing).** The Chunk-A/B precedent
> stands: **synthetic e2e first (QA-first, black-box) against the existing `poll-pool` leaves +
> the new `race`/`select` surface, units co-land with their /dev crate wave, keep the build
> compilable.** Chunk C has THREE row flavours: (1) **synthetic RED-first e2e** (§C1–§C4 + §C5a)
> that witness `race`/`select`/`timeout` + the findings-#3/#4 cancellation through the existing
> `poll-read`/`poll-log` capacity leaves + the new combinator surface (+ ONE new `poll-block`
> never-readying-fd leaf for the finding-#3 leak observable, Gap G10) — clean runtime-RED on HEAD
> (the combinators / leaf are absent), authorable QA-first in Stage-1 Wave-1; (2) **intrinsics
> unit** rows (§C1-unit, §C4b, §C4d — the race-node loser-drop, finding #3's active
> deregistration, finding #4's `AcquirePermit` cancel-safety) co-landing in `cranelisp-intrinsics`
> `#[cfg(test)]` with the /dev cancellation wave; (3) **web e2e** rows (§C5b/§C5c cancel-on-
> disconnect + graceful shutdown) that need the **FIXME-0470 concurrent fan-out** — **deferred
> with 0470**. The synthetic rows are the QA-first acceptance the per-crate triads make green;
> the findings #3/#4 rows are the load-bearing volume proofs the chunk is gated on.

---

## §C1 — `race` (first-to-complete wins; the loser is CANCELLED)

**Acceptance (arch §9 + Witnessable).** `race : IO a -> IO a -> IO a` runs two effects, the
**first to complete wins and its value is returned**; the **loser is cancelled** — `cancel` is
the *consequence* of losing the race = **drop the loser's future** (§9), which (per the A→C RAII
contract, gate (a)) releases its `Permit` AND (per finding #3) deregisters its reactor interest,
and (crucially) means the loser's **completion side-effect never occurs** (it is dropped before
`Poll::Ready`). The loser-cancellation is the load-bearing half — a race that ran both to
completion would be a `Par`, not a `race`.

### C1-syn — synthetic RED-first (the winner-value + loser-cancellation core)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `race_returns_first_completed_value` | e2e (synthetic) | `nt` | `(race (poll-read tok cap FAST) (poll-read tok cap SLOW))` with FAST ≪ SLOW returns the **FAST** branch's value; wall-clock ≈ FAST (≪ SLOW) — the slow branch did not gate completion. The winner-value half | P | **RED-first** (`race` is an absent IO-node-tag surface — clean runtime-RED "undefined: race"; Gap G8/G9) |
| `race_loser_completion_side_effect_absent_neg` | e2e (synthetic) | `nt` | `(race (poll-log tok cap FAST "win") (poll-log tok cap SLOW "lose"))`: only the WINNER's `"win"` tag prints to stdout; the LOSER's `"lose"` tag **does NOT appear** — the loser was cancelled (future dropped) **before** its `Poll::Ready` print phase. **The load-bearing `_neg`** — a race that ran both to completion (a `Par`) would print BOTH tags | P+N | **RED-first** (load-bearing; Gap G8/G9) |
| `race_loser_releases_resource_permit` | e2e (synthetic) | `nt` | the A→C RAII contract's **e2e exercise** (the named Chunk-C e2e for §2B). On a **shared capacity-1 token**: `(bind (race (poll-read T 1 FAST) (poll-read T 1 SLOW)) (fn [_] (poll-read T 1 D)))` — after the race resolves (FAST wins, SLOW cancelled), the trailing same-token `poll-read` proceeds **immediately** (wall-clock ≈ FAST + D, NOT FAST + SLOW + D) — proving the cancelled loser **freed its permit** on drop. A leaked loser permit would leave capacity-1 exhausted ⇒ the trailing read would wait out SLOW ⇒ the upper-bound fails | P+N | **RED-first** (the A→C contract Chunk C exercises; Gap G8/G9) |

### C1-unit — the race-node loser-drop machinery (intrinsics co-landing)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `race_node_on_first_ready_drops_loser_future_releasing_permit` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | the `race` IO node, on the **first** branch's `Poll::Ready`, **drops** the other branch's `EffectPoll` future ⇒ its RAII `Permit` releases (`permits` increments + front FIFO waiter woken) AND its reactor-interest handle deregisters (finding #3) — i.e. the winner's value is returned AND the loser's resources are reclaimed in one step. The negative face: the loser's `Poll::Ready` body never runs (the future is dropped, not awaited) | P+N | **co-landing** (the race-node cancellation seam — Gap G9; depends on the /dev combinator wave) |

---

## §C2 — `select` (returns WHICH branch won + its value; distinct from `race`)

**Acceptance (arch §9 + 0447 second half).** `select : List (IO a) -> IO a` — like `race` but over
an N-way list and (per the /spec design surfacing this Phase) **reports which branch won** (its
index / a tagged winner), where `race` returns only the value. The other branches are cancelled
exactly as a race loser is (drop ⇒ permit + interest release). The distinction from `race` is the
load-bearing half (else `select` would be redundant with a fold of `race`).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `select_returns_winning_branch_and_value` | e2e (synthetic) | `nt` | `(select [(poll-read t0 cap SLOW) (poll-read t1 cap FAST) (poll-read t2 cap SLOW)])` (distinct tokens, overlapping) resolves to the **index-1** (FAST) winner **and** its value, per the /spec winner-reporting shape; wall-clock ≈ FAST. The losers (indices 0,2) are cancelled | P | **RED-first** (`select` absent IO-node-tag surface; the exact winner-report shape pins at Gap G8) |
| `select_reports_winner_index_distinct_from_race_neg` | e2e (synthetic) | `nt` | `select` reports **which** branch won (an observable index/tag), whereas `race` reports only the value — the two are **distinct** combinators (the `_neg`: `select`'s result is NOT just the bare value `race` would give; the winner identity is recoverable). Authored to whichever winner-reporting shape `/spec` lands (Gap G8) | N | **RED-first** (Gap G8 — the `select` winner-report shape) |

---

## §C3 — `timeout` (`timeout d io`: completes-in-time → result; exceeds → timeout indication + io CANCELLED)

**Acceptance (arch §9 + 0447 second half).** `timeout : Duration -> IO a -> IO (Option a)` —
**derived**: `timeout d io = race io (sleep d)`. If `io` completes **before** `d` → `(Some result)`;
if `io` **exceeds** `d` → the timeout fires, returns the **timeout indication** (`None`), and
**cancels `io`** (drops its future ⇒ permit + interest release; its completion side-effect never
occurs). A **wall-clock two-sided window** (the capacity-park style), exactly as the §1B/§B3 timed
rows.

> **Free-standing-test note (Gap G10).** `timeout` is **derived `.cl` stdlib** (`race io (sleep
> d)`) and tests MUST NOT depend on `stdlib/` (root `CLAUDE.md` §"Stdlib separation"). So the §C3
> rows express `timeout` **inline** as `(race io (poll-read sleep-tok cap d))` — the existing
> `poll-pool` `poll-read` IS an armed-timer "sleep that returns its `ms`", so the derived form is
> constructible from the combinator surface + the existing leaf with ZERO stdlib dependency. If
> `/spec`/`/stdlib` land a first-class `timeout` returning `(Option a)`, `/qa` re-points the rows
> to it (and the `Option`-discriminating assertion); until then the inline `race`-form carries the
> acceptance.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `timeout_io_completes_before_deadline_returns_result` | e2e (synthetic) | `nt` | `(timeout D_LONG (poll-read tok cap D_SHORT))` with D_SHORT ≪ D_LONG returns the io's result (the `(Some …)` arm, or the io value via the inline `race` form); wall-clock ≈ D_SHORT (`< D_LONG`) — the io won, the deadline did not fire. Two-sided window (`> 0.5·D_SHORT` AND `< D_LONG`) | P | **RED-first** (`race`/`timeout` absent; Gap G8/G9) |
| `timeout_io_exceeds_deadline_fires_and_cancels_io_neg` | e2e (synthetic) | `nt` | `(timeout D_SHORT (poll-log tok cap D_LONG "io"))` with D_LONG ≫ D_SHORT → the timeout **fires** (returns the timeout indication / `None`, or the deadline branch via the inline `race`), wall-clock ≈ D_SHORT (`< D_LONG` — did NOT wait out the io), **AND the io is CANCELLED**: its `"io"` Ready-phase tag **does NOT appear** in stdout (dropped before completion). **The load-bearing `_neg`** — a timeout that let the io run to completion would print `"io"` and take ≈ D_LONG. Two-sided window (`> 0.5·D_SHORT` AND `< D_LONG`) | P+N | **RED-first** (load-bearing; Gap G8/G9/G10) |

---

## §C4 — Structured cancellation at volume (the load-bearing findings #3 / #4 rows)

**These are the rows the chunk is gated on** (the A3-review prerequisites — see "The two Chunk-C
prerequisites" above). They prove cancellation **at volume** in a long-running reactor neither
**leaks** (finding #3: a cancelled poll deregisters its fd interest — no `fd_waiters` growth) nor
**lost-wakes** (finding #4: a future cancelled while parked awaiting a permit does not strand the
next live waiter or the freed permit). §C4a is the A→C permit-release contract's standalone e2e;
§C4b/§C4d are the direct unit pins (the in-memory `fd_waiters` / FIFO assertions not subprocess-
observable); §C4c/§C4e are their volume e2e faces (the bounded-completion proxy).

### C4a — a cancelled in-flight poll releases its permit; the next waiter on that token proceeds (e2e)

The A→C contract completion (gate (a)), standalone. (Distinct from §C1c, which exercises it
*through* `race`; §C4a is the same contract through `timeout`-cancel and asserts the **next live
waiter** specifically.)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `cancelled_inflight_poll_releases_permit_next_waiter_proceeds_e2e` | e2e (synthetic) | `nt` | on a **shared capacity-1 token**, a `timeout`-cancelled in-flight `poll-read` (deadline fires before it readies) **releases its permit**, and a concurrently-parked **next waiter** on the SAME token (a second same-token effect that was parked awaiting the permit) **proceeds** to completion — the A→C contract end-to-end. A leaked permit would leave the next waiter parked forever ⇒ the program hangs (caught by the harness 30 s cap = a loud RED). Wall-clock ≈ deadline + the waiter's D | P+N | **RED-first** (the A→C contract; Gap G8/G9) |

### C4b — finding #3: a cancelled poll DEREGISTERS its fd interest (no `fd_waiters` leak) — unit + volume e2e

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `dropping_armed_fd_poll_deregisters_reactor_interest` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | an `EffectPoll` that **armed real fd/timer interest** (registered an `fd_waiters`/`timer_waiters` entry + a live `mio` registration), dropped **mid-flight** (parked, not yet `Ready`), **actively removes** its `fd_waiters`/`timer_waiters` entry + mio-deregisters on `Drop` (the finding-#3 `EffectPoll`-owned registration handle). The negative face: after the drop the reactor's `fd_waiters` map does **NOT** still contain the dropped future's entry (no orphaned waiter persisting until the fd readies) | P+N | **co-landing** (finding #3 — RED-first: HEAD has NO active deregistration, the A3-review-confirmed gap; Gap G9) |
| `volume_cancellation_does_not_leak_fd_waiters_bounded` | e2e (synthetic) | `nt` | a **long loop** that races/`timeout`-cancels **many** (≥ 200) in-flight poll effects each arming **real fd interest** (the new `poll-block` never-readying-fd leaf, Gap G10) over a **long-running reactor** completes in **bounded wall-clock** and **exits 0** — the "cancel many → no unbounded waiter growth" observable (the e2e proxy for finding #3; the direct `fd_waiters`-count assertion is the unit row above). On HEAD (no active deregistration) the `fd_waiters` map + mio registrations grow without bound across the loop ⇒ unbounded memory / slowdown ⇒ the wall-clock ceiling fails (or OOM) | N | **RED-first** (finding #3 volume face; needs `poll-block`, Gap G10) |

### C4c — finding #4: a future cancelled while parked awaiting a permit does NOT lost-wake — unit + volume e2e

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `dropping_acquirepermit_while_parked_does_not_lost_wake` | unit (`cranelisp-intrinsics`) | `nt` (`-p`) | over a fixture capacity-1 token with the permit held: TWO `AcquirePermit` waiters park in the FIFO; **cancel the FRONT waiter while it is parked** (drop its `AcquirePermit`); then release the held permit. The **next LIVE waiter** (the second) is woken and acquires, and the freed permit is **claimed** — NOT lost to the stale front waker. The negative face: a `pop_front()` that woke the dead front waker (no-op) while the live second waiter stayed parked is the lost-wakeup this guards. Requires `Drop for AcquirePermit` (remove own waker on cancel) OR pop-until-live release | P+N | **co-landing** (finding #4 — RED-first: HEAD has NO `Drop for AcquirePermit`, the A3-review-confirmed gap; Gap G9) |
| `volume_cancel_while_awaiting_permit_next_live_waiter_proceeds` | e2e (synthetic) | `nt` | over a **capacity-bounded** token where many effects **park awaiting a permit**, repeatedly `timeout`/race-cancel a **parked-awaiting-permit** future at **volume** (≥ 200): every cancellation is followed by the **next live waiter proceeding** — the loop completes + **exits 0**, no deadlock, no unclaimable permit. On HEAD (no `AcquirePermit` cancel-safety) a cancelled parked waiter strands its successor + the freed permit ⇒ the loop hangs (harness 30 s cap = loud RED) | P+N | **RED-first** (finding #4 volume face; Gap G9) |

---

## §C5 — cancel-on-disconnect + graceful shutdown (the §10 reference patterns)

**Acceptance (arch §9/§10 + Witnessable).** Two §10 reference patterns: a **disconnected
handler is cancelled** (cancel-on-disconnect — the client drops the connection ⇒ its in-flight
handler poll is cancelled, resources released); **graceful shutdown cancels outstanding strands**
(SIGTERM/shutdown ⇒ the outstanding handler strands are cancelled, the server drains + exits). The
**web** variants need the **concurrent per-connection fan-out** (multiple outstanding handler
strands to cancel) — which is **WALLED on FIXME 0470** (`handle-conn` is a user fn `classify_expr`
treats as `Sequential`, so the serve loop runs **serially**; `SPRINT.md` 2026-06-29 wall record).
**Therefore the web-e2e rows §C5b/§C5c are DEFERRED with 0470**; the **synthetic** graceful-
shutdown core (§C5a) — which needs no fan-out — carries the §10-pattern acceptance this chunk.

### C5a — synthetic graceful-shutdown core (no fan-out; the deferrable-independent acceptance)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `shutdown_cancels_outstanding_inflight_effect_releasing_resources` | e2e (synthetic) | `nt` | a **shutdown trigger** (modelled as a `race` of an in-flight `poll-block`/`poll-log` against a short-deadline "shutdown signal" `poll-read`) **cancels** the outstanding in-flight effect: its completion side-effect **does NOT occur** (its tag absent) AND its resource releases (a trailing same-token effect proceeds immediately — permit freed). The synthetic core of "shutdown cancels an outstanding strand" — no web/HTTP, no fan-out. Two-sided wall-clock window | P+N | **RED-first** (the §10 graceful-shutdown pattern via the combinator surface; Gap G8/G9/G10) |

### C5b/C5c — the web reference patterns (DEFERRED with FIXME 0470 — need the concurrent fan-out)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `web_handler_cancelled_on_client_disconnect` | e2e (raw-process) | `nt` | a client that **disconnects mid-request** has its per-connection handler **cancelled** — the in-flight handler poll is dropped, its resources (connection fd interest + any permit) released, and the server keeps serving subsequent requests. **The cancel-on-disconnect §10 pattern** | P+N | **DEFERRED → FIXME 0470** (needs the concurrent per-connection fan-out — a detached supervised handler strand to cancel; the serve loop is SERIAL until 0470's interprocedural launch analysis unwalls the fan-out. Co-lands with the 0470 resolution + the Gap-G4 port-param web fixture; `/sprint` routes) |
| `web_server_graceful_shutdown_cancels_outstanding_handler_strands` | e2e (raw-process) | `nt` | on a shutdown signal the server **cancels its outstanding handler strands** (their in-flight polls dropped, resources released), drains, and **exits cleanly** (no hang, no leaked strand) — **the graceful-shutdown §10 pattern at the server level** | P+N | **DEFERRED → FIXME 0470** (needs ≥ 1 outstanding *concurrent* handler strand to cancel — only exists under the fan-out; §C5a is the synthetic stand-in until 0470 unwalls it) |

---

## §C6 — Regression guards / invariants (Chunk C must not perturb the floor)

Chunk C adds the combinator surface + cancellation on top of the Chunk-A substrate + the Chunk-B
control layer; it must not regress the green rows, the S95 blocking-carrier proofs, or the single-
lane suite. Cancellation reuses the Chunk-A RAII drop-release machinery + the §8.1 permit map; it
adds active reactor-interest deregistration (finding #3) + `AcquirePermit` cancel-safety (finding
#4) **on the same machinery** — it does not fork it.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| the 4 `poll-pool` capacity rows (EXISTS, Chunk A: `same_token_capacity_n_poll…` / `…capacity_1_poll…` / `n_distinct_token_poll_capacity…` / `distinct_poll_effects_sharing_one_token…`) | e2e | `nt` | the Chunk-A poll-carrier capacity proofs stay GREEN — the finding-#3/#4 cancel-safety additions do not regress the non-cancelled acquire/park/release path | P | regression-replay |
| the Chunk-B fan-out / supervisor / degree rows (EXISTS, Chunk B: `concurrency_fanout.rs` — `…no_user_spawn…`, `detached_faulting_effect_does_not_abort…`, `degree_n_bounds_inflight…`, `launch_and_continue_runs_concurrently…`) | e2e | `nt` | the Chunk-B launch-and-continue + supervisor + backpressure proofs stay GREEN — cancellation does not perturb the detached-strand / admission machinery | P | regression-replay |
| the S95 blocking-carrier capacity guards + the 3 two-pool guards (EXISTS, S95) | e2e | `nt` | the blocking-carrier capacity + two-pool routing proofs stay GREEN — Chunk C touches neither the blocking carrier nor two-pool routing | P | regression-replay |
| the 5 `concurrency_reactor.rs` rows (EXISTS, S94) | e2e | `nt` | the real-leaf reactor suspend/resume + overlap proofs stay GREEN — the cancellation drop-path does not perturb the await boundary | P | regression-replay |
| `chunk_c_no_new_public_api_edge_or_abi_bump_neg` | e2e | `nt` | Chunk C adds **no** new `cranelisp-types` / `cranelisp-platform` `public-api.txt` edge line and **no** `ABI_VERSION` bump: `race`/`select` are in-process IO node tags (pinned consts off the default edge), `timeout` is derived `.cl`, cancellation lights up the already-reserved `drop_state` + the Chunk-A future-drop RAII path; combinators are runtime-internal (no platform-ABI surface). Mirrors the Chunk-A/B `no_new_public_api_edge…` guards (`tests/concurrency_poll_edge_guards.rs`), extended to the Chunk-C surface | N | RED-first if a wave leaks an edge/ABI bump; else stays-green |
| single collapsed lane stays green | e2e + unit | `nt` | `cargo nextest run` (the one post-cutover lane) stays green beyond the named RED-first set — a genuine regression is any RED beyond the §C Stage-1 RED-first rows + the 1 known cold-start intermittent (`repl_introspection::imports_filter_neg_nonexistent_module_not_error`, the documented 30 s harness-cap heisenbug, NOT Chunk-C-caused) | P | regression-replay |

---

## §C7 — Flagged gaps shaping Chunk-C Stage-1 authoring

- **G8 — the combinator/cancellation spec anchors (`target: /spec`, in flight THIS Phase).** The
  `race`/`select`/`timeout` typing + structured-cancellation semantics (0447 **second half** — the
  only remaining open half) is being authored by the sibling `/spec` agent now (`spec/10-io.md`
  §10.12.6 item 3 already names it the committed-but-not-yet-specified layer). The §C rows cite the
  combinator anchors **provisionally** (working anchors `spec/10-io.md §10.12.8` "Control
  Combinators" + `spec/12-runtime.md §12.7.10` "Structured Cancellation"); `/qa` pins each `//
  spec:` back-trace to the as-landed anchor at Stage-1. The `select` winner-report shape (§C2) +
  the `timeout` `(Option a)` return shape (§C3) are the two spec details the rows are authored
  against — `/qa` re-points to whichever `/spec` lands.
- **G9 — the cancellation interior seams (`target: /design` int + `/backend` + `/dev`).** The
  concrete seam names depend on the sibling `/design` int agent's Chunk-C reactor.md elaboration
  (in flight) + the /dev wave: **finding #3** (the `EffectPoll`-owned reactor-registration handle
  whose `Drop` deregisters `fd_waiters`/`timer_waiters` + mio), **finding #4** (`Drop for
  AcquirePermit` / pop-until-live), and the `race`/`select` IO-node-tag cancellation codegen +
  intrinsics. The unit rows (§C1-unit, §C4b, §C4d) + the synthetic e2e rows co-land WITH that wave;
  `/qa` authors to whichever seam lands (the `StrandEvent` **cancellation** variant name — "race
  loser / timeout fired → what was cancelled", arch §11 — is a `#[non_exhaustive]` add; minor,
  /qa authors to the landed kind, the Chunk-A G2 / Chunk-B G6 precedent).
- **G10 — the `poll-block` never-readying-fd cancellable leaf + the fd-leak observability
  (`target: /platform` + `/dev`, co-land).** The existing `poll-pool` leaves (`poll-read`/`poll-
  log`) suspend on an **armed timer** that **self-clears at its deadline** — so a *dropped* timer
  poll's entry self-clears and does NOT exhibit finding #3's unbounded `fd_waiters` leak (the leak
  is specifically an **fd that never readies** after a dropped poll armed interest on it). The
  finding-#3 volume e2e (§C4c) therefore needs a **`poll-block` leaf** that arms interest on a
  **never-readying fd** (e.g. the read end of an unwritten pipe) and is **cancellable by drop** —
  authored WITH the /dev cancellation wave + added to `tests/scripts/build-link-prereqs.sh`. The
  **direct** `fd_waiters`-count assertion is the **unit** row (§C4b, intrinsics); the e2e (§C4c)
  uses the **bounded-completion proxy** (cancel many → bounded wall-clock + exit 0). An absent
  `poll-block` is a clean runtime-RED (does NOT block authoring §C4c RED-first).
- **G11 — the web cancel-on-disconnect / graceful-shutdown rows depend on FIXME 0470 (`target:
  /sprint` to route; `/design` int to resolve 0470).** §C5b/§C5c need the **concurrent per-
  connection fan-out** (detached supervised handler strands to cancel) — **WALLED on FIXME 0470**
  (interprocedural launch analysis; `handle-conn` is a user fn `classify_expr` treats as
  `Sequential` ⇒ the serve loop runs serially). The two web-e2e rows are **named, not authored**,
  until 0470 unwalls the fan-out; the **synthetic** §C5a graceful-shutdown core (no fan-out)
  carries the §10-pattern acceptance meanwhile. If 0470 lands this chunk, §C5b/§C5c co-land
  against the Gap-G4 port-param web fixture + a disconnect/shutdown harness hook; else they carry
  forward with 0470 (the cancel-on-disconnect/shutdown *mechanism* is still proven synthetically
  by §C1/§C3/§C4/§C5a — the web rows are the headline-workload confirmation, not the mechanism
  proof).

These are surfaced here (not filed as FIXMEs) per the Phase-3 constraint (edit only
`tests/plan/`); `/sprint` routes G8 to `/spec`, G9 to `/design` int + `/backend` + `/dev`, G10 to
`/platform` + `/dev` at the Chunk-C wave gate, G11 to the wave gate (0470 forward/defer decision).

---

## §C8 — Phase-3 (Chunk C) exit gate confirmation

`/qa` confirms it has enough from the ratified contracts (`effect-concurrency.md` §9/§10/§11 + the
Phase-2 gate (a) A→C contract + the A3-review findings #3/#4 + the in-flight `/design` int
reactor-cancellation pass + the in-flight `/spec` 0447 second half + the reused `spec/10-io.md`
§10.12.4.1 / §10.12.7) to draft the Phase-5 (Chunk-C) Stage-1 failing tests. The sibling `/spec`
(combinator typing + cancellation semantics) and `/design` (reactor cancellation interior +
`race`/`select` node tags) agents are authoring the co-requisite anchors THIS Phase — the
provisional-cite gaps (G8/G9) close at Stage-1 authoring.

**Counts (Chunk C): 16 functional rows + 6 §C6 regression guards = 22 rows** —
- **§C1 `race`** — 3 synthetic e2e (winner-value P; loser-side-effect-absent `_neg` P+N
  load-bearing; loser-releases-permit P+N — the A→C contract e2e) + 1 intrinsics unit (race-node
  loser-drop P+N) = 4.
- **§C2 `select`** — 2 synthetic e2e (winner-branch+value P; winner-index-distinct-from-race
  `_neg` N) = 2.
- **§C3 `timeout`** — 2 synthetic e2e (completes-in-time P; exceeds-fires-and-cancels `_neg` P+N
  load-bearing) = 2.
- **§C4 structured cancellation (findings #3/#4 — the gated rows)** — 1 e2e (A→C permit-release
  next-waiter P+N) + finding #3: 1 intrinsics unit (active deregistration P+N) + 1 e2e (volume no-
  leak N) + finding #4: 1 intrinsics unit (`AcquirePermit` cancel-safety P+N load-bearing) + 1 e2e
  (volume next-live-waiter P+N) = 5.
- **§C5 cancel-on-disconnect / graceful shutdown** — 1 synthetic e2e (graceful-shutdown core P+N) +
  2 web e2e **DEFERRED → 0470** (cancel-on-disconnect; graceful-shutdown-at-server) = 3.
- **§C6 regression guards** — 6 named (4 poll-pool collapsed + Chunk-B fan-out collapsed + S95
  blocking/two-pool collapsed + 5 reactor + no-new-edge `_neg` + single-lane-green).

**e2e ↔ unit split (of the 16 functional rows):**
- **e2e (`/qa`-authored): 13** — **11 synthetic RED-first** (C1a/C1b/C1c, C2a/C2b, C3a/C3b, C4a,
  C4c, C4e, C5a — writable QA-first Stage-1 Wave-1 against the existing `poll-pool` leaves + the
  new `race`/`select` surface; C4c additionally needs the `poll-block` leaf, Gap G10) + **2 web
  DEFERRED → 0470** (C5b, C5c).
- **unit (`/dev`/intrinsics-authored, named for surface completeness + mandatory-unit-per-fix):
  3** — C1-unit (race-node loser-drop), C4b (finding #3 active deregistration), C4d (finding #4
  `AcquirePermit` cancel-safety). Co-land in `cranelisp-intrinsics` `#[cfg(test)]` with the /dev
  cancellation wave.
- **Of the 16:** ~12 RED-first (the Chunk-C build surface) + 2 DEFERRED (0470) + the rest co-
  landing. The new-file target: a new `tests/concurrency_cancellation.rs` (un-gated, the post-
  cutover single lane, mirroring `concurrency_poll_capacity.rs` + `concurrency_fanout.rs`) for the
  synthetic e2e rows; the unit rows land in `cranelisp-intrinsics` `#[cfg(test)]` with the /dev
  wave; the deferred web rows co-land with the 0470 resolution against the Gap-G4 port-param web
  fixture (serialised with `exemplar_web.rs` via the `web-serve` nextest group if 8080 is shared).

### Open verdict for `/sprint` + user

The Chunk-C Stage-1 surface is **draftable now** for §C1–§C4 + §C5a (the 11 synthetic RED-first
e2e rows, QA-first against the existing `poll-pool` leaves + the new `race`/`select`/`timeout`
surface). The single collapsed `nt` lane is the only lane post-cutover — no lane blocker.
Sequencing dependencies:

1. **The combinator surface (`race`/`select`) + the cancellation interior are the keystone** (Gap
   G8 spec + Gap G9 design/dev). The synthetic e2e rows are **RED-first immediately** (they
   reference the intended `race`/`select` surface; RED = "undefined: race" / the loser is not
   cancelled / the permit/interest leaks). **Recommend `/sprint` sequence the `race`/`select` IO-
   node-tag codegen + intrinsics + the finding-#3/#4 reactor cancel-safety + (Gap G10) the
   `poll-block` leaf early in the chunk** so the acceptance rows have a real combinator + a real
   cancellable-never-readying leaf before /dev claims the chunk green (the Chunk-A Gap-G1
   precedent).
2. **The findings #3/#4 rows (§C4) are the load-bearing gate** — they prove the chunk's actual
   deliverable (cancellation at volume neither leaks nor lost-wakes). §C4b pins finding #3
   (active fd-interest deregistration); §C4d pins finding #4 (`AcquirePermit` cancel-safety); §C4c
   /§C4e are their volume e2e faces. `/review` (int reactor) walks these on the change-set; they
   are the durable record of the A3-review prerequisites.
3. **The A→C RAII-Permit-release-on-drop contract is verified here** (§C1c + §C4a — the e2e
   exercise of the Chunk-A §2B intrinsics-unit predecessor `dropping_inflight_poll_releases_
   permit_next_waiter_proceeds`). Co-review with the Chunk-A drop-release machinery (the named
   A→C contract).
4. **The web cancel-on-disconnect + graceful-shutdown rows (§C5b/§C5c) are DEFERRED with FIXME
   0470** (the concurrent per-connection fan-out is walled — interprocedural launch analysis). The
   cancellation *mechanism* is fully proven synthetically (§C1/§C3/§C4/§C5a); the web rows are the
   headline-workload confirmation and co-land if/when 0470 unwalls the fan-out (`/sprint` routes
   the 0470 forward/defer decision at the wave gate — the user is already weighing it per the
   sprint status).

## Phase-3 (Chunk C) plan record (`/qa` 2026-06-29)

Plan authored against the Chunk-C contracts above; the sibling `/spec` (0447 second half —
`race`/`select`/`timeout` typing + structured cancellation) and `/design` (reactor cancellation
interior — findings #3/#4 + the `race`/`select` IO node tags) agents are authoring the co-
requisite anchors in parallel THIS Phase — the provisional-cite gaps (G8/G9) close at Stage-1.
No test code yet (Phase 5). The Chunk-C RED-first set is gated on (i) the `race`/`select` combinator
surface, (ii) the finding-#3/#4 reactor cancel-safety, (iii) the Gap-G10 `poll-block` leaf; the web
cancel-on-disconnect/shutdown rows are deferred with FIXME 0470. A `tests/plan/ledger.md` entry
mirroring the Chunk-C RED-first set will be added at Chunk-C Stage-1 close.

## Wave-C1 landing record (Phase-5 Chunk-C + C-fanout Stage-1, `/qa` 2026-06-29 — ACTUAL)

The as-landed record of the QA-first wave. Per the Chunk-A/B precedent + the task constraint
("keep the build COMPILABLE + suite RUNNABLE after C1"), Wave-C1 authors the black-box e2e rows
that compile as Rust and run RED today (the combinator surface / cancellation foundations /
fan-out fixture are absent → clean **runtime**-RED, not a compile break — e2e shell out to the
binary). The intrinsics UNIT rows co-land with their /dev crate wave. No `#[ignore]`; every test
carries a `// spec:` ref (all anchors verified by `spec_link_check.py` — `/spec` landed §10.12.8/.9/.10
+ §12.4.4 this Phase, so Gap G8 is CLOSED, not provisional).

### C1-LANDED — e2e file (`/qa`): `tests/concurrency_cancellation.rs` (un-gated, runs in `nt`)

The synthetic combinator + cancellation rows. **11 RED-first** on HEAD (clean runtime signal:
`undefined: race` / `select` / `poll-block` absent / the loser is not cancelled):

- §C1 `race` ×3 — `race_returns_first_completed_value` (P); `race_loser_completion_side_effect_absent_neg`
  (P+N, load-bearing); `race_loser_releases_resource_permit` (P+N — the A→C RAII contract e2e, §2B's exercise).
- §C2 `select` ×2 — **RE-POINTED to the as-landed spec** (Gap G8 resolved): the plan drafted §C2 against a
  provisional "select reports the winner INDEX" shape, but `spec/10-io.md` §10.12.8 **item 3** that LANDED
  says `select`/`race` return ONLY the winner's VALUE (NOT its index — `select` is the n-ary generalisation
  of `race` over a List; the discriminant is encoded in each branch's result value). So the rows are
  `select_returns_first_completed_value` (P) and `select_only_winner_value_returned_losers_side_effects_absent_neg`
  (N) — NOT the `_index` rows the plan named. The plan's §C2 table is superseded by these two.
- §C3 `timeout` ×2 — `timeout_io_completes_before_deadline_returns_result` (P);
  `timeout_io_exceeds_deadline_fires_and_cancels_io_neg` (P+N, load-bearing). Expressed INLINE as
  `(race io (poll-read deadline-tok cap d))` per the free-standing-test rule (no stdlib `timeout`).
- §C4 ×3 (the gated findings #3/#4 e2e faces) — `cancelled_inflight_poll_releases_permit_next_waiter_proceeds_e2e`
  (P+N, the A→C contract through timeout-cancel); `volume_cancellation_does_not_leak_fd_waiters_bounded`
  (N — finding #3 volume face, needs the `poll-block` leaf Gap G10); `volume_cancel_while_awaiting_permit_next_live_waiter_proceeds`
  (P+N — finding #4 volume face). VOLUME_N=200, bounded-wall-clock + exit-0 proxies (the direct
  `fd_waiters`-count / FIFO-lost-wakeup assertions are the co-landing C2 intrinsics UNIT rows §C4b/§C4d).
- §C5a ×1 — `shutdown_cancels_outstanding_inflight_effect_releasing_resources` (P+N — the synthetic
  graceful-shutdown core, no fan-out).

### C1-LANDED — e2e file (`/qa`): `tests/concurrency_fanout_web.rs` (un-gated, runs in `nt`)

The C-fanout marquee web rows + the launch-eligibility-negative observable. Includes a `/qa`-owned
**port-parametrized raw-process web harness** (the Gap-G4 deliverable: `free_port()` ephemeral-port
reservation + `spawn_server(fixture, port)` via `CRANELISP_PORT` + `ServerGuard` (kill-on-drop,
SIGTERM) + `http_request(port, …)` — mirrors `tests/exemplar_web.rs` but port-param, so these rows
never collide with the fixed-8080 exemplar test nor each other under parallel nextest). **4 web rows
RED-first** (the port-param poll-shape fan-out fixture `tests/fixtures/web_fanout/main.cl` is a
co-landing /port + /int 0470 deliverable; absent on HEAD ⇒ the readiness probe surfaces the early
child exit as a fast loud RED, ~1.5s, NOT a 20s hang) + **1 GREEN verify pin**:

- §C-fanout `web_server_fans_out_concurrent_requests_overlap` (P) — **C-fanout** (the marquee: K
  concurrent slow requests OVERLAP ≈max not sum; the ratio assertion is fixture-D-agnostic).
- §C-fanout `web_handler_fault_yields_500_for_that_request_server_lives` (P+N) — **C-fanout** (the web
  500-mapping: fault route → 500, server keeps serving; §12.7.9).
- §C5b `web_handler_cancelled_on_client_disconnect` (P+N) — **C3 + C-fanout** (needs the concurrent
  fan-out AND Chunk-C cancellation).
- §C5c `web_server_graceful_shutdown_cancels_outstanding_handler_strands` (P+N) — **C3 + C-fanout**
  (SIGTERM → outstanding strands cancelled → clean exit within 10s; needs ≥1 concurrent outstanding
  strand AND cancellation).
- **E3 (launch-eligibility negative, observable)** `e3_token0_discarded_subtree_not_launched_stays_source_ordered`
  — **GREEN verify pin** (token-0 / `Commutative` shared-stdout discarded sub-tree must NOT be launched
  ⇒ same-token-0 effects stay SOURCE-ORDERED a<b<c; failing-not-ignored-faithful, the B1c precedent —
  trivially holds on HEAD's serial loop, guards that the E3 token-0 REFUSAL keeps the order once C-fanout
  lands).

### C1-LANDED — edge guard added to `tests/concurrency_poll_edge_guards.rs` (un-gated, `nt`)

- §C6 `chunk_c_no_new_public_api_edge_or_abi_bump_neg` — **GREEN stays-green** (no `race`/`select`/
  `timeout`/cancel public item on the `cranelisp-platform`/`cranelisp-types` default edge; `ABI_VERSION`
  stays 8). Flips RED if a Chunk-C wave leaks an edge / bumps the ABI. Mirrors the Chunk-A/B no-edge guards.

### The E1/E2/E3 launch-eligibility negative matrix (/arch's 0470 ruling, `effect-concurrency.md` §4.1)

The predicate: a discarded, locally-token-disjoint bind sub-tree is launch-eligible IFF (E1)
result-discarded, (E2) value-locality (every effect acts on a value bound WITHIN the sub-tree; shares
no free var with the continuation), (E3) touches NO `Commutative` (token-0) / `Sequential` (token-1)
shared-singleton effect, and no opaque-user-fn-in-effect-position. **Disposition:**

- **E3 token-0 (observable e2e) — LANDED** as `e3_token0_discarded_subtree_not_launched_stays_source_ordered`
  (the one black-box-observable negative: token-0 ordering preserved).
- **The remaining negatives are /int UNIT rows** (co-land WITH the C-fanout /dev wave — they assert the
  `classify_expr` / sub-tree-launch class on hand-built bind chains, not subprocess-observable):
  - E2 **shared-token** sub-tree NOT launched (a sub-tree whose effect rides a token from a module-global
    pool handle — not locally-bound-per-launch — FAILS E2, classifies non-launch).
  - E2 **value-shared-with-continuation** sub-tree NOT launched (the sub-tree shares a free var with the
    continuation ⇒ E2 violated ⇒ non-launch).
  - E3 **shared-token (token-1 / `Sequential`)** sub-tree NOT launched.
  - **opaque-user-fn-in-effect-position** NOT launched (an unknown footprint ⇒ REFUSE; the reason the
    handler must be inlined to platform leaves for the launch to fire).
  - The POSITIVE companion (a fresh-`conn`, discarded, capacity-N sub-tree IS launched) is the /int unit
    that the C-fanout `web_server_fans_out_concurrent_requests_overlap` e2e exercises end-to-end.

### Co-landing rows owned by later /dev waves (named for surface completeness)

Reference types/fns/leaves/fixtures absent on HEAD (`race`/`select` node tags, `Drop for AcquirePermit`,
the `EffectPoll`-owned reactor-registration handle, the `poll-block` leaf, the port-param web fixture);
authoring them now would break the single-lane build. They co-land WITH their /dev wave:

- **C2-intrinsics** (`cranelisp-intrinsics` `#[cfg(test)]`, the cancellation-foundations wave): §C4b
  `dropping_armed_fd_poll_deregisters_reactor_interest` (finding #3 active deregistration, P+N); §C4d
  `dropping_acquirepermit_while_parked_does_not_lost_wake` (finding #4 `AcquirePermit` cancel-safety, P+N).
  PLUS the Gap-G10 `poll-block` never-readying-fd cancellable leaf (`/platform` + `/dev`; added to
  `tests/scripts/build-link-prereqs.sh`) that flips the two §C4 volume e2e rows toward green.
- **C3-intrinsics** (the combinator node + runtime wave): §C1-unit
  `race_node_on_first_ready_drops_loser_future_releasing_permit` (P+N — the race-node loser-drop seam).
- **C-fanout /int + /port** (0470): the port-param poll-shape fan-out web fixture
  (`tests/fixtures/web_fanout/main.cl`, /port-owned) that flips the 4 web e2e rows toward green; the
  /int E1/E2/E3 unit matrix above (E2 shared-token / value-shared, E3 token-1, opaque-user-fn negatives
  + the positive companion).

### Measured suite state (Wave-C1 close)

- **`cargo nextest run --no-fail-fast`** — **1743 run: 1728 passed / 15 failed / 1 skipped** (49.5s).
  - **1728 passed** = the Chunk-A+B 1726 baseline + 2 new GREEN (the E3 token-0 verify pin + the §C6
    `chunk_c_no_new_public_api_edge_or_abi_bump_neg` edge guard). **No pre-existing test regressed; no
    timing flake fired** (the documented `repl_introspection` 30s cold-start heisenbug did not surface
    this run). The 1 skip = the S94-demoted CPU-floor benchmark.
  - **15 failed** = EXACTLY the Wave-C1 RED-first set: 11 in `concurrency_cancellation.rs` (§C1×3, §C2×2,
    §C3×2, §C4×3, §C5a×1) + 4 in `concurrency_fanout_web.rs` (the C-fanout marquee + 500-mapping +
    cancel-on-disconnect + graceful-shutdown). All fail FAST (the 11 synthetic ≈0.023s each — clean
    `undefined: race` / absent-leaf runtime-RED; the 4 web ≈1.5s each — fast fixture-absent early-exit,
    no hang). A genuine regression would be any RED BEYOND these 15.
- A `tests/plan/ledger.md` entry mirroring this record will be added at Chunk-C Stage-1 close proper
  (after the C2/C3/C-fanout /dev waves flip the RED set green).
