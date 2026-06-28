# Sprint 95 — Effect-concurrency Slices 3 + 6 (token-capacity `Semaphore` pool; two-pool routing) — Failing-test PLAN (Phase 3 deliverable)

> **Revised 2026-06-28** for the `/arch` **capacity-on-token** re-bless
> (`effect-concurrency.md` §8.1/§8.2): capacity rides `(token, capacity)` **dynamically on
> the IO node** (`effect_on_resource_with_capacity`, append-only 32→40), NOT a static
> `DefKind.cardinality` field — that model + its `cranelisp-types` edge are retired. See
> §6 "What changed" for the row-level delta.

**Owner:** `/qa`. **Status:** PLAN ONLY — no test code yet. The failing tests land in
**Phase 5 Stage 1** (QA-first, sprint-wide, before any per-crate D/D/R cycle). This
document enumerates the row-by-row test surface so `/sprint` + the user can review
coverage before implementation waves are allocated.

**Scope source:** `sprints/SPRINT.md` (S95 Scope 1 — slice 3 token-capacity `Semaphore`
pool; Scope 2 — slice 6 two-pool routing; Scope 3 — the minimal `PollState` env helper;
the Phase-2 `/arch` gate rulings (a)/(c)/(d) — note gate ruling (b)'s static-`DefKind`
carrier is **superseded** by the §8.1/§8.2 capacity-on-token re-bless).
**Contract of record:** `design/arch/effect-concurrency.md` **§8.1** (the slice-3
`(token, capacity)`-dynamic-on-the-node carrier — the ratified seam) / **§8.2**
(within-token source ordering) / §8 (resource-token model under async) / §7 (two-pool
model) + App-B (as-built ↔ target). **Spec of record:** `spec/10-io.md` **§10.12.4.1**
(Resource Cardinality — Token Pools; being renamed cardinality→capacity in parallel —
anchor unchanged; `/spec` actioned FIXME 0447 — the capacity-N pool / (N+1)th-parks
observable is now normative) + §10.12.4 / §10.12.5 / §10.12.6. **Design of record
(interior):** `design/int/reactor.md` §2.6 (Par-overlap) / §5 (token-capacity `Semaphore`
— the slice-3 item) + the as-built reactor boundary. **Public-api edge target:**
`cranelisp-platform` — the additive ungated `CLIO::effect_on_resource_with_capacity`
constructor + the 32→40 node-widen (baseline-diff in Phase 5; **NO `cranelisp-types`
edge** — the retired `DefKind.cardinality` touch is GONE; no `ABI_VERSION` bump).
**Test-leaf helper:** `cranelisp-platform` `PollState` env accessor (`concurrency`-gated,
`/platform` provides — Scope 3).

## Baseline (Phase-3 sanity, `/qa` 2026-06-28)

Carried from the S94-close ledger (not re-run this Phase — PLAN only). The named lane
baselines a genuine regression is measured against:

- **Default `cargo nt`** (feature-OFF, release gate) — **fully GREEN** (S94 close:
  1699+ run / 0 failed; the 3 two-pool guards PASS here on the rayon path).
- **`nt-reactor-e2e`** (`cargo nextest run -p cranelisp --features concurrency-runtime`)
  — **1699 passed / 3 failed** (`--no-fail-fast`): the 3 reds are **exactly** the named
  slice-6 two-pool guards (`resource_serial_diff_token_parallelizes`,
  `auto_io_independent_diff_token_parallelizes_e2e`,
  `auto_io_par_grouping_uniform_across_modes`); the 5 S94 poll-shape
  `concurrency_reactor.rs` rows are GREEN.

Source-of-truth checks done this Phase: the model was **re-blessed to capacity-on-token**
(`/arch` §8.1/§8.2 — `(token, capacity)` dynamic on the IO node, NOT a static `DefKind`
field; the retired `DefKind.cardinality` design is GONE — no `cranelisp-types` edge
touch). `CLIO::effect_on_resource_with_capacity` does **not** exist on HEAD and the
`IO_TAG_EFFECT` node is **not yet widened 32 → 40** (the one genuinely-new carrier —
RED-first by construction for every row that names it). `PollState` does **not** exist in
`crates/cranelisp-platform/src/concurrency.rs` (Scope-3 `/platform` deliverable). The
S94 in-tree `async-demo` / `async-read` leaf declares `poll_shape` only — it does **not
yet declare token + capacity** (the slice-3 `effect_on_resource_with_capacity` /
`declare_concurrent_platform!` knob;
`/platform` + `/dev` extend it — Gap G1). The `nt-reactor-e2e` lane alias **already
exists** (`.cargo/config.toml`, landed S94) and the `src/` `concurrency-runtime`
passthrough is wired — **no Gap-G1-style lane blocker this sprint** (unlike S94). **Any
RED after this point is in-scope work.**

## Conventions / legend

- **Lane** (where the row runs — the four canonical invocations):
  - `nt` — `cargo nextest run` (feature-OFF, the release gate; e2e binary + all
    default-feature unit tests). The byte-identical-when-off floor.
  - `nt-concurrency` — `-p cranelisp-types -p cranelisp-platform -p cranelisp-intrinsics
    --features cranelisp-intrinsics/concurrency` (ABI-v7 layout-contract unit guards +
    the `PollState` helper unit).
  - `nt-concurrency-runtime` — `-p cranelisp-intrinsics
    --features cranelisp-intrinsics/concurrency-runtime` (the reactor implementation —
    mio reactor + `EffectPoll` + strand sink + Semaphore pool; unit-tier in intrinsics).
  - `nt-reactor-e2e` — `cargo nextest run -p cranelisp --features concurrency-runtime`
    (the whole `cranelisp` suite WITH the reactor runtime on — the binary built with the
    `concurrency-runtime` passthrough so a compiled-from-source program drives
    `cranelisp_run_io` through the real reactor + Semaphore pool + two-pool router).
    **Exists on HEAD** (S94); no new alias needed.
- **Tier**: `unit` (`/dev`- or `/platform`-authored, `#[cfg(test)]` in the owning crate,
  named here for surface completeness — landed in the same change-set as the fix per the
  mandatory-unit-test-per-fix discipline) or `e2e` (`/qa`-authored, `tests/*.rs`,
  subprocess via the `Cranelisp` builder). **No middle tier** (`tests/CLAUDE.md`).
- **Posture**: `RED-first` = a failing guard the fix flips green; `flip-to-green` = an
  existing S94 named-known-failing guard that slice 6 makes pass in `nt-reactor-e2e`
  (no test-code change — the implementation flips it); `regression-replay` = an existing
  guard that must stay green; `stays-green` = a feature-off / frozen-edge invariant guard.
- **P/N**: positive (correct behaviour appears) / negative (wrong behaviour absent).

> **Why the headline is split unit ↔ e2e (the S94 reconciliation, carried).** The
> Semaphore pool + two-pool router live in `cranelisp-intrinsics`, compiled only with
> `concurrency-runtime` ON. The default / `--link` binary **never** enables it (the
> deployment invariant, `reactor.md` §1). So the parking + routing *mechanism* is
> reachable from outside the intrinsics crate ONLY through the `nt-reactor-e2e` binary.
> The genuine slice-3/slice-6 "real leaf through the full path" assertions are the
> **`nt-reactor-e2e` rows** (§1B/§1C/§1D/§1F/§2A/§2B); everything else is unit-tier
> substrate proof. The strand-stream park/resume (§1E) and the first-writer-wins
> reconciliation event (§1G) are **not** subprocess-observable (in-memory sink, `/strand`
> dump deferred — `reactor.md` §3), so they are intrinsics-unit rows, NOT e2e.

---

## §1 — Slice 3: token-capacity `Semaphore` pool — `(token, capacity)` dynamic on the node

**Model (re-blessed S95, `/arch` §8.1/§8.2 — capacity-on-token).** Capacity rides **with
the token, dynamically on the IO node, platform-supplied at the effect site** — NOT a
static `DefKind` field. An additive sibling constructor
`CLIO::effect_on_resource_with_capacity(token, capacity, f)` appends `capacity` at
`IO_TAG_EFFECT` payload **offset 32** (node widens **32 → 40 bytes**, append-only — the
fn-name handle stays at offset 24; the old `effect_on_resource(token, f)` ≡
`…_with_capacity(token, 1, f)`). The trampoline keeps a host-owned
`HashMap<token, Semaphore(capacity)>` keyed by the node-read token. **Capacity attaches to
the resource (token): distinct token ⇒ independent capacity; shared token ⇒ shared pool.**
`token == 0` ⇒ no acquire; the (capacity+1)th **parks**; capacity-1 preserves source order.
**The retired model's `DefKind.cardinality` field + loader lift + backend DefKind-bake are
GONE** (§8.1 retirements — no `cranelisp-types` edge touch).

> **S95 scope boundary — capacity-N is demonstrated on the BLOCKING carrier
> (user-confirmed, 2026-06-28).** The token-capacity `Semaphore` pool (acquire/park/release
> around dispatch) lands and is exercised on the **blocking** `IO_TAG_EFFECT` carrier
> (`effect_on_resource_with_capacity` → the rayon/blocking pool, §7) — the DB-pool sharing
> and (N+1)th-park cases are fully demonstrable there. **Poll-shape live capacity-N supply +
> acquire-around-poll is DEFERRED to S96** (it co-lands with the web-platform rewrite, its
> real consumer — `/backend` deferred it as a Phase-3 refinement because the acquire must
> wrap the poll establish→ready arc). In S95 the **poll node only RESERVES** the
> `(token, capacity)` slots at the sentinel (capacity 1); the poll/reactor side proves only
> **distinct-token (independent) overlap** (the unchanged slice-2 mechanism, §1B), NOT
> capacity-N. Live poll-shape capacity-N is an **S96 row** (with the web rewrite), not S95.

Acceptance (`SPRINT.md` Scope 1 + §8; S95 = blocking carrier): blocking effects on **one**
token of capacity N run concurrently while the (N+1)th **parks** until a permit frees;
same-token capacity-1 blocking effects stay serial **and ordered**; two distinct blocking
effects sharing one token share its pool; the strand stream shows the park/resume; and —
on the poll side, unchanged from slice-2 — independent (distinct-token) poll effects
overlap on the reactor. Spec anchor: `spec/10-io.md` §10.12.4.1 (items 1–5; being renamed
cardinality→capacity in parallel — anchor unchanged).

### 1A — the `(token, capacity)` node carrier + the `Semaphore`-per-token pool

The one-field generalization of the existing `ResourceSerial` carrier (§8.1): the new
constructor + the append-only 32→40 node widen + the `HashMap<token, Semaphore>` pool.
The constructor is an **additive ungated** `cranelisp-platform` public-api edge (a bare
`CLIO` sibling, no gated type) — baseline-diff in Phase 5.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `clio_effect_on_resource_with_capacity_additive_public_api_edge` | unit (`cranelisp-platform`) | `nt` | the new `CLIO::effect_on_resource_with_capacity(token, capacity, f)` constructor appears on the **default** (ungated) `crates/cranelisp-platform/public-api.txt` edge as an additive sibling of `effect_on_resource` — no gated type, no removal; the 32→40 node-widen const move is the only layout change. Baseline regenerated in the same /dev change-set (baseline-diff discipline) | P | RED-first (constructor absent on HEAD) |
| `effect_on_resource_with_capacity_appends_capacity_at_offset_32_byte_identical` | unit (`cranelisp-platform`/`cranelisp-backend`) | `nt` | `…_with_capacity(token, cap, f)` writes `capacity` at `IO_TAG_EFFECT` payload **offset 32** (append-only: the fn-name handle stays at offset 24, `resource_token` at 16); the node widens 32 → 40; `effect_on_resource(token, f)` lowers **identically** to `…_with_capacity(token, 1, f)` so the existing cap-1 / `ResourceSerial` node bytes are unchanged | P+N | RED-first |
| `semaphore_pool_keyed_by_token_sized_from_node_capacity` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | the trampoline reads `(token, capacity)` off the **blocking** `IO_TAG_EFFECT` node and acquires from a host-owned `HashMap<token, Semaphore(capacity)>` around blocking dispatch — effects **sharing a token share one semaphore**; capacity 1 ⇒ `Semaphore(1)` == today's `ResourceSerial`; N ⇒ `Semaphore(N)`; `token == 0` ⇒ **no acquire** (unrestricted). The poll-shape node only **reserves** the `(token, capacity)` slots at the sentinel (capacity 1) this sprint — live poll acquire is S96 | P | RED-first |

### 1B — distinct-token (independent) poll effects overlap on the reactor (≈max not sum)

The §8 "token-disjoint effects → separate concurrent futures" fact on the **poll/reactor**
side — the **unchanged slice-2 mechanism** (independent poll leaves overlap via `join_all`;
no shared permit). This is the poll side's *distinct-token overlap* proof; capacity-N on
poll is NOT exercised this sprint (S96 — the poll node only reserves the slots at the
sentinel).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `n_distinct_token_poll_leaves_overlap_max_not_sum` | e2e | `nt-reactor-e2e` | N (≥3) data-independent (distinct-token) poll-shape async leaves, each delaying `D`, in an auto-IO-parallel / `Par` form, overlap on ONE reactor thread — wall-clock ≈ **max**(D) not N·D; summed result proves all ran. Generous midpoint (1.5·D) so the structural inequality is jitter-robust. The slice-2 overlap mechanism, unchanged — no capacity acquire on the poll path | P+N | RED-first |

### 1C — same-token capacity-N (BLOCKING carrier): N concurrent, the (N+1)th parks

The §8 "same-token capacity N (new) → `Semaphore(N)` keyed by the token" fact +
§10.12.4.1 item 2 (the (N+1)th **MUST NOT begin** until a permit frees — observable as
wall-clock latency), demonstrated on the **blocking** carrier (rayon/blocking pool, §7) —
the `Semaphore` acquire wraps blocking dispatch.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `same_token_capacity_n_blocking_admits_n_concurrent_nplus1_parks` | e2e | `nt-reactor-e2e` | (N+1) **blocking** effects (declared via `effect_on_resource_with_capacity`, each a `D`-ms sleep) on **one** token of capacity **N** (concretely N=2, 3 effects): the first N overlap on the blocking pool, the (N+1)th **parks** on the token's `Semaphore` until a permit frees ⇒ wall-clock ≈ **2·D** (two waves), distinguishable from unbounded (~1·D) AND from serial (~3·D); summed result proves all ran. The (N+1)th-parks deferral is the load-bearing assertion (§10.12.4.1 item 2) | P+N | RED-first |

> **Pick N and D so the three regimes are unambiguous at a generous margin.** With N=2,
> D=60 ms: unbounded ≈ 60 ms, capacity-2 ≈ 120 ms, serial ≈ 180 ms. Assert capacity-2
> wall-clock is **both** `> 1.5·D` (≈ 90 ms — proves the (N+1)th parked, did not overlap
> freely) **and** `< 2.5·D` (≈ 150 ms — proves the first two DID overlap, not fully
> serial). Two-sided window, wide on both edges — timing-flakiness is a banned
> disposition. Size D so the e2e stays well under the 100 ms-per-test budget concern
> while the three regimes remain separable (the test's wall-clock is dominated by the
> deliberate delay, not compute).

### 1D — same-token capacity-1 (BLOCKING carrier): serial AND source-ordered

§10.12.4.1 item 3 — capacity 1 is exactly `ResourceSerial`: at most one effect at a
time, the rest serialise **in source order** (exclusion *and* order, carried deliberately
— a bare permit gives exclusion but not order, §8.2 invariant). Demonstrated on the
**blocking** carrier.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `same_token_capacity_1_blocking_serial_and_source_ordered` | e2e | `nt-reactor-e2e` | three **blocking** effects (via `effect_on_resource_with_capacity`) on **one** token of capacity **1**, each delay D, serialise (wall-clock ≈ 3·D, not overlapped) **AND** complete in **source order** — the order is observable (ordered append to a sink the effect writes, or an order-encoding result), proving exclusion did not reorder | P+N | RED-first |

> **The ordering half is the negative face (`_ordered`).** Item 3's source-order
> guarantee is the property a bare-`Semaphore(1)` would silently violate (exclusion
> without order). The row asserts BOTH the serial wall-clock AND that the observable
> completion order equals source order — a capacity-1 token that overlapped, or completed
> out of order, fails it. This is the §8.2 "within-token source ordering carried on
> purpose" invariant at the e2e edge.

### 1E — strand stream shows the park/resume (dev-observable, unit-tier)

§10.12.4.1 item 2's informative half: the (N+1)th effect's park/resume surfaces in the
dev-facing strand stream (§10.12.6). NOT subprocess-observable (in-memory sink) ⇒
intrinsics-unit.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `capacity_n_park_resume_recorded_in_strand_stream` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | a capacity-N pool with (N+1) same-token **blocking** effects records the (N+1)th effect **parking** on the permit and **resuming** when one frees in the strand sink (`StrandEvent::EffectSuspended`/`EffectResumed`, OR a new `#[non_exhaustive]` `TokenParked`/`TokenResumed` kind — `/dev`'s choice; the enum is already `#[non_exhaustive]`) | P | RED-first |

> **`/qa` authors to whichever event kind `/dev` lands.** The `StrandEvent` enum is
> `#[non_exhaustive]` (`strand.rs:58`); slice 3 may reuse `EffectSuspended`/`EffectResumed`
> (the fd-park precedent) or add `TokenParked`/`TokenResumed`. The unit asserts a park
> *then* a resume correlated to the (N+1)th strand id, whichever names `/dev` chooses —
> flagged Gap G2 (minor; affects the assertion's event name, not the row's existence).

### 1F — capacity-on-token sharing (BLOCKING carrier): TWO DISTINCT effects share ONE token's pool

The case the retired per-effect model **could not express** (§8 — "per-effect capacity
yields N+N+N"): a DB connection pool where `query` / `execute` / `begin` over one pool
share **one** token of capacity N. Because capacity attaches to the **resource (token)**,
two *different* effect kinds on the same token draw from the same `Semaphore` — total
in-flight across both effects is bounded by N, and the (N+1)th (of either kind) parks.
Fully demonstrable on the **blocking** carrier (the DB pool is the real consumer).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `distinct_blocking_effects_sharing_one_token_share_one_pool_nplus1_parks` | e2e | `nt-reactor-e2e` | TWO **distinct BLOCKING** effect kinds (e.g. `pool-read` + `pool-write`, each via `effect_on_resource_with_capacity`) declaring the **same** token of capacity **N** draw from ONE shared `Semaphore(N)`: with N=2 and 3 mixed-kind effects in flight, at most 2 overlap and the 3rd parks regardless of which kind it is — total sum-in-flight ≤ N across both effects (the DB-pool case; two-sided timing window as §1C). The shared-pool bound is the load-bearing assertion — a per-effect pool would let each kind run N concurrently (no cross-kind bound) and fail it | P+N | RED-first |

### 1G — reconciliation: same token, different capacity ⇒ first-writer-wins

§8.1 reconciliation rule (pinned): if two effects on one token declare **different**
capacities (a platform bug), the value that **created the token's semaphore wins**
(first-writer-wins — the conservative deterministic choice; never exceeds a declared
ceiling), and a dev-facing strand event **records the disagreement**. NOT an
abort/`assert` (a trust-boundary violation that mis-sizes a pool, does not corrupt
memory) and NOT silent-max (would raise the bound past a capacity the platform declared
unsafe). The recorded event is not subprocess-observable ⇒ intrinsics-unit. Demonstrable on
the **blocking** carrier (where the live capacity acquire runs this sprint).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `same_token_conflicting_capacity_first_writer_wins_and_records_event` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | two **blocking** effects on one token declaring different capacities (say 2 then 5): the token's `Semaphore` is sized by the **first** writer (capacity 2 — never the later/larger value), AND a dev-facing strand event records the disagreement; a second writer does NOT resize the existing pool (no silent-max, no abort) | P+N | RED-first |

---

## §2 — Slice 6: blocking/CPU two-pool routing (close the feature-on regression)

The descriptor's **blocking?** (= the node tag: `IO_TAG_EFFECT` blocking vs
`IO_TAG_EFFECT_POLL` poll-shape — gate ruling (a)/(b)) routes each effect: blocking →
rayon (`spawn_blocking`-style), poll-shape → the reactor. The async `Par` arm partitions
branches by tag and drives both pools concurrently, joining via a **wakeable** rayon→
reactor bridge (gate ruling (c) — **forbid `block_on(rayon_join)` on the reactor
thread**). Acceptance: the 3 named guards flip GREEN; a mixed `Par` overlaps on both pools.

### 2A — the 3 named two-pool guards flip GREEN in `nt-reactor-e2e`

These are **existing** `spec_10_io.rs` blocking-effect (`test-capture`) wall-clock
witnesses — GREEN feature-off (rayon path), RED in `nt-reactor-e2e` today (the slice-2
reactor routes blocking effects through its one `join_all` thread). Slice 6 routes
blocking branches back to rayon ⇒ they parallelize feature-on. **No test-code change** —
the implementation flips them; the ledger Stage-1 note records the flip.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `resource_serial_diff_token_parallelizes` (EXISTS) | e2e | `nt-reactor-e2e` | two diff-token (1,2) 200 ms ResourceSerial blocking calls run concurrently feature-on (wall-clock < 1.5·D ≈ 300 ms) — blocking branches route to rayon, not the single reactor thread | P | flip-to-green |
| `auto_io_independent_diff_token_parallelizes_e2e` (EXISTS) | e2e | `nt-reactor-e2e` | a data-independent Commutative blocking pair parallelizes feature-on (< 300 ms) | P | flip-to-green |
| `auto_io_par_grouping_uniform_across_modes` (EXISTS) | e2e | `nt-reactor-e2e` | the blocking-`Par` grouping parallelizes **uniformly** across `--run` + `--link` feature-on (both < 300 ms) | P | flip-to-green |

### 2B — mixed blocking + poll-shape `Par` overlaps on both pools

The two-pool composition acceptance (`SPRINT.md` Scope 2): one `Par` with a blocking
branch (→ rayon) AND a poll-shape branch (→ reactor) drives both pools concurrently and
joins. The gate-ruling-(c) wakeable bridge is what makes the rayon completion wake the
reactor-side join without a starving `block_on`.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `mixed_blocking_and_poll_par_overlaps_on_both_pools` | e2e | `nt-reactor-e2e` | a `Par` whose branches are ONE blocking `test-capture` sleep leaf (→ rayon) + ONE poll-shape `async-demo` leaf (→ reactor), each delay D, overlap concurrently — wall-clock ≈ **max**(D) not sum; both results join correctly (summed exit proves both ran). The blocking branch on rayon does NOT starve the poll branch on the reactor (the wakeable-bridge property, observed as overlap not serialization) | P+N | RED-first |

### 2C — the wakeable rayon→reactor bridge (Principle-8 constraint, unit)

Gate ruling (c)'s load-bearing constraint: the cross-pool completion signal MUST be a
**wakeable future** (rayon `spawn` → `futures` oneshot woken via `cx.waker()`), NOT
`block_on(rayon_join)` on the reactor thread (re-introduces the exact starvation) and NOT
a third bespoke dispatcher. Observable proxy: a long rayon branch concurrent with a
poll branch does not starve the reactor.

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `two_pool_join_blocking_branch_does_not_starve_reactor` | unit (`cranelisp-intrinsics`) | `nt-concurrency-runtime` | a two-pool join with a long rayon (blocking) branch + a concurrent poll-shape branch resolves the poll branch via the reactor **while** the rayon branch runs (the completion is a wakeable future woken via `cx.waker()`, not a reactor-thread `block_on`) — the poll branch is not blocked behind the rayon branch; the join composes the two **existing** dispatchers (no third one) | P | RED-first |

---

## §3 — Invariants: feature-off byte-identical + `--link` no executor

Slice 3/6 must not perturb the production default (`concurrency-runtime` OFF). The
`HashMap<token, Semaphore>` pool / two-pool routing path is constructed ONLY feature-on;
feature-off the blocking `Par` stays on rayon, byte-identical; `--link` links no executor.
The node's new `capacity` field at offset 32 is inert data feature-off (the widened node
is still produced — the 32→40 widen is ungated — but nothing reads `capacity` or acquires
a permit without the runtime).

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `blocking_par_default_build_constructs_no_semaphore_path_neg` | unit (`cranelisp-backend`/`cranelisp-intrinsics`) | `nt` | a default (feature-off) build constructs **no** `HashMap<token, Semaphore>`-pool / two-pool-router path — blocking `Par` lowers to the unchanged rayon `dispatch_par_branches_with_trace`; the node's `capacity` field rides as inert data (no acquire site reachable feature-off) | N | RED-first if the gating leaks; else stays-green |
| `real_io_program_default_build_output_unchanged` (EXISTS, S94) | e2e | `nt` | a real-IO `--run` program's stdout/exit is byte-identical through the default binary — slice-3/6 changes are invisible feature-off | P | regression-replay |
| `link_io_program_runs_without_executor` (EXISTS, S94) | e2e | `nt` | a small IO program `--link`ed then RUN succeeds (exit 0, correct value) — the linked binary works with no reactor/executor present (`mio`/`futures` never compiled into the exe-bundle path; the `dep:`-gated guarantee) | P | regression-replay |
| `link_path_does_not_enable_concurrency_runtime_neg` (EXISTS, S94) | unit (`src/`) | `nt` | the exe-bundle / `--link` build path never enables `concurrency-runtime` (structural assertion on the feature wiring — the deployment invariant slice 3/6 must preserve) | N | regression-replay |

> The 3 named guards of §2A **also** stay GREEN in the default `nt` lane feature-off
> (they are the production blocking-`Par` overlap witnesses on rayon) — that is the
> feature-off-byte-identical floor for the two-pool work, already covered by their
> default-lane pass; §2A tracks only their feature-ON flip.

---

## §4 — The `PollState` env helper (Scope 3) — test-leaf offset-safety in one place

The S95 **poll-shape** test leaves (the `async-demo` leaf, consumed by the poll-side rows
§1B distinct-token overlap + §2B's poll branch) declare against the raw `IO_TAG_EFFECT_POLL`
env today (offset math + SAFETY comments). Per Scope 3, `/platform` folds a **minimal
typed env accessor** — `PollState` with `arg(i)` / `scratch(i)` / `set_result(v)` over
the R1 env layout — into `cranelisp-platform` (`concurrency`-gated, off the frozen edge),
so the env-layout convention lives in **one** place. **Rationale (load-bearing): a poll
leaf mis-deriving an offset would otherwise masquerade as a routing bug → a false RED that
costs a misdirected `/dev` triage.** Owner: `/platform` provides, `/qa` consumes. (The
capacity rows §1C/§1D/§1F use the **blocking** carrier — sleep-style effects, no
`PollState` env — so `PollState` serves the poll path + the S96 poll-capacity work.)

| Test name | Tier | Lane | Asserts | P/N | Posture |
|---|---|---|---|---|---|
| `poll_state_env_accessor_arg_scratch_set_result_round_trip` | unit (`cranelisp-platform`) | `nt-concurrency` | `PollState::arg(i)` reads the i-th marshaled i64 arg, `scratch(i)` reads/writes leaf scratch, `set_result(v)` writes the host-known result slot — at the R1 env offsets (`[header \| code_ptr \| drop_glue_ptr \| env = result-slot + i64 args + scratch]`); a write-then-read round-trip pins the offset convention so the §1B/§2B poll test leaves are offset-safe | P | RED-first (`PollState` absent on HEAD) |

**Test-leaf shapes (the surface `/qa`'s e2e consume, `/platform` + `/dev` author).** Two
kinds this sprint:
- **Blocking capacity leaf** (§1C/§1D/§1F) — a `D`-ms-sleep BLOCKING effect declaring token
  + capacity via `effect_on_resource_with_capacity` (the capacity pool's S95 carrier). One
  leaf for §1C/§1D; TWO distinct kinds on one token for §1F. No `PollState` env (blocking,
  not poll-shape).
- **Poll overlap leaf** (§1B + §2B poll branch) — the S94 `async-demo` poll-shape leaf
  (independent leaves overlapping on the reactor — the unchanged slice-2 mechanism), written
  against `PollState`. Its `(token, capacity)` slots are only **reserved** at the sentinel
  this sprint; live poll-shape capacity-N is S96.

Both are **platform effects** (not stdlib) → the free-standing-test rule is satisfied (zero
`stdlib/` dependency; the e2e uses the in-tree leaves via the platform-effect surface).
Lane: `nt-reactor-e2e` for the consuming e2e; `nt-concurrency` for the `PollState` unit.

---

## §5 — Flagged gaps shaping Stage-1 authoring

- **G1 — the capacity-declaring leaves (`target: /platform` + `/dev`).** Two leaf kinds
  this sprint (the S95 capacity carrier is **blocking**, per the scope boundary above):
  - **Blocking capacity leaf** (§1C/§1D/§1F) — a `D`-ms-sleep BLOCKING effect declaring
    token + capacity via `effect_on_resource_with_capacity` (one leaf for §1C/§1D; TWO
    distinct kinds on one token for §1F). This is the load-bearing S95 carrier — `/platform`
    (declare) + `/dev` (node-widen bake @32 + `HashMap<token, Semaphore>` acquire/park around
    blocking dispatch). No `PollState` (blocking, not poll-shape).
  - **Poll overlap leaf** (§1B + §2B poll branch) — the **existing** S94 `async-demo`
    poll-shape leaf (independent leaves overlapping on the reactor — the unchanged slice-2
    mechanism). Its `(token, capacity)` slots are only **reserved** at the sentinel this
    sprint; live poll-shape capacity-N is **S96** (co-lands with the web rewrite).

  `/qa`'s e2e *consume* these from compiled source. **Reconcile the leaf name(s) + the
  per-row token/capacity knob when the leaves land** (mirror the S94
  `ASYNC_LEAF_PLATFORM`/`ASYNC_LEAF_EFFECT` const pattern in `concurrency_reactor.rs`).
  **Does not block** authoring the e2e rows RED-first (they reference the intended shape;
  RED = "leaf does not yet declare capacity", a meaningful runtime-RED per the S94 QA-first
  precedent). The `nt-reactor-e2e` lane + the `src/` passthrough already exist (no S94-style
  lane blocker). Flag to `/sprint` at the wave gate so the blocking capacity leaf lands
  early in the slice-3 wave.
- **G2 — the strand park/resume event kind (`target: /dev` intrinsics).** Whether
  §1E (park/resume) and §1G (capacity-disagreement) assert `EffectSuspended`/`EffectResumed`
  (reuse) or new `TokenParked`/`TokenResumed` / a disagreement kind depends on `/dev`'s
  slice-3 choice (`StrandEvent` is `#[non_exhaustive]`). Minor — affects only the event
  name in the §1E/§1G unit assertions. `/qa` (here: the named unit rows) authors to
  whichever `/dev` lands.
- **G3 — `cranelisp-platform` additive ungated edge (`effect_on_resource_with_capacity`).**
  The capacity-on-token model lands the new `CLIO` constructor + the 32→40 node-widen const
  on the **default** `crates/cranelisp-platform/public-api.txt` edge (NOT a
  `cranelisp-types` `DefKind` touch — that retired-model edge is GONE). Per the baseline-diff
  discipline (`tests/CLAUDE.md` §public-api) the `/dev` change-set regenerates
  `crates/cranelisp-platform/public-api.txt` + updates the facade/BC narrative + the §1A
  edge unit, atomically. Additive only (new sibling, no removal, no gated type); no
  `ABI_VERSION` bump (the node layout is an in-process backend↔intrinsics convention,
  append-only). The S94 `concurrency_descriptor_absent_from_default_public_api_neg`
  frozen-edge guard stays green (the full `ConcurrencyDescriptor` remains gated; the bare
  `CLIO` constructor is not a gated type).

These are surfaced here (not filed as FIXMEs) per the task constraint (edit only
`tests/plan/`); `/sprint` routes G1/G2 to `/platform` + `/dev` at the Phase-4 wave gate.

---

## §6 — Phase-3 exit gate confirmation

`/qa` confirms it has enough from the ratified contracts
(`effect-concurrency.md` §7/§8/§8.1/§8.2 + App-B + the gate rulings (a)/(c)/(d) +
`spec/10-io.md` §10.12.4.1) to draft the Phase-5 Stage-1 failing tests:

- **Slice 3 — `(token, capacity)` node carrier + pool (§1A)** — 1 platform unit (additive
  ungated `CLIO::effect_on_resource_with_capacity` public-api edge) + 1
  platform/backend unit (capacity appended @32, 32→40 widen, cap-1 byte-identical) + 1
  intrinsics unit (`HashMap<token, Semaphore(capacity)>` keyed by token). Anchor: §8.1 +
  §8.
- **Slice 3 — distinct-token POLL overlap (§1B, slice-2 mechanism)** — 1 `nt-reactor-e2e`
  (≈max not sum; the unchanged poll/reactor overlap, no capacity acquire). Anchor: §8
  (token-disjoint → concurrent) + §10.12.4.1 item 5.
- **Slice 3 — capacity-N park, BLOCKING carrier (§1C)** — 1 `nt-reactor-e2e` (N concurrent
  + (N+1)th parks, two-sided timing window). Anchor: §10.12.4.1 item 2 + §8 (`Semaphore(N)`
  keyed by token).
- **Slice 3 — capacity-1 serial+ordered, BLOCKING carrier (§1D)** — 1 `nt-reactor-e2e`
  (serial AND source-ordered). Anchor: §10.12.4.1 item 3 + §8.2 (within-token source
  ordering carried).
- **Slice 3 — strand park/resume (§1E)** — 1 intrinsics unit (NOT subprocess-observable).
  Anchor: §10.12.4.1 item 2 informative half + §10.12.6 + `reactor.md` §3.
- **Slice 3 — capacity-on-token sharing, BLOCKING carrier (§1F)** — 1 `nt-reactor-e2e` (two
  distinct blocking effects, one token, one shared pool; the DB-pool case the per-effect
  model couldn't express). Anchor: §8 (shared token ⇒ shared pool) + §8.1.
- **Slice 3 — first-writer-wins reconciliation (§1G)** — 1 intrinsics unit (same token /
  different capacity ⇒ first-writer-wins + recorded event; NOT subprocess-observable).
  Anchor: §8.1 reconciliation rule (pinned).
- **Slice 6 — the 3 named guards flip GREEN (§2A)** — 3 existing e2e flip-to-green in
  `nt-reactor-e2e` (no new code). Anchor: gate ruling (a) (routing reads the node tag) +
  §7.
- **Slice 6 — mixed both-pools (§2B)** — 1 `nt-reactor-e2e` (blocking + poll-shape `Par`
  overlaps on both pools). Anchor: §7 two-pool model + gate ruling (c).
- **Slice 6 — wakeable bridge (§2C)** — 1 intrinsics unit (no `block_on` starvation; two
  existing dispatchers composed). Anchor: gate ruling (c) Principle-8 constraint.
- **Invariants (§3)** — 1 backend/intrinsics `_neg` (no Semaphore-pool path feature-off;
  the `capacity` field rides inert) + 2 existing e2e regression-replays (byte-identical +
  link-no-executor) + 1 existing src/ `_neg` (link path never enables runtime). Anchor:
  App-B(a)/(d) + `reactor.md` §1.
- **`PollState` helper (§4)** — 1 platform unit (env-accessor round-trip). Anchor:
  Scope 3 + the R1 env layout.

**Counts:** **19 planned rows** — **10 e2e** (`/qa`-authored): 5 RED-first `nt-reactor-e2e`
(§1B distinct-token, §1C capacity-N park, §1D capacity-1 ordered, §1F capacity-on-token
sharing, §2B mixed both-pools) + 3 flip-to-green `nt-reactor-e2e` (§2A the named two-pool
guards, existing, no new code) + 2 default-`nt` regression-replays (§3 byte-identical +
link-no-executor, existing); **9 unit** (`/dev`-/`/platform`-authored, named for surface
completeness + the mandatory-unit-per-fix discipline): §1A (3: platform public-api edge,
node-widen @32 byte-identical, `Semaphore`-keyed-by-token) + §1E (1, strand park/resume) +
§1G (1, first-writer-wins reconciliation) + §2C (1, wakeable bridge) + §3 (2:
no-semaphore-path-neg + link-path-neg) + §4 (1, `PollState`). **Of the 19:** 5 new
RED-first e2e + 3 flip-to-green e2e + 7 RED-first units; the rest (2 e2e + 2 units) are
regression-replay/stays-green carries. The new file/extend target: extend
`tests/concurrency_reactor.rs` (or add `tests/concurrency_capacity.rs`) for the §1B–§1F +
§2B reactor-e2e rows (share the leaf machinery — the blocking capacity leaf for §1C/§1D/§1F
and the poll overlap leaf for §1B/§2B; gated `#[cfg(feature="concurrency-runtime")]`).

> **What changed from the pre-revision plan (capacity-on-token re-bless, `/arch`
> §8.1/§8.2).** DROPPED the 4 rows tied to the retired static-`DefKind.cardinality` model
> (the `cranelisp-types` field unit, its frozen-edge `_neg`, the backend DefKind-bake unit,
> the loader-lift-of-DefKind-cardinality unit — that edge is GONE). ADDED the
> `cranelisp-platform` additive-ungated public-api edge row
> (`effect_on_resource_with_capacity` + 32→40 widen), the constructor/node-widen
> byte-identical unit, the §1F capacity-on-token **sharing** e2e (two distinct effects, one
> token — the DB-pool case), and the §1G **first-writer-wins** reconciliation unit. RENAMED
> cardinality→capacity throughout (spec anchor §10.12.4.1 unchanged). UNCHANGED: the 3
> two-pool flip-to-green guards, byte-identical-off, `--link`-no-executor, the `PollState`
> helper. Net: row count steady at **19**, lane mix shifts to **10 e2e / 9 unit** (was 9/10
> — +1 e2e from §1F sharing; §1A unit count drops 5→3 as the DefKind rows retire and the
> platform-edge + node-widen rows land; +1 unit from §1G reconciliation).

> **Scope correction (user-confirmed, 2026-06-28) — capacity-N is demonstrated on the
> BLOCKING carrier; poll-shape live capacity → S96.** `/backend` deferred poll-shape live
> capacity supply + acquire-around-poll to S96 (it co-lands with the web-platform rewrite,
> its real consumer — the acquire must wrap the poll establish→ready arc). Plan effect, **no
> row count change** (still 19, 10 e2e / 9 unit): the §1C/§1D/§1F capacity rows re-target to
> **blocking** effects via `effect_on_resource_with_capacity` (the DB-pool sharing + park
> cases are fully demonstrable on the blocking pool); §1B is reframed as the **poll-side
> distinct-token overlap** (the unchanged slice-2 mechanism, no capacity acquire); the
> poll node only **reserves** the `(token, capacity)` slots at the sentinel (capacity 1)
> this sprint. Live poll-shape capacity-N is a **named S96 row** (with the web rewrite).
> Unchanged: the 3 two-pool flip-to-green guards, distinct-token poll overlap (§1B),
> first-writer-wins (§1G, demonstrable on blocking), byte-identical-off, `--link`-no-executor,
> the `PollState` helper, the additive-ungated `cranelisp-platform` edge row.

### Open verdict for `/sprint` + user

The Stage-1 surface is **draftable now** for all of §1/§2/§3/§4. Unlike S94, **the
`nt-reactor-e2e` lane + the `src/` passthrough already exist** — there is no lane blocker.
The only sequencing dependency is **Gap G1** (the capacity-declaring leaves + `PollState`):
the §1B–§1F + §2B e2e rows are draftable RED-first immediately (they reference the intended
leaf shape; RED = "leaf does not yet declare capacity"), and flip GREEN once `/platform` +
`/dev` land the **blocking capacity leaf** (§1C/§1D/§1F) + the node-widen/`Semaphore`
acquire wire + `PollState` for the poll overlap leaf (§1B/§2B). **Recommend `/sprint`
sequence the blocking capacity leaf + the `effect_on_resource_with_capacity` carrier +
`HashMap<token, Semaphore>` acquire/park wire (Scope 1, `/platform` + `/dev`) + `PollState`
(Scope 3, `/platform`) early in the slice-3 wave** so the acceptance rows have a real leaf
to consume before `/dev` claims the slice green. Slice 6 (§2A/§2B) co-lands with slice 3
per gate ruling (a) (independent — routing reads the node tag) and reuses the same
`nt-reactor-e2e` lane. **Live poll-shape capacity-N is explicitly deferred to S96** (the
poll node reserves the slots at the sentinel this sprint).

## Stage-1 ledger note

At Phase-5 Stage-1 close `/qa` will add a `tests/plan/ledger.md` entry recording: (1) the
5 new RED-first `nt-reactor-e2e` capacity/two-pool e2e rows authored failing-not-ignored
(gated `#[cfg(feature="concurrency-runtime")]`, compiled OUT of default `nt` so no
collateral RED there); (2) the **3 named two-pool guards transition from "named
known-failing slice-6 guards" (S94 ledger entry) to "slice-6 acceptance — flips GREEN in
`nt-reactor-e2e`"** — on slice-6 land the S94 entry is **resolved/removed** per the
close-time verification protocol (test now passes on HEAD in the reactor lane), with the
removal noted in the close report; (3) the default-`nt` byte-identical + link-no-executor
replays stay GREEN (the feature-off floor); (4) the 9 unit-tier rows are `/dev`-/`
/platform`-authored in the owning crate's `#[cfg(test)]` with the fix (not authored by
`/qa` this Stage — named here for surface completeness), incl. the `cranelisp-platform`
public-api baseline regen for the additive `effect_on_resource_with_capacity` edge
(baseline-diff discipline); (5) the capacity-N pool is exercised on the **blocking carrier**
this sprint (§1C/§1D/§1F via `effect_on_resource_with_capacity` → blocking pool) — **poll-shape
live capacity-N + acquire-around-poll is DEFERRED to S96** (co-lands with the web-platform
rewrite; the poll node only reserves the `(token, capacity)` slots at the sentinel in S95),
so a named S96 row (live poll capacity) carries forward in the roadmap. Expected post-Stage-1
default `nt`: unchanged-GREEN (the new e2e are gated out; the additive ungated edge changes
the platform `public-api.txt` baseline but adds no RED). Expected post-slice-6
`nt-reactor-e2e`: the 3 named guards GREEN + the 5 new capacity/two-pool rows GREEN; a
genuine regression is any RED beyond the (then-green) named set.
