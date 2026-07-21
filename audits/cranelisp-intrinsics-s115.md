# cranelisp-intrinsics — whole-context assessment (S115)

> **Point-in-time record, 2026-07-21.** Rotation slot: `cranelisp-intrinsics`
> (last assessed `audits/cranelisp-intrinsics-s87.md`, 2026-06-20 — the
> longest-unassessed bounded context). Read-only on the context; every claim
> below carries file:line verified against source at HEAD (`5ba28de8` + the
> S115 working tree). Recommendations are **proposals**, disposed at S116
> Phase 1. No FIXMEs filed.

**Scope**: `crates/cranelisp-intrinsics/src/` (35 files, 19,036 raw lines),
`design/intrinsics/`, the crate `CLAUDE.md`, and the e2e/plan surface touching
the crate (`tests/ms_p6_mode_self_tests.rs`, `tests/plan/memory-safety-coverage.md`
§4/§4.1, `tests/plan/s115-instrumentation-matrix.md` W7,
`design/arch/safety-invariants.md` §4 R8/R13).

---

## 1. Verdict

| Attribute | Grade | One-line basis |
|---|---|---|
| Design quality (fitness) | **strong** | The tier-5 mode design is a model of Principle 6/18: three env gates over the *two already-single-sourced* funnels, byte-identical-off, zero ABI/catalog/IR delta. A1 was the right gap to close. |
| Design realisation | **weak** | `diagnostic-modes.md` §6's mandated self-tests ("plant a fault the mode must catch … at the `alloc`/`rc` seams") did **not** land as specified; what landed tests mechanism internals in isolation. The doc still brands itself "pre-implementation". |
| Simplicity & volume — code | **adequate** | No production fn over budget (S87 HIGH-3 held). Residue: 3 `read_i64` implementations, 2 dead `pub fn`s. |
| Simplicity & volume — docs | **adequate** | `CLAUDE.md` is dense, high-value, and mostly verified true; four falsifiable claims (§4). |
| Simplicity & volume — tests | **weak in the instrument tier, strong elsewhere** | 59% test density crate-wide; but the crate's *own* safety instruments carry near-zero detection proof (§3). |
| Duplication | **weak** | Divergent-duplication carried unfixed since S87 (F3), and the crate `CLAUDE.md` asserts the opposite of what the source does. |
| Risk-weighted coverage | **weak** | M2 has **zero** detection evidence anywhere in the tree; M1's was retired; M3's works (probe-verified here) but is uncommitted; A2/A3/A4's release faces have zero coverage. |
| Maintainability | **strong** | `unsafe` discipline remains exemplary — S87's one gap (`call_continuation`) is the only historical miss and every seam carries an honest `// SAFETY:`. Comment honesty is high; the exceptions are named in §4. |
| Memory freshness | **adequate** | Structural claims verified true (module visibility, feature retirement, blessed-const locking, base-vs-payload). Two falsified claims + one stale count. |

### The acid test

> *If we lost this context's code and docs but retained the insight from
> experience, and produced a lean, high-quality solution second time around —
> would it look like this?*

**The runtime mechanism: yes. The instrument tier: no.**

The runtime half is close to what a second-time solution would build. Two
single-sourced funnels (`alloc::alloc_with_rc`, `alloc::dealloc`), two dec
funnels (`rc::consume_shallow`, `drop::atomic_dec_rc`), one shallow-inc funnel
(`rc::rc_inc`), a base-pointer 2-word header locked by `const _: () = assert!`,
and a nullary-tag guard at every RC entry. That narrowness is exactly what made
the tier-5 modes cheap: the design's §2 actor table (`diagnostic-modes.md:64-81`)
could hook the whole allocator lifecycle in four places because the seam was
already right. A rewrite would keep this.

The instrument tier is where the delta is, and it is not a hygiene delta — it
is the same finding W7 just made about the rest of the project, applied to the
crate that *supplies* W7's instruments. A second-time solution built with the
detection-proof bar in hand would not have shipped **M2 at all in its current
shape**: `CRANELISP_SCRUB_FREED` writes a poison word that nothing in the
repository ever reads back, plants, or observes. It would not have shipped a
`pub fn reset_counts()` that can zero the counters that are M3's *only*
release-mode evidence base, with rustdoc naming a caller that does not exist. It
would not carry three `read_i64` implementations under a `CLAUDE.md` sentence
saying there is one. And it would not describe a 37-entry catalog as 29 in an
`/arch`-approved facade — which is the *same* finding S87 closed as HIGH-1,
recurred, because the S87 cure ("cite the test constant, don't restate the
number") was defeated by a test whose *name carries the number*.

The one-sentence version: **this crate builds the detectors the project trusts,
and it is the least-instrumented consumer of its own discipline.** R8 is graded
`dynamic-lane`/VERIFIED and called "still the strongest row"
(`safety-invariants.md:210`, W7 matrix). That grade is inherited, not earned —
see §3.

---

## 2. Current state — the RC/alloc seam and the diagnostic modes

### 2.1 What exists, verified

| Mechanism | Site | Verified |
|---|---|---|
| M1 quarantine | `diagnostics.rs:38-59, 168-234` | FIFO `VecDeque<(usize, Layout)>` behind `LazyLock<Mutex<…>>`, byte-capped; hooked at `alloc.rs:302` |
| M2 scrub | `diagnostics.rs:128-162` | word-wise + byte-tail poison `0xDEAD2FEE_DEAD2FEE`; hooked at `alloc.rs:302` via `scrub_and_dispose` |
| M3 parity | `diagnostics.rs:236-339` | atexit registered from `alloc.rs:219`; `alloc_parity_report` pure; abort at `:300-304` |
| A1 inc-liveness | `rc.rs:489-495` (debug) + `:512-516` (release-gated) | the genuinely-new assert; **the crate's best-instrumented seam** |
| A2 dec-liveness/underflow | `rc.rs:412-417, 432-443` | |
| A3 drop-glue underflow | `drop.rs:83-88, 105-117` | |
| A4 dealloc size sanity | `alloc.rs:240-279` | debug double-free + header-integrity; release size floor at `:269` |
| Fixed dealloc order | `alloc.rs:284-310` | `rc_trace` → capture `FREED_TRACKED` → scrub → quarantine-or-release → count. Matches design §4 exactly. |

Byte-identical-off is real: every gate is a `LazyLock<bool>` cached at first
read (`diagnostics.rs:41-94`), the quarantine `VecDeque` is never constructed
when off, and `ensure_parity_registered` (`:99-112`) registers no atexit when
both parity gates are unset. `diagnostics/tests.rs:134` pins the defaults.

### 2.2 What the modes actually detect (probe evidence)

Probe run from the sanctioned scratch dir with `CRANELISP_LIB` set, never the
repo root:

```
(defn main [] (Pure "hi"))   # the 0745 program-result-value leak
CRANELISP_ALLOC_PARITY=1 cranelisp --run leak.cl --no-cache
→ [ALLOC_PARITY] IMBALANCE — LEAK (allocs > deallocs — blocks never freed)
  [ALLOC_PARITY]   ALLOC_COUNT=2 DEALLOC_COUNT=1 delta=1
  [ALLOC_PARITY]   surviving live allocations: 1
  [ALLOC_PARITY]     0xb792da84c720 size=26 payload@16=0x2
→ Aborted (core dumped)
```

**M3's full production wiring — counters → atexit → dump → abort — works.** I
verified it end-to-end. That is worth recording because *no committed test
proves it*, and the design's release-capability claim (`diagnostic-modes.md:198-204`,
"parity uses the always-on `ALLOC_COUNT`/`DEALLOC_COUNT`") rests on it.

### 2.3 Is R8's VERIFIED grade earned at the source? **No — it is inherited.**

The W7 bar (matrix §"W7 re-audit", `memory-safety-coverage.md` §4.1 prong 2) is:
a row is VERIFIED only with a cited **plant of the fault the instrument claims
to catch, and an observation of detection**. "The mechanism exists at file:line"
and "a test exercises it" are both explicitly *not* that bar. Applying it to the
crate's own instruments, row by row:

| Instrument | Cited evidence | What the tests actually do | Verdict at the bar |
|---|---|---|---|
| **M1 quarantine** | "quarantine ×2" | `diagnostics/tests.rs:12, 35` construct a bare `Quarantine::new()` and hand it `std::alloc::alloc` blocks, then assert `blocks.len()` and FIFO order. **No freed-block reuse is planted; `alloc_with_rc` is never called; `quarantine_enabled()`/`scrub_and_dispose`/the `QUARANTINE` static are never exercised; no stale-dec assert is observed firing.** The e2e detection fence was retired S114 (`tests/macro_expansion_interior_alias_double_free.rs:220-240`), and the surviving M1 e2e (`ms_p6_mode_self_tests.rs:98`) is a *no-false-fire* test. | **asserted-but-unproven** |
| **M2 scrub** | "scrub ×2" | `diagnostics/tests.rs:64, 81` assert that `scrub()` memsets. **Nothing anywhere in the repository reads a poisoned word back**, plants a use-after-free, or observes the poison producing a wrong value / a fault / an `old_rc <= 0` trip. `grep -rn CRANELISP_SCRUB_FREED` over the whole tree returns exactly one live use: `ms_p6_mode_self_tests.rs:107`, a no-false-fire test. | **asserted-but-unproven — the weakest instrument in the crate** |
| **M3 parity** | "parity ×4" + `ms_p6_mode_self_tests:55` | The four `alloc_parity_report(…)` cells (`diagnostics/tests.rs:100-127`) DO plant synthetic imbalances and observe the report — this is a genuine, correctly-synthetic detection proof **of the pure report function**. The wiring (counters → atexit → abort) is unproven by test; the e2e that proved it is retired. | **partially proven** |
| **A1** | — | `rc/tests.rs:43` `a1_rc_inc_fires_on_stale_inc` allocates, frees, asserts the precondition, incs, and `#[should_panic(expected = "STALE RC INC")]`; `:56` is the positive control. **Synthetic, both polarities, at the production funnel.** This is the model the other rows should copy. | **VERIFIED** (debug half) |
| **A4 debug** | — | `alloc/tests.rs:64` plants a real double-free through `dealloc` and observes the panic. | **VERIFIED** (debug half) |
| **A1–A4 release faces** (`seam_hard_fail`) | — | `grep seam_hard_fail` → 6 call sites, **zero tests**. No test anywhere sets `CRANELISP_RC_DEC_CHECK` and observes a located abort. This is the same "ZERO standing positive assertions" that `memory-safety-coverage.md` §5 records for `RC_DEC_CHECK`. | **unasserted** |
| **A2/A3 debug** | — | No `should_panic(expected = "STALE RC DEC")` exists in `rc/tests.rs` or `drop/tests.rs`. (`drop/tests.rs:174`'s "NOT live" is `vec_runtime::debug_assert_live_buffer`, a different guard.) | **asserted-but-unproven** |

**Two consequences worth naming.**

First, R8's own citation is broken. The W7 matrix credits R8 with
"`ms_p6_mode_self_tests:55` plants a **teardown leak** e2e and observes the M3
abort." Line 55 of that file is inside the **tombstone comment** for
`m3_parity_catches_planted_leak`, retired at S115 W3c — the test does not exist.
R8's cited e2e detection proof is a citation of its own obituary. This is not
this crate's file to fix, but it is the evidence R8's grade rests on.

Second, the m1/m3 lesson has now recurred a **fourth** time in this crate's
orbit — and the crate is where the cure lives. `ms_p6_mode_self_tests.rs:47-54`
already names it precisely: *"the compliant durable shape is a test-only
injected imbalance at the intrinsics allocator/diagnostics seam behind an
inert-unless-set env gate … That hook is `/dev`(intrinsics) source — outside
`/testing`'s boundary — and did not land in this wave."* The owed item is
named, scoped, and unbuilt. `/qa` correctly refused to plant on 0745
(`0745-*.md`; a fence must not be collateral of someone else's fix), which
leaves the synthetic hook as the *only* route. It is the single
highest-leverage thing this crate could build.

### 2.4 The intrinsics half of the S115 RC work

The crate's own RC invariants are **asserted where the assert is cheap and
example-tested where it is not.** Concretely: the shallow-inc/dec discipline is
funnelled and guarded (`rc.rs:407-518`, nullary-tag guard, `debug_assert` on
both halves), but the *recursive* discipline — `drop.rs`'s six `consume_*`
functions (`consume_slist:134`, `consume_sexp:171`, `consume_vec_with:224`,
`consume_vec_of_string:256`, `consume_io_tree:280`, `consume_closure:517`),
which the crate `CLAUDE.md:64-66` correctly says "mirror the backend's inline
drop glue (`emit_rc_dec_with_inline_drop_glue`)" — has no invariant asserted at
all. There is no cross-check that any `consume_*` and its backend mirror agree.
The only evidence they agree is `drop/rc_balance.rs`'s 10 `assert_balanced`
alloc==dealloc cells — example-tested, per-shape, and blind to a *systematic*
divergence that both sides make identically.

This is the crate's largest **mirror** duplication and it is the one the crate
cannot unilaterally fix; it is stated here as design feedback, not as a defect.

### 2.5 The header's shape — the second-time question 0745 forces

`HeapHeader = { alloc_size: i64, rc: i64 }` (`cranelisp-types/src/heap.rs:18-37`),
16 bytes, no type tag, **no drop-glue pointer**. Every field access is a
positive offset from base, locked by `const _: () = assert!`. As a *layout*
this is right and a rewrite would keep it: two words is the minimum that
supports a sized free plus an RC, and the base-pointer convention (departing
from the sketch's interior pointer) has paid for itself.

But the shape has one structural consequence the crate does not state anywhere,
and 0745 is the bill arriving: **there is no generic "release this heap value"
operation, and there cannot be.** `consume_shallow` is shallow-only by contract
(`rc.rs:386-405`); every deep release is type-directed, either by the backend's
inline glue or by picking the right `drop::consume_*` by hand. So at every seam
where a heap value *leaves typed context*, nobody can release it:

- `0745-*.md` documents exactly this — the `Pure` payload's reference transfers
  to the returned program result, `consume_io_tree`'s `IO_TAG_PURE` arm
  deliberately does nothing with it, and "**nobody releases it**"; the FIXME's
  own resolution is blocked because the owner must "know `main`'s return type
  and hence whether the `i64` is a" heap pointer. That is not an int bug and not
  a backend bug — it is the header's shape presenting its invoice.
- The same shape recurs at `HostCallbacks` (a DLL gets an `i64` and a
  base-vs-payload convention, `alloc.rs:331-340`, DEF-6's origin) and at the
  `Pure`-payload / trampoline-return seam generally.

A second-time solution would make this an **explicit, recorded architectural
choice** rather than an emergent one. Two coherent answers exist: (a) keep the
2-word header and make "a value leaving typed context has a *named* releasing
owner" an enumerated invariant — every such seam gets a register row and a
protocol; or (b) add a third header word (glue fn-ptr or type id) and gain a
generic releaser at the cost of 8 bytes per allocation and a version bump. The
finding is not that (b) is right. The finding is that **the choice has never
been made, and 0745 is the third seam to trip over it.** Routing this as an
`/arch` design question is the recommendation (R-6); it is also the honest
framing for 0745's "/arch consult REQUIRED on the release mechanism".

---

## 3. Duplication (three code facets + spec facet)

**Mirror.** The `drop::consume_*` ⟷ backend `emit_rc_dec_with_inline_drop_glue`
pair (§2.4). Real, deliberate, correctly documented — and unasserted. Past the
"a defect class recurring across mirrors" threshold? Not yet: 0633/0638 were
*key*-identity defects, not mirror-divergence defects. Watch, don't cut.

**Divergent — the S87 F3 residue, unfixed and now contradicted by the record.**
`crates/cranelisp-intrinsics/CLAUDE.md:32-36` states:

> `heap_access::{read_i64,write_i64}` (`pub(crate)`, MED-1/FIXME 0370) is the
> **single owner** of the raw `*(base+off)` primitive — do not open-code it

Source at HEAD:

| Site | Signature | Delegates to `heap_access`? |
|---|---|---|
| `heap_access.rs:31,40` | `(base: i64, offset: isize)` | — (the declared owner) |
| `trace.rs:199,210` | `(base: i64, offset: usize)` | **yes** (`:200`, `:211`) — a thin type-adapting wrapper, fine |
| `drop.rs:67` | `(base: i64, offset: usize)` | **no** — open-codes `*((base as *const u8).add(offset) as *const i64)` |
| `vec_runtime.rs:63,72,81` | `read_len` / `read_cap` / `read_data_ptr` | **no** — own offset consts |

`heap_access` has **two** production callers (both in `trace.rs`); everything
else in the crate reaches around it. And `drop.rs:208-210` declares its own
`VEC_LEN_OFFSET`/`VEC_CAP_OFFSET`/`VEC_DATA_PTR_OFFSET` triple over the *same*
Vec layout that `vec_runtime.rs` already owns — two layout-accessor families for
one layout, which is precisely S87's NEW-3, verbatim, three sprints on. The
`CLAUDE.md` sentence is the finding: a single-owner claim that a `grep` refutes
is worse than no claim, because the next code-touching agent trusts it.

**Entry-point.** Clean. Every RC op routes through one of the three funnels; the
`catalog.rs` name-agreement contract is single-owner with a completeness +
uniqueness guardrail (`catalog/tests.rs:59`, positive and negative).

**Spec-surface redundancy.** None surfaced from this context — it exposes no
language construct.

---

## 4. Record integrity — claims a file-open refutes

The S114 assessment's headline recurred here. Each of the following was verified
against source, not inferred.

| # | Claim | Where | Reality |
|---|---|---|---|
| **RI-1** | catalog is "16 core + the 12 `cranelisp_trace_*` family + `catch-runtime-error`" (= 29), authority = "`name_set_is_exactly_the_expected_29`" | `lib.rs:128-133` (the `/arch`-approved facade `//!`) | The table holds **37** entries; the test is `name_set_is_exactly_the_expected_37` (`catalog/tests.rs:59`), `EXPECTED_NAMES` (`:6-52`) lists 37. **Both the count and the cited test name are wrong.** This is S87 HIGH-1 recurring: the S87 cure was "cite the test constant, never restate the number", and it failed because the *test's name carries the number*, so the citation is itself a stale-count carrier. |
| **RI-2** | `heap_access` is the single owner of raw heap reads; "do not open-code it" | crate `CLAUDE.md:32-36` | Refuted by `drop.rs:67`, `vec_runtime.rs:63/72/81` (§3). |
| **RI-3** | `alloc_count` "read by int's `/mem` slash command"; `reset_counts` "Called between tests for isolation"; "test contexts call `reset_counts` at session start" | `alloc.rs:59-61, 110-111` | The `/mem` half is **true** (`src/repl/commands.rs:1137-1145`, `src/repl/format.rs:16-18`). But `reset_counts()` has **zero callers anywhere in the repository**, and `bytes_peak()` has zero callers. Both are `pub`. |
| **RI-4** | root re-exports `alloc_count, bytes_current, dealloc_count` serve "`src/{session_v4,pipeline,platform}.rs`" | `lib.rs:239` | Actual consumers are `src/repl/commands.rs` + `src/repl/format.rs`. |
| **RI-5** | `diagnostic-modes.md` is "**DESIGN (S113 W5a), pre-implementation**"; §7 lists three stale-citation fixes owed to `/dev` under FIXME 0656 | `design/intrinsics/diagnostic-modes.md:3-4, 291-310` | Implemented S113 and extended S115. The §7 rider is **drained** — `layout.rs:3` and `:49` now correctly cite int's `src/exe.rs::generate_startup_object` / `define_cstr_data`. The doc still prints the owed work. |
| **RI-6** | `design/intrinsics/` "Documents here" table | `design/intrinsics/CLAUDE.md` | Omits `diagnostic-modes.md`, the crate's most-cited design doc this sprint. |
| **RI-7** | `design/int/reactor.md` cited **61 times** in this crate's source + once in `Cargo.toml:11` | `reactor.rs`×2, `io.rs`×3, `catalog.rs`×1, `strand.rs`×1, `io/tests.rs`×15, `reactor/tests.rs`×39 | The file is at `design/intrinsics/reactor.md`; `design/int/reactor.md` **does not exist**. Relocated at S97 (FIXME 0486), recorded in `design/intrinsics/CLAUDE.md` — and 61 citations were never re-pointed. Every `// spec:` line among them is an unresolvable anchor. |
| **RI-8** | seam-map test counts "current at seeding" | crate `CLAUDE.md:19-21` | 13 of 14 counts still exact; `rc` is 26 in the doc, **28** at HEAD. The map's *shape* claim (which modules externalize vs inline) is fully correct and is the part worth keeping. |
| **RI-9** | R8's e2e detection proof is `ms_p6_mode_self_tests:55` | `tests/plan/s115-instrumentation-matrix.md` W7 table | Line 55 is inside the tombstone for the **retired** `m3_parity_catches_planted_leak`. (Not this crate's file — routed to `/qa`.) |

Verified-true and worth recording so nobody "fixes" them: the base-vs-payload
DEF-6 discipline and its fn-ptr identity pin (`lib.rs`, `host_callbacks`), the
blessed layout-ABI `const _: () = assert!` locking, the `concurrency-runtime`
feature retirement (`Cargo.toml:6-12`), `reactor`/`strand` `pub(crate)`
(`lib.rs:214, 226`), `diagnostics` `pub(crate)` (`:182`), the IVar SeqCst
carve-out, and the "no hand-written `Drop for EffectPoll`" warning. The crate
`CLAUDE.md` is, RI-2/RI-8 aside, an unusually high-fidelity document.

---

## 5. R13 — re-examined

R13 (fork-join error-slot ferry) is `unasserted` and parked with explicit user
sanction at S115 Phase 1, gated on the test-discovery implementation wave
(`safety-invariants.md:211`; matrix row at `:60`).

**Parking it remains right. The status word and the trigger are both wrong.**

- The ferry is **live production code today**, serving spec §12.4.3 lenient
  eval, entirely independent of test discovery: `ivar.rs:15-30` (the `+40`
  error slot), `:662-668` (`ivar_force` stashes the worker's panic), `:688-720`
  (`ivar_dealloc` frees the ferried String), plus `panic::set_runtime_error`
  join-side. Gating the *assert* on "the test-discovery implementation wave"
  mis-states why it is parked — the invariant is exercised on every lenient
  spark that panics, now.
- The status word `unasserted` ("**the hole**") also undersells what exists.
  `ivar/tests.rs` carries planted-fault coverage with both polarities:
  `:157-173` plants a thunk panic and asserts the message is ferried into the
  `error` field; `:183-204` asserts `ivar_dealloc` frees the ferried String (a
  leak plant); `:229` is the negative control (the ferry does not fire without a
  real panic); `:1044` covers the backoff-wait re-raise path. By the W7 bar this
  is a **proven** unit-tier instrument, not a hole.

So the honest re-grade is: the *mechanism* is well-instrumented at the unit
tier; what is missing is a tier-3 assert at the fork-join boundary, whose
absence is a cost decision. Re-word the row rather than schedule work (R-7).

---

## 6. Recommendations

Seven, ordered by leverage. Each carries evidence, cost class, proposed owner,
and a "done" that cures the risk rather than the symptom.

### R-1 — Build the synthetic fault-injection hook, and give M1/M2/M3 a real detection proof each

**Evidence.** §2.3. M2 has zero detection evidence in the entire repository; M1's
was retired at S114 and declared non-re-plantable from live defects; M3's
production wiring works (probe, §2.2) but no committed test says so. The owed
item is already named and scoped in `tests/ms_p6_mode_self_tests.rs:47-54` as
`/dev`(intrinsics) source that "did not land in this wave", and `/qa` has
already (correctly) refused the only available live plant (0745).

**Done.** A test-only, inert-unless-set injection hook at the
`alloc`/`diagnostics` seam, plus **one plant-and-detect cell per mode driving
the production funnels** (`alloc::alloc_with_rc` / `alloc::dealloc` with the
gate ON, not hand-built `Quarantine` instances):

- M1 — free a block under quarantine, assert the address is never re-handed by a
  subsequent `alloc_with_rc`, and assert the stale-dec/inc assert fires against
  it (the keystone claim of `diagnostic-modes.md` §1);
- M2 — free a block under scrub, read the payload back, assert poison; and
  assert a stale `rc_inc`/`consume_shallow` against a poisoned rc trips
  `old_rc <= 0` (the design's stated third interpretation, `:130-133`);
- M3 — inject an imbalance and observe the atexit dump + non-zero abort, both
  polarities (leak and double-free);
- each fail-on-revert demonstrated; the e2e face returns as
  `m3_parity_catches_injected_imbalance` per the tombstone's own plan.

Also cover the four `seam_hard_fail` release faces (A1–A4) under
`CRANELISP_RC_DEC_CHECK` — today `seam_hard_fail` has six call sites and zero
tests, which is `memory-safety-coverage.md` §5's "ZERO standing positive
assertions" reproduced inside the crate that owns it.

**Cost.** Medium (one `/dev` change-set + one `/testing` e2e face).
**Owner.** `/dev`(intrinsics), with `/testing` for the e2e cell and `/qa` to
re-grade R8 afterwards.

> This is the recommendation that matters. The other six are hygiene by
> comparison. It is also the one that turns R8's inherited grade into an earned
> one, and it retires the m1/m3 lesson at its source instead of recording its
> fourth occurrence.

### R-2 — Cure the catalog-count recurrence at its mechanism, not its value

**Evidence.** RI-1. S87 closed this exact finding (HIGH-1, "three-way catalog
count disagreement") with the cure "cite the test constant, never restate the
number". It recurred within three sprints because the test is *named* for the
count, so the citation carries the stale number and the prose restated it anyway.

**Done.** `catalog/tests.rs`'s test renamed to a count-free name
(`name_set_is_exactly_expected`); `lib.rs:128-133` states the *composition*
("core + the `cranelisp_trace_*` family + `catch-runtime-error`") with **no
integer and no number-bearing symbol**; the count exists in exactly one place,
`EXPECTED_NAMES.len()`. The generalisable rule — *a symbol whose name encodes a
count is a stale-count carrier, not a citation* — is worth stating wherever
`/review` keeps its checklist.

**Cost.** Small. **Owner.** `/arch` (the facade `//!` is `/arch`-approved) with
`/dev` for the test rename.

### R-3 — Converge the three `read_i64`s, or retire the single-owner claim

**Evidence.** §3, RI-2. Carried from S87 F3 (then MED-1's residue), third sprint
open. `heap_access` has two production callers; `drop.rs:67` open-codes the
deref; `drop.rs:208-210` duplicates `vec_runtime`'s Vec layout accessors.

**Done.** Either (a) `drop::read_i64` delegates to `heap_access` as `trace.rs`
already does, and `drop.rs`'s `VEC_*_OFFSET` triple reads `vec_runtime`'s
consts — after which the `CLAUDE.md` sentence is true; or (b) the
`CLAUDE.md:32-36` claim is downgraded to what is actually true. **(a) is
strongly preferred** — the sentence is right and the code is wrong, not the
reverse. Note this is a *soundness-neutral* change: every site is
`// SAFETY:`-commented today.

**Cost.** Small. **Owner.** `/dev`(intrinsics).

### R-4 — Remove `reset_counts` / `bytes_peak`, or protect M3 from them

**Evidence.** RI-3. Both are `pub` with zero callers anywhere; `reset_counts`'s
rustdoc names a caller that does not exist. This is not merely dead surface: it
is a **live hazard to the crate's own instrument**. `reset_counts()` zeroes
`ALLOC_COUNT` and `DEALLOC_COUNT` — which `diagnostics.rs:291-292` reads as M3's
sole evidence base, and which are M3's *only* release-mode signal
(`diagnostic-modes.md:198-204`: the live-set enrichment is debug-only). Any
future caller silently converts M3's parity check into a lie, with no diagnostic.
This is a sibling of S87's F4 (`IntrinsicEntry::is_runtime`, also still `pub`,
also still consumer-free — `grep` shows only its own derivation test at
`catalog/tests.rs:152` and two prose mentions), so it is a **recurring class**
in this crate: public surface carried for an un-arrived consumer.

**Done.** Both removed from the public surface and `public-api.txt` (preferred);
or, if kept, M3 gains a guard (a generation counter, or `reset_counts` refusing
to run once a parity gate is on) and rustdoc that states the hazard.

**Cost.** Small. **Owner.** `/arch` (public surface) with `/dev`.

### R-5 — Re-point the 61 stale `design/int/reactor.md` citations

**Evidence.** RI-7. The file moved to `design/intrinsics/` at S97 (FIXME 0486)
and 61 in-crate citations plus `Cargo.toml:11` were never updated;
`design/int/reactor.md` does not exist. 15 of them are `// spec:` anchors in
`io/tests.rs` and 39 in `reactor/tests.rs`, so `plan/spec_link_check.py`-class
traceability over this crate is resolving against a missing file.

**Done.** All 62 re-pointed to `design/intrinsics/reactor.md`; mechanical,
`sed`-able, no behavioural effect.

**Cost.** Small. **Owner.** `/dev`(intrinsics).

### R-6 — `/arch`: rule on the header's shape and the "value leaves typed context" seam family

**Evidence.** §2.5. `HeapHeader` is `{alloc_size, rc}` with no glue pointer, so
no generic release exists; every deep release is type-directed. 0745 is the
third seam to trip over this (after DEF-6's base-vs-payload and the
`Pure`-payload/trampoline return), and its own FIXME records that the release
mechanism is blocked pending an `/arch` consult because the releasing party must
know the value's type. Today the constraint is emergent, stated nowhere, and
rediscovered per incident.

**Done.** An `/arch` ruling recorded in `safety-invariants.md` (a register row)
and `bounded-contexts.md` §4b, choosing explicitly between: **(a)** keep the
2-word header, and make "every seam where a heap value leaves typed context has
a named releasing owner" an enumerated invariant with the seams listed
(program-result value, `Pure` payload, `HostCallbacks` returns, `--link` startup
return); or **(b)** add a third header word (glue fn-ptr / type id), accepting
+8 bytes per allocation and a layout version bump, and gain a generic releaser.
Either answer unblocks 0745 at the right altitude; the current state — implicit
(a) with no enumeration — does not.

**Cost.** Medium (an `/arch` pass; **not** an implementation commitment).
**Owner.** `/arch`, with `/design`(intrinsics) + `/design`(int) consulted.
**Pairs with** the S116 0745 carry — do not resolve 0745 without this.

### R-7 — Record-integrity batch (documents)

**Evidence.** RI-5, RI-6, RI-8, RI-9, and §5.

**Done.**
- `diagnostic-modes.md`: drop the "pre-implementation" banner (`:3-4`) and the
  drained §7 FIXME-0656 rider (`:291-310`, verified fixed at `layout.rs:3/:49`);
  §6's self-test paragraph becomes true when R-1 lands, so leave it as the
  specification it is. → `/design`(intrinsics)
- `design/intrinsics/CLAUDE.md`: add `diagnostic-modes.md` to the Documents
  table. → `/design`(intrinsics)
- crate `CLAUDE.md:19-21`: `rc` count 26 → 28; better, **delete the counts and
  keep the shape claim** (which modules externalize vs inline is the durable,
  useful half; the integers are decay-in-waiting and 1-of-14 has already
  drifted). → `/dev`(intrinsics)
- `safety-invariants.md` R13: re-word the park trigger to the lenient-eval
  ferry's own grain (the ferry is live production today, not test-discovery
  machinery), and re-grade off `unasserted` given `ivar/tests.rs:157/183/229/1044`
  are planted, both-polarity, unit-tier proofs (§5). → `/arch`
- `s115-instrumentation-matrix.md` W7: R8's cited e2e proof
  (`ms_p6_mode_self_tests:55`) points at a tombstone; re-cite or drop, and
  re-grade M1/M2 to `asserted-but-unproven` per §2.3 — which is the bar working,
  not a regression. → `/qa`

**Cost.** Small (one batch). **Owner.** split as annotated.

---

## 7. Disposition trail

*(Appended at S116 Phase 1 by `/sprint` — accepted → FIXME number, or declined →
rationale. Not written by `/audit`.)*

| # | Disposition | Note |
|---|---|---|
| R-1 | | |
| R-2 | | |
| R-3 | | |
| R-4 | | |
| R-5 | | |
| R-6 | | |
| R-7 | | |

### Carried from S87 (`audits/cranelisp-intrinsics-s87.md`)

| S87 finding | Status at S115 |
|---|---|
| NEW-1 `call_continuation` missing `// SAFETY:` | **RESOLVED** |
| NEW-2 `vec_set_copy` RC asymmetry (→ `/arch`) | Superseded by the S115 backend RC/ownership track; not re-derived here |
| NEW-3 / F3 open-coded heap reads + `drop.rs` Vec-accessor family | **STILL OPEN**, third sprint → R-3 |
| NEW-4 / F4 `IntrinsicEntry::is_runtime` pub, no consumer | **STILL OPEN**, third sprint → folded into R-4 (same class) |
| NEW-5 stale `dispatch_par_branches` doc refs | **RESOLVED** |
| NEW-6 `panic!` on unknown IO tag | Not re-derived (unchanged; the ADT-corruption fail-fast rationale stands) |
| HIGH-1 catalog count disagreement | **RECURRED** → R-2 |
