# Memory-safety diagnostic modes and RC/alloc seam checks

Owner: `/design` (intrinsics). Implements
`crates/cranelisp-intrinsics/src/diagnostics.rs` and the hooks in
`alloc.rs`, `rc.rs` and `drop.rs`.

Everything here serves safety-register row **R8** (RC balance: every
allocation has exactly one net free) in `design/arch/safety-invariants.md` §4.
The three modes are R8's dynamic-lane mechanism (ladder tier 5); the seam
checks are its asserted mechanism (tier 3, `safety-invariants.md` §2). `arch`
owns the row, and R8's detector grades are `qa`'s.

Scope: env-gated allocator behaviour and checks inside intrinsic bodies. There
is no ABI, catalog, `cranelisp-types` surface or emitted-IR change. A change
needing any of those goes to `arch`.

Section numbers are stable: tests, the crate memory and sibling designs cite
them.

**Evidence status.** The modes, the A1–A4 release faces, the fault-plant
protocol (§7) and its eight detection triplets are in source, none `#[ignore]`d.
The end-to-end M3 cell and its clean control are in
`tests/intrinsics_m3_detection_s116.rs`. **Two limits bound any grade:**

- the M3 over-free row proves report polarity and atexit wiring, not a real
  double free (§7.2);
- the A2/A3/A4 release faces prove header *plausibility*, not that a pointer is
  a base (§7.5).

**Open:** FIXME 0857 (`qa`) regrades R8 against this evidence, carrying both
limits.

---

## 1. Why allocator-seam modes

Most of the suite cannot observe a use-after-free that does not change output,
or a leak at all (`tests/plan/memory-safety-coverage.md` §5). Under `--run` and
the REPL a prematurely freed block is usually still readable, so a wrong-
lifetime program can pass by layout luck.

The allocator seam is the one place every free flows through. The modes turn
layout luck into a deterministic fault at the offending operation.

**Quarantine is the keystone.** The stale-dec checks (`is_live` in the dec
funnels and the JIT's `rc_dec_check`) are defeated by reuse: once
`alloc_with_rc` hands the same address out again, a stale dec sees a live block.
M1 never releases a freed block, so it can never be live again and the existing
checks fire reliably. The modes serve as extra environment faces for the
tier-4 oracle lane (`tests/safety_oracle_lane.rs`).

## 2. The seam

| Actor | Role |
|---|---|
| `alloc::alloc_with_rc` | the only allocation funnel: writes the header, bumps `ALLOC_COUNT` and the byte counters, and (debug) records `LIVE_ALLOCS` and clears `FREED_TRACKED` |
| `alloc::dealloc` | the only free funnel, reached by every shallow and drop-glue free: bumps `DEALLOC_COUNT` and (debug) moves the address from `LIVE_ALLOCS` to `FREED_TRACKED` |
| `rc::consume_shallow`, `drop::atomic_dec_rc` | the two decrement funnels; every `drop::consume_*` routes through `atomic_dec_rc` |
| `rc::rc_inc` | the one shallow increment funnel |

Every mode hooks the two lifecycle funnels and the two always-on counters.
Nothing new is tracked.

## 3. The three diagnostic modes

All three are off by default, read their environment once per process through a
cached `LazyLock`, and live in Rust bodies, so every execution mode behaves the
same.

### M1 — no-reuse quarantine

- `dealloc` withholds the block from the system allocator instead of releasing
  it. The block is logically freed — counted, removed from `LIVE_ALLOCS`,
  recorded in `FREED_TRACKED` — but never handed out again.
- **Retention.** Unbounded by default: probe programs are short-lived, and
  keeping every block gives the strongest signal. `CRANELISP_QUARANTINE_MAX_BYTES`
  caps retained bytes, releasing the oldest blocks FIFO. The cap is in bytes
  because it must bound RSS; releasing the coldest blocks keeps recent-free
  UAFs caught.

### M2 — scrub on free

- `dealloc` overwrites the whole allocation (header and payload,
  `total_size` bytes, including a ragged tail) with the word
  `0xDEAD2FEE_DEAD2FEE`.
- The pattern is wrong under every reading: as an integer or tag it is a large
  negative value; as a pointer it is non-canonical, so a dereference faults at
  the use; as an RC word it trips the underflow checks and never looks like
  `rc == 1`.
- `FREED_TRACKED` captures the block's identity before the scrub. Composed with
  M1, the allocator never overwrites the poison.

### M3 — alloc/free parity

- At exit (one atexit handler, registered once), check
  `ALLOC_COUNT == DEALLOC_COUNT` and, in debug builds, that `LIVE_ALLOCS` is
  empty.
- Leaks show as `allocs > deallocs`; this is the face M1 and M2 cannot see,
  because a leaked block is never freed. An over-free shows as
  `deallocs > allocs`.
- On imbalance it prints the ledger, plus the surviving live blocks in debug,
  then aborts non-zero. An imbalance is an in-process invariant breach: a
  located hard failure, never a `Result`.
- `CRANELISP_ALLOC_PARITY_DUMP` prints the ledger at exit and continues.
  `CRANELISP_RC_STATS` only prints counts.

## 4. Environment contract and composition

| Variable | Effect |
|---|---|
| `CRANELISP_QUARANTINE_FREED` | M1 on |
| `CRANELISP_QUARANTINE_MAX_BYTES` | M1 byte cap; read only under M1 |
| `CRANELISP_SCRUB_FREED` | M2 on |
| `CRANELISP_ALLOC_PARITY` | M3 hard check |
| `CRANELISP_ALLOC_PARITY_DUMP` | M3 print-and-continue |
| `CRANELISP_RC_DEC_CHECK` | release gate for the A1–A4 seam checks (§5), shared with the backend's codegen-time dec check |

- **Composition.** The gates are independent. Quarantine, scrub and parity
  together are the strongest configuration. Order inside `dealloc` is fixed:
  capture identity → scrub → quarantine or release → bump `DEALLOC_COUNT`.
- **Off means no work.** With every variable unset, each funnel pays one cached
  boolean load per gate: no quarantine list, no atexit handler, no write.
- **Release-capable.** The modes read sizes from the header and use the
  always-on counters, so they run in release builds. Only the enriched
  `is_live`/`FREED_TRACKED` reporting is debug-only.

## 5. Seam checks A1–A5

Each seam has an always-on `debug_assert!` twin and a release face gated by
`CRANELISP_RC_DEC_CHECK`. The release face is the shared precheck (§7.5),
which runs first. Every seam keeps the nullary-tag guard ahead of both: a bare
tag is not a heap pointer.

| Row | Seam | Release face | Debug twin |
|---|---|---|---|
| A1 | `rc::rc_inc` | precheck: plausible header, `rc > 0` | `is_live` |
| A2 | `rc::consume_shallow` | precheck, plus the post-RMW underflow gate | `is_live`, `old_rc > 0` |
| A3 | `drop::atomic_dec_rc` | precheck, plus the post-RMW underflow gate | `is_live`, `old > 0` |
| A4 | `alloc::dealloc` | `header_size_plausible(total_size)` before `Layout` construction | double-free (`LIVE_ALLOCS.remove`) and header-integrity checks |
| A5 | `alloc::alloc_with_rc` | none | header scan under `CRANELISP_HEAP_SCAN` |

- The post-RMW gates stay. The precheck covers the planted single-threaded
  case; the post-RMW check covers a concurrent race.
- Both faces emit the prefix `[CRANELISP RC/ALLOC SEAM VIOLATION]`.

## 6. What the modes detect

| Fault class | Deterministic face |
|---|---|
| Premature free with a live alias (the false-`Fresh` family) | M2 poison on the stale read; M1 keeps the block out of reuse; A2/A3 at the stale dec |
| Wrong drop glue freeing the wrong sub-object | M2 on the stale read; M3 on the imbalance |
| Double free | the A4 debug twin; M3 as `deallocs > allocs`; under M1 the second free hits a quarantined block |
| Leak | M3 only |
| Type confusion on a live, correctly counted block | none by construction — a static judgement or the differential oracle catches it |

Detection rows are proven by the §7 triplets. Tests of mode internals are
controls, not detection evidence.

## 7. The test-only fault-plant protocol

A crate-private hook that plants one deterministic fault on a production
allocation so each detector can be shown to fire. It is compiled into every
build, so an end-to-end child exercises the real counter → atexit → report →
abort path. It adds no `pub` item, catalog entry, exported symbol, Cargo
feature, ABI, heap-layout or IR change.

### 7.1 Activation and the arming discipline

| Variable | Required value |
|---|---|
| `CRANELISP_TEST_FAULTS` | exactly `s116-detection-proof-v1`; anything else is fully off |
| `CRANELISP_TEST_FAULT` | exactly one `FaultPlant` spelling |

- The arm string is the protocol version, not a sprint. Committed children pin
  it; changing it silently disarms them.
- `FaultPlant` is closed: `M1StaleReuse`, `M2StaleRead`, `M3Leak`,
  `M3OverFree`, `A1ZeroRc`, `A2InteriorPointer`, `A3FreedPointer`,
  `A4MalformedHeader`.
- **Configuration errors.** With the arm set, a missing, empty, unknown or
  multiple spelling aborts with `[CRANELISP TEST-FAULT CONFIG ERROR]`. The
  parse is forced by the first hook call — the process's first allocation —
  so **the guarantee is state-and-action precedence:** the child aborts before
  any plant state exists and before any action applies. It is never a partial
  plant. Literal pre-allocation timing would need a pre-`main` seam the crate
  does not have, and is not required.
- With the arm absent there is no state construction, allocation, counter
  adjustment or failure. Plant variables never enable a detector; detector
  variables never plant.

**Arming is lane-scoped by construction.** These rules are a structural
invariant, enforced by `tests/detector_arming_discipline_guard.rs`:

- **Never suite-global.** No detector or plant variable is exported by the
  shell, `.cargo/config.toml`, `.config/nextest.toml`, a build script or a
  wrapper.
- **Never `set_var` in a shared process.** Every gate is a process-lifetime
  `LazyLock`, and the ledger and quarantine are process-global. A `set_var`
  after first read is a no-op that looks armed, and an in-process toggle makes
  results depend on scheduling.
- **The only legal arming** is a spawned child `Command` with `.env_clear()` and
  an enumerated allow-list (§7.6).

Globally arming M3 would abort every still-red leak guard and make every RED
read as "M3 fired". `review` rejects a change that arms a detector any other
way.

### 7.2 One funnel hook, closed events and actions

`alloc_with_rc` and `dealloc` call one hook, `test_fault_event(event) →
FaultAction`, which returns `NoAction` when unarmed. The event and action sets
are the protocol's entire surface.

| Event | Site | Legal actions |
|---|---|---|
| `PostAlloc { base, total_size }` | after header, counters and tracking | `NoAction`, `CapturePlant` |
| `PreFree { base, total_size }` | after the header read and its gated check, before debug tracking | `NoAction`, `SuppressFree` |
| `PostFree { base, total_size, withheld }` | after the `DEALLOC_COUNT` bump | `NoAction`, `ExtraDischarge` |

- **`CapturePlant`** records the base and size in the one-shot plant slot and
  touches no memory.
- **`SuppressFree`** returns before tracking removal, scrub, quarantine and the
  count. The block is genuinely leaked, so the ledger stays truthful. It fires
  once.
- **`ExtraDischarge`** bumps `DEALLOC_COUNT` once without touching memory. It
  is the only UB-free route to `deallocs > allocs`, so the M3 over-free row
  proves polarity and wiring only. The real double-free face is the A4 debug
  twin.

The hook provides no counter setter, pointer write, callback or replacement
allocator. RC plants enter through the ordinary `rc_inc`, `consume_shallow` and
`atomic_dec_rc` entries; tests never call `seam_hard_fail` directly.

**Selection is deterministic.** Rows needing a specific allocation (M1, M2,
A1–A4) capture the first `PostAlloc` whose size matches
`PLANT_MARKER_PAYLOAD`, a payload the compiler never emits. The two M3 rows
fire on the first matching event, so the same spelling works in a unit child
and in a compiler child.

**Observation.** The single read-only `fault_observation()` reports the plant,
whether it fired, the planted base and size, and quarantine-retained bytes. The
M2 stale read goes through `heap_access::read_i64`.

**Report identity.** An armed ledger plant prepends exactly this line to the
atexit report; the clean control prints no such line and never names the
plant:

```
[ALLOC_PARITY] test-fault plant M3Leak fired — injected alloc/dealloc parity imbalance
```

### 7.3 The eight plant triplets

Each row is a child-process triplet:

- **positive** — plant plus the detector under test;
- **clean control** — detector, no plant;
- **negative control** — plant, detector off.

Removing or bypassing the detector must make the positive fail. Where a row
also arms M1 or M2, those modes are **containment**, not the subject: they keep
the negative control's unrejected operation inside mapped, quarantined memory,
so no control gets its polarity by executing UB.

| Plant | Positive arms | Positive observes | Negative arms | Negative observes |
|---|---|---|---|---|
| `M1StaleReuse` | M1+M2+gate | the base is withheld and not re-handed across 64 same-layout allocations; a stale `rc_inc` is seam-rejected | M2+gate | zero retained bytes; the fixture performs no stale operation |
| `M2StaleRead` | M1+M2+gate | payload@16 reads `POISON_WORD`; a stale RC op is seam-rejected | M1+gate | the pre-free sentinel; no poison-derived rejection |
| `M3Leak` | parity | report naming the plant and leak face; surviving block listed; non-zero abort | plant only | no report line; normal exit |
| `M3OverFree` | parity | `deallocs > allocs` face; non-zero abort | plant only | no report line; normal exit |
| `A1ZeroRc` | gate | seam prefix at `rc_inc` with `rc=0`, before the `fetch_add` | plant only | no prefix; the block frees cleanly |
| `A2InteriorPointer` | gate | seam prefix at `consume_shallow`, header predicate, before the `fetch_sub` | plant only | no prefix; the debug twin aborts first (expected) |
| `A3FreedPointer` | M1+M2+gate | seam prefix at `atomic_dec_rc`, poisoned-header predicate | M1+M2 | no prefix; the debug twin aborts |
| `A4MalformedHeader` | M1 (uncapped) + gate | header set to `8`; seam prefix before `Layout` construction | M1 (uncapped) | no prefix |

- **Hook and fixture stay separate.** The hook only captures or applies a
  ledger action. Every corruption — zeroing an RC, forming an interior address,
  writing `8` into a header, the pre-free sentinel — is a fixture write through
  `heap_access::write_i64` on the captured production identity.
- **M1 asserts retention, not reuse.** The negative control must not assert
  that the base *is* re-handed; that would encode an allocator assumption.
- **A4 needs M1 uncapped in both legs.** A FIFO release under a byte cap would
  free the block with the corrupted layout.
- **The A labels** follow the fault classes of the
  [S116 detection-proof plan](../../tests/plan/s116-test-plan.md#4-track-c-positive-detection-proof).
- **M3's end-to-end cell**, `m3_parity_catches_injected_imbalance`, runs the
  compiler binary under this protocol. Its clean sibling is
  `m3_parity_clean_child_exits_normally_control`.

### 7.4 Safety and concurrency constraints

- At most one plant is armed, and it fires once through an atomic
  compare-exchange.
- A plant touches only the base and size captured from its production event.
  Validation precedes any RC atomic or `Layout` construction (§7.5).
- Retained blocks have one fixture owner. No test frees reclaimed memory or
  relies on allocator address reuse.
- **No control obtains its polarity by executing UB.**
- The protocol is process-global because the allocator is. Subprocess
  isolation means rayon and reactor frees cannot miss a thread-local override.
- Diagnostics name the plant and its identity.

### 7.5 Seam checks are prechecks

**Each gated check runs at the top of its seam, above the debug twin and above
the mutation it guards.** Both orderings are load-bearing:

- **Validation before mutation** (Principle 25): a check after the RMW is not a
  check, and would let a negative control reach its polarity by executing the
  mutation.
- **Above the twin:** test children run the debug profile, where a twin that
  fires first means the release face is never observed.

The triplets fail when only the order is reverted.

`seam_precheck(ptr, site)` is the single owner, called first in `rc_inc`,
`consume_shallow` and `atomic_dec_rc`. When the gate is armed it reads the
alleged base's two header words and rejects unless:

- **(a)** `header_size_plausible(alloc_size)`: the word converts to `usize`, is
  at least `HeapHeader::SIZE`, and forms a valid
  `Layout::from_size_align(size, 8)`; and
- **(b)** `rc > 0`.

`dealloc` applies predicate (a) to its `total_size` above its debug block, so a
poisoned header produces a located message instead of a `Layout` panic.

- **No alignment clause.** A `HeapString`'s size is `16 + 8 + byte_len` raw
  bytes (27 for `"abc"`), so requiring 8-alignment would reject every string
  in an armed lane. Padding strings would be a heap-layout version change.
- **Residual:** a wild word that is positive, at least 16 and Layout-valid
  passes (a) and is caught by (b) or not at all. Grade the release face as
  *plausibility, not proof of basehood*.
- **Fault risk is signal.** A wholly wild pointer may fault at the header read
  — a crash located at the offending seam, reachable only when armed.
- **Off costs nothing new:** the cached gate load was already present.

**Discrimination.** Positives assert the seam prefix is present and names the
plant and seam. Negative controls assert the prefix is absent; the child may
still terminate through the debug twin (`panicked at …`), which is the
containment working, not the detector.

### 7.6 Child-process harness shape

Every proof runs in a fresh subprocess.

- **Unit children** (M1, M2, M3 over-free, A1–A4) re-exec the crate's test
  binary through `std::env::current_exe()`, selecting the child by test name.
  Each child body is an ordinary, non-ignored `#[test]` that returns
  immediately when unarmed, so every suite run executes unarmed inertness. The
  parent test spawns the child and makes the assertion.
- **Compiler children** (M3 leak and its clean control) run the built
  `cranelisp` binary on a minimal program.

Both use `.env_clear()` plus an enumerated allow-list at the call site: the
absolute program path, `CRANELISP_LIB` and `CRANELISP_PLATFORM_PATH` for
compiler children, any loader path genuinely needed, and the named detector and
plant variables. Each gets a unique temporary directory, and compiler children
run with `--no-cache`. They capture stdout, stderr and status, and inherit no
ambient `CRANELISP_*` setting.

### 7.7 Acceptance mapping

`tests/plan/s118-test-plan.md` §3.1 sets four per-row requirements:

| Requirement | Met by |
|---|---|
| Triplet at the production funnel; no bypass | the §7.2 hook and read-only observation; the §7.3 arms |
| Fail-on-revert, recorded per row | the §7.3 negative controls and the row comments in `diagnostics/tests.rs`; reverting the §7.5 order alone fails the A rows |
| Subprocess isolation | §7.1 and §7.6 |
| Unarmed inertness, unit-pinned | the non-ignored child bodies (§7.6) and the unarmed protocol row (§10) |

Governing principles: 5 (testability is structural), 6 (a closed three-event,
three-action surface rather than a general fault API), 7 (one precheck owner),
18 and 25 (validation before mutation), and 4 (arming stays per-lane).

## 8. Cost and concurrency

- **Unarmed:** one cached boolean or closed-enum load per gate. No allocation,
  lock, counter write, IR or ABI change.
- **Armed:** lane-only. The quarantine list is a `Mutex` with the same
  contention profile as `LIVE_ALLOCS`; the plant slot is a one-shot
  compare-exchange; the precheck adds two header loads.
- The IVar spark's SeqCst RC is untouched.
- **The arming discipline (§7.1) is a concurrency invariant:** a `LazyLock`
  gate and a process-global ledger cannot be re-armed safely inside a
  parallel-nextest process.

## 9. Layout and access ownership

The modes and plants read and write heap words, so they depend on one owner
for each fact:

- **`heap_access::{read_i64, write_i64}`** is the raw-access owner the modes,
  the plants and `drop.rs` use. `drop.rs` keeps no private reader
  (`crates/cranelisp-intrinsics/src/drop/tests.rs` guards it).
- **`vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}`** is the Vec
  layout authority; `drop.rs` imports it rather than copying it (same guard).
- **`drop.rs`** owns the ADT field offsets and `CLOSURE_DROP_GLUE_OFFSET`,
  derived from `HeapHeader::SIZE`; `ivar.rs` imports the closure offset.
- **There is no counter-reset seam.** `reset_counts` and `bytes_peak` are gone,
  because a reset would erase M3's only evidence. The counters are
  process-lifetime (bounded-context §4b, invariant 8). `alloc/tests.rs` guards
  their absence.

## 10. Unit-scenario matrix

| Submodule | Positive | Edge | Negative or detector |
|---|---|---|---|
| `diagnostics` protocol | unarmed ⇒ `NoAction`, no state, no count change, no allocation | exact arm plus one spelling fires once; marker size selects the intended allocation | unknown, empty or multiple spelling is a configuration error before any plant state or action; a wrong arm string is fully off |
| `diagnostics` precheck | a well-formed live base passes, including a ragged `HeapString` size | size exactly `HeapHeader::SIZE`; smallest and largest legal sizes; non-multiple-of-8 accepted | poisoned word, undersized, Layout-invalid, `rc == 0` and `rc < 0` rejected; the RC word is unchanged after a rejection |
| `diagnostics` modes | clean M1/M2/M3 children exit normally | odd-byte scrub tail; quarantine cap 0, exact and over, FIFO release order | both M3 polarities; the plant line present when armed, absent when clean |
| `alloc` | normal cycle; counters monotonic | header-integrity and double-free twins fire in debug | `M1StaleReuse`, `M2StaleRead`, both M3 plants; A4 rejection before `Layout` |
| `rc` | nullary tags no-op; live inc and dec unchanged | the 1 → 0 transition; non-atomic RC composition | `A1ZeroRc`, `A2InteriorPointer`; no mutation before rejection |
| `drop` | every `consume_*` unchanged | Vec with zero length or capacity; heap elements; recursive `SList`/`Sexp`/IO walks | `A3FreedPointer` through the precheck |
| `heap_access`, `vec_runtime` | accessor round trip; typed Vec field reads | largest field offset; the data pointer | the M2 stale read uses the shared accessor |
| catalog and facade | exact expected name set; surviving counter accessors | missing, duplicate or unexpected names | `reset_counts` and `bytes_peak` absent |
| end-to-end (`test`) | the clean M3 compiler child exits normally | `env_clear` plus allow-list; unique temporary directory; `--no-cache` | the leak child reports, then aborts non-zero; with parity off there is no report |

## 11. Cross-references

- [`ownership-and-disposal.md`](ownership-and-disposal.md) §6 — IO-node
  teardown, whose unknown-tag and reserved-witness arms report under this
  document's `CRANELISP_RC_DEC_CHECK` gate.
- `design/arch/safety-invariants.md` §2 (ladder tiers), §4 R8 (the owning row).
- `design/runtime/s118-structural-embedding-ownership.md` §4.1 — the first use
  of these detectors as an investigative instrument.
- `tests/plan/memory-safety-coverage.md` — the oracle lane and the blindness
  measurement.
- The [S116 fault classes](../../tests/plan/s116-test-plan.md#4-track-c-positive-detection-proof),
  the [S118 arming gate](../../tests/plan/s118-test-plan.md#1-certification-split-and-detector-arming-discipline-ruling-3-structural)
  and the [S118 triplet acceptance](../../tests/plan/s118-test-plan.md#31-eight-detector-rows-plant-triplets-0848).
- `crates/cranelisp-intrinsics/CLAUDE.md` §"Debug hooks" — the environment
  variable reference for contributors.
