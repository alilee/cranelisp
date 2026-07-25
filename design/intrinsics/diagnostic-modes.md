# Memory-safety diagnostic modes (tier-5) + RC/alloc seam asserts (tier-3)

Subordinate topic doc for `cranelisp-intrinsics`. **MODES IMPLEMENTED (S113
W5a); DETECTION-PROOF PROTOCOL DESIGNED S116, IMPLEMENTATION-READY S118 Phase
3.** Owner: `/design`(intrinsics); implementation is `/dev`(intrinsics), while
subprocess and lane wiring is `/qa`/`/testing`
(`tests/plan/memory-safety-coverage.md`, `tests/plan/s118-test-plan.md` §1/§3).
The M1/M2/M3 mechanisms and A1--A4 release faces exist; §7 adds the missing
positive proof that each detects the fault it claims to detect, and §9 lands the
owed single-owner convergence plus the approved subtractive API change.

**S118 Phase-3 refresh (this pass), against the S118 plan and arch verdict
rulings 2/3/6/7:**

- §7.1 records the **lane-scoped arming invariant** structurally (arch ruling
  3) — child `.env`/`env_clear` only, never suite-global, never `set_var`.
- §7.5 is new and load-bearing: the env-gated seam checks must become
  **prechecks**, hoisted above their mutation and above the always-on
  `debug_assert!` twins. Without it the four A rows are unprovable in the debug
  profile and validation-before-mutation is unimplementable. §5's assert
  inventory is amended accordingly.
- §7.2 closes the hook's event/action set; §7.3 gives the eight plant triplets
  explicit armed sets, faces, and UB-containment — the per-row fail-on-revert
  polarity `tests/plan/s118-test-plan.md` §3.1 requires; §7.6 pins the
  child-process harness shape; §7.7 maps the four test-plan acceptance
  requirements onto this design.
- **Subsection numbers §7.1–§7.4 are unchanged from S116** (the test plan and
  the committed e2e cite them); the three new subsections are appended as
  §7.5–§7.7.
- §9 becomes the one convergence change-set: 0850's remaining half (ruling 6)
  plus the ruling-7 subtractive API removal, with the invariance pin.
- §9a records the 0859 oracle protocol as a cross-reference only (ruling 2).
- §10 refreshes the submodule × complexity/edge/negative unit matrix and the
  serial `/dev` order.

Register trace: everything here is the **R8 row** (RC balance — "every alloc
exactly one net free; scope decs match incs") of `design/arch/safety-invariants.md`
§4. The three diagnostic modes are R8's `dynamic-lane` mechanism (ladder
**tier 5**, §2.5); the seam asserts are R8's `asserted` mechanism (ladder
**tier 3**, §2.3, in-process-invariant-breach ⇒ always-on `assert!` sub-form).
Selected per the W0-gate depth ruling (SPRINT.md W5: build order oracle → **tier
5 → tier 3** → tiers 1–2). The palette maps 1:1 onto the ladder — no parallel
taxonomy (Principle 7; SPRINT §Scope-A revision 1).

`/arch` owns the register row itself; this doc is the intrinsics-side mechanism
elaboration the row cites (SPRINT §Scope-A revision 1). Any change that needs a
register-row edit, a `cranelisp-types` surface, a backend→intrinsics
extern-signature change, or a catalog entry is out of scope here and files
FIXME `target: /arch` (SPRINT revision 2 — the modes are **intrinsics-internal,
env-gated allocator behaviour** with no ABI change).

---

## §1. Why tier 5 exists — the structural-blindness argument (grounded)

`tests/plan/memory-safety-coverage.md` §5 quantifies it: ~97% of the suite
cannot see a UAF that does not perturb output, >98% cannot see a leak, and the
strongest deterministic UAF signal (`RC_DEC_CHECK`) is asserted nowhere. The
0641 false-`Fresh` family is the canonical shape: because the ownership summary
declared `Fresh`, the return-value protect (inc) is elided, so a param's RC is
dec'd to zero at scope exit **while a returned alias still points at it** →
premature free → UAF. Under `--link` glibc turns the corrupted heap into a
deterministic SIGABRT; under `--run`/REPL the freed block is usually **still
readable by layout luck**, so the read returns the plausibly-correct value and
the test PASSES green. That false-green is exactly the blindness this track
ends.

The tier-5 modes convert layout-luck into determinism at the **allocator seam**
— the one place every heap value's free flows through — so a memory-safety
fault names itself at the faulting op instead of N crossings later (or never).
They are detector *multipliers* for the tier-4 oracle lane (`safety_oracle_lane.rs`):
the lane sets them as additional env faces (MS-P6), and a UAF that was
`--link`-only becomes RED in every mode.

### The load-bearing mechanism insight (why quarantine is the keystone)

The existing stale-dec assert (`rc::consume_shallow` and `drop::atomic_dec_rc`
both `debug_assert!(alloc::is_live(ptr))`, and the JIT-inline `rc_dec_check`)
is **defeated by reallocation**: `alloc_with_rc` clears `FREED_TRACKED` and
re-populates `LIVE_ALLOCS` at the same address, so a stale dec *after* the block
was reused sees `is_live == true` and passes silently. The premature-free UAF
then corrupts a live, semantically-unrelated allocation — the worst face. **No-
reuse quarantine (M1) withholds the freed block from the system allocator, so
`is_live` stays `false` forever** and the already-present stale-dec asserts fire
deterministically at the offending dec. Quarantine does not add a new check; it
makes the checks the crate already has *reliable*. That is the Principle-18 move
— enforce the invariant by representation (a freed block is never
representable as live again) rather than by racing the allocator.

---

## §2. Actors and functions (Principle 21 — before mechanism)

The seam is narrow and already single-sourced:

| Actor | Role at the seam |
|---|---|
| `alloc::alloc_with_rc` | the ONE alloc site; writes header, bumps `ALLOC_COUNT`/`BYTES_*`, records `LIVE_ALLOCS`, clears `FREED_TRACKED` |
| `alloc::dealloc` | the ONE dealloc site; every free (shallow + every recursive drop-glue leaf) funnels here before `std::alloc::dealloc`; bumps `DEALLOC_COUNT`, removes `LIVE_ALLOCS`, records `FREED_TRACKED` |
| `rc::consume_shallow` / `drop::atomic_dec_rc` | the TWO dec funnels; both already assert `is_live` + underflow before the atomic sub; `drop::consume_{slist,sexp,vec_with,io_tree,closure}` route through `atomic_dec_rc` (Principle 7 — no open-coded dec) |
| `rc::rc_inc` | the ONE shallow inc funnel; **asserts nothing today** (the tier-3 gap, §5 A1) |

The missing function the modes add: *"when a block is freed, make a later
touch of it deterministically wrong or fatal, and make the alloc/free ledger a
hard invariant."* Every mode hooks one of the two existing funnels
(`alloc_with_rc`, `alloc::dealloc`) plus the two atomic counters — nothing new
is tracked (Principle 7; the counters and side-tables already exist for
`RC_STATS`/FIXME-0494).

---

## §3. The three diagnostic modes (mode inventory)

All three: default OFF; env read ONCE at process start (cached `LazyLock`);
byte-identical-off (the env-unset path is the current code, unchanged); no
emitted-IR change (these are Rust bodies inside `runtime/alloc`/`runtime/dealloc`,
not codegen — the backend emits the same call it emits today). Composition in
§4.

### M1 — No-reuse-after-free quarantine

**What:** on `alloc::dealloc`, instead of calling `std::alloc::dealloc(base,
layout)`, push `(base, layout)` onto a process-global quarantine list and leave
the bytes mapped. `DEALLOC_COUNT` still increments, `LIVE_ALLOCS.remove` still
happens, `FREED_TRACKED` still records — the block is *logically* freed, just
never *physically* reclaimed, so it can never be re-handed by `alloc_with_rc`.

**Interaction with RC dec paths (dispatch item 1):** this is the keystone from
§1 — the block's address is permanently out of `LIVE_ALLOCS`, so the stale-dec
asserts in `consume_shallow`/`atomic_dec_rc`/`rc_dec_check` fire deterministically
on any dec of a prematurely-freed pointer (the 0641/0633 faces), instead of
silently succeeding against a reused chunk.

**Retention policy:** default = **unbounded** (repro/lane-scoped — a test
program is short-lived; the strongest signal keeps every freed block). A byte
cap `CRANELISP_QUARANTINE_MAX_BYTES=N` bounds retention for long-running use:
FIFO — once retained bytes exceed `N`, release the oldest quarantined blocks to
the system allocator until back under `N`. Releasing the oldest reopens the
reuse window for the *coldest* blocks only, so the recent-free UAF (the common
case) stays caught. Bytes, not count, because the leak/UAF pressure is byte
volume and the cap must bound RSS. When off, the list is never constructed
(zero cost).

### M2 — Scrub-freed-memory poisoning

**What:** on `alloc::dealloc`, immediately before release-or-quarantine,
overwrite the whole allocation (header + payload, `total_size` bytes) with a
poison pattern.

**Pattern choice (Principle 20 — make a UAF read unrepresentable-as-plausible):**
per-`i64`-word `0xDEAD2FEE_DEAD2FEE` ("dead to free"). It is chosen so a stale
read is deterministically wrong in **every** interpretation:
- as an `Int`/tag — a large negative value (`< NULLARY_TAG_THRESHOLD` is false
  and the magnitude is never a plausible small result), so a 0641-family
  `_repl_yields_correct_value` read returns garbage, not the expected int;
- as a **pointer** — `0xDEAD2FEE...` is non-canonical on x86-64/aarch64, so a
  UAF that dereferences a poisoned field faults immediately (SIGSEGV at the
  use) rather than wandering;
- as an **RC field** — a poisoned rc reads as a wild count, so a stale
  inc/dec trips the `old_rc > 0` underflow assert (and never coincidentally
  reaches the `old_rc == 1` free arm).

**Where it hooks:** the free seam (`alloc::dealloc`), after `FREED_TRACKED`
captures the pre-poison `(total_size, payload_word@16)` for the stale-dec
report (order matters — capture the identity *before* scrubbing). Scrub is most
lethal composed with M1 (the allocator never overwrites the poison with freelist
metadata); standalone it still poisons the instant-of-free-to-reuse window.

**Cost when off:** one cached env-bool load per `dealloc`; no write.

### M3 — Paired alloc/free hard-check

**What:** promote the alloc/free ledger from advisory stats to a hard
invariant. `ALLOC_COUNT`/`DEALLOC_COUNT` are already always-on atomics.
- **At process exit** (atexit, registered once — the `RC_STATS` pattern):
  assert `ALLOC_COUNT == DEALLOC_COUNT` and (debug builds) `LIVE_ALLOCS` empty.
- **Double-free face:** already caught at `alloc::dealloc` (the
  `LIVE_ALLOCS.remove(&addr).is_some()` debug_assert); M3 promotes it to the
  hard-check family so it fires in the release-gated lane too, and the exit
  ledger shows `DEALLOC_COUNT > ALLOC_COUNT`.
- **Leak face:** `ALLOC_COUNT > DEALLOC_COUNT` at exit (this is what R2-class
  leaks trip even when output is byte-identical — the face scrub/quarantine
  *cannot* see, because a leaked block is never freed).

**Report seam:** stderr dump at the exit hard-check, listing the imbalance and
(debug) the surviving `LIVE_ALLOCS` addresses with their `(size, payload@16)`;
mid-run inspection via `CRANELISP_ALLOC_PARITY_DUMP` (print-and-continue, no
abort) for bisecting a long run. **Hard-fail semantics:** on imbalance at exit
the process aborts non-zero *after* the dump — an imbalance is a compiler
defect (in-process invariant breach), so it is a located hard-fail, never a
laundered `Result` and never release UB (ladder §2.3). Distinct from
`RC_STATS`, which only *prints* the counts.

---

## §4. Env-var contract, composition, byte-identical-off

Naming follows the existing `CRANELISP_*` allocator/RC family
(`CRANELISP_RC_TRACE`, `_HEAP_SCAN`, `_RC_DEC_CHECK`, `_RC_STATS`,
`_NONATOMIC_RC`):

| Env var | Mode | Values |
|---|---|---|
| `CRANELISP_QUARANTINE_FREED` | M1 quarantine | set = on |
| `CRANELISP_QUARANTINE_MAX_BYTES` | M1 retention cap | `N` bytes; unset = unbounded |
| `CRANELISP_SCRUB_FREED` | M2 poison | set = on |
| `CRANELISP_ALLOC_PARITY` | M3 hard-check | set = on (registers the atexit check) |
| `CRANELISP_ALLOC_PARITY_DUMP` | M3 mid-run dump | set = print-and-continue |

**Composition:** the three are independent boolean gates and **compose freely**
— quarantine+scrub+parity is the intended strongest configuration and the
default the lane runs. Ordering inside `dealloc` is fixed: capture
`FREED_TRACKED` identity → (M2) scrub → (M1) quarantine-or-release → bump
`DEALLOC_COUNT`. `MAX_BYTES` only reads under M1.

**Default = all off, byte-identical-off (hard discipline, S99 precedent):** with
every var unset, each `dealloc`/`alloc` runs exactly today's code (one cached
env-bool load per mode, no branch taken). **No ABI change, no catalog entry, no
`cranelisp-types` surface, no emitted IR** — the backend emits the same
`runtime/alloc`/`runtime/dealloc`/inline-RC it emits now; the modes live entirely
inside the intrinsic bodies (SPRINT revision 2; the `alloc.rs` metadata that
detects double-frees today is the only state they touch). The modes therefore
also work identically in all execution modes (`--run`/REPL/`--link`) — no
mode-divergence surface.

**Release-capability:** M1/M2/M3 do **not** require the `#[cfg(debug_assertions)]`
side-tables — quarantine reads the size from the header, scrub reads
`total_size` from the header, parity uses the always-on `ALLOC_COUNT`/
`DEALLOC_COUNT`. They are env-gated in **both** profiles (the release lane can
run them). The `is_live`/`FREED_TRACKED` *reporting* enrichment stays
`#[cfg(debug_assertions)]` as today; the modes degrade gracefully to
counter-only reporting in release.

---

## §5. Tier-3 RC/alloc seam asserts (assert inventory)

Each traces R8; sub-form = in-process-invariant-breach ⇒ always-on `assert!`
(ladder §2.3). Pattern per the dispatch item 5: `debug_assert!` for the hot
default + an **env-gated release check** (reuse the existing
`CRANELISP_RC_DEC_CHECK` gate for the dec/inc liveness family, so release lanes
opt in without a new flag).

| # | Seam | Invariant asserted | Status today |
|---|---|---|---|
| A1 | `rc::rc_inc` | inc target is live + `rc > 0` (an inc of a freed/poisoned ptr is a defect) | **GAP — no check today**; add `is_live` + `rc > 0`, mirroring `consume_shallow`'s dec-half. The inc-half of FIXME 0494's dec-half check |
| A2 | `rc::consume_shallow` | dec target is live + `old_rc > 0` | present (`is_live` debug_assert + underflow); formalize the `RC_DEC_CHECK`-gated release variant |
| A3 | `drop::atomic_dec_rc` | dec target is live + `old_rc > 0` | present; it is the funnel every recursive drop-glue leaf (`consume_{slist,sexp,vec_with,io_tree,closure}`) routes through — the 0633/0638 recursive-free seams inherit it |
| A4 | `alloc::dealloc` | not a double-free (`LIVE_ALLOCS.remove` is `Some`) + header-integrity (`recorded == total_size`) | present (FIXME 0494); M3 promotes double-free to the hard-check family; add the `RC_DEC_CHECK`-gated release variant |
| A5 | `alloc_with_rc` | header written correctly; `total_size >= HeapHeader::SIZE` | present (`scan_live_headers` under `HEAP_SCAN`); no change — noted for completeness |

A1 was the only genuinely-new assert at S113; A2–A4 release-gate existing
debug-only checks so the release/`--link` lane earns the same signal. None
require an interface change — all are internal to intrinsic bodies. `rc_inc`'s
nullary-tag guard (`ptr < NULLARY_TAG_THRESHOLD`) is preserved ahead of the new
check (a bare tag is not a heap pointer).

**S118 amendment (§7.5).** Two changes to this inventory, both intrinsics-
internal and both prerequisites for the A-row detection proofs:

1. **All four gated checks become PREchecks** — hoisted above their mutation
   and above the always-on `debug_assert!` twins. A check that runs after the
   RMW it guards cannot satisfy validation-before-mutation, and in the debug
   profile it is never reached.
2. **A2 gains the release face it lacked.** "dec target is live" has no
   release-lane expression (`is_live` needs the debug side table), so the
   shared `seam_precheck` adds a **header-plausibility** predicate: the alleged
   base's `alloc_size` word must be `>= HeapHeader::SIZE` and 8-aligned. This
   catches an interior/non-base address (word@0 is a tag or field) and a
   poisoned/quarantined base (word@0 is `0xDEAD2FEE…`, not 8-aligned). It is a
   plausibility check, not a proof of basehood — grade it there (§7.5).
   `alloc::dealloc`'s A4 predicate widens the same way.

---

## §6. Acceptance — which REDs fire deterministically under the modes

The W5a obligation (SPRINT W5-open): **re-run the 15-RED W5-family acceptance
set under the modes BEFORE the W5b fix wave**, and the modes must make the
free-class faults fire deterministically (or the RED is characterized as
mode-invisible with the reason). `/qa`/`/testing` own the run (one-agent-one-
test-run); this design states the expected outcome per class.

**Fire deterministically under quarantine+scrub (M1+M2), all modes:**

- **0641 B-1/B-2/I-1/I-2** (`tests/false_fresh_provenance_residual.rs`, 8 REDs
  = 4 vectors × {REPL-value, `--link`-heap}). The premature free of the aliased
  param → M2 scrubs the block → the `_repl_yields_correct_value` read returns
  poison (deterministically wrong, no longer layout-luck green); M1 keeps it
  out of reuse so the `_link_does_not_corrupt_heap` face fires in JIT/`--run`
  too, not only under glibc `--link`. The A2/A3 stale-dec asserts also fire at
  the scope-exit dec of the freed alias.
- **MS-P7 COW-set→project** (`safety_oracle_lane.rs::safety_lane_cow_set_read_link_corruption_red`).
  Today `--link`-only (correct under `--run`); M1+M2 extend the deterministic
  signal into `--run`/REPL — the projection-out read hits poison. (This also
  supplies the discriminator MS-P7 records: whether the abort persists under
  `CRANELISP_NO_OWNERSHIP=1` decides the ownership-independent-backend vs
  elision half — the modes give a deterministic face in both toggle states.)
- **0633 DG-R1a/b/c** (`tests/adt_drop_glue_underkey.rs`). Wrong glue frees the
  wrong sub-object → M2 makes the subsequent stale read poison; M3's double-
  free/parity face catches the free imbalance; MS-P4 (module-axis cell) rides
  the same signal.
- **0638 macro-alias double-free** (`tests/macro_expansion_interior_alias_double_free.rs`,
  ×3 modes). Already fires the `alloc.rs:222` double-free debug_assert; M3
  promotes it to the hard-check family (fires in release-gated + `--link`), and
  M1 makes the second free hit a quarantined block (named, not a corrupted
  reused chunk). Robust across all three modes.

**Fires under paired-counter (M3) only:**

- Any **leak** RED in the family (R2-class `rc-miscount`): scrub/quarantine are
  blind to a leak (the block is never freed, so never scrubbed) — M3's exit
  parity (`allocs > deallocs`) is the leak face.

**Mode-invisible — characterized (not a modes failure):**

- **Multi-arity §5.1.2 wrong-accepts** (String heap-ptr read as `Int`). These
  are `wrong-accept` type-safety defects, **not** free-class: the heap block is
  live and correctly counted; reading a live String pointer as an Int yields a
  wrong value with **no allocator event**. The tier-5 allocator modes cannot
  see them by construction; they are caught by the tier-1/2 static judgment and
  the tier-4 differential oracle (behavioural divergence on/off), which is where
  the W5b frame places them. Correctly out of W5a scope.

The S113 implementation landed the mechanisms, but not this section's required
positive self-tests. S116 closes that evidence gap through the production-path
injection contract in §7. Mechanism-internal tests remain useful unit controls,
but cannot satisfy a detector row by themselves.

---

## §7. Test-only fault-plant protocol (S116 design, S118 implementation-ready)

**Status (S118 Phase 3): implementation-ready.** Nothing of §7 exists in source
at HEAD — `grep FaultPlant|test_fault crates/` is empty — so the two committed
M3 e2e cells (`tests/intrinsics_m3_detection_s116.rs`) are RED for absence of
mechanism, not for a wrong mechanism. This refresh fixes the four things the
S116 text left to implementation invention: the seam-check *ordering*
prerequisite (§7.5) without which the four A rows are unprovable in the debug
profile (and M1/M2's stale-RC legs lose their rejection), the hook's exact
event/action closure (§7.2), the child-process
harness shape (§7.6), and the per-row armed sets, faces, and UB-containment
(§7.3).

### 7.1 Boundary, activation, and the arming discipline

The injection seam is **crate-private and diagnostic-test-only in purpose**, but
is compiled into the executable so an e2e subprocess can prove the real
counter→atexit→report→abort wiring. It adds no `pub` item, catalog entry,
exported symbol, Cargo feature, ABI, heap-layout, or emitted-IR change.

Activation requires both exact child-process values:

| Variable | Required value | Purpose |
|---|---|---|
| `CRANELISP_TEST_FAULTS` | `s116-detection-proof-v1` | explicit protocol arm; absent or any other value is fully off |
| `CRANELISP_TEST_FAULT` | one closed `FaultPlant` spelling | selects exactly one plant |

The arm string keeps its `s116-` spelling: it is the protocol version, not the
sprint of landing, and the committed e2e children already pin it. Changing it
would silently disarm those cells.

The private closed enum is `FaultPlant::{M1StaleReuse, M2StaleRead, M3Leak,
M3OverFree, A1ZeroRc, A2InteriorPointer, A3FreedPointer,
A4MalformedHeader}` — the eight spellings `tests/plan/s118-test-plan.md` §3.1
names, unchanged. Parsing happens once per process. Unknown, empty, or
multiple spellings are a hard test-configuration error before allocation; they
never become a partial plant. With the arm value absent there is no state
construction, mutation, allocation, counter adjustment, or new failure. The
ordinary M1/M2/M3/A-gate variables remain detector controls; test variables
plant faults only and never silently enable the detector under test.

#### Arming is lane-scoped by construction (arch ruling 3; test plan §1)

This is a **structural invariant of the protocol**, not a test-hygiene
preference. State it here because `/qa`'s W1 static grep gate enforces exactly
this and the design is what the gate cites:

1. **Never suite-global.** No detector or plant variable
   (`CRANELISP_QUARANTINE_FREED`, `_MAX_BYTES`, `CRANELISP_SCRUB_FREED`,
   `CRANELISP_ALLOC_PARITY`, `_DUMP`, `CRANELISP_RC_DEC_CHECK`,
   `CRANELISP_TEST_FAULTS`, `CRANELISP_TEST_FAULT`) is exported at suite scope
   — not in the developer shell, not in `.cargo/config.toml`, not in
   `.config/nextest.toml`, not in a build script or wrapper.
2. **Never `set_var` in a shared process.** No test may call
   `std::env::set_var` on any of them. Every gate is a `LazyLock` read once per
   process, and the ledger + quarantine are process-global: an in-process
   toggle is order-dependent under parallel nextest and produces a grade that
   depends on test scheduling. A `LazyLock` already forced before the `set_var`
   makes the toggle a no-op that *looks* armed — the worst outcome for a
   detection proof.
3. **The only legal arming** is a spawned child `Command` with `.env_clear()`
   plus an explicit, enumerated allow-list (§7.6).
4. **The failure this prevents**: a globally-armed M3 aborts every still-red
   leak guard in the 28-RED baseline, so the whole Track-B acceptance
   arithmetic evaporates and every RED reads as "M3 fired". Track B runs its
   acceptance legs *with* detectors armed — per child, never per suite.

`/review` rejects any change-set that arms a detector outside a child
`.env`/`env_clear` construction. Existing per-child armed legs (the
`ms_p8_conj_leak` parity leg, the M3 subprocess pair) are already compliant.

### 7.2 One production funnel, closed event/action set

`alloc_with_rc` and `dealloc` remain the only lifecycle funnels. They call one
hook, `diagnostics::test_fault_event(event) -> FaultAction`, which returns
`NoAction` whenever the arm variable is absent. Both the event and the action
sets are **closed** — this is the whole API surface of the protocol, and
enumerating it here is what stops `/dev` from inventing a general fault API
(Principle 6):

| Event | Site | Payload | Legal actions |
|---|---|---|---|
| `PostAlloc` | `alloc_with_rc`, after header init + counters + tracking, before `rc_trace`/return | `{ base, total_size }` | `NoAction`, `CapturePlant` |
| `PreFree` | `dealloc`, immediately after the `total_size` header read, **before** the debug tracking block | `{ base, total_size }` | `NoAction`, `SuppressFree` |
| `PostFree` | `dealloc`, after the `DEALLOC_COUNT` bump | `{ base, total_size, withheld }` | `NoAction`, `ExtraDischarge` |

Action semantics, exhaustively:

- **`CapturePlant`** — record `(base, total_size)` in the one-shot plant slot.
  No memory is touched. This is how a fixture gets a *production-allocated*
  identity to corrupt or observe.
- **`SuppressFree`** — `dealloc` returns immediately: no `LIVE_ALLOCS`
  removal, no scrub/quarantine, no `DEALLOC_COUNT` bump. The block is
  **genuinely leaked**, so M3's ledger stays truthful and the report shows both
  the count delta and the surviving live address. Fires at most once.
- **`ExtraDischarge`** — bump `DEALLOC_COUNT` once more without touching
  memory. Fires at most once. **Honesty note for the 0857 regrade:** this is
  the only UB-free route to the `deallocs > allocs` polarity, so the M3
  over-free row proves the *report polarity and atexit wiring*, not a real
  double-free. The real double-free face remains the debug
  `LIVE_ALLOCS.remove` assert (A4/§3). Grade it there, not higher.

The hook must NOT provide counter setters, arbitrary pointer writes, callback
registration, or a replacement allocator. RC plants enter through the ordinary
`rc_inc` / `consume_shallow` / `drop::atomic_dec_rc` entry points; tests never
call `seam_hard_fail` directly.

**Plant selection is deterministic**, by row:

- rows needing a *specific* allocation (M1, M2, A1–A4) select at `PostAlloc`
  by an exact marker size: the child fixture calls
  `alloc::alloc_with_rc(PLANT_MARKER_PAYLOAD)` for a payload size the compiler
  never emits in that child, and `CapturePlant` fires on the first event whose
  `total_size` matches. One deterministic identity, no address guessing;
- rows that only need *an* allocation (M3 leak, M3 over-free) fire on the
  first matching event. This is what lets the same two spellings work
  identically in a Rust unit child and in the compiler-binary e2e child.

**One read-only fixture observation**, `pub(crate)`, no setters:
`fault_observation() -> FaultObservation { plant, fired, planted_base,
planted_total_size, quarantine_retained_bytes }`. M2's stale read goes through
`heap_access::read_i64` — the single mechanical read owner (§9). M1 requests
subsequent same-layout blocks through `alloc_with_rc` and never instantiates
`Quarantine` directly.

**Report identity (pinned by a committed e2e).**
`tests/intrinsics_m3_detection_s116.rs` asserts the child's stderr contains
`M3Leak`, `alloc`, `dealloc`, and (`parity` | `imbalance`) — all lowercase,
which today's `[ALLOC_PARITY] IMBALANCE …` report does not satisfy. When a
plant is armed the atexit report therefore prepends one line of exactly this
shape:

```
[ALLOC_PARITY] test-fault plant M3Leak fired — injected alloc/dealloc parity imbalance
```

The clean-control sibling must produce no such line, and must not print the
plant spelling anywhere.

### 7.3 The eight plant triplets

Each row is a child-process triplet: **positive** (plant + detector under
test), **clean control** (detector, no plant), **negative control** (plant,
detector under test off). Removing or bypassing a detector must make the
committed *positive* fail rather than false-green — that is the fail-on-revert
polarity `tests/plan/s118-test-plan.md` §3.1 makes a hard per-row acceptance
input.

Read the "armed" columns literally. Where a row arms M1 (and sometimes M2)
*in addition to* the detector under test, those modes are **containment**, not
the subject: they keep the negative control's un-rejected operation inside
mapped, quarantined memory so no control ever obtains its polarity by executing
UB (§7.4). A containment mode is never the detector whose absence the row
claims to detect.

| Row / plant | Detector under test | Armed (positive) | Positive observation | Armed (negative control) | Negative observation | Containment |
|---|---|---|---|---|---|---|
| `M1StaleReuse` | M1 quarantine | M1+M2+`RC_DEC_CHECK` | retained bytes > 0 and the planted base is withheld; across K=64 same-layout `alloc_with_rc` calls the base is never re-handed; a stale `rc_inc` on it is seam-rejected | M2+`RC_DEC_CHECK` (M1 OFF) | `quarantine_retained_bytes == 0`; the fixture performs **no** stale op | M1 absent ⇒ the freed block is reclaimed, so the negative control stops at the retention observation and never touches it |
| `M2StaleRead` | M2 scrub | M1+M2+`RC_DEC_CHECK` | fixture writes a sentinel at payload@16, frees; `heap_access::read_i64(base, 16)` reads exactly `POISON_WORD`, and a stale RC op on the poisoned base is seam-rejected | M1+`RC_DEC_CHECK` (M2 OFF) | the same read returns the pre-free sentinel, and no poison-derived rejection occurs | M1 keeps the block mapped in both legs |
| `M3Leak` | M3 parity | `ALLOC_PARITY` | atexit report naming the plant + leak face, non-zero abort; live set shows the surviving block | plant only (parity OFF) | no report line, normal exit (one block leaked, harmless) | a real leak is never UB |
| `M3OverFree` | M3 parity | `ALLOC_PARITY` | atexit report with the `deallocs > allocs` face, non-zero abort | plant only (parity OFF) | no report line, normal exit | ledger-only; no memory is freed twice |
| `A1ZeroRc` | A1 release face | `RC_DEC_CHECK` | seam prefix + `rc_inc` + `rc=0`, **before** the `fetch_add` | plant only (gate OFF) | seam prefix absent; rc returns to 1 and the fixture frees the block cleanly | block stays live throughout; `is_live` twin never fires |
| `A2InteriorPointer` | A2 release face | `RC_DEC_CHECK` | seam prefix + `consume_shallow` + header-plausibility predicate, before the `fetch_sub` | plant only (gate OFF) | seam prefix absent | the debug `is_live` twin aborts the negative control before the RMW — expected, recorded, not the detector's observation |
| `A3FreedPointer` | A3 release face | M1+M2+`RC_DEC_CHECK` | seam prefix + `atomic_dec_rc` + the poisoned-header predicate, before the `fetch_sub` | M1+M2 (gate OFF) | seam prefix absent | M1 keeps the quarantined base mapped; the `is_live` twin aborts the negative control |
| `A4MalformedHeader` | A4 release face | M1 (uncapped) + `RC_DEC_CHECK` | fixture writes `8` into the planted header; `dealloc` emits the seam prefix + size predicate **before** `Layout` construction and disposal | M1 (uncapped), gate OFF | seam prefix absent | M1 uncapped ⇒ `dealloc` never reaches `std::alloc::dealloc`, so a wrong `Layout` is never used to free; **`CRANELISP_QUARANTINE_MAX_BYTES` must be unset in both legs** or a FIFO release would free with the corrupt layout |

Row notes:

- **Hook vs fixture, kept separate.** The hook only ever *observes and
  records* (`CapturePlant`) or applies one of the two closed M3 ledger actions.
  Every corruption — zeroing an RC (A1), forming an interior address (A2),
  writing `8` into a header (A4), the pre-free sentinel (M2) — is a **fixture**
  write through `heap_access::write_i64`, applied to the production-allocated
  identity the hook recorded. That is what keeps the hook from becoming an
  arbitrary-pointer-write API (Principle 6) while every plant still acts on a
  real production allocation (Principle 5).
- **The A rows are only implementable after §7.5's precheck hoist.** As built,
  A2/A3/A4's positives are pre-empted by their debug twins and A1–A3's checks
  run post-mutation. Land §7.5 first (implementation order, §10).
- **M1's row proves retention and non-reuse**, which is the property §1 calls
  the keystone; the stale-op leg is the consequence, and it borrows M2's poison
  to make the rejection deterministic. Do not assert "the base *is* re-handed"
  in the negative control — that would encode a system-allocator reuse
  assumption. Assert the detector's own observable (retention) instead.
- **Clean controls** (detector on, no plant) exist for all eight rows and are
  the cheapest guard against a detector that fires on correct programs. For M3
  this is the already-committed `m3_parity_clean_child_exits_normally_control`.
- The A labels follow `tests/plan/s116-test-plan.md` §4's fault classes.
  Existing source comments using the older function-oriented inventory are
  reconciled in implementation so one label never means two plants.

M3 additionally has root e2e cell `m3_parity_catches_injected_imbalance`,
running the production compiler binary under this exact protocol and asserting
the full atexit report and abnormal status. Its clean sibling runs the same
minimal program with M3 on and no plant. Unit children own both M3 polarities;
e2e proves composition, not a second mechanism.

### 7.4 Safety and concurrency constraints

- At most one plant is armed and fires once via atomic compare/exchange.
- A plant touches only a base/size captured from that production event;
  range/lifecycle validation precedes any RC atomic or `Layout` construction
  (this is what §7.5 delivers).
- Retained blocks have one fixture owner and cleanup path. No test frees
  reclaimed memory or relies on allocator address reuse.
- **No control obtains its polarity by executing UB.** Every negative control
  either arms a containment mode (§7.3) or stops before the unsafe follow-on.
- The protocol is process-global because the allocator is; subprocess
  isolation means rayon/reactor frees cannot miss a thread-local override.
- Diagnostics include plant spelling and identity, not an unrelated address as
  the sole oracle.

### 7.5 Mechanism prerequisite — seam checks are PREchecks (S118 refinement)

**Load-bearing; without it the A-rows cannot be proven and §7.4's
validation-before-mutation rule is unimplementable.**

As built, every env-gated release seam check runs *after* its mutation and
*after* the always-on `debug_assert!` twin:

| Seam | As-built order | Consequence |
|---|---|---|
| `rc::rc_inc` | `debug_assert!(is_live)` → `fetch_add` → gate `old_rc <= 0` | check is post-mutation |
| `rc::consume_shallow` | `debug_assert!(is_live)` → `fetch_sub` → `debug_assert!(old_rc > 0)` → gate | debug twin aborts first |
| `drop::atomic_dec_rc` | `debug_assert!(is_live)` → `fetch_sub` → `debug_assert!(old > 0)` → gate | debug twin aborts first |
| `alloc::dealloc` | debug double-free + header-integrity asserts → gate `total_size < HeapHeader::SIZE` | debug twin aborts first |

Unit and e2e children run in the **debug profile**, where the `debug_assert!`
twins are live. A plant that trips a twin never reaches the gate, so the
positive assertion "the seam names itself" fails on a *working* detector — the
row is unprovable as written. And a post-mutation check violates §7.4: the
negative control's polarity would be obtained by executing the very mutation
the detector exists to prevent.

**Ruling for this design: the env-gated seam checks move to the top of their
seam, before the debug twins and before any mutation.** One shared owner in
`diagnostics` (Principle 7):

- `seam_precheck(ptr, site) -> ()` — no-op unless `rc_check_release_enabled()`.
  When armed: (a) read the alleged base's `alloc_size` word at offset 0 and
  reject unless it is `>= HeapHeader::SIZE` **and** 8-aligned; (b) read the RC
  word at offset 8 (relaxed) and reject unless `> 0`. Rejection is
  `seam_hard_fail` naming `site`, the pointer, and which predicate failed.
  Called first in `rc_inc`, `consume_shallow`, and `atomic_dec_rc`.
- `alloc::dealloc` hoists its existing gated header check above the debug
  block, and widens the predicate from `total_size < HeapHeader::SIZE` to
  "`< HeapHeader::SIZE` or not 8-aligned", so a poisoned (M2-scrubbed) header
  produces a located seam message instead of a `Layout` panic.

Properties:

- **Byte-identical-off preserved.** Off = one cached bool load, already
  present today; no new load, branch, or emitted IR.
- **(a) is the release face of "the dec/inc target is a live allocation
  base".** The `is_live` half needs `LIVE_ALLOCS` (debug-only), so the release
  lane has never had one. The header-plausibility predicate is its honest
  approximation: it catches an interior/non-base address whose word@0 is a tag
  or field value (A2), and it catches a poisoned/quarantined base whose word@0
  is `0xDEAD2FEE…` (not 8-aligned) (A3). It is a **plausibility** check, not a
  proof of basehood — `/qa`'s 0857 regrade must grade it at that tier and not
  as "base-pointer validity proven".
- **The existing post-RMW gates stay.** The precheck covers the planted,
  single-threaded case; the post-RMW check keeps the concurrent-race window.
  Both emit the same `[CRANELISP RC/ALLOC SEAM VIOLATION]` prefix.
- **Fault risk is a signal, not a regression.** The precheck dereferences the
  alleged base's first two words. A wholly wild pointer may fault at the read —
  a located crash at the offending seam, strictly better than the silent RMW it
  replaces, and reachable only with the gate armed.

This is the second genuinely-new assert since S113 (A1 was the first); §5's A2
row is amended by it. It is intrinsics-internal: no public item, no ABI, no
catalog entry, no `cranelisp-types` surface — no `/arch` gate.

#### Debug-twin discrimination (the rule the triplets assert against)

In the debug profile each A-seam has two faces: the always-on `debug_assert!`
twin (message: `panicked at …`) and the env-gated release check (message
prefix: `[CRANELISP RC/ALLOC SEAM VIOLATION]`). The triplets prove the
**release face** and discriminate by prefix:

- **positive** asserts the seam prefix is PRESENT and names the plant + seam;
- **negative control** asserts the seam prefix is ABSENT. The child may still
  terminate abnormally via the debug twin — that is the UB containment doing
  its job, recorded as the row's expected negative-control failure mode, never
  mistaken for the detector's observation.

### 7.6 Child-process harness shape

Every proof runs in a **fresh subprocess**; nothing toggles a gate in a shared
process (§7.1). Two child kinds, one construction discipline:

- **Unit children** (rows M1, M2, M3 over-free, A1–A4) re-exec the crate's own
  test binary via `std::env::current_exe()`, selecting the child body by test
  name. The child body is an **ordinary non-`#[ignore]`d `#[test]`** that
  returns immediately when the arm variable is absent. Two consequences worth
  the choice: the normal suite runs every child body unarmed on every run,
  which *is* acceptance item 4 (unarmed byte-inertness) executing continuously;
  and no spec-bearing assertion hides behind `#[ignore]` (root `CLAUDE.md`
  §Testing). The parent test — the committed assertion — is the one that spawns.
- **Compiler children** (M3 leak, and the M3 clean control) spawn the built
  `cranelisp` binary on a minimal program, as
  `tests/intrinsics_m3_detection_s116.rs` already does.

Both kinds: `.env_clear()`, then an explicitly enumerated allow-list at the
call site — the absolute program path, `CRANELISP_LIB`,
`CRANELISP_PLATFORM_PATH` (compiler children), any loader path the child
genuinely needs, and the named detector/plant variables. Unique temp directory,
`--no-cache` for compiler children, capture of stdout/stderr/status. A
developer's ambient `CRANELISP_*` diagnostics are never inherited.

### 7.7 Acceptance mapping

`tests/plan/s118-test-plan.md` §3.1 states four per-row requirements; this
design satisfies them as follows, and `/dev`'s change-set is the evidence:

| Test-plan requirement | Where this design meets it |
|---|---|
| 1. triplet at the production funnel; no bypass, no direct `Quarantine` instantiation | §7.2 event table + the `pub(crate)` read-only observation; §7.3 armed columns |
| 2. fail-on-revert demonstrated and **recorded per row** | §7.3's negative-control column IS the recorded polarity; `/dev` records the revert demonstration per row in the change-set, `/review` verifies the record. The precheck hoist (§7.5) is what makes the positive observable at all, so a revert of it is itself a detected regression |
| 3. subprocess isolation per §7.1 | §7.6 harness shape (`env_clear` + enumerated allow-list, unique tempdir, `--no-cache`, exact arm string, exactly one plant spelling) |
| 4. unarmed byte-inertness, unit-pinned | §7.6's non-ignored child bodies run unarmed on every suite run; plus an explicit `diagnostics` unit row (§10) asserting no state construction, counter adjustment, or allocation when the arm variable is absent |

Principle 5 (Testability is structural) requires the production-funnel hook.
Principles 18 (Enforce invariants structurally) and 25 (Narrowing carries its
check) require validation-before-mutation and both polarities — §7.5's precheck
hoist is where P25 actually bites: a narrowing whose check runs *after* the
narrowed operation is not a check. Principle 6 (Complexity has a budget)
rejects a general fault API; the closed three-event / three-action set in §7.2
is the budget. Principle 7 (Single source of truth) keeps existing funnels,
counters, and the one `seam_precheck` owner authoritative. Principle 4
(Parallel development first-class) is what §7.1's arming invariant protects:
suite-global arming makes one lane's diagnostics everyone's failure.

---

## §8. Quality attributes

Assessed this sprint (`/design` stewardship — untouched attributes are named as
such, the confirmation being the stewardship):

- **Simplicity (Principle 6):** three env gates over the two existing funnels +
  two existing counters, one closed three-event/three-action hook, and one
  shared `seam_precheck`. S118 adds exactly one new predicate
  (header-plausibility, §7.5) and one shared precheck owner — no new module, no
  new state, no new gate variable. Off = today's code.
- **Maintainability:** the S118 blast radius is bounded to `diagnostics.rs` +
  the four seam call sites + `drop.rs`'s constant/reader deletions. §9's
  convergence *reduces* the maintained surface (three duplicate constants, one
  duplicate reader, two public fns). The one place a future change-set can
  quietly break the proofs is the precheck ordering — hence §7.5 states it as
  an ordering contract, not a code comment.
- **Observability:** the whole point — a free-class fault names its seam at the
  faulting op (poison read / stale-dec rejection / parity dump) instead of N
  crossings later or never. S118 adds the plant-identity line so a report says
  *which* injected fault produced it (§7.2).
- **Testability (Principle 5):** the seam is already single-sourced. The closed
  protocol proves production paths in isolated children; mechanism-internal
  helper tests are controls, not detection evidence. §7.6's non-ignored,
  no-op-when-unarmed child bodies make byte-inertness a continuously-executed
  property rather than a claim.
- **Concurrency:** the quarantine list and counters are process-global; the
  list uses a `Mutex` modelled on the existing `LIVE_ALLOCS`/`FREED_TRACKED`
  ones, same contention profile, lane-only. The plant slot is a one-shot
  compare/exchange. The IVar spark SeqCst-atomic RC (BC §4b invariant 3) is
  untouched. **The arming invariant (§7.1) is a concurrency invariant**: a
  `LazyLock` gate plus a process-global ledger cannot be safely re-armed
  in-process under parallel nextest.
- **Performance:** diagnostic modes retain their cached-gate cost. The fault
  hook's unarmed path is one cached closed-enum read and `NoAction`; the
  precheck's unarmed path is the cached bool load already present. No
  allocation, lock, counter write, or IR/ABI change when off. Armed is
  test-only use; the precheck's two extra loads are gate-only.
- **Untouched this design:** the reactor, IO, and trace subsystems — no change
  in S118; `reactor.md` and `intrinsics-table.md` are unaffected.

---

## §9. The convergence batch (0850 + arch ruling 7) — one change-set

Arch ruling 6 verified at HEAD that S117 W5 converged only the buffer-lifecycle
half of 0850. Ruling 7 attaches the owed S116 ruling-5 API removal to the same
change-set. Both are **behaviour-invariant with zero public-API delta except
the named subtraction**, which is why they ride together: one change-set, one
invariance pin, one baseline regeneration.

### 9.1 R1 — `drop.rs` raw-read convergence (0850, first half)

`heap_access::{read_i64, write_i64}` is the single mechanical owner of
`*(base + off)` (`crates/cranelisp-intrinsics/CLAUDE.md` §"Heap layout" says so
already; the source contradicts it). At HEAD `drop.rs:62-69` carries a private
`read_i64(base: i64, offset: usize)` — the same operation with a `usize`
offset instead of `heap_access`'s `isize`.

- Delete the private reader. Its thirteen call sites (`drop.rs:140, 141, 177,
  178, 284, 287, 291, 409, 412, 419, 468, 470, 521`) take
  `heap_access::read_i64`, adapting `usize` → `isize` at the call by making the
  offset constants `isize` (preferred — the adaptation then happens once, at
  the constant, not thirteen times) or by an `as isize` at each site.
- `TAG_OFFSET`/`FIELD0_OFFSET`/`FIELD1_OFFSET` stay in `drop.rs` (they are ADT
  field geometry, not Vec layout) but derive from `HeapHeader::SIZE` rather
  than restating `16`: `const TAG_OFFSET: isize = HeapHeader::SIZE as isize;`
  and the two field offsets as `TAG_OFFSET + 8`/`+ 16`. Removes the third
  magic-number copy of the header size in this file at zero behavioural cost.

### 9.2 R2 — Vec layout-authority convergence (0850, second half)

`vec_runtime` is the single owner of Vec layout constants (already blessed and
locked by `const _: () = assert!(…)`, FIXME 0245). `drop.rs:207-210` copies
them under different names.

- Delete `VEC_LEN_OFFSET`/`VEC_CAP_OFFSET`/`VEC_DATA_PTR_OFFSET`; use
  `vec_runtime::{LEN_OFFSET, CAP_OFFSET, DATA_PTR_OFFSET}`.
- `consume_vec_with` (`drop.rs:236-238`) open-codes three raw reads through
  `base.add(OFFSET)`; route all three through `heap_access::read_i64` with the
  imported constants. The data pointer reads as an `i64` and casts to
  `*mut i64` at the use, as elsewhere in the crate.
- No new `pub(crate)` typed reader is required by this convergence; if one is
  introduced it belongs in `vec_runtime` beside the constants, never in
  `drop.rs`.

This separates **layout authority** (`vec_runtime`, `HeapHeader`) from
**mechanical access** (`heap_access`) without duplicating either (Principle 7).
The recurrence history matters: this is the third-sprint recurrence of S87 F3 —
the guidance was true in `CLAUDE.md` and false in source for three sprints, so
the fix is to make the guidance true, never to weaken it (Principle 19 sibling:
no module privileged by name — `drop.rs` is not exempt from the owner it cites).

### 9.3 R3 — adjacent duplication, bounded

`CLOSURE_DROP_GLUE_OFFSET = 24` exists twice inside this crate (`drop.rs:507`
as `usize`, `ivar.rs:567` as `isize`) — same constant, same backend-emitted
closure layout (Decision 11), two copies. It is adjacent to 0850's class but
outside arch ruling 6's literal scope. Disposition: fold it in **only if** it
lands in the same change-set with a demonstrably zero behaviour delta —
`drop.rs` (the drop-glue module, the closure-teardown authority) declares the
single `pub(crate) const` and `ivar.rs` imports it. If it does not fold
cleanly, `/dev` files a FIXME rather than carrying a silent third copy.

### 9.4 R4 — the subtractive API change (arch ruling 7, S116 ruling 5)

Approved in S116, unlanded, still `pub` at `alloc.rs:86` (`bytes_peak`) and
`alloc.rs:121` (`reset_counts`), still in the baseline
(`public-api.txt:7, :15`). Retaining `reset_counts()` can zero the counters
that are M3's *only* evidence, so it is a live hazard to the instrument this
sprint is proving. Both have zero repository consumers.

In the same change-set:

- delete `reset_counts()` and `bytes_peak()`; no guarded replacement is
  authorized absent a concrete consumer;
- clean the rustdoc that cites them — `alloc.rs:63-80`, where four *surviving*
  accessors (`alloc_count`, `dealloc_count`, `bytes_allocated`,
  `bytes_current`) each describe themselves "since the last `reset_counts`".
  After removal the correct statement is **monotonic process-lifetime
  evidence** (`bytes_current` is live-bytes, not monotonic — state it as
  process-lifetime, no reset seam). This rustdoc edit is the substantive half:
  a dangling `[`reset_counts`]` intra-doc link is a rustdoc error, and a
  "since the last reset" claim with no reset is exactly the doc-memory rot the
  S115 audit's RI-3 recorded;
- regenerate `crates/cranelisp-intrinsics/public-api.txt` via the canonical
  `cargo public-api --omit blanket-impls,auto-derived-impls -p
  cranelisp-intrinsics` — a subtractive-only two-line diff, riding side by side
  with the source change (`design/arch/CLAUDE.md` §"Baseline-diff discipline");
- grep-zero `reset_counts`/`bytes_peak` across the crate's `src/` + rustdoc.

No cache-schema, heap-layout, C-ABI, or intrinsic-catalog change. **Cross-crate
residue:** `design/arch/bounded-contexts.md` §4b invariant 8 still says "int's
`reset_counts` should be called at session start in test contexts" — that
sentence becomes false with this change and is `/arch`-owned. FIXME 0876 filed.

### 9.5 R5 — record integrity (carried from S116, unchanged)

The flat catalog carries no prose/test-name count. Its guard is
`name_set_is_exactly_expected`; `EXPECTED_NAMES.len()` is the only numeric
authority. All live reactor citations under the crate point to
`design/intrinsics/reactor.md`; `design/int/reactor.md` is not an alias. The
mechanical correction spans source, Cargo, and test `// spec:`/`// design:`
citations and ends with a grep-zero check.

### 9.6 Invariance pin

`/qa` pins R1–R3's behaviour-invariance as: **every baseline RED stays
byte-identically RED in this change-set**, and every currently-GREEN drop/Vec/
ADT cell stays green (`tests/plan/s118-test-plan.md` §3.2). A RED that *flips*
here is mis-attributed evidence that reopens attribution, not a win — the
convergence deletes duplicate spellings of the same reads; it cannot fix an
ownership defect. Unit-tier pins are the `heap_access`/`vec_runtime` rows of
§10, including the grep-zero "no local reader or offset copy in `drop.rs`".

## §9a. 0859 — the detector surface as oracle (cross-reference only)

Per arch ruling 2, the instrument for the ProjectionOf production-artifact
witness is the **existing env-gated detector surface** — M1/M2/M3 plus the
RC/parity counters — used as an oracle over isolated-declaration-mutation
experiments (`ownership_facts.rs`: `ProjectionOf(0) → Fresh`, applied singly,
restored after each experiment) in fresh subprocesses.

Three statements bind this crate, and nothing more:

1. **The §7 fault-plant protocol is NOT the instrument.** Plants prove
   detectors; they cannot witness a declaration. No plant spelling, hook event,
   or action is added for 0859, and no new seam, carrier, or observation
   surface is designed for it here.
2. **The oracle may only be used after the §7 detection proofs land** (the
   0768 rule: an unproven detector cannot serve as an oracle). This is the
   ordering dependency Track A's internal sequencing must respect.
3. **The experiment protocol is `/qa`-owned** (`tests/plan/s118-test-plan.md`
   §3.5). If every surveyed production shape stays emission-inert under armed
   detectors, that is the FIXME's disposition 2 — returned to the user, not
   overridden with test-only facts.

Arming for these experiments obeys §7.1 exactly: child `.env`/`env_clear`,
never suite-global, never `set_var`.

---

## §10. Unit-scenario matrix and implementation order

`/dev` owns every row below (`#[cfg(test)]` beside its seam, per the crate's
externalized-`tests.rs` convention). The subprocess/e2e row is `/testing`'s.

| Submodule | Normal / positive | Complexity / edge | Negative / detector |
|---|---|---|---|
| `diagnostics` (protocol) | arm absent ⇒ `NoAction`, zero state construction, zero counter adjustment, zero allocation (acceptance item 4) | exact arm string + exactly one spelling parses and fires **once**; marker-size selection picks the intended allocation | unknown / empty / multiple spellings are a hard config error **before** any allocation, never a partial plant; wrong arm string is fully off |
| `diagnostics` (precheck) | armed gate passes a well-formed live base | `alloc_size` exactly `HeapHeader::SIZE`; smallest and largest legal sizes | non-8-aligned header rejected; `alloc_size < HeapHeader::SIZE` rejected; `rc == 0` and `rc < 0` rejected; **rejection precedes mutation** (the RC word is unchanged after a rejected call) |
| `diagnostics` (modes) | clean M1/M2/M3 children exit normally | odd-byte scrub tail; quarantine cap 0 / exact / over, FIFO release order | both M3 report polarities (`allocs > deallocs`, `deallocs > allocs`); plant-identity line present when armed, **absent** when clean |
| `alloc` | normal alloc/dealloc; counters monotonic across the process | header-integrity and double-free twins still fire in debug | M1 `M1StaleReuse`, M2 `M2StaleRead`, both M3 faces, A4 rejection **before** `Layout` construction |
| `rc` | nullary tag no-ops; live inc/dec unchanged | RC 1→0 free transition; non-atomic-RC diagnostic composition | A1 `A1ZeroRc`, A2 `A2InteriorPointer`; no mutation before rejection |
| `drop` | every `consume_*` behaviourally unchanged after §9 convergence | Vec zero len / zero cap; heap elements; recursive SList/Sexp/IO protocol | A3 `A3FreedPointer` through the validated precheck path |
| `heap_access` / `vec_runtime` | round-trip through the shared accessor; typed Vec reads at LEN/CAP/DATA_PTR | largest field offset; the data-pointer field; `isize` offset adaptation | M2's stale read goes through the shared accessor; **grep-zero: no local reader and no offset copy in `drop.rs`** |
| `catalog` / facade | exact expected name set; the four surviving counter accessors | missing / duplicate / unexpected name guards | count-bearing prose grep-zero; `reset_counts`/`bytes_peak` absent from src, rustdoc, and baseline |
| subprocess / e2e (`/testing`) | clean M3 compiler child exits normally | `env_clear` + enumerated allow-list; unique tempdir; `--no-cache` | M3 leak child reports **then** aborts non-zero; parity-off child has no report line |

**Serial implementation order.** Each step is a separate change-set; the order
is a dependency order, not a preference:

1. **§7.5 precheck hoist + the shared `seam_precheck`** — the mechanism
   prerequisite. Lands with its own `diagnostics` precheck unit rows and the
   rejection-precedes-mutation negatives. Every existing suite cell must be
   unaffected (the gate is off by default).
2. **§7.1/§7.2/§7.6 closed protocol** — enum, hook, three events, three
   actions, one read-only observation, the child harness, the plant-identity
   report line. Unarmed byte-inertness rows land here.
3. **M1/M2 + A1–A4 triplets** (six rows) against the seams from step 1.
4. **Both M3 unit children** + the `/testing` handoff for the two committed
   e2e cells; those flip GREEN here.
5. **§9 convergence batch** (R1–R5, one change-set) with the §9.6 invariance
   pin and the subtractive baseline regeneration.
6. **Review**: unarmed behaviour, UB-free controls, per-row fail-on-revert
   records, baseline diff, grep-zero proofs, and no detector armed outside a
   child `.env`/`env_clear`.

Steps 1–4 are Track A's must-ship core (FIXME 0848); step 5 is FIXME 0850 +
arch ruling 7. `/qa`'s 0857 regrade consumes step 6's records and must not
begin before they exist.

---

## §11. Cross-references

- `design/arch/safety-invariants.md` §2 (ladder tiers 3/5), §4 R8 — the owning
  register row (arch-owned; FIXME `target: /arch` to change it).
- `tests/plan/memory-safety-coverage.md` §1 (oracle lane the modes feed), §5
  (the blindness quantification), §6 (increment sequencing).
- `tests/plan/s113-test-plan.md` MS-P4/MS-P6/MS-P7 — the lane rows the modes
  ride; the acceptance run.
- `tests/plan/s116-test-plan.md` §4/§6 — the A-label fault classes; positive
  proof and owner acceptance.
- `tests/plan/s118-test-plan.md` §1 (arming discipline + the static gate), §3.1
  (the eight rows + four acceptance requirements), §3.2 (0850 invariance pin),
  §3.3 (subtractive baseline cells), §3.4 (0857 regrade sequencing), §3.5
  (0859 conditional) — the acceptance contract this design is written against.
- `sprints/SPRINT.md` §Architecture review — rulings 2 (0859 oracle, no new
  seam), 3 (lane-scoped arming), 6 (0850 target verified at HEAD), 7 (the
  subtractive API change rides the 0850 change-set).
- `crates/cranelisp-intrinsics/src/{alloc,rc,drop,diagnostics,heap_access,
  vec_runtime}.rs` — the seams; the crate `lib.rs` `//!` is the
  `/arch`-approved facade (unchanged apart from §9.4's subtraction).
- `crates/cranelisp-intrinsics/CLAUDE.md` §"Debug hooks" / §"Heap layout" —
  `/dev`-owned; the heap-layout paragraph already declares `heap_access` the
  single owner, which §9 makes true in source.
- `tests/intrinsics_m3_detection_s116.rs` — the two committed M3 e2e cells
  whose assertions pin the arm string and the report identity (§7.2).

## Next skills

- `/dev`(intrinsics) — implement §10's six serial steps in order; step 1
  (precheck hoist) gates steps 3–4. Record per-row fail-on-revert evidence in
  the change-set.
- `/arch` — action FIXME 0876 (BC §4b invariant 8 cites the removed
  `reset_counts`); confirm §9.4's subtractive baseline is the only public-API
  delta and that §7.5's precheck adds no cross-crate surface.
- `/qa` — regrade R8 only from landed detector evidence (0857), grading the M3
  over-free row and the A2/A3 header-plausibility face at the tiers §7.2/§7.5
  state honestly; 0859's oracle may not begin before step 4 lands.
- `/testing` — the two M3 e2e cells already exist and flip at step 4; the W1
  static arming gate enforces §7.1.
- `/review`(intrinsics) — reject bypass tests, UB-dependent controls,
  open-ended fault APIs, nonzero unarmed behaviour, any detector armed outside
  a child `.env`/`env_clear`, and any RED that flips inside the §9
  change-set (§9.6).
