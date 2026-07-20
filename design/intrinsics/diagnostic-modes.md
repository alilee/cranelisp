# Memory-safety diagnostic modes (tier-5) + RC/alloc seam asserts (tier-3)

Subordinate topic doc for `cranelisp-intrinsics`. **DESIGN (S113 W5a),
pre-implementation.** Owner: `/design`(intrinsics); implemented by
`/dev`(intrinsics) after this design settles; lane wiring is `/qa`/`/testing`
(`tests/plan/memory-safety-coverage.md`).

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

A1 is the only genuinely-new assert; A2–A4 are release-gating existing
debug-only checks so the release/`--link` lane earns the same signal. None
require an interface change — all are internal to intrinsic bodies. `rc_inc`'s
nullary-tag guard (`ptr < NULLARY_TAG_THRESHOLD`) is preserved ahead of the new
check (a bare tag is not a heap pointer).

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

**Self-tests (MS-P6):** each mode lands with one deliberate-violation unit test
that plants a fault the mode must catch — a quarantine+scrub read-after-free
returns poison; a double-free trips M3; a leaked alloc trips the exit parity.
These are `/dev`(intrinsics) `#[cfg(test)]` unit tests at the `alloc`/`rc` seams
(the crate's tests externalize to `alloc/tests.rs`, `rc/tests.rs`) plus the
`/qa` lane faces. The unit test is mandatory per each fix (root CLAUDE.md
§Testing); the e2e face is the oracle lane wiring the env vars.

---

## §7. FIXME 0656 residual — stale citations to re-point (for `/dev`)

Independent comment-only rider drained opportunistically in this intrinsics
change-set (the FIXME is `target: /dev`; deletes when actioned). Three stale
rustdoc citations point at the deleted backend startup-`.o` emitter; re-point
each at int's live `src/exe.rs`:

- `crates/cranelisp-intrinsics/src/layout.rs:3` — names
  `cranelisp-backend::exe::generate_startup_object_checked`; the live emitter is
  **int's `src/exe.rs::generate_startup_object`**.
- `crates/cranelisp-intrinsics/src/layout.rs:49` — says the hash is baked "by
  `cranelisp-backend` (`define_cstr_data`)"; the live `define_cstr_data` is
  **int's (`src/exe.rs`)**.
- `crates/cranelisp-intrinsics/src/io.rs:1140` — cites the ambiguous
  `exe.rs::define_cstr_data`; the intended referent is **int's `src/exe.rs`**.

(NOT stale, leave as-is: `panic.rs:326` cites int's live
`src/exe.rs::generate_startup_object`.) These have no behavioural effect; fix by
symbol not line number (lines have shifted). After the edits, `/dev`
`git rm`s `design/arch/fixmes/0656-stale-citations-to-deleted-backend-startup-emitter.md`.

---

## §8. Quality attributes

- **Simplicity (Principle 6):** no new machinery — three env gates over the two
  existing funnels + two existing counters; one genuinely-new assert (A1). Off
  = today's code.
- **Observability:** the whole point — a free-class fault names its seam at the
  faulting op (poison read / stale-dec assert / parity dump) instead of N
  crossings later or never.
- **Testability (Principle 5):** the seam is already single-sourced (one alloc,
  one dealloc, two dec funnels), so the modes are structurally testable at the
  `alloc`/`rc` unit seams and as oracle-lane env faces; no internal-session
  bridging.
- **Concurrency:** the quarantine list and counters are process-global; the
  list needs a `Mutex` (or a lock-free stack) — modelled on the existing
  `LIVE_ALLOCS`/`FREED_TRACKED` `Mutex`es, same contention profile, lane-only.
  The IVar spark SeqCst-atomic RC (BC §4b invariant 3) is untouched.
- **Performance:** off = one cached bool load per alloc/dealloc, zero writes;
  on = lane-only (never production — R8's production carve-out stays
  `unasserted` by design, cost; recorded in the register).
- **Untouched this design:** the reactor, IO, trace subsystems — no change.

---

## §9. Cross-references

- `design/arch/safety-invariants.md` §2 (ladder tiers 3/5), §4 R8 — the owning
  register row (arch-owned; FIXME `target: /arch` to change it).
- `tests/plan/memory-safety-coverage.md` §1 (oracle lane the modes feed), §5
  (the blindness quantification), §6 (increment sequencing).
- `tests/plan/s113-test-plan.md` MS-P4/MS-P6/MS-P7 — the lane rows the modes
  ride; the acceptance run.
- `crates/cranelisp-intrinsics/src/{alloc,rc,drop}.rs` — the seams; the crate
  `lib.rs` `//!` is the `/arch`-approved facade (unchanged — no public surface
  delta).
- `crates/cranelisp-intrinsics/CLAUDE.md` §"Debug hooks" — the env-var table
  `/dev` extends with the three new rows at implementation.
</content>
</invoke>
