# `rc::rc_inc` — the blessed RC-inc entry point (S85 Phase 3)

**Status.** Phase 3 design — DESIGN ONLY (no source edits). Feeds /dev (intrinsics) Phase 5 + the /dev (primitives) re-route follow-on. Implements *within* the `/arch` ruling (0397), which is authoritative; this doc does not re-rule, it pins the implementation shape.

**Author.** `/design (intrinsics)`, 2026-06-17.

**Reads.** `sprints/SPRINT.md` §Scope + §"Architecture review (Phase 2)" (b); `design/arch/fixmes/0397-arch-intrinsics-rc-inc-entry-point.md`; `spec/appendix-c-nfr.md` §C.4.1; `design/arch/bounded-contexts.md` §4b; `crates/cranelisp-intrinsics/src/rc.rs` (`consume_shallow` — the dec mirror; there is NO existing `rc_inc`); `crates/cranelisp-primitives/src/marshal.rs` (`shallow_rc_inc`); `crates/cranelisp-primitives/src/string.rs` (`string_identity`); `crates/cranelisp-intrinsics/public-api.txt`; `design/arch/CLAUDE.md` §"Baseline-diff discipline".

> **S119 amendment (`/design`, tranche A).** `rc_inc(ptr: i64)` **stays** the
> blessed public mechanism and its shape is unchanged by the typed consume
> funnel. What changes is that it acquires a single typed caller:
> `cranelisp_intrinsics::handle::Borrowed::to_owned(self) -> Owned` is the one
> place in the pair's Rust bodies where a new reference is minted, and it
> delegates here. The two primitives re-route sites this doc pinned
> (`marshal.rs::shallow_rc_inc`, `string.rs::string_identity`) become
> `.to_owned()` call sites in tranche A. The end-state intent — `rc_inc`'s only
> caller being `to_owned` — is a **tranche-C** outcome, not tranche A's:
> `io.rs` and `trace.rs` still call it raw and are out of tranche A's slice.
> `design/runtime/s119-typed-consume-funnel.md` §2.2 and §6.3.

> **Scope note.** This is a subordinate topic doc, not the intrinsics master. The crate has no `design/intrinsics/intrinsics.md` master today — the canonical surface is the crate-root `//!` rustdoc + per-item `///` (facade retired S74 W3 per BC §4b §"Per-surface documentation"). This doc elaborates the **one** S85 addition to that surface: `pub fn rc_inc(ptr: i64)`. It does not restate the whole crate; it pins the fn's shape, ordering rationale, safety contract, the two primitives re-route sites, the unit-test obligations, and the baseline bump so /dev can implement against acceptance criteria. It is the structural sibling of `design/intrinsics/intrinsics-table.md` (which pinned the `INTRINSICS_TABLE` addition the same way).

---

## 1. What is being added, and why now

### 1.1 The asymmetry being closed

`cranelisp_intrinsics::rc` is the blessed single owner of the **extern-Rust RC path** (the inc/dec that Rust-implemented externs perform on their own heap arguments — distinct from the backend's *inline* `atomic_rmw` inc/dec emitted at codegen, `design/backend/ring2-rc.md` §"Atomic discipline"). Today that module owns exactly **one** half of the discipline:

- **dec half — owned.** `consume_shallow(ptr)` (`rc.rs:78`): nullary-tag-skip → atomic `fetch_sub(1, Release)` → `rc_trace("dec", …)` → on last ref, `fence(Acquire)` + `dealloc`. One owner for the shallow-dec.
- **inc half — NOT owned.** There is **no `rc_inc`**. Every RC-inc site open-codes its own atomic (or, in one case, a non-atomic) increment:
  - `cranelisp-primitives::marshal.rs::shallow_rc_inc` — **non-atomic** `*rc_ptr += 1` (the live hazard, §3.1).
  - `cranelisp-primitives::string.rs::string_identity` — atomic `fetch_add(1, Release)` (already correct, §3.2).
  - intrinsics-internal sites — `trace.rs::rc_inc_if_heap` (open-coded SeqCst) and `ivar.rs::ivar_spark` (SeqCst) — carry their own orderings; the `/arch` per-site ordering review (BC §4b invariant 3) brings both IN scope this sprint with distinct dispositions (§6). (`drop.rs` was a FIXME misidentification — it has no production inc site; §6.3.)

This violates Principle 7 (single source of truth): the inc discipline has no single owner the way the dec does. The S85 deliverable restores symmetry — `rc_inc` is to the inc half exactly what `consume_shallow` is to the dec half.

### 1.2 Why now — the soundness precondition

S85 wires automatic IO scheduling (§10.12) onto the live compile path, so `ivar_spark → rayon::spawn` actually forks user work across threads. A **non-atomic** RC inc on a value shared across a fork-join boundary becomes a genuine data race the moment the wiring activates (`sprints/SPRINT.md` §Scope item 2). The non-atomic `shallow_rc_inc` was "sound today" only because no spark forked an `sconcat`/`quote-sexp` callee mid-flight (`marshal.rs:152-163` NOTE). That precondition dissolves with the wiring. The fix MUST land *with* the wiring, not after it (`sprints/SPRINT.md` §Scope; FIXME table 0397 row).

---

## 2. The `rc_inc` signature, rustdoc, and body shape

**Mirror `consume_shallow` precisely** (`/arch` ruling 0397; FIXME 0397 §"Proposed resolution" item 1). Same nullary-tag-skip via the same threshold, same RC field derivation from `HeapHeader::RC_OFFSET`, same `rc_trace` call (op = `"inc"`), same `#[inline]`, same `&AtomicI64` view. The only structural differences from the dec mirror: `fetch_add` not `fetch_sub`, no underflow `debug_assert!`, no last-ref free path (inc never frees).

Target-stated (/dev authors the exact text; this is the design intent):

```rust
/// Increment the reference count of a heap value (shallow).
///
/// The blessed extern-Rust RC-inc entry point — the inc-half mirror of
/// [`consume_shallow`]. Use this anywhere a Rust-implemented extern creates a
/// new reference to a heap value it received or is sharing (e.g. an item
/// copied into a fresh ADT cell, or an identity-share that returns its arg
/// with a fresh count). Single owner for the shallow-inc discipline
/// (Principle 7) — open-coded `fetch_add` / `*rc_ptr += 1` at extern call
/// sites must route through here.
///
/// No-op for values below `NULLARY_TAG_THRESHOLD` (bare nullary tags of
/// Mixed-category ADTs — not heap pointers).
///
/// # Ordering
///
/// Uses `fetch_add(1, Ordering::Release)`. Release is the NFR C.4.1 floor
/// ("RC increment MUST use at least Release ordering"; `spec/appendix-c-nfr.md`
/// §C.4.1) and matches the backend's inline `atomic_rmw` inc (SeqCst ≥ Release)
/// and the existing atomic share path. An inc creates a new reference; the
/// Release publishes any writes that established the new reference before the
/// count is observed by another thread (the symmetric counterpart to the dec's
/// Release + free-path Acquire fence in `consume_shallow`).
///
/// # Safety
///
/// `ptr` must be either a valid heap base pointer whose RC is > 0, or a bare
/// nullary tag (< `NULLARY_TAG_THRESHOLD`).
#[inline]
pub fn rc_inc(ptr: i64) {
    if ptr < cranelisp_types::NULLARY_TAG_THRESHOLD as i64 {
        return; // bare tag — no heap alloc to inc
    }
    // SAFETY: caller guarantees ptr is a valid heap base with RC > 0.
    let rc_ptr = unsafe {
        &*((ptr as *const u8).add(HeapHeader::RC_OFFSET as usize) as *const AtomicI64)
    };
    let old_rc = rc_ptr.fetch_add(1, Ordering::Release);
    rc_trace("inc", ptr, old_rc + 1);
}
```

### 2.1 Derivation notes (load-bearing, must match the dec mirror)

- **Nullary-tag skip.** `ptr < cranelisp_types::NULLARY_TAG_THRESHOLD as i64` — the *same* threshold `consume_shallow` uses (`rc.rs:79`), the single discriminator for "is this i64 a heap pointer?" (`design/runtime/runtime.md` §"Nullary tags"; Principle 7). Bare tags are not heap pointers; inc on one would corrupt a tag value.
- **RC field offset.** Derived from `HeapHeader::RC_OFFSET` (`= 8`), never a magic `.add(8)` — single-sourced from `cranelisp-types` exactly as `consume_shallow` (`rc.rs:84`) and `string_identity` (`string.rs:122`) already do.
- **`&AtomicI64` view.** Cast the RC field to `&AtomicI64` and call `fetch_add` — identical mechanism to `consume_shallow`'s `fetch_sub` view (`rc.rs:83-86`). The atomic view is required for the data-race-free guarantee under sparks (NFR C.4.1).
- **`rc_trace("inc", ptr, new_rc)`.** Pass the *post*-inc value (`old_rc + 1`) so the trace line reads the resulting count — consistent with `consume_shallow`'s `rc_trace("dec", ptr, old_rc - 1)` (`rc.rs:91`) and with the existing `string_identity`'s `rc_trace("inc", s, new_rc)` (`string.rs:125`). The `"inc"` op string already exists in the trace vocabulary (the module `//!` and `string_identity` both use it).
- **No underflow assert, no free path.** Unlike the dec mirror, an inc cannot underflow and cannot free — so `rc_inc` carries neither the `debug_assert!(old_rc > 0)` nor the `if old_rc == 1 { fence; dealloc }` arm. (An inc on an rc=0 value is a caller bug the safety contract forbids; we do not assert it because reading rc=0 here is already UB-adjacent and the dec-side underflow guard catches the lifecycle error at the matching dec.)

### 2.2 Ordering rationale — `fetch_add(1, Release)` (the `/arch` ruling, recorded here)

`/arch` ruled `Ordering::Release` (`sprints/SPRINT.md` §"Architecture review (Phase 2)" (b)). The grounds, for the implementer:

1. **NFR floor.** `spec/appendix-c-nfr.md` §C.4.1: *"RC increment MUST use at least Release ordering."* Release is the minimum the spec permits; this fn sits exactly at the floor.
2. **Consistency with the inline backend path.** The backend emits inc/dec as inline `atomic_rmw` with Cranelift SeqCst semantics (`design/backend/ring2-rc.md` §"Atomic discipline"); SeqCst ≥ Release, so the extern path at Release is *no weaker than* a value's inline-emitted incs — a value incremented inline in one place and via `rc_inc` in another sees a consistent (≥ Release) discipline.
3. **Consistency with the already-correct share path.** `string_identity` already uses `fetch_add(1, Release)` (`string.rs:124`) — routing it through `rc_inc` is behaviour-preserving (§3.2), and `rc_inc`'s Release matches it exactly.

This is **not** a SeqCst choice: the inc has no cross-variable ordering obligation that Release fails to provide (the new reference's establishing writes are what Release publishes; the matching Acquire is the dec-side free fence in `consume_shallow`). Release is the correct floor, not a compromise.

---

## 3. The two `cranelisp-primitives` re-route sites (the /dev follow-on)

Once `rc_inc` exists, `/dev` (narrow on `cranelisp-primitives`) routes both open-coded inc sites through it and deletes the open-coded arithmetic (FIXME 0397 §"Proposed resolution" item 3; closes audit MED-1, `audits/primitives-2026-06-14.md`). This is the *primitives* half — a separate /dev deployment from the intrinsics-crate `rc_inc` addition, sequenced after it (the entry point must exist before the consumers can route through it).

### 3.1 `marshal.rs::shallow_rc_inc` — the bug fix

**Current (`marshal.rs:148-169`):** non-atomic `*rc_ptr += 1` on the raw `*mut i64` at `HeapHeader::RC_OFFSET`, guarded by the nullary threshold, carrying the MED-1 NOTE that documents the divergence as a tracked hazard.

**Re-route:** replace the body of `shallow_rc_inc` with a call to `cranelisp_intrinsics::rc::rc_inc(val)`. The nullary-threshold guard is now *inside* `rc_inc`, so the wrapper collapses to a one-line delegate (or the helper is deleted and call sites — `deep_rc_inc_slist`, the `quote_sexp_build` `TAG_SEXP_STR`/`TAG_SEXP_SYM` arms — call `rc::rc_inc` directly; /dev's choice on whether to keep the local-name wrapper for readability). Either way the **non-atomic `*rc_ptr += 1` is deleted**, and the `HeapHeader` import + raw-pointer arithmetic in this helper go with it.

**This is the bug the re-route fixes.** The current inc is non-atomic; under the S85 auto-IO wiring a spark can fork a callee that shares a value being inc'd here, and a non-atomic increment racing an atomic inc/dec from another thread is a data race (lost update → premature free / use-after-free). Routing through `rc_inc` (atomic `fetch_add(Release)`) closes it. The `marshal.rs:152-163` MED-1 NOTE is **deleted** with the re-route (the hazard it tracked is gone; the FIXME it points at is resolved).

### 3.2 `string.rs::string_identity` — the dedup (behaviour-preserving)

**Current (`string.rs:115-127`):** atomic `fetch_add(1, Release)` on a `&AtomicI64` at `HeapHeader::RC_OFFSET`, then `rc::rc_trace("inc", s, new_rc)`, then `return s`. This is **already correct** — the re-route is a pure dedup, not a fix.

**Re-route:** replace the inline `fetch_add` + `rc_trace` block (the body of `string_identity` except the `return s`) with a single `rc::rc_inc(s)` call, then `s`. The local `use std::sync::atomic::{AtomicI64, Ordering}` + `use cranelisp_types::HeapHeader` imports in this fn are deleted (now `rc_inc`'s concern). Behaviour is identical: same Release ordering, same `rc_trace("inc", …)` with the post-inc count, same returned pointer.

> **One subtlety for /dev:** `string_identity` skips the nullary-threshold check today (a `HeapString` is always a heap pointer, never a bare tag). Routing through `rc_inc` adds the (cheap, always-false-for-strings) threshold branch. This is harmless — strings are always `≥ NULLARY_TAG_THRESHOLD`, so the branch is never taken — and is the correct trade for single-ownership (Principle 7 over a one-branch micro-optimisation; Principle 6 — minimum mechanism, one inc path not two).

---

## 4. Unit-test obligations (Phase 5 /dev)

A **unit test is mandatory per fix** (root `CLAUDE.md` §Testing; `memory/feedback_unit_test_per_fix.md`), written *before* the implementation. `rc_inc` lives in `crates/cranelisp-intrinsics/src/rc.rs`, so its unit tests go in that file's `#[cfg(test)] mod tests`, **mirroring the existing `consume_shallow` tests** (`rc.rs:154-200`). Required cases:

1. **`rc_inc` increments the RC** — the inc-mirror of `decision24_consume_shallow_frees_last_reference` / `..._preserves_shared_reference`. Allocate a heap cell (rc=1) via `alloc::alloc_with_rc`; `rc_inc` it (rc 1→2); then `consume_shallow` once (rc 2→1, **not** freed — assert `dealloc_count` delta == 0); then `consume_shallow` again (rc 1→0, freed — assert delta == 1). This proves the inc landed at the canonical RC field and is observed by the dec mirror. (Cross-check: this is exactly the round-trip `marshal.rs::shallow_rc_inc_targets_canonical_rc_field` already exercises for the marshal helper — §4 note below.)
2. **`rc_inc` skips bare nullary tags** — the inc-mirror of `decision24_consume_shallow_skips_nullary_tags`. Call `rc_inc(0)`, `rc_inc(1)`, `rc_inc(100)`, `rc_inc(NULLARY_TAG_THRESHOLD - 1)`; assert `alloc_count` / `dealloc_count` deltas are 0 (no heap touched — and, crucially, no corruption of the tag value, since a non-skipped inc would write through a non-pointer).
3. **`rc_inc` traces** — the inc-mirror of `test_rc_trace_does_not_panic`. Assert `rc_inc` on a valid cell does not panic with tracing exercised; the `"inc"` op string is emitted (a does-not-panic assertion suffices, matching the existing trace test's bar — stderr output is not captured in the unit tier).

Each test carries a `// spec:` comment. The natural annotation is `spec/appendix-c-nfr.md §C.4.1 — RC increment atomic, ≥ Release` for case 1/2 (the atomicity + correctness obligation) and `12-runtime §12.3.2 — RC trace logging does not panic` for case 3 (matching the sibling trace tests' annotation, `rc.rs:122/129`).

**Primitives-side guard (already present, keep green).** The re-route must not regress `marshal.rs::shallow_rc_inc_targets_canonical_rc_field` (`marshal.rs:381-404`) or `decision24_sconcat_rc_balanced` (`marshal.rs:448-484`) — they assert the marshal incs land on the RC field and that `sconcat` stays RC-balanced. After the re-route these pass unchanged (the inc behaviour is preserved; only the inc *path* moves into `rc_inc`). No new primitives-side unit test is *required* for the dedup of `string_identity` (behaviour-preserving), but the existing `string.rs` string round-trip tests must stay green; for the `marshal.rs::shallow_rc_inc` change a behaviour-preserving assertion is already provided by `shallow_rc_inc_targets_canonical_rc_field`. /dev confirms both files' test modules pass post-re-route.

**e2e assessment (per root `CLAUDE.md` §Testing — assess BEFORE the fix).** The data-race the fix closes is only observable under the live auto-IO wiring (S85's other workstream) forking a spark over a shared value. The /qa green-up verification for S85 (`sprints/SPRINT.md` Phase-3 provisional shape) covers the end-to-end soundness; this doc does not own that test. The unit tier above is the mandatory per-fix guard at the seam where `rc_inc` lives; the cross-mode soundness is the /qa workstream's e2e obligation, not a duplicate here.

---

## 5. Baseline + rustdoc (the canonical surface)

Per baseline-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff discipline"): adding a `pub fn` to `cranelisp-intrinsics` moves the crate's `public-api.txt` baseline, so the implementing change-set MUST, **in the same commit**:

1. **Regenerate** `crates/cranelisp-intrinsics/public-api.txt` via the canonical command:
   `cargo public-api --omit blanket-impls,auto-derived-impls -p cranelisp-intrinsics > crates/cranelisp-intrinsics/public-api.txt`.
   The diff adds exactly one line — `pub fn cranelisp_intrinsics::rc::rc_inc(i64)` — in the `pub mod cranelisp_intrinsics::rc` block, alphabetically between `consume_shallow` and `is_rc_trace_enabled` (the existing block is `consume_shallow` / `is_rc_trace_enabled` / `rc_trace` / `rc_underflow_check`, `public-api.txt:151-155`). No other baseline line changes — `rc_inc` adds a fn, touches no type, no trait impl, no auto-trait projection.
2. **Author the per-item `///`** on `rc_inc` (the §2 rustdoc draft is the starting text) — this is the canonical rationale surface; there is no `facades/intrinsics.md` to update (retired S74 W3 → BC §4b + source rustdoc). The crate-root `//!` already frames the dec half ("This module provides the trace logging infrastructure …"; the `consume_shallow` §"Consuming helper" block); /dev may add a one-line mention that `rc_inc` is the inc-half mirror, but no structural `//!` rewrite is needed — a single new `pub fn` with full `///` is the whole surface delta.
3. **No `cranelisp-types` change** (`sprints/SPRINT.md` §"Architecture review (Phase 2)" (b)/(d): *"No `cranelisp-types` impact."* — `rc_inc` takes/returns `i64`, uses only the already-imported `HeapHeader::RC_OFFSET` + `NULLARY_TAG_THRESHOLD`). **No BC edit** — BC §4b already states the RC discipline in prose; an inc-half entry mirroring the dec half is within the stated shape, not a new invariant.

Skill split (per the discipline): `/dev` (intrinsics) regenerates the baseline + authors the `///` as part of the implementing change-set; `/design` (this doc) records the expected one-line diff so `/review` can confirm baseline + rationale landed together; `/review` confirms both are present in the same diff at PR time.

---

## 6. The intrinsics-internal inc sites — per-site design (the `/arch` ordering review)

FIXME 0397 §Issue listed *other* open-coded inc sites inside `cranelisp-intrinsics` itself and Phase 3 deferred them pending a per-site ordering review. `/arch` ran that review and recorded the rulings in **`design/arch/bounded-contexts.md` §4b invariant 3** (the canonical policy home — the per-site table + the `drop.rs` correction live there; this section implements *within* those rulings, it does not re-rule). Two corrections to the Phase-3 inventory came out of the review:

- **There are only TWO production intrinsics-internal inc-site questions, not three.** The third — `drop.rs` — was a **misidentification** in the FIXME; see §6.3.
- The remaining two (`trace.rs::rc_inc_if_heap`, `ivar.rs::ivar_spark`) split: one is **IN scope this sprint** (adopt `rc_inc`, SeqCst→Release), the other is **KEEP SeqCst, documented**.

### 6.1 `trace.rs::rc_inc_if_heap` — IN scope: route through `rc_inc` (SeqCst → Release downgrade)

The four Trace-ADT field accessors (`accessor_*`, `trace.rs:1383–1490` tests) hand out a sub-reference to a field value via `rc_inc_if_heap`, which today open-codes its own `&AtomicI64` view at offset 8 and a `fetch_add(1, SeqCst)`. **`/arch` ruling (BC §4b inv 3 table, row 3): ADOPT `rc_inc` (Release).** The SeqCst here is **gratuitous, not load-bearing** — nothing in the trace machinery depends on this inc being globally ordered against the trace stack, the `TRACE_THREAD_ID` role-CAS (`trace.rs:327/651`), or `TRACE_BODY_RUNNING`; those orderings are carried by their *own* SeqCst atomics and are unaffected by the field-accessor inc's ordering. A field value inc'd here and dec'd elsewhere via `consume_shallow`/`consume_trace_call` (both Release + free-path Acquire) sees a consistent ≥ Release discipline — exactly what `rc_inc` provides. No cross-variable happens-before is lost by the downgrade.

**What /dev does:**
- Route `rc_inc_if_heap`'s body through `crate::rc::rc_inc(val)` — either collapse the helper to a one-line delegate or have the four accessors call `rc::rc_inc` directly (/dev's choice on keeping the local wrapper name for readability), mirroring the `shallow_rc_inc` re-route shape in §3.1.
- **Delete the open-coded arithmetic:** the local `AtomicI64`/`Ordering::SeqCst` view, the offset-8 `fetch_add`, and the helper's raw-pointer derivation go — that machinery now lives once, in `rc_inc`.
- **Guard-equivalence note (must hold for behaviour preservation):** the current heap-check guard `(val as usize) >= NULLARY_TAG_THRESHOLD` is equivalent, *for this representation*, to `rc_inc`'s skip guard `ptr < NULLARY_TAG_THRESHOLD as i64 → return`. Heap pointers and bare tags are never negative, so the unsigned `>=` test and the signed `<`-skip partition the same value space identically — a value `rc_inc`s iff `rc_inc_if_heap` would have. Behaviour is preserved except the **intended** SeqCst→Release downgrade.
- **Tests stay green:** the existing `accessor_*_rc_incs_field` unit tests (`trace.rs:1383–1490`) assert each accessor increments the field's RC; they remain valid and MUST stay green — the inc still lands on the same RC field, just via `rc_inc`. No new trace-side unit test is required for the re-route (behaviour-preserving apart from the ordering floor change, which the unit tier does not observe); /dev confirms the `accessor_*` module passes post-re-route.

### 6.2 `ivar.rs::ivar_spark` RC inc (`ivar.rs:98`) — IN scope: KEEP SeqCst, documented

The spark task takes a reference to the IVar cell before `rayon::spawn`, via a `fetch_add(1, SeqCst)` at `ivar.rs:98`. **`/arch` ruling (BC §4b inv 3 table, row 4): KEEP SeqCst — NOT routed through `rc_inc`.** This inc is **load-bearing**: it is paired with the spark's later `fetch_sub(1, SeqCst)` on the same RC field (`ivar.rs:117`) and interleaves with the IVar state-machine's SeqCst atomics (the `STATE_OFFSET` CAS PENDING→EVALUATING→RESOLVED, the resolved-value/error publish-stores at `ivar.rs:184/191/219`). The module's stated discipline is "all atomics use SeqCst (Decision 13)" (`ivar.rs:37`) — a single uniform total order across the cell's RC and state transitions that the fork-join correctness argument (`test-discovery.md` §6 ferry) reasons about. Demoting *one* of the cell's atomics to Release while its siblings stay SeqCst would break the uniform-total-order invariant the IVar protocol is verified against, for no benefit (the inc is one-per-spark, not a hot path).

**What /dev does — no behaviour change, documentation only:**
- The inc stays `fetch_add(1, SeqCst)`. It is **NOT** routed through `rc_inc` (which is Release).
- Add a **documenting comment** at `ivar.rs:98` recording that this is a deliberate, owned divergence from the blessed `rc_inc` entry point — SeqCst is retained for the IVar uniform-total-order invariant (Decision 13, `ivar.rs:37`), cross-referencing **FIXME 0397** and **`bounded-contexts.md` §4b invariant 3** (the canonical policy home + the per-site table row). This turns an accidental-looking open-coded atomic into a legible, justified exception, so a future reader (or `/review`) does not "fix" it by routing it through `rc_inc`.

### 6.3 `drop.rs` — removed from scope: NO production inc site (FIXME misidentification)

FIXME 0397 listed `drop.rs` as a third intrinsics-internal inc site (`Release`). **`/arch` corrected this (BC §4b inv 3, post-table note): `drop.rs` carries NO production RC-inc site.** Its production RC operations are all *decrements* (drop glue: `consume_*`, `dec_shallow_io` — atomic `fetch_sub(1, Release)` + free-path Acquire). The two `fetch_add(1, Release)` occurrences in `drop.rs` (`:542`, `:722`) are inside `#[cfg(test)] mod tests` — helpers that simulate a second reference to exercise the non-last-ref dec path. **No alignment action; nothing for /dev to touch in `drop.rs`.** (The `fetch_add`s elsewhere in the crate — `alloc.rs`/`io_observer.rs`/`vec_runtime.rs`/`trace.rs:138` — are bookkeeping counters, not RC, and are likewise out of scope.)

### 6.4 This sprint's full inc-site disposition

| Site | Crate | Disposition | Where |
|---|---|---|---|
| `marshal.rs::shallow_rc_inc` | primitives | route through `rc_inc` (Release) — **bug fix**, was non-atomic | §3.1 |
| `string.rs::string_identity` | primitives | route through `rc_inc` (Release) — behaviour-preserving dedup | §3.2 |
| `trace.rs::rc_inc_if_heap` | intrinsics | route through `rc_inc` (Release) — **SeqCst→Release downgrade**, gratuitous SeqCst removed | §6.1 |
| `ivar.rs::ivar_spark` (`:98`) | intrinsics | **KEEP SeqCst** — load-bearing; add documenting comment cross-ref'ing FIXME 0397 / BC §4b inv 3 | §6.2 |
| `drop.rs` (`:542`, `:722`) | intrinsics | **no action** — `#[cfg(test)]` helpers, not a production inc site | §6.3 |

Canonical policy home for all five rows: `design/arch/bounded-contexts.md` §4b invariant 3.

---

## 7. Acceptance (for /sprint to transcribe)

- `pub fn rc_inc(ptr: i64)` exists in `cranelisp_intrinsics::rc`, mirroring `consume_shallow`: nullary-tag-skip via `NULLARY_TAG_THRESHOLD`, RC field at `HeapHeader::RC_OFFSET`, atomic `fetch_add(1, Ordering::Release)`, `rc_trace("inc", ptr, new_rc)`, `#[inline]`, with the §2 rustdoc (ordering rationale + safety contract).
- Three `rc_inc` unit tests (increments / skips-nullary / traces) land green in `rc.rs` `#[cfg(test)] mod tests`, mirroring the `consume_shallow` tests, each with a `// spec:` annotation — written before the fix.
- `crates/cranelisp-intrinsics/public-api.txt` regenerated in the same change-set; diff is exactly the one `rc_inc` line.
- `marshal.rs::shallow_rc_inc` routes through `rc_inc`; the non-atomic `*rc_ptr += 1` and the MED-1 NOTE are deleted; existing marshal RC tests stay green.
- `string.rs::string_identity` routes through `rc_inc`; the inline `fetch_add` + local atomic/`HeapHeader` imports are deleted; behaviour-preserving, existing string tests stay green.
- FIXME 0397 is deletable by `/arch` once `rc_inc` lands (FIXME table 0397 row: "/arch deletes 0397 once `rc_inc` lands").
