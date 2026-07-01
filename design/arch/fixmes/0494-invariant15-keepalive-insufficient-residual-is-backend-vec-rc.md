---
number: 0494
target: /arch
filed_by: /dev
filed_at: 2026-07-01
sprint_filed: 98
refers_to: design/arch/bounded-contexts.md §4b invariant 15 + §3 backend-obligation note, design/arch/fixmes/0486-arch-int-backend-boundary-for-the-trampoline.md (S98 Level-1 ruling), crates/cranelisp-intrinsics/src/{io.rs (await_poll_node), reactor.rs (EffectPoll/StateClosure), drop.rs}, tests/launch_vec_send_corrupt.rs, tests/launch_grid_corrupt.rs, tests/exemplar_web.rs
status: open
---

# Invariant-15 runtime keep-alive LANDED but does NOT fix bug #2 — the residual UAF is a /backend borrowed-Var two-live-vec RC miscount, not the poll state-closure

## Context — what S98 band-A asked for

FIXME 0486 Level-1 (S98 /arch ruling) locked: bug #2's launched-effect UAF is fixed by
**runtime-owned keep-alive of the poll effect's state-closure** at the intrinsics
`EffectPoll`/`reg` seam (BC §4b invariant 15), **no backend change**. `/dev` (this crate)
was to land the fix, flip `launch_grid_corrupt` + `launch_vec_send_corrupt` green, and
un-ignore `exemplar_web`.

## What landed (correct, kept)

The invariant-15 runtime keep-alive is **implemented and correct** — the **net-zero-inc**
variant: `io::await_poll_node` takes ONE extra RC ref (`rc_inc`) on the state-closure and
hands it to the `EffectPoll`, which releases it (`consume_closure`) exactly once at resolve
(`Poll::Ready` or cancel-drop) via a new `StateClosure` RAII guard; the node's field-0 is
left untouched, so the sub-tree's own tag-4 reclamation still dec's the node's ref and the
closure is freed at the LATER of {node-release, effect-resolve} = true rc→0. This preserves
the pre-fix closure free-timing (listener/conn lifetime correct) AND holds the state-closure
live across a launched teardown. Unit-tested at the seam (2 green: `reactor::tests::
keepalive_state_closure_consumed_exactly_once_on_{ready,cancel_drop}` — exactly-once release
across suspend/resume and cancel). Release gate clean (zero new warnings). This half is DONE
and should stay.

## The finding — invariant 15 is necessary but NOT sufficient for bug #2

With the correct keep-alive landed, **both guards remain RED** (`launch_vec_send_corrupt`,
`launch_grid_corrupt` → genuine SIGABRT `free(): chunks in smallbin corrupted`, server
serves then crashes). The state-closure keep-alive does not touch the failing object.

**Root cause (measured, two independent lines of evidence):**

1. **QA Stage-1 reduction (S98, already in the fixture header):** the load-bearing floor is a
   **borrowed-Var `(Vec …)` with TWO vecs both live** across the launched render — NOT the
   marshaled `Response`/String. String body alone: 0/8. Single live vec: 0/8. **Two live
   vecs: 8/8 SIGABRT.** The vecs (`g` = `build`, `s` = `assoc`-churned) are consumed by
   `render` into the body String INSIDE `make-resp` and dropped at its `let` scope **before**
   `send-conn` even exists — so they are **not captured in the send-conn state-closure**.
   Keeping that closure alive (invariant 15) cannot keep the vecs alive.

2. **/dev A/B of both invariant-15 variants (this sprint):**
   - **net-zero-inc** (shipped): preserves free-timing → server serves correctly
     (`exemplar_web::fans_out` reliably green 3/3, ~2.1s, identical to pre-fix) → the launched
     two-live-vec render runs → **still SIGABRTs**. RC trace shows a UAF *write* to freed
     memory (heap-metadata overrun), not a clean RC underflow.
   - **move-out-with-sentinel** (arch-preferred in the 0486 note): eager-frees EVERY poll
     effect's closure on `Ready`, **including the `accept` effect's closure that captures the
     LISTENER**. Freeing it early wedges the accept loop → the server **hangs** after the
     first connection → the launched vec-render never runs enough to trip the bug → no SIGABRT
     → the guard reads "no signal" and goes **false-green**, while the real serve path
     reliably breaks (`exemplar_web` times out 3/3, 22s). This is a **hang masking the crash**,
     not a fix — precisely the "un-isolated recurring failure" trap.

So the arch-preferred variant is a false-green, and the correct variant leaves the defect. The
residual UAF is a **backend codegen RC miscount on the borrowed-Var vec path
(`ring2-rc.md §5.5`) exercised by the launched strand** — the exact retarget the S98 /qa
Stage-1 note flagged ("the failing hold is the borrowed vec, not the marshaled Response…
retargets /backend's fix toward the borrowed-Var vec RC path"), which the Level-1 ruling
noted but held "invariant 15 unchanged."

## Proposed resolution

1. **Keep** the shipped invariant-15 runtime keep-alive (net-zero-inc) — it is the faithful,
   correct runtime half of the contract and is unit-tested. BC §4b invariant 15 stands as the
   runtime contract; it is just not the whole story for bug #2.
2. **Re-scope the Level-1 "no backend change" premise.** The evidence contradicts it: the
   bug-#2 guard UAF is a `/backend` borrowed-Var two-live-vec RC miscount on the launched
   strand, not a state-closure arg-lifetime gap. `/arch` should either (a) re-point the
   Phase-5 owner of the guard-flip to `/dev`(backend, on `cranelisp-backend` codegen) with a
   fresh minimal repro, or (b) if `/arch` still believes it is runtime-shaped, name the
   specific runtime object whose lifetime is wrong (it is not the poll state-closure — proven
   above).
3. **Guards + `exemplar_web` stay as they were at S98 entry:** `launch_vec_send_corrupt` +
   `launch_grid_corrupt` RED (un-ignored defect repros, correct — the defect persists);
   `exemplar_web::serves_form` re-`#[ignore]`'d with the finding + FIXME 0486 pointer (I
   reverted the un-ignore — un-ignoring would inject a flaky RED, worse than the guarded
   ignore). `0492` (exemplar v9 adoption, blocked on bug #2) stays blocked.
4. **Minimal repro for the /backend handoff** (per root `CLAUDE.md` §"Cross-skill defect
   handoff requires minimal repro"): the two committed guards are the repro; the smaller
   `launch_vec_send_corrupt` (two live `(Vec Int)`, borrowed-Var `get`/`assoc`, launched
   `send-conn`, no ADT wrapper) is the reduction floor. A `/backend` deployment should shrink
   further toward a non-server repro (launched strand + two-live-borrowed-vec render, no
   socket) and inspect the CLIF/`CRANELISP_RC_TRACE` for the borrowed-Var vec double-dec.

## Operational implication

- Band-A does **not** deliver green guards this sprint via the intrinsics seam. The runtime
  keep-alive half is done; the guard-flip is owed to a **/backend codegen** fix (new or
  re-pointed task). `0486` should stay OPEN carrying this residual; `0492` stays blocked.
- I did not edit `design/` (per `/dev` boundary) beyond this FIXME. The `reactor.md`/
  `io-trampoline.md` invariant-15 cite-back that `/design` was to add with the fix should now
  also record that keep-alive is necessary-not-sufficient for bug #2.
