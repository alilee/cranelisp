---
number: 22
title: A pointer published across a frame-outliving boundary has a named retention owner
---

# Principle 22 — A pointer published across a frame-outliving boundary has a named retention owner

> Authored S101 Wave 5 as the user-mandated **lifetime-across-suspension recurring-class ruling** (per `memory/feedback_review_root_cause_and_duplication` escalation). **RATIFIED by the user at the S101 Phase-7 close review, 2026-07-03** (full text reviewed at close; `sprints/archive/sprint-101.md` §Outcome is the audit trail), per the sprint-close-only convention in `principles.md`.

**Statement.** Whenever a raw pointer — a code pointer, a heap value, a baked argument block, a message buffer — is **published** across a boundary that outlives the publishing frame's synchronous lifetime model, the design MUST name a **single retention owner** whose release point is the boundary's **un-publish event**. Freeing, or invalidating in place, a still-published referent at frame/turn/teardown time is forbidden **by construction**: displacement is a *move of the retained handle into the boundary's retention structure* (representation, per Principles 18/20) — never `*x = None`, never a direct free at the publishing site. The publication boundaries in this architecture are: GOT-slot publication (compiled callers embed the slot; heap closures embed the code pointer directly), reactor suspension/registration (a deferred effect's baked args outlive the constructing frame), launched-strand handoff (a detached strand's inputs outlive the launching turn), and staged→live displacement (a superseded entry's `Code` may be the last `Arc` over live JIT pages).

**Companion detection rule.** Every such boundary lands with a **layout-neutral, debug-mode liveness tripwire at the consume point** — the pattern proven by `cranelisp-intrinsics`: `alloc::is_live` at the RC-dec point (`drop.rs::atomic_dec_rc`), the `databuf_guard` side-table for untracked vec data buffers (`vec_runtime.rs`), and the GOT-trace `SlotFreeze`/`TrapPatch` events for the code-pointer boundary. *Layout-neutral* is load-bearing: ASAN and `MALLOC_CHECK_` both **hid** the S98 instance by perturbing allocator layout (`memory/feedback_verify_fix_not_symptom_absence`); side-table instrumentation that does not touch the allocation is the one class that cannot close the race window it is watching.

**Motivating recurrence (the register).** Three-plus instances of the same class, each initially fixed per-instance:

1. **S97/S98 — launched-effect baked-arg UAF** (FIXMEs 0486/0494): a reactor-deferred effect's args were freed by the constructing frame's teardown. Cured by the runtime-owned keep-alive at the `EffectPoll`/`reg` seam; the contract is canonical as **`bounded-contexts.md` §4b invariant 15** (arg-lifetime-across-suspension is runtime-owned, because deferral-across-frame-teardown is a runtime-scheduling fact the backend's synchronous lifetime model does not model).
2. **S101 — the `*code = None` displacement class**: dropping a superseded entry's `Code` Arc (possibly the last) while its GOT slot and compiled callers still reference the JIT pages. Cured structurally by the session **RetentionPool + ABI-epoch slot freeze** (`design/int/session-transaction.md` §6/§7 — the commit gate is the single slot-policy authority; BROKEN code moves to the pool, never `None`d in place). **FIXME 0479 then found a third missed displacement site in the same sprint** (slot-less staged entry replacing a slotted prior) — the direct proof that per-instance fixing of this class does not terminate: every displacement site is a new opportunity to miss the move-to-pool.
3. **0494 bug #2 — launched-strand heap teardown** (closed S98): free-ownership defect on launched teardown; the standing drop-glue tripwires above are its residue and remain the class's detectors. (The 3 `drop::tests` failures newly visible at S101 via default-members are a *test-fixture* artifact of these tripwires, not a live product instance — see the S101 `/qa` ledger.)
4. **S101 — the trap-stub message buffer**: `compile_trap_stub` bakes the message *address*; bytes are read per invocation. Handled by construction — the retention pool pairs every retained `Code` with its message buffer, one owner, one release point (`session-transaction.md` §6.2).

**Ruling.** The class gets the structural guard, not continued per-instance fixes:

- Any change-set that **introduces or widens** a boundary where a raw pointer can outlive its publishing frame must, in the same change-set: (a) **name the retention owner and the un-publish release point** at the boundary's canonical home (facade / BC invariant / subsystem design doc); (b) implement displacement as a **move into the retention structure**; (c) land — or cite as covering — a **layout-neutral debug tripwire** at the consume point.
- `/review`'s standing watchlist: any diff that frees or `None`s a possibly-published referent in place — `ModuleEntry` `code` Arcs, GOT-visible pointers, reactor/strand-visible heap values, baked buffers — without a named owner is a finding, regardless of whether a crash reproduces.
- The boundary inventory is part of the **actor/function model** (Principle 21): suspension points, publication points, and teardown points are actor-boundary functions; a design that does not name them has not laid the actors bare.

**Cross-references.**

- Principle 18 — Enforce architectural invariants structurally (the retention structure *is* the enforcement).
- Principle 20 — Model invariants by representation (moving the handle into the pool makes "freed while published" unrepresentable; the ABI-epoch slot freeze is the same idea for ABI identity).
- Principle 21 — Actors and functions before mechanism (FIXME 0486's UAF fell in the unnamed crack between two locally-correct actors; the publication boundary was the unnamed function).
- Principle 14 — FFI layout discipline (the tripwires must be layout-neutral for the same reason layout is a contract).
- `bounded-contexts.md` §4b invariant 15 — the reactor-seam instance of this Principle, pre-dating it.
- `design/int/session-transaction.md` §6–§7 — the GOT/Code instance of this Principle.
