# Signature/body pre-pass — the structural close of the H6/H7 import race

**Owner**: `/design` (int). **Status**: DESIGN (Sprint 93 Phase 3 — the reactor gate).
**Supersedes** (as the structural successor): `design/int/heisenbug-race-closure.md`
(the H4→H5→H6→H7 tactical lineage). **Subordinate to**: `design/int/int.md` §1,
`design/arch/bounded-contexts.md` §6, `design/arch/sequences/concurrency-dependency-service.mmd`.

This document specifies the **signature/body pre-pass barrier** — the arch-pinned
structural fix (S93 Phase 2 ruling, BC §6) for the compiler-internal H6/H7
import/typecheck race (`'helper-val' not found in module 'helper'`, FIXME 0425
item 1) and the D0030 mutual-import deadlock (FIXME 0426). It is the **gate** of
Sprint 93: the reactor (slice-2) implementation does not begin until the isolated
race repro is deterministically green, achieved via this fix.

Scope discipline (arch R2): this design covers **0425 item 1 ONLY**. FIXME 0425
items 2–4 (`SharedState` per-field ownership sweep, `cached_modules` dual-store
collapse, priority/nice worker unification) are **non-gating, drain-if-time** and
are explicitly **not designed here** — see §7.

---

> **As-built reconcile (S93 Wave-2b/2c — FIXME 0452/0453 ruling; BC §6 canonical).**
> This doc was authored as forward DESIGN; three points are reconciled to the
> as-built. **BC §6 is the canonical record; this doc mirrors it.**
>
> 1. **Eval-thread rest state is `TypecheckDone`, not `TypecheckWorking`** (§3.1,
>    §5/§7 step 5). The originally-designed exclusive `TypecheckWorking` claim and
>    the as-built terminal `TypecheckDone` rest are **B1-equivalent**: neither sits
>    in a typecheck queue (`typecheck_first`/`typecheck_next`), so neither is
>    pool-reclaimable. The entry rests in `TypecheckDone` while the eval thread
>    drives — `claimable XOR owned → owned`, no pool worker can re-claim it. This
>    is a wording reconcile, not a behaviour change.
>
> 2. **The net-subtractive machinery-LOC mandate is RETIRED as wrong, not a
>    defect** (§5, §7 step 2, §7 close). Per the 0452 ruling, the requeue kernel is
>    **reused** (it also drives dep-file discovery + submodule super-import ordering
>    — not deletable), and the Invariant-SW structural single-owner claim inherently
>    costs more LOC than the deleted `eval_owned` convention flag — the Principle-18
>    structure-over-convention trade. **Net-additive (~+75) is the correct floor.**
>    The surviving, load-bearing invariant is *one* readiness protocol, **no second
>    live wait/notify subsystem** (Principle 7) — keep that, drop the net-LOC
>    projection.
>
> 3. **`signatures_ready` field + `register_module_signatures` + the
>    `SignatureBarrierRegister` trace tag were REMOVED (Wave-2c — the one
>    subtraction taken).** They were live-dead: `signatures_ready` was set only by
>    `notify_typecheck_done` (coincident with `pool → TypecheckDone`), and
>    `register_module_signatures` had no live caller. The barrier predicate now
>    reads **pool-terminal state (`TypecheckDone|Complete`) directly**: because
>    `notify_typecheck_done` runs post-`finalize_cluster`, the terminal pool
>    transition already **IS** the signature-publication edge. Wherever §3 below
>    names `signatures_ready` / `register_module_signatures` as live machinery, read
>    it as **"the pool-terminal predicate (`TypecheckDone|Complete`)"** — the
>    explicit Phase-A bit was the design's framing device, not the as-built
>    mechanism.

---

## 1. Why the tactical lineage kept resurfacing (the problem restated)

The race is **not** a single bug; it is a **class** of bug enabled by one
structural defect. FIXME 0425 names it precisely: the dependency
**publish / readiness / block / resume** protocol is *one logical temporal
invariant smeared across four files* — `src/scheduler.rs`, `src/worker.rs`,
`src/process_form.rs`, `src/session_v4.rs` — with **no single owning subsystem**
(`concurrency-architecture.md` §3.5 "Very High" risk; §3.6 "High" risk). The
`concurrency-dependency-service.mmd` diagram asserts a clean invariant — "only
the scheduler mutates readiness state; workers never read shared state directly"
— but the as-built **achieves it by convention** (every call site must remember
to route through the right call), **not by construction**. That is a Principle 18
gap (invariant enforced by discipline, not representation) and a Principle 13 gap
(the diagram claims a "dependency service" actor the code does not embody as a unit).

The tactical lineage is the evidence that convention does not hold under load.
Each patch closed one interleaving window; the race re-emerged through the next:

| Hyp | Tactical patch | Disposition (current as-built, S93) |
|---|---|---|
| H4 | elide duplicate `register_dep` publish/register pair | landed; net-positive; **did not close the race** |
| H5 | `eval_in_flight` RAII flag suppressing worker re-claim | **DELETED in S78** (in-call-stack restructure) — arch now forbids it as the gate (R1, Principle 8) |
| H6 | atomic `ensure_module_exists` via DashMap `entry()` | **landed** (now in `cranelisp-types::ensure_module_exists`, atomic) |
| H7 | (named, never isolated) residual data-plane window | **the live recurring failure** — fires ~5–10% under contention, ~1/14 full runs since S92 slice-1 CPU load |

The decisive observation: **with `eval_in_flight` deleted and `ensure_module_exists`
already atomic, the race still fires.** The residual mediation is the `eval_owned`
role-flag on `ModuleState` plus the `try_unblock_locked` early-return — *another
convention flag of the same family*. S78 Wave-2b already diagnosed this class as
**structural** ("needs a /design decision on single-orchestrator ownership of the
REPL module, not a condvar patch"). S93 actions that decision.

The residual H7 window (to be pinned deterministically by `/qa`, §5) is the
**body-observes-an-incompletely-published-sibling** window described by §3.6: a
reader (the dependent's body, on the eval thread or a worker) observes a
dependency's terminal readiness (`is_typechecked(dep) → TypecheckDone`) and then
reads `symbol_tables[dep]`, but the readiness signal and the symbol publication are
ordered **by convention across scheduler + typecheck + reader fast-paths**, not by a
single barrier. The fix removes the window by construction: **no body is admitted
to read any sibling table until every signature in the closure is wholly published.**

---

## 2. The structural fix — two coupled invariants

The fix replaces the convention-spread protocol with **two structural invariants**,
both **internal to `src/`** (no cross-crate interface change — see §4 and the BC §6
boundary note). They are the `src/` embodiment of the
`concurrency-dependency-service.mmd` two-phase barrier.

### Invariant PP — Signature pre-pass barrier (the gate)

> **Every module's signatures register before any body typechecks.**

Concretely, for a cluster admitted to the pipeline:

1. **Phase A — signature registration.** The scheduler computes the cluster's
   **static dependency closure** from the Pass-0 structural import declarations
   (`extract_module_declarations` already peels `mod`/`import`/`export`/`platform`
   in `process_cluster_once` Pass-0 — no inference needed to know *which* modules
   the closure contains). Each closure module's signatures become visible when the
   module reaches the **pool-terminal `TypecheckDone|Complete`** state (the as-built
   publication edge — see As-built reconcile point 3; the design's framing named a
   per-module `signatures_ready` bit, which was removed in Wave-2c as live-dead). A
   scheduler gate `await_signature_barrier(closure)` opens when the **last** closure
   module reaches that terminal state. It is the S78 **requeue gate**, not a thread-park (BC §6):
   a pool worker that reaches the gate frees its thread back to the pool and requeues
   its body work; only the eval thread (the REPL main thread, no pool slot) genuinely
   waits (§3.1).

2. **Phase B — body typecheck.** Once the barrier opens, bodies typecheck against
   a **now-complete** signature table. A body blocks **only** on in-mem / codegen
   readiness (`wait_for_inmem` — a strictly *later*, monotone signal), **never** on
   a sibling's signature. The per-symbol `block_for_typecheck` /
   `notify_symbol_typechecked` readiness path — the convention chokepoint §3.5/§3.6
   describe — is **retired** for the signature dimension (it is replaced by the
   barrier; the `.mmd` already commits to this retirement).

**Why this closes H6/H7 structurally**: the readiness signal a body observes
(barrier-open) is, *by construction*, downstream of the publication it depends on
(all closure signatures). There is no "observe-ready-then-read-stale" window
because the read target is wholly published before any reader is admitted. The
window §3.6 calls "the core correctness contract that is hard to prove without
compartmentalisation" becomes provable: the barrier *is* the compartment.

### Invariant SW — Single-writer (single orchestrator) per module

> **A module's signature registration is driven by exactly one orchestrator,
> enforced by an exclusive claim transition — not by a role flag.**

The current dual-orchestration (eval thread vs pool worker can both reach the same
module) is mediated by the `eval_owned` early-return in `try_unblock_locked` — a
convention flag keyed on orchestration *role* (data on `ModuleState`). The
structural replacement: the claim itself is **exclusive by construction** — a
module is *claimable* (present in `typecheck_first`/`typecheck_next`) **XOR**
*owned* (popped, in `TypecheckWorking`). A pop removes it from the queue
atomically under the scheduler state lock; an owned module is never re-pushed while
owned. Both the eval thread and pool workers draw from the **same** claim
discipline. There is no second path to suppress, so there is no flag to set.

`eval_owned` and the deleted `eval_in_flight` are the *same convention-flag
family*; Invariant SW subsumes both: the entry module's "single owner" property
falls out of the uniform exclusive-claim rule instead of a role-keyed special case.

**The two invariants are coupled, not independent.** PP without SW would let two
orchestrators concurrently drive the same module's Phase-A registration (re-opening
the H6-class overwrite at signature granularity). SW without PP would keep the
per-symbol convention readiness path (the §3.6 window). Together they make the
publish→readiness→resume ordering **structural**: one writer, one barrier, one
monotone codegen signal in Phase B.

---

## 3. Concrete `src/` changes — functions, structs, ordering guarantee

Grounded against the **current** as-built (S93): `ModuleState { pool, waiters,
jit_reserved, inmem_done, inmem_claimed, object_working, object_done, error, sexps,
eval_owned, blocked_on }`; `ModulePool ∈ {TypecheckFirst, TypecheckNext,
TypecheckWorking, TypecheckBlocked, TypecheckDone, Failed, Complete}`; claim via
`try_take_work_locked`; readiness via `notify_typecheck_done` /
`notify_symbol_typechecked` / `block_for_typecheck` / `try_unblock_locked`;
in-call-stack cluster sexps ride `PriorityWork::Typecheck { module, sexps }`;
gap-retry via `ClusterOnce::Gap { dep }` + `drive_module_dep` (worker) /
`register_dep_for_eval` (eval).

### 3.1 `src/scheduler.rs` (primary — the new barrier subsystem)

- **`ModuleState`**: ~~add `signatures_ready: bool`~~ **(NOT added — Wave-2c
  reconcile.** No explicit Phase-A bit exists in the as-built; the barrier predicate
  reads pool-terminal state (`TypecheckDone|Complete`) directly, because
  `notify_typecheck_done` runs post-`finalize_cluster` so `pool → TypecheckDone`
  already IS the signature-publication edge — see the As-built reconcile callout,
  point 3, and BC §6.) Retire `eval_owned` once SW lands (the uniform exclusive-claim
  rule subsumes its single-owner role) — staged in §5 Step 5, not Step 1, to avoid a
  half-migrated dual model (Principle 8).
- **`dependency_closure(root, &import_decls) -> Result<ClosureOrder, CycleError>`**:
  topologically order the static import closure from Pass-0 decls; reuse
  `detect_cycle_locked` for the back-edge check. A cycle returns `CycleError`
  (this is the D0030 disposition — see §3.3).
- ~~**`register_module_signatures(m: &ModuleFullPath)`**~~ **(REMOVED — Wave-2c
  reconcile; no live caller.** The design's framing was an explicit Phase-A
  registration unit driving `m`'s signatures to a `signatures_ready` bit; the
  as-built has no such call. The module-atomic publication is the existing
  `finalize_cluster` → `notify_typecheck_done` → `pool → TypecheckDone` transition,
  which flips `m` from wholly-absent to wholly-published for *all* its symbols at
  once (no per-symbol publish window) — exactly the property the design assigned to
  `register_module_signatures`. The barrier predicate reads that pool-terminal state.
  The `.mmd`'s `register_module_signatures` actor message is satisfied by the
  cluster-finalize edge, not a separate call.)
- **`await_signature_barrier(closure: &ClosureOrder) -> Result<(), SchedulerError>`**:
  the **S78 requeue gate**, NOT a thread-park (FIXME 0450 ruling B; BC §6
  "Signature-barrier worker-pool model — free-back-to-pool requeue, NOT
  thread-park"). A **pool worker** that reaches a module whose static-import closure
  is not yet wholly `signatures_ready` registers the unregistered closure members
  into the Phase-A queue (the existing register-edge), **frees its thread back to the
  pool**, and requeues its body work to be re-claimed when the barrier opens — it
  **never blocks a pool thread** on a signature dependency (preserving S78's
  free-back-to-pool deadlock-freedom; `s78-implementation.md` §0/§1.3). The scheduler
  **opens the barrier** — sweeping the requeue via the existing
  `priority_work_available` / `completion` condvar — when the **last** closure module
  reaches `signatures_ready`. The one genuine waiter is the **eval thread** (the REPL
  main thread, *not* a pool thread): it consumes no pool slot, so its wait never
  reduces pool capacity. With no parked pool workers, a bounded pool of size ≥ 1
  cannot deadlock by all-workers-parked.
- **`wait_for_inmem(fq)` / `notify_inmem_codegen_complete(fq)`**: the Phase-B-only
  readiness pair (the existing `wait_module_inmem_complete_blocking` /
  `notify_typecheck_done` codegen-readiness role, narrowed to Phase B). The
  per-symbol `notify_symbol_typechecked` signature-readiness path is **deleted**
  (subsumed by the barrier).
- **Claim discipline (`try_take_work_locked` / `dispatch_typecheck_locked` /
  `try_unblock_locked`)**: formalise the exclusive pop (already mostly true — a pop
  removes from the deque); remove the `eval_owned` early-return branch in
  `try_unblock_locked`, replacing it with the uniform rule "a module owned (in
  `TypecheckWorking`) is not re-pushed." `try_unblock_locked` **gates the requeue on
  the closure-barrier predicate** (every module in the closure has
  `signatures_ready`) in place of the per-dep `blocked_on` flag — this is the
  requeue-gate substrate of `await_signature_barrier` (§3.1): the scheduler sweeps
  the requeued body work when the last closure module reaches `signatures_ready`.

### 3.2 `src/worker.rs` + `src/process_form.rs` + `src/cluster.rs`

- **`process_cluster_once` (the shared core)**: split the existing Pass-1
  (register signatures/macros/defaults) from Pass-2 (expand + check bodies) at the
  **orchestration** boundary. Pass-1 for the whole closure runs in Phase A; Pass-2
  bodies run only after `await_signature_barrier`. The `ClusterOnce::Gap { dep }`
  variant for **signature** dependencies is removed — signature deps are resolved
  in Phase A, so a body never returns a signature gap. Only codegen/in-mem gaps
  remain in Phase B.
- **`drive_module_dep`** (`src/process_form/dependency.rs`): becomes the Phase-A
  closure-walk driver — it registers each discovered closure module's edge and routes
  it through `register_module_signatures`, then **returns its thread to the pool**
  (the S78 register-edge + return-to-pool discipline — never parks internally). The
  retry-from-top loop is retained **only** for Phase-B codegen gaps.
- **`handle_typecheck_work_shared`**: a worker that claims a module checks the
  closure's Phase-A barrier; if any closure member is not yet `signatures_ready` it
  registers the unregistered members' edges, **frees its thread back to the pool**,
  and requeues the body work (gated on the closure-barrier predicate, §3.3) rather
  than parking on the barrier. The requeued claim runs the module's Pass-2 bodies
  only once the scheduler opens the barrier (last closure module `signatures_ready`).

### 3.3 The ordering guarantee (how signatures become visible before bodies)

The new ordering, stated as an invariant a reader of `try_take_work_locked` /
`await_signature_barrier` can verify locally:

> For any module `m` admitted to Phase B (Pass-2 body typecheck), **every** module
> in `closure(m)` has `signatures_ready = true`, and that bit transitioned to
> `true` under the scheduler state lock strictly before `m`'s body claim. The
> scheduler state lock's release-acquire chain carries the happens-before edge from
> each `register_module_signatures` write to the `await_signature_barrier` return,
> and from there to the body's read of `symbol_tables[sibling]`.

This is the structural property the convention protocol only *approximated*.

---

## 4. How 0426 (D0030 mutual-import deadlock) is subsumed

D0030: when A's Pass-0 hits `(import [B [*]])` it blocks on B's signatures while B's
Pass-0 hits `(import [A [*]])` and blocks on A's — neither progresses, because
signatures register incrementally form-by-form rather than in a separate pre-pass
(FIXME 0426 / Decision 0030).

The pre-pass addresses D0030 along the **same axis** as the race — it is "the kind
of change a dependency-service extraction invites" (0426 §"Proposed resolution"),
which is exactly why arch coupled the two (R3: 0426 evaluated in the same design
pass). **The disposition is settled by user ruling (S93 Phase-3 review): mutual
imports are a compile-time cycle-error — they are NOT compiled.** Concretely:

- **The ratified disposition (module-atomic barrier; src/-only; closes the GATE):**
  Phase A drives each closure module's **full** signature registration in
  dependency (topological) order. A cycle has **no** topological order;
  `dependency_closure` returns `CycleError`, and the existing `detect_cycle_locked`
  fires. **Effect on D0030: the deadlock (a hang) becomes a deterministic
  cycle-detected error at the import site.** This is a strict improvement — a hang
  is the worst failure mode; a clean diagnostic is correct, debuggable behaviour —
  and it is **fully achievable in `src/` with no cross-crate change.** It does
  **not** compile mutually-importing modules, by design ruling.

- **The rejected alternative — compiling mutual imports (rejected by user ruling,
  S93; NOT deferred):** a "fine reading" would register **only signatures**
  (Pass-1) for all closure modules *including both directions of a cycle*, then run
  all bodies in Phase B, compiling mutual imports. **This is rejected.** It would
  require `register_module_signatures` to register a module's signatures WITHOUT
  running its bodies — i.e. typecheck would have to expose a Pass-1-only entry
  callable independently of Pass-2. The current typecheck surface
  (`cranelisp_typecheck::check_forms`) runs Pass-1 + Pass-2 **atomically in one
  call frame** (S78 in-call-stack model). Worse, Cranelisp **infers** unannotated
  signatures (`(defn id [x] x)` has no written type), so a complete signature-only
  pass for inferred definitions would need typecheck's inference engine, not a
  syntactic int-side scan — **a cross-crate change to `crates/cranelisp-typecheck`,
  owned by `/typecheck` + `/arch`**, contradicting BC §6's "no cross-crate
  interface impact." The user ruling closes this off: there will be no
  mutual-import compilation, so no such cross-crate Pass-1 entry will be added.

**Disposition for S93 (final, ratified):** mutual imports = **compile-time
cycle-error**. The module-atomic barrier (Invariants PP+SW) closes the H6/H7 race
structurally **and** converts the D0030 deadlock into a clean cycle-error — both
`src/`-only, with no cross-crate interface change. The authoritative home for the
ruling is **BC §6** (resolving FIXME 0448 — the COARSE reading) and the
`concurrency-dependency-service.mmd` Note (both carry the S93 user ruling). FIXME
0448 is **closed** (resolved + deleted by /arch); this document records the
disposition, it does not pose it as an open question.

---

## 5. Why structural, not convention (Principle 8 / Principle 18)

The S93 ruling R1 **forbids** landing the tactical `eval_in_flight`
convention-flag as the gate. The contrast is the whole point of the fix:

- **`eval_in_flight` (heisenbug §8.2, now deleted) was an additive side-channel.**
  It left the dual-orchestration model intact and added a boolean to *suppress* one
  path's queue-push in a specific window. It is convention because (a) a human must
  remember to set/clear it at exactly the right scope — the S61 record shows the
  painful "narrow-vs-function-entry" scope tuning (§3e'), live evidence of its
  fragility — and (b) it patches one symptom window, not the class. Principle 18
  (enforce invariants by representation, not discipline) and Principle 8 (no interim
  implementations) both reject it. `eval_owned` is the same family — a role flag
  with a special-case early-return.

- **The pre-pass makes the flag unnecessary.** Under PP, no body is dispatched until
  the barrier opens — there is no concurrent claim *to* suppress, so there is
  nothing for a flag to gate. Under SW, the claim is exclusive by construction — the
  single-owner property that `eval_owned` asserted by convention is now a
  *consequence of the representation* (claimable XOR owned). The invariant the
  `.mmd` diagram draws ("only the scheduler mutates readiness; pool workers
  free-back-to-pool and are requeued, never reach into shared state") becomes the
  *structure* of the code, not a property every call site must uphold. This is
  precisely Principle 13 (the diagram's actor is embodied as a unit) and Principle 18
  (structural enforcement).

Net complexity (Principle 6 — complexity has a budget): the barrier **replaces**
the per-symbol wait/notify subsystem and the `eval_owned`/`eval_in_flight` flag
family. The load-bearing constraint is **one readiness protocol — no second live
wait/notify subsystem** (Principle 7): the `.mmd` retires
`notify_symbol_typechecked`/per-symbol `block_for_typecheck`, and keeping both live
would be two readiness protocols for one logical invariant. **The earlier
"net-neutral or subtractive machinery-LOC" projection is RETIRED as wrong (0452
ruling; As-built reconcile point 2; BC §6):** the requeue kernel is *reused* (not
deletable — it also drives dep-file discovery + submodule super-import ordering),
and the Invariant-SW structural single-owner claim costs more LOC than the deleted
`eval_owned` flag (the Principle-18 structure-over-convention trade). **Net-additive
(~+75) is the correct floor**; the one subtraction taken is the live-dead
`signatures_ready`/`register_module_signatures`/`SignatureBarrierRegister` removal
(reconcile point 3). The surviving invariant — one protocol, no second live
subsystem — is the load-bearing constraint on the Phase-5 implementation (§5 risk).

---

## 6. The `/qa` isolation hook — named seam + triggering interleaving

The gate's shape is **isolate-then-fix** (Scope 1a/1b): `/qa` first turns the
"unisolated recurring failure" into a **pinned, deterministic** failing test, then
the fix flips it green and keeps it green under contention.

### Named seam

The fix lives in `src/scheduler.rs` (the barrier + claim discipline), so the
isolation seam is the **scheduler readiness API surface**, instrumented with the
existing `#[cfg(test)]` accessor pattern S61 established (`module_pool_for_test`,
`force_typecheck_blocked_for_test`, `try_unblock_for_test`, `eval_in_flight_for_test`
— extend with `signatures_ready_for_test` + injectable pause-points). Two test
tiers:

1. **Structured-interleaving unit test (`src/scheduler.rs::tests`, deterministic).**
   Model the 2-module import graph `helper ← user` with two simulated orchestrators
   (eval `t1`, worker `t2`) and **two test-only pause gates**:
   - **P_publish** — between "set `helper` pool → `TypecheckDone`" and "all of
     `helper`'s symbols visible in `symbol_tables[helper]`" (the §3.6 publication
     window).
   - **P_read** — in the dependent's resume path, after `is_typechecked(helper)`
     returns true, before the body reads `symbol_tables[helper]` for `helper-val`.

   The triggering interleaving (reproduces `'helper-val' not found` **before** the
   fix): force `t1` to take **P_read inside the window P_publish has opened** —
   `t1` observes `helper` terminally ready and reads its table while `helper-val`
   is not yet in it. Assert the read finds `helper-val`. **Pre-fix:** an
   interleaving exists where it does not (RED). **Post-fix:** `P_read` is in Phase
   B, which is **unreachable** until `await_signature_barrier` (all signatures
   published), so the interleaving cannot occur — GREEN in *every* schedule.

2. **Loom model (if `/qa` adopts loom; the strongest form).** Model
   `symbol_tables[helper]` as a loom cell and the pool transition as a loom atomic;
   two loom threads run the publish and the dependent resume-read. Assert: in **all**
   interleavings, "observe `is_typechecked(helper)`" ⟹ "subsequent read of
   `symbol_tables[helper]` contains `helper-val`." Loom exhaustively finds the
   pre-fix counter-interleaving and proves its absence post-fix. This is the
   deterministic-replacement for the 6-thread stress repro's nondeterminism.

### Existing stress repro (the contention guard)

`tests/repl_persist_race.rs::heisenbug_race_reduced_concurrent_import_pairs`
(6 threads × 2 sequential import pairs, fast-fail over 10 trials; `tests/plan/ledger.md`
:2118) stays in the suite as the **contention** guard. Acceptance: it stays green
20/20 under full-suite load. The deterministic test (tier 1/2) is the **regression
pin** (un-ignored per `memory/feedback_failing_not_ignored.md`); the stress test is
the **load** guard. Both are required (they answer different questions — Principle 5).

---

## 7. Phase-5 `/dev` implementation plan (ordered; per-step unit-test seam)

Single agent, serial (worktree isolation broken). Each step lands with its unit
test(s) **first** (failing), then the change flips them green (per `memory/
feedback_unit_test_per_fix.md`). Steps 1–3 are scheduler-internal and unit-testable
without the full pipeline; steps 4–6 integrate; step 7 is the gate.

1. **Static dependency-closure + cycle error.**
   `dependency_closure(root, &import_decls) -> Result<ClosureOrder, CycleError>`,
   reusing `detect_cycle_locked`.
   *Unit seam* (`src/scheduler.rs::tests`): acyclic 3-module graph → assert
   leaves-first order; 2-cycle → assert `CycleError`. Single-threaded, deterministic.

2. **Phase-A barrier.** `await_signature_barrier(closure)`. *(As-built reconcile:
   no `signatures_ready` field and no `register_module_signatures` are added — the
   barrier predicate reads pool-terminal state `TypecheckDone|Complete` directly,
   point 3.)*
   *Unit seam*: register N modules under scoped threads; assert the barrier blocks
   until the last module reaches `TypecheckDone`, then opens (extends the S61
   `try_unblock_locked_*` test shape with the new test accessors).
   *Risk*: this is the scheduler state-machine change — **Principle 6 budget
   pressure.** The barrier must **replace**, not parallel, the per-symbol
   wait/notify path — *one readiness protocol, no second live wait/notify subsystem*
   (Principle 7). **Net LOC is net-additive (~+75), the correct floor (0452 ruling);
   the prior "neutral/subtractive" target is retired** (reconcile point 2).

3. **Single-writer exclusive claim.** Formalise the exclusive pop; remove the
   `eval_owned` early-return in `try_unblock_locked`, replacing it with the uniform
   "owned ⟹ not re-pushed" rule.
   *Unit seam*: two simulated claimers race one module → assert exactly one obtains
   the Phase-A drive; the other (if a pool worker) frees back to the pool and is
   requeued when the barrier opens (it does **not** park). (Direct successor to S61's
   `try_unblock_locked_suppressed_*` tests, re-expressed structurally.)

4. **Worker Phase-A/Phase-B split (requeue gate).** `process_cluster_once`
   (`src/worker.rs::handle_typecheck_work_shared`): gate Pass-2 behind the
   **requeue gate** — `try_unblock_locked` admits the body claim only when the
   closure-barrier predicate holds (every closure module `signatures_ready`), in
   place of the per-dep `blocked_on`. A worker that hits an unregistered closure
   member registers the closure edges via `drive_module_dep`
   (`src/process_form/dependency.rs` — the closure-walk Phase-A driver), **frees its
   thread back to the pool, and requeues** the body work; it **never parks a pool
   thread** on the barrier. Remove the signature-`Gap` path (signature deps resolve
   in Phase A, so a body never returns a signature gap).
   *Unit/integration seam*: a worker driving a 2-module import never parks on a
   signature dependency and never returns a signature `ClusterOnce::Gap`; the body is
   re-claimed from the pool once the barrier opens; retry-from-top survives **only**
   for codegen gaps.
   *Risk*: retry-from-top idempotence must be preserved for the Phase-B path; the
   requeue must re-enter cleanly (no lost-wakeup) when the scheduler sweeps on the
   last `signatures_ready`.

5. **Eval-thread integration + retire `eval_owned` (exclusive-claim retirement).**
   `src/eval.rs::process_single_form` / `register_dep_for_eval`: the eval thread is
   the **one genuine waiter** — it rests the entry module in the terminal
   **`TypecheckDone`** pool state (the **as-built**; B1-equivalent to the
   originally-designed exclusive `TypecheckWorking` claim — neither state sits in a
   typecheck queue, so neither is pool-reclaimable; reconcile point 1) and **never
   releases it to the pool while driving** (it consumes no pool slot, so its wait
   never reduces pool capacity). On a dependency gap it waits on the *dependency's*
   terminal readiness **without** moving the entry to `TypecheckBlocked`, so the
   entry is `claimable XOR owned → owned` and no pool worker can ever re-claim it —
   this closes the **B1 dual-orchestration defect by construction** and is the
   structural replacement for `eval_owned`. Delete the `eval_owned` field and its
   `try_unblock_locked` branch; narrow `wait_module_inmem_complete_blocking` to the
   Phase-B codegen-wait. Land the per-symbol signature-drive retirement + `eval_owned`
   removal together with the requeue-gate in **one change-set** (no half-migrated
   interim — Principle 8); no second live protocol (Principle 7). **The change-set is
   net-additive (~+75), not net-subtractive** (reconcile point 2; the one subtraction
   taken is the live-dead `signatures_ready` family, point 3).
   *Unit seam*: REPL one-form import resolves deterministically; the deterministic
   `/qa` test (§6 tier 1) is green; `repl_persist_race.rs` stress test stays green.
   *Risk*: this is the S78 single-orchestrator decision landing — verify watcher
   reload (`re_register_module`) still funnels the entry module through the uniform
   exclusive claim, not a role-keyed path.

6. **Retire dead scaffolding + reconcile observability.** Delete
   `notify_symbol_typechecked` (signature path), the per-symbol
   `block_for_typecheck` signature branch, and any `eval_in_flight` remnants;
   reconcile/rename trace tags (the barrier transitions want a
   `SignatureBarrier{closure, state}`-style tag for proof-on-fix dumps, replacing
   the per-symbol `IsTypecheckedHit`/`RegisterImportsLookup` race-evidence tags
   where they no longer apply). *(As-built reconcile: the `SignatureBarrierRegister`
   trace tag was removed with the live-dead `register_module_signatures` — Wave-2c,
   point 3 — since there is no register call to tag; the barrier-open transition is
   read off the pool-terminal predicate.)* `src/observability.rs` only — no boundary
   change.
   *Unit seam*: trace-tag format tests; assert no `notify_symbol_typechecked` call
   remains on the import path.

7. **Gate close.** The deterministic repro (§6) is green; the stress repro is green
   20/20 under contention; full suite shows no RED beyond the known intentional
   guards. This is the behavioural gate (Scope 1 "Gate (behavioural)").
   *Seam*: `cargo nextest run` clean; capture a post-fix interleaving/loom artifact
   alongside the test (the structural successor to `tests/sprint61/race-evidence/`).

**Cross-cutting risk (Principle 6):** `src/scheduler.rs` is the most complex `src/`
module; a barrier *adds* states. **The mitigation is NOT net-LOC neutrality — that
projection is retired (0452 ruling; BC §6).** The correct mitigation is the
load-bearing structural invariant: **one readiness protocol — no second live
wait/notify subsystem.** The barrier subsumes the per-symbol wait/notify subsystem
**and** the `eval_owned`/`eval_in_flight` flag family (so no parallel protocol
survives), but it is **net-additive (~+75)** because the requeue kernel is reused
and the Principle-18 single-owner claim costs more than the deleted convention flag.
That additive cost is the accepted price of structural-over-convention enforcement,
already arch-ruled — it is **not** a signal for a fresh arch revisit. (A genuinely
net-subtractive variant would require retiring the per-dep Phase-0 signature drive,
which the submodule super-import ordering blocks — option B of 0452, not taken.)

---

## 8. Scope discipline (arch R2)

**Designed here (the gate):** FIXME 0425 **item 1 only** — the structural
signature/body pre-pass closing the H6/H7 race, + the D0030 deadlock→cycle-error
subsumption (0426; mutual imports = compile-time cycle-error, ratified user ruling
S93).

**Noted, NOT designed here (non-gating, drain-if-time — 0425 items 2–4):**
- `SharedState` per-field ownership sweep (move REPL-only state out of the shared
  plane).
- `cached_modules` dual-store collapse (`SharedState` vs `SchedulerState`).
- priority/nice worker subsystem unification.

These are pure-structure cleanups that may ride the same dependency-service arc
*if* the race fix runs short, but they are **not** on the gate's critical path and
are not specified by this document. The separate `/design` drain items 0430
(docstring-into-source regen) and 0440 (listing-surface classifier unification) are
likewise out of this design pass's scope.

---

## 9. Boundary hygiene + cross-references

- **No `cranelisp-types` change.** `ModuleState` is `src/scheduler.rs`-internal
  (confirmed S61 §3d'' boundary review: `cranelisp-types` has no `ModuleState`
  symbol). The barrier reads pool-terminal `ModulePool` state (`TypecheckDone|
  Complete`), all `src/`-internal (no `signatures_ready` field is added — Wave-2c,
  reconcile point 3). No `Serialize` impact, no ABI impact.
- **No `crates/` change.** The whole fix — including the D0030 mutual-import
  disposition — is `src/`-internal. Mutual imports are a compile-time cycle-error
  (ratified user ruling, S93): the module-atomic barrier converts the deadlock into
  a deterministic `CycleError` with no cross-crate interface change. The "compile
  mutual imports" alternative (a typecheck signature-only Pass-1 entry) is
  **rejected, not deferred** — so no cross-crate typecheck change is admitted (§4).
- **No open cross-boundary question.** FIXME 0448 (which posed the coarse-vs-fine
  question) is **closed** — resolved + deleted by /arch. The authoritative record
  of the ruling lives in BC §6 (the COARSE reading ratified) and the
  `concurrency-dependency-service.mmd` Note (both carry the S93 user ruling).

Cross-refs: `design/arch/bounded-contexts.md` §6 (boundary note);
`design/arch/sequences/concurrency-dependency-service.mmd` (the blessed two-phase
barrier); `design/int/concurrency-architecture.md` §3.5/§3.6 (the convention-spread
protocol this retires); `design/int/heisenbug-race-closure.md` (the tactical
lineage this supersedes); `design/arch/fixmes/0425-*.md`, `0426-*.md` (the gate
FIXMEs); `tests/repl_persist_race.rs`, `tests/plan/ledger.md`:2118 (the stress
repro).
