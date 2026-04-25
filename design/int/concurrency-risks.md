# Concurrency Risks — v4 scheduler / workers / shared state

**Status**: Wave-2 draft authored from Sprint 62's audit output.
**Inputs**:
- `design/int/concurrency-audit.md`
- `design/int/heisenbug-race-closure.md`
- `design/int/observability.md`
- `sprints/SPRINT.md` §Scope item 2, §Skill Plans `/int` + `/arch`

## 1. Purpose

This document is the ranked backlog derived from the concurrency audit.
Its job is to answer the question the audit does not answer:

> **What should be closed first, and why?**

The register is the handoff from Sprint 62 Wave 1 (inventory) to Wave 3
(test strategy) and to Sprint 63+ implementation work.

## 2. Ranking method

Per `sprints/SPRINT.md` and `/arch` Phase 2 review, ranking is
**lexicographic**, not multiplicative.

### Tier definitions

1. **Tier 1 — Observed**
   - A committed failing test reproduces the issue.
   - These are addressed before all other concurrency risks.
2. **Tier 2 — Suspected by pattern**
   - No committed repro at this exact site yet, but the audit matched a
     known-fires pattern (non-atomic check-then-insert, publish-after-register,
     condvar/queue coupling, unsafe-impl drift on a cross-thread handle).
3. **Tier 3 — Unknown surface**
   - The audit could not state the invariant crisply enough, or the invariant
     is only present in stale / insufficient source prose.

### Blast-radius ordering within a tier

Within each tier, order by blast radius:

1. process-abort / hang / use-after-free class
2. wrong-result
3. spurious-error
4. diagnostic-only

## 3. Risk register

### Tier 1 — Observed

| ID | Tier | Audit stable key(s) | Detection signal | Blast radius | Why this tier | Mitigation / closure target | Owning sprint |
|---|---|---|---|---|---|---|---|
| CR-1 | Tier 1 | `{worker::handle_import::(symbol_tables.contains_key && scheduler.is_typechecked)}` + `{session_v4::SharedState, symbol_tables}` | `tests/sprint23.rs::heisenbug_race_reduced_concurrent_import_pairs` | spurious-error (missing symbol on import fast path), with potential wrong-result if a stale partial table were ever consumed successfully | Committed failing test exists; audit column H also matches the H6 two-map fast-path pattern | Remove the split fast-path as an independent authority OR prove it via a single canonical publish/read protocol; add one narrow structured-interleaving test plus one reduced model-check harness | S63 |

### Tier 2 — Suspected by pattern

| ID | Tier | Audit stable key(s) | Detection signal | Blast radius | Why this tier | Mitigation / closure target | Owning sprint |
|---|---|---|---|---|---|---|---|
| CR-2 | Tier 2 | `{worker::register_dep}` + `{session_v4::SharedState, module_sexps}` + `register_dep_for_eval` protocol described in `src/session_v4.rs` | Audit + source review show the same publish-before-register discipline is implemented in more than one path (worker path and REPL/session recovery path) | spurious-error / wrong-result | This is a known pattern: duplicated concurrency protocol across two authorities drifts even when each local invariant is documented | Introduce one canonical dependency-registration service used by both worker discovery and REPL blocked-dependency recovery; back it with one shared structured test fixture | S63 |
| CR-3 | Tier 2 | `{scheduler::ModuleState::blocked_on}` (cross-ref `design/arch/CLAUDE.md` Decision 30) | Architectural analysis: mutual imports deterministically block both sides in form-by-form scheduling | process-hang / non-termination | Not yet a committed reduced failing test in this register, but it is a known wait-cycle pattern and already recognized as an architectural constraint | Add a narrow integration repro if one is not already committed; then either (a) document as a deliberate Ring-4 constraint with explicit diagnostics, or (b) schedule a module-system redesign sprint | S63+ |
| CR-4 | Tier 2 | `{cranelisp_backend::cache::object::CacheWritePacket}` | Audit §4a.5: `unsafe impl Send` depends on a transitive “contains no raw pointers” claim about `ObjectCompileInput` | process-abort / UB if the claim silently regresses | Matches the “unsafe impl depends on cross-module composition” pattern; there is no committed failing test, but the failure mode would be severe | Replace unsafe impl with derived Send if possible; otherwise add compile-time trait assertions and a local unit test that locks the composition invariant to the current type graph | S63 |

### Tier 3 — Unknown surface

| ID | Tier | Audit stable key(s) | Detection signal | Blast radius | Why this tier | Mitigation / closure target | Owning sprint |
|---|---|---|---|---|---|---|---|
| CR-5 | Tier 3 | `{scheduler::SchedulerState::cached_modules}` + `{session_v4::SharedState::cached_modules}` | Audit §9.1: dual-store finding; invariant not crisp enough to classify as legitimate cross-store coordination or accidental duplication | wrong-result / spurious-error | Auto-mapped from `invariant-unclear`; the system currently has two physical stores for one apparently-related concept | `/arch` adjudicates whether this is one logical set in two homes or two intentionally distinct stores; S63 removes one store or writes an explicit cross-store invariant and tests it | S63 |
| CR-6 | Tier 3 | `{cranelisp_types::got::GotTable}` | Audit §4a.2 + §9.5: source SAFETY prose still describes the pre-Decision-31 process-lifetime retention model | process-abort / use-after-free if future edits follow the stale comment rather than the real invariant | Auto-mapped from `unsafe-impl-prose-invariant`; the issue is not a known live bug today, but the current source comment is not trustworthy enough to audit mechanically | `/arch` ratifies the composite Decision-31 temporal-lifetime invariant; `got.rs` SAFETY comment is rewritten to cross-reference it; add one regression test that exercises redefinition + slot swap against reclaim | S63 |

## 4. Notes on collapsed rows

The audit auto-maps rows, but this register collapses some pairs into one
logical risk when the failure mode is clearly shared.

### 4.1 `cached_modules`

The audit produced two Tier-3 rows:
- scheduler-side `cached_modules`
- session-side `cached_modules`

This register treats them as **one logical risk** because the danger is not
"two independent bugs"; it is one unresolved question about duplicated state.

### 4.2 H6 residue surface

The audit produced:
- one observed Tier-1 row at the worker fast path
- one related symbol-table publication surface row

This register treats them as **one observed risk** because the failing test is
already the evidence that the coupling is not yet proven safe.

## 5. Systemic risk analysis — why the row count understates the danger

The audit rows are useful, but they understate the real risk unless they are
read in architectural context.

The main systemic issue is not merely that a few fields are shared.
It is that the **concurrency protocol is spread across too many authorities**:

- `session_v4.rs` owns part of dependency publication, REPL retry, and object-worker lifecycle
- `worker.rs` owns another part of dependency publication, import handling, and priority-worker behavior
- `scheduler.rs` owns readiness, blocking, and wake-up semantics
- `pipeline.rs` still owns part of eval/runtime transition behavior

That spread has four consequences:

1. **Invariant fragmentation** — a correctness statement often spans multiple files.
2. **Mirrored fixes** — one race fix often requires changing two or three paths.
3. **High test setup cost** — proving one property needs too much scaffolding.
4. **Poor local reasonability** — a reviewer cannot validate the safety of one function by reading one module.

This means some risks are larger than their individual row suggests. In
particular, CR-1 and CR-2 are not independent bugs; together they indicate a
wider architectural problem: the dependency-registration / publication protocol
is not yet sufficiently compartmentalised.

## 6. Design-level containment plan

Before, during, or immediately after S63 race closure work, the integration
layer should move toward a more **compartmentalised concurrent shape**.
These are not cosmetic refactors; they reduce the amount of state that has to
be reasoned about concurrently.

### 6.1 Single concurrency kernel

Create one internal subsystem that owns:
- dependency publication,
- scheduler registration,
- wait/unblock transitions,
- and readiness observation.

No other module should independently implement a publish-before-register or
"is ready, then read the table" protocol.

**Effect on risk**: directly reduces CR-1 and CR-2.

### 6.2 Ownership boundaries for shared state

Adopt an explicit rule:

> Every mutable shared-state field has one owning module; non-owners may call
> owner APIs but may not mutate the field directly.

In practice:
- `scheduler.rs` owns scheduler queues/pools and cached-module scheduler state
- one session-side concurrency service owns dependency publication state
- worker code consumes the service, not the raw fields

**Effect on risk**: turns cross-file temporal invariants into module-local ones.

### 6.3 Immutable work packets between session and workers

Where possible, move from "workers read many live shared maps directly" toward
"workers claim a work item / packet with the exact data needed for the next
step".

This does **not** require actorising the whole compiler. It does mean:
- fewer open-ended reads from `SharedState`
- less dependence on ambient mutable session state
- easier unit and model testing

**Effect on risk**: shrinks the concurrent surface and makes structured tests smaller.

### 6.4 Collapse duplicate stores

Any dual-store finding like `cached_modules` should be treated as a design smell
until proven otherwise. The default remediation should be:
- collapse to one authoritative store,
- or write an explicit cross-store invariant plus tests if two stores remain.

**Effect on risk**: directly addresses CR-5 and prevents similar future Tier-3 rows.

### 6.5 Isolate REPL-only state from worker-visible state

REPL state (`current_module`, `repl_check_state`, slash-command context,
watcher/reload helpers) should be structurally isolated from worker-facing
state so that workers do not need accidental visibility into REPL concerns.

**Effect on risk**: lowers reasoning cost and reduces the chance that REPL fixes
perturb worker behavior.

### 6.6 Prefer “remove concurrency” to “prove more concurrency”

When a surface is difficult to model-check or structure-test because too many
components race at once, the preferred first move is to simplify the design,
not to build a bigger harness.

That principle matters here: some of the current risk is **architectural
concurrency that we do not need to keep**.

## 7. Recommended implementation order

1. **CR-1** — observed heisenbug residue on import fast path
2. **CR-2** — duplicated dependency-registration protocol
3. **Containment step A** — establish a single dependency-registration / readiness authority
4. **CR-4** — unsafe impl drift on cache-writer packet
5. **CR-5** — `cached_modules` dual-store adjudication and cleanup
6. **CR-6** — rewrite stale `GotTable` invariant and add reclaim guard test
7. **CR-3** — mutual-import deadlock (unless a committed repro upgrades it to Tier 1 earlier)

## 8. What “closed” means for this register

A risk is not closed by comment-only acknowledgement. Closure requires:

1. a committed test or explicit rationale for why a test is inapplicable,
2. a current design invariant stated in the owning doc,
3. the implementation changed to match the invariant where necessary,
4. the risk row updated to `closed` or removed with a cross-reference to the
   commit/test that absorbed it.

## 9. Relationship to the test-strategy document

This register intentionally does **not** choose the proof method for each risk.
That is the job of `design/int/concurrency-test-strategy.md`.

This document supplies:
- the ordering,
- the blast radius,
- the target audit keys,
- and the owning sprint.

The test strategy supplies:
- loom / structured-interleaving / miri applicability,
- CI cadence,
- and exact closure evidence expectations.

## 10. Brief source from the sprint plan

Yes — the Sprint 62 plan already provided a strong brief for this
register. The operative requirements came from:

- `sprints/SPRINT.md` §Scope item 2
- `sprints/SPRINT.md` §Architecture Review item 5
- `sprints/SPRINT.md` `/int` skill plan acceptance text

In distilled form, that brief was:

- derive risks **from the audit**, not from memory,
- rank them **Tier 1 / Tier 2 / Tier 3**, not by fake arithmetic,
- order within a tier by blast radius,
- make Tier-3 rows automatic for unclear invariants,
- and produce a register that can drive Sprint 63 implementation work.
