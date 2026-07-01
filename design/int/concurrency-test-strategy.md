# Concurrency Test Strategy — gaining and maintaining control

**Status**: Wave-3 draft authored from Sprint 62's audit + risk register.
**Inputs**:
- `design/int/concurrency-audit.md`
- `design/int/concurrency-risks.md`
- `design/int/observability.md`
- `design/int/heisenbug-race-closure.md`
- `tests/CLAUDE.md`
- `sprints/SPRINT.md` §Scope item 3 and `/qa` acceptance bullets

## 1. Purpose

This document answers the third Sprint 62 question:

> **How do we gain and maintain control over concurrency issues?**

The answer is not “run the stress test more.”
The answer is a layered strategy:

1. use a **bounded-permutation model checker** where the state can be reduced
   enough to fit,
2. use **structured interleaving tests** in the real workspace where model
   checkers do not fit the concrete types,
3. keep **stress runs** only as weak regression guards,
4. and refresh the audit whenever new shared-state sites appear.

## 2. Architecture-first rule

Before choosing a proof tool, apply this rule:

> **Do not spend verification effort preserving a concurrency shape that should be designed away.**

This strategy therefore has two layers:

1. **containment / compartmentalisation** — reduce and isolate the concurrent
   surface so it is locally understandable,
2. **verification** — apply loom, structured interleaving, unit checks, and
   stress regressions to the reduced surface.

If a risk requires too much harness complexity to test cleanly, that is itself
signal that the design may still be too entangled.

### 2.1 Preferred containment moves

Before or alongside test authoring, prefer these design moves:

- one authoritative dependency-registration / readiness protocol,
- one owner module per mutable shared-state field,
- immutable or narrow work packets between session and workers where feasible,
- elimination of duplicate stores,
- separation of REPL-only state from worker-visible concurrency state.

These are not outside the test strategy — they are what make the tests small,
credible, and maintainable.

## 3. Framework decision

### Chosen framework

**Primary bounded-permutation framework: `loom` v0.7.x**

Why `loom`:
- strongest fit for atomic ordering and mutex/condvar reduced models,
- good ecosystem familiarity,
- appropriate for proving tiny publication / observation invariants,
- and the best match for the actual Tier-1/Tier-2 risks that can be shrunk
  without importing the whole workspace.

This choice does **not** mean loom is used everywhere.
It means:
- when a risk can be reduced to atomics / Mutex / Condvar / Arc,
- loom is the first proof tool to reach for.

Where loom does not fit — especially **DashMap** and real scheduler/session
surfaces — the strategy uses structured interleaving tests instead.

## 4. Framework scoring worksheet

Scale:
- **Yes** = good fit
- **Partial** = possible with significant shim / reduction work
- **No** = poor fit for the real surface
- **Cost** = approximate CI multiplier for a narrow focused test set

| Framework | Handles atomic orderings? | Handles DashMap? | CI cost multiplier | Can a normal skill run it? | Notes |
|---|---|---:|---:|---|---|
| `loom` 0.7.x | Yes | No / requires shim | ~10–30× for the covered micro-tests | Yes (stable, dev-dep) | Best for reduced publish/observe and lock/condvar models |
| `shuttle` | Partial | No / requires shim | ~2–10× | Yes | Useful scheduler exploration tool, but weaker fit for our current reduced atomic invariants than loom |
| `miri` | Partial for concurrency, strong for UB | No practical direct fit for DashMap-heavy integration surfaces | ~10–100× | No (nightly required) | Good secondary tool for unsafe/raw-pointer checks, not primary race-closure tool |
| Structured interleaving only | Partial | Yes | ~1–3× | Yes | Best fit for real code paths, but not exhaustive like a model checker |

### Decision rationale

`loom` is chosen because the highest-value proof targets are the ones where a
small ordering mistake causes a large amount of nondeterministic pain:
- publish-before-register,
- condvar/queue ordering,
- fast-path “is ready, then read” couplings.

Those are exactly the cases loom handles well once reduced.

The main limitation is explicit and accepted:
- **real `DashMap` surfaces will not be proven directly in loom**.

Those get structured interleaving tests in the real workspace.

## 5. Per-risk applicability matrix

### Tier 1 and Tier 2 risks scored against the chosen framework

| Risk ID | Risk | Loom status | Why |
|---|---|---|---|
| CR-1 | observed H6 residue on `handle_import` fast path | **requires-shim** | The real surface uses `DashMap` + scheduler state + session protocol. A reduced loom model is valuable for the publication/observation invariant, but the real path still needs a structured interleaving test. |
| CR-2 | split dependency-registration protocol | **framework-inapplicable** (for the whole real shape) | This is primarily an authority-duplication/design risk. The proof target is behavior parity across two code paths; structured interleaving tests in the real workspace are the right primary tool. |
| CR-3 | mutual-import deadlock | **framework-applicable** | The essence is a small lock/queue/wait graph. A reduced loom model can explore the cycle; a separate integration repro should prove the concrete user-visible hang/error story. |
| CR-4 | `CacheWritePacket` unsafe impl drift | **framework-inapplicable** | This is a type-composition / unsafe-boundary risk. Compile-time assertions, narrow unit tests, and maybe miri later are the right tools. |

## 6. Design-to-test mapping

The intended relationship between design containment and proof mode is:

| Design move | What it buys in testing |
|---|---|
| Single dependency-registration service | One protocol to prove instead of two mirrored paths |
| Owner module per shared field | Smaller unit/structured tests with fewer ambient assumptions |
| Immutable work packets | Less dependence on broad shared mutable maps in test setup |
| Duplicate-store collapse | Removes cross-store consistency tests entirely |
| REPL/worker state separation | Fewer mixed-mode races; clearer reader-class boundaries |

A useful heuristic:
- if a proof target still needs three subsystems and five shared maps just to
  express the invariant,
- the design should probably be reduced before the test is written.

## 7. Candidacy matrix by audit surface

| Audit surface | Candidate proof mode | Practicality | Notes |
|---|---|---|---|
| `worker::handle_import` + `SharedState::symbol_tables` fast path | structured interleaving test in real code + loom reduced model of publish/observe ordering | **requires shim** | Real code uses `DashMap`; reduced model should replace it with `Mutex<HashMap<...>>` or atomic counters to prove the ordering rule, while the real workspace test proves the actual code path |
| `scheduler::take_priority_work` / `notify_typecheck_done` condvar + queue invariants | loom | **admits bounded interleaving** | Good loom candidate: queue state, condvar notification, and readiness transitions can be reduced to small shared state |
| `session_v4::module_sexps` publish-before-register | loom + structured test | **admits bounded interleaving** | Small reduced model is natural; real code path should also get a barrier-driven integration test |
| `cached_modules` dual-store | structured test after `/arch` adjudication | **exceeds useful model-check depth until the ownership question is answered** | First decide whether two stores remain; then write either a single-store test or a cross-store consistency test |
| `Code` / `GotTable` / `Arc<Jit>` temporal lifetime | structured test + runtime assertions | **framework-inapplicable** | Real JIT pages, raw pointers, and Arc lifetimes are not loom territory; use targeted regression tests and explicit invariants |
| `CacheWritePacket` unsafe impl | compile-time trait test + unit test | **framework-inapplicable** | No scheduler interleaving to model; prove composition and single-threaded handoff assumptions directly |

## 8. Structured interleaving pattern

The standard real-workspace pattern is:
- `Barrier` to align actors at the critical point,
- atomic phase markers for post-failure diagnosis,
- no sleeps,
- and no “spin until it probably races” guessing.

### 6.1 Atomic-ordering example

**Target shape**: publish-before-register / observe-after-publish

```rust
use std::sync::{Arc, Barrier};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::thread;

#[test]
fn publish_then_flag_is_observable_to_reader() {
    let gate = Arc::new(Barrier::new(2));
    let published = Arc::new(AtomicBool::new(false));
    let payload_len = Arc::new(AtomicUsize::new(0));

    let g1 = Arc::clone(&gate);
    let p1 = Arc::clone(&published);
    let l1 = Arc::clone(&payload_len);
    let writer = thread::spawn(move || {
        g1.wait();
        l1.store(3, Ordering::Release);
        p1.store(true, Ordering::Release);
    });

    let g2 = Arc::clone(&gate);
    let p2 = Arc::clone(&published);
    let l2 = Arc::clone(&payload_len);
    let reader = thread::spawn(move || {
        g2.wait();
        while !p2.load(Ordering::Acquire) {}
        assert_eq!(l2.load(Ordering::Acquire), 3);
    });

    writer.join().unwrap();
    reader.join().unwrap();
}
```

This is the micro-shape loom should own.
The real `module_sexps` / scheduler path then gets a structured integration
version using the actual session types.

### 6.2 Lock-protected-invariant example

**Target shape**: queue push + condvar wake + atomic claim under one mutex

```rust
use std::collections::VecDeque;
use std::sync::{Arc, Condvar, Mutex};
use std::thread;

#[derive(Default)]
struct State {
    queue: VecDeque<u32>,
    shutdown: bool,
}

#[test]
fn condvar_wake_observes_pushed_work_under_same_lock() {
    let pair = Arc::new((Mutex::new(State::default()), Condvar::new()));

    let producer_pair = Arc::clone(&pair);
    let producer = thread::spawn(move || {
        let (lock, cv) = &*producer_pair;
        let mut state = lock.lock().unwrap();
        state.queue.push_back(7);
        cv.notify_one();
    });

    let consumer_pair = Arc::clone(&pair);
    let consumer = thread::spawn(move || {
        let (lock, cv) = &*consumer_pair;
        let mut state = lock.lock().unwrap();
        while state.queue.is_empty() && !state.shutdown {
            state = cv.wait(state).unwrap();
        }
        assert_eq!(state.queue.pop_front(), Some(7));
    });

    producer.join().unwrap();
    consumer.join().unwrap();
}
```

This is the standard shape for scheduler queue / condvar reduced models.

### 6.3 DashMap example

**Target shape**: avoid `contains_key` + `insert` split; use one atomic entry path

```rust
use dashmap::DashMap;
use std::sync::{Arc, Barrier};
use std::thread;

#[test]
fn dashmap_entry_api_collapses_check_then_insert_race() {
    let map = Arc::new(DashMap::<&'static str, usize>::new());
    let gate = Arc::new(Barrier::new(2));

    let m1 = Arc::clone(&map);
    let g1 = Arc::clone(&gate);
    let t1 = thread::spawn(move || {
        g1.wait();
        m1.entry("helper").or_insert(1);
    });

    let m2 = Arc::clone(&map);
    let g2 = Arc::clone(&gate);
    let t2 = thread::spawn(move || {
        g2.wait();
        m2.entry("helper").or_insert(2);
    });

    t1.join().unwrap();
    t2.join().unwrap();

    assert_eq!(map.len(), 1);
    assert!(map.get("helper").is_some());
}
```

This is not exhaustive like loom, but it is the right real-workspace pattern
for DashMap-backed state.

## 9. Stress-run role

**Normative wording**:

> **Stress runs are retained as weak regression guards; `/sprint` MAY run them; they are NEVER sufficient closure proof per se.**

Statistical note:
- an N-run 0/N gate shows only that the observed failure rate is below roughly
  `1/N` with weak confidence;
- it does **not** prove the absence of the race.

Stress runs remain valuable for:
- catching regressions after a fix,
- validating that a narrowed repro is still gone under load,
- and preserving historical comparability with prior sprint evidence.

They are not the acceptance proof.

## 10. CI cadence

### On push / normal PR
Run only the cheap deterministic pieces:
- structured interleaving tests,
- narrow unit tests,
- existing integration repros,
- no wide stress loops,
- no exhaustive loom sweep.

**Budget**: keep added wall-clock under ~2 minutes for the concurrency subset.

### Nightly / scheduled
Run the heavier proof tools:
- loom test set,
- selected stress runs,
- optional miri jobs for unsafe/raw-pointer surfaces once added.

**Budget**: 10–20 minutes acceptable for the dedicated concurrency job.

### Release / sprint-close confidence run
Run:
- all narrow deterministic concurrency tests,
- the loom suite,
- the known historical stress repros,
- and collect observability dumps if a failure appears.

## 11. Audit refresh cadence

Refresh the audit when any of these happen:

1. a new field of type `Arc<T>`, `Mutex<T>`, `RwLock<T>`, `DashMap<_,_>`,
   `AtomicX`, or `OnceLock<T>` is added in the target surfaces,
2. a new `unsafe impl Send` or `unsafe impl Sync` lands,
3. a new `thread_local!` block stores a raw pointer or `UnsafeCell`,
4. a new worker-reachable process-global `static` appears,
5. or a structural owner of shared state moves between files/modules.

Suggested mechanical checks:

```bash
rg -n '\b(Arc|Mutex|RwLock|DashMap|OnceLock|Atomic[A-Za-z0-9]+)\s*<' src crates/cranelisp-typecheck crates/cranelisp-primitives crates/cranelisp-intrinsics
rg -n 'unsafe impl\s+(Send|Sync)\b' src crates
rg -n 'thread_local!' src crates
```

## 12. Maintenance rule for new shared-state sites

Before a new site lands, its author must supply:

1. classification (`atomic-by-construction` / `under-lock-L` /
   `published-then-read` / `invariant-unclear`),
2. a one-sentence invariant,
3. reader classes affected,
4. whether the site matches a known race pattern,
5. and the expected proof mode (loom, structured interleaving, unit-only, etc.).

If the author cannot state the invariant crisply, the site is treated as a
Tier-3 candidate until clarified.

## 13. Immediate plan for Sprint 63

Recommended first wave:

1. **Containment step A** — refactor dependency registration into one internal
   authority before adding broad new proof harnesses.
2. **CR-1** — after containment step A, add one structured interleaving
   integration test for the real `handle_import` / readiness path and one
   reduced loom model for the publication/observation invariant.
3. **Containment step B** — adjudicate and collapse `cached_modules` dual-store
   if possible before writing cross-store consistency tests.
4. **CR-4** — eliminate or harden `CacheWritePacket`'s unsafe impl with
   compile-time and unit checks.
5. **CR-5 / CR-6** — resolve the unclear and stale-invariant surfaces.

**Key strategy point**: where a small containment refactor can turn an ugly,
fragile concurrency proof into a narrow one, do the refactor first.

## 14. Brief source from the sprint plan

Yes — the sprint plan already contained a strong brief for this document.
The most useful source text was:

- `sprints/SPRINT.md` §Scope item 3
- `/qa` acceptance bullets in `sprints/SPRINT.md`
- `/arch` review notes requiring:
  - one chosen framework,
  - framework scoring,
  - three worked examples,
  - exact stress-run wording,
  - CI cadence,
  - and audit-refresh rules.

In practice, the plan was detailed enough to serve as a near-complete outline.
