# Concurrency Audit — v4 scheduler, workers, session, runtime trace

**Status**: Wave-1 final (Sprint 62). §1–7, §9, §10 authored by `/int`.
§4a (Wave-1 late extension — Grep-2 + thread_local overlay) also
`/int`-authored. §8 (typecheck crate) `/typecheck`-authored per
SPRINT.md §Skill Plans.

**Wave-1 extension (late)**: §2 Methodology adds Grep 2 (`unsafe impl
Send|Sync`) and Grep 3 (`thread_local!` + raw pointer). A new column
J (type-system status) extends the schema. §4a collects the 19 new
rows (10 `unsafe impl` + 3 thread_local + 6 RefCell completeness
overlay). §9.5 captures the Decision-31 composite temporal-lifetime
invariant for `Code` + `GotTable` + `Arc<Jit>`. §10.2 tallies refreshed
(§6.3 `repl_check_state` priority-worker row cleared per §8.2
refutation; §4a.2 `GotTable` added as new `unsafe-impl-prose-invariant`
Tier-3 candidate).

**Sprint**: 62 — Concurrency Control (pure design sprint).

## §1 Intro

### Purpose

This document is the exhaustive inventory of shared-state access sites
across the four files in Sprint 62's audit surface. It is the
denominator for the Sprint 62 risk register
(`design/int/concurrency-risks.md`, Wave 2) and the test strategy
(`design/int/concurrency-test-strategy.md`, Wave 3). Without this
inventory, any downstream race-closure claim is scoped to what we
happened to notice during debugging — the posture Sprint 61's
methodology pivot retired.

### Non-goals

- No fixes. Every row is observational; no code is edited in S62.
- No ranking. Ranking lives in the risk register (Wave 2) using the
  lexicographic three-tier rubric set by `/arch` Phase 2 §5.
- No test authoring. Test strategy lives in the test-strategy document
  (Wave 3).
- No spec interpretation. Invariants are stated from code; `/spec`
  adjudication (if any) is flagged for the Wave-1 gate, not resolved
  here.

### Relation to Sprint 61 methodology

S61 exited stress-run verification as primary closure proof
(`design/int/heisenbug-race-closure.md §7.10`). The audit is the first
of the three artefacts that replace stress-run verification with
evidence-gated investigation. Every row in this audit with classification
`invariant-unclear` becomes a Tier-3 risk register entry automatically
(§10), ensuring "unknown" becomes tracked rather than invisible.

### Completeness criterion (locked by `/arch` Phase 2 §4)

> 100% of fields typed `Arc<T>`, `Mutex<T>`, `RwLock<T>`, `DashMap<_,_>`,
> `AtomicX`, or `OnceLock<T>` in the target files have an entry. Every
> entry carries one of four labels (`atomic-by-construction`,
> `under-lock-L`, `published-then-read`, `invariant-unclear`). Every
> `invariant-unclear` entry becomes a Risk Register Tier-3 row
> automatically — no ratio budgeting. `Arc<T>` cloned into worker
> threads requires separate entries per reader thread class when the
> invariant differs per reader.

## §2 Methodology

### Denominator grep

This audit uses **two complementary denominator greps**. Rust's
`Send`/`Sync` auto-traits prevent non-thread-safe data from being
shared across threads *by default*; Grep 1 catches types that opt into
the auto-trait machinery correctly and whose thread-safety rests on
declared concurrency primitives. Where authors have `unsafe impl`-ed
the auto-traits directly, they have asserted an invariant the compiler
cannot verify — Grep 2 surfaces these so the audit can capture them
too. A third pattern (raw pointer stashed in a `thread_local!`) is
greppable as a structural tell and is audited alongside Grep 2.

**Grep 1** — declared concurrency primitives (the original denominator,
S62 Wave 1 scope as locked by `/arch` Phase 2 §4):

```
rg -n '\b(Arc|Mutex|RwLock|DashMap|OnceLock|Atomic[A-Za-z0-9]+)\s*<' <files>
```

Augmented by eyeball for `Condvar` (structurally always paired with a
`Mutex`, so it appears in the row for the companion Mutex, but we
enumerate condvars explicitly in §4.3) and for static declarations
(`static X: AtomicU64 = ...`). Every match produces at least one row
unless the match is in `#[cfg(test)]` code, a doctest, or a comment.

**Grep 2** — manual auto-trait overrides (added Wave-1 late, widens
the audit to types where the type system has been sidestepped):

```
rg -n 'unsafe impl\s+(Send|Sync)\b' <workspace>
```

Every match is a type whose thread-safety invariant lives in author
prose, not in the type system. Every match is an audit row; the row's
column G states the invariant the author asserted and column J
(`Type-system status`, added below) records whether the invariant is
stated crisply enough to audit or whether it lives only in informal
comments. Rationale: these types circumvent Grep 1's denominator — a
struct with a `*const T` field and an `unsafe impl Send` does not
match Grep 1's pattern, but is exactly as much a shared-state surface
as anything Grep 1 captures. Without Grep 2, such types would drop
silently out of the audit's denominator.

**Grep 3** (structural overlay, not an independent grep but called out
here) — thread-local-plus-raw-pointer coordination. The greppable
shape is a `thread_local! { ... Cell<*const T> ... }` or
`thread_local! { ... Cell<*mut T> ... }` block. These are coordination
patterns the type system cannot check: the temporal-lifetime invariant
("the `*const T` is valid only while the originating `T` is still
alive on the originating thread") lives in surrounding prose. Also
included here: `thread_local! { ... UnsafeCell<...> ... }` where the
cell holds machine-state data structures (e.g., signal-handler
`sigjmp_buf`). Grep 3 matches are recorded as audit rows with column
J = `thread_local-coordination`. A `RefCell<T>` inside a
`thread_local!` is NOT a Grep-3 match — `RefCell` is auto-safe and
the only observable race-like failure (re-entrant `with()` while the
`RefMut` is live) is a panic, not a data race; those blocks are
audited for completeness under column J = `auto-derived-safe` with a
one-sentence invariant (see §4a.6).

**Reachability-from-worker** (third denominator principle, added
Wave-1c) — shared state reached on a codegen worker's call stack that
is not already covered by Grep-1 or Grep-2 overlays — specifically,
process-global statics (`static X: AtomicU*`, `static Y: OnceLock<_>`,
`static Z: LazyLock<_>`) in crates invoked from priority or nice
worker threads — is in scope via this rule. Rationale: Grep-1 caught
fields on `struct`s; Grep-2 caught `unsafe impl` boundary crossings;
but module-level `static`s in crates other than the original target
surface are a third category the compiler guarantees are `Sync` (by
the `Sync` bound on `static`) but whose *invariants* (what writes
them, who reads them, is the write atomic, does the `OnceLock`
parse-cost fit budget, etc.) the audit must still record. The
sharing pattern is likewise in scope: e.g., `Arc<dyn TargetIsa>`
cloned into every worker's JIT construction is a shared-state surface
even when every access is a deterministic read, because its
lifetime-and-mutation discipline is a backend-crate internal claim
the audit must capture alongside the field sites it enables.

The grep signature is:

```
rg -nE '^\s*static\s+\w+:\s*(Atomic\w+|OnceLock<|LazyLock<)' crates/cranelisp-backend/
```

This is *scoped* to `cranelisp-backend` (and implicitly any crate
reached from a worker) — not a workspace-wide re-audit. The scope
constraint matters: an unscoped Grep-1 on the full workspace would
bring in `cranelisp-types`, `cranelisp-frontend`, etc.; the audit is
deliberate about not going there because those crates are either not
reached by workers (frontend) or are already covered by their data
flowing through `SharedState` (types). Worker-reachable
process-global statics in the `cranelisp-runtime` crate are already
covered by §7 (runtime trace).

### Classification rubric

Four labels. Every field carries exactly one. If a field's invariant
cannot be stated as one crisp sentence (column G), classify as
`invariant-unclear` and leave column G empty — the row is durable
evidence of ignorance and automatically escalates to Tier 3 at §10.

| Label | Definition | Worked example from this audit |
|---|---|---|
| `atomic-by-construction` | All reads and writes are single atomic ops; no compound invariant across multiple ops. Racing observers see a linearly-ordered sequence of individual writes. | `SharedState::next_type_id` (§6) — monotonic `fetch_add`; the "no duplicate TypeId" invariant is a direct consequence of `AtomicU32::fetch_add` and requires no surrounding lock. |
| `under-lock-L` | The field participates in a compound invariant that is preserved only by holding a named lock `L` across a sequence of ops. Readers not holding `L` may observe a torn invariant. | `SchedulerState::modules` (§4.2) under `SchedulerV4::state` — the `modules` HashMap's per-entry `ModuleState::pool`, `waiters`, `jit_reserved` fields must be consistent with the queues (`typecheck_first`, `typecheck_next`, `priority_queue`, `typecheck_done`); only the top-level `state` Mutex preserves this. |
| `published-then-read` | Writer finalises the field once (possibly across multiple ops), then publishes a flag/condvar wake; readers observe only after the publish. Invariant rests on happens-before via the publish primitive, not on continuous lock ownership. | `SharedState::module_sexps` (§6) write+flag pattern: priority worker writes the typechecked sexps then `notify_symbol_typechecked`; readers consume the sexps only after observing the scheduler's typechecked state. |
| `invariant-unclear` | No crisp one-sentence invariant can be stated from the code as it exists. The site is a durable candidate for Tier-3 attention; may be a clean pattern not yet recognised, or a genuine gap. | `SharedState::cached_modules` (§6) relative to `SchedulerState::cached_modules` (§4.2) — the audit cannot state *from code* whether these are two physical stores of one logical set (Principle-7 violation) or two legitimate stores (cache-hint + authoritative). Flagged for `/arch` at Wave-1 gate. |

### Addressing scheme

Every row's column A is `{module-path, field-name}` — the stable
identity that survives line drift and re-ordering. Line numbers are
captured as "verified-at-SHA" annotations in column B. Individual rows
may override the section SHA if the reader needs per-row precision
(e.g., a row split reader-class-wise across two sites).

**Verified-at-SHA (document)**: `f22dd2d` (HEAD on branch `main`,
2026-04-22). Every row in §4–§7 references this SHA in column B
unless specifically overridden.

### Column J — type-system status

Added Wave-1 late alongside Grep 2. Every row carries exactly one of
four labels:

| Label | Definition |
|---|---|
| `auto-derived-safe` | No `unsafe impl Send` / `unsafe impl Sync` appears in the reachability path from the row's declared types. Rust's auto-trait inference applies; the type system is intact. |
| `unsafe-impl-with-invariant` | The row's declared type (or a type in its reachability path) carries an `unsafe impl Send` or `unsafe impl Sync`, AND the invariant underlying that override is stated in column G crisply enough to audit. |
| `unsafe-impl-prose-invariant` | The type carries an `unsafe impl`, AND an invariant exists in source comments, BUT the invariant is not stated crisply enough in column G for the audit to verify mechanically. Flagged for `/arch` adjudication — auto-Tier-3 per §10.1 (new rule). |
| `thread_local-coordination` | The row is a Grep-3 match: a raw pointer or `UnsafeCell`-wrapped machine state stashed in a `thread_local!` block. The temporal-lifetime invariant (valid while originating-frame is live) lives outside the type system by construction. |

**Default for Grep-1 rows**: rows whose declared types are all
auto-derived `Send+Sync` — the Grep-1 denominator as it stood at
Wave-1 first draft — default to column J = `auto-derived-safe` unless
reachability touches an `unsafe impl`, in which case the row's column
J names that impl. Existing rows in §4–§8 that contain `Arc<Jit>`,
`Arc<Linker>`, or `Arc<LoadedPlatform>` aliases reach through types
with `unsafe impl Send+Sync` (`Code`, `GotTable`, `LoadedPlatform`)
and would carry `unsafe-impl-with-invariant` in column J; the audit
does not retroactively annotate these because the invariants live on
the declaring type's row in §4a (new section) and the cross-reference
is structural.

### Schema extension

Rows in §4–§8 use the 9-column schema (A–I). Rows in §4a (new section
below) use the full 10-column schema (A–I + J). Existing §4–§8 rows
that default to column J = `auto-derived-safe` are not retrofitted —
the addition is forward-only. If a future refresh promotes a §4–§8
row to carry a non-default column J (e.g., the `SharedState::kept_dlls`
row because `LoadedPlatform` carries `unsafe impl Send+Sync`), the
row's column J is added at that refresh.

### Reachability-per-reader-class

Four reader classes are distinguished:

- **Scheduler thread** (`S`): the main thread when it drives the
  scheduler directly (e.g., `register_module`, `re_register_module`).
- **Priority worker** (`P`): a persistent priority worker thread
  polling `take_priority_work` (`src/worker.rs::priority_worker_loop_shared`).
- **Nice worker** (`N`): a nice worker thread polling
  `take_object_codegen` (§10 cache-writer path).
- **REPL eval** (`R`): the main thread during `eval` after priority
  workers have spawned — reading SharedState and scheduler state
  cooperatively with priority workers.

Rows are reader-class-expanded (one row per `(field, reader-class)`
pair) only when the invariant differs across readers. Otherwise a
single `S/P/N/R` summary row is used.

### H6 grep signature

The residue pattern from S61 Wave 3's H6 investigation:

```
contains_key(K)  …  insert(K, V)
```

where the `…` is ANY code (locks acquired and released, other
operations, another method entry) and the two calls are not performed
under a single continuous lock hold on the map's owning Mutex. A
publish-after-register variant is also flagged: `map.insert(K, V)`
before a flag is flipped to publish visibility, where the flag is
checked BEFORE a subsequent `map.get(K)` that requires V.

This grep is run against each candidate field-site and the result
recorded in column H (`yes` / `no`) with a short hint when `yes`.

## §3 Target surface

| File | Line count | Verified-at-SHA | Section | Author |
|---|---:|---|---|---|
| `src/scheduler.rs` | 2361 | `f22dd2d` | §4 | `/int` |
| `src/worker.rs` | 5041 | `f22dd2d` | §5 | `/int` |
| `src/session_v4.rs` | 5417 | `f22dd2d` | §6 | `/int` |
| `crates/cranelisp-runtime/src/trace.rs` | 740 | `f22dd2d` | §7 | `/int` |
| `crates/cranelisp-typecheck/src/**` | — | `f22dd2d` | §8 | `/typecheck` |
| `crates/cranelisp-backend/**` (scope-constrained — see below) | — | `f22dd2d` | §4b | `/backend` |

Section boundary for §8: all files under `crates/cranelisp-typecheck/src/`.
No file in that subtree is audited by `/int`; no file outside that
subtree is audited by `/typecheck`.

**Scope constraint for §4b (`cranelisp-backend`)**: *"process-global
statics + any shared state on the codegen-worker call path. Not a full
crate audit."* This is the reachability-from-worker denominator per §2
— it is deliberately narrower than a full owned-surface audit on the
backend crate. Known files derived from the Wave-1c grep evidence:

- `crates/cranelisp-backend/src/jit.rs` — `JIT_FREE_MEMORY_CALL_COUNT`
  static, `build_isa()` + `build_shared_isa()` entry points, `Jit`
  struct internals reachable from workers.
- `crates/cranelisp-backend/src/cache/manifest.rs` — `FINGERPRINT:
  OnceLock<String>`.
- `crates/cranelisp-backend/src/compiler/control_flow.rs` —
  `LENIENT_DISABLED: LazyLock<bool>`.
- `crates/cranelisp-backend/src/display.rs` — 22 borrow sites against
  `&DashMap<ModuleFullPath, SymbolTable>`; likely REPL-eval-only
  reader class (not codegen-worker), to be confirmed or split by
  `/backend` in Step 2.

This file list is the Step 1 scaffolding; `/backend` may extend it
during Step 2 authoring as internal knowledge surfaces additional
worker-reachable sites (per-function caches, intrinsic registries,
multi-sig dispatch tables, per-module codegen state).

The document-wide SHA is `f22dd2d`; any row with a different
"verified-at" is called out in column B.

### §3.1 Grep-2 overlay surface (Wave-1 extension)

The four primary files remain the Grep-1 surface. Grep 2 matches
(`unsafe impl Send|Sync`) span additional files across three crates —
`/int`, `/backend`, `/platform`, and the shared `cranelisp-types`
crate. Rather than extend the primary-surface table to twelve rows
and split §4–§7 into sub-sections per crate, the Wave-1 extension
places all Grep-2 rows in a new §4a "Type-system-override surface".

Rationale for the section-rather-than-per-file layout (**Option β**
as raised in the Wave-1 late-extension brief):

1. Grep 2 is a **second-denominator overlay** — structurally distinct
   from the Grep-1 enumeration — and deserves its own section rather
   than dispersal across per-file sections.
2. The unsafe impls span `/int`-owned, `/backend`-owned, `/platform`-
   owned, and `cranelisp-types`-owned files. A single second-
   denominator section signals honestly that this is a workspace-wide
   pass, not an extension of `/int`'s primary surface.
3. `§10.2` tallies and auto-mapping rules reference §4a uniformly;
   per-file dispersal would require re-stating the new `column J`
   auto-Tier-3 rule multiple times.
4. Future refresh cycles that uncover additional `unsafe impl` sites
   extend §4a in place rather than amending §3's primary-file list.

Grep-2 overlay files audited in §4a:

| File | Owning crate | Site count | §4a sub |
|---|---|---:|---|
| `src/code.rs` | `cranelisp` (/int) | 1 (`Code`) | §4a.1 |
| `crates/cranelisp-types/src/got.rs` | `cranelisp-types` | 1 (`GotTable`) | §4a.2 |
| `crates/cranelisp-types/src/module.rs` | `cranelisp-types` | 1 (`ModuleEntry<C>`) | §4a.3 |
| `src/session_v4.rs` | `cranelisp` (/int) | 4 (2 unsafe impl + 2 thread_local raw-ptr) | §4a.4 |
| `src/platform.rs` | `cranelisp` (/int) | 1 (`LoadedPlatform`) | §4a.5 |
| `crates/cranelisp-platform/src/lib.rs` | `cranelisp-platform` | 1 (`PlatformFn`) | §4a.5 |
| `crates/cranelisp-backend/src/lib.rs` | `cranelisp-backend` | 1 (`CompilationResult`) | §4a.5 |
| `crates/cranelisp-backend/src/cache/object.rs` | `cranelisp-backend` | 1 (`CacheWritePacket`) | §4a.5 |
| `src/expander.rs` | `cranelisp` (/int) | 1 (`JMP_BUF` UnsafeCell thread-local) | §4a.4 |
| RefCell-in-thread_local summary (6 sites) | runtime + /int | 6 | §4a.6 |

Total new audit rows: **13 primary** (10 unsafe-impl + 2 thread_local
raw-pointer + 1 UnsafeCell thread_local) + **6 summary** for the
RefCell-in-thread_local completeness overlay = 19 rows.

## §4 Scheduler — `src/scheduler.rs`

`SchedulerV4` (top-level struct at lines 266–277, as
`pub struct CompileScheduler`) owns one `Mutex<SchedulerState>` plus
three `Condvar`s. `SchedulerState` (lines 213–236) is the mutex-guarded
payload: a `HashMap<ModuleFullPath, ModuleState>`, four `VecDeque`
queues, a `HashSet`, and a boolean shutdown flag.

Schema reminder: A={module-path,field-name} / B=verified-at-SHA /
C=reader-class / D=operation / E=lock-held / F=classification /
G=invariant (one sentence) / H=H6-grep-match / I=current-status.

### §4.1 `CompileScheduler` — top-level fields

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `scheduler::CompileScheduler::state` | `f22dd2d` L267 | S/P/N/R | `lock()` for every access to sub-fields | the mutex itself | `under-lock-L` (L = this mutex) | All reads and writes of `SchedulerState` sub-fields happen under this single Mutex, making the aggregate invariant (queues consistent with `modules[m].pool`, waiter lists consistent with `jit_reserved`) tractable. | no | stable (S57+) |
| `scheduler::CompileScheduler::priority_work_available` | `f22dd2d` L270 | P (wait); S/P/R (notify) | `wait_while` by priority workers; `notify_all` after `state` mutation | paired with `state` | `published-then-read` | Every writer that adds priority work (`register_module`, `notify_typecheck_done`, `notify_symbol_typechecked`, `unblock`) MUST notify before dropping `state` OR immediately after, so at least one parked priority worker observes the new queue state. | no | stable |
| `scheduler::CompileScheduler::object_work_available` | `f22dd2d` L273 | N (wait); S/P (notify) | `wait_while` by nice workers; `notify_all` after `state` mutation | paired with `state` | `published-then-read` | Every writer that transitions a module into `TypecheckDone` MUST notify before dropping `state` OR immediately after, so at least one parked nice worker observes the readiness. | no | stable |
| `scheduler::CompileScheduler::completion` | `f22dd2d` L276 | R/S (wait); S/P/N (notify) | `wait_while` by `wait_module_inmem_complete_blocking` / `wait_inmem_complete`; `notify_all` on inmem/object completion + failure + shutdown | paired with `state` | `published-then-read` | Every terminal transition (`notify_inmem_codegen_complete`, `notify_inmem_codegen_batch_complete`, `notify_module_failed`, `notify_object_codegen_complete`, `shutdown`) MUST notify on this condvar so blocked waiters unblock. | no | stable |

### §4.2 `SchedulerState` — mutex-guarded payload fields

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `scheduler::SchedulerState::modules` | `f22dd2d` L215 | S/P/N/R | `contains_key` / `insert` / `get` / `get_mut` / iter | `state` Mutex | `under-lock-L` | Each `ModuleFullPath` has at most one `ModuleState` entry; `ModuleState::pool` is in sync with the module's presence in exactly one of the four queues at every release of the state lock. | no (all `contains_key`+`insert` pairs in this file are under a single continuous `self.lock()` hold — e.g., L344/L353, L383/L388) | stable |
| `scheduler::SchedulerState::typecheck_first` | `f22dd2d` L218 | S/P | `push_back` / `pop_front` / remove-by-value | `state` Mutex | `under-lock-L` | Membership of `m` in `typecheck_first` implies `modules[m].pool == TypecheckFirst`; popping transitions pool to `TypecheckWorking` under the same lock acquisition. | no | stable |
| `scheduler::SchedulerState::priority_queue` | `f22dd2d` L221 | S/P | `push_back` / `pop_front` / mutate `PriorityStatus` / iter | `state` Mutex | `under-lock-L` | Each `PriorityEntry` transitions `Ready → Working → Waiting → (removed)` monotonically while the module's symbol is in `jit_reserved`; dependency graph edges (`dependencies`, `dependents`) are consistent across entries in the queue. | no | stable |
| `scheduler::SchedulerState::typecheck_next` | `f22dd2d` L224 | S/P | `push_back` / `pop_front` | `state` Mutex | `under-lock-L` | Membership implies `modules[m].pool == TypecheckNext`; transitions to `TypecheckWorking` on claim, atomic with the pop. | no | stable |
| `scheduler::SchedulerState::typecheck_done` | `f22dd2d` L228 | S/P/N | `push_back` / `pop_front` / iter | `state` Mutex | `under-lock-L` | Membership implies `modules[m].pool == TypecheckDone` AND `modules[m].inmem_done==false` OR `modules[m].object_done==false` (else the module is `Complete` and is removed). | no | stable |
| `scheduler::SchedulerState::cached_modules` | `f22dd2d` L233 | S/P/R | `contains` / `insert` / `remove` | `state` Mutex | `invariant-unclear` |  | no (this field, internally; but cross-cutting with `SharedState::cached_modules` — see §9) | flagged for `/arch` Wave-1 gate |
| `scheduler::SchedulerState::shutdown` | `f22dd2d` L235 | S/P/N/R | read in wait predicates; write in `shutdown()` | `state` Mutex | `under-lock-L` | Monotonic false→true; set under lock with all three condvars notified; every wait-predicate observes it under the same lock. | no | stable |

#### `ModuleState` sub-fields (all under `SchedulerState::modules[m]`, therefore under `state` Mutex)

Sub-fields inherit the `under-lock-L` classification of `modules`.
Individual invariants:

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `scheduler::ModuleState::pool` | `f22dd2d` L53 | S/P/N/R | read/write during pool transitions | `state` Mutex | `under-lock-L` | Module is in exactly one queue matching its pool value (or none for `TypecheckWorking`, `TypecheckBlocked`, `Failed`, `Complete`). | no | stable |
| `scheduler::ModuleState::waiters` | `f22dd2d` L57 | S/P | mutate during `register_dep` and satisfy-on-notify | `state` Mutex | `under-lock-L` | `waiters[sym]` contains exactly the modules whose `blocked_on` resolves to `(this_module, sym)` and have not yet been unblocked. | no | stable |
| `scheduler::ModuleState::jit_reserved` | `f22dd2d` L61 | P | insert on claim, remove on complete | `state` Mutex | `under-lock-L` | At most one worker has a given `(module, symbol)` reserved at any time; removal happens only after the codegen result is published (code ptr written). | no | stable |
| `scheduler::ModuleState::inmem_done` | `f22dd2d` L64 | S/P/R | bool write once; read in wait predicates | `state` Mutex | `under-lock-L` | False→true monotonic; set only after every symbol in the module has published a code ptr. | no | stable |
| `scheduler::ModuleState::inmem_claimed` | `f22dd2d` L75 | P | bool set on claim, cleared on notify | `state` Mutex | `under-lock-L` | True implies exactly one priority worker owns the cache-hit inmem load in-flight; cleared before the completion notification. | no (the split that closed the S58 Wave 2c claim-then-do race is documented in the field comment, L72–74) | stable (S58 Wave 2c) |
| `scheduler::ModuleState::object_working` | `f22dd2d` L81 | N | bool set on claim, cleared on notify | `state` Mutex | `under-lock-L` | True implies exactly one nice worker owns object codegen in-flight for this module. | no | stable |
| `scheduler::ModuleState::object_done` | `f22dd2d` L84 | S/N/R | bool write once | `state` Mutex | `under-lock-L` | False→true monotonic; for cache-hit, initialised true; for source compile, set after `.o` file write completes. | no | stable |
| `scheduler::ModuleState::error` | `f22dd2d` L87 | S/P/N/R | Option write on failure | `state` Mutex | `under-lock-L` | Set exactly once across the module's lifetime; after set, module is in `Failed` pool. | no | stable |
| `scheduler::ModuleState::resume_from_form` | `f22dd2d` L91 | P | Option write on block, read on resume | `state` Mutex | `under-lock-L` | Set on `TypecheckBlocked` entry to the form index at which the block occurred; cleared (set None) on full re-entry. | no | stable |
| `scheduler::ModuleState::blocked_on` | `f22dd2d` L96 | S/P/R | Option set on block, cleared on unblock | `state` Mutex | `under-lock-L` | Forward edge used for cycle detection; `Some(dep)` implies module is in `TypecheckBlocked` pool AND `modules[dep].waiters[_]` contains this module. | no | stable |
| `scheduler::ModuleState::eval_in_flight` | `f22dd2d` L111 | R (set/clear); S/P (read) | bool set by REPL-eval before `wait_module_inmem_complete_blocking`, cleared on return | `state` Mutex (linearised — see L107–109 comment) | `under-lock-L` | True implies REPL-eval owns the module's post-unblock retry; priority workers MUST NOT push the module into `typecheck_first` (`try_unblock_locked` checks this under the state lock). | no (S61 Wave 3 step 3e' closed H5 by taking the state lock on both set and read) | stable (S61 Wave 3) |

### §4.3 Condvar-plus-flag pairs — H6-pattern grep outcomes

H6 pattern ("publish-after-register": flag flipped before published
data visible to reader) was grepped against each condvar callsite.

| Site | Notifier | Wait predicate | H6-match? | Notes |
|---|---|---|---|---|
| `register_module` L362 | `priority_work_available.notify_all()` after `modules.insert` + `typecheck_first.push_back`, both under same lock | priority worker waits on `take_priority_work` predicate (pool/queue observation under same lock) | no | Both mutation and wake are synchronised by the single `state` Mutex acquisition. |
| `register_module_cached` L400 | `object_work_available.notify_all()` after `modules.insert` + `typecheck_done.push_back` + `cached_modules.insert` | nice worker predicate | no | Single lock hold for all three inserts. |
| `re_register_module` L467 | `priority_work_available.notify_all()` | priority worker predicate | no | State mutation atomic under lock. |
| `notify_symbol_typechecked` L610 | `priority_work_available.notify_all()` after waiter list mutation | `wait_module_inmem_complete_blocking` predicate | no | Under-lock waiter mutation. |
| `notify_typecheck_done` L720/L754 | `typecheck_done.push_back` then `priority_work_available` + `object_work_available.notify_all` | both worker predicates | no | Single lock hold. |
| `notify_module_failed` L771 | `priority_work_available` + `completion.notify_all` after `error`/`pool=Failed` | all predicates | no | Single lock hold. |
| `notify_priority_codegen_complete` L801 | `priority_work_available.notify_all` after `jit_reserved.remove` + status mutation | priority predicate | no | Under-lock. |
| `notify_inmem_codegen_complete` L823 | `completion.notify_all` after `inmem_done=true` + `inmem_claimed=false` | `wait_*_inmem_complete` predicates | no | Under-lock. |
| `notify_inmem_codegen_batch_complete` L848 | `completion.notify_all` after pool transition | as above | no | Under-lock. |
| `notify_object_codegen_complete` L901/L913 | `completion.notify_all` + `object_work_available.notify_all` after `object_done=true`, `object_working=false` | as above | no | Under-lock. |
| `shutdown` L923-925 | all three condvars | all predicates with `shutdown` check | no | Single write under lock. |

Outcome: **no condvar-plus-flag pair in `scheduler.rs` exhibits the
publish-after-register H6 shape** — every mutation and its corresponding
notify are linearised by the `state` Mutex. H6 residue (where it exists)
is in `handle_import` (§5.5) crossing the `symbol_tables` DashMap
boundary, not in the scheduler's own condvars.

## §4a Type-system-override surface (Grep 2 + thread_local overlay)

This section is the second-denominator pass described in §2 and
scoped in §3.1. Every row covers a site where the type system's
auto-trait machinery has been bypassed (`unsafe impl`) or sidestepped
(raw pointer in `thread_local!`); the invariant that justifies the
bypass lives in author prose, not in the type system.

Schema: A–I per §2 plus column J (type-system status). Every row's
column G states the invariant (paraphrasing or quoting the source
`SAFETY:` comment). Every row's column J = `auto-derived-safe`,
`unsafe-impl-with-invariant`, `unsafe-impl-prose-invariant`, or
`thread_local-coordination`.

### §4a.1 `src/code.rs::Code` — JITModule/Linker wrapper

| A | B | C | D | E | F | G | H | I | J |
|---|---|---|---|---|---|---|---|---|---|
| `code::Code` (enum — `Jit { jit: Arc<Jit>, ptr: *const u8 }` / `Linker { linker: Arc<Linker>, ptr: *const u8 }`) | `f22dd2d` L72–87, unsafe impls L106–107 | S (writer — batch finalise); P/N/R (readers — function dispatch via `ModuleEntry::Def.code`) | clone the `Arc`, read `ptr`; never mutate the contained `Jit`/`Linker` after construction | none — thread-safety rests on `Arc`'s own Send+Sync plus post-finalize immutability of the `Jit`/`Linker` body | `published-then-read` | Source comment L98–105 (quoted): "`Arc<Jit>` / `Arc<Linker>` carriers are themselves `Send + Sync`; the `*const u8` pointer is an integer handle into pages the Arc keeps alive. `Jit` is not auto-`Sync` because of `JITModule`'s interior mutability around its symbol cache, but the post-finalize state we hold here is read-only: `Code` instances only support cloning the `Arc` (thread-safe refcount bumps) and reading `ptr` (no method dispatch on `Jit`)." | no | stable (S58 Wave 3b) — **Wave-1c re-verification**: source comment L98–105 + module-level docs L38–53 are current with Decision 31 / Wave-3b (module docs L33–36 explicitly document `kept_jits` dissolution; SAFETY block at L38–53 references per-redefinition reclaim, not process-lifetime pages). Column G matches source; no rewrite needed. Contrast §4a.2 `GotTable`, whose source comment is stale. | `unsafe-impl-with-invariant` |

Decision 31 linkage: this row carries the JIT-memory lifetime
invariant — no thread may hold a reference into JIT code whose
`Arc<Jit>` has been dropped. See §9.5.

**Wave-1c re-verification outcome** (precedent check against
`GotTable`'s stale-invariant finding at §4a.2): the `Code` source
comment was re-read at SHA `f22dd2d` on 2026-04-22. Both the
inline SAFETY comment (L98–105) and the module-level docs (L38–53
§Safety) explicitly document the Wave-3b/Decision-31 reclaim model
— no `kept_jits` claim, no process-lifetime-pages claim. The
column-G statement matches the current source. **No rewrite
required.** The `GotTable` drift pattern (source comment stale w.r.t.
Decision 31) is confirmed as specific to `crates/cranelisp-types/src/got.rs`
and does not generalize to the adjacent `src/code.rs`; the Code
authors updated the SAFETY text when Wave 3b landed.

### §4a.2 `crates/cranelisp-types/src/got.rs::GotTable` — GOT slots

| A | B | C | D | E | F | G | H | I | J |
|---|---|---|---|---|---|---|---|---|---|
| `cranelisp_types::got::GotTable` (`slots: Box<[AtomicPtr<u8>; GOT_TABLE_SIZE]>`) | `f22dd2d` L26–28, unsafe impls L33–34 | S (writer at registration); P/N (writers on codegen completion — `store_slot` with `Release`); R (readers via JIT code + `load_slot` with `Acquire`) | `store_slot(slot, ptr)` — `AtomicPtr::store(Release)`; `load_slot(slot)` — `AtomicPtr::load(Acquire)`; JIT code reads raw bytes at `got_base + slot*8` | none beyond per-slot `AtomicPtr` release/acquire pairing | `atomic-by-construction` | Source comment L30–32 (quoted): "`GotTable` contains `AtomicPtr` which is inherently `Send+Sync`. The raw pointer values stored point to JIT code pages that remain valid for the process lifetime (Cranelift leaks code memory on drop)." — However, under Decision 31 per-redefinition reclaim, JIT code pages **do not** remain valid for the process lifetime: the prior generation's pages are freed when the last `Arc<Jit>` drops. The comment's quoted invariant is **stale with respect to Decision 31**. The actual Decision-31 invariant is stated at §9.5: GOT-slot atomic swap must be paired with the originating generation's `Arc<Jit>` being kept alive by at least one `ModuleEntry::Def.code` for the duration of any read that observed the slot value. | no | **flagged for /arch** — invariant in source comment predates Decision 31 and should be rewritten | `unsafe-impl-prose-invariant` (source-comment invariant is stale w.r.t. Decision 31; the correct invariant lives in §9.5, not in the `GotTable` impl itself) |

**New finding.** The `GotTable` source comment ("JIT code pages remain
valid for the process lifetime") was accurate under the pre-Decision-31
retention model (`kept_jits` held all JIT batches until session
teardown). Wave-3b dissolved `kept_jits`; the JIT lifetime is now
per-redefinition. `GotTable` itself has not been updated to reflect
this. The actual invariant under Decision 31 is a cross-cutting
statement on the relationship between `GotTable::store_slot` and the
currently-live `Arc<Jit>` — stated in §9.5, not at the `GotTable`
site. `/arch` to adjudicate whether the `GotTable` SAFETY comment is
rewritten or a cross-reference note is added.

### §4a.3 `crates/cranelisp-types/src/module.rs::ModuleEntry<C>` — module entry

Discovered during Grep 2 pass — was NOT on the original 10-site list
supplied by `/sprint`. `rg 'unsafe impl'` found it in active code at
`crates/cranelisp-types/src/module.rs:559-560`.

| A | B | C | D | E | F | G | H | I | J |
|---|---|---|---|---|---|---|---|---|---|
| `cranelisp_types::module::ModuleEntry<C>` (enum — variants include `Def { platform_fn_ptr: Option<*const u8>, code: Option<C>, ... }`) | `f22dd2d` L559–560 (module.rs) | S/P/N/R | DashMap insert/read via `SymbolTable<C,_>::entries`; field reads on `Def` variant | DashMap shard (per-entry) | `published-then-read` (per §6.1 `SharedState::symbol_tables` row) | Source comment L540–558 (paraphrased): the `*const u8` `platform_fn_ptr` is an integer handle into DLL code pages kept alive by the session's `kept_dlls` Vec (see §4a.5 `LoadedPlatform`); threads dereferencing `platform_fn_ptr` must hold a live handle transitively via the session. The `code: Option<C>` field's safety is delegated to the `C: CodeStore` bound, which requires `Send + Sync + 'static`; for `C = Code` (the integration layer's enum per Decision 35) the §4a.1 invariants apply. | no | stable (S58+, Decision 25/32/35) | `unsafe-impl-with-invariant` |

### §4a.4 `src/session_v4.rs` and `src/expander.rs` — thread_local-coordination surface

Four rows:

| A | B | C | D | E | F | G | H | I | J |
|---|---|---|---|---|---|---|---|---|---|
| `session_v4::TestRunnerState` (struct — `tc_modules: *const DashMap<...>`, `current_module: *const ModuleFullPath`); `unsafe impl Send` | `f22dd2d` L4276–L4283 | R (set by REPL-eval before JIT invocation); any thread executing JIT (in practice: REPL eval thread only, since test externs are called from JIT dispatched on the eval thread) | create on stack in REPL-eval scope; `set_test_runner_state(&state)` stashes `*const` into `TEST_RUNNER`; JIT-called externs read via `TEST_RUNNER.with(...)`; cleared on return | none — temporal-lifetime invariant | `published-then-read` (the pointer-stash is the publish; JIT invocation is the synchronous read-window) | The `*const T` fields point into data owned by the REPL-eval stack frame enclosing the JIT invocation. They are valid only between `set_test_runner_state` and `clear_test_runner_state` on the same thread. `Send` is claimed (not `Sync`) because the struct is moved into the thread-local, but only the setting thread ever reads the thread-local. Effectively: "only valid while the enclosing REPL-eval frame is alive on the originating thread." | no | stable (S57 W2 G6) | `unsafe-impl-with-invariant` (invariant is clearly stated by the set/clear pair + thread-local storage pattern) |
| `session_v4::TEST_RUNNER: thread_local! { Cell<*const TestRunnerState> }` | `f22dd2d` L4285–L4288 | R (set on REPL-eval); JIT extern readers on the same thread | `Cell::set` on enter; `Cell::get` in `discover_tests_extern`, `run_test_extern`; `Cell::set(null)` on exit | none — Cell is `!Sync` by construction, thread-local is per-thread | `published-then-read` | The pointer is readable only while the originating `TestRunnerState` is still alive on the originating thread: `set_test_runner_state` runs in the REPL-eval frame, JIT calls are synchronous within that frame, `clear_test_runner_state` runs before the frame drops. No worker thread accesses `TEST_RUNNER`. | no (no cross-thread path; re-entrant set/clear would be a misuse but not a race) | stable (S57 W2 G6) | `thread_local-coordination` |
| `session_v4::TraceDisplayState` (struct — `symbol_tables: *const DashMap<...>`); `unsafe impl Send` | `f22dd2d` L4427–L4432 | R (set by REPL-eval before trace format); JIT extern reader on the same thread | `set_trace_display_state(&state)`; JIT-called `repl_trace_format` reads via `TRACE_DISPLAY.with`; cleared on return | none — temporal-lifetime invariant | `published-then-read` | Same shape as `TestRunnerState`: the `*const` field points into data owned by the REPL-eval frame enclosing the JIT invocation. Valid only between `set_trace_display_state` and `clear_trace_display_state` on the same thread. `Send` only (not `Sync`) because one thread sets, one thread (same thread in practice) reads via the thread-local. | no | stable (repl/spec.md §4.12 trace display) | `unsafe-impl-with-invariant` |
| `session_v4::TRACE_DISPLAY: thread_local! { Cell<*const TraceDisplayState> }` | `f22dd2d` L4434–L4437 | R (set on REPL-eval); JIT extern readers on the same thread | as above | none | `published-then-read` | The pointer is readable only while the originating `TraceDisplayState` is still alive on the originating thread; same lifetime pattern as `TEST_RUNNER`. | no | stable | `thread_local-coordination` |
| `expander::JMP_BUF: thread_local! { UnsafeCell<SigJmpBuf> }` (signal-handler longjmp buffer) | `f22dd2d` L265–268 (src/expander.rs) | S/P/R (any thread executing macros via `invoke_jit_protected`); signal handler on the same thread | `sigsetjmp(JMP_BUF.get())` on entry; `siglongjmp(JMP_BUF.get())` from `signal_handler_longjmp` on SIGFPE/SIGILL/SIGBUS | none — `UnsafeCell` provides interior mutability, thread-local ensures per-thread isolation | `published-then-read` | Source comment L261–264 (quoted): "Thread-local jump buffer for signal recovery during JIT macro execution. Only accessed by the signal handler and `invoke_jit_protected` on the same thread. Signal delivery for SIGFPE/SIGILL/SIGBUS is synchronous (delivered to the thread that caused the trap)." — invariant is that the buffer is only meaningful between `sigsetjmp` and either its zero-return or the signal-handler's `siglongjmp`; no cross-thread access. `UnsafeCell` is used instead of `Cell` because the buffer is a fixed-size POSIX struct accessed by raw FFI. | no | stable (macro signal recovery — S32-ish) | `thread_local-coordination` |

### §4a.5 Cross-crate unsafe impls — retention-root-Arc'd data

Four rows in three crates, sharing a common pattern: the underlying
data is code pages or DLL handles kept alive by a process- or
session-lifetime retention root, and the raw pointer in the struct is
an integer handle into those pages.

| A | B | C | D | E | F | G | H | I | J |
|---|---|---|---|---|---|---|---|---|---|
| `platform::LoadedPlatform` (struct — holds `libloading::Library`, manifest Strings, `Vec<OwnedPlatformFnDescriptor>`); `unsafe impl Send`/`Sync` | `f22dd2d` L21–40 (src/platform.rs) | S (writer — platform load); P/N/R (readers — function dispatch via registered platform fn pointers) | construct once; pushed into `SharedState::kept_dlls: Mutex<Vec<LoadedPlatform>>`; retained for session lifetime; `_library` field is never read after construction (drop fires DLL unload at session end) | `kept_dlls` Mutex on write; no lock on read-via-fn-pointer (the retention is the invariant) | `published-then-read` | Source comment L32–38 (quoted): "`LoadedPlatform` holds a `Library` handle whose code segment is mapped for the process lifetime (DLLs are never unloaded). Function pointers into the code segment are valid from any thread. The `_library` field is never read after construction — only its drop side effect (unloading the DLL) is load-bearing. `OwnedPlatformFnDescriptor` fields are `String`/`usize`/`*const` and are read-only after manifest parsing. Send+Sync are needed for retention in `SharedState::kept_dlls`." | no | stable (S57 W3 G8) | `unsafe-impl-with-invariant` |
| `cranelisp_platform::PlatformFn` (`#[repr(C)]` struct — `name: *const u8`, `jit_name: *const u8`, `ptr: *const u8`, param-name ptr arrays); `unsafe impl Send`/`Sync` | `f22dd2d` L60–91 (crates/cranelisp-platform/src/lib.rs) | S (writer — manifest parse at DLL load); S/P/N/R (readers — name/ptr lookup during platform fn registration and dispatch) | `#[repr(C)]` struct returned from DLL's `cranelisp_platform_manifest` entry point; read by `LoadedPlatform` constructor to populate `OwnedPlatformFnDescriptor`; no mutation after DLL load | none — pointers are read-only after construction | `published-then-read` | Source comment L87–89 (quoted): "`PlatformFn` is a C-ABI struct with raw pointers; it is only constructed and accessed within unsafe blocks during DLL loading. The pointers must remain valid for the lifetime of the manifest." The `LoadedPlatform` retains the DLL, and the DLL's `.rodata` / `.data` sections (which own the pointed-to name strings) stay mapped for the process lifetime; so "valid for the lifetime of the manifest" reduces to "valid for the process lifetime" in practice. | no | stable | `unsafe-impl-with-invariant` |
| `cranelisp_backend::CompilationResult` (struct — `code_ptrs: HashMap<Symbol, *const u8>` plus non-raw fields); `unsafe impl Send`/`Sync` | `f22dd2d` L120–156 (crates/cranelisp-backend/src/lib.rs) | Backend compile-to-module caller thread (writer); integration layer (reader — constructs `Code::Jit { jit, ptr }` per symbol) | returned from `compile_to_module` across worker boundaries; consumed immediately by `/int` to build `Code::Jit` entries, after which the raw pointers are held only inside `Code` | none — the struct is a one-shot return handoff | `published-then-read` | Source comment L147–154 (quoted): "`code_ptrs` is `HashMap<Symbol, *const u8>`. The raw pointer is an integer handle into JIT-emitted pages owned by the caller's `Arc<Jit>` (Decision 35); transmitting the integer across threads is safe. The caller (integration layer) constructs `Code::Jit { jit, ptr }` where `Arc<Jit>` is the lifetime root for `ptr`. This `unsafe impl` exists so `CompilationResult` can be returned across worker boundaries." | no | stable (S58 W3b Decision 35) | `unsafe-impl-with-invariant` |
| `cranelisp_backend::cache::object::CacheWritePacket` (struct — `PathBuf`, `ModuleFullPath`, `Vec<u8>`, `ObjectCompileInput` plus other serde-safe fields); `unsafe impl Send` (Send only) | `f22dd2d` L103–128 (crates/cranelisp-backend/src/cache/object.rs) | P (writer — nice worker sends to background cache-writer); cache-writer thread (reader) | constructed on the sending thread with all data owned (`Vec<u8>`, `PathBuf`, `HashMap<String, String>`); sent across channel to cache-writer; consumed once | channel send/recv provides the happens-before | `published-then-read` | Source comment L126–127 (quoted): "`CacheWritePacket` must be Send for background thread use. `ObjectCompileInput` contains no raw pointers." — the `unsafe impl Send` exists because `ObjectCompileInput` (imported from elsewhere in backend) contains Cranelift IR types not all of which auto-derive Send; the author has verified none hold raw pointers or non-Send state. | no | stable (background cache writer) | `unsafe-impl-with-invariant` (invariant: `ObjectCompileInput` is no-raw-pointers; this is a cross-module claim — if `ObjectCompileInput`'s definition ever adds a `*const T` field the claim breaks silently) |

Sub-finding: `CacheWritePacket`'s invariant depends on the internal
composition of `ObjectCompileInput`. If `/backend` adds a raw-pointer
field there without updating this impl, the Send claim becomes
unsound silently. Flag for `/backend` review: recommend replacing the
`unsafe impl Send` with a derived `Send` by removing unsafe impls
from the composed types (if possible), or adding an assertion.

### §4a.6 RefCell-in-thread_local — completeness overlay

Six thread_local blocks contain `RefCell<T>` (or `Cell<Option<u64>>`)
rather than raw pointers. These are not Grep-3 matches — `RefCell` is
auto-safe, and thread_local ensures per-thread isolation of the cell
itself. The only observable failure mode is re-entrant `with()` while
a `RefMut` is live, which is a `borrow_mut` panic (not a data race,
not UB). Summary row per site for audit completeness:

| Site | Type | Invariant (column G) | Column J |
|---|---|---|---|
| `crates/cranelisp-runtime/src/panic.rs::RUNTIME_ERROR` (L11–13) | `thread_local! { RefCell<Option<String>> }` | Set by `runtime_panic` extern called from JIT; read+taken by host via `take_runtime_error` after JIT returns. No re-entrant `with()` pattern — panic handler and host-reader are disjoint call sites. | `auto-derived-safe` |
| `crates/cranelisp-runtime/src/io_trace.rs::IO_TRACE_BUF` (L242–244) | `thread_local! { RefCell<VecDeque<IoTraceEvent>> }` | Hot-path `record_event` borrows mutably for push; `dump_thread_buffer` borrows mutably for drain. Both are disjoint call sites per the code's discipline. Re-entrant `with()` is a `borrow_mut` panic; not audited in S62 (not a race). | `auto-derived-safe` |
| `crates/cranelisp-runtime/src/io_trace.rs::IO_TRACE_THREAD_ORD` (L249) | `thread_local! { RefCell<Option<u64>> }` | First-write assigns via `fetch_add` on the static counter; subsequent reads return the cached value. No re-entrant `with()` path. | `auto-derived-safe` |
| `src/observability.rs::SCHEDULER_TRACE_BUF` (L293–294) | `thread_local! { RefCell<VecDeque<SchedulerTraceEvent>> }` | Same shape as `IO_TRACE_BUF`, per-thread scheduler trace buffer. | `auto-derived-safe` |
| `src/observability.rs::SCHEDULER_TRACE_THREAD_ORD` (L296) | `thread_local! { RefCell<Option<u64>> }` | Same shape as `IO_TRACE_THREAD_ORD`. | `auto-derived-safe` |
| `crates/cranelisp-runtime/src/trace.rs::THIS_THREAD_ID` (L63–68) | `thread_local! { u64 }` (value, not RefCell) | Assigned once via `THREAD_ID_COUNTER.fetch_add`; read-only thereafter. | `auto-derived-safe` |

Joint note: re-entrant `with()` is a panic (not a race); audit for
re-entrant `with()` patterns is **out of scope for S62 concurrency
audit** but recorded here for completeness. If a future review
surfaces a re-entrant `with()` in any of the above, it produces a
local `borrow_mut` panic on that thread — no cross-thread visibility
hazard.

## §4b Backend — codegen-worker reachability (Wave-1c extension)

This section is the reachability-from-worker pass described in §2
(third denominator principle) and scoped in §3. Every row covers
shared state reached by codegen workers in the `cranelisp-backend`
crate: process-global statics, shared ISA clones, and internal
backend-owned state on the codegen-worker call path. Scope is
reachability-from-worker — *not* a full owned-surface audit of the
backend crate.

Schema: the full 10-column schema (A–I per §2 + column J per §2's
"Column J — type-system status"). Most rows here are expected to
carry column J = `auto-derived-safe` (the type system is intact —
`Sync` is guaranteed by the `static` bound or by `AtomicU*`/`OnceLock`
auto-Sync), with the invariant interest living in column G (write
discipline, publish-then-read shape, cost-budget claims).

**Authoring responsibility**: this section is a **Step-1 stub**.
`/int` scaffolds the section headings and the file list in §3; the
rows are authored by `/backend` in Step 2 based on both the grep
evidence enumerated below and internal knowledge of backend-only
state not visible from `/int`'s vantage (per-function caches,
intrinsic registries, multi-sig dispatch tables, per-module codegen
state).

**Handoff note to `/backend`**: verify the `Jit` column-G invariant
against the `GotTable` stale-invariant precedent surfaced in Wave-1b
(see §4a.2 and §9.5). `Jit` and `Code` are adjacent code with the
same authors, and both participate in Decision 31's `kept_jits`
dissolution. If `Jit`'s in-crate SAFETY comments reference a
retention model pre-dating Decision 31/Wave 3b (`kept_jits` alive,
process-lifetime pages, etc.), the invariant must be rewritten to
reference the per-redefinition reclaim model and cross-reference
§9.5 — following the same pattern `/int` surfaced for `GotTable`.

### §4b.1 Process-global statics

Three process-global `static`s in `cranelisp-backend` are reached from
codegen-worker call stacks. Each carries a `Sync`-by-construction
wrapper (`AtomicU64`, `OnceLock`, `LazyLock`); the audit interest lives
in column G (write/read discipline, cost-budget claim, interaction with
Decision 31). A re-run of the scoped grep at SHA `f22dd2d` confirmed
the set is complete — the only other `static` match
(`src/jit.rs:992 SLAB`) is inside a `#[test]` body (not production code)
and is out of scope.

| A | B | C | D | E | F | G | H | I | J |
|---|---|---|---|---|---|---|---|---|---|
| `cranelisp_backend::jit::JIT_FREE_MEMORY_CALL_COUNT` (`AtomicU64`) | `f22dd2d` L181–182; writer L244–245; read accessor `jit_free_memory_call_count()` L188–190 | S/P/N/R (writer: every thread whose `Arc<Jit>` drop releases the last clone — all four classes trigger this); R (reader: integration-layer reclaim test in `src/code.rs::tests`) | single `fetch_add(1, Relaxed)` per `Jit::drop` that successfully calls `unsafe JITModule::free_memory()`; single `load(Relaxed)` in test accessor | none beyond `AtomicU64` itself | `atomic-by-construction` | Monotonic `fetch_add` counter used solely to assert that the `free_memory` path fires in Decision-31 reclaim tests — no production code reads the value; `Relaxed` ordering is correct because the counter is only read after the test has `drop`-ped the `Arc<Jit>` chain, and the final `fetch_add` happens-before the `load` via the `Arc` drop's implicit release. | no | stable (S58 W3b Decision 31 — introduced specifically as test evidence for the reclaim path) | `auto-derived-safe` |
| `cranelisp_backend::cache::manifest::FINGERPRINT` (function-local `static FINGERPRINT: OnceLock<String>` inside `binary_fingerprint()`) | `f22dd2d` cache/manifest.rs L208; `get_or_init` body L210–227 | S/P/N (writer on first call; readers on subsequent calls — every cache read/write path consults `binary_fingerprint()` during manifest validation) | `OnceLock::get_or_init(\|\|{...})` on first call derives an `mtime-{secs}.{nanos}` string from `std::env::current_exe()` + `fs::metadata(exe).modified()`; subsequent calls take the fast-path `Some(&String)` branch and `.clone()` it | `OnceLock`'s internal sync — exactly-one initializer runs; other threads block on first access only | `published-then-read` | The fingerprint is `current_exe()` mtime as a formatted string; write-once by `OnceLock`'s internalised `Once` semantics; readers observe either the fully-initialised `String` or wait on the internal `Once`. Initialisation cost is two syscalls (`current_exe()`, `metadata.modified()`) — paid exactly once per process; subsequent reads are a map + clone. | no | stable (fingerprint stable across process lifetime by construction — the exe file's mtime cannot change underneath a running process without invalidating the binary) | `auto-derived-safe` |
| `cranelisp_backend::compiler::control_flow::LENIENT_DISABLED` (`LazyLock<bool>`) | `f22dd2d` compiler/control_flow.rs L1878–1881 | S/P/N (writer on first read; readers per-invocation of sparkability analysis — every `let`-block codegen path consults `LENIENT_DISABLED`) | `LazyLock::new(\|\| env::var("CRANELISP_NO_LENIENT").is_ok_and(\|v\| v == "1"))`; readers dereference `*LENIENT_DISABLED` → `bool` | `LazyLock`'s internal `Once` — exactly-one env-read | `published-then-read` | Env-var-derived compile-time decision gate (disable lenient eval / sparkable bindings when `CRANELISP_NO_LENIENT=1`); env var value is stable across a process's lifetime by convention; one `env::var` syscall per process, cached `bool` thereafter. No interaction with Decision 31 (decision is codegen-time, not reclaim-time). | no | stable (S60 lenient-eval observability gate) | `auto-derived-safe` |

### §4b.2 `Arc<dyn TargetIsa>` sharing pattern

The ISA is constructed once per session via `build_shared_isa()` and
cloned into each worker's `Jit` via `new_with_isa(isa, extra_symbols)`
(jit.rs:289–302). A second, parallel constructor
`cache::object::build_isa(is_pic: bool)` exists for ObjectModule
compilation (cache/object.rs:135) and is invoked per-cache-packet on
the cache-writer thread; this is a fresh ISA per call, not a shared
one, so it carries a distinct invariant shape and gets its own row.

| A | B | C | D | E | F | G | H | I | J |
|---|---|---|---|---|---|---|---|---|---|
| `cranelisp_backend::jit::{build_isa, build_shared_isa, Jit::new_with_isa}` (`Arc<dyn TargetIsa>`) | `f22dd2d` jit.rs L36–63 (`build_isa`), L283–291 (`build_shared_isa`, doc L283–288 explains the sharing intent), L298–303 (`new_with_isa`) | S (writer — session-start construction); P/N (readers via per-worker `Jit` that holds an `Arc` clone) | `build_shared_isa()` constructs one `Arc<dyn TargetIsa>`; integration layer clones it per worker; each worker's `Jit::from_isa` passes the clone to `JITBuilder::with_isa`; `Arc` drops when the last `Jit` drops | none — the `Arc` itself is the sync primitive; `TargetIsa: Send + Sync` is auto-derived from Cranelift | `published-then-read` | The ISA is constructed once before workers spawn and never mutated afterwards; all workers observe an immutable shared view. `TargetIsa: Send + Sync` is a trait-bound guarantee from Cranelift; the `Arc` provides thread-safe refcount bumps. No `unsafe impl` in the backend — the type system is intact. Lifetime discipline: each `Jit`'s `Arc` clone is dropped when that `Jit` drops (Decision 31 reclaim path); the shared ISA is released when the last `Jit` drops, or earlier if the integration layer releases its own clone. | no | stable (session-start ISA sharing is the established pattern; Cranelift's `TargetIsa: Send + Sync` is load-bearing) | `auto-derived-safe` |
| `cranelisp_backend::cache::object::build_isa(is_pic: bool)` (fresh `Arc<dyn TargetIsa>` per call, `is_pic=true`) | `f22dd2d` cache/object.rs L135–166 | N (cache-writer thread — called from `process_cache_packet` per packet) | fresh `Arc<dyn TargetIsa>` constructed per call; scoped to one `ObjectModule` compilation; dropped when the packet's compilation completes | none — per-call fresh `Arc`, no cross-call sharing | `atomic-by-construction` (trivially: the `Arc` is not shared at all) | A distinct ISA is built per `.o` compilation with `is_pic=true` (relocatable code), separate from the JIT's `is_pic=false` shared ISA. Each call lives only for the duration of one `ObjectModule` compilation on the cache-writer thread; nothing cross-thread-shared. Note: the two `build_isa` functions (jit.rs and cache/object.rs) are near-duplicates differing only in the `is_pic` flag — a future refactor could unify them, but the split is not a correctness concern for S62. | no | stable (S58 cache-writer path) | `auto-derived-safe` |

Note on `Jit` itself: per §4a.1 and the Step-1 scaffold, `Jit` does not
carry its own `unsafe impl Send/Sync` — cross-thread safety is
delegated structurally through `Arc<Jit>` inside `Code::Jit`. The
Wave-1c re-verification of `Jit`'s SAFETY comments is recorded in
§4b.5 below (no drift; `kept_jits` is explicitly documented as
dissolved).

### §4b.3 `display.rs` reader class

The 22 `&DashMap<ModuleFullPath, SymbolTable>` borrows in `display.rs`
are confirmed REPL-eval-only. Evidence: grep for `format_value`,
`format_result_value`, `format_type_qualified`, `format_scheme_display`,
`format_ctor_display`, and `format_adt_type_qualified` across
`crates/cranelisp-backend/src/`, `src/worker.rs`, and `src/scheduler.rs`
returns zero call sites in `worker.rs`/`scheduler.rs`. The only
non-`display.rs` callers are: (a) `src/session_v4.rs` (REPL-eval paths
for `/list`, `/info`, `/sig`, result display); (b)
`compiler/trace_codegen.rs` which emits a call to
`cranelisp_trace_format` — the runtime-crate extern
`repl_trace_format` that reads the `TRACE_DISPLAY` thread-local set on
the REPL eval thread (see §4a.4 `TraceDisplayState`). JIT-executed
trace code runs synchronously on the eval thread during REPL
evaluation, not on codegen workers. Single row suffices.

| A | B | C | D | E | F | G | H | I | J |
|---|---|---|---|---|---|---|---|---|---|
| `cranelisp_backend::display::*` (22 borrow sites against `&DashMap<ModuleFullPath, SymbolTable<C, L>>`) | `f22dd2d` display.rs — entry points `format_value` L36, `format_result_value` L52, `format_type_qualified` L101, `format_scheme_display` L117, `format_ctor_display` L315, helpers `lookup_type_def_from_tables` L328, `format_adt_value` L351, `format_adt_type_qualified` L391 | R (REPL-eval thread only; trace format path runs synchronously on the eval thread via the `TRACE_DISPLAY` thread-local — see §4a.4) | read-only `DashMap::get` on `symbol_tables`; the `SymbolTable` entries read (`TypeDef`, `Constructor`, `Def`) are `published-then-read` per §6.1 | none in this site — the underlying `symbol_tables` invariant is §6.1's | `published-then-read` | Display functions are pure readers of `symbol_tables`: no writes, no mutation. The `DashMap` invariant (entries inserted before their public-typechecked publish, §6.1) is the load-bearing property; display just observes already-published state. No codegen-worker reachability — confirmed by call-site grep. Cross-reference: §6.1 `SharedState.symbol_tables` for the write-side invariant. | no | stable (REPL display is a post-codegen pure reader) | `auto-derived-safe` |

### §4b.4 Internal backend state

`/backend` internal audit. The audit looked for: (a) shared caches
on `FnCompiler` or `CompileContext`; (b) intrinsic registries;
(c) multi-sig dispatch tables; (d) per-module codegen carry-over
state; (e) cache-directory coordination state; (f) `CompilationResult`
invariant drift; (g) vec_elem_inc / drop-glue caches. Each finding
— including "looked and found nothing" — is recorded below.

**Finding §4b.4-a: `FnCompiler<M, C, L>` is per-function; no shared
state.** Every field of `FnCompiler` (compiler/mod.rs L446–533) is
per-invocation: `FunctionBuilder<'a>`, `&mut M`, `HashMap`s for
`variables`/`variable_types`/`last_uses`/`closure_drop_glue`,
per-function TCO state (`current_fn_name`, `tail_loop_block`,
`in_tail_position`), and a `CompileContext` (which holds only `&`
references to outer data). There is no `Mutex`, `Arc<Mutex<...>>`,
`DashMap`, `OnceLock`, or any Cell-of-shared field. No row needed —
the struct's shape is inherently thread-safe because each codegen
worker constructs its own `FnCompiler` per function it compiles.

**Finding §4b.4-b: `CompileContext` `&`-references.** `CompileContext`
(compiler/mod.rs L258–296) carries `&HashMap<Symbol, FuncId>` for
`func_ids`/`func_arities` (per-module, constructed afresh per
`compile_to_module` invocation, lib.rs L509), `&DashMap<ModuleFullPath,
SymbolTable<C, L>>` for `symbol_tables`, `ModuleFullPath` for
`current_module`, and `Option<&[TracedFnInfo]>` for `traced_fns`. The
`symbol_tables` reference is the only cross-worker shared surface and
it is covered by §6.1 — `CompileContext` introduces no new invariant
there. Writes to `symbol_tables` from inside the backend crate are
test-only (jit.rs L940, L1137 — both inside `#[test]` fn bodies), so
production codegen-worker paths treat the map as read-only during the
compile pass.

**Finding §4b.4-c: Intrinsic registries are constructed afresh per
call; no shared registry.** `intrinsic_symbols()` (jit.rs L90–161)
returns a fresh `Vec<IntrinsicSymbol>` on each call — there is no
cached `static` `IntrinsicTable`. Each `Jit::from_isa` invocation
calls `register_intrinsics(&mut builder)` which loops over
`intrinsic_symbols()` and registers the symbols on the per-`Jit`
`JITBuilder` (jit.rs L166–170, L310–311). No cross-worker shared
registry exists; each worker's `Jit` owns its own symbol-to-ptr
mapping via the `JITBuilder`-derived `JITModule`. No row needed.

**Finding §4b.4-d: vec_elem_inc / drop-glue `FuncId`s live on the
`Jit`, not on a shared cache.** `resolve_elem_inc_fn_ptr`
(compiler/vec_codegen.rs L538–557) and `build_elem_inc_fn` (L637)
declare runtime-named `FuncId`s via `self.module.declare_function(...)`
— the `FuncId`s are owned by the current `Jit`'s `JITModule`.
`closure_drop_glue` and `drop_glue_depth` live on `FnCompiler`
(compiler/mod.rs L517, L522) and are per-function. There is no shared
`vec_elem_inc_cache` across workers; the project-memory entry naming
one refers to the sketch (pre-Wave-3b), not the current backend. No
row needed.

**Finding §4b.4-e: Cache-directory coordination — `CacheManifest` is
serde-only, with the serialise/deserialise happening through
`read_manifest` / atomic file-write paths.** `cache/manifest.rs`
`CacheManifest` (L25) is a plain struct; concurrency control is
externalised (the cache-writer thread is the single writer —
§4a.5 `CacheWritePacket` invariant). No in-memory shared `CacheManifest`
state exists across codegen workers; each read goes through a fresh
`read_manifest(cache_dir)` call that deserialises from disk.
`process_cache_packet` (cache/object.rs L224–227) takes a
`&DashMap<ModuleFullPath, SymbolTable>` parameter — this is the
same `symbol_tables` borrowed from the integration layer (or empty
in tests), not a backend-owned surface; §6.1 covers the invariant.
No new row needed.

**Finding §4b.4-f: `CompilationResult` (§4a.5 row) invariant is
current — no drift.** Re-read at SHA `f22dd2d` (lib.rs L120–156,
SAFETY comment L147–154). The invariant text — "`code_ptrs` is
`HashMap<Symbol, *const u8>`; the raw pointer is an integer handle
into JIT-emitted pages owned by the caller's `Arc<Jit>`
(Decision 35); the caller (integration layer) constructs
`Code::Jit { jit, ptr }` where `Arc<Jit>` is the lifetime root for
`ptr`" — correctly reflects the Wave-3b / Decision-35 retention
model. No `kept_jits` claim, no process-lifetime-pages claim. The
§4a.5 row's column I (`stable (S58 W3b Decision 35)`) matches
current source. No action required.

**Finding §4b.4-g (new): `cache::object::build_isa` is a silent
duplicate of `jit::build_isa`.** Two near-identical functions build
a `TargetIsa`, differing only in the `is_pic` flag. Not a correctness
concern for S62 (both are auto-derived `Send+Sync` per §4b.2), but
recommended for `/backend` housekeeping — unify into one
`build_isa(is_pic: bool)` at a future refresh. Noted for Wave-2
follow-up, not Tier-escalated.

**Summary**: one row added to §4b.2 (`cache::object::build_isa`);
zero rows added in §4b.4 itself. All other candidates investigated
were per-invocation local state, not shared across workers.

### §4b.5 `Jit` SAFETY-comment verification (precedent check vs §4a.2 `GotTable`)

Per the Step-1 handoff note, this section records the verification
of `Jit`'s in-crate SAFETY comments against the Wave-1b
stale-invariant precedent (§4a.2 `GotTable` — the "JIT code pages
valid for process lifetime" claim was stale relative to
Decision 31 / Wave 3b `kept_jits` dissolution).

**Files re-read at SHA `f22dd2d`**: `crates/cranelisp-backend/src/jit.rs`
module-level docs L192–220 (`# Memory reclaim (Decision 31)` +
`# Safety invariant`), `impl Drop for Jit` SAFETY comment L246–258,
and the field-level comment on `pub(crate) static
JIT_FREE_MEMORY_CALL_COUNT` L172–182.

**Outcome — current, no drift.** Every SAFETY passage explicitly
references the current Decision-31 / Wave-3b model:

- L209–211 (module docs): "(`Arc<Jit>` cloned per-entry into
  `Code::Jit { jit, ptr }` on each `ModuleEntry::Def.code` — Sprint 58
  Wave 3b dissolved the pre-existing `SharedState.kept_jits`
  side-store — or stack-local `Jit` instances in REPL eval/backend
  tests)"
- L213–217 (module docs): "Per Decision 31 Scenario 2, when a REPL
  user redefines a defn the prior entry's `Code::Jit` clone drops;
  once the last clone referencing a particular `Jit` batch drops (no
  more entries reference it), `Arc::drop` triggers `Jit::drop` which
  calls `free_memory` and reclaims the per-batch JIT pages."
- L249–254 (`Drop` impl SAFETY): "`Arc<Jit>` cloned per-entry into
  `Code::Jit { jit, ptr }` on `ModuleEntry::Def.code` — Sprint 58
  Wave 3b dissolved the pre-existing `SharedState.kept_jits`
  side-store"
- L178–180 (`JIT_FREE_MEMORY_CALL_COUNT` docs): "Decision 31 requires
  the reclaim path actually runs on every `Jit` drop; this counter is
  the observable evidence it does."

No stale `kept_jits` claim, no "process-lifetime pages" claim, no
references to the pre-Wave-3b retention model. The invariant on the
`Jit` side is **current**. This matches the `Code` re-verification
outcome at §4a.1 — the `GotTable` drift pattern is confined to
`crates/cranelisp-types/src/got.rs` and does not generalize to
adjacent backend code.

**Action**: none. The `Jit` source comments are correctly aligned
with Decision 31; no rewrite required; no `/arch`-gate flag.

## §5 Worker — `src/worker.rs`

`/int`'s worker module is 5,041 LOC but owns no long-lived shared
state of its own — the bulk is parameter passes of `Arc<SharedState>`
and `&CompileScheduler` references into stack-local `ModuleCompiler`
contexts. The §5 rows below are primarily reachability matrices:
which reader class touches which §6 or §4 field under what invariant,
plus three worker-internal items (cache-writer path, `handle_import`
H6 residue, `re_register_module` REPL entry point).

### §5.1 Worker-owned state

Confirmed empty. `ModuleCompiler` (stack-local per module-form-group
typecheck) holds `&mut` borrows of:

- `ctx.symbol_tables: &DashMap<ModuleFullPath, SymbolTable<...>>` —
  alias for `SharedState::symbol_tables` (§6).
- `ctx.next_type_id: &AtomicU32` — alias for `SharedState::next_type_id` (§6).
- `ctx.scheduler: &CompileScheduler` — alias for the scheduler (§4).
- `ctx.shared_state: Option<&SharedState>` — the full shared state handle.

No owned `Arc<T>`, `Mutex<T>`, `DashMap<_,_>`, `AtomicX`, or
`OnceLock<T>` fields live on the `ModuleCompiler` struct. Therefore
**no row**: §5's inventory is zero-owned-fields.

### §5.2 Priority-worker claim loop reachability

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `worker::priority_worker_loop_shared → scheduler.take_priority_work` | `f22dd2d` L3345 | P | claim loop: wait on `priority_work_available`, pop queue under `state` lock, transition `pool` | `state` Mutex | `under-lock-L` | Worker never observes a `TypecheckFirst`/`TypecheckNext` module without also popping it atomically into `TypecheckWorking` pool under the same lock acquisition. | no | stable |
| `worker::priority_worker_loop_shared → SharedState::module_sexps.lock()` | `f22dd2d` L3345 | P | read+remove sexps on claim | `SharedState::module_sexps` Mutex | `under-lock-L` | Claim-removes the sexps exactly once per typecheck task; caller is the sole possessor for the remainder of the task. | no | stable (S57 W4 G9) |

### §5.3 Nice-worker claim loop reachability

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `worker::nice_worker_loop → scheduler.take_object_codegen` | `f22dd2d` | N | claim loop: wait on `object_work_available`, pop `typecheck_done`, set `object_working=true` | `state` Mutex | `under-lock-L` | At most one nice worker holds `object_working=true` for a given module at any time; claim and pop are atomic under the state lock. | no | stable |
| `worker::nice_worker_loop → SharedState::symbol_tables.get(m)` | `f22dd2d` | N | DashMap read to enumerate codegen targets | DashMap shard RwLock (implicit) | `published-then-read` | The nice worker reads `symbol_tables[m]` only after `modules[m].pool == TypecheckDone` has been observed; typecheck's final write of `SymbolTable` for `m` happens-before the pool transition and the condvar notify. | no | stable (Decision 22 / S58 Step 5b) |

### §5.4 Cache-writer path (`.meta.json` + `.o`)

The nice worker, after successful object codegen, writes two files per
module: the `.o` object file (Linker output) and a `.meta.json` manifest
record. Both writes update `SharedState`:

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `worker` → `SharedState::compiled_o_paths.lock().push(path)` | `f22dd2d` | N | Mutex-guarded push after on-disk write succeeds | `compiled_o_paths` Mutex | `under-lock-L` | Path is pushed exactly once per module per session, only after `.o` write flushes and the `object_done=true` scheduler notification is staged. | no | stable |
| `worker` → `SharedState::cache_state.lock().as_mut().record(...)` | `f22dd2d` | N | Mutex-guarded manifest record update | `cache_state` Mutex | `under-lock-L` | Manifest hash entry is added atomically with the `.meta.json` write; the write-through-Mutex guarantees no partial record is visible to a concurrent `record_cache_hit` from a priority worker. | no | stable |

The "`.meta.json` write failed" stderr path called out in the S61 Wave 3
step 3f review is a non-fatal diagnostic, not a correctness invariant —
it does not participate in any invariant required for correct execution
and so is not a separate audit row.

### §5.5 `handle_import` + `register_dep` (S61 H6 residue site)

This is the one confirmed non-trivial H6 residue in the `/int` audit
surface.

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `worker::handle_import::(symbol_tables.contains_key && scheduler.is_typechecked)` | `f22dd2d` L1229–L1231 | P/R | fast-path check on two separate maps, then `register_imports` reads `symbol_tables[dep]` | none across the pair; each map has its own internal locking | `published-then-read` (post S60 Wave 2 Round 4 fix) | The fast-path fires only when `scheduler.is_typechecked(dep)` is true; `is_typechecked` implies `dep.pool ∈ {TypecheckDone, Complete}` which implies `symbol_tables[dep]` has been fully populated by the typechecking worker before the pool transition and condvar notify — so the observer's subsequent `register_imports` read sees a complete SymbolTable. | **yes** (pattern: two-map fast-path without a single atomic envelope) — BUT the coupling is enforced by the typechecker's publication discipline on the scheduler side (pool transition happens only after the SymbolTable is final). The S61 H6 residue (≈5–10% fail rate on `heisenbug_race_reduced_concurrent_import_pairs`) indicates that the discipline is not provably tight under all interleavings observed in stress. | Tier 1 (observed) for risk register; see §10 |
| `worker::register_dep` | `f22dd2d` L1356 | P | writes a waiter entry on `modules[dep].waiters` through the scheduler API | `state` Mutex (via scheduler method) | `under-lock-L` | Waiter registration is linearised with the target module's `pool` observation: if `dep` has already transitioned to `TypecheckDone`, the scheduler call returns `None` (no waiter created) and the caller retries inline; otherwise the waiter is installed under the same lock acquisition that observed the non-terminal pool. | no | stable (S61 Wave 3) |

### §5.6 `re_register_module` (REPL eval entry point)

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `worker` → `scheduler.re_register_module(m)` (called from REPL after source edit) | `f22dd2d` (worker call site from REPL bootstrap) | R | scheduler-side re-insertion into `TypecheckFirst`; clears `cached_modules`, resets `ModuleState` | `state` Mutex | `under-lock-L` | Cross-session state for `m` is cleared atomically with the re-insertion; readers that see the reset never see stale cache-hit inmem pointers from the prior generation. | no | stable |
| `worker` → `SharedState::symbol_tables.remove(m)` (REPL re-register path) | `f22dd2d` | R | DashMap key removal | DashMap shard | `published-then-read` | The removal happens before `scheduler.re_register_module`; any priority worker that races the REPL's re-register will observe either the old SymbolTable (and produce a stale result that the REPL discards) or the new seed (and proceed correctly). Decision 31 per-redefinition reclaim rests on this. | no | stable (Decision 31) |

## §6 Session — `src/session_v4.rs`

This is the density centre of the audit. `SharedState` (declared
lines 533–671) has 17 long-lived fields — the `/arch` Phase 3a readout
estimated 16, but physical inspection finds one additional (`scheduler`
itself is a field of SharedState at L536, bringing the count to 17 if
counted; the scheduler is audited in §4 and is cross-referenced
rather than duplicated here). The rows below cover the 16 non-scheduler
fields plus the two REPL-specific items (§6.3, §6.4).

### §6.1 `SharedState` fields

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `session_v4::SharedState::scheduler` | `f22dd2d` L536 | S/P/N/R | method calls on `CompileScheduler` | — (its own Mutex inside) | — (cross-reference to §4) | Cross-reference to §4; not re-stated here. | no | stable |
| `session_v4::SharedState::project_root` | `f22dd2d` L541 | S/P/N/R | read-only after construction | none | `atomic-by-construction` | Written exactly once during session construction before any worker thread spawns; read-only thereafter. | no | stable (S57 W4 G9) |
| `session_v4::SharedState::lib_dirs` | `f22dd2d` L548 | S/P/N/R | lock for `resolve_module_file` reads; rare writes via reconfigure API | `lib_dirs` Mutex | `under-lock-L` | The Vec is read atomically under the mutex on each module-path resolution; concurrent reconfiguration (test-only) sees a read-after-write-after-lock happens-before. | no | stable |
| `session_v4::SharedState::platform_dirs` | `f22dd2d` L553 | S/P/N/R | lock for platform DLL search; rare writes | `platform_dirs` Mutex | `under-lock-L` | Same invariant as `lib_dirs`. | no | stable |
| `session_v4::SharedState::module_sexps` | `f22dd2d` L559 | S/R (writer); P (reader-and-remover) | insert by register/reload; remove-on-claim by priority worker | `module_sexps` Mutex | `published-then-read` | Writer inserts the full Vec\<Sexp\> before calling `scheduler.register_module` (or `re_register_module`); priority worker claims the module under the scheduler state lock and only then pops the sexps — the scheduler pool transition is the publish barrier. | no (writer publishes via scheduler; reader observes through scheduler pool) | stable (S57 W4 G9) |
| `session_v4::SharedState::suspend_states` | `f22dd2d` L565 | P | insert on module block, remove on resume | `suspend_states` Mutex | `under-lock-L` | Each `ModuleFullPath` has at most one `ModuleSuspendState` entry at a time; the entry is a complete snapshot of `ModuleCompiler` local state needed to resume. | no | stable (S57 W4 G9) |
| `session_v4::SharedState::cache_dir` | `f22dd2d` L569 | S/P/N/R | read-only after construction | none | `atomic-by-construction` | Option set once during session construction; never mutated. | no | stable |
| `session_v4::SharedState::compiled_o_paths` | `f22dd2d` L573 | N (writer); R (reader at end-of-session, e.g., `--link`) | Mutex-guarded push / snapshot | `compiled_o_paths` Mutex | `under-lock-L` | Accumulates exactly one path per module that completes object codegen in this session; readers consume only after all workers have quiesced. | no | stable |
| `session_v4::SharedState::promote_nice_workers` | `f22dd2d` L577 | S (writer); N (reader) | single-bit atomic flag | none (it's the atomic itself) | `atomic-by-construction` | Monotonic false→true within a session phase; readers poll on the hot-flush path and respond idempotently to the transition. | no | stable |
| `session_v4::SharedState::cached_modules` | `f22dd2d` L582 | S/P/R (via `try_cache_hit_load`, file-watcher cascade, `re_register_module`) | insert on cache-hit load; remove on invalidation; `contains` checks | `cached_modules` Mutex | `invariant-unclear` |  | no (per-field); **cross-cutting dual-store with `SchedulerState::cached_modules` §4.2 — flagged §9** | flagged for `/arch` Wave-1 gate |
| `session_v4::SharedState::file_to_module` | `f22dd2d` L587 | P (writer in `handle_import`); R (reader in file-watcher `try_pop_changes`) | Mutex-guarded insert on canonicalised path; lookup on FS event | `file_to_module` Mutex | `under-lock-L` | Every module with a resolved on-disk source has at most one canonical-path key mapping to its `ModuleFullPath`; lookups see a fully-inserted entry or none. | no | stable |
| `session_v4::SharedState::cache_state` | `f22dd2d` L592 | P/N (writers for record hits/writes); R (initialisation, snapshot at end) | Mutex-guarded option initialise / record update | `cache_state` Mutex | `under-lock-L` | Manifest records are added exactly once per successful cache hit or object write; Option is `Some` iff caching is enabled for this session. | no | stable |
| `session_v4::SharedState::symbol_tables` | `f22dd2d` L608 | S/P/N/R | DashMap entry seed / mutate / read (52+ call sites across typecheck + codegen + REPL) | DashMap shard RwLock (per key) | `published-then-read` | Writer (typechecker via `TypeCheckEnv::ensure_module_exists` + per-form Def inserts) populates an entry fully, and the module transitions to `TypecheckDone` only after the last Def is inserted; readers that observe the pool transition see a complete `SymbolTable`. (S61 H6 residue is the residual risk: see §5.5 / §10.) | yes (shared surface with §5.5 residue) | **Tier 1 candidate** for risk register |
| `session_v4::SharedState::next_type_id` | `f22dd2d` L612 | S/P | `fetch_add(1, Relaxed)` across all TypeCheckEnv instances | none (it's the atomic itself) | `atomic-by-construction` | Every TypeId issued by the session is unique; monotonically non-decreasing; no invariant across multiple fetches other than uniqueness. | no | stable (S51) |
| `session_v4::SharedState::current_module` | `f22dd2d` L616 | R (read+write); S (initialisation) | Mutex-guarded single-value swap | `current_module` Mutex | `under-lock-L` | Reads and writes are single-value under the Mutex; the value is only meaningful in REPL mode where one thread (REPL eval) drives reads and writes. In batch mode, worker-thread reads occur under the same Mutex with the guarantee that no concurrent writer exists. | no | stable |
| `session_v4::SharedState::repl_check_state` | `f22dd2d` L621 | R (primary); P (read for REPL retry post-unblock) | Mutex-guarded option read/mutate | `repl_check_state` Mutex | `invariant-unclear` |  | no | **flagged for Wave-1 gate — reader-class split** |
| `session_v4::SharedState::typecheck_products` | `f22dd2d` L628 | P (writer); N (reader) | DashMap insert per module / read-on-claim for codegen | DashMap shard | `published-then-read` | Writer inserts the `TypecheckProduct` entry before calling `scheduler.notify_typecheck_done`; readers observe the entry only after the pool transition, via the scheduler's publication barrier. | no | stable |
| `session_v4::SharedState::kept_dlls` | `f22dd2d` L663 | S/P/N/R (readers through transitively-held `fn_ptr`s); P (writer — platform load) | Mutex-guarded push (append-only) | `kept_dlls` Mutex | `published-then-read` | A `LoadedPlatform` is pushed before any `ModuleEntry::Def.platform_fn_ptr` derived from it is registered into `symbol_tables`; the Vec is never drained for session lifetime; readers dispatching through `fn_ptr` rely on the handle being retained. | no | stable (S57 W3 G8) |
| `session_v4::SharedState::introspection` | `f22dd2d` L665 | P (writer, per compiled symbol); R (reader, REPL slash commands) | DashMap insert per symbol; REPL reads on demand | DashMap shard | `published-then-read` | Writer inserts the `Introspection` entry for `sym` before or during the inmem codegen completion; REPL reads rely on the user having evaluated the symbol, which implies codegen completion published the entry first. | no | stable |

### §6.2 `CompilerSession.shared: Arc<SharedState>` clone sites

`Arc<SharedState>` is cloned into every persistent worker thread on
spawn (`priority_worker_loop_shared` and `nice_worker_loop_shared`
closures). The clone is a single `Arc::clone` call at spawn time; no
subsequent clones happen per work item.

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `session_v4::CompilerSession::shared` (Arc\<SharedState\> clone into worker thread) | `f22dd2d` | S (writer — thread spawn); P/N (readers — thread body) | `Arc::clone` on spawn; `&*shared` reads in worker body | none (atomic refcount on Arc) | `atomic-by-construction` | Arc refcount is incremented atomically before the thread's move closure captures the value; every worker sees the same underlying `SharedState` memory. | no | stable |

### §6.3 `repl_check_state` invariant against concurrent typecheck

The REPL-eval thread reads and mutates `repl_check_state` across every
eval. During `register_dep_for_eval` (L1431), a priority worker may
concurrently resume a blocked module and transitively reach
`symbol_tables` via TypeCheckEnv. The REPL-eval thread's CheckState is
locally scoped (not behind this field during the critical section),
but the Option's Some-ness is mutated at eval start/end.

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `session_v4::SharedState::repl_check_state` — REPL-eval reader | `f22dd2d` L621 | R | take / put_back around each eval | `repl_check_state` Mutex | `under-lock-L` | The Option is taken (Some→None) at eval start and put back (None→Some) at eval end; no priority worker reads the Option in the intervening window. | no | stable |
| `session_v4::SharedState::repl_check_state` — priority-worker reader (**REFUTED by §8.2**) | `f22dd2d` L621 | P | (claimed: no read — **confirmed by /typecheck §8.2**: typecheck crate does not import `SharedState`; holds `CheckState` via `&mut` only) | `repl_check_state` Mutex (not reached from P) | `under-lock-L` | The Option is only read by the REPL-eval thread; priority workers do not depend on `SharedState` and cannot reach this field (§8.2 refutes the Phase-3a priority-worker-reader claim — see §8.2 "`repl_check_state` priority-worker-reader claim — verdict: REFUTED"). | no | stable (`invariant-unclear` tag cleared Wave-1 late per §8.2 recommendation) |

The priority-worker-reader row was tagged `invariant-unclear` in the
Wave-1 draft pending `/typecheck` confirmation that priority workers
do not reach `repl_check_state`. §8.2 (authored by `/typecheck`) has
confirmed the claim with a dependency-graph argument: the typecheck
crate does not import `SharedState` at all, so no code path there can
reach this field; workers invoke typecheck with a fresh/worker-scoped
`&mut CheckState`. The tag is cleared. §10.2 tally is updated
accordingly — this removes one of the three original
`invariant-unclear` rows.

### §6.4 `cached_modules` dual-store

`SharedState::cached_modules: Mutex<HashSet<ModuleFullPath>>` (L582)
AND `SchedulerState::cached_modules: HashSet<ModuleFullPath>` (L233)
coexist. Both are inserted in broadly the same path (cache-hit load
flow). Per the Wave-1 gate agenda (SPRINT.md §Notes item 2) this is a
Principle-7 adjudication question for `/arch`: one logical set with
two physical stores, or two legitimate stores with different roles?

Provisional classification: `invariant-unclear` (column F of the
§6.1 row for `cached_modules`, and of the §4.2 row for
`SchedulerState::cached_modules`). The two rows cross-reference; a
single Tier-3 risk register entry will represent the pair.

## §7 Runtime trace — `crates/cranelisp-runtime/src/trace.rs`

Four long-lived items in this file (no `OnceLock` found — see §7.3).

### §7.1 Static atomics

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `runtime::trace::TRACE_THREAD_ID` | `f22dd2d` L53 | any thread executing traced code | CAS-style assignment / read-back | none (it's the atomic itself) | `atomic-by-construction` | A single thread owns the trace role at any time; `0` means unowned; competing `trace` invocations from other threads observe non-zero and skip. | no | stable |
| `runtime::trace::THREAD_ID_COUNTER` | `f22dd2d` L61 | any thread on first `THIS_THREAD_ID` access | `fetch_add(1, Relaxed)` | none | `atomic-by-construction` | Every thread issues one unique ID on first access; IDs are strictly positive (starts at 1); `0` reserved for "no owner". | no | stable |

### §7.2 Static mutex

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `runtime::trace::TRACE_STACK` | `f22dd2d` L86 | single owning thread (guarded by `TRACE_THREAD_ID`) | lock / push / pop / mutate frame fields | `TRACE_STACK` Mutex | `under-lock-L` | Stack depth matches call depth of the traced body; frame `name`, `params`, `result`, `start`, `children` are populated left-to-right across lifetime of a single frame; poisoning recovery is safe because the stack is append-only during normal operation. | no | stable |

### §7.3 `OnceLock<TraceFilter>` — audit finding: site not found in `trace.rs`

Per Wave-1 gate agenda item 1 (SPRINT.md §Notes), `/arch` Phase 2 §1
required this audit to cover an `OnceLock<TraceFilter>` site in
`crates/cranelisp-runtime/src/trace.rs`. Grep on the specified file
returns zero `OnceLock` matches.

**Broader grep** (for the Wave-1 gate record): `OnceLock` in
`crates/cranelisp-runtime/src/` matches only in
`crates/cranelisp-runtime/src/io_trace.rs`:

- `TRACE_ANCHOR: OnceLock<Instant>` (io_trace.rs L58)
- `IO_TRACE_FILTER: OnceLock<Option<TraceFilter>>` (io_trace.rs L83) ← likely intended referent
- `PUBLISHED_BUFFERS: OnceLock<std::sync::Mutex<Vec<Vec<IoTraceEvent>>>>` (io_trace.rs L271)

`io_trace.rs` is not in Sprint 62's audit surface as currently scoped
(the surface names `trace.rs`, not `io_trace.rs`). **Wave-1 gate
decision required** (`/arch`): (a) drop the `OnceLock<TraceFilter>`
callout; (b) extend the audit surface to cover `io_trace.rs` and
author its section in Wave 1 (`/int` proposes adding ~3 rows to §7);
(c) treat `io_trace.rs` as out-of-scope for S62 and covered under
`/backend`'s review pass on observability instrumentation. Default
recommendation pending gate: (b), because
`IO_TRACE_FILTER: OnceLock<Option<TraceFilter>>` is the exact type
`/arch` Phase 2 §1 named and the concurrency surface is structurally
equivalent to the intended audit target.

### §7.4 RC-field atomic reads (cross-reference)

The codegen-emitted `AtomicI64` reads on heap-allocated RC fields
(L470–474 in `trace.rs::clone_atomic_rc` and throughout the codegen
emit path) are owned by `/backend`'s RC invariant framework (§7.4 of
`design/arch/decisions` around Decision 31) and are audited implicitly
by the generated code's conformance tests, not by field-level enumeration
here. Row suppressed — out of audit denominator per §2 grep (no
`AtomicI64<T>` *field* declaration in the target files; the atomic is
reinterpret-cast from raw heap bytes).

## §8 Typecheck — `crates/cranelisp-typecheck/`

### §8.1 Preamble

**Ownership**: the typecheck crate OWNS no long-lived shared state. The
`§2` denominator grep across `crates/cranelisp-typecheck/src/**` returns
exactly two classes of matches:

- **`&'a` borrowed references** on `TypeCheckEnv` (checker.rs): the
  `DashMap<ModuleFullPath, SymbolTable<C,L>>` and `AtomicU32` are owned
  by the session (`SharedState::symbol_tables` §6.1 and
  `SharedState::next_type_id` §6.1 respectively). `TypeCheckEnv` is a
  *borrowed view*, not a home.
- **Process-global `OnceLock`s** in `trace.rs`: install-once forwarding
  hook (`SYMBOL_TABLE_ENSURE_HOOK`) and a `#[cfg(test)]`-only event
  buffer (`TEST_HOOK_EVENTS`). Neither is session-scoped.

**Implication**: every invariant on `TypeCheckEnv::modules` is
*co-owned* with /int §6 — the physical DashMap lives in SharedState,
the readers/writers live on both sides of the crate boundary. The
cross-crate link and joint invariant statement are proposed additions
to §9 (see §8.5 below); within §8 each row declares the typecheck-side
reader/writer behaviour only.

**Verified-at-SHA (this section)**: `f22dd2d` — same as the
document-wide SHA recorded at §3.

**CheckState note**: `CheckState` (checker.rs L52–L84) is a stack-local
value passed as `&mut CheckState` to inference methods. The caller owns
it. It contains no `Arc`/`Mutex`/`RwLock`/`DashMap`/`OnceLock`/`AtomicX`
fields and is therefore out of the §2 denominator. Its relationship to
`SharedState::repl_check_state` (§6.3) is that the REPL session stores
*a* `CheckState` inside that Mutex — but the typecheck crate never
accesses the Mutex; it receives `&mut CheckState` on already-unlocked
ownership handed in by the caller.

### §8.2 `checker.rs` — `TypeCheckEnv`

Schema reminder: A={module-path,field-name} / B=verified-at-SHA /
C=reader-class / D=operation / E=lock-held / F=classification /
G=invariant (one sentence) / H=H6-grep-match / I=current-status.

Reader-class row expansion on `TypeCheckEnv::modules` distinguishes
two access paths:

- **Ensure-path**: `ensure_module_exists` (L233–L293) — the S61 Wave 3
  step 3e'' atomic check-then-insert.
- **Lookup-path**: 52+ read sites across checker.rs / infer.rs /
  adt.rs / traits.rs / program.rs / builtins.rs (counted by
  `rg self.modules` / `env.modules`). Representative call sites:
  `current_symbol_table` (L176), `current_symbol_table_mut` (L189),
  `has_module` (L296), `lookup_type_def` (L304), iteration over
  `self.modules.iter()` (L308, L328, L365).

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `typecheck::checker::TypeCheckEnv::modules` (ensure-path) | `f22dd2d` L148 / L233–L293 | S/P/R | `entry(path).or_insert_with(...)` — shard-locked check-then-insert; emits `SymbolTableEnsure { Created | AlreadyPresent }` after the shard lock is released | DashMap shard write-lock (held by `entry(...)` guard across the closure) | `atomic-by-construction` | A concurrent ensure on the same `path` serialises behind the shard write-lock: exactly one caller observes `Vacant` and inserts; all others observe `Occupied` and leave the populated table intact (no overwrite). | no (S61 Wave 3 step 3e'' closed the prior `contains_key` … `insert` residue by collapsing to a single shard-locked `entry` call) | stable (S61 Wave 3) |
| `typecheck::checker::TypeCheckEnv::modules` (lookup-path) | `f22dd2d` L148 / 52 sites | S/P/R | `get` / `get_mut` / `contains_key` / `iter` / per-entry `SymbolTable` mutation via `RefMut` guard | DashMap shard RwLock (per-guard) | `published-then-read` | A reader that observes `modules[m]` after the writer (priority worker's typecheck of `m`) has transitioned `m` to `TypecheckDone` (§4.2) sees a complete `SymbolTable` for `m`; mid-typecheck concurrent reads on `m` are confined to the same worker's own `CheckState` + per-form incremental `ModuleEntry` inserts which are monotonic-additive within a module (no entry is removed mid-typecheck). | no (H6 residue on this physical map is enumerated on the /int side under `handle_import` §5.5 — cross-crate, not typecheck-internal) | stable (S60 Wave 2 Round 4 / S61 Wave 3 on the cross-crate surface) |
| `typecheck::checker::TypeCheckEnv::next_id` | `f22dd2d` L142 | S/P | `fetch_add(1, Relaxed)` via `self.next_id.fetch_add(1, Ordering::Relaxed)` across `fresh_type_var` / `fresh_id` helpers | none (it's the atomic itself) | `atomic-by-construction` | Every TypeId issued by any `TypeCheckEnv` aliasing the same `AtomicU32` is unique; monotonically non-decreasing; no invariant across multiple fetches other than uniqueness (matches §6.1 `SharedState::next_type_id` invariant — same physical atomic). | no | stable (S51) |

**`repl_check_state` priority-worker-reader claim — verdict: REFUTED.**

Phase 3a asserted "priority workers don't read `SharedState::repl_check_state`"
but flagged the claim as unverified (§6.3 priority-worker-reader row
classified `invariant-unclear`). The typecheck-side audit resolves it:

1. `rg -n "repl_check_state" crates/cranelisp-typecheck/src/` returns
   exactly **one** match — a doc comment in checker.rs L109 that
   *mentions* the REPL's Mutex-holding pattern for context. No code
   path reads or writes the field.
2. `rg -n "SharedState|shared_state" crates/cranelisp-typecheck/src/`
   returns **two** matches, both in comments (program.rs L2191 and
   checker.rs L393). The typecheck crate does not import or reference
   `SharedState` at all — it cannot read `repl_check_state` because
   the symbol is not in its dependency graph.
3. `CheckState` values are passed into the typecheck crate as
   `&mut CheckState` by the caller; the caller (integration crate) is
   responsible for taking the Mutex before passing the reference. On
   priority-worker threads the typecheck entry point is invoked with
   a fresh/worker-scoped `CheckState` (§6.3 REPL-eval row's invariant
   "no priority worker reads the Option in the intervening window"
   holds: priority workers never touch the Mutex at all).

**Recommendation to /int**: remove the `invariant-unclear` tag from
§6.3's priority-worker row and replace its column F with a
cross-reference note "priority workers do not read
`repl_check_state` — confirmed by §8.2, typecheck crate does not
depend on `SharedState`." Proposed invariant text for column G:
"The Option is only read by the REPL-eval thread; priority workers do
not depend on `SharedState` and cannot reach this field." This moves
the row from `invariant-unclear` to `under-lock-L` with a single
reader class (R), eliminating one of the three auto-Tier-3 rows tallied
in §10.2.

### §8.3 `trace.rs` — observability hooks

| A | B | C | D | E | F | G | H | I |
|---|---|---|---|---|---|---|---|---|
| `typecheck::trace::SYMBOL_TABLE_ENSURE_HOOK` | `f22dd2d` L65 | S (writer — install once at `main()` startup); S/P/R (readers — every `emit_symbol_table_ensure` call) | `OnceLock::set` on install; `OnceLock::get` + null-check + fn-ptr call on every emission | none (OnceLock semantics) | `published-then-read` | The install call is single-shot before any typecheck worker spawns; every subsequent reader observes either `None` (no sink installed — no-op fast path) or `Some(hook)` with the forwarding pointer fully published; the installed `hook` function pointer does not change over the session's lifetime. | no | stable (S61 Wave 3 step 3d'') |
| `typecheck::trace::tests::TEST_HOOK_EVENTS` | `f22dd2d` L100 | test-process-only (any `#[test]` thread) | `OnceLock::get_or_init(|| Mutex::new(Vec::new()))`; then Mutex lock + push / take on the Vec | `TEST_HOOK_EVENTS` inner Mutex | `under-lock-L` | The Mutex-guarded Vec is a test-harness sink: pushes and drains under the inner Mutex preserve event ordering for the asserting test; no production code path reaches this symbol (gated by `#[cfg(test)]`). | no | stable — test-only, not in production reachability graph |

### §8.4 Other files (confirmation of zero owned shared state)

**Grep command**:

```
rg -n '\b(Arc|Mutex|RwLock|DashMap|OnceLock|Atomic[A-Za-z0-9]+)\s*<' crates/cranelisp-typecheck/src/
```

**Output summary** (post-filter for field declarations, excluding
comment/doc matches, excluding `#[cfg(test)]` fixture scaffolding):

| File | Match count | Disposition |
|---|---:|---|
| `checker.rs` | 4 | `TypeCheckEnv::modules` (L148), `TypeCheckEnv::next_id` (implicit via L142 `&'a AtomicU32`), `TypeCheckEnv::new` signature (L163, same field), `TypeCheckEnv::modules()` accessor (L383 / L429) — all reference the two fields covered in §8.2. `TestFixture::modules` / `TestFixture::next_id` (L1619–L1620) are `#[cfg(test)]` scaffolding — out of denominator per §2 rubric. |
| `trace.rs` | 3 | `SYMBOL_TABLE_ENSURE_HOOK` (L65) in §8.3; `TEST_HOOK_EVENTS` (L100) in §8.3; doc comment (L19) — not a field. |
| `builtins.rs` | 1 | L57 — function parameter type on `register_builtins`, not a field declaration. Out of denominator. |
| `program.rs` | 1 | L2191–L2194 comment block referencing `Arc<Jit>` and `SharedState.kept_jits` — both in comments, no field. Out of denominator. |
| `adt.rs`, `infer.rs`, `resolve.rs`, `unify.rs`, `scheme.rs`, `scope.rs`, `traits.rs`, `lib.rs` | 0 | No matches. |

**Confirmation**: no `Arc<T>` / `Mutex<T>` / `RwLock<T>` / `DashMap<_,_>`
/ `AtomicX` / `OnceLock<T>` *field declaration* exists anywhere in the
typecheck crate outside `checker.rs::TypeCheckEnv` (covered in §8.2)
and `trace.rs` (covered in §8.3). No surprises; the Phase 3a
"pure-functions only" claim for the eight non-audited files holds.

#### §8.4 Addendum (Wave-1b) — Grep-2 denominator on typecheck crate

**Grep-2 command** (per /int's §2 schema extension):

```
rg -nE 'unsafe impl\s+(Send|Sync)\b' crates/cranelisp-typecheck/src/
```

**Output**: zero matches. A widened scan across the whole crate
(`crates/cranelisp-typecheck/`, including `tests/` if any) also returns
zero matches.

**Type-system status (column J) for the typecheck crate**: uniformly
`auto-derived-safe`. No `unsafe impl Send` / `unsafe impl Sync`
override appears in any typecheck-crate source file; no raw-pointer
coordination pattern (Grep-3 class) appears either. All shared-state
access in this crate is via borrowed `&'a` references to
`SharedState`-owned primitives whose Grep-1 audit lives under §6
(`SharedState::symbol_tables` / `SharedState::next_type_id`). The
reachability from `TypeCheckEnv` into `unsafe impl`-bearing
types owned elsewhere (e.g. `Code`, `GotTable`, `LoadedPlatform` per
§4a) is *downstream* through the /int-owned `SharedState` fields — and
per /int's schema-extension rule (§2, "the addition is forward-only"),
§8.2 / §8.3 rows are NOT retrofitted with column J; the reachability
invariant lives on the declaring row in §4a where the `unsafe impl`
actually sits.

**Confirmation**: §8's type-system surface is empty. The crate's
contribution to /int's §4a tally is zero rows. §8.FIXME (Option B +
Decision 3X draft below) is unaffected by /int's Wave-1b extension —
/int's §4a is a disjoint surface from §8's (§4a is "types that override
Send/Sync"; §8 has no such types, only borrows).

### §8.FIXME `checker.rs:205` disposition

**Final choice: Option B — ratify as numbered Decision in
`design/arch/CLAUDE.md`.**

**Rationale** (reaffirmed after audit): the audit confirms
`TypeCheckEnv` owns no shared state — it is structurally a borrowed
view. Accepting formal ownership (Option A) would require
`TypeCheckEnv` to become the invariant home for a field it does not
own, inverting the SharedState ownership boundary established by /arch
Decision 22 and Decision 32. Option C (defer) is prohibited without a
named target sprint and is not justified — the ownership question has
a clean structural answer. Option B memorialises the
/int-authors-with-/typecheck-reviews arrangement that the S61 H6 fix
actually used and which the §8.2 `ensure-path` row classifies as
`atomic-by-construction`.

**Proposed Decision 3X text** (for /arch to ratify at Wave-1 gate;
slightly refined from Phase 3a draft to cite the audit rows):

> **Decision 3X — Co-owned invariants on borrowed SharedState maps.**
> Where the typecheck crate exposes a `&'a` borrow of a session-owned
> concurrency primitive (e.g. `TypeCheckEnv::modules` borrowing
> `SharedState::symbol_tables`, `TypeCheckEnv::next_id` borrowing
> `SharedState::next_type_id`), the concurrency invariant on that field
> is *co-owned*: `/int` authors the mechanism on its side of the
> boundary and on the typecheck side when the fix must live there;
> `/typecheck` reviews the typecheck-side diff before commit; the
> invariant statement lives in `design/int/concurrency-audit.md §9`
> with cross-references on both sides' per-row entries. The
> `checker.rs::ensure_module_exists` rewrite of Sprint 61 Wave 3 step
> 3e'' (Decision 32 H6 closure) is the founding instance. Further
> `/int` → `crates/cranelisp-typecheck/src/` edits under this precedent
> require `/arch` arbitration and explicit scoping; the precedent is
> narrow by default.

**In-sprint code change**: the one-line FIXME comment at
`crates/cranelisp-typecheck/src/checker.rs:205` will be removed at
sprint close (replaced by a short pointer to Decision 3X) — per
SPRINT.md §FIXME Debt, that is the permitted in-sprint change if the
disposition is A or B. No other code touched.

### §8.5 Cross-cutting contributions to §9

*The following are proposed additions to §9 (cross-cutting findings).
`/sprint` merges them into the existing §9.1–§9.4 at Wave-1 close;
this subsection does not edit /int's §9 text directly.*

**Proposed §9.5 — `TypeCheckEnv::modules` ↔ `SharedState::symbol_tables`
(joint invariant).** The two names refer to the same physical
DashMap: /int's `SharedState::symbol_tables` (§6.1) is the owner;
/typecheck's `TypeCheckEnv::modules` (§8.2) is a `&'a` borrow. The
joint invariant — populated entries are monotonic-additive within a
module until `TypecheckDone` is published — is authored by /int on
the writer side (§5.3 nice worker, §5.5 handle_import) and relied on
by /typecheck on the reader side (§8.2 lookup-path row). The H6
residue documented in §5.5 is against the cross-crate fast-path
coupling, not against the DashMap's internal discipline.

**Proposed §9.6 — `TypeCheckEnv::next_id` ↔ `SharedState::next_type_id`
(alias note).** Every `TypeCheckEnv` instance borrows the same
`AtomicU32` from `SharedState::next_type_id` (§6.1); the uniqueness
invariant stated at §6.1 is the same invariant stated at §8.2 — one
physical atomic, two rows, identical `atomic-by-construction` label.

**Proposed addition to §9.2 (Decision 30 disambiguation) — typecheck
non-participation.** `TypeCheckEnv::lookup_type_def` (checker.rs L304)
scans all modules in the DashMap for a TypeName; this scan is NOT the
mutual-import deadlock site. The scan holds no lock across iteration
boundaries (each `guard` is dropped at end-of-iter) and performs no
scheduler-side state mutation. The deadlock stated in /arch Decision 30
is scheduler-side (form-by-form mutual `register_dep`) and does not
involve typecheck-crate code paths. §9.2's classification (architectural
constraint, not race) is unchanged.

**Proposed addition to §9.3 (Decision 31 — typecheck reader invariant).**
Typecheck readers of `SharedState::symbol_tables` (via
`TypeCheckEnv::modules`) do NOT assume `got_slot` stability across
concurrent redefinition. The §8.2 lookup-path row's `published-then-read`
invariant rests on monotonic-additive per-form `ModuleEntry` inserts
within a module, not on the GOT-slot or `Code::Jit` handle remaining
identity-stable across redefinition. Typecheck never dereferences a raw
`fn_ptr` and never holds a `Code::Jit` Arc across a read of
`ModuleEntry::Def`; the per-redefinition reclaim (Decision 31) is
therefore transparent to typecheck-side readers.

**Proposed addition to §9 (new §9.5 placement)**: `/sprint` to renumber
— the four proposed items above land as §9.5 (joint symbol_tables),
§9.6 (next_type_id alias), with §9.2 and §9.3 gaining one-paragraph
typecheck-side amendments rather than separate new sections.

## §9 Cross-cutting findings

### §9.1 `cached_modules` dual-store (Principle-7 adjudication)

`SharedState::cached_modules` (§6.1, L582) and
`SchedulerState::cached_modules` (§4.2, L233) are both populated on
cache-hit load and both consulted on re-register. This audit cannot
state from code whether these are (a) one logical set redundantly
stored in two locations (Principle-7 violation — one state, two
homes), or (b) two distinct stores with different roles (e.g., a
cache-hint in SharedState + an authoritative scheduler-side record for
`re_register_module`'s clearing logic). Both §6.1 and §4.2 rows
classify as `invariant-unclear`. A single Tier-3 risk register row
covers the pair (pending `/arch` adjudication at Wave-1 gate). If
`/arch` rules (a), the resolution is a code change in S63+ removing
one of the two stores. If `/arch` rules (b), the resolution is an
invariant statement added to both rows and the rows are reclassified
(likely `under-lock-L` for the scheduler side and `under-lock-L` for
the SharedState side, with a documented cross-store consistency
invariant that the two are synchronously co-mutated).

### §9.2 Decision 30 — mutual-import deadlock

`design/arch/CLAUDE.md` Decision 30 records that the v4 scheduler
can deadlock on form-by-form mutual imports: module A imports B, B
imports A, both are pushed to `typecheck_first`, both block on each
other's `register_dep`. This is an **architectural constraint, not a
race** — the scheduler's behaviour is deterministic on the
interleaving; the problem is the absence of a cycle-break policy.
The relevant row is §4.2 `ModuleState::blocked_on`; the invariant
column states forward-edge consistency but does not claim absence of
cycles. No H6 match; no shared-state misuse; the audit flags it here
so the Wave-2 risk register can assign it a tier (likely Tier-2 by
pattern if an observed test exists, else Tier-3).

### §9.3 Decision 31 — per-redefinition JIT reclaim

`design/arch/CLAUDE.md` Decision 31 establishes that every REPL
redefinition produces a new `Arc<Jit>` (or `Arc<Linker>`) on the
matching `ModuleEntry::Def.code`, and when the prior entry drops, the
`Jit::Drop` call reclaims JIT memory. Every reader of
`SharedState::symbol_tables` (§6.1) MUST preserve the GOT-slot
atomic-swap invariant: reads of `Def.code` go through the DashMap
entry, which holds the Arc, keeping the JIT alive for the duration of
the read borrow. The §6.1 row for `symbol_tables` and the §5.3 row
for the nice-worker reader reference this invariant. Decision 31 is
the cited authority; the audit records the invariant as
`published-then-read` and notes that the per-redefinition reclaim is
predicated on no priority worker holding a raw fn_ptr across a
redefinition boundary without holding the DashMap ref.

### §9.4 TypeId monotonic allocation

`SharedState::next_type_id: AtomicU32` (§6.1) is the session-wide
source of fresh TypeIds. The invariant (every issued TypeId is unique)
is stated on §6.1. §8 (typecheck crate) will supply the
`TypeCheckEnv::next_id: &'a AtomicU32` borrowed-alias row and confirm
that every TypeCheckEnv instance aliases the same atomic. Cross-section
consistency between §6 and §8 is verified at Wave-1 merge.

### §9.5 Decision 31 — temporal-lifetime invariants on `Code` + `GotTable` + `Arc<Jit>`

Decision 31 (`design/arch/CLAUDE.md`) establishes per-redefinition
reclaim: every REPL redefinition produces a new `Arc<Jit>` (or
`Arc<Linker>`), and when the last reference drops, JIT pages are
freed. This cross-cuts three rows in §4a and two rows in §4–§6:

- **§4a.1 `Code`** — `Arc<Jit>` is the lifetime root for the raw `ptr`;
  they drop atomically. The `unsafe impl Send+Sync` rests on
  post-finalize immutability of the `Jit` body plus `Arc`'s auto-Send+Sync.
- **§4a.2 `GotTable`** — atomic slot swap via `AtomicPtr::store(Release)`
  / `load(Acquire)` serialises concurrent writers + readers. The
  in-source SAFETY comment ("JIT code pages valid for the process
  lifetime") is **stale relative to Decision 31** and is flagged for
  `/arch` rewrite.
- **§5.3 nice-worker reader of `SharedState::symbol_tables`** and
  **§6.1 `SharedState::symbol_tables`** — readers observe
  `ModuleEntry::Def.code` through the DashMap entry, which holds the
  `Arc<Jit>` via `Code::Jit`, keeping the JIT alive for the duration
  of the read borrow.

**Composite invariant statement (proposed Wave-1 gate addition — for
`/arch` ratification):**

> **Decision-31 temporal-lifetime invariant.** No thread may hold a
> raw reference into JIT code (a `*const u8` code pointer, a GOT-slot
> value, or a dereferencable `ptr` field inside `Code::Jit` / `Code::Linker`)
> whose originating `Arc<Jit>` / `Arc<Linker>` has been dropped. The
> invariant is maintained by three structural mechanisms:
>
> 1. `ModuleEntry::Def.code: Option<Code>` holds the `Arc` alongside
>    the `ptr`; the two drop together.
> 2. GOT-slot writes use `AtomicPtr::store(Release)`; reads use
>    `AtomicPtr::load(Acquire)`; the pairing serialises the swap with
>    any concurrent reader's observation of the slot value.
> 3. A caller that observes a GOT-slot value or a `Code::Jit.ptr`
>    must hold (directly or transitively) a live reference to the
>    owning `Arc<Jit>` for the duration of the dereference — in
>    practice this is the DashMap entry borrow on `symbol_tables[m]`,
>    which holds the `Code` which holds the `Arc`.
>
> The invariant is **not** "JIT code pages remain valid for the
> process lifetime" (the pre-Wave-3b retention model under `kept_jits`).
> It is per-redefinition, carried by the `Arc` reference graph.

**Row cross-reference**: §4a.1 (`Code`), §4a.2 (`GotTable`), §5.3
(nice-worker reader), §6.1 (`SharedState::symbol_tables`), §9.3
(prior Decision-31 subsection, amended by this section).

**Action on `/arch` Wave-1 gate**: ratify the composite invariant
above into a numbered addendum to Decision 31, and direct
`cranelisp-types/src/got.rs:30-32` SAFETY comment to be rewritten to
cross-reference it. Author prose refers to the stale "process
lifetime" claim; the cross-reference eliminates the staleness without
changing the in-code comment's structure.

## §10 Handoff to risk register

The audit's output to `design/int/concurrency-risks.md` (Wave 2) is
governed by these rules.

### §10.1 Auto-mapping rules

- **Every row with classification `invariant-unclear`** (column F) →
  **Tier-3 risk register row** automatically. No ratio budgeting.
- **Every row with column J = `unsafe-impl-prose-invariant`** (new
  rule, Wave-1 late) → **Tier-3 risk register row** automatically —
  these are sites where the author has asserted thread-safety via
  `unsafe impl`, an invariant exists in author prose, but the audit
  cannot verify the invariant mechanically. Same rule shape as the
  column-F rule; different rationale (prose-not-verifiable rather
  than no-invariant-statable).
- **Every reachability-from-worker row** (§4b) **without a stated
  invariant in column G** (Wave-1c rule) → **Tier-3 risk register
  row** automatically. Same rule shape as the column-F
  `invariant-unclear` rule and the column-J
  `unsafe-impl-prose-invariant` rule. Rationale: a row that
  establishes reachability (a static is written from workers, an
  `Arc<dyn TargetIsa>` is cloned across workers) but cannot state
  the invariant crisply is durable evidence that the worker-reachable
  shared state is not well-understood at the audit's level of
  analysis — identical Tier-3 posture to the column-F and column-J
  auto-mappings.
- **Every row with H6-grep-match = yes** (column H) → **Tier-2
  candidate** (Suspected by pattern).
- **Every row with an observed failing test that reproduces a race at
  that field** → **Tier-1** (Observed).

### §10.2 Current tallies (Wave-1 final, post-extension)

From §4–§8 plus new §4a:

**Column F `invariant-unclear` rows**:
- §4.2 `SchedulerState::cached_modules` (dual-store; §9.1)
- §6.1 `SharedState::cached_modules` (dual-store; §9.1 — paired row)
- ~~§6.3 `repl_check_state` priority-worker reader~~ — **cleared**
  Wave-1 late per §8.2 typecheck-side refutation (dependency-graph
  argument: typecheck crate does not import `SharedState`). Net
  reduction of one Tier-3 candidate from the pair.
- **Count: 2** (both cross-reference to §9.1 — one logical finding)

**Column J `unsafe-impl-prose-invariant` rows** (new Tier-3 sub-category):
- §4a.2 `GotTable` — source SAFETY comment L30–32 is stale relative
  to Decision 31 ("JIT code pages valid for process lifetime" is the
  pre-Wave-3b retention model; Decision-31 per-redefinition reclaim
  invalidated it). Correct invariant lives at §9.5 but is not stated
  on the `GotTable` declaration itself. Resolution: `/arch` to
  ratify §9.5's composite invariant and direct rewrite of the
  SAFETY comment at `got.rs:30-32`.
- **Count: 1**

**Column H H6-grep-match = yes rows** (Tier-2 candidates):
- §5.5 `handle_import` fast-path on two-map coupling
- §6.1 `SharedState::symbol_tables` (surface of the §5.5 residue)
- **Count: 2** (cross-referenced; logically one surface)

**Total Tier-3 auto-mapped rows**: 2 (column F) + 1 (column J) = **3
Tier-3 auto-mapped rows** handed to Wave 2 risk register. Column F
count dropped from 3→2 (§6.3 `repl_check_state` cleared); column J
added 1 (§4a.2 `GotTable`). Net: unchanged at 3, but the composition
shifted — one was cleared on evidence, one was added on broader grep.

**Wave-1c close — §4b authored by `/backend`**. Row counts added:

- §4b.1 (process-global statics): **3 rows**
  (`JIT_FREE_MEMORY_CALL_COUNT`, `FINGERPRINT`, `LENIENT_DISABLED`);
  all column J = `auto-derived-safe`; all column I = stable; zero
  Tier-3 auto-mappings (all three have crisp column-G invariants and
  are reachability-from-worker rows WITH stated invariants).
- §4b.2 (`Arc<dyn TargetIsa>` sharing): **2 rows** — one for the JIT
  shared ISA (`jit::build_shared_isa` + `Jit::new_with_isa`), one
  for the cache-writer-thread per-packet ISA
  (`cache::object::build_isa`, a near-duplicate noted for Wave-2
  housekeeping). Both column J = `auto-derived-safe`; both column I =
  stable; zero Tier-3 auto-mappings.
- §4b.3 (`display.rs` reader class): **1 row**, reader-class `R`
  only. Confirmed REPL-eval-only by call-site grep across backend
  crate + `worker.rs`/`scheduler.rs` (no worker-path callers; trace
  format path runs on eval thread via `TRACE_DISPLAY` thread-local).
  Column J = `auto-derived-safe`; column I = stable; zero Tier-3.
- §4b.4 (backend-internal state): **0 rows added.** Seven findings
  recorded, all of the shape "looked and found nothing
  cross-worker-shared": `FnCompiler` per-function; `CompileContext`
  `&`-refs only; intrinsic registries built afresh per call; no
  shared vec_elem_inc / drop-glue cache; cache-directory coordination
  externalised through serde + single-writer; `CompilationResult`
  invariant verified current (no drift); `cache::object::build_isa`
  duplicate noted for Wave-2 housekeeping.
- §4b.5 (`Jit` SAFETY re-verification): **0 new rows.** Verification
  record only. `Jit` SAFETY comments at jit.rs L192–258 are current
  with Decision 31 / Wave-3b (explicitly reference `kept_jits`
  dissolution). No `/arch`-gate flag needed; the `GotTable` drift
  pattern does not generalize.

**Wave-1c net effect on Tier-3 count**: +0. All six §4b rows carry
stated column-G invariants and `auto-derived-safe` column J. No
new `invariant-unclear` rows; no new `unsafe-impl-prose-invariant`
rows. The `Code` column-G re-verification against the `GotTable`
precedent found **no drift** (§4a.1 column I updated in Step 1);
the `Jit` re-verification in §4b.5 likewise found no drift.
Column-J `unsafe-impl-prose-invariant` tally remains at 1 (still
`GotTable` only).

**Non-trivial findings worth Wave-2 risk-register callout beyond the
auto-map**: the `CacheWritePacket::unsafe impl Send` invariant
depends on `ObjectCompileInput`'s internal composition (no raw
pointers); this is a silent-break risk flagged in §4a.5. Not auto-mapped
(column J = `unsafe-impl-with-invariant`), but recommended for Wave-2
Tier-3 inclusion as a `/backend` follow-up. Left for Wave 2 to decide.

### §10.3 Pre-identified Tier-1 rows

Per SPRINT.md §10 handoff and `design/int/heisenbug-race-closure.md`
§7.10:

- **`sprint23::heisenbug_race_reduced_concurrent_import_pairs`** — the
  committed failing test (currently ~5–10% stress-failure rate on
  `handle_import`'s two-map fast path). Cites audit rows §5.5 and
  §6.1 by stable key `{worker::handle_import, (symbol_tables,
  scheduler.is_typechecked)}` and `{session_v4::SharedState,
  symbol_tables}`.
- **`sprint61_observability_io::io_trace_off_path_*_generous_ceiling`** —
  the harness-ceiling Tier-1 (not a race, but the observation-discipline
  evidence bar is identical per SPRINT.md §Scope item 2). Cites audit
  rows in §7 if `/arch`'s Wave-1 gate decision extends the audit
  surface to `io_trace.rs`; otherwise cites §7.3 as the
  site-not-found finding and the corresponding Tier-1 entry is
  deferred to the audit-surface extension in Wave 1 part 2 (per §7.3
  default recommendation).

### §10.4 Citation convention

The risk register cites audit rows by the column-A stable key —
`{module-path, field-name}` — NOT by line number. Line drift between
sprints invalidates line-number citations but does not invalidate
field-name citations. The verified-at-SHA annotation (column B) lets
readers cross-reference the row at the specific commit it was audited
against; the risk register is expected to re-verify on audit refresh
(SPRINT.md §Scope item 3 — audit refresh cadence).

---

## Appendix A — Notes on row counts vs Phase 3a estimate

Phase 3a estimated ~75–100 rows total. The Wave-1 draft lands at:

- §4: 22 rows (4 top-level + 7 SchedulerState + 11 ModuleState); Phase 3a est ~18 ✅ within bound
- §4a (Wave-1 late extension, Grep 2 + thread_local overlay): 13 primary rows + 6 completeness-overlay rows = **19 rows**. Not in Phase 3a estimate (Grep-2 denominator was added after Phase 3a).
- §5: 7 rows (worker-owned = 0; reachability = 7); Phase 3a est ~15–20 — **below estimate** because the per-reader-class expansions collapse at single-invariant sites and cross-references avoid re-enumerating SharedState fields
- §6: 21 rows (17 SharedState fields + 1 Arc clone + 2 REPL-invariant + 1 dual-store); Phase 3a est ~35–45 — **below estimate** for the same collapse-via-cross-reference reason
- §7: 3 rows (2 atomics + 1 mutex); Phase 3a est ~4–6 — within bound if `OnceLock` site is added in Wave 1 part 2 per §7.3 default recommendation
- §4b (Wave-1c reachability-from-worker extension): **6 rows** (3 statics + 2 ISA-sharing + 1 display reader class; §4b.4 and §4b.5 added no rows, only verification findings). Not in Phase 3a estimate (reachability-from-worker denominator was added in Wave-1c).

Total §4–§7 (Grep-1 surface): 53 rows. §4a (Grep-2 + thread_local
overlay, Wave-1 late extension): 19 rows. §4b (Wave-1c extension): 6
rows. If Wave-1 gate extends §7
to cover `io_trace.rs`, add ~3 rows → 56 (Grep-1 total).
`/typecheck`'s §8 contributed ~6 rows. **Document total: ~84 rows
(Grep-1 53 + §4a 19 + §4b 6 + §8 6)** — within Phase 3a's ~75–100
estimate once the Grep-2 overlay and Wave-1c reachability-from-worker
extension are counted. Without §4a the count was 59; §4a was the
Wave-1-late extension, §4b the Wave-1c extension. Coverage criterion
still met: 100% of fields matching the combined Grep-1 + Grep-2 +
Grep-3 + reachability-from-worker denominators.
