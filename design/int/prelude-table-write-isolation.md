# Foreground public-write isolation — the prelude-table write chokepoint (S114 Track C, FIXME 0604)

> Subordinate topic doc, cited from `design/int/int.md`. Owned by `/design`(int).
> Authored S114 Phase 3 to satisfy the FIXME 0604 routing ("/design(int) records
> the isolation contract") and `/qa`'s S114 plan of record
> (`design/arch/fixmes/0604-*.md` §"/qa S114 Phase-3 plan of record" +
> `tests/plan/s114-test-plan.md` §4.2). SPRINT.md §Scope-C — **SHIPS this sprint**
> (user approved Phase 1). Companion to `index-worker-isolation.md` (the
> *background* index-feed half, S110); this doc is the *foreground*
> concurrent-compile half the 0604 re-scope (FIXME §S110) moved attribution to.
>
> **Status: LANDED-AND-CORRECTING (S115 Track B).** The chokepoint
> (`check_terminal_closure`) + census + MODULE_TRACE landed S114 W5
> (`58ac8e46`), but with a **provider-existence** predicate that is
> structurally BLIND to the live phantom (see §2.2 — /qa S114 re-attribution +
> /arch Phase-2 §4). S115 corrects the predicate to **declared-export closure**,
> dispositions the **one missed census row** (`commit_staging_to_live`), and
> lands the /qa synthesized-trigger unit test. The ship gate stays STRUCTURAL,
> not a stable-RED flip (the sanctioned no-stable-RED exception stands — 0604
> §"Why a FIXME despite the no-FIXME rule"); writer identification is
> DESIRED-not-required for 0604 to retire (the re-based plan, 0604 §"/qa S114
> Phase-6b re-base").

## 0. The defect, in one line

A **foreground** concurrent-compile writer intermittently inserts a **phantom
public `bit-and → primitives/bit-and` binding into the live `prelude` module's
symbol table**, outside prelude's declared export closure. A later legitimate
`(import [super [bit-and]])` then meets two distinct terminals and the §8.6.5
peer-poison fires **spec-correctly** — *the poison is correct; the bug is the
phantom WRITE upstream.* Fingerprint: only `bit-and` leaks (never the
identically-shaped `bit-or`/`bit-xor`), scheduling-dependent (16/16 in one
environment, 0 in others) — a concurrent mis-attribution, not deterministic logic
(class `shared-state-write-race`).

## 1. The actors and the function between them (Principle 21)

The foreground concurrent-compile path has **multiple writers** into module
symbol tables running at once: the eval thread plus priority/nice pool workers,
building `num.bits` + `num.bits.test` + `prelude` + prelude's ~13 re-exported
domain modules concurrently. Each can insert a **public** entry into *some*
module's live table. The correctness the recipe rests on today is **not
isolation** — it is that every such write targets the *right* table and stays
inside that module's export closure. That correctness is unasserted, so one
mis-targeted write (or a materialized fallback hit gone public) reaches
`prelude`'s table and is never caught until the poison fires N steps later.

The **missing function**: *"a public binding entering a module's live table is
inside that module's export closure — checked at ONE chokepoint every foreground
writer routes through."* Today the check exists only as an S113 observability
rider (`imports.rs::assert_prelude_closure`, `debug_assert!` + `MODULE_TRACE`),
called *beside* insertions, prelude-only, and non-fatal in release.

## 2. The isolation contract (the structural ship gate)

Two deliverables, per `/qa`'s plan of record. Neither is a per-interleaving patch;
the cure is isolation **by construction** (the S61→S93 precedent — see
`heisenbug-race-closure.md` → `signature-body-prepass.md`).

### 2.1 Foreground writer census (the 0660 enumeration discipline)

Enumerate **every** seam on the foreground concurrent-compile path that can insert
a **public** entry into a module's live symbol table. Each writer either **routes
through the single chokepoint (§2.2)** or carries a **named legal-skip** with its
rationale. The census table lands **in the change-set** (every writer
dispositioned — the acceptance instrument, `tests/plan/s114-test-plan.md` §4.2).

**Seed (from `prelude-import-convergence.md` §3.4 + the PLAN §S109 static
narrowing).** As-built dispositions verified at HEAD (`5ba28de8`):

| Writer seam | Destination table | Public entries? | Disposition |
|---|---|---|---|
| `imports.rs::install_exports` (`Visibility::Public`) | the exporting module (explicit `current_module`) | **yes** — re-export edges | **routes** (`imports.rs:182`) |
| `imports.rs::install_imports` (`Visibility::Private`) | the importing module (explicit `current_module`) | no (Private) | routes (`imports.rs:116`; no-op — `!is_public()`) |
| `imports.rs::insert_detecting_ambiguity` (poison consumer) | current module | reads/marks existing | **CORRECT — DO NOT TOUCH** (0604 refers_to; the §8.6.5 consumer) |
| `cluster.rs::insert_cluster` (Wave-3a-β scaffold commit) | the cluster's own module | yes (public defs) | routes (`cluster.rs:337`) — **but normally empty**: `process_cluster` commits through `worker::commit_staging_to_live`, so `insert_cluster`'s `entries` loop is a no-op on the live path (see the row below) |
| **`worker::commit_staging_to_live`** (the REAL staging→live commit) | the cluster's own module (`worker.rs:439`; `live.insert` `:513`) | **yes** — every public Def AND re-export edge | **MISSED at S114** — the census claimed closure while this seam bypasses the gate. **S115: route it** (§2.4) |
| `process_form/form_dispatch::register_macro_in_module` (defmacro reg) | current module | yes (macro `Def`) | routes (`form_dispatch.rs:395`) — a macro `Def` is non-`Import` → own-def arm → Ok with **no map read**, guard-safe under the held `get_mut` (`:360`) |
| the Code-install sites | mutate existing entries only | no new public entry | legal-skip |
| `process_form/cache_restore.rs` | restored module | yes | off the recipe path (`--no-cache`); disposition per its own guard |
| `worker::inject_prelude_if_needed` / `install_module_session_env` | session-side maps (`prelude_fallback`, aliases) — **not** a symbol-table public entry | n/a | legal-skip (§3.4 writers = bit + env, not table entries) |

The census's job is to prove the set is **closed** — that no *other* foreground
seam can insert a public table entry. The S114 census **missed
`commit_staging_to_live`**: `insert_cluster` (the seam the S114 census named as
the commit gate) is a Wave-3a-β scaffold whose per-entry loop is normally empty —
the live commit path is `worker::process_cluster_once` → `commit_staging_to_live`
(`worker.rs:307`), which drains staging under a `get_mut` guard and never routed
through the gate. That is the seam the phantom evidence names (0604 refers_to;
0698 finding 2). §2.4 dispositions it. The prime suspects §3 tell the census where
to look hardest.

### 2.2 The ONE chokepoint — terminal-table export-closure gate (LANDED; predicate CORRECTED S115)

Consolidate the public-insert seams onto **one guarded chokepoint**
(`imports.rs::check_terminal_closure`, landed S114) carrying the invariant:

> **A module never accepts a new public entry outside its declared export
> closure.**

The chokepoint is an **unconditional, diagnosed, generalized error**
(trust-boundary tier, `safety-invariants.md` §2, /arch Phase-2 §4 sub-form
ruling): it fires in **every** build (not just debug), for **any** module (not
just `prelude`), returns a `CranelispError::TypeError` that **self-identifies as
an internal R7 invariant breach naming the seam** (never mistakable for a user
diagnostic — a session abort would kill a REPL on a defect the user cannot act
on), and a firing **names its caller in production** with the module, name, and
source edge. `MODULE_TRACE` emits the same at the seam (`imports.rs:336`).

#### The false premise the S114 predicate rests on (CORRECTED)

The landed predicate `write_is_closure_valid` (`imports.rs:357`) and its
prelude-only sibling `prelude_write_is_closure_valid` (`imports.rs:245`) are
**provider-existence** shaped: a re-export/import edge is valid iff its
**source** module provides the name (`src.get(source.symbol).is_some()`). Their
rationale comments assert *"`bit-and` is homed in num.bits, **absent from
primitives**"* — this clause is **FALSE**. `bit-and` **IS a bundled public
primitive** (`crates/cranelisp-primitives/src/lib.rs:412`; homed in `num.bits`
only as a wrapper `(defn bit-and … (primitives/bit-and …))`,
`stdlib/num/bits.cl:58`). Consequently the phantom
`bit-and → primitives/bit-and` names a **genuine provider** — provider-existence
returns `true` and **passes the phantom by construction** (/qa S114
re-attribution point 1; /arch Phase-2 §4). *Any provider-existence check is
structurally blind to this defect.*

#### The corrected predicate — declared-export closure keyed on the DESTINATION

The distinguishing fact: `bit-and` is **outside prelude's declared export
closure**. `stdlib/prelude.cl` re-exports a **specific** primitive set —
`(export [primitives [Int Bool Float String]])` (line 52), a curated list, **not
a glob** — plus its ~13 domain-module re-exports; `bit-and` is in **none** of
them. The correct question is not *"does the source provide the name?"* but
*"does the **destination** module `M` **declare** this public name in its own
export surface?"*

> **`check_terminal_closure(M, entry)`** — a **public** entry is closure-valid
> iff:
> - the entry is `M`'s **own definition** (non-`Import`: `Def`/`TypeDef`/… — a
>   public def is exported by §8.4) → **Ok with NO map read**; **or**
> - the entry is a public re-export `Import` whose **name ∈ D(M)**, where **D(M)
>   is `M`'s declared-export name-set** — the union of the names `M`'s own
>   `(export …)` specs bring in. `name ∉ D(M)` (the phantom shape) → **rejected +
>   diagnosed**.
> - `D(M)` **unknown/not-yet-recorded** for `M` → **permit** (the diagnostic must
>   never false-fire — a foreign write racing ahead of `M`'s own export
>   processing is permitted; the guard catches it once `D(M)` is recorded).

This is exactly the /qa synthesized-trigger shape (`tests/plan/s115-test-plan.md`
§3.1): **provides-name-but-outside-declared-exports** — a public `Import` whose
`source` genuinely provides the name (so provider-existence passes) but whose
name is **not** in `D(M)` (so declared-export closure rejects). The existing
chokepoint unit test cannot guard this — its injected source lacks the name, so
it passes both predicates (the /qa binding finding); the synthesized trigger must
inject an out-of-closure name *that a real source provides*.

#### `D(M)`'s data source + the deadlock hazard (Principle 26 / 18)

`D(M)` is the **authoritative declared-export set** — computed from `M`'s
`(export …)` **specs** (the `ExportSpec` names at the `install_exports` seam,
which are entry-independent, so the check is not circular against the entries it
validates), captured **session-side** keyed by `M`. This is a **new
int-internal `SharedState` field** (`declared_exports: DashMap<ModuleFullPath,
HashSet<Symbol>>`, unserialized/recomputed-per-session — modelled on
`prelude_fallback`); **no `cranelisp-types` edit, no schema/public-api impact**
(/arch Phase-2 §7 confirms none planned). `/dev` populates it at the
export-processing seam from `ExportSpec` names; if `/dev` finds a cleaner
session-side source for the same set, the **contract** (`name ∈ M`'s declared
export surface) is what binds, not the storage.

**The deadlock hazard is honored by two independent margins** (0698 forward
hazard; /arch Phase-2 §4 "closure PRECOMPUTED"):

1. `D(M)` lives in a **separate** `DashMap` from `symbol_tables`, so reading it
   never re-enters the `symbol_tables` shard a `get_mut` guard holds — the exact
   re-entrancy that a *"read `M`'s own live exports"* implementation would
   deadlock on at `register_macro_in_module` (`form_dispatch.rs:395` runs under
   the `get_mut` at `:360`).
2. The **own-def arm reads no map at all** — a macro/def `Def` short-circuits to
   Ok, so `register_macro_in_module` stays guard-safe by construction even for
   the corrected predicate (it never reaches the `Import` arm).
3. For `commit_staging_to_live` (§2.4), the `D(M)` lookup is **precomputed
   before** `symbol_tables.get_mut(module)` and the borrowed set (or a membership
   closure) is passed into the guarded drain loop — no session-map read under the
   guard, per the /arch directive.

The chokepoint is **isolation by construction**: a mis-targeted or materialized
phantom write is *rejected at the seam*, so no phantom can ever reach a live table
— the poison downstream then has only genuine terminals to compare.

### 2.3 What must NOT be touched

- **`insert_detecting_ambiguity`** (`imports.rs::insert_detecting_ambiguity`,
  ~L547-560) — the §8.6.5 distinct-terminal poison *consumer* is **correct**. It
  is the *symptom* surface, not the *cause*. Weakening it would "solve" the visible
  error by hiding a real spec-correct ambiguity (the negative twin
  `super_import_wrapper_collides_when_prelude_globs_primitive_neg` fences exactly
  this — do not weaken the poison).
- The `concurrency_capacity` threshold defect stays a **SEPARATE** defect
  (effect-concurrency track) — not folded here (0604 §Guard/verify notes).

### 2.4 The missed census row — routing `commit_staging_to_live` (S115 disposition)

`worker::commit_staging_to_live` (`worker.rs:439`) is the **live** staging→live
commit — every foreground cluster (eval thread + pool workers) commits its
public Defs and re-export edges here, draining `staging.symbols` into
`live.insert` (`:513`) under the `symbol_tables.get_mut(module)` guard (`:483`).
The S114 census claimed closure but this seam **bypasses `check_terminal_closure`
entirely**; it is the very writer the phantom evidence names (0604 refers_to;
0698 finding 2). **Disposition: ROUTE it** — the only census row that is neither
already-routed nor a legal-skip.

**Shape (deadlock-safe, precompute-before-guard):**

1. **Before** `symbol_tables.get_mut(module)` (`:483`), look up `D(module)` once
   from the session-side `declared_exports` map (§2.2) — a read of a **separate**
   `DashMap`, so it is safe even if it ran under the guard; precomputing it first
   honors the /arch directive uniformly and keeps the drain loop guard-clean.
2. Inside the drain loop, **before `live.insert(name, entry)`** (`:513`), call
   `check_terminal_closure(symbol_tables, module, &name, &entry, span, &d_module)`
   for each staged entry. A public re-export `Import` whose name ∉ `D(module)`
   returns the diagnosed error; `commit_staging_to_live` already returns
   `Result<…, CranelispError>`, so the rejection propagates through the existing
   error path with nothing committed.
3. `commit_staging_to_live` commits `module`'s **own** cluster, so `D(module)`
   (recorded from that same cluster's export specs) contains every legitimate
   re-export edge → they pass; only a mis-targeted/materialized phantom whose
   name is absent from `module`'s declared exports rejects. A foreign write
   mis-targeting a `module` whose `D` is already recorded is rejected; one racing
   ahead of `D(module)`'s recording hits the unknown-permit arm (never
   false-fires) — and the landed `MODULE_TRACE`/diagnostic still names the seam
   if it ever fires.

**Span:** the staged commit has no per-entry user span (drained from staging);
use `Span::SYNTHETIC` (as `insert_cluster` and `register_macro_in_module`
already do at their gate calls) — the diagnostic self-identifies as an internal
R7 breach, so a synthetic span is correct (it is never a user-actionable
location).

**Greppable structural guard (Principle 18):** after this lands, a public-insert
seam that bypasses `check_terminal_closure` is a `/review` finding — the census
table (in `imports.rs` and here) is closed, `commit_staging_to_live` included.

## 3. Prime suspects (where the census looks first)

1. **A materialized prelude fallback going public.** §8.6.4 says the
   materialise-or-not of a prelude transparent-fallback hit is zero-semantic-weight
   — but ONLY while such a materialization is never public. A concurrent worker
   materializing a fallback hit as a **public** table entry **is** the phantom.
   (`prelude-is-implicit-import-one-fallback-no-outer-scope` — the fallback is one
   transparent lookup, never a table write.)
2. **An import-direction write landing in the wrong table** during the concurrent
   build of prelude's ~13-module re-export closure — whichever symbol's install
   interleaves is the one that leaks (the `bit-and`-only, not-`bit-or` fingerprint
   = interleaving, not logic).

## 4. Acceptance (the ship gate — no flip, structural)

Per `/qa` (`tests/plan/s115-test-plan.md` §3.1 + 0604 §"/qa S114 Phase-6b
re-base"):

1. **Synthesized-trigger chokepoint unit test** (METHOD §2.2, fail-on-revert,
   interleaving-independent): inject a public re-export `Import` whose `source`
   **provides** the name but whose name is **outside** `D(M)`
   (provides-name-but-outside-declared-exports) → assert the diagnosed error. The
   *existing* chokepoint unit test cannot guard the corrected predicate (its
   injected source lacks the name — it passes both predicates; the /qa binding
   finding).
2. **Census table in the change-set** — every foreground writer dispositioned,
   **`commit_staging_to_live` included** (§2.4).
3. **Corrected predicate**: provider-existence → declared-export closure
   (`D(M)`); the `prelude_write_is_closure_valid` / `write_is_closure_valid`
   rationale comments corrected (bit-and IS a primitive — the falsified-premise
   rider, /arch Phase-2 §4 revision 2; paired with the /testing fixture-comment
   correction on `check_terminal_closure_rejects_out_of_closure_public_write`).
4. **≥25× deterministic-recipe sweep** vs the real stdlib (`--run` + REPL) —
   **behavioural no-regression** (the pre-fix baseline is 0-fire in this
   environment; the fail-on-revert guard is the synthesized trigger, NOT the
   sweep). One time-boxed load-amplified re-induction attempt, abandoned without
   prejudice if quiet.
5. **The two GREEN twins hold**
   (`tests/spec_08_prelude_outer_scope.rs::super_import_wrapper_over_specific_prelude_compiles_clean`
   — the correct pole, a free tripwire that reddens if the phantom ever turns
   deterministic; and the `_collides_…_neg` poison twin — the poison stays
   spec-correct).
6. **This doc records the contract** (done — §2.2/§2.4). FIXME 0604 retires when
   the corrected predicate + closed census (incl. `commit_staging_to_live`) +
   synthesized-trigger guard land; **writer identification is DESIRED, not
   required** (the re-based plan). Any interim firing anywhere names its seam via
   the diagnosed error and narrows the fix to it.

## 5. Principles cited

- **Principle 21** — the multi-writer actors + the missing "public write is
  in-closure" function named before the chokepoint mechanism (§1).
- **Principle 26** — the closure check reads settled state, not a name heuristic:
  the DESTINATION module's declared-export surface `D(M)`, recorded from its own
  `(export …)` specs (§2.2) — NOT the provider-existence heuristic the S114
  predicate mistook for it.
- **Principle 18** — the invariant is enforced structurally at one chokepoint
  every writer routes through (the greppable structural guard: a public-insert
  seam bypassing the chokepoint is a `/review` finding), not by per-interleaving
  patches.
- **Principle 7** — one chokepoint, one closure check (the S113 rider consolidates
  onto it; the poison consumer stays its single correct self).

## 6. Cross-references

- `design/arch/fixmes/0604-*.md` — the defect, the re-scope to foreground, and
  `/qa`'s plan of record.
- `src/imports.rs` (`check_terminal_closure`:322 / `write_is_closure_valid`:357 —
  the landed chokepoint + provider-existence predicate to correct;
  `install_exports`:182 / `install_imports`:116 — routed writers;
  `assert_prelude_closure`:217 / `prelude_write_is_closure_valid`:245 — the S113
  rider (falsified comment at :251); `insert_detecting_ambiguity` — the §8.6.5
  poison consumer, DO NOT TOUCH).
- `src/worker.rs` (`commit_staging_to_live`:439, `live.insert`:513, `get_mut`:483)
  — the REAL staging→live commit, the missed census row §2.4 routes.
- `src/cluster.rs` (`insert_cluster`:337) — the Wave-3a-β scaffold gate call
  (normally-empty entries loop).
- `crates/cranelisp-primitives/src/lib.rs:412` — `bit-and` IS a bundled
  primitive (the falsified-premise evidence).
- `tests/plan/s115-test-plan.md` §3.1 — the synthesized-trigger binding finding.
- `design/int/index-worker-isolation.md` — the *background* index-feed isolation
  (S110); this doc is the foreground companion.
- `design/int/heisenbug-race-closure.md` / `signature-body-prepass.md` — the
  S61→S93 isolation-by-construction precedent.
- `design/arch/safety-invariants.md` §2 (trust-boundary diagnosed-error tier) +
  R7 register row — the assertion tier the promotion targets.
- `design/arch/prelude-import-convergence.md` §3.4 — the writer-census seed.
- `tests/plan/s114-test-plan.md` §4.2 + `tests/spec_08_prelude_outer_scope.rs` —
  the acceptance frame + the two GREEN twins.
