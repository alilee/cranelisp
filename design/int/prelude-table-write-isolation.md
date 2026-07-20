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
> **Status: DESIGN, pre-implementation.** The ship gate is STRUCTURAL, not a
> stable-RED flip (the sanctioned no-stable-RED exception stands — 0604 §"Why a
> FIXME despite the no-FIXME rule").

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
narrowing):**

| Writer seam | Destination table | Public entries? | Disposition |
|---|---|---|---|
| `imports.rs::install_exports` (`Visibility::Public`) | the exporting module (explicit `current_module`) | **yes** — re-export edges | **route through chokepoint** |
| `imports.rs::install_imports` (`Visibility::Private`) | the importing module (explicit `current_module`) | no (Private) | private-only — legal-skip (records rationale) |
| `imports.rs::insert_detecting_ambiguity` (poison consumer) | current module | reads/marks existing | **CORRECT — DO NOT TOUCH** (0604 refers_to; the §8.6.5 consumer) |
| `cluster.rs::insert_cluster` (staging→live commit gate) | the cluster's own module | yes (public defs) | **route through chokepoint** |
| the Code-install sites | mutate existing entries only | no new public entry | legal-skip |
| `process_form/cache_restore.rs` | restored module | yes | off the recipe path (`--no-cache`); disposition per its own guard |
| `worker::inject_prelude_if_needed` / `install_module_session_env` | session-side maps (`prelude_fallback`, aliases) — **not** a symbol-table public entry | n/a | legal-skip (§3.4 writers = bit + env, not table entries) |

The census's job is to prove the set is **closed** — that no *other* foreground
seam can insert a public table entry. The prime suspects §3 tells the census where
to look hardest.

### 2.2 The ONE chokepoint — terminal-table freeze / export-closure gate

Consolidate the public-insert seams onto **one guarded chokepoint** carrying the
invariant:

> **A module that has reached terminal never accepts a new public entry outside
> its declared export closure.**

At that chokepoint, **promote the S113 `assert_prelude_closure` check from a
prelude-only `debug_assert!` to an unconditional, diagnosed, generalized error**
(trust-boundary tier, `safety-invariants.md` §2): the check fires in **every**
build (not just debug), for **any** terminal module (not just `prelude`), and a
firing **names its caller in production** with the module, name, source edge, and
the closure it breached — turning the next occurrence anywhere into a located
defect instead of another quiet-environment hunt. The check keys on the write's
**settled source** (Principle 26 — read the edge, not a name heuristic; the
existing `prelude_write_is_closure_valid` shape): a re-export/import edge is
closure-valid iff its source module genuinely provides the name publicly; a
module's own public definition is exported by §8.4; an *unknown* source is
permitted (the diagnostic must never false-fire the build).

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

Per `/qa` (`tests/plan/s114-test-plan.md` §4.2 + 0604 §Acceptance):

1. **Chokepoint unit test** (METHOD §2.2, fail-on-revert): an attempted
   out-of-closure public insert into a terminal table is **rejected + diagnosed**.
2. **Census table in the change-set** — every foreground writer dispositioned
   (routes-through / named legal-skip).
3. **≥25× deterministic-recipe sweep** vs the real stdlib (`--run` + REPL) —
   **behavioural no-regression** (the pre-fix baseline is 0-fire in this
   environment, so the sweep guards against regression, it is **not** the defect
   guard; the fail-on-revert guard rides the chokepoint unit test).
4. **The two GREEN twins hold**
   (`tests/spec_08_prelude_outer_scope.rs::super_import_wrapper_over_specific_prelude_compiles_clean`
   — the correct pole, a free tripwire that reddens if the phantom ever turns
   deterministic; and the `_collides_…_neg` poison twin — the poison stays
   spec-correct).
5. **This doc records the contract** (done); FIXME 0604 retires when the
   chokepoint + census + guards land. Any interim firing anywhere names its seam
   via the promoted diagnosed error and narrows the fix to it.

## 5. Principles cited

- **Principle 21** — the multi-writer actors + the missing "public write is
  in-closure" function named before the chokepoint mechanism (§1).
- **Principle 26** — the closure check reads the write's settled source edge, not
  a name heuristic (§2.2).
- **Principle 18** — the invariant is enforced structurally at one chokepoint
  every writer routes through (the greppable structural guard: a public-insert
  seam bypassing the chokepoint is a `/review` finding), not by per-interleaving
  patches.
- **Principle 7** — one chokepoint, one closure check (the S113 rider consolidates
  onto it; the poison consumer stays its single correct self).

## 6. Cross-references

- `design/arch/fixmes/0604-*.md` — the defect, the re-scope to foreground, and
  `/qa`'s plan of record.
- `src/imports.rs` (`install_exports`/`install_imports`/`assert_prelude_closure`/
  `prelude_write_is_closure_valid`/`insert_detecting_ambiguity`) — the writer +
  rider + poison consumer seams.
- `src/cluster.rs` (`insert_cluster`) — the staging→live commit writer.
- `design/int/index-worker-isolation.md` — the *background* index-feed isolation
  (S110); this doc is the foreground companion.
- `design/int/heisenbug-race-closure.md` / `signature-body-prepass.md` — the
  S61→S93 isolation-by-construction precedent.
- `design/arch/safety-invariants.md` §2 (trust-boundary diagnosed-error tier) +
  R7 register row — the assertion tier the promotion targets.
- `design/arch/prelude-import-convergence.md` §3.4 — the writer-census seed.
- `tests/plan/s114-test-plan.md` §4.2 + `tests/spec_08_prelude_outer_scope.rs` —
  the acceptance frame + the two GREEN twins.
