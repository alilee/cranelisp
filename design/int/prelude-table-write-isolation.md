# Foreground public-write isolation — the prelude-table write chokepoint (S114 Track C, FIXME 0604)

> Subordinate topic doc, cited from `design/int/int.md`. Owned by `/design`(int).
> Authored S114 Phase 3 to satisfy the FIXME 0604 routing ("/design(int) records
> the isolation contract") and `/qa`'s S114 plan of record
> (S114 §4.2, retained in Git at `7b1220c7`). Companion to `index-worker-isolation.md` (the
> *background* index-feed half, S110); this doc is the *foreground*
> concurrent-compile half established by the S110 re-scope.
>
> **Status: delivered and closed.**
> The current candidate contract, complete route census, three session-init
> dispositions and corrected bootstrap facts are recorded in §§2.1–2.4. The
> retired 0604/0740/0793/0818 group now has its current closure and historical
> attribution limits in `design/arch/bounded-contexts.md` §6. This topic doc
> remains the detailed Binary/int mechanism carrier.
>
> **S121 correction — current design.** The lifecycle migration separates a
> terminal binding from its local name candidates. The binding-shaped
> `check_terminal_closure(M, binding, …)` can no longer observe a re-export and
> has become a hardcoded no-op; it is deleted, together with
> `write_is_closure_valid` and their binding-loop call sites. The ONE live gate
> is candidate-shaped:
>
> ```text
> check_exposed_candidate_closure(destination, local_name, canonical_source,
>                        visibility, span, declared_exports)
> ```
>
> It admits private candidates, same-module candidates, and a public
> cross-module candidate whose local name is in `D(destination)` (or whose `D`
> is not yet known); it rejects the remaining public cross-module exposure.
> `install_imports`, `install_exports`, prepared publication and the retained
> staging-publication seam route every candidate exposure through it. Own
> definitions are exported by §8.4 and are not falsely described as having
> passed a candidate gate. Bootstrap's proof enumerates name candidates, not
> bindings, and includes a public cross-module/outside-`D(M)` negative. The
> S114/S115 diagnosis below remains provenance; this paragraph and §2.2's
> corrected contract govern the current representation.
>
> Historical status below.
>
> **Status: LANDED-AND-CORRECTING (S115 Track B).** The chokepoint
> (`check_terminal_closure`) + census + MODULE_TRACE landed S114 W5
> (`58ac8e46`), but with a **provider-existence** predicate that is
> structurally BLIND to the live phantom (see §2.2 — /qa S114 re-attribution +
> /arch Phase-2 §4). S115 corrects the predicate to **declared-export closure**,
> dispositions the **one missed census row** (`commit_staging_to_live`), and
> lands the /qa synthesized-trigger unit test. The ship gate stays STRUCTURAL,
> not a stable-RED flip (the historical no-stable-RED exception stands);
> writer identification was desired rather than required for structural
> closure.

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

The **historical missing function**: *"a public binding entering a module's live table is
inside that module's export closure — checked at ONE chokepoint every foreground
writer routes through."* Today the check exists only as an S113 observability
rider (historical `imports.rs::assert_prelude_closure`, `debug_assert!` + `MODULE_TRACE`),
called *beside* insertions, prelude-only, and non-fatal in release.

## 2. The isolation contract (the structural ship gate)

Two deliverables, per `/qa`'s plan of record. Neither is a per-interleaving patch;
the cure is isolation **by construction** (the S61→S93 precedent — see
`heisenbug-race-closure.md` → `signature-body-prepass.md`).

### 2.1 Historical foreground-writer census (S114/S115 provenance)

The tables in this subsection record the binding-era investigation. They remain
useful provenance for the missed writer, but they are not the current routing
contract: the S121 candidate census is §2.4, and a binding "legal-skip" is no
substitute for checking a `NameCandidate` exposure.

**Seed (from `prelude-import-convergence.md` §3.4 + the PLAN §S109 static
narrowing).** As-built dispositions verified at HEAD (`5ba28de8`):

| Writer seam | Destination table | Public entries? | Disposition |
|---|---|---|---|
| `imports.rs::install_exports` (`Visibility::Public`) | the exporting module (explicit `current_module`) | **yes** — re-export edges | **routes** (`imports.rs:182`) |
| `imports.rs::install_imports` (`Visibility::Private`) | the importing module (explicit `current_module`) | no (Private) | routes (`imports.rs:116`; no-op — `!is_public()`) |
| historical `imports.rs::insert_detecting_ambiguity` (poison consumer) | current module | read/marked existing bindings | superseded by candidate preservation plus use-site selection |
| `cluster.rs::insert_cluster` (Wave-3a-β scaffold commit) | the cluster's own module | yes (public defs) | routes (`cluster.rs:337`) — **but normally empty**: `process_cluster` commits through `worker::commit_staging_to_live`, so `insert_cluster`'s `entries` loop is a no-op on the live path (see the row below) |
| **`worker::commit_staging_to_live`** (the REAL staging→live commit) | the cluster's own module (`worker.rs:439`; `live.insert` `:513`) | **yes** — every public Def AND re-export edge | **MISSED at S114** — the census claimed closure while this seam bypasses the gate. **S115: route it** (§2.4) |
| historical `process_form/form_dispatch::register_macro_in_module` (defmacro reg) | current module | yes (macro `Def`) | binding-era route, superseded by source-ordered macro checkpoint publication |
| the Code-install sites | mutate existing entries only | no new public entry | legal-skip |
| `process_form/cache_restore.rs` | restored module | yes | off the recipe path (`--no-cache`); disposition per its own guard |
| `worker::inject_prelude_if_needed` / `install_module_session_env` | session-side maps (`prelude_fallback`, aliases) — **not** a symbol-table public entry | n/a | legal-skip (§3.4 writers = bit + env, not table entries) |

**The three session-init seams (S121, FIXMEs 0740 + 0793).** The census above
enumerates the *foreground concurrent-compile* path. Session init is a distinct
regime — single-threaded, before any worker is spawned — and its seams were
neither routed nor recorded, so the §2.4 structural grep resolved to an argument
rather than a disposition. They are named here, with the scope boundary stated
explicitly so a future reader does not have to re-derive it:

> **Scope boundary.** Session-init table construction (`bootstrap.rs`,
> `session_v4/lifecycle.rs`) and platform-DLL load orchestration
> (`platform.rs`) are outside the foreground concurrent-compile path. Init runs
> once, single-threaded, before the worker pool exists; DLL load is an
> orchestration act on a synthetic `platform.<name>` module. Neither can produce
> the phantom this gate exists to catch. They carry dispositions anyway, because
> a closure claim a grep can falsify is exactly the failure the census discipline
> prevents.

| Writer seam | Destination table | Public entries? | Disposition |
|---|---|---|---|
| `bootstrap.rs::mount_synthetic_modules` (`src/bootstrap.rs:240`) | `root`, `primitives`, `macros`, `Option`, `IO`, `Trace` | **yes** — own definitions, plus ONE intra-module public `Import` | **named legal-skip, ASSERTED**. Own-def and intra-module-self-alias arms only; the skip carries a detection proof (below) |
| `session_v4/lifecycle.rs` `PRIMITIVES_TABLE` mount (`:268-274`) | `primitives` | **yes** — a whole-table clone of `cranelisp_primitives::PRIMITIVES_TABLE` | **named legal-skip**. A whole-**table** mount, not an entry insert; every entry is `primitives`' own definition (own-def arm), installed at init before `mount_synthetic_modules` (`:286`) and before any worker spawns |
| `platform.rs::register_platform_in_tc` | `platform.<name>` | **yes** — own-def `PlatformEffect` | **named legal-skip**. `SymbolTable::install_platform` installs the declaration in its canonical module; it creates no public cross-module exposure for the candidate gate to adjudicate |

**Two factual corrections, recorded so they stop propagating.** FIXME 0740
characterised `bootstrap.rs`'s four `Int/Bool/Float/String → primitives/<name>`
edges into the live `macros` table as cross-module PUBLIC re-exports — "the exact
phantom shape". **That is false.** Those edges carry `Visibility::Private`
(`src/bootstrap.rs`), so `check_exposed_candidate_closure`'s private-candidate
clause returns `Ok` before any other arm is consulted: they are not public writes at
all. Bootstrap's one genuinely public `Import` is `Bind → primitives/IO.Bind`
(`src/bootstrap.rs:849-858`), whose source module is `primitives` — the
destination — so it takes the **intra-module self-alias** arm with no `D` read.
Four records repeated the "exact phantom shape" wording without opening the file;
this row states the Private ground so a fifth does not.

**Current bootstrap proof.** The S121 replacement iterates
`all_name_candidates`, asserts that the sweep is non-empty, sends every
candidate through §2.2, and injects a public cross-module candidate outside
`D(M)` that must reject. Iterating bindings or starting from an empty table is
not acceptable evidence for candidate exposure.

The census's job is to prove the set is **closed** — that no *other* foreground
seam can insert a public table entry. The S114 census **missed
`commit_staging_to_live`**: `insert_cluster` (the seam the S114 census named as
the commit gate) is a Wave-3a-β scaffold whose per-entry loop is normally empty —
the live commit path is `worker::process_cluster_once` → `commit_staging_to_live`
(`worker.rs:307`), which drains staging under a `get_mut` guard and never routed
through the gate. That is the seam the historical phantom evidence named.
Section 2.4 dispositions it. The prime suspects §3 tell the census where
to look hardest.

### 2.2 The ONE chokepoint — candidate export-closure gate

Consolidate public candidate-exposure seams onto **one guarded chokepoint**
(`imports.rs::check_exposed_candidate_closure`) carrying the invariant:

> **A module never accepts a public cross-module name candidate outside its
> declared export closure.**

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
primitive** (`crates/cranelisp-primitives/src/declarations.rs:314`; homed in `num.bits`
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

> **`check_exposed_candidate_closure(M, local, source, visibility, D(M))`** — a name
> candidate is closure-valid iff it is private, its canonical source is in
> `M`, its public local name belongs to `D(M)`, or `D(M)` is not yet known.
> Otherwise the public cross-module exposure is rejected and diagnosed.

The lifecycle binding is not an input: own definitions are exported by §8.4,
while cross-module exposure lives only in `NameCandidate`. A binding-shaped
gate or a second predicate over bindings is therefore untruthful and must not
be reintroduced.

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
2. Every publication route obtains `D(M)` **before** acquiring the destination
   table's write guard, then passes that value to the candidate-shaped gate.
   Same-module and private candidates short-circuit from their supplied facts;
   the gate never re-enters either session map.

The chokepoint is **isolation by construction**: a mis-targeted or materialized
phantom write is *rejected at the seam*, so no phantom can ever reach a live table
— the poison downstream then has only genuine terminals to compare.

### 2.3 What must NOT be touched

- **Candidate coexistence and use-site selection**
  (`imports.rs::install_candidates`) — importing distinct canonical sources is
  permitted. Typecheck filters those candidates by the use-site constraints and
  reports ambiguity only when more than one viable candidate remains; do not
  restore the former import-time poison to pre-empt that decision.
- The `concurrency_capacity` threshold defect stays a **SEPARATE** defect
  (effect-concurrency track) — not folded into this candidate-isolation design.

### 2.4 Publication routes candidates, not bindings (S121 correction)

Prepared publication and the retained legacy staging-publication seam validate
the complete `all_name_candidates` batch before mutating the destination table
or publishing a GOT change. `install_imports`, `install_exports`, and bootstrap
birth do the same at their candidate-exposure seams. Each route obtains `D(M)`
before its module write guard and calls the one §2.2 gate with the candidate's
local name, canonical source, visibility, and span.

Bindings are lifecycle values and are not closure-checked. Consequently the
old binding-loop gate, `write_is_closure_valid`, and the associated
slot-before-gate residual all retire rather than moving elsewhere. An error
validating any candidate rejects the candidate batch before table or GOT
publication.

**Greppable structural guard (Principle 18):** a public cross-module
name-candidate exposure that bypasses `check_exposed_candidate_closure`, or any restored
binding-shaped closure predicate, is a `/review` finding.

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

The delivered structural evidence retained by
`design/arch/bounded-contexts.md` §6 and `tests/plan/s115-test-plan.md` §3.1 is:

1. **One candidate-shaped gate:** a public external candidate outside `D(M)`
   rejects; inside `D(M)` admits; private, same-module/self-alias, and
   unknown-`D(M)` candidates admit.
2. **Closed candidate census:** imports, exports, prepared publication, retained
   staging publication, and bootstrap candidate exposure all route through that
   gate before table or GOT mutation.
3. **Obsolete mechanisms absent:** no binding-shaped/no-op gate and no
   `write_is_closure_valid` remain.
4. **Bootstrap proof:** `all_name_candidates` is non-empty and the injected
   forbidden public cross-module/outside-`D(M)` candidate rejects.
5. **≥25× deterministic-recipe sweep** vs the real stdlib (`--run` + REPL) —
   **behavioural no-regression** (the pre-fix baseline is 0-fire in this
   environment; the fail-on-revert guard is the synthesized trigger, NOT the
   sweep). One time-boxed load-amplified re-induction attempt, abandoned without
   prejudice if quiet.
6. **The two GREEN twins hold**
   (`tests/spec_08_prelude_outer_scope.rs::super_import_wrapper_over_specific_prelude_compiles_clean`
   — the correct pole, a free tripwire that reddens if the phantom ever turns
   deterministic; and the `_collides_…_neg` poison twin — the poison stays
   spec-correct).
7. **This doc records the current contract:** §2.2 defines the sole predicate
   and §2.4 owns the candidate routes. The retired group retains the historical
   attribution limits stated in `design/arch/bounded-contexts.md` §6.

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

- `design/arch/bounded-contexts.md` §6 — current closure carrier for the retired
  0604/0740/0793/0818 group and its historical attribution limits.
- `src/imports.rs` — the sole candidate-shaped
  `check_exposed_candidate_closure` and the
  `install_exports` / `install_imports` routes; `insert_detecting_ambiguity`
  remains the §8.6.5 poison consumer.
- `src/worker.rs` — prepared and retained staging publication enumerate the
  complete candidate batch before mutation.
- `src/bootstrap.rs::mount_synthetic_modules` — candidate seeding and the
  non-vacuous `all_name_candidates` proof for its named legal skip.
- `src/session_v4/lifecycle.rs::seed_session_symbol_tables` — the `PRIMITIVES_TABLE` whole-table
  mount, the third session-init census row.
- `src/platform.rs::register_platform_in_tc` — the canonical own-definition
  DLL-load seam and its named legal skip.
- `src/cluster.rs` (`insert_cluster`:337) — the Wave-3a-β scaffold gate call
  (normally-empty entries loop).
- `crates/cranelisp-primitives/src/declarations.rs:314` — `bit-and` IS a bundled
  primitive (the falsified-premise evidence).
- `tests/plan/s115-test-plan.md` §3.1 — the synthesized-trigger binding finding.
- `design/int/index-worker-isolation.md` — the *background* index-feed isolation
  (S110); this doc is the foreground companion.
- `design/int/heisenbug-race-closure.md` / `signature-body-prepass.md` — the
  S61→S93 isolation-by-construction precedent.
- `design/arch/safety-invariants.md` §2 (trust-boundary diagnosed-error tier) +
  R7 register row — the assertion tier the promotion targets.
- `design/arch/prelude-import-convergence.md` §3.4 — the writer-census seed.
- `tests/spec_08_prelude_outer_scope.rs` — the two acceptance twins.
