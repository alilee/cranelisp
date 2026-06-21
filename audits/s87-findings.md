# Sprint 87 Stage-B — /arch cross-cutting synthesis + pre-Phase-H consolidation backlog

> **What this is.** The Wave-2a `/arch` synthesis pass over the eight per-crate
> Stage-B deep audits (`audits/{crate}-s87.md`) + the LOC triage
> (`audits/loc-s87.md`) + the C.1 exemplar adequacy review
> (`exemplar/notes-stdlib-adequacy-s87.md §FULL`). It finds the patterns no
> single-crate pass can see, validates and re-ranks the eight cross-cutting
> themes /sprint drafted (T1–T8), produces ONE severity-ranked pre-Phase-H
> consolidation backlog, and frames the scope-decision gate (Stage-B exit;
> /sprint + user run the gate, this doc is its input).
>
> **Authority.** `/arch` cross-cutting synthesis (SPRINT.md Stage B mechanism 4).
> READ-ONLY on code. The per-crate audits already propose crate-internal `/dev`
> FIXMEs (owned by each crate's triad) — this doc does NOT re-file those; it files
> only the genuine **cross-crate** consolidations `/arch` arbitrates (T1, T2, T3 —
> see §6). Citations are `file:line` from the eight passes.
>
> **Method note (the recurrence lens).** Per
> `memory/feedback_review_root_cause_and_duplication`, two themes are flagged as
> *recurring-class* signals — duplication families that survived multiple audits
> and that local-correctness review will not catch: **T1 (FQ-walk ×5)** and **T6
> (duplication families)**. Each gets a root-cause recommendation (§5), not just a
> "delete the dupe" line — because the symptom is N copies and the disease is "no
> single seam owns this." Date: 2026-06-20.

---

## 0. Headline

**No Blocker across all eight crates.** Per-crate baseline reconciliation is
**strongly positive** — most prior HIGH findings resolved (typecheck's entire HIGH
tier / FIXME 0240; backend's phantom entry + god-file splits; src/'s session/worker
god-file decomposition; primitives' HIGH-1/MED-1; platform 6-of-7; intrinsics
HIGH-1/HIGH-3/MED-1; frontend's dual-pipeline retirement). The crates are
architecturally sound.

**The durable misses are duplication families.** What survived — across S70…S86,
untouched — is *not* correctness debt; it is **single-source-of-truth debt** (Principle
7) and **interim-architecture residue** (Principle 8). The S87 fresh-view passes,
read together, show three of these have crossed from "smell" into "actively producing
or enabling defects":

1. **FQ type-rendering** is now copy-pasted **5×** across 3 crates (T1) — and Wave-0
   *deepened* it (the correct-but-symptom `format_type_fq` add). The recurrence tell.
2. **vec-set/vec-push RC labor-split** (T2) is the S86 `vec_set_copy` seed, confirmed
   from **both** sides (backend F3 + intrinsics NEW-2) — a paired-change-or-UAF item.
3. **Host-callback wiring** (T3) is hand-mirrored at 2 production sites in 2 crates
   with no shared builder — confirmed from **both** src/ F-B and platform F2 — the
   DEF-6 root enabler and the FIXME-0407 prerequisite.

These three are the must-track cross-crate consolidations (§6 files them). Everything
else is per-crate `/dev`/`/design` backlog (the owning triads' FIXMEs already name
them) or doc-currency cleanup.

---

## 1. Cross-cutting themes — validated, refined, ranked

The eight themes /sprint drafted (SPRINT.md "Wave-1b audit results") are **confirmed
as a set** — every one is grounded in ≥1 crate pass. The synthesis refines severity,
quantifies **leverage** (how many findings/defect-classes each collapses) and **risk**,
and re-ranks. Rank is by **(leverage × correctness-or-defect-enablement) ÷ change-risk**,
not by raw severity.

| Rank | Theme | Spans (crates) | Severity | Leverage | Risk | Must-fix-before-Phase-H? |
|---|---|---|---|---|---|---|
| **1** | **T2 — vec-set/push RC labor-split** | backend + intrinsics (+ primitives 3rd witness) | Important | Collapses DEF-2/DEF-3 family + deletes 1 runtime branch + 1 codegen helper (`emit_vec_set_copy_temp_compensation`) + unblocks F6 COW-skeleton extract | **HIGH — paired-change-or-UAF** (one side alone re-opens 0296) | **MAYBE → lean YES** (see §3) |
| **2** | **T3 — host-callback JIT-vs-`--link` divergence** | src/ + platform + exe-bundle (+ intrinsics ABI) | Important | Closes DEF-6 *root enabler*; is the **0407 prerequisite**; removes the only structural mode-divergence in the host boundary | **MED** (consumer-side refactor; 0407 widens it ×3 if unfixed) | **MAYBE** (see §3 + §4-b) |
| **3** | **T4 — DEF-1 codegen-batch seam (the residual)** | src/ (the open site) ; typecheck (the model, already correct) | Important | The structural fix for DEF-1's residual; makes codegen-scope and typecheck-scope ask one reachability question | **LOW-MED** (additive: thread `prelude_fallback` into one fn) | **YES** (correctness; has a committed red repro — see §3) |
| **4** | **T1 — FQ type-rendering ×5 / Type-walk duplication** | types + typecheck + src/ | Important | Collapses 5 walks → 1 parameterized walk; retires 2 dead exports (T5 overlap); pre-empts the *next* "fixed one, others wrong" drift | **LOW** (correct-as-shipped; output conventions preserved as config) | **NO** (high-value-but-deferrable; recurrence-escalated §5) |
| **5** | **T5 — dead-path / dead-export class** | backend + types + typecheck + intrinsics | Suggestion→Important (backend) | The `produce_disasm`/0418 class; backend F2 harbors the *last* eager-disasm capture the D1b ruling retired | **LOW** | **NO** (cheap deletions; backend F2 partially overlaps T1's dead-export retirement) |
| **6** | **T6 — persistent duplication families** | backend + frontend + primitives + src/ | Suggestion (each) | Each extraction is local; the *aggregate* signal is the recurrence | **LOW** | **NO** (recurrence-escalated §5 — the signal matters more than any one fix) |
| **7** | **T7 — over-budget functions** | typecheck + backend + src/ | Suggestion | Pure legibility/testability | **LOW** | **NO** (opportunistic; touch-when-edited) |
| **8** | **T8 — interim-arch residue** | types (SymbolTable concurrency) + backend (cache migration) + frontend (PEG docs) + primitives (runtime-crate docs) | Suggestion→Important (types) | Resolving the *limbo* (decide target, then act or retract) | **LOW** | **NO** — but **one decision owed** (§3 T8-types: is the DashMap-inner target still live?) |

**Refinements to /sprint's draft ranking:**

- **T2 promoted to #1** over T1. /sprint's draft listed T1 first (HIGH leverage). T1's
  leverage is real but its *risk* is LOW and it is correct-as-shipped — it is the
  deferrable kind of debt. **T2 carries a UAF risk if mis-sequenced** and collapses an
  active S86 defect family — that combination (defect-adjacent + paired-change hazard)
  is what a synthesis should surface to the gate first, even though both are "Important."
- **T4 promoted ahead of T1.** T4 is the only theme with a *committed red repro*
  (`spec_08_modules.rs::def1_prelude_provided_defn_called_bare_enters_codegen_batch`,
  the S86 ledger entry). It is a correctness residual, not a maintainability item.
- **T1 stays Important but is reframed as the headline *recurrence* signal** (§5), not
  the headline *fix*. Its value is the root-cause it exposes (no single seam owns
  Type-rendering), which is escalated rather than rushed.
- **T5 and T6 partially overlap** (backend F2 dead-disasm; types dead exports are both
  "dead-path" and "FQ-walk-duplication"). The backlog (§2) de-duplicates: types' dead
  exports are retired *as part of* the T1 consolidation change-set, not as a separate T5
  item.

---

## 2. The prioritized pre-Phase-H consolidation backlog

Ordered. Each item: scope, owning skill(s), est. size, dependency, and a
**must-land-before-Phase-H** recommendation with rationale. Three buckets:
**(i) must-fix-first** (correctness/architecture risk Phase H would build on);
**(ii) high-value-but-deferrable** consolidation; **(iii) nice-to-have**.

### Bucket (i) — must-fix-first (the gate shortlist; see §3 for the rationale)

| # | Item | Theme | Scope (crates) | Owner(s) | Size | Dependency | Before Phase H? |
|---|---|---|---|---|---|---|---|
| **B1** | **DEF-1 codegen-batch seam** — thread `prelude_fallback` into `derive_codegen_batch` (`src/worker.rs:599`) so codegen-scope == typecheck-scope reachability | T4 | src/ (the fix); typecheck (the model) | `/dev` src/ (`/int`) | S | none (additive; has red repro) | **YES** |
| **B2** | **vec-set/push RC-model alignment** — stop runtime inc (`vec_runtime.rs:220`), hoist consuming-inc up-front in `compile_vec_set`, delete `emit_vec_set_copy_temp_compensation` (`vec_codegen.rs:404-456`) | T2 | backend + intrinsics | `/arch` arbitrates → paired `/dev` backend + `/dev` intrinsics | M | **PAIRED** (both sides one change-set; unit test each side) | **YES (lean)** |

### Bucket (ii) — high-value-but-deferrable consolidation

| # | Item | Theme | Scope | Owner(s) | Size | Dependency | Before Phase H? |
|---|---|---|---|---|---|---|---|
| **B3** | **Shared `HostCallbacks` builder** (consumer-side) — one builder both `src/platform.rs:253` + `cranelisp-exe-bundle/src/lib.rs:131` call; kills the hand-mirror | T3 | src/ + exe-bundle + intrinsics (host the builder) | `/arch` (ABI/boundary) → `/dev` int + backend | M | **0407 prerequisite** (do NOT widen `HostCallbacks` before this lands) | **MAYBE** (§3) |
| **B4** | **FQ Type-rendering consolidation** — one parameterized walk in `cranelisp-types::types` (config: primitive-naming bare\|qualified, var-naming numbered\|lettered); 5 sites → thin callers; retire dead `format_type_display`/`format_type_with_vars` exports (T5 overlap); fix `concrete_type_name` no-impl strip (typecheck Finding 4/S87-1) | T1 (+T5) | types + typecheck + src/ | `/arch` (owns `Type`) → `/dev` typecheck + src/ | M | ships with `public-api.txt` regen | **NO** |
| **B5** | **Backend ISA-duplication delete** — `jit.rs::build_isa()` → call `cache::object::build_isa(false)` | T6 | backend | `/dev` backend | S | none (pure deletion) | **NO** |
| **B6** | **Backend dead-in-prod `Jit::compile_defn` family** — collapse to thin wrapper over `compile_defn_in_module` OR drop the `disasm`/`set_disasm` capture (the last eager-disasm the D1b ruling retired) | T5 | backend | `/dev` backend | S–M | none | **NO** |
| **B7** | **Backend cache-migration residue** — deletion pass with removal success-criterion: `CacheMetadata`, `build_cache_packet` deprecated envelope, `got.rs`/`codegen_types.rs` re-export shims | T8 | backend | `/dev` backend | M | verify no external consumers first | **NO** |
| **B8** | **SymbolTable concurrency target currency DECISION** — `/arch` rules: is the DashMap-inner + atomic + `&self`-write target still live, or has `&mut self`-behind-outer-DashMap converged as sufficient? Then either schedule the migration OR retract the baseline ruling + deferral rustdocs + sequence diagram | T8 | types | **`/arch`** (decision, not impl) | S (decision) / L (if migrate) | none | **NO** (but decide before Phase H opens — see §4) |

### Bucket (iii) — nice-to-have (opportunistic; touch-when-edited)

| # | Item | Theme | Scope | Owner | Notes |
|---|---|---|---|---|---|
| B9 | `emit_extern_call_1..4` arity ladder → one slice-based helper | T6 | backend | `/dev` backend | "do not add `_5`" trap; split across 2 modules |
| B10 | Twin symbol-table walkers (`resolve_in_module`/`arity_in_module`/`resolve_*_target`) → one parameterized walker | T6 | backend | `/dev` backend | folds with F4/F5 mod.rs pass; shrinks mod.rs |
| B11 | Over-budget functions: `monomorphise_call` ~307 (typecheck), `compile_resolved_call` 271 (backend), `try_cache_hit_load` ~254 + `CompilerSession::new` ~216 (src/) | T7 | typecheck + backend + src/ | `/dev` per crate | mechanical phase-extraction; touch when next edited |
| B12 | Frontend: shared head-classifier (F4+F7), synth-Sexp kit (F2), stale-PEG docs (F3) | T6 | frontend | `/dev`/`/design` frontend | F3 is a cheap doc fix carrying baseline rec #5 |
| B13 | Primitives: omission-direction registration guard test (MED-1); `str_split`/`str_join` via `vec_runtime` accessors (MED-2, T2-adjacent); stale runtime-crate docs (LOW-1) | T6 | primitives | `/dev` primitives + `/qa` | MED-1 is the `neq-string` defect-class seam, still unguarded |
| B14 | Intrinsics: `// SAFETY:` on `call_continuation` transmute (NEW-1); 6 open-coded heap reads → `heap_access` (NEW-3); `is_runtime` field justify/drop (NEW-4) | T5/T6 | intrinsics | `/dev` intrinsics + `/arch` (NEW-4 touches public-api) | NEW-1 is a one-line discipline gap on the hottest fn-ptr cast |
| B15 | Doc-currency: platform.md ABI v5→v6 (platform F1); backend `design` FunctionArtifacts overclaim (F9); src/ dead accessors (F-H) | T8 | platform/backend/src/ | `/design` per crate | mechanical |

### C.1 [COMPILER] adequacy gaps (folded into the backlog per the Phase-4 gate)

| # | Item | Class | Owner | Before Phase H? |
|---|---|---|---|---|
| **B16** | **Bitwise intrinsics** (`bit-and`/`bit-or`/`bit-xor`/`bit-not`/`shl`/`shr`/`popcount`) + `num/bits.cl` wrappers — FIXME 0416 (filed by /port) | language gap | `/spec` (semantics) + `/backend` (1:1 CLIF lowering) + `/stdlib` (wrappers) | **NO** (forward-flow feature; near-trivial codegen but a spec-semantics decision) |
| **B17** | **DEF-2 — curated `conj` corrupts heap-ADT elements** (wrapper-RC / consuming-convention bug) | defect (G2) | repro queued for `/qa` → `/backend` resolves; **no FIXME** (failing test is the record per `feedback_no_fixme_with_failing_test`) | **MAYBE** (it is the *same RC-convention family* as T2/B2; see §3 note) |

> The C.1 [STDLIB] gaps (G3 `range`, G4 `char->digit`, G5 `str-assoc`, + adoption
> swaps) are NOT in this backlog — they are `/stdlib` C.2 authoring (Wave 1d, in
> progress) and `/port` exemplar-refresh, not Phase-H-gating compiler work.

---

## 3. Must-fix-before-Phase-H shortlist (the single most important output for the gate)

Phase H is the release-compiler phase: it *builds on* whatever the compiler does at
Stage-B exit. The filter for "must-fix-first" is: **would Phase H build on a
correctness bug, a paired-change hazard, or an architectural divergence that becomes
harder to fix once the release surface is committed?**

**Recommended must-fix-first (in order):**

1. **B1 — DEF-1 codegen-batch seam (T4). MUST.** This is the only item with a
   *committed red repro*. Codegen-scope and typecheck-scope disagree about
   reachability: a prelude-provided plain `defn` called bare typechecks (the §8.8.1
   fallback surfaces it) but its body never enters the consuming module's codegen
   batch → `codegen error … undefined function`. Phase H (release builds, `--link`)
   would ship that divergence. The fix is additive and low-risk (thread
   `&prelude_fallback` into one function). **Gate it in.**

2. **B2 — vec-set/push RC-model alignment (T2). LEAN MUST.** Not a live defect today
   (inc + dec net out, suite green), so *strictly* it could defer. BUT: (a) it is a
   **paired-change-or-UAF** item — the longer the labor-split persists, the more code
   accretes around the compensation dance, and the riskier the eventual paired fix; (b)
   it collapses the **same RC-convention family** as the active **B17/DEF-2 `conj`
   defect** — both are "Vec-element consuming-inc discipline not single-sourced." Fixing
   the convention once, before Phase H, is cheaper than fixing it twice after. **Lean
   to gating it in, paired-and-tested; if the gate defers it, B2 and B17/DEF-2 must be
   scheduled together** (they are one root cause: Vec element-write RC discipline lives
   in two crates). The gate (user) decides; the synthesis recommendation is **YES,
   paired with B17**.

3. **B3 — shared `HostCallbacks` builder (T3). MAYBE → decide at the gate.** Today the
   two production sites *agree* (DEF-6 is fixed); the risk is structural, not active.
   The decision hinges on **0407**: if any Phase-H or near-term sprint will land Model-B
   closure callbacks (0407 widens `HostCallbacks` by 3 fields ×2 sites), B3 is the
   prerequisite and should land first. If 0407 stays deferred indefinitely, B3 is
   high-value-but-deferrable (bucket ii). **Recommendation: gate-in B3 IFF 0407 is on
   the near roadmap; otherwise defer.** This is the answer to chartered question (b),
   §4-b.

**Explicitly NOT must-fix-first** (deferrable consolidation): B4 (FQ-rendering — correct
as shipped), B5–B15 (cleanups), B16 (bitwise — forward-flow feature, not a Phase-H
blocker). And the one **decision** owed regardless: **B8 (SymbolTable concurrency target
currency)** — not an implementation gate, but `/arch` should rule before Phase H opens
so the release compiler is not carrying a 3-sprint-stale Principle-8 limbo with an
undecided target (§4).

---

## 4. Phase-H gate framing

Phase H currently gates on three carried FIXMEs (confirmed-deferred at Stage A):

- **0050** (/int) — display protocol (list/seq pretty-printer).
- **0052** (/repl) — `/learn` system.
- **0365** (/spec) — `Type.member` accessor qualification.

**S87 adds to the gate input:**

- **must-fix-first (correctness/hazard):** **B1 (DEF-1 codegen-batch, T4)** — gate-in;
  **B2 (vec RC-model, T2)** — gate-in (paired with B17/DEF-2); **B3 (HostCallbacks
  builder, T3)** — gate-in *conditional on 0407 roadmap position*.
- **owed decision (not an impl gate):** **B8** — `/arch` rules on the SymbolTable
  concurrency target before Phase H opens.
- **deferrable:** B4–B16 are scheduled post-gate at the user's discretion.

**Surfaced at the gate but user decisions, not /arch ranking** (per the charter): the
two exploratory design tracks' sign-offs — `--release` LLVM tier (U1–U4) and embedded
REPL agent (U1–U6). These are not S87 implementation and not part of this backlog's
ranking; they are flagged here only so the gate's input set is complete.

### Chartered question (a) — the single-resolution-seam question (T4)

> *Is `derive_codegen_batch` the one remaining seam that must consult the prelude
> fallback? Is there a deeper unification?*

**Answer: it is the one remaining *codegen-side* seam, and the deeper unification is
"codegen-scope and typecheck-scope must ask the SAME reachability question."**

The evidence across three crates is consistent:

- **typecheck (the model — correct).** The DEF-1 *resolution* seam is **ONE, correctly
  wired** (typecheck §2): a single gate `prelude_fallback_target`, a single shared
  primitive `cranelisp_types::resolve_with_fallback`, and the S86-missed
  monomorphisation-collection chokepoint (`collect_imported_constrained_calls`) is now
  routed through the fallback-aware seam. typecheck is the reference implementation.
- **src/ (the residual — the open site).** `derive_codegen_batch` (`worker.rs:599`)
  enumerates the batch from the **current module's table only** + names in `program` —
  it never reads `prelude_fallback`. So codegen re-derives "what is in scope" *without*
  the fallback typecheck applies. **That disagreement IS DEF-1's residual** (src/ §3).
- **The intent is one seam; the implementation is N consultations.** The
  `prelude_fallback` bit is read at ~10 independent src/ sites. Most are correct
  (recognition funnels through one site `expander.rs:267`; introspection display). But
  **two are off-canonical re-inlines** (src/ F-G: `describe_symbol`,
  `format_eval_result_body` re-inline the current→prelude→root hop instead of the
  canonical `lookup_with_prelude_fallback`) and **one chokepoint omits the consultation
  entirely** (`derive_codegen_batch`).

**The deeper unification.** There is no single function all consumers can call (codegen
batch derivation, typecheck resolution, and introspection display ask the question in
genuinely different shapes/positions). But there IS one *invariant* they must all honour:
**"what is reachable in this module includes the prelude outer scope, computed one way."**
The durable fix is two-part: (1) **B1** — make `derive_codegen_batch` consult
`prelude_fallback` so codegen-scope == typecheck-scope (the correctness fix); (2) **B12
/ src/ F-G** — route the two off-canonical display re-inlines through
`lookup_with_prelude_fallback` (the hardening, deferrable). typecheck needs no change —
it is already the single-seam reference. So: **`derive_codegen_batch` is the one
remaining seam that must consult the fallback; the deeper unification is the
codegen-scope-equals-typecheck-scope invariant, achieved by B1, not by a grand
resolution-engine merge.**

### Chartered question (b) — host-callback-divergence (T3)

> *Is the shared `HostCallbacks` builder the right fix, and is it truly the 0407
> prerequisite?*

**Answer: YES to both — with a sequencing condition.**

**Is the shared builder the right fix?** Yes. The divergence is confirmed structural
from both consumer crates (src/ F-B + platform F2 + the exe-bundle 10-line
"this-makes-the-`--link`-path-match" comment). The runtime `HostCallbacks` value is
hand-constructed at **two production sites in two crates** (`src/platform.rs:253` JIT/REPL;
`cranelisp-exe-bundle/src/lib.rs:131` `--link`) **with no shared builder** — agreement is
maintained by manual mirroring + a cross-file comment, which is exactly the
Principle-7/Principle-8 anti-pattern that produced **DEF-6** (the window where one wired
`heap_alloc` = base-returning and the other `heap_alloc_payload` = payload-returning, a
heap-corrupting mismatch). The platform crate **correctly cannot** fix it (it must not
depend on `cranelisp-intrinsics` — that would invert the DAG, Principle 3); the fix is
**consumer-side**: one builder in the lowest crate that can name both intrinsic pointers
(`cranelisp-intrinsics`, or a host-side helper both consumers call). The platform crate's
own **layout-hash export path is the divergence-proof counter-example** (platform §3.3:
one data representation, both modes dereference identically) — the callback wiring should
adopt that shape. So the shared builder is not merely *a* fix; it is the fix that makes
the contract divergence-proof-by-construction rather than divergence-prone-by-hand-mirror.

**Is it truly the 0407 prerequisite?** Yes. 0407 (Model-B closure callbacks) widens
`HostCallbacks` with `rc_inc`/`rc_dec`/`invoke_closure` (ABI bump) — **three more fields
every construction site must wire identically.** Widening a 2-site hand-mirror by 3
fields *multiplies* the DEF-6 hazard by 3 across the same 2 sites. 0407's own "Proposed
resolution §2" already flags the three sub-contracts (capture/RC, error-slot ferry,
threading) that must hold across the FFI and across threads — i.e. 0407 is the
closure-callback instance of exactly the wiring-agreement problem DEF-6 was the allocator
instance of. **Do not widen `HostCallbacks` until there is one place that constructs it.**

**Sequencing condition (the MAYBE in §3).** B3 is the *prerequisite* for 0407, not a
prerequisite for Phase H per se. If 0407 is on the near roadmap, B3 must land first
(gate-in). If 0407 stays deferred, B3 is deferrable consolidation. **Recommendation to
the gate: gate-in B3 iff 0407 is scheduled within the Phase-H arc; otherwise bucket (ii).**
0407 itself stays **open and cited, not actioned** this sprint (SPRINT R2).

### Boundary note — fork-join error-slot ferry (cross-crate trace, for legibility)

The S86 §12.4.3 fork-join error-slot ferry obligation is **partially observable** across
the audits and the **platform half is sound** (platform F6: `EffectOutcome` DLL-local
catch → C-ABI value ferry is correct). The open half is downstream — whether the
**fork-join join** (intrinsics / `src/worker.rs` trampoline) propagates a faulted
`EffectOutcome` from a Par branch to the joining thread vs. drops it. This is **not an
S87 backlog item** (no committed repro yet; it is a recorded obligation in
`design/arch/test-discovery.md`), but it intersects **0407** (the callback error-slot
ferry sub-contract) — so when 0407/B3 are actioned, this obligation is the natural
co-resolution. Flagged here only so the cross-crate trace stays legible.

---

## 5. Recurrence escalations (per `feedback_review_root_cause_and_duplication`)

Two themes are *recurring-class* signals — duplication families that survived multiple
audits and that local-correctness review will not catch. The memory's directive: on
second occurrence, run a root-cause pass *before* applying another local fix; name the
symptom as a duplication finding, not a clean pass. Both get a **root-cause
recommendation**, not a "delete the dupe" line.

### Escalation 1 — T1 (FQ type-walk ×5; Wave-0 *deepened* it)

**The recurrence, stated plainly.** The `Type`-enum walk is now copy-pasted **5×** across
3 crates with **2 divergent primitive-naming conventions** (types Finding 1):
`impl Display` (bare); dead `format_type_display` (bare); `format_type_fq` (FQ, **added
in Wave 0**); `display.rs` ×2 (FQ). The S86 campaign already paid for this class (the
"fixed it in one place, the others still wrong" drift). **Wave-0 is the tell**: the
`format_type_fq` add was *individually correct* (it fixed the type-error renderer to emit
FQ names per spec §5.3) but it was a **symptom patch that deepened the duplication** — a
fourth walk added instead of the existing FQ walk shared. The /arch Phase-2 "keep-distinct"
advisory was applied to the *implementations* when it should have been applied only to the
*output conventions*.

**Root cause (not "delete the dupe").** The disease is **no single seam owns
Type→string rendering**, and `Type` lives in `cranelisp-types` where the seam *should*
be but isn't (only 2 of the 5 walks live there, and one of those is dead). The recurrence
will continue every time a new type-name-into-a-message site is written
(`concrete_type_name` no-impl strip is already the *6th*, with a *3rd* convention —
strip-to-bare-local).

**Recommendation.** **B4** — one parameterized walk in `cranelisp-types::types` (config:
primitive-naming bare\|qualified, var-naming numbered\|lettered); the 5 (6) sites become
thin config-selecting callers; the "keep-distinct" advisory survives **at the output level**
(conventions are config values, not copies); the 2 dead exports retire in the same
change-set (T5 overlap). **Process recommendation for `/review`:** the Wave-0 episode is
the textbook case the memory describes — a clean local review that missed the
duplication-deepening. Future `/review` prompts on any `Type`-rendering or
name-into-message change MUST ask "does this walk already exist elsewhere? am I adding
the Nth copy?" before passing. **This is high-value but NOT must-fix-before-Phase-H** —
it is correct as shipped; the escalation is about *not deepening it further* and
scheduling the consolidation, not rushing it.

### Escalation 2 — T6 (persistent duplication families)

**The recurrence, stated plainly.** Multiple duplication families flagged in the
**2026-04-23** backend/frontend audits are **intact 14 months later**, across crates:

- backend: two `build_isa` (F1), `emit_extern_call_1..4` arity ladder (F5), twin
  symbol-table walkers (F11), vec COW skeletons (F6).
- frontend: two synthetic-Sexp DSLs (F2), test/prod mirror of `is_top_level_form` (F4),
  head-set expressed twice (F7).
- primitives: the three-edit registration seam (MED-1) — the `neq-string` defect-class
  seam, **still with no omission guard**.
- src/: prelude-fallback re-inlined off-canonical (F-G), `register_dep` prologue inlined
  ×5 (F-L), `register_synth_adt` mirrors typecheck (F-J).

**Root cause (not "delete each dupe").** These are not one bug; they are a **standing
tolerance for two-site duplication** — each individually sits at "2 sites, below the
rule-of-three extraction threshold," so each individual `/review` correctly passes it,
and the aggregate never gets escalated. **That is the exact gap the memory names**:
local-correctness review is necessary but not sufficient; the *family* is invisible
without a cross-cutting pass. The recurring-class signal is that the SAME families
reappear audit after audit because nothing triggers extraction at 2 sites.

**Recommendation.** Two parts. (1) **Schedule the cheapest, highest-confidence
extractions** (B5 ISA-delete is a *pure deletion*; B9 arity-ladder, B10 walker, B12
frontend head-classifier, B13 primitives omission-guard) as a **single
duplication-consolidation change-set per crate**, not piecemeal — the memory's "unify
before shipping the next patch." (2) **Process: lower the extraction trigger for
recurring families.** The rule-of-three is right for *new* duplication; for a family that
has appeared in **2+ consecutive audits**, the second audit appearance IS the third
signal — treat it as past-threshold. Concretely: `/review` should flag a 2-site duplicate
as *Important* (not Suggestion) when a prior audit already named it. **None of these are
must-fix-before-Phase-H** — but the primitives omission-guard (B13/MED-1) is the one with
a *defect-class precedent* (`neq-string`) and should be prioritized within bucket (ii)/(iii).

---

## 6. FIXMEs filed

Per the charter, the synthesis files only the genuine **cross-crate** consolidations
`/arch` arbitrates (the per-crate `/dev` items are owned by each crate's triad and the
audits already name them; the C.1 [COMPILER] gaps are 0416 already-filed + B17/DEF-2
which is a failing-test-record, no FIXME). Three cross-crate items need a durable
`/arch`-owned trigger:

| FIXME | Target | Theme | What it tracks |
|---|---|---|---|
| **0417** | /arch | T2 / B2 | vec-set/push RC-model alignment — the paired backend + intrinsics change (stop runtime inc, hoist consuming-inc, delete compensation). PAIRED-OR-UAF. |
| **0419** | /arch | T3 / B3 | Shared consumer-side `HostCallbacks` builder — DEF-6 root-enabler closure + 0407 prerequisite. (Cites 0407, which stays open.) |
| **0420** | /arch | T1 / B4 | FQ Type-rendering consolidation — one parameterized walk in `cranelisp-types`; retire dead exports; ships with `public-api.txt` regen. |

> 0418 deliberately skipped per the charter (it was the Wave-0 PIF FIXME, resolved by
> removal). 0416 (bitwise / B16) is already filed by /port and stays open. 0407 stays
> open and cited (B3/0419 references it as its dependent). The SymbolTable-concurrency
> currency **decision** (B8) is `/arch`'s own to rule and is NOT filed as a FIXME — it is
> a synthesis recommendation for `/arch` to action directly (decide, then act-or-retract).

---

## 7. Per-crate baseline reconciliation roll-up (currency check)

| Crate | Prior baseline | Reconciliation verdict |
|---|---|---|
| typecheck | `typecheck-20260531.md` | **Strongly positive** — entire HIGH tier (FIXME 0240) resolved; DEF-1 seam single+correct; residue is LOW typecheck-internal + the cross-crate FQ no-impl (→B4) |
| backend | `backend-20260423.md` | **Mixed-positive** — files shrank, tests localized, phantom entry deleted; but HIGH-3 **duplication families intact** (F1/F5/F11) + 2 dead-in-prod artifacts (F2) + cache residue not shrunk (F7) |
| src/ | `src-20260423.md` | **Strongly positive** — session/worker god-files split (FIXME 0109); 3 baseline findings resolved; residue is over-budget fns + the DEF-1 codegen seam (→B1) + host-callback (→B3) |
| frontend | `frontend-20260423.md` | **Positive** — dual-pipeline retired; no god function; residue is synth-DSL duplication (F2) + stale PEG docs (F3) + 2-site mirrors |
| intrinsics | `intrinsics-2026-06-14.md` | **Strongly positive** — HIGH-1/HIGH-3/MED-1(bulk)/LOW-1/LOW-2 resolved; unsafe exemplary (1 missing SAFETY comment); the vec_set_copy seed (→B2) |
| primitives | `primitives-2026-06-14.md` | **Strongly positive** — HIGH-1/MED-1 resolved well (guard tests + const asserts); residue is the registration seam guard (MED-1) + doc currency |
| platform | `platform-2026-06-14.md` | **Strongly positive** — 6 of 7 resolved; unsafe exemplary; the headline is consumer-side host-callback divergence (→B3), not a platform-crate defect |
| types | `facades/types-audit-s69.md` | **Positive** — mechanical/relocation findings resolved; FQTypeName held; 2 open: FQ-rendering proliferation (→B4) + SymbolTable concurrency limbo (→B8) |

**Net:** the recurring misses are the duplication families (T1/T6 — recurrence-escalated)
and one interim-arch limbo (T8-types). No crate carries a Blocker; no crate's residue
*by itself* gates Phase H — the gate items are the cross-crate themes (B1/B2/B3), not any
single crate's interior debt.
