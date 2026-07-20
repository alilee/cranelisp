# Foundational safety invariants and their assertion mechanisms

**ASSESSMENT + REGISTER (S111 `/arch`, 2026-07-17).** The register (§4) is canonical and
maintained ongoing. The Principle framed in §5 was **RATIFIED by the user at the S111
Phase-7 close (2026-07-18) as a single principle** and now lives canonically at
`principles/25-narrowing-carries-its-check.md` (indexed in `principles.md`); §5 records
the ratification. This document remains the **binding frame** for the S112
memory-safety-soundness mechanism — the mechanism builds to it. The `/design` cascade
(§6) is the scoped task list for the follow-up increment.

**W5 execution frame (S113, user-ruled depth).** The build wave executes tiers **4 + 5 +
3 + 1–2** (generative harness deferred S114). Tier 4 is LANDED (S113 W1 standing lane —
see §2 tier 4); R7's tier-3 assert landed S113 W4. Every W5 change-set traces to a
register row + ladder tier — the ladder is the only mechanism vocabulary (no parallel
taxonomy); the per-row annotations in §4 carry the W5 trace. Named capacity fallback:
the §3b origin split (and its schema bump) may slip to S114 — §3a/§3c do not depend on
it (the rule table classifies May-claims in the existing representation; §3b is the
unrepresentability hardening on top).

**Motivating systemic finding (S111, user-directed).** Every memory-safety defect in the
S111 ledger was found *incidentally* — adversarial review, a stdlib migration tripping a
latent crash, a golden-lane audit — never *structurally prevented* and never named by an
assertion at the seam where it broke. The architecture must think in foundational
invariants and mechanical ways to assert them, not in per-instance patches.

## §1. The class: unsound narrowing of a safety judgment

The memory-model spine (`ownership-inference.md` §2.1) rests on **monotone soundness**:
every analysis dimension has a conservative ⊤ (`Owned`/`Escapes`/`Crossing`/atomic/heap),
and *widening toward ⊤ is always safe — only performance degrades*. That property is
load-bearing and correct. But it protects exactly one direction. Every optimization is a
**narrowing**: the compiler concludes a static judgment stronger than ⊤ and, on its
strength, **elides a safety operation** — an RC protect/inc, an atomic RMW, a distinct
drop-glue symbol, a bounds validation, a recompile. Monotone soundness guarantees nothing
about that direction, and as-built, *nothing mechanically checks that a narrowing preserved
soundness*. A wrong narrowing silently removes the safety operation, and the elision is
invisible until an adversarial input constructs the case the judgment got wrong.

The S111 ledger is a catalogue of exactly this shape:

| Defect | The unsound narrowing | The elided safety op | How it was found |
|---|---|---|---|
| §3.7 vec-COW UAF (CS-5 target) | `vec-set`/`vec-push` declared `result: Fresh` (false leaf fact); declared facts unreachable from prelude-fallback modules with an anti-conservative `Fresh` default | return-value protect | user-constructed repro (S110) |
| 0641 B-1 false-`Fresh` | transfer walk drops element provenance at `VecLit` construction — container origin `Fresh` despite param-reaching element | return-value protect | adversarial `/review` of CS-5 |
| 0641 B-2 | producer publishes unconditional `ProjectionOf` from a *conditional* (may) origin | (latent) any consumer trusting unconditionality | adversarial `/review` |
| 0641 I-1/I-2 | capture / element-store provenance laundering | protect on captured/stored alias | adversarial `/review` |
| 0633 drop-glue under-key | glue symbol keyed on bare `fqtn.name` — two semantic identities narrowed to one key | per-instantiation glue body | `/review` Important on CS-1 (and CS-1 had **canonized the bug in a passing test**) |
| 0640 non-injective mangle | sanitize collapsed `A-B`/`A_B` to one symbol — identity narrowing again, one layer down | distinct glue symbol | adversarial `/review` of the 0633 fix |
| CS-4 B-1/B-2 wrong-accepts | typecheck narrowed "this scheme is generic" from an unsound discriminator | type-safety rejection (heap ptr read as Int) | adversarial `/review`, twice |
| 0604 phantom prelude write | (violation of a relied-on invariant with **no assertion at its seam**) | — | ~320 unlocatable no-fires; seam still unknown |
| 0637 sibling GOT slot | cache load implicitly narrows "these bytes are valid" by trusting a persisted index | bounds validation | `/review` suggestion on CS-2 |

Two structural observations:

1. **The class recurs anywhere a safety operation is elided by a static judgment** — it is
   not an ownership-analysis problem. Keyed identity (a mangle IS a narrowing: many-named
   semantic identity → one symbol), cache trust (load-time narrowing: bytes → valid
   indices), GOT indexing, and type-scheme generalization all produced the same shape in
   one sprint.
2. **The S111 fixes that closed their class did so by asserting, not by patching.** CS-2's
   always-on `assert!` at `GotTable::{store,load}_slot` + the diagnosed `CacheStale` at the
   cache seam; CS-1.2's injective escape with a **total decoder and a round-trip witness
   test** ("the round-trip test IS the injectivity verification" — accepted with no
   separate review cycle). The instance-patches (CS-1.1's re-key before the injectivity
   question was asked; CS-5 before the container axis was asked) each needed an adversarial
   follow-up to find the next layer. The mechanism, not the instance, is what closes a class.

## §2. The assertion-mechanism ladder

Five tiers, strongest first. For every safety-eliding narrowing and every foundational
invariant, the design question is "which is the strongest applicable tier?" — and the
answer is recorded in the register (§4). Each tier has an S111-proven exemplar.

1. **Unconstructable (Principles 18/20).** The violation has no representation.
   Exemplars: `got_slot` lives only on concrete-callable `DefKind` variants (slot ⟺
   `is_concrete()`, S83/S84); backend⊥primitives dep-ban. Reach for this first; it is not
   always available for *analysis results* (a summary is a claim about dynamic behavior,
   not a data shape) — but it IS often available for the *producer seam* (see §3, the
   conditional/unconditional origin split).
2. **By-construction witness.** The narrowing ships a checkable artifact whose validity
   *implies* the property — proof, not sampling. Exemplar: CS-1.2's `escape_symbol`
   (prefix-free escaping + total decoder + round-trip-decode test = injectivity for **all**
   inputs, where the 0633-R3 alphanumeric battery was blind to the class). Rule: **every
   mangle from semantic identity to symbol either ships a decoder witness or is
   additionally keyed by a disambiguator** (span/disc, as the mono inner-fn names are).
3. **Seam assertion.** The invariant is checked exactly where it could break, so a
   violation *names its seam at the moment it happens*. Two sub-forms, per the CS-2
   `store_slot` ruling (the trust-boundary taxonomy, now general):
   - **In-process invariant breach ⇒ always-on `assert!`** — a compiler defect; located
     hard-fail, never release UB, never a laundered `Result`.
   - **Untrusted external data (persisted cache, DLL exports) ⇒ diagnosed error + safe
     recovery** at the load boundary (`CacheStale` → recompile; layout-hash refusal).
   Exemplar: CS-2 (both halves). Counter-exemplar: 0604 — the prelude-export invariant had
   *neither*, and the violation has been unlocatable for ~320 runs; one `debug_assert!` +
   trace emit at the live-table insertion seam converts a ghost into a named seam.
4. **Differential equivalence against the conservative fallback (the R7 oracle).** For
   narrowings justified by a whole-program analysis — where no local witness exists — the
   check is behavioral: the optimized lowering must be observationally equivalent
   (output + exit + heap balance) to the conservative lowering. This requires the
   conservative fallback to be **permanently reachable** (the analysis-off toggle,
   `ownership-inference.md` §6.2) — which monotone soundness already guarantees is sound.
   Exemplars: the CS-5 emission cert; the CS-0.5 certification of three sprints of
   accumulated reshape. The S111 gap is that the check ran *ad hoc per change-set* and its
   golden lane rotted silently for three sprints (S104/S109/S110) because it was invisible
   to nextest — the check must be a **standing gate**, which is the parallel `/qa`
   coverage-strategy work (this doc mandates the requirement; `tests/plan/` owns the lane
   mechanics, corpus policy, and cadence — reference, not duplicated here).
   **LANDED S113 W1**: the standing nextest-visible lane (`tests/safety_oracle_lane.rs`
   + the `SafetyMatrix` combinator; 0641 B-1 RED-under-lane was the acceptance proof) —
   and it immediately earned its keep, catching MS-P7 (a `--link`-only COW-set→project
   UAF, the 0641 class's third reaching context) with the on/off discriminator recorded.
5. **Dynamic self-check lanes.** Properties only observable at runtime (RC balance) get a
   checking mode that converts silent corruption into diagnosed failure under test:
   DEC_CHECK stale-dec tripwires, alloc/free parity counts, checking allocator/ASan lanes.
   These are the assertion *form* of invariants that cannot be statically discharged; they
   ride tier 4's lanes.

**Example-based testing and adversarial review are discovery, not checks.** They found
every S111 defect and closed none of the classes. A green suite over examples asserts
nothing about the inputs nobody wrote; the ladder exists so that each invariant has a
check that quantifies over *all* inputs (tiers 1–2), *all* executions through a seam
(tier 3), or a *maintained equivalence* (tiers 4–5).

## §3. Soundness-by-construction for narrowing (the deep cure — gates the 0641 fix)

The 0641 residuals are not three bugs; they are three unregistered rules of one walk. The
cure is to make the ownership transfer walk a **lattice-monotone abstract interpretation
whose rules are enumerated and classified** — so an unsound narrowing is a *type of rule
violation visible at design review*, not a fact someone must adversarially discover.

**(a) The provenance/origin axis gets its own explicit ⊤.** The mode lattice's ⊤ is
`Owned`. The *result-origin* axis as-built has no stated ⊤, and that absence is exactly
where the bugs live: on this axis the **conservative point is "may reach anything the
inputs reach"** (the May/conditional claims), and `Fresh` / unconditional
`AliasOf`/`ProjectionOf` are the *strong* claims — the ones that license elision.
Normative rule: **information loss in the walk must move toward May, never toward a
stronger claim.** 0641 B-1 is precisely an anti-monotone rule: `VecLit` element-store
*discarded* element provenance and thereby *strengthened* the claim to `Fresh`. Under the
stated rule, a container's origin is at least the join of its elements' param-reaches
(`MayAliasOf` over the union) — losing the per-element detail is fine; losing the *reach*
is the unsound direction. Same rule covers capture (I-1) and element-store-return (I-2).

**(b) The producer seam gets the Principle-20 treatment.** §3.7's reservation clause
("`AliasOf`/`ProjectionOf` are reserved for provable unconditional claims") is currently a
prose contract that B-2 violated one level above the arm it was written for. Make it
unconstructable: split the origin carrier so conditional and unconditional origins are
**distinct variants** (`Origin::Unconditional(..)` vs `Origin::Conditional/May(..)`), and
the hard-claim publish arms of `origin_to_result_mode` pattern-match only the
unconditional variant. Publishing a hard claim from a conditional origin then has no
representation. `/design`(typecheck) evaluates the exact shape; the requirement is the
structural reservation, not the specific enum.

**(c) The rule table is enumerated and normative.** `design/typecheck/ownership-inference.md`
§15 (the provenance model) gains a finite table of transfer rules — one row per
construct (call, let, match-arm binding, VecLit/ctor store, projection, capture,
suspension) — each classified: **widening** (join toward ⊤ — always admissible),
**precision-preserving** (carries provenance exactly), or **narrowing** (makes a claim
stronger than the join of its inputs — admissible ONLY with a named justification: a
truthful+reachable declared leaf fact, or a structural argument recorded on the row).
`/review` rejects a `transfer.rs` change that adds or alters a rule absent from the table
— the same discipline as an unjustified `pub`. The 0623 matrix (behavioral axis) extends
with the container-store × projection-out × capture axes so each row has example pins —
but the *table*, not the examples, is the completeness argument.

**(d) The end-to-end discharge is tier 4.** Rule-level review (c) and producer structure
(b) are static; the dynamic discharge of the whole composition is the differential oracle:
analysis-on vs analysis-off, byte-level behavior + RC balance, as a standing gate over a
corpus that includes the matrix shapes. The reference-semantics framing makes this precise:
**the conservative all-Owned lowering IS the definition of correct behavior for the
memory model; an elision is correct iff equivalent to it.** An elision that cannot keep
its conservative twin reachable is inadmissible by definition (there is nothing to check
it against). Note the two named non-oracle surfaces route to their own tiers: keyed
identity → tier 2 (injectivity witness — its "conservative fallback" is not a toggle but
per-identity uniqueness); persisted trust → tier 3 (diagnosed error at load).

**(e) Binding sequencing for 0641 (user-directed).** The false-`Fresh` class is closed by
this mechanism, **not patched instance-by-instance**: the `/design`(typecheck) increment
that actions FIXME 0641 authors (a)–(c) as its frame FIRST, then lands B-1/I-1/I-2 as
rule-table corrections inside it, with the tier-4 gate as acceptance. A VecLit spot-fix
without the lattice/table frame repeats CS-1.1 → 0640: the next laundering site is one
adversarial review away.

## §4. The foundational-invariant register

Status vocabulary (descending strength): `unconstructable` (tier 1) · `witnessed`
(tier 2) · `asserted` (tier 3) · `gated` (tier 4 standing) · `dynamic-lane` (tier 5) ·
`matrix-tested` (example pins with a completeness argument) · `example-tested` (**the
gap**) · `unasserted` (**the hole**). A row at `example-tested` or `unasserted` is an open
item against `/arch` — either it gets a mechanism or the register records why none is
reachable (the Principle-18 "behavioral form is the right answer" carve-out, stated per
row, never defaulted).

| # | Invariant (what safety relies on) | Status today | Mechanism owed | Owner / seam |
|---|---|---|---|---|
| R1 | **Ownership-summary truth** — no published summary/mode lets a consumer elide a protect/inc/atomic the dynamic behavior needs | `example-tested`; tier-4 lane now standing (S113 W1) and already catching instances (MS-P7, the 0641 class's third reaching context, `--link`-only) | §3 (a)–(d): monotone rule table + P20 producer split — **W5 fix wave (tiers 1–2)**: §3a/§3c + 0641 B-1/I-1/I-2 rule-table corrections + the paired `/dev`(backend) B-2/I-2 consume fix; §3b producer split (+ its schema bump) is the named capacity fallback, may slip S114 — §3a/§3c do not depend on it | `/design`(typecheck) `ownership/transfer.rs`, `fixpoint.rs`; `/design`(backend) consume seam; `/qa` gate |
| R2 | **Elision-consumer safe default** — unknown/new summary variants keep the safety op (`== Fresh` binaries; exhaustive `ResultMode` match, no `#[non_exhaustive]`) | `unconstructable` (P18 exhaustiveness; verified no third escape, S111 P3) — a model | maintain; `/review` re-runs the `_ =>`/`== Fresh` grep per landing | landed (types + backend) |
| R3 | **Declared-fact truthfulness + reachability** — a primitive whose emission deviates from the consuming convention carries declared, reachable facts (§3.7 contract) | `matrix-tested` (whole-table sweep, CW-F3a/Fence-3, 5-site/1-helper pin) | evaluate P7 single-sourcing: the emission convention as one artifact consumed by both `ownership_facts.rs` and `vec_codegen` (today the declaration and the emission are un-tied prose twins in two crates) | `/design`(backend + primitives) |
| R4 | **Keyed-identity injectivity** — every mangle semantic-identity → symbol is injective (or additionally disambiguator-keyed) | drop-glue: `witnessed` (CS-1.2 decoder + round-trip — THE tier-2 model). All other mangle families: **unaudited** | census every symbol-mint site (`LinkerSymbol` mangles, `impl$FQType$FQTrait` method keys, inner-fn discriminators [span-keyed — verify], GOT data symbols, platform export names); each row → witness or disambiguator | `/design`(backend) `resolution.rs` naming primitives + census |
| R5 | **GOT index in range** — every slot read/write < table size; allocation fallible | `asserted` (CS-2: always-on `assert!` store/load + fallible allocate + cache-seam diagnosed error) — THE tier-3 model | extend cache-seam validation to `borrowed_sibling_slot` **with** its first consumer (FIXME 0637) — disposition re-affirmed S113 W5: **parked to the first consumer, NOT in-W5** (the sibling is carrier-only, zero production readers since S102; validating an unread index guards nothing, and pre-building the check ahead of its consumer is the P8 half-measure — the co-landing rule IS the mechanism) | `/design`(backend) rides the borrowed-convention track |
| R6 | **Persisted-index trust boundary** — every index/key/slot deserialized from `.meta.json` is validated at load; violation = diagnosed `CacheStale`, never trusted into emission | partial `asserted` (`callable_got_slot` only) | **generalize 0637 to the boundary**: census every persisted index (sibling slot; `callees` FQs [feeds the future reverse index]; summary param indices — an out-of-range `MayAliasOf(k)` from corrupt bytes indexes `arg_origins[k]`; span keys) → ONE validation seam in `deserialise_meta_with_build_id`, one `CacheStale` class each | `/design`(backend, cache submodule) |
| R7 | **Prelude export closure** — prelude's live table gains no entry outside its exports post-compile (spec §8.6.4's mechanical shadow) | **`asserted`** (S113 W4: `assert_prelude_closure` at the int live-table insertion seams, tier 3; no false-fires in the landing window) | maintain; the 0604 ghost now names its seam on next firing — `/qa`'s 0604 work consumes the named seam | landed (int) |
| R8 | **RC balance** — every alloc exactly one net free; scope decs match incs | `dynamic-lane` (DEC_CHECK, alloc/free parity, checking-allocator faces) | **W5 tier-5 build**: the three diagnostic modes — no-reuse-after-free quarantine, scrub-freed poisoning, paired alloc/free hard-check — intrinsics-internal, env-gated, no ABI change; plus **W5 tier-3** assertion density at the RC/alloc seams (backend/intrinsics); modes ride the standing tier-4 lane as its detection faces; production stays unasserted by design (cost) — recorded carve-out | `/design`(intrinsics) modes; `/design`(backend) seam asserts; `/qa` lanes (plan-owned) |
| R9 | **Differential-oracle equivalence** — analysis-on ≡ analysis-off observationally + heap-balanced (the meta-invariant; reference semantics of §3d) | **`gated`** (S113 W1: standing nextest-visible lane — `tests/safety_oracle_lane.rs` + `SafetyMatrix`; acceptance = 0641 B-1 RED-under-lane; first catch MS-P7) | maintain; W5 fix wave verifies under lane + tier-5 modes; corpus grows toward the 0623 matrix shapes | landed (`/qa`-owned lane) |
| R10 | **Resolve-once keyed reads hard-fail** (P24) — downstream consumers never re-derive; miss = diagnosed error | `asserted` (S110 hard-error arms + KC-N1..N6 negatives) — a model | maintain; P24 sweep register covers the residual scan census | landed |
| R11 | **Concreteness at codegen** — no `Type::Var` reaches RC-classify / slot emission / mangle | `unconstructable` (P20 S84: slot ⟺ `is_concrete()`) + backstop asserts (incl. CS-1.2's at the mangle) | maintain | landed |
| R12 | **Published-pointer retention** (P22) / ABI-epoch slot freeze | designed (`ownership-inference.md` §5.6), pre-implementation | the R3-machinery sprint lands the slot-freeze assert WITH the mechanism, not after | `/design`(int) at the session-transaction sprint |
| R13 | **Fork-join error-slot ferry** — worker panic reaches the join; no silent swallow (spec §12.4.3) | **`unasserted`** known pre-existing (test-discovery.md owed item) | tier-3 ferry obligation at both fork-join boundaries when actioned | `/design`(intrinsics/backend) — parked, named |
| R14 | **COW count-truth** — the runtime rc==1 in-place branch is sound iff every live independently-owned reference is counted; an uncounted (borrowed) source reaches a COW op only under an analysis-proven bound (result does not outlive the source's scope-dec — the escape gate); the conservative (analysis-off) mode counts everything (all-Owned per `ownership-inference.md` §6.2/R7), making the runtime rc check correct by construction | **partial** (S114 P2 F6 refresh — the S113 outcome overstated this as drained): the S113 W5b landing restored the toggle-off polarity + the escape-gated producer inc, but **match-var-pattern escape-recording (B-2) + link-mode divergence (MS-P7) carry** — B-2 is a TYPECHECK fix (the backend gate is correct and cannot distinguish wrong-`Some(false)`; F4), sharing the S114 schema window; MS-P7's attribution is gated on call-chain evidence (F5) | S114 Tracks A/B: the B-2 escape-fact correction in the typecheck carrier wave (ONE schema window with the `VarRef`/`ApplyRef` flip, 21→22 — F7); 0664 §13.5/§13.7 reconciliation first-within the 0668 `/design`(backend) deployment (the falsified producer-seam inc shape retired from the design record); checks = tier-4 lane + row-6 DEC_CHECK | `/design`(typecheck) B-2; `/design`(backend) 0668/0664; MS-P7 pending attribution |

Maintenance rule: `/arch` re-audits the register at every Phase-2 architecture review; a
new safety-eliding surface (a new analysis, a new mangle family, a new persisted carrier,
a new trust boundary) adds its row **in the change-set that introduces it** — arriving
unregistered is the defect.

## §5. Principle 25 — RATIFIED (user-approved S111 Phase-7 close, 2026-07-18)

> **Principle 25 — Narrowing carries its check: a safety elision is defined against, and
> checkable against, its conservative fallback.**

**Ratified as a SINGLE principle** — the split alternative (the differential-checkability
principle, clauses 1–2, separate from the assert-at-seam principle, clause 3) was offered
and declined; the three clauses are one idea: elision is measured against the conservative
reference. The canonical text — the three parts as framed here (conservative-at-⊤ as
reference semantics / an elision without a reachable conservative fallback is
inadmissible; widening free while narrowing names its justification + check tier, with
green suites + adversarial review as discovery not checks; a foundational safety invariant
asserted at its seam, not merely tested) plus the relationship statement (the enforcement
arm of monotone soundness — P18 for dynamic judgments, P20 extended to analysis claims) —
lives at **`principles/25-narrowing-carries-its-check.md`**, indexed in `principles.md`.
Cite it from there; this section is the ratification record, not a second home
(Principle 7). This document (§§2–4, §6) remains the **binding frame** the ratified
principle governs: the S112 memory-safety-soundness mechanism builds to it.

## §6. Cascade — the `/design` task list for the follow-up increment

Scoped so `/sprint` can dispatch each as one narrow deployment. Ordering: task 1 gates the
0641 fix; tasks 2–4 are independent of it and of each other.

> **W5 status (S113).** Task 1 is the W5 fix-wave increment (§3a/§3c + 0641 corrections
> + the paired backend consume fix; §3b conditional — the named capacity fallback).
> Task 4's R7 assert LANDED S113 W4. Task 5's tier-4 lane LANDED S113 W1. Tasks 2 (i)/(ii)
> and 3 (the backend censuses + cache-boundary generalization) are NOT in W5's ruled
> depth — they remain the S114+ cascade. W5 increment order (ruled at W5 open): tier-5
> modes + tier-3 seam asserts FIRST (detector multipliers), then the tiers-1–2 fix wave
> verified under lane + modes.

1. **`/design`(typecheck) — the monotone walk (gates 0641; consumes §3 as its binding
   frame).** Author the origin/provenance lattice with its explicit ⊤ (§3a) + the
   enumerated, classified transfer-rule table in `design/typecheck/ownership-inference.md`
   §15 (§3c) + the conditional/unconditional origin split at the producer seam (§3b, P20
   shape to be designed). Then land B-1/I-1/I-2 as rule-table corrections. Extend the 0623
   matrix axes (container-store × projection-out × capture) with `/qa`. Correct the CS-5
   B3.2 rustdoc over-claim to the covered axes (0641's named small item). Pair with the
   `/dev`(backend) half `/qa` attributed for B-2/I-2 (the vec-set-result consume seam —
   ownership-independent, wrong values under toggle-off).
2. **`/design`(backend) — elision + identity census.** (i) Census every safety-eliding
   consumer read (protect elision, non-atomic confined RC, S104 spark thunk-RC elision,
   borrow elision, projection elision): each mapped to its summary premise + verified
   safe-direction default on unknown facts — the R2-row discipline made complete. (ii)
   Census every symbol-mint site for R4: each row → decoder witness or disambiguator key;
   `resolution.rs`'s two naming primitives are the natural single home. (iii) The 0637
   forward obligation stays co-landed with the sibling-slot consumer (R5 row).
3. **`/design`(backend, cache) — the persisted-trust boundary (generalizes 0637).** Census
   every index/key/slot in `.meta.json` (R6 row's list is the seed); design the ONE
   validation seam in `deserialise_meta_with_build_id` with a diagnosed `CacheStale` class
   per family. Trust-boundary taxonomy per §2 tier 3: cache bytes are external data —
   diagnose and recompile, never assert.
4. **`/design`(int) — live-table seam assertions.** The R7 guard: `debug_assert!` +
   `MODULE_TRACE` emit at every live-table insertion seam enforcing the prelude-export
   closure (0604's named first step — observability BEFORE the fix, so the next firing
   names the seam). Audit the sibling seams (publication edge, watcher reload,
   redefinition commit) for the same treatment; R12's slot-freeze assert is pinned to the
   session-transaction sprint, not here.
5. **`/qa` (coordination, not tasking — the parallel coverage strategy owns it).** Tier 4
   as a standing, nextest-visible gate (oracle equivalence + RC-balance lanes on every
   emission-affecting change-set; corpus growth toward the matrix shapes). This doc
   supplies the mandate (P25 clause 1–2) and the admissibility rule; lane mechanics,
   cadence, and corpus policy live in `tests/plan/`.

## §7. Manifestation sites on ratification

Per the manifestation-site question: this file is the register's permanent home (canonical
set; `design/arch/CLAUDE.md` row added S111). Ratification LANDED (2026-07-18): the
Principle is filed as `principles/25-narrowing-carries-its-check.md` + indexed in
`principles.md`; the four import-block additions (`arch`/`design`/`dev`/`review` per
`principles/CLAUDE.md`) are tracked by FIXME 0643 (the skill-def files sit outside
`design/arch/`, so the ratifying fire could not edit them directly). Still pending by
design: the §3 walk model manifests in `design/typecheck/ownership-inference.md` §15 (its
owner's home) with this doc citing it — the S112 `/design`(typecheck) increment (§6 task
1); the trust-boundary taxonomy is already carried by the CS-2 ruling record (SPRINT
archive) and lives durably in §2 here + `GotTable` rustdoc.
