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
   *implies* the property — proof, not sampling. Live exemplar:
   `cranelisp_types::drop_glue_symbol_name` (`module.rs` — every variable-length
   component length-prefixed + hex-encoded, so the encoding is prefix-free and trivially
   decodable: injectivity for **all** inputs by construction, pinned by the
   `module/tests.rs` injectivity/structure battery). The model's S111 origin, CS-1.2's
   backend-local `escape_symbol` (prefix-free escaping + total decoder + round-trip-decode
   test, where the 0633-R3 alphanumeric battery was blind to the class), was DELETED at
   S118 W3 §8 with the second glue-identity home — the discipline it carried now lives in
   the types-owned mint. Rule: **every mangle from semantic identity to symbol either
   ships a decoder witness (or is injective-by-construction with a structure pin) or is
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

**Detection-proof requirement (amended S118 per FIXME 0768; METHOD §2.2 "an instrument
is unverified until it is proven to detect").** The instrument tiers `asserted`, `gated`,
and `dynamic-lane` each require a **cited capability proof** on the row — the test that
plants the fault and observes detection, in the METHOD §2.2 shapes: fail-on-revert for
gates and seam asserts, per-variant negatives for validators, planted-synthetic triggers
for lanes/modes, per-build-configuration for conditional fences. A **live catch of a real
defect** (named, with its sprint record) also qualifies — it is the strongest possible
proof. Without a citation the honest status is **`asserted-but-unproven`** (likewise
`gated-but-unproven` / `lane-unproven`), ranked **below `matrix-tested`**, and it is an
open item against `/arch` exactly as `example-tested` is. The citation SHOULD name the
fault class planted, because that bounds what is proven — the complement is the
instrument's blind spot, and the S115 R7 lesson is that the blind spot is invisible
precisely while the instrument is green ("no false fires" read as health was silence;
the predicate was provider-existence-shaped and structurally could not see the live
phantom). An existence claim about the mechanism ("the assert is landed") is not a
capability claim about the instrument; only the planted fault distinguishes them.

> **S118 row re-audit under the amendment (`/arch`, 2026-07-25 — the 0768 pass).**
> Rows re-graded against the cited-proof requirement: **R10 PROVEN** (the KC-N1..N6
> negative cells observe each hard-error arm fire per variant — the per-variant shape).
> **R13 PROVEN at its stated unit boundary** (the three cited `ivar/tests.rs` cells
> plant both ferry polarities + first-error-wins — planted-fault shape; the composed
> scheduler/reactor boundary remains the owed mechanism, as the row already records).
> **R9 PROVEN** (acceptance was 0641 B-1 RED-under-lane — fail-on-revert by
> construction — and the lane has a named live catch, MS-P7). **R5 and R6 carry NO
> cited planted-fault/fail-on-revert cell** — honest grade `asserted-but-unproven`
> (R5) / `partial-asserted-but-unproven` (R6) until a citation lands (R5's natural
> vehicle: a planted out-of-range slot cell at first touch of the seam or with the
> 0637 consumer change-set; R6's: the S115-scheduled census's per-class `CacheStale`
> negatives). **R7** stands as regraded (`asserted`-but-BLIND) — it is this
> amendment's motivating counterexample, and its S115 cure ships with a synthesized
> injected-trigger test that is fail-on-revert by construction, i.e. arrives
> proof-carrying. **R8's detector-mode grades are `/qa`-owned and deliberately
> awaited**: the S118 Track-A plant triplets (FIXME 0848) are the proofs, and the
> 0857 regrade lands INTO this vocabulary — per-row proven or downgraded, never
> asserted-by-assumption.

> **S116 Phase-2 re-audit (2026-07-22, `/arch`).** R13 is regraded to its
> demonstrated unit boundary and R15 records the typed-context/transitive-discharge
> ruling. R8's detector grades remain `/qa`-owned and are corrected by S116 Track C.

> **S119 Phase-3 exit-gate additions (2026-07-26, `/arch`).** Rows **R17** (heap
> category before RC operation) and **R18** (no fabricated concreteness) added from
> the measured non-concrete release contract
> (`design/backend/non-concrete-release-contract.md` §3.1/§3.2). Naming map: the
> contract's local hyphenated rules R-1/R-2 are register rows R17/R18; its R-3
> (a non-concrete frame is not a legal codegen target — proved, not preferred, §4.3)
> is recorded as the **R11 regrade** below; its R-4 (actionable refusal) is a
> diagnostic-quality bar, not a safety-invariant row. **R11 REGRADED**: its
> `unconstructable` claim was falsified by the S119 census — two hand-mint sites
> bypass the S84 slot gate (see the row). Restoration mechanism is P-1
> (`design/typecheck/non-concrete-producer-obligations.md` §2.1/§6.1); proof
> vehicle is the FIXME-0926 unit gate cell.

| # | Invariant (what safety relies on) | Status today | Mechanism owed | Owner / seam |
|---|---|---|---|---|
| R1 | **Ownership-summary truth** — no published summary/mode lets a consumer elide a protect/inc/atomic the dynamic behavior needs | **§3 mechanism LANDED — the S113-W5 fallback was not needed** (re-verified S115 P2): §3a lattice + §3c rule table (`design/typecheck/ownership-inference.md` §16) + **§3b producer split** all landed S113 W5 (`3297adf8`) — `Origin::{Unconditional,Conditional}` is a *walk-internal* enum (`transfer.rs:150`; no serde, no schema impact — the anticipated bump was unnecessary; persisted `ResultMode` unchanged) and the hard-claim publish arms match ONLY `Unconditional` (`transfer.rs:263–283`). Tier-4 lane `gated` (R9). **Open instances remain**: the MS-P7 chained-face family (the §3.7 `MayAliasOf` family's 4th reaching context — chained links; immediate face fixed `68cd7a96`) proves summary truth still fails for chained may-alias contexts | S115 chained-face fix at the **family grain** (binding invariant: *every may-alias link whose accounting includes a consumer-emitted release needs its protect*) — designed as §16.2 rule-table rows/corrections, NEVER a per-consumer arm; 0693 fence lands before/with; contingent carrier enrichment (if any) = `cranelisp-types` FIXME → `/arch` + one schema window | `/design`(typecheck) `ownership/transfer.rs`; `/qa` gate |
| R2 | **Elision-consumer safe default** — unknown/new summary variants keep the safety op (`== Fresh` binaries; exhaustive `ResultMode` match, no `#[non_exhaustive]`) | `unconstructable` (P18 exhaustiveness; verified no third escape, S111 P3) — a model | maintain; `/review` re-runs the `_ =>`/`== Fresh` grep per landing | landed (types + backend) |
| R3 | **Declared-fact truthfulness + reachability** — a primitive whose emission deviates from the consuming convention carries declared, reachable facts (§3.7 contract) | `matrix-tested` (whole-table sweep, CW-F3a/Fence-3, 5-site/1-helper pin) | evaluate P7 single-sourcing: the emission convention as one artifact consumed by both `ownership_facts.rs` and `vec_codegen` (today the declaration and the emission are un-tied prose twins in two crates) | `/design`(backend + primitives) |
| R4 | **Keyed-identity injectivity** — every mangle semantic-identity → symbol is injective (or additionally disambiguator-keyed) | drop-glue: `witnessed` (CS-1.2 decoder + round-trip — THE tier-2 model). All other mangle families: **unaudited** | **SCHEDULED S115** (SPRINT §B owed item): census every symbol-mint site (`LinkerSymbol` mangles, `impl$FQType$FQTrait` method keys, inner-fn discriminators [span-keyed — verify], GOT data symbols, platform export names); each row → witness or disambiguator | `/design`(backend) `resolution.rs` naming primitives + census |
| R5 | **GOT index in range** — every slot read/write < table size; allocation fallible | `asserted-but-unproven` (0768 amendment: the CS-2 mechanism is landed — always-on `assert!` store/load + fallible allocate + cache-seam diagnosed error — and remains the tier-3 mechanism model, but no planted out-of-range/fail-on-revert cell is cited; proof citation owed at first touch of the seam or with the 0637 consumer change-set) | extend cache-seam validation to `borrowed_sibling_slot` **with** its first consumer (FIXME 0637) — disposition re-affirmed S113 W5: **parked to the first consumer, NOT in-W5** (the sibling is carrier-only, zero production readers since S102; validating an unread index guards nothing, and pre-building the check ahead of its consumer is the P8 half-measure — the co-landing rule IS the mechanism) | `/design`(backend) rides the borrowed-convention track |
| R6 | **Persisted-index trust boundary** — every index/key/slot deserialized from `.meta.json` is validated at load; violation = diagnosed `CacheStale`, never trusted into emission | partial `asserted-but-unproven` (`callable_got_slot` only; no cited planted-`CacheStale` cell — 0768 amendment; the scheduled census's per-class negatives are the proof vehicle). **The 0869 `WrittenTraitImpl` carrier (`design/arch/trait-impl-cache-carrier.md` §5) adds its validation + row extension in its introducing change-set** | **SCHEDULED S115** (SPRINT §B owed item; routed `/dev`(backend, cache) — the seam, taxonomy, and seed list here are the design pin; the census table lands as an artifact in the cache-submodule rustdoc and `/review` verifies its completeness): census every persisted index (sibling slot; `callees` FQs [feeds the future reverse index]; summary param indices — an out-of-range `MayAliasOf(k)` from corrupt bytes indexes `arg_origins[k]`; span keys) → ONE validation seam in `deserialise_meta_with_build_id`, one `CacheStale` class each | `/dev`(backend, cache submodule); `/review` census-completeness |
| R7 | **Prelude export closure** — prelude's live table gains no entry outside its exports post-compile (spec §8.6.4's mechanical shadow) | **`asserted`-but-BLIND to the live phantom (S115 P2 re-audit, verified at HEAD)**: BOTH landed guards — the S113 W4 `assert_prelude_closure` debug-assert AND the S114 W5 `check_terminal_closure` chokepoint (`58ac8e46`) — test **provider-existence-shaped** predicates (`src/imports.rs::{prelude_,}write_is_closure_valid`), and `bit-and` IS a bundled public primitive (`cranelisp-primitives/src/lib.rs:412`), so the live phantom (an *undeclared-PUBLIC* entry outside prelude's DECLARED exports) passes both by construction. The prior "names its seam on next firing" claim was FALSE for this defect. Census also incomplete: `commit_staging_to_live` (src/worker.rs:439/:513) routes through NO gate at HEAD (grep-verified). The S113 predicate's source comment ("bit-and … absent from primitives") carries the falsified premise — correct it in the wave | the S115 0604 early wave (FIXME 0604 re-based plan): **declared-export-closure** predicate (closure PRECOMPUTED — no map read under the DashMap `get_mut` guard, deadlock hazard honored) as an **unconditional diagnosed error** at the chokepoint whose message self-identifies as an internal R7 invariant breach naming the seam (never mistakable for a user diagnostic — the tier-3 sub-form ruling, S115 P2); `commit_staging_to_live` census row dispositioned (route-or-legal-skip); `MODULE_TRACE` at the seam; `/testing` synthesized injected-trigger unit test (fail-on-revert by construction, interleaving-independent) | `/dev`(src) early wave; `/design`(int) §2.2 correction rides |
| R8 | **RC balance** — every alloc exactly one net free; scope decs match incs | `dynamic-lane` — **the W5 tier-5 + tier-3 build LANDED S113 (re-verified S115 P2)**: M1 no-reuse-after-free quarantine (`CRANELISP_QUARANTINE_FREED` + byte cap), M2 scrub-freed poisoning (`CRANELISP_SCRUB_FREED`), M3 alloc/free parity hard-check (`CRANELISP_ALLOC_PARITY`/`_DUMP`) — env-gated, byte-identical-off, hooked on the two single-sourced funnels (`crates/cranelisp-intrinsics/src/diagnostics.rs`), **each mode with unit-tier synthetic self-tests** (`diagnostics/tests.rs` — quarantine ×2, scrub ×2, parity ×4; the §4.1 mandate satisfied); A1–A4 RC/alloc seam checks release-gated on `CRANELISP_RC_DEC_CHECK` (intrinsics funnels + codegen-time gates in `backend/src/heap.rs` + `vec_codegen.rs`) | maintain; the S115 `/qa` matrix verifies the standing `RC_DEC_CHECK` positive-assertion set (designed set vs residue — the 4 referencing test files) and per-mode self-test currency; production stays unasserted by design (cost) — recorded carve-out unchanged | landed (intrinsics + backend); `/qa` lanes (plan-owned) |
| R9 | **Differential-oracle equivalence** — analysis-on ≡ analysis-off observationally + heap-balanced (the meta-invariant; reference semantics of §3d) | **`gated` — PROVEN** (0768: the acceptance was 0641 B-1 RED-under-lane — fail-on-revert by construction — and the lane carries a named live catch, MS-P7) (S113 W1: standing nextest-visible lane — `tests/safety_oracle_lane.rs` + `SafetyMatrix`) | maintain; W5 fix wave verifies under lane + tier-5 modes; corpus grows toward the 0623 matrix shapes | landed (`/qa`-owned lane) |
| R10 | **Resolve-once keyed reads hard-fail** (P24) — downstream consumers never re-derive; miss = diagnosed error | `asserted` — PROVEN (0768: the KC-N1..N6 negatives ARE the cited per-variant detection proof — each observes its hard-error arm fire) — a model | maintain; P24 sweep register covers the residual scan census | landed |
| R11 | **Concreteness at codegen** — no `Type::Var` reaches RC-classify / slot emission / mangle. **S119 step-back restatement (`/arch`, 2026-07-27 — the checkable form; the ruling NC-1 asserts):** the slot invariant is **kind-partitioned** — a GOT slot is the value-capability of an entry whose ONE compiled/hosted body is sound for every instantiation reachable through the slot, with one licence per producer class. For every entry with `callable_got_slot() == Some(_)`: kind **`UserFn`** (incl. mangled mono / multi-sig / macro-clause variants) ⇒ `scheme.ty.is_concrete()` MUST hold — the S84 ⟺, correctly scoped to inference-derived bodies whose emitted RC is type-directed, for which R-3 proves concreteness is the ONLY licence; kind **`Constructor`** ⇒ slotted WITHOUT a scheme predicate, licensed by I-CT′ **representation-parametricity** (the body moves each parameter word opaquely and owes ZERO RC ops on residual words — checked by the ctor-template negative cells + the R17 census ctor partition, `non-concrete-release-contract.md` §4.1, never by a scheme test); kind **`Primitive{Extern}`/`PlatformEffect`** ⇒ licensed by the hand-written body's **declared contract** (R3 declared-fact truthfulness, R16 fences, platform layout-hash/`CLOwned`). The reverse direction for `UserFn` (concrete determined ⇒ slotted) is enforced behaviorally: a missed instance is a loud missing-slot failure (the S84 forcing function), never a silent fallback. **Why the universal phrasing did damage:** "a def has a slot ⟺ `is_concrete()`" stated over ALL defs carried an unstated sanctioned exception (slotted polymorphic ctors and primitives — `bind : ∀a b.…` has held a slot since bootstrap), so it could not be asserted as stated and was asserted nowhere; the two unsanctioned `UserFn` mints hid in that exception's shadow for 35 sprints | **REGRADED `example-tested` (S119 Phase-3 gate)** — the prior `unconstructable` claim was a property of `finalize.rs`'s determination points that two hand-mint sites bypass: `adt.rs:618-637` (synthetic accessors — `Concrete { got_slot }` over `∀a. (Fn [(Bx a)] a)`) and `traits/impl_check.rs:1043,1078-1090` (`scheme::mono` over a residual `fn_type`). Measured: 2,497 release admissions + 5,499 category licences censused, two reproduced SIGSEGVs at the 1023/1024 boundary (`non-concrete-release-contract.md` §2). The class survived S84→S119 exactly because the invariant was one function's property, not a structural gate — and because its stated form was unassertable (see the invariant cell) | **P-1, the universal slot gate** (`non-concrete-producer-obligations.md` §2.1/§6.1 CS-1): ONE mint helper — the only way to obtain a slot in typecheck — restores the `UserFn` clause; the 0926 unit gate cell (polymorphic accessor ⇒ `Polymorphic`, slot-less) is the standing proof; NC-1 (`tests/plan/s119-test-plan.md` §3.7) asserts the kind-partitioned predicate whole-table; backend's R17 census is the consequence-side detector until it reads zero. **S120 structural completion (`/arch`-ruled 2026-07-27):** (i) a **types-owned witness mint** for `UserFnState::Concrete` — a fallible constructor checking `is_concrete()` at the crate boundary, so a fourth mint site outside typecheck's helper is also checked (payload privatisation assessed then, gated on a grep confirming reads are accessor-mediated per `callable_got_slot()` discipline; serde shape unchanged ⇒ NO schema bump); (ii) **R6 load-boundary validation**: a restored `Concrete{slot}` `UserFn` entry re-checks `is_concrete()` at the cache seam → diagnosed `CacheStale` — the durable warm-cache guard beyond the one-time schema window (serde bypasses any smart constructor; the trust boundary must re-check) | `/dev`(typecheck) CS-1; `/dev`(backend) census; `/arch` S120 witness mint |
| R12 | **Published-pointer retention** (P22) / ABI-epoch slot freeze | designed (`ownership-inference.md` §5.6), pre-implementation | the R3-machinery sprint lands the slot-freeze assert WITH the mechanism, not after | `/design`(int) at the session-transaction sprint |
| R13 | **Fork-join error-slot ferry** — worker panic reaches the join; no silent swallow (spec §12.4.3) | **unit-boundary `asserted` — PROVEN at that boundary** (0768: the cited cells plant both ferry polarities — the planted-fault shape) — the production IVar ferry is live independently of test discovery, and `ivar/tests.rs::{test_ivar_force_ferries_panic_to_joiner,ivar_force_backoff_wait_reraises_ferried_panic,ivar_inline_claim_dual_panic_first_error_wins}` plant both ferry polarities and the first-error rule. What remains unproven is the tier-3 composed fork→join boundary through the scheduler/reactor, not the ferry mechanism itself | add one integration assertion at each distinct production fork-join composition boundary; do not rebuild or re-defer the already-proven IVar mechanism | `/qa` integration tier with `/design`(intrinsics) boundary census |
| R14 | **COW count-truth** — the runtime rc==1 in-place branch is sound iff every live independently-owned reference is counted; an uncounted (borrowed) source reaches a COW op only under an analysis-proven bound (result does not outlive the source's scope-dec — the escape gate); the conservative (analysis-off) mode counts everything (all-Owned per `ownership-inference.md` §6.2/R7), making the runtime rc check correct by construction | **partial — S115 P2 refresh**: the S114 gates DISCHARGED — **B-2 escape-fact correction LANDED** (Track A carrier wave, ONE schema window 21→22) and **MS-P7 attribution RESOLVED** (W3 evidence brief `078d324b`: CLIF byte-identical `--run`/`--link`, the shared IR contains the double-dec — the mode axis was only the detector; owner = typecheck ownership) with the **immediate face FIXED** (`68cd7a96`, `ProjectionOf` escape-force). **Open residue = the chained-face family** (nested-projection; let-chained intermediate; the unprobed Conditional-container sibling — probe-first) — the R1 row's S115 fix | the S115 chained-face fix under the family-grain invariant (see R1); negative control stays GREEN (whole-value nested transfer projected by the CALLER); checks = tier-4 lane + row-R8 DEC_CHECK | `/design`(typecheck) chained faces; `/dev`(backend) 0693 fence rides before/with |
| R15 | **Transitive discharge and typed-context ownership** — replacing or releasing an owned heap slot discharges every transitively owned heap field, at arbitrary finite value depth; when static type is no longer carried, ownership must already have transferred to a named type-aware releasing owner | **ruled, implementation partial (S116 P3 interface ruling)** — retain the two-word `HeapHeader { alloc_size, rc }`; no type/drop word and no generic type-erased deep release. Generated code has static type and must call reusable type-directed glue. This includes displacement inside typed code: a TCO tail jump that replaces a loop-parameter slot releases the superseded value unless the existing transfer/COW predicate proves that exact owner moves forward. Runtime protocol consumers own their known node layouts. At the result exit, int carries `(i64, Type)`, narrows once to `ConcreteType`, and reads the module-qualified glue identity/address through the approved keyed contract (`drop_glue_symbol_name` + `CompilationArtifacts.drop_glues` for fresh JIT; existing linker resolution for cache/link), retaining the JIT/object owner through last observation and release. Platform/DLL values remain governed by typed `CLOwned<T>`/callback contracts. The backend's `MAX_DROP_GLUE_DEPTH = 4` shallow-dec fallback violates this invariant and must be removed, not raised | S116 Track A first reduces the corruption face, then `/design`(backend) specifies reusable named/per-concrete drop glue whose recursion follows runtime values rather than compiler inlining depth. The TCO slot-replacement seam consumes that mechanism under one backend-owned replacement/transfer predicate; it does not gain a bespoke shallow dec. `/design`(int) consumes the exact types-owned name + backend artifact projection recorded in `interfaces.md`, as one result-release protocol across fresh JIT/cache-hit/REPL/run/link. Every displacement/exit gets value-before-release, move/exemption, keyed-presence, retention-through-call, and exact-once negative cells. No third header word, new ABI field, generic releaser, ambient lookup, or second compile entry | `/arch` types naming contract + backend API approval; `/design`(backend) generated glue/TCO/artifact; `/design`(int) result boundary; `/qa` bounded depth/displacement/exit matrix |
| R16 | **Structural embedding takes exactly one reference (RE-1/RE-2, S118 W2b — FIXME 0835)** — a runtime helper that embeds an existing heap structure into a new one *by pointer* takes exactly one `rc_inc`, on the node it stores; the auditable corollary is that the inc count for one embed is **1, independent of the embedded structure's size and depth** (a producer whose inc count scales with `\|structure\|` is minting references no owner holds). Dual: every `cranelisp-intrinsics::drop::consume_*` is tree-ownership drop glue — releases the one handed reference, descends only on the last — and is structurally incapable of discharging an unowned reference, so RE-1 is the only producer discipline this consumer can be paired with | `asserted` — **PROVEN** (RED-first fail-on-revert per the S118 W2b record: the tier-3 counter-based fence rows `crates/cranelisp-primitives/src/marshal/tests.rs::{re1_embed_takes_exactly_one_reference_whatever_the_tail_size, re1_embed_inc_tally_is_one_per_call_plus_one_per_copied_item}` — the second pins the inc *tally* at `\|xs\|+1`, closing the 0885 finding that a balance-only fence admitted the rejected move-variant; fault classes bounded: producer over-inc, deep-walk regression, move-variant) | maintain; any NEW embedding producer adds its own inc-count fence in the introducing change-set (this register's maintenance rule); the S119 option-paper typed-handle option (`ownership-stratum-options.md` §2) would raise this row toward tier 1 (unrepresentable) | `/dev`(runtime pair) `marshal.rs`; full statement `design/runtime/s118-structural-embedding-ownership.md` §2 + `design/primitives/primitives.md` §4 #13 |
| R17 | **Heap category before RC operation** (contract rule R-1) — no RC operation (inc or dec, guarded or unguarded, at any seam) is emitted on a word whose heap category codegen cannot name from the word's own static type. A residual type variable is the *absence* of a category, not `Mixed`; the `NULLARY_TAG_THRESHOLD` guard discriminates tags from pointers, **never scalars from pointers**, and citing it as a pointer test is the defect | `unasserted` — the single violating seam is `signature_heap_category`'s `Err(_) ⇒ HeapCategory::Mixed` arm (`crates/cranelisp-backend/src/compiler/rc_emission.rs:486-495`), measured S119 at 3,646 bare-`Var` licences across the suite with two reproduced SIGSEGVs (`non-concrete-release-contract.md` §2.3–§2.5). **The declaration channel is a structural feeder (0929 site 3, verified):** `context.rs:265-284` (`extract_constructor`) materialises `CtorMeta`/`CtorField` from the ctor *declaration's* scheme, so a polymorphic product's field type is `Type::Var(a)` permanently — the arm-flip criterion (census reads zero) is **unreachable while this channel stands**; NC-5 (`s119-test-plan.md` §3.7) is the stated flip precondition | the §5.1 **permanent debug-profile census instrument** (0768-compliant: it has already detected — the S119 design-window census is its live catch), then a per-family flip of the arm to a **located error** gated on measured zero traffic; the arm is the gate on its own removal. **Declaration-channel cure seam (`/arch`-ruled 2026-07-27, 0929 ask 4):** ctor field-type materialisation for category/glue purposes delegates to the **types-owned refusing projection** (`cranelisp-types/src/heap.rs::ctor_field_concrete_types`, the R18 model site) or an instantiation-substituting sibling landed beside it in `heap.rs` — never a hand-rolled `scheme.ty` params walk (the `context.rs:280` `unwrap_or(Type::Int)` is that walk's fabricating arm); the backend-interior carrier shape (`CtorField { ty: ConcreteType }`, instantiation keying) is `/design`(backend)'s inside the release-contract window. End state: `asserted` (tier-3 located hard-fail at the seam) | `/dev`(backend) `rc_emission.rs`; `/design`(backend) CtorMeta; contract `non-concrete-release-contract.md` §3.1/§5.1 |
| R18 | **No fabricated concreteness** (contract rule R-2; Principle 25 applied to the type channel) — no component presents a downstream gate with a type, category, shape, or mode more concrete than what it actually knows in order to pass a gate that would otherwise refuse. A gate that cannot be satisfied is a **producer obligation**, never a licence to invent the missing fact. **Model sites — the required spelling (0929 ask 2):** `crates/cranelisp-typecheck/src/program/support.rs:321` (explicit `ViewBuildError::NotConcrete` match on a documented legitimate case) and `crates/cranelisp-types/src/heap.rs:310-334` (`ctor_field_concrete_types` — one residual field refuses the whole ctor via `Option` collect, "conservatively ineligible") | `unasserted` — **instance census extended S119 (0929 asks 1/discharge; verified at source 2026-07-27).** The three contract instances: backend `Err ⇒ Mixed` (`rc_emission.rs:493`), backend's type-keyed shallow-dec arm (`fn_compiler.rs:1287`), typecheck lenient `→ ConcreteType::Int` (`cranelisp-types/src/mono_expr.rs:836-841`). Plus, from the 0929 census: **(4)** `cranelisp-typecheck/src/ownership/fixpoint.rs:221` — `unwrap_or(ConcreteType::String)` seeding per-param ownership facts; graded an **ungraded narrowing owing its P25 check** (the rustdoc's soundness claim covers only the Copy⊑Borrowed edge; nothing checks that a residual-typed param may legally *stay* below ⊤ `Owned` through the fixpoint — the elide-an-inc class); disposition: gain the check + the NC-3(b) fail-on-revert row, or a proof that promotes it to the model list; owner `/dev`(typecheck). **(5)** `cranelisp-backend/src/drop_glue.rs:398` — `unwrap_or(ConcreteType::Int)` for a missing Vec elem arg; disposition: **located refusal** per the `:497-505` pattern, never Int-elem glue ("believed dead" is graded-by-inspection, the Assurance failure state); owner `/dev`(backend). **(6)** `cranelisp-backend/src/compiler/context.rs:280` — `unwrap_or(Type::Int)` when `field_count` exceeds the scheme's params; **Type-side laundering** (fabricates BEFORE the boundary, then passes `from_type`); disposition: located refusal; owner `/dev`(backend), rides the R17 declaration-channel cure. **(7)** `cranelisp-backend/src/compiler/fn_compiler.rs:1214` — defensive dead arm (preceding filter guarantees `Some`); wrong spelling only (`expect`/`filter_map`); low severity. **(8)** int trio `src/eval.rs:586` / `src/repl/commands.rs:632` / `src/pipeline.rs:133` — absent display/expr type defaults to `Type::Int` flowing toward the R15 `(i64, Type)` result-release seam; **severity ungraded — grading owed by `/design`(int)**, never assumed benign | backend: R17's census + arm flip covers the backend instances; typecheck: **P-1 makes a fabricating mint unconstructable** (tier 1 — the ONE helper is the only slot mint) and the L-1/L-2/L-3 defaulting step replaces the lenient fabrication, with its own lenient-fallback census whose zero reading is the flip criterion (`non-concrete-producer-obligations.md` §3). Each fabricating arm becomes the gate on its own removal. **Structural-closure ruling (0929 ask 3, `/qa` recommendation ACCEPTED 2026-07-27): census-as-enforcement.** `ConcreteType`'s variants stay `pub` — exhaustive backend matching and legitimate known-Int literals are load-bearing; sealing is rejected. NC-2 (families A+B: `from_type` discards AND pre-boundary `Type::…` laundering; pinned allow-list, every entry citing an open defect, a NEW site REDs the cell in its own change-set, detection proof per 0768) is the standing enforcement. Once NC-2 lands with its proof, the row's residual grade is **asserted-with-a-named-falsifier** (falsifiers: the census pattern firing, or a fabricating literal outside `unwrap_or` position found by the next sweep) | `/dev`(backend) + `/dev`(typecheck) + `/design`(int) grading; contracts `non-concrete-release-contract.md` §3.2 + `non-concrete-producer-obligations.md` §2–§3 |

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
3. **The persisted-trust boundary (generalizes 0637).** Census
   every index/key/slot in `.meta.json` (R6 row's list is the seed); design the ONE
   validation seam in `deserialise_meta_with_build_id` with a diagnosed `CacheStale` class
   per family. Trust-boundary taxonomy per §2 tier 3: cache bytes are external data —
   diagnose and recompile, never assert. *(S115 P2 re-route: executed as a `/dev`(backend,
   cache) change-set — the R6 row + this taxonomy + the named seam are the design pin; the
   census table lands in the cache-submodule rustdoc and `/review` verifies completeness.)*
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
