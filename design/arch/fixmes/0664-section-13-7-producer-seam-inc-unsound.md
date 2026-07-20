---
number: 0664
target: /design
filed_by: /dev
filed_at: 2026-07-19
sprint_filed: 113
refers_to: design/backend/ownership-codegen.md §13.7 (+ §13.5 matrix cell); crates/cranelisp-backend/src/compiler/vec_codegen.rs (SourceOwnership COW cores); tests/false_fresh_provenance_residual.rs (B-2/I-2); tests/safety_oracle_lane.rs (MS-P7); tests/ownership_reuse.rs (l_c3_*); tests/clif_golden_lane.rs
status: open
---

# §13.7 producer-seam inc is UNSOUND — cannot be both differential-oracle-compliant and loop-safe

## Severity

Important (blocks the W5b B-2/I-2/MS-P7 flips; the fix as designed regresses green fences)

## Summary

The §13.7 fix ("the mutate/grow same-pointer branch under `SourceOwnership::Borrowed`
must emit one `rc_inc` on the returned pointer") is **empirically unsound**. Landing
it as stated flips B-2/I-2/MS-P7 but **regresses two green fences**; every attempt to
narrow it hits a fundamental conflict between the design's own two acceptance
requirements. `/dev` did NOT land it (no-regression discipline); §15 (the tier-3
seam asserts) landed clean and byte-identical-off. B-2/I-2/MS-P7 stay RED, attributed
here.

## The `/dev` root-cause investigation (the §13.3 twice-burned discipline)

Attribution CONFIRMED against `CRANELISP_RC_STATS` + `CRANELISP_NO_OWNERSHIP=1` on the
two repros (toggle-off): the mutate branch IS taken (`reuse_hit=1`), the result is
garbage (freed-heap read), `allocs==deallocs` with a correct-value MISS — the missing
inc, not a spurious consume dec. So far the design's hypothesis held.

**But the unconditional producer-seam inc over-retains two shapes the design's
Var-only examples missed** (both reproduced, both green-before / RED-after the inc):

1. **Fresh-temporary source** — `(vec-len (vec-set [10 20 30] 0 99))`. The literal is
   a temp (rc=1) that TRANSFERS into the result; it has no separate scope-dec. The
   inc → rc=2 → **leak** (1 alloc, 0 dealloc; `ALLOC_PARITY` IMBALANCE; the
   `vec_codegen::tests::vec_lifecycle_is_rc_balanced` fence). `/dev` narrowed the fix
   to Var sources only (`Borrowed { source_scope_bound }`), which fixes THIS.

2. **Loop-threaded in-place churn** — `(recur (vec-set v i x))`, `v` a loop param
   (a `Var`). The result transfers via `recur` to the next iteration (becomes the new
   `v`); there is NO separate scope-dec of the old value. The inc → rc=2 → the next
   iteration's COW sees rc>1 → COPY branch → **alloc scales with iteration count**
   (`ownership_reuse::l_c3_reuse_heap_balance_iteration_independent` +
   `l_c3_sustained_epoch_allocs_independent_of_mutation_count`; also drifts the
   `04_vec_cow_loop` golden frame). The `source_scope_bound` Var-gate does NOT fix
   this — the loop source IS a Var. **Verified: disabling the inc flips both l_c3
   tests back to GREEN.**

## Why no producer-seam rule works (the fundamental conflict)

The correct discriminator is **escape**: inc iff the result outlives the source
binding's scope-dec.

| case | source | result destination | needs inc? |
|---|---|---|---|
| B-2/I-2 | `Var` param | returned / stored in returned container | **yes** |
| negative | `Var` | consumed in-frame (`vec-len`) | no (scope elides the alias drop) |
| loop | `Var` loop param | transferred via `recur` | **no** (in-place) |
| fresh temp | literal | any | no (transfers) |

Escape is an **analysis-dependent** fact (`MonoExpr::Apply.escapes`, read via
`node_escapes`). But §13.7's acceptance requires the fix to also correct the
**toggle-off** conservative lowering (`CRANELISP_NO_OWNERSHIP=1`, "analysis-on ==
analysis-off == correct value"), where the escape fact is ABSENT (`None`). So:

- **inc-always** (the design): toggle-off B-2/I-2 correct, but the loop regresses in
  BOTH toggle states.
- **inc-iff-escape**: loop safe, but toggle-off B-2/I-2 wrong (escape fact absent).

**No producer-seam rule satisfies both.** The §13.7 premise — an analysis-independent
producer inc — is unachievable: escape is inherently a consumer-context property, not
a producer-site one.

## Recommended re-framing (for /design + /qa)

The escaping-alias UAF is a **consumer-context** property, so the fix likely belongs at
the seams that MAKE the result escape and can see it structurally, analysis-independently:
- the return-boundary / match-var-bind that returns a value aliasing a scope-dec'd
  binding, and the vec-lit element store that keeps such an alias — inc iff the stored/
  returned value is a live-binding alias (a `Var`-rooted COW result), a structural check.
- OR accept that B-2/I-2's *toggle-off* correctness is out of reach without a carrier and
  re-scope the acceptance (drop the toggle-off requirement for these two, gate the inc on
  `node_escapes == Some(true)` for the analysis-on default — which flips the committed
  default-mode B-2/I-2/MS-P7 e2e faces and does NOT regress the loop; `/dev` can land this
  immediately if /design/qa rule the toggle-off differential a separate follow-on).

The design's §13.5 negative-cell claim ("`(vec-len (vec-set v 0 9))` … the inc is paired
by the temporary drop") is only true for a **`Var`** source; it is false for a literal
source (leak) and says nothing about the loop-transfer case. §13.7 + §13.5 both need the
correction.

## /arch RULING (2026-07-19, W5b impasse) — the impasse dissolves: the toggle-off path contains the defect

**The joint acceptance was unsatisfiable only because the "conservative" lowering is not
conservative.** Verified at the seam: `cow_source_ownership` (`vec_codegen.rs:576-582`)
defaults every non-return-source to `SourceOwnership::Borrowed` — a purely SYNTACTIC
classifier, gated on neither the analysis facts nor the toggle. So the toggle-off lowering
carries a static borrow narrowing (an uncounted stake at a COW site) with no check and no
register row. But the spine already DEFINES toggle-off as the conservative **all-Owned**
lowering (`design/arch/ownership-inference.md` §6.2 / the R7 oracle; P25 clause 1) — this is
not a re-scope question, it is a defect against the ruled definition of the toggle. With an
untruthful count, the COW rc==1 branch reuses a vector someone else still references; that
is the whole B-2/I-2/MS-P7 mechanism, in both toggle states.

**The governing invariant (new register row R14, `safety-invariants.md` §4): COW
count-truth.** The runtime rc==1 in-place branch is sound iff every live
independently-owned reference is counted. An uncounted (borrowed) source may reach a COW op
only under an analysis-proven bound (the result does not outlive the source's scope-dec —
the escape gate); the conservative mode counts everything, and then the runtime rc check
makes it correct by construction (rc≥2 ⇒ copy).

**Ruled shape — candidate (b) as diagnosis, escape-gated producer inc as mechanism, ONE
change-set with two halves:**

1. **Polarity restore (toggle-off = all-Owned, as already ruled).** Analysis-off ⇒
   `SourceOwnership::Borrowed` is unreachable; every COW source is counted; the copy branch
   fires when rc≥2. The loop allocates per iteration toggle-off — that is what conservative
   MEANS (monotone soundness: only performance degrades). This half is what makes the
   differential oracle's reference semantics sound again for COW shapes.
2. **Analysis-on: `Borrowed` classification comes only from the settled ownership facts
   (the landed Origin lattice — a fresh temp is Fresh/transfer, never Borrowed), and the
   COW core incs iff the result escapes the source's scope (`node_escapes`); a
   recur-transfer is not an escape (in-frame loop-header jump) so l_c3 reuse is preserved;
   an ABSENT escape fact defaults to inc (the UAF-safe direction, P25).** This is /dev's
   named immediately-landable option — now WITH toggle-off correctness restored rather than
   waived.

**The halves are NOT separable**: landing the gate without the polarity restore leaves the
oracle lane comparing correct-on against garbage-off (divergent cells, acceptance-dirty);
landing polarity without the gate leaves the analysis-on REDs. One change-set.

**Candidate (a) — consumer-seam alias-inc — REJECTED.** Per-consumer copies of the inc
decision at every consume shape (match-bind, vec-lit store, projection, return) are the P7
mirror family, and a future consume shape misses the rule by construction (the
enumeration-miss class). Escape is computed by the analysis and recorded on the node — the
producer reads the settled fact (P26 shape); consumers re-deriving it structurally is
distributed re-derivation.

**Cascade (same change-set or paired):** `/design`(backend) corrects
`design/backend/ownership-codegen.md` §13.5 (the negative-cell claim is Var-source-only —
false for literal, silent on loop-transfer) + §13.7 (the analysis-independent-producer-inc
premise is retracted for the ruled shape); rule-table row per §3c: the borrowed-COW passing
is a NARROWING (justification = escape analysis; check = tier-4 lane + the row-6 DEC_CHECK
already landed). `/qa`: any fence asserting reuse/alloc-independence UNDER TOGGLE-OFF
re-scopes to analysis-on (the reuse is an optimization, never a conservative-mode
guarantee); scoped golden re-baseline for toggle-off drift per the §6.2 precedent.

**Timing: in-sprint W5b extension** — the classifier is ONE localized site (verified) and
the gate is /dev-named-landable; both halves in one change-set, verified under lane+modes,
the 7 REDs are the acceptance. **Named fallback:** if the polarity restore surfaces
multi-seam coupling beyond `cow_source_ownership` + the caller-side arg convention at COW
sites, B-2/I-2/MS-P7 carry to S114 with this ruling as the binding frame and the R14 row
annotated `unasserted — oracle reference compromised for COW shapes` (an open register hole
against /arch, honestly recorded; W5's spine — detectors + frame + B-1 — stands delivered
either way).

## What /dev landed (W5b + the ruled W5b extension)

- **§15 tier-3 seam asserts** (byte-identical-off): row 6 (`heap::emit_rc_dec_check_gated`
  shared seam extends `CRANELISP_RC_DEC_CHECK` to the Vec-aware dec) + row 5 (vec-get
  elision self-check, P25). Rows 1-4 deferred (SSA-seam fact-carriers absent).

- **The ruled two-halves COW fix — LANDED (partial), no regression.**
  - **Half 1 (polarity restore, R14 count-truth):** `cow_source_ownership` toggle-off ⇒
    all-`Owned`, `Borrowed` unreachable; the COW site COUNTS a live-`Var` source
    (`cow_source_needs_toggle_off_count` inc) ⇒ rc≥2 ⇒ runtime copy branch ⇒ correct by
    construction. A fresh producing temp is classified `Owned` (transfer), never `Borrowed`.
  - **Half 2 (escape-gated inc):** analysis-ON, a live-`Var` `Borrowed { retain_reused }`;
    the mutate/grow inc fires iff `node_escapes(cow_apply) != Some(false)` (escape OR
    absent ⇒ inc, P25; `Some(false)` recur-transfer / in-frame ⇒ no inc). `node_escapes`
    threaded from the apply dispatch to the COW seam (`FnCompiler::pending_cow_escapes`).
  - **Flips (verified toggle-on AND toggle-off):** I-2 ×2 (`fresh_container_holding_cow_
    aliased_element_{repl,link}`) + I-1 ×2 (`container_element_provenance_returned_param_
    {repl,link}`). **No regression**: l_c3 ×2 GREEN (escape gate → no inc for the recur
    loop, in-place reuse preserved), golden byte-identical (no re-baseline), `vec_lifecycle`
    (fresh-temp) GREEN. Counterexample unit cells added (`cow_polarity_tests`: BorrowedInFrame
    / Owned = zero inc; BorrowedEscaping = one inc).

- **B-2 ×2 + MS-P7 CARRY to S114 (the ruling's NAMED FALLBACK — coupling beyond the COW
  seam).** Root confirmed empirically:
  - **B-2** `(match (vec-set v 1 99) [r r])`: the COW `Apply` carries **`escapes=Some(false)`**
    (typecheck's `match-var-pattern-unconditional-ProjectionOf` escape-recording bug — the
    result escapes via the var-pattern→return but is recorded non-escaping). The escape gate
    correctly declines to inc a "non-escaping" result; the match then dec's the scrutinee
    while `r` returns it ⇒ UAF. The gate CANNOT distinguish this wrong-`Some(false)` from the
    correct-`Some(false)` loop (both present-and-false), so no backend rule flips it — it
    needs the **typecheck escape fact corrected** for the match-var-pattern transfer. This is
    a DIFFERENT typecheck seam than the §16 half that landed. (Confirms the ruling's Half-2
    dependency on a correct recorded escape fact; the fact is present-but-wrong here, not
    absent, so the P25 default does not save it.)
  - **MS-P7** `safety_lane_cow_set_read_returns_set_value_abort_free_red`: REPL + `--run`
    return 9 (both toggles — the COW half is correct); the `--link` face still diverges
    (per-turn JIT vs whole-module ObjectModule) — a REPL-vs-link seam, not the COW.

  Both carry to S114 with this ruling as the binding frame; **R14 is satisfied for the
  classifiable (count-truth) cases** (I-2/I-1, toggle correct-by-construction) and annotated
  `partial — match-var-pattern escape-recording (B-2) + link-mode divergence (MS-P7) carry`
  for the two match/link-coupled faces.

- **NOT** the earlier unconditional producer-seam inc (falsified above; it flips B-2/MS-P7
  but regresses l_c3 + golden — the reason the escape gate is the ruled shape).
