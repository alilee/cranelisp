---
number: 0641
target: /design
filed_by: /sprint
filed_at: 2026-07-17
sprint_filed: 111
refers_to: crates/cranelisp-typecheck/src/ownership/transfer.rs (VecLit element-store / ProjectionOf composition);
  crates/cranelisp-backend/src/compiler/fn_compiler.rs:1736 (return_is_fresh_by_summary elision) + the CS-5 rustdoc completeness claim;
  design/typecheck/ownership-inference.md §15; design/arch/ownership-inference.md §3.7/§3.7.1; FIXME 0623 (body-shape matrix);
  S111 CS-5 /review Blockers B-1/B-2 + Importants I-1/I-2 (adversarial review of e99535e4)
status: open
---

# False-`Fresh` residual: the ownership walk launders alias provenance through CONTAINER-ELEMENT flow and capture (the §3.7 class, one mechanism deeper)

## Summary — the centrepiece closed vec-assoc COW; the false-`Fresh` CLASS has a residual it did not target

CS-5 (§3.7, `e99535e4`) truthfully declared the vec-set/vec-push COW facts and made them reachable, closing the `vec_assoc_param_mutate_return_uaf` family (17/17). Its adversarial review then found the **same false-`Fresh` → protect-elided → UAF class survives via a mechanism the §3.7 model + the 0623 body-shape matrix do not cover: the transfer walk drops alias provenance at container construction/projection and at capture.** All PRE-EXISTING (byte-stable across CS-5, NOT regressions), all memory-safety.

## The residual vectors (repros committed by /testing, failing-not-ignored)

**B-1 — container-element provenance laundering (the clearest):**
```clojure
(defn f [v] (vec-get [v] 0))          ; no COW op needed
(defn main [] (Pure (vec-get (f [1 2 3]) 1)))
```
`CRANELISP_OWNERSHIP_TRACE=1`: `f: modes=[Owned] result=Fresh` — FALSE. The walk builds `VecLit [v]` with origin `Fresh` (the literal container is fresh), losing that its ELEMENT origin reaches param `v`; `vec-get`'s `ProjectionOf(0)` consumer roots at the fresh container → body origin `Fresh` → `origin_to_result_mode` publishes `Fresh` → `return_is_fresh_by_summary` (`fn_compiler.rs:1736`) elides the protect → scope-exit dec frees the returned alias. `--run` garbage / REPL garbage / **`--link` deterministic `corrupted double-linked list` SIGABRT** / `CRANELISP_NO_OWNERSHIP=1` correct.

**B-2 — producer publishes an unconditional claim from a conditional origin:**
`(defn f [v] (match (vec-set v 1 99) [r r]))` → trace `result=ProjectionOf(0)`. A var-pattern binds the whole (COW `MayParam`) scrutinee, yet the walk publishes UNCONDITIONAL `ProjectionOf(0)` — violates the §3.7 reservation clause ("`AliasOf`/`ProjectionOf` reserved for provable UNCONDITIONAL claims") one level up from the `origin_to_result_mode` `MayParam` arms CS-5 fixed. Latent under today's binary `==Fresh` consumers (they keep protect), but a real producer seam defect. (A 2nd, ownership-INDEPENDENT crash is stacked under this scrutinee/COW shape — fails toggle-off too — needs /qa attribution + a backend fix.)

**I-1 — capture of a let-bound param alias:** `(defn mk [v] (let [r v] (fn [] (vec-get r 1))))` invoked after `mk` returns → reads freed heap; capturing the param DIRECTLY is correct. Capture-accounting laundering.

**I-2 — fresh container holding a COW-aliased element returned:** `(defn f [v] [(vec-set v 0 9)])` → garbage both toggle states. Element-store accounting.

## Requested action (the follow-up ownership increment)

`/design`(typecheck): extend the §15 provenance model with a **container-element axis** — VecLit element-store must propagate the element's origin into the container's provenance (so a projection-out of an aliased element yields the alias origin, not `Fresh`), and match-var-pattern binding must publish a MAY-claim (`MayAliasOf`) when the scrutinee origin is conditional, never unconditional `ProjectionOf`. Add the axis to the **0623 matrix** (container-store × projection-out × capture). `/qa` attributes the toggle-off-independent stacked crash (backend) under B-2/I-2. Then `/dev`(typecheck + backend) implements; the committed repros are the trigger.

**Also correct the CS-5 rustdoc over-claim NOW** (small, `/design` or `/dev`): `fn_compiler.rs` §B3.2 says the `==Fresh` elision is sound iff **leaf** facts are truthful+reachable — the review disproved that (the WALK launders provenance with truthful, reachable leaf facts). Scope the claim honestly to the covered axes until this increment lands.

Fix-vs-carry is `/sprint` + user: the centrepiece delivered its DECLARED scope (vec-assoc COW); this class is pre-existing + new-design-sized. Evidence-gated carry is legitimate (repros committed); or extend in-sprint if the user directs.

## /arch gating note (2026-07-17, user-directed)

**The increment is GATED on the sound-narrowing mechanism — `design/arch/safety-invariants.md` §3 is the binding frame.** The false-`Fresh` class closes by making the transfer walk lattice-monotone (explicit provenance ⊤; enumerated, classified rule table in `design/typecheck/ownership-inference.md` §15; P20 conditional/unconditional origin split at the producer seam), with the differential oracle as the standing end-to-end discharge — B-1/I-1/I-2 then land as rule-table corrections inside that frame, **never as a VecLit spot-fix** (the CS-1.1 → 0640 lesson: an instance-patch without the mechanism is one adversarial review away from the next layer). The `/design`(typecheck) pass authors §3(a)–(c) first; cascade task list at `safety-invariants.md` §6 item 1.
