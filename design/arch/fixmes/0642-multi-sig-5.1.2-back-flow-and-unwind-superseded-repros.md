---
number: 0642
target: /design
filed_by: /sprint
filed_at: 2026-07-18
sprint_filed: 111
refers_to: spec/05-definitions.md §5.1.2 (Multi-Signature — I-C correction, user-settled 2026-07-18);
  spec/03-types.md §3.3 (annotations descriptive, no added rigidity);
  crates/cranelisp-typecheck (multi-sig clause inference — the artificial no-back-flow block);
  tests/multi_arity_clause_param_51_2.rs (+ any CS-4.1 param-subtraction / carried CS-4.2 assets) — SUPERSEDED repros asserting REJECTION;
  S111 SPRINT.md §"I-C + 0628 RESOLVED + SCRIBED"
status: open
---

# I-C: implement the corrected §5.1.2 (multi-sig = clauses as separate mutually-recursive functions) and UNWIND the superseded multi-arity change-sets

## What was settled (user-ratified 2026-07-18; spec already scribed)

`spec/05-definitions.md` §5.1.2 previously carried a DRIFT — "each clause checked
independently / no back-flow between clauses." That is corrected. The settled rule:
**a multi-signature `defn` is inference-equivalent to its clauses written as separate,
mutually-recursive top-level functions.** A self-call to a sibling clause pins types
through that clause's signature exactly like any call; annotations are DESCRIPTIVE
(§3.3 — a written type variable does not add rigidity). Only genuine dispatch
ambiguity (same-arity clauses whose signatures can unify) is an error; a
genuinely-polymorphic clause alongside a non-overlapping concrete clause is admissible.

Empirical anchor (the proof the drift was artificial): un-annotated
`(defn rp4 ([p rot] (let [q (rp4 p rot 0)] p)) ([p rot idx] (add-i64 p (add-i64 rot idx))))`
ERRORED under the old rule ("ambiguous, not pinned §5.1.2") but the identical logic as
two separate functions `rp4a`/`rp4b` COMPILES CLEAN. Corrected: `rp4` is
`(Fn [Int Int] Int)`, safe. **The whole multi-arity "memory-safety" saga dissolves** —
the UAF was an artifact of the drift plus monomorphise-by-sibling, not a real defect.

## Requested action (S112 — coordinated typecheck wave, NOT a spot-fix)

1. **/design (typecheck):** refine the multi-sig inference design so clause inference
   flows exactly as separate mutually-recursive functions would — remove the artificial
   independence / no-back-flow block and the "cannot be left polymorphic" restriction;
   keep the §5.1.1 ambiguity + dispatch-coherence checks.
2. **/testing:** UNWIND the superseded assets — the `rp4`-shaped program becomes an
   **accepting** test (asserts it compiles + runs with the corrected type), NOT a
   rejection guard. Retire `multi_arity_clause_param_51_2` (and any CS-4.1
   param-subtraction / carried CS-4.2 rejection assets) that encode the drifted intent.
   Add positive coverage: non-overlapping poly+concrete multi-sig compiles and both
   clauses run; same-arity-unifiable clauses still error (ambiguity, §5.1.1).
3. **/dev (typecheck):** implement; the accepting test + the ambiguity-still-errors
   test are the trigger. Unit test at the inference seam per METHOD §2.2.

## Fix-vs-carry

CARRIED to S112 by /sprint + user (2026-07-18). Spec resolution landed in S111 as the
normative deliverable; implementation is a clean, well-defined typecheck wave sized
alongside the 0628/0639 trait-form wave and the memory-safety-soundness track — all
three are S112 implementation tracks.
