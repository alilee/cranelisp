---
number: 0927
target: /design (int)
filed_by: /arch
filed_at: 2026-07-26
sprint_filed: 119
refers_to: design/arch/bounded-contexts.md §6 (the S119 macro-clause ABI ownership
  ruling bullet — the canonical statement);
  design/int/macro-turn-ownership.md §3 Rule 0, §8 D0/D4, §12 (the open
  dependency this answers);
  src/process_form/macro_clause.rs (prepare_macro_clause_turn — the pin seam);
  crates/cranelisp-typecheck/src/ownership/publish.rs:38 (why "by construction"
  was not available)
status: open
---

# Absorb the FIXME-0922 Rule-0 enforcement ruling into `macro-turn-ownership.md`

`/arch` ruled the tranche-B boundary question at the S119 Phase-3 exit gate
(FIXME 0922, resolved and deleted). The canonical statement now lives in
`design/arch/bounded-contexts.md` §6 (the new macro-clause-ABI bullet). Summary:

1. **Not satisfied by construction today.** Clause defns run the full
   `check_forms` path and the ownership fixpoint publishes summaries onto
   callable entries (`ownership/publish.rs:38`); a fresh-result clause can
   legally classify `Mode::Borrowed` and backend elides its parameter release.
   The declaration therefore needs a structural pin, not a normative statement
   about an accident.
2. **The pin lives at int's clause-preparation seam**: after `check_forms`
   returns and before the clause entry is published for codegen, int CLEARS the
   synthesized clause entry's `mode_summary`. Summary-absent ⇒ the all-Owned
   Decision-24 compilation — exactly the convention `SexpListToSexpI64V1` now
   declares. Widening toward Owned is always sound; the cost is a few redundant
   RC ops in clause bodies (compile-time only). Structural under Principle 19:
   int knows clause-ness by construction (it synthesized the defn); no
   name-prefix privileging enters typecheck or backend. No `cranelisp-types`
   delta, no schema delta, no public-API delta.
3. **D4's fence lives in int**: a unit row over the prepared turn asserting the
   published clause entry carries NO mode summary — fails if a future inference
   widening reattaches one. D0's CLIF measurement stands unchanged as the
   binding emission-side gate before Rules 1–3 land.

## Ask

Fold this into `macro-turn-ownership.md` (§3 Rule 0's enforcement note, §8 D4's
location, §12's second bullet resolves), and hand the pin + fence to the
`/dev`(int) obligations list. Delete this FIXME when absorbed.
