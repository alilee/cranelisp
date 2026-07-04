---
number: 0516
target: /dev (cranelisp-typecheck)
filed_by: /sprint
filed_at: 2026-07-04
sprint_filed: 102
refers_to: crates/cranelisp-typecheck/src/{checker,program}.rs (check_forms seam, 0514), src/imports.rs (insert_detecting_ambiguity), spec/08-modules.md §8.6.4/§8.6.5
status: open
---

# Complete the collision-rule move to the shared seam — §8.6.5 ambiguity + the #8 REPL import-over-def hole

0514 relocated the §8.6.4 def-over-(import|export|prelude) rejection to the shared `check_forms` Pass-1 seam (all modes). Two pieces of the collision-rule family are NOT yet fully at that shared seam — both surfaced by the S102 /arch mode-gating audit + the Wave-B 0514 landing. Closing them makes the enforcement fully mode-uniform and removes the last host-resident collision logic that is the substrate for the mode-gating cancer class.

## Issue 1 — §8.6.5 import-over-prelude ambiguity is still host-resident (imports.rs)
Wave B added the §8.6.5 distinct-terminal poison as a companion in `src/imports.rs::insert_detecting_ambiguity` (host/int layer), not at the shared typecheck seam. It works and is currently mode-uniform, but the /arch audit flagged it as the next candidate to sprout a mode gate under the same "batch fixture" pressure that produced 0514 — because a language-semantic rejection living in the host layer is exactly that substrate. Relocate §8.6.5 into the shared name-binding path alongside §8.6.4, keyed on the real discriminant (cluster membership / terminal identity), not mode.

## Issue 2 — #8: REPL import-over-def in a SEPARATE later cluster is not rejected (mode-divergence)
Concrete: REPL turn 1 `(defn foo …)`; REPL turn 2 `(import [m [foo]])`. Turn 2 is an import over an existing local def — should reject (§8.6.4, mode-uniform). Today it does NOT: no def is registered in turn 2's cluster, so the def-registration seam doesn't fire, and the import installer skips. **Batch rejects the same shape (import+def in one cluster → seam fires); REPL (separate turns) silently allows it** — the exact dual-path class this whole thread drove out, residual on this one edge. Cure: when installing an import/export, reject if the bare name already resolves to a local `Def` in the current module (the symmetric companion, extended to the cross-cluster REPL case) — ideally unified with Issue 1 at the shared seam.

## Verification
`/qa` owes a failing-not-ignored test for Issue 2 (REPL `defn` then separate-turn `import` of the same name → rejected, mode-parity vs batch). Filed alongside this. When both issues land, `/dev` deletes this FIXME; the src/CLAUDE.md note recording the #8 residual is removed.

## /arch design (acid-test re-audit, 2026-07-04) — SHARED PREDICATE, not shared insert

**There is NO single physical insert chokepoint, and that is deliberate architecture (BC §2), not accident:** import/export install writes the LIVE table int-side in Pass-0 (`src/imports.rs` `insert_detecting_ambiguity` → `insert`); def/typedef register writes the STAGING table typecheck-side in Pass-1 (`program.rs:999`/`register_defn_signature`), committed on cluster Ok. Different tables, crates, passes — kept separate by the ratified `check_forms`-pure-w.r.t.-live boundary. **Do NOT merge the two inserts** (fights the boundary for no soundness gain). The unified unit is ONE shared PREDICATE called at BOTH binding events.

**Acid-test verdict: CONFIRMED early-branch duplication.** Two checks re-answer "does adding name N collide with the existing binding of N?" split by event — `reject_def_over_binding` (checker.rs:1013, def-event, via `resolve_current_or_prelude`) and `insert_detecting_ambiguity` (imports.rs:498, import-event) — each carrying its OWN prelude-outer-scope machinery. #8 is the drift-symptom: the import-event arm `continue`s (imports.rs:553-561), SKIPPING local-def-over-incoming-import.

**Cure — ONE /dev change-set (the companion IS the unification; #8 can't be fixed at the def-seam because in #8 no def registers that turn):**
1. **Lift the §8.6.4 predicate + message into a shared `cranelisp-types` free fn** (beside `resolve_with_fallback`/`resolve_terminal_entry_and_home`): `check_binding_addition(name, incoming_provenance, resolved_home) -> Result`. Rewire `reject_def_over_binding` (checker.rs:1034-1056) to call it — pure refactor, suite stays green. Establishes ONE rule in code.
2. **Same change-set: add the import-event arm** — `insert_detecting_ambiguity` (imports.rs:553-561), when `existing` is a module-LOCAL `Def`/`TypeDef` (home==current) and `new_entry` is an incoming Import/Export, REJECT via the shared helper instead of `continue`. Fires ONLY across clusters (= #8); never double-fires within a cluster (Pass-0 install precedes Pass-1 def-register, so no local def exists at install time).
3. Unit tests: both events × both orders × {same-cluster, separate-cluster REPL} — the separate-turn import-over-def cell is the new guard (mirrors the already-passing batch def+import case). This flips `import_over_def_repl_separate_turn_rejected` GREEN.

Provenance-driven symmetric rule: incoming Def vs existing import/export/prelude ⇒ error (done); incoming Import/Export vs existing local Def ⇒ error (the missing arm); own prior Def same provenance ⇒ redefinition allowed; two Imports distinct terminals ⇒ §8.6.5 poison (unchanged); miss ⇒ free.

**FOLDED INTO THIS CHANGE-SET (user-directed 2026-07-04):** extract `ensure_prelude_bit(ctx, module, sexps, fresh)` to single-source the Replace/Additive prelude-fallback-bit invariant (process_form.rs:194/208), with the fresh-recompute-vs-incremental-delta choice made INSIDE the helper; both arms call it. Not the acid-test disease (the arms do genuinely different transitions, not duplicated work) — but it is the single spot the two arms write the SAME invariant, the drift-risk that is the same theme as #8/0514; single-sourcing it (Principle 7) closes that risk while /dev is already in this file for the collision-rule unification. Behavior-preserving (both arms correct today); suite stays green.

## Operational implication
Not blocking the ownership increment. Completes the "no silent non-compliance path in ANY mode" guarantee (Wave B's claim currently has this one residual). Full context: `sprints/SPRINT.md` §Notes Wave-B + /arch-audit + re-audit entries; `memory/feedback_investigate_suspected_dual_path.md` (the acid test).
