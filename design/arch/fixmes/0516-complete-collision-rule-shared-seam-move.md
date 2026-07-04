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

## Operational implication
Not blocking the ownership increment. Completes the "no silent non-compliance path in ANY mode" guarantee (Wave B's claim currently has this one residual). Full context: `sprints/SPRINT.md` §Notes Wave-B + /arch-audit entries; `memory/feedback_investigate_suspected_dual_path.md` (the acid test).
