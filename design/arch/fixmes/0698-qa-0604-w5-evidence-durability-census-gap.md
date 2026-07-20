---
number: 0698
target: /qa
filed_by: /review
filed_at: 2026-07-20
sprint_filed: 114
refers_to: design/arch/fixmes/0604-*.md + src/imports.rs (census block +
  check_terminal_closure/write_is_closure_valid) + src/worker.rs::commit_staging_to_live
  (:439, live.insert :513) + design/int/prelude-table-write-isolation.md
status: open
---

# 0604 W5 follow-through — evidence durability, census gap, predicate gap

## Severity
Important

## Issue

Three findings from the W5 review of commit `58ac8e46` (C3/0604 chokepoint):

1. **Evidence durability.** The MAJOR re-attribution evidence — this VM now
   reproduces 0604 **25/25 deterministically**; the FIXME premise is FALSE
   (`bit-and` IS a bundled primitive); the phantom public entry bypasses every
   gated src/ install seam — exists ONLY in the `58ac8e46` commit message.
   FIXME 0604 itself was last touched pre-W2 (`fec151ef`) and still records the
   old premise and "no stable RED". A deterministic repro on a known VM is the
   single most valuable asset this defect has ever had; it must be recorded in
   0604 (environment, recipe, rate) before it is lost to context decay.

2. **Census gap (Principle 18 — the census's own greppable-guard clause).**
   The foreground writer census in `src/imports.rs` claims the public-insert
   seam set is CLOSED, but omits `worker.rs::commit_staging_to_live`
   (src/worker.rs:439; `live.insert` at :513) — the staging→live commit that
   writes every typecheck-staged entry (including public Defs) into the live
   table, and the very seam the commit message names as the suspected writer
   ("typecheck staging→live commit"). The entries ORIGINATE cross-crate, but
   the WRITE is a src/ seam and must be dispositioned (route through the gate
   or a named legal-skip with rationale, e.g. "staged entries are own-Defs,
   never Import edges — closure-valid by §8.4"). Until it is dispositioned the
   census cannot support its closure claim, and the "bypasses EVERY src/ install
   seam" evidence statement is unverifiable from the change-set.

3. **Predicate gap (disclosed, needs the doc corrected).**
   `write_is_closure_valid` is a provider-existence check. Per finding 1 the
   live phantom's source (`primitives`) genuinely provides `bit-and`, so the
   landed gate PASSES the actual defect by construction; the commit itself says
   "the correct check is declared-export closure, not provider-existence."
   `design/int/prelude-table-write-isolation.md` §2.2 still records the false
   premise and the provider-existence shape as sufficient (and its doc census
   differs from the as-landed census: no defmacro-register row, no
   staging-commit row). The chokepoint unit fixture
   (`imports/tests.rs::check_terminal_closure_rejects_out_of_closure_public_write`,
   "primitives has NO bit-and") is counterfactual — valid mechanics test,
   misleading comment.

   Forward hazard to record with the corrected check: the
   `form_dispatch.rs::register_macro_in_module` gate call runs under a held
   `get_mut` guard and is safe ONLY because the predicate does no map read for
   non-Import entries. A declared-export-closure check that reads the target
   module's own declared exports would deadlock there (DashMap re-entrancy).

## Proposed resolution

/qa (0604 owner): scribe the W5 evidence into 0604; direct /dev(src) to add the
`commit_staging_to_live` census row (route or legal-skip); with the
deterministic repro in hand, consider instrumenting/gating that seam with the
declared-export-closure check — 25/25 determinism makes locating the writer a
single run, not a hunt. FIXME `target: /design`(int) or fold here: correct
prelude-table-write-isolation.md's premise + census + check shape.

## Context

W5 /review of `58ac8e46`, review priority 3. `insert_detecting_ambiguity`
verified untouched. The four gated seams (install_exports, install_imports,
insert_cluster, defmacro register) match the census's route-through rows;
worker.rs error path via `notify_module_failed` verified sound.
