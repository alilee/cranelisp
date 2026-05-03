# Legacy test plans — provenance only

These documents are superseded. Do NOT consult as ground truth.

| File | Replaced by | Reason |
|---|---|---|
| `strategy.md` | `../PLAN.md §"Strategy — two tiers, no middle"` | Original four-layer pyramid (unit → boundary → integration → e2e) predated the v4 `CompilerSession` architecture. The integration tier coupled to `compile_unit()`/`ReplSession` and drifted with every `session_v4`/`worker` refactor. Strategy pinned 2026-05-03 to two tiers (e2e against the exe, unit inside the crate) — recorded in `memory/project_test_strategy.md`. |
| `ring0.md`, `ring1.md`, `ring2.md`, `ring3.md`, `ring4.md` | `../PLAN.md` (incremental) | Ring-by-ring phasing was the Sprint-0..Sprint-22 delivery model. Project moved past it; rings were superseded by sprint-by-sprint waves under METHOD.md. Coverage rows live in `../PLAN.md` as one continuous spec→tests register, not partitioned by ring. |
| `ring0-readiness.md` | n/a (closed) | Ring 0 readiness check from Sprint 0; permanent context, no successor. |
| `sprint-61-plan-gap-retro.md` | `../PLAN.md §"Authoring discipline"` (Phase 3a derivation rule) | Lesson absorbed: Phase 3a derivation includes at least one property-level row per defect class. Retro itself preserved here for provenance. |
| `tempdir-audit.md` | `../../CLAUDE.md §"Fresh Temp Directory per Test"` (rule) + `../helpers.md §"Design constraints"` (enforcement) | Audit closed Sprint 61 Wave 5. Rule landed; the e2e helper API enforces tmpdir discipline by construction. |
| `neg-coverage-candidates.md` | `../negative-coverage.md` (running register) | Sprint 61 shortlist; promotions absorbed into the running register. |

The current canonical set of plan documents:

- `../PLAN.md` — normative spec → tests bridge
- `../helpers.md` — e2e helper API design
- `../ledger.md` — failure ledger
- `../risks.md` — qualitative risk register
- `../coverage-gaps.md` — per-crate coverage analysis (refreshed on cadence)
- `../negative-coverage.md` — `[Tested]` → `[Tested+Neg]` upgrade register
