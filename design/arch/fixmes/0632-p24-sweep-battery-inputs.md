---
number: 0632
target: /qa
filed_by: /arch
filed_at: 2026-07-17
sprint_filed: 111
refers_to: design/arch/principles/24-resolve-once.md + sprints/SPRINT.md §4 + audits/cranelisp-backend-s110.md §2.1
status: open
---

# Principle-24 sweep: the transcription criterion + pre-seeded register rows

## Context

The S111 Principle-24 enforcement sweep (SPRINT.md §4) is a read-only
verification lane: classify every unindexed iteration compiler-wide as
enumeration (carve-out 1) or identity-scan (defect). `/qa` authors the pattern
battery + classification criteria as plan rows and owns the compiler-wide
register; `/audit`'s frontend-rotation assessment carries the frontend leg.
This FIXME hands `/qa` the `/arch`-confirmed inputs so the plan rows transcribe
rather than re-derive.

## The ask

1. **The criterion is `principles/24-resolve-once.md`, transcribed verbatim —
   no paraphrase.** Confirmed at S111 Phase 3: the acid test ("does the answer
   depend on which entries happen to be present elsewhere, or on the order a
   collection iterates?"), the two carve-outs (¶"Two carve-outs": enumeration
   discipline = complete set consumed + tie is an ambiguity error, never
   first-match; `/search` = the one sanctioned genuine scan, human-facing
   candidates only, REPL-only), and the enforcement paragraph (an
   implementation found scanning is an instance of the defect class, never
   counter-evidence) are the exact classification text. Plan rows cite the
   principle file; divergent restatements are how criteria drift.
2. **Crate scoping (SPRINT.md §4, binding):** `cranelisp-typecheck` → `src/`
   (int) → `cranelisp-frontend`, in that priority order. **Backend is DONE** —
   cite `audits/cranelisp-backend-s110.md` §2.1's classification of its four
   surviving `symbol_tables.iter()` walks as legit enumerations; do not redo.
   `cranelisp-types/resolve.rs` is the sanctioned chain itself.
   Primitives/intrinsics/platform close on a single zero-hit grep pass.
3. **Pre-seeded register row (from the S110 backend audit):**
   `crates/cranelisp-backend/src/jit.rs:117` — platform-symbol registration is
   **last-write-wins** across loaded platform DLLs. Classification:
   *enumeration whose tie-discipline is convention-only* — platform names are
   globally unique today by convention, so no tie has fired, but a name
   collision would be silently resolved by load order (incidental order = the
   acid test's divergence surface). The sweep decides whether it needs a
   structural tie-error (the enumeration-discipline rule: a tie is an
   ambiguity error, never broken by iteration order) or a documented
   uniqueness invariant at the load seam. This row enters the register
   pre-classified as the worked example of the "enumeration vs scan" boundary
   case.

## Closure

`/qa` actions into `tests/plan/` rows (the battery + register home) and deletes
this file.
