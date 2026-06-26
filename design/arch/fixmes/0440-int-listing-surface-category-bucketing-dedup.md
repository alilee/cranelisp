---
number: 0440
target: /design
filed_by: /arch
filed_at: 2026-06-26
sprint_filed: 91
refers_to: src/repl.rs::handle_list, src/repl.rs::handle_exports, src/session_v4/lifecycle.rs::list_user_definitions, src/agent/harvest.rs, src/worker.rs::is_internal_listing_name, design/int/int.md §3.3
status: open
---

# int listing surface — unify the per-entry category-bucketing (the dual-`/list` Principle-7 residue)

## Issue

The S91 single-pipeline audit (BC §6, 2026-06-26) confirmed the compile pipeline
is single-path across `--run`/`--link`/REPL — no mode fork was introduced. The
audit's one residual finding is a **surface-layer (introspection) Principle-7
duplication**, not a compile-path divergence:

There are now **three** independent iterations over a module symbol table that
each re-derive the same `ModuleEntry`/`DefKind` → user-facing category bucketing
(Macros / Traits / Types / Fns / Constructors), plus a fourth filtering site in
the agent harvest:

1. `src/repl.rs::handle_list` — REPL `/list`; returns a formatted `String`.
2. `src/repl.rs::handle_exports` — REPL `/exports`; returns a formatted `String`
   (adds the `is_public()` gate + prefix filter, otherwise the same bucketing).
3. `src/session_v4/lifecycle.rs::list_user_definitions` — the structured
   int-surface (`Vec<SymbolInfo>`) consumed by the test classifier
   (`list_classification_tests.rs`), `tests/facade_pif_rows.rs`, and the agent.
4. `src/agent/harvest.rs` — filters the same internal-name set out of harvested
   source.

These are **REPL-only / introspection-only surfaces** (introspection is
REPL-only per `memory/introspection-repl-only-principle.md`); none is on the
`--run`/`--link` compile path, so this is **not** a Principle-11 violation and
**not** a Blocker.

**Why it matters (the divergence symptom the user surfaced).** The S91 Phase-6
`__expr`-in-`/list` defect leaked in FOUR sibling sites *because each had its own
copy of the internal-name filter*. S91 correctly mitigated the **filter** half by
extracting one predicate — `worker::is_internal_listing_name` over the single
literal `SYNTHETIC_EXPR_WRAPPER` — now shared by all four sites. That closes the
specific `__expr` class of drift. **But the category-bucketing match arms
themselves remain N-copied** (sites 1–3 each transcribe the
`DefKind::Macro`/`Constructor`/`TypeDef`/`TraitDecl` → category mapping
independently). The next "constructors should/shouldn't appear in listing X"
or "new `DefKind` variant" change is the next four-site drift waiting to happen —
exactly the shape that produced the `__expr` bug, one level up from the filter.

## Proposed resolution

Make `list_user_definitions` (the structured `Vec<SymbolInfo>` classifier) the
**single source of truth** for "what category is this entry, and is it a listable
user definition." The REPL renderers (`handle_list`, `handle_exports`) consume its
output and apply only their presentation concerns (the `append_name_category`
formatter they already share; `/exports`'s `is_public()` + prefix filter as a
post-filter on the structured rows). The harvest filter already shares the
predicate; confirm it can consume the same classifier or at minimum stays on the
shared predicate. Net: one bucketing match, three thin presentation adapters —
the same shape S91 already applied to the *filter* predicate, extended to the
*classification* it gates.

This is a `/design` (int) call on the exact seam (does `SymbolInfo` grow a
`Visibility`/public flag so `/exports` can post-filter it? does `handle_list`
format directly off `SymbolInfo` rows?); `/dev` (int) implements; the existing
`list_classification_tests.rs` + `repl_introspection.rs` byte-identity tests pin
behaviour through the refactor.

## Operational implication / Context

- **Severity: Important (not Blocker).** Surface-layer duplication on REPL-only
  paths. The compile-pipeline invariant is intact; this is debt-hygiene that
  removes the recurrence vector for the bug-class the user flagged.
- **Not this-sprint-mandatory.** S91's shared-predicate mitigation stops the
  `__expr`-class bleed; the structural unification is the durable fix and is
  safe to schedule into a future int-hygiene wave.
- **No new failing test required** (per `memory/feedback_no_fixme_with_failing_test.md`
  this is a structural-dedup change request, not a defect repro) — the existing
  classification + byte-identity tests are the regression guard for the refactor.
- Filed by `/arch` from the S91 single-pipeline audit; the verdict and the
  inertness/no-fork findings are recorded at the manifestation site, BC §6
  "Known architectural constraints".
