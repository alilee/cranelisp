---
number: 0944
target: /qa
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: tests/plan/ — carries per-sprint plans and named audit artefacts
  (coverage-gaps.md, negative-coverage.md) but no standing rolling category for
  uniformity-across-variants; .claude/commands/qa.md §Plan rows does not name it
status: open
---

# Standing coverage-audit category: coverage by definition variants

## Issue

The user directed (S108, 2026-07-12) that this be carried as a **rolling** `/qa`
coverage-audit category, not handled as a one-off finding:

> "a category risk that qa should audit coverage against — coverage by definition
> variants. It is an example of codepath duplication that we are trying everything we
> can to eliminate."

It is not recorded anywhere. `tests/plan/coverage-gaps.md` and
`tests/plan/negative-coverage.md` exist as artefacts but neither defines this as a
standing lens, and `.claude/commands/qa.md` does not name it among the audit categories.

**The category.** When the same defect keeps recurring at new sites AND the codebase has
grown a family of near-duplicate helpers to patch each site, the root cause is a
coverage-matrix failure, not N independent bugs — and the variant family is itself the
codepath duplication this project fights hardest. The user's framing: *"with good tests,
needing these variants would have failed."*

Audit any operation that must behave **uniformly** across a family of variants:
definition forms (`defn`/`deftype`/`deftrait`/`defmacro`/`def`), resolution sites, import
shapes (specific / renamed / member / glob / re-export), provenance (explicit import vs
implicit prelude), output kinds. For each family, ask whether a **variant × {positive,
negative} matrix** exists pinning uniformity, and whether it pressures ONE codepath or
each variant has grown its own. A missing cell is where a variant silently diverges.

The S108 instance: def-over-prelude rejection was enforced for `defn`/`defn-`/`deftype`
and silently bypassed by `deftrait`, trait methods, and `defmacro` — against six
`*_or_prelude` resolver variants and a `prelude_fallback` bit threaded through ~93 sites.

**Why both polarities are load-bearing.** A **twin fixture** — the invariant satisfied two
ways, asserting the same outcome (a name via explicit import vs via implicit prelude) —
goes RED at every site that forgot the shared mechanism, forcing one intrinsic
implementation instead of per-site patches. A **negative** cell ("what must NOT happen":
the def-over-prelude rejection, the distinct-terminal poison) catches the sites that
silently accept, exposing a wrong rationale as a live conformance gap rather than a
feature.

This is the class-level counterpart of the single-defect rule that a `/review`-caught
correctness defect is a testing miss.

## Proposed resolution

`/qa` to record it as a standing rolling category in `tests/plan/` — either a new
per-category artefact under `tests/plan/` naming the families currently in scope and
their matrix status, or a section in the existing `tests/plan/coverage-gaps.md` if `/qa`
prefers one artefact. It should state the audit procedure, not just the concept:

1. On seeing a recurring class plus a variant-helper family, stop patching the newest
   site. Name the invariant, enumerate **every** site it governs, and build the
   site × {positive, negative} matrix first — `/qa` designs, `/testing` authors. A site
   omitted from the enumeration is a variant that will regrow.
2. The RED set from that matrix is both the proof of every real gap and the acceptance
   spec for the convergence; the structural criterion is "no per-site variant should be
   NEEDED".
3. Fix coverage before, and as the driver of, the architecture fix.

If `/qa` judges the durable home to be `.claude/commands/qa.md` §Coverage process
instead, that skill-def edit is the user's — record the category in `tests/plan/` and
flag the skill-def line for them.
