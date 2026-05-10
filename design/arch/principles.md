# Architectural Principles

The criteria `/arch` applies to every design decision and the standard against which sprint scope is reviewed. Maintained, not duplicated — when these principles are cited elsewhere (skill defs, design docs, reviews) they are cited by name; this file is the single canonical home.

The principles below were derived from the prototype's complexity analysis (59 audit findings across 4 modules) and refined as the reimplementation has progressed. Sprint citations record the originating context where one is recorded; principles 11–13 are Sprint 26 additions surfaced by the dual-pipeline defect.

Authoring and revision are part of `/arch`'s role. Principles evolve at sprint close (Phase 7 review per the methodology) — never mid-sprint, to avoid reactive rule-making. Revisions cite the sprint that motivated the change and commit before sprint archive.

Each Principle is one file at `principles/NN-{slug}.md`. Index:

- [Principle 01](principles/01-decoupling-over-convenience.md) — Decoupling over convenience
- [Principle 02](principles/02-narrow-interfaces.md) — Narrow interfaces
- [Principle 03](principles/03-dependency-flows-toward-stability.md) — Dependency flows toward stability
- [Principle 04](principles/04-parallel-development-first-class.md) — Parallel development is a first-class constraint
- [Principle 05](principles/05-testability-is-structural.md) — Testability is structural
- [Principle 06](principles/06-complexity-has-a-budget.md) — Complexity has a budget
- [Principle 07](principles/07-single-source-of-truth.md) — Single source of truth
- [Principle 08](principles/08-no-interim-implementations.md) — No interim implementations of later-ring capabilities
- [Principle 09](principles/09-rings-are-accretive.md) — Rings are accretive
- [Principle 10](principles/10-parser-keywords-distinct-syntax.md) — Parser keywords are for distinct syntax only
- [Principle 11](principles/11-single-pipeline-mode-parameters.md) — Single pipeline, mode parameters
- [Principle 12](principles/12-design-for-full-spec-surface.md) — Design for the full spec surface
- [Principle 13](principles/13-interfaces-md-is-auditable.md) — `interfaces.md` is auditable
- [Principle 14](principles/14-ffi-layout-discipline.md) — FFI boundary types are governed by layout discipline
- [Principle 15](principles/15-facade-types-live-with-behavior.md) — Facade types live with their behavior
- [Principle 16](principles/16-punctuation-symbols-are-not-special.md) — Punctuation symbols are not special
- [Principle 17](principles/17-module-locality-in-typecheck.md) — Module locality in typecheck
