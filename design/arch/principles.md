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
- [Principle 18](principles/18-enforce-invariants-structurally.md) — Enforce architectural invariants structurally where possible (S68 — motivating context: Decision 0048 §"Structural invariant — backend dep-ban", user-arbitrated revision 2026-05-17)
- [Principle 19](principles/19-no-module-privileged-by-name.md) — No module is privileged by name (S78 — motivating context: entry-module de-special-casing + prelude-as-outer-scope, user-approved 2026-06-11)
- [Principle 20](principles/20-model-invariants-by-representation.md) — Model a cross-field invariant by representation; accessor-enforcement is the explicit fallback (S83 — motivating context: the recurring "180 locations" cross-field-invariant churn + the FIXME 0354 `got_slot`/`constrained_fn` SIGSEGV; user-directed representation-first reshape, Phase 2 ratification 2026-06-14. **S84 generalisation (2026-06-16): the encoded invariant is slot ⟺ fully-concrete (no `Type::Var`), NOT slot ⟺ unconstrained — the gate predicate is `Type::is_concrete()`; FIXME 0374**)
- [Principle 21](principles/21-actors-and-functions-before-mechanism.md) — Model the actors and the functions between them before synthesising a mechanism (S98 — motivating context: the S97 v9 model pivot + FIXME 0486's unnamed arg-lifetime-across-suspension contract; user-directed, FIXME 0483, Phase 2 authoring 2026-07-01)
- [Principle 22](principles/22-published-pointers-have-retention-owners.md) — A pointer published across a frame-outliving boundary has a named retention owner (S101 — motivating context: the lifetime-across-suspension recurring class — S97/S98 launched-effect arg UAF → BC §4b invariant 15, the S101 `*code = None` displacement class + FIXME 0479's third missed site, 0494 bug #2's drop-glue tripwires; user-mandated Wave-5 recurring-class ruling 2026-07-03, **ratified by the user at S101 Phase-7 close, 2026-07-03**)
- [Principle 23](principles/23-tests-mirror-module-composition.md) — Unit tests mirror module composition — submodule × scenario class (S102 — motivating context: the S101 strategy-matrix escape class — 0479 complementary-cell UAF, 0483/0488 single-cell instantiation pins, D1/D2 zero-scenario strategies, backend's monolithic 5.9k-line root `tests.rs`; architecture half of the S101 user ruling whose methodology half is METHOD §2.2; authored S102 Phase 2 resolving FIXME 0494, ratification at S102 Phase-7 close)
- [Principle 24](principles/24-resolve-once.md) — Resolve once — a semantic identity is derived by exactly ONE keyed-lookup CHAIN at exactly ONE pipeline stage and crosses stage boundaries as a resolved FQ value; downstream stages do keyed reads and hard-fail on miss, never re-derive. Resolution is a chain of keyed lookups (scope precedence + explicit import/re-export pointers + prelude-fallback-once), never a search: NO ambient scan derives a compile-necessary identity at ANY stage — there is no valid search for identity. Carve-outs: complete-set enumeration (order-independent; failure mode incompleteness, not divergence; dispatch selection is this shape) and the human-facing `/search` scan, the one sanctioned genuine scan (S110 — motivating context: FIXME 0583's backend resolver, the "two resolvers, one name" mirror class 3× in S109; instances unified: 0583/§10-DC-11/0590/0585/R-2; user directive S109 P5; authored S110 Phase 3, strengthened compiler-wide S110 Phase 7, **ratified by the user at S110 Phase-7 close, 2026-07-16**, with the strengthened wording)
