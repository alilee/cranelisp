# design/typecheck/

Solution design documents for the Cranelisp typechecker (inference, traits, monomorphisation). Owned by `/design`, narrow-deployed to this crate.

## Purpose

These documents describe *how* the typechecker solves problems — algorithms, data structures, internal architecture, and trade-offs. They evolve alongside the implementation: sketched before coding, refined during, and updated when designs change.

This is distinct from:
- `design/arch/interfaces.md` — the *boundary contract* (what goes in and out)
- `spec/03-types.md`, `spec/07-traits.md` — the *language definition* (what behaviour is correct)

## What to Document

- **Inference engine**: Algorithm W implementation, unification, occurs check, substitution strategy
- **Constraint solving**: trait constraint propagation, constrained polymorphism detection
- **ADT type checking**: constructor inference, pattern exhaustiveness, type parameter instantiation
- **Monomorphisation**: specialisation collection, cross-module specialisation, cache interaction
- **Scope and environment**: scope stack design, variable resolution, module interaction
- **Design evolution**: what changed and why across sprints, and what was considered but rejected (per-sprint history lives in the docs themselves and `sprints/archive/`)

## Conventions

- One file per major subsystem (e.g., `inference.md`, `traits.md`, `monomorphisation.md`)
- Include typing rules in judgement notation where they clarify the algorithm
- Record rejected alternatives briefly — "considered X, chose Y because Z"
- Update docs when the implementation changes; stale design docs are worse than none

## Document index

This memory establishes two typecheck-owned collections:

| Collection | Purpose |
|---|---|
| `typecheck-current-designs` | Current typecheck master, subsystem and active feature designs for inference, constraints, traits, ADTs, monomorphisation, ownership and typed publication. |
| `typecheck-historical-records` | The one superseded working record still held for a live citation — `s87-fq-walk-consolidation.md` §2.4. It retires when `arch` rehomes that contract. |

Both are established collections, and every reference in either is live: a
historical grade does not excuse a stale citation. Git carries ordinary
delivery history, so a completed working plan is deleted rather than retained
once its durable content has a current home (S122; §"Redirections" below).

Maintained by `design`. An agent designing against this crate reads the current
designs; the retained record carries a top-of-file `HISTORICAL` banner and is
not current design intent. Where it and a current doc disagree, the current doc
and the source win.

**Master.** `typecheck.md` — the single source of design intent; every other doc
is subordinate. **`typecheck.md` §9.8 is the Sprint-121 C3 visit's order,
reservations, per-filing dispositions and handoffs** — six change-sets, covering
the fifteen allocated filings plus the two cross-stream arms `arch` added on
2026-09-01 (the FIXME-0869 written-trait-impl producer and the FIXME-0798
alias call-site flip). Start there when working this crate in S121, then read the
subordinate doc each row names.

**Durable subsystem docs** (one-per-subsystem, current):
`inference.md`, `traits.md`, `monomorphisation.md`, `adt.md`,
`ownership-inference.md` (**read §19 first for S121, then §20** — the ownership-result
correction: the `ResultMode::MayAliasAny` ⊤, the reaching-parameter-set join that
retires the lowest-index representative, and refusal-publishes-nothing; §§3.2, 13.5,
13.6(c), 13.6(h), 14.2, 14.4 and 18.3 are corrected in place against it. **§20 is the
shadowing correction wave: its direction and its `CACHE_SCHEMA_VERSION` 27 → 28 were
USER-APPROVED and BUILT on 2026-09-07 — read it as an AS-BUILT record, NOT as accepted or
released; the wave's review, full census and `public-api.txt` gate are outstanding** — it
carries the measured runtime abort and the silent RC-parity face that falsify §19.3/§19.10's
result-axis-only record, which are corrected in place against it),
`hkt.md`, `signature-match.md`, `auto-curry.md`,
`io-types.md`, `check-form-api.md` (the per-form pipeline API; a `// spec:` anchor
for `program/tests.rs`), `ast-annotation.md` (the AST-co-located annotation model).

**Active subordinate feature docs** (scoped elaborations of a subsystem doc, live):
`use-site-candidate-selection.md` (**APPROVED — user decision 2026-09-02**, S121
W3 — syntactic filtering, isolated HM trials, fixed-point settlement,
constructor-pattern selection, canonical identity writeback and complete
ambiguity diagnostics → subordinate to `inference.md` + `traits.md` + `adt.md`),
`checked-body-publication.md` (**USER-APPROVED 2026-09-03** for the private body
ledger and the complete §11 state-cleanup basket), S121
C3 — a body-occurrence ledger delaying strict publication to the settled
window; its §9 consumes the same-canonical-name rule established by
`spec/05-definitions.md` §5.13 and `spec/08-modules.md` §8.6.4. Its §11 limits
the cohesive state cleanup to ledger-owned registration/callee facts, one body
frame, whole `MethodResolutions` transport, one-way `expr_types` handoff and
the obsolete `redef_slots` deletion → subordinate to `typecheck.md` +
`use-site-candidate-selection.md`),
`non-concrete-producer-obligations.md` (S119, **re-grounded S121** on the adopted
unified lifecycle — typecheck's half of the non-concrete release contract: P-1 as
funnel *consumption* rather than a local gate, product-accessor/trait-method
monomorphisation (FIXME 0924), the product-only accessor boundary that retires
FIXME 0867, the typed-demand close of FIXME 0935, the lenient view's defaulting
step and located residual refusal (FIXME 0913), the backend instance census,
and the separate keyed ownership-seed observation → subordinate to
`monomorphisation.md` + `adt.md`, governed by
`design/arch/symbol-table-lifecycle.md` and
`design/backend/non-concrete-release-contract.md`),
`result-context-specialization.md` (S121 — complete concrete substitutions as the
specialization identity, governed by the
[instance identity funnel](../arch/interfaces.md#instance-identity-funnel) and
`design/arch/s122-overload-reorder-publication.md` → subordinate to
`monomorphisation.md`),
`s116-method-signature-resolution.md` (S116 — one `method_sig` tail; DESIGN,
implementation pending → subordinate to `traits.md`),
`qualified-trait-impl.md` (S117 canonical trait identity at the `impl` seam —
**LANDED**; §7 carries the as-built confirmation and FIXME 0794's falsification →
subordinate to `traits.md`),
`fixme-0365-field-accessor-dotted.md` (dotted field accessors → subordinate to
`adt.md`), `dotted-ctor-registration.md` (dotted `Type.Ctor` capability, S109 →
subordinate to `adt.md`), `s87-traits-decomposition.md` (the `traits/` module cut +
`monomorphise_call` phase boundaries — retained as the active decomposition
**precedent**, cited by the `program.rs` split design), `program-decomposition.md`
(the S109 `program.rs` module-cut sign-off),
`type-expr-resolver-convergence.md` (S110 FIXME 0590 — the four-mirror `TypeExpr`
resolver single-source refactor → subordinate to `inference.md` + `traits.md`),
`return-poly-dispatch-signal.md` (S110 R16/R17 — the unresolved-return-poly
dispatch signal + the typecheck→int carrier → subordinate to `traits.md` +
`monomorphisation.md`),
`typed-resolution-carrier.md` (S114 Track A — the `VarRef`/`ApplyRef` carrier
flip PRODUCER side; totality at `infer_var`/the Apply chokepoints, binder-provenance
plumbing, the `from_expr` `ViewBuildError` gate, F-D2-10 riding the flip →
subordinate to `monomorphisation.md`, governed by
`design/arch/typed-resolution-carrier.md`).

**Retained working record.** `s87-fq-walk-consolidation.md` (`HISTORICAL`-bannered)
is held for **§2.4 only** — the byte-for-byte `Type`-rendering table that three
`crates/cranelisp-types/src/types/tests.rs` cases name in their `// spec:`
anchors. The rendered surface (`render_type` + its two config enums) is
`arch`-owned; `design/arch/bounded-contexts.md` §"Type rendering" is its current
account. Rehoming the contract there, and re-pointing those anchors, is `arch`'s
to do — until it lands, deleting this doc silently breaks three traceability
anchors.

**Redirections.** Seven working records were deleted at S122 (Git retains them);
a citation to one of them reads instead:

| Deleted record | Read instead |
|---|---|
| `sprint50-fixes.md` | `spec/08-modules.md` §8.9.1 + §8.9.4 (a new module is seeded with special forms only; builtin type names are reachable by import or qualification, never by inheritance) and `design/arch/bounded-contexts.md` §2 for the source-ordered `defmacro` checkpoint that replaced eager clause compilation |
| `phase-b-plan.md` | `crates/cranelisp-typecheck/src/builtins.rs` + `resolve.rs` rustdoc for the intrinsic-vs-ADT kind split (the four scalars are intrinsic records returning their bare `Type` variant; ADT-shaped bundled types stay type definitions, and the fix for a mismatch belongs at the mint site, never as a bridge in `unify`); `ast-annotation.md` for the AST-co-located annotation model that retired the per-mono side maps |
| `wave-3a-check-form.md` | `typecheck.md` §6.4 (staging-vs-live write dispatch) and §5 (the two-pass discipline inside `check_forms`); `crates/cranelisp-typecheck/src/cluster.rs` module rustdoc for the accessor's as-built shape |
| `s76-resolution-and-enablement.md` | `crates/cranelisp-typecheck/CLAUDE.md` §"Bare-name resolution & the prelude fallback" and `design/arch/bounded-contexts.md` §7 (the resolution primitive owns the walk; this crate owns view selection and the kind-specific projection) + §2 for `check_type_expr` |
| `step4-macro-deps.md` | `crates/cranelisp-typecheck/CLAUDE.md` §"`Def.callees` completeness contract" and `typecheck.md` §5 (callee harvest, late-edge union, atomic publication) |
| `dashmap-migration.md` | `typecheck.md` §7.5 (hold one table guard at a time) and §6.1 (the mutation contract the migration was a step toward) |
| `stateless-tc-impl.md` | `traits.md` §1.1 (`TypeCheckEnv` + `CheckState`; no registries) and `typecheck.md` §7.1 |
