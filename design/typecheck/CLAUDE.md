# design/typecheck/

Interior design of `cranelisp-typecheck`: inference, traits, ADTs,
monomorphisation, ownership inference and typed publication. Owned by `design`,
narrow-deployed to this crate.

These documents state *how* the crate meets its obligations. Required language
behaviour is `spec/`'s; the crate boundary and cross-crate contracts are
`arch`'s (`design/arch/bounded-contexts.md` §2 and focused contracts under
`design/arch/`); implementation gotchas for `dev` are in
`crates/cranelisp-typecheck/CLAUDE.md`.

## Start here

[`typecheck.md`](typecheck.md) is the master and the single statement of design
intent. Its §10 is the document map: every subordinate document, its subject and
its standing. Read the master, then the subordinate for the subject at hand.
Where a subordinate disagrees with the master, the master wins; where either
disagrees with source, repair the document.

## Conventions

- One document per independently changing subject, subordinate to the master.
- State current design and the rationale that prevents a plausible mistake.
  Delivery narrative, completed change-set plans and superseded alternatives go
  to Git, not into a current design.
- Record a rejected alternative briefly when its loss would invite re-proposing
  it: "considered X, chose Y because Z".
- Update the design in the same change-set as the implementation it describes.
- When a working plan completes, move its durable content to the subject's
  document and delete the plan; add a redirection below if anything cites it.
- When a rewrite renumbers cited sections, the document ends with a "Former
  section numbers" table so existing source, test and document citations still
  resolve; re-point citations when their owners next touch them.

## Collections

This memory establishes one collection, declared in `standing-documents.toml`:

| Collection | Purpose |
|---|---|
| `typecheck-current-designs` | The master and every current subordinate design listed in its §10. |

Every reference in the collection is live; a historical grade does not excuse
a stale citation.

## Redirections

These working records were deleted at S122 (Git retains them). A citation to one
of them reads instead:

| Deleted record | Read instead |
|---|---|
| `s87-fq-walk-consolidation.md` | [Type rendering](../arch/interfaces.md#type-rendering), the byte-for-byte contract; `render_type` rustdoc for the API promise |
| `sprint50-fixes.md` | `spec/08-modules.md` §8.9.1 + §8.9.4 (a new module is seeded with special forms only; builtin type names are reachable by import or qualification, never by inheritance) and `design/arch/bounded-contexts.md` §2 for the source-ordered `defmacro` checkpoint that replaced eager clause compilation |
| `phase-b-plan.md` | `crates/cranelisp-typecheck/src/builtins.rs` + `resolve.rs` rustdoc for the intrinsic-vs-ADT kind split (the four scalars are intrinsic records returning their bare `Type` variant; ADT-shaped bundled types stay type definitions, and the fix for a mismatch belongs at the mint site, never as a bridge in `unify`); `ast-annotation.md` for the AST-co-located annotation model that retired the per-mono side maps |
| `wave-3a-check-form.md` | `typecheck.md` §6.4 (staging-vs-live write dispatch) and §5 (the two-pass discipline inside `check_forms`); `crates/cranelisp-typecheck/src/cluster.rs` module rustdoc for the accessor's as-built shape |
| `s76-resolution-and-enablement.md` | `crates/cranelisp-typecheck/CLAUDE.md` §"Name resolution" and `design/arch/bounded-contexts.md` §7 (the resolution primitive owns the walk; this crate owns view selection and the kind-specific projection) + §2 for `check_type_expr` |
| `step4-macro-deps.md` | `crates/cranelisp-typecheck/CLAUDE.md` §"`callees` completeness" and `typecheck.md` §5 (callee harvest, late-edge union, atomic publication) |
| `dashmap-migration.md` | `typecheck.md` §7.5 (hold one table guard at a time) and §6.1 (the mutation contract) |
| `check-form-api.md` | [Per-form dispatch](typecheck.md#51-per-form-dispatch) (former check_form and DefnMulti sections); `design/typecheck/traits.md` §6 "Detection" (former Constrained polymorphism); `design/typecheck/typecheck.md` §5.2 items 1–3 and 5 (former invariants); `design/typecheck/typecheck.md` §5 for an unsectioned citation |
| `s87-traits-decomposition.md` | `design/typecheck/typecheck.md` §3.1 (the traits module cut and visibility; former sections 0–1), `design/typecheck/traits.md` §1.6 (submodule concerns and dispatch cohesion; former section 3), `design/typecheck/monomorphisation.md` §3.9 (engine phases and state channels; former section 2) |
| `program-decomposition.md` | `typecheck.md` §3.1 (the `program/` cut and its visibility rule; former sections 0–1); `monomorphisation.md` §3.1 and §3.3 (the finalize ordering and the Pass-4 collectors; former sections 2.1 P0–P5 and 2.2); `crates/cranelisp-typecheck/CLAUDE.md` §"Testing" and Principle 23 (a test's home is the unit it exercises; former section 3) |
| `typed-resolution-carrier.md` | [Recording the verdicts](ast-annotation.md#21-recording-the-resolution-verdicts) and `ast-annotation.md` §2–§3 (producer chokepoints, binder provenance, `Apply` totality, builtin pairing, the view-build gate; former sections 1–4 and 16), with [backend keyed consumption](../arch/backend-keyed-consumer.md) §1 and §4 for the shared contract; `typecheck.md` §9.1 (dispatch completeness, the no-impl error disposition and the impl-existence predicates; former sections 5, 14.2 and 14.4); `design/typecheck/ownership-inference.md` §3.3 rule 3 (match-var-pattern escape; former section 6); `typecheck.md` §9.7 (settlement-window classification; former sections 14.1 and 15). Former sections 7–13 were a delivered S114 change-set plan. |
| `stateless-tc-impl.md` | [registry-free state](traits.md#11-no-registries) (`TypeCheckEnv` + `CheckState`; no registries) and `typecheck.md` §7.1 |
| The former `typecheck.md` §9.8 S121 C3 visit plan, per-filing dispositions and handoffs (removed S122; §9.8 now holds Module aliases) | The subject documents it cited for each filing's current state: `non-concrete-producer-obligations.md` §1 and §6, the [auto-curry free-variable rule](auto-curry.md#2-free-variables-remain-in-the-ordinary-inference-context) and [seam taxonomy](auto-curry.md#3-the-seam-taxonomy--fixme-0776s-typecheck-instance-fixme-0779s-evidence), `design/typecheck/ownership-inference.md` §4.5, §3.3 and §10.3, `qualified-trait-impl.md` §7, `traits.md` §3.0.1. Standing constraints it carried are in `typecheck.md` §9. |
