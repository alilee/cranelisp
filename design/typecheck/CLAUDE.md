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

This memory establishes two collections, declared in `standing-documents.toml`:

| Collection | Purpose |
|---|---|
| `typecheck-current-designs` | The master and every current subordinate design listed in its §10. |
| `typecheck-historical-records` | `s87-fq-walk-consolidation.md`, held only for its §2.4 `Type`-rendering table, which three `crates/cranelisp-types/src/types/tests.rs` cases cite. It carries a `HISTORICAL` banner and is not design intent. It retires when `arch` restates the table under `design/arch/bounded-contexts.md` §"Type rendering" and the anchors re-point. |

Every reference in either collection is live; a historical grade does not excuse
a stale citation.

## Redirections

These working records were deleted at S122 (Git retains them). A citation to one
of them reads instead:

| Deleted record | Read instead |
|---|---|
| `sprint50-fixes.md` | `spec/08-modules.md` §8.9.1 + §8.9.4 (a new module is seeded with special forms only; builtin type names are reachable by import or qualification, never by inheritance) and `design/arch/bounded-contexts.md` §2 for the source-ordered `defmacro` checkpoint that replaced eager clause compilation |
| `phase-b-plan.md` | `crates/cranelisp-typecheck/src/builtins.rs` + `resolve.rs` rustdoc for the intrinsic-vs-ADT kind split (the four scalars are intrinsic records returning their bare `Type` variant; ADT-shaped bundled types stay type definitions, and the fix for a mismatch belongs at the mint site, never as a bridge in `unify`); `ast-annotation.md` for the AST-co-located annotation model that retired the per-mono side maps |
| `wave-3a-check-form.md` | `typecheck.md` §6.4 (staging-vs-live write dispatch) and §5 (the two-pass discipline inside `check_forms`); `crates/cranelisp-typecheck/src/cluster.rs` module rustdoc for the accessor's as-built shape |
| `s76-resolution-and-enablement.md` | `crates/cranelisp-typecheck/CLAUDE.md` §"Bare-name resolution & the prelude fallback" and `design/arch/bounded-contexts.md` §7 (the resolution primitive owns the walk; this crate owns view selection and the kind-specific projection) + §2 for `check_type_expr` |
| `step4-macro-deps.md` | `crates/cranelisp-typecheck/CLAUDE.md` §"`Def.callees` completeness contract" and `typecheck.md` §5 (callee harvest, late-edge union, atomic publication) |
| `dashmap-migration.md` | `typecheck.md` §7.5 (hold one table guard at a time) and §6.1 (the mutation contract) |
| `stateless-tc-impl.md` | `traits.md` §1.1 (`TypeCheckEnv` + `CheckState`; no registries) and `typecheck.md` §7.1 |
| `typecheck.md` §9.8 (the S121 C3 visit plan, per-filing dispositions and handoffs; removed S122) | The subject documents it cited for each filing's current state: `non-concrete-producer-obligations.md` §1 and §6, the [auto-curry free-variable rule](auto-curry.md#2-free-variables-remain-in-the-ordinary-inference-context) and [seam taxonomy](auto-curry.md#3-the-seam-taxonomy--fixme-0776s-typecheck-instance-fixme-0779s-evidence), `design/typecheck/ownership-inference.md` §4.5, §3.3 and §10.3, `qualified-trait-impl.md` §7, `traits.md` §3.0.1. Standing constraints it carried are in `typecheck.md` §9. |
