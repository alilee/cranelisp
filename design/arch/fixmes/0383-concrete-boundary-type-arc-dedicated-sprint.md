---
number: 0383
target: /sprint
filed_by: /arch
filed_at: 2026-06-16
sprint_filed: 84
refers_to: design/arch/concrete-boundary-type.md, design/arch/fixmes/0381-bare-var-reaches-codegen-in-compiled-generic-prelude-body.md, design/arch/fixmes/0375-backend-retire-1024-rc-guard-from-typevar-path.md, design/arch/bounded-contexts.md §3 invariant 9
status: open
---

# Open a dedicated arc for the concrete-only codegen-boundary type + generic-body-codegen elimination

## Issue

The S84 user ruling (2026-06-16) re-directed Cluster A: the goal is that **generics
are not REPRESENTABLE at the backend boundary** — a concrete-only type (no `Var`
variant) at the typecheck→backend seam, not a pile of downstream checks. /arch
investigated and designed this: `design/arch/concrete-boundary-type.md`.

The design is a **5-phase arc that is NOT the remainder of S84.** Only Phase 1
(the `ConcreteType` scaffold) is S84-sized and it is LANDED this session (see
"Scaffold" below). Phases 2–5 are a multi-sprint migration whose centre of gravity
(Phase 2 mono-produces-ConcreteType, Phase 4 generic-body elimination) each
rival a full S84-Cluster-A spine wave.

The critical finding forcing the arc (FIXME 0381): arming the FIXME-0379 backend
backstop fired **317×** because the prelude/stdlib compiles GENERIC FUNCTION BODIES
once as uniform-word templates carrying free `Type::Var`s — the §12.1 model, NOT
per-instance monomorphisation. The boundary type alone is insufficient without
Phase 4 (generic-body elimination): a generic body has no `ConcreteType`
annotation, so it cannot reach codegen; only concrete monomorphised instances are
emitted; prelude generics become on-demand mono roots.

## Proposed resolution

**Open a dedicated sprint (S85 or later) for Phases 2–5.** Sequencing, crates,
public-api/BC/cache impact, risk, and HONEST sizing are in
`design/arch/concrete-boundary-type.md` §4. Summary:

- **Phase 1 — `ConcreteType` + fallible `from_type` conversion.** SMALL. **LANDED
  this session** (scaffold, no behaviour change).
- **Phase 2 — mono produces `ConcreteType`; AST carries it** (`codegen_type` field
  or a `MonoExpr` codegen-AST — /design decides §2.4). LARGE; `cranelisp-types`
  baseline move + **`CACHE_SCHEMA_VERSION` bump** (AST is on the cached serde
  shape). The §2.4 decision is the central migration choice.
- **Phase 3 — backend consumes `ConcreteType`; `classify` loses the `Var` arm.**
  MEDIUM-LARGE (~13 backend files read `inferred_type`). Retires
  `is_representation_undetermined()` + the §3.11.1 standalone scan (subsumed by
  the conversion). One `public-api.txt` REMOVAL (the predicate).
- **Phase 4 — eliminate generic-body codegen; prelude generics → on-demand mono
  roots.** LARGE, HIGH risk (the 317× phase). Retires FIXME 0381's root.
- **Phase 5 — relax §12.1** (the staged 0373(iii) wording; now genuinely
  backend-internal). SMALL.

Strict ordering 1→2→3→4→5. The interim S84 guards (§3.11.1 position-complete check
+ the deferred 0381 backstop) hold the soundness line across the gap between
Phase 1 and Phase 3 — the arc can be deferred without re-opening the SIGSEGV.

## Operational implication / Context

- **Scaffold landed this session (Phase 1):** `crates/cranelisp-types/src/concrete.rs`
  — `ConcreteType` (no `Var`/`TyConApp`), `from_type`/`to_type`, `NotConcrete`;
  10 unit tests; `public-api.txt` regenerated (additive only, no cache bump).
- This arc **subsumes** the FIXME-0379 two-predicate belt-and-braces *framing*
  (the structural type replaces the two agreeing predicates), **drops** the
  FIXME-0375 backstop (made inexpressible — `classify` takes `ConcreteType`), and
  **folds in** FIXME 0381 (its proposed resolution IS Phase 4). 0381 + 0375 are
  annotated to point here; they close at Phase 4/Phase 3 respectively.
- Principle 18/20 cross-refs gain this doc at the relevant phase close (NOT
  mid-sprint — the principle-stability rule).
- This is a /sprint scope-arbitration item: when to schedule the dedicated arc,
  and whether to land Phase 1's scaffold now (done) vs as the arc's first wave.
