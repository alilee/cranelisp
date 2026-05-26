---
number: 0222
target: /dev (typecheck)
filed_by: /review
filed_at: 2026-05-26
sprint_filed: 70
refers_to: crates/cranelisp-typecheck/src/{traits.rs,program.rs,adt.rs,checker.rs}, sprints/archive/sprint-70.md §"step 2", design/arch/cranelisp-types-settled-verdict-s70.md, S69 audit memo
status: open
---

# Cascade `cranelisp-typecheck` source off S70 types-side narrows

## Issue

Sprint 70 Phase 3 (commits `4cfd01e`, `0c202e3`, `b291a38`) and Phase B foundation (`5e20405`) made structural changes to `cranelisp-types` that broke `cranelisp-typecheck` consumer sites. Per Sprint 70's frontend-narrow scope, typecheck cascade was explicitly deferred ("wash-through in their own sprints" per `feedback_facade_first_migration.md`). At Sprint 70 close, `cargo check -p cranelisp-typecheck` shows **282 errors** — pre-S70 baseline was 277; S70 added 5 net errors.

The +5 breakdown:

**3 step-2-introduced sites** (direct cascade from S70 step 2's `ConstrainedFn { defn: Defn } → { variant: DefnVariant }` narrow per S69 Sub 35 cascade closure):

- `traits.rs:1354` — accesses `.docstring` on `cf.variant` (DefnVariant lacks this field; metadata is on the parent `ModuleEntry::Def`)
- `traits.rs:1361` — accesses `.params()` / `.body()` methods on `cf.variant` (DefnVariant exposes them as fields, not methods)
- `program.rs:1637` — `let annotated_ast: Option<Defn>` type annotation now wrong; ast is `Option<DefnVariant>` post-S35

**4 pre-existing latent sites** (S35/S23 cascade not done in typecheck; S70's narrows surfaced them):

- `adt.rs:278` — DefnVariant access pattern
- `adt.rs:377` — DefnVariant access pattern
- `checker.rs:588` — DefnVariant access pattern
- `checker.rs:682` — DefnVariant access pattern

The S70 commit `0c202e3` (types-solidness step 2) message names this carry explicitly: "all 7 carry as typecheck wave-3 cascade work for S71+".

## Proposed resolution

Per the S35 invariant (metadata canonical on parent `ModuleEntry::Def`, NOT on the inner `DefnVariant`):

1. **traits.rs:1354+1361** — rewrite metadata access to read from the parent `Def` entry, not from `cf.variant`. The constrained-fn template's name/docstring/visibility/span live on the parent Def's fields; the inner `variant: DefnVariant` carries only `params` (field) + `body` (field) + `span`. Access pattern:
   ```rust
   // before (broken): cf.variant.docstring, cf.variant.visibility, cf.variant.params(), cf.variant.body()
   // after: look up the parent Def via fq → entry; read entry.docstring, entry.visibility, etc.;
   //   for params/body specifically, read cf.variant.params / cf.variant.body (no parens — they're fields)
   ```

2. **program.rs:1637** — fix type annotation: `let annotated_ast: Option<DefnVariant>` (not `Option<Defn>`). Trivial.

3. **adt.rs:278, adt.rs:377, checker.rs:588, checker.rs:682** — apply the same S35 invariant. Read each site in context; route metadata access to the parent Def; route payload access (params/body/span) to the DefnVariant.

After these 7 sites are resolved, typecheck should compile (or surface additional cascade-from-S70 errors that this FIXME's resolution will discover). Pre-existing typecheck errors unrelated to S70's narrows stay as their own cascade work (separate FIXME territory).

**Verification target**: `cargo check -p cranelisp-typecheck` returns to **277 errors or below** (S70 pre-step-2A baseline). Aspirational: 0 errors if downstream cascades all land, but that depends on factors outside this FIXME's scope (broader S69-audit dispositions, S70 frontend changes consumer-cascading into typecheck, etc.).

**Bundling**: pairs naturally with FIXME 0221 (backend D41 source rotation) if the user wants both consumer crates rotated in one S71 sprint. Independent if scoped separately.

## Operational implication / Context

Without this cascade, `cargo check --workspace` stays broken on typecheck. Frontend has been rotated (Sprint 70 Phase A + B); types have been rotated (Sprint 70 Phase 3 + B). Typecheck and backend (FIXME 0221) are the last two consumer crates owing rotation off the S70 types-side changes.

Sprint 70 Phase B `/review` verdict named this follow-up as **Important** severity. The work is mechanical given the S35 invariant grounding; estimated <1 day of focused /dev (typecheck) narrow work.

## Related

- FIXME 0221 — Backend D41 source rotation (parallel scope; same S71+ sprint candidate)
- Sprint 70 commit `0c202e3` — types-solidness step 2 (the narrow that surfaced the 7 sites)
- Sprint 70 commit `b291a38` — types-solidness step 3 (SymbolRef + Pattern::Constructor lift; check if typecheck has additional cascade from this commit too)
- S69 Submission 35 — original metadata-canonical-on-parent ruling
- S69 Submission 23 — DefnVariant fused-tuple narrative (related cascade items at `param_annotations` deletions)
