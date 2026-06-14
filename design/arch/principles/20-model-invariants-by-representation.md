---
number: 20
title: Model a cross-field invariant by representation; accessor-enforcement is the explicit fallback
---

# Principle 20 — Model a cross-field invariant by representation; accessor-enforcement is the explicit fallback

**Statement.** When two or more fields of a boundary type are *correlated* — one field constrains which values another may legally take — model the invariant as a **sum type whose variants are exactly the legal states**, each variant carrying exactly the data valid in that state. Construct the correct variant **once, at the point the state becomes known** ("parse, don't validate"). The illegal combination then has no representation, every reader matches exhaustively (compiler-enforced), and no accessor or convention is needed. Intent-accessor + sole-writer (read the correlated fields only through a method that hides the illegal pairing, write them only through one atomic mutator) is the **explicit fallback**, used only where the sum-type collapse is genuinely blocked — and when used, it is a *bridge to* the representation form, not the destination.

**The discriminator (keeps this from becoming "enum everything").** Apply the cross-field-invariant test: *is there a field combination that is constructable but meaningless?*

- **Correlated fields with few legal states → sum type.** If the answer is yes (a combination is representable but no valid pipeline state produces it), collapse the correlated fields into one enum, one variant per legal state.
- **Genuinely independent fields → leave flat.** If every field combination is meaningful, the fields are independent; collapsing them into a sum type is wrong and combinatorial (N independent two-valued fields would force 2^N variants). Flat is correct.

This is the structural-vs-behavioural choice of Principle 18 made specific for the *cross-field* case. Principle 18 says "prefer the structural mechanism when both exist." Principle 20 names the structural mechanism for correlated fields — the sum type — and names its fallback precisely (the single-source-of-truth accessor of Principle 18's "single-home" form), so the choice is not re-litigated case by case.

**Rationale.** A cross-field invariant enforced by read-discipline ("every reader must respect that field A constrains field B") is asymmetric in cost: adding a *field* is cheap (a builder default cascades lightly), but the invariant recurs at every raw reader, and the invariant breaks the moment one reader forgets it. The canonical worked example: `ModuleEntry::Def` carried a `got_slot: Option<usize>` field parallel to a `kind: DefKind::UserFn { constrained_fn }` discriminator. A constrained-fn *template* is not directly callable (only its monomorphised variants are), so `Def { got_slot: Some(_), kind: UserFn { constrained_fn: Some(_) } }` is meaningless — yet representable. One call-resolution reader (`resolve_got_target`) read the raw `got_slot` and dispatched a cross-module `call_indirect` through the template's never-populated (NULL) slot → SIGSEGV (FIXME 0354). The S82 stopgap added a `callable_got_slot()` accessor (returns `None` for a template regardless of the stored field) and a `mark_constrained_template()` sole-writer — the Principle-18 single-source-of-truth fallback. That stopgap *enforced* the invariant but did not *forbid* the illegal state; the bug recurs the moment a new reader or writer forgets the accessor. The representation fix (move `got_slot` onto the callable `DefKind` variants; a template variant has no slot field) makes the illegal pairing **unconstructable** — the strongest form of Principle 18.

**The timing wall is the crux, and it is a feature, not an obstacle.** Correlated fields are often set at *different pipeline stages* — that is precisely why the flat shape drifts into the illegal state in the first place. In the worked example, the slot is allocated in typecheck Pass 1 (before constraint status is known) and the kind is flipped to a template in Pass 2. The flat shape lets the entry sit in an indeterminate state between the two passes. A sum type forces the question "when is the state actually known?" and resolves it in one of two ways:

1. **Defer the determined-state construction past the determining stage.** Do not build the final variant until the discriminating fact is in hand. (Worked example: defer GOT-slot allocation until *after* Pass-2 constraint detection — allocate the slot at the moment the entry is known to be a concrete callable, not before.) Preferred when the deferral is local and cheap.
2. **Name the interstage explicitly with a `Pending`/not-yet-determined variant.** When work must happen between registration and determination (e.g. Pass-1 signature registration must produce an entry that Pass 2 then refines), add a variant that *names* the indeterminate state and carries no field that the later state would invalidate. The illegal pairing is still unconstructable; the interstage is honest rather than latent.

Either way, "parse, don't validate" pushes the determination to the boundary where the fact is known. An interim flat field that is "sometimes meaningful" is the anti-pattern this Principle retires.

**When the fallback is the right answer.** The accessor + sole-writer fallback is legitimate only when the sum-type collapse is *genuinely* blocked — a hard timing/sequencing constraint that admits neither deferral nor a clean interstage variant, or a churn cost so large it must be staged across sprints. When the fallback is chosen, it MUST be recorded as a fallback (a bridge to the representation form), not silently adopted as the destination — and the representation form remains the standing refactor candidate. A fallback adopted without that record becomes permanent drift.

**Consequence.**

- When proposing or auditing a boundary type with correlated fields, `/arch` applies the cross-field-invariant test first. A constructable-but-meaningless combination is a representation defect, not merely a reader-discipline matter.
- The sum-type collapse and its timing-wall resolution land **together** — the interstage question is part of the collapse, not a follow-up. A collapse that leaves the timing wall unresolved (a `Pending` variant nobody constructs, or a deferral that races) is incomplete.
- `/dev` resists re-introducing a "convenience" flat field that re-opens a collapsed invariant. The variant set is the contract; widening it back to independent fields loses the property.
- The cascade of a collapse (rewriting raw `Def { field, .. }` matches to the new variant shape) is **mechanical** where readers consume the field for storage/serde/codegen, and is the *point* where it forces a reader to state which legal state it expects — exhaustive matching surfaces every reader that silently assumed the now-impossible state.

**Cross-references.**

- Principle 18 — Enforce architectural invariants structurally where possible (the genus; this Principle is the cross-field species — the sum type is the structural mechanism for correlated fields, the accessor is its single-source-of-truth fallback).
- Principle 07 — Single source of truth (the accessor fallback is the single-home form; the sum type makes the single home structural).
- Principle 06 — Complexity has a budget (the discriminator guards against "enum everything" — independent fields stay flat; the budget is spent only where a combination is constructable-but-meaningless).
- BC §7 "Callable address" (`design/arch/bounded-contexts.md`) — the worked example's manifestation site, where `got_slot` moves onto the callable `DefKind` variants (S83, FIXME 0356/0357; amends Decision 0035).
