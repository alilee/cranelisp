---
number: 0434
target: /qa
filed_by: /sprint
filed_at: 2026-06-25
sprint_filed: 90
refers_to: tests/plan/ledger.md §"Sprint 90 Phase-6 — D-qual-impl-target", spec/07-traits.md §7.3.1, spec/08-modules.md §8.5
status: open
---

# Coverage sweep — test QUALIFIED and BARE forms of every REPL-display-qualified name-position

## Issue
S90 Phase-6 live smoke surfaced **D-qual-impl-target**: a module-qualified type path in
impl-target position (`(impl Num primitives/Int …)`) is re-rooted under the current module
to a phantom `user/primitives/Int` (and `user/Widget` → `user/user/Widget`), so trait
dispatch never matches — while the **bare** target (`impl Num Int`) works. The defect itself
has its failing-not-ignored repros (`spec_07_traits::impl_qualified_primitive_type_target_resolves_to_canonical`
+ `…_user_type_…`, commit `cbdafd4`) — owner `/frontend`, carried to S91.

**The deeper, untracked gap:** a corpus sweep (`/qa`, 2026-06-24) confirmed **every** existing
trait/impl test uses a **bare** target; **zero** use a qualified path. The qualified-resolution
path was never exercised — a structural blind spot. The embedded agent found it only because it
**writes the language the way the REPL displays it** (it mirrors the `:primitives/Int` value
display), making it a coverage-exercising consumer the human-written corpus could not match.

This blind spot is almost certainly **not unique to impl targets.** Any syntactic position that
takes a type/name which the REPL *displays qualified* (`:primitives/Int`, `:(Fn …) user/id`,
`Color.Red`/`user/Color`) is a candidate for the same qualified-vs-bare divergence — type
annotations, `deftype`/`deftrait` references, qualified constructor patterns, import targets,
etc. The corpus tests these in bare form by habit; the qualified form is under-exercised.

## Proposed resolution
After `/frontend` fixes D-qual-impl-target (S91), `/qa`:
1. **Lands the `[Tested+Neg]` annotation** on `spec/07-traits.md §7.3.1` asserting qualified and
   bare impl targets resolve identically (coordinate the spec-side annotation with `/spec`).
2. **Sweeps the name-positions** the REPL displays qualified and adds a qualified-AND-bare pair
   (or a `_neg` that the qualified form must NOT re-root) for each: impl targets ✓ (done),
   type annotations (`:primitives/Int x`), `deftype`/`deftrait`/`impl` type references,
   qualified constructor patterns in `match`, import/`mod` targets. Each pair asserts the two
   forms are interchangeable (or documents where they intentionally differ, per spec).
3. Records the sweep result in `tests/plan/ledger.md` + promotes the relevant spec rows to
   `[Tested+Neg]`.

## Operational implication / Context
This is a **proactive coverage class**, not a single defect — it has no single failing test, so
it needs this FIXME as the durable trigger (the D-qual-impl-target repros cover only the one
position). Methodology lesson (S90 outcome, Findings): *trait/impl — and likely other —
conformance coverage must test qualified AND bare forms of every name-position the REPL displays
qualified.* The agent-as-coverage-exerciser dividend is the reason this surfaced; the sweep
generalises the guard so the class can't silently regress. Gate-relevant for whichever sprint
picks up D-qual-impl-target (do the sweep in the same increment as the fix, while the context
is hot).
