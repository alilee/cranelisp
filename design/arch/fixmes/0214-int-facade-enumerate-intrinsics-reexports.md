---
number: 0214
target: /design (int)
filed_by: /sprint
filed_at: 2026-05-17
sprint_filed: 68
refers_to: design/arch/facades/int.md §"Exe-bundle startup contract", crates/cranelisp-exe-bundle/public-api.txt, design/arch/CLAUDE.md §"Baseline-diff discipline"
status: open
---

# `facades/int.md` does not enumerate the 8 intrinsics force-link re-exports

## Issue

Sprint 68 generated `crates/cranelisp-exe-bundle/public-api.txt` for the first time (Wave 5). The 11-line baseline contains:

- `cranelisp_init_platform` extern fn (named in facade)
- `cranelisp_init_primitives` extern fn (named in facade per Wave 3)
- **8 intrinsics force-link re-exports**: `alloc`, `drop`, `io`, `ivar`, `panic`, `rc`, `intrinsics_string`, `intrinsics_vec` (**NOT enumerated by name** in the facade)

`facades/int.md` describes the intrinsics force-link discipline generally and points to `facades/intrinsics.md`, but no line names the 8 submodules individually.

Wave 6 `/review (int)` flagged this as Important — per `design/arch/CLAUDE.md` §"Baseline-diff discipline":

> "every pub-api line in the baseline is named in the corresponding facade (or marked internal-but-exposed with rationale)"

The pre-S68 7 primitives re-exports (`bool`, `float`, `int`, `marshal`, `ring0`, `string`, `vec`) WERE explicitly named in the retirement prose at facades/int.md line 1262 — symmetric naming should exist for the 8 retained intrinsics ones.

## Proposed resolution

`/design (int)` adds an enumerated bullet list in `facades/int.md` §"Exe-bundle startup contract" (or §"Consumed surface — `cranelisp-intrinsics`") naming the 8 intrinsics re-exports:

```
Force-link re-exports retained from `cranelisp-intrinsics`:
- `alloc` — heap allocator surface
- `drop` — drop-glue trampolines
- `io` — IO trampoline + token machinery
- `ivar` — IVar runtime
- `panic` — panic handler
- `rc` — reference counting primitives
- `intrinsics_string` — heap-string allocator/reader
- `intrinsics_vec` — vec runtime
```

Then the facade-compliance baseline check at PR-time can confirm "every pub-api line named in facade" for `cranelisp-exe-bundle`.

## Operational implication / Context

Not blocking S68 deliverables. Documentation-discipline gap; should be fixed in S69. The baseline-diff discipline established in S67 is the canonical contract — int's facade is just slightly behind on enumerating the items it carries.

Two related stylistic suggestions surfaced in same review:
- Facade pseudocode at int.md line 965 (`Arc::clone(&*PRIMITIVES_TABLE)`) doesn't match implementation (`(*PRIMITIVES_TABLE).as_ref().clone()`). Both semantically equivalent; align in same FIXME pass.
- Principle 18 not cited by number in `facades/int.md`. Decision 0048's explicit init-hook discipline is the motivating example; citation closes the loop.
