---
number: 0223
target: /arch
filed_by: /review
filed_at: 2026-05-26
sprint_filed: 70
refers_to: design/arch/facades/*.md (4 citation sites for PrimitiveKind + 1 for ConstructorInfo)
status: open
---

# Facade-text catch-up: `PrimitiveKind` and `ConstructorInfo` retired-but-cited

## Issue

Sprint 70 Phase B's configuration→source completeness sweep (`design/arch/cranelisp-types-settled-verdict-s70.md`) surfaced two facade-text staleness items beyond the types-crate gaps:

- **`PrimitiveKind`** — retired by S69 Submission 36 (promoted to `ModuleEntry::SpecialForm` variant). Still cited 4× across facades.
- **`ConstructorInfo`** — retired (per `crates/cranelisp-types/src/check.rs` rustdoc: "`pub struct ConstructorInfo { ... }` retired — see `DefKind::Constructor` rustdoc in `module.rs` and `design/arch/bounded-contexts.md` §7 "Multi-legged authoring" for the ctor-as-Def shape"). Still cited in `design/arch/facades/backend.md:441`.

These are facade-text drift items, not source gaps. The retired types ARE gone from source per S69 Sub 36 (PrimitiveKind) and the post-S69 ctor-as-Def cascade (ConstructorInfo). Facade text just hasn't caught up.

## Proposed resolution

`/arch` sweep across `design/arch/facades/*.md`:

```bash
grep -rn "PrimitiveKind\|ConstructorInfo" design/arch/facades/ --include="*.md"
```

For each hit:
- **PrimitiveKind** — rotate the citation to point at the post-S69-Sub-36 shape. The shape was: `PrimitiveKind` was a `DefKind` variant carrying inline-eligibility metadata; S69 Sub 36 retired it (special forms got their own `ModuleEntry::SpecialForm` variant; primitives' inline-eligibility moved to per-call-site `ResolvedCall::BuiltinFn { name }` per the `DefKind::Primitive` rustdoc at `module.rs:864-877`). Citations should rotate to the new home as appropriate per local context.
- **ConstructorInfo** — rotate to `DefKind::Constructor { type_name: FQTypeName, tag: usize, field_count: usize, internal: bool }` per `module.rs:911-928` + BC §7 "Multi-legged authoring" + the migration map in `check.rs` rustdoc.

After the sweep, regenerate any `cargo public-api` baselines that read facade-text in their flow (likely none — public-api reads source, not facades).

## Operational implication / Context

These citations are facade-narrative drift, not load-bearing API contracts. A reader following the citation would land on a missing type and have to chase down the retirement; the rotation makes the narrative legible. No source change required.

Sprint 70 Phase B `/review` verdict named this follow-up as **Suggestion** severity. Low priority; opportunistic during /arch's next facade-touching fire.

## Related

- S69 Submission 36 — PrimitiveKind retirement (promoted SpecialForm to its own ModuleEntry variant)
- Post-S69 ctor-as-Def cascade — ConstructorInfo retirement (DefKind::Constructor shape per BC §7)
- `design/arch/cranelisp-types-settled-verdict-s70.md` §"Out-of-scope items" — the original surfacing
