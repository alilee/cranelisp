---
number: 0508
target: /qa
filed_by: /sprint
filed_at: 2026-07-04
sprint_filed: 102
refers_to: crates/cranelisp-typecheck/src/traits/monomorphise.rs:1034 (build_mangled_name), :587 (register_mono_entry); tests/generic_value_use_mono.rs
status: open
---

# Bare mono-mangle key collides for two same-named imported generics — silent wrong-dispatch (newly reachable by CS-488ab)

## Issue (Wave-8a review, Important)

`build_mangled_name` (monomorphise.rs:1034) = `"{fn_name}${types}"` from the **bare** symbol + concrete param type names only — **home-independent**. `register_mono_entry` (monomorphise.rs:587) inserts under that bare mangled name into the **caller's** current symbol table. So:

> Two distinct modules `a` and `b` each defining a public generic `iden2`, both referenced in one consumer at the same concrete arg type — `(a/iden2 5)` and `(b/iden2 5)` — both mint key **`iden2$Int` in the consumer module**. The `seen` map short-circuits the second mint; `register_mono_entry`'s `existing_got_slot` reuse binds the second call to the **first module's body**. Silent wrong-dispatch — a miscompile, no diagnostic.

**Net-new reachability from CS-488ab** (Wave 8a): pre-fix the same-module FQ path missed (raw `/`-key) and the cross-module FQ path did not mint at all, so this shape produced a loud "undefined function". The 0488 fix (correctly) makes cross-module FQ generics mint — trading the loud error for a silent mis-mint in this narrow two-same-named-home shape. The Wave-8a unit tests (u_a2, u_b) exercise only the single-home case; nothing guards the two-home collision.

## Proposed resolution

Per root `CLAUDE.md` defect protocol, the durable record is a **narrow failing-not-ignored repro** (this FIXME's `/qa` half): two modules, same bare generic name, same arg type, both FQ-referenced in one consumer → assert both bodies dispatch correctly (currently the second silently dispatches the first's body). `// spec:` annotated, `FIXME(/…)` pointing at the resolver.

The **fix owner is an /arch-level question** (route on once the repro exists): should the mono mangle key be **home-qualified** when the bare name is ambiguous across imports (e.g. `a.iden2$Int` vs `b.iden2$Int`), or is there a cheaper disambiguation at `register_mono_entry`? Home-independent mangling predates this change-set; CS-488ab only made the collision reachable. Not a Wave-8b blocker (uncommon legal shape); resolve this sprint if capacity, else carries with the repro as the guard.

## Operational implication

Silent miscompiles are the worst defect class — the failing repro is the trigger + regression guard. Full evidence: `sprints/SPRINT.md` §Notes Wave-8a review entry.

## /arch ruling 2026-07-04 — mangling question RESOLVED; this FIXME kept OPEN for its /qa-repro half only

The "/arch-level question" half of this FIXME is answered. **Home-qualify the
mono mangle key** — this is the SAME cure as 0483 (ADT-arg erasure): both are
`build_mangled_name` dropping distinguishing facts. The unified fix — one
canonical, total, home-qualified mangler with grammar
`{home}/{bare}${recursive-concrete-sig}` — is designed in **FIXME 0516**
(`target: /dev`, cranelisp-typecheck) and cures 0483 + 0508 in one change-set.
There is no cheaper `register_mono_entry`-local disambiguation: the collision
also fires at the home-blind `seen`-dedup key (`program.rs:~3469`), so the fix
must live in the shared mangler, not a spot patch. Durable invariant recorded at
`design/arch/interfaces.md` §"Mono-instance linker identity is lossless by
construction" (Principle 7 + Principle 20).

**This FIXME stays OPEN as the /qa-repro half.** The two-same-named-imported-home
failing-not-ignored e2e repro (two modules, same bare generic name, same arg
type, both FQ-referenced in one consumer → assert both bodies dispatch
correctly; currently the second silently dispatches the first's body) is still
owed and is the durable guard for the HOME axis (distinct from the 0483×3
guards, which cover the ADT-arg axis). Author it RED against HEAD; the 0516
mangler fix flips it green. `// spec:` annotated, pointing at 0516 as the
resolver. Not folded/deleted — the repro is 0508's reason to exist.
