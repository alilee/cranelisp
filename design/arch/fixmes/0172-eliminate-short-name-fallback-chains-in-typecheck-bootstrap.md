---
number: 0172
target: /typecheck
filed_by: /sprint
filed_at: 2026-05-11
sprint_filed: 66
refers_to: crates/cranelisp-typecheck/src/checker.rs (defining_module_for ~L578, fqtn_for_bare_type_name ~L563), design/arch/principles/17-module-locality-in-typecheck.md, design/arch/decisions/0045-traitimpl-storage-in-trait-defining-module.md, design/arch/fixmes/0187-int-migrate-typecheckenv-consumers-off-narrowed-helpers.md
status: deferred-with-named-residue
---

# S67 W3 update — deferred-with-named-residue

Sprint 67 Wave 3 /dev (typecheck) narrowed TypeCheckEnv from 37 public
methods toward the facade target of 2 (`new` + `next_type_id`). Per the
PIF row 21 expectation in `design/arch/facades/typecheck.md` §"TypeCheckEnv
target shape — narrowing target", ~28 of the ~30 helper methods drop to
`pub(crate)`.

Final state: 17 methods remain `pub` because `int` consumes them
cross-crate (`src/session_v4.rs`, `src/worker.rs`, `src/platform.rs`,
`src/session.rs`). Narrowing those would break the consumer build.

The remaining migration burden is captured in `design/arch/fixmes/0187-int-migrate-typecheckenv-consumers-off-narrowed-helpers.md`,
which lists each remaining `pub` method, its cross-crate consumer site(s),
and the suggested migration path (most consumers can migrate to direct
`SymbolTable::get` reads with per-symbol chain-follow per Principle 17).

Once /dev (int) lands FIXME 0187, the typecheck-side narrowing of these
methods is a mechanical follow-up — change `pub` → `pub(crate)` and the
facade compliance test (`row_21_*`) flips green at threshold ≤4.

The original substance of FIXME 0172 (Principle 17 short-name fallback
chain in `defining_module_for` and `fqtn_for_bare_type_name`) is **also**
captured by 0187's "Phase A — REPL introspection migration": when
`session_v4.rs:3693` (the consumer of `defining_module_for`) migrates to
direct chain-follow, the helper itself either narrows to `pub(crate)` or
deletes. `fqtn_for_bare_type_name` is already `pub(crate)`; its remaining
substantive issue (the hardcoded primitive type list at lines 810–814) is
also follow-up work — the chain-follow becomes principled when the
prelude's per-symbol Import bindings reach every callsite, which is a
bootstrap-ordering concern downstream of the consumer migration.



# 0172 — Eliminate short-name fallback chains in typecheck bootstrap (Principle 17 follow-up)

## Issue

Sprint 66 Wave 3a-α redo /review (typecheck) surfaced two **Principle 17 short-name fallback chain** violations that survived the redo. Both live in `crates/cranelisp-typecheck/src/checker.rs` and exist as workarounds for registration-ordering during the synthetic-module bootstrap path:

### Site 1 — `defining_module_for` (`checker.rs:578-587`)

Probes the `primitives` module first by short name; falls back to `state.current_module` on miss. Called from `trait_home_for` when the trait member's per-symbol `ModuleEntry::Import` binding isn't yet present in the writer's view — a registration-ordering case during bootstrap.

Consumers:
- `traits.rs:404` — impl-write site (Pattern B retargeting).
- `traits.rs:1025` — body-check `FQTraitName` construction.
- `src/session_v4.rs:3715` — REPL trait-display formatting (public API surface — the function is `pub`).

The Principle 17 violation: short-name lookups MUST resolve in the current module only; no fallback. The fallback masks resolution gaps and undermines the locality guarantee.

### Site 2 — `fqtn_for_bare_type_name` (`checker.rs:563-574`)

Hardcoded match against `"Int" | "Bool" | "Float" | "String" | "Vec" | "IO" | "Trace" | "TestResult"` defaults the `FQTypeName`'s module to `primitives` when short-name lookup fails. Used at `traits.rs:406,583,589,751,1029` to build impl-write keys.

The Principle 17 violation: this IS a short-name fallback chain in disguise — it acts as a silent safety net that supplies a primitives-FQ when the prelude's per-symbol Import bindings haven't yet seeded the user-mode symbol table. In the typical case the prelude carries these names and the fallback is never hit; in shadowing edge cases (user defines a type named `Vec` or `Int` in their own module without shadowing intent) the fallback supplies the wrong FQ.

## Why this isn't a Wave 3a-α blocker

Both violations are **bounded to bootstrap-time registration paths** and don't appear at the typecheck facade boundary (the public-API contract). The facade's behavioral contracts are honored regardless: consumers observe correct trait/type resolution because in practice the prelude's per-symbol Import bindings carry the universal names before any code that needs to chain-follow them. The violations are internal-implementation Principle-17 debt, not facade defects.

`/review` flagged them as **Important** but not Blocker. User-arbitrated (Sprint 66 close, 2026-05-11): record as a future-sprint FIXME; Sprint 66 facade adoption is delivered without the fallback fix.

## Proposed resolution

**The principled fix is registration ordering, not the fallback.** During bootstrap:

1. Establish primitives' symbol table first (in particular, all primitive type names like `Int`/`Bool`/`Float`/`String`/`Vec`/`IO`/`Trace`/`TestResult` must be registered as `ModuleEntry::TypeDef` entries in `primitives` before any code that needs to chain-follow them).
2. Establish prelude's per-symbol `ModuleEntry::Import` bindings into user-mode (and any other mode that needs universal-feeling names) before any trait registration code runs that might need to chain-follow those names.
3. Once steps 1 and 2 are guaranteed by the bootstrap call graph, the chain-follow primitive in `trait_home_for` and `fqtn_for_bare_type_name` can succeed without fallback — and the fallback code can be deleted.

### Implementation hints (for the resolving /typecheck pass)

- Audit `register_builtins` and its callees in `crates/cranelisp-typecheck/src/builtins.rs` to identify the exact ordering invariant that needs to hold.
- The chain-follow primitives `trait_home_for` and `chain_follow_to_home` (introduced by Wave 3a-α redo Sub-C) are already correctly factored; the fix is upstream of them — make sure the symbol-table state they read is sufficient at every call site.
- After deletion, the public-API surface of `defining_module_for` may change (it could become `pub(crate)` or even private); coordinate with `src/session_v4.rs:3715` REPL consumer if so.
- The hardcoded type-name list in `fqtn_for_bare_type_name` (`"Int" | "Bool" | "Float" | "String" | "Vec" | "IO" | "Trace" | "TestResult"`) is a smell — fully delete after registration ordering is correct.

### Test surface

- Wave 3a-α redo Sub-D added a "current-module-only short-name resolution" test (`checker.rs:3564 test_short_name_lookup_is_current_module_only`) that asserts the principled behavior at the function-level. After this FIXME's fix, that test continues to pass; additionally, a new test could assert `defining_module_for` and `fqtn_for_bare_type_name` no longer fall back (i.e., probe a scenario where the prelude has NOT seeded user-mode and verify the resolution either succeeds via chain-follow or fails cleanly without producing a fallback FQ).

## Operational implication / Context

This is a Wave 3a-α follow-up carry — implementation-internal Principle 17 enforcement that doesn't gate facade adoption but does represent two known violations in production typecheck source. Resolution can land in:

- Wave 3a-β (cluster-atomic triad) if β's design naturally touches bootstrap ordering.
- A focused S67 cleanup pass on the bootstrap-time registration graph.
- Wherever a /typecheck pass next has bandwidth.

**Not urgent.** The two fallback paths are bounded and don't manifest in the typical user-mode scenarios; the FIXME exists to make sure the principle-violation debt doesn't accumulate forgotten.

## Why a FIXME and not inline TODO

Per Sprint 66 methodology (`sprints/METHOD.md` §3.3): cross-skill change requests live in `design/arch/fixmes/`. `/sprint` files this targeting `/typecheck` as the natural owner; the FIXME persists in git history until a /typecheck pass picks it up, evaluates whether bootstrap ordering can absorb the fix, actions it (or defers with explicit rationale), and deletes the FIXME file.
