---
number: 0239
target: /arch
filed_by: /sprint
filed_at: 2026-05-30
sprint_filed: 72
refers_to: crates/cranelisp-typecheck/src/builtins.rs (seed_test_primitives §1057-1298), design/arch/facades/typecheck.md, design/arch/bounded-contexts.md §2, crates/cranelisp-primitives/src/lib.rs (PRIMITIVES_TABLE)
status: open
---

# Generalize: "instantiate a module symbol table from a source" as facade concept

## Issue

Sprint 72 Wave 1 surfaced a structural mismatch in how unit-test fixtures relate to production primitive registration. After Trigger 1 (delete `register_primitives` flow per Decision 0048), 81 unit tests in `cranelisp-typecheck` failed because `TestFixture::new()` no longer seeds primitives.

The mitigation was `seed_test_primitives` (`builtins.rs:1057-1298`) — a hand-rolled, in-crate duplicate of ~38 primitive scheme constructions that mirrors `cranelisp-primitives::PRIMITIVES_TABLE`. This is **structurally wrong**:

1. **Drift risk**: when `PRIMITIVES_TABLE` evolves (new primitive, scheme tweak), `seed_test_primitives` silently goes stale; trait-method / constrained-poly tests pass against the wrong oracle. No test verifies they match. `test_primitive_count` (line 1474) checks names only.

2. **Wrong test discipline**: test fixtures should be selected to **fully flex the data structure** — exercising overloads, polymorphism, constraints, edge-arity cases — not to mirror production content. A test fixture that mirrors production tests both at once: a change to production content invalidates the test.

3. **No facade concept**: there is no architectural concept for "instantiating a module symbol table from a source." Sources include:
   - The `PRIMITIVES_TABLE` static (cranelisp-primitives' approach)
   - `.meta.json` cache reload (cranelisp-backend's approach)
   - Programmatic test builders (the gap this FIXME names)
   - Hypothetical future: foreign-module ABI bindings, DLL platform descriptors, etc.

Each source-type currently uses its own ad-hoc code path; no shared facade. Test fixtures fall through the cracks.

## Proposed resolution

`/arch` authors a facade concept — **"ModuleSymbolTableSource"** or similar — that captures the contract for instantiating a module's `SymbolTable<C, L>` from a source. The contract specifies:

- What the source provides (entry shapes, scheme structure, FQ identity, visibility, etc.)
- What the consumer expects (compiled SymbolTable ready for typecheck/backend/REPL consumption)
- Invariants: e.g., every entry has correct `seq` ordering; visibility is honored; no half-state on failure

Sources implement against the facade:
- **`PrimitivesSource`**: `cranelisp-primitives::PRIMITIVES_TABLE` static; Arc-cloned at session init
- **`CacheSource`**: `.meta.json` reload path
- **`TestSource`**: test fixtures select entries that exercise the data structure surface, not mirror production primitives

Phase B disposes seed_test_primitives:
- Either deleted in favor of TestSource (the right answer)
- Or retained as a TestSource implementation focused on shape-coverage (overloads, poly schemes, constraint chains) rather than production-content mirroring

The facade then guides Phase B's IntrinsicType activation work (per S72 Wave 2 close): `PRIMITIVES_TABLE` is a PrimitivesSource that registers Int/Float/Bool/String as `IntrinsicType { ty: Type::Int }` entries (per the dual-representation-defect fix); typecheck consumes via the facade, never reaches into specific source machinery.

## Operational implication / Context

Without this facade, primitive registration drift is silent. Phase B's IntrinsicType activation will touch the same surface (`register_builtin_type_names`, `seed_test_primitives`); ideal to land the facade concept concurrently so both changes flow through the same abstraction.

Sprint 72 Wave 2 `/review typecheck` named this as Important finding **I-3**.

## Related

- Decision 0048 — `cranelisp-primitives` as uniform module with SymbolTable + GOT
- Decision 0047 — FQTypeName binding at resolved-stage boundaries
- Sprint 69 Submission 30 — dormant `ModuleEntry::IntrinsicType { ty: Type }` variant
- Sprint 72 SPRINT.md §Notes 2026-05-30 — dual-representation defect surfaced
- Sprint 72 Wave 2 /review verdict — I-3 (oracle gap)
- `feedback_audit_per_item_analysis`, `feedback_configuration_grounds_facade` — methodology
