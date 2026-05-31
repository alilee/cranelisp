---
number: 0046
title: Wave 3a splits into α (locality refactor) before β (cluster-atomic triad)
status: pre-implementation
filed: sprint 66 (Phase 3 FIXME 0168 resolution)
canonical_location: design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md §"Sequencing"; design/arch/facades/typecheck.md §"Bounded-context invariants" item 10; design/arch/principles/17-module-locality-in-typecheck.md
amends: [0044]
amended_by: []
retracts: []
reframes: []
filed_by_fixme: 0168
---

# 0046 — Wave 3a-α (locality refactor) precedes Wave 3a-β (cluster-atomic triad)

## Statement

Sprint 66 Wave 3a re-fires as two sub-waves:

- **Wave 3a-α — locality-correctness refactor** (estimated 3–5 days). Replace 40+ direct `self.modules.X` access sites in `crates/cranelisp-typecheck/src/{checker,infer,traits,builtins}.rs` with the four principled access-pattern shapes defined in Principle 17. The ~6 direct mutating writes in `builtins.rs` + `checker.rs` (impls written into foreign modules) retarget to the writer's module per Decision 0045. The 91 register-call sites and 51 read-access sites already flow through `current_symbol_table` / `current_symbol_table_mut`; α's surgery is on the orphaned cross-module accesses that don't.

- **Wave 3a-β — cluster-atomic triad implementation** (estimated 3–4 days). Build `frontend::build_form` (FIXME 0156), `typecheck::check_forms` (Decision 44 third amendment 2026-05-13 — single-call cluster surface; internal two-pass discipline), `int::process_cluster` (Decision 44), and the `SymbolTableAccess` accessor adaptation, atop the locality-correct typecheck.

Wave 3a-β cannot start before α completes. The reasoning is structural: cluster-atomic correctness depends on every typecheck read and write flowing through `ctx.current_symbol_table[_mut]()`. An orphaned `self.modules.X` pierce in a typecheck pass would read live during cluster mode (ignoring staging) and silently weaken the live-table invariant, rendering Decision 44's staging surgery ineffective. The third Wave 3a re-attempt (2026-05-12) blocked on exactly this — the locality violations are structurally inconsistent with the cluster-atomic shape, not just stylistically untidy.

Total Wave 3a envelope: ~6–9 days (α + β), within the Sprint 66 envelope per `sprints/SPRINT.md`.

## Rationale

The Wave 3a triad as originally scoped (Decision 44) assumed the typecheck source was already locality-correct and that the surgery would be on the `SymbolTableAccess` accessor and the orchestrator. In fact, ~40+ direct `self.modules.X` access sites bypass the accessor entirely — short-name lookups iterating every module, `find_impl_for_type` scanning the whole module set, `all_methods_of_type` aggregating across modules, mutating writes landing in foreign modules. With these sites in place, the accessor surgery alone does not buy cluster atomicity:

- A short-name lookup that iterates `self.modules` finds entries in the live table only — staging entries written earlier in the same cluster are invisible. Pass 2 cannot see Pass 1's signatures (the very property cluster atomicity is supposed to provide).
- A cross-module mutating write lands in a different module's live table, bypassing the staging-and-drain shape entirely. Cluster failure cannot roll it back; cluster commit is moot because the write already happened.

Both pathologies are removed by Principle 17's access-pattern enforcement. Once every read flows through `current_symbol_table()` (which routes through staging for the current module) and every write flows through `current_symbol_table_mut()` (which targets staging for the current module), the cluster-atomic property holds by construction. α is therefore a precondition for β, not a parallel workstream.

### Why not interleave α with β?

Interleaving was considered. Rejected because:

1. **Diagnosability.** β's tests assert cluster-atomic properties (Pass 2 sees Pass 1 signatures; cluster failure leaves live byte-identical). With α incomplete, a failing β test could mean either "the new triad is wrong" or "an unconverted access site is leaking through" — debugging cost is much higher.

2. **Reviewability.** α is a mechanical-feeling but locally-thoughtful sweep (each site has a principled replacement, but the principle requires reading the surrounding code). β is a small number of new functions and a non-trivial orchestrator shape. Interleaving them produces a single PR that mixes 40+ small site replacements with the structural triad, which `/review` cannot audit cleanly.

3. **Test cadence.** α can land with the existing test suite (the access-pattern replacements should be observably identical for non-cluster code paths, which is currently every code path). β changes the dispatch shape — a new gate test (`tests/process_form_dispatch.rs` revision per Decision 44 §"Sequencing") is part of β. Decoupling lets α land and stabilise before β changes the test surface.

## Consequences

### Decision 0044 amendment

Decision 0044's "Sequencing" section is amended to reference the α-then-β split. The original sequencing item 3 ("Wave 3a triad re-fires") becomes item 3' ("Wave 3a-α — locality refactor; precondition") and 3'' ("Wave 3a-β — triad re-fires atop locality-correct typecheck"). The semantic content of Decision 0044 (the cluster-atomic shape, SymbolTableAccess, View, the two-pass surface) does not change.

### Per-skill assignment

- **Wave 3a-α** is `/dev` narrow per typecheck: a typecheck-internal sweep with no facade or cross-crate impact. `/arch` review per Phase 5 (no public-API change anticipated; if α surfaces one, file FIXME `target: /arch`). `/qa` confirms no regression in current behaviour (every access-pattern replacement should be observably identical pre-cluster).
- **Wave 3a-β** is the original triad (frontend + typecheck + int) per Decision 44's Sequencing. `/arch` reviews public-API changes (`check_form` → `check_forms` per Decision 44 third amendment; `process_form` → `process_cluster`); `/dev` narrow per crate implements; `/review` per crate audits as-built against facade.

### Acceptance criteria for α

α is complete when:

1. No `self.modules.X` access remains in `crates/cranelisp-typecheck/src/` outside the four principled shapes (Principle 17).
2. The ~6 direct mutating writes in `builtins.rs` + `checker.rs` write to the current module (writer's module, per Decision 0045).
3. `find_impl_for_type` walks the current module's transitive import closure (per Decision 0045 + `/spec`'s resolution of FIXME 0169).
4. `all_type_defs` / `all_macros` / equivalent bulk-introspection paths are current-module-only; multi-module aggregation moves to the orchestrator (session/REPL layer).
5. Existing test suite remains green; no new test failures.
6. `/review` typecheck audit confirms compliance with Principle 17.

### Acceptance criteria for β

β is complete when:

1. `frontend::build_form` produces `ParsedEntry` values per FIXME 0156's resolution; `parse_defmacro` becomes `pub(crate)`.
2. `typecheck::check_forms(parsed: Vec<ParsedEntry>, ctx: &mut SymbolTableAccess, symbol_tables: &SymbolTables) -> Result<(), CheckError>` exists; pure with respect to live state; internal two-pass discipline (Pass 1 signatures, Pass 2 bodies) lives inside its frame.
3. `int::process_cluster` constructs `SymbolTableAccess::Cluster { modules, staging, current_module }` per cluster, makes one `check_forms` call per cluster, then commits staging atomically into live (drop-on-Err / drain-on-Ok).
4. `(begin form₁ … formN)` REPL inputs are unwrapped into one cluster (per `/spec` resolution of FIXME 0165); non-`begin` REPL inputs are one-form clusters.
5. `tests/process_form_dispatch.rs` revision passes (forward-ref defns inside `(begin)` work; cross-input forward references produce a clear error).
6. `/review` per-crate audit confirms compliance with the facades for frontend, typecheck, int.

## Cross-references

- `design/arch/decisions/0044-cluster-atomic-typecheck-orchestrator-staging.md` §"Sequencing" — the amendment lives there.
- `design/arch/decisions/0045-traitimpl-storage-in-writers-module.md` — the storage-placement Decision Wave 3a-α realises.
- `design/arch/principles/17-module-locality-in-typecheck.md` — the access-pattern principle Wave 3a-α encodes.
- `design/arch/facades/typecheck.md` §"Bounded-context invariants" item 10 — the module-locality invariant.
- `design/arch/fixmes/0168-arch-traitimpl-storage-and-typecheck-module-locality.md` — the FIXME this Decision resolves (deleted on commit).
- `sprints/SPRINT.md` — Wave 3a envelope expansion (recorded by `/sprint`).

## Sequencing

1. This Decision + Decision 0045 + Principle 17 + facade updates land (this commit).
2. `/spec` lands FIXME 0169 (impl-visibility traversal mechanism — Reading 2 transitive recommended).
3. Wave 3a-α — typecheck locality-correctness refactor.
4. Wave 3a-β — cluster-atomic triad re-fires atop locality-correct typecheck (per Decision 44 §"Sequencing").
