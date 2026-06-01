---
number: 0048
title: `cranelisp-primitives` owns a statically-constructed `SymbolTable` AND its `Arc<GotTable>`; CompilerSession references the static at startup; from session-init onward primitives dispatch is functionally equivalent to any other module
status: pre-implementation (S68)
sprint_filed: 68
filed_at: 2026-05-17
amended: 2026-05-17 (S68 Phase 3) — A2 revised: `Code::Primitive` marker variant (per user direction, full word); new §"Structural invariant — backend dep-ban" added (per user direction — `cranelisp-backend` MUST NOT depend on `cranelisp-primitives`)
amended: 2026-05-31 (S73 Phase 2, FIXME 0244) — **A2 reversed** (user-arbitrated): the `Code::Primitive` marker variant is dropped; primitives entries carry `code: None` (the `ModuleEntry::def(..).build()` builder default); primitive-ness is read from `kind: DefKind::Primitive`. The A1b position (`code: None`) is the accepted shape.
amended: 2026-05-31 (S73 Phase 2 top-up, user-arbitrated) — **backend dep-ban is now a bidirectional severance** `cranelisp-primitives ⟂ cranelisp-backend`. Consequent on the A2 reversal: with every entry `code: None`, primitives never constructs a `Code` value and therefore has no reason to *name* `Code` at all. Per user direction, primitives MUST NOT import `cranelisp-backend`; it builds a `()`-flavoured `SymbolTable<(), ()>` and `int` concretizes to `<Code, ()>` at the session mount via `SymbolTable::into_concrete::<Code, ()>()` (preserving the shared `Arc<GotTable>`). The previously-"permitted" `primitives → backend` edge retires. See §"Structural invariant — backend dep-ban" (rewritten below).
---

# 0048 — Primitives' SymbolTable + GotTable are statically constructed in the primitives crate

The `cranelisp-primitives` crate owns its `SymbolTable<C, L>` AND the `Arc<GotTable>` referenced by that table's `got()` field, both initialised at `LazyLock` time inside the crate. CompilerSession's startup path obtains an `Arc`-clone of the same SymbolTable (and therefore the same GotTable, transitively) and inserts it into the session's `SymbolTables` map at `ModuleFullPath::primitives()`. From the instant session-init completes, primitives' dispatch path is functionally equivalent to any other module — the standard cross-module call sequence (Decision 23 two-GOT model, Decision 31 GOT-indirect dispatch) is the *only* path. Backend's `symbol_lookup_fn` carries no primitives special-case.

## Decision

### Shape

```rust
// crates/cranelisp-primitives/src/lib.rs
use std::sync::{Arc, LazyLock};
use cranelisp_types::{GotTable, SymbolTable};

/// The synthetic `primitives` module's symbol table and GOT. Both are constructed
/// once per process at LazyLock init time; the contained `Arc<GotTable>` is
/// populated with raw `*const u8` fn pointers at prescribed slot indices for
/// every non-inlined primitive (string ops, marshal, per-type to_string,
/// int/float/bool conversions, `not`).
///
/// Per A2 reversal (S73 Phase 2, FIXME 0244, user-arbitrated 2026-05-31): each
/// `ModuleEntry::Def.code = None` — the builder default of
/// `ModuleEntry::def(scheme, kind).build()`. Primitive-ness is NOT encoded in
/// the `code` lifecycle field; it is read from `kind: DefKind::Primitive`
/// (the canonical fact, already consulted at 34 read sites). `code` retains
/// its single responsibility — the per-entry *runtime resource handle*
/// (`Some(Code::Jit{..})` / `Some(Code::Linker{..})` when there is owned
/// compiled code to retain/reclaim; `None` when there is not). Primitives have
/// no per-entry owned resource (the `LazyLock` is the owner), so `code: None`
/// is correct. The GOT slot continues to hold the raw `*const u8` per
/// **Decision 35** ("GOT is the single source of truth for callable
/// addresses; no per-entry pointer field") — preserved intact. There is no
/// `.primitive()` / `.code()` setter and no `CodeStore` constructor; the
/// builder's "`code` is runtime-state, not constructor-settable" invariant is
/// vindicated, not bent.
///
/// The `Arc` semantics already in `SymbolTable.got: Arc<GotTable>` carry the
/// wiring — primitives' GOT is NOT a new category in Decision 23's two-GOT
/// model; it is the SymbolTable-GOT row of that model, instantiated in static
/// memory rather than in per-session heap.
pub static PRIMITIVES_TABLE: LazyLock<Arc<SymbolTable<(), ()>>> = LazyLock::new(|| {
    // `()` code-store flavour — primitives never names `Code` (S73 sever).
    let table = SymbolTable::<(), ()>::new(ModuleFullPath::primitives());
    // populate ModuleEntry::Def entries with got_slot indices (code: None)
    // populate table.got() Arc<GotTable> with raw fn ptrs
    Arc::new(table)
});
```

CompilerSession startup:

```rust
// src/session_v4.rs (sketch) — int concretizes the ()-flavoured static to <Code, ()>
let primitives = (*cranelisp_primitives::PRIMITIVES_TABLE)
    .as_ref().clone()                  // SymbolTable<(), ()>  (got: Arc<GotTable> shared)
    .into_concrete::<Code, ()>();      // SymbolTable<Code, ()> — code: None per entry; got carried through
session.symbol_tables.insert(ModuleFullPath::primitives(), primitives);
```

The session's primitives `ModuleEntry`s hold `code = None` (A2 reversal, FIXME 0244) — there is no owned resource per entry (the `LazyLock` is the owner of the static fn addresses, which are not a reclaimable `Code` resource); primitive-ness is read from `kind: DefKind::Primitive`. The `Arc<GotTable>` they reach via `symbol_table.got()` is the same `Arc<GotTable>` the static created. There is one and only one GotTable for primitives in the process, regardless of how many sessions exist concurrently.

### The invariant

**From session-init onward, primitives dispatch is functionally equivalent to any other module.** Every primitive call from JIT-emitted code follows the standard cross-module call sequence:

1. Backend's codegen emits a GOT-indirect load against `__cranelisp_got_primitives` (CLIF: `global_value` on a `Linkage::Import` data symbol — byte-identical to user-to-user cross-module calls per Decision 23).
2. The JIT-mode `Module` impl's `symbol_lookup_fn` resolves `__cranelisp_got_primitives` to `symbol_tables[primitives()].got().base_ptr()` — which is the static `GotTable`'s base.
3. The emitted code loads the fn ptr from `got_base + slot * 8` and calls.

Backend's `symbol_lookup_fn` has no primitives-specific branch. `JITBuilder::symbol(name, ptr)` direct registration is reserved exclusively for intrinsics (Decision 43's backend-emitted-call targets that are *not* a module).

## Relationship to other Decisions

- **Decision 31 (one `JITModule` per compile batch; `Arc<Jit>` lifecycle).** Primitives are the **named exception** to the per-batch cardinality. Their lifecycle is **process-static**, not per-batch — the `LazyLock`'s init runs once; the `Arc<GotTable>` and the `Arc<SymbolTable>` survive every batch and every session. Decision 31's reclaim semantics (`Arc<Jit>` → 0 → `unsafe free_memory()`) **do not apply** to primitives because primitives have no `Code::Jit`; their fn ptrs are static Rust function addresses, not JIT pages. State this exception in Decision 31's "Consequences" the next time it is amended; no functional change to 31, only an explicit carve-out.
- **Decision 35 (GOT is single source of truth; no per-entry pointer field).** **Aligned (invariant preserved).** Primitives store fn ptrs in `GotTable` slots indexed by `ModuleEntry::Def.got_slot`, exactly as Decision 35's post-rollback canonical statement prescribes. No sibling `fn_ptr` field is introduced. The only difference from JIT user fns is the *origin* of the slot's `*const u8`: a Rust static address rather than a `jit.get_finalized_function()` return value. The slot itself, the read path, the GOT lifecycle are all uniform. Post-A2-reversal (FIXME 0244) primitives carry `code: None` — Decision 35's "no per-entry pointer field" invariant holds trivially: there is no `code` payload at all, and the GOT remains the single source of truth for callable addresses.
- **Decision 23 (two-GOT model — SymbolTable GOT vs `.o` data-section GOT).** **No new category.** Primitives' static `Arc<GotTable>` IS the SymbolTable-GOT row of Decision 23's table — it is "an `Arc<GotTable>` field on `SymbolTable`" exactly as the table says. The fact that the `Arc` is initialised once-per-process in static memory rather than once-per-session in heap is irrelevant to the model's semantics: same name (`__cranelisp_got_primitives`), same per-slot semantics, same atomic-swap discipline, same JIT-mode resolver path (`symbol_table.got().base_ptr()`). For `--link` mode, primitives' `.o` data-section GOT is the dual just as for any other module — exe-bundle's startup hook (see "Cascade" below) populates the linker-side GOT at process startup before any compiled code runs, mirroring Decision 23's "initialised by the linker at load time, never mutated" row.
- **Decision 43 (runtime split into primitives + intrinsics).** **Confirms the asymmetry.** Primitives are a module (this Decision wires them in as one); intrinsics are not a module (`JITBuilder::symbol(name, ptr)` direct registration is the canonical and only path; intrinsics have no `SymbolTable` entries, no GOT). The asymmetry becomes load-bearing post-S68 — it is the categorical line.
- **Decision 30 (form-by-form scheduler; `register_module_cached`).** **Cache-hit reload short-circuits for primitives.** Primitives are never cached (no `.meta.json`, no `.o`); the static is always present at session start. The cache-hit reload path of `register_module_cached` does not run for the primitives module — it cannot, and need not. State this carve-out in the design doc that hosts `register_module_cached`'s contract (`design/backend/module-caching.md`) at the next refresh.

## Structural invariant — backend dep-ban → bidirectional severance (S68 Phase 3 user revision 2026-05-17; rewritten S73 Phase 2 top-up 2026-05-31)

**`cranelisp-primitives ⟂ cranelisp-backend` — neither crate depends on the other.** Workspace `[dependencies]` and `[dev-dependencies]` alike, in both directions. The architectural invariant — "primitives dispatch reaches code via GOT, never via direct extern" — is **enforced structurally by the workspace DAG**: backend has no Rust-path visibility into primitives' fns, so backend physically cannot emit a direct-call instruction targeting a primitive. The only available path from backend-emitted code to a primitive is through the type-erased `SymbolTable` + GOT mechanism that resides in `cranelisp-types` (Decision 23 two-GOT model; Decision 31 GOT-indirect dispatch).

**Dep direction (S73 — bidirectional severance).** Both edges are forbidden:

- `cranelisp-backend → cranelisp-primitives` — forbidden (the original S68 dep-ban; backend must not name a primitive's extern fn).
- `cranelisp-primitives → cranelisp-backend` — **also forbidden as of S73** (top-up). The S68 model permitted this edge so primitives could name `Code` as the type parameter on `LazyLock<Arc<SymbolTable<Code, ()>>>`. The A2 reversal (FIXME 0244) removed primitives' only use of `Code` (every entry is `code: None`), and per user direction primitives now builds a `()`-flavoured `SymbolTable<(), ()>` and drops `cranelisp-backend` from its manifest entirely. `int` concretizes the static to `<Code, ()>` at the session mount via `SymbolTable::into_concrete::<Code, ()>()`, which maps each `code: Option<()>` to `None::<Code>` and carries the shared `Arc<GotTable>` through verbatim. Type uniformity with the live `SymbolTables<Code, ()>` map is thus achieved at the **session layer**, not at the primitives build — the pre-S73 "`C = Code` is load-bearing at the primitives build" framing is retired.

The workspace DAG is acyclic and the two crates are now mutually independent — verified pre-fire.

**Source-side landing split (S73 re-scope).** The primitives-side of the severance (drop `use cranelisp_backend::Code`, remove the `cranelisp-backend` line from `crates/cranelisp-primitives/Cargo.toml`, change the static to `<(), ()>`) lands **this sprint** (S73 Phase 5 `/dev primitives`). The backend-side cleanup (delete the `cranelisp_primitives::*` Rust paths from `intrinsic_symbols()`, remove the `cranelisp-primitives` line from backend's `Cargo.toml`, delete the `Code::Primitive` variant from `code.rs`) is **deferred to a future backend sprint** per user direction — it is decoupled from primitives by the severance (primitives no longer hostage to backend's red build) and tracked by FIXME 0191 + the backend sprint scope.

**Enforcement.**

1. **Cargo.toml is the contract (both manifests, S73).** `crates/cranelisp-backend/Cargo.toml` MUST NOT list `cranelisp-primitives`, AND `crates/cranelisp-primitives/Cargo.toml` MUST NOT list `cranelisp-backend` — under `[dependencies]` or `[dev-dependencies]`. The compliance test (`/qa`) is a trivial parse-and-assert of both manifests, NOT a CLIF-shape inspection. (The backend-manifest half remains red until the deferred backend sprint cleans `intrinsic_symbols()`; the primitives-manifest half lands this sprint.)
2. **Test #4 superseded.** The earlier `/qa` test plan proposed CLIF-shape inspection of backend output to verify "no direct call to primitives". The dep-ban replaces it — a structural property of the workspace is strictly stronger than a behavioral assertion verifiable only at compile time, because the structural property forecloses the behavior across all compilation paths (debug, release, future codegen modes, hypothetical `#[cfg(test)]` shims). `/sprint` incorporates the test #4 reframe at Phase 4 wave-org time.
3. **Phase 5 Wave 4 implementation consequence.** Backend's current `intrinsic_symbols()` body has direct Rust-path references to `cranelisp_primitives::ring0::ring0_jit_symbols()` plus the ~22 individual extern fns. All such references are deleted in Wave 4; the `cranelisp-primitives` line in `crates/cranelisp-backend/Cargo.toml` then comes out. Cleanup is mechanical but extensive — covered by FIXMEs 0182 (`ring0_jit_symbols()` retirement) + 0191 (`intrinsic_symbols()` primitives entries retirement).

User direction 2026-05-17: "backend should not import primitives crate." This converts the invariant from a behavioral assertion to a structural property of the workspace DAG.

## Cascade

The following facades and design docs must update because of this Decision (S68 Wave 2):

- `design/arch/facades/primitives.md` — `PRIMITIVES_TABLE` type is `LazyLock<Arc<SymbolTable<(), ()>>>` (S73 sever — was `LazyLock<Arc<SymbolTable<Code, ()>>>` S68; `LazyLock<SymbolTable>` pre-S68 per FIXME 0159); document that the `Arc<GotTable>` reachable via `.got()` is statically initialised, never reallocated, and preserved through `int`'s `into_concrete::<Code, ()>()` at the session mount. Per A2 reversal (FIXME 0244): `code = None` (builder default); primitive-ness read from `kind: DefKind::Primitive`; raw `*const u8` in GOT per Decision 35. Note the `not` addition (Decision C1). Note the §"Structural invariant — backend dep-ban → bidirectional severance". (Landed S73 Phase 2 top-up.)
- `design/arch/facades/intrinsics.md` + `bounded-contexts.md §4a/§4b` — the primitives↔intrinsics **layout-ABI** boundary (FIXME 0245): heap/Vec layout consts are intrinsics' blessed public ABI; primitives is a named Rust consumer; intrinsics is the only workspace dep primitives keeps besides `cranelisp-types`. (Landed S73 Phase 2 top-up.)
- `design/arch/facades/backend.md` — `intrinsic_symbols()` body shrinks (FIXME 0191); primitives entries retire. The §"`primitives_inline.rs` retirement narrative" updates: the GOT-indirect dispatch path is *the* path post-S68, and inline substitution becomes the optional optimisation it was always intended to be. **Add (S68 Phase 3 revision):** dep-ban statement — `cranelisp-backend` MUST NOT depend on `cranelisp-primitives`; the workspace DAG enforces the GOT-dispatch invariant structurally. Phase 5 Wave 4 cleanup deletes the current `cranelisp_primitives::*` Rust paths from `intrinsic_symbols()` and removes the `cranelisp-primitives` line from `Cargo.toml`.
- `design/arch/facades/intrinsics.md` — confirm `JITBuilder::symbol(name, ptr)` is intrinsics-only post-S68. No public-API change expected; doc-comment refresh only.
- `design/arch/facades/int.md` — session-init references `cranelisp_primitives::PRIMITIVES_TABLE`. No `ring0_jit_symbols()` consumption.
- `design/backend/module-caching.md` (FIXME 0163) — cache-hit reload carve-out for the primitives module.
- `design/int/platform-registry-removal.md` (FIXME 0162) — GOT-as-source-of-truth narrative.
- `design/typecheck/ast-annotation.md` (FIXME 0164) — same.
- `src/CLAUDE.md` §"JIT Symbol Names" — table row for primitives changes to "GOT-indirect via `PRIMITIVES_TABLE.got()`".
- `design/arch/fixmes/0161-*.md` — closes with one-line note "superseded by Decision 48 (static-table-in-crate hybrid)".

## Rationale: alternatives considered

- **Alternative B1: primitives' SymbolTable + GotTable constructed per-batch like all modules, lifecycle-aligned with Decision 31.** Rejected. The user explicitly identified per-batch redundancy as a "smell": primitives' fn ptrs are address-stable for the process lifetime, identical across every batch and every session. Per-batch construction does the same work N times for no semantic gain and inflates the surface area of `register_intrinsics`. Principle 7 (single source of truth) is the operative test — one static, not N copies.
- **Alternative B2: process-lifetime static with a new "static GOT" category added to Decision 23's two-GOT model.** Rejected. The `Arc<GotTable>` shape already in `SymbolTable.got` is sufficient — an `Arc<GotTable>` whose backing `GotTable` lives in static memory is operationally identical to one in heap memory from the GOT-API consumer's POV (`base_ptr()`, `load_slot()`, `store_slot()` all work uniformly). Adding a third category would introduce special-cased dispatch logic in `symbol_lookup_fn` — defeating the goal of this Decision (which is *eliminating* primitives' special case). The user's framing of "B-hybrid" landed exactly because B1 and B2 are a false dichotomy: the static-Arc shape avoids both pitfalls.
- **Alternative A1 (re Decision A2 framing): `Code::Extern { name: &'static str, ptr: *const u8 }` variant in the `Code` enum.** Rejected by Decision A2 (S68 review, user-arbitrated). `Code` carries lifecycle ownership; primitives have no lifecycle owner per-entry (the `LazyLock` is the owner, and it is process-static). A payload-bearing `Extern` variant would either duplicate the GOT's `*const u8` storage (breaking Decision 35's "single source of truth") or carry only a name (gratuitous wrapping with no semantic content).
- **Alternative A1b: `code: None` on every primitives entry; no `Code` enum variant for extern origin. — ACCEPTED (S73 Phase 2, FIXME 0244).** Was the Phase 2 verdict and the §"Shape" text up to 2026-05-17; briefly displaced by the A2 `Code::Primitive` marker (2026-05-17 — 2026-05-31); **restored as the accepted shape by the A2 reversal** (FIXME 0244, user-arbitrated 2026-05-31). The A2 marker's rationale — "make the lifecycle category visible at every match site over `code`" — never cashed out: `Code::Primitive` was referenced functionally in exactly two non-test places (a `Debug` arm and `ptr()` returning null), both no-ops equivalent to `None`, and produced zero match sites doing real work on the category. Meanwhile primitive-ness is already read from `kind: DefKind::Primitive` at 34 sites. The marker duplicated a *kind* fact into the *lifecycle* field. `code: None` restores `code`'s single responsibility (runtime resource handle), is the `ModuleEntry::def(..).build()` builder default (no `.primitive()`/`.code()` setter, no `CodeStore` constructor), and is unambiguous in practice ("primitive — never has code" vs "user fn — not yet compiled" is disambiguated by the non-optional `kind`, held by every site that cares).
- **Alternative E1 (re §"Structural invariant — backend dep-ban"): behavioral CLIF-inspection test ("backend's emitted CLIF never contains a direct call to a primitive symbol").** Considered and superseded by the dep-ban (user direction 2026-05-17). Behavioral tests verify a single compilation path; structural dep-bans foreclose the behavior across all paths (debug, release, hypothetical future codegen modes, `#[cfg(test)]` shims). The dep-ban is strictly stronger and trivially testable (parse Cargo.toml; assert absence). The behavioral test is dropped from `/qa`'s Phase 4 plan.

## Consequences

- **No `Code::Primitive` marker variant** (A2 reversed, S73 Phase 2, FIXME 0244). The S68-Phase-3 marker is dropped; the `Code` enum carries only the two lifecycle-owning variants `Code::Jit(Arc<Jit>)` / `Code::Linker(Arc<Linker>)`. Every primitives `ModuleEntry::Def.code = None` (the `ModuleEntry::def(..).build()` builder default); primitive-ness is read from `kind: DefKind::Primitive`. Phase 5 `/dev backend` deletes the variant and its dedicated `code.rs` unit tests; `/dev primitives` rebuilds the two construction sites via the builder and rewrites the marker test to assert `kind`. Decision 35 invariant preserved (the GOT is the single source of truth for callable addresses).
- **`cranelisp-primitives ⟂ cranelisp-backend` — bidirectional severance** (S68 Phase 3 dep-ban + S73 top-up). Neither crate depends on the other. The primitives-side (drop `cranelisp-backend`; build `SymbolTable<(), ()>`) lands this sprint (S73). The backend-side (delete `cranelisp_primitives::*` Rust-path references in `intrinsic_symbols()`; remove the `cranelisp-primitives` line from `crates/cranelisp-backend/Cargo.toml`) is **deferred to a future backend sprint** per the S73 re-scope. Workspace DAG remains acyclic. The GOT-dispatch invariant for primitives becomes a structural property of the workspace, not a behavioral assertion. `int` achieves `<Code, ()>` type uniformity at the session mount via `into_concrete`.
- Backend's `intrinsic_symbols()` shrinks (FIXME 0191 closure); the primitives entries it currently enumerates retire.
- `ring0_jit_symbols()` retires (FIXME 0182 closure).
- `cranelisp-primitives`' published Rust API collapses to one item (`PRIMITIVES_TABLE`); the ~22 individual `pub extern "C" fn` items demote to `pub(crate)` with `#[used]` discipline to prevent DCE.
- `cranelisp-exe-bundle`'s force-link `pub use cranelisp_primitives::string;` lines retire; an `init_primitives_got()` startup hook (or equivalent `#[used]` ref via `extern crate cranelisp_primitives;` in `cranelisp_init_platform`) replaces them — for `--link` mode the static archive must contain the primitives fns AND must populate the linker-side `.o` data-section GOT at startup before any compiled code runs.
- `not` is authored as a primitive (Decision C1; FIXME 0157 closure).
- Decision 31's consequences gain an explicit "primitives exempt — process-static" carve-out at next amendment.
- Decision 30's cache-hit reload path acquires an explicit "primitives module never cached" carve-out.

## Status pointer

This Decision is **active** through S68's implementation and lockdown. Once S68 closes with `PRIMITIVES_TABLE` published, the special-case branches deleted, and facades regenerated against the new shape, the Decision becomes vestigial (the commitment is embodied in `facades/primitives.md` + `facades/backend.md` + `facades/intrinsics.md` + `facades/int.md` + the source). At S68 close (Phase 7), `/arch` evaluates per `design/arch/CLAUDE.md` §"Decisions" whether to retire this Decision to `legacy/decisions/` or keep it as an environmental record of the primitives-vs-modules asymmetry resolution.

## Cross-references

- `decisions/0023-uniform-codegen-mode-as-module-property.md` (legacy) — two-GOT model that this Decision instantiates for primitives
- `decisions/0031-one-jitmodule-per-compile-batch.md` — the per-batch JIT lifecycle this Decision carves an exception from
- `decisions/0035-code-enum-integration-layer.md` — the GOT-as-source-of-truth post-rollback statement this Decision aligns with
- `decisions/0043-runtime-split-into-primitives-intrinsics.md` — the categorical distinction (modules vs. backend-emitted targets) that makes the asymmetry load-bearing
- `decisions/0030-form-by-form-scheduler-mutual-imports.md` — `register_module_cached` flow carve-out for primitives
- `fixmes/0210-arch-primitives-as-uniform-module-with-symboltable-and-got.md` — the primary FIXME this Decision resolves
- `fixmes/0161-arch-post-s66-static-got-for-primitives.md` — superseded by this Decision
- `principles/07-single-source-of-truth.md` — operative test for B1 rejection
- `principles/08-no-interim-implementations.md` — the static-table shape is the **target** shape, not an interim
- `principles/14-ffi-layout-discipline.md` — primitives are FFI; layout discipline applies
- `principles/15-facade-types-live-with-behavior.md` — the static table sits with the primitives it indexes
- `principles/17-module-locality-in-typecheck.md` — primitives belong with primitives crate, not with backend
- `principles/18-enforce-invariants-structurally.md` — the dep-ban as worked example; the GOT-dispatch invariant is enforced by the workspace DAG, not by a behavioral test (S68 Phase 3 user revision 2026-05-17). Note: Principle 18 is grounded by the dep-ban, which is unaffected by the A2 reversal (FIXME 0244); the dropped `Code::Primitive` marker was never load-bearing for P18.
