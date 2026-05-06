---
number: 0150
target: /dev
filed_by: /arch
filed_at: 2026-05-05
sprint_filed: 65
refers_to: design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md, design/arch/principles/16-punctuation-symbols-are-not-special.md, design/arch/legacy/substance-scoping.md §1.7, design/arch/bounded-contexts.md §4 (retiring), design/arch/fixmes/0103-dev-runtime-int-trace-io-trace-relocation-and-io-observer.md, spec/appendix-a-builtins.md, crates/cranelisp-runtime/, crates/cranelisp-backend/src/operators.rs, crates/cranelisp-backend/src/compiler/literals.rs, crates/cranelisp-backend/src/jit.rs, stdlib/core/num.cl, stdlib/core/formats.cl
status: open
---

# Implement Decision 43: split `cranelisp-runtime` into `cranelisp-primitives` + `cranelisp-intrinsics`

## Issue

Decision 43 (runtime split) is filed but unimplemented. Source still carries the broken model:

- `cranelisp-runtime` bundles two distinct categories (language-level primitives + backend-emitted intrinsics) under one BC.
- Backend carries trait knowledge as a `(TraitName, Symbol, TypeName) → primitive-name` table (`cranelisp-backend/src/operators.rs:323–394`) and a parallel operator-as-value table in `literals.rs:327–332` — a Decision-14 closure-table mechanism that Principle 16 prohibits and Decision 43 retracts.
- Spec primitives are inconsistently realised in source. Some appear only as inline-CLIF substitutions in the backend's name-keyed table with no symbol-table entry; others appear as separately-named extern fns (`cranelisp_op_*`) that duplicate named primitives (`add-i64` etc.) as addressable forms. The mappable path (primitive as a first-class value) and the inline path (primitive at a direct call site) are not coherent for every spec primitive.

Decision 43's resolution requires deleting the trait-knowledge maps in coordinated fashion with the crate split, the stdlib trait-impl audit, the BC §4 retirement, and a coverage gate that proves every spec primitive works on both paths.

## Proposed resolution

Multi-crate migration; sequenced per Decision 43's "Sequencing" section. Phasing per-crate to keep intermediate states green:

**Phase 1 — `/dev` (arch-direct, types-adjacent)**: Land empty `cranelisp-primitives` and `cranelisp-intrinsics` crate skeletons; root `Cargo.toml` workspace updates; placeholder facades at `design/arch/facades/primitives.md` + `design/arch/facades/intrinsics.md`; `cranelisp-runtime` retains all symbols (no deletions yet — the new crates re-export from runtime initially to keep deps stable).

**Phase 2 — `/dev` (runtime, primitives, intrinsics, all narrow)**: Move sources per the Decision-43 migration table:

| Source | Destination |
|---|---|
| `cranelisp-runtime/src/primitives/{int,float,bool,mod}.rs` | `cranelisp-primitives/src/` |
| `cranelisp-runtime/src/rc.rs` | `cranelisp-intrinsics/src/rc.rs` |
| `cranelisp-runtime/src/drop.rs` | `cranelisp-intrinsics/src/drop.rs` |
| Allocator (`cranelisp_alloc` etc.) | `cranelisp-intrinsics/src/alloc.rs` |
| `cranelisp-runtime/src/io.rs` (trampoline) | `cranelisp-intrinsics/src/io.rs` |
| `cranelisp-runtime/src/panic.rs` | `cranelisp-intrinsics/src/panic.rs` |
| IoObserver registration API (post-FIXME 0103) | `cranelisp-intrinsics/src/io_observer.rs` |

**Coordinate with FIXME 0103** (trace/io_trace relocation runtime → int): both FIXMEs touch `cranelisp-runtime/src/io.rs` and the IoObserver registration site. Resolve sequencing at wave-plan time:

- Option (a) — FIXME 0103 lands first in S65 (per current scope): IoObserver lives in `cranelisp-runtime` until this FIXME's wave, then migrates to `cranelisp-intrinsics` as part of Phase 2.
- Option (b) — bundle both into the same wave: IoObserver lands directly in `cranelisp-intrinsics`; FIXME 0103 closes within this FIXME's wave.

`/sprint` chooses at the wave-plan boundary.

**Phase 3 — `/dev` (backend) — apply Principle 16**: Delete trait-knowledge maps and rename the file:

1. Delete `cranelisp-backend/src/operators.rs:323–394` (`(TraitName, Symbol, TypeName) → primitive-name` map). Per Principle 16 — backend has no trait knowledge; trait dispatch resolves at typecheck/stdlib.
2. Delete `cranelisp-backend/src/compiler/literals.rs:327–332` (`"+" → "cranelisp_op_add"` map). Per Principle 16 — operator-as-value is not a separate path; the symbol resolves and dispatches by name like any other reference.
3. Rename `cranelisp-backend/src/operators.rs` → `cranelisp-backend/src/primitives_inline.rs` (or similar name-neutral form). Files named for the lexical shape of their contents are an architectural smell per Principle 16; the legitimate role of this file is "name-keyed inline primitive substitutions" and the name should reflect that. The surviving substitution table at line 38 (`"add-i64" => iadd`) is name-keyed and stays.
4. Update `cranelisp-backend/src/jit.rs` `IntrinsicSymbol` array: remove `cranelisp_op_*` entries (their existence today is the Decision-14 mechanism Decision 43 retracts); keep legitimate intrinsic-backed primitive GOT slots (e.g., `int-to-string`).
5. Backend's `Cargo.toml` revises: depend on `cranelisp-intrinsics` (for emitted-symbol declarations) AND `cranelisp-primitives` (for symbol-table seeding); drop `cranelisp-runtime` dep.

**Phase 4 — `/dev` (stdlib, primitives) — trait-impl audit**: Each `(impl Trait Type)` body in the stdlib should call the primitive directly, e.g.:

```
(impl Num Int
  (defn + [a b] (add-i64 a b)))
```

Audit every relevant impl — `(impl Num Int)`, `(impl Display Int)`, `(impl Eq Int)`, `(impl Ord Int)`, `(impl Num Float)`, and any other primitive-backed impl `/qa` surfaces — and refactor where the impl was relying on backend's collusion (i.e., the impl method was an empty marker that backend's `(Trait, method, Type) → primitive-name` map intercepted before the call ever reached the impl body, or where the body delegated back to the operator and only "worked" because the map intercepted upstream of the recursion). The refactor must precede or land with the Phase 3 deletions; otherwise the recursion breaks at runtime.

After the audit, delete the `cranelisp_op_*` extern fn duplicates from `cranelisp-primitives/src/primitives/int.rs` (post-relocation). The single named-primitive form (`add-i64` etc.) is the addressable form; the operator-as-value path goes through the resolved trait-impl entry, which calls the primitive directly.

**Phase 5 — `/dev` (arch + per-crate)**: Retire `cranelisp-runtime`; finalise BCs and facades.

1. Once all sources have moved, delete `crates/cranelisp-runtime/`. Workspace `Cargo.toml` removes the member.
2. `bounded-contexts.md` §4 retires; replaced by §4a (Primitives) + §4b (Intrinsics) per Decision 43.
3. `design/arch/facades/runtime.md` retires; replaced by `design/arch/facades/primitives.md` + `design/arch/facades/intrinsics.md` (full bodies authored from the Decision-43 categorisation).
4. `src/CLAUDE.md` "JIT Symbol Names" section updates: "Runtime infrastructure" row renames to "Intrinsic"; user-visible primitives row says "registered into the symbol table at `primitives/<name>`".
5. `cargo public-api` baselines for the new crates; the runtime baseline file deletes.

## Test coverage gate (S66 — `/qa`-directed)

The new `cranelisp-primitives` crate's populate is **gated on test coverage**. Before Phase 4 closes, `/qa` authors integration tests proving that every spec primitive works on both paths the language exposes. Test authoring waits until the new crates exist (Phase 1) and the migration is far enough along that the test target is stable; the populate of `cranelisp-primitives` does not close until the tests pass.

**Spec is the authority on the primitive list.** Primary reference: `spec/appendix-a-builtins.md` (e.g., the "Boolean" subsection at line ~75 includes `not`; integer + float arithmetic + comparison primitive tables surround it; extern primitives follow). Cross-spec references — `spec/03-types.md` (type-related extern primitives), `spec/12-runtime.md`, and any other normative section — are part of the surface. `/qa` reads spec exhaustively; this FIXME does not enumerate the list because the spec does, and a stale enumeration here would compete with the authority.

**For every primitive listed in spec, two tests must pass:**

- **Inline-path test** — direct call site `(prim args...)`. Exercises backend's name-keyed inline substitution (the surviving `primitives_inline.rs` table) for primitives that are inline-substituted, or the GOT-direct call for primitives that are not.
- **Mappable-path test** — primitive as a first-class value: `(let [f prim] (f args...))`, or `(map prim ...)`, or any form that requires the primitive to be addressable as a value. Exercises GOT-indirect dispatch through the symbol-table entry.

Both tests must pass for every spec primitive. Anything in spec that fails one or both is an implementation gap that this FIXME closes. The current state — `not` has only the inline path via `crates/cranelisp-backend/src/operators.rs:64`, no symbol-table entry, mappable path almost certainly fails — is exactly the gap the gate exists to surface.

The test suite is the durable record. Coverage holes are visible at PR time, regression caught permanently, and the "what is a primitive" question routes to spec rather than to the FIXME body.

## Operational implication / Context

- **Multi-crate scope.** Touches `cranelisp-runtime` (retires), `cranelisp-primitives` (new), `cranelisp-intrinsics` (new), `cranelisp-backend` (deletions + rename), stdlib (audit), `crates/cranelisp-exe-bundle/` (linker dep updates), `src/` (Cargo deps + JIT-symbol-names doc), workspace `Cargo.toml`.
- **Coordinates with FIXME 0103** (trace/io_trace relocation). The IoObserver registration site is co-resident with the io trampoline; both FIXMEs can land independently if Phase 2 is sequenced as Option (a) above, or bundled if Option (b).
- **Coordinates with FIXME 0107** (PlatformFnDescriptor non-exhaustive — currently in S65 scope). No direct file overlap; can run in parallel.
- **NOT a blocker for S65 facade-adoption work.** S65 currently scopes the 7 cross-crate FIXMEs (0098, 0099, 0100, 0103, 0104, 0107, 0108) plus `cargo public-api` enforcement. This FIXME's implementation can run as S65 Wave 0 (delays the facade-adoption work; user-decided trade-off), as S66 (sequenced after S65 facade adoption stabilises), or as a dedicated multi-crate sprint of its own. `/sprint` decides at the next sprint-plan boundary.
- **Tests are S66 work.** The coverage gate above gates the `cranelisp-primitives` populate; test authoring follows Phase 1 (crate skeletons exist) and precedes Phase 4 close (impl audit not declared done until tests pass).
- **Risk: stdlib trait-impl audit.** The Phase 4 audit may surface impls that relied on backend's collusion in non-obvious ways — operators that "just worked" because backend intercepted before the impl body ran. Where the impl body is empty, fill with a direct primitive call. Where the impl body delegates back to the operator (`(defn + [a b] (+ a b))` — circular under the corrected model), the recursion breaks the moment the trait-knowledge map deletes; the audit must catch these before Phase 3 lands.
- **Test impact (intermediate paths).** Tests that exercise operators-as-values (`(let [f +] (f 1 2))`) currently route through `cranelisp_op_add`; after the Phase 4 deletions, the path goes through the `+`-symbol-table-entry's GOT slot which holds the `(impl Num Int)` impl body which calls `(add-i64 a b)` which backend may inline. Net behaviour unchanged; intermediate code path different. The S66 mappable-path tests are the regression guard.
