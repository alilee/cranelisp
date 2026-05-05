---
number: 0150
target: /dev
filed_by: /arch
filed_at: 2026-05-05
sprint_filed: 65
refers_to: design/arch/decisions/0043-runtime-split-into-primitives-intrinsics.md, design/arch/legacy/substance-scoping.md §1.7, design/arch/bounded-contexts.md §4 (retiring), design/arch/fixmes/0103-dev-runtime-int-trace-io-trace-relocation-and-io-observer.md, crates/cranelisp-runtime/, crates/cranelisp-backend/src/operators.rs, crates/cranelisp-backend/src/compiler/literals.rs, crates/cranelisp-backend/src/jit.rs, stdlib/core/num.cl, stdlib/core/formats.cl
status: open
---

# Implement Decision 43: split `cranelisp-runtime` into `cranelisp-primitives` + `cranelisp-intrinsics`

## Issue

Decision 43 (runtime split) is filed but unimplemented. Source still carries the broken model:

- `cranelisp-runtime` bundles two distinct categories (language-level primitives + backend-emitted intrinsics) under one BC.
- `cranelisp-backend/src/operators.rs:323–394` carries `(TraitName, Symbol, TypeName) → PrimitiveOp` maps — backend special-casing trait knowledge.
- `cranelisp-backend/src/compiler/literals.rs:327–332` carries the parallel `"+" → "cranelisp_op_add"` map for operator-as-value.
- `cranelisp_op_*` extern fns in `cranelisp-runtime/src/primitives/int.rs` duplicate the named primitives (`add-i64` etc.) as separately-named addressable forms.

Decision 43's resolution requires deleting these in coordinated fashion with the crate split, the stdlib trait-impl audit, and the BC §4 retirement.

## Proposed resolution

Multi-crate migration; sequenced as one wave per Decision 43's "Sequencing" section. Phasing per-crate to keep intermediate states green:

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

**Phase 3 — `/dev` (backend)**: Delete trait-knowledge maps:

1. Delete `cranelisp-backend/src/operators.rs:323–394` (`(TraitName, Symbol, TypeName) → PrimitiveOp` map).
2. Delete `cranelisp-backend/src/compiler/literals.rs:327–332` (`"+" → "cranelisp_op_add"` map).
3. Rename `cranelisp-backend/src/operators.rs` → `cranelisp-backend/src/primitives_inline.rs`. The surviving substitution table at line 38 (`"add-i64" => iadd`) is name-keyed; keep.
4. Update `cranelisp-backend/src/jit.rs` `IntrinsicSymbol` array: remove `cranelisp_op_*` entries; keep `int-to-string` etc. (legitimate intrinsic-backed primitive GOT slots).
5. Backend's `Cargo.toml` revises: depend on `cranelisp-intrinsics` (for emitted-symbol declarations) AND `cranelisp-primitives` (for symbol-table seeding); drop `cranelisp-runtime` dep.

**Phase 4 — `/dev` (stdlib, primitives)**: Delete duplicate addressable forms + audit trait impls:

1. Delete `cranelisp_op_add … cranelisp_op_ge` (10 extern fns) from `cranelisp-primitives/src/primitives/int.rs` (post-relocation).
2. Audit stdlib's `(impl Num Int)`, `(impl Display Int)`, `(impl Eq Int)`, `(impl Ord Int)`, `(impl Num Float)` impls. Each impl body should call the primitive directly: `(defn + [a b] (add-i64 a b))`. Refactor where the impl was relying on backend's collusion (i.e., the impl method was the empty marker that backend's `(Trait, method, Type) → primitive-name` map intercepted before the call ever reached the impl body).

**Phase 5 — `/dev` (arch + per-crate)**: Retire `cranelisp-runtime` crate; finalise BCs and facades.

1. Once all sources have moved, delete `crates/cranelisp-runtime/`. Workspace `Cargo.toml` removes the member.
2. `bounded-contexts.md` §4 retires; replaced by §4a (Primitives) + §4b (Intrinsics) per Decision 43.
3. `design/arch/facades/runtime.md` retires; replaced by `design/arch/facades/primitives.md` + `design/arch/facades/intrinsics.md` (full bodies authored from the Decision-43 categorisation).
4. `src/CLAUDE.md` "JIT Symbol Names" section updates: "Runtime infrastructure" row renames to "Intrinsic"; user-visible primitives row says "registered into the symbol table at `primitives/<name>`".
5. `cargo public-api` baselines for the new crates; the runtime baseline file deletes.

## Operational implication / Context

- **Multi-crate scope.** Touches `cranelisp-runtime` (retires), `cranelisp-primitives` (new), `cranelisp-intrinsics` (new), `cranelisp-backend` (deletions + rename), stdlib (audit), `crates/cranelisp-exe-bundle/` (linker dep updates), `src/` (Cargo deps + JIT-symbol-names doc), workspace `Cargo.toml`.
- **Coordinates with FIXME 0103** (trace/io_trace relocation). The IoObserver registration site is co-resident with the io trampoline; both FIXMEs can land independently if Phase 2 is sequenced as Option (a) above, or bundled if Option (b).
- **Coordinates with FIXME 0107** (PlatformFnDescriptor non-exhaustive — currently in S65 scope). No direct file overlap; can run in parallel.
- **NOT a blocker for S65 facade-adoption work.** S65 currently scopes the 7 cross-crate FIXMEs (0098, 0099, 0100, 0103, 0104, 0107, 0108) plus `cargo public-api` enforcement. This FIXME's implementation can run as S65 Wave 0 (delays the facade-adoption work; user-decided trade-off), as S66 (sequenced after S65 facade adoption stabilises), or as a dedicated multi-crate sprint of its own. `/sprint` decides at the next sprint-plan boundary.
- **Risk: stdlib trait-impl audit.** The Phase 4 audit may surface impls that relied on backend's collusion in non-obvious ways — operators that "just worked" because backend intercepted before the impl body ran. Where the impl body is empty, it must be filled with a direct primitive call. Where the impl body delegates back to the operator (`(defn + [a b] (+ a b))` — circular under the corrected model), the recursion breaks the moment the trait-knowledge map deletes; the audit must catch these before Phase 3 lands.
- **Test impact.** Tests that exercise operators-as-values (`(let [f +] (f 1 2))`) currently route through `cranelisp_op_add`; after Phase 4 deletes those duplicates, the path goes through the `+`-symbol-table-entry's GOT slot which holds the `(impl Num Int)` impl body which calls `(add-i64 a b)` which backend may inline. Net behaviour unchanged; intermediate code path different. Test suite should pass through the migration without test-side changes; if tests depend on the duplicated symbol, that's a test bug to surface.
