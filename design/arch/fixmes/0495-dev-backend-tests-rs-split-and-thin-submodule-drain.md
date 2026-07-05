---
number: 0495
target: /dev
filed_by: /qa
filed_at: 2026-07-03
sprint_filed: 101
refers_to: crates/cranelisp-backend/src/tests.rs, sprints/METHOD.md §2.2 "Implementation-strategy unit scenarios", design/arch/fixmes/0494-arch-facade-unit-test-organization-convention.md, tests/plan/coverage-audit-s101.md §3.2
status: open
---

# Backend: split the flat crate-root `tests.rs` along submodule lines + drain the named thin strategy submodules

**Crate**: cranelisp-backend (`/dev` narrow).

## Issue

The S101 coverage audit (`tests/plan/coverage-audit-s101.md` §3.2) confirms the
backend as the priority unit-tier drain target:

1. **The named anti-pattern exhibit** (METHOD §2.2, FIXME 0494): a flat 5,861-line
   crate-root `tests.rs` holding 76 tests over 32,548 LOC of well-composed
   submodules — per-submodule coverage is unattributable by construction.
2. **~5,000 LOC of compiler strategy with zero dedicated per-submodule tests**:
   `compiler/rc_emission.rs` (788 LOC / 2 inline tests — the worst
   coverage-to-strategy ratio in the codebase), `compiler/control_flow/fn_as_value.rs`
   (960 / ~7 happy-only — the 0483/0474 crash-and-leak seam),
   `compiler/match_codegen.rs` (588 / 0), `compiler/control_flow/let_if.rs`
   (472 / 0 — branch RC), `compiler/control_flow/lambda.rs` (538 / 0),
   `compiler/control_flow/dependent_spark.rs` (433 / 0), `compiler/resolution.rs`
   (426 / 0), `compiler/context.rs` (275 / 0), `primitives_inline.rs`
   (612 / 11, all `_happy`-named).
3. **Strategy-matrix cells named by S101 defects and still untested at unit
   grain**: the runtime rc>1 COW copy branch (0474's leak branch — sibling
   rc-tests pin only the compile-time consuming-inc decision table); the
   per-instantiation wrapper matrix in `fn_as_value.rs` (0483's SIGBUS axis);
   GOT exhaustion/freeze/trap-patch (`got.rs` self-documents allocation as
   UNCHECKED; the W4 exhaustion guard has no direct unit pin).

## Proposed resolution

1. **Split `tests.rs`** by moving each attributable bucket next to the submodule
   it exercises (`foo/tests.rs` or `#[cfg(test)] mod tests` sibling), per METHOD
   §2.2 / 0494. Audit-provided bucket map: vec_codegen 20+, got 6–20,
   lib/module-assembly 6–20, resolution/apply 6–20, fn_as_value ~5, trap stub 3,
   fn_compiler 3, extern_call 2, lambda/launch 3, literals/match 2, jit ~3.
   Pure relocation first; no behaviour change.
2. **Drain the thin submodules** per the §2.2 taxonomy {complexity, edge,
   negative}, prioritized: rc_emission → fn_as_value (instantiation-count +
   rc-branch matrices) → got (exhaustion/freeze/trap-patch) → let_if branch RC →
   match_codegen shape matrix → resolution/primitives_inline curry arms.

## Progress — S102 CS-B3.0 (partial relocation; step 1 only)

**Relocated (green):** the fully self-contained `compile_trap_stub` trio
(`trap_stub_raises_provenance_message_and_returns_sentinel`,
`trap_stub_is_callable_at_nonzero_arity`, `trap_stub_raises_on_every_invocation`)
moved from the flat crate-root `src/tests.rs` into a `#[cfg(test)] mod
trap_stub_tests` beside `compile_trap_stub` in `src/lib.rs` (Principle 23). Pure
relocation, zero behaviour change. These depend only on `compile_trap_stub` + the
intrinsics panic slot, so no shared-harness plumbing was needed.

**Remainder (still in `src/tests.rs`, 73 tests):** the remaining buckets
(vec_codegen ~30, lib/module-assembly + got `decision_23_*` + `sprint56_*` +
`decision_36_*`, resolution/apply, fn_as_value value-use trio + curry,
extern_call, lambda/launch, literals/match, jit) all consume the ~600-line
shared harness at the top of `tests.rs` — `TestCheckResult` + `empty_check` +
`enrich_defn_from_side_maps` + the compile-and-run drivers +
`empty_tables`/`empty_aliases`/`make_def_entry_slot`/`vec_elem_for_test`/
`vec_len_for_test`/`run_vec_query_value_consumer`. **The gating sub-task is
extracting that harness into a crate-visible `#[cfg(test)] mod test_support`
(items → `pub(crate)`) that submodule test homes `use`.** That extraction is a
focused, higher-risk change-set of its own (it rewrites every test's helper
imports) and was deliberately NOT bundled with the golden-oracle-witness
change-set (B1-be) to keep the tree green and the empty-diff witness clean. It
should ride its own B3.0-continuation change-set before the B3.1 seam-drain
(step 2, which adds new scenario tests and needs the homes in place).

Status stays **open** — step-1 relocation is partially drained; step 2 (thin-
submodule scenario drain) is untouched (B3.1+ per `design/backend/
ownership-codegen.md` §13.2, not this wave).

## Progress — S102 (step 1 COMPLETE: harness extraction + full relocation, 2026-07-04)

**DONE — step 1 (the gating sub-task) is fully drained.** The ~600-line shared
harness was extracted into a crate-visible `#[cfg(test)] pub(crate) mod
test_support` (`crates/cranelisp-backend/src/test_support.rs`, items →
`pub(crate)`): `TestCheckResult` (+ fields), `empty_check`, `empty_tables`,
`empty_aliases`, `vec_len_for_test`, `enrich_defn_from_side_maps`,
`concretize_test_body`, `enrich_expr_from_side_maps`, `make_def_entry`,
`make_def_entry_slot`, `make_def_entry_inner`, `test_compile_and_run`,
`test_compile_program_and_run`, `option_type_tables`, the shared object-module
helpers (`make_object_module`, `table_with_def_and_slot`, `make_int_defn` — used
by both the module-assembly and dispatch buckets), and the vec-query value-use
kernel (`insert_inline_vec_query_entry`, `vec_elem_for_test`,
`run_vec_query_value_consumer`, `vec_int_lit`, `vec_query_value_consumer`).
Per-submodule test homes reach it via `use crate::test_support::*` (the module
re-exports the exact crate-root prelude the flat tests relied on).

All **73** remaining crate-root tests were relocated **verbatim** (bodies
unchanged; only the harness `use` path adjusted) into per-submodule homes:

| Home | Tests |
|---|---|
| `compiler/vec_codegen/tests.rs` | 25 (Vec-codegen) + `vec_get`/`vec_lit` locals |
| `module_assembly_tests.rs` (crate root, beside `compile_to_module`) | 24 (module-assembly + GOT-emission: `compile_to_module`/`decision_23_*`/`decision_36_*`/`sprint56_*`/multi-sig/mono) |
| `compiler/apply/dispatch_tests.rs` | 4 (trait-method + platform-effect dispatch) |
| `compiler/control_flow/fn_as_value/value_use_tests.rs` | 7 (fn-as-value + value-use trio + curry) |
| `compiler/extern_call.rs` (inline `mod tests`) | 2 |
| `compiler/control_flow/lambda.rs` (inline `mod tests`) | 2 |
| `compiler/control_flow/launch.rs` (inline `mod tests`) | 1 |
| `compiler/literals.rs` (inline `mod tests`) | 4 |
| `compiler/match_codegen.rs` (inline `mod tests`) | 2 |
| `jit/disasm_tests.rs` | 2 |

`src/tests.rs` is retired (`git rm`); the crate-root `mod tests;` declaration is
removed from `lib.rs`. Pure relocation — count invariant held exactly (`cargo
nextest`: 3804 run / 3793 passed / 11 failed / 1 skipped, byte-identical to the
pre-relocation baseline; the 11 REDs are the pre-existing e2e guards, none in
this crate). `cargo check --tests` clean, zero warnings; golden-CLIF diff empty.

**Remainder = step 2 only** (the thin-submodule scenario drain per the §"Proposed
resolution" taxonomy: rc_emission → fn_as_value → got → let_if → match_codegen →
resolution/primitives_inline). Step 2 **rides Wave 11** with the mechanism
change-sets it co-lands with (0474/0483 `fn_as_value`/`rc_emission` seam per
`design/backend/ownership-codegen.md` §13.2) — the fn_as_value/rc_emission
scenario cells co-land with the mechanism that flips the 0474/0483 guards, so
adding them now would be premature (they must land against the fixed mechanism,
not HEAD). Status stays **open**; the per-submodule homes are now in place for
step 2 to drop scenarios into.

## Progress — S102 Wave 11 B3.1a (step 2 PARTIAL: vec_codegen COW-polarity cells; 2026-07-04)

**Step-2 drain SHRINKS by the `vec_codegen` COW-core cells.** The §13.5
branch × polarity matrix for the `SourceOwnership` consumed-source contract
(design/backend/ownership-codegen.md §13.3 Ruling 2) landed as
`compiler/vec_codegen/cow_polarity_tests.rs` (5 cells): copy-branch release
present iff `Owned` (vec-set + vec-push), Borrowed releases nothing on any
branch (the negative/static-site cells), and the owned−borrowed rc-dec delta is
exactly one release (the contract, not a spot dec — Principle 18). These assert
the SPECIFIC copy-branch rc-emission (`atomic_rmw.i64 sub` count) at the core
seam, co-landing with the mechanism that flips the vec-set-as-value COW leak.

The `fn_as_value` / `rc_emission` seam-drain cells for the OTHER Wave-11 fixes
are covered at their landing grain as follows (the AST-scaffolding cost of an
isolated in-process unit cell for each is disproportionate, so they are pinned
where the seam is observable): **item 25** curry-glue idempotency + the
**auto-curry capture double-inc** cure → the `vec_cow_value_use_leak` curry +
`curried_partial_and_static_call…` e2e guards (flipped GREEN); the **TCO
scope-cleanup flush** (`flush_let_scopes_before_tail_jump`) → the golden-CLIF
re-baseline (f2/f3/f4 — the dead-block-after-jump → live-before-jump structural
delta) + the static-site `vec_cow_value_use_leak` e2e guard (flipped GREEN).

**Step-2 remainder still OPEN:** got (exhaustion/freeze/trap-patch), let_if
branch RC, match_codegen shape matrix, resolution/primitives_inline curry arms,
and the deeper rc_emission cells REMAIN. Status stays **open** — the drain
shrank by rc_emission (COW polarity) + fn_as_value (curry/TCO covered at
e2e/golden grain), not the whole taxonomy.

## Progress — S102 Wave 11b B3.2 (step 2 PARTIAL: apply moded-arg matrix; 2026-07-04)

**Step-2 drain SHRINKS by the `apply` caller-side borrow-elision cells.** The
B3.2 borrow-elision core (`design/backend/ownership-codegen.md` §3.1–§3.5) landed
its §3.1 per-argument RC decision as the pure `moded_arg_rc(category, mode,
owned_binding)` and pinned the FULL `{heap category} × {mode} × {owned-binding vs
temporary}` matrix (3×3×2, all 18 cells + the negative/scalar, byte-identical-off,
elision, post-call-dec, and Copy classes) in
`compiler/apply/moded_arg_rc_tests.rs` (6 tests). This is the §13.5 apply-row
scenario space; the temp+`Borrowed` post-call-dec cell is the one whose absence
leaked a fn-as-value closure in isolation testing (caught by the RC-balance
oracle, now a pinned matrix cell + design as-built note). The §3.2 callee
`borrowed_vars`, §3.4 adaptation, and §3.5 R2 wrapper are covered at e2e/golden
grain (the 9-entry ON re-baseline + the a–e class repros; §3 as-built). Status
stays **open** — the drain shrank by the `apply` caller matrix, not the whole
taxonomy.

## Progress — S102 Wave 11 B3.3 (step 2 PARTIAL: rc_emission/heap non-atomic RC cells; 2026-07-05)

**Step-2 drain SHRINKS by the `heap.rs` + `rc_emission.rs` RC-atomicity cells.**
B3.3 (per-site non-atomic RC for `Confined` cells,
`design/backend/ownership-codegen.md` §5) landed its §13.5 matrix at seam grain:
`heap::tests::rc_atomicity_b33_tests` (6 cells) pins the five gated helpers
(`emit_rc_inc[_guarded]`, `emit_rc_dec[_guarded]`, `emit_vec_rc_dec_with_drop`)
× `RcAtomicity` → {non-atomic arm, atomic arm verbatim}, CLIF-text asserted,
INCLUDING the §2.2 negative/else-arm identity class (the plain helper ==
`_atomicity(Atomic)` byte-for-byte) and the h2 non-atomic-op-share counter.
`fn_compiler::b33_node_confined_tests` (3 cells) pins the `node_confined`
classifier — the fact-bearing (StringLit/Lambda/Apply/VecLit/ConstrADT) vs
non-fact-bearing variant matrix + the `Some(true)⇒NonAtomic` derivation. The
through-binding confinement carrier (`confined_bindings` population + the
materialization-inc/consuming-arg/vec-scope-dec wiring) is covered at
golden/e2e grain (the 6-entry ON re-baseline: 03/04/05/08/f1/f2, each a
confined materialization inc flipped `atomic_rmw add → load/iadd/store`; the
anti-race SAFETY that a spark-crossing board keeps atomic RC). Status stays
**open** — the drain shrank by the rc_emission/heap RC-atomicity cells, not the
whole taxonomy (got exhaustion/freeze, let_if branch RC, match_codegen shape
matrix, resolution/primitives_inline curry arms REMAIN).

## Operational implication / Context

Sequencing: rides increment I's first backend change-sets — increment I lands on
exactly these seams (fn_as_value/COW rework per backend §12.7, 0476 DefKind cure),
so the drain is the same-wave test half, not a separate sprint. The 22 intentional
REDs (0474/0483 guards among them) flip green against this work; the unit scenarios
prevent the *next* adjacent cell from escaping.
