---
number: 0290
target: /int
filed_by: /dev
filed_at: 2026-06-07
sprint_filed: 76
target_sprint: 77
refers_to: src/bootstrap.rs, design/arch/test-discovery.md §6 "Publishing catch-runtime-error", crates/cranelisp-intrinsics/src/panic.rs, crates/cranelisp-intrinsics/src/catalog.rs
status: open
---

# int: seed the `primitives/catch-runtime-error` language entry

## Issue

FIXME 0270 (S76 W4a /dev intrinsics) landed the `catch-runtime-error` combinator
in `cranelisp-intrinsics`:

- `crates/cranelisp-intrinsics/src/panic.rs` —
  `#[export_name = "catch-runtime-error"] pub extern "C" fn catch_runtime_error(thunk_closure: i64) -> i64`
  (invokes the thunk, reads/clears the runtime-error slot, marshals heap
  `(Ok result)` / `(Err message)`).
- `crates/cranelisp-intrinsics/src/catalog.rs` — registered in
  `intrinsics_table()` (entry 28), so the JIT symbol resolves in ALL modes
  (JIT setup, cache-hit, `--link`).

What is NOT yet done — and is int's, per `test-discovery.md` §6's last bullet
("Seed the `primitives` entry in `src/bootstrap.rs`") — is the **language-level
symbol binding**. Until int seeds it, user code cannot import or call
`catch-runtime-error`: the typechecker has no `primitives/catch-runtime-error`
entry, so `(import [primitives [catch-runtime-error]])` / a bare
`(catch-runtime-error …)` call does not resolve at the language level even though
the JIT symbol exists.

## Proposed resolution

In `src/bootstrap.rs` (`mount_synthetic_modules` / the `primitives` seeding
path), add a `primitives` `ModuleEntry::Def` keyed `catch-runtime-error` with:

- **scheme** `forall a. (Fn [(Fn [] a)] (Result a String))` — a **plain forall
  scheme with empty `constraints`**, modelled exactly on `register_bind_primitive`
  (`bootstrap.rs` `bind` seeding): one fresh quantified var `a`, no trait bounds,
  so the constrained-fn monomorphisation machinery is NOT engaged. One runtime
  body serves every `a` (uniform i64 ABI).
- **kind** `DefKind::Primitive`.

The JIT name = ABI name = `catch-runtime-error` (already the
`intrinsics_table()` entry name and the export name) — backend lowers the call as
`Linkage::Import` against the key, resolved from the intrinsics archive. No new
backend codegen.

Note: `Result` must be among the primitives bootstrap ADT seeds (per
`test-discovery.md` ruling 1 — "`Pair` and `Result` join the primitives bootstrap
seeds"). Confirm `Result` (Ok=0 / Err=1, declaration order — the combinator's
marshalling assumes this tag order) is seeded before this entry; seed it if not.

## Operational implication / Context

Once seeded, the §5 acceptance becomes e2e-testable:
`(catch-runtime-error (fn [] (/ 1 0)))` → `(Err …)`; a passing thunk → `(Ok …)`;
works in ALL modes incl. `--link` (self-contained intrinsic, no live session).
The intrinsics-side combinator + ferry + guard-cleanup are already landed and
unit-tested (FIXME 0270, deleted). This is the remaining language-binding seam,
which is irreducibly an int concern (bootstrap owns the synthetic `primitives`
table).
