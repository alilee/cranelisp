---
number: 0629
target: /qa
filed_by: /examples
filed_at: 2026-07-16
sprint_filed: 110
refers_to: tests/examples.rs (expected_exits table) + examples/36-multi-arity.cl
status: open
---

# Reconcile tests/examples.rs — new example 36-multi-arity.cl => 8

## Context

S110 Phase 6b (`/examples`) added a new learning-sequence example,
`examples/36-multi-arity.cl`, teaching multi-signature `defn` dispatch
(spec §5.1.2) — the language capability unblocked by the S110 C-4 fix
(`303df28a`): an entry `main` whose body calls an overloaded fn now
dispatches and returns cleanly, mode-uniform (`--run` == `--link`).

The e2e guard `tests/examples.rs` pins the on-disk example file set against an
`expected_exits()` table; adding a file without its row breaks that guard.
`tests/` is owned by `/testing`/`/qa`, so `/examples` cannot edit the table —
hence this FIXME.

## The ask

Add one row to `tests/examples.rs`'s `expected_exits()` (or equivalent):

    "36-multi-arity.cl" => 8

Verified by `/examples` on 2026-07-16 with the freshly-built
`target/debug/cranelisp`:

- `--run examples/36-multi-arity.cl` => exit **8**, stable over 5 consecutive
  invocations.
- `--link examples/36-multi-arity.cl -o … && ./…` => exit **8** (mode-uniform).

Eight `pass=1` sub-tests (arity dispatch ×3, type dispatch ×3, default-overload
×2); a drop below 8 signals a regression. No platform DLL / env var / symlink
is involved — the example uses only `primitives` (via the examples prelude,
plus an explicit `(import [primitives [Vec]])`) and a local `deftype Blob`.

## Notes

- Positioned after `35-ctor-disambiguation.cl`. The full replay set is now 35
  top-level `.cl` files (01–36, minus the `16-modules/` directory at 47) — the
  S110 Phase-6b `/examples` report and `examples/plan-examples.md` §2 carry the
  updated table.
