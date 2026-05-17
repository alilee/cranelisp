# Public-API baseline regeneration discipline

Owned by `/qa`. Codified in Sprint 67 Wave 0 to close edge settlement.
See `design/arch/CLAUDE.md §"Baseline-diff discipline"` for the
parallel architectural statement.

## What's baselined

One `public-api.txt` per per-crate edge, committed at:

```
crates/cranelisp-types/public-api.txt
crates/cranelisp-frontend/public-api.txt
crates/cranelisp-typecheck/public-api.txt
crates/cranelisp-backend/public-api.txt
crates/cranelisp-primitives/public-api.txt
crates/cranelisp-intrinsics/public-api.txt
crates/cranelisp-platform/public-api.txt
```

The `int` binary has no `public-api.txt` (binary crate; its surface
is the cranelisp exe CLI + REPL, governed by `tests/repl_*.rs` and
the integration tests in `tests/facade_*.rs`).

## When to regenerate

Any change that touches a crate's public Rust surface — `pub` items,
visibility changes, signature drift, type re-exports, module
restructure — requires the baseline to be regenerated in the **same
change-set** as the source change. Reviewers (`/review`, the user)
read the baseline diff alongside the source diff to assess whether
the change is a legitimate edge evolution or accidental surface
leakage.

This is the "two-update discipline" codified in
`design/arch/CLAUDE.md §"Baseline-diff discipline"`:

1. Regenerate `crates/{crate}/public-api.txt`.
2. Update the matching `design/arch/facades/{crate}.md` (or
   `facades/backend-cache.md` for the cache submodule) to name +
   disposition each added/changed/removed item.
3. Commit both alongside the source change.

Skipping (1) breaks the next baseline-diff check at PR time. Skipping
(2) breaks the facade-compliance test (`tests/facade_compliance.rs`).

## How to regenerate

```bash
# Install once per machine.
rustup toolchain install nightly
cargo +nightly install cargo-public-api

# Regenerate one crate's baseline.
cargo +nightly public-api --simplified \
    --manifest-path crates/cranelisp-backend/Cargo.toml \
  > crates/cranelisp-backend/public-api.txt

# Or regenerate every crate's baseline (loop).
for c in types frontend typecheck backend primitives intrinsics platform; do
  cargo +nightly public-api --simplified \
      --manifest-path "crates/cranelisp-$c/Cargo.toml" \
    > "crates/cranelisp-$c/public-api.txt"
done
```

The `--simplified` flag matches the format the existing tooling
expects (`tests/public_api_relocations.rs` uses the same flag when
diffing against committed baselines).

## Skill responsibility split

Per `tests/CLAUDE.md §"Public-API enforcement"` and S67 Phase 3 plan:

- `/dev` (per crate) regenerates the baseline as part of the
  implementing change-set.
- `/design` (per crate) updates the facade to match.
- `/review` confirms both updates are present in the same diff at PR
  time and the change is intentional.
- `/qa` (this file) owns the discipline statement and the failing
  compliance tests that enforce it.

## Drift-resolution flow

Intentional facade-shape change — author updates the facade `.md`
first, regenerates the baseline, commits both atomically. Reviewers
read the facade diff to understand the intent.

Unintentional drift — fix the source to match the facade; baseline
does NOT regenerate. Reviewers reject any baseline diff that doesn't
have a matching facade-diff explanation.

When in doubt, look at the facade first: it is the authoritative
statement of as-designed surface.

## Enforcement tests

- `tests/public_api_relocations.rs` — structural diff between the
  committed baseline and the current `cargo +nightly public-api`
  output. Fails on any drift (added or removed items, signature
  changes). Sprint 66 origin.
- `tests/facade_compliance.rs` — substring check that every pub-api
  item appears in the corresponding facade document. Fails on
  orphans. Sprint 67 origin.
- `tests/facade_pif_rows.rs` — per-row failing tests for substantive
  PIF rows in the S67 disposition table. Each test names the row +
  owning /dev wave. Fails today; flips green as /dev resolves.

These tests collectively form the "frozen contract" at every crate
edge that S67 establishes.
