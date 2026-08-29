---
number: 0945
target: /testing
filed_by: /sprint
filed_at: 2026-08-29
sprint_filed: 119
refers_to: tests/facade_compliance.rs — checks the committed
  crates/{crate}/public-api.txt baselines; neither it nor tests/CLAUDE.md records
  the cargo-public-api version the baselines were generated under
status: open
---

# Record the cargo-public-api version the public-api.txt baselines require

## Issue

`tests/facade_compliance.rs` checks the committed `crates/{crate}/public-api.txt`
baselines, and those baselines are **version-sensitive in a way nothing in the repo
records**.

They were regenerated under **cargo-public-api 0.52** (commit 4109c3e, 2026-06-13). 0.52
stopped rendering function parameter names — upstream's rationale being that parameter
renames are not API changes and should not show as diffs. Regenerating with **0.51 or
older** produces an inverse **110+/110-** churn against the committed baselines, because
those versions still emit parameter names.

This is a cross-environment constraint, not a machine-local one: this workstation, any
other the project is developed on, and CI must all be on >= 0.52 to stay in parity. A
`grep -rn "public-api"` over `CLAUDE.md`, `tests/CLAUDE.md` and `crates/*/CLAUDE.md`
turns up the regeneration command in places but no version floor anywhere.

The failure mode is quiet and expensive: a contributor on an older toolchain regenerates
a baseline, sees a 110-line diff that looks like a real API change, and either commits
churn or spends a sprint slot chasing a phantom relocation.

Current state of this machine: cargo-public-api 0.52.0, so the constraint is satisfied
in practice today — this is about recording it before it is violated.

## Proposed resolution

`/testing` to add a short subsection to `tests/CLAUDE.md` near the `--link`/platform
prerequisites material, stating:

- The baselines are generated under cargo-public-api **>= 0.52**; do not regenerate with
  0.51 or older.
- The regeneration command:
  `cargo +nightly public-api -s --omit auto-derived-impls > crates/{crate}/public-api.txt`
- Installing needs the `pkg-config` and `libssl-dev` apt packages (transitive
  `openssl-sys` dependency).
- Every environment running the check — every workstation and CI — must match, or the
  diff churns.

If `/testing` judges the version floor to belong in a per-crate `crates/*/CLAUDE.md`
instead, one home is enough; `tests/CLAUDE.md` is preferred because the check itself is a
test-tier concern. A stronger option, if cheap: have `facade_compliance.rs` assert the
tool version and fail with this explanation, which upgrades the record from asserted to
measured per root `CLAUDE.md` §Assurance.
