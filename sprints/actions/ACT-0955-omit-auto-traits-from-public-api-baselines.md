---
id: ACT-0955
title: Omit generated auto-trait impls from public-API baselines
status: deferred
priority: next-sprint
from: sprint
to: arch
sprint: 121
filed_at: 2026-09-05
refers_to:
  - design/arch/CLAUDE.md §Baseline-diff discipline
  - tests/public_api_relocations.rs
  - crates/cranelisp-platform/public-api.txt
---

## S122 disposition (user-approved 2026-09-30)

Under the [approved S122 disposition](../../tests/plan/s122-evidence-delta.md#final-disposition-proposal-2026-09-30):

- **Carried to S123 (K11, public-API baseline batch).** First deferral. It
  lands in one `arch` batch with ACT-0963 item 2 and ACT-0971; the batch's
  non-empty generated diff needs one user confirmation.
- Source on 2026-09-30: the guard in `tests/public_api_relocations.rs` still
  passes only `--omit auto-derived-impls`, and
  `crates/cranelisp-backend/src/cache/object.rs` still has
  `unsafe impl Send for CacheWritePacket`.

## Request

In the next sprint, add `--omit auto-trait-impls` to the repository's one
canonical `cargo public-api` invocation. Generated `core::marker` rows such as
`Freeze`, `Unpin`, `Send` and `Sync` dominate the baselines and review output;
explicit implementations such as `unsafe impl Send for PlatformFn` remain
visible with this option.

Treat this as one coordinated baseline-format migration, not as part of an
unrelated API change. First identify any auto-trait property that is a required
cross-crate contract and give it a direct source or test fence if omission
would otherwise hide it. Then update the canonical documentation and executing
guard together and regenerate every tracked library baseline once.

## Completion evidence

- The documented command and `tests/public_api_relocations.rs` use the same
  `--omit auto-trait-impls` policy.
- All seven tracked baselines are regenerated in one mechanical change and the
  user approves the resulting contraction before promotion.
- A planted ordinary public-API addition still fails the guard, while explicit
  `Send`/`Sync` implementations required by an ABI contract remain represented
  or receive an equivalent direct fence.
- No product behavior, language specification, cache schema or platform ABI is
  changed by the baseline-format migration.

## Coupled cleanup: compiler-checked cache packet transfer

S122 QA's historical-review intake E3 found an explicit `unsafe impl Send` for
`CacheWritePacket` in `crates/cranelisp-backend/src/cache/object.rs` although
all its fields already have auto-`Send` (inspected against the committed public
API baselines; removal has not yet been compiled). The explicit impl prevents
a future non-Send field from being rejected at the writer-thread handoff in
`src/cache_writer.rs`.

During this coordinated baseline change, have `dev` (backend) remove the
redundant impl and its comment, then verify that the writer handoff compiles
with derived `Send`. Include the explicit-to-auto `Send` row change in `arch`'s
user-approved baseline proposal and resulting diff. No behavioral test was
allocated: the compile-time bound is the relevant check. Original finding:
historical S22 I-1/S23 review, recoverable at Git checkpoint `07f46769`.
