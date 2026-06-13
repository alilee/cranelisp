---
number: 0338
target: /qa
filed_by: /dev
filed_at: 2026-06-13
sprint_filed: 81
refers_to: tests/platform_errors.rs::platform_abi_version_mismatch_e2e (assertion at ~line 300), design/arch/fixmes/0337-arch-dispatch-funnel-fault-catch-must-be-dll-local.md (the ABI 4→5 bump that this test must track)
status: open
---

# `platform_abi_version_mismatch_e2e` hard-codes the host ABI version `4` — must track the 0337 Option-A bump to `5`

## Issue

The FIXME 0337 Option-A implementation (DLL-local fault catch + `EffectOutcome`
cross-ABI signal) bumped `cranelisp_platform::ABI_VERSION` from **4 → 5** (the
`call_effect_thunk` force-return contract changed). The host now correctly
reports its required version as `5` when refusing a stale DLL.

The e2e `tests/platform_errors.rs::platform_abi_version_mismatch_e2e` asserts
the refusal message names **both** the DLL's stale `found` version (`2`, baked
into the `shapes-badabi` fixture) **and** the host's `expected` version, which
it hard-codes as `"4"`:

```rust
assert!(
    out.stderr.contains("2") && out.stderr.contains("4"),
    "ABI-version-mismatch error MUST report BOTH the DLL's stale version (2) \
     and the runtime's required version (4) ...",
    out.stderr
);
```

With the host now at ABI 5, the actual (correct) stderr reads:

```
DLL .../libcranelisp_shapes_badabi.so ABI version 2 does not match expected 5
```

so `out.stderr.contains("4")` fails. The behaviour is CORRECT — the test's
expectation is stale. This is the only failing test in the canonical suite
after the 0337 fix (1276 passed / 1 failed / 1 skipped; the 1 skip is the still-
ignored `boom` e2e retired at the 0337 step-3 /qa action).

The accompanying comment block (~lines 283–292) also narrates "`expected` = 4 as
of Sprint 81 / FIXME 0327 — the IO_TAG_EFFECT node-widen bumped the host ABI
3 → 4" and must update to name the Option-A 4 → 5 bump.

`/dev` cannot edit `tests/` (owned by `/qa`, per `tests/CLAUDE.md` two-tier
rule + the `/dev` boundary), so this is filed rather than fixed in-change-set.

## Proposed resolution

Update the assertion's expected-version token from `"4"` to `"5"` (and the
comment narrative from "3 → 4" to "4 → 5, Option A"). The `shapes-badabi`
fixture's stale `found = 2` is unchanged (2 ≠ 5 still holds). Substring
matching on `"5"` keeps the test mode-equivalent and toolchain-robust.

This is naturally bundled with the 0337 step-3 /qa action (un-ignoring
`platform_dispatch_error_carries_fn_name`) — both are the e2e-layer follow-up to
the same Option-A change-set.

## Operational implication / Context

The `cranelisp-platform` source + crate-local tests (`abi_version_is_5`,
`sprint71_abi_version_baseline_co_regen`, `macro_exports_got_in_manifest_order`)
and the `cranelisp-intrinsics` unit tests are all green at ABI 5; the platform
`public-api.txt` baseline is regenerated. Only this one workspace-`tests/` e2e
carries the stale literal. Until /qa updates it, the canonical `cargo nextest
run` shows 1276/1/1 instead of the expected 1277/0/1.
