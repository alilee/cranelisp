# S122 selected backend closure — retired record

Owner: `design` (backend). Status: **retired.** Every S122 backend correction
landed at the S122 close (2026-10-02). The full delivery record, with its
mechanism readings, options and run identifiers, is in Git history at
`3bdf398e`. This file keeps only the section anchors that source, tests and
other designs still cite, each pointing at the rule's current home. Delete it
when those citations move.

## 2. Canonical result-root use — 0898

`compile_to_module` requests each body's result-root drop glue through
`ConcreteType::result_root()`; the backend adds no second normalisation
([transitive drop glue](transitive-drop-glue.md)).

## 3. Shared Vec nullary-tag guard — 0906

Every guarded increment, the Vec copies included, routes through
`heap::emit_rc_inc_guarded`, which owns the one tag-versus-pointer decision
([non-concrete release](non-concrete-release-contract.md) §3.6).

### 5.1 0747 — retire the manufactured consolidation

Moot: the three finders it compared are deleted, and binder identity is the
ownership plan's ([uniform counting](uniform-counting.md) §3).

## 7. Delivered Q4 macro alias correction

A macro-clause executable takes its parameter types from the selected arm's
scheme, never a relookup by generated label
([compile-to-module](compile-to-module.md) §4). The return-protect half of the
correction is deleted with return protection
([uniform counting](uniform-counting.md) §5).

## 8. IOR-5 — an IO-combinator result is fresh

Moot: every result is owned, so no freshness rule exists
([uniform counting](uniform-counting.md) §4). `apply::IoCombinator` survives
as the spark exclusion and the interceptor classifier.

## 9. ACT-1037 — `vec-set` index guard

The rule is [backend.md §7](backend.md#7-runtime-failure), "One Vec index
guard". `qa`'s
[closure record](../../tests/plan/s122-evidence-delta.md#act-1037-vec-set-bounds-check-closed)
holds the evidence, including the `--link` limit.

### 9.2 Correction

The `vec-set` core is the only lowering of `vec-set` and opens with the shared
guard (backend.md §7). One routed item remains open: `vec-set-copy`'s caller
precondition, `0 <= idx < len`, is unstated in the helper's rustdoc and in the
catalog convention row. Those carriers belong to `dev`(intrinsics) and `arch`.

## 10. ACT-1040 — panic propagation (proposal)

**Withdrawn.** The user ruled on 2026-11-15 that a runtime panic ends the
process in every mode ([backend.md §7](backend.md#7-runtime-failure)); none of
the propagation options was built.

### 10.2 The fact every option rests on

Pre-W1 code; in Git history at `3bdf398e`.

### 10.3 Options

The options (A0 sentinel propagation, A complete propagation, C non-local exit,
D native unwinding) and the pre-W1 mechanism reading they rested on are in Git
history at `3bdf398e`. ACT-1040 and ACT-1042 carry their own reproductions.
