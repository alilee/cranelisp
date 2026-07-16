---
number: 0621
target: /sprint
filed_by: /arch
filed_at: 2026-07-16
sprint_filed: 110
status: open
refers_to: crates/cranelisp-typecheck/src/checker.rs::record_reference_target
  (`user_fn_refs.insert(span, resolved.fq)` — the `callees` feed);
  cranelisp_types::Resolved::storage_fq (the correct identity, landed S110
  W1.1); design/arch/backend-keyed-consumer.md §1.1.2 "Residual".
---

# `Def.callees` records the reference-identity `Resolved.fq` — an ALIAS for renamed imports and bare member references — starving keyed edge consumers

## One line

The `callees` feed (`user_fn_refs`, recorded beside the `resolved_targets`
carrier in `record_reference_target`) still persists `Resolved.fq` — the
WRITTEN-spelling identity. For a renamed import (`[(foo bar)]` → edge
`{m, bar}`, entry stored at `{m, foo}`) or a bare accessor reference (edge
`{m, v}`, entry at `{m, Box.v}` — accessors are `UserFn` `Def`s, so they DO
record) the persisted edge names a key that fetches nothing.

## Why it was deliberately left out of the 0620 fix

The S110 W1.1 ruling (`backend-keyed-consumer.md` §1.1.2) flipped only the
`resolved_targets` carrier onto `storage_fq()`. `callees` is persisted
`.meta.json`; changing what it records is a MEANING change requiring a
`CACHE_SCHEMA_VERSION` bump, and the 0620 fix was pinned value-only inside
the schema-19 window. Two feeds, one resolution, two identities — documented
divergence, not drift.

## Impact today (low) and tomorrow (real)

- `save.rs::dependency_sort`: an alias edge matches no local entry → treated
  as external; emission order falls back (Kahn's + alphabetical) — benign.
- The S101 session-transaction reverse index (`design/int/
  session-transaction.md`): edges keyed by an alias FQ silently miss the
  redefinition's affected-set closure — the 0472 starvation class. The
  machinery is not yet live in the dev session; it MUST NOT go live while
  `callees` can carry alias edges.

## Requested action

Schedule (next schema-bump window, or as a prerequisite of the
session-transaction machinery going live, whichever first): `/dev`
(typecheck) flips the `user_fn_refs` insert to `resolved.storage_fq()`,
bumps `CACHE_SCHEMA_VERSION` in the same change-set, and pins a
renamed-import + bare-accessor `callees` unit each (`program::tests::
callees_*` family). Cross-check `extract_call_graph_edges`' ResolvedCall
channel is already storage-keyed (it is, post-W0.1b — verify at landing).
