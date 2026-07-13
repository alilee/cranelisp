---
number: 0582
target: /design
filed_by: /arch
filed_at: 2026-07-13
sprint_filed: 109
refers_to: design/typecheck/dotted-ctor-registration.md §6 (blast-radius table)
  + §3 (resolver notes); corrected model in
  design/arch/dotted-ctor-canonical-keys.md §§1–6 (the W1.1a COORDINATE
  re-ruling, user-ruled P5); empirical basis = /arch re-application of the
  preserved W1.1a patch (73 regressions vs the S109 baseline, classes pinned).
status: open
---

# `dotted-ctor-registration.md` §6 blast-radius table is empirically wrong — correct to the coordinate model

## Issue

The §6 table scoped the blast-radius audit to TYPECHECK consumers of bare
ctor keys and marked the int/backend rows "unaffected/covered-by-
construction". The W1.1a landing measured 73 regressions. Rows that need
correction (mechanisms verified live; details + fixes in
`design/arch/dotted-ctor-canonical-keys.md` §3):

1. **"Tag dispatch / ConstrADT codegen — Unaffected" is WRONG.** Backend
   `CompileContext::lookup_constructor` (context.rs:146) follows import
   chains exactly ONE hop and its global fallback probes bare keys. Two
   classes: pattern-position `unknown constructor` (the root of the entire
   prelude/e2e cascade, via `collections.list.test`), and the SILENT
   wrong-value class — a cross-module bare nullary ctor value misses the
   tag path and compiles as a fn-value closure (CLIF-verified) → runtime
   "match failed". Fix = collapse onto `resolve_driven` (one backend
   resolver) + canonical-aware probes.
2. **Missing row: int value display.** `display.rs::ctor_field_types`
   (:533) raw-probes the bare ctor key for the scheme → alias → fields
   dropped from every data-ctor value render.
3. **Missing row: int member-glob import.** `imports.rs::collect_member_glob`
   scans `public_symbols()` for `Def{Constructor}` — collects canonical
   (dotted) names only; bare aliases are `Import` edges and are skipped, so
   a member-glob importer loses bare ctor references.
4. **Missing row: SEEDED constructor writers.** `src/bootstrap.rs::
   register_synth_adt` (+ the hand-appended `IO.Bind`) and typecheck's own
   `builtins.rs` fixture seeds keep bare keys → a seeded/user keying split.
   User-ruled: keying is UNIFORM (all writers mint canonical + alias); the
   design must state the writer inventory, not only adt.rs.
5. **§3's staging note should point at the primitive.** The
   `resolve_intra_module_alias_staging` fallback patches around
   `chain_follow_committed`'s false premise (same-module member aliases hop
   within the CURRENT module, which may be staged). Arch-ruled: the
   types-owned walk takes same-module Import hops through the caller's
   first-hop VIEW; the typecheck-side fallback is not the durable shape.
   This also owns the latent same-cluster `--run` field-accessor defect.

## Proposed resolution

`/design` (typecheck, narrow) revises §6 into the cross-crate table matching
`dotted-ctor-canonical-keys.md` §3 (or cites it as the authority and keeps §6
typecheck-scoped with an explicit pointer), adds the writer-inventory
paragraph (§1 of the arch note), and records the audit lesson: **a
symbol-table keying change's blast radius is every crate's raw `table.get`
probe, not the owning crate's** — the §6 audit method (grep typecheck) was
the failure, not the individual rows. Delete this FIXME when landed.
