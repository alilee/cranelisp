---
number: 0366
target: /typecheck
filed_by: /qa
filed_at: 2026-06-16
sprint_filed: 83
refers_to: spec/05-definitions.md §5.2.6, spec/08-modules.md §8.6.5, crates/cranelisp-typecheck/src/adt.rs (synthesise_one_accessor / synthesised_accessor_names), crates/cranelisp-typecheck/src/program.rs (deferred_accessor_collisions), tests/spec_05_definitions.rs::repl_cross_cluster_duplicate_field_accessor_is_ambiguous
status: open
---

# REPL cross-cluster duplicate-field accessor collision is missed — diverges from `--run`/`--link`

## Issue

The S83 W2 accessor ruling (spec §5.2.6 + §8.6.5, commits `843f17f` /
`1e1d0a3`) makes same-module duplicate field-name accessors **ambiguous**:
given `(deftype Box [:primitives/Int v])` and `(deftype Cup
[:primitives/Int v])` in the same module, both synthesise an accessor named
`v`, so the bare name `v` is **poisoned** — any bare use of it MUST be a
compile-time error (`ambiguous bare name 'v'`, listing `Box.v` / `Cup.v`).

This works correctly in `--run` / `--link`, where the whole program is one
compilation cluster (guarded green by
`tests/spec_05_definitions.rs::accessor_cross_type_duplicate_field_name`).

It does **NOT** work in the REPL. There, each input line is a separate
cluster. The duplicate-field poison classifier keys on the per-`CheckState`
`synthesised_accessor_names` set (`crates/cranelisp-typecheck/src/adt.rs`,
`synthesise_one_accessor` / `synthesised_accessor_names`). On the cluster
that defines `Cup`, that set does not contain `v` — the first accessor `v`
(from `Box`) was synthesised and committed in a PRIOR cluster, not in this
`CheckState`. The collision is therefore missed and the REPL falls through
to the still-live suppress-and-first-wins path
(`crates/cranelisp-typecheck/src/program.rs`,
`deferred_accessor_collisions`), which emits:

```
; warning: field accessor `v` for type `Cup` conflicts with a name already
  bound to `v`; the accessor is suppressed and the existing binding is kept
```

and then resolves `(v (Box 5))` to `:primitives/Int 5`.

Net: in the REPL, defining `Box` then `Cup` on separate lines and then
evaluating `(v (Box 5))` returns `5` with a warning, instead of the
spec-mandated ambiguity error. The spec gives the REPL no exemption from
§5.2.6 + §8.6.5 — this is a real REPL/`--run` divergence (the defect class
CLAUDE.md calls out).

Failing-not-ignored guard (the durable record + the trigger to fix):
`tests/spec_05_definitions.rs::repl_cross_cluster_duplicate_field_accessor_is_ambiguous`
— drives the REPL with three separate inputs (`Box`, `Cup`, then `(v (Box
5))`) and asserts the bare use is an `ambiguous bare name 'v'` error and is
NOT silently resolved to `5`. It is RED today; it flips green when the gap
below is closed.

## Proposed resolution

Re-derive the accessor collision from the **committed live symbol-table
entry** when synthesising an accessor in a later cluster — not solely from
the per-`CheckState` `synthesised_accessor_names` set. When synthesising
accessor `v` for `Cup`, probe the live (already-committed) bindings as well
as the in-cluster staging set; if a committed accessor `v` belongs to a
**different type** (`Box.v`), poison the bare name `v` (ambiguity) rather
than suppress-and-first-wins.

This is analogous to the staging+live union probe fix in commit `b612532`
for the non-accessor collision — extend the same union-probe pattern to the
accessor-synthesis path so that a bare accessor colliding with a committed
accessor of a different type is poisoned, in the REPL exactly as in `--run`.

Once poisoning fires across clusters, the still-live
`deferred_accessor_collisions` suppress-and-first-wins branch should no
longer be reached for the duplicate-field (different-type) case.

## Operational implication / Context

- **Severity: low.** REPL-only, and niche — it requires two product types
  with the SAME field name defined across SEPARATE REPL inputs. No effect on
  `--run` / `--link`, which already poison correctly.
- **But a genuine spec-conformance divergence** between modes: the REPL
  silently first-wins where `--run` errors, which violates the
  no-REPL-exemption principle for §5.2.6 + §8.6.5.
- The long-term escape named in the spec for legitimately using one of two
  colliding accessors is the deferred `Type.member` accessor-qualification
  (`Box.v` / `Cup.v` dotted syntax), tracked separately as FIXME 0365
  (`target: /spec`). That escape does not change the poisoning requirement
  here — bare `v` must still be ambiguous in all modes.
