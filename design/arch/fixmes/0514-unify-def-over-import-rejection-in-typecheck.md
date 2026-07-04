---
number: 0514
target: /dev
filed_by: /arch
filed_at: 2026-07-04
sprint_filed: 102
refers_to: src/process_form.rs §process_cluster_once (L172), src/worker.rs §commit_staging_to_live (L488-517), src/imports.rs §insert_detecting_ambiguity (L538-561), crates/cranelisp-typecheck/src/form.rs §check_forms (Pass-1 register loop, L249-254), spec/08-modules.md §8.6.4
status: open
---

# Move the §8.6.4 definition-over-(import|export) rejection to the shared typecheck seam (retire the mode-gated int-side gates)

## Issue

The §8.6.4 rejection (a `defn`/`deftype`/`deftrait`/`defmacro` whose name is
already in scope via `import` OR `export` is ALWAYS a compile-time error) is
implemented in `int` as **two mode-gated seams**, both switched by the single
`additive` bool at `process_form.rs:172` (`strategy == ModuleStrategy::Additive`):

1. **def-over-import** — a pre-scan in `worker::commit_staging_to_live`
   (`reject_def_over_import`, worker.rs:504-517);
2. **import/export-over-local-def** (symmetric) — in
   `imports::insert_detecting_ambiguity` (`reject_over_local_def`,
   imports.rs:550-558), threaded via `install_imports_gated`/`install_exports_gated`.

Because both gates are `false` on the whole-module `Replace` path, **batch
`--run`/`--link` does not reject** — the pre-0484 def-wins behaviour survives.
Only the incremental REPL (`Additive`) path rejects. This is a mode divergence
on a point of language semantics and **violates the frozen spec** — §8.6.4
(S102) states the error "does not depend on textual order … on import shape
(specific, renamed, member, glob, or glob re-export), or on visibility (private
import or public export)." The user (sole arbiter) has ruled: one shared code
path, both modes get the identical error.

Why it cannot be fixed by simply un-gating the two existing seams: the symmetric
Pass-0 gate (`insert_detecting_ambiguity`) runs BEFORE the module's own defs are
registered. In `Replace` the live table has no module-local defs at Pass-0 (they
stage during `check_forms`), so an incoming import has nothing to collide with
there — the symmetric direction is structurally undetectable at Pass-0 for batch.
The two directions must collapse to ONE seam where staged defs and installed
imports are both visible.

## Proposed resolution

Move the unified check into typecheck's **`check_forms` Pass-1 registration
seam** (`crates/cranelisp-typecheck/src/form.rs`, the `CheckPass::Register`
loop, L249-254 — concretely at the `register_defn_signature`/type-def
registration point in `program.rs`/`checker.rs` that inserts the new
`ModuleEntry::Def`/`TypeDef` into staging). Both modes traverse `check_forms`;
in cluster mode its staging-first **union `View`** already exposes the live
`ModuleEntry::Import` entries that int's Pass-0 installed (form.rs L37-43). So at
the moment a Def is registered, its name can be tested against a pre-existing
explicit `Import` entry (private or public) in the union view.

One check covers everything:

- **Both directions collapse.** "A staged Def whose name is bound by an explicit
  `Import` entry" is the same predicate whether the import or the def was written
  first — order-independent by construction (all Pass-0 imports precede
  `check_forms`).
- **Export-brought is automatic** (§8.4.0). Exports are `ModuleEntry::Import`
  with `Public` visibility; keying on the variant (not visibility) covers both.
- **Glob/specific-uniform** — reads the installed entry, never the import shape.
- **Redundant `(import [m [X]]) (export [m [X]])` still dedups** — both are
  `Import` edges to the same terminal; they never reach the Def-vs-Import check.
- **Prelude names stay shadowable** — they are an OUTER scope, never `Import`
  entries in the inner table.
- **Cluster atomicity preserves the byte-identical property** the commit-gate
  pre-scan gave: an `Err` from `check_forms` drops staging, live untouched.

Emit a `CheckError::TypeError` reproducing `imports::def_over_binding_error`'s
message (name the source module + `module/name` FQ remedy; the union view
carries `Import { source, visibility }` so both are readable). No new
`cranelisp-types` shape needed.

Disposition of the `e1fe4a8` commit-gate implementation:

- **Delete** the `reject_def_over_import` param + pre-scan
  (worker.rs:436/495-517) and its plumbing up through
  `process_cluster_with_staging`/`process_form.rs` finalize call.
- **Delete** the `reject_over_local_def` param + branch (imports.rs:550-558) and
  the `install_imports_gated`/`install_exports_gated` reject-arg plumbing; the
  Pass-0 installer reverts to shape-only ambiguity detection.
- **Delete** the `additive` bool at process_form.rs:172 once its last consumer
  is gone (verify no other consumer first).
- `imports::def_over_binding_error` is int-side and typecheck can't call it —
  either relocate the message construction into typecheck or reproduce it there
  (Principle 7: keep a single message form — consider hoisting the string to a
  `cranelisp-types` helper if both crates still need it, else move it wholesale).

## Operational implication / Context

- **Unit test (mandatory) at the typecheck seam** first — a `check_forms`
  cluster with an installed `Import` + a colliding `Defn`, asserting the reject,
  under BOTH `ModuleStrategy` values (they must now behave identically). Plus the
  export-visibility variant and the redundant-dedup non-collision.
- **e2e is warranted** — this is exactly a `--run`/`--link`/REPL divergence.
  `/qa` owns the integration guards. The two REPL guards
  (`tests/spec_08_modules::import_used_then_shadowed_by_defn_is_rejected_error`,
  `::import_shadowed_by_defn_before_first_call_is_rejected_error`) should keep
  passing; a NEW batch e2e must assert `--run` rejects the same shape.
- **These existing unit tests encode the OLD (to-be-inverted) behaviour and will
  fail — they must flip to assert rejection** (hand to `/qa` / `/dev`):
  `worker::tests::commit_allows_defn_over_import_on_replace_path` (worker/tests.rs:1636)
  and the Replace-path "must NOT reject" case at `imports/tests.rs:685`.
- **Fixture / stdlib blast radius (the real risk).** `Replace` now rejecting
  means every whole-module program that glob-imports/exports a module and then
  defines a name that module also exports will (correctly) error. Known:
  `tests/fixtures/preludes/test-standard.cl` — `(export [primitives [*]])` then
  `(deftype (Option a) …)` (primitives seeds `Option`) → collision. The real
  `stdlib/prelude.cl` and the exemplar likely share the shape. Remedy per §8.6.4
  is import hygiene: drop the redefined names from the glob source, or don't
  redefine the seeded name. Sweep before/with the fix: `/stdlib`, `/qa`
  fixtures, `/port` exemplar. This is a coordinated cleanup, not a one-file edit.
- **Confidence the seam is correct: high.** `check_forms` is the single function
  both modes call; the union view already surfaces Pass-0 imports; cluster
  atomicity already gives the byte-identical-on-reject property. The only design
  judgement left to `/dev` is the exact registration call-site inside
  `program.rs`/`checker.rs` and the message relocation.
