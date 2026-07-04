---
number: 0514
target: /dev
filed_by: /arch
filed_at: 2026-07-04
sprint_filed: 102
refers_to: src/process_form.rs §process_cluster_once (L172), src/worker.rs §commit_staging_to_live (L488-517), src/imports.rs §insert_detecting_ambiguity (L538-561), crates/cranelisp-typecheck/src/form.rs §check_forms (Pass-1 register loop, L249-254), crates/cranelisp-typecheck/src/checker.rs §resolve_current_or_prelude (L961) / §prelude_fallback_target (L895), spec/08-modules.md §8.6.4 / §8.8.1
status: open
---

# Move the §8.6.4 definition-over-(import|export|prelude) rejection to the shared typecheck seam (retire the mode-gated int-side gates)

## RULING UPDATE (user, 2026-07-04) — NO prelude exception

The always-error rule has **NO exceptions**: the prelude is just an implicit
import, so **redefining/shadowing a prelude-provided name is the same
compile-time error** as shadowing an explicit import. The prior "prelude names
remain shadowable" carve-out is **REMOVED**. This is load-bearing for the seam
choice (see §"Two scopes" below) and it re-anchors the 0475 pins from
allow-shadow to error.

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

## Two scopes — and why only typecheck sees both

The rule (post-ruling) must reject a definition that collides with a name bound
in EITHER scope:

- **(a) inner-table explicit imports/exports** — `ModuleEntry::Import` entries
  (private import or public export, §8.4.0) in the current module's own symbol
  table.
- **(b) outer-scope prelude bindings** — the implicit prelude glob (§8.8.1).
  These are **NOT flattened** into the module's table; they live in the separate
  `prelude` module and are reached only at bare-name resolution time via the
  `PreludeFallback` bit (`memory/project_prelude_outer_scope.md`,
  `crates/cranelisp-typecheck/CLAUDE.md §"Bare-name resolution & the
  implicit-prelude OUTER SCOPE"`).

The int commit gate (`commit_staging_to_live`) reads only
`live.symbols.get(name)` — it sees (a) but has **no prelude-fallback machinery**,
so it structurally cannot see (b). This **disqualifies the int commit gate** as
the home for the prelude-inclusive rule and confirms the seam must be in
typecheck, which is the one place bare-name resolution (inner-scope + prelude
outer-scope) already lives.

## Proposed resolution

Move the unified check into typecheck's **`check_forms` Pass-1 registration
seam** (`crates/cranelisp-typecheck/src/form.rs`, the `CheckPass::Register`
loop, L249-254 — concretely at the `register_defn_signature`/type-def
registration point in `program.rs`/`checker.rs` that inserts the new
`ModuleEntry::Def`/`TypeDef`). At that point, `TypeCheckEnv` has visibility of
BOTH scopes and already exposes the single two-scope chokepoint:

**`resolve_current_or_prelude(state, name, span)` (checker.rs:961)** layers the
staging-first inner-table `View` AND the prelude outer scope (with the
public-only head filter) via the shared `cranelisp_types::resolve_with_fallback`
primitive, returning `Resolved<C>` (terminal entry + home). Probe the
name-being-defined through this chokepoint (or the non-error
`probe_current_or_prelude`, L1431) and reject when it yields a binding whose
provenance is anything OTHER than the module's own prior `Def` being redefined —
i.e.:

- an inner-table explicit `Import`/export entry (home = another module via the
  `Import.source`), OR
- a prelude-outer-scope PUBLIC terminal (home = `prelude`/`primitives`, reached
  only because `prelude_fallback_target(current_module)` is `Some` — a module
  that does not receive the implicit prelude has no outer scope to collide with).

A resolve to the module's OWN existing `Def` (home == current module) is an
ordinary **redefinition** (the REPL redefine path), NOT a collision — leave it
to the existing redefinition machinery. The collision fires precisely when the
sole in-scope binding for the name is an explicit import/export or a prelude
outer entry.

This single predicate, sourced from the existing two-scope resolver (Principle 7
— one resolution chokepoint, not a hand-rolled inner-table scan), covers
everything:

- **Both directions collapse** (def-over-import AND import-over-def): "a Def
  whose name already resolves in scope" is order-independent by construction —
  all Pass-0 imports and the prelude bit precede `check_forms`.
- **Export-brought is automatic** (§8.4.0) — exports are `Import { Public }`; the
  resolver returns them like any inner binding.
- **Prelude-provided names now reject** (the ruling) — the same resolver returns
  the prelude terminal; NO variant carve-out.
- **Glob/specific/prelude-glob uniform** — reads the resolved binding, never the
  import shape.
- **Redundant `(import [m [X]]) (export [m [X]])` still dedups** — that is
  import-over-import, handled by the Pass-0 `both_indirect` terminal-equality
  arm, and never reaches Def registration.
- **Private prelude entries do NOT collide** — the `prelude_terminal_visible`
  (`is_public()`) head filter already treats them as not-found (I-1 discipline),
  so they are not in the outer scope.
- **The prelude module itself** never self-collides — `prelude_fallback_target`
  returns `None` when `current_module == prelude`.
- **Cluster atomicity preserves the byte-identical property** the commit-gate
  pre-scan gave: an `Err` from `check_forms` drops staging, live untouched.

Emit a `CheckError::TypeError` reproducing `imports::def_over_binding_error`'s
message shape (name the source module + `module/name` FQ remedy — the resolved
`home`/`Import.source` supplies both; for a prelude terminal the remedy names the
terminal's home module, e.g. `primitives/map`). Reproduce/relocate the message
in typecheck (int's `def_over_binding_error` is not reachable from the
typecheck crate); Principle 7 favours one message form — consider a
`cranelisp-types` helper if both crates still need it. No new `cranelisp-types`
shape needed.

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
- **0475 pins RE-ANCHOR to error (the ruling's direct consequence).** The pins
  that currently assert prelude/builtin names stay shadowable — `tests/
  vec_query_value_use.rs` (the `0475 drain` GREEN pins at L183/L203/L219) and the
  contrast note at `tests/spec_08_modules.rs:2206-2207` ("prelude-PROVIDED names
  remain shadowable — the 0475 pins") — now flip: a def over a prelude-provided
  name is a compile-time error. `/qa` re-anchors these; the spec's §8.6.4
  "Contrast pins (unaffected)" language and any §8.6.1/§8.8.1 "explicit imports
  and local definitions shadow prelude-fallback names" wording that grants the
  carve-out must be corrected by `/spec` (file `target: /spec`) — the impl change
  MUST NOT land ahead of the spec correction.
- **Blast radius (the real risk — now much larger).** Two tiers:
  1. *Explicit import/export collisions* (tier a). Every whole-module program
     that glob-imports/exports a module then defines a name that module also
     exports errors under `Replace`. Known:
     `tests/fixtures/preludes/test-standard.cl` — `(export [primitives [*]])`
     then `(deftype (Option a) …)` (primitives seeds `Option`) → collision.
  2. *Prelude-provided collisions* (tier b — the ruling's new reach, DOMINANT).
     Because nearly every user module receives the implicit prelude and the
     prelude re-exports primitives + stdlib names, ANY module that defines a name
     the prelude provides (`map`, `filter`, `Option`, `+`, `Some`, …) now errors
     unless it fully-qualifies the reference to the prelude one and renames its
     own. This is a broad, coordinated cleanup across `stdlib/`, `examples/`,
     `exemplar/`, and many `tests/` fixtures — not a one-file edit. `/sprint`
     should scope tier-b as its own coordinated sweep (owners `/stdlib`,
     `/examples`, `/port`, `/qa`) and sequence it with the impl + spec landing,
     or the whole suite goes red at once. Remedy per §8.6.4 is import hygiene +
     rename / fully-qualify.
- **Confidence the seam is correct: high.** `check_forms` is the single function
  both modes call, AND the only place that sees BOTH scopes (inner-table view +
  prelude fallback) — the int commit gate cannot see the prelude outer scope, so
  the ruling forces the typecheck home regardless. The two-scope resolver
  chokepoint (`resolve_current_or_prelude`) already exists; cluster atomicity
  already gives byte-identical-on-reject. The design judgement left to `/dev`:
  the exact registration call-site inside `program.rs`/`checker.rs`, the
  own-redefinition-vs-collision provenance discrimination, and the message
  relocation.
