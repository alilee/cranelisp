# Macro availability model

**Status.** Adopted cross-context contract, delivered (S76 W-Macro,
user-approved 2026-06-03; source-ordered checkpoint amendment user-approved
2026-09-03). Owner `arch`. The normative language rules live in the spec —
[§9.3.4, §9.3.6, §9.2.5, §9.12 and §9.12.1](../../spec/09-macros.md) and
[§5.13.2](../../spec/05-definitions.md) — and are not restated here. This
document states the architectural model those rules rest on: which
definitions exist when a macro expands, why, how the passes and publication
domains realise it, and which alternatives it rules out. Which context owns
each half of expansion is
[macro expansion ownership](macro-expansion-ownership.md).

## 1. The rule

- A macro's expansion may reference definitions in **dependency modules**
  (modules typechecked before the defining module; loaded, typechecked and
  compiled just in time when an expansion first needs one) and **macros**,
  including same-module macros whose checkpoint has already succeeded.
- A **same-module non-macro definition** — `defn`, `def`, `const`, a `deftype`
  constructor, a trait method — is not available at expansion time. A clause
  that needs a helper places it in a dependency module or inlines the logic.
- **defmacro-before-use** holds within a module and within a REPL `begin`
  cluster. A name used textually before its `defmacro`, or after a failed
  attempt with no prior committed definition, is an ordinary reference that
  reaches the AST builder and name resolution as a non-macro.
- **Qualified references** `mod/macro` are not source-order constrained: they
  target a dependency module, and the module dependency graph is acyclic.
- The rule is identical in the REPL and in batch. The divergence from
  Clojure's module-wide macro availability is deliberate.

## 2. Why: round-trip safety

`regenerate_backing_file` (`src/save.rs`) writes a REPL session back to disk
as one batch module. A same-module helper called at expansion time would be a
Pass-2/3 entity that does not yet exist when the regenerated file recompiles,
so the round trip would fail. Resolving every expansion-time reference against
dependencies and already-committed macros makes REPL ≡ batch hold by
construction rather than by a parity check; the regenerator emits every macro
before the functions that use it for the same reason.

Consult this constraint before proposing any relaxation. "Let a clause call
an earlier same-module `defn`" reads as a small convenience and breaks session
regeneration.

## 3. Passes and publication domains

A module compiles in three logical passes and two publication domains.

1. **Pass 1 — source-order expansion with macro checkpoints (the compile-time
   layer).** The binary's expand loop walks forms in order, recognising heads
   against committed tables and executing committed clauses to fixpoint. At
   each direct or expansion-produced `defmacro` it typechecks the parent and
   complete clause set, closes and compiles the expansion-time dependency and
   generated-realization closure, and publishes parent, clauses and
   defining-module generated realizations as one module-local checkpoint
   before the next form expands. Nothing from that macro is callable before
   its checkpoint succeeds.
2. **Pass 2 — register non-macro signatures** over the fully expanded form
   set, including macro-generated definitions.
3. **Pass 3 — typecheck non-macro bodies** against the complete registered set
   and commit atomically.

Passes 2 and 3 are `check_forms`'s two internal passes. Pass 1 completes before
the one `check_forms` call, and `check_forms` never triggers macro execution.

**The pass order is the enforcement.** When a clause executes, the module's
own non-macro definitions are not yet registered and are structurally
invisible; no dynamic check polices §1. Typecheck rewrites the resulting
"undefined variable" inside a synthesised clause body into the actionable
diagnostic (§6).

**Checkpoint properties.**

- A failed checkpoint publishes nothing of that attempt and leaves any prior
  committed generation in place.
- A successful checkpoint is durable: later expansion, non-macro typecheck or
  codegen failure does not roll it back, and the later REPL §18 dependent cure
  is outside checkpoint success.
- A checkpoint is not a cluster boundary: non-macro forms on both sides stay
  in one HM cluster with full forward-reference and mutual-recursion scope.
- A dependency module publishes through its own module transaction. There is
  no cross-module prepared publication or rollback set.
- Redefinition publishes the new active clause set exactly. The binary
  identifies an old clause row by its typed `(group, clause_index)` identity
  and the canonical key constructor, never by parsing a generated-name prefix.
  Shrinking from `N` to `M < N` clauses retires indices `M..N` through explicit
  absent-key `ChangeAbi` decisions in the same `publish_compiled_staged` call,
  after verifying each live binding is a private, slotted `MacroClause` of that
  parent; omission alone never deletes. Retired slots stay tombstoned with
  frozen GOT pointers and their owners return for session retention; a later
  growth takes fresh slots. Cache load validates the parent/clause relation in
  both directions and regenerates on any mismatch.

## 4. Decision 44 stays true

Non-macro cluster atomicity (Decision 44:
[typecheck context](bounded-contexts.md#2-typecheck-cratescranelisp-typecheck)
invariants 2 and 11 and the [`check_forms` narrative](interfaces.md#check_forms))
operates unchanged on the Pass-2/3 layer: `check_forms` receives an already
fully expanded `Vec<ParsedEntry>`, stages, and commits on whole-cluster `Ok`.
Macro checkpoints sit deliberately outside that rollback domain. The statement
is true rather than aspirational because Pass-1 helpers are dependencies or
committed macros — no same-module clause compile is interleaved with the
cluster check (the hazard §7 records).

## 5. Mechanism carriers

- **Recognition.** `ResolutionScope::resolve_macro_head`
  (`crates/cranelisp-types/src/resolve.rs`) over a committed first-hop `View`;
  typecheck's body resolution is the same query over staging ∪ live.
  Recognition needs no typecheck dependency.
- **Loop and checkpoints.** `process_form::process_cluster_once` — driven by
  `cluster::process_cluster` on workers and directly by the eval and
  redefinition paths — with `src/expander.rs::expand_sexp_recursive`,
  `src/process_form/macro_resolution.rs` (`compile_macro_if_needed`) and
  `src/process_form/macro_clause.rs` (`compile_macro_checkpoint`).
- **Execution.** `JitMacroExpander` behind `cranelisp_types::MacroExpander`;
  only committed clauses are invoked.
- **Publication.** The prepared commit and
  `SymbolTable::publish_compiled_staged` with
  `StagedPublicationDecision::ChangeAbi`.
- **Dependency loading.** A form that needs an unloaded module surfaces a
  `ResolutionGap`; the binary loads the dependency and re-runs the form.
- **No provisional invocation machinery**: no unpublished-candidate call,
  reserved-GOT candidate stack, cross-module publication set or observation
  fence. The 2026-09-03 amendment added no public item, cache-schema field,
  backend contract or platform interface.

## 6. The rejected program and its diagnostic

A clause that calls a same-module `defn`, or reads a same-module `def`/`const`,
is a rejected program, not a defect. Typecheck reports
`undefined variable: <name> — macro expansion may not reference same-module
non-macro definitions; define <name> in a dependency module (or import it)`
(`enrich_macro_clause_resolution_error`,
`crates/cranelisp-typecheck/src/program/support.rs`). Evidence:
`tests/s76_macro_availability.rs::macro_clause_calls_same_module_defn_helper_rejected_neg`
and `::macro_clause_reads_same_module_def_value_rejected_neg`. `stdlib/defs.cl`'s
`def`/`def-` inlining their name mangling instead of calling `make-def-name` is
the correct authoring pattern under this rule.

## 7. Alternatives ruled out

Each still reads as a plausible simplification; the reason it lost is kept.

| Alternative | Why it lost |
|---|---|
| Module-wide `defmacro` pre-pass (Clojure parity) | Reinstates a pre-pass the form-by-form pipeline rejects and leaves REPL and batch divergent. |
| `defmacro` as a cluster boundary | Splits a file's non-macro forms into sub-clusters, breaking §5.13.1 mutual recursion across a `defmacro`. |
| Best-effort use-before-def with on-demand callee compile (the original S76 recommendation) | The S76 concrete trace showed a clause's same-module `defn` callee had an empty GOT slot at expansion — regular codegen is deferred past body checking, clause codegen is not — and pre-compiling the callee closure (`block_for_macro_codegen`) would still break round-trip regeneration (§2). The dead path was deleted, not wired. |
| One prepared transaction spanning Pass 1, dependency modules, macro execution, the HM cluster and presentation (S117) | Could fail after publication, reconstructed the entered form's subject by ambient scan and introduced a second lifecycle store. Superseded 2026-09-03 by durable source-order checkpoints (FIXME 0863 records the history). |

## 8. Where the contract manifests

| Carrier | Content |
|---|---|
| `spec/09-macros.md` §9.2.5, §9.3.4, §9.3.6, §9.12, §9.12.1; `spec/05-definitions.md` §5.13.2 | Normative rule, three-pass model, checkpoint semantics |
| [Bounded contexts](bounded-contexts.md) | Per-context statements |
| [Boundary types](interfaces.md) | Narrative companion to the types |
| [Symbol-table lifecycle](symbol-table-lifecycle.md) §5.4 | Macro declaration population and publication cadence |
| [`check_forms` narrative](interfaces.md#check_forms) | Non-macro atomicity with the checkpoint amendment |
| [Compilation sequence](sequences/exec-flow-compilation.mmd) | Pass 1 in the binary |
| `src/save.rs::generate_fns_and_macros` | Macros-first regeneration order |
| `tests/s76_macro_availability.rs`, `tests/spec_09_macros.rs` | Solution-level evidence |

## 9. Open obligations

Distinct from the delivered behaviour above:

- FIXME 0863 — int-interior reconciliation of the checkpoint model and its
  focused failure/durability coverage list; open, target `dev`.
- Spec §9.12.1 and the §9.3.6 same-spelled-candidates rule carry
  `[Uncovered S121]`; the traceability band is `qa`'s.
- ACT-0970 — suspected macro-redefinition persistence gap in the backing
  file; unattributed, routed to `qa`.

## 10. Retired section remaps

Earlier revisions carried the S76 option space, the concrete trace and the
finalized spec proposal, superseded by the delivered spec text and the
2026-09-03 amendment. For readers holding an old citation:

| Old section | Now |
|---|---|
| §0 (the locked decision) | This document |
| §0.1, §0.2 | §1 |
| §0.3 | §2 |
| §0.4 | §3 |
| §0.5 | §4 |
| §0.6, §5 (spec proposal) | Delivered: the spec sections named in the status line |
| §0.7, §0.9, §6 (mechanism) | §5 |
| §0.8 | §6 |
| §1–§4, §4.4 (option space, recommendation, trace), §7 (review items) | §7; the full deliberation is Git history |
