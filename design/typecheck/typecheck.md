# `cranelisp-typecheck` — master design

Owner: `design` narrow-deployed to typecheck. Readers: `design` and `dev` working
this crate, and `arch` checking cross-crate coherence.

This is the crate's single statement of design intent. Every other document in
`design/typecheck/` is a subordinate elaboration of one subject (§10); where a
subordinate and this document disagree, this document wins, and the source wins
over both until the disagreement is repaired.

It designs against, in authority order:

1. [Bounded contexts §2](../arch/bounded-contexts.md#2-typecheck-cratescranelisp-typecheck)
   — what the crate owns and its cross-context invariants 1–10.
2. The published surface — `crates/cranelisp-typecheck/public-api.txt` (the
   checked baseline) and the crate-root rustdoc in `src/lib.rs` (per-item
   contracts).
3. The architectural [principles](../arch/principles.md) and the cross-crate
   rulings that source cites as "Decision N"; the
   [decision label index](../arch/decisions/README.md) resolves each label to its
   current home.

Git history carries how the crate reached this shape; this document states only
the current design and the rationale whose loss would invite a plausible mistake.

---

## 1. Bounded context — what we own

> "Untyped AST becomes typed AST plus populated symbol tables. Typecheck infers
> types, resolves traits, classifies polymorphism, and analyses match
> exhaustiveness." — BC §2

In scope:

- Hindley-Milner inference over every `Expr`, `Pattern` and `MatchArm` variant.
- Trait declarations, impl registration and method resolution, including
  higher-kinded traits, constrained polymorphism and monomorphisation.
- ADT typing: constructor schemes, exhaustiveness, type-parameter instantiation
  and accessor synthesis.
- Per-symbol callee extraction onto each callable's `callees` (the call graph
  typecheck produces for redefinition and emission order).
- Interprocedural ownership inference over the monomorphised call graph
  (`ownership-inference.md`, governed by `design/arch/ownership-inference.md`).
- Dependency-gap signalling: a cross-module dependency that is not yet
  typechecked is returned as `CheckError::Gap(ResolutionGap::…)` for `int` to
  satisfy, never waited on (Principle 3 — the crate sits below the scheduler).

Out of scope: AST construction and macro expansion (frontend); code emission and
RC discipline (backend); scheduling, sessions, module loading and the synthetic
`primitives`/`macros` mount (`int`); runtime helpers (primitives/intrinsics);
shared boundary types (`cranelisp-types`, owned by `arch`).

The crate has no cadence and no shared session state. `int` invokes it
synchronously, one cluster at a time.

---

## 2. Public surface

The canonical surface is `public-api.txt` plus the `lib.rs` rustdoc; this section
is a map, not a second contract.

- `check_forms` — the cluster-atomic entry (Decision 44): checks one cluster's
  `ParsedEntry` list against `SymbolTableAccess` (staging over live), the other
  modules' `SymbolTables`, `ModuleAliases` and `PreludeFallback`, returning
  `Result<CheckResult, CheckError>`.
- `instantiate_demands` — the reload seed: re-requests typed `MonoDemand`s
  through the same monomorphisation worklist after a redefinition
  (`monomorphisation.md` §3.8). It is not a second instantiation engine.
- `check_type_expr` — standalone `TypeExpr → Type` resolution for annotation and
  platform-signature contexts.
- `signature_matches_exact` / `signature_matches_partial` — the importable-symbol
  search predicates (`signature-match.md`).
- Scaffolding exposed for tests and direct drivers: `CheckState`,
  `TypeCheckEnv`, `PreludeFallback`, `advance_next_id_past_table`,
  `SymbolTableAccess`, `SymbolTableRead`, `SymbolTableMut`. Production `int`
  uses the entry functions only.
- Crate-owned result types: `CheckResult`, `CheckError` (`Gap` or located
  `TypeError`), `DispatchGap`, `UnresolvedDispatchSite`.
- The symbol-table-ensure trace hook for `int`'s scheduler tracing.

A `public-api.txt` change is an inter-crate public-API change: it needs the
user's approval before implementation and rides its source change-set under
`design/arch/CLAUDE.md` §"Baseline-diff discipline".

---

## 3. Internal architecture

### 3.1 Module map

| Unit | Responsibility |
|---|---|
| `form.rs` | The public entry functions (§2). |
| `program/` | The cluster pipeline (§5): `register` (Pass 1, including `register/multi_sig`), `body` (Pass 2), `finalize` (post-passes, harvest windows, ambiguity, publication), `mono_collect` (call-site demand collection), `callees` (the callee harvest), `support` (the concrete codegen-view builder), and the `#[cfg(test)]` `test_driver` and `test_support`. `mod program` is private and nothing in it is `pub`; a helper shared between its submodules is `pub(super)`, and `pub(crate)` only when a caller outside `program/` exists. |
| `traits/` | `registry` (trait declarations), `impl_check` (impl registration, HKT impl methods, method minting), `dispatch` (method resolution, dispatch-argument selection and impl lookup at the trait's home), `monomorphise` (the instance engine, `monomorphisation.md` §3.9), `type_resolve` (impl-target, declaration-identity, occurrence and constructor-variable predicates; the trait and HKT signature wrappers over `resolve` are `TypeCheckEnv` methods in `checker.rs`). `mod traits` is private and nothing in it is re-exported publicly; a helper shared between its submodules is `pub(super)`, and `pub(crate)` only when a caller outside `traits/` exists. |
| `ownership/` | The ownership-inference pass: `classify`, `transfer`, `fixpoint`, `confinement`, `uniqueness`, `publish`, `sites`, `trace` (`design/typecheck/ownership-inference.md` §1.3). |
| `checker.rs` | `TypeCheckEnv`, `CheckState`, cross-module lookup and the scope-resolution seam (§3.3). |
| `infer.rs` | Algorithm W per expression variant, with `infer_var` as the reference-resolution chokepoint. |
| `candidate_selection.rs` | Use-site selection among same-spelling canonical candidates (`use-site-candidate-selection.md`). |
| `adt.rs` | ADT registration, exhaustiveness and accessor synthesis. |
| `resolve.rs` | The one `TypeExpr → Type` resolver behind `TypeExprCtx` (`type-expr-resolver-convergence.md`). |
| `unify.rs` | Unification with rigid constraint variables, occurs check and type-error rendering (see [type names in errors](#83-type-names-in-error-messages)). |
| `cluster.rs` | `SymbolTableAccess`, the staging-versus-live choke point (see [staging dispatch](#64-staging-versus-live-dispatch)). |
| `scheme.rs`, `scope.rs`, `result.rs`, `signature_match.rs`, `trace.rs` | Generalise/instantiate, the lexical scope stack, the result types, the search predicates and the trace hook. |
| `builtins.rs` | Test-only synthetic world (`#[cfg(test)]`); production mounts are `int`'s. |

Module tests sit beside their production unit; `crates/cranelisp-typecheck/CLAUDE.md`
§"Testing" names the homes.

### 3.2 Maintainability watch

`checker.rs` is the largest production module and collects lookup helpers that
have no narrower home. Split it along a responsibility seam when a change would
otherwise add a new concern to it; do not split it by size alone (Principle 6).
Open audit points live in the action and filing registers; historical
assessments remain in Git.

### 3.3 Cross-module lookups

Short-name resolution is current-module-only, with per-symbol chain-follow
through `Import`/`Reexport` entries — never a universe scan (Principle 17;
`crates/cranelisp-typecheck/CLAUDE.md` §"Name resolution").
`resolve_terminal_entry_and_home` is the navigation primitive, staging-aware
through `probe_module_entry_owned`. Every bare-name reference resolves through the
one scope seam: `TypeCheckEnv::scope_resolve` / `scope_resolve_in` for a single
terminal, or `scope_resolve_candidates` when the use site selects among
same-spelling canonical candidates (`use-site-candidate-selection.md`).
Registration rejects nothing for sharing a spelling with an import, export,
prelude binding or derived member (`spec/08-modules.md` §8.6.4); the prelude participates only as
the fallback those seams apply.

**A reader that already holds a type's identity reads it by key.** An
`FQTypeName` names its home module and the type's own key there, so its
`TypeDefInfo` is the binding at that key, projected through `type_def_view_of`
(staging-aware, no scope, no candidate set). Constructor instantiation and
match exhaustiveness are such readers: they start from the scrutinee's type or
the resolved constructor's origin. Re-resolving the type's bare spelling
through the scope seam re-derives a settled identity ([Principle 24](../arch/principles/24-resolve-once.md))
and fails whenever §8.6.4 lets another declaration share the spelling, such as
another type's constructor. A miss at the key is a located error, never a
retry by spelling. The keyed read records no lookup dependency, exactly as the
bare route it replaces (§3.4).

Assurance: asserted with a named falsifier. A production caller passing an
`FQTypeName`'s halves to `lookup_type_def_in_module` or another scope reader
would refute conformance. The ACT-1002 review census found none. Retiring the
remaining spelling-reader production use would permit restricting that
reader to tests and making this boundary structural.

A centralised lookup index is not planned: it would be a bookkeeping change with
no measured performance need.

### 3.4 Qualified lookup dependencies

Status: **implemented against the user-approved API and committed, with the
int consumer, at `56e4d2e1` (2026-09-26); full suite green.** The fact, its carriers and its consumers are
`arch`'s [qualified lookup dependencies](../arch/interfaces.md#qualified-lookup-dependencies).
This section is typecheck's producer.

Typecheck records, for the module it checks, every other module whose table
answered a qualified reference. It reads that module from
`Resolved.lookup_module` and never re-derives it (Principle 24). It does not
filter compiler-owned modules and loads nothing; exclusion and use are `int`'s
([dependency record](../int/int.md#76-dependency-record-and-validity)).

- **One recording seam.** The scope seam (§3.3) records `lookup_module` from
  every successful result it returns, whether a single terminal or a candidate
  set, and whatever the root module. Recording belongs to the one private
  scope-construction step, not to its wrappers or their callers, so a new
  wrapper cannot resolve without recording. That step accepts only answer
  shapes that expose their answering modules through one private trait, so a
  new answer shape cannot bypass recording either.
- **Outcomes.**
  - *Success* is recorded, including a probe whose caller discards it: a type
    attempt that found a trait, a pre-check or a diagnostic render. A
    discarded answer still shaped the result, and an extra member costs at
    most a cache miss. Gap recording
    (§7.3.1) differs deliberately: there a discarded failure would become a
    load request.
  - *Failure* records nothing, because the carrier names only a table that
    answered. The absent module of `QualifiedModuleUnknown` is a gap, not an
    edge.
  - *Self-qualified, alias-to-self and bare* references carry no
    `lookup_module`. Bare references reach other modules through declared
    edges.
- **Sink and rollback.**
  - Each entry call collects its modules apart from the staging table. Each
    entry that runs with staging — `check_forms`, `instantiate_demands` and
    `check_type_expr` in cluster mode — writes them into the cluster's staging
    table through `record_lookup_dependency` once, on success. No production
    caller runs `check_type_expr` in cluster mode today; it writes for
    consistency, so no entry collects and then discards on success. Writing
    during resolution would need a mutable staging borrow while a caller may
    hold a shared one (§7.5).
  - A type error or gap discards the collection with the call. `int`'s retry
    reruns from the top and records afresh, so nothing unsettled reaches
    staging (Principle 26) and no rollback is needed beyond §7.4.
  - Without staging (the `Live` access mode, which platform signatures and REPL
    search use through `check_type_expr`) there is no sink, so nothing is
    recorded. Typecheck never writes the set to a live table.
  - The entry call owns the collector, and the environment's private staging
    carrier borrows it. Every seam wrapper reaches the environment, including
    the root-taking wrappers that have no `CheckState`, and a collector exists
    only with staging. The seam is read-only, so the collector is
    interior-mutable. The construction step inserts and releases the borrow
    before returning, so no borrow spans a resolution.
  - The carrier holds the collector by reference, under its existing
    single-threaded `Send`/`Sync` precondition. An owned interior-mutable field
    on `TypeCheckEnv` would remove its public `Sync` and `Freeze`, which is a
    public-API change; the reference leaves this crate's `public-api.txt`
    unchanged.

**Route census** (source read at `56e4d2e1`; the pattern and stacked-bound rows
are the §3.5 routes):

| Reference kind | Route | Recorded by |
|---|---|---|
| Value, value-position constructor, qualified dotted member `m/T.x` | `lookup`: the full spelling first (the alias target — `<current>.q` for a `(mod q)` child — or the absolute module), then the §3.5 walk over that same one module (§3.6), which supplies the gap. Reference recording resolves the full spelling by the first probe's chain. Every probe goes through the seam | Seam |
| Type positions: annotations, `deftype` fields, aliases, trait and HKT signatures, HKT impl signatures | The type-expression resolver, through the candidate seam | Seam |
| Impl target head | The type lookups, qualifier kept (§7.3.1) | Seam |
| Trait: impl trait slot, pairing head, constraint slot, type-or-trait step R (§7.3.2) | `resolve_trait` and the impl trait resolver | Seam |
| Trait in a stacked bound, `:Eq :m/Tr a` | `resolve_trait` as written, the step R resolution (§3.5) | Seam |
| Qualified pattern constructor `m/C` or `m/T.C` | The qualified walk alone (§3.5) | Seam |
| Bare dotted member `T.x`, value or pattern | Head resolved bare; member read by key in the parent type's or trait's home | Nothing: the home is reached through the closure |
| Keyed reads at a resolved home: impl discovery, trait declarations, method-to-trait, ownership facts, the reach of a monomorphisation re-check to its generic body | Not spelled references | Nothing: the home is reached through the closure |
| Qualified spelling inside a cross-module monomorphisation re-check ([monomorphisation](monomorphisation.md#37-cross-module-body-recheck-scoping)) | The seam, relative to the defining module, in the checked module's staging environment | Seam, as a dependency of the module being checked; only that module's own path is excluded. Conservative: an extra member costs at most a cache miss |
| Macro heads | `int`'s recogniser | `int` |

**Grades.**

- *A qualified spelling resolved through the seam is recorded*:
  **structural** within the crate, for every wrapper and answer shape.
  Falsifier: a second `ResolutionScope` construction in the crate (today there
  is one).
- *Every qualified reference kind is recorded*: **measured** for the census
  families by the census cell below; **asserted with a named falsifier**
  beyond them. Falsifier: a qualified spelling that reaches a table without
  the seam, such as a new rooted route. No caller records a module itself; the
  seam is the only recording point.
- *An unrecorded miss cannot change a cached answer*: **asserted with a named
  falsifier.** A qualified spelling reads one module, its written module after
  alias substitution ([§3.6](#36-one-reading-of-a-qualified-module)), and that
  module's absence is the form's gap. `(mod q)` installs the private alias
  `q → <current>.q`, so every reading, value or pattern, reaches the declared
  child and never consults absolute `q`; the `mod` declaration is already the
  declared edge. An undeclared registered child is never consulted. Falsifier:
  a cached module resolves `q/x` to one module while a fresh compile of the
  same sources resolves it to another.

**Evidence** (`crates/cranelisp-typecheck/src/form/tests.rs`):

- `lookup_dependency_census_records_answering_module`: one row per census
  family through the seam; one alias row per distinct path by which a spelled
  qualifier reaches the seam — value, type resolution, step R, the stacked
  bound and patterns; and the value and pattern "undeclared child" rows, which
  seed a registered `<current>.q` the module never declared and require
  exactly `q` recorded (§3.6). A declared child reaches the seam through its
  alias.
- Negative cells: `lookup_dependency_census_bare_and_self_qualified_record_nothing`,
  `lookup_dependency_rejected_cluster_writes_nothing_neg` and
  `lookup_dependency_live_mode_records_nothing`.

### 3.5 Qualified stacked bounds and constructor patterns

Status: **implemented and committed at `56e4d2e1` (2026-09-26).** This corrects the confirmed
defects LB-1, LB-2 and LP-1 to LP-3
([S122 evidence delta](../../tests/plan/s122-evidence-delta.md#source-read-lookup-leads--classification-2026-09-26)).
Each route resolved a qualified spelling without the qualified path. Each now
takes the route its annotation twin already takes, or value position's
qualified walk, so existing semantics decide. The public surface does not change.

**Stacked trait bound** (`[:Ts :m/Tr x]`, spec §3.9.2):

- Every trait in the stack resolves as written through `resolve_trait`, the
  §7.3.2 step R resolution. It applies alias substitution (§9.8) and the
  existence, visibility and kind checks, and returns the canonical home. No
  arm takes the spelled qualifier as the home, so bare and qualified members
  take the same step.
- Step R and the stack share one crate-private step, which returns its
  failure. Step R drops that failure, because the type failure decides that
  route. A stack has no other reading, so its failure is the form's failure
  and goes through the one projection (§7.3.1):
  - an absent module records `Type(module/Tr)`, and `int` loads and retries
    (§7.3.2 "The gap requests a load");
  - a present module without the trait, a private trait, or a non-trait is a
    located error with no gap.
- Unchanged:
  - pairing the home with the spelled trait name (see the renamed-import lead
    in §11);
  - how a constraint is used after registration
    ([inference](inference.md), rigid seeding);
  - enforcement of a declared bound that the body does not use. That is
    DB-1, designed separately in
    [declared bounds at settlement](#921-declared-bounds-are-discharged-at-settlement).
    This correction does not depend on it: LB-1 pins the scheme's canonical
    identity.

**Qualified constructor pattern** (`(m/C x)` or `(m/T.C x)`, spec §6.2.1):

- Spec §8.6.5 gives constructors the same rule in value and pattern
  positions. The pattern route's qualified arm does not resolve the bare name
  inside the spelled module, where that module's private names and
  non-re-exported imports would be visible. It uses the qualified walk that
  `lookup` uses:
  - the one written module from the one source (§3.6);
  - that module resolved through the scope seam as the composed
    `module/name`, with alias substitution, the public-only filter and no
    prelude retry;
  - that module's gap when it yields no winning terminal.
- **One walk.** `lookup`'s qualified block is the crate-private
  `resolve_qualified_walk`. Its callers pass what counts as a winning
  terminal: one with a scheme for a value, and a constructor for a pattern.
  The rooted helper stays for its other callers, which are not qualified
  references.
- **The walk is not value position's only qualified step.** Before the walk,
  `lookup` resolves the full spelling through the seam. When that probe
  fails, the walk probes the same module and supplies its gap; the pattern
  route calls the walk alone. Both read the one written module after alias
  substitution, so the two positions agree for every spelling (§3.6).
- **Pattern outcomes.**
  - A constructor terminal is instantiated and recorded in `pattern_ctors`
    as before.
  - With no winning candidate, the pattern fails with its located "unknown
    constructor in pattern" error. At that point a qualified name writes the
    walk's gap, or no gap, as the pending gap, as `infer_var` always writes
    for the value twin; bare and dotted names leave it untouched. The
    qualified arm has no scrutinee-directed fallback, so the miss is always
    the form's failure and this is the §7.3.1 recording point. `int` then loads, retries or reports exactly as it does for the
    value twin. For example, LP-3's unloaded module is loaded, and LP-2's
    private constructor reports what `(shapes/Hid 8)` reports.
  - The auto-curry arity guard reads the same resolution for a callee that
    has already been typed as a value. It drops the gap, because it is a
    probe.
- The dotted and bare arms are unchanged. The internal-constructor gate still
  reads the name with its qualifier removed; see §11.
- Quasiquote templates lower to `macros/SCons` and `macros/SNil` in both
  positions (`crates/cranelisp-frontend/src/synth.rs`). A pattern template
  therefore resolves as its value-position template does, including through
  an import alias or a `(mod macros)` spelled `macros` (review A-4, a `qa`
  candidate hygiene lead).

**Lookup dependencies.** Both routes reach tables only through the seam, so
§3.4 records them there; neither records a module itself.

**Grades.**

- *The pattern route and value position's qualified fallback share the
  walk's module, seam and gap choice*: **structural**, because both call one
  step. Falsifier: a second qualified candidate source in the crate.
- *A qualified constructor resolves the same way in pattern and value
  position*: follows from §3.6's structural grade and is not separately
  graded. R1-V and `qualified_value_and_pattern_name_one_module` (§3.6)
  measure it.
- *No qualified trait or pattern spelling reaches a table outside the seam*:
  **asserted with a named falsifier**, the §3.4 census.

**Evidence.**

- E2E (`tests/spec_08_modules.rs`):
  - `fq_stacked_bound_trait_through_alias_resolves_in_aliased_module`;
  - `fq_stacked_bound_trait_to_missing_module_rejected_neg`;
  - `fq_ctor_pattern_through_alias_resolves_in_aliased_module`;
  - `fq_ctor_pattern_private_constructor_rejected_neg`;
  - `fq_ctor_pattern_as_only_reference_loads_its_module`.

  The quasiquote suites and `tests/spec_06_pattern_matching.rs` guard the
  unchanged routes.
- Unit cells beside the §7.3 cells in
  `crates/cranelisp-typecheck/src/form/tests.rs`:

  | Cell | Setup and reference | Expected |
  |---|---|---|
  | `stacked_bound_through_alias_constrains_target_home` | Seeded `b` declares `Tr`; alias `bb` names `b`; `[:T1 :bb/Tr x]` | Accepted; the parameter's constraints include `b/Tr` |
  | `stacked_bound_absent_module_is_type_gap` | `[:T1 :nosuch/Tr x]`, no `nosuch` | `Gap(Type(nosuch/Tr))` |
  | `stacked_bound_present_module_without_trait_is_type_error_neg` | Seeded `b` without `Tr`; `[:T1 :b/Tr x]` | Located error, no gap |
  | `stacked_bound_bare_members_unchanged` | Control: bare `[:T1 :T2 x]` | Unchanged |
  | `qualified_ctor_pattern_through_alias_resolves_in_target` | Seeded `b` with public `C`; alias `bb`; pattern `(bb/C v)` | Accepted; `pattern_ctors` records `b`'s constructor |
  | `qualified_ctor_pattern_private_constructor_matches_value_twin_neg` | `b` declares `C` private; pattern `(b/C v)` from another module | Not accepted; the same `CheckError` as the value twin `(b/C 1)` |
  | `qualified_ctor_pattern_absent_module_is_value_twin_gap` | Pattern `(b/C v)`, no `b` | The gap the value twin `(b/C 1)` returns |
  | `qualified_ctor_pattern_ignores_undeclared_child_module` | Registered but undeclared child `<current>.q` (no alias) and absolute `q`, both with `C`; pattern `(q/C v)` | Resolves to absolute `q` (§3.6) |
  | `qualified_non_constructor_pattern_is_located_error_neg` | Control: `b/f` is a function; pattern `(b/f v)` | Located "unknown constructor in pattern", no gap |
  | `qualified_macros_scons_pattern_resolves` | Control: seeded `macros` with `SCons`; pattern `(macros/SCons h t)` | Accepted |

- The §3.4 census cells cover the stacked-bound and pattern families.

### 3.6 One reading of a qualified module

Status: **implemented 2026-09-26; uncommitted.** It corrects the confirmed
defect R1-V
([classification](../../tests/plan/s122-evidence-delta.md#producer-review-r-1-and-a-4--classification-2026-09-26)).

**Requirement.**

- Spec §8.6.6 step 3 resolves a qualifier in "a child module of the current
  module".
- §8.11.2 item 1 defines that child as one registered by `(mod name)` in the
  current module.
- §8.5.4 edge 2 confines child-of-current resolution to registered
  submodules and aliases.
- §8.11.2.1 forbids a bare module name reaching the submodule in one position
  and the root module in another.
- A recorded refuter would read §8.1.1 into step 3. Adopting it would change
  only R1-V's value leg.

**Design.**

- A declared child already has exactly one reading. `(mod q)` installs the
  private alias `q → <current>.q`, which `int` restores on a cache hit, so
  §8.6.6 step 1 reaches the child in every position.
- A synthesised `<current>.q` candidate would therefore add nothing for a
  declared child and a non-conforming reading for an undeclared one, so none
  exists.
- A qualified `module/name` names exactly one module: the written module path
  after alias substitution (§9.8). The one candidate source,
  `checker.rs::qualified_candidate_module`, yields that module and no child.
- The walk (§3.5) is the one qualified step for value position's fallback and
  for patterns: it probes that module, projects the winner and otherwise
  returns that module's gap. No child-versus-absolute gap precedence exists.
- Reference recording (`record_reference_target`) resolves the full spelling
  through `def_resolved`, the same seam chain value position's first probe
  uses. Value position's scheme and its recorded target therefore come from
  one resolution (Principle 24).

**Consequences.**

- Value and pattern positions agree for every spelling.
- An undeclared registered child is never consulted, so what else is loaded
  cannot change an answer, and a cached answer cannot rest on an unrecorded
  miss (§3.4).
- Quasiquote `macros/…` spellings are redirected only through an alias
  (A-4 narrows).
- Aliases, mount aliases, self-qualified normalisation, the scope seam,
  lookup-dependency recording and gaps are unchanged.

**Grade.** *A qualified spelling denotes one module, in every position*:
**structural**, because the crate has one candidate source and it yields one
module. Falsifier: a second qualified candidate source in the crate.

**Outside this crate.** `int`'s bare-name import and export resolution uses
declared children rather than registered modules or backing files
([int §6.9](../int/int.md#69-bare-module-names-in-import-and-export)).
This is IR-1's correction of the same undeclared-child capture in import and
export positions; its evidence and status belong to that surface.

**Evidence.**

- E2E: R1-V (`tests/spec_08_modules.rs::qualified_name_to_undeclared_registered_child_resolves_to_root_module`),
  GREEN on all six legs.
- Unit cells:
  - `crates/cranelisp-typecheck/src/form/tests.rs`:
    - `qualified_value_and_pattern_name_one_module`: with an undeclared
      registered child and absolute `q`, the value's scheme, its recorded
      callee and the pattern all name `q`; with `(mod q)`'s alias installed,
      all three name the child;
    - `qualified_name_does_not_fall_back_to_undeclared_child_neg`: a member
      only the undeclared child exports is `q`'s member gap, in value and
      pattern position, and records nothing;
    - `qualified_ctor_pattern_ignores_undeclared_child_module` (§3.5 table);
    - the §3.4 census's "undeclared child" rows.
  - `crates/cranelisp-typecheck/src/program/register/tests.rs::qualified_candidate_module_is_the_written_module`.
  - `crates/cranelisp-typecheck/src/checker/tests.rs::qualified_lookup_loaded_module_missing_member_has_no_phantom_child_gap`.
- The census, value-twin, pattern and negative cells were RED before the
  change. Detection proof: restoring a child-first probe in the walk failed
  all four; reverted.

---

## 4. Quality attributes

- **Simplicity (Principle 6).** One cluster path, one `TypeExpr` resolver, one
  unification seam and one scope-resolution seam. New behaviour extends these
  seams; a parallel pipeline, resolver or walker is a defect.
- **Observability.** `CheckResult` and the located `CheckError` are the
  diagnostic product. The only trace surface is the symbol-table-ensure hook
  (`design/int/heisenbug-race-closure.md` §8.3.4); per-symbol introspection is
  backend's and `int`'s.
- **Performance.** Cross-module resolution is per-symbol chain-follow; no spec
  criterion pins typecheck time, and performance work waits for a measurement.
- **Testability (Principle 5).** `check_forms` takes its tables as arguments, so
  unit tests drive it through `TestFixture` over `cranelisp-types` alone, with no
  `cranelisp-primitives` dependency.

---

## 5. Pipeline inside `check_forms`

1. **Pass 1 — register** (`program/register.rs`). Each form installs its
   canonical declarations and exposes their module-scope candidates under
   `spec/08-modules.md` §8.6.4: type definitions, trait declarations and
   methods, trait impls, and signature schemes. Distinct canonical declarations
   sharing a spelling coexist; use sites select among them
   (`use-site-candidate-selection.md`). No body is checked.
2. **Pass 2 — body check** (`program/body.rs`). Algorithm W checks each body
   against its registration. The checked AST and initial canonical callees stay
   in the private body ledger (`checked-body-publication.md`); active expression
   and resolution facts stay on `CheckState`. Initial callees come from
   `crates/cranelisp-typecheck/src/program/callees.rs::harvest_callees`.
3. **Finalize** (`program/finalize.rs`). Generalisation, overload resolution and
   the multi-signature back-flow drain (`monomorphisation.md` §11), the
   ambiguity backstop, the two post-settlement monomorphisation harvest windows
   (`monomorphisation.md` §3.3), and final publication: each body's AST and
   complete callee set are published together, once
   (`crates/cranelisp-typecheck/CLAUDE.md` §"`callees` completeness"). The
   ownership pass then runs over the published concrete bodies
   (`design/typecheck/ownership-inference.md` §1.2).

All writes go through `SymbolTableAccess`. `int` commits the staging table only
when the whole cluster succeeds.

### 5.1 Per-form dispatch

`check_forms` drives the crate-private per-form entry `program::check_form` once per
form per pass, merges each `FormCheckResult` into one `ModuleCheckAccumulator`, then
calls `finalize_check_result`. None of these is public; `check_forms` is the entry.

| Form | Pass 1 (`Register`) | Pass 2 (`CheckBody`) |
|---|---|---|
| Type definition | Register the type and its constructors (`adt.md`). | Nothing. |
| Trait declaration | Register the declaration and its methods ([trait declaration](traits.md#2-trait-declaration)). | Nothing. |
| Trait impl | Register the impl and check its written method bodies ([trait implementation](traits.md#3-trait-implementation)); return the generated default methods. | Nothing. |
| Single-signature definition | Record the body's registration (fresh parameter and return variables) in the body ledger. | Check the body against that registration. An impl method already checked in Pass 1 is skipped. |
| Multi-signature definition | Register one entry per clause (`monomorphisation.md` §11). | Check each clause body; overload settlement happens in finalize. |

A REPL expression reaches typecheck already wrapped as a zero-parameter definition
named `__expr` and is checked like any definition; it is a monomorphisation root
(`monomorphisation.md` §3.2). The test-only driver (`program/test_driver.rs`)
performs the same wrapping for in-crate tests.

### 5.2 Pass invariants

1. **Every registration precedes every body check.** Checking a body whose
   definition was never registered is an error, not an implicit registration.
   This is what lets a body call a definition later in the cluster (spec §3.5.2).
2. **Pass 1 is one sweep in form order.** Each form registers when it is reached;
   there is no hidden sort by form kind. Default methods produced by impls are
   registered after the sweep and their bodies are checked after the Pass-2 sweep.
   A body may refer to any definition in the cluster. A declaration-level reference
   to a type declared later in the cluster is a different matter; see the open item
   in §11.
3. **One `CheckState` per cluster.** All bodies share one substitution, so a call
   in one body constrains the callee's registration variables. Each Pass-2 body
   starts from the trait constraints Pass 1 left, and definitions already
   generalised are re-settled before each body (`monomorphisation.md` §5.1).
4. **Settlement follows all bodies.** A body's scheme may be generalised and
   written back as soon as its check ends, so later siblings instantiate it
   (`monomorphisation.md` §5.1); that writeback neither settles nor publishes.
   Final generalisation, overload settlement and monomorphisation run in finalize,
   after every body has been checked, so a body's expression types are provisional
   until then. Nothing is published before finalize (§5 step 3).
5. **One accumulator per cluster, owned by one call.** The accumulator is created
   before Pass 1 and consumed by finalize. It is never shared across threads; each
   `int` worker owns its call's `CheckState` and accumulator (§7.1).

---

## 6. Mutation discipline

### 6.1 The contract

`check_forms` never receives `&mut SymbolTable`. It writes through
`SymbolTableAccess` (§6.4), and each module table mutates per entry through its
inner `DashMap`. The only whole-table mutations belong to `int` on the initiating
thread: structural declarations at module registration and the REPL
`defn_order` append after a commit.

This is what makes per-symbol gaps operationally sound: a waiter resumed on
`SymbolTypechecked(fq)` can read the other module's table through shared shard
access, and a second worker's cross-module read does not block behind a
whole-table write lock.

### 6.2 What typecheck writes

- The caller-owned AST is annotated in place (`ast-annotation.md`).
- Declarations, schemes, synthesised accessor and monomorphised entries, and
  checked-body publications go to staging through the types-crate funnels. A
  callable's lifecycle state (`Life`) is set only by those funnels
  (`design/arch/symbol-table-lifecycle.md`); typecheck consumes that vocabulary
  and never grows a local variant beside it.
- The checked module's lookup dependencies go to staging once, when the entry
  succeeds ([lookup dependencies](#34-qualified-lookup-dependencies)).

### 6.4 Staging-versus-live dispatch

`SymbolTableAccess` selects per module: the cluster's own module reads a
staging-over-live union and writes staging (`SymbolTableRead::Cluster`); every
other module reads live. The distinction is absorbed inside the accessors, so no
register or lookup site branches on it. `cluster.rs` rustdoc records the as-built
shape.

---

## 7. Concurrency model

### 7.1 What the crate sees

An `int` worker supplies the cluster's `SymbolTableAccess`, read-only
`SymbolTables` for other modules, the session's `ModuleAliases` and
`PreludeFallback`, and owns the per-call `CheckState`. The crate reads no session
or scheduler state and never waits; dependencies surface as `CheckError::Gap`.

### 7.2 Worker ordering

One worker per module is a scheduler-ordering rule, not a lock-safety
requirement: per-entry locks make concurrent mutation of one table safe. Mutual
imports are `int`'s to diagnose as a cycle (BC §6); typecheck neither detects
nor waits on them.

### 7.3 Gap-return contract

| Gap | Raised when | `int` response |
|---|---|---|
| `ResolutionGap::SymbolTypechecked(fq)` | A qualified value, constructor or pattern reference names a module absent from the session tables, or a member absent from a present module. | Typecheck that module, then retry the whole cluster; a member still absent from a terminal module is `int`'s "no member" error. |
| `ResolutionGap::Type(fqt)` | A qualified name in a type position or a stacked trait bound (§3.5) names a module absent from the session tables. | As above. |

Typecheck asks for `SymbolTypechecked`, not `SymbolInMemory`: it needs a scheme,
not compiled code, so a gap never waits on codegen. `ResolutionGap` is shared
with frontend, which alone raises `MacroInMem`.

#### 7.3.1 Producing the type gap

Status: **implemented 2026-09-25 and committed at `56e4d2e1`; integrated and
QA-accepted** (see *Evidence* below).

`spec/08-modules.md` §8.5.4 edge 1 makes an unresolved qualified type a
resolution-layer `Type` gap, and invariant 8 of
[bounded contexts §2](../arch/bounded-contexts.md#2-typecheck-cratescranelisp-typecheck)
makes a missing module a `Gap`. Both typecheck gaps reach `int` through one
carrier: the pending gap on `CheckState`, which the `check_forms` boundary lifts
when the form fails with a type error.

- **Source.** A type expression resolves through the one `TypeExpr` resolver
  behind the checker's type-expression entries (§3.1). An impl head's target
  resolves through the kind-specific type lookups: its FQ type name, and its
  concrete type with arguments. An absent module fails either route with the
  resolution primitive's `QualifiedModuleUnknown`, which carries the
  alias-substituted module (§9.8) and the member name.
- **Impl targets keep their qualifier.** The frontend preserves the module on an
  impl target's head, and every impl-target lookup resolves the head as written:
  - a head qualified by another module keeps `module/name`, so that module
    decides it and an absent one becomes the gap;
  - a bare or self-qualified head resolves as the bare name, the same collapse
    the type-expression resolver applies, so an in-cluster target stays visible
    through staging;
  - a qualified intrinsic target is named by its canonical symbol, not its
    spelling, so `primitives/Int` names `primitives/Int` once.

  Resolving only the bare head name is the rejected shape: an impl on an
  unloaded module's type could never gap, `(impl Tr b/T …)` was rejected when
  `b/T` was reachable only by qualification, and a same-named local type could
  capture the target. The head's bare name remains for diagnostic text only.
- **Recording point.** The gap is recorded where a type-position failure becomes
  the form's failure, not where resolution fails. A gap recorded by a discarded
  attempt would turn a later, unrelated type error into a load request, and the
  retry would misreport it as a missing member. These callers try a type and
  discard the failure, so they record nothing:
  - the type-or-trait annotation (§7.3.2), in both the parameter and
    value-annotation routes, when the trait arm is taken;
  - the trait-tail recognizer;
  - the impl arity pre-check and the impl accessor-collision pre-flight, which
    leave an unresolvable target to the impl's own lookup.
- **One projection.** The type-expression entries and both impl-target lookups
  return a private type-position failure with no implicit conversion into the
  per-form error. Its conversion into the form's failure is one projection: for
  an absent module it records `Type(module/name)`; for every failure it returns
  the same located error that the plain `ResolveError` conversion produces. A
  caller of these entries cannot bypass the gap with `?` (**structural**: the
  bypass does not compile), and that includes the impl-target route.
- **Limits of the structural grade** (asserted, with falsifiers):
  - `check_type_expr` leaves through one named exit that returns the located
    error without recording, because its callers, platform signatures and REPL
    search, run no gap loop. The type does not stop a gap-loop caller from
    using that exit.
  - The general resolution primitive stays crate-visible for other kinds. A new
    type lookup written directly against it bypasses the projection.
  - Falsifier for both: a qualified type position in a checked form whose
    module is absent reports "not loaded" instead of a `Type` gap.
- **Residual leads** (from review; not executed, no cell scheduled):
  - *HK impl heads drop the constructor's qualifier.* In
    `traits/impl_check.rs`, the higher-kinded path's primitive-name check and
    its arity kind-check read the constructor's bare name, so a qualified
    constructor is kind-checked against a same-named local type, or not at
    all. Both are discarding probes: they record no gap. A cell needs `sprint`
    scheduling.
- **Unchanged.** The carrier, the lift and the public surface are unchanged;
  this produces the gap that `lib.rs` already documents. A missing member of a
  present module stays a located "unknown type" error. That result does not
  depend on load order, because both orders resolve against the loaded module.

**Evidence.** Reported by `dev` on 2026-09-25 and not re-executed here:

- Unit cells sit beside `gap_on_missing_module_plain` in `form/tests.rs`: the
  parameter annotation, `deftype` field, alias and impl-target routes each
  return the gap, and a present module without the type stays a type error.
  The projection's own cell is in `checker/tests.rs`. The route cells were
  observed RED before the change. The impl-target cell first failed with the
  bare-name face, which exposed the dropped qualifier. A planted
  record-every-failure fault failed the negative cells.
- The spec 7 trait suite, including the qualified impl-target canonical
  controls, stays GREEN.
- E2E: `tests/spec_08_modules.rs::fq_type_annotation_alone_loads_its_module`,
  its alias-only sibling,
  `tests/cache.rs::fq_type_only_reference_loads_its_module_on_a_fresh_compile`
  and `fq_type_annotation_to_missing_module_errors_at_reference_site_neg`
  are GREEN in the integrated full suite. The last one's location leg
  depends on int's reference-site walk
  ([int §6.3.1](../int/int.md#631-locating-a-gap-at-its-reference-site)).
- An independent review found no blocking issue, and QA judged the
  evidence adequate
  ([S122 evidence delta](../../tests/plan/s122-evidence-delta.md#fresh-fq-type-only-loading--evidence-delta-2026-09-25)).

#### 7.3.2 Type-or-trait annotations

Status: **implemented 2026-09-25.** It corrects the defects F-a (value
route) and F-b (parameter route) described below
([S122 evidence delta](../../tests/plan/s122-evidence-delta.md#annotation-trait-fallbacks-f-a-f-b--intake-and-allocation-2026-09-25)).

A single named annotation on a parameter (`[:X x]`) or a value (`:X e`) is a
type if a type candidate exists, otherwise a trait (spec §3.9.3). A qualified
`X` resolves in its named module, which is loaded first (§8.6.1, §8.6.6). Both
routes decide the reading in the same three steps:

- **Step T — type first.** The annotation resolves through the
  type-expression entry. Success is the type reading.
- **Step R — trait reading as written.** If the type attempt fails, a single
  named reference is resolved as a trait through `resolve_trait`, spelled as
  written (`module/name` when qualified). An impl's constraint slot and an HK
  pairing head already resolve a trait reference this way
  (`traits/impl_check.rs`). That resolution applies alias substitution, the
  existence, visibility and kind checks, and yields the trait's canonical home.
  The trait arm is taken only when it succeeds, and its constraint or
  satisfaction check uses that home.
- **Step F — otherwise the type failure becomes the form's failure.** The
  failed trait attempt is discarded and records nothing. The type failure goes
  through the one projection (§7.3.1), so an absent module records
  `Type(module/name)`.

- **The gap requests a load; it does not decide the kind.** `int` loads the
  gap's module and retries the cluster (§7.3); it reads the gap's member name
  only to locate and word its diagnostic. The retry repeats steps T and R
  against the loaded module. A trait there takes step R, a type takes step T,
  and a name that is neither is a located "unknown type" error. No trait gap
  variant is needed.
- **Why the as-written spelling.** The former fallbacks showed the failures of
  the alternatives:
  - Taking the qualifier as the home without resolving it accepted a reference
    to an absent module, or to a missing member of a present one (F-a, value
    route). The type attempt's failure was dropped, and a still-variable expression passed the satisfaction check.
  - Testing the bare name (F-b, parameter route) let a local or prelude trait
    of the same spelling take the trait arm for `:zz/Tr`. It also rejected a
    trait reachable only by qualification.
  - Either shape also recorded an alias qualifier as the home, so the impl
    lookup in the home missed.
- **One step for both routes.** The two routes are entrances to one constraint
  shape. A single crate-private trait-reading step replaces the syntax-only
  `single_trait_bound_from_annotation`, whose only callers are these two
  routes. Both routes call the step, so the decision cannot diverge between
  them again. The parameter route constrains its fresh variable with the
  resolved home. The stacked bound (§3.5) resolves each member through the
  same step and projects its failure instead of dropping it.
- **Unchanged.** The public surface, `ResolutionGap`, `TypePositionFailure` and
  its projection. Also unchanged: the impl constraint slot and the
  satisfaction-check rules
  ([inference §4.5](inference.md#45-value-position-annotations)). The trait
  name paired with the home stays the spelled name, as in the bare arm today
  (see the renamed-import lead in §11).

**Evidence.**

- E2E: `tests/spec_08_modules.rs::fq_value_annotation_neg_missing_module_rejected_unloaded_trait_accepted`
  (FA-1) and `fq_param_trait_annotation_resolves_in_named_module_neg_not_captured_by_bare_trait`
  (FB-1) were RED for their predicted reasons before the change and are
  GREEN after it.
- Unit: these cells sit in `form/tests.rs` beside the §7.3.1 cells
  (`type_or_trait_*`). Every cell was observed RED before the change and
  is GREEN after it.

  | Cell | Route | Setup and annotation | Expected | Before the fix |
  |---|---|---|---|---|
  | U1 | Value | `(defn h [t] :some.mod/T t)`, no `some.mod` | `Gap(Type(some.mod/T))` | RED: accepted |
  | U2 | Parameter | Current module declares trait `Tr`; `[:some.mod/Tr x]`, no `some.mod` | `Gap(Type(some.mod/Tr))` | RED: accepted |
  | U3 | Parameter | Seeded module `b` declares trait `Tr` and is not imported; `[:b/Tr x]` | Accepted; the parameter's constraint is `b/Tr` | RED: type error |
  | U4 | Value | Alias `bb` names `b`; `b` declares `Tr` with an impl for `Int`; `:bb/Tr 5` | Accepted | RED: rejected, because the home is `bb` |
  | U5 | Parameter | As U4; `[:bb/Tr x]` | Accepted; the constraint is `b/Tr` | RED: type error |
  | U6 | Value | Seeded `b` has no `X` of either kind; `:b/X t` | Located `TypeError`, no gap | RED: accepted. The unresolved home also accepted a present module's missing member |

### 7.4 Rollback

A failed cluster leaves no live mutation: `int` drops the staging table. The
type-variable counter is monotonic and deliberately not rolled back, so ids
minted by a failed attempt are abandoned rather than reused (BC §2 invariant 7).
A failed call's collected lookup dependencies never reach staging (§3.4).
There is no snapshot/restore primitive.

### 7.5 Guard discipline — hold one table guard at a time

`SymbolTables::get` hands out a per-shard `DashMap` guard; cluster staging hands
out a `RefCell` borrow. A lookup that follows a chain — an import hop, a trait
reference to its home, an import collection feeding a write — **clones the entry
out of the first guard, drops it, and only then takes the next.**

Two guards on one shard where one writes deadlock the process; a second borrow of
the staging table panics. Both need a particular module pair or cluster shape, so
a passing suite is weak evidence. Grade: **asserted with a named falsifier** —
nothing in the types prevents holding two guards; the falsifier is a hang or a
borrow panic on an unexercised crossing. `checker.rs::current_symbol_table`
rustdoc carries the rule where the guards are minted.

---

## 8. Error construction (Decision 39)

Every `CheckError::TypeError` carries an `ErrorLocation`.

### 8.1 Producer policy

| Field | Policy |
|---|---|
| `span` | Always, from the offending node (`Span::SYNTHETIC` for synthetic forms). |
| `file` | When the caller supplied it. |
| `fq` | When the error concerns a determinable definition; the formatter uses it to find the per-definition source. |
| `line_col`, `context` | Left `None`; the integration formatter resolves them. |

Batch output renders `file:line:col` from the span; the REPL uses `fq` for an
inline snippet. Warnings follow the same policy.

### 8.3 Type names in error messages

[REPL error presentation §5.3](../../repl/spec/05-error-presentation.md#53-type-error-quality-tested)
requires a type error to name the expected and actual types fully qualified.
Every type rendered into a typecheck message goes through the shared
`render_type` walk with `PrimitiveNaming::Qualified` (mismatch, rigid-variable
escape and occurs-check messages in `unify.rs`); "no impl" messages name the
canonical trait and the fully qualified impl type. The walk and its naming
conventions are `arch`'s
([bounded contexts §7 "Type rendering"](../arch/bounded-contexts.md#7-cross-crate-types-cratescranelisp-types));
do not add a local type printer.

---

## 9. Traits, monomorphisation and ADTs

### 9.1 Traits

- Typecheck emits `ResolvedCall::TraitMethod` for a trait-dispatched call,
  operators included. Where the resolved impl is a primitive operator
  (`Num.+` at `Int`, for example), typecheck substitutes
  `ResolvedCall::BuiltinFn` itself (`traits/dispatch.rs`), because backend has
  no trait knowledge (Decision 43).
- A trait method's single unresolved tail is classified once, at declaration
  registration, as a required return type or a default body
  (`TraitMethodKind`; `s116-method-signature-resolution.md`).
- An `impl` head resolves once to canonical trait identity; minting, keying,
  rollback and enrolment consume that settled product and never re-read the
  written spelling (`qualified-trait-impl.md`).
- `impl$` storage keys are minted only by `trait_impl_key`. The written-impl
  record is built from the values the impl shell is built from, inside
  `register_trait_impl`'s transaction, and upserts per `(type, trait)`
  ([trait implementation](traits.md#3-trait-implementation).0.1; `design/arch/trait-impl-cache-carrier.md`).
- Impl existence is one keyed probe at the trait's resolved home, keyed by
  the receiver's canonical identity
  ([receiver identity](#911-impl-existence-is-keyed-by-the-receivers-identity);
  [dispatch roots](traits.md#701-dispatch-roots-at-the-methods-home-spec-7112)).
  Bare-name-rooted predicates live only in `checker/test_support.rs`, behind
  `#[cfg(test)]`, with their chain-follow unit cells. Production callers use
  the resolved identity; they cannot call these test predicates.
  The former module-specific and read-view predicates are deleted.
- A deferred trait call retried from settled state that reaches a concrete type
  with no impl propagates the located no-impl error naming the owning trait; a
  nullary return-dispatched method pinned to a type without an impl is rejected
  this way, not at codegen. A caller of `try_resolve_trait_method` that discards
  its error needs a fenced reason. The only one is the auto-curry re-attempt in
  `program/mono_collect.rs`, which falls back to builtin resolution; its no-impl
  face is fenced by `tests/trait_method_noimpl_swallow_siblings.rs`.

`traits.md` carries the subsystem; `hkt.md` the constructor-variable path.

#### 9.1.1 Impl existence is keyed by the receiver's identity

Status: **implemented, independently reviewed and QA-adequate 2026-09-27.**
The final workspace run passes this surface's evidence. It corrects the confirmed
defect BN-1
(`tests/spec_07_traits.rs::impl_for_same_named_type_in_another_module_does_not_satisfy_trait_neg`).
The former home-rooted step scanned the trait's home and compared each
shell's bare type name, so `m`'s impl for `m/U` also satisfied `main/U`.
The permanent regression now rejects that program during typechecking.

**Requirement.** A type's identity includes its home module (spec §8.1,
§3.8.4), and an impl is for that one type (§7.3). Decision 47 permits bare-name
recognition only for the built-in scalar types
([interfaces](../arch/interfaces.md), "Resolved-stage type identity").

**Rule.**

- *Receiver identity.* One crate-private derivation maps a settled type's head
  to its canonical `FQTypeName`:
  - an ADT gives its own `FQTypeName`, with its arguments dropped (the
    registration grain, [mangling](traits.md#31-mangling--mangle_trait_method));
  - a built-in scalar gives its identity in the synthetic `primitives` module,
    where bootstrap installs it (spec §8.9.1). Principle 19 permits the literal
    at this construction site;
  - any other head has none. Each route keeps its own classification of those
    heads.

  Any bare name the crate still reads (for the primitive short-circuit or a
  diagnostic) is this identity's `name`, not a second classification.
- *Probe.* Impl existence is the binding at
  `trait_impl_key(receiver, trait)` in the trait's home, read through the
  staging-aware keyed probe. It returns the shell, so existence and
  `impl_module` come from one read. The home is never scanned, and
  no route matches by bare name.
- The probe accepts only an `FQTypeName`, so a bare-name caller does not
  compile.

**Routes.** Every production route to impl existence uses the derivation and
the probe:

| Route | Site | Unchanged |
|---|---|---|
| Call-site dispatch | `traits/dispatch.rs`, method resolution | Deferral on a non-nominal head; the no-impl diagnostic |
| The shared satisfaction step (§9.2.1) | `traits/dispatch.rs::trait_satisfaction` | Its head classification. Its callers, the declared-bound check and `verify_constraints`, need no change |
| Candidate trials | `candidate_selection.rs` | A non-nominal head stays viable ([candidate trials](use-site-candidate-selection.md#53-isolated-candidate-trials)) |
| Value-position trait annotation | `infer.rs::infer_annotate` | Its function-head and variable-head arms and messages (§11) |

**What the correction removes.**

- Dispatch re-resolved a scalar's bare name in the trait's home to build its
  `FQTypeName`. The pre-fix module cell with a home-local ADT named `Int`
  observed a wrong rejection: `unknown type Int (from module test)`.
  The derivation replaces that re-resolution; the cell now dispatches to
  the scalar's implementation. The unused type-in-module lookup is deleted.
- The bare-name fallback that read `impl_module`, and its degrade to
  `current_module`, are deleted. The dispatch mangle's `FQTypeName` is the
  receiver identity.

**Considered.**

- Keep scalar re-resolution in the trait's home: rejected. It re-derives an
  identity the type already carries (Principle 24) and produced the confusion
  above.
- Put the derivation on `Type` in `cranelisp-types`: rejected. It would change
  the public API for one consumer crate. Potential extension: move it through
  `arch` and the user gate when a second crate needs this identity.
- Change the shell key: rejected. That changes the persisted key, and the
  registration side is already correct.

**Not changed.** Public API, persisted shape and cache schema. Impl registration,
the `impl$` key and the mangle grammar. The trait side of the key: every route
already supplies the trait's resolved home. The renamed-trait lead in §11 is
unaffected. The bare-name-rooted predicates of §9.1 are test-only.
The primitive short-circuit's keying and the no-impl renderers stay open
([traits open items](traits.md#11-open-items); §11).

**Grade.** *An impl satisfies only its own receiver type*: **structural** for
the routes, because the probe accepts only an `FQTypeName` and has one key
constructor. The scalar derivation must equal the identity that registration
resolves. That is **measured** by
`crates/cranelisp-typecheck/src/traits/dispatch/tests.rs::dispatch_mangle_equals_definition_writeback_key_lockstep`
at `Int`. In the suite, a mismatch would appear as a new no-impl rejection, not
as a silent acceptance. The bare-name test predicates are structurally
excluded from production by `#[cfg(test)]`.

Review notes that `Float`, `Bool` and `String` rely on the full suite for
registration/dispatch alignment; the module lock-step cells exercise `Int`.
Potential simplification: derive registration and dispatch identity through
one function. This is a design lead, not part of the delivered correction.

**Open review leads (not executed or accepted as residuals).**

- The no-impl renderer can re-resolve a bare type name to the wrong home.
  Falsifier: a caller importing `a/U` dispatches a trait at a `b/U` value and
  receives a diagnostic naming `a/U`. The dispatch site already holds the
  receiver identity. This is the renderer issue retained above, not a failure
  of the keyed existence probe.
- Two unused enumeration pairs in `checker.rs` retain bare-name shell scans:
  the `get_impls_for_type_with_state` and `get_implementing_types_with_state`
  entry points and their module helpers. They have no production consumer;
  review recommends removing the speculative helpers when this surface is
  next changed. They are not the production existence routes graded above.

**Evidence delivered** (`dev`, module; confirmed in the final workspace run):

- The shared step, as a twin: `a/U` has an impl and same-named `b/U` has none.
  `a/U` is satisfied and `b/U` is not.
- Scalar and ADT twins, in both directions:
  - an impl for an ADT named `Int` does not satisfy `Int`;
  - an impl for `Int` does not satisfy that ADT.
- Dispatch at `b/U` gives the located no-impl error, not a resolution to
  `a/U`'s writer.
- The trait home declares its own unimplemented ADT named `Int`, and `Int` has
  an impl. `(tr 5)` dispatches to that impl's `…$primitives/Int` symbol.
- One twin each for the candidate-trial and value-position routes. Each route
  supplies its own type to the derivation, so each needs a twin.
- Detection: seven module cells were RED on the original code and GREEN
  after correction, with their accepted legs preserved. Under QA's RED-first
  allocation, no equivalent bare-name matching plant was repeated.
- The BN-1 e2e cell is GREEN, and its control stays GREEN.
- The alias-target annotation fixture now installs intrinsic `Int` in
  `primitives` and imports it into its trait module, matching production.
  Independent review confirms that its original lookup subject is preserved.

### 9.2 Constraint propagation (Decision 19)

`generalize` collects trait constraints from active type variables into
`Scheme.constraints`. A constrained function is a template whose concrete bodies
are produced by call-site monomorphisation.

#### 9.2.1 Declared bounds are discharged at settlement

Status: **implemented and committed; AD-6's clause-arm rejection cell is
delivered.** It corrects the confirmed defect DB-1
([intake](../../tests/plan/s122-evidence-delta.md#declared-bound-not-checked-at-the-call-site--intake-2026-09-26)).

**Requirement.**

- Spec §3.9.2 restricts an annotated parameter to types that implement the
  trait, and a stacked bound is a conjunction.
- §3.3.2 makes a constraint a claim that the compiler checks and the caller
  relies on.

**Why the mint alone does not discharge it.**

- Within one cluster, a constrained definition keeps its un-generalised Pass-1
  signature. A same-cluster caller therefore pins its parameter variables
  through the shared substitution (spec §3.5.2;
  `program/body.rs::determine_fn_state`).
- When a caller pins a declared-bound variable to a concrete type,
  generalisation drops the bound, because the variable is no longer
  quantified. The definition then settles concrete, and no instance is
  minted, so `verify_constraints` never runs.
- A bound the body uses is caught by the deferred dispatch at the pinned
  type, located in the body. An unused bound has no other check.
- A caller in another cluster instantiates the published template, and the
  mint verifies its instance at the call site.

**Rule.**

- After the cluster's substitution settles, check every declared parameter
  bound of every registration in the cluster's body ledger against that
  parameter's settled type, through the shared satisfaction step below.
- The check runs after multi-signature variant settlement and before the first
  monomorphisation window ([monomorphisation §3.3](monomorphisation.md#33-the-driver-and-its-settlement-windows)
  step 6): `program/finalize.rs::check_declared_bounds`, called from
  `finalize_check_result_inner`. It records nothing (Principle 26).
- Visit registrations in ledger order, which is source order, and each
  registration's bounds in parameter order and then in written order. The
  first failure, which is the one reported, is then deterministic.

**Carrier.**

- Pass 1 records a registration's declared bounds on its ledger registration
  (`RegisteredBody.declared_bounds`). It writes them from the same resolution
  that seeds the active constraint (§3.5, §7.3.2). The trait-impl fast path
  records none (see Grade).
- The check reads that record, not `CheckState`'s active constraints. Those
  are reset to the Pass-1 snapshot before each body, and at finalize they
  still hold the last body's instantiation residue, so their content depends
  on processing order.

**Shared satisfaction step.** One crate-private step,
`TypeCheckEnv::trait_satisfaction` (`traits/dispatch.rs`), judges whether a
settled type satisfies a trait, by the type's head:

- A nominal head, a scalar or an ADT, satisfies the trait if and only if the
  trait's home holds an impl shell keyed by that head's identity (§9.1.1).
  Every shell is written to the trait's home.
- A function head never satisfies a trait, whatever its arguments: the
  impl-target grammar (spec §7.3) admits no function type.
- A variable or constructor-variable head is undetermined.

The declared-bound check and `verify_constraints` both call this step.

- In the declared-bound check, a still-variable parameter is undetermined and
  is skipped. Generalisation lifts its bound into the scheme, and the mint
  verifies each instance.
- `verify_constraints` sees only concrete signatures. Through the shared step
  it rejects a cross-cluster call of `(defn f [:Ts x] …)` at a function type,
  at the call site. That is the other route's face of the same requirement.

**Failure.**

- The error is the located no-impl error, extended with the declaration:
  ``no impl of trait <FQ trait> for type <type> (declared bound of parameter
  `x` of `f`)`` (§8.3). The settled type renders through `render_type`, so a
  parametric ADT shows its arguments.
- It is located at the declaring registration's span. A multi-signature
  clause's registration span is the clause's own. Its error names the authored
  family, never the internal clause name.
- The pinning call site is not located, because finding it would need a scan
  of the cluster's call sites (Principle 24). Potential extension: locate it
  there if the REPL error-presentation spec or a user ruling requires it.

**Diagnostics that do not move.**

- Deferred-dispatch re-resolution (monomorphisation §3.3 step 1) runs first.
  A bound the body uses therefore keeps its body-located error.
- A cross-cluster call keeps the mint's call-site error.

**Unchanged.**

- Generalisation, and the same-cluster monotype rule.
- Rigid seeding ([inference](inference.md)).
- Candidate selection's trial constraint filter, and the value-position
  satisfaction check (see §11). Both use the same keyed impl probe (§9.1.1),
  but neither uses this step's head classification.

**Grade.** *A declared parameter bound holds at every concrete type the program
gives the parameter*: **measured**. The same-cluster route is measured by this
check, through DB-1 and the module cells with their detection proof. The
cross-cluster route is measured by the mint verification. Falsifier: a
declared bound pinned by a route that is neither in the body ledger nor
minted. None is known; an impl method checked at Pass 1 with a declared bound
on its own parameter would be one.

**Evidence.**

- E2E: DB-1 (`tests/spec_03_types.rs::declared_trait_bound_is_checked_at_the_call_site`),
  GREEN on all six legs.
- Unit cells in `crates/cranelisp-typecheck/src/program/finalize/tests.rs`:

  | Cell | Subject | Result |
  |---|---|---|
  | `declared_bound_pinned_in_cluster_without_impl_rejected_at_definition` | `(defn f [:Ts x] 7)` and a same-cluster caller at `U` | Rejected at `f`, naming the FQ trait and type, the parameter and `f` |
  | `declared_stacked_bound_second_member_unsatisfied_rejected` | Stacked bound, second member unsatisfied | Rejected, naming that member |
  | `declared_bound_pinned_in_cluster_with_impls_accepted` | Caller at `Int` with both impls | Accepted |
  | `declared_bound_without_caller_stays_constrained_template` | No caller | A constrained template; nothing rejected |
  | `declared_bound_pinned_to_parametric_adt_without_impl_rejected` | Caller at `(Option Int)`, no `Option` impl | Rejected, rendering the arguments |
  | `declared_bound_pinned_to_function_type_rejected` | Same-cluster caller at a function type | Rejected |
  | `declared_bound_cross_cluster_caller_rejected_at_call_site` | Discriminating control: `f` in a committed earlier cluster, the caller at `U` in a later one | Rejected by the mint at the call site; GREEN before the fix, so the defect is cluster-local pinning |
  | `declared_bound_cross_cluster_function_type_rejected_at_call_site` | Cross-cluster call at a function type | Rejected by `verify_constraints` through the shared step |
  | `declared_bound_on_multi_signature_clause_satisfied_in_cluster_accepted` | Sibling self-calls pin two clauses at types satisfying their respective bounds | Accepted; both bounded clauses are concrete |

- Five cells were RED before the change; the accepted, template and control
  legs were GREEN. Detection proof: discarding the check's result failed the
  four same-cluster rejection cells, and the accepted, template, control and
  cross-cluster function-type and multi-signature positive cells stayed silent; reverted.
- RQ-1's multi-signature positive cell is GREEN and joined the silent leg of
  the detection proof. The HKT cell followed its allocated stop rule: no
  supported parameter syntax binds a constructor variable (spec §7.8.3).
  Finding-scoped review accepted it, and `qa` retired the HKT cell.
- **AD-6:** `declared_bound_on_multi_signature_clause_unsatisfied_in_cluster_rejected`
  in the same file is GREEN. Only a
  rejected program reaches the arm that names the authored family.
  - Subject: the multi-signature world with clause 1's bound changed from
    `:Tr` to `:Ts`.
  - Required: rejected, naming `test/Ts`, `test/U`, parameter `x` and `f`,
    not the internal clause name. The location must lie within `f`'s
    definition.
  - Detection is already recorded: under the discard mutant, the program was
    accepted ([QA allocation](../../tests/plan/s122-evidence-delta.md#corrections)).
    The permanent cell reuses that detection evidence.
- RQ-2's super-import fixture now supplies its required `Eq Int` impl. The
  missing-impl contrast was RED, and the repaired fixture GREEN; its D4
  resolution subject is preserved. Finding-scoped review resolved RQ-2.

### 9.3 Monomorphisation

No non-concrete type reaches codegen under any reachable instantiation:

- A callable is a codegen target only as `Life::Concrete`; a non-concrete
  definition is `Life::Template` and carries no slot
  (`design/arch/symbol-table-lifecycle.md`;
  `design/backend/non-concrete-release-contract.md`). Typecheck consumes the
  settlement funnels and has no local slot gate
  (`non-concrete-producer-obligations.md`).
- Instances come from one reachable-instance worklist seeded from roots, keyed by
  the complete concrete substitution; each instance is named by the one encoder
  `InstanceLink::instance_key` (`monomorphisation.md` §3.3, §3.5;
  `result-context-specialization.md`). No second mangle grammar.
- A polymorphic product-accessor instance is re-synthesised from its template
  recipe, never produced by re-checking a body.
- A residual type in a codegen view may be defaulted only under the licence in
  `non-concrete-producer-obligations.md` §3.2; otherwise the ambiguity backstop
  refuses it at a located position (`monomorphisation.md` §4).
- Reload demands carry `Span::SYNTHETIC`; a stale demand declines to a warning
  (`monomorphisation.md` §3.8).

`CheckResult` carries no instance list: instances are ordinary concrete
callable bindings published through staging, and `MonoDefn` is a plain
`Defn` wrapper.

### 9.4 ADT typing

`TypeDefInfo`, `ConstructorInfo` and `FieldInfo` describe registered ADTs;
patterns infer by unification with nominal constructor resolution, and
exhaustiveness is checked in `adt.rs` (`adt.md`). Explicit type parameters and
field types are enforced by frontend before typecheck (`spec/05-definitions.md`
§5.2.4); typecheck adds no declaration-shape reject and owns only named-type
resolution. Product types generate accessors named canonically `Type.field`;
bare `field` is a candidate for that spelling, selected at each use
(`fixme-0365-field-accessor-dotted.md`); sum payload labels generate none.

### 9.6 Multi-signature definitions and auto-curry

A multi-signature `defn` produces one entry per signature. It is inference-
equivalent to its clauses as separate mutually recursive functions
(`spec/05-definitions.md` §5.1.2; `monomorphisation.md` §11), and each
constrained clause follows the ordinary template path. Private clause labels
select declarations; executable identity is the authored family plus its full
concrete signature. Auto-currying and its drain seams are in `auto-curry.md`.

### 9.7 Record from settled state (Principle 26)

Every span- or entry-keyed carrier this crate produces is derived once from the
state its settlement window guarantees, never recorded early and patched. The
resolution carriers meet this: each verdict is written at its resolution seam
or settlement point, and the `Apply` verdict is order-independent
([recording the verdicts](ast-annotation.md#21-recording-the-resolution-verdicts)).
One standing, tripwired re-derivation remains (`overload_homes`,
`monomorphisation.md` §11.8.9).

The same classification over the rest of the producer surface — callees,
codegen views, pattern constructors, deferred self-call dispatch, scheme
write-backs — has not been done; it is the open typecheck leg of the Principle 24
classification kept among QA's [unresolved leads](../../tests/plan/PLAN.md#active-allocation-and-unresolved-evidence),
under the carve-outs and corollary of [Principle 24](../arch/principles/24-resolve-once.md).

### 9.8 Module aliases

Typecheck follows `ModuleAliases`; it never populates them. Qualified-name
normalisation passes the referring module to `substitute_module_alias`; typecheck
never walks alias segments or spells an alias key itself, fixtures included
(`design/arch/module-alias-scoped-lookup.md`).

---

## 10. Document map

| Subject | Document | Standing |
|---|---|---|
| Inference and substitution | `inference.md` | Current |
| Use-site candidate selection | `use-site-candidate-selection.md` | User-approved; implemented |
| Checked-body ledger and publication | `checked-body-publication.md` | User-approved; implemented |
| Traits: registry, impls, dispatch, defaults | `traits.md` | Current |
| Method-tail classification | `s116-method-signature-resolution.md` | Implemented |
| Canonical trait identity at `impl` | `qualified-trait-impl.md` | Implemented |
| Higher-kinded traits | `hkt.md` | Current |
| Monomorphisation, reload demands, ambiguity backstop, multi-signature back-flow | `monomorphisation.md` | Current |
| Complete-substitution specialization identity | `result-context-specialization.md` | Implemented |
| Non-concrete producer obligations | `non-concrete-producer-obligations.md` | Current: the funnel, one instance identity, accessor re-synthesis and residual-parameter defaulting |
| Return-polymorphic dispatch signal | `return-poly-dispatch-signal.md` | Implemented (`CheckResult.unresolved_dispatch`) |
| `TypeExpr` resolver convergence | `type-expr-resolver-convergence.md` | Implemented |
| ADT typing | `adt.md` | Current |
| Field accessors | `fixme-0365-field-accessor-dotted.md` | Current |
| Dotted constructor registration | `dotted-ctor-registration.md` | Current |
| Auto-currying | `auto-curry.md` | Current |
| AST annotation, resolution carriers and publication | `ast-annotation.md` | Current |
| IO typing | `io-types.md` | Current |
| Importable-symbol signature match | `signature-match.md` | Current |
| Ownership inference | `ownership-inference.md` | Current; governed by `design/arch/ownership-inference.md` |

The `program/` and `traits/` cuts are §3.1 and the finalize ordering is
`monomorphisation.md` §3.3. Deleted records and where their content now lives
are listed in `design/typecheck/CLAUDE.md` §"Redirections".

---

## 11. Open design items

- **Exhaustiveness internal-constructor fallback.** After a canonical member-key
  miss, `crates/cranelisp-typecheck/src/adt.rs::check_exhaustiveness_in_module`
  still scope-resolves the
  constructor spelling. Its default `internal = false` is correct for current
  product constructors. Falsifier: an `internal: true` product constructor
  with a contested spelling; users cannot construct one today. Convergence
  can use the raw-key fallback already used by `instantiate_ctor`.

- **Principle 26 classification of the remaining producer surface** (§9.7).
- **Declaration-level forward reference within a cluster.** Spec §5.13.1 and
  §8.10.4 let non-macro definitions, including impls, reference types declared
  later in the cluster. Pass 1 registers in form order (§5.2 item 2), and
  `tests/spec_09_macros.rs::macro_expanded_begin_impl_neg_before_deftype_is_rejected`
  requires an impl expanded before its `deftype` to be rejected, citing spec §9.6
  and §8.2. The spec text and that test disagree, and this design takes neither
  side. `spec` owns the reconciliation and `qa` the intake; typecheck's design
  follows the ruling. (Source-read and test-read lead; not executed here.)
- **A type position naming a present but non-terminal module** (§7.3.1): a
  cycle or in-flight load through a type-only reference (spec §8.5.4 edges
  6–7). It fails as "unknown type", not as the value path's member-absent gap.
  The trigger is a failing cell of that shape.
- **A qualified trait in an impl's trait or constraint slot whose module is
  not loaded.** Spec §8.6.1 requires the module to be loaded, or an
  unknown-module error (§8.6.6 step 5), for every kind of name. The slot
  resolves through `resolve_trait` and returns a located error with no gap.
  This is a source-read lead, not executed and not allocated. The trigger is a
  failing cell. The repair would project the failure through the §3.5 stacked
  bound's step; no new gap variant is needed, because the `Type` gap only
  requests a load (§7.3.2).
- **The internal-constructor gate reads a qualified pattern's bare name.**
  `check_constructor_pattern` first asks whether the name, with its qualifier
  removed, names an internal constructor in the current module's scope. It
  does not use the constructor that §3.5 resolves. A qualified `(m/Bind v)` of
  an ordinary constructor could therefore be rejected because the prelude's
  internal `Bind` is in scope. The resolved constructor's origin already
  carries the flag. This is a source-read lead, not executed. The trigger is a
  failing cell.
- **A private qualified member yields a generic miss, not a visibility
  error.** `resolve_qualified` returns a visibility violation as `Err`, but
  its only production caller, the §3.5 walk, discards it; only unit tests
  observe that arm. The behaviour predates §3.6. Decide whether to surface
  the visibility error or collapse the channel. Source-read (S122 review
  AD-2), not executed.
- **One no-impl diagnostic has two type renderers.** The §9.2.1 check renders
  the settled type through `render_type`. The nominal face of
  `verify_constraints`, and the dispatch no-impl error in
  `traits/dispatch.rs`, instead re-resolve the bare type name in the caller's
  scope (`fq_type_name_for_diagnostics`), which drops type arguments and falls
  back to the bare name when the type is not in scope, contrary to §8.3. The
  same requirement at the same type can therefore print differently by route.
  Decide whether to converge on `render_type`, which changes existing message
  text. Source-read (S122 review AD-4). One instance was observed: DB-1's
  cross-cluster leg X1 renders `main/U` as bare `U`. §9.1.1 leaves these
  renderers unchanged.
- **The value-position satisfaction check differs on a function head.** It
  rejects only a fully concrete function type, while §9.2.1's shared step
  rejects any function head. When the value check's head classification next
  changes, or a cell accepts `:Tr` on a function with a residual variable,
  converge it onto the shared step. §9.1.1 changes only its nominal arm.
- **Candidate trials treat a function head as viable.** The trial filter
  passes any head without a nominal identity. So a trait obligation settled
  at a function type does not eliminate the candidate, although
  [candidate trials](use-site-candidate-selection.md#53-isolated-candidate-trials)
  make a concrete unsatisfied obligation incompatible. Changing this could
  change which candidate a use selects. It is a source-read lead and has not
  been executed. The trigger is a failing cell. §9.1.1 keeps the current
  behaviour.
- **Some bare type positions do not filter to type candidates.** Spec §8.6.5
  rule 2 keeps only types in a type position, and `resolve.rs` does
  (`resolve_type_candidate`). `resolve_type`, `concrete_type_for_impl_target`,
  the two impl-target arity checks in `traits/impl_check.rs` and the
  scrutinee-in-scope gate of `check_constructor_pattern` instead take the
  single-terminal scope resolve. A type whose spelling another type's
  constructor shares is therefore predicted to be ambiguous there, for example
  as an impl target. The arity checks and the gate discard the error, so they
  would skip a check or fall through to candidate selection rather than
  reject. This is a source-read lead (S122, ACT-1002 assessment), not
  executed. The trigger is a failing cell; the repair would route these
  readers through the type-filtered candidate resolution.
- **A trait reached through a renamed import** (spec §8.3.5). Both
  type-or-trait routes (§7.3.2) and the stacked bound (§3.5) pair the resolved
  home with the spelled name. A renamed trait would therefore get
  an identity that does not exist. This is a source-read lead, not executed.
  The trigger is a failing cell.
- Subject-level open items are in their subject documents: [trait open items](traits.md#11-open-items),
  `inference.md` §6 and [checked-body open items](checked-body-publication.md#10-open-items),
  for example.
