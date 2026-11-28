# Sprint 125 — the binary clean and green

Designs for the S125 `src/` focus band, by `design`(int), Phase 3,
2026-11-26. Source was read at `main` `4c844f62`; nothing here is in source.
The scope is `sprints/SPRINT.md` §Scope and §Architecture review. Defect
identifiers are rows of the
[S124 evidence delta §14.15](../../tests/plan/s124-evidence-delta.md#1415-defects-carried-by-failing-tests).

## Overview

Every defect in the band is binary-internal except opaque `IO`, which
realises `arch`'s row IO-T: `IO` has no constructors, and `primitives/pure`
is a host-promised built-in (§1). The other designs share one theme: each defect is a second
derivation of something the binary already decides once elsewhere. Each
design deletes the second derivation instead of guarding it
([Principle 07](../arch/principles/07-single-source-of-truth.md),
[Principle 11](../arch/principles/11-single-pipeline-mode-parameters.md)).

| § | Item | Second derivation removed | Inter-crate change |
|---|---|---|---|
| 1 | Opaque `IO`: 1105, 1106, 1108 | three seeded constructors and a name-keyed gate, replaced by no constructor and a host-promised `primitives/pure` | IO-T (re-decided 2026-11-26) |
| 2 | `/type`: 1089, 1099 | a private parse-and-check that publishes, replaced by the turn's own expand and staging check, stopping before publication | none |
| 3 | Display: 1062, 1109; an `IO` payload (`s125_io5_double_display`) | pairing by first appearance (D-1); two marker sites; a result-owner refusal that duplicates a one-hop projection | D-1 only |
| 4 | Persistence: 1068, 1101, 1005, 1102; the S125-Q5 refusal | a non-exhaustive section selector; kind-grouped order; a cache written regardless of the file; a macro origin inferred from spans | none |
| 5 | Loading and search: 1096, 1100, 1092, 1079 | twelve child-path searches; a second qualification pass; a skip that reads as complete; an owner rule the cycle walk has and the loader lacks | none |
| 6 | Commit planning 1090; the 1087 cost (**left S125** with the trace deferral) | a publication check newer than the table it reads | none |
| 7 | Filings: ACT-0965, ACT-1060, ACT-1093, FIXME 0863, FIXME 0889 | — | none |
| 8 | The macro clause's trap guard (F2) | a second writer of the process's trap dispositions, deleted | none |

Out of S125: defects 1087 and 1090 and ACT-1093 left the sprint with the
trace deferral (user, 2026-11-26). Their analysis in §6 and §7 stays as the
design for the sprint that takes trace work.

Changing order: §4's three `save.rs` changes land as one ordered change-set
(selector first). §4.4 shares §4.2's record carrier and lands with it. §1 follows `arch`'s build order without step 4. §1's
display arm (§3.2) must land before IO-T's step 3. Everything else is
independent.

## Open questions

- **For the user, not blocking (§8.5, S125-Q12).** What the compiler owes
  when macro clause code raises a trap that no specification clause governs.

- **For the user, when trace work is scheduled (§6.2).** ACT-1087: fix at
  the cost stated, or keep the residual. `design`(int) recommends keeping
  it.
- **For `spec`, not blocking:**
  - §4.2: whether to refuse a hand-written file `begin`, which is §9.6's
    SHOULD error. Today's leniency is kept, and refusing it would be a
    separate change.
  - §5.3: a dependency indexed privately drops its `defmacro` forms, so a
    module that imports a macro by name is indexed only when the macro's
    module is loaded or cached. Whether §17.19's expansion allowance covers
    this is `spec`'s call.

## 1. Opaque `IO` (1105, 1106, 1108)

Row IO-T ([interfaces](../arch/interfaces.md#opaque-io-row-io-t)), as
re-decided on the user's position on 2026-11-26, says `IO` has no
constructor entries, like `Vec`. `primitives/pure` is a host-promised
built-in typed from its signature, as `bind` is, and the backend builds the
`Pure` node directly. Typecheck's half (1107, the gate deletions) is
`design`(typecheck)'s, and the `pure` lowering and schema walk are
`design`(backend)'s.

### 1.1 What the bootstrap seeds

`src/bootstrap.rs` changes as follows.

- **`register_io_type`** installs `IO` as `TypeRecord::Defined`, with type
  parameter `a`, the docstring "Deferred IO computation tree" and an empty
  constructor list. The binding is installed directly: there is no
  constructor recipe for `build_adt_entries` to derive.
- **Deleted:** `Pure`, `Effect`, `IO.Bind` with its scheme and synthetic
  body, the `TypeDefInfo` extension, and the bare `Bind` exposure. No
  `IO.*` key and no bare `Pure`, `Effect` or `Bind` remain in any table. So
  every user spelling of a constructor is undefined: bare, qualified,
  dotted, scrutinee-picked or imported. That is structural, with no gate to
  forget.
- **`primitives/pure`** is seeded with `insert_primitive`, beside `bind`
  (step 6). It has scheme `∀a. (Fn [a] (IO a))`, parameter `x` and the
  docstring "Lift a value into IO". `insert_primitive` installs it through
  `install_host_promised` as a public `RustPrimitive` with no body and no
  slot. Typecheck types it from the scheme, and the backend lowers it inline
  (row IO-T; `design`(backend)). It is an ordinary first-class function
  (§10.2.3).
- **`SynthCtor`** loses `internal`, and `register_synth_adt` stops passing
  the flag to `AdtCtorSpec::new`. `Option`, `Pair` and `Result` are
  otherwise unchanged, and their constructors carry their type's
  visibility.
- **`src/redefine/type_structure.rs`**: `ctor_shape` stops reading the
  removed flag, and `CtorOrigin` loses the field. Under the row every
  constructor's visibility is its type's, so no comparison is lost.
- **Exposure census.** The bootstrap then seeds no public alias at all. The
  comments that name "ONE intra-module public self-alias"
  (`primitives/Bind`) are corrected: `bootstrap.rs` above
  `mount_synthetic_modules`, and the bootstrap legal-skip in `imports.rs`.
  The census test
  `bootstrap::tests::bootstrap_public_candidate_exposures_are_self_aliases_or_private`
  still guards the class.
- **The residual, measured.** The row's one residual is a bootstrap that
  seeds an `IO` constructor again. A bootstrap unit test asserts, after
  `mount_synthetic_modules`, that `IO`'s `TypeDefInfo` has an empty
  constructor list and that the `primitives` table has no key beginning
  `IO.`. It needs a detection proof: it turns red against today's bootstrap.
- **Fixtures.** Test fixtures that build `CallableOrigin::Ctor` drop the
  field. They are in `src/eval.rs`, `src/save.rs`, `src/display.rs`,
  `src/result_owner.rs`, `src/repl/mod.rs`, `src/worker/tests.rs` and
  `src/session_v4/list_classification_tests.rs`. The bootstrap tests that
  read `Pure`, `Effect` or `Bind` change with it.

### 1.2 Other binary readers

- **Value display (1109).** An `IO` value renders `#io` from `Type::is_io`
  before any constructor-table read (§3.2). After step 3 the table is empty,
  so a display that walked it would have nothing to name.
- **`/info IO`** describes `IO` with no constructors, as it describes `Vec`.
  It reads the empty `TypeDefInfo`, so no `/info` change is needed beyond
  the bootstrap. `qa` holds the observation.
- **No other `src/` reader.** No `IO_TAG_*` constant and no `Pure`, `Effect`
  or `Bind` name is read in `src/` outside the bootstrap and its tests, and
  the bind-chain pass reads neither (source search at `4c844f62`).

### 1.3 Order and seams

`arch`'s order (packet §4), without step 4 (trace markers, deferred with
TR-1):

1. **Additive:** `primitives/pure` (the seed above) and its backend lowering
   are added while `Pure` is still public. The binary's half is one
   `insert_primitive` call, and it lands with `dev`(backend)'s lowering.
2. **Consumers move to `pure`.** That is other roles' work. The stdlib's
   `io/monad.cl` re-exports `primitives/pure` rather than defining its own.
3. **The cascade**, one change-set:
   - IO-T in types;
   - the §1.1 removal of every `IO` constructor, the flag deletions and the
     unit assertion, in `src/`;
   - typecheck's deletions;
   - by `dev`(backend): removal of the `ConstrADT` `IO` case, and the schema
     walk treating `IO` like `Vec`. `compute_layout_hash` and
     `generate_schema` keep their signatures and return different values;
     `ABI_VERSION` is unchanged;
   - `CACHE_SCHEMA_VERSION` +1;
   - regenerating both committed schemas that name `IO`, the
     [shapes schema](../../platforms/shapes/src/shapes.platform-schema) and
     the [web schema](../../exemplar/platforms/web/src/web.platform-schema),
     and rebuilding both dylibs, by `dev` in the same change-set.
     `platforms/shapes/` is a test-suite platform under `qa`'s control, so
     `qa` allocates its evidence.

   §3.2's `#io` arm must already be in place. 1105 to 1108 flip here.

The binary's seams are `register_io_type`, the `pure` seed,
`register_synth_adt`, the shape comparison and the display classifier.

### 1.4 Evidence leads for `qa`

- The 1105, 1106 and 1108 cells, and 1107's, which is typecheck's.
- `primitives/pure` applied and as a value: passed to a higher-order
  function and stored, at the REPL, `--run` and linked.
- Every spelling of `Pure`, `Effect` and `Bind` is undefined: bare,
  qualified, dotted, scrutinee-picked and imported, in an expression and in
  a pattern.
- `/info IO` lists no constructors.
- The bootstrap unit assertion above, with its red run against the current
  bootstrap.
- After step 3, a nested `IO` value displays `#io`.
- The shapes and web platforms load and run after the schema change. Their
  regenerated schemas have no `primitives/IO` entry, and an old dylib is
  refused by the layout-hash gate.
- A sidecar written before the bump is a miss.

## 2. `/type` (1089, 1099)

**Mechanism: confirmed and wider than recorded.**

- `src/repl/commands.rs::typecheck_only` builds the raw form and calls
  `worker::check_program_compat_no_gap`. That goes through
  `process_cluster_with_staging`, which runs `commit_staging_to_live` on
  success.
- Every `/type` therefore writes into the live table with no code. A
  definition stays there and faults on its next call (1089). A plain
  expression also leaks its `__expr` into live on every query, and a
  definition query reads back the previous input's `__expr`.
- It never expands macros, so a macro head is an undefined variable (1099;
  now read in source, not only by control).

**The requirement.** repl spec §3 (after the slash-command table) and
S124-Q10: `/type` of a definition form reports an error and defines
nothing. `/type` never evaluates a form.

**Designed change.** `/type` becomes the turn's own per-form steps,
stopping before publication (Principle 11's mode parameter at the
publication boundary):

1. **Expand** through `process_form/macro_resolution.rs::try_expand_sexp`,
   reached through the eval compiler (`eval.rs::with_eval_compiler`). It
   gets the same recognition and hygiene qualification as an evaluated
   turn. `/type` does not load a module: a macro or reference whose module
   is not loaded is a located error, as a dependency gap already is.
   `/expand`'s read-only resolver is not used, because it does not qualify
   and cannot run a macro restored from cache.
2. **Classify.** The expansion must build to exactly one expression. A
   definition form, a `defmacro`, a structural form, or a macro that expands
   to a definition (`def`) is refused with the located "a definition form
   has no type" error.
3. **Check without commit** through `worker::check_cluster_to_staging`,
   which already returns the staged table with nothing committed. The type
   is read from the staged `__expr`, and the staging is dropped.
   `check_program_compat_no_gap` loses its `/type` caller.

No prologue, macro checkpoint, codegen or commit runs. Typecheck already
exposes what this needs. The `arch` trigger in §2.4 of the review does not
fire.

**Evidence leads.**

- The 14 1089 cells and `s124_type_macro_expression`.
- New:
  - live holds no new `__expr` after `/type 1`;
  - `/type (def x 1)` is refused;
  - `/type` of a macro whose home module was restored from cache;
  - `/type` of a reference to an unloaded module is refused and loads
    nothing.
- Unit: the staging check leaves the live table unchanged.

**Usability finding, not designed here.** A dependency-gap error renders
as `{gap:?}`. `dev` may correct it on the same pass.

## 3. Display (1062, 1109)

### 3.1 1062 through row D-1

**Mechanism: confirmed at `4c844f62`, and removed in W2.** The binary's
value display paired type arguments with field variables in first-appearance
order, in a helper that `push_adt_heap_value` alone called and that W2
deleted. No other first-appearance pairing remained in `src/`.

**Designed change.**

- `push_adt_heap_value` resolves the constructor's storage key once,
  through the canonical member key with the product fallback.
- It converts the type arguments to `ConcreteType` and calls
  `cranelisp_types::ctor_field_types_at`, recursing on each field.
- The first-appearance pairing helpers are deleted (done in W2).

**D-1's falsifier holds.** The value is not converted. Only the type
arguments become `ConcreteType`, and that fails only for a residual type,
which §3.11 keeps out of executed values. Polymorphic `None` and `[]` take
`eval.rs`'s display-only path. A failed conversion renders an explicit
internal marker and never a guessed type.

**Evidence leads.** `match_field_parameter_order::s124_1062_e_subject_repl`.
A parameter no field mentions, and a nested out-of-order product, each with
an in-order control. A unit test at `push_adt_heap_value`.

### 3.2 1109, the REPL display only

**Mechanism: located.**

- Both markers are produced in `src/display.rs`. `src/styled.rs` renders
  role spans only.
- A closure renders `<closure>` at two sites, the result document's `Fn` arm
  and `push_field_value`'s.
- Nested `IO` has no arm. It falls into the ADT walk over `IO`'s
  constructor table, which gives `(IO.Pure 1)` today. After IO-T the table
  is empty, so the walk could name no node.

**Designed change.** `push_field_value` is the one per-value classifier:

- an `IO` type (`Type::is_io`) renders `#io`, before any constructor-table
  read, reading no memory;
- a function type renders `#closure`;
- both carry the plain role.

The result document keeps only the `:Type` envelope and takes its value
spans from `push_field_value`, so the top level and fields cannot diverge
(Principle 07). Doc comments and unit tests that say `<closure>` migrate in
the same change-set. Trace output is untouched: it renders in intrinsics,
and TR-1 is deferred.

`int.md` §12.1 reject 17 ("an `IO` branch in a formatter") concerns
release, and the marker makes no ownership decision. The reject's wording is
sharpened accordingly.

**Evidence leads.**

- `s124_markers_closure_display` and `s124_markers_nested_io_display`.
- `[(primitives/sleep 0)]` → `[#io]`, a box holding `pure 1`, and
  `(Option.Some f)` → `(Option.Some #closure)`.
- Migrate `closure_value_display_shows_closure_token`.
- The top-level double-`pure` case (§3.3).

**Side observation.** `push_adt_value_form` recognises `Vec` by bare name.
That is a [Principle 19](../arch/principles/19-no-module-privileged-by-name.md)
exposure: a user type named `Vec` would misrender. It is a lead for `qa`.

### 3.2a Defect B: a field the residual parameter does not reach

**Status: built, uncommitted, and under `review`. Recorded as it stands, not
endorsed.** It repairs Defect B
([evidence delta §30.2](../../tests/plan/s125-evidence-delta.md#302-the-replay-intake)).
The display refused every field of a value when any type argument was
residual. It should refuse only a field whose type mentions the residual
parameter.

**Mechanism as built** (`src/display.rs::ctor_field_types`):

- It instantiates every residual type argument twice through the one rule,
  `cranelisp_types::ctor_field_types_at` (row D-1): first as `Int`, then as
  `Bool`.
- It reads the fields only when the two instantiations agree. A field that
  differs between them has a residual type, and the display then renders the
  explicit marker, as it did before.
- No field is read at a guessed representation. T-RESID-DISPLAY's
  `(primitives/Some [])` control and 1062's cells hold that line.
- It changes no `cranelisp_types` operation, so the `arch` trigger in §30.2
  does not fire.

### 3.3 A program result whose payload is itself `IO`

**Attribution (`qa`, S125 evidence delta §11): confirmed in source.**
- `(primitives/pure (primitives/pure 1))` at the REPL prints the execution
  notice, then the invariant "program result reached the result owner still
  wrapped in (primitives/IO Int)".
- The refusal is the `ty.is_io()` check at the top of
  `src/result_owner.rs::ReleasePlan::new`, which `OwnedProgramResult::new`
  calls.
- The driver forces the outer `IO`. Its word is the inner, unforced
  `Pure` node, and `driver_result_type` (then in `src/pipeline.rs`, now the
  owner's private step in `src/result_owner.rs`) correctly projects the type
  one hop, to `(IO Int)`. The owner then refuses that legitimate payload
  type.
- Repl spec §1.2.1 and §1.5 require it to display `#io`. The control
  `(primitives/pure [(primitives/pure 1)])` displays `[#io]`. The class is
  `check-domain-overreach`: the check guards a second unwrap by refusing
  every `IO` payload.

**Why a second unwrap is already impossible.** Both projections take one
hop and are called once:
- the observed type: `driver_result_type` (`ty.unwrap_io()` when
  `ty.is_io()`), at each driver call site;
- the release key: `release_key`, which takes
  `ConcreteType::result_root()` of the producer's codegen body type
  (`crates/cranelisp-types/src/concrete.rs`). `result_root` strips exactly
  one outer `primitives/IO`.

The `is_io` refusal therefore adds no protection. It mistakes an `IO`
payload for an un-unwrapped program, as `qa` suggested; verified.

**Designed change.**
- **The projection moves into the owner.** `ReleasePlan::new` (and so
  `OwnedProgramResult::new`) takes the program's *static* result type. It
  performs the one hop itself, deriving the observed payload type from the
  static type and the release key from `result_root()` of the codegen type,
  side by side in one function.
- **Callers do not unwrap.** The REPL eval (`src/pipeline.rs`), `--run`
  (`src/session_v4/lifecycle.rs`) and the test runner
  (`src/session_v4/test_runner/run.rs`) pass the static type.
  `driver_result_type` becomes the owner's private step, and its
  `driver_result_type_*` tests move with it.
- **The guarantee becomes structural.** With no caller-side unwrap, there is
  no path by which an already-unwrapped type reaches the owner, so the
  owner's one hop is the only hop.
- **`dev` confirms the test runner's type.** The runner's `read.result_ty`
  is the arm's static result type, so it already fits. `dev` confirms this
  as its first act: if the runner passes an unwrapped type, it passes the
  static one instead.
- **The `is_io` refusal is deleted.**
- **The payload's glue.** An `IO b` payload is an owned reference to an IO
  node and is released like any other owning result, through backend's
  canonical glue keyed by its concrete type.
  - The backend pre-requests glue for `body.ty().result_root()`
    (`crates/cranelisp-backend/src/lib.rs`), here `(primitives/IO Int)`.
  - `drop_glue.rs` gives an `IO` type `GlueShape::Io`, the glue the control
    already uses for a `Vec` element.
  - The owner's resolver finds it under the same key. The outer node,
    forced by the driver, stays the runtime's
    ([result owner](result-owner.md) §4.4). No `IO`-specific release branch
    is added (`int.md` §12.1 reject 17).
- **Display.** The owner's observed type is `(IO Int)`, so the result
  document renders `#io` through §3.2's classifier.
- **The error category.** The refusal surfaced an internal invariant as
  `codegen error at 0..0` for a legal program. Deleting it removes that
  diagnostic for this case altogether; it is not recategorised. The owner's
  remaining invariant (a non-concrete type with no codegen view) keeps its
  internal category, because no legal program reaches it.

**Gate:** none. The change is `src/`-only and uses `result_root()` and the
backend's glue as they are.

**The unit row `dev` writes RED first** (`src/result_owner.rs` tests): plan
a release for a program of static type `(IO (IO Int))` whose codegen body
type is the same. Assert:
- the plan succeeds;
- the owner's observed type is `(primitives/IO Int)`;
- the release target is resolved for the key `(primitives/IO Int)`.

It is RED today on the refusal. Beside it:
- the existing control: a static `(IO String)` plans `String`;
- a negative row: a static `(IO Int)` keys `Int`, never `(IO Int)`, so the
  one hop is taken once and only once.

**Evidence leads.** The e2e cell is `opaque_io::s125_io5_double_display`
(REPL, `#io`). Further leads:
- the same program under `--run`, where the exit code is 0, since the
  payload is not an `Int`;
- the same program as a test body;
- an allocation balance for the payload node's release, through the
  existing result-owner balance harness.

## 4. Persistence (1068, 1101, 1005, 1102)

The cited design is [session persistence](session-persistence.md) §§1.3,
1.4 and 2.4. Its §1.3 order and §1.4 dependency ordering are replaced by
§4.2 when §4.2 lands.

### 4.1 One exhaustive selector (1068, 1101)

**Mechanisms: confirmed** at `4c844f62`; the functions named here were
deleted by the W7 change (§4.5).

- *1068.* The function section (`generate_fns_and_macros`) skipped
  `Decl::Overloaded(_)`. The family's base-name record exists
  (`src/session_v4/types.rs::definition_identity`); only the selection
  dropped it.
- *1101.* The type section (`generate_types`) selected by
  `Binding::type_def_info()`. A minted instance of a product constructor
  keeps the type facet and has no record, so it reported unrendered and the
  whole save was refused. The instance exclusion
  `worker::is_internal_listing_entry` was applied in the function section
  and not there.
- *The completeness guard was vacuous.* Its classifier
  (`section_entry_claimed_or_excluded`) answered true for every `Decl`, so
  the sweep could not fire.

**Designed change.** One exhaustive selector, with no wildcard arm, maps
each binding to *persisted* or *excluded, with its reason*:

- **Persisted:** `Overloaded` (its base-name record and live docstring),
  plain callables, macros, defined types, traits, and a non-instance product
  constructor carrying the type facet.
- **Excluded, before any facet is read:** minted instances (published
  `Life`), constructors without a facet, trait methods, implementation
  shells, special forms and internal names.
- **Implementations** stay enumerated from `written_trait_impls`.

Every generator selects through it. The vacuous guard is deleted: a new
`Decl` variant now fails to compile until it is classified (a structural
grade). Whether an instance should keep the type facet at all is a separate
question about types, not needed here.

**Evidence leads.**

- Unit: one row per `Decl` variant; the function section renders a
  multi-signature family; a minted product-constructor instance (a user
  type and the seeded `Pair`) is excluded.
- e2e: the four 1068 cells and the three `s124_save_after_*` cells, with
  their controls.
- Other readers of `type_def_info()` that may count instances as types:
  a lead.

### 4.2 Authored order (1005)

**Mechanism: confirmed in `save.rs`** at `4c844f62`:

- `generate_module_source` wrote the structural sections in the wrong
  order.
- Traits, types and implementations sorted alphabetically.
- Macros came first, then functions in callee order (`dependency_sort`).
- Imports merged by module.
- Leg a, a redefined member of a shared `begin`, was
  `partial-record-update`: the sibling records still held the shared form.
- The cells' locus token, `multi_definition_record` in `save.rs`, names no
  symbol in source. The writer is the record publication path
  (`eval.rs::record_defining_turn_source`,
  `form_dispatch.rs::record_macro_introspection`). That is a `test`
  notation repair.

**The requirement.** Repl spec §15.4, rules 2 and 4, under the user's
ruling of 2026-11-27: the unit of persistence is the **authored entry**,
identically for a file and the REPL.

**The model.** Every live definition has exactly one owning entry, and
regeneration writes each entry once, in authored order.

- **A written entry** is one written definition form, and it owns that one
  definition. A redefinition by a written form replaces the entry in place.
- **A macro-call entry** is one authored macro call. It owns every key its
  expansion defined, as one unit (§4.4).
- **A structural entry** is one module spec of an `import` (a
  multi-module `import` contributes one per spec), one platform, one `mod`
  or one `export` spec. They are read from the table in its order (§4.6,
  R4).
- **A REPL-entered `begin` is not an entry.** It dissolves at entry into
  its members, recursively. Each member becomes a written entry or a
  macro-call entry at its own place, and an expression member persists
  nothing.
  - The dissolution is persistence-only: the turn still compiles, refuses
    and publishes as one turn, so turn atomicity is unchanged.
  - A `begin` produced by a macro's expansion stays inside that macro-call
    entry.
  - File source admits no hand-written top-level `begin` (spec §9.6,
    S125-Q8), and regeneration never writes one.
- **A legacy backing file holding a `begin`.** Today's file load accepts
  it, as §9.6's SHOULD-level leniency, and this design keeps that
  acceptance unchanged.
  - Such a `begin` reaches the same literal-`begin` walk as a REPL one, so
    it dissolves the same way, with no file-specific branch. Its members
    take file positions in member order.
  - The next regeneration writes them as members, so the file converges
    to conforming source.
  - Refusing a file `begin`, the SHOULD's error, would be a separate
    change in the batch and file-load path, with its own cells. It is
    flagged for `sprint` and `spec`, and not designed here.

**The record.** The authored-form record becomes one record per entry,
keyed by its authored position. A definition reaches its entry through that
position.

- **A written entry** records its own form, with verbatim source where it
  has some. For a `begin` member that is the member's own slice, not the
  outer `begin`.
- **A macro-call entry** records the authored call, the call's identity
  (§4.4) and the keys its expansion generated.
- **Origins** are those of §4.4: `Written` for a written entry's
  definition, `Generated` for each key of a macro-call entry.

**Positions.**

- A file entry takes its file position, the span start of the entry's own
  form.
- A REPL entry takes the next entered sequence, after every file position.
  A `begin`'s members take consecutive sequences in member order.
- A redefinition inherits the position of the entry it replaces. A
  re-entered macro call inherits its entry's position.
- A whole-file rebuild resets every position from the file. A regenerated
  file's order equals the sort, so positions stay stable.
- `process_form.rs`'s `BuiltProgram::position_of` keys a position by the
  form it is given. The literal-`begin` walk gives it each member, not the
  outer form. That walk already treats each member as its own
  source-ordered position.

**The macro-before-use exception** is unchanged.
`SymbolTableMacroResolver` records the same-module macros an entry
recognises while expanding it. On redefinition, if any of them sits after
the inherited position, the entry moves to just after the latest one, and
nothing else moves.

**Regeneration** writes the structural sections first, in rule 4's order.
It then writes every definition entry once, by position. Because no entry
is ever shared, a redefinition never splits anything. The W7 `begin`-split
writer, its shared-position tie-break and its shared-form ledger were deleted,
not fixed (as built: `save.rs::emit_definitions` writes each
position-and-form entry once; §4.5).

R1 and R3 (§4.6) resolve by construction:

- **R1:** a macro call that was a `begin` member is its own entry, written
  once as authored, and `(defn a [] 20)` replaces its own entry.
- **R3:** each member has its own position, so members keep member order.

**Rehydration** ([session persistence](session-persistence.md) §2.4.2)
never meets a `begin` in a regenerated file. A legacy file's `begin` is
dissolved by the walk above at load, so rehydration needs no `begin` case of
its own. The §4.5 gap is unchanged: a cache-restored module keys no macro
call until it is rebuilt (delta §17.4).

**Gate:** none. The record, the dissolution, the positions and the writer
are all in `src/`.

**A shrinking re-entry is refused** (user, 2026-11-27): see §4.4, *A
re-entry that drops a definition*. No entry can therefore lose a key while
the key stays live.

**Unit rows `dev` writes RED first** (`src/session_v4/authored_record_tests.rs`
and `src/save.rs` tests):

1. A REPL `(begin (defn f [] 1) (defn g [] 10))` saves as `(defn f [] 1)`
   and `(defn g [] 10)` in that order, with no `(begin`.
2. A legacy file `begin`, accepted under §9.6's leniency, is dissolved at
   load. Its members' records carry distinct file positions in member
   order, and the next save writes the members with no `(begin`.
3. R1: `(defmacro make …)`, `(begin (make f) (defn a [] 1))`,
   `(defn a [] 20)` saves `(make f)` once and `(defn a [] 20)` once.
4. R3: `(begin (defn z …) (defn a …) (defn m …))`, then a redefinition of
   `a`, saves `z`, `a`, `m`.
5. A macro-call entry records its call and its generated keys. A
   re-entered call replaces that entry in place.
6. A re-entry that would drop a generated key is refused (§4.4).

**Existing tests that assert the old behaviour.** Each writes a `begin`
once as authored, or relies on a member carrying the outer form. `qa`
re-baselines them:

- `tests/repl_persist.rs`:
  - `persist_repl_begin_spanning_sections_written_once`, through
    `assert_spanning_begin_written_once`. The new expectation is that the
    `deftype` and the `impl` are each written once, with no `(begin`, and
    the cold restart still holds.
  - `persist_file_loaded_begin_spanning_sections_written_once` depends on a
    file `begin`, which §9.6 does not admit. It becomes a leniency cell: a
    legacy backing file holding the spanning `begin` loads, and the next
    save writes the `deftype` and the `impl` once each, with no `(begin`,
    and the cold restart still holds. Its trace is spec §9.6's SHOULD
    leniency, not rule 1. If the file refusal is ever scheduled, the cell
    becomes that refusal's cell instead.
  - `s124_1005_a_begin`: its survivors are now members by construction.
    Check that its clauses do not require the `(begin` text.
  - `s125_w7_r1_begin_macro_member_survives_redefinition_and_restarts` and
    `s125_w7_r3_begin_member_redefinition_keeps_order` stand as written.
    They are the e2e for rows 3 and 4.
- `src/save.rs` tests: `regen_literal_begin_multi_defn_emits_once`,
  `regen_repl_begin_spanning_sections_emits_once` and
  `rehydrate_fills_private_heads_and_begin_members_with_outer_form`. The
  last is now a legacy-file case: its members carry their own forms, not
  the outer one. Also
  check `regen_macro_expansion_artifact_emits_authored_origin_once`: a
  macro call is still written once, now as its own entry.
- `src/session_v4/authored_record_tests.rs`:
  `an_unsplit_begin_is_written_once_as_authored` (now dissolved) and
  `a_begin_split_by_redefinition_writes_each_survivor_alone`, whose
  outcome is unchanged but whose mechanism is now dissolution.
- A sweep of `tests/cache.rs`, `tests/repl_lifecycle_matrix.rs`,
  `tests/repl_redefinition.rs` and `tests/spec_09_macros.rs` found no
  assertion on a saved `(begin` text. `qa` should confirm.

**Other evidence leads.**

- e2e: `s124_1005_b_names`, `b_kinds`, `b_redefine` and
  `c_structural_order`.
- Gaps:
  - rules 2 to 4 on a cache-restored module (rule 6, §4.5);
  - file load followed by REPL appends;
  - a macro's redefinition newly using a later macro;
  - a `begin` holding an expression member.

### 4.3 The cache never ahead of the file (1102)

**Mechanism: confirmed in `src/session_v4/lifecycle.rs`.**

- `regenerate_backing_file` updates the stashed source hash and marks the
  module stale only after a successful write.
- It returns early, leaving the stash at the on-disk file's hash, in five
  cases: refused render, write failure, unseen save, the inline-`mod` guard
  and empty source.
- `flush_final_persist` marks modules stale unconditionally. The object
  pass then writes the live table under the old hash, and the next session
  accepts it.

**The invariant.** A module's cache entry is written only from a table that
agrees with the source hash it is recorded under.

**Designed change.**

- The cache writer holds one per-module agreement state:
  - every load and reload read, and every successful regeneration write,
    set it to *agrees*;
  - a definition turn whose regeneration did not write sets it to
    *diverged*, which covers all five early returns.
- Divergence retires the module's object and `.meta` through
  [§7.7](int.md#77-one-generation-beside-an-entry-act-1083)'s retirement,
  and refuses writes until the next agreeing write.
- Object publication reads the state under the lock it publishes under,
  closing the window between a turn's publication and its regeneration.
- `flush_final_persist` needs no condition of its own.

**Residual, asserted with a falsifier.** How the entry restore treats a
decoded definition absent from the source was not read. It is falsified if,
after the fix, a `.meta` listing a definition the source lacks, under a
matching hash, still restores and faults on a call. That would be a second
defect, in the entry preload.

**Evidence leads.**

- Unit: the state's transitions; publication refused or retired while
  diverged.
- e2e: `s124_refused_save_cached_restart_survives_call_and_next_turn` and
  its controls.
- Gaps: a refused save reached other than through 1101 (which closes with
  §4.1); a write failure; an inline-`mod` module with a cached restart.

### 4.4 A macro-generated definition is not redefined (S125-Q5)

**The rulings.** User, 2026-11-26 (spec §9.6.1, appendix D S125-Q5):
- a definition generated by a macro call cannot be redefined by a later
  form, and the redefinition is refused;
- re-entering the same macro call may replace the definitions it
  generates;
- any other form producing a live generated name is refused: another macro
  call, another macro, or a written form;
- a reload whose file no longer holds the call, and defines a formerly
  generated name by hand, is accepted, because the reloaded file replaces
  the module.

**What exists.** Within one compilation unit a second definition of a name
is already refused. Typecheck's `program::BodyLedger::reject_duplicate`
refuses a second definition of one name in one cluster, whatever its
origin. A module file is one cluster, so a file load, a whole-file reload
([session transaction](session-transaction.md) §7.3) and `--run` need
nothing new for a duplicate inside one file. What is missing is the case
across turns: a REPL turn that redefines a name an earlier turn's macro
call, or the file's, generated.

**The origin carrier.** The binary has no structural record that a
definition is macro-generated.
`form_dispatch.rs::record_macro_introspection` infers expansion from a span
difference, and only in REPL mode. So §4.2's authored-form record gains one
origin fact per definition:
- `Written`: the definition is its own authored form, or a `begin` member;
- `Generated`, carrying the generating call's identity (below).

The turn sets it where the expander already knows the form was a
recognised macro call (`try_expand_sexp`), and stages it with the record.
The span inference for `expanded` is then deleted; the record reads the
fact (Principle 24: recorded once, never inferred).

**The call's identity.** Two calls are the same call when both of these
hold:
- they resolve to the same macro: the macro's canonical `FQSymbol`,
  recorded at recognition. Two spellings of one macro (bare through an
  import, aliased or qualified) are therefore one macro, and a redefined
  macro keeps its identity;
- their authored forms are structurally equal with spans ignored, the head
  compared by that resolved identity and every argument by value.

Position is not part of the identity, because a re-entered call is a new
turn at a new position. A re-entry that replaces inherits the original
call's position (§4.2).
- **Falsifier.** The identity is wrong if the ruling's "same macro call"
  is meant to include a call of the same macro with edited arguments, such
  as `(defrecord P [a])` re-entered as `(defrecord P [a b])` to change the
  record. Under this identity that is another call, and it is refused when
  it produces a live generated name. A user report or a `spec` reading to
  that effect returns the identity here. Widening it to the resolved macro
  alone would then admit any call of that macro.

**The refusal and the replacement.** The commit's guarded validation
(`worker.rs::validate_guarded_staging`, ahead of
`redefine.rs::classify_redefinition`) reads, for each definition a turn
stages under a live key whose record is `Generated`, the staged record's
origin:
- `Generated` by the same call: accepted, and the replacement is an
  ordinary redefinition, classified as usual;
- `Written`, or `Generated` by another call: refused.

The rules for the refusal:
- It covers every definition class the turn stages under that key:
  callables, types, traits and implementations.
- The diagnostic is located at the redefining form. It names the
  definition and the macro that generated it; the wording is `dev`'s.
- It is a rejected redefinition, so the live definition and the
  regenerated file are unchanged (repl §15.6).

**A reload replaces the module's origins.** A watcher reload is a
whole-file rebuild (session transaction §7.3). It stages the module's
records afresh from the file, so it replaces every authored-form record of
the module, origins included:
- a call no longer in the file leaves no `Generated` origin behind;
- a name the file now defines by hand is `Written`.

The rebuild's validation reads the rebuild's own staged records, never the
records it replaces, so the reload is accepted. Within the rebuilt file,
the cluster rule above still refuses a duplicate.

**A re-entry that drops a definition is refused** (user, 2026-11-27). An
identical re-entry whose new expansion, after the macro was redefined,
would no longer define a key the previous expansion defined is refused,
naming the dropped definitions. The live table and the backing file are
unchanged.

- **The comparison is per entry, because it is about a set.** The
  macro-call entry already records its generated keys (§4.2). The check
  compares that recorded set with the new expansion's, and refuses when a
  recorded key is missing.
- **It runs once, at the head of the entry.** That is after
  `try_expand_sexp` returns the complete expansion, and before any of its
  members reaches either publication point. A refused re-entry therefore
  publishes no checkpoint and no cluster member.
  - The per-key redefinition check of §4.6 (R2) is the same predicate
    module. It still runs at both publication points.
  - The set check sits ahead of them for every key of the entry.
- **The set is compared before settlement.** The expansion's keys are
  read with the same identity the records use before `impl` identities
  settle (`definition_identity`, and a `defmacro`'s name). The entry
  therefore records its set in that form.
- **Falsifier.** An expansion that spells one `impl` head two ways across
  re-entries, such as an alias and then a qualified name, would read as
  dropped plus added, and would be refused. A cell that shows this,
  through a redefined macro emitting a respelled head, would move the
  `impl` comparison to settled identities at `finalize_cluster`. That
  costs a two-stage check.
- **A re-entry that adds keys passes.** A grown set's new keys are new
  definitions, owned by the entry.
- **The diagnostic** is located at the re-entered call. It names each
  dropped definition and the macro; the wording is `dev`'s.

**Gate:** none. The carrier, the expander's fact and the commit validation
are all in `src/`. Typecheck's cluster rule is used as it is.

**Evidence leads.**
- e2e, REPL:
  - a macro call generating `f`, then a written `(defn f …)` turn, is
    refused at the redefinition; `f` keeps its generated body; the backing
    file is unchanged;
  - the same for a generated type and a generated implementation;
  - a name generated by the file's macro call, redefined at the REPL;
  - control: a `Written` definition redefined at the REPL is accepted.
- e2e, re-entry:
  - the same call re-entered, after the generating function was changed by
    redefining its macro, replaces the generated definitions; the file
    keeps one call at the original position;
  - the same call spelled through another route to the same macro (bare
    through an import, then qualified) is the same call and is accepted;
  - refused: a call of the same macro with different arguments that
    generates a live name; a different macro generating the same name.
- e2e, reload: a file that replaces the macro call with a hand-written
  definition of a formerly generated name is accepted on reload. A
  following REPL redefinition of that name is then accepted, because it is
  `Written`.
- e2e, one unit: a file holding a macro call and a later written definition
  of a name it generates is refused, in `--run`, linked and on reload. This
  is the existing cluster rule, observed with a macro-generated first
  definition.
- Unit (`dev`, RED first): an identical re-entry, after the macro is
  redefined to emit one name fewer, is refused, naming the dropped key.
  Nothing publishes: no checkpoint and no cluster member. The live set and
  the saved file are unchanged. Control: the same re-entry emitting the
  same set, or a superset, is accepted.
- e2e lead: `(defmacro two [] '(begin (defn p [] 1) (defn q [] 2)))`,
  `(two)`, then `(defmacro two [] '(defn p [] 1))` and `(two)` again. The
  re-entry is refused naming `q`; `(q)` stays 2; the file is unchanged.
- Unit:
  - the record's origin is set from the expander's fact; a same-span
    expansion still reads `Generated`, which the deleted inference got
    wrong;
  - call identity: equal across spans and head spellings, unequal on any
    argument;
  - validation accepts same-call `Generated`, and refuses `Written` and
    another call's `Generated`;
  - a rebuild's records carry no origin of a removed call.
- `s124_1005_a_macro` re-baselined to the refusal (§4.2).

### 4.5 As built (W7)

Where the W7 build departs from §4.1–§4.4. The authored-entry model of
2026-11-27 (§4.2) supersedes the W7 `begin`-split path, and §4.6 supersedes
the *Imports* bullet.

- **The refusal's site.** `process_form::refuse_generated_redefinition` runs
  in `finalize_cluster`, after the cluster's `impl` identities settle and
  before anything publishes, not in `worker.rs::validate_guarded_staging`.
  That validation sees the staged table but not the staged records, and an
  `impl` record has no key before its identities settle. It runs only for
  an increment: a whole-file rebuild has replaced the module's records.
- **Imports.** The import merge is kept. Rule 4's section order is built;
  emitting each import form as written needs the authored form on
  `ImportSpec`, which it does not carry.
- **Retirement.** A divergence removes the module's `.o` and `.meta` and
  refuses `.meta` writes and manifest entries until the file agrees. The
  existing manifest entry is kept: with no `.meta` it restores nothing.
- **Gaps left.** A cache-restored module has no records until its first
  regeneration rehydrates them, and rehydration keys no macro call. Until
  then a redefinition there takes an entered position rather than its file
  position, and a generated definition there is not refused.

As built by the W7 correction (§4.2, §4.4, §4.6):

- **The entry record.** An entry is the set of per-definition records that
  share its position and authored form; a macro-call entry's records also
  carry its keys (`Introspection::entry_keys`, as `EntryKey`). The writer
  writes the first record of each position-and-form pair, so two different
  forms that ever share a position are both written, never dropped.
- **Dissolution.** `process_form::process_literal_begin` gives each member
  its own origin, including in a resumed continuation. The REPL turn text
  (`eval::record_defining_turn_source`) records each record's own slice of the
  turn, so a member keeps its verbatim text.
- **Re-entry.** `process_form::enter_macro_call` runs after `try_expand_sexp`
  and before either publication point: it refuses a dropped key and gives the
  re-entered call its entry's position, so a key a superset adds joins the
  entry and the call is written once.
- **R2.** `refuse_generated_redefinition` is the one predicate; the checkpoint
  asks it inside `compile_macro_if_needed`, and `finalize_cluster` per staged
  record. The rebuild fact is `AttemptFacts::replaces_module_records`, read
  from the provenance the attempt already carried.
- **A call over a written definition (R5).** When a macro call generates a
  key a written entry owns, `Introspection::install_authored` gives the key
  the call's position: the call becomes the one owning entry of all its keys
  and the written entry is retired, so the call is written once, after the
  macro it uses (`tests/plan/s125-evidence-delta.md` §19.4).
- **Residual, asserted with a falsifier.** A continuation resumed after a
  gap inside a macro call's expansion re-walks the expanded products without
  the call, so they record `Written`. It is falsified by a generated
  definition that, after an FQ-macro gap mid-expansion, is accepted for
  redefinition by a written form.

### 4.6 W7 review corrections

`review` (Codex `0ba03b4b`) found four defects in the built §4 (S125 evidence
delta §17.5). R2 and R4 needed design. R1 and R3 resolve by construction
under the authored-entry model of 2026-11-27 (§4.2).

#### R2: a macro checkpoint bypasses the §9.6.1 refusal

**Mechanism: confirmed in source.**
- A `defmacro` publishes as its own checkpoint inside
  `process_form/macro_resolution.rs::compile_macro_if_needed`, which
  calls `compile_macro_checkpoint`.
- The record is written after the checkpoint returns
  (`record_macro_introspection`), which overwrites the live origin.
- `finalize_cluster` runs the refusal (`refuse_generated_redefinition`)
  later, over the ordinary cluster's records only, so it never sees the
  macro.
- So `(maker)` generating `g`, followed by a written `(defmacro g …)`,
  publishes the new `g`, rewrites its origin to `Written`, and regeneration
  then drops `(maker)`.

**The one decision point.** A turn has exactly two publication funnels:
- the checkpoint funnel `compile_macro_if_needed`, which every `defmacro`
  passes through: a direct one in Pass 2 (`process_form.rs`, the
  `FormKind::Defmacro` arm), a literal-`begin` member and an expansion
  product;
- the ordinary cluster, at `finalize_cluster`.

The refusal is one per-key predicate, the body of today's
`refuse_generated_redefinition`: given the live record and the staged
origin, it refuses or passes. Both funnels call it before they publish
anything for that key.

- **At the checkpoint.** `compile_macro_if_needed` takes the macro's
  staged `AuthoredFacts` (position and origin), which each of the three
  callers computes *before* the call rather than after. It applies the
  predicate to the macro's key before `compile_macro_checkpoint` runs, and
  then passes the same facts to `record_macro_introspection`. A refused
  checkpoint therefore publishes nothing and writes no record. The live
  `g`, its `Generated` origin and the saved `(maker)` all stand.
- **Re-entering the same call** passes, because the staged origin is
  `Generated` by the same call. That covers `(maker)` re-entered, which
  regenerates `g`. The re-entry must also pass §4.4's set check, which
  runs once at the head of the entry, before either publication point. A
  re-entry that would drop a recorded key is refused there, before `g`'s
  checkpoint.
- **A whole-file rebuild is exempt** at both funnels, for one reason: it
  replaces the module's records. Today `finalize_cluster` reads the
  rebuild fact from its `SourceProvenance`, but a checkpoint runs before
  finalisation. The attempt's provenance therefore rides `AttemptFacts`,
  set where the attempt starts, and both funnels read that one value.
- **Earlier checkpoints of the same turn stay published.** In
  `(begin (defmacro h …) (defmacro g …))` with `g` refused, `h` remains.
  That is the checkpoint rule ([S117 recovery](s117-conformance-recovery.md)
  §1.1.2: a later failure retains a committed macro), and it is not a
  partial redefinition of `g`.
- **A `defmacro` generated by a file's own macro call.** A file loaded in a
  REPL session stages its expansion products through the same
  `Generated`-origin path (`process_form.rs`, the expansion-product
  arm). A later REPL `(defmacro g …)` reaches the Pass-2 arm with a
  `Written` origin and is refused. The cache-restored residual of §4.5
  (records absent until rehydration) is unchanged; delta §17.4 names it.

**Gate:** none. Everything is in `src/`.

**Evidence leads.**
- `test`'s R2 cells: the three turns, with the third refused and located
  at it; `(g)` stays 10; the file keeps `(maker)` and holds no written
  `g`.
- The file variant: a `defmacro` generated by the file's macro call,
  redefined at the REPL, is refused.
- A re-entered `(maker)` is accepted.
- In a `begin` holding an earlier macro and a refused one, the earlier
  macro is live.
- Unit (`dev`, RED first): the checkpoint funnel refuses a `Written`
  staged origin over a live `Generated` record and publishes nothing; it
  passes a same-call `Generated` origin; it skips the check for a rebuild
  attempt.

#### R4: imports and platforms in authored order (repl §15.4 rule 4)

**Mechanism: confirmed in source.**
- The table already holds each module's structural specs in authored
  order. `process_form/form_dispatch.rs` appends each import form's specs
  and each platform spec as the form is processed, and a whole-file
  rebuild refills them from the file (`int.md` §6.10).
- The order is lost only in `src/save.rs`:
  - `generate_imports` merges specs per module and alias into one
    `(import [...])` form;
  - `generate_platforms` sorts.

**Designed change: no public field.** Rule 4 orders a section's *items* by
authorship. The table's spec order is that order, so the writer stops
reordering it:
- **Imports.** One `(import [...])` form per spec, in table order. The
  implicit prelude spec is filtered as today. An exact repeat of an earlier
  spec is dropped, so an import kept by a save is written once, and the
  `…_written_once_control` cell stays green. The per-route merge
  (`merge_list` and the glob and name-less rules) is deleted.
- **Platforms.** Table order, with exact repeats dropped, and no sort.
- **Exports** are already rendered in table order and are unchanged.
- **Round trip.** Reloading the saved file refills the table with the same
  specs in the same order, so regeneration is a fixed point.

**The rule, not a residual.** Under the 2026-11-27 ruling, a
multi-module `import` contributes one entry per module spec (§4.2). One
form per spec is therefore what rule 4 requires. `(import [aa [a] bb [b]])`
saves as `(import [aa [a]])` and `(import [bb [b]])`, in that order. No
form boundary needs recording, and no `ImportSpec` field is needed.

**Cost.** One `dev` change in `src/save.rs`. `generate_imports` shrinks
to a filter, repeat removal and per-spec rendering, a net removal of about
forty lines, and `generate_platforms` loses its sort. Three unit rows: the
entered order `aa/a`, `bb/b`, `aa/c` writes three forms in that order; a
repeated spec is written once; platforms keep their entered order. No
schema change and no cache effect.

**Gate:** none.

**Evidence leads.**
- `test`'s R4 cells: three import turns saved as three forms in entered
  order; two platforms, `test-capture` then `stdio`, saved in that order.
- The fixed-point leg: save, reload, then save again gives the same file.
- A glob followed by a list from the same module keeps both forms, in
  order.

This supersedes §4.5's *Imports* bullet.

#### R1 and R3: resolved by construction

Under the entry model (§4.2) a `begin` dissolves at entry, so there is no
shared form to split or tie-break.

- **R1.** The macro-call member is its own entry, written once.
- **R3.** Each member has its own position, in member order.

The W7 `begin`-split code and its shared-position tie-break are deleted
rather than corrected. §4.2's unit
rows 3 and 4 are their RED-first rows.

## 5. Module loading and search (1096, 1100, 1092, 1079)

### 5.1 One anchored module-file resolver (1096)

**Mechanism: confirmed, and wider than filed.**

- `src/pipeline.rs::resolve_module_file` searches a child's whole dotted
  path, project root first, and never consults the declaring file's
  directory.
- `process_form/dependency.rs::enrol_declared_submodule` is one of thirteen
  callers making that search. The others are in cache restore, the
  dependency record, the index, `lifecycle.rs`, `/mod` and `dependency.rs`.
- `write_inline_mod_to_disk` holds a second, correct derivation of the
  child path.
- The index names a module from every `.cl` path under each root
  (`index_worker.rs::enumerate_cl_modules`).

**The requirement.** Spec §8.2.5 (the child resolves only to
`{parent_dir}/{stem}/{name}.cl`) and §8.11.2's addressability paragraph
from the S124-Q14 ruling.

**Designed change.**

- **The resolver.** `resolve_module_file` becomes anchored. For `a.b.c`,
  it finds the topmost ancestor whose file the tier search finds, and the
  module's file is that file's directory joined with the remaining segments.
  With no ancestor file, as for a dotted root module, the full-path tier
  search stands.
  - This is §8.2.5 applied recursively, and it is the Q14 rule.
  - All thirteen callers agree without change, the cached face included,
    because validity re-derives through it.
- **The inline-mod writer** calls the resolver (Principle 07).
- **The index** admits an enumerated `(name, file)` only when the resolver
  maps `name` to `file`. The enumeration stays Principle 24's complete-set
  carve-out.
- **Consequences that follow from the spec.**
  - A project that overrides a library root also takes every dotted module
    under it.
  - A project root whose child exists only in a library now fails to
    compile, as §8.2.5 requires.

**Evidence leads.**

- The four `s124_declared_child_*_not_replaced_*` cells and the five
  `search::s124_child_index_*` cells, with the override and
  presence-not-an-error controls.
- The existing §8.11.2 root-module cells stay green.
- Unit, at the resolver:
  - library ancestor with a project child file;
  - project ancestor;
  - no ancestor file;
  - two libraries, the earlier holding only the child;
  - project ancestor with a library-only child (refused).
- A known weakness: the library's value 1 equals a refused compile's exit
  status.

### 5.2 Qualify each expansion at its own macro (1100)

**Mechanism: confirmed.**

- `src/expander.rs::expand_recognized_macro` re-expands a macro's raw
  output in the using module's scope, where an unimported sibling macro is
  not recognised.
- Only after the whole walk does `try_expand_sexp` qualify
  (`qualify_expanded_sexp`), and nothing recognises heads after that.
- `/expand` never qualifies, which is a second divergence with the same
  cause.

**The requirement.** Spec §9.3.4: an expansion may reference its defining
module's dependencies and macros. The using module's imports are not a
condition.

**Designed change.**

- Qualification moves into the shared walk: in `expand_recognized_macro`,
  once a macro from another module returns, its output is qualified against
  that one defining module. The rule is
  [expansion qualification](expansion-qualification-scope.md) §2.1,
  unchanged.
- Re-expansion then meets `d/inner` and takes the qualified recognition
  path.
- The final whole-form pass and its accumulated defining-module list are
  deleted, leaving one qualification site. The qualifier moves to
  `expander.rs`.
- `/expand` shows what the compiler checks.
- A qualified head produced this way records its module as a lookup
  dependency ([§7.6.2](int.md#762-lookup-dependencies)), which only adds
  edges.

No defining module crosses the frontend boundary: the head carries it in
its spelling. The `arch` trigger does not fire.

**Defect A, the remaining leak.** Qualifying each macro's output is still
blind to which symbols the caller wrote, so a bare name in an argument
resolves in the macro's module. Its repair is
[expansion qualification §2.7](expansion-qualification-scope.md#27-caller-text-is-never-qualified).

**Consistent with S125-Q4 (user, 2026-11-26: a macro-introduced reference
is checked against the caller's visibility).** The qualified head
`d/inner` and every qualified function reference are resolved from the
using module, through the ordinary visibility check:
- a public companion macro resolves;
- a private one (`defmacro-`) or a private helper is refused as private
  when the caller is outside `d`'s subtree, and resolves inside it.

No adjustment is needed. The design adds no visibility exception of its
own.

**Evidence leads.**

- The six `s124_macro_sibling_outer*` cells, with their glob and qualified
  controls.
- A unit test of a two-level expansion with only the outer macro imported.
- A `/expand` parity cell.
- A negative cell: a user-supplied argument naming a using-module symbol
  stays bare.
- S125-Q4: an expansion that calls a private companion macro is refused
  as private from a module outside the subtree, and accepted from a
  submodule of the defining module. The same for a private helper
  function.
- Re-run the selective `stdlib/derive` import, whose
  `illegal redefinition of __expr` face `qa` reports shares the cause.

### 5.3 The index never skips for session state (1092)

**Mechanism: confirmed.**

- `index_worker.rs::checked_typecheck_module` installs imports against a
  private copy of the live tables. An unloaded dependency is absent from the
  copy; a registered but unpublished one is present with no definitions.
- Either way the install fails, `mark_skipped` counts the module as
  indexed, and the search answers as complete.

**The requirement.** Repl spec §17.19 R10: no reachable module is omitted
because it or a dependency is not loaded or still compiling.

**What "complete" means.** Every reachable module has recorded its rows or
is unindexable for a reason true in every session: invalid source, or forms
whose indexing needs expansion. The pending count never reaches zero while a
module is deferred.

**Designed change**, to
[index isolation](index-worker-isolation.md) §3.1. Every write stays
private, so INDEX-ISOLATION holds.

- **An unloaded dependency:** before installing a module's imports, the
  index makes each named module present in the private substrate. It uses
  the live table if published, else the `.meta` table under branch (b)'s
  gates, else indexes it privately from source: recursively, depth first,
  with a cycle guard, into the same discard map.
- **Registered, not terminal:** the module stays pending on that
  dependency and is not skipped. The dependency's publication and failure
  hooks re-enqueue it. This is branch (a)'s existing rule extended one hop.
- **A failed dependency** takes the from-source path. It contributes no
  rows only if its source is invalid.

ACT-0952, indexing through macros, remains the later completion.

**Evidence leads.**

- The two `s124_search_reach_*` cells; `neg_missing_dependency_no_row`
  stays green.
- The module rows allocated in delta §14.3. The *registered, not
  published* row is the only discriminator of face 2.
- Unit: the pending count stays above zero while a deferral is open.
- `index_typecheck_mutates_no_live_shared_state` stays green.

### 5.4 A reference through a mount loads its owner (1079)

**Mechanism: confirmed in source; the attribution to `src/` stands.** The
S124 record held it as a hypothesis.

- **The gap names the substituted path.** `src/process_form.rs` takes the
  gap's module (`gap_target_module`) and calls
  `process_form/dependency.rs::drive_module_dep`, as the macro-recognition
  path does.
  - `cranelisp_types::substitute_module_alias` walks the path one segment
    at a time and follows every alias present.
  - With `p` unloaded, its mount `p.s → q` is not yet in the alias map, so
    the gap names `p.s` (subject A). With `p` loaded and `q` not, it names
    `q.t` (subject B).
  - Typecheck reports a gap here, not a hard error: the refusal text is
    `drive_module_dep`'s own. So `int.md` §6.13's "no inter-crate change"
    falsifier does not fire.
- **The loader has no owner rule.** `drive_module_dep` loads the dependency
  only when the whole path resolves to a file (`resolve_module_file`), and
  refuses otherwise. A pending path's owner is never loaded, so its mounts
  are never installed.
- **The cycle walk has the rule, but only once.** `ReachWalk`'s `visit`
  already follows an unresolved qualifier to its owner through
  `owning_module_file`, the longest proper prefix that names a module file.
  `resolve_pending` re-substitutes pending qualifiers but emits an edge only
  when the result names a file. An owner revealed by a later substitution
  (`q` for `q.t`) is never visited: REPRO-1079-c's chain.

**Requirement.** Spec §8.5.4 (a qualified name is self-sufficient) and
§8.6.6 rule 2 (restart on the rewritten path).

**Designed change.** The rule is
[int §6.13](int.md#613-import-and-export-entries-and-export-mounts-s124),
*A qualified reference through a mount loads the mount's owner*,
unchanged. Three things follow from today's source:

- **One owner rule, two readers.** `owning_module_file` becomes the rule
  both `drive_module_dep` and the cycle walk read, so they cannot disagree
  (Principle 07). Its module-file test is `resolve_module_file`, so it
  follows §5.1's anchored resolver once that lands.
- **The driver reports what it drove.**
  - When the gap's path names no file, `drive_module_dep` drives its owner
    if the owner is not yet loaded.
  - It returns the module it actually drove, and the caller records that
    module as the cluster's `Gap` dependency, so the retry waits on the
    owner.
  - Where the owner is already loaded, or no prefix names a file, today's
    located "not found" refusal stands. This is the termination condition:
    each retry loads a module not loaded before.
- **The walk emits revealed owners.** `resolve_pending` emits an owner edge
  for every still-pending qualifier, which `ReachWalk` deduplicates.

**Gate:** none. Every change is in `src/`. Types' substitution and
typecheck's gap are used as they are.

**Evidence leads.**

- REPRO-1079-a and -b, subjects and controls, in `--run`, `--link` and the
  REPL: the eight `spec_08_modules::s124_1079_*` cells flip.
- REPRO-1079-c, the chained cycle and its control, if not already
  allocated. It turns green only with the walk's change, which makes it
  the discriminator for that half.
- Unit:
  - the driver returns the owner for a pending path, and the target once
    the owner's mount is installed;
  - "not found" stands when the owner is loaded and has no mount for the
    next segment, the termination leg;
  - `resolve_pending` emits a revealed owner.
- A negative cell: a path whose owner is loaded and mounts nothing at that
  segment is refused once, located at the reference, with no retry loop.
- Subject C rests on `(import [q []])` loading nothing, as spec §8.3.6
  requires. The owner rule covers it, so no import change is designed.

### 5.5 As built (W8)

Where the W8 build departs from or adds to §5.1–§5.4, int §7.1 (ACT-0994)
and int §7.7 (ACT-1085).

- **1096.** `pipeline::module_file_target` answers where a module's file
  must be (`Anchored` beside the topmost ancestor file, or `Searched`);
  `resolve_module_file` and the inline-mod writer both read it. The index
  enumerates `(name, file)` pairs and keeps a pair only when the resolver
  maps the name to that file. `pipeline::expected_module_file` gives the
  path a module is read from or would be; the inline-mod writer writes it,
  and a missing declared child's refusal names it.
- **1079.** `drive_module_dep` returns the module it drove, and every caller
  that records a `Gap` (and `/mod`'s wait) uses that module.
  - *Added:* an owner that is the referring module or one of its ancestors
    refuses as "not found". Its mounts are installed before the reference,
    so driving it would only wait on the referrer as a cycle
    (`bare_mod_decl_neg_does_not_resolve_sibling_file` caught this).
- **1092.**
  - The index provides each import and export target through a private
    substrate (`index_worker::PrivateSubstrate`): a published or seeded
    module by its live table, an unregistered or failed one from source,
    depth first, with a cycle guard. A registered module still compiling
    defers the dependent (`ImportableIndices::defer_on`); the dependency's
    publication or failure hook returns it to the worklist.
  - *Not built:* the dependency's `.meta` branch. A `.meta` decodes to a
    table of another code-store type, so a dependency always takes the
    from-source path. A dependency whose forms need expansion makes its
    dependents unindexable (ACT-0952).
  - *Added:* an import of a macro from a module indexed from source installs
    nothing for that name, because macros are not indexed. The importing
    module's other definitions are still indexed (E-1092's macro row).
  - The substrate reads the scheduler's publication state
    (`CompileScheduler::publication_read`) before it snapshots the tables,
    and classifies every dependency from that read (review F1, the §6.1
    order). A dependency that publishes after the read defers the dependent,
    and the deferral's settled re-check returns it to the worklist.
  - A declaration whose names list loads nothing (`imports::names_load`)
    provides no module (review F2, spec §8.3.7).
  - The `{gap:?}` rendering (§2) is replaced at every site by
    `dependency::unresolved_reference_message`, which names `module/member`.
- **1100.** The qualifier is `src/expander/qualify.rs`, called from
  `expand_recognized_macro` with the call site's lexical scope, so a name the
  caller binds and passes as an argument stays bare. `MacroResolver` gains
  `current_module`.
- **ACT-0994.** `wait_module_typecheck_settled` also waits while the
  module's cached load is outstanding; a loaded completion acts only while
  the module is `Claimed`. Row (1) reaches the window only when the fresh
  registration reaches its terminal pool before the stale completion
  arrives; with the registration still queued the old code also marked
  nothing.
- **ACT-1085.** `cache::CacheDirectory` holds the owner lock
  (an `owner.lock` file in the project's cache directory, `File::try_lock`) or a private directory
  under the system temporary directory. `ObjectCache::for_session` is the
  one construction; `shutdown` ends the hold after the workers join.
  *Residual:* an exit path that skips `shutdown` leaves the private
  directory in the temporary directory.

## 6. Commit planning (1090) and the cost of 1087

**Left S125** with the trace deferral (user, 2026-11-26). Both are designed
here for the sprint that takes trace work, and neither is scheduled.

### 6.1 Read publication before the tables (1090)

**Mechanism: confirmed and refined.**

- `src/worker.rs::plan_staging_commit_inner` copies every live table, and
  only later does `cache/dependency_record.rs::covered_set` ask the
  scheduler whether each member has published.
- A member that publishes between the two reads is counted as published
  but walked from its old copy, so its own dependencies drop out of the
  covered set.

**Designed change.**

- Planning takes the published set, as a snapshot, before it copies the
  tables. `covered_batch`'s predicate consults that snapshot.
- A member then counts as published only if it was published when its table
  was copied.
- The object pass keeps its own deferral on a miss and is unaffected.

**Asserted, with a falsifier.** This relies on the publisher writing the
live table before the scheduler marks the module published
(`publish_prepared_generation_with`). If a reading shows the reverse, both
reads move under one lock. `dev` confirms the order as its first act.

**Evidence leads.** The cell `trace::s124_1090_mixed_restore_subject` is
run-dependent (2 of 30), so a rate is weak evidence. Prefer a deterministic
module test that publishes the member between the copy and the check
through a test hook. It needs a detection proof against the current order.

### 6.2 1087: the cheapest correct control, costed

[Tracing](../arch/tracing.md), *Decision: the residual stands*, and
[§7.6.4](int.md#764-reference-edges-and-the-covered-trace-set-row-b10)
(C1) hold the record. C1 already makes restored and linked launches correct.
Only the launch that first compiles the module omits frames.

**Ruled out.**

- *The first launch waits for the prelude.* It deadlocks:
  prelude → parent → child → prelude. Commit planning sits on a publication
  path, which is why C1 could move only the object pass.
- *Lazy coverage at run time.* It changes trace frame generation and the
  runtime entry, a backend and intrinsics public change.
- *Running the first launch from the object.* It does not help a REPL
  start.

**The cheapest correct control** narrows `arch`'s option:

1. `covered_set` already detects the case (the prelude read while
   unpublished). It reports that beside the set, as a private field on the
   batch and the prepared commit.
2. Commit planning records the module in an owed set in `SharedState`,
   only when the batch holds a target whose body contains a `trace` form. A
   private AST walk finds it.
3. When the prelude publishes or fails, codegen alone re-runs for the
   owed modules' trace-bearing targets, against a fresh set. They republish
   through the ordinary prepared publication as an ABI-preserving
   redefinition ([session transaction](session-transaction.md) slot
   versioning), with no re-typecheck.
4. An entry batch's commit and the first evaluation wait for the owed set to
   drain.

**Cost.**

- **Code:** about 150 to 250 lines in `src/` (`dependency_record.rs`,
  commit planning, a prelude-publication hook, the startup ordering rule),
  plus module tests.
- **New state:** one owed set and one flag on the batch.
- **No public or schema change:** objects are already correct through C1,
  and the recompile is JIT-only.
- **Extra compilation:** none for any shipped stdlib module, since none
  holds a trace form. Elsewhere it is one extra codegen per trace-bearing
  target.

**Risks.**

- It adds a second, startup-time publication branch serving a population
  the shipped library does not contain.
- The republish must not count as a cache generation, rewrite the `.meta`
  or re-trigger an object pass. If the ordinary publication cannot be made
  JIT-only for it, the cost becomes a whole-cluster rebuild.
- It adds a startup ordering rule whose freedom from deadlock is asserted
  (the owed recompile waits only on an already-terminal prelude), not
  measured.

**What it changes.** The first `--run`, `--no-cache --run` and REPL start
record the same frames as a second launch and `--link`. That removes the
last known mode divergence in tracing.

**Evidence it would need.**

- The existing cell flips.
- Negative controls:
  - no recompile when the prelude had published;
  - none for an owed module without a trace form;
  - REPL-start and `--no-cache` legs.
- A recovery count read as zero over the stdlib.

**Recommendation.** Keep the residual as the settling target's one named
exception. It is memory-safe, and the harm is a missing diagnostic frame.
The control is bounded at one `dev` pass, but it adds a recovery branch and
an ordering rule for an empty shipped population, which the risk-weighted
control standard does not favour. Strict mode parity is the user's to
choose.

## 7. Filings

Each filing was verified against its `refers_to` source first.

| Filing | Opened | Finding | Disposition |
|---|---|---|---|
| ACT-0965 item 1 | `src/lib.rs`, the comment under `pub(crate) mod repl;` | The comment now says what `repl` holds; the stale "deleted / future work" claim is gone | Resolved |
| ACT-0965 item 2 | `src/worker.rs` (`compile_and_publish_prepared`, `load_cached_module_via_linker`), `src/session_v4/lifecycle.rs` (`link_by_name`), `src/AGENTS.md` (the ~100-line rule) | Three named functions still exceed the budget. The fourth (`process_regular_form_with_origin`) no longer exists under that name | Resolved by the "when opened" rule now in [int.md §12.1](int.md#121-standing-review-rejects) item 21, which is where the action requires it. Each function is decomposed or excepted when planned work next opens it |
| ACT-0965 item 3 | `src/worker.rs`, the cache linker's host-extern walk and `dlsym_host_symbol` (a miss is skipped silently); backend `jit.rs`, `Jit::finish_builder` and `Jit::define_symbol` | Two routes resolve host externs | Designed: one binary-owned resolver walks the host-promised externs once into a name-to-address map. It feeds both `Jit::define_symbol` and `Linker::register_symbol`, which are already public, and a miss is one named error in both modes. API +0. It does not reach the JIT's eager intrinsic set, which the backend derives itself; moving that would need a backend item, and so `arch`. Lead: a unit test where a missing extern is the same error on both routes. **As built (W9):** `worker::host_extern_addresses` feeds both routes; a name the host cannot supply is absent from both, not a named error, because the host-promised set includes names the backend lowers inline or through the intrinsic catalog (`bind`, `pure`, the Trace accessors), and only the backend's lowering classification tells them apart |
| ACT-1060 | `src/repl/mod.rs` (the session-lock test's `/context` path) | Fixed at `8667a868`: the path is in the test's temporary directory | Close: `qa` runs the action's `git status` check after the next suite run |
| ACT-1093 | `src/syntax/cheatsheet.txt`, `trace` topic | Holds: no strict-evaluation note beside `nanos` | **Left S125** with the trace deferral (user, 2026-11-26). When scheduled: `dev`(src) adds one line citing spec §4.12.2; no design needed |
| FIXME 0863 | `design/int/s117-conformance-recovery.md`, `int.md`; source search for the retired types | Item 2 held only in a retained "superseded" block; the types are absent from source | Item 2 resolved: the block is deleted from `s117-conformance-recovery.md`. Item 1 (checkpoint coverage) is `qa`'s; retarget the FIXME to `qa` |
| FIXME 0933 | `src/platform.rs`: the descriptor loop, `parse_and_check_platform_type_sig`, `fqize_type_expr`, `require_io_return` and `refuse_function_types` (W9); `crates/cranelisp-types/src/module.rs::install_platform` and `SlotMintError`'s `Display` | **The central claim no longer holds.** A lowercase manifest leaf does survive `fqize_type_expr` as `TypeExpr::TypeVar` and checks to a `Type::Var`, and `refuse_function_types` passes a variable (`function_type_within`). But no polymorphic slotted entry can be minted: `install_platform`, the one funnel every `PlatformEffect` mint passes, runs `ConcreteType::from_type` on the scheme first and refuses with `SlotMint(NotConcrete)`. `platform.rs` maps that to a diagnosed `ModuleError` naming the platform function. The refusal is structural at the converged mint gate (the P-1 shape), and it is a load error, not a panic. What remains is the diagnostic: it reads "cannot mint a callable GOT slot for a non-concrete scheme (Var(n))", which names an internal variable, not the written signature | **Resolve the soundness claim, and correct the message without a second check.** The `install_platform` error mapping in `platform.rs` matches `LifecycleError::SlotMint(SlotMintError::NotConcrete(_))` and renders: platform function `<p>/<f>`'s signature `<written sig>` contains a type variable, so a platform signature must be fully concrete ([total concreteness](../arch/total-concreteness.md) §3.5). Any other lifecycle error keeps today's wording. No gate beside `refuse_function_types` is added, because it would test the same property twice. Gate: none. **Unit row `dev` writes RED first** (`src/platform/tests.rs`): a descriptor whose signature has a lowercase leaf, such as `(Fn [a] (primitives/IO primitives/Int))`, is refused as a load error naming the function and quoting the written signature, and no entry is installed. RED today on the message. Control: the concrete signature still mints. **e2e lead for `qa`:** optional. It needs a fixture platform built with a residual leaf, beside `platforms/shapes-badabi`, and is worth it only if `qa` judges the unit row insufficient for an author-facing message. When the row lands, the FIXME can be deleted |
| FIXME 0889 | `src/expander.rs::invoke_clause`; `tests/macro_turn_marshal_leak_0889.rs` | Its "resolved in S122" claims hold. The 46-allocation residue was not re-measured | Keep. No design change: [macro-turn ownership](macro-turn-ownership.md) stands. Retarget to `qa` as allocator-instrumentation attribution. Its trigger fires only if the settling target claims zero session residue |

The focus band's stale citation at `src/platform.rs:555`, outside this
brief, was read too. It cites a deleted FIXME 0318 and spec §8.11, now
"Search Paths". The rule is spec §8.9.3. It is a comment-only repair for
`dev`(src).

### 7.1 `load_cached_module_via_linker`: decomposed, not excepted

W9 opened `src/worker.rs::load_cached_module_via_linker` (199 lines), so
[int §12.1](int.md#121-standing-review-rejects) item 21 applies (`review`,
Codex `4e9cbc53`). **Decision: decompose it.** No exception is justified.
The function runs five steps in sequence, each with its own failure rule or
invariant, and none shares local state with another except the values each
hands to the next.

| Step | Responsibility | Invariant or failure it owns | Hands on |
|---|---|---|---|
| 1. Read the artefact | Cache directory, `try_load_cached_module` and the `has_object` check | Each absence is a located `ModuleError` naming the module | The cached module |
| 2. The session's linker symbol set | One `Linker` holding the intrinsics catalog, the host-promised externs (`host_extern_addresses`, ACT-0965 item 3's one resolver), platform-effect slot pointers, compiled-body slot pointers and every module's GOT data symbol | Completeness: one set, read from one walk of the tables. Today it is three walks plus two catalogs; one walk is the cohesive shape. A null slot is skipped, as today | The linker |
| 3. Load and wire the slots | `load_cached_object`, then for each codegen target store its address in the module's GOT | Decision 37: a target with no linked address is a hard error, never a null slot | The loaded targets |
| 4. Publish the owners | One `Code::linker` per loaded target through `publish_compiled_owner`, all sharing one `Arc<Linker>` | Retention (Principle 22; `int.md` §7.4): each published pointer's owner is that `Arc`. The step takes the linker by value from step 3, so the mapped pages cannot drop between wiring and publication. Displaced owners drop after the loop | — |
| 5. Record and report | `append_o_path` for `--link`; return the loaded owners' symbols | The `--link` set includes every restored object (S86 D5b) | The symbols |

- **What stays in the function.** The function becomes the five calls in
  order, with the module's GOT handle taken once between steps 2 and 3. The
  order is unchanged.
- **Where the steps live.** Each step is a private function in
  `worker.rs`. Steps 3 and 4 could join `src/worker/` beside the other
  publication helpers if `dev` finds that clearer; it is not required.
- **Seams, not a line split.** Step 2 is the seam ACT-0965 item 3 already
  names: the session's one view of host and session symbols for a
  `Linker`. Steps 3 and 4 are the wire-then-own pair that §12.1 item 12
  (no split publication) governs. Behaviour does not change, so no
  e2e change is needed.
- **Unit rows for `dev`.** These are existing-behaviour pins, not REDs,
  since the refactor changes no behaviour.
  - Step 2: the set holds an intrinsic, a host extern, a platform effect
    and a GOT data symbol, from a fixture session.
  - Step 3: a target missing from the object is the hard error, and no
    slot is written.
  - Step 4: every loaded target ends with a `Code::Linker` owner sharing
    one `Arc`.

`src/AGENTS.md` therefore needs no exception entry.

## 8. The macro clause runs under no binary trap guard (F2)

The binary installs no trap handler. `invoke_clause` calls the clause entry as
a plain `extern "C"` call. Intrinsics' guard
([process lifecycle §1.8](../intrinsics/process-lifecycle.md#18-the-trap-guard-one-disposition-armed-per-thread))
is the process's one writer of the `SIGFPE`, `SIGILL`, `SIGBUS` and `SIGSEGV`
dispositions. The contract, its grades and its evidence live in
[macro-turn ownership Rule 8](macro-turn-ownership.md#rule-8--a-failing-clause-ends-the-process-int-recovers-nothing)
and §8 D5–D6 there. The numbered subsections below are kept because source,
tests and the spec cite them.

- **The binary's guard was not repaired to follow §1.8, because a second
  guard is excluded.** Two guards that each install once and forward compose,
  but the "one writer" property would then need a census across two crates.
  If an answer to §8.5 needs containment, it is a new `arch` row: intrinsics
  publishes its guard and the binary calls it.
- **What the binary does not protect.** No accepted program raises a trap in
  clause code other than stack exhaustion. Division by zero is a checked panic
  (spec §12.7.3), and the backend's only emitted trap follows
  `runtime/panic`, which never returns (`crates/cranelisp-backend/src/raise.rs`).

### 8.1 A trap in a macro clause

Its outcome is
[macro-turn ownership Rule 8](macro-turn-ownership.md#rule-8--a-failing-clause-ends-the-process-int-recovers-nothing):

- stack exhaustion reaches the Rust runtime's overflow handler;
- any other trap ends the process on its signal;
- the outcome is the same before and after the first platform force.

### 8.3 Unit evidence

These are cells D5 (the workspace census) and D6 (dispositions unchanged by a
clause call) of macro-turn ownership §8, in
`src/expander/trap_dispositions_tests.rs`.

### 8.5 Open, for `spec` and the user: a trap in a macro clause

The user holds this as
[S125-Q12](../../spec/appendix-d-open-questions.md#s125-q12-what-happens-when-a-macro-clause-raises-an-otherwise-unspecified-hardware-trap):
what the compiler owes when clause code raises a trap that no specification
clause governs. Q12 states the options. Stack exhaustion is excluded, because
it is already a runtime panic.

- **The current design is option A.** A trap of this kind ends the process on
  its signal, with no compiler report.
- **What each option needs.**
  - *Option A* needs no change.
  - *Option B* needs a new `arch` row. Intrinsics would publish its guard,
    and add a way to end the process through its terminator with a line that
    is not a panic report. The guard must also leave stack exhaustion to the
    panic path, which `SIGSEGV` and `SIGBUS` cannot distinguish without the
    fault address.
  - *Option C* needs the same published guard, and a recovery boundary that
    `design`(int) cannot make sound. Abandoned frames may hold locks or
    references, and a memory fault may already have corrupted the heap.
- **`design`(int)'s reading:** A is adequate while no program can reach the
  case. B is the step up if defect reports are wanted. C should be excluded.
  The verdict is the user's.

## Change history

Designed 2026-11-26 (S125 Phase 3), against `4c844f62`. §8 designed and
delivered 2026-11-28, Phase 6b.
