# Sprint 125 architecture review (Phase 2)

Working packet for the Phase 2 checkpoint. Standing documents cite the batch
rows by label (IO-T, TR-1, D-1, B18) in
`design/arch/interfaces.md` §Approved changes not yet in source; they do not
link here. `arch`, 2026-11-26, at `main` HEAD `4c844f62` with no source change
since the S124 close.

## Verdict

Signed off for Phase 3, with two decisions for the user (§3) and the scope
adjustments in §4.

- Three public-API batches are approved: IO-T (types), TR-1 (intrinsics) and
  D-1 (a binary consumer edge, no item).
- Row B18 (ACT-1111) stays escalated. `arch` recommends it stay carried.
- Every other in-scope item needs no inter-crate change. Each has a named
  trigger that returns it to `arch` (§2.4).
- **S124-Q19 does not move any verdict.** Both options keep `primitives/pure
  :: (Fn [a] (IO a))` as §10.2 states; Q19 decides only what "pure function"
  means in §3.2.3 prose.

## 1. How opaque `IO` is realised

The rulings of 2026-11-22: `IO` has no language constructors; `pure` is the
public lift; a nested `IO` value displays as `#io` and a function value as
`#closure` in the one canonical format (spec §12.9.1, used by the REPL and by
`trace`).

What source did at the Phase 2 reading (HEAD `4c844f62`); S125 has since
deleted the gate and the pairing named below:

- `src/bootstrap.rs::register_io_type` seeds `Pure` and `Effect` as public
  constructors and `Bind` as `internal: true` with a public bare exposure.
- Typecheck hides `Bind` by a name-keyed re-resolution
  (two `is_internal_constructor_check` functions in typecheck's
  `checker.rs`, called from `infer.rs`; deleted in S125).
  It is a second resolver beside the scoped chain, and a qualified
  `primitives/Bind` passes it (defect 1105): the
  [Principle 24](../design/arch/principles/24-resolve-once.md) mirror class.
- `adt.rs`'s exhaustiveness check drops internal constructors from the set to
  cover. A match with `Pure` and `Effect` arms is then accepted and fails on a
  bind node (1107). The exclusion is unsound for any type with a hidden
  constructor.
- `Effect`'s field is typed as the IO's value and holds a thunk (1106).
- Nothing outside typecheck reads `internal`. The backend recognises a `Pure`
  construction by `(primitives/IO, IO_TAG_PURE)`
  (its `pure_payload_type` in `compiler/apply.rs`, deleted in S125), releases `IO` as runtime-owned
  before shape derivation (`drop_glue.rs::is_io`), and builds `Bind` and
  `Effect` nodes by tag. Display and descriptor baking walk `IO`'s
  constructor table only because nothing has said `IO` is opaque.

Options weighed:

| Option | Shape | Grade | Cost |
|---|---|---|---|
| A, gate | Mark all three internal; re-key typecheck's gate on the resolved identity; delete the exhaustiveness exclusion | measured | no public change; keeps a bespoke flag and gate beside visibility; the false `Effect` scheme and the short `Bind` node stay, unreachable |
| B, private constructors (approved, then replaced) | `IO`'s constructors are module-private to `primitives`; only `Pure` survives, as the typing carrier of `primitives/pure` | structural in the resolver; measured at typecheck's call sites; an asserted staging-view residual | adds `ConstructorAccess` and `ResolutionScope::resolve_member`; introspection still lists `Pure` as a member of `IO` |
| C, no constructors (approved, Phase 3) | `IO` shaped like `Vec`; `pure` is a host-promised primitive the backend lowers inline to the `Pure` node, as it lowers `bind` | structural | types −2, 1 changed; one backend lowering; typecheck deletes its gates and exclusion |

B was chosen first on the reading that C needed a new typing path for
`pure`'s body (`infer.rs::instantiate_ctor`). That reading was wrong: `bind`
has no body; it is typed from its scheme as a host-promised `RustPrimitive`
and the backend builds its node (`compiler/apply.rs::lower_host_promised`,
`compiler/io_nodes.rs::emit_bind_node`). `pure` takes the same path. On
2026-11-26 the user held that `Pure` being the exception to the opaque type
does not warrant lifting the veil, and `arch` re-decided on C (§2.1).

## 2. Batches

### 2.1 IO-T — types: `IO` without constructors — approved

Exact delta, producers, consumers, schema effect and the expected baseline
are in row IO-T. In summary:

- Types removes `CallableOrigin::Ctor::internal` and `AdtCtorSpec::internal`,
  and `AdtCtorSpec::new` loses its flag. Nothing is added.
- Baseline: types −2, 1 changed; every other crate +0. The backend's
  `compute_layout_hash` and `generate_schema` change their output, not
  their lines.
- `CACHE_SCHEMA_VERSION` +1, because `CallableOrigin` is persisted. The
  platform ABI and the IO node layouts do not change.
- The three questions are yes; no module's intent changes, so no escalation.
- The refusal of every `Pure` spelling is structural: no binding exists.

**Re-decision (Phase 3, 2026-11-26), replacing private constructors.** The
first statement of this row kept one module-private `Pure`. Two Phase 3
corrections followed: `design`(typecheck) found that the dotted and
scrutinee-picked member reads skip §8.7.3, which added
`ResolutionScope::resolve_member` and a staging-view residual, and
`design`(int) found the schema walk reading `IO`'s constructor list. The
user then held that `IO.Pure` being constructible inside `primitives` still
lifts the veil of the opaque type. `arch` re-assessed option C against
source:

- `pure` needs no body. It is host-promised and typed from its scheme, as
  `bind` is, and the backend's shared host-promised lowering serves direct
  and first-class use alike.
- `ConstructorAccess` and `resolve_member` lose their only consumer and are
  withdrawn. The member-read gap does not exist for user types: a
  `deftype`'s constructors carry the type's visibility and both member
  paths resolve the parent through the scope first. Probed at HEAD with a
  private `shapes/Secret`: `(Hid v)`, `Secret.Hid` and `shapes/Secret.Hid`
  are all refused from `main`. The falsifier is in the row.
- The staging-view residual has no subject and is dropped.
- The schema walk change stands unchanged.

Riding on IO-T, with no public item of their own:

- **Binary (`src/bootstrap.rs`).** Install `IO` with type parameter `a` and
  no constructors; seed `primitives/pure` with `insert_primitive` beside
  `bind`; delete `Pure`, `Effect`, `IO.Bind` and the `Bind` exposure; drop
  `SynthCtor::internal`. The bootstrap's unit tier asserts `IO` has no
  constructor and no `IO.` key. `IO` keeps its type parameter, unlike
  `Vec`'s empty list behind defect 1104 (excluded).
- **Backend.** Lower `pure` inline to the `Pure` node with its payload-glue
  word; delete the `ConstrADT` path's `IO` case. This is backend interior.
- **Typecheck (defect 1107, clean house).** Delete the name-keyed
  internal-constructor gates and the exhaustiveness exclusion; the unit
  fixture (`builtins.rs::with_io`) mirrors the bootstrap shape. A `Pure`
  spelling refuses as an ordinary unknown name.

### 2.2 TR-1 — intrinsics: trace display markers — approved

Row TR-1. `DescriptorKind::Io = 8` renders `#io`; `Fn` renders `#closure`.
The backend bakes `Io` for an `IO` type. Intrinsics baseline +2, the enum's
two paths. `CACHE_SCHEMA_VERSION` +1. Independent of B18.

The REPL's markers (`src/display.rs`, `src/styled.rs`; 1109) need no public
change: `Type::is_io` already exists.

The canonical format has two renderers: the binary's and intrinsics'
`trace_format.rs`. That is a standing
[Principle 07](../design/arch/principles/07-single-source-of-truth.md)
exposure. This sprint changes both in step and does not widen to converge
them.

### 2.3 D-1 — binary display consumes `ctor_field_types_at` — approved

Defect 1062: the binary's display paired type arguments with field
variables by first appearance (its `build_adt_subst`, deleted in S125 W2), a second derivation of
`cranelisp_types::ctor_field_types_at`, which pairs them by declared
parameter. The binary takes the published function, a new consumer edge with
+0 baselines. Falsifier: if display must convert or narrow its value to call
it, which would happen only for a residual type reaching value display,
contrary to spec §3.11, the design returns here.

### 2.4 In scope with no inter-crate change

Each returns to `arch` if its design finds otherwise.

| Item | Reading | Returns to `arch` if |
|---|---|---|
| `/type` (1089, 1099) | `src/repl/commands.rs::typecheck_only` runs its own parse-and-check against the live tables. It writes `__expr` and any definition into the live session, and it never expands macros. This is [Principle 11](../design/arch/principles/11-single-pipeline-mode-parameters.md)'s early-branch duplication, a live instance of FIXME 0939. The cure is the shared form path with a check-only, non-publishing mode, refusing a definition form as the ruling requires | the shared path needs a non-publishing check that typecheck does not expose |
| Persistence (1005, 1068, 1101, 1102) | Binary-internal: `save.rs` section writers, `session_v4/lifecycle.rs` final persist. 1101 can tell an instance from a declaration through published `Life` and `template_owner()` | a cache refusal or invalidation needs a new backend cache entry |
| Module loading and search (1092, 1096, 1100) | Binary-internal: `index_worker.rs`, `process_form/dependency.rs`, `process_form/macro_resolution.rs` (the expander is the binary's) | an expansion must carry its defining module across the frontend boundary |
| 1090 | `worker.rs::plan_staging_commit_inner` read order | — |
| ACT-1110 | `crates/cranelisp-intrinsics/src/trace.rs::SKIPPED_NAME` is `::skipped::`; the collect entry already receives the value and descriptor, so `::untraced::` with the body's value is internal to intrinsics | — |
| ACT-0965 | Items 1 and 2 are `design`(int)'s. Item 3: two routes resolve host externs (`worker.rs::dlsym_host_symbol` for the cache linker; the JIT's lookup map). `arch` prefers converging on one resolver, a structural grade, to a parity observation | convergence needs a backend public change |
| ACT-1060, ACT-1093, FIXMEs 0863 and 0889, `src/platform.rs:555` | binary-internal or comment-only | — |

## 3. Decisions for the user

### 3.1 Row B18 (ACT-1111): include in S125, or keep carried

**Problem.** You directed typed trace entries on 2026-11-22 and carried the
work. Row B18 holds the exact delta: four entries per value kind replacing
`cranelisp_collect_trace(i64, i64)` and `cranelisp_trace_format(i64, i64)`.
Neither its shape nor its bounded-contexts sentence, which puts handle types
in emitted signatures, is approved. S125 opens the same two entries for TR-1
and ACT-1110.

**Resolution `arch` recommends: keep it carried.** It is not `src/` and is
not in the settling target. Neither TR-1 nor ACT-1110 changes B18's shape or
makes it dearer later: TR-1 adds a descriptor kind B18 keeps, and ACT-1110's
correction carries into each new entry. The focus band already needs
decomposition. The standing ordering advice also holds: typing the catalog's
register classes first types floats and truth values once, not twice.

**Tradeoffs.** Including it shares one intrinsics and backend design pass
with TR-1 and ACT-1110, and could share one schema bump. It costs twelve
export lines, a backend selection pass, a window in which no trace form
builds, and your ruling on the bounded-contexts sentence first. Keeping it
carried leaves the unconfirmed `(i64, i64)` line in the intrinsics baseline
for another sprint.

### 3.2 ACT-1087: the accepted residual against the settling target

**Problem.** A trace form in a declared child of a prelude dependency omits,
on the launch that first compiles it, frames a second launch and `--link`
record. `arch` accepted this as a residual on 2026-11-19
([tracing](../design/arch/tracing.md), *Decision: the residual stands*),
because each control cost more than missing diagnostic frames. Its cell,
`trace::s124_1087_subject_run_first_launch`, fails on purpose and is
attributed to `src/`. The S125 settling target allows no failing test
attributed to `src/`, and root `AGENTS.md` counts a divergence between modes
as a defect.

**Resolution `arch` recommends: reopen it for costing.** `design`(int) costs
the cheapest correct control, recompiling the form once the prelude
publishes, limited to modules whose batch ran while the prelude was
unpublished and that hold a trace form. If the cost is bounded, it is fixed
in S125. If it is not, the residual stands and the settling target names this
one cell as its exception.

**Tradeoffs.** Fixing it removes the last known mode divergence in tracing,
at the cost of a second compile for a population that no shipped stdlib
module is in. Keeping the residual keeps a deliberate RED in the focus
module, which the clean-and-green rule does not otherwise admit.

## 4. Scope adjustments

1. **ACT-1110 and ACT-1111 are not `src/`.** Both are
   `cranelisp-intrinsics`. ACT-1110 joins under *clean house* with TR-1,
   since TR-1 opens the same files. ACT-1111 follows §3.1.
2. **Defect 1109 has a trace leg.** §12.9.1 is one format, so TR-1
   (intrinsics, backend) joins the display group. `qa` allocates a trace cell
   for each marker; the current cells are REPL-only.
3. **FIXME 0929 has left `src/`.** Its binary row is done (verified at
   `src/repl/commands.rs::typecheck_only`, which returns a located error with
   no default type). Its remainder, the NC-2 census with its detection legs,
   spans backend and typecheck and is `qa`'s to allocate. Move it to the
   hygiene band.
4. **Opaque `IO` is a cross-surface migration.** `Pure` appears in 193 test
   files (about 2,450 lines), 42 examples, 18 exemplar files, 6 stdlib files,
   5 `user/` pages and the crate unit tiers of backend and typecheck. The
   stdlib's `io/monad.cl` defines its own `pure` over `Pure`. It must
   re-export `primitives/pure`, not define a second one (Principle 07).
   Examples 21 and 23 explain node kinds in comments that the opacity ruling
   removed from the language.
5. **Typecheck joins for 1107 only**, under clean house. Its other carries
   remain excluded.

**Build order for opaque `IO`**, callee-first and additive first, so the
suite is never mass-red:

1. `primitives/pure` and its backend lowering are added while `Pure` is
   still public (binary, backend). Nothing breaks.
2. Consumers move to `pure`: stdlib (`dev`), tests (`test`), examples
   (`training`), exemplar (`dev`), `user/` (`docs`), crate unit tiers (`dev`
   per crate). Tests are stdlib-free and write `primitives/pure` or import it.
3. IO-T, the bootstrap's removal of every `IO` constructor, the typecheck
   deletions, the backend's removal of the `ConstrADT` `IO` case, and the
   schema walk with the two regenerated platform schemas land as one
   cascade, with the schema bump. 1105 to 1108 flip green here.
4. TR-1 and the REPL markers, independent of steps 1 to 3 except that TR-1's
   `#io` cell needs no constructor table, which step 3 removes.

Each schema-bumping change-set bumps once; IO-T and TR-1 may share a bump
only if they land in one change-set.

## 5. Hygiene-band FIXMEs targeted at `arch`

| FIXME | Verified against | Disposition |
|---|---|---|
| 0776 | `design/typecheck/monomorphisation.md` §3.3 (two windows, a standing rule routing a new one to `arch`); `auto-curry.md` §1.2 (three seams); `mono_collect.rs::resolve_auto_curry`, which takes a required `AutoCurryDrain`, named at every call (`candidate_selection.rs`, `finalize.rs`) | **Declined.** The local seam sets and their grades stand; Principles 24 and 26 govern the classes. The S124 typecheck audit judged a seam registry would measure, not remove, the cost. Deleted in Phase 3, after `design`(typecheck) repointed its two citations |
| 0783 | `crates/cranelisp-backend/src/rc_ownership_fence_tests.rs`: six fenced files, the fence and its false-fire control exist | **Resolved.** Folded into register row R10 as a `gated` instrument for analysis-result consumers on the backend counting surface, with its detection proof and blind spots. No new row and no Principle 25 corollary: re-deriving from shape is the re-derivation Principle 24 already forbids. Deleted |
| 0938 | `design/arch/principles/AGENTS.md` lacked the three rules; Principle 24 carries the worked example | **Resolved.** The three rules are in principles `AGENTS.md` §Authoring a Principle. It is authoring guidance, not a Principle amendment, so it need not wait for Phase 7. Deleted |
| 0939 | Principle 11's body states the rule and Sprint 26 origin and has no audit test | **Kept** for the S125 Phase 7 principle review, which amends the body. `/type` (§2.4) is fresh evidence |
| 0942 | `design/AGENTS.md`, owned by `arch` (`standing-documents.toml`), said what design documents are about, not their order | **Resolved.** The ruled order is in `design/AGENTS.md` §Design-doc expectations, which every design role reads. Deleted |
| 0943 | Principle 21 and the shared contracts cover items 3 and 4; items 1, 2, 5 and 6 had no receiver-level carrier | **Resolved.** Items 1, 2 and 5 are evidence bullets under the public-API criteria, and item 6 is an obligation, in `design/arch/AGENTS.md` §Public-API discipline. Deleted |

The user's local memory entries for 0938, 0942 and 0943 ("Principle wording
states intent", "Design-doc structure", "Proposal discipline") can retire.
`arch` did not edit them.

## 6. What `design`(int) can start on

- **ACT-0965:** nothing from `arch` is needed (§2.4).
- **ACT-1110:** this is `design`(intrinsics) and `dev`(intrinsics), not
  `design`(int). No `arch` input is needed.
- **ACT-1111:** waits on §3.1. It does not block `design`(int).
- **Opaque `IO`:** `design`(int) may start the bootstrap and display design
  against rows IO-T and D-1, as re-decided in §2.1. Its bootstrap section
  and `design`(typecheck)'s `io-types.md` and `typecheck.md` IO-T section
  encode private constructors and must be revised first (§7).

## 7. Handoffs

- **`design`(typecheck):** repoint `monomorphisation.md` §3.3's standing rule
  (file a new window to `arch`, no FIXME link) and `auto-curry.md`'s sentence
  before §3.2 (`arch` declined a general rule in S125; the local rule
  stands). Done in Phase 3; `arch` deleted 0776.
- **IO-T re-decision, this packet's section 2.1:**
  - `design`(int), `design/int/s125-binary-clean.md`: seed `IO` with no
    constructors and `pure` with `insert_primitive`; drop `ConstructorAccess`,
    the `Ast`-bodied template and the falsifier on `infer_constradt`; add the
    bootstrap unit assertion of no `IO` constructor and no `IO.` key.
  - `design`(typecheck), `design/typecheck/io-types.md` and
    `typecheck.md`'s IO-T section: drop `ConstructorAccess`, `resolve_member`,
    the written-member table and the staging falsifier; `IO`'s constructor
    set is empty; `pure` is a host-promised `BuiltinFn` typed from its
    scheme.
  - `design`(backend): the `pure` lowering beside `emit_bind_node`, its
    spark treatment, and the removal of `pure_payload_type` and the
    `ConstrADT` `IO` case at its three call sites.
  - `qa`: the falsifying spellings (`Pure`, `primitives/Pure`, `IO.Pure`,
    `primitives/IO.Pure`, a bare `(Pure x)` arm on an `IO` scrutinee) now
    each refuse as unknown names; the private-ctor member-read cells are
    not needed. First-class `pure` needs a cell.
- **`qa`:** trace cells for `#io` and `#closure`; FIXME 0929's census
  remainder; attribution stands for 1105 to 1108 under the new build order.
- **`spec`:** S124-Q19, with no architecture dependency.
