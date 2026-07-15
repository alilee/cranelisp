# Sprint 110: Backend pure keyed-lookup consumer — the resolution-boundary centrepiece

**Status**: PHASE 3 DESIGN

**Goal**: Land the user-directed S110 **centrepiece (0583)** — make the backend a
**pure keyed-lookup consumer**: typecheck emits fully-qualified SYMBOLS *and*
fully-qualified TYPES on every mono-view reference, and the backend performs **zero**
name resolution and **zero** bare-type-name resolution. This collapses the recurring
"two resolvers, one name" mirror class at its architectural root (3× in S109 alone).
Plus the two S109-close items ruled into S110: the **stdlib-compile smoke gate (0605)**
and the **index-feed write-race isolation fix (0604)**.

**Audit**: {Phase 4 — the 0583 FIXME recommends pulling `cranelisp-backend` + the
resolution seam forward in the rotation (the S107 backend audit MISSED the resolution
boundary; the new "bounded-context responsibility boundary" lens is why). Candidate:
`cranelisp-backend`. Confirm at Phase 4.}

## Scope (user-approved 2026-07-15 — breadth: BROAD)

A **centrepiece-led, broad** sprint. The through-line is the resolution boundary:
one initiative (0583) dissolves an entire recurring defect class, and the class's
sibling instances (the ADT-registration mirror R-2; the value-position mint class
0585; the four-mirror type-var resolver 0590) fold under it as the same
"one operation, re-derived per site, must be single-sourced" theme. The two
non-negotiable S109-close carries (0604/0605) ride alongside as their own tracks. The
user chose **broad**: the src/-audit hygiene track (R-1/R-3/R-4/R-5/R-6 → FIXMEs
0606–0610) drains in-sprint while backend is the audit-rotation focus, and **all three
adjacent standing carries** (vec-assoc UAF, R16/R17, C-4) are pulled in. Per "no defer
for size; decompose into waves," Phase 4 splits this — scope is not shrunk.

### 1. CENTREPIECE — backend pure keyed-lookup consumer (0583) — LEAD
`/arch`-designed, **phased one reference-kind per wave**, each following the S109 `§10`
template (resolved-FQ on the mono node → keyed read → hard `CodegenError` on miss,
Principle 18, no fallback). Two axes:
- **Symbol axis** — delete `resolve_driven` + the arbitrary-order `symbol_tables.iter()`
  global scan and the ten `resolve_*` entry points in
  `crates/cranelisp-backend/src/compiler/resolution.rs`. Per-kind waves: call targets
  (`resolve_got_target`, highest-traffic — start here), constructors (patterns done in
  S109 §10), effect/extern targets, arity/callable/callee-summary, vec-query. Each wave
  records the already-computed FQ on the mono node; backend does `tables.get(fq).get()`.
- **Type axis** — audit the mono view + backend (`schema.rs` layout-hash, ADT
  tag/layout, drop-glue, `heap.rs`) for any bare-type-name resolution/keying; ensure
  every type reference carries `FQTypeName` from typecheck and the backend keys on it.

**Folds under the centrepiece** (same mirror class):
- **R-2 (S109 src audit)** — `bootstrap.rs::register_synth_adt` ↔ typecheck's
  `register_type_def_with_ctor_infos` near-line-for-line mirror (S109 had to hand-apply
  the canonical-key change to BOTH). One ADT-entry builder in `cranelisp-types`, two thin
  callers. `/arch`-owned (a types-crate interface question).
- **0585** — value-position monomorphisation must be uniform across ALL value positions
  (Apply arg / Let / if-branch / match-arm / vector element), not per-position
  whitelisted (3rd instance of the class). The S109 *instance* was fixed (0571.2); this
  is the **class** record — the structural guard/invariant so a 4th position can't
  reintroduce the leak. `/arch` structural design + `/qa` value-position × {mint,die}
  matrix.
- **0590** — the written-type-var resolver is FOUR mirrors (`traits/type_resolve.rs` ×3
  + `form.rs`), each minting on its own. Same "one resolver" theme; `/design` (typecheck)
  single-source refactor. **Independent of 0583's backend seam** (S109 corrected the
  "folds in" premise) — co-scheduled for thematic coherence, sized as its own wave.

### 2. Stdlib-compile smoke gate (0605) — PROCESS, must-have
The coverage gap that let 0604 ship invisibly: stdlib self-tests are not in
`cargo nextest`; a compiler regression that breaks stdlib importability has zero CI
signal. Tier-1 gate: an e2e family behind
`use_workspace_stdlib_for_stdlib_conformance_only()` that `--run`s a program importing
**every top-level stdlib module** (enumerated at test time, not hand-listed), asserting
clean compile + exit 0; the failing MODULE is named. `/qa` design (gate in
`tests/plan/s109-attribution-index-feed-race.md §6`) → `/testing` build. Same infra wave
candidate: the `agent_flag_errors_on_non_agent_build` build-interleave race (nextest
profile/ordering fix). Tier-2 (stdlib self-test execution) sized separately, not S110.

### 3. Index-feed write-race isolation (0604) — DEFECT, must-have (user-ruled S110)
The background stdlib file-index feed racily writes a phantom public
`bit-and → primitives/bit-and` into the live `prelude` table, spuriously poisoning
`num.bits.test`'s legitimate `super`-import (blocks 27 self-tests). Root: the indexer
typechecks candidate modules through the real import-installing path against the LIVE
`symbol_tables`, then "undoes the residue" (R13) — mutate-live-then-undo, concurrent with
compiles, is the defect surface. **Durable cure = isolation by construction** (indexer
typechecks into staging/discard substrate, never live), NOT per-interleaving patches
(S61→S93 heisenbug lineage). `/dev` (int) + `/design` (int) records the isolation
contract. **Verify behaviorally** — ≥25-iteration sweep of the deterministic recipe on
the real stdlib lands WITH the fix (false-green-from-perturbation risk is why S109
carried it). Distinct crate/seam from 0583 (int shared-state isolation vs backend BC
violation) — thematically adjacent, may wave together.

### 4. src/-audit hygiene track (R-1/R-3/R-4/R-5/R-6 → FIXMEs 0606–0610) — IN SCOPE (broad)
Drains the S109 `src/` audit debt while backend is the rotation focus. **src-touching
work is SERIAL** (worktree isolation broken); these overlap files (repl.rs, process_form)
so Phase 4 pins an order. R-2 is not here — it folds into the centrepiece (§1).
- **0606 (R-1)** — decompose the 5,103-line `repl.rs` god-file (`repl/{search,format,
  commands}.rs`); `/dev` src/ + `/design` int cut sign-off (0580 template), public-api
  zero-diff.
- **0607 (R-3)** — `design/int/` currency pass: `int.md` as-built rewrite, surgical
  `agent.md §2.2` fix (documents a RETIRED classifier with a now-wrong MUST-NOT warning),
  44-doc sprawl triage (0578 template); `/design` int.
- **0608 (R-4)** — over-budget function batch worst-first (`main.rs::run` 394L/9 params,
  etc.) + narrative relocation into `design/int/`; `/dev` src/.
- **0609 (R-5)** — S87 residue (dead-code allows, `extra_jit_symbols` vestige, production
  unwrap) + the phantom-shim reachability verdict; `/dev` src/ + `/qa`/`/design` typecheck.
- **0610 (R-6)** — hygiene: gitignore `agent_trace.txt` + stray `user.cl`; refresh stale
  `lib.rs` comments; `/dev` src/.

### 5. Adjacent standing carries — IN SCOPE (broad)
- **vec-assoc UAF ×2** (backend RC/heap soundness, nondeterministic garbage) —
  co-scheduled since 0583 opens the backend and the audit rotation lands there. Repro
  owed (`/testing`, stdlib-free); backend triage.
- **R16/R17** — return-type-poly ambiguity *error quality* (dispatch WORKS; only the
  unresolved-case message leaks `__expr`-no-GOT-slot instead of clean §3.11). **Coordinated
  typecheck+int** change-set (dispatch-selected-no-impl signal + `src/exe.rs::validate_main`
  entry-ambiguity). The S109-close fix-now decision is now YES (broad).
- **C-4** — multi-arity-call-from-`main` "no main" misdirect (int/overload batch,
  `lifecycle.rs::lookup_main_code_ptr`). Repro + attribution triage owed.

### Longer carries (NOT pulled in)
- **0528** ownership_reuse, **S107** deftype_ctor_trailing — long-known carries.
- **0553** ownership instantiation entry point — Phase-H theme, carry.
- **0463** network-poll example — Phase 6 candidate.
- **0050/0052** — display-protocol / learn-system — blocked/user-deferred; not 2×-forced.
- **0589** (frontend type-var routing — in-crate backstop landed, no live bug),
  **0595** (rigid-unify structural hardening) — W6 residuals; low-pri, ride 0590's wave
  if that lands.
- **0603** — spec §3.3.4 let-generalize parenthetical (safe direction, `/spec`) — verify
  whether S109 landed it; if not, tiny `/spec` fix.

### Out of scope (deferred, with rationale)
- **0577 threads C/D** (primer→99%, gap loop) — deferred WITH scenario testing; mine the
  observability signal (landed S109) first. Target: after scenarios seeded.
- **Phase H proper** (R3 machinery sprint → increments I/II → `--release`) — the
  centrepiece is a **Phase-H enabler** (backend-consumes-FQ is exactly the ownership
  codegen seam), but the ownership machinery sprint is the *next* Phase-H step, sequenced
  after 0583 cleans the boundary. Not opened this sprint.

## FIXME debt

| FIXME | Target skill | Status | Notes |
|---|---|---|---|
| 0583 | /arch | open | **CENTREPIECE** — backend pure keyed-lookup consumer (FQ symbols + FQ types) |
| 0585 | /arch | open | value-position uniform mint — class record + structural guard (folds under 0583) |
| 0590 | /design (typecheck) | open | four-mirror written-type-var resolver convergence (co-scheduled) |
| 0604 | /dev (int) + /design (int) | open | index-feed phantom-prelude write-race — isolation by construction |
| 0605 | /testing (+/qa design) | open | stdlib-compile smoke gate |
| 0606 | /dev (src/) + /design (int) | open | R-1 — decompose repl.rs god-file (5,103 lines) |
| 0607 | /design (int) | open | R-3 — design/int/ currency pass (int.md, agent.md §2.2, doc sprawl) |
| 0608 | /dev (src/) | open | R-4 — over-budget function batch worst-first + narrative relocation |
| 0609 | /dev (src/) + /qa/design (typecheck) | open | R-5 — S87 residue batch + phantom-shim reachability verdict |
| 0610 | /dev (src/) | open | R-6 — gitignore agent_trace.txt/user.cl; refresh lib.rs comments |
| 0589 | /design (frontend) | open | qualified-lowercase annotation mint hole — backstop landed, no live bug (low-pri) |
| 0595 | /design (typecheck) | open | rigid-unify structural hardening (W6 residual, low-pri) |
| 0553 | /dev (typecheck) | carry | ownership instantiation entry point — Phase-H theme |
| 0463 | /examples | carry | network-poll example — Phase 6 candidate |
| 0050 | /repl (blocked) | carry | list/seq pretty-printer — blocked on display-protocol impl |
| 0052 | /docs | carry | learn-system REPL feature — user-deferred S107 |

*(New FIXMEs from the audit disposition filed in Phase 1 once accepted.)*

## Audit disposition (S109 → `audits/src-s109.md`) — ALL SIX ACCEPTED (2026-07-15)

Disposition trail written to `audits/src-s109.md §4`. Broad breadth chosen → the full
src/-audit debt drains in-sprint.

- **R-1 — decompose `repl.rs` god-file** → **ACCEPTED → FIXME 0606** (`/dev` src/ +
  `/design` int cut sign-off).
- **R-2 — bootstrap↔typecheck ADT-mirror** → **ACCEPTED → folds into 0583** (§1); no
  separate FIXME.
- **R-3 — `design/int/` currency pass** → **ACCEPTED → FIXME 0607** (`/design` int).
- **R-4 — over-budget function batch** → **ACCEPTED → FIXME 0608** (`/dev` src/).
- **R-5 — S87 residue batch + phantom-shim verdict** → **ACCEPTED → FIXME 0609** (`/dev`
  src/ + `/qa`/`/design` typecheck).
- **R-6 — repo/comment hygiene** → **ACCEPTED → FIXME 0610** (`/dev` src/).

**`/audit` calibration (0583 finding):** the resolution-boundary violation was missed by
every prior audit. The "bounded-context responsibility boundary" lens (added S109, surfaced
R-2) is now a standing category; confirm the S110 rotation pulls `cranelisp-backend` +
the resolution seam forward (Phase 4).

## Architecture review (Phase 2) — `/arch`, 2026-07-15

**VERDICT: SIGN-OFF (with pinned revisions).** The broad scope is coherent; the
centrepiece is tractable and correctly framed as plumbing-not-new-logic; no bucket
needs re-scoping. Four pinned revisions/clarifications (marked ▲ below) bind Phase 3+.
Evidence base: `resolution.rs` read in full; mono-view carriers
(`cranelisp-types/src/{mono_expr,check}.rs`) read; all 26 backend resolver call sites
enumerated; a full type-axis survey of the backend (finding T below); the R-2 mirror
pair read side-by-side (`src/bootstrap.rs:131–285` ≡ `typecheck/src/adt.rs:123–211`).

### 1. The 0583 finding that reshapes the phasing — two facts the FIXME didn't have

**(F1) The transport already half-exists.** `MonoExpr::Var`/`MonoExpr::Apply` already
carry `resolved_call: Option<Box<ResolvedCall>>` — but only for trait-method /
sig-dispatch / auto-curry / builtin legs, and `ResolvedCall` carries **mangled names
and bare Symbols, not FQ identities** (no module leg). Every PLAIN reference (user fn,
primitive, ctor, effect, extern) rides `resolved_call: None` and is re-resolved by the
backend. Separately, typecheck ALREADY records every statically-resolved user-fn
reference as `FQSymbol` at the `infer_var` chokepoint (`checker.rs::record_user_fn_ref`,
the S101 `Def.callees` feed) — the FQ is computed and in-hand at exactly the seam the
carrier needs; the initiative is genuinely a recording change, not new resolution logic.

**(F2 — finding T) The type axis is ALREADY CLOSED except for one kind.** Full backend
survey: every type-identity read (`heap.rs` classify/mixed-adt, drop glue in
`rc_emission.rs`/`vec_codegen.rs`, `schema.rs` layout-hash closure, `trace_codegen.rs`
descriptor baking, `context.rs::lookup_type_def`/`ctor_meta_at`/`constructor_metas`)
keys on an `FQTypeName` read off the node's `Type::ADT`/`ConcreteType::ADT` — direct
two-level keyed reads through the single-sourced `cranelisp-types` readers
(`type_ctor_names`, `value_layout`, `member_key`). **Zero bare type-name resolution
exists.** The only bare resolver on the type axis is `context.rs:146
lookup_constructor(name: &str)` — constructor **construction/reference** position
(ctor `Apply` at `apply.rs:757/781`, nullary/data ctor `Var` at `literals.rs:202/218`,
ctor-as-value at `fn_as_value.rs:532`, plus two narrow synthetic-body fallbacks in
`match_codegen.rs:263/600`) — reaching `resolve_driven`'s arbitrary-order
`symbol_tables.iter()` scan. Pattern position was cured in S109 §10.
▲ **Revision 1: the sprint-plan "type axis" bucket re-scopes** from
"audit + FQ-ize schema/tag/drop-glue/heap" (already FQ — nothing to do) to
"ctor construction/reference folds into the symbol-axis waves as one more kind."
This SHRINKS expected work; it is not a scope cut — the end-state is unchanged.

### 2. The 0583 design shape (pinned now; full working doc + approved diff in Phase 3)

**One carrier serves every reference kind.** New span-keyed sidecar
`MethodResolutions.resolved_targets: HashMap<Span, FQSymbol>` (mirror of
`pattern_ctors`) + two mono-view fields
`MonoExpr::Var.resolved_target: Option<FQSymbol>` and
`MonoExpr::Apply.resolved_target: Option<FQSymbol>` (`#[serde(default)]`), populated
via a **required** `MonoExpr::from_expr` parameter (the §10 unforgettable-parameter
template, Principle 18). Semantics per §10.1: the FQSymbol is **the storage identity
under which the referenced `Def` actually resolved** (canonical `Type.Ctor` for sum
ctors; mangled-variant key for sig-dispatch/mono instances; the bare key otherwise) —
"whichever key HIT", recorded at the ONE typecheck resolution chokepoint. For
dispatch legs this makes `resolved_target` the module-bearing FQ of the mangled entry,
leaving `ResolvedCall`'s shape untouched (preferred over widening `ResolvedCall` —
one carrier, one backend read; `ResolvedCall` stays supplementary metadata for the
inline-builtin intercepts).

**Backend end-state**: ONE keyed fetch — `entry_at(&FQSymbol)` (the `ctor_meta_at`
generalisation) — then kind-discrimination on the ONE fetched entry's `DefKind`
replaces all ten resolvers: got-slot via `callable_got_slot()`, platform/poll via the
`PlatformEffect` variant, extern via `PrimitiveExtern`, vec-query via
`PrimitiveBody::Inline`, arity via `param_names.len()`, summary via `mode_summary()`,
ctor tag/meta via the `Constructor` variant. Carrier-miss or entry-miss =
**hard `CodegenError`** (Principle 18) — ▲ **Revision 2 (the Principle-8 guard): NO
soft fallback, ever, not even "temporarily".** A kind either reads the carrier with
hard-miss or still runs the untouched legacy path — a keyed-read-else-`resolve_driven`
hybrid is the half-resolver Principle 8 forbids and is the review's per-wave REJECT
criterion. `resolve_driven` never gains a sometimes-keyed mode; it only loses callers.

### 3. The phased wave plan (each independently correct-and-shippable)

| Wave | Content | Deletes | Shippability |
|---|---|---|---|
| **W0 — producer** (ONE coordinated `/dev` deployment, S109-W1 style; types diff `/arch`-pre-approved) | `cranelisp-types` carriers (sidecar map + 2 mono fields + `from_expr` required param); typecheck population at the resolution chokepoint for ALL statically-resolved reference kinds (user fns, primitives, ctors incl. construction position, effects, externs, mangled variants); **`CACHE_SCHEMA_VERSION` 18→19** same change-set | nothing | Behaviour-invariant: carriers ride unread; suite stays green; one schema bump for the whole initiative |
| **W1 — call seam** (`apply.rs` dispatch funnel — highest traffic, leads per the FIXME) | Callee dispatch reads `resolved_target` → `entry_at` keyed read; kind arms off the entry; ctor-`Apply` (`data_constructor_info`) included (finding T) | apply-site reach of `resolve_got_target`, `resolve_platform_effect_target`, `resolve_poll_effect_target`, `resolve_extern_target`, `resolve_callee_summary`, `lookup_constructor@apply.rs` | Whole kinds flip atomically w/ hard-miss; value seam still on intact legacy path |
| **W2 — value seam** (`literals.rs`, `fn_as_value.rs`) | Var/value refs read carrier: fn-as-value gate, closure-wrapper arity, vec-query discrimination, summary, nullary-ctor tag, ctor-as-value. **The 0585 guard lands here** (see §5) | `resolve_is_callable_target`, `resolve_func_arity`, `resolve_vec_query_primitive`, remaining `resolve_callee_summary` + `lookup_constructor` reach | Same atomic-kind rule |
| **W3 — deletion + residue** | Resolve the ONE identified bypass (below); then delete `resolve_driven` + `resolve_chain` + the `symbol_tables.iter()` scan + all ten entry points + `lookup_constructor`; `resolution.rs` shrinks to the two naming primitives (`got_data_symbol_name`, `inner_fn_discriminator_for`) | the resolver seam itself | End-state; the structural invariant becomes greppable (zero `resolve_*` in backend) |

**The one identified riskiest residual (W3 design question, named now):** bodies built
OUTSIDE the sidecar-threaded `from_expr` path — `lib.rs::lenient_mono_from_expr` +
the synthetic/lenient fallbacks at `match_codegen.rs:263` — have no carriers. Phase-3
design must either thread carriers through those view builders or prove-and-pin (unit
test) that the kinds reaching them are same-module/self-contained and give them a
scoped, non-driven keyed helper. This is exactly the class of hole that would otherwise
re-open the scan through the back door; it gets its own design subsection.

**Per-wave verification obligation:** each consuming wave's brief enumerates its call
sites (the §1 inventory is the checklist) and shows carrier coverage for each; any
backend-*synthesized* name (not a mono-node reference) gets explicit treatment. Fallback
posture if a late wave proves unreachable in-sprint: the shipped state after any
completed wave is coherent (fewer kinds keyed, legacy intact for the rest) — but carry
requires evidence per the no-defer-for-size rule, not habit.

### 4. Public-API / cross-crate impact table (per bucket)

| Bucket | `cranelisp-types` / public API | Cache | Cross-crate reach |
|---|---|---|---|
| 0583 W0 | `MethodResolutions.resolved_targets` (+1 field), `MonoExpr::{Var,Apply}.resolved_target` (+2), `from_expr` signature (−1/+1); baseline regen + `interfaces.md` + BC §3/§7 in the same change-set | **18→19** (the only bump this sprint) | typecheck (producer), backend (consumer, all internal — resolvers are `pub(crate)`, zero backend baseline movement) |
| 0583 W1–W3 | none | none | backend-internal |
| R-2 builder | +`AdtCtorSpec` (descriptor: name, typed named fields, `internal`, docstring, pre-allocated `got_slot`) + `build_adt_entries(fqtn, type_params, type_var_ids, adt_docstring, ctors, visibility) -> Vec<(Symbol, ModuleEntry)>` — pure, product/sum split + schemes + `ConstrADT` synth body + canonical `member_key`+bare-alias edges + `TypeDef` computed ONCE; callers keep their own inserters (typecheck's §8.6.5-aware staging insert; bootstrap's plain insert) and slot allocation | none (entry shapes unchanged) | typecheck `adt.rs` + `src/bootstrap.rs` become thin callers (one coordinated `/dev` change-set) |
| 0585 | none (folds into W2) | none | — |
| 0590 | none expected (typecheck-internal convergence); escalation path to `/arch` stays open per its FIXME | none | typecheck only; **independent of the 0583 seam** (confirmed — different files: `traits/type_resolve.rs` + `form.rs` vs `program.rs`/mono population) |
| 0604 | none expected. Contingency: if the indexer's staging/discard substrate needs a types-level primitive beyond the existing staging-view vocabulary, FIXME `target: /arch` — do NOT hand-roll a second staging shape in int | none | int-internal |
| 0605 | none | none | tests/ only |
| 0606–0610 | ▲ **Revision 3 (gate restated):** the binary has NO `public-api.txt` (BC §6) — the "pure decomposition" claim for 0606/0608 is gated by (a) **zero movement on any library crate's baseline** (none should be touched) and (b) e2e byte-identity + unit tier green. Do not invent a binary baseline to satisfy the letter of the claim | none | src/ only |
| vec-assoc UAF | none until triaged (repro first) | — | backend |
| R16/R17 | ▲ **Revision 4 (contingency flagged):** the "dispatch selected NO impl" signal crossing typecheck→int may need a types-level carrier (error variant or `CheckResult` field). Shape comes to `/arch` in Phase 3 with `/design` (typecheck)'s proposal — budget it in the wave, don't discover it mid-implementation | none expected | typecheck + int coordinated |
| C-4 | none | — | int |

**Landing discipline**: no types change-set lands in Phase 2 (S109 precedent held —
review-only phase, working tree left clean for `/sprint`). Phase 3: `/arch` authors the
working design doc (`design/arch/backend-keyed-consumer.md`: carrier contract, wave
briefs, the W3 residual ruling, per-site inventory) with the pinned W0 + R-2 diffs;
W0 executes as ONE coordinated `/dev` deployment (the `from_expr` signature change +
schema bump force cross-crate atomicity — a types-only landing would strand the
same-change-set bump rule); the R-2 builder may land `/arch`-side (additive, no
consumers, no serde change) with callers wired by `/dev`. Baseline-diff discipline
(regen via `cargo public-api --omit blanket-impls,auto-derived-impls -p
cranelisp-types`, `interfaces.md`, BC §7) applies to both change-sets.

### 5. 0585 — the structural-guard decision

**Ruled: the invariant is adopted; NO new machinery beyond what 0583 already builds.**
Three legs, two already in flight:
1. **One enumeration** — mint and die share the `for_each_child_expr` value-position
   walk (landed S109 0571.2; `/review` verifies the whitelist is actually deleted in
   the wave that touches it).
2. **The loud backstop is W2's keyed read** — under the carrier, a value-position `Var`
   whose target entry is a slot-less `Polymorphic` template hard-fails with a precise
   `CodegenError` ("generic value reference reached codegen without a mono instance"),
   in RELEASE builds too — strictly stronger than the FIXME's debug-assert candidate,
   and it replaces the misleading `undefined variable` leak (`literals.rs:191`). A
   4th value position cannot reintroduce a *silent* leak: it either flows through the
   shared walk (minted) or dies loudly at the keyed read.
3. `/qa`'s value-position × {mint, die} matrix proceeds as planned (unchanged).
The invariant's permanent manifestation: Principle 24 (§6) + a BC §2 (typecheck) note,
Phase 3. FIXME 0585 closes when W2 + the matrix land.

### 6. Recurring-mirror-class principle — decision

**NEW Principle 24 will be authored** (not an amendment — P7 states single-source but
does not bind the *stage* question; P17 is scoped to typecheck locality). Working
statement: **"Resolve once — a semantic identity (name, type, member, dispatch target)
is derived at exactly ONE pipeline stage and crosses stage boundaries as a resolved,
fully-qualified value; downstream stages perform keyed reads and hard-fail on a miss,
never re-derive."** Instances unified: 0583 (backend re-resolving names + the ctor
axis), 0590 (four typecheck resolver mirrors), 0585 (per-position re-derived mint
enumeration), R-2 (twice-derived ADT entry construction), and retrospectively the S109
§10/DC-11 class. Timing per the P21/P23 precedent and the close-only register rule:
**authored in Phase 3** (so the triad imports it during the waves — the import-block
trio update per `principles/CLAUDE.md` rides the same commit), **ratified at Phase 7
close**. The operative BC commitment ("the backend is a pure keyed-lookup consumer;
zero name resolution, zero bare-type-name resolution") is edited into BC §3 in Phase 3
regardless — BC statements are not register changes. This also discharges the
backend-CLAUDE.md contradiction the FIXME names (its "no trait knowledge, one dispatch
path" aspiration vs the live resolver).

### 7. Audit rotation — CONFIRMED

S110 pulls **`cranelisp-backend` + the resolution seam** forward, with the
"bounded-context responsibility boundary" lens as a standing category. Timing
recommendation to `/sprint`: schedule the audit AFTER the W3 deletion wave if the
schedule allows — the audit then assesses the end-state and its boundary lens verifies
the violation is structurally gone (grep-zero `resolve_*`), rather than auditing a
mid-migration tree. If waves slip, audit the as-is state and say so.

### 8. Coherence of the broad scope — confirmed, with ordering constraints for Phase 4

The through-line holds: §1–§3 buckets are genuinely one class (now nameable as
Principle-24 instances); 0604/0605 are correctly NOT conflated with 0583 (distinct
crate/seam — 0604's own FIXME records the non-fold; concur). Serial source-touching
constraints for Phase 4 to pin:
- **typecheck chain (serial)**: 0583-W0 first (it changes `from_expr` callers +
  `program.rs`), then 0590 (different files, same crate), then R16/R17's typecheck half.
- **backend chain (serial)**: W1 → W2 → W3; vec-assoc UAF triage/fix after its repro
  exists — schedule against the wave that has `apply.rs`/`heap.rs` open, don't
  interleave.
- **src/ chain (serial)**: 0604 early (must-have defect, `index_worker.rs`/`imports.rs`);
  **0606 before 0608** (the repl.rs decomposition changes the file map 0608's
  worst-first batch would otherwise churn against); R-2 caller wiring (`bootstrap.rs`)
  and C-4 (`lifecycle.rs`) slot anywhere in the chain; 0609/0610 small, late. 0607 is
  docs-only (`/design` int) and may run parallel to non-int work.
- 0605 (`/testing`, tests/ only) is low-collision; still serialize with any other
  tests/-touching work.
- Read-only/design-only work (0607, the 0609 phantom-shim verdict analysis, `/qa`
  matrices) may fan out in parallel per the standing rule.

**Sizing note**: this is a large sprint by wave count, per the user's broad ruling —
the decomposition above is what makes it executable; nothing is flagged unreachable
at review time.

### Next skills (Phase 3)

1. **`/arch`** (continuation): author `design/arch/backend-keyed-consumer.md` (carrier
   contract + pinned W0/R-2 diffs + W3 residual ruling + per-site inventory) + Principle
   24 (+ four import blocks) + BC §3/§2 edits + `interfaces.md`; land the R-2 builder.
2. **`/design` (typecheck)**: 0590 convergence note (its own wave, independent of the
   0583 seam) + the R16/R17 dispatch-signal proposal (escalate carrier shape to `/arch`).
3. **`/design` (int)**: 0604 isolation contract; 0607 currency pass; 0606 cut sign-off.
4. **`/qa`**: 0585 value-position matrix rows + the 0583 per-wave acceptance rows
   (kind-flip negatives: hard-miss pins per wave, mirroring §10.9's loud-miss pin) +
   0605 gate design confirmation.
5. Then `/sprint` Phase 4 wave/order pinning per §8.

## Skill plans (Phase 3)

### /design (typecheck)

**Task.** Two design deliverables authored (design-doc only; no source touched):

1. **FIXME 0590 — four-mirror `TypeExpr` resolver convergence.**
   `design/typecheck/type-expr-resolver-convergence.md`. The four parallel
   resolvers (`resolve::resolve_type_expr` + `traits/type_resolve.rs`'s
   `resolve_trait_type_expr` / `resolve_type_expr_hkt` / `resolve_type_expr_hkt_impl`
   + `form.rs::check_type_expr`) collapse onto the ONE `resolve::resolve_type_expr`
   behind a head-resolution `TypeExprCtx` (`self_type: Option<Type>` + a `ConVars`
   enum carrying HKT constructor-variable interception). Structural recursion +
   mint-on-miss + co-reference `var_map` single-sourced; the three free-function
   mirrors DELETED; the never-error `Named` fabrication arms ruled OUT (route
   through `resolve_terminal`). Staged: (A) mechanical `form.rs` collapse (drop
   `collect_type_var_ids`), (B) the `TypeExprCtx` convergence, (C) the rustdoc
   correction (trait sigs mint, they do not route `None`). **Standalone typecheck
   wave** (its own Phase-5 `/dev` deployment), independent of the 0583 backend
   seam. **No `cranelisp-types` touch / no cache bump / typecheck-internal
   `public-api.txt`** (`mod resolve` is private, zero baseline hits) — the `/arch`
   escalation path stays open but is NOT triggered.

2. **R16/R17 — the unresolved-return-poly-dispatch signal.**
   `design/typecheck/return-poly-dispatch-signal.md`. Signal = a return-poly
   dispatch UNRESOLVED after final substitution, grounded in the dispatch OUTCOME
   ("no impl selected"), NOT surface-type concreteness (which false-positived on
   `(add2 3 4)` in the S109 revert — the load-bearing negative). typecheck rejects
   ordinary body value positions directly at finalize with the shared §3.11
   message; the entry/eval RESULT position (`main` for `--run`/`--link`; `__expr`
   for REPL eval) typecheck cannot reject (Principle 19 — no entry designation),
   so the signal crosses to int. **Cross-crate carrier escalated to `/arch`
   (FIXME 0611)** with the recommended shape: a transient
   `CheckResult.unresolved_dispatch: Vec<UnresolvedDispatchSite>` field
   (typecheck-owned, int-consumed, NO `cranelisp-types` edit, NO cache bump — the
   set is empty for every valid program). Coordinated typecheck+int change-set;
   int half is `/design`+`/dev` (int).

**Refs.** `design/typecheck/type-expr-resolver-convergence.md`;
`design/typecheck/return-poly-dispatch-signal.md`;
`design/arch/fixmes/0611-r16-r17-unresolved-dispatch-carrier.md`;
`design/arch/fixmes/0590-resolver-mirror-family-convergence-onto-mint-capability.md`;
sources cited: `crates/cranelisp-typecheck/src/resolve.rs`,
`crates/cranelisp-typecheck/src/traits/type_resolve.rs`,
`crates/cranelisp-typecheck/src/form.rs`,
`crates/cranelisp-typecheck/src/traits/dispatch.rs`,
`crates/cranelisp-typecheck/src/program/finalize.rs`,
`crates/cranelisp-typecheck/src/result.rs`.

**Acceptance.** 0590: post-convergence there is exactly ONE `TypeExpr→Type`
minting walk (`/review` grep-criterion: zero `fresh_var`/`fresh_var_id` outside
`resolve_type_expr`'s `mint_free_var` closures; three deleted free functions);
the FV-13/FV-14 over-broadening guards stay green; the Named-tightening `/qa`
matrix (bare / qualified / unknown × {trait-sig, HKT-sig, HKT-impl}) is authored.
R16/R17: rows 16/17 flip from the `__expr`-no-GOT-slot leak to the clean §3.11
message; rows 13–15 stay green; `(add2 3 4)` (and every arg-directed dispatch)
stays computable and unflagged (the S109-revert fence); `/arch` ratifies the
FIXME-0611 carrier before the Phase-5 wave. Both are design-only this phase —
Phase-5 `/dev` (typecheck) + `/dev`/`/design` (int) implement.

### /design (int)

**Task.** Three design-doc deliverables authored (no source touched); all in `design/int/`.

1. **FIXME 0604 — index-feed write-race isolation contract.**
   `design/int/index-worker-isolation.md` (new; subordinate to `int.md` +
   the `heisenbug-race-closure.md`→`signature-body-prepass.md` isolation lineage).
   Records the **isolation-by-construction** cure: the background stdlib indexer's
   only output is the in-memory `importable_indices` rows; every intermediate
   (symbol tables / aliases / prelude-fallback / staging) is a function-local
   **discard substrate**, and the feed writes **no foreground-consumable cache
   artifact**. R13 becomes true by construction, not by cleanup. **Key finding:**
   the S91 refactor (`9ba2ca91`) already isolated the *in-memory* tables
   (`checked_typecheck_module` → `private_tables`), so the FIXME/attribution's named
   seam (mutate-live-then-undo in `index_branch_c`) is already cured — yet the defect
   still reproduces, because the feed still writes the **shared cache**
   (`shared.cache.record_source_hash`/`record_compiled` + a `.meta`) that a later
   real `/import` consumes as a cache-hit (§25.5). §3.3 severs that persistent-artifact
   channel; §3.1 flags the still-stale `index_branch_c` docstrings (retired
   mutate-live model) for `/dev` rewrite; §3.2 tightens the live `&shared.prelude_fallback`
   thread to a private snapshot. **Reviewer-greppable invariant** in §5 (zero
   `&shared.*` map into any install/typecheck/register call; zero `shared.cache`
   write on any index branch). **Contingency (Phase-2 Rev on 0604) evaluated and does
   NOT fire** — the substrate needs no new types-level staging primitive (a cloned
   `PreludeFallback` DashMap; the existing `SymbolTableAccess::cluster` view), so **no
   `/arch` FIXME filed**. Verify-first: `/dev`+`/testing` run the ≥25× trace sweep to
   LOCATE the residual writer (prime suspect = the cache channel) BEFORE patching
   (verify-fix-not-symptom).

2. **FIXME 0607 — `design/int/` currency pass.** (a) `int.md §3` rewritten to
   as-built (S81→S110 restructures: Wave-D landed → `eval.rs`/`repl.rs` split out;
   `session_v4/`+`process_form/`+`worker/` submodule dirs; `redefine.rs` transaction;
   phantom `scheduler_trace/` rename retired; per-file LOC no longer pinned — a
   subsystem+module-home map instead). (b) **Surgical `agent.md §2.2` fix**: the
   retired symbol-resolution classifier + its now-wrong "MUST NOT" warning replaced
   with the as-built **form-count rule** (`forms.len()==1 → Repl` else `Agent`,
   `symbol_is_known` NOT consulted; user ruling 2026-07-12, `src/agent/mod.rs:70-148`),
   the MUST-NOT now protecting the LIVE invariant. (c) HISTORICAL banners on 18
   superseded slice/working docs; a **doc-index** added to `design/int/CLAUDE.md`
   (0578 template: master / durable subsystem / active subordinate / reference
   lineage / historical). The full `agent.md` restructure stays deferred.

3. **FIXME 0606 — `repl.rs` decomposition cut sign-off.**
   `design/int/repl-decomposition.md` (new; the 0580 `program.rs` template — cut
   signed off first, mechanical move by `/dev` in Phase 5). The 5,234-line god-file
   cuts to `repl/search.rs` (the `/search` UI) + `repl/format.rs` (the `_doc`
   formatters) + `repl/commands.rs` (the `handle_*` battery, incl. `handle_imports`)
   + residual `repl.rs` (dispatch + prompt/banner/editor + the shared
   resolution/referer toolbox). Precise function→file boundaries with current line
   ranges, the shared-toolbox placement (§1.5), the `fq_arg_tests` three-way test
   split (§2), the FORMAT layout-render pressure valve (§1.6), and the
   behaviour-invariant / zero-library-baseline-diff acceptance contract (§4). Couples
   with deliverable 2 (`int.md §3.3` + `src/CLAUDE.md` module map update with the move).

**Refs.** `design/int/index-worker-isolation.md`; `design/int/repl-decomposition.md`;
`design/int/int.md §3`; `design/int/agent.md §2.2`; `design/int/CLAUDE.md`;
`design/arch/fixmes/{0604,0606,0607}-*.md`;
`tests/plan/s109-attribution-index-feed-race.md`; sources cited:
`src/session_v4/index_worker.rs`, `src/imports.rs`, `src/agent/mod.rs`, `src/repl.rs`,
`src/CLAUDE.md` §"Session/REPL module map".

**Acceptance.** 0604: the §5 grep is the `/dev`/`/review` structural criterion; the
≥25× real-stdlib sweep + write-seam unit test land WITH the fix (fail-on-revert);
twin guards stay green. 0607: `int.md §3` matches the tree (spot-check `session_v4/`,
`process_form/`, `repl.rs`); every superseded doc carries a banner; `agent.md §2.2`
describes the form-count rule. 0606: the cut is mechanical-and-behaviour-invariant
(golden REPL e2e green, zero library-baseline diff, no `repl/` file over ~1,500 lines).
All design-only this phase — Phase-5 `/dev` (src/) implements 0604's fix + 0606's move;
`/design` (int) updates the int.md/CLAUDE.md maps with the move.

## Notes

- **Phase 1 (2026-07-15):** scope drafted between sprints (S109 closed, archived). The
  S110 centrepiece (0583) is a **standing user directive** (S109 P5) — the backend runs a
  full name resolver instead of consuming FQ symbols/types from typecheck, the root of a
  mirror class that recurred 3× in S109. Two S109-close carries are non-negotiable S110
  (0605 process gate, 0604 write-race, both user-ruled). **Gates RESOLVED with user
  2026-07-15:** (a) breadth = **BROAD** — centrepiece + src/-audit-debt drain
  (R-1/R-3/R-4/R-5/R-6 → FIXMEs 0606–0610); (b) all three adjacent carries **IN**
  (vec-assoc UAF, R16/R17, C-4); (c) audit **ALL SIX ACCEPTED** (R-2 folds into 0583).
  Scope settled → advanced to Phase 2. **Phase 2 next:** `/arch` reviews the broad scope
  for coherence + the 0583 phasing (reference-kind wave sequence, symbol vs type axis),
  public-API impact (the `cranelisp-types` ADT-entry builder + any `FQTypeName` mono-view
  carrier + cache-schema bump), interim-architecture risk (Principle 8 — the phased
  delete of `resolve_driven` must not leave a half-resolver), and confirms the audit
  rotation pulls backend forward.
- **Phase 2 (2026-07-15):** `/arch` **SIGN-OFF with 4 pinned revisions** (all
  incorporated into §"Architecture review"). Two review findings reshape 0583: (F1) the
  FQ transport half-exists — typecheck already records `FQSymbol` at the `infer_var`
  chokepoint (S101 `callees` feed), so the initiative is a recording change, not new
  resolution logic; (F2/Rev-1) the type axis is ALREADY closed except ctor construction
  (schema/tag/drop-glue/heap all key on `FQTypeName`), which folds into the symbol-axis
  waves — SHRINKS the work. Pinned: one span-keyed carrier (`resolved_targets` sidecar +
  `MonoExpr::{Var,Apply}.resolved_target`), 4-wave plan (W0 producer + `CACHE_SCHEMA_VERSION`
  18→19 → W1 call seam → W2 value seam + 0585 guard → W3 delete `resolve_driven`);
  Rev-2 = NO soft fallback ever (per-wave REJECT criterion); **new Principle 24 "Resolve
  once"** authored Phase 3 / ratified Phase 7; R-2 builder shape pinned (`AdtCtorSpec` +
  `build_adt_entries`); 0585 guard = W2's hard `CodegenError` (no new machinery); audit
  rotation confirmed (backend, ideally post-W3). Named W3 risk: view-builders outside the
  `from_expr` path (`lenient_mono_from_expr`, `match_codegen.rs:263`) get a Phase-3 design
  subsection. Serial-chain ordering pinned for Phase 4 (§8). No types change-set landed in
  Phase 2 (review-only). Advanced to Phase 3.
