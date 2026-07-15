# Sprint 110: Backend pure keyed-lookup consumer — the resolution-boundary centrepiece

**Status**: PHASE 5 LANGUAGE (ACTIVE)

**Goal**: Land the user-directed S110 **centrepiece (0583)** — make the backend a
**pure keyed-lookup consumer**: typecheck emits fully-qualified SYMBOLS *and*
fully-qualified TYPES on every mono-view reference, and the backend performs **zero**
name resolution and **zero** bare-type-name resolution. This collapses the recurring
"two resolvers, one name" mirror class at its architectural root (3× in S109 alone).
Plus the two S109-close items ruled into S110: the **stdlib-compile smoke gate (0605)**
and the **index-feed write-race isolation fix (0604)**.

**Audit**: `cranelisp-backend` + the resolution seam (CONFIRMED Phase 4, per `/arch` §7).
Rotation pulled forward because the S107 backend audit MISSED the resolution-boundary
violation (0583 finding). Read-only, dispatched in the Phase 6/7 window — **ideally
post-W3** so it assesses the end-state and its "bounded-context responsibility boundary"
lens verifies the grep-zero (`resolve_*` gone). → `audits/cranelisp-backend-s110.md`;
disposed S111 Phase 1.

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
- **0603** — RESOLVED S109 (no FIXME file; §3.3.4 parenthetical now consistent with
  §3.4 monomorphic-`let`, `03-types.md:222`).
- **0612 (`/spec`)** — polymorphism-boundary sidenote. **USER-RULED 2026-07-15:** the
  monomorphic-`let` / rank-1 boundary is a deliberate language-definition line (retire the
  §3.5:388 "current implementation" hedge); `/spec` authors a detailed "supported vs
  decisively-not-supported" sidenote framing it as a **movable** boundary, then the
  *capability* (let-generalisation) is **PARKED** until a real limiting scenario appears.
  Doc-only, no compiler change, behaviour already GREEN-pinned. Dispatched S110; FIXME
  closes on sidenote landing.

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
| 0604 | /dev (int) + /design (int) | open | index-feed write-race — **attribution CORRECTED P3**: mutate-live seam S91-cured; real channel = shared-cache §25.5 write. `/dev` targets cache channel + trace-sweep-locates-first |
| 0605 | /testing (+/qa design) | open | stdlib-compile smoke gate |
| 0611 | /arch | open | R16/R17 unresolved-dispatch carrier — `/design` typecheck recommends transient `CheckResult.unresolved_dispatch` field (no types edit); `/arch` ratifies shape (filed P3) |
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

### /arch — 0583 design + Principle 24 + R-2 builder (2026-07-15, COMPLETE)

**Task**: execute Phase-2 "Next skills" item 1 — author the 0583 working design
doc, Principle 24, the BC edits; land the R-2 builder; pin the W0 producer diff.

**Landed** (two commits on main):
1. **R-2 ADT-entry builder** — `cranelisp_types::{AdtCtorSpec, build_adt_entries}`
   (`crates/cranelisp-types/src/adt_build.rs` + 4 unit tests; additive, no
   consumers; no serde/cache impact; `public-api.txt` regenerated +16 lines;
   `interfaces.md` §"ADT-entry builder" + BC §7 paragraph). Caller wiring
   (typecheck `adt.rs` + `src/bootstrap.rs` become thin callers) = ONE
   coordinated Phase-5 `/dev` change-set, behaviour-invariant.
2. **`design/arch/backend-keyed-consumer.md`** — the 0583 working design:
   one-carrier contract (§1: `resolved_targets` sidecar + 2 mono fields +
   REQUIRED `from_expr` param; per-kind "whichever storage key HIT" table),
   Rev-2 no-soft-fallback per-wave REJECT criterion (§1.2), backend `entry_at`
   end-state reader (§1.3), backend-synthesized-name treatment (§1.4),
   re-verified per-site inventory S1–S24 with wave assignment (§3 — the
   Phase-2 "26" reconciled; the SET binds, W3 grep gate is the criterion),
   four wave briefs (§4), the 0585 W2 guard (§7).
3. **W3 residual RULED** (§5): thread-carriers wins, executed as **typecheck
   = sole mono-view producer** (W0.b view totalization) — Phase-3 findings:
   the lenient arm's reach is full-spectrum (scoped-helper proof is FALSE for
   `__expr`/macro-clause bodies), synthetic bodies are `Span::SYNTHETIC` (span
   transport structurally unavailable → ctor identities populated DIRECTLY at
   synthesis, which also deletes match_codegen.rs:263/600's fallback need),
   and `jit.rs::compile_defn` has NO live caller (unit-harness only; stale
   rustdoc corrected in W3). `lenient_mono_from_expr` deletes in W3.
4. **Principle 24 "Resolve once"** authored (`principles/24-resolve-once.md` +
   index row + ALL FOUR import blocks arch/design/dev/review, same commit;
   **ratification = Phase-7 close**). BC §3 invariant 10 (backend pure
   keyed-lookup consumer) + BC §2 producer-obligation/0585 note +
   `overview.md` backend sentence + `design/arch/CLAUDE.md` row landed now
   (BC edits are not register changes).

**Pinned, NOT landed**: the full W0 producer diff (design doc §8) — carrier
fields, `from_expr` signature, typecheck `record_resolved_target` chokepoints,
W0.b totalization, backend test-harness sidecar population, and
`CACHE_SCHEMA_VERSION` **18→19** — ONE coordinated Phase-5 `/dev` deployment
(cross-crate atomicity: the signature change + bump must ride the typecheck
producer; carrier fields alone were deliberately NOT pre-landed).

**Acceptance/refs**: suite untouched by the landed change-set (additive;
`cargo check --workspace` clean; types unit tests green). Phase-2 impact table
refined honestly in §5: W0 grows by the lenient-builder relocation (types) +
the backend `lib.rs:905` view-selection flip (backend-internal); "W1–W3 zero
baseline movement" claim preserved.

**Interface completeness for `/qa`**: CONFIRMED — the design doc §9 enumerates
the acceptance surface (per-site checklist §3 = per-wave flip sets; §1.1
hard-miss negative families; §1.2 REJECT criterion; §4 per-wave verification
obligations incl. W0 byte-identity and the W2 0585 value-position × {mint,die}
matrix; §6 R-2 behaviour-invariance). `/qa` can draft the 0583 per-wave
acceptance rows from it directly.

**Next skills**: per Phase-2 §"Next skills" — `/design` (typecheck) 0590 +
R16/R17 proposal; `/design` (int) 0604/0607/0606; `/qa` acceptance rows; then
`/sprint` Phase-4 wave pinning (§8 serial chains; W0.a+W0.b are one schema
window).

### /qa — sprint-wide failing-test plan (2026-07-15, COMPLETE; Phase-3 exit gate MET)

**Plan location**: `tests/plan/PLAN.md` §"Sprint 110" (the drafting spec
`/testing` authors to in Phase 5). Risk register: `tests/plan/risks.md`
§"S110 risk read" (10 entries, S110-1…S110-10). Vocabulary add:
`class=shared-state-write-race` (tests/CLAUDE.md, per 0604 §Acceptance 4).

**Per-bucket row counts** (PLAN §S110):
- §A 0583: 6 W0 rows (invariance + CLIF byte-identity + cache 18→19 +
  totalization pins + the **W1 harness pin** KC-W0-6, blocking for W1) +
  10 kind-coverage verification rows (KC-K1…K10; verify-first, KC-K10
  operator-as-value the likely new cell) + 6 hard-miss negative rows
  (KC-N1…N6, **unit-tier by construction** — post-W0 a well-formed program
  cannot produce a missing carrier, so the loud-miss families are backend
  unit-harness fixtures, enumerated per the S108 Inc2 rule; KC-N6 is the
  local-variable false-positive fence) + 4 W3 rows (grep gate as structural
  acceptance, no-live-lenient pins, S19/S20 residue).
- §B 0585: 6-position × {mint, die} matrix; **the missing REDs are
  VP-3/4/5 (if-branch / match-arm / vector-element)**; KC-N5 is the arch
  ruling's loud backstop leg.
- §C 0590: 10-row behaviour-tightening matrix (bare/qualified/unknown ×
  trait-sig/HKT-sig/HKT-impl) — TX-1 the tightening positive RED, TX-5/TX-6
  the fabrication-deletion negative REDs, TX-8/TX-9 = FV-13/FV-14 must-hold
  fences; **blast-radius scout pinned BEFORE the flip** (`/dev` executes).
- §D R16/R17: the 2 committed REDs are the acceptance (RD-1/RD-2 flip);
  **RD-3 is the new load-bearing negative** — arg-directed dispatch result in
  an ordinary value position must not be flagged (the exact S109-revert
  cell), authored FIRST; 3-item typecheck/int unit enumeration; gated on
  `/arch` ratifying 0611.
- §E 0605: gate design CONFIRMED with two refinements — (1) enumeration is
  **RECURSIVE** public modules (top-level-only would miss `num.bits`, the
  0604 blast radius; `(mod- …)` subtrees excluded, which covers `.test`),
  (2) shape = **ONE enumerating test, per-module `--run` subprocess loop,
  aggregated all-failures report** (a generated test-per-module needs a
  hand-list, which rots). SG-2 = the `agent_flag_errors_on_non_agent_build`
  build-interleave infra fix, same wave.
- §F 0604: **attribution correction LANDED** in
  `tests/plan/s109-attribution-index-feed-race.md` §2 (mutate-live seam
  S91-cured; prime suspect = the shared-cache §25.5 write channel; the
  `--no-cache` boundary reconciled — it excludes stale-content, not the
  intra-session artifact race). 7 acceptance rows; IF-1 = the ≥25×
  locate-FIRST trace sweep gating the fix, with an explicit re-scope arm if
  the writer proves foreground.
- §G vec-assoc: repro-owed is **DISCHARGED** (committed S109,
  `tests/vec_assoc_param_mutate_return_uaf.rs`, reduced to 2 lines,
  stdlib-free, rc-miscount/premature-free evidenced); 5 rows = the 2 RED
  flips + unit enumeration + **VA-4 polarity-inversion fence**
  (`vec_cow_value_use_leak.rs` must stay green) + CLIF-first triage note.
- §H C-4: repro DISCHARGED (committed S109,
  `multi_arity_call_from_main_batch_no_main_neg`); attribution triage note
  written (int batch-entry candidate, two-hypothesis discrimination, explicit
  re-attribution arm if the seam lands in typecheck); 3 rows.
- §I 0609 phantom shim: **VERDICT — UNREACHABLE post-0571 → `/dev` DELETES
  the shim** (PLAN §I records the three-leg basis: MacroInMem/Type gaps have
  no live producers; the sole child-path synthesis is `lookup`'s probe whose
  post-0571 gap selection surfaces the abs gap; the residual abs-hard-error
  arm probed empirically in 4 shapes — the honest visibility error surfaces
  every time). 3 deletion pins, incl. **D-3: the recommended structural
  closure** (propagate the abs probe's hard error at `checker.rs:1325`,
  making the child gap unproducible — converts the one empirical leg to
  structural).
- §J R-2: 4 behaviour-invariance rows (writer-twin check via the existing
  DC suite = the must-hold set; mirror-deleted `/review` criterion;
  slot-allocation-stays-caller-side unit pin).
- §K 0606/0608/0610: invariance gates only (Rev-3 — zero library-baseline
  movement, golden-REPL byte-identity, unit tier green); no new rows.

**e2e-vs-unit enumeration**: the plan's central call — 0583's hard-miss
negatives are unit-tier by construction (with the KC-N6 fence), the flip
positives ride the EXISTING e2e suite as invariance guards (verify-first
kind sweep), and W0 invariance gets a CLIF byte-identity harness across the
six lenient entry classes. Every unit deferral is enumerated in its row.

**Coverage-gap findings**: (1) operator-as-value (KC-K10) likely has no e2e
cell — author before W2; (2) the S109 AL-3/AL-4/private-member diagnostic
rows must be verified-authored before the 0609 shim deletion (D-1); (3)
0585's if/match/vec cells confirmed absent from
`generic_value_use_mono.rs` — the named missing REDs; (4) SG-1 top-level-only
would have been a false gate — recursive enumeration required.

**Phase-3 exit gate: CONFIRMED** — the design surface (`backend-keyed-consumer.md`
§9 + the two typecheck notes + the int isolation contract) is sufficient to
draft every failing test sprint-wide; `/testing` has a complete authoring
order (PLAN §S110 "Phase-5 sequencing note"). → `/sprint` Phase-4 wave org.

### /testing (P5-S1) — QA-first failing set (2026-07-15, COMPLETE)

Authored the sprint-wide failing e2e set from PLAN §S110, failing-not-ignored,
RED-for-right-reason at HEAD. Full suite: **4557 tests, 4544 pass, 13 fail, 1
skip** (~81s). Every RED traces to an in-scope S110 row or a pre-existing open
defect — **no genuine regressions**.

**6 NEW REDs authored (RED-for-right-reason confirmed):**
- **§B 0585 VP-3/4/5 die legs** (`generic_value_use_mono.rs`):
  `generic_value_in_if_branch_indeterminate_neg`,
  `…_in_match_arm_indeterminate_neg`, `…_as_vec_element_indeterminate_neg` — each
  leaks `undefined variable: gcount` at codegen instead of the §3.11 ambiguity
  (`check-gate-leak`); land green under W2. The 3 MINT legs
  (`…_mints_and_runs`) are GREEN (pin S109 0571.2's fix; must-hold).
- **§C 0590 TX-1** (`spec_07_traits.rs`) `trait_method_sig_bare_user_type_resolves`
  — bare user type in a trait-method sig errors `unknown type: MyType`
  (mirror-1 `wrong-reject`); green post-convergence.
- **§C 0590 TX-5** `hkt_trait_sig_unknown_named_errors_neg` — an unknown Named in
  an HKT trait sig is silently fabricated (deftrait "succeeds"); must ERROR
  post-convergence (mirror-2 `silent-accept`).
- **§E 0605 SG-1** (`stdlib_conformance.rs`, new file)
  `stdlib_all_public_modules_compile_and_run` — recursive public-module enum
  (37 modules; skips `prelude.cl` + `(mod- …)` subtrees, no hand-list) +
  per-module `--run` subprocess loop + aggregated report. **36/37 compile
  clean; `derive` FAILS** (`parse error … unexpected quasiquote form — should
  have been expanded`, derive.cl:5306). Surfaced signal per PLAN "report, don't
  skip" — see handoff below.

**GREEN pins/fences authored (must-hold across their waves):** RD-3
`arg_directed_dispatch_result_in_value_position_not_flagged` (the R16/R17
false-positive fence, `(let [r (add2 3 4)] r)` → 7); TX-8
`annotation_unknown_uppercase_named_still_errors_fence` (FV-13); TX-9
`trait_path_resolution_unaffected_by_mint_fence` (FV-14).

**Pre-existing S110-acceptance REDs verified RED-for-right-reason (flip at their
waves):** RD-1/RD-2 (`spec_03_types`), C4-1
(`multi_arity_call_from_main_batch_no_main_neg`), VA-1/VA-2
(`vec_assoc_param_mutate_return_uaf`; VA-2 = `corrupted double-linked list`
SIGABRT under `--link`). VA-4 inversion fence (`vec_cow_value_use_leak.rs`)
GREEN; IF-4 0604 twins GREEN (poison intact). D-1 diagnostic rows (AL-3/AL-4 +
`private_fq_member_errors_not_displays_mode_uniform_neg`) all GREEN — cover the
0609-shim-backstopped behaviour before deletion. KC-K10 operator-as-value
covered by existing `operator_as_first_class_value` (verify-first).

**Deferred to /dev unit tier (enumerated):**
- **TX-6** (0590 mirror-3, HKT impl method unknown Named) — NOT e2e-expressible
  well-formed: an impl-method type annotation inherits the trait's `(f a)`, so
  the fabricated empty-module ADT MISMATCHES rather than silently accepts,
  masking the mechanism. Unit obligation over `resolve_type_expr_hkt_impl`: (i)
  unknown Named leaf ERRORS `unknown type`; (ii) known in-scope Named resolves
  (positive control); (iii) error names the unknown type. Comment in
  `spec_07_traits.rs` records the enumeration.
- **KC-N1..N6** (0583 hard-miss families) — unit-tier by construction (a
  well-formed program never carries a missing carrier post-W0); enumeration is
  the PLAN §A.2 table, handed to `/dev` (backend harness) at the W1/W2 gate.
- **KC-W0-3** cache rows (18→19 stale-cache neg) — author IN the W0 change-set
  (the schema bump doesn't exist on HEAD; a RED now would be meaningless);
  DC-9/DC-14 template.
- **KC-W0-4/5/6, TX-10, RD unit set, IF-2, VA-3, C4-2, AB-1/AB-4, D-2/D-3** —
  `/dev` unit obligations per their PLAN rows (unchanged).

**Handoffs / flags to /qa + /sprint:**
- **SG-1 `derive` signal** → `/qa` attribution: `derive` (macro-support module,
  `(import [prelude [])`, quasiquotes in `defn-` bodies) fails to compile via
  `[*]` import with `unexpected quasiquote form — should have been expanded`.
  NOTHING in the corpus imports/uses `derive` today, so it is uninvoked. This is
  INDEPENDENT of the 0604 race SG-1 was expected to gate (it is a
  quasiquote-handling/parse failure), so SG-1 will NOT auto-green when 0604
  lands. `/qa` to attribute: real defect (→ `/dev`) vs enumeration refinement
  (exclude `derive`). Gate lands RED per the "report, don't skip" directive.
- **SG-2** (`agent_flag_errors_on_non_agent_build` build-interleave) → FLAGGED,
  not actioned. The interleave (an `--features agent` build clobbering the
  non-agent `target/debug/cranelisp` mid-suite) does not reproduce under a
  single-profile `cargo nextest run` (the standard suite compiles only the
  non-agent lane; the agent-feature tests are `#[cfg(feature = "agent")]`).
  Fixing/validating a nextest-profile/target-dir isolation needs the dual-build
  orchestration that isn't part of the standard run; an unvalidated
  `.config/nextest.toml` change risks the suite. Routed to `/qa`/`/dev` with the
  dual-build acceptance ("agent e2e family passes 3× consecutive, no retry").
- **IF-7 `class=shared-state-write-race` retro-tag** — applied WITH the 0604 fix
  (post-fix, per the row), not now.

### /qa (P5-S1 attribution) — SG-1 + SG-2 verdicts (2026-07-15, COMPLETE)

Both P5-S1 flags attributed; record `tests/plan/s110-attribution-sg1-sg2.md`;
FIXMEs 0613/0614/0615 filed; PLAN §E rows + risks.md (S110-10 amended, S110-11
added) updated.

**SG-1 (`derive`): REAL DEFECT — layered, two owners. NOT an enumeration
refinement.** The gate did its job; excluding `derive` would recreate the 0605
blindness.
- **Layer 1, compiler (`/dev`, FIXME 0613):** quote/quasiquote are NEVER
  desugared outside macro-clause compilation — sole production caller of
  `expand_quasiquotes` is `src/process_form/macro_clause.rs:53`, vs the stated
  desugar-on-every-form contract (frontend `lib.rs:48`,
  `design/frontend/frontend.md:127`); likely dropped in the S76 W-Macro
  migration. Minimal repro (stdlib-free, REPL ≡ `--run`):
  ``(defn helper [x] `(if ~x 1 0))`` → `unexpected quasiquote
  form — should have been expanded`. This is what derive.cl:5306 (line 166,
  first `defn-` template) hits — no macro invocation involved. One-line /spec
  user confirmation requested (0613); default disposition is the fix.
- **Layer 2, stdlib (`/stdlib`, FIXME 0614):** fixing layer 1 does NOT green
  the gate — derive.cl's macros call ~30 same-module `defn-` helpers, which
  §9.3.4 forbids and the compiler ENFORCES (probe-verified diagnostic). The
  module has never compiled on the v4 pipeline; its S87 tail comment
  mis-attributes the failure.
- **Disposition:** gate stays RED, failing-not-ignored, tracing to 0613+0614.
  **Fix-vs-carry: CARRY both to S111** (uninvoked module, broad sprint, 0613
  wants a small seam ruling — int chokepoint vs inside `build_form`; `/sprint`
  may pull 0613 into W-SRC if slack). In-sprint obligation: `/testing` commits
  the 1-line narrow repro + quote-family matrix (0613 §/testing request).

**SG-2 (`agent_flag` interleave): build-artifact provenance race — `/testing`
infra, FIX in-sprint (rides the planned W-GATE lane). FIXME 0615.** The
harness hardcodes `target/debug/cranelisp` (`e2e.rs:368–371`); the agent lane
rebuilds that SAME path, so an interleaved `--features agent` build swaps the
binary mid-suite and feature-OFF guards exec a feature-ON binary. Deterministic
in binary provenance — not an assertion flake (forbidden dispositions don't
apply). Fix shape: agent-lane `CARGO_TARGET_DIR=target/agent` via a committed
launcher script + lane-aware binary resolution in `materialise()` — a nextest
setup-script ordering fix alone CANNOT cure a between-invocations race.
Acceptance: /testing's 3×-consecutive bar + a deliberate dual-build clobber
check, scheduled when no other agent is testing. **Separate root from 0604**
(build substrate vs runtime SharedState) — not folded.

### /dev (W0) — 0583 producer change-set (2026-07-15, LANDED)

ONE coordinated cross-crate deployment across `cranelisp-types` +
`cranelisp-typecheck` + `cranelisp-backend`, per `backend-keyed-consumer.md` §8.
**Suite: 13 pre-existing S110 REDs UNCHANGED (zero new failures); +2 new unit
rows GREEN** (`cache_v18_meta_rejected_after_resolved_target_carriers`,
`var_and_apply_carry_resolved_target_from_sidecar_keyed_by_span`).
`public_api_relocations` flips GREEN (types baseline regenerated). Backend +
typecheck `public-api.txt` = ZERO movement (verified). Behaviour-invariant by
construction — carriers ride UNREAD until W1.

**Landed (W0.a — carriers + producer + schema):**
- `cranelisp-types`: `MethodResolutions.resolved_targets` span-keyed sidecar
  (`check.rs`); `MonoExpr::{Var,Apply}.resolved_target: Option<FQSymbol>`
  (`#[serde(default)]`); `from_expr` gains the REQUIRED `resolved_targets`
  third param (§10 unforgettable template), `Var`/`Apply` arms populate by span.
- `cranelisp-typecheck`: `record_resolved_target` writer at the `infer_var`
  F1 chokepoint (`checker.rs`), recording the terminal STORAGE FQ for EVERY
  table-resolved reference kind (any `ModuleEntry::Def` — user fn, primitive,
  ctor, effect, extern, mangled/mono variant); env-shadow gate skips locals.
  Sidecar threaded through `FormCheckResult`/`ModuleCheckAccumulator` +
  `build_concrete_codegen_view` + the finalize codegen-view rebuild + the
  `monomorphise_call` direct `from_expr` — exact mirror of `pattern_ctors`.
- `cranelisp-backend`: `CACHE_SCHEMA_VERSION` **18 → 19** (same change-set);
  test-harness `from_expr` callers updated.
- Baseline: `cranelisp-types/public-api.txt` regenerated (2 mono fields +
  sidecar + `from_expr` signature + the §5 `lenient_from_expr` relocation) —
  matches the /arch-pinned §8 diff exactly, nothing beyond it.

**Landed (W0.b — partial, the SAFE clauses):**
- `lenient_mono_from_expr` RELOCATED to `cranelisp_types::MonoExpr::lenient_from_expr`
  (beside `from_expr`, same two REQUIRED sidecar params) — ONE home for view
  construction. The backend entry point is now a thin delegator (byte-identical:
  empty sidecars ⇒ `None` carriers, exactly as before).

**Landed (R-2 — typecheck half):**
- `adt.rs::register_type_def_with_ctor_infos` rewired onto
  `cranelisp_types::build_adt_entries` (thin caller: pre-allocates GOT slots +
  builds `AdtCtorSpec`s, inserts returned pairs — `Def`/`TypeDef` verbatim,
  bare `Import` aliases through the extracted §8.6.5 contest classifier
  `install_bare_ctor_alias`; product accessor synthesis kept as the
  typecheck-only follow-on). The dead `register_constructors` + `CtorBuild.tag`
  deleted; `build_constructor_scheme` demoted to `#[cfg(test)]`. Behaviour-
  invariant — all adt/DC/exemplar suites GREEN, ZERO cache impact (entry shapes
  unchanged). `src/bootstrap.rs`'s half wires in the src/ track later (per
  dispatch).

**DEFERRED within-W0 (flagged to /arch + /sprint — NOT improvised):** the W0.b
**full totalization flip** — backend `lib.rs:905` view-selection hard-error arm
+ typecheck populating `codegen_view` for ALL codegen-reached entries
(ctors/accessors) + synthetic-body `resolved_ctor`-at-synthesis. Rationale: the
flip retires the `requires_codegen_view` bypass and makes `lib.rs:909` a hard
error, which requires typecheck to view-populate Constructor-kind entries across
new registration seams. Its shippability gate is **CLIF byte-identity**, and I
have no automated byte-identity harness to verify the flip (KC-W0-2 is
`/testing`'s W0 deliverable). Improvising it risks a silent codegen regression
the passing suite would not catch (suite-green ≠ byte-identical CLIF). **W1/W2
do NOT depend on it** — they consume the `resolved_target` carrier, which IS
delivered; only **W3**'s deletion of `lenient_mono_from_expr` depends on the
totalization. Recommend it lands as a follow-on W0.b change-set gated on the
KC-W0-2 golden-CLIF harness, before W3. `lenient_from_expr` is already relocated
so that follow-on is a backend-`lib.rs` + typecheck-view-population edit only.

### /review (W0) — 0583 producer change-set review (2026-07-15, COMPLETE)

Reviewed `41fab350` against `backend-keyed-consumer.md` §1/§3/§4/§8/§9. **Verdict:
NOT clean to build W1 on as sequenced** — the crate-level machinery is sound and
behaviour-invariant (keep it), but the producer is incomplete on three reference
legs and the W0.b deferral under-claims W1's dependency. Two Blockers filed:

- **Blocker — FIXME 0616 (`target: /dev`, typecheck): producer records only a
  subset of the resolutions `lookup` performs.** (1) NO Apply-span writer exists —
  all dispatch-selection seams write `resolved_calls` only, so
  `MonoExpr::Apply.resolved_target` is structurally always `None`; post-W1 every
  trait-method/sig-dispatch/auto-curry call (incl. operators) hard-fails.
  (2) Self-recursive references are filtered by the env-shadow gate
  (`body.rs:652` binds the defn name as a local) — every recursive fn hard-fails
  at W1; the `record_user_fn_ref` self-edge skip must NOT be mirrored here.
  (3) Dotted `Type.member` refs resolved via `resolve_dotted_member_entry` (the
  home-module probe) are invisible to `record_resolved_target`'s narrower
  `scope_resolve` re-probe — a type-only import + `(Maybe.Some 3)` gets no
  carrier. Root cause shared: the writer is a SECOND, narrower resolution probe
  instead of capture-at-the-resolving-seam (§1.1's binding property; Principle
  24 applied to the producer itself). Same-sprint fix: W0 top-up change-set in
  the same schema-19 window (0472 precedent), before W1.
- **Blocker — FIXME 0617 (`target: /sprint`): W0.b flip must precede W1, not
  merely W3.** Lenient-built bodies (generic templates, `__expr` disp-3,
  macro-clause — §5 finding 1: full reference-kind spectrum) get EMPTY sidecars
  from the backend delegator; W1's flipped sites serve those bodies and Rev-2
  forbids the per-body hybrid. Re-pin: KC-W0-2 harness → W0.b flip → W1.
- **Important:** (a) `resolved_target_fq`/`def_terminal_fq` is a verbatim mirror
  of `resolve_user_fn_ref_fq`/`user_fn_fq_of` and `infer_var` now resolves the
  same name up to 3× — consolidate (folded into 0616). (b) Backend unit-harness
  fixture sidecars are still EMPTY maps (design §4 pinned population into W0;
  it moved to `/testing` Stage-1 KC-W0-6) — W1 additionally gates on that landing.
- **Minor:** `adt/tests.rs` scheme-shape tests now pin the `#[cfg(test)]`
  replica of `build_constructor_scheme`, not the production derivation inside
  `build_adt_entries` (builder has own coverage; replica can drift).

Verified clean: carrier contract exactly matches the §8 pinned diff (types
baseline: sidecar + 2 mono fields + `from_expr` −1/+1 + `lenient_from_expr`,
nothing beyond; backend/typecheck baselines zero movement); `from_expr` third
param is structurally unforgettable and all call sites thread it; W0 is
write-only (zero production backend reads of `resolved_target`; all `None`
constructions sit in `#[cfg(test)]`); no soft fallback anywhere (Rev-2 clean);
schema 18→19 correct with the KC-W0-3 stale-cache guard (const-asserted) +
CLAUDE.md updated; R-2 rewiring verified faithful arm-by-arm — `build_adt_entries`
reproduces tag order, GOT-slot order, scheme shapes, product facet + docstring
fallback, entry ordering, and `install_bare_ctor_alias` EXTRACTS (does not fork)
the §8.6.5 contest classifier; the `register_constructors` mirror is actually
deleted; lenient relocation is byte-identical (empty sidecars ⇒ `None`).

Next skills: `/dev` (typecheck, 0616 top-up), `/sprint` (0617 re-pin), then
`/testing` KC-W0-2/KC-W0-6 before the W0.b flip and W1.

### /dev (W0.1) — 0616 producer top-up (2026-07-15, LANDED)

Resolved Blocker FIXME 0616 (the three carrier legs the W0 writer missed) +
folded in the "Resolve once" consolidation. Typecheck-internal, value-only —
**same schema-19 window** (no `CACHE_SCHEMA_VERSION` bump), zero public-API
movement, behaviour-invariant (carrier still WRITE-ONLY — nothing reads
`resolved_target` until W1). Applied "recording happens where resolution
happens" (§1.1), NOT a parallel re-probe.

- **Leg 1 (Apply-span dispatch writer).** New `dispatch_target_fq` +
  `record_dispatch_target` beside `resolved_call_to_fqsymbol` (single-sourced
  module derivation — the `callees` projection, extended with the `BuiltinFn`
  arm the operator leg needs). Wired at EVERY dispatch-selection seam that
  writes through `state` (infer.rs 655/845/912 trait/primitive + deferred +
  value-position; register.rs multi-sig; mono_collect.rs sig-dispatch ×2 +
  auto-curry) AND the three mono-recheck seams writing the per-instance local
  `resolutions` (monomorphise.rs self-recursion + inner-constrained +
  inner-parametric-hop). `finalize_mono_codegen_view` now reads
  `resolved_targets` from the PER-INSTANCE `resolutions` (the enclosing map
  carries no mono-time dispatch selections — `f$Int`/`f$Float` collide at one
  template span); `pattern_ctors` stays on the enclosing map (instance-invariant).
  `(+ 1 2)` → `primitives/add-i64` at the Apply span (the named W1 failure).
- **Leg 2 (self-recursion carve-out).** New `CheckState.current_defn`
  (installed by `check_defn_body`, torn down on exit; deliberately NOT during
  the mono/impl recheck — its self-dispatch is the leg-1 SigDispatch writers).
  `record_reference_target` records the enclosing defn's own storage FQ for an
  env-shadowed self-reference — explicitly diverging from the `callees`
  self-edge skip (the two feeds' gates are semantically different).
- **Leg 3 (dotted `Type.member`).** New `resolve_dotted_member_fq` +
  `dotted_member_identity` core (single-sources the entry + FQ readers,
  Principle 7); `infer_var` records `(fqtn.module, member_key)` for a dotted
  ref (invisible to the bare-name `scope_resolve`). Feeds only `resolved_targets`
  (dotted refs are `callees` residue).
- **Consolidation (the Important mirror).** Deleted `resolve_user_fn_ref_fq`/
  `user_fn_fq_of`/`resolved_target_fq`/`def_terminal_fq`/`record_user_fn_ref`/
  `record_resolved_target`; `infer_var` now resolves each name ONCE via
  `resolve_ref_target` → records `resolved_targets`, derives the `callees` edge
  as a `UserFn`-filtered projection (Principles 7/24). `def_resolved` is the ONE
  chain-follow both feeds + the `BuiltinFn` home probe share.

Pins (typecheck `#[cfg(test)]`, one per leg): `resolved_target_operator_call_
carries_primitive_fq_at_apply_span`, `resolved_target_self_recursion_carries_
own_fq_at_var_span`, `resolved_target_dotted_ctor_carries_member_key_at_var_span`.
Suite: **4562 run, 4549 pass, 13 fail (the unchanged pre-existing S110 REDs),
1 skip** — +3 new green pins, zero new failures. `cargo check`/`--tests`/clippy
clean (added `#[allow(clippy::too_many_arguments)]` to the two seams that grew a
param). `cranelisp-types`/typecheck/backend baselines: zero movement.

§1.1 deviation flagged to `/arch` (do-not-improvise): `dispatch_target_fq`
derives the TraitMethod/SigDispatch module from `resolved_call_to_fqsymbol` =
`current_module` (the shipped `callees` model, whose own rustdoc notes the
pending "Step 5: look up the impl's defining module"). For a **cross-module**
user trait-method dispatch (impl in module B, called from A) the mangled entry
lives in B while the carrier records A — the backend's W1 keyed read would
entry-miss. This is a PRE-EXISTING modelling gap shared with `callees` (masked
today by the backend's global-fallback scan), NOT introduced here; W1's keyed
read is where it surfaces. Recorded for `/arch` to rule on the correct
storage-module derivation before W1 flips the trait-method leg.

## Waves (Phase 4)

**Constraint (binding).** Worktree isolation is broken → **source-touching work is
SERIAL** (one editor at a time). The waves below are logical groupings on a **pinned
linear execution order**; read-only / test-authoring / design-only / `/review` /
`/audit` steps overlap freely. `/arch` §8 pinned the per-chain constraints; this is their
linearisation. Every `/dev` wave is followed by a narrow `/review`. **Only W0 moves a
library baseline** (the `cranelisp-types` carrier fields + R-2 builder already regen'd;
W0 adds the schema bump) — W1–W3 and the src/ track are zero-public-API.

### Stage 1 — QA-first (ONE `/testing` dispatch, sprint-wide) — FIRST
`/testing` authors the full failing e2e/unit set from `PLAN.md §S110` (buckets A–J:
0583 W0/kind-flip/hard-miss, 0585 if/match/vec, 0590 tightening + FV-13/14 fence, R16/R17
incl. the RD-3 `(let [r (add2 3 4)] r)` false-positive fence, 0605 recursive-enum gate +
SG-2 infra, 0604 twin-guards-stay-green, the already-committed vec-assoc/C-4 REDs verified,
R-2 invariance). Author the S109 AL-3/AL-4/private-member diagnostic rows (D-1) **before**
the 0609 shim deletion. Failing-not-ignored. Verify-first rows checked. Populates the
backend unit-harness fixture sidecars (the W0/KC-W0-6 pin) so W1 doesn't red the backend
unit suite.

### Stage 2 — per-crate D/D/R (PINNED ORDER; serial on source)

**The dependency backbone:** `W0` gates the entire backend chain (W1–W3 read the carriers)
and the R16/R17 impl; `0611` (arch ratifies the R16/R17 carrier) gates the R16/R17 impl;
`0606` (repl.rs decomposition) precedes `0608` (over-budget batch). Everything else is
order-flexible within the serial spine.

- **W0 — producer** (`/dev`, coordinated typecheck + types + backend-harness). Carrier
  fields (`resolved_targets` sidecar + `MonoExpr::{Var,Apply}.resolved_target` `#[serde(default)]`)
  + REQUIRED `from_expr` param + typecheck population at the resolution chokepoints for all
  statically-resolved kinds + **W0.b totalization** (relocate `lenient_mono_from_expr` beside
  `from_expr` in `cranelisp-types`; synthetic bodies get `resolved_ctor` at synthesis) +
  **`CACHE_SCHEMA_VERSION` 18→19** + R-2 caller wiring (typecheck `adt.rs` → `build_adt_entries`)
  + backend unit-harness fixture-sidecar population. Behaviour-invariant (suite green, CLIF
  byte-identity across the six lenient entry classes). → `/review`. **GATES the backend chain.**
**W0-completion front (all BEFORE W1 — re-pinned after the W0 review's 2 Blockers, `7c943300`):**
- **W0.1 — producer top-up (B1 / FIXME 0616, `/dev` typecheck).** The W0 producer
  `record_resolved_target` is a SECOND narrow probe that misses three legs — fix by
  **capturing at the resolving seams instead** (Principle 24, not a third probe): an
  **`Apply`-span writer** at the dispatch-selection seams (`traits/monomorphise.rs`,
  `infer.rs`, `program/register.rs`, `mono_collect.rs`) so trait / sig-dispatch / auto-curry /
  operator calls carry `resolved_target` (today `MonoExpr::Apply.resolved_target` is
  structurally always `None`); **self-recursion** capture (the env-shadow gate must not skip
  the self-edge the backend keys via `resolve_got_target`); **dotted `Type.member`** capture
  (`resolve_dotted_member_entry`). Consolidate the `infer_var` triple-probe into one (the
  Important mirror). Same schema-19 window; one unit pin per leg. → `/review`.
- **W0.2 — harnesses (`/testing`, before W1).** **KC-W0-2** golden-CLIF byte-identity harness
  (the gate that makes the W0.b flip shippable) + **KC-W0-6** backend unit-harness
  fixture-sidecar population (else the backend unit suite reds at W1). tests/ + backend-src;
  serialize builds with the source waves.
- **W0.b flip (`/dev`, before W1, gated on KC-W0-2).** The FULL totalization deferred within
  W0 (`41fab350`): backend `lib.rs` view-selection hard-error arm + typecheck populating
  `codegen_view` for ALL codegen-reached entries (ctors/accessors) + synthetic
  `resolved_ctor`-at-synthesis. Lenient-built bodies (full reference-kind spectrum) get empty
  sidecars today, so W1's flipped sites would hard-miss them and Rev-2 forbids the per-body
  hybrid — **hence before W1, NOT W3** (B2 / FIXME 0617). `lenient_from_expr` already
  relocated → reduces to a backend-`lib.rs` + typecheck-view-population edit. → `/review`.

- **W1 — backend call seam** (`/dev` backend, S1–S9). `resolved_target` → `entry_at` keyed
  read; kind arms off the entry; ctor-`Apply` included. → `/review`.
- **W2 — backend value seam + 0585 guard + vec-assoc fix** (`/dev` backend, S10–S18).
  Value/Var refs read the carrier; the slot-less-template value read hard-`CodegenError`s
  (the 0585 loud backstop); **vec-assoc UAF ×2 fix rides here** (`heap.rs`/`apply.rs` open —
  RC premature-free). → `/review`.
- **W3 — backend delete + residue** (`/dev` backend, S19–S24). **Depends on the W0-completion
  front (W0.1 + W0.b) landing.** Resolve the outside-`from_expr` view-builder residual
  (subsumed by W0.b), then delete `resolve_driven` + `resolve_chain` + the
  `symbol_tables.iter()` scan + all ten entry points + `lookup_constructor`. **W3 grep gate:
  zero `resolve_*` in backend** (structural acceptance, `/review` + audit). → `/review`.
- **W-TC — 0590 resolver convergence** (`/dev` typecheck; after W0 on the serial typecheck
  chain). Blast-radius scout FIRST (the never-error `Named`-fabrication deletion), then the
  `TypeExprCtx` single-source collapse; FV-13/FV-14 fence holds. → `/review`.
- **W-RD — R16/R17 error quality** (`/arch` ratifies 0611 carrier shape → `/dev` coordinated
  typecheck + int). Dispatch-outcome signal → §3.11 clean message; RD-3 false-positive fence.
  → `/review`.
- **W-604 — index-feed write-race isolation** (`/dev` int; must-have, schedule early in the
  int/src spine). The ≥25× `CRANELISP_MODULE_TRACE=1` sweep **LOCATES the residual writer
  first** (prime suspect: the shared-cache §25.5 channel per the corrected attribution), THEN
  the isolation fix + unit pin at the true write seam. Twin guards stay green. → `/review`.
- **W-SRC — src/ hygiene chain** (`/dev` src/, serial): **0606** repl.rs decomposition
  (mechanical move, cut signed off) → **0608** over-budget batch worst-first + narrative
  relocation → **0609** DELETE the phantom shim (`/qa` ruled UNREACHABLE; D-3 propagate the
  abs hard error to make it structural) → **0610** hygiene (gitignore `agent_trace.txt`/`user.cl`
  + refresh `lib.rs` comments) → **C-4** multi-arity-main fix (int batch path) + R-2 `bootstrap.rs`
  caller wiring. Each step → `/review`. `int.md` map update rides 0606's move (0607 largely
  landed Phase 3).
- **W-GATE — stdlib-compile smoke gate** (`/testing`; tests/ only, parallel-safe lane).
  Recursive-public-module enum + per-module subprocess loop + aggregated report; SG-2
  `agent_flag` build-interleave infra fix rides it.

**Wave gate (before each advance):** scan `design/arch/fixmes/` for `target: /skill-in-wave`
+ `status: open`; any match blocks. **Audit dispatch:** `/audit` on `cranelisp-backend` +
the resolution seam (read-only) in the Phase 6/7 window, ideally **post-W3** so it assesses
the end-state and its boundary lens verifies the grep-zero (`/arch` §7).

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P2 | /arch | S110 broad scope review | (shim §II.3) | (shim) | — SIGN-OFF w/ 4 pinned revisions; type-axis mostly-closed finding |
| P3 | /arch | backend-keyed-consumer.md + Principle 24 + R-2 builder | (shim §II.3) | (shim) | — `8170ea45`+`accde23c`: S1–S24 inventory, W3 residual ruled, R-2 landed |
| P3 | /design (typecheck) | 0590 convergence + R16/R17 signal | (shim §II.3) | (shim) | — `99d6996f`: `TypeExprCtx` collapse; FIXME 0611 filed |
| P3 | /design (int) | 0604 isolation + 0607 currency + 0606 cut | (shim §II.3) | (shim) | — `061c54a2`: 0604 attribution CORRECTED (cache channel, not live-write) |
| P3 | /qa | sprint-wide PLAN §S110 (exit gate) | (shim §II.3) | (shim) | — `ffdaa4b9`: buckets A–J; 0609 ruled UNREACHABLE→delete; 0605 recursive-enum |
| P3 | /spec | §3.5.5 polymorphism-boundary sidenote (0612) | (shim §II.3) | (shim) | — `41d8e32b`: monomorphic-`let` normative + movable; hedge retired; capability parked |
| P5-S1 | /testing | sprint-wide QA-first failing tests (PLAN §S110) | (shim §II.3) | (shim) | — `c31b6050`: 13 REDs RED-for-right-reason, no regressions; SG-1 `derive` gate catch |
| P5-S1 | /qa | SG-1/SG-2 attribution | (shim §II.3) | (shim) | — `9ae05c2a`: SG-1 = REAL layered defect (0613 /dev quasiquote-not-desugared + 0614 /stdlib helper-violation); SG-2 = build-artifact race (0615 /testing) |
| W0 | /dev | 0583 producer (types+typecheck+backend) | (shim §II.3) | (shim) | — `41fab350`: carriers+`from_expr`+F1 producer+cache 18→19+R-2 typecheck half+lenient relocation; baseline holds 13 REDs; **W0.b full totalization DEFERRED** (gated on KC-W0-2 golden-CLIF; needed before W3, not W1/W2) |

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
- **Phase 3 (2026-07-15):** three design agents ran in parallel on disjoint surfaces,
  all committed to main (shared-tree discipline honoured — each staged only its own files).
  - **`/arch`** (`8170ea45` R-2 builder + `accde23c` design/principle/BC): `design/arch/
    backend-keyed-consumer.md` (one-carrier contract, exhaustive **S1–S24** per-site
    inventory, 4 wave briefs, W3 residual RULED = typecheck sole mono-view producer via
    W0.b totalization → deletes the synthetic-body fallback); **Principle 24 "Resolve
    once"** + 4 import blocks + BC §3 invariant 10 + §2 producer obligation; R-2
    `AdtCtorSpec`/`build_adt_entries` landed (4 unit tests, public-api +16 additive, cache
    NEUTRAL); W0 pinned not executed (`CACHE_SCHEMA_VERSION` 18→19 rides the Phase-5
    producer change-set). **W1 pin for `/dev`:** the backend unit-test harness must
    populate fixture sidecars or W1 reds the whole backend unit suite.
  - **`/design (typecheck)`** (`99d6996f`): 0590 converges the four resolvers onto
    `resolve_type_expr` via one `TypeExprCtx` (typecheck-internal, zero public-API; the
    never-error `Named`-fabrication arms delete → behaviour-tightening for a `/qa` matrix +
    blast-radius scout, FV-13/FV-14 the fence); R16/R17 signal grounded in dispatch
    OUTCOME not surface-type → **FIXME 0611** to `/arch`.
  - **`/design (int)`** (`061c54a2`): **0604 attribution CORRECTED** — the mutate-live
    seam was S91-cured (`9ba2ca91`); the surviving leak is the shared-cache §25.5 write
    channel (`write_index_meta` → `record_source_hash`/`record_compiled`), consumed
    verbatim by the foreground import (the `bit-and`-only per-module fingerprint fits a
    cache-artifact race). Isolation contract severs it; ≥25× trace sweep must LOCATE the
    residual writer before `/dev` patches. **Action owed:** route the correction to `/qa`
    (owns `tests/plan/s109-attribution-index-feed-race.md §2`) + fold into the Phase-5
    `/dev` brief (target the cache channel, NOT the cured `index_branch_c` live-write). Also
    delivered: 0607 currency pass (`int.md` as-built + surgical `agent.md §2.2` fix + 18
    doc banners + doc-index) and 0606 repl.rs cut sign-off (search/format/commands/residual,
    precise boundaries; mechanical move is Phase-5 `/dev`).
  - **`/qa`** (`ffdaa4b9`): `PLAN.md §S110` buckets A–J + `risks.md` S110 read. **0604
    attribution correction LANDED** in the doc `/qa` owns (§2 now names the cache channel;
    `class=shared-state-write-race` vocab added). Refinements: 0605 needs **recursive**
    public-module enum (top-level-only would miss `num.bits` itself) + one enumerating test
    with a per-module subprocess loop; **0609 ruled UNREACHABLE → DELETE the shim** (D-3:
    propagate the abs hard error to make it structural); vec-assoc + C-4 repros **already
    discharged** as committed REDs. **Phase-3 exit gate CONFIRMED.**
- **Phase 4 (2026-07-15):** wave org written (§Waves). Serial-source spine with the
  dependency backbone (W0 gates the backend chain + R16/R17; 0611 gates R16/R17 impl; 0606
  before 0608). Audit rotation CONFIRMED = `cranelisp-backend` + resolution seam, post-W3.
  Dispatch log seeded with the P2/P3 rows. **Held at the Phase-4→5 boundary per the "plan
  the sprint" ask — the build (Phase 5: QA-first `/testing`, then the per-crate D/D/R
  cycles) awaits the user's go.** Planning arc (Phases 1–4) complete: scoped, arch-signed-off,
  designed (4 design commits on main incl. Principle 24 + R-2 builder), test-planned, waved.
- **Phase 5 START (2026-07-15, user go):** Status → LANGUAGE (ACTIVE). **Stage 1 (QA-first)
  dispatched** — one sprint-wide `/testing` invocation authoring the failing e2e set from
  `PLAN §S110` (buckets A–J), failing-not-ignored, the gate before any consuming `/dev`
  wave. On its green-for-right-reason return, Stage 2 begins on the serial spine, W0 first.
