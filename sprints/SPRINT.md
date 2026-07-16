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

### /arch (W0.1 cross-module ruling) — storage-module derivation RULED (2026-07-15)

Ruling authored into `design/arch/backend-keyed-consumer.md` **§1.1.1** (per-leg
derivation rules + completeness sweep + pinned types diff); Decision 0045
amended in place; `design/arch/CLAUDE.md` synced.

**The ruling.** Trait-impl method `Def`s live in the **impl-WRITER's module**
(ground truth verified: `finalize_impl_method_writeback` writes via
`current_symbol_table_mut` after the module restore, `impl_check.rs:514–518`;
only the `TraitImpl` SHELL goes to the trait's home). This placement is
structurally FORCED — `compile_to_module` hard-errors unless a compiled defn's
entry + GOT slot are in the compiling module's own table (backend
`lib.rs:939–947`), and the method bodies compile in the writer's batch — so
D45's method-co-location clause is **amended**, not enforced. The writer's
module is knowable at the dispatch seam only from the shell ⇒ a
`cranelisp-types` change IS needed (PINNED, not landed — enum-field additions
force cross-crate atomicity): `ModuleEntry::TraitImpl.impl_module` (durable
discovery→storage pointer, written from `state.current_module` at the shell
construction) + `ResolvedCall::TraitMethod.impl_module` (resolution product,
populated by `try_resolve_trait_method` from the exact-key shell probe;
consumers read, never re-derive — resolves the callees.rs "Step 5" note AND
repairs the S101 reverse-index edges for cross-module trait calls). Both
required fields, no serde default; **same schema-19 window, no new bump**.

**Completeness sweep (the load-bearing part; full table in §1.1.1):** all
mono-minted SigDispatch legs are CORRECT (record `current_module` where
`register_mono_entry` stores — caller's table, verified ×4); overload
SigDispatch correct-by-reach (the pending gate is run-local — cross-module
multi-sig dispatch doesn't exist today, a latent pre-existing language gap,
not a 0583 blocker); Var-leg user fn / primitive / ctor / dotted / effect /
extern / self-recursion / synthetic all correct. **Two MORE producer gaps
found**: (a) AutoCurry plain leg records `{current_module, target}` for
possibly-imported targets — fix by transporting the callee Var's
already-recorded carrier through `pending_auto_curry` (resolve-once,
shadow-correct); (b) the fn-value mono rewrite (`mono_collect.rs:79–88`)
renames the AST Var without updating `resolved_targets[arg_span]` — post-W2
the 0585 guard would hard-fail a valid program; fix = sidecar insert at the
rename.

**`/dev` action (W0.1b — fix, NOT fold into W1):** one coordinated `/dev`
change-set (typecheck-led; types + typecheck + `src/repl.rs::impl_entry`
fixture): the two `impl_module` fields + writer at the shell construction +
`try_resolve_trait_method` population + `dispatch_target_fq`/
`resolved_call_to_fqsymbol` reading the field + the AutoCurry and
fn-value-rewrite fixes; types `public-api.txt` regen + `interfaces.md` +
rustdoc in the same change-set; one unit pin per fixed leg (cross-module
trait dispatch; imported-target curry; fn-value rewrite). **W1 is GATED on
W0.1b** — the gap is broad, not corner-case: every non-primitive impl of a
prelude-provided trait called from user code entry-misses (the 0185
short-circuit covers only the primitive operator table), and every curry of
an imported fn misses. Recommended order: **W0.1b → KC-W0-2/KC-W0-6 → W0.b →
W1** (W0.1b slots into the existing W0-completion front; Rev-2 forbids
discovering producer gaps via backend hard-misses, and W1 is backend-narrow
while this fix is cross-crate).

Next skills: `/dev` (typecheck, W0.1b per the §1.1.1 pinned diff), then
`/review` (narrow, typecheck+types), then the W0-completion front as re-pinned.

### /dev (W0.1b) — cross-module storage-module fix (2026-07-15, LANDED)

Landed `/arch`'s §1.1.1 ruling as ONE coordinated types+typecheck+int change-set,
**same schema-19 window (no `CACHE_SCHEMA_VERSION` bump)** — verified the
reasoning holds: the two enum-field additions force cross-crate atomicity, but
they land inside the schema-19 window and `BUILD_ID` staleness + the 0472
precedent cover dev-cache skew (no serde meaning-change to an existing field;
new required fields on fresh builds only). Behaviour-invariant — the carrier is
WRITE-ONLY until W1, so the suite holds the **13-RED baseline** exactly.

Per-leg:
- **Trait-method (main).** `ModuleEntry::TraitImpl` gains `impl_module:
  ModuleFullPath` (required, no serde default; rustdoc = amended D45: shell =
  discovery record at the trait's home, `impl_module` = where the bodies live),
  written from `state.current_module` at the shell construction
  (`impl_check.rs` — verified current is the WRITER there, before the per-method
  module switch). `ResolvedCall::TraitMethod` gains `impl_module` (required),
  populated by `try_resolve_trait_method` via a new
  `checker::impl_module_in_home` helper (exact canonical-key probe
  `impl${fq_for_mangle}${fq_trait_name}` at the trait home, bare-name fallback
  for the intrinsic-receiver head skew; degrades to `current_module` only on a
  pathological miss). `resolved_call_to_fqsymbol` now READS `impl_module` (the
  callees.rs "Step 5" answer — also repairs the S101 reverse index for
  cross-module trait calls). SigDispatch mono legs untouched.
- **AutoCurry plain leg.** `pending_auto_curry` widened with the callee `Var`
  span; `resolve_auto_curry` transports the callee's already-recorded
  `resolved_targets` carrier for a plain-fn curry (resolve-once, shadow-correct;
  `None` for a local target), replacing the wrong `{current_module, target}`
  derivation. Trait/builtin curries still derive from the inner resolution.
- **Fn-value mono rewrite.** `pass4_monomorphise` inserts `{current_module,
  mangled_sym}` at `arg_span` alongside the `rename_var_at_span` — so the W2
  0585 keyed read sees the minted instance's storage, not the slot-less template.

Cascade: `into_concrete` arm, `src/repl.rs::impl_entry` fixture, `check/tests.rs`
serde-roundtrip + typecheck/backend test constructors, `cranelisp-types/CLAUDE.md`
+ backend CLAUDE.md already at schema-19, `public-api.txt` regen (+2 lines, the
two new fields only). One unit pin per fixed leg (all green):
`traits::dispatch::tests::resolved_target_cross_module_trait_method_records_impl_writer_module`,
`program::tests::resolved_target_autocurry_imported_target_records_targets_home`,
`program::tests::resolved_target_fn_value_mono_rewrite_carries_mangled_carrier`.
Suite: **4565 run, 4552 pass, 13 fail (unchanged S110 REDs), 1 skip** (+3 pins,
zero new failures). `cargo check --workspace --tests`/clippy clean.

**§1.1.1 deviation flagged to `/arch` (do-not-improvise): ONE plumbing step
beyond the literal leg-3 insert.** The design attributed "the carrier reaches
codegen" for the fn-value rewrite to W0.b's view-totalization. But the enclosing
concrete defn's `codegen_view` is ALREADY rebuilt post-mono at
`finalize_annotations_and_publish` (`finalize.rs`) from the RENAMED AST +
`accumulator.resolved_targets`; the only missing plumbing was that
`sweep_post_pass_outputs` discarded `state.method_resolutions.resolved_targets`
(swept only `resolved_calls`), so pass-4 carriers never reached the accumulator.
I extended the sweep to carry `resolved_targets` into the accumulator (behaviour-
invariant — the field rides unread until W1). This makes the leg-2 finalize-drain
and leg-3 fn-value carriers reach the EXISTING enclosing-view rebuild NOW (and is
what makes the leg-3 pin observable). The LENIENT/synthetic-body totalization
(`Span::SYNTHETIC` bodies, ctor/accessor direct population) remains W0.b as
ruled. `interfaces.md` is `/arch`-owned — the two new fields likely want a
one-line narrative there (`ResolvedCall`/`ModuleEntry` sections); FLAGGED, not
edited.

### /review (producer W0.1+W0.1b) — 0583 producer gate review (2026-07-15, COMPLETE)

Reviewed `635f364b` (W0.1) + `144828d1` (W0.1b) against `backend-keyed-consumer.md`
§1.1/§1.1.1/§8, narrow to typecheck+types. **Gating verdict: GO — the producer is
complete and correct to build W1 on.** Zero Blockers. All targeted probes green
(the 6 carrier pins + the 17 `callees_*` guards); 13-RED baseline asserted by both
commits, not re-run (per dispatch).

**Storage-module correctness (the W1-gating check) — verified per leg:**
- **Trait-method**: the shell write (`impl_check.rs:153–167`) goes into
  `trait_home`'s table via `symbol_table_mut_in` while `state.current_module`
  is UNTOUCHED — it IS the writer's module there (the D1 trait-home switch
  happens later, only around default-method BODY checks, and
  `finalize_impl_method_writeback` runs after the unconditional restore at
  `impl_check.rs:520–524`, writing via `current_symbol_table_mut` = writer).
  **Explicit, default, and HKT methods all land through that ONE writeback
  tail**, so `impl_module` names the true storage for every method class.
  Cross-module shapes checked: trait T / impl B / caller A (three distinct) —
  shell at T carries B, probe roots at T, carrier `{B, mangle}` ✓;
  re-exported trait refs (chain-follow terminates at T regardless of path) ✓;
  prelude-trait impls from user code (the §1.1.1 named-broad case) ✓.
  No latent W1 hard-miss shape found.
- **The `impl_module_in_home` probe**: the exact key
  (`impl${fq_for_mangle}${fq_trait_name}`) matches the writer key whenever the
  S102 mangle lock-step holds — the SAME condition for the call to resolve at
  all, so an exact-probe miss on a valid program implies the bare fallback,
  whose predicate is IDENTICAL to `has_impl_in_home`'s (which just returned
  true over the same table) — so the fallback cannot record a module the
  existence check didn't ground, and the `degrade to current_module` arm is
  dead in practice (Suggestion: a debug trace on it; silent-wrong if ever live).
  Bare-name collisions (a/Point vs b/Point) discriminate on the exact key for
  ADT receivers; the colliding-miss shape also breaks the mangle, i.e. the
  program is already invalid and W1 fails it LOUDLY — acceptable.
- **AutoCurry plain leg**: callee-span transport verified shadow-correct
  (reads only what `infer_var` recorded; `None` for locals) and correct across
  all three drain seams (per-defn, mono-recheck under the swapped per-instance
  map, finalize) — the map read always targets the map the callee Var wrote. Pinned.
- **Fn-value mono rewrite**: sidecar insert at `arg_span` with the caller's
  module matches `register_mono_entry` storage; pinned.
- **Mono legs**: `record_self_recursion_dispatch` + inner legs receive
  `current_module` AFTER `recheck_body_for_mono`'s restore — matches storage ✓.

**The flagged W0.1b deviation (finalize.rs:667 sweep) — SOUND, not a mask.**
Post-pass carriers (pass-4 fn-value rename at `mono_collect.rs:88–104`;
finalize-drained auto-curry) land in `state.method_resolutions` AFTER the
per-form snapshots (which are superset CLONES, `body.rs:120/560`); the sweep is
the only bridge into `accumulator.resolved_targets`, and
`finalize_annotations_and_publish` (runs after the sweep, `finalize.rs:794→799`)
rebuilds every `Concrete` view from it (`finalize.rs:890/910`). HashMap-extend
is idempotent-overwrite: no drop, no double-count; the same-span rename value
correctly clobbers the stale template FQ. The lenient/synthetic totalization
correctly remains W0.b.

**Consolidation ("Resolve once") — CLEAN.** `resolve_ref_target`/`def_resolved`
is the ONE chain-follow; `callees` is a `UserFn` projection of the same
resolution; the deleted sextet is gone (grep: only doc-comment mentions remain).
Self-edge gates verified both right: carve-out writes `resolved_targets` only,
`callees` skip retained; all 17 `callees_*` guards green. `impl_module_in_home`
is NOT a resolver mirror — a keyed shell probe within the ALREADY-RESOLVED trait
home reading the resolution product (no chain-follow, no scan beyond the
pre-existing `has_impl_in_home` pattern). One corner behaviour change, in the
agreeing direction: a qualified `m/f` whose child-of-current-module candidate is
a non-`UserFn` Def no longer falls through to the absolute candidate for the
`callees` edge — the new stop agrees with `lookup`'s candidate order (the old
fall-through could record an edge to an entry the reference didn't type-check
against).

**Behaviour-invariance + baseline — CONFIRMED.** Carrier write-only (every
backend `resolved_target:` construction sits in `#[cfg(test)]`); types
`public-api.txt` diff = exactly the two `impl_module` lines;
`CACHE_SCHEMA_VERSION` = 19 unchanged; both new fields required, zero
`#[serde(default)]` (P18/P20) ✓.

**Findings filed** (neither gates W1 — advisory for `/sprint` disposition):
- **FIXME 0618 (`/arch`, Important)**: `interfaces.md` carries NO narrative for
  the W0 carrier fields OR the two `impl_module` fields — §1.1.1's pinned diff
  named it as riding the change-set; land before sprint close.
- **FIXME 0619 (`/dev` typecheck; Important + 3 Minor)**: (1)
  `builtin_storage_fq` resolves the JIT name through USER scope — a
  prelude-suppressed module with a local fn named `add-i64` + `(import
  [primitives [+]])` + `(+ 1 2)` records the user fn as the carrier for a call
  the backend emits as the primitive (wrong-dispatch at W1 on a narrow-but-valid
  shape; one-line kind-filter fix); (2) the self-recursion carve-out fires on
  any same-named LOCAL (`(defn f [] (let [f …] (f 3)))`) — harmless ONLY while
  the backend's locals check precedes the keyed read (the §1.1 pinned order; W1
  brief must keep it); (3) the AutoCurry plain-arm `callees` edge still derives
  the CALLER's module for an imported target (pre-existing; now contradicts
  `dispatch_target_fq`'s "carrier and callees agree" rustdoc); (4) typecheck
  `CLAUDE.md` still names the deleted `record_user_fn_ref`.
- **Coverage note (`/qa`/`/testing`)**: the cross-module trait pin exercises the
  READ half via a synthetic shell; the WRITER half (a real `(impl)` for an
  IMPORTED trait ⇒ shell `impl_module` = writer ≠ trait_home) is verified by
  source reading but not pinned end-to-end — a cheap 3-module pin would close it
  (W1's hard-miss e2e catches it loudly regardless).

Next skills: `/sprint` (dispose 0618/0619; advance the W0-completion front —
W0.2 KC-W0-2/KC-W0-6 → W0.b flip → W1 as re-pinned), `/arch` (0618), `/dev`
(typecheck, 0619 — can ride any pre-W1 typecheck slot).

### /testing (KC-W0-2) — the W0.b golden-CLIF byte-identity gate (2026-07-15, LANDED)

Built the W0.b shippability gate: `tests/golden_clif_w0b.rs` + corpus/goldens
under `tests/fixtures/clif_w0b/` (MANIFEST there). GREEN at HEAD (producer state
`144828d1`); 5 tests, 0.13s. **Gate name for the W0.b `/dev` wave:**
`cargo nextest run --test golden_clif_w0b` (test prefix `golden_clif_w0b_*`).

**Five live lenient classes pinned** (each an isolated free-standing fixture;
frames byte-verbatim, sorted, via `CRANELISP_CODEGEN_DUMP='*'` + `--run
--no-cache`, the L-B1 capture contract):
1. ctor `Def` synthetic body — `user::Box.MkBox`
2. synthesised accessor — `user::Point.x/.y`
3. `f$Var` multi-sig variant — `user::pick$Int`, `user::pick$Int+Int`
4. `__expr` §3.11.2-disposition-3 — `user::__expr`
5. non-concretized macro-clause — `user::__macro_twice_clause_0`

**Normalization = byte-verbatim, NO canonicalization** (the L-B1 precedent).
Admissible because the dump is DETERMINISTIC — the harness double-captures and
asserts identity BEFORE the golden compare, every run. Verified not a
false-green: a single value-number tamper reds the gate; restore greens it. A
RED under W0.b means real codegen drift (the wave is behaviour-invariant, so the
expected delta is EMPTY); re-baseline is scoped+attributed only, per MANIFEST.

**Class 06 "generic template reached by direct compile" is NOT in this e2e gate
— it is structurally backend-unit-only.** Pure `Polymorphic`/`Constrained`
templates are excluded from the codegen name-set (`src/worker.rs:896-902`) and
produce no `.o`; the only path that lowers a bare template is `jit.rs::compile_defn`,
which has ZERO live callers (all `#[cfg(test)]`; verified 2026-07-15, matching
design §5 finding 3). `tests/` being e2e-only, that class's byte-identity guard
IS the backend unit suite (folds into KC-W0-6 / W3 view-migration), not this gate.

**KC-W0-6 red-first answer (dispatch question):** the **backend unit suite reds
FIRST** on a missing carrier — it is the direct in-crate consumer with
hand-built fixture tables/exprs and NO live producer to populate sidecars, so a
W1 hard-miss flips it immediately (exactly what design §4 W0.a pins). This e2e
gate reds LATER and on a different signal — byte-DIVERGENCE in the live path,
which presupposes the typecheck producer actually ran. Sequence KC-W0-6
(fixture-sidecar population, incl. class-06's template fixtures) IN W0, before
W1, as already pinned.

### /dev (W0.b) — the totalization flip (2026-07-15, LANDED)

Made typecheck the SOLE mono-view producer for every codegen-reached body;
backend `lib.rs` view-selection now HARD-ERRORS on a `codegen_view: None`
(Principle 18) instead of rebuilding a lenient view. **Golden gate GREEN,
byte-identical per class; full suite = the 13-RED baseline UNCHANGED (zero new
regressions); no `CACHE_SCHEMA_VERSION` bump.**

**The flip mechanism (typecheck + backend).**
- `program::support::build_concrete_codegen_view` made TOTAL — strict
  `from_expr` first, `lenient_from_expr` fallback — so every concrete defn
  (incl. best-effort bodies whose strict view previously failed, e.g. a `main`
  calling a multi-sig `pick`) carries a view. Was `None`-on-fail.
- **Synthetic bodies populated DIRECTLY at synthesis** (`Span::SYNTHETIC` is
  outside span-keyed transport): ctor `Def`s in the `adt.rs::register_type_def_with_ctor_infos`
  `build_adt_entries` return loop (`ConstrADT` body, empty sidecars); product
  field accessors in `synthesise_one_accessor` — the accessor's single pattern
  arm gets `resolved_ctor` = the owner product ctor's canonical STORAGE key (the
  bare type name), which CLOSES the backend S19 `resolved_ctor: None` fallback.
- Backend `lib.rs:905` region: the `requires_codegen_view` bypass RETIRED (fn +
  its two predicate unit tests deleted); the match reads a present view for ALL
  kinds and returns a precise `CodegenError` on `None`. `lenient_mono_from_expr`
  survives only as the `#[cfg(test)]`-reachable `jit.rs::compile_defn` helper
  (rustdoc corrected — no live caller, KC-W0-2 finding; W3 deletes both).

**Ownership side-channel (the byte-identity subtlety, flagged as a §5 note to
`/arch`).** Populating views pulls entries into the ownership fixpoint universe
(`collect_universe` keyed on "has a view"); the accessor got a `self`-Borrowed
summary → RC-drop elided → CLIF DIVERGED (golden class 02 RED), and the
cluster-fixpoint perturbation cascaded into `main`. Cure: `collect_universe`
now PINS the universe to the pre-flip set — a genuine STRICT-concrete body
(`from_expr` succeeds on the stored `ast`), which the lenient/synthetic classes
fail — so ctor/accessor/lenient-fallback views stay OUT of ownership,
`mode_summary: None`, byte-identical. (The flip changes WHERE the view is built,
not codegen; this keeps that true through the ownership seam too.) NOT a §5
deviation in mechanism — the §5 ruling stands; this is the one non-obvious seam
the byte-identity gate surfaced. Flagged for `/arch` awareness.

**Golden-gate result (byte-identity confirmed per class).**
`cargo nextest run --test golden_clif_w0b` = 5/5 GREEN, byte-identical: 01 ctor
`Def`, 02 synth accessor (the `resolved_ctor` keyed read via `ctor_meta_at`
lowers identically to the old `lookup_constructor` fallback — the DC-11 cure
holds), 03 multi-sig (incl. the lenient `main`), 04 `__expr`, 05 macro-clause.
No re-baseline.

**KC-W0-6 (backend + int fixture-sidecar population).** Added
`test_support::test_codegen_view` (total, threads `resolved_targets`) as the
hand-built-fixture view helper. Fixed the two backend fixtures that hit the new
hard-error (`cache::tests` `answer`, `fn_as_value` ctor `Some`) and the int-side
`worker::tests::mk_def_with_got` (covered 4 int-test regressions — view-less
macro-clause/defn fixtures). `jit.rs::compile_defn` "the REPL calls directly"
rustdoc corrected (every caller `#[cfg(test)]`). Broad per-fixture
`resolved_targets` FQ population is best co-landed WITH W1 (the reads validate
them; a blind unread carrier risks silent mis-dispatch, anti-Principle-24) — the
enabling helper is landed.

**FIXME 0619 legs.** Item 1 (Important — `builtin_storage_fq` kind-gate,
pinned), item 3 (Minor — AutoCurry plain-arm callees edge now via `user_fn_refs`,
not the wrong caller-module), item 4 (Minor — CLAUDE.md `record_user_fn_ref` →
`record_reference_target`) all LANDED. Item 2 (self-recursion carve-out over-
matching a same-named local) DEFERRED to the W1 brief as a locals-check-before-
keyed-read invariant (FIXME 0619 updated to carry only item 2).

**New pins (typecheck `#[cfg(test)]`, all green):**
`resolved_target_builtin_fq_ignores_shadowing_user_fn` (0619 leg 1),
`w0b_synth_accessor_view_carries_resolved_ctor` (§5 obligation 1),
`w0b_every_codegen_reached_entry_carries_a_view` (§5 obligation 2 — the
totalization pin).

**Acceptance.** `golden_clif_w0b` GREEN (byte-identical); backend + typecheck
unit suites GREEN; full `--no-fail-fast` = 13-RED baseline unchanged (the 13 are
the known S110 defect guards — `derive` quasiquote 0613, the `_neg` guards, vec
UAF, etc.); `cargo check --workspace --tests` + clippy clean (no new lints); no
`CACHE_SCHEMA_VERSION` bump (population-extent rides the schema-19 window +
BUILD_ID, per design §8). W3 can now delete `lenient_mono_from_expr` + the
lenient arm (both dead on the live path).

### /dev (W1) — the call seam (2026-07-16, BLOCKED on a producer gap → FIXME 0620)

Flipped the `apply.rs` dispatch funnel from resolution-by-scan to a keyed read of
the `MonoExpr::{Apply,Var}.resolved_target` carrier → the ONE
`CompileContext::entry_at(&FQSymbol)` fetch (the `ctor_meta_at` generalisation:
direct two-level map read, NO chain-follow / NO alias substitution / NO global
scan — Rev-2 §1.3) → discriminate on the fetched entry's `DefKind`. **The core flip
is CORRECT (`golden_clif_w0b` 5/5 GREEN byte-identical), but W1 is BLOCKED by a
BROAD producer gap and did NOT land** (would add ~6 new e2e REDs beyond the ~13
baseline).

**Sites flipped (S1,S2,S5,S6,S7,S8,S9) — each lost its apply-site resolver caller:**
- **S1** `apply.rs` BuiltinFn `is_extern_primitive` GOT-vs-extern — was
  `resolve_got_target(op_name).is_some()`; now `entry_at(apply_target).callable_got_slot().is_some()`.
- **S2** BuiltinFn platform GOT-flip — same `resolve_got_target` → `entry_at` flip.
- **S5** `compile_consuming_arg_list_moded` borrow-elision — was
  `resolve_callee_summary(name)`; now `entry_at(fq).mode_summary()` (the `callee`
  name param retired). `resolve_callee_summary` keeps its W2 caller (S15).
- **S6** `compile_direct_call` poll arm — was `resolve_poll_effect_target`; now the
  `DefKind::PlatformEffect { poll_shape: true }` arm off the ONE fetch.
- **S7** `compile_direct_call` unified GOT dispatch — was `resolve_got_target`; now
  `entry.callable_got_slot()` off the fetch (home == `fq.module`, byte-identical
  (symbol, slot)). `resolve_got_target` keeps its W2 callers (S10/S13).
- **S8** platform fn-name stamp — was `resolve_platform_effect_target`; now the
  `DefKind::PlatformEffect` discriminator off the same fetch (`fq_name = home/fq.symbol`).
- **S9** `PrimitiveExtern` ABI key — was `resolve_extern_target`; now the
  `DefKind::PrimitiveExtern` arm (`fq.symbol` IS the ABI key).
- **Locals-before-keyed-read (0619 item 2, §1.1 pinned invariant):** `compile_var_apply`
  checks `variables.contains_key(name)` FIRST (moved above the ctor/keyed arms) so
  a shadowing local (the producer's self-recursion carve-out over-matches it) is
  never mis-dispatched to the carrier's FQ. Commented as the pinned invariant.
- `resolve_platform_effect_target` / `resolve_poll_effect_target` /
  `resolve_extern_target` lost their SOLE (apply-site) callers → `#[allow(dead_code)]`
  + W3-delete note (kept for their `resolution/tests.rs` unit callers; deleted in
  W3 §3 S23). `data_constructor_info` deleted (dead after S3). `entry_at` added to
  `CompileContext` (context.rs) as the §1.3 reader.

**BLOCKER — S3/S4 (ctor `Apply`) + all member-aliased references, FIXME 0620 →
/arch.** The §1.1 carrier for a sum ctor / field accessor MUST be the canonical
`member_key` terminal (`IO.Pure`, `Box.v`), but the producer records the bare
**alias** (`Pure`, `v`) — `cranelisp_types::resolve::Resolved.fq` (resolve.rs:458/687)
composes `symbol: canonical_symbol(WRITTEN_NAME)`, not the terminal storage key
where `Resolved.entry` lives. `entry_at` (direct read) lands on the `Import` alias
and misses (`undefined function: v`/`Pure`). BROAD: every bare sum-ctor construction
+ every field-accessor call, same-module and imported. Dispatch-leg Apply carriers
(trait/sig-dispatch/auto-curry) are UNAFFECTED (they record the mangled key
directly). The W0.1b sweep table mis-attributed the ctor recorder to `instantiate_ctor`;
the actual recorder is `record_reference_target` → `scope_resolve`, which emits the
alias. **Fix is cross-crate (cranelisp-types resolve.rs OR typecheck
record_reference_target) — out of the backend-narrow boundary → flagged to /arch
(FIXME 0620), NOT improvised (Rev-2 forbids a backend chain-follow).** S3/S4 are
therefore kept on the UNTOUCHED legacy `lookup_constructor` resolver (Rev-2 §1.2
option b, "the wave has not arrived" — NOT a hybrid; the ctor kind is simply not
flipped) so ctors still compile; only the member-aliased accessor calls (UserFn
kind, keyed path) red the e2e suite.

**KC-W0-6 (backend fixture sidecars):** NOT done — ~23 backend unit fixtures
(`poll_codegen`/`par_codegen`/`dispatch`/`extern_call`/`module_assembly`/`launch`
tests) hand-build empty `resolved_targets` and now hard-miss the keyed read;
populating them is co-land-with-W1 work, deferred until the producer gap unblocks
a landable W1 (populating fixtures that can't ship is premature).

**Tree state / next.** The W1 backend implementation is complete, builds clean
(`cargo check`/`--tests`/clippy zero warnings), and is `golden_clif_w0b` 5/5
byte-identical — but is left UNCOMMITTED (stashed after committing this note +
FIXME 0620) because it reds the suite pending the producer fix. Sequence to land:
(1) /arch rules FIXME 0620 (canonical terminal-key carrier for member-aliased
refs); (2) a typecheck-or-types /dev change-set lands it (+ per-leg unit pins);
(3) re-deploy /dev (backend) → pop the W1 stash, flip S3/S4 to the keyed
`ctor_meta_at` read, populate the KC-W0-6 fixture sidecars, verify golden +
13-RED-baseline-unchanged, commit.

### /arch (0620 ruling + producer re-sweep) — RULED; types half LANDED (2026-07-16)

**Ruling (`backend-keyed-consumer.md` §1.1.2, FIXME 0620 deleted).** Neither
filed candidate as filed: candidate 1 (repoint `Resolved.fq`) rejected — `fq`
is the display/attribution/`callees` reference identity under the S20/S21
byte-identity pins; candidate 2 as filed ("derive off `Resolved.entry`'s
storage key") is not implementable — a `ModuleEntry` does not carry its own
table key (an accessor is a plain `UserFn` `Def`), and the class is BROADER
than member keys: **renamed imports/re-exports `[(foo bar)]` (grammar §2)
hit the identical gap**, unrecoverable from any terminal entry. The uniform
fix: **the walk surfaces the terminal storage key** — `Resolved` gains
`storage_key` + `storage_fq()` (threaded through both chain-follow walks; the
only actor that knows the key) — and the recorder records THAT.
`Resolved.fq` untouched → display byte-identical by construction.

**Landed by /arch (types half, behaviour-invariant):** `Resolved.storage_key`
+ `storage_fq()` + `#[non_exhaustive]`; `chain_follow_committed`/
`chain_follow_to_home` thread the key (`resolve_terminal_entry_home_and_key`
pub(crate) sibling; the public fn is now its projection); 5 unit pins
(`resolve/tests.rs::storage_key_*`: member alias, renamed import, qualified
renaming re-export, prelude-fallback alias, unaliased identity); types
`public-api.txt` +2 additive; `interfaces.md` two-identities narrative; types
CLAUDE.md trap entry. Workspace compiles untouched; types suite 199/199.

**→ /dev (typecheck) ACTION — the ~3-line recorder flip + pins (unblocks W1):**
1. `checker.rs::record_reference_target` — the `resolved_targets` insert
   (checker.rs:1429) takes `resolved.storage_fq()` instead of
   `resolved.fq.clone()`. `user_fn_refs` (the `callees` feed) STAYS on
   `resolved.fq` — persisted-value stability; residual filed as FIXME 0621.
2. `callees.rs::builtin_storage_fq` — the `def_resolved` arm returns the
   resolution's `storage_fq()` (same value today; structural uniformity).
3. Unit pins per §1.1.2: member-aliased ctor carrier == `member_key`
   (`Pure` → `IO.Pure`); member-aliased accessor carrier == `member_key`
   (`v` → `Box.v`); renamed-import carrier == source storage key.
4. NO `CACHE_SCHEMA_VERSION` bump (value-only conformance repair inside the
   schema-19 window; carrier unread until W1; `BUILD_ID` covers dev-cache
   skew).

**Re-sweep verdict (the class close).** §1.1.2's recorder-grounded 19-row
table traces the ACTUAL recorder for every reference kind (the §1.1.1 sweep
had mis-attributed the ctor recorder to `instantiate_ctor`; the bare-spelling
recorder is `record_reference_target`) and verifies recorded SYMBOL ==
terminal storage key. After the /dev flip: **NO remaining producer gap for
any W1 OR W2 kind** — rows 1–19 all storage-key-correct; the rename surface
of the language is exactly the `Import`-edge `source.symbol`, which the walk
now threads across every edge. §1.1's new carrier value-source rule
(walk-resolved `storage_fq()` / mint-resolved probe-or-registration key /
transport — NEVER a written spelling) is the structural close; `/review`
rejects violations on sight. **W1 re-deploy (pop `stash@{0}`, flip S3/S4 to
keyed `ctor_meta_at`, populate KC-W0-6 fixtures) is GO once the /dev flip
lands — no further producer prerequisites, W2 producer work also nil.**

### /dev (W1 re-deploy) — LANDED (2026-07-16)

Coordinated typecheck-recorder-flip + backend-W1 re-deploy, one change-set.

**Step 1 — recorder flip (typecheck, value-only, no schema bump).**
- `checker.rs::record_reference_target`: the `resolved_targets` insert now takes
  `resolved.storage_fq()` (was `resolved.fq.clone()`) — records the TERMINAL
  storage key, not the written alias (§1.1.2). `user_fn_refs`/`callees` UNCHANGED
  on `.fq` (FIXME 0621). Carrier rustdoc updated to the two-identities model.
- `program/callees.rs::builtin_storage_fq`: the `def_resolved` arm maps
  `r.storage_fq()` (was `r.fq`) — same value today, flipped for uniformity.
- 3 unit pins (`program/tests.rs`): member-aliased bare ctor carrier ==
  `member_key(Maybe, Some)`; member-aliased bare accessor carrier ==
  `member_key(Box, v)`; renamed-import `[lib [foo as bar]]` carrier == source
  storage key `lib/foo`. Typecheck lib suite 693/693.

**Step 2 — backend W1 re-deploy.**
- `git stash pop stash@{0}` — clean (backend-only, disjoint from the typecheck
  flip); the S1–S9 `apply.rs` flips + `entry_at` + locals-before-keyed-read
  invariant landed intact.
- **S3/S4 ctor `Apply` flipped** (`apply.rs::compile_var_apply`): the legacy
  `lookup_constructor` chain-follow → keyed `ctor_meta_at` read off the callee
  Var's carrier (now the canonical `member_key`). Callee carrier computed ONCE,
  reused by the ctor branch + the S5/S7 direct-call arm. This removes the last
  apply-site caller of `lookup_constructor`; the fn stays (live W2/W3 callers in
  `literals.rs`/`fn_as_value.rs`/`match_codegen.rs` S11/S16/S19/S20) for the §3
  W3 deletion — no `#[allow(dead_code)]` needed (not yet dead).
- **KC-W0-6 fixture population (24 backend unit fixtures)**: the harness now
  threads the dispatch carriers it computes from the tables it builds —
  `TestCheckResult.resolved_targets` + `make_def_entry_slot_with_targets`/
  `make_def_entry_with_targets` (compile_to_module fixtures: dispatch/extern/
  match/module_assembly), `jit::compile_defn_with_targets` +
  `lenient_mono_from_expr(expr, resolved_targets)` (CLIF-probe fixtures: poll/
  par/launch), plus shared `call_carriers`/`insert_user_fn_stub` helpers (a
  NotDetermined stub makes `entry_at` resolve to the byte-identical FuncId tail).
  `extern_..._without_resolved_call_fails` assertion updated to the Rev-2
  carrier-miss error (replaces the old "undefined function" surface).

**Acceptance — ALL GREEN.** `golden_clif_w0b` 5/5 byte-identical (mechanism
change, not codegen); backend unit 411/411; typecheck unit 693/693; the 5 named
accessor/ctor e2e classes GREEN + `applied_annotation_bare_var_pins_through_ctor`
GREEN; full suite **exactly 13 RED** — unchanged known-defect guards (3×
generic_value §3.11, ownership_reuse, 2× spec_03 §3.11, 2× spec_05, 2× spec_07,
2× vec_assoc UAF [W2 fix], stdlib_conformance = SG-1 `derive`/0613). ZERO
W1-signature reds (no carrier-miss/entry-miss anywhere in the suite) → no
W1-introduced regressions. No public-API/schema/cache change (backend-internal +
value-only typecheck flip). `cargo check --workspace --tests` clean; no new
clippy lints in touched files.

### /dev (W2) — value seam + 0585 backstop + vec-assoc UAF (2026-07-16, LANDED with a scoped carry)

Backend-narrow. Three deliverables; two clean, the third (0585) surfaced a
cross-crate scope finding (below). **Baseline 13 → 11** (VA-1/VA-2 flipped;
VP-3/4/5 carry — see finding). `golden_clif_w0b` 5/5 byte-identical.

**1. Value-seam flip (S10–S18) — the carrier read replaces the value-site
resolvers.** `MonoExpr::Var.resolved_target` is threaded from the `compile_expr`
dispatch (`fn_compiler.rs`) into `compile_var`, and on into `compile_fn_as_value`
→ `compile_fn_wrapper_body` → `emit_wrapper_call`, plus `emit_curry_target_call`
and `compile_auto_curry`/`_wrapper` (auto-curry threads the Apply carrier;
`apply.rs` AutoCurry arm passes `apply_target`). Six new keyed-read helpers on
`CompileContext` (`context.rs`): `is_callable_target_at` (S12), `arity_at` (S14),
`callee_summary_at` (S15), `is_inline_primitive_at` (S17/S18), `got_entry_at`
(S10), `is_slotless_template_at` (0585). Per-site:
- S11 nullary-ctor fold → `nullary_constructor_tag(carrier)` → `ctor_meta_at`.
- S12 fn-as-value gate → `is_known_function(name, carrier)` (`func_ids` fast-path
  ∨ `is_callable_target_at`).
- S13 operator-as-value → direct `got_entry_at({primitives, <mapped>})` (§1.4
  synthesized name, no carrier/resolver).
- S14 arity → `arity_at`. S15 summary → `callee_summary_at`. S16 ctor-as-value →
  `ctor_meta_at`. S17 vec-query → `is_inline_primitive_at(carrier)`. S10
  GOT-entry → `got_entry_at(carrier)` + hard-miss (Rev-2, no scan fallback).
- S18 (BuiltinFn curry leg) → `is_inline_primitive_at({primitives, jit_name})`;
  the TraitMethod arm keys `emit_wrapper_call` off `{impl_module, mangled}` (the
  W0.1b resolution product).

**Resolvers that lost their value-site callers (for W3 deletion, §3 S23):**
`resolve_is_callable_target`, `resolve_func_arity`, `resolve_vec_query_primitive`,
`resolve_callee_summary` (each now caller-less), and `resolve_got_target` /
`resolve_got_entry` (only the dead-but-present `resolve_got_entry` references
`resolve_got_target` now). All marked `#[allow(dead_code)]` with a §3-S23 note;
the four caller-less ones dropped from the `compiler/mod.rs` re-export (kept only
`resolve_got_target` for the dead `resolve_got_entry`). `lookup_constructor`
retains its S19/S20 callers (both W3), so it is NOT yet dead. **W3 grep-gate
delta:** after W3 deletes S19–S23, the gate goes green — the value seam already
holds zero live resolver reach. Fixture top-up: `test_support.rs` populates the
value-position vec-query Var carrier (`collect_vec_query_value_carriers` →
`make_def_entry_slot_with_targets`) so the 3 `vec_*_as_value` unit fixtures key
correctly. Backend unit 416/416.

**2. The 0585 loud backstop (design §7 leg 2) — LANDED, but see the finding.**
`literals.rs::compile_var`: a value-position `Var` whose carrier fetches a
slot-less `Polymorphic`/`Constrained` template now hard-`CodegenError`s with the
§7 wording ("generic value reference '<name>' reached codegen without a mono
instance"), release builds included, REPLACING the misleading `undefined
variable: gcount` leak at `literals.rs:191`. Confirmed firing on the die case.

> **CROSS-CRATE FINDING (VP-3/4/5 need typecheck, not backend).** The three §B
> die-leg negatives (`generic_value_{in_if_branch,in_match_arm,as_vec_element}_
> indeterminate_neg`) assert the output **contains `"ambiguous"` and does NOT
> contain `"codegen error"`** — and their `// defect:` locus is
> `crates/cranelisp-typecheck §3.11 finalization gate ... owner=/dev`. Every
> backend `CranelispError::CodegenError` displays as `"codegen error at …:"`, so
> **no backend error — including this honest §7 backstop — can satisfy the
> assertion.** The die case (`(if c gcount gother)` at top level, a polymorphic
> value with no concrete use) must die CHECK-SIDE with the §3.11.1 ambiguity
> BEFORE codegen. typecheck's `find_ambiguous_value_position`
> (`program/finalize.rs`) already scans if/match/vec positions but is skipped for
> a top-level POLYMORPHIC expression (the known unlanded gap: typecheck
> CLAUDE.md "the §3.11 ambiguity gate … Not yet landed … reported to /sprint as a
> coordinated seam"). **These three are a typecheck §3.11 finalization fix, out
> of backend narrow-deployment.** They stay RED as failing-not-ignored repros
> (their own record+trigger — no redundant FIXME per the "no FIXME with a failing
> test" rule). The dispatch's "backend backstop flips them green / 13 → 8" is
> therefore not achievable backend-only; the honest outcome is **13 → 11**, and
> the 0585 CLASS closes when the typecheck §3.11 leg lands alongside this
> backstop. Recommend `/sprint` schedule a typecheck `/dev` deployment for the
> §3.11.1 top-level-polymorphic-value gate.

**3. vec-assoc UAF ×2 (VA-1/VA-2) — ROOT-CAUSED + FIXED, behaviorally verified.**
- **Root cause (RC-trace + CLIF evidenced).** `(defn assoc [v i x] (vec-set v i
  x))`: the COW in-place arm (rc==1) returns the SAME Vec pointer, so `v`'s
  reference transfers into the returned Vec — but `v` is a heap param that
  `pop_scope_with_cleanup` `rc_dec`s at scope exit (block4 in the CLIF decs `v3`
  unconditionally), freeing the just-returned Vec. RC trace: one `alloc rc=1` →
  premature `free rc=0 len=3` BEFORE the caller's `vec-get` reads it → garbage /
  `--link` SIGABRT. The identity fn `(idv [v] v)` is safe only because a bare-Var
  return is a recognized move (`return_var_in_scope`); a COW-computed return that
  ALIASES the param was not.
- **Fix at the RC-emission seam** (not a symptom move). New free fn
  `return_cow_source_in_scope` (`fn_compiler.rs`) recognizes a body that is
  directly `(vec-set v …)`/`(vec-push v …)` with `v` a scope-frame binding →
  records `FnCompiler::return_cow_source`. Two coordinated effects: (a) `v` folds
  into `skip_var` so its scope-exit dec is suppressed (`protect_return_value`
  no-ops when `skip_var` is set — no spurious inc); (b) `compile_vec_set`/
  `compile_vec_push` (`vec_codegen.rs::cow_source_ownership`) flip the COW **copy**
  branch from `Borrowed` to `Owned` so the copy path (which returns a FRESH Vec,
  leaving `v` unreferenced) releases `v` itself — scope cleanup no longer does.
  Both arms then decrement `v` exactly once: in-place transfers, copy releases.
  Byte-identical when the pattern is absent (`Borrowed`, no emission) — hence
  `golden_clif_w0b` unchanged.
- **Behavioral verification (per the "verify fix, not symptom" rule).** exit=99
  under `--run`; VA-1 (REPL, full value) + VA-2 (`--link`, exit 99, no SIGABRT)
  GREEN; **10× `--run` deterministic 99**; RC trace balanced (one alloc, one free
  — the free now lands AFTER the `vec-get` read). Copy-branch exercised with a
  SHARED source (`w` used by both `assoc` and a later `vec-get w`) → `w` COPIED
  (unmutated, `b=6`), result 105, clean exit, no leak/double-free — the `Owned`
  copy branch verified. `vec-push` param-return variant → 30. **VA-4**
  (`vec_cow_value_use_leak`, the leak-inversion fence, all 3) stays GREEN — no
  over-correction into a leak.
- **VA-3 unit pin** (`return_cow_source_tests`, 5 tests): vec-set/vec-push on a
  returned scope param ⇒ `Some(v)`; identity bare-Var return, non-frame source,
  and `vec-get` (non-mutating) ⇒ `None`. Pins the ownership DECISION at the seam.

**Release gate:** `cargo check -p cranelisp-backend` (lib + `--tests`) zero-warning;
`clippy --all-targets` no new lints in touched files; no public-API/schema/cache
change (CACHE_SCHEMA_VERSION stays 19, backend-internal). Full suite 11 RED (the
13 W1 baseline − VA-1/VA-2); every RED traces to a known open defect (VP-3/4/5
typecheck §3.11, R16/R17 ×2, 0590 ×2, spec_05 ×2, ownership_reuse, SG-1 derive).

### /review (W2) — value seam + 0585 + vec-assoc (2026-07-16, `369c226c`)

**Gating verdict: W2 is CLEAN to build W3's deletions on.** The value seam holds
zero live resolver reach (census grep-verified); Rev-2 held (hard `CodegenError`
on S10 carrier/entry miss, §1.2 wording; the only fallbacks are the local
per-unit `func_ids`/`func_arities` maps, which the design blesses — not
resolvers); S13/S18 use the §1.4 synthesized `{primitives, <name>}` direct read;
all six `context.rs` helpers are thin kind-arm projections off `entry_at`;
operator-as-value probed working under TestStandard. Dead-marking census is
ACCURATE: the four caller-less resolvers have only `resolution/tests.rs` unit
callers; `resolve_got_target`'s sole non-test caller is the dead
`resolve_got_entry` (apply.rs:1777); `lookup_constructor` retains exactly its
S19 (match_codegen.rs:263) + S20 (:600) callers — the W3 grep-gate delta is
correctly scoped. No public-surface movement (all `pub(crate)`). No `unsafe`
touched. 0585 backstop fires with the exact §7 wording (probed:
`(if (lt-i64 0 1) gcount gother)` → "generic value reference 'gcount' reached
codegen without a mono instance"), plain release-reachable error, correctly
ordered after the local-`variables` and `is_known_function` gates. **The `/dev`
VP-3/4/5 finding is CONFIRMED correct**: the die-leg negatives
(`tests/generic_value_use_mono.rs`) assert `contains("ambiguous")` AND NOT
`contains("codegen error")` — structurally unsatisfiable by any backend
`CodegenError`; they need the typecheck §3.11.1 gate; not a W2 defect.

**Finding R-W2-1 (Important — the headline): the vec-assoc RC fix is NARROW;
the UAF class stays open on sibling shapes (probed at `369c226c`,
deterministic, both faces).** The fix covers only the direct-body shape. Two
2-line siblings still fail:

- `(defn f [v i x] (let [r (vec-set v i x)] r))` +
  `(vec-get (f [1 2 3] 1 99) 1)` → REPL garbage i64 (0/3 correct; RC trace:
  alloc → premature free BEFORE the read); `--link` with
  `(defn main [] (Pure …))` deterministically ABORTS ("corrupted double-linked
  list", exit 134) — the exact VA-1/VA-2 signature.
- `(defn m [v i x] (match i [_ (vec-set v i x)]))` → REPL garbage.

**Mechanism (evidenced, not conjectured): both siblings go GREEN under
`CRANELISP_NO_OWNERSHIP=1`.** The kill path is the B3.2 return-protect elision:
the enclosing fn's ownership summary computes `result == Fresh` — typecheck
`ownership/transfer.rs:590` defaults a summary-less callee's result to
`ResultMode::Fresh`, and the COW primitives carry no summary — so
`return_is_fresh_by_summary` elides `protect_return_value`,
`pop_scope_with_cleanup` decs `v`, and the COW in-place arm's returned ALIAS is
freed. A `Fresh` result claim for a COW op is FALSE on the rc==1 in-place arm
(dynamically Fresh-or-AliasOf(0)); the `unwrap_or(Fresh)` default is the
UNSOUND direction for the elision consumer — it contradicts the spine's
absence-⇒-conservative rule (`ownership-inference.md` monotone soundness) and
falsifies the B3.2 rustdoc claim (fn_compiler.rs: "`result == Fresh` is
therefore now sound for *any* body shape"). The W2 recognizer compensates at
exactly ONE body shape — a second, narrower codepath deciding what the summary
already claims (the divergent-duplication smell). Probed SAFE for the record:
direct body (fixed), if-branch (one or both COW arms), chained
`(vec-push (vec-push v 4) 5)`, let-bound local source, lambda-captured source,
COW result re-consumed in-body, shared-source copy branch (101, RC balanced —
no Owned-flip leak; VA-4 verified independently), nested double-COW aliasing
corners (correct; the `is_last_use` gate confines the flip to one site).
**Routing:** (a) `/testing` commits the two sibling repros failing-not-ignored
(REPL + `--link` faces; record+trigger, no FIXME per the failing-test rule);
(b) the class fix is typecheck-side (COW primitive result facts / the
transfer.rs:590 Fresh default) — cross-crate, out of backend narrow scope,
needs `/sprint` to schedule with `/arch`/`/qa` attribution; the B3.2 rustdoc
claim corrects in the fixing change-set; (c) `/qa`: the vec-assoc matrix
covered VA-1..4 but no body-shape variant axis (direct/let/if/match ×
{in-place, shared}) — the definition-variant coverage lens applies. Not a W2
regression (pre-existing; W2 fixed a real subset and its own claims all held) —
hence Important, not Blocker; must be scheduled in-sprint, not carried by habit.

**Finding R-W2-2 (Minor, `/dev`): `return_cow_source_in_scope` rustdoc
overclaims its guard.** "Restricting to the direct body guarantees `v` is used
exactly once" and "the element argument aliasing `v` … does NOT match" are
false of the function as written — `(vec-set v (vec-get (vec-set v 0 1) 0) x)`
matches, with `v` used twice (the recognizer never scans `args[1..]`). The
operative safety condition lives elsewhere: `cow_source_ownership` only flips
inside the `is_last_use` COW arm, so the flip lands at exactly one site and the
suppressed scope dec is balanced by exactly one release (probed correct in the
aliasing corners). Correct the rustdoc to name the real invariant (or add the
scan it claims) — an RC seam documenting a guard it doesn't enforce is a
maintenance hazard.

Minor observation (no action owed): stale `lib.rs` rustdoc still narrates
resolver-based arity/GOT resolution (lines 37/106/556/842/1463 area) — already
scheduled for W3 by design §4.

### /dev (W3) — the deletion wave (2026-07-16, BLOCKED on a producer gap → FIXME 0622)

Backend-narrow. The W3 deletions were IMPLEMENTED in full and GREEN in isolation,
but landing them exposes a **cross-module-mono `pattern_ctors` producer gap** in
typecheck that the §1.1.2 completeness re-sweep missed. Per Rev-2 (§1.2, no
keyed-read-else-resolver hybrid) and the dispatch ("a match-position hard-miss is
a producer gap to flag to /arch, NOT a workaround"), **W3 cannot delete the S19
fallback until the producer gap closes** — mirroring W1 → BLOCKED on 0620 → W1.1b
→ re-deploy. Work preserved in `git stash@{0}` ("S110 W3 backend deletion …");
tree restored to the clean W2 green baseline.

**What was implemented (all green in the stash):**
- **S19 (`match_codegen.rs:263`)** — deleted the `None`-arm `lookup_constructor`
  fallback; a `None` `resolved_ctor` on any ctor pattern is now a hard
  `CodegenError` (Principle 18; the §5 W0.b totalization claim).
- **S20 (`match_codegen.rs:600`)** — folded `resolve_field_types` onto
  `ctor_meta_at(resolved_ctor)` (renamed `concrete_field_types`); the arm's carried
  storage identity replaces the redundant `lookup_constructor` re-resolution.
  Threaded `fq` through `compile_constructor_pattern` → `compile_data_pattern`.
- **Deleted the resolver family (§3 S21–S23):** `resolve_driven` + `resolve_chain`
  + the `symbol_tables.iter()` global scan + all ten entry points
  (`resolve_got_target`, `resolve_is_callable_target`, `resolve_vec_query_primitive`,
  `resolve_callee_summary`, `resolve_platform_effect_target`,
  `resolve_poll_effect_target`, `resolve_extern_target`, `resolve_func_arity`,
  `lookup_constructor` in `context.rs`, `resolve_got_entry` in `apply.rs`).
  `resolution.rs` shrinks to the two naming primitives (`got_data_symbol_name`,
  `inner_fn_discriminator_for`). Deleted the 8 resolver unit tests in
  `resolution/tests.rs` (kept the 2 naming-primitive tests). Deleted the backend
  `lenient_mono_from_expr` wrapper (`lib.rs`); its test-only caller
  (`jit::compile_defn`) now calls `cranelisp_types::MonoExpr::lenient_from_expr`
  directly. Dropped `resolve_got_target` from the `compiler/mod.rs` re-export.
- **Grep gate (would be) GREEN:** `resolve_driven|resolve_*_target|lookup_constructor|
  lenient_mono_from_expr` → zero LIVE occurrences in `crates/cranelisp-backend/src/`
  (only rustdoc/comment mentions remain; the `vec_codegen::resolve_elem_*_fn_ptr`
  drop-glue helpers and `match_codegen::resolve_field_types`→`concrete_field_types`
  are not name resolvers). Backend rustdoc updated (`lib.rs //!` lines 37/84/106/556-area,
  `compiler/mod.rs`, `context.rs` `module_aliases` field, `cranelisp-backend/CLAUDE.md`
  seam map). `module_aliases` is now threaded-but-unread — its removal from
  `compile_to_module`/`build_compile_context` moves the `pub` surface, so deferred
  out of W3 (noted in the field rustdoc).
- **Backend unit suite 408/408 GREEN** in the stash (416 − 8 deleted resolver
  tests). Threaded a `pattern_ctors` sidecar into the test harness (`test_support.rs`
  `TestCheckResult`/`make_def_entry_inner`) — the KC-W0-6 discipline — and populated
  it in `test_compile_match_with_fields`. `golden_clif_w0b` 5/5 byte-identical.

**The blocking gap (FIXME 0622, `target: /arch`).** A generic ctor-pattern body
(`is-ok?`/`unwrap-or` in `fn.result`) monomorphised by a cross-module call (from
`fn.result.test` via `[super […]]`) yields a mono instance whose
`MonoMatchArm.resolved_ctor` is `None`: the mono view is built at
`monomorphise.rs:519` with the CALLER's `pattern_ctors`, but the template's Ok/Err
pattern spans were recorded in the DEFINING module's separate check run. The
`monomorphise.rs:516-518` comment states the false assumption ("the original
template check's entries serve every instance"). Masked on W1/W2 by the S19
fallback; W3's deletion surfaces it as a hard miss that fails `fn.result.test`
codegen → cascades to `unknown type Result` → ~53 `spec_11_stdlib` /
`stdlib_conformance` REDs. Same-module mono and direct user matches are correct
(verified). The fix is typecheck-side (transport / union the defining module's
template `pattern_ctors` into the cross-module mono view — the pattern-ctor analog
of W0.1b's storage-module derivation), out of backend narrow scope.

**Recommendation:** `/arch` rules the transport mechanism (FIXME 0622); `/sprint`
schedules a typecheck `/dev` fix + a `/testing` cross-module-mono pattern-ctor
repro (failing-not-ignored); then re-dispatch W3 `/dev` (backend) to pop
`stash@{0}` and complete the grep-gate deletion. Full suite currently at the
clean W2 11-RED baseline (unchanged; W3 landed nothing).

**Note for `/audit`:** the resolution seam is NOT yet grep-zero — W3 is blocked on
FIXME 0622. The backend end-state (zero live `resolve_*`) is implemented and
staged in `stash@{0}`, pending the producer fix.

### /arch (0622 ruling + exhaustive producer sweep) (2026-07-16)

**FIXME 0622 RULED + deleted** — `design/arch/backend-keyed-consumer.md`
**§1.1.3** is the binding record. Headline findings:

1. **The gap class is CHECK-RUN provenance, broader than filed.** The mono view
   at `monomorphise.rs:519` reads the ENCLOSING run's `pattern_ctors` while the
   body was annotated by the per-instance recheck. That misses cross-module
   (the filed repro) AND cross-check-run same-module (REPL-incremental:
   template defined in input 1, first concrete call in input 2) — the latter
   kills the FIXME's union candidate outright (the defining run's map no
   longer exists at mint time).
2. **The transport mechanism already exists — no new machinery.**
   `recheck_body_for_mono` re-checks the full body with the fresh per-instance
   map live and `current_module` switched to `home`; `check_constructor_pattern`
   → `instantiate_ctor` re-records every ctor-pattern span into the
   per-instance map, defining-module-correct, and the auto-curry drain runs
   inside the swap window. The per-instance map is already complete for all
   three carriers; P7 just reads two different maps.
3. **One sibling cell found by the exhaustive sweep:**
   `register_test_fn_mono_roots` (`register.rs:931`) — same structure (view
   from enclosing maps, body from per-root recheck); correct-by-reach same-run,
   gapped on the cross-run retry edge.
4. **Why this is the LAST producer axis:** a span-keyed sidecar has exactly
   three axes — key values (closed 0616), carrier values (closed §1.1/§1.1.2),
   map instance (closed §1.1.3). The §1.1.3 matrix dispositions every cell of
   3 carriers (grep-closed: `resolved_target`×2 + `resolved_ctor`) × 9
   view-construction paths (grep-closed `from_expr`/`lenient_from_expr`
   callers).

**`/dev` action (typecheck-narrow, ONE change-set, pinned §1.1.3):**
`finalize_mono_codegen_view` takes the per-instance `resolutions` and builds
the view from ITS two sidecars (delete the `:516–518` false-assumption
comment; state the pairing rule); `register_test_fn_mono_roots` builds from
its per-root recheck maps; `sweep_post_pass_outputs` extends all THREE
`MethodResolutions` fields (drops `pattern_ctors` today — harmless but
partial). NO `cranelisp-types` edit, NO public-API movement, **NO
`CACHE_SCHEMA_VERSION` bump** (value-only conformance repair inside the
schema-19 window, 0472/0620 precedent; `BUILD_ID` covers dev-cache skew).
Unit pins failing-first per §1.1.3 item 4: cross-module mono ctor-pattern
carrier (RED on main), cross-run same-module twin (RED on main), same-run
regression pin. **The unit pins ARE the failing-not-ignored defect record —
do NOT also schedule a `/testing` e2e repro** (an e2e cannot fail on main
while the S19 fallback stands; the ~53 stdlib REDs on the stash are the W3
re-deploy's wave-level acceptance).

**W3 re-deploy verdict: after the `/dev` change-set lands with its pins, the
producer is COMPLETE across all carriers × construction paths — W3 pops
`stash@{0}` (do not touch it until then), deletes S19/S20 + the resolver
family, and runs the §3 grep gate with NO further producer prerequisites.
This is the last producer touch of the 0583 initiative.**

### /dev (W3 re-deploy) — 0622 producer fix + W3 backend deletion (2026-07-16, LANDED)

Coordinated typecheck (0622 map-provenance fix) + backend (staged W3
deletion) re-deploy per the `/arch` §1.1.3 ruling. Two commits on `main`.

**Step 1 — the 0622 map-instance fix (`4c899dd9`, typecheck-only, no
`cranelisp-types` diff, no schema bump).** Three edits, all "read the right
map" per the check-run pairing rule:
1. `traits/monomorphise.rs::finalize_mono_codegen_view` — signature takes the
   per-instance `resolutions: &MethodResolutions` (was `resolved_targets:
   &HashMap`); the view is now built as `MonoExpr::from_expr(body,
   &resolutions.pattern_ctors, &resolutions.resolved_targets)` — BOTH sidecars
   off the one per-instance map. The `:516–518` false-assumption comment is
   deleted and the pairing rule stated in its place. P7 caller passes
   `&resolutions`.
2. `program/register.rs::register_test_fn_mono_roots` — the sibling cell:
   `build_concrete_codegen_view(..)` now takes `&resolutions.pattern_ctors,
   &resolutions.resolved_targets)` (the per-root recheck maps), not
   `state.method_resolutions.*` (closes the cross-run retry edge).
3. `program/finalize.rs::sweep_post_pass_outputs` — added
   `accumulator.pattern_ctors.extend(taken.pattern_ctors)` so the sweep of the
   3-field `MethodResolutions` is total (was dropping `pattern_ctors`;
   behaviour-invariant today).

**The 2 (+1) unit pins** (`program/tests.rs`, spec: §1.1.3): a
`collect_resolved_ctors` walker + a `mono_match_arm_ctor` finder, then —
(i) `mono_ctor_pattern_view_cross_module_carries_resolved_ctor` (RED on main:
arm `None`; GREEN after: `lib/Box`), (ii)
`mono_ctor_pattern_view_cross_run_same_module_carries_resolved_ctor` (the
REPL-incremental twin — template checked in run 1, first concrete call in run 2;
RED on main; GREEN after: `test/Box`), (iii)
`mono_ctor_pattern_view_same_run_carries_resolved_ctor` (regression guard —
GREEN on main too). RED-on-main verified by reverting the one-line
`finalize_mono_codegen_view` fix: pins (i)/(ii) fail with `left: None`, (iii)
passes — then the fix restored. These pins ARE the failing-not-ignored 0622
record (no `/testing` e2e — an e2e cannot fail on main while S19 stands).
Typecheck unit suite 696→699 tests, all GREEN.

**Step 2 — pop the staged W3 backend deletion (`be06f6cb`).** `git stash pop`
of `stash@{0}` applied CLEANLY (backend-only, 13 files, disjoint from the
typecheck fix; stash auto-dropped on success). The deletion (net **-993 LOC**,
209 ins / 1202 del): `resolve_driven` + `resolve_chain` + the arbitrary-order
`symbol_tables.iter()` global scan; the ten resolver entry points
(`resolve_got_target`, `resolve_is_callable_target`,
`resolve_vec_query_primitive`, `resolve_callee_summary`,
`resolve_platform_effect_target`, `resolve_poll_effect_target`,
`resolve_extern_target`, `resolve_func_arity`, `lookup_constructor`,
`resolve_got_entry`); the S19 None-arm fallback + S20 folded onto
`ctor_meta_at(arm.resolved_ctor)`; the backend `lenient_mono_from_expr` wrapper
+ the `lib.rs:909` lenient rebuild arm; the 8 dead resolver unit tests + the
`mod.rs` re-export trim.

**Acceptance — all met:**
- **Grep gate GREEN (the zero-resolver structural proof).** The acceptance
  grep `resolve_driven|fn resolve_.*_target|fn lookup_constructor|lenient_mono_from_expr`
  and the full W3 gate both return ZERO live-code matches in
  `crates/cranelisp-backend/src/` — every remaining occurrence is rustdoc /
  comment. `resolution.rs` retains exactly `got_data_symbol_name` +
  `inner_fn_discriminator_for`.
- `golden_clif_w0b` **5/5 GREEN byte-identical**.
- Backend unit suite **408/408 GREEN**; typecheck unit suite **699/699 GREEN**.
- Full suite back to the **11-RED baseline** (VP-3/4/5 ×3
  [`generic_value_use_mono` if/match/vec], R16/R17 ×2 [`spec_03_types`
  value-position-constraint + unresolved-return-type-dispatch], 0590 ×2
  [`spec_07_traits` hkt-sig + bare-user-type-sig], spec_05 ×2 [ctor-trailing-form
  + multi-arity-no-main], `ownership_reuse` chaining-toggle-off, SG-1 `derive`
  quasiquote). W3 restored 11, added none — the ~53 stdlib cross-module-mono
  hard-miss REDs the staged deletion caused are all GREEN (stdlib conformance
  now fails ONLY on `derive`, the pre-existing SG-1 quasiquote defect).
- `cargo check --workspace --tests` clean; clippy clean at all edit sites (the
  only warnings are the pre-existing project-wide `result_large_err` +
  doc-list baseline). No public-API/schema/cache impact (typecheck value-only,
  backend deletion).

**For `/audit`:** the resolution seam is now grep-zero — the backend performs
ZERO name resolution; the 0583 backend half is complete and the four-axis
producer space (key / value-source / storage-key / map-provenance) is closed.

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
- **W0.1b — cross-module storage-module fix (`/arch` ruled `b48902ab`; `/dev` coordinated
  types+typecheck+int, before W1).** The W0.1 review + arch completeness sweep found the
  producer records the CALLER's module, not the STORAGE module, on three legs — masked
  today by the backend global scan, hard-fails at W1's keyed read (Rev-2: no discovering
  gaps via backend misses). Fix per `backend-keyed-consumer.md §1.1.1`: (i) **trait-method**
  — `ModuleEntry::TraitImpl.impl_module` + `ResolvedCall::TraitMethod.impl_module` (both
  REQUIRED, no serde default, schema-19 window, cross-crate atomic); `dispatch_target_fq`
  reads it (also repairs the S101 reverse-index for cross-module trait calls); (ii)
  **AutoCurry plain leg** — transport the callee Var's recorded carrier through
  `pending_auto_curry`; (iii) **fn-value mono rewrite** (`mono_collect.rs:79-88`) — sidecar
  insert at the Var rename (else the 0585 guard hard-fails post-W2). Cascade: `into_concrete`,
  `src/repl.rs::impl_entry` fixture, types baseline regen. One unit pin per leg;
  behaviour-invariant (13-RED baseline holds). → `/review`.
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
- **W-RD — R16/R17 error quality + the 0585 die-leg typecheck close** (`/arch` ratifies 0611
  carrier shape → `/dev` coordinated typecheck + int). Dispatch-outcome signal → §3.11 clean
  message; RD-3 false-positive fence. **COUPLED IN (W2 finding):** the 0585 die legs
  (VP-3/4/5) need typecheck's §3.11 finalization gate (`find_ambiguous_value_position`) to fire
  for a **top-level polymorphic value** (currently skipped) so `(if c gcount gother)` dies
  check-side with the `"ambiguous"` §3.11 message — the backend backstop landed W2 is the
  loud fallback, but the neg tests assert the check-side message. Same `finalize.rs` §3.11
  gate as R16/R17 → land together. → `/review`.
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
| W0 | /dev | 0583 producer (types+typecheck+backend) | (shim §II.3) | (shim) | — `41fab350`: carriers+`from_expr`+F1 producer+cache 18→19+R-2 typecheck half+lenient relocation; baseline holds 13 REDs; W0.b totalization DEFERRED |
| W0 rev | /review | W0 producer change-set | (shim §II.3) | (shim) | — `7c943300`: **2 Blockers** — B1/0616 producer misses Apply/self-rec/dotted legs; B2/0617 W0.b flip must precede W1 |
| W0.1 | /dev | producer top-up (0616, typecheck) | (shim §II.3) | (shim) | — `635f364b`: 3 legs captured at resolving seams + triple-probe consolidated (Resolve-once); baseline holds; flagged cross-module trait-method module gap → /arch |
| W0.1 rule | /arch | cross-module storage-module ruling | (shim §II.3) | (shim) | — `b48902ab`: trait bodies live in impl-WRITER's module (D45 amended); `impl_module` carrier; completeness sweep found +2 gaps (AutoCurry, fn-value rewrite); W1 blocked until W0.1b |
| W0.1b | /dev | cross-module storage fix (types+tc+int) | (shim §II.3) | (shim) | — `144828d1`: `TraitImpl.impl_module` + `ResolvedCall::TraitMethod.impl_module` (schema-19 window) + AutoCurry transport + mono-rewrite sidecar; baseline holds; 6 producer pins |
| prod rev | /review | producer W0.1+W0.1b | (shim §II.3) | (shim) | — `8a72d320`: **GO, 0 Blockers** — storage-module correct all cross-module shapes; deviation sound; consolidation clean. Findings 0618 (/arch doc) + 0619 (/dev; item 1 Important) |
| W0.2 | /testing | KC-W0-2 golden-CLIF gate | (shim §II.3) | (shim) | — `f5d0197f`: 5 goldens byte-verbatim (class-06 backend-unit-only); KC-W0-6 reds-first; gate for W0.b |
| W0.b | /dev | totalization flip (typecheck+backend) | (shim §II.3) | (shim) | — `7e8972c3`: typecheck sole mono-view producer + backend hard-error arm; **golden 5/5 byte-identical**; KC-W0-6 helper + 0619 items 1/3/4; ownership-universe pin (→/arch note); baseline holds. **W0 FRONT CLOSED** |
| W1 | /dev | backend call seam (S1–S9) | (shim §II.3) | (shim) | — **BLOCKED, not landed** (`c1098c3c` note+FIXME only): golden byte-identical but member-aliased carrier records alias not canonical key → FIXME 0620 (/arch); W1 backend STASHED |
| W1 rule | /arch | 0620 member-alias carrier + producer re-sweep | (shim §II.3) | (shim) | — `dd759afc`: **class CLOSED** — walk surfaces `Resolved.storage_key`/`storage_fq()` (uniform, cures renamed-imports too); 19-row recorder-grounded table + carrier value-source rule (/review-enforced); types half landed |
| W1 rd | /dev | W1 re-deploy (recorder flip + backend) | (shim §II.3) | (shim) | — `86038e27`: `storage_fq()` recorder flip + stash pop + S3/S4 ctor keyed + 24 fixtures; golden 5/5; **13-RED baseline restored, W1 LANDED**, zero regressions |
| W2 | /dev | value seam + 0585 backstop + vec-assoc (S10–S18) | (shim §II.3) | (shim) | — `369c226c`: value seam resolver-free; **vec-assoc UAF root-caused+fixed+behaviorally-verified** (VA-1/2 GREEN, VA-3 pin, VA-4 fence); 0585 backend backstop landed. Baseline **13→11**. **VP-3/4/5 owe a typecheck §3.11.1 leg** (couples R16/R17) |
| W2 rev | /review | W2 change-set | (shim §II.3) | (shim) | — `143d6fb4`: **CLEAN for W3**; but vec-assoc fix is NARROW — sibling UAFs live (let/match COW-return), root = ownership `transfer.rs:590` Fresh-default for summary-less COW → typecheck class-fix owed (route /arch) |
| W3 | /dev | delete resolver + grep gate | (shim §II.3) | (shim) | — **BLOCKED** (`f6f88152` note+FIXME): staged deletion green in isolation but cross-module mono `pattern_ctors` hard-miss → FIXME 0622 (/arch); W3 backend STASHED |
| W3 rule | /arch | 0622 + exhaustive producer sweep | (shim §II.3) | (shim) | — `4d7aee66`: **4th axis found+closed** = MAP-INSTANCE (read enclosing vs per-instance map); §1.1.3 3×9 matrix; fix = "read the right map" (3 edits); +1 sibling (test-fn roots). **Producer space CLOSED** |
| W3 rd | /dev | W3 re-deploy (0622 fix + deletion) | (shim §II.3) | (shim) | — `4c899dd9`+`be06f6cb`: read-the-right-map + stash pop; **grep-zero (−993 LOC), golden 5/5, 11-RED restored**. **0583 BACKEND HALF COMPLETE** |

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
