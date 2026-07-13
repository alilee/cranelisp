# cranelisp-typecheck — whole-context assessment (Sprint 108)

> **What this is.** The S108 rotation assessment of the `cranelisp-typecheck`
> bounded context, authored by `/audit` per `.claude/commands/audit.md` (the
> acid test + quality attributes, including the Duplication attribute as
> extended this sprint per FIXME 0564 — mirror / divergent / entry-point /
> spec-surface). Rotation trigger: escalation trigger 6 — the prelude ≡
> explicit-import resolution convergence (`design/arch/prelude-import-convergence.md`)
> is a major arc that completed in this context at S108 Inc3.
>
> **Prior assessment**: `audits/cranelisp-typecheck-s87.md` (authored by
> `/review` under the pre-acceptance-gate regime; its findings carried **no
> disposition trail** — reconciled in §2.8 below). Read-only on the context;
> every finding carries file:line evidence.

---

## 1. Verdict

| Attribute | Grade | One-line basis |
|---|---|---|
| Design quality (fitness) | **strong** | The post-convergence resolution layer (`ResolutionScope` fallback-intrinsic + one §8.6.4 seam) IS the second-time design; Principle-17 module-locality holds; traits/ and ownership/ subsystems are deliberately shaped. |
| Design realisation | **weak** | Not code-vs-arch (the convergence landed faithfully, `/review` CLEAR) but the crate's own `design/typecheck/` tree: `traits.md` describes a **deleted** data model (`TraitRegistry`/`ImplRegistry`), and the master doc `typecheck.md` cites the retired facade as its contract. |
| Simplicity & volume | code **adequate** / docs **weak** / tests **strong** | `traits/` decomposition landed (S87 rec actioned); `program.rs` (3,962 lines) is the remaining growth magnet; `design/typecheck/` is 23 files, roughly half sprint-/ring-era. |
| Duplication (extended lens) | **strong** | The divergent `_or_prelude` family is gone (grep = 0), the definition entry points are one seam, the class is structurally closed on the check path (§2.4 verdicts each residual site). |
| Risk-weighted coverage | **strong** | The convergence is pinned by a production-path variant × polarity matrix (R1–R8 green, S1–S21, twin fixtures), all e2e through the real binary; one known RED carry (dotted-ctor, S109) traces correctly. |
| Maintainability | **adequate** | New seam code is exemplary; stratified doc-comments (stale S78 mechanism descriptions, "outer scope" wording) and one misleading retained name are first-sprint residue. |
| Memory freshness | **strong** | `crates/cranelisp-typecheck/CLAUDE.md` was rewritten this sprint and every claim I checked matches the code; one two-word wording slip against its own framing rule. |

**The acid-test answer.** For the resolution and definition layer — the part
of this context that carried the S108 arc — the answer is now **yes**: the
second-time solution *is what was just built*. A rewrite with today's insight
would produce exactly `ResolutionScope` with the fallback decided once at
scope construction and no fallback-less public entry point
(`crates/cranelisp-types/src/resolve.rs:91–151`, private walk at :422), one
`reject_def_over_binding` seam that every definition form routes through
(`program.rs:911/932–937/954`; int `form_dispatch.rs:244`), and the variant ×
polarity matrix as its acceptance harness. That is a rare, verifiable pass.

For the context as a whole the answer is **mostly, with named excess**: the
rewrite would keep the crate's shape (per-variant `infer_expr` dispatch, the
five-module `traits/` split, `ownership/` as a staged subsystem, sibling
`*/tests.rs` test organisation, the `with_scope` single-sourced glue) — but it
would **not** reproduce the 23-file `design/typecheck/` tree with a falsified
`traits.md` at its centre, the stratified S78-era doc-comments that describe a
retry mechanism that no longer exists, a 3,962-line `program.rs` with several
150–290-line phase drivers, or the three S87 findings still standing
undispositioned two audit generations later. Those are precisely the deltas
this assessment recommends closing.

---

## 2. Current state

### 2.1 Design quality (fitness) — strong

- **The convergence is the design the context should always have had, and it
  is now in place.** One semantic reference operation:
  `ResolutionScope::resolve` with the prelude fallback intrinsic at
  construction (`cranelisp-types/src/resolve.rs:91–151`); one definition
  seam: `reject_def_over_binding` (`resolve.rs:200`), consumed by typecheck
  via a 3-line adapter (`checker.rs:1021–1031`) and by int without a
  typecheck dependency (`src/process_form/form_dispatch.rs:244`). The
  forgettable per-call fallback decision is unrepresentable (Principles
  18/20) — this is design fitness earned from implementation history (the
  E3/E8/0558/E9 + S8/S14/S15/S16 recurrence register), exactly what the
  attribute asks for.
- **Module-locality (Principle 17) holds.** The S87 verdict (production
  scan-free, single-key access) re-checks clean in the seam code read for
  this assessment; the one bulk scan is the enumerated
  `find_trait_method_decl` reader (§2.4).
- **Subsystem shape is deliberate.** `traits/` is five purpose-named modules
  (`registry`/`dispatch`/`impl_check`/`monomorphise`/`type_resolve`, largest
  1,107 lines) — the S87-2 recommendation actioned
  (`design/typecheck/s87-traits-decomposition.md`); `ownership/` is the
  staged S100–102 analysis (classify/confinement/fixpoint/transfer/uniqueness/
  publish, 615-line max file) matching `design/typecheck/ownership-inference.md`'s
  increment plan.
- **One fitness watch-item**, not a finding: `program.rs` remains the
  single-file home of registration + body-check + finalize + mono-collection
  (§2.3). The second-time solution would give it the `traits/` treatment.

### 2.2 Design realisation — weak

The arc itself realised its design faithfully — `/review` verified the §7
structural criterion CLEAR, and my independent re-grep confirms it (§2.4). The
weak grade is the crate's own design tree, in the doc→code direction:

- **`design/typecheck/traits.md` is falsified at its foundation.** Its §1
  presents the trait system as three registries on a `TypeChecker` struct —
  `trait_registry: TraitRegistry` with `decls: HashMap<TraitName, TraitDecl>`,
  an `ImplRegistry`, `active_constraints` (traits.md:11–32), with the
  duplicate check specified as "Error if `trait_registry.decls` already
  contains the trait name" (traits.md:76). The code says the opposite, in its
  own words: *"The old `TraitRegistry` and `ImplRegistry` global caches have
  been eliminated"* (`traits/mod.rs:9`, `checker.rs:18`) — trait decls are
  symbol-table-resident `ModuleEntry::TraitDecl` entries, impls are
  `ModuleEntry::TraitImpl` written to the trait's defining module (Decision
  45), and the duplicate check is the raw same-module idempotency probe
  (`registry.rs:85–116`) downstream of the §8.6.4 seam. The doc also
  addresses "Ring 3 implementers" (traits.md:5) — the ring axis was retired
  S64. This was flagged by `/review` this increment (SPRINT.md Inc3, "Imp2
  design/typecheck/traits.md stale (/design tc)") and is confirmed here as
  structural, not cosmetic: an agent trusting §1 would design against a
  deleted architecture. → Recommendation 1.
- **The master doc's contract list has a dead reference.** `typecheck.md`
  names as its contract #2 `design/arch/facades/typecheck.md` (typecheck.md:8)
  — that facade was retired at S72 Wave 5 (all nine facades retired;
  `design/arch/CLAUDE.md` facades row); the canonical surface is source
  rustdoc + BC §2. The single source of design intent mis-cites its own
  contract. → folds into Recommendation 1.
- **Realisation in the code→doc direction is otherwise current where it
  matters**: `monomorphisation.md` §3.7 carries the cross-module scoping
  rationale the CLAUDE.md cites; `ownership-inference.md` matches the landed
  carrier state; the convergence ruling's §3.2 "landed as" annotation
  correctly records the `scope_resolve`/`scope_resolve_in` deviation from the
  designed `scope_for` shape.

### 2.3 Simplicity & volume optimality

**Code — adequate.** 13,074 lines in top-level modules + `traits/` 6,303 −
test-support (`builtins.rs` 2,431 is `TestFixture` world-building, confirmed
S87 and still true — `builtins.rs:196–197` constructs test envs). What the
rewrite would not reproduce:

- `program.rs` at 3,962 lines with phase drivers over the ~100-line
  convention: `finalize_check_result_inner` **188 effective lines**
  (program.rs:2016–2383; S87 measured ~150 — it has *grown* ~25% since,
  absorbing the S101 callees harvest and ownership publish),
  `check_form_body_single_defn` ~287 raw (program.rs:1078–), `pass4_monomorphise`
  ~260 raw. The `traits/` split is the in-context precedent for the cure.
  → Recommendation 4.
- Two S87 dead-path items survive unchanged: the `parsed_to_top_level`
  `_ => None` silent-drop catch-all (`form.rs:512`) and the
  `#[allow(dead_code)]` `lookup_constructor_type` helper that hard-roots at
  `ModuleFullPath::from("user")` (`checker.rs:667–671`) — the
  attractive-nuisance Principle-17/19 violation S87-4 named. → Recommendation 5.

**Docs — weak.** `design/typecheck/` holds 23 markdown files; at least 14
carry Ring-2/Ring-3/sketch-era framing (grep hit list includes `traits.md`,
`inference.md`, `typecheck.md`, `hkt.md`, `adt.md`), and several are
sprint-scoped working documents (`sprint50-fixes.md`, `phase-b-plan.md`,
`implementation-slice-s66.md`, `wave-3a-check-form.md`,
`s76-resolution-and-enablement.md`, `step4-macro-deps.md`,
`fixme-0365-field-accessor-dotted.md`) that the directory's own convention
("one file per major subsystem", `design/typecheck/CLAUDE.md`) does not
sanction as durable references. Over-documentation is decay-in-waiting — the
falsified `traits.md` (§2.2) is what this class matures into. → Recommendation 1
(triage rides the traits.md rewrite).

**Tests — strong.** 661 in-crate unit tests green (S108 gate), sibling
`*/tests.rs` organisation per METHOD §2.2, `resolve/tests.rs` +
`checker/tests.rs` + `program/tests.rs` attributable per submodule; the
types-side seam carries 28 dedicated resolve unit tests (S108 CS1). No excess
found; the fixture world (`builtins.rs`) is large but is the price of the
no-`cranelisp-primitives`-dep isolation, which the rewrite would keep.

### 2.4 Duplication — strong (extended lens: mirror / divergent / entry-point / spec-surface)

This is the arc's home attribute, assessed with the FIXME-0564-extended lens
the convergence itself exemplifies.

**Divergent duplication — ELIMINATED.** The census of 12 same-purpose
resolver variants (`prelude-import-convergence.md` §2) is gone: my independent
`grep -rn "_or_prelude" crates/ src/` returns **zero** hits; the free
`resolve`/`resolve_with_fallback` are private internals
(`cranelisp-types/src/resolve.rs:422` — "**Private (S108 Wave-G)** … the sole
public resolution entry point" is the scope method); `prelude_fallback`
consultation in this crate reduces to exactly the enumerated set — the
threading (`checker.rs:312/462/496`, `form.rs:98–163`), the single bit-consult
helper `prelude_fallback_target` (`checker.rs:877–888`) read at the scope
constructors, the enumerated bulk reader (`dispatch.rs:394`), and test
support. The drifting-sibling family this facet names is not merely
consolidated; its recurrence mechanism (per-variant fallback) is
unrepresentable.

**Entry-point duplication — CLOSED at the definition seam.** Every
typecheck-side definition form hits `reject_def_over_binding` at the one
visible place: `deftype` (program.rs:911), `deftrait` name + each method name
(program.rs:932–937, placed at the arm so plain AND HKT registration branches
share one call site), `defn`/`defn-` (program.rs:954); `defmacro` reaches the
identical types-owned seam from int (form_dispatch.rs:244). The variant ×
polarity matrix (`tests/plan/PLAN.md:1753–1859`) is the standing lever that
keeps it one codepath.

**Is the class TRULY closed on the check path?** **Yes, structurally** — a
fallback-less resolver is unrepresentable (no public fallback-less entry
point exists in `cranelisp-types`; a scope with `prelude: None` is an
explicit, reviewable construction decision), and the only raw current-module
probes are named as probes answering same-module identity
(`probe_module_entry_owned`; `registry.rs:85–92` documents its §8.6.4
relationship precisely). Verdicts on each named residual site:

- **`find_trait_method_decl`** (`dispatch.rs:382–396`) — **legitimate, not a
  residual variant.** It is a table *enumeration* (method-name → declaring
  `TraitDecl`), unanswerable by `resolve` (which walks name → entry); it is
  enumerated in the ruling's §3.4 non-resolution-reader set, and its prelude
  hop carries its own I-1 `public_only` head filter (dispatch.rs:394–395,
  423, 429). Watch-item only: it is a *second* implementation of
  "consult-prelude-with-I-1-filter" — if a second bulk reader ever appears,
  extraction is due (the S87-5 logic, now at n=1).
- **Scope-construction glue** — **closed.** The `/review`-flagged
  triplication was single-sourced into `with_scope` (`checker.rs:901–917`),
  which all three seams (`scope_resolve`, `scope_resolve_in`, the
  `reject_def_over_binding` adapter) route through; verified in source, and
  the helper's rustdoc cites the 0564/0565 divergent-duplication category
  applied to the crate's own new code — the lens is self-installing.
- **Dotted-ctor `resolve_dotted_field_accessor`** (`checker.rs:1404–1442`) —
  **not a fallback-class residual.** Its head resolution routes through
  `scope_resolve` (checker.rs:1424–1426, fallback-aware); the carried defect
  (committed RED `spec_08_modules::dotted_constructor_in_value_position_resolves`,
  /qa-attributed) is an *enumeration miss in the registration model* —
  accessors get canonical `Type.field` keys (adt.rs inverted model §1.6.1),
  constructors are never `Type.Ctor`-keyed — uniform across provenances, so
  prelude parity holds. It is a live defect with its guard, handled by the
  defect protocol, not a recommendation. It does, however, feed the
  spec-surface facet ↓.
- **Residual divergence WITHIN the one codepath**: FIXME 0567 (resolve's I-1
  filter tests the chain-followed terminal, not the prelude head —
  `cranelisp-types/src/resolve.rs:523–531`) is tracked to `/arch`, unreachable
  through the stock prelude; the display-tier hand-rolled lookup is
  int-territory, ruled a settled deviation (§3.5.1) with its I-1 half fixed
  this sprint. Neither reopens the class in this context.

**Mirror duplication — clean.** The one live mirror `/review` found this arc
(`eval.rs:566` display hop) was int-side and was collapsed (S108 Inc3 close);
in-crate, the S87 "mirror comments are intentional symmetry" verdict stands,
and `find_trait_method_decl_in_module`'s two enumeration arms
(dispatch.rs:419–434) are a justified staging-aware/foreign-module split, not
a copy.

**Spec-surface redundancy (new facet) — one candidate, routed to the user.**
Spec §8.5.2 gives constructors **three** reference forms: bare `Ctor` (when in
scope), qualified `module/Ctor`, and dotted `Type.Ctor`. The dotted CTOR form
is the one that has never worked (the S109 carry above), and `/qa` sized its
implementation as not-small (adt.rs registration model + resolver arm +
codegen-key ripple). The redundancy question is prior to the fix: `Type.Ctor`
duplicates what `Ctor`-in-scope and `module/Ctor` already express (unlike
`Type.field` accessors, which have no alternative form and stay). Candidate
simplification → Recommendation 3.

### 2.5 Risk-weighted coverage — strong

Top technical risks derived from invariants + defect history, each verdicted:

- **Risk: a resolution/definition site silently lacking prelude parity** (the
  E3/E8/0558/E9/S8/S14–S16 class — this context's dominant historical defect
  class). **Pinned, production-path.** The S1–S21 site enumeration + R1–R8
  RED-to-GREEN matrix (`tests/plan/PLAN.md:1753–1859`) runs e2e through the
  real binary (`spec_08_name_shadowing.rs`, `spec_07_traits.rs`,
  `spec_08_prelude_outer_scope.rs`), twin-fixture shape, both polarities,
  mode parity pinned (R3). All R-rows verified GREEN post-landing and stand
  as regression pins (`[Tested+Neg]`). This is the strongest coverage posture
  any context has shown at audit.
- **Risk: the §8.6.4 seam regressing per-form** (a new definition form
  bypassing it). **Pinned** for all current forms (R2–R8 negatives per form);
  structurally guarded by the one-visible-arm placement (program.rs
  `check_form_register`); the standing `/qa` "coverage by definition
  variants" category owns the forward sweep as forms are added.
- **Risk: cross-module monomorphisation scoping** (the three load-bearing
  facts, CLAUDE.md §"Cross-module monomorphisation"). **Pinned** at unit tier
  (`program::tests::cross_module_imported_constrained_fn_monomorphises_in_defining_scope`)
  with the design rationale current (`monomorphisation.md` §3.7).
- **Risk: `callees` edge starvation** (silently dropping edges starves the
  S101 transaction reverse index — CLAUDE.md §"Def.callees"). **Pinned**
  (`program::tests::callees_*`; the 0472 all-seams `harvest_callee_edges`
  contract documented at the seam).
- **Known RED carry**: the dotted-ctor guard (S109, `// defect:` traced,
  PLAN §VI row) — the failing-not-ignored discipline working as designed.
- **Residual un-pinned corner**: FIXME 0567's terminal-vs-head filter
  divergence has no failing unit pin yet (the FIXME itself specifies
  "failing unit pin first" when `/arch` actions it) — tracked, types-side,
  acceptable.

### 2.6 Maintainability — adequate

The new seam code sets the crate's high-water mark (the `with_scope` rustdoc,
the `registry.rs:85–103` idempotency-vs-name-freedom comment, the
`is_internal_constructor` `Bind` gotcha). The debt is **stratified
doc-comments** left by the arc:

- `scope_resolve` carries TWO doc blocks: the stale S78 block
  (checker.rs:919–954) describing the retired caller-side retry — including
  the now-false "The two-hop is realized caller-side … NOT inside
  `cranelisp_types::resolve`" (checker.rs:951–953) and a reference to the
  retired resolver family — concatenated with the correct post-Wave-G block
  (checker.rs:955–967). An agent reading top-down learns the dead mechanism
  first. (Known: SPRINT.md Inc3 tracks "scope_resolve stale doc-comment" as a
  micro-task — but the sweep is wider than that one comment ↓.)
- "Outer scope" as a scoping-level concept persists in rustdoc against the
  ruling's explicit wording rule (`prelude-import-convergence.md` §1: say
  "the prelude fallback", never "the outer scope"): `prelude_fallback_target`
  (checker.rs:863–866), `scope_resolve` (:919–922), `resolve_constructor_entry`
  (:1580–1581), `resolve_terminal_entry_scoped` (:1608–1611, still citing "S78
  §2.7.5 — Chokepoint 1"), and five sites in `dispatch.rs` (:362–405).
- **One misleading retained name**: `resolve_entry_in_current_module`
  (checker.rs:1571–1574) — the §3.3 collapse map marked it *deleted*; it was
  instead retained as a 1-line projection over `scope_resolve` (a reasonable
  deviation) — but the name affirmatively asserts current-module-only while
  the behaviour is fallback-aware, and its own doc (:1566–1570) never mentions
  the prelude. This is the anti-family hazard inverted: the retired
  `_or_prelude` names over-advertised the fallback; this one denies it. Its
  siblings already model the fix (`resolve_terminal_entry_scoped`,
  `resolve_terminal_fq_scoped` — the `_scoped` family). A future agent
  needing "this but with the prelude" re-fragments the chokepoint.
  → Recommendation 2.

### 2.7 Memory freshness — strong

`crates/cranelisp-typecheck/CLAUDE.md` was substantially rewritten by the arc
(§"Bare-name resolution & the prelude fallback") and every load-bearing claim
I checked verifies against source: the two-semantic-operations model, the
`with_scope`/`scope_resolve` seam locations, the idempotency-probe carve-out
(matches registry.rs:85–116), the `Bind` visibility gotcha, the `/`-split
guard, the `find_trait_method_decl` enumeration-reader carve-out, the
`callees` contract, the mono scoping facts. The stale :169 reference and the
spec-inverted rule of thumb named by the ruling's §4.3 are confirmed gone. No
dead references, no stale counts, no changelog accretion. One two-word slip:
the Testing section still says "to exercise the **outer-scope** fallback"
(CLAUDE.md:262), contradicting the file's own §"Bare-name resolution" framing
rule — fold into the Recommendation 2 sweep.

### 2.8 Prior-assessment reconciliation (S87 → S108)

The S87 assessment predates the acceptance gate, so its findings carry no
disposition trail. Honest reconstruction:

| S87 finding | S108 status |
|---|---|
| S87-1 half-FQ "no impl" diagnostics (IMPORTANT) | **STILL OPEN** — `dispatch.rs:64–70` renders both halves bare; `monomorphise.rs:670–676` renders `fq_trait` FQ but `impl_type` bare (from `concrete_type_name`, deliberately bare for mangling). Two same-named ADTs still yield an undisambiguable diagnostic. |
| S87-2 over-budget phase drivers (IMPORTANT) | **RESOLVED in traits/** (`monomorphise_call` now ~145 lines with seven extracted phase helpers, monomorphise.rs:83–228; the five-module split per `s87-traits-decomposition.md`); **REGRESSED in program.rs** (`finalize_check_result_inner` 188 effective, grew from ~150). |
| S87-3 `parsed_to_top_level` `_ => None` silent drop (SUGGESTION) | **STILL OPEN** — form.rs:512 unchanged, third audit generation. |
| S87-4 `lookup_constructor_type` `"user"` default (SUGGESTION) | **STILL OPEN** — checker.rs:667–671 unchanged, dead-code-gated. |
| S87-5 prelude filter-discipline extraction (SUGGESTION) | **RESOLVED structurally** — superseded by the convergence (the I-1 filter is intrinsic to `ResolutionScope::resolve`; the one remaining hand-rolled hop is the enumerated bulk reader). |

Two SUGGESTIONs and one IMPORTANT surviving two generations without a recorded
accept/decline is itself a finding about the pre-gate era; they are re-raised
once, consolidated, as Recommendation 5 — if declined at Phase 1, the trail
this time will say so.

---

## 3. Recommendations

Proposals only — disposed at next sprint's Phase 1; no FIXMEs filed by
`/audit`. The dotted-ctor defect is NOT here (live defect, committed guard,
S109 carry already scheduled).

**R-1. Rewrite `design/typecheck/traits.md` against the as-built model, and
triage the design-doc sprawl in the same pass.** *(design feedback)*
- Evidence: §2.2 — traits.md:11–32/76 vs `traits/mod.rs:9`, `checker.rs:18`,
  `registry.rs:85–116`; typecheck.md:8 dead facade citation; 23-file tree
  with ≥7 sprint-scoped working docs against the directory's own one-file-
  per-subsystem convention.
- Cost: **medium**. Owner: **/design** (typecheck) — aligns with the already-
  carried `/review` Imp2 item.
- Done: traits.md describes the symbol-table-resident model
  (`ModuleEntry::TraitDecl`/`TraitImpl`, Decision 45 chain-follow, the §8.6.4
  seam + idempotency probe, the five-module `traits/` layout) with no
  `TraitRegistry`/`ImplRegistry`/Ring framing; typecheck.md's contract list
  cites BC §2 + source rustdoc (not the retired facade); each sprint-scoped
  doc is either folded into a subsystem doc, or moved under an explicit
  historical marker. Cures the risk (an agent designing against a deleted
  architecture), not just the stale text.

**R-2. One post-convergence doc-and-naming sweep of the resolution seams.**
- Evidence: §2.6/§2.7 — the stale S78 doc block (checker.rs:919–954, false
  "two-hop is realized caller-side" claim), "outer scope" rustdoc at
  checker.rs:863/921/1580/1609 and dispatch.rs:362–405, CLAUDE.md:262; the
  misleading `resolve_entry_in_current_module` name (checker.rs:1571) vs its
  `_scoped` siblings. Subsumes and widens the already-tracked
  "scope_resolve stale doc-comment" micro-task (SPRINT.md Inc3).
- Cost: **small** (mechanical; no assertion or behaviour change). Owner:
  **/dev** (typecheck).
- Done: no rustdoc in the crate describes the caller-side retry; `grep -in
  "outer scope" crates/cranelisp-typecheck/` yields zero conceptual uses
  (historical citations may remain if past-tensed);
  `resolve_entry_in_current_module` renamed into the `_scoped` family (e.g.
  `resolve_entry_scoped`) with a doc naming the intrinsic fallback. Cures the
  recurrence vector (`/review` already classed misleading resolution rustdoc
  as one — its S1 finding this sprint), not just the wording.

**R-3. Spec-surface simplification candidate: drop dotted `Type.Ctor`
constructor references (spec §8.5.2), keeping `Type.field` accessors.**
*(spec-surface redundancy — USER decision; → `/spec` only if accepted)*
- Evidence: §2.4 — constructors have three reference forms; the dotted form
  has never worked (committed RED, S109 carry), and `/qa` sized the
  implementation as not-small (adt.rs registration model + resolver arm +
  codegen-key ripple), while `Ctor`-in-scope + `module/Ctor` already express
  everything it would. Field accessors are NOT redundant (no alternative
  form) and are unaffected.
- Cost: **small** if accepted (spec §8.5.2 edit + retire the RED as
  spec-conformant-rejection pin) vs the **medium** S109 implementation if
  declined. Owner: **user → /spec** (accepted) or the existing **/dev S109
  carry** (declined).
- Done (accepted path): §8.5.2 no longer grants ctor dotted references; the
  committed test re-baselines to assert the (now-conformant) rejection;
  the S109 carry is cancelled. Either disposition closes the current
  spec-says-X/compiler-does-Y gap — that is the risk being cured.

**R-4. Give `program.rs` the `traits/` treatment.**
- Evidence: §2.3 — 3,962 lines; `finalize_check_result_inner` 188 effective
  and growing (2016–2383), `check_form_body_single_defn` ~287 raw,
  `pass4_monomorphise` ~260 raw; the in-context precedent
  (`s87-traits-decomposition.md`) demonstrably improved traits/.
- Cost: **medium** (mechanical split + test relocation; behaviour-identical).
  Owner: **/dev** (typecheck), design sign-off by **/design** on the module
  cut (register / body / finalize / mono-collect is the natural seam set).
- Done: no `program.rs` submodule exceeds ~1,200 lines; the phase drivers
  are named sub-functions within budget; `program/tests.rs` splits alongside
  per METHOD §2.2 attributability.

**R-5. Disposition the S87 residue batch (three small in-crate items).**
- Evidence: §2.8 — S87-1 half-FQ diagnostics (dispatch.rs:64–70,
  monomorphise.rs:670–676; user-facing disambiguation failure); S87-3
  `_ => None` silent drop (form.rs:512; frontend-contract break would vanish
  rather than fail loudly); S87-4 `"user"`-defaulting dead helper
  (checker.rs:667–671; Principle-17/19 attractive nuisance).
- Cost: **small** (all three together are one change-set: a
  `fq_type_name_for_diagnostics` render at the two error sites + an
  `unreachable!` with invariant message + helper deletion/de-defaulting).
  Owner: **/dev** (typecheck); the S87-1 fix wants a `/testing` twin repro
  (two same-named ADTs, assert the FQ name in the diagnostic).
- Done: the "no impl" message renders both halves FQ under two same-named
  ADTs; a new `ParsedEntry` variant fails compilation or loudly at
  `parsed_to_top_level`; no production-reachable helper roots at `"user"`.
  If any item is instead **declined**, the trail records it and the next
  audit stops re-raising it — either outcome cures the two-generation
  no-disposition drift.

---

## 4. Disposition trail

*(Appended at S109 Phase 1 by `/sprint` + the user; not by `/audit`.)*

**S109 Phase 1 (2026-07-13) — disposed with user:**

- **R-1 ACCEPTED** → FIXME 0578 (`/design` typecheck). traits.md rewrite +
  doc-sprawl triage.
- **R-2 ACCEPTED** → FIXME 0579 (`/dev` typecheck). Resolution-seam doc/naming
  sweep. Note: the rustdoc must adopt the settled §8.8.1 model — prelude is an
  **implicit import / one transparent-fallback lookup, NOT an "outer scope"** — so
  the sweep is also a model correction, not only wording.
- **R-3 DECLINED.** The proposal was to drop dotted `Type.Ctor` constructor
  references from spec §8.5.2 as redundant. The user instead chose the
  **full-capability fix** (S109 scope bucket 2): same-named constructors across
  in-scope types are a first-class pattern (option/result-likes with `Some`/`Ok`,
  distinct types sharing `Address`/`Node`), and the dotted form is their
  type-namespacing mechanism — the assessment undersold it as "redundant." Two
  decisive facts overrode the redundancy read: (a) the language **already displays**
  a constructor value as `Color.Red` (the canonical dotted form) but rejects that
  same text as *input* — an input/output asymmetry, not a missing convenience; and
  (b) field accessors already coexist + disambiguate via the dotted form
  (§8.5.2 modules.md:743, tested), so constructors being RED is an inconsistency,
  not a surplus. `module/Ctor` cannot disambiguate two same-named constructors in
  the **same** module, leaving the dotted form the only path. S109 therefore
  IMPLEMENTS the form (define+import same-named ctors, `/dev` typecheck +
  `/spec` §8.5.2 clarification) rather than dropping it; the committed RED
  (`dotted_constructor_in_value_position_resolves`) is the record + trigger. The
  next audit should stop re-raising R-3.
- **R-4 ACCEPTED** → FIXME 0580 (`/dev` typecheck + `/design` sign-off).
  `program.rs` module split.
- **R-5 ACCEPTED** → FIXME 0581 (`/dev` typecheck). S87 residue batch; the S87-1
  half-FQ-diagnostic twin repro coordinates with the dotted-ctor same-named-ADT
  work.
