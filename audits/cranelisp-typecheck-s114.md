# cranelisp-typecheck — whole-context assessment (Sprint 114)

> **What this is.** The S114 rotation assessment of the `cranelisp-typecheck`
> bounded context, authored by `/audit` per `.claude/commands/audit.md` (acid
> test + quality attributes; duplication assessed with the extended
> mirror/divergent/entry-point/spec-surface lens). Rotation trigger: FIRMED at
> Phase 4 — this sprint's heaviest surgery (the typed `VarRef`/`ApplyRef`
> carrier flip, the settlement drain, MS-P7, F-D2-11) landed here; last
> assessed S108.
>
> **Prior assessment**: `audits/cranelisp-typecheck-s108.md`. Its five
> recommendations were all disposed at S109 Phase 1 with a full trail (§2.8
> below reconciles their fates). Read-only on the context; every finding
> carries file:line or commit evidence, independently verified.
>
> **Known S115 carries NOT re-derived here** (attributed in
> `sprints/SPRINT.md` + `tests/plan/s114-test-plan.md` §11/§11.1): the chained
> `MayAliasOf` faces (×2 pins), the GOT-slot carrier-loss pair (0705 + the
> fn-as-value pin), the entry-return `Pure` leak (backend), the 0694 nullary
> flap condition, and the §11.8.10 harvest-window three-invocation contract.
> One exception is forced: the "0590 resolver mirrors + `_hkt` arms" carry is
> re-examined in §2.2/§2.9 because this audit found its premise **falsified by
> source** — that is new information, not a re-derivation.

---

## 1. Verdict

| Attribute | Grade | One-line basis |
|---|---|---|
| Design quality (fitness) | **strong** | The carrier flip IS the second-time design: closed sums make "unresolved" unrepresentable, totality holds at one Var chokepoint + a monotone Apply lattice, the `Unresolved`/`NotConcrete` split is load-bearing and correctly placed; the settlement/P26 discipline is now structural, not procedural. |
| Design realisation | **weak** | Not code-vs-design for the arc (the flip landed faithfully; sweeps verified) but the crate's RECORD layer: the master doc `typecheck.md` §§2–5 describe a file tree two generations gone and a retired facade as "normative"; FIXME 0590 is a **zombie** — resolved S110, falsely re-dispositioned S113, driving phantom S114/S115 work; the designed `program/tests.rs` split was silently not executed. |
| Simplicity & volume | code **adequate** / docs **weak** / tests **adequate** | ~20.7k production LOC, shape deliberate; `finalize.rs` 1,517 lines vs its own ~820 design estimate and ~1,200 ceiling; `checker.rs` (3,180) is the new growth magnet. Docs: 28 files with a falsified master core. Tests: rich and pinning, but `program/tests.rs` is a 10,576-line monolith its own design ordered split. |
| Duplication (extended lens) | **strong** | Independently re-verified: zero active `resolved_targets` reads; ONE shadow discriminator (`resolves_to_carrier_identity` ×5 + `callee_has_keyed_carrier` ×5 + the post-scope carrier read); ONE child-enumeration walker; ONE bulk prelude reader (still n=1); the four `TypeExpr` mirrors are ACTUALLY converged (better than the records claim). |
| Risk-weighted coverage | **strong** | Carrier totality pinned at unit tier at the exact seams (`mono_expr/tests.rs` Unresolved arms, `scope/tests.rs` provenance ×8) + e2e CA-1..CA-5 through the real binary; suite certified 5148/5143/5 stable REDs, every RED attributed with owner + class; the flap is NAMED per the standing convention, never folded into a scalar. |
| Maintainability | **adequate** | New seam rustdoc is the crate's best yet (the carrier-flip annotations, the `callee_has_keyed_carrier` contract, the deferred-dispatch discriminator comment); the debt is record-side (below), plus ~10 `#[allow(dead_code)]` accessor-pair retentions in `checker.rs` and the test-only `has_impl_with_state` still reading as live in prose. |
| Memory freshness | **weak** | `crates/cranelisp-typecheck/CLAUDE.md` carries four falsified/dead claims, including an "STILL OPEN" verdict on a FIXME resolved two sprints ago and a behavioural contract (`build_concrete_codegen_view` "best-effort, None on failure") the carrier flip deliberately retired. |

**The acid-test answer.** For the **code**, the answer is now the strongest a
typecheck audit has recorded: the second-time solution would reproduce the
resolution + carrier layer essentially as-built. A rewrite with today's insight
produces exactly `VarRef::Local | VarRef::Global` / `ApplyRef::Dispatch |
ViaCallee` closed sums with no unresolved constructor, one Var chokepoint
(`record_reference_target`), the `or_insert(ViaCallee)` monotone stamp, the
`ViewBuildError::{Unresolved, NotConcrete}` gate precedence, per-frame binder
provenance at minimal blast radius, and one carrier-verdict discriminator
consumed everywhere a name-scan could wrong-dispatch. The S108 conflation this
crate carried (`Option<FQSymbol>` meaning both "local" and "producer bug") is
structurally gone, and the acceptance sweeps that verify it
(`typed-resolution-carrier.md` §14–§15) check out against source.

For the **record layer**, the answer is no — and the gap is no longer
cosmetic. A rewrite would not reproduce: a master design doc whose §3.1 table
budgets files deleted in S87/S109 and whose §2 declares a facade retired at
S72 "normative"; a FIXME that survived its own S110 resolution, was
re-dispositioned in S113 with a claim (*"convergence has not happened"*) one
file-open would have refuted, and then consumed S114 /arch sequencing,
/design deferral prose, a /testing probe, and an S115 scope slot — for a
refactor that landed two sprints earlier; or a 10,576-line test monolith whose
split was designed, ordered by the accepted R-4 done criterion, and silently
dropped. The crate's code discipline (verify against source, one seam, loud
misses) has outrun its record discipline; S114's own sweeps were rigorous
about code and inherited the record rot uninspected. That asymmetry is this
assessment's central finding.

---

## 2. Current state

### 2.1 Design quality (fitness) — strong

- **The carrier is the design the S108/S113 defect history was asking for.**
  The check-gate-leak class (×3 in S113) and the `Option` conflation are
  closed by TYPE: `crates/cranelisp-types/src/mono_expr.rs:177`
  (`ViewBuildError`), the total `var_refs`/`apply_refs` maps, and
  `from_expr` reading the resolution verdict BEFORE the type (gate precedence
  Unresolved-before-NotConcrete). Totality is by construction at the one Var
  chokepoint and the Apply epilogue `or_insert(ApplyRef::ViaCallee)` stamp,
  whose P26 safety is a real monotone-lattice argument
  (`typed-resolution-carrier.md` §14.1), not ordering luck.
- **The discriminator discipline landed single-sourced.** "Name is a TRIGGER,
  carrier is the IDENTITY" is one helper at the inference seams
  (`CheckState::resolves_to_carrier_identity`, `checker.rs:388`, consumed at
  `infer.rs:341/369/759/939/984`), one guard at the collectors
  (`callee_has_keyed_carrier`, `program/support.rs:28`, five named consumers),
  and a direct carrier-variant read at the one post-scope seam where frames
  are gone (`infer.rs:1215–1218`, with a rustdoc explaining exactly why it
  reads the recorded verdict instead of recomputing). This is the W3-review
  Important-1/-3 class closed the right way.
- **Settlement discipline is scribed with teeth.** `monomorphisation.md`
  §11.8.10 records the three harvest windows with per-window justification,
  four idempotence obligations each tied to an as-built mechanism, an honest
  cost note, and a standing rule that a FOURTH window is an /arch escalation
  event, not an implementation convenience. That is exactly the trajectory
  control a growth-prone mechanism needs.
- **Fitness watch-items** (not findings): `checker.rs` (3,180 lines) is the
  post-split growth magnet — it absorbed the carrier chokepoint, the
  provenance plumbing, and the lookup families; and the §14.1 `ViaCallee`
  lattice rests on an "at most ONE Dispatch writer per Apply span" invariant
  that is argued (disjoint span populations via `mem::take` isolation) but
  not separately pinned.

### 2.2 Design realisation — weak (the record layer)

The arc realised its design faithfully — the flip, the drains, and the W7
fixes match `typed-resolution-carrier.md` §§2–9, and the §14/§15 acceptance
sweeps' claims re-verify against source (§2.4). The weak grade is the crate's
own records, in three independent instances:

**(a) FIXME 0590 is a zombie record, and S114 planned real work from it.**
The four-mirror `TypeExpr` resolver convergence **landed in S110**: commit
`5ed07d60` ("converge four TypeExpr resolver mirrors onto one (S110 W-TC,
FIXME 0590)", 2026-07-16, ancestor of HEAD), recorded as DELIVERED in the
S110 outcome (`sprints/archive/sprint-110.md` §Delivered: "0590 (four
TypeExpr resolvers → one `TypeExprCtx`)"). Current source confirms:
`TypeExprCtx` + `ConVars` live in `resolve.rs:33/69`; the sig wrappers are
the live callers (`traits/impl_check.rs:708/721`, `traits/registry.rs:232`);
the mirror functions are deleted; `form.rs`'s `collect_type_var_ids` pre-walk
is deleted (mint-on-miss comment at `form.rs:413`); and the never-error
`Named` fabrication arms are gone — `resolve_named` (`resolve.rs:266–288`)
errors on an unknown name, its rustdoc explicitly recording "the never-error
`Named` fabrication arms of the former HKT mirror resolvers are DELETED".

Yet the FIXME file was never deleted (only its S110 close-table row went
stale as "open"), and the record then compounded:

- **S113**: the disposition appended to
  `design/arch/fixmes/0590-...md` asserts *"Kept open (convergence has not
  happened)"* — false at the time of writing, refutable by opening
  `traits/type_resolve.rs` (whose lines 153–163 record the collapse).
- **S114 Phase 1–3**: SPRINT.md Track E scheduled the "convergence"; /arch
  sequenced it LAST with a "latent-defect suspicion" for the `_hkt`
  never-error arms; `typed-resolution-carrier.md` §10.3(5) states the arms
  "live in `traits/type_resolve.rs` (×3) + `form.rs::check_type_expr`" —
  none exist.
- **S114 W1/W7**: /testing authored `tests/hkt_named_arm_probe.rs` whose
  comment claims the arm is "MASKED by the `form.rs::check_type_expr`
  pre-walk (which errors first)" — there is no pre-walk; the observed reject
  IS the landed convergence behaving correctly. `typecheck.md` §10's 0590 row
  (updated W7) repeats "DEFERRED — S115 candidate" with the same phantom
  latent-defect note, and `crates/cranelisp-typecheck/CLAUDE.md:92–96` says
  the four mirrors are "STILL OPEN".

No wrong compiler behaviour follows (the code is in the GOOD state), but the
cost is real: two sprints of planning/design/probe effort spent on deleted
code, an S115 scope slot booked for a no-op, and — the process face — a
five-agent chain (S113 /design-frontend → S114 /sprint, /arch,
/design-typecheck, /testing) in which no one verified the record against
source. This is the "derive the model from the source, not the record" class,
inverted onto the FIXME ledger itself. → Recommendation 1.

**(b) The master doc's core is falsified while its appendages stay fresh.**
`design/typecheck/typecheck.md` — "the single source of design intent...
where this doc and a subordinate doc disagree, this doc wins" — is actively
maintained at its S112–S114 sections (§9.7's P26 sweep record is current and
verified) while §§2–5 describe a different crate:

- §2 opens "The facade `design/arch/facades/typecheck.md` is normative"
  (typecheck.md:45) and §13 lists three facade docs as normative cross-refs
  (typecheck.md:604–606) — the facades were retired at S72; the directory now
  contains only s69/s70 audit files. (The header's contract list was
  corrected by the S109 0578 fix — the body was not.)
- §3.1's as-built table (typecheck.md:79–92) budgets `program.rs` 6,985
  ("Highest-debt file") and `traits.rs` 2,919 — files split away in S109 and
  S87 respectively; every LOC figure is stale.
- §4.1/§5.1 present the 2026-04-23 audit's six remediations as the live
  maintenance roadmap, headed by "HIGH — duplicate pipelines
  (`check_program*` / `check_repl_input*`)... this design doc's #1
  simplification target" — the duplicate pipelines are GONE (the names
  survive only as test-driver methods, `checker/test_support.rs:160/183`,
  explicitly "matching the retired `check_program`").
- §2.1's drift register and §11's tracked items anchor on FIXMEs
  0008/0098/0033/0043 — none exist in `design/arch/fixmes/` (0008 was moved
  to the legacy Decision register, commit `d2849a5a`); the doc's tracking
  claims are unverifiable dead ends.
- §10's status column contradicts the directory index of record:
  `step4-macro-deps.md` is "Current" here, HISTORICAL-bannered in
  `design/typecheck/CLAUDE.md`'s 0578 triage.

This is precisely the decay class the S108 assessment flagged for `traits.md`
(R-1), recurring one level up: the 0578 fix rewrote traits.md and triaged the
doc tree but left the master's body. An agent instructed that this doc "wins"
would design against a deleted architecture. → Recommendation 2.

**(c) The designed test split was silently not executed.**
`design/typecheck/program-decomposition.md` (the S109 0580 sign-off) §3
designs the `program/tests.rs` per-submodule split in detail — including an
explicit rejected-alternative box: *"Alternative considered — keep
`program/tests.rs` as one file... Rejected"* — and stages it inside Stage B.
Stage B landed the file cut (commit `1d65fdbd`) **without** the test split:
`program/tests.rs` is one flat 10,576-line file (213 tests, no inner
modules), grown +40% from the 7,505 lines the design measured. No deferral
was recorded anywhere I can find; the rejected alternative is simply what
shipped. The accepted R-4 done criterion ("splits alongside per METHOD §2.2
attributability") is unmet, and `finalize.rs` (1,517 lines) now exceeds both
the design's ~820 estimate and the criterion's ~1,200 ceiling.
→ Recommendation 3.

### 2.3 Simplicity & volume optimality

**Code — adequate.** ~20.7k production LOC (excluding sibling test files,
test support, and the 2,472-line `builtins.rs` fixture world, which remains
the price of the no-`cranelisp-primitives` isolation and which the rewrite
keeps). The shape is deliberate: `program/` seven purpose-named submodules,
`traits/` five, `ownership/` nine staged files (largest 1,137). What the
second-time solution would not reproduce:

- `finalize.rs` at 1,517 — +85% over its own design estimate in five sprints,
  because the settlement machinery keeps landing there (harvest windows 1–3
  all live in this file, `monomorphisation.md` §11.8.10's table cites
  finalize.rs:1023/1168/1191). The §11.8.10 window structure IS the natural
  cut line. → folds into Recommendation 3.
- `checker.rs` at 3,180 — the largest production file post-split; watch-item
  (§2.1), not yet over any stated budget.
- ~10 `#[allow(dead_code)]` "accessor pair; exercised via TestFixture"
  retentions in `checker.rs` (:860/:975/:992/:999/…) plus the test-only
  `has_impl_with_state` (`checker.rs:2662`; production callers: zero — only
  `checker/tests.rs` and `test_support.rs:325`) already classified for
  deletion by the §14.4 sweep. Marginal; noted for the next in-crate hygiene
  batch, not a standalone recommendation.

**Docs — weak.** 28 files in `design/typecheck/`. The 0578 triage (S109) gave
the tree an index of record with HISTORICAL banners — good — but the master
doc's core is falsified (§2.2b), the index and the master's §10 disagree on
at least one doc's status, and `typed-resolution-carrier.md` §10.3(5) +
`typecheck.md` §10 carry the 0590 phantom (§2.2a). The archive trigger on
`typed-resolution-carrier.md` ("the Phase-5 carrier wave lands; this doc's
producer contract folds into rustdoc") has fired but was extended in place
with the §14/§15 sweep records instead — defensible as an acceptance record,
but the trigger text is now stale against its own doc.

**Tests — adequate.** 789 in-crate unit tests green (W7 record), sibling
organisation everywhere EXCEPT the program monolith (§2.2c). The unit tier
sits at the right seams (below). No excess found — the volume is pinning
real invariants.

### 2.4 Duplication — strong (independently re-verified)

- **Divergent — still eliminated, and extended.** Zero active
  `resolved_targets` reads survive the flip (grep: comments only, all
  past-tense "was `resolved_targets`"). The four-mirror `TypeExpr` resolver
  family is converged onto ONE canonical resolver with a data-varying
  `TypeExprCtx` (`resolve.rs:31–33`: "a new resolution context is a new
  `TypeExprCtx` construction, never a second resolver") — the records
  claiming otherwise are the §2.2a finding; the CODE is clean.
- **Entry-point — closed and self-enforcing.** The shadow-vs-table decision
  is one discriminator consumed at five inference seams + five collectors +
  one post-scope carrier read (§2.1); the child-enumeration walk is ONE
  helper pair (`for_each_child_expr[_mut]`, `program/support.rs:48/102`) that
  every structural walker routes through — the S108-era "duplicate `Expr`
  walkers" risk (which the stale master doc still lists as HIGH) is
  structurally closed.
- **Mirror — clean.** The S108 watch-item stands at n=1: the one bulk
  prelude enumeration reader (`find_trait_method_decl`,
  `traits/dispatch.rs:442`) is still the only hand-rolled prelude hop;
  no second bulk reader has appeared.
- **Spec-surface — nothing new surfaced this cycle.** (The S108 R-3
  candidate was declined with a decisive user rationale; correctly not
  re-raised.)

### 2.5 Risk-weighted coverage — strong

Top risks derived from the crate's invariants + this sprint's defect history,
each verdicted:

- **Risk: a reference reaching codegen with no resolution verdict** (the
  check-gate-leak class the carrier exists to close). **Pinned,
  production-path + unit-tier at the exact seam**:
  `mono_expr/tests.rs::from_expr_real_span_var_miss_errors_unresolved` (+
  Apply sibling) pin the gate; CA-1..CA-5 pin the e2e faces (located
  trait-naming error, all-local totality, shadow-over-global, ViaCallee
  positive, no-codegen-leak standing negative); the F-D2-10 ×4 flips landed
  RED→GREEN through the real binary.
- **Risk: binder provenance mis-grained** (shadow disambiguation). **Pinned**
  — `ScopeStack.frame_spans` with 8 unit tests in `scope/tests.rs`; the
  self-recursion carve-out (`VarRef::Global`, the 0616 guard) is an
  enumerated unit obligation.
- **Risk: settlement-window regression** (harvest idempotence). **Pinned by
  contract + fences**: §11.8.10's four obligations each name an as-built
  mechanism; MC-X4/X4b are a deliberate two-face fence against a partial
  fix; the fourth-window /arch tripwire is standing.
- **Risk: the 5 stable REDs.** All are NEW probe-discovered defects pinned
  this sprint, each S115-attributed with owner + class + fix constraints
  (chained `MayAliasOf` ×2 → /dev(typecheck) ownership with the family-grain
  invariant binding the fix; entry-`Pure` leak → backend; GOT-slot
  carrier-loss pair → backend 0705 + typecheck fn-as-value). The
  failing-not-ignored discipline is working exactly as designed, and the
  certification separated stable-REDs-exact from the NAMED flap (0694) per
  the standing convention.
- **Residual un-pinned corner**: the §14.1 single-Dispatch-writer invariant
  (watch-item, §2.1) and the F-D2-12 fence carrying the benign-swallow
  verdict at `mono_collect.rs:781` — both argued and recorded, neither has a
  dedicated failing-on-revert pin. Acceptable; named so the next audit can
  check drift.

### 2.6 Maintainability — adequate

The carrier-era rustdoc is the crate's high-water mark — the
`resolve_deferred_trait_calls` comment (infer.rs:1202–1214) explains the
post-scope carrier read's WHY at exactly the depth a future agent needs; the
`callee_has_keyed_carrier` contract names its five consumers; the flip
comments consistently record "was `resolved_targets`" with sprint provenance.
The debt is concentrated record-side (§2.2, §2.7). Code-side residue:
`checker.rs:2061/2683` rustdoc still narrates `has_impl_with_state` as a live
verification path (it is test-only); the `#[allow(dead_code)]` accessor-pair
population (§2.3). Neither warrants its own recommendation; both ride the
next hygiene batch.

### 2.7 Memory freshness — weak

`crates/cranelisp-typecheck/CLAUDE.md` was graded strong at S108; two heavy
sprints later it has decayed exactly where the code moved fastest:

- **Falsified contract**: §"Concrete-boundary `codegen_view` population"
  describes `build_concrete_codegen_view` as "best-effort: `Some` on
  `from_expr` success, `None` on failure" — the S114 flip widened it to
  `Result<Option<..>, CranelispError>` (`program/support.rs:282–288`) where
  `Unresolved` PROPAGATES and only `NotConcrete` falls back. The distinction
  this paragraph erases is the carrier's crux (conflating them "re-opens the
  check-gate-leak class one level up", carrier doc §8).
- **Falsified status**: the §"Written type variables" 0590 paragraph
  (CLAUDE.md:92–96) — "four MIRROR resolvers... STILL OPEN" (§2.2a).
- **Dead references**: `traits.rs:~1508` (split S87), `program.rs` seam names
  ×3 (split S109), `traits.rs::check_impl_method` (now
  `traits/impl_check.rs`).
- **Stale fact**: cross-module mono fact 3 names `has_impl_with_state` as the
  verification path — production impl lookup no longer routes through it
  (zero production callers; the live path is `has_impl_in_home`,
  `traits/dispatch.rs:75`).

The §"Bare-name resolution" and §"callees" sections remain substantially
accurate (one stale carrier name at §callees: "writes `resolved_targets`").
→ Recommendation 4.

### 2.8 Prior-assessment reconciliation (S108 → S114)

All five S108 recommendations were disposed at S109 Phase 1 (full trail in
`audits/cranelisp-typecheck-s108.md` §4) — the first complete
accept/decline→action cycle for this context:

| S108 rec | Disposition | S114 verification |
|---|---|---|
| R-1 traits.md rewrite + doc triage (FIXME 0578) | ACCEPTED, landed S109 | **DONE and durable** — the CLAUDE.md index of record + HISTORICAL banners exist; traits.md current. The class recurred one level up in typecheck.md's body (§2.2b) — the fix was scoped to traits.md + the header contract list, not the master's core. |
| R-2 resolution-seam doc/naming sweep (0579) | ACCEPTED, landed S109 (commit `68774c8b`) | **DONE** — "outer scope" grep is clean of conceptual uses (survivors are lexical-let-scope comments in `ownership/transfer.rs:855/879` + spec-citing test comments — legitimate); `resolve_entry_in_current_module` renamed into the `_scoped` family. |
| R-3 drop dotted `Type.Ctor` | DECLINED (full-capability fix chosen) | Correctly not re-raised; the capability landed S109. |
| R-4 program.rs split (0580) | ACCEPTED, landed S109 (commits `dd7a458d`/`1d65fdbd`) | **PARTIAL** — file cut + phase-split done; the test-split half of the done criterion silently dropped and the finalize budget since breached (§2.2c). |
| R-5 S87 residue batch (0581) | ACCEPTED, landed S109 (commit `2c3b7056`) | **DONE** — FQ no-impl diagnostics, loud `parsed_to_top_level`, dead `"user"`-defaulting helper removed. |

The disposition mechanism works; what it did not catch is a *partially*
executed acceptance (R-4) — the done criterion was multi-part and no gate
re-checked the parts.

### 2.9 The record-vs-source failure class (cross-cutting)

Three of this assessment's four weak findings are one class: **a record
asserted something about the source that a single file-open would have
refuted, and downstream agents consumed the record instead of the source.**
The 0590 chain (§2.2a) is the sharpest instance — five agents across two
sprints, including this sprint's Phase-2 /arch review and Phase-3 design
deployments, propagated "the mirrors exist" while the mirrors' own file
recorded their deletion. The crate's CODE discipline is the opposite (loud
keyed misses, verify-at-seam, falsifiability-first — the MS-P7 fix's first
act was confirming the fact chain absent). The gap is procedural: FIXME
dispositions and carry decisions have no verify-against-source step. This is
surfaced as process feedback inside Recommendation 1 for the Phase-1
processing to weigh — the fix is cheap (the disposition step opens
`refers_to`), and the S110 close-table row that started the rot ("open"
beside a §Delivered line saying converged) suggests the close checklist
could also assert FIXME-table-vs-outcome consistency.

---

## 3. Recommendations

Proposals only — disposed at S115 Phase 1; no FIXMEs filed by `/audit`. No
live compiler defect was uncovered (the 0590 finding is record corruption
over CORRECT code; the 5 suite REDs are already attributed and carried).

**R-1. Disposition FIXME 0590 against source; correct the four records that
carry its phantom; strike the phantom S115 scope slot.** *(record integrity +
process feedback)*
- Evidence: §2.2a — commit `5ed07d60` (in HEAD) + `sprints/archive/sprint-110.md`
  §Delivered vs `design/arch/fixmes/0590-...md` "convergence has not
  happened" (S113); the four falsified records:
  `design/typecheck/typecheck.md` §10 0590 row,
  `design/typecheck/typed-resolution-carrier.md` §10.3(5),
  `crates/cranelisp-typecheck/CLAUDE.md:92–96`,
  `tests/hkt_named_arm_probe.rs:1–18` (comment narrative only — the test
  itself is a valid born-green regression fence and should be KEPT with a
  corrected comment).
- Cost: **small** (verification is done — this section is the evidence; the
  edits are mechanical). Owner: **/sprint** (FIXME lifecycle + S115 scope
  strike) with riders to **/design**(typecheck) (the two design-doc rows),
  **/dev**(typecheck) (CLAUDE.md paragraph — may merge into R-4), and
  **/testing** (the probe-file comment).
- Done: FIXME 0590 deleted (or re-scoped ONLY to residuals verified live in
  source — the sole candidate found is the FIXME's rustdoc-inaccuracy
  sub-item, to be re-checked, since the S110 wave may have cured it); no
  surviving record claims the mirrors/never-error arms exist; S115 Phase 1
  carries no "0590 deployment" slot. **Process feedback for the same gate:**
  adopt "a FIXME disposition or carry decision verifies the claim against
  `refers_to` source" as the disposition step's first act, and have the
  Phase-7 close checklist assert FIXME-table-vs-§Delivered consistency (the
  S110 close is the counterexample). Cures the class (§2.9), not just this
  instance.

**R-2. Rewrite `typecheck.md`'s falsified core against the as-built crate.**
*(design feedback — the S108 R-1 class, one level up)*
- Evidence: §2.2b — typecheck.md:45 + :604–606 (retired facades as
  normative), :79–92 (dead file tree), §4.1/§5.1 (retired 20260423-audit
  roadmap presented as live, incl. a resolved "duplicate pipelines" #1
  priority), §2.1/§11 (tracking anchored on nonexistent FIXMEs
  0008/0098/0033/0043), §10 status contradiction with the CLAUDE.md index.
- Cost: **medium**. Owner: **/design**(typecheck).
- Done: §2 states the ACTUAL contract sources (BC §2 + `public-api.txt` +
  lib.rs rustdoc — the header already says this; the body must agree); §3
  reflects the live module tree; the maintenance roadmap is re-derived from
  the live tree or explicitly retired in favour of the audit cycle; every
  FIXME the doc tracks resolves to a live file or a recorded resolution; §10
  agrees with the index of record. Cures the risk (the doc that "wins"
  mis-designing future work), not the stale text.

**R-3. Execute the designed `program/tests.rs` split; re-budget
`finalize.rs` at the harvest-window seams.**
- Evidence: §2.2c — `program-decomposition.md` §3 (designed split, explicit
  rejected-alternative box for what actually shipped, staged plan with
  suite-green gates already written); `program/tests.rs` 10,576 lines / 213
  tests / zero inner modules (7,505 at design time); `finalize.rs` 1,517 vs
  ~820 design estimate / ~1,200 accepted ceiling; §11.8.10's three windows
  all resident in finalize.rs give the natural function-level cut.
- Cost: **medium** (mechanical; the design and its citation-update list —
  CLAUDE.md test-path names, `tests/plan` citations — already exist). Owner:
  **/dev**(typecheck).
- Done: per-submodule sibling test files per the §3 distribution table (a
  RED attributes to a production submodule by file); no `program/` submodule
  exceeds ~1,200 lines; the R-4/0580 done criterion is finally met in full.
  If instead DECLINED (e.g. the monolith is judged acceptable), record it in
  `program-decomposition.md` §3 superseding the rejected-alternative box —
  either outcome ends the silent divergence between design and tree.

**R-4. Crate `CLAUDE.md` currency sweep.** *(memory freshness)*
- Evidence: §2.7 — the falsified `build_concrete_codegen_view` contract (the
  crux `Unresolved`-propagates/`NotConcrete`-falls-back distinction absent),
  the 0590 "STILL OPEN" paragraph, dead `traits.rs`/`program.rs` seam
  references, `has_impl_with_state` as live verification path, the §callees
  `resolved_targets` name.
- Cost: **small**. Owner: **/dev**(typecheck).
- Done: every load-bearing claim in the file verifies against current
  source; the codegen_view section states the post-flip `ViewBuildError`
  contract explicitly (it is the file's most safety-relevant fact); no dead
  file references. (The 0590 paragraph edit coordinates with R-1.)

---

## 4. Disposition trail

*(Appended at S115 Phase 1 by `/sprint` + the user; not by `/audit`.)*

**2026-07-20 — S115 Phase 1, user approved. All four recommendations ACCEPTED.**

- **R-1 ACCEPTED and executed at Phase 1**: FIXME 0590 verified against source
  per the recommendation's own re-check clause — the sole residual candidate
  (the resolve.rs/checker.rs rustdoc inaccuracy) is CURED (rustdoc now
  records the "former four mirror resolvers" past-tense with correct mint
  semantics on the live `TypeExprCtx` path; `resolve.rs:116`,
  `checker.rs:2950/2979/3005`). 0590 deleted by `/sprint` (audit-disposal
  exception, METHOD §3.3 as amended this sprint); no S115 "0590 deployment"
  slot exists in `sprints/SPRINT.md`. Riders filed: design-doc rows →
  FIXME 0721 (folded with R-2, same owner/wave); CLAUDE.md paragraph →
  FIXME 0723 (folded with R-4); probe-comment correction → FIXME 0724
  (test KEPT as a born-green fence). **Process feedback ADOPTED as METHOD
  amendments** (user-approved): §3.3 "verify-against-source first" binding
  disposition rule + §2.2 Phase-7 close-checklist FIXME-vs-§Delivered
  consistency assertion.
- **R-2 ACCEPTED** → FIXME 0721, `target: /design` (typecheck), S115.
- **R-3 ACCEPTED** → FIXME 0722, `target: /dev` (typecheck), S115. Flagged
  under METHOD §2.4 2× escalation (second carry of the half-executed S108
  R-4 acceptance): ships this sprint; a further silent drop is not an
  option — decline path requires superseding the design's
  rejected-alternative box.
- **R-4 ACCEPTED** → FIXME 0723, `target: /dev` (typecheck), S115 (merges
  the R-1 CLAUDE.md rider).
