# Sprint 119: The Release Class and the Typed Stratum

**Status**: PHASE 1 SCOPE DRAFT

**Goal**: Rule and close the non-concrete-release defect class (0903/0907/0916/0917) — the
three-faced family that today refuses, leaks, or writes wild — and attack the same failures
at the representability level by landing option-1 typed handles (tranches A+B), taking the
macro-turn leak (0889) out of the code's reach rather than out of its measurements.

**Audit**: `src/` — the binary and integration layer (user-selected 2026-07-26; last audited
S109, the oldest in rotation). Read-only, dispatched in the Phase 6/7 window →
`audits/src-s119.md`, disposed at S120 Phase 1.

---

## Baseline at open (measured 2026-07-26 at `5520186d`, clean tree)

`cargo nextest run --no-fail-fast`: **5,660 run / 5,639 passed / 21 failed / 1 skipped.**

Twenty of the twenty-one are the S118-certified carry set. The twenty-first —
`nullary_return_dispatch_method_only_import::…_no_codegen_leak` — carries a `// defect:`
annotation (`class=check-gate-leak locus=typecheck`, found=S112, owner `/dev`) and is a
**named member of the 0694 load-flap family** (`tests/plan/s115-test-plan.md` §"Member 1").
Its reappearance on the first S119 run, unprompted, is fresh evidence for Track C and is
recorded here as the sprint's opening 0694 datum. **No untraced RED.**

RED attribution by owning defect:

| Defect | Cells | Owner |
|---|---|---|
| 0907 (IO `Bind` release) | 7 | `/design`(backend) |
| 0917 (nullary-arm protect inc) | 3 | `/dev`(backend) |
| 0867 (accessor synthesis gate) | 3 | `/dev`(typecheck) |
| 0863 (macro presentation transaction) | 2 | `/design`→`/dev`(src) |
| 0868 / 0869 (cache restoration) | 2 | `/dev`(src) |
| 0916 (wild guarded RC write) | 1 | `/design`+`/dev`(backend) |
| 0913 (residual-param result leak) | 1 | `/design`(typecheck) |
| 0694 (`launch_grid`) | 1 | `/qa` |
| 0694 (flap member, above) | 1 | `/qa` |

---

## Phase 1 dispositions (user, 2026-07-26)

### Sprint shape — **structural-first**

Approved: the option paper's §6.2 core **in full** — option-1 tranche A **and** tranche B, so
the 0889 recovery lands this sprint — alongside Track 1 (the release class). Track 2's ruled
carries **demote to riders**, taken in the priority order recorded there. The user accepted
explicitly that S118's finding — ownership work consumes the sprint — is likely to repeat.

### Option paper §7 — the five decisions

| # | Decision | Disposition |
|---|---|---|
| 1 | Option 2 (uniform-but-redundant RC emission as the dev-tier default) | **DEFER pending measurement.** Nothing structural commits now; the twin-control measurement gate (uniform vs current emission, exemplar + suite, via the marginal harness) runs inside Track 3 at near-zero cost and hands S120 real numbers. `ownership-inference.md` is **not** re-staged this sprint. |
| 2 | The S119 core — tranches A+B + option-3 generalization | **APPROVED in full** (see sprint shape). Per-tranche contracts still pass the normal Phase-3 design gates. |
| 3 | Option 4 — the bounded emission-audit spike | **NOT YET DISPOSED** — see §Open Phase-1 items. `/sprint` recommends deferring to S120: with tranche B in scope the sprint has no room for a discretionary spike, and option 4's reach shrinks anyway if option 2 is later adopted. |
| 4 | 0889 recovery route | **Via tranche B**, this sprint — implied by the structural-first approval. **Blocked on 0920** (see below): tranche B's scope as written does not contain the 0889 leak. |
| 5 | Normative leak-lane form | Routed to `/qa` in Phase 3 to propose, bundled with 0890. User arbitrates only if the certification split's meaning changes. |

### `cranelisp-types` S118 audit — **all five recommendations ACCEPTED**

Design **Strong**, realisation **Adequate**; the auditor's priority is truth-restoration of
the facade, not redesign. FIXMEs filed by `/sprint` per METHOD §2.6:

| R | Ask | Filed as | Owner |
|---|---|---|---|
| R1 | Delete five zero-consumer public types; resolve the Decision-39 append carrier one way | **0918** | `/arch` (+`/dev`(int) rider if routed) |
| R2 | Retract the phantom concurrency/`dll` narrative; fix retired citations; settle `PlatformSpec.name` | **0919** | `/arch` |
| R3 | Land the injective GOT data-symbol mint | rides existing **0748** | `/arch` + `/dev` |
| R4 | `module.rs` rustdoc history compaction (doc-only) | **0919** | `/arch` |
| R5 | Symbol-anchor the crate `CLAUDE.md` citations | **0919** | `/arch` |

R2+R4+R5 filed as one FIXME because the assessment itself calls them "one coherent
facade-truth pass if accepted together". R3 is scheduling weight on 0748, not a new filing —
it rides the types window that 0869's `CACHE_SCHEMA_VERSION` 23→24 bump and 0898's
`result_root()` collapse already open. `/sprint` filed no disposition prose into
`audits/cranelisp-types-s118.md` §4 (outside `/sprint`'s files); these FIXMEs plus this
section are the disposition record, and git history is the audit trail.

---

## Verify-against-source findings (METHOD §3.3, performed 2026-07-26)

Every scope carry below was verified against its `refers_to` source as the binding first act.
All central claims **hold**. Four corrections must be carried into the dispatch prompts so
they do not propagate:

1. **0920 (filed) — tranche B's scope does not contain the 0889 leak.** The option paper
   (`:236-237`) scopes tranche B as "`marshal.rs` (339 lines, the macro-expansion data path)"
   and designates it the 0889 recovery vehicle. Those are two different files: the 339-line
   file is `crates/cranelisp-primitives/src/marshal.rs` (runtime `quote_sexp`/`sconcat`
   helpers); the 0889 leak lives in `src/marshal.rs` (**732 lines**) plus
   `src/expander.rs::invoke_clause` — in the **int binary**, which §1.1 explicitly excludes
   from "the hand-written runtime pair". **This is a Phase-2 blocker**: the sprint's headline
   deliverable is currently scoped at the wrong file and assigned to the wrong `/design`
   surface. `/arch` re-scopes before Phase 3 dispatch.
2. **0917's cited locus is wrong.** `protect_return_value` lives at
   `crates/cranelisp-backend/src/compiler/rc_emission.rs:156` (in
   `impl FnCompiler`), **not** in `fn_compiler.rs`; `git log -S` shows it was never there.
   The type-qualified reading (`FnCompiler::protect_return_value`) is right; the file is not.
   Call sites: `match_codegen.rs:322,574`, `control_flow/lambda.rs:554`,
   `control_flow/launch.rs:261`.
3. **0916's title is stale** ("loses TCO"). The body already carries `/qa`'s falsification —
   TCO is intact (`jump block1` in both variants); the mechanism is a wild guarded RC write on
   a scalar at the `NULLARY_TAG_THRESHOLD` n=1023/1024 boundary, re-attributed to 0903
   family 2 with severity raised to memory-unsafe. Correct the title in the fixing window.
4. **0863's frontmatter is stale** (`status: deferred`, `target_sprint: 118`). The design is
   verified **READY** — `design/int/s117-conformance-recovery.md` §6.5 records `/arch`
   ruling 11, preconditions re-verified unmet at HEAD, and two deltas the implementing wave
   must absorb. Its stated blocker (land 0745 first) is **discharged** — 0745's
   implementation completed at `fc3375f9..16a26408`.

Also confirmed, load-bearing for scope: **`CACHE_SCHEMA_VERSION` = 23** at
`crates/cranelisp-backend/src/cache/mod.rs:375` — the ruled 23→24 window is unspent.
**Nothing of 0869 has landed** (zero hits for `WrittenTraitImpl`, `written_trait_impls`,
`enrol_written_trait_impl`, `trait_impl_key`). **0903's gate implementation is absent** —
`fn_compiler.rs:1288` is still type-keyed, with rustdoc at `:1230-1261` saying so
deliberately; the re-land after the ruling is genuinely a paste. **0867's seam is exactly as
described** (`adt.rs:136` computes `is_product`, `:241-245` gates synthesis on it over
`ctor_infos[0]` only, `:240` carries the comment the spec contradicts). **0907's severity is
understated** in its own severity block — the `/stdlib` appendix reconciles it to two named
modules (`core.io` and its parent `core`), matching the measured baseline.

Tranche A's sizing is sound: **83** `extern "C" fn` in the pair (intrinsics 81 + primitives 2
— exact match to the paper's ~83), **136** non-extern `i64`-taking fn declarations, **36**
`consume_*` call sites in primitives (`string.rs` 27, `marshal.rs` 8, `int.rs` 1).

---

## Scope

Two co-spines and a rider set. Track 1 and Track 3 are both the sprint; Track 2 is the dial.

### Track 1 — The non-concrete-release class (spine)

One design window ruling three faces of one class, then implementation.

- **0903** — re-rule §4.1 over the *whole* measured class. The S118 frame-key ruling was
  implemented and measured to turn 16 green corpus programs into hard codegen refusals; the
  gate implementation and three negative cells are held back unlanded so the re-land after
  the ruling is a paste (verified absent from the tree). **Co-ruled with 0907 and 0916.**
- **0907** — rule how a concrete `IO T` value is released. `IO`'s existential `Bind` ctor
  defeats canonical per-concrete glue derivation at `drop_glue.rs:497-505`, so every release
  hard-refuses; `bootstrap.rs:767-783` is the manual seed. `/stdlib` proved there is no legal
  re-spelling workaround. Three candidate directions are on the file, one of which
  (admission exclusion) restores the silent leak and should be weighed as such.
  **7 REDs, 2 of 38 stdlib modules, 2 examples.**
- **0916** — memory-unsafe wild guarded RC write on a scalar payload. Correct the title.
- **0917** — unbalanced threshold-guarded protect inc at
  `FnCompiler::protect_return_value` (**`rc_emission.rs:156`** — see finding 2);
  per-solve-linear at application scale; the real owner of exemplar cell #21.
- **0891** — unblocks the moment 0903 rules; falsification preserved paste-ready.
- **0915** — backend frame composition (items 1–3) plus the int presentation rider (item 4);
  the §5.5 frame guard was deferred into this window because every current trigger rides
  0907's refusal.
- **0906** — nit; folds the third hand-rolled nullary-skip guard, with a scoped golden
  re-baseline (not byte-identical — block creation order swaps CLIF numbering).

**Acceptance**: 0907×7 + 0917×3 + 0916×1 = **11 REDs green**; `stdlib_conformance` 38/38;
`examples::every_example_runs_with_documented_exit` green; exemplar cell #21 residue inside
its pin; **zero new codegen refusals across the 16-program corpus the S118 measurement
named** — this last is the gate the S118 ruling failed, so it is asserted, not assumed.

### Track 3 — The typed stratum (co-spine)

Attacks the same failures at the representability level: make the wrong count unwritable.

- **Tranche A — the drop/consume funnel.** `cranelisp-intrinsics::drop` plus the 36
  primitives `consume_*` call sites newtyped to `Owned` / `Borrowed`. `Owned` is
  `#[must_use]`, no `Copy`/`Clone`, debug-profile drop-bomb; `Borrowed` is `Copy` and cannot
  be stored, with `.to_owned()` the single home of `rc_inc`. C-ABI/JIT surface untouched —
  `extern "C"` keeps `i64`; the typed layer begins at the shim. **Shim-fact single-sourcing
  from the declaration table is part of tranche A's design, not a follow-on** — it is the
  §2.2 false-confidence mitigation and the trusted base narrows to it. W3-independent, no
  schema/ABI risk, no `cranelisp-types` impact (confirmed by the S118 types audit).
  Precedents already silent in-tree: the S117 Vec-of-String boundary and platform's
  `CLOwned<T>`.
- **Tranche B — the macro-turn marshal path, and with it FIXME 0889.** **Scope blocked on
  0920** until `/arch` chooses between the primitives-side file, the int-side file that
  actually leaks, or both as B1/B2. Whichever is chosen, `/design`(int) must rule the
  ownership protocol before any `/dev` dispatch if `src/marshal.rs` is in scope — 0889 itself
  requires this. The 0889 exact-value pins flip from documented-residual to zero on success.
  The naive-release path is warned against by the 0638 interior-alias history; the point of
  the tranche is that the danger *is* the miscounting typed handles remove.
- **Option 3 generalization** — per-crate unit-tier marginal helper; the `/qa` lens rule that
  a unit row asserting balance at one point is the anti-pattern (assert a rate, a tally, or a
  marginal); the cold/warm cache axis (0890); threshold-cell retirement; decision 5's
  normative-form proposal.
- **The option-2 measurement gate** — uniform-vs-current emission measured on the exemplar and
  the suite via the marginal harness's twin-control shape. **Report only**, no commitment;
  the deliverable is the number S120 decides on.

**Acceptance**: the S118 instrument set re-runs **byte-identically** across the tranche
churn (this is the mitigation for churn masking behaviour change — it is the acceptance
criterion, not a nicety); RE-1 fences and existing unit rows pin behaviour unchanged;
`public-api.txt` delta confined to the pair where signatures are `pub`; extern names and ABI
unchanged; 0889's residue pins read zero if tranche B reaches the leak; the option-2
measurement lands as a number with its method recorded.

### Track 2 — Ruled carries, demoted to riders

Every item has a ruling or approved design in force; none needs new architecture. Taken in
this order as capacity allows — this **is** the drop order, deepest last:

1. **0867** — `/dev`(typecheck): synthesise accessors over every ctor arm's field list, not
   just `ctor_infos[0]`. Single seam (`adt.rs:136,241-245`), no open spec question,
   attribution finalized. **3 REDs.** Cheapest RED-per-effort in the sprint. Honour the
   `/stdlib` blast-radius rider (26 symbols, cross-module head/rest contest).
2. **0869** + **0868** — `/dev`(src) + `cranelisp-types`: the carrier ruling is authored and
   in force (`design/arch/trait-impl-cache-carrier.md`); `CACHE_SCHEMA_VERSION` 23→24 in the
   implementing change-set only; re-point the two hand-rolled `impl$` mint sites
   (`traits/dispatch.rs:143`, `traits/impl_check.rs:421`). 0868 survives independently.
   **2 REDs**, and the schema window that **0898** and **0748/R3** both ride.
3. **0863** — `/design`→`/dev`(src): the cluster-wide prepared macro registration and
   presentation transaction. Design verified READY; absorb the two §6.5 deltas. **2 REDs**
   (DF-1/DF-2). **Second deferral spent** — see §Open Phase-1 items.
4. **0913** — `/design`(typecheck) rules the lenient view (`MonoExpr::lenient_from_expr`) and
   corrects `result-owner.md` §1.1.1's scope; then `/dev`. **1 RED.** Must **not** be closed
   by pinning annotations in tests or docs.
5. **0914** — `/design`(int): move `/mem`'s counter window past `release_program_result()`.
   Instrument truthfulness — `/mem` today reports a phantom leak for every heap value.
6. **Documentation and fixture riders**: 0870, 0874 (platform audit R1/R5), 0873
   (design approved, `/arch` gate passed — implementation only, three conditions on the
   change-set), 0871, 0900, 0798, 0799.

### Track 4 — Types-crate facade truth

**0918** (dead surface + append carrier) and **0919** (facade-truth pass) as `/arch` work,
plus **0748** riding Track 2 item 2's schema window. Doc and dead-surface work;
`public-api.txt` regenerated in the same change-set.

### Track C — carried, with one bounded obligation

0694 / 0604 / 0818 remain open. This sprint does **not** attempt the heisenbug. It owes one
thing: the S116 D1 discriminating experiment, plus a recorded re-measurement of the opening
flap datum in §Baseline. 0859's disposition rides here.

### Explicitly out of scope

| Item | Rationale | Target |
|---|---|---|
| Option 1 tranches C and D | Capacity — A+B is already two-to-three dev waves | S120 |
| Option 2 **adoption** (its measurement is in scope) | Re-sequences `ownership-inference.md`; must not interleave with a release-class window | S120, on the measurement |
| Option 4 spike | Recommended deferral — see §Open Phase-1 items | S120 |
| Tracks D/E beyond the named carries | Descoped by the user at S118 close; groundwork stays banked | S120+ |
| 0604 / 0818 root cause | Three-sprint heisenbug; needs the discriminating experiment first, which is in scope | S120 |
| `--release` tier, LLVM backend | Phase H sequence — gated behind the memory model | post-S120 |

### Capacity note

Two co-spines plus riders exceeds an S118-sized sprint, and the user approved it knowing so.
The honest consequence: **Track 2 items 3–6 and Track 4 R4 are the likely casualties**, and
0863 would take a third deferral. If capacity binds, drop in this order: Track 4 R4 →
Track 2 item 6 → Track 2 item 5 → Track 2 item 4 → Track 2 item 3. Track 1 and Track 3
tranche A do not drop. Track 3 tranche B drops only if 0920 cannot be resolved in Phase 2.

---

## Open Phase-1 items

Three dispositions are still owed before Phase 2 closes:

1. **Option-4 spike** (paper decision 3) — authorize or defer. `/sprint` recommends **defer to
   S120**.
2. **0863's third deferral** — under the structural-first shape 0863 is Track 2 item 3, which
   the capacity note flags as a likely casualty. Its second deferral is spent (S117→S118,
   user-approved), so METHOD §2.4 requires **explicit user sign-off** for a third. Sign it off
   now as a conditional, or promote 0863 above tranche B.
3. **0912** (`/spec` frames, user rules) — should an undeclared `deftype` field,
   `(deftype B (Mk [v]))`, be rejected at declaration time? §3.11.1's full-concreteness check
   does not reach declarations. **Coupled to Track 1**: the free-var template keeps feeding one
   of 0903's leak families, so the answer changes what the release ruling must cover. Needs
   arbitration **before** the 0903 window opens, not after.

Lower-priority escalations for disposition at any point in the sprint: **0859**
(`/qa`, target_sprint 118 undischarged — ship or return its R-2 user disposition);
**0463** (`/examples`, deferred 3× with the trigger still unmet — fourth deferral with
sign-off, or close won't-do); **0050** (`/int`, ~50-sprint carry whose stated blocker expired
when the display protocol landed at S106 — ship or close); **0553** (`/typecheck`, deferred
to S114, five sprints ago); **0821** fork (c) (`/arch` + user — is the `examples/`
free-standing distortion itself a signal that some stdlib forms belong in prelude?
`/examples` parks its S120 row on the answer); **0708** (spec cascade owed; the user already
ruled Reading A-structural on 2026-07-21).

---

## FIXME debt

56 open + 9 deferred at open, plus 0918/0919/0920 filed at Phase 1. The table lists those in
scope or requiring a disposition. Full inventory: `design/arch/fixmes/`.

| FIXME | Target skill | Status | Track / disposition |
|---|---|---|---|
| 0903 | /design (backend) | open | T1 — the co-ruling |
| 0907 | /design (backend) | open | T1 — co-ruled with 0903 |
| 0916 | /design + /dev (backend) | open | T1 — memory-unsafe; title correction owed |
| 0917 | /dev (backend) | open | T1 — locus correction owed (finding 2) |
| 0891 | /dev (backend) | deferred, blocked_on 0903 | T1 — re-land is a paste |
| 0915 | /design (backend) + /design (int) | open | T1 |
| 0906 | /dev (backend) | open | T1 rider — scoped golden re-baseline |
| 0920 | /arch | open | **T3 blocker** — tranche B scope |
| 0889 | /design (int) | open | T3 tranche B — the recovery target |
| 0890 | /qa | open | T3 option-3 — cold/warm axis |
| 0867 | /dev (typecheck) | open | T2 ① |
| 0869 | /dev (src) + types | open | T2 ② — schema 23→24 |
| 0868 | /dev (src) | open | T2 ② |
| 0898 | /arch | deferred → S119 | T2 ② rider — rides the schema window |
| 0748 | /arch | open | T4 R3 — rides the schema window |
| 0863 | /dev (src) | deferred ×2 | T2 ③ — sign-off owed |
| 0913 | /design (typecheck) | open | T2 ④ |
| 0914 | /design (int) | open | T2 ⑤ |
| 0870, 0874, 0871 | /dev + /design (platform) | open | T2 ⑥ (platform audit R1/R5/R2) |
| 0873 | /design → /dev (platform) | open | T2 ⑥ — arch gate passed |
| 0900, 0798, 0799 | /testing | open / deferred ×2 | T2 ⑥ |
| 0918, 0919 | /arch | open | T4 — types audit R1 / R2+R4+R5 |
| 0694, 0604, 0818 | /qa | open | Track C — D1 experiment only |
| 0859 | /qa | deferred, target 118 | Escalation disposition |
| 0912 | /spec | open | **Open Phase-1 item — user arbitration** |
| 0821 | /arch | open | Escalation disposition — fork (c) |
| 0708 | /spec | open | Spec cascade owed (user ruled 2026-07-21) |
| 0050 | /int | deferred ~50 sprints | Escalation — blocker expired |
| 0553 | /typecheck | deferred ×2 | Escalation |
| 0463 | /examples | deferred ×3 | Escalation |
| 0765, 0764 | /dev, /review | open | Process rules — fold into dispatch discipline |

---

## Architecture review (Phase 2)

{Pending — `/arch` against this DRAFT. Two questions lead: **0920** (tranche B's scope and
owning surface, a blocker on the sprint's headline deliverable) and the **0903/0907/0916
co-ruling's** shape — specifically whether the three faces admit one ruling or whether 0907's
existential `Bind` needs its own mechanism.}

## Skill plans (Phase 3)

{Pending.}

## Waves (Phase 4)

{Pending.}

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P1 | Explore ×4 | read-only carry/FIXME/audit inventory + source verification | session | — | Read-only fan-out, not a role dispatch |

## Notes

**2026-07-26 — Phase 1 opened.** Baseline measured at `5520186d` (21 REDs, all attributed;
the 21st is a 0694 flap member — see §Baseline). No SPRINT.md existed; S118 archived clean.

**2026-07-26 — user dispositions taken** (sprint shape structural-first; option 2 deferred
pending measurement; audit target `src/`; types audit R1–R5 all accepted). 0918/0919 filed
for the audit acceptances; 0920 filed for the tranche-B scope defect found during
verify-against-source.

**Process rules carried from the S118 Phase-7 findings, in force this sprint:**

- `git add -A` in a shared tree is banned; path-scoped staging is the rule.
- "Landed with zero consumers under static-only review" is **not landed** — require a
  consumer or an executing test before crediting foundation work. (The S116 foundation's two
  latent defects surfaced only when W3 wired the first consumer.) **This bears directly on
  tranche A**, which is foundation work by construction.
- Delegated `/review` (Codex) keeps its S118 shape: max three rounds per wave, ordered
  architecture → pins → mechanical; every delegated finding adjudicated before acceptance
  (S118's adjudication disproved two false claims); a delegated Blocker does not hold
  parallel design work.
- Stall handling: watchdog stall ⇒ verify tree clean ⇒ re-dispatch. S118 saw two stalls and
  four 529s with zero work lost but real wall-clock cost — build slack into wave estimates.
- STOP-and-FIXME (D2) and no-fix-without-repro (0765) both fired productively in S118 and
  stay armed.
- Phase 6a/6b combined for `/repl`, `/stdlib`, `/examples` is the recorded bounded-P6
  default.

## Outcome (Phase 7)

{Pending.}
