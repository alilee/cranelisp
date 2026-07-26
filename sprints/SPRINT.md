# Sprint 119: The Non-Concrete Release Contract, and the Typed Consume Funnel

**Status**: PHASE 2 ARCH REVIEW — `/arch` sign-off granted for Phase 3 on the restructured
scope; **two user dispositions owed** before dispatch (§Open items).

**Goal**: State and enforce the contract for releasing a value whose static type codegen
cannot fully see — the question the stratum has never answered and whose five faces produce
most of today's REDs — and make the wrong reference count unwritable at the consume funnel.

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

| Defect | Cells | Owner | Disposition (per §Architecture review) |
|---|---|---|---|
| 0907 (IO `Bind` release) | 7 | `/design`(backend) | Closed by Spine 1 |
| 0917 (protect-licence classification) | 3 | `/dev`(backend) | Closed in the Spine-1 window, distinct axis |
| 0867 (accessor synthesis gate) | 3 | `/dev`(typecheck) | Rider 1 — **after** the accessor disposition |
| 0863 (macro presentation transaction) | 2 | `/design`→`/dev`(src) | Conditional — §Open items ① |
| 0868 / 0869 (cache restoration) | 2 | `/dev`(src) | Rider 2; carry acceptable |
| 0916 (wild guarded RC write) | 1 | `/design`+`/dev`(backend) | Closed by Spine 1 (family-2 unsafety) |
| 0913 (lenient-view result root) | 1 | `/design`(typecheck) | **Contract face in Spine 1**; implementation a rider |
| 0694 (`launch_grid` + flap member) | 2 | `/qa` | Carried; bounded D1-experiment obligation only |

**Floor** (spines only): 21 → **10**. **Ceiling** (all riders): 21 → **2**.

---

## Architecture review (Phase 2)

`/arch` ruling 2026-07-26, dispatched under the user's directive that the sprint pursue the
option paper's outcomes — *simplification and control* — rather than discharge a FIXME
ledger, with the focus decision explicitly delegated. **Verdict: PASS WITH RESTRUCTURING.**
The Phase-1 draft's ingredients were right; its framing was a ledger. Restated below.

Actioned during the review: **FIXME 0920 resolved** — `ownership-stratum-options.md`
§2.3/§2.4/§6.3 re-scoped, index updated, FIXME deleted (commit `3232a061`).

### The outcome, made checkable

The stratum opens the sprint with **four places a defect can hide**: prose consume contracts,
undefined non-concrete release behaviour, the fabricated lenient-view type, and the unbalanced
protect licence. At close, none of the four remains unaddressed at contract level. Six gates:

| Gate | What must be true at close |
|---|---|
| **G1 — release-contract totality** | One normative contract section with a **five-face disposition table**, each face assigned exactly one of {canonical glue, I-CT-proven shallow dec, runtime-directed teardown, located refusal the user can act on}, and the producer side forbidden from fabricating concreteness. 0907×7 + 0917×3 + 0916×1 green. **Zero new refusals across the 16-program corpus named in FIXME 0903** — asserted, not assumed; this is the gate the S118 ruling failed. Plus the `f4_sudoku.clif::user::Grid.cells` static re-baseline witness and the 0907 trait-instance leak cell balancing. |
| **G2 — mechanism count stays one** | The S118 collapse is preserved: grep-zero fence green throughout, and **no fix this sprint adds a new emission licence arm**. The 0917 fix is a provenance *classification* correction (nullary `ConstrADT` is Fresh), not a new special case. A `/review` reject criterion. |
| **G3 — raw-handle representability** | Zero `consume_*` signatures take raw `i64` (36 call sites flipped); the pair's raw-`i64` heap-handle internal declarations fall from the measured 136 by tranche A's exact slice, before/after counts recorded in the change-set; the 83 extern shims byte-identical at the ABI. |
| **G4 — prose-contract elimination** | Shim ownership annotations single-sourced from the primitives declaration table (one derivation, unit-checked), and **each tranche carries a positive drop-bomb detection proof** — a deliberate leaked-on-the-floor test the debug bomb catches. Per the 0768 rule: an instrument is unverified until proven to detect. |
| **G5 — instrument truthfulness** | Unit-tier marginal helper landed plus `/qa`'s lens rule (assert a rate, a tally, or a marginal — never a point); 0890 re-derived; the option-2 uniform-vs-current number recorded with its method. |
| **G6 — 0889** | Exact-value pins read zero if tranche B lands; otherwise an explicit recorded carry (§Open items ②). |

### The focus ruling

**Sprint 119 is: state and enforce the non-concrete release contract; make the wrong count
unwritable at the consume funnel.**

**Spine 1 — control: the class contract.** Not three FIXMEs plus riders, but **one ruling
answering one question the stratum has never answered**: how is a value released when codegen
cannot see its full concrete type? Today five places hit this and each behaves differently:

| Face | Today's behaviour |
|---|---|
| Ctor templates | Ruled (§4.1 / I-CT) — sound |
| Synthetic accessors of generic / undeclared-field products | Silent leak |
| Generic trait-method instances | Silent leak **plus** the 0916 wild atomic write at payload+8 |
| IO's existential `Bind` | Hard refusal, no legal re-spelling |
| Typecheck lenient-view result root (0913) | A **fabricated** `ConcreteType::Int` that silently unhooks glue |

0913's placement in the Phase-1 draft's rider batch was precisely the too-narrow framing the
user objected to — it is a producer-side face of the same contract and is pulled up into
Spine 1. The window is `/design`(backend) with `/design`(typecheck) co-owning the producer
face (the contract binds producers: no fabricated concreteness), and `/arch` on the IO
tri-context seam — seeded by int's `bootstrap.rs:767-783`, torn down by
`cranelisp-intrinsics::free_io_branches`, refused by backend's `drop_glue.rs:497-505`. **0917
rides the same window as a distinct named axis** (concrete types; protect-licence
classification), not folded into the class. 0891's re-land is a paste after the ruling;
0915 and 0906 ride as drafted.

**Spine 2 — simplification: tranche A, then the re-scoped tranche B.** Tranche A as approved,
under the consumer-proof discipline of G4. **Tranche B is re-scoped** (0920 resolved): it is
the **int-side macro-turn boundary** — `src/marshal.rs` (732 lines) plus
`src/expander.rs::invoke_clause` — a third typed surface consuming the intrinsics-public
`Owned`/`Borrowed` vocabulary that tranche A forces public anyway (the `consume_*` fns are
`pub`, primitives already depends on intrinsics, and `src/` links it; `/arch` verified no
`consume_*` call exists in `src/` today, so B *introduces* the discipline there).
`/design`(int) rules the protocol first, per 0889's own precondition. No `cranelisp-types`
delta.

**Option 2 deferral — CONFIRMED, with the reasoning made explicit.** `/arch` tested whether
uniform emission is the dominant simplification lever by classifying the 21 REDs against it:
it would dissolve **at most 0917×3** (protect-licence arithmetic). The other eighteen are glue
identity and derivation (0907/0916/0913 — uniform emission still has to know *what to call* on
a non-concrete value), typecheck gates (0867), int transactions (0863), cache (0868/0869), and
the heisenbug (0694). Option 2's value is **prophylactic against future special-case defects,
not curative of the present baseline**, and it carries the unmeasured atomic-traffic risk the
S94 floor ruling flagged at ~10× on parallel RC-heavy workloads. The measurement gate stays in
scope, report-only, sequenced **after** Track-1 implementation lands — a measurement taken
against emission we are about to change is not decision-grade for S120.

**The release class is not dissolved by any lever.** No option makes it go away; it holds the
sprint's only memory-unsafety and its largest RED block. It is a co-spine, not a symptom.

### Sequencing

1. **Phase 3**: the Spine-1 co-ruling window and the tranche-A contract design run together
   (both design-only). Binding on the co-ruling: **measure before binding** — the held-back
   0903 gate plus the corpus run is executed *inside* the design window; a ruling that has not
   survived the 16-program corpus does not bind. The S118 §4.1 falsification is the precedent
   and must not repeat.
2. **Implementation order**: Spine-1 backend/typecheck waves first (largest control payload,
   closes the memory-unsafety, 0891's paste rides) → tranche A → **0867 rider** → tranche
   B-int (protocol ruling, then dev) → the 0869/0868 schema window (0898 and 0748/R3 riding) →
   0913 implementation → 0914 → 0863 conditional.
3. **Must-not-interleave** — each is a `/review` reject or a dispatch constraint:
   - **Spine-1 backend implementation and tranche-A signature churn never share a wave.** Each
     needs its own byte-identical instrument re-run for drift to stay attributable.
   - **0867 lands only after the contract's accessor-family disposition is ruled.** Fixing
     0867 mints accessors for every sum type and distinct-name product — it *widens 0903
     family-1's surface*. Landing it first manufactures new members of an unruled leak class.
     The Phase-1 draft missed this interaction and had 0867 as the cheapest first rider.
   - **0863 never interleaves with tranche B-int** — both rework the same `src/` macro-turn
     seams. 0863 runs only after B-int lands or is dropped.
   - **Exactly one schema window** (23→24, 0869's implementing change-set). No other track is
     authorized a schema delta; if the Spine-1 IO ruling discovers a persistence need it
     returns to `/arch` rather than taking the window.
   - **Option-2 adoption happens under no capacity outcome this sprint.** The measurement is
     the deliverable.

### What defers, and why

Deferred by `/arch` ruling, not by user decision: the **option-4 spike** → S120 (with tranche
B in scope there is no discretionary-spike capacity, and its reach shrinks if option 2 is
adopted on the S120 measurement). Also: **tranches C/D** → S120; **option-2 adoption** → S120
on the number; **Track 2 items 5–6 and the types-audit R4 compaction** drop before anything
structural does; **0918/0919 stay** (cheap, `/arch`-owned — facade truth is control).
Everything in §Explicitly out of scope stands.

**0912 explicitly does not gate this sprint** — `/arch` decoupled it from the Spine-1 window,
against the Phase-1 draft. The contract must cover the generic half regardless of how the
undeclared-field question is answered, so the ruling's *shape* does not depend on it. If the
user later rules declaration-time rejection, one source spelling stops feeding family 1 and a
contract arm goes dead — removed then. `/spec` frames it on its own schedule. The escalation
stack (0859 / 0463 / 0050 / 0553 / 0821 / 0708) likewise gates nothing; dispose at `/sprint`'s
cadence.

### Risk

- **Principle 8 (interim architecture)**: none introduced. The typed layer is target-state —
  the `i64` extern shim is the permanent ABI boundary, not a bridge — and tranche boundaries
  are whole seam families, so no seam is left half-typed. The A-landed / C-pending interim is
  module-aligned and acceptable. The real hazard is S118's: **a ruling or a typed layer landing
  with zero executing consumers.** Mitigations are structural here — measure-before-binding for
  the contract; the eleven acceptance REDs are the contract's executing consumers; the
  per-tranche drop-bomb detection proof is the typed layer's.
- **Public API**: `cranelisp-intrinsics` gains `Owned`/`Borrowed` and changed `consume_*`
  signatures — approved in principle, exact `public-api.txt` diff at the Phase-3 exit gate;
  extern names and ABI byte-identical; primitives delta confined to its two shims if `pub`.
  Backend and typecheck expected zero-delta for Spine 1 (glue classification and the lenient
  view are internal). Any new extern or types-crate need returns to `/arch`. **No
  `cranelisp-types` delta anywhere in approved scope.**
- **`CACHE_SCHEMA_VERSION`**: stays 23 unless rider 2 lands; 23→24 belongs to 0869's
  implementing change-set alone, with 0898 and 0748/R3 riding that window.
- **Honest failure mode**: the co-ruling window is the long pole and its predecessor was
  falsified once by measurement. **If a unified five-face contract does not converge in one
  window, the fallback is severable rulings in fixed order** — 0917 first (narrow, independent,
  3 REDs), then IO routing (7 REDs), then the accessor and trait families — rather than holding
  all eleven REDs hostage to a single statement. The corpus gate applies to each severed piece
  identically. For option 2 nothing irreversible exists to commit; the measurement must show
  the uniform-vs-current cost on exemplar and suite, with method, before S120 may adopt.

**Sign-off**: granted for Phase 3 on this restructured scope. The Phase-3 exit gate takes the
intrinsics `public-api.txt` diff and the tranche-A shim-fact design.

---

## Open items — two user dispositions owed before Phase 3 dispatch

`/arch` collapsed the Phase-1 draft's three open items plus the paper's five queued decisions
to these two. Both are real choices with consequences.

**① 0863's third deferral (METHOD §2.4).** Its second deferral is spent (S117→S118,
user-approved). Under the restructured sequencing 0863 is last — it cannot interleave with
tranche B-int, which reworks the same `src/` macro-turn seams. Either **sign off a conditional
third deferral** (0863 executes late-sprint only if the int surface clears with capacity
remaining, else it is S120's first item), or **promote it above tranche B-int**, accepting that
0889 then likely carries instead. `/arch` recommends signing the conditional: 0863's design is
READY and does not decay, while B-int is this sprint's structural commitment. Two REDs either
way.

**② Ratify the tranche-B re-scope consequence.** B is materially larger than the paper priced
— 732 lines plus the expander protocol plus a `/design`(int) ruling, against 339 lines inside
the pair — and it is now **the first structural item to drop if capacity binds**. That makes
the Phase-1 commitment "0889 lands this sprint" **best-effort rather than guaranteed**. If you
want 0889 guaranteed, tranche B must explicitly displace Track-2 riders 2–5 (the cache schema
window, 0913's implementation, 0914). `/arch` recommends accepting best-effort: the leak is
compile-time-bounded, exactly pinned, and does not grow with runtime.

Lower-priority escalations, disposable at any point and gating nothing: **0859** (`/qa`,
target_sprint 118 undischarged); **0463** (`/examples`, deferred 3×, trigger still unmet);
**0050** (`/int`, ~50-sprint carry whose stated blocker expired at S106); **0553**
(`/typecheck`, deferred to S114); **0821** fork (c) (`/arch` + user); **0708** (spec cascade
owed; user ruled Reading A-structural 2026-07-21). **0912** is a live normative question for
`/spec` to frame at whatever point suits you — it does not gate this sprint.

---

## Scope

### Spine 1 — the non-concrete release contract

`/design`(backend) leads; `/design`(typecheck) co-owns the producer face; `/arch` on the IO
tri-context seam. One ruling, five faces, measured before it binds.

Carries: **0903** (re-rule §4.1 over the whole measured class; the held-back gate and three
negative cells re-land as a paste), **0907** (the IO existential face; three candidate
directions are on the file, one of which — admission exclusion — restores the silent leak and
must be weighed as such), **0916** (memory-unsafe wild write; title correction owed),
**0913** (the fabricated-concreteness producer face), **0917** (distinct axis: provenance
classification, not a new licence arm), **0891** (paste after the ruling), **0915** (backend
frame composition + the int presentation rider), **0906** (nullary-skip guard fold, with a
scoped golden re-baseline — not byte-identical; block creation order swaps CLIF numbering).

**Acceptance**: gates G1 and G2 above.

### Spine 2 — the typed consume funnel

- **Tranche A** — `cranelisp-intrinsics::drop` plus the 36 primitives `consume_*` call sites
  newtyped. `Owned` is `#[must_use]`, no `Copy`/`Clone`, debug-profile drop-bomb; `Borrowed` is
  `Copy`, cannot be stored, and `.to_owned()` is the single home of `rc_inc`. The C-ABI/JIT
  surface is untouched — `extern "C"` keeps `i64`; the typed layer begins at the shim.
  Shim-fact single-sourcing from the declaration table is **part of tranche A's design**, not a
  follow-on: it is the §2.2 false-confidence mitigation and the trusted base narrows to it.
- **Tranche B-int** — `src/marshal.rs` + `src/expander.rs::invoke_clause`, consuming the
  intrinsics-public vocabulary. `/design`(int) rules the ownership protocol before any `/dev`
  dispatch. This is the 0889 recovery vehicle. The naive-release path is warned against by the
  0638 interior-alias history; the point of the tranche is that the danger *is* the miscounting
  typed handles remove.
- **Option 3 generalization** — per-crate unit-tier marginal helper; `/qa`'s lens rule; the
  cold/warm cache axis (0890); threshold-cell retirement; decision 5's normative-form proposal.
- **The option-2 measurement gate** — uniform-vs-current emission on exemplar and suite via the
  marginal harness's twin-control shape, **after** Spine-1 implementation. Report only.

**Acceptance**: gates G3, G4, G5, G6 — and the S118 instrument set re-running
**byte-identically** across the tranche churn, which is the acceptance criterion for churn
masking behaviour change, not a nicety.

### Riders, in drop order (deepest last)

1. **0867** — `/dev`(typecheck), `adt.rs:136,241-245`. **Gated on the accessor-family
   disposition.** 3 REDs. Honour the `/stdlib` blast-radius rider (26 symbols, cross-module
   head/rest contest).
2. **0869 + 0868** — `/dev`(src) + types. The carrier ruling is in force
   (`design/arch/trait-impl-cache-carrier.md`); `CACHE_SCHEMA_VERSION` 23→24 in the implementing
   change-set only; re-point the two hand-rolled `impl$` mint sites (`traits/dispatch.rs:143`,
   `traits/impl_check.rs:421`). 2 REDs, and the window **0898** and **0748/R3** ride.
3. **0913 implementation** — after its contract face is ruled in Spine 1. Must **not** be closed
   by pinning annotations in tests or docs.
4. **0914** — `/design`(int): move `/mem`'s counter window past `release_program_result()`.
5. **0918 / 0919** — `/arch`: types-audit R1 and the R2+R4+R5 facade-truth pass. Kept because
   facade truth is control; R4's compaction drops first if capacity binds.
6. **Platform and testing riders** — 0870, 0874, 0873 (design approved, `/arch` gate passed),
   0871, 0900, 0798, 0799.
7. **0863** — conditional, last, never interleaved with tranche B-int. §Open items ①.

### Track C — carried, one bounded obligation

0694 / 0604 / 0818 remain open. This sprint does **not** attempt the heisenbug. It owes the
S116 D1 discriminating experiment and a recorded re-measurement of the opening flap datum in
§Baseline. 0859's disposition rides here.

### Explicitly out of scope

| Item | Rationale | Target |
|---|---|---|
| Option-4 emission-audit spike | `/arch` ruling — no discretionary-spike capacity with tranche B in scope; reach shrinks if option 2 is adopted | S120 |
| Option-1 tranches C and D | Capacity — A + B-int is already the structural commitment | S120 |
| Option 2 **adoption** (its measurement is in scope) | Re-sequences `ownership-inference.md`; prophylactic not curative; unmeasured atomic-traffic risk | S120, on the number |
| Tracks D/E beyond the named riders | Descoped by the user at S118 close; groundwork stays banked | S120+ |
| 0604 / 0818 root cause | Three-sprint heisenbug; the discriminating experiment is the prerequisite and is in scope | S120 |
| `--release` tier, LLVM backend | Phase H sequence — gated behind the memory model | post-S120 |

---

## Verify-against-source findings (METHOD §3.3, performed 2026-07-26)

Every scope carry was verified against its `refers_to` source as the binding first act. All
central claims hold. Four corrections must ride the dispatch prompts so they do not propagate:

1. **0917's cited locus is wrong.** `protect_return_value` lives at
   `crates/cranelisp-backend/src/compiler/rc_emission.rs:156` (in `impl FnCompiler`), **not**
   `fn_compiler.rs`; `git log -S` shows it was never there. Call sites:
   `match_codegen.rs:322,574`, `control_flow/lambda.rs:554`, `control_flow/launch.rs:261`.
2. **0916's title is stale** ("loses TCO"). The body already carries `/qa`'s falsification —
   TCO is intact (`jump block1` in both variants); the mechanism is a wild guarded RC write on
   a scalar at the `NULLARY_TAG_THRESHOLD` n=1023/1024 boundary. Correct in the fixing window.
3. **0863's frontmatter is stale** (`status: deferred`, `target_sprint: 118`). Its design is
   verified READY (`design/int/s117-conformance-recovery.md` §6.5, `/arch` ruling 11, two
   deltas the implementing wave must absorb) and its 0745 blocker is **discharged**
   (`fc3375f9..16a26408`).
4. **0907's own severity block understates the breakage** — the `/stdlib` appendix reconciles
   it to two named modules (`core.io` and its parent `core`), matching the measured baseline.

Also confirmed and load-bearing: `CACHE_SCHEMA_VERSION` = 23 at
`crates/cranelisp-backend/src/cache/mod.rs:375`, window unspent; nothing of 0869 has landed
(zero hits for `WrittenTraitImpl`, `written_trait_impls`, `enrol_written_trait_impl`,
`trait_impl_key`); 0903's gate is absent from the tree (`fn_compiler.rs:1288` still type-keyed,
rustdoc at `:1230-1261` saying so deliberately); 0867's seam is exactly as described
(`adt.rs:136` computes `is_product`, `:241-245` gates synthesis on it over `ctor_infos[0]`
only). Tranche A sizing: **83** `extern "C" fn` in the pair (exact match to the paper's ~83),
**136** non-extern `i64`-taking declarations, **36** `consume_*` call sites.

---

## FIXME debt

56 open + 9 deferred at open; 0918/0919 filed at Phase 1; **0920 filed and resolved within
Phase 2**. The table lists those in scope or requiring disposition. Full inventory:
`design/arch/fixmes/`.

| FIXME | Target skill | Status | Disposition |
|---|---|---|---|
| 0903 | /design (backend) | open | Spine 1 — the co-ruling |
| 0907 | /design (backend) | open | Spine 1 — IO existential face |
| 0916 | /design + /dev (backend) | open | Spine 1 — family-2 unsafety; title correction owed |
| 0913 | /design (typecheck) | open | **Spine 1 contract face**; implementation rider 3 |
| 0917 | /dev (backend) | open | Spine 1, distinct axis; locus correction owed |
| 0891 | /dev (backend) | deferred, blocked_on 0903 | Spine 1 — paste after the ruling |
| 0915 | /design (backend) + /design (int) | open | Spine 1 |
| 0906 | /dev (backend) | open | Spine 1 rider — scoped golden re-baseline |
| 0889 | /design (int) | open | Spine 2 tranche B-int — the recovery target |
| 0890 | /qa | open | Spine 2 option-3 — cold/warm axis |
| 0920 | /arch | **RESOLVED** `3232a061` | Tranche B re-scoped onto the int marshal boundary |
| 0867 | /dev (typecheck) | open | Rider 1 — gated on the accessor disposition |
| 0869, 0868 | /dev (src) + types | open | Rider 2 — schema 23→24 |
| 0898, 0748 | /arch | deferred → S119 / open | Ride rider 2's schema window |
| 0914 | /design (int) | open | Rider 4 |
| 0918, 0919 | /arch | open | Rider 5 — types audit R1 / R2+R4+R5 |
| 0870, 0874, 0871, 0873 | /dev + /design (platform) | open | Rider 6 |
| 0900, 0798, 0799 | /testing | open / deferred ×2 | Rider 6 |
| 0863 | /dev (src) | deferred ×2 | Rider 7, conditional — **§Open items ①** |
| 0694, 0604, 0818 | /qa | open | Track C — D1 experiment only |
| 0859 | /qa | deferred, target 118 | Escalation, gates nothing |
| 0912 | /spec | open | **Decoupled by `/arch`** — does not gate this sprint |
| 0821, 0708 | /arch, /spec | open | Escalations, gate nothing |
| 0050, 0553, 0463 | /int, /typecheck, /examples | deferred | Escalations, gate nothing |
| 0765, 0764 | /dev, /review | open | Process rules — fold into dispatch discipline |

---

## Skill plans (Phase 3)

{Pending — dispatch blocked on §Open items ① and ②.}

Planned Phase-3 dispatches once unblocked: `/design`(backend) + `/design`(typecheck) on the
Spine-1 co-ruling (measure-before-binding: the corpus run executes inside the window);
`/design`(runtime pair) on the tranche-A contract including shim-fact single-sourcing;
`/design`(int) on the tranche B-int ownership protocol; `/qa` on the test plan, the option-3
normative-form proposal (paper decision 5) and 0890; `/arch` on the IO tri-context seam and the
Phase-3 exit gate (intrinsics `public-api.txt` diff + the tranche-A shim-fact design).

## Waves (Phase 4)

{Pending.}

## Dispatch log

| Wave | Agent | Surface | Model | Effort | Non-default reason |
|---|---|---|---|---|---|
| P1 | Explore ×4 | read-only carry/FIXME/audit inventory + source verification | session | — | Read-only fan-out, not a role dispatch |
| P2 | /arch | sprint scope (restructuring ruling) | fable (shim) | xhigh | — |

## Notes

**2026-07-26 — Phase 1 opened.** Baseline measured at `5520186d` (21 REDs, all attributed; the
21st is a 0694 flap member). No SPRINT.md existed; S118 archived clean.

**2026-07-26 — user dispositions.** Sprint shape structural-first; option 2 deferred pending
measurement; audit target `src/`; types audit R1–R5 all accepted (filed 0918/0919; R3 rides
0748). 0920 filed for the tranche-B scope defect found during verify-against-source.

**2026-07-26 — user redirection.** *"We are taking the items too narrowly/strictly. I want the
outcomes the paper is searching for — simplification and control."* Focus decision delegated to
`/arch`; anything not serving those outcomes authorised for deferral. `/arch` restructured the
sprint from a ledger into one outcome with two spines, pulled 0913 up from rider to contract
face, gated 0867 behind the accessor disposition, resolved 0920 by re-scoping tranche B onto
the int marshal boundary, deferred the option-4 spike by ruling, and decoupled 0912.

**Process rules carried from the S118 Phase-7 findings, in force this sprint:**

- `git add -A` in a shared tree is banned; path-scoped staging is the rule.
- "Landed with zero consumers under static-only review" is **not landed**. This bears directly
  on both spines — hence measure-before-binding for the contract and a per-tranche drop-bomb
  detection proof for the typed layer.
- Delegated `/review` (Codex) keeps its S118 shape: max three rounds per wave, ordered
  architecture → pins → mechanical; every delegated finding adjudicated before acceptance; a
  delegated Blocker does not hold parallel design work.
- Stall handling: watchdog stall ⇒ verify tree clean ⇒ re-dispatch. Build slack into estimates.
- STOP-and-FIXME (D2) and no-fix-without-repro (0765) stay armed.
- Phase 6a/6b combined for `/repl`, `/stdlib`, `/examples` is the recorded bounded-P6 default.

## Outcome (Phase 7)

{Pending.}
