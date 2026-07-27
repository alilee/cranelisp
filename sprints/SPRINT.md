# Sprint 119: The Non-Concrete Release Contract, and the Typed Consume Funnel

**Status**: PHASE 5 LANGUAGE (ACTIVE) — Phase 3 closed with `/arch` **PASS WITH CONDITIONS**
(§Phase-3 exit gate); waves organized below. Phase 5 stage 1 (`/testing`) not yet dispatched.

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

## Open items — DISPOSED (user, 2026-07-26)

`/arch` collapsed the Phase-1 draft's three open items plus the paper's five queued decisions
to two. The user took `/arch`'s recommendation on both.

**① 0863 — CONDITIONAL THIRD DEFERRAL SIGNED OFF (METHOD §2.4).** Its second deferral was
spent (S117→S118). Under the restructured sequencing 0863 is last and cannot interleave with
tranche B-int, which reworks the same `src/` macro-turn seams. **It executes late-sprint only
if the int surface clears with capacity remaining; otherwise it is S120's first item and needs
no further sign-off.** Rationale on the record: 0863's design is READY and does not decay,
while tranche B-int is this sprint's structural commitment. Two REDs either way.

**② Tranche-B re-scope consequence — RATIFIED.** Tranche B is materially larger than the paper
priced (732 lines plus the expander protocol plus a `/design`(int) ruling, against 339 lines
inside the pair) and is **the first structural item to drop if capacity binds**. The Phase-1
commitment "0889 lands this sprint" is therefore **best-effort, not guaranteed** — accepted on
the record, on the grounds that the leak is compile-time-bounded, exactly pinned, and does not
grow with runtime. Tranche B does **not** displace riders 2–5.

**③ FIXME 0859 — `/qa` discharged it as disposition 2 and returned it to you (Phase 3).** Its
finding: materialisation erases the production RC distinction at the current boundary, so **no
witness can exist** without manufacturing exactly the surface the FIXME itself forbids.
`/qa` recommends accepting R-2 on transfer units plus body guards plus the nine S117 witnesses,
**with a named revival trigger** — increment II reuse tokens, or option-2 adoption. Tranche A's
derivation narrows 0859's surface by one class but does not discharge it: its residual is a
production-artifact witness for `ProjectionOf(0)` on the *inline* `vec-get` row, and inline rows
have no shim for the derivation to touch. No action needed before Phase 5; disposition at your
convenience.

Lower-priority escalations, disposable at any point and gating nothing: **0463** (`/examples`, deferred 3×, trigger still unmet);
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
| 0889 | /dev (int) | ruled P3 | Spine 2 tranche B-int — protocol landed, retargeted to `/dev` |
| 0920 | /arch | **RESOLVED** `3232a061` | Tranche B re-scoped onto the int marshal boundary |
| 0921 | /design (runtime pair) | open, filed P3 | Host↔JIT transfer form; **plus a confirmed defect** — `consume_sexp` has no `TAG_SEXP_ANNOTATED` arm, leaking both heap fields of every annotated cell |
| 0922 | /arch | **RESOLVED** at the gate | Rule-0 pin ruled at int's clause-preparation seam; absorbed by 0927 |
| 0923 | /arch | **RESOLVED** at the gate | IO tri-context seam approved; R17/R18 register rows added |
| 0925 | /arch | **RESOLVED** at the gate | Two schema windows granted, two owners |
| 0924 | /design (typecheck) | ruled P3, open | The monomorphisation obligation — W4; **gates 0916 and rider 0867** |
| 0926 | /qa | open, filed P3 | Slot-gate cell, the sum-arm corpus extension repro, `/stdlib`'s bare-alias contest cell |
| 0927 | /design (int) | open, filed at the gate | Absorb the Rule-0 enforcement ruling + D4's fence |
| 0928 | /design (runtime pair) | open, filed at the gate | Gate outcomes: `free_io_node` classification, the three tranche-A rulings, 0921's disposition |
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

Dispatched 2026-07-26 in three rounds. `/dev` is not invoked in Phase 3.

**Round 1 (concurrent — distinct directories, no commits, cargo reserved to `/design`(backend)
per the one-agent-one-test-run rule):**

### /design (cranelisp-backend) — Spine 1, the non-concrete release contract

- **Task**: author the five-face disposition table as a normative contract section, and
  execute the measure-before-binding corpus run inside the window.
- **Design refs**: `design/backend/transitive-drop-glue.md` §4.1/§10/§11; FIXMEs 0903, 0907,
  0916, 0917, 0891, 0915, 0906; `drop_glue.rs:497-505`; `bootstrap.rs:767-783`;
  `rc_emission.rs:156`.
- **Acceptance**: G1 + G2. The ruling does not bind until it survives the 16-program corpus.
  Severable-fallback order stated if the unified contract does not converge.

### /design (cranelisp-primitives + cranelisp-intrinsics) — Spine 2, tranche A

- **Task**: the `Owned`/`Borrowed` contract over the drop/consume funnel, with shim-fact
  single-sourcing from the declaration table as part of the design, not a follow-on.
- **Design refs**: `design/arch/ownership-stratum-options.md` §2.1–§2.4 (as amended
  `3232a061`); the S117 Vec-of-String boundary; platform's `CLOwned<T>`.
- **Acceptance**: G3 + G4, including the per-tranche drop-bomb detection proof.

### /design (int / `src/`) — Spine 2, tranche B-int and the 0889 protocol

- **Task**: rule the macro-turn ownership protocol before any `/dev` dispatch, per 0889's own
  precondition; carry 0914 and the 0915 int presentation rider.
- **Design refs**: FIXMEs 0889, 0914, 0915; `src/marshal.rs`; `src/expander.rs::invoke_clause`;
  the 0638 interior-alias history; `design/int/result-owner.md`.
- **Acceptance**: G6; protocol stated before implementation; no `cranelisp-types` delta.

### /qa — test plan

- **Task**: `tests/plan/s119-test-plan.md`; the option-3 normative-form proposal (paper
  decision 5); 0890 re-derivation; the Track-C D1 discriminating experiment; the corpus gate's
  assertion form.
- **Acceptance**: G5; every gate G1–G6 has a named cell or a named measurement.

**Round 1 delivered 2026-07-26.** Four artefacts:
`design/backend/non-concrete-release-contract.md` (the ruling),
`design/runtime/s119-typed-consume-funnel.md` (tranche A),
`design/int/macro-turn-ownership.md` (the 0889 protocol),
`tests/plan/s119-test-plan.md`. Outcomes below.

**Round 2 (dispatched)**: `/design`(typecheck) on the producer face — 0913's lenient view and
the new **0924** monomorphisation obligation — against the landed contract.

**Round 3**: `/arch` Phase-3 exit gate — FIXMEs **0922** and **0923**, the intrinsics
`public-api.txt` diff, the tranche-A shim-fact design, the two new `safety-invariants.md`
register rows (R-1, R-2), and the `launch.rs:452` dispensation.

---

### Round-1 outcome — the finding that reshapes the sprint

**FIXME 0903 family 1 is memory-unsafe, not a silent leak.** `/design`(backend) reduced it to
four lines with no trait and no higher-kinded type:

```lisp
(deftype (Bx a) [:a v])
(defn get [b] (v b))
(defn main [] (Pure (get (Bx 1024))))
```

`1023` exits 255 correctly; **`1024` and `5000` SIGSEGV** — the same `NULLARY_TAG_THRESHOLD`
boundary `/qa` measured for 0916, on a different family. CLIF shows one frame carrying both
faces: an `atomic_rmw add [field+8]` on a raw scalar, and a field-discharge-free `dealloc` of
`self`. **The repro is currently unguarded** — `/testing` authors it as the cheapest
memory-safety cell in the class.

Worse, **the ctor template's own I-CT licence carries the identical shape** (3,108 licences on
residual params). I-CT proves the *count* balances; it is silent on whether the word is a
reference at all. §4.1's rejection of "delete the pair" rested on behaviour-identity with
pre-migration HEAD — **falsified**.

**The frame-key falsification reproduced exactly at S119 HEAD**: `spec_*` 893 run, 8 → 24
failed, **+16 hard refusals**, one sprint later on a moved tree. The ruled narrowing is
confirmed unlandable alone. Measure-before-binding earned its place.

### The contract as ruled

Four rules, then a total five-face table. **R-1**: a residual type variable has no heap
category; the threshold guard discriminates tags from pointers, **never scalars from
pointers**. **R-2**: no fabricated concreteness — binding on producers in both crates, with
three measured instances (backend's `Err ⇒ Mixed`, backend's type-keyed shallow-dec arm,
typecheck's `lenient_from_expr → ConcreteType::Int`). **R-3**: a non-concrete frame is not a
legal codegen target — *proved, not preferred*: counting the residual word SIGSEGVs on scalars,
not counting it use-after-frees on a duplicating arm (`(Pair x x)`), and runtime discovery is
impossible without R15. **Monomorphisation is the only sound disposition.** **R-4**: the
refusal must be actionable, folding 0915 in as the quality bar.

| Face | Disposition | Closes |
|---|---|---|
| Ctor template param | **Canonical glue at the caller** — the pair *deletes* under new invariant I-CT′ | 0891 |
| Synthetic accessor (F1) | Canonical glue after monomorphisation | 0903 fam 1 |
| Generic trait-method instance (F2) | Canonical glue after monomorphisation | 0903 fam 2, **0916** |
| IO existential `Bind` | **Runtime-directed teardown** — intrinsics tag-walker; backend owns only `Pure`'s payload | **0907 ×7** |
| Lenient-view result root | Canonical glue after the producer stops fabricating | **0913** |

0917 sits deliberately **outside** the table — concrete types throughout; folding it in was the
framing error `/arch` corrected.

**G2 holds.** Retired: §4.1's exception, I-CT and its standing obligation, the `Err ⇒ Mixed`
fabrication, the type-keyed release arm, two monomorphisation exemptions. Added: one intrinsics
entry point (a split of an existing body) and one lattice point. **No new emission licence
arm.** Seven `/review` reject criteria recorded.

### The scheduling consequence

**Ten of the eleven Spine-1 REDs — 0917×3 + 0907×7 — close with backend-only changes.** 0916
is producer-gated on FIXME 0924 (monomorphisation) and does **not** ride the backend wave. The
narrow in-frame alternative was rejected because R-3 proves it converts a SIGSEGV into a
use-after-free.

The backend flip is **census-gated, not review-gated**: the fabricating arm stays, instrumented
in production form per the 0768 rule, until measured traffic reads zero. The arm is the gate on
its own removal.

Implementation order: 0917 (backend only, 3 REDs) → face 4 IO glue (backend, 7 REDs) → face 1
ctor-template retirement (backend, 0 REDs, −2,216 census A and −3,108 census B) → faces 2+3
monomorphisation (typecheck producer + backend, 0916) → face 5 lenient view (typecheck, 0913).

### Tranche A as designed

New `pub mod handle` in `cranelisp-intrinsics`: `Owned` (`repr(transparent)`, `#[must_use]`, no
`Copy`/`Clone`, debug drop bomb with a `!thread::panicking()` clause) and `Borrowed<'a>`
(`Copy`, **lifetime-branded**, no discharge operation at all). Eight operations, closed set.
The **trusted base is counted, not asserted**: 4 definitions + 1 macro generator + 6
hand-written shim sites, with a structural grep gate.

**The load-bearing finding: the shim-fact derivation axis is `ParamFlow`, never `Mode`.** The
S102 CS-B split declares only-read heap params (`str-eq`, `str-len`, the `?`-predicates,
`vec-len`) as `Mode::Borrowed` while the Decision-24 ABI still consumes. A `Mode`-driven
derivation would flip five rows and **silently delete five decs** — exactly the
plausible-but-wrong single-sourcing a hand-written second assertion would have hidden.

The detection proof is a **triplet**, not a row: positive (leaked handle panics), no-false-positive
(discharged fixture stays silent), and survivable-under-unrelated-unwind (proves the
`thread::panicking()` clause and fails on deleting the clause alone).

**G3's count was corrected as unfalsifiable-as-written**: the 136 is syntactic; 30 are
`ring0.rs` scalar arithmetic that never flips, and 3 flip their *return* while still grepping
as `i64`-taking. Ruled: record both. Semantic baseline **N_heap = 103**; tranche A's exact
slice is **42 declarations**, giving N_heap 103 → 61 and syntactic 136 → ~100. The 36
`consume_*` sites decompose to **29 production** call sites plus doc/`use` mentions.

Public-API delta: `cranelisp-intrinsics` additive (`handle` module, both types, 8 methods) plus
**10 changed `consume_*`/`dec_shallow_io` signatures**. `cranelisp-primitives`: **zero delta**
— both generated shims are `pub(crate)`. ABI byte-identical. No `cranelisp-types` delta.

### The 0889 protocol

Verified first: `invoke_clause` (`src/expander.rs:512-549`) is the **only** production caller of
`src/marshal.rs`. Blast radius is one function and one `pub(crate)` module.

Ruled: the macro-clause ABI **declares** its ownership (Rule 0); argument trees are
single-owner and **transferred** — crossing the ABI *is* the discharge, so
`protect_marshalled_cell`, its four call sites, and `marshal::rc_inc` are **deleted**; the
result tree is observed through a `Borrowed` then discharged once via `consume_sexp`.

On the 0638 trap: the cure is **not** "release the args at turn exit with better counting" —
that keeps two owners across the call. It is "do not retain the args at all." And Rule 2 is
**not** a revert to pre-0638 top-only protection: that state was *asymmetric* (top at RC 2,
interiors at RC 1), and the asymmetry is what 0638 pinned. Rule 2 produces the uniform
single-owner state the S114 negative-control twin proved correct — which neither the old nor
the current code has ever had.

Arena/epoch **rejected** on five grounds, the sharpest being that escape is not "no": `trace`
cells land in an int ring buffer and lenient-eval sparks allocate off-thread, so wholesale
reclaim would trade a leak class for a use-after-free class — in the sprint chartered to make
instruments truthful. Retained as fallback only under a stated entry condition.

**0863 orthogonality is now proved, not hoped**: 0863 reworks clause *preparation/publication*,
B-int reworks clause *invocation*, and **Rule 7** (no marshal handle outlives its invocation
frame) is what keeps them disjoint. Had the protocol released "at turn exit", *turn* would have
acquired two meanings mid-sprint exactly where 0863 moves the boundary.

### `/qa`'s plan and its two returns

`tests/plan/s119-test-plan.md` §2 is a gate→instrument map; §11.2 makes "gate asserted in
prose, instrument missing" itself a close-gate failure. The G1 corpus gate is three-layered —
the 16 programs enumerated by name, a per-program result table that the ruling does not bind
without, and a standing assertion that every Spine-1 change-set records a focused manifest run
(missing record = `/review` REJECT), plus a corpus **extension clause** after rider 1 because
0867 widens family 1. G2 gets a mechanical **emission-licence census cell**. An **IO-Bind
balancing marginal guard** fences 0907 against being "fixed" by admission-exclusion.

**Decision 5 proposed and it does NOT change the certification split's meaning — no user
arbitration required.** Every e2e balance cell becomes either a marginal pair or a degenerate
absolute whose ambient-zero premise is continuously executed by a named GREEN control in the
same binary; thresholds banned. Exactly one threshold cell exists at baseline
(`…residue_at_most_1400`), retired after 0917's fix.

**FIXME 0859 discharged as disposition 2 and returned to the user** (see §Open items ③).

### Corrections to this plan from Round 1

- **The 0890 row in §FIXME debt was stale** — the FIXME was actioned and deleted at S118
  pre-gate, whose §11.3 *inverted* its premise (warm cache-hit children carry zero ambient).
  Corrected below; G5's residue is planned as a warmed-pair harness mode with its own 0768
  capability cells.
- **Baseline convention restated**: **20 stable REDs + 1 named-flap member**, which never folds
  into the exact scalar. `/design`(backend)'s own run measured 20 with the flap member green —
  consistent with its class, and now a second datum for Track C.
- **0916's title corrected in-file**; the stale slug was deliberately retained to avoid a
  rename race with the concurrent agents, and is flagged as stale.
- **One out-of-pair compile break**: `crates/cranelisp-backend/src/compiler/control_flow/launch.rs:452`
  (inside that file's `#[cfg(test)] mod tests`) calls `consume_closure` with a raw `i64` and
  **will not compile after tranche A CS-2**. Needs a one-line fix from `/dev`(backend) or an
  explicit dispensation — narrow deployment forbids the runtime-pair designer ruling it.
  `/arch` takes this at the exit gate.
- **`src/marshal.rs:316` carries its own `pub fn rc_inc` doing a non-atomic `*rc_ptr += 1`** —
  the exact hazard closed inside the pair at S85, still live on the int side. Deleted by the
  0889 protocol.

## Phase-3 exit gate — `/arch`, 2026-07-26

**VERDICT: PASS WITH CONDITIONS.** Phase 3 is complete — the five-face contract survived its
corpus measurement, the producer half is ruled against it, tranche A and the 0889 protocol are
ruled with their instruments specified, and `/qa`'s plan maps every gate to a named instrument.
None of the conditions re-opens design. FIXMEs **0922, 0923, 0925 resolved and deleted**;
**0927** (`/design` int) and **0928** (`/design` runtime pair) filed.

### The schema window — option (b) granted: **TWO windows, two owners**

The Phase-2 "exactly one schema window" rule is **amended**. `/design`(typecheck) showed both
producer fixes are serde-visible *meaning* changes where a stale sidecar re-introduces the
defect — 0924 restores an accessor as `Concrete{got_slot}` and the **memory-unsafety returns on
warm cache**; 0913 restores the fabricated root and the **leak returns**. So:

- **Window 1 — typecheck producer, 23→24**, taken by 0924's CS-1, **shared** by CS-2 and 0913's
  CS-3 under the S111-0621 one-bump precedent. **Binding condition**: all three producer
  change-sets land in-sprint; if CS-3 slips to S120 the shared licence expires at close and CS-3
  takes its own window then. A schema-24 sidecar carrying fabricated `ConcreteType::Int` roots
  across a sprint boundary is precisely the defect-reintroduction the ruling prevents.
- **Window 2 — 0869's cache carrier, 24→25**, with 0898 and 0748/R3 riding as authorized.

If waves reorder, the integers swap; **the invariant is two increments, two owners, and no other
change-set touches the constant.** Option (a) was rejected for coupling a memory-safety fix to a
cache fix and forcing typecheck work into a `/dev`(src) change-set; option (c) for carrying the
SIGSEGV class plus four REDs into S120 against the sprint's chartered outcome.

### The IO tri-context seam (0923) — approved on all three asks

`cranelisp-intrinsics` gains `pub fn free_io_node` plus one `#[export_name]` C-ABI shim (the
pair's **84th** extern; must resolve under `--link` as well as JIT). It is a **split of
`consume_io_tree`'s existing body at the dec** — no new mechanism, behaviour byte-identical.
Backend owns what only the type knows (`Pure`'s payload via ordinary `drop<T>`; no IO-specific
payload releaser — reject criterion 5); the runtime owns what only the value knows.
`ctor_shapes` stays untouched and unreached for `primitives/IO` — `drop_glue.rs:497-505` is a
*correct* check on a precondition IO structurally cannot meet, and weakening it would weaken it
for every user type. Int's `Bind` seed stays, with the R-4 introspectability obligation
(`/info Bind`) binding on whatever `/dev` does to it.

**The named residual is acceptable-with-a-guard**: a `Pure` payload nested inside an *unrun*
`Bind` sub-tree is not discharged. R-2 forbids fabricating the existential, and both
alternatives are worse — today's hard refusal, or admission-exclusion's unbounded silent leak,
which `/examples` measured at **82.7 MB per 800k iterations**. `/qa`'s failing-not-ignored guard
is mandatory and may not be `#[ignore]`d.

**`free_io_node` lands raw `i64`, permanently**, in the Spine-1 window *before* tranche A: its
precondition is a count already at zero, and an `Owned` models a live counted reference, so it
sits beneath the handle abstraction alongside `atomic_dec_rc`. Tranche A's CS-5 count record
enumerates it as a named exclusion — expected **N_heap = 103 + 1 − 42 = 62** — so G3's semantic
count does not silently drift by one.

### Two register rows, and a regrade

`design/arch/safety-invariants.md` §4 gains **R17 — heap category before RC operation** (the
contract's R-1; `unasserted`; seam `rc_emission.rs:486-495`; the permanent §5.1 census is the
mechanism, each family flipping to a located error only on measured zero — the arm is the gate
on its own removal) and **R18 — no fabricated concreteness** (R-2; three measured instances).
The register runs unhyphenated, so the contract's R-1/R-2 land as R17/R18 with the mapping
recorded.

**`/arch` also regraded R11 ("Concreteness at codegen") from `unconstructable` to
`example-tested`** — a consequence the dispatch did not ask for. The S119 census **falsified**
it: two hand-mint sites bypass the S84 slot gate. P-1 restores it; 0926's gate cell is the proof.

### Rule-0 enforcement (0922) — ruled now, no S120 needed

"Satisfied by construction" was **not available**: clause defns run the full `check_forms` path
and the ownership fixpoint publishes summaries onto callable entries, so a fresh-result clause
can legally classify `Borrowed` and backend elides its release. The per-clause divergence hazard
is real. Ruled: the ABI witnesses ownership as well as calling convention, and **the pin lives
at int's clause-preparation seam** — after `check_forms`, before publication, int **clears the
synthesized clause entry's `mode_summary`**. Summary-absent yields the all-Owned compilation,
which *is* the declared convention; widening toward Owned is always sound, at a few redundant
compile-time RC ops. Structural under Principle 19 — int knows clause-ness by construction, and
no name-prefix privileging enters typecheck or backend. No types, schema, or public-API delta.

### Tranche A — public-API approved as enumerated; three rulings

Approved: additive `pub mod handle` (`Owned`, `Borrowed<'a>`, the 8 operations as a **closed
set** — adding one is an `/arch`-visible change) plus **10 changed signatures** (9 public
`consume_*`/`dec_shallow_io`/`consume_trace_call`, plus private `free_io_branches` →
`Borrowed<'_>`). `cranelisp-primitives` **zero delta**. All 83 extern shims keep
`extern "C" fn(i64,…) -> i64`. No `cranelisp-types` delta. The trusted-base count (4 definitions
+ 1 generator + 6 shim sites) with its grep gate is **ratified as the auditable contract**.

Rulings: `ElemConsumeFn` spelled **inline**, no `pub` alias; the **debug-profile-conditional
`Drop` is acceptable** in the baseline, with conditionality named in the rustdoc (the
`cfg(not(debug_assertions))` empty-`Drop` alternative rejected as code written for a
documentation property); and the **`launch.rs:452` dispensation is GRANTED** to
`/dev`(runtime pair) — exactly that one call expression, the one-line
`unsafe { Owned::from_abi(cont_ptr) }` wrap, in CS-2's change-set. Any wider backend edit in the
tranche-A wave is a `/review` REJECT.

### Gates confirmed, G3 amended

**G3 is amended as the designer ruled**: the 136 was unfalsifiable as written (30 `ring0.rs`
scalars never flip; 3 flip return-only). Record both numbers; **semantic `N_heap` = 103 is the
acceptance quantity**, tranche-A slice **42**, net **62** at CS-5 with the `free_io_node`
exclusion; consume sites 29 production plus the test tier. G1 ratified with its three layers and
a **required** (not optional) 0867 extension clause. G2 ratified with the census cell — 0917's
`NoReference` lattice point is a classification correction, not a licence arm, and the census
cell is its first client. G4/G5/G6 ratified; the `ParamFlow`-never-`Mode` derivation axis is
confirmed load-bearing (`Mode` is the analysis fact, `ParamFlow` the ABI fact). The close gate's
schema check becomes **"exactly two windows, as assigned"**.

### Principle 8 — no interim architecture; two confirmations

**I-CT → I-CT′ ratified.** The census falsified the premise under which `/arch` ratified I-CT:
the pair's inc half is a wild write on scalar payloads at n ≥ 1024, and I-CT proves count
balance while being silent on reference-hood. I-CT′ is strictly simpler and is target-state, not
a bridge — under Decision-24 the template frame owes nothing, so the pair *deletes*. The
census-gated staged flip is the anti-interim pattern: a permanent instrument that is its own
removal criterion, not scaffolding.

**R-3 changes nothing in `ownership-inference.md`'s staging, and sharpens the option-2
deferral.** The analysis already runs post-monomorphisation, and faces 2/3 landing *expands* the
ABI-bearing mode-vector class — a precision gain. Option 2's standing is unchanged and
sharpened: **uniform emission cannot legally count a residual word either**, so the wild-write
class is orthogonal to uniform-vs-elided emission. That confirms both the Phase-2 finding (option
2 dissolves at most 0917×3) and the measurement's sequencing after Spine 1.

### Conditions attached to the PASS

1. Window 1's sharing condition — all three producer change-sets in-sprint, or CS-3 takes its own
   window in S120.
2. `free_io_node` lands raw, in the Spine-1 window, enumerated in tranche A's CS-5 count record.
3. The 0922 pin and its fence join `/dev`(int)'s obligations **before** tranche B-int's Rules 1–3
   land; D0 remains the binding measurement gate.
4. The `launch.rs` dispensation is scoped to the single call expression.
5. The face-4 residual guard and the four-line accessor repro are **stage-1 `/testing` work,
   before the implementing waves**.

---

## Waves (Phase 4)

Organized 2026-07-26 from the four Phase-3 plans and the exit gate. Source-touching waves run
**serially** (worktree isolation is broken on this project). Each wave carries its own
instrument re-run so drift stays attributable.

### Wave 1 — QA-first, sprint-wide (Phase 5 stage 1)

| Skill | Surface | Task | Status |
|---|---|---|---|
| /testing | `tests/` | The four-line accessor repro (1023 GREEN / 1024 SIGSEGV) — **currently unguarded and the cheapest memory-safety cell in the class**; the family-1 accessor marginal guard; the IO-`Bind` balancing marginal guard (the fence against 0907 being "fixed" by admission-exclusion); the face-4 residual guard, failing-not-ignored; 0926's slot-gate cell | pending |

Gate before W2: every gate G1–G6 has a live instrument, per `/qa`'s §11.2 — a gate asserted in
prose with no instrument is itself a close-gate failure.

### Wave 2 — Spine 1, backend (10 of the 11 REDs)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-backend | Piece 1 — **0917**: `ValueProvenance` gains the `NoReference` bottom point; the probe-independence pin is replaced by the strictly stronger monotonicity pin. The emission-licence census instrument lands here with its detection proof. **3 REDs** | pending |
| /dev | cranelisp-intrinsics | The `free_io_node` split (raw `i64`, permanent) — lands before tranche A per gate condition 2 | pending |
| /dev | cranelisp-backend | Piece 2 — **face 4**, the IO glue arm + `free_io_node` call. `core.io` and `core` flip together; `21-hello-io` at 243 and `23-io-sequence` at 178 in all four cells. **7 REDs** | pending |
| /dev | cranelisp-backend | Piece 3 — **face 1**, retire the ctor-template pair under I-CT′. 0 REDs; census A −2,216, census B −3,108; zero emission change on any concrete param | pending |
| /dev | cranelisp-backend | Rider **0906** with its scoped golden re-baseline | pending |
| /review | cranelisp-backend | Change-set review — seven reject criteria from the contract §8, plus the per-change-set focused corpus-manifest run (absence = REJECT) | pending |

### Wave 3 — Spine 2 tranche A, runtime pair

Never shares a wave with W2's backend churn — each needs its own byte-identical instrument re-run.

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | intrinsics + primitives | CS-1 vocabulary + the detection triplet + grep gate (ships in the **same** change-set as CS-2 — it must not land with zero consumers) → CS-2 A1 funnel, incl. the `launch.rs:452` one-line dispensation → CS-3 A3-then-A2 → CS-4 the derivation + `string-identity` → CS-5 counts, three-class churn check, `public-api.txt` | pending |
| /review | intrinsics + primitives | Class-1/2/3 churn verdict; the enumerated public-API diff against `/arch`'s approval | pending |

### Wave 4 — typecheck producer (schema Window 1)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | cranelisp-typecheck | **MEASURE-1b first** (cheap A/B: pin `get`'s parameter and see whether the SIGSEGV disappears — decides whether CS-2's F1 half is a successor-discovery widening only) → CS-1 P-1 + the F2 scheme-truth fix, **landing together with rider 0867** per `/design`(typecheck)'s recommendation (same function, one review surface) → CS-2 A-MINT + the F2 collection trigger → CS-3 `default_residual_parameters` + census. **0916 + 0867×3 + 0913** | pending |
| /review | cranelisp-typecheck | Five fence items — notably that a **concrete** accessor and a **concrete** impl method stay byte-identical; a golden-CLIF diff outside F1/F2 is a finding, not a re-baseline | pending |

**Window 1's bump (23→24) is taken by CS-1 and shared by CS-2 and CS-3.** If CS-3 slips, the
licence expires at close.

### Wave 5 — Spine 2 tranche B-int (best-effort)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /design | int | Absorb **0927** — the Rule-0 pin at the clause-preparation seam, plus D4's fence | pending |
| /dev | src/ | **D0 first** (read the convention out of two clause shapes' CLIF *before* Rules 1–3 land) → Rules 1–3 → Rule 4. **D1 is a hard gate**: all five interior-alias double-free pins must re-clear under plain *and* armed lanes. Riders 0914, 0915 item 4 | pending |
| /review | src/ | — | pending |

### Wave 6 — cache carrier (schema Window 2)

| Skill | Crate | Task | Status |
|---|---|---|---|
| /dev | src/ + cranelisp-types | **0869** (carrier, 24→25) + **0868**, with **0898** and **0748/R3** riding. Re-point the two hand-rolled `impl$` mint sites | pending |
| /arch | design/arch + types | **0918** / **0919** — types-audit R1 and the R2+R4+R5 facade-truth pass (R4 compaction drops first if capacity binds) | pending |

### Wave 7 — riders and the deferred conditional

| Skill | Surface | Task | Status |
|---|---|---|---|
| /dev | platform | 0870, 0874, 0873, 0871 | pending |
| /qa + /testing | tests/ | Track-C **D1 discriminating experiment** (~200× isolated under equal host load, tee'd) + the recorded re-measurement of the opening flap datum; the option-2 measurement, **report-only, after Spine 1** | pending |
| /dev | src/ | **0863** — conditional third deferral signed off; runs only if the int surface clears with capacity remaining. **Never interleaves with W5** | pending |

### Must-not-interleave (binding; each is a `/review` reject or a dispatch constraint)

- W2 backend implementation and W3 tranche-A signature churn never share a wave.
- 0867 lands only after P-1 is implemented — `/arch` and `/design`(typecheck) both confirm it
  unblocks on **CS-1 alone**, not the whole obligation; hence the W4 pairing.
- W7's 0863 never interleaves with W5. The `src/expander.rs` overlap is textual, not semantic —
  B-int first, 0863 rebases.
- **Exactly two schema windows, as assigned.** No other change-set touches the constant.
- Option-2 adoption happens under no capacity outcome this sprint; the measurement is the
  deliverable, and it never shares a wave with tranche churn.

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

**2026-07-27 — USER RULING ON DIRECTION: total concreteness at end of typecheck.**
The user overruled `/arch`'s kind-partitioned slot invariant (`f5d30808`):

> "I disagree with arch — we need concrete types at the end of typecheck. we need to
> eliminate edge cases that seem to need polymorphism. In the future when we have more
> sophisticated storage layouts, there will be no chances for generic functions."

`/sprint`'s reading, put to `/arch` for re-ruling: the `Constructor` licence
(representation-parametricity) and the `Primitive{Extern}` licence for `bind` /
`catch-runtime-error` both rest on **every value being a uniform i64 tag-or-pointer** —
a property of today's representation, not of constructors or primitives. Unboxed scalar
fields, a flat `(Vec Int)` versus a pointer-array `(Vec String)`, or any packed layout
retires them, and `design/arch/release-llvm-backend.md` puts exactly that on the roadmap.
So the licence is scheduled for demolition by work already planned, and it would break
**silently** — the failure mode is a wrong body, not a type error.

`/arch`'s own recorded lesson cuts the same way: *an invariant stated universally with an
unstated exception is unassertable*. The `f5d30808` ruling fixed the *unstated* half and
kept three exceptions; an invariant with three licences is still harder to check and
easier to hide in than one with none, and two unsanctioned mints have already shown what
hiding in a licence's shadow costs.

Under total concreteness the five-face table's faces 1–3 and 5 become **unreachable
states** rather than dispositions, R-1 becomes vacuous, the `Err ⇒ Mixed` arm has no
traffic by construction rather than by census, and NC-1 returns to a single universal
predicate with today's polymorphic primitives as **intentional REDs against open
defects** — a more honest instrument than a partition table.

Re-ruling dispatched to `/arch` with an honest-dissent clause. **Sequencing bias recorded:
S119 ships as planned unless a landed ruling is actively wrong under the new target** —
Phase 5 has not dispatched, and the contract and producer obligations are reviewed.
Pending that ruling, `/qa`'s NC-1 partition table (`fdea7e29`) may be superseded.

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
