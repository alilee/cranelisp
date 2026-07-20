# Sprint 114 — sprint-wide test plan (Phase 3, 2026-07-20, /qa)

Scope: SPRINT.md tracks A–E (typed resolution carrier + settlement-consumer
drain + binding-indirection contract + src/frontend drains). The S113
attributed-carry ledger (31 suite REDs at close, every one owner+trigger
attributed) is the acceptance backbone: **most drain waves have their
acceptance rows already committed as REDs** — this plan states which REDs
flip per wave, which NEW cells /testing authors in the Phase-5 Stage-1
QA-first battery, and what is unit-tier (/dev) vs e2e (/testing).

Companions: `s113-test-plan.md` (row IDs reused where the family continues),
`design/arch/typed-resolution-carrier.md` (binding for §3), FIXME 0668 (the
Track-B seam evidence). Conventions unchanged from S113: twin-row-per-axis is
binding on every matrix; `[oracle]` rows run under the safety lane;
RED = failing-not-ignored until the named flip trigger.

**Do not run the suite during the parallel-free design phase** — the RED
inventory below is documented from the S113 close records; /testing verifies
it live at Phase 5 Stage 1 before authoring (any drift from this accounting
is reported to /qa, not silently absorbed).

## 0. Risk read (shapes depth)

1. **The carrier flip is the sprint's heaviest surgery** (multi-crate,
   serde-visible, `resolved_target` ×368/59 files). The risk is a partial
   flip: a consumer arm keeping the old `Option`-convention behaviour behind
   an exhaustive-looking match, or a producer chokepoint that is total for
   Globals but silently manufactures `Local`. Mitigation: §3's totality
   cells + the helper-classification sweep AS the acceptance check (carrier
   doc §5.2), plus the unit-tier obligations enumerated in §3.4 (the
   enumerated-deferral discipline — e2e cannot see `from_expr`'s error arm
   directly).
2. **Track B is the UAF family** — the standing risk is instance-patching
   (the review-REJECTED one-level recognizer). The §2 matrix pressures ONE
   contract: a variant that fixes differently from its siblings names a
   second codepath.
3. **ONE schema window** (21→22). Two bump-worthy changes (carrier reshape +
   B-2 escape-fact correction) must land in one invalidation event; a second
   bump in this sprint is a plan violation to report, not absorb (F7).
4. **Two-skills-one-seam** (F3) — discharged by §1; no typecheck change-set
   may touch the capture/let-alias consume accounting, and no backend
   change-set may touch the match-var-pattern escape *fact*.
5. **Mode-axis debt in the Track-B family file**: `binding_indirection_consume.rs`
   currently runs `--run` only; the S113 matrix discipline (variant ×
   {on,off} × {repl,--run,--link}) is completed this sprint (§2).

## 1. FIXME 0669 disposition — the I-1 capture face (REQUIRED-BEFORE-PHASE-4 item, F3)

**Verdict: the 0641 I-1 capture face JOINS the 0668 backend consume-seam
family. It does not stay typecheck.**

Grounds:

1. **The toggle is the discriminator.** 0668's evidence table (verified
   2026-07-19, both toggles) has I-1 — `(let [r v] (fn [] (vec-get r 1)))` —
   returning garbage under `CRANELISP_NO_OWNERSHIP=1` as well as ON. Post
   R14 polarity restore, toggle-off is the conservative all-Owned lowering:
   no `transfer.rs` fact is consulted. A crash that survives analysis-off
   cannot be owned by the analysis.
2. **Structural identity with cell G.** `(let [r v] …)` binds a `Var` to a
   `Var` without counting; both scope-dec; the closure capture stores the
   alias with no independent count — exactly the let-bind-alias mechanism of
   cell G (`(let [q v] [q])`), with closure capture as the consume position
   instead of the vec-lit store. Closure capture is already an enumerated
   position in 0668's consume-position × operand-provenance contract.
3. **The committed locus is superseded evidence.** The pins'
   `// defect: locus=…transfer.rs::capture-of-let-bound-param-alias` records
   the S111 attribution, made before cells E/F/G proved the family
   ownership-independent and pre-COW. The 0668 evidence supersedes it.

Consequences (binding on Phase 4):

- The ×2 capture pins (`false_fresh_provenance_residual.rs::
  capture_let_bound_param_alias_{repl_yields_correct_value,link_does_not_corrupt_heap}`)
  **leave Track A's typecheck drain list and join the Track B contract's
  acceptance set** (flip trigger: the 0668 consume-contract /dev change-set).
  Track A's typecheck RED count drops 10→8; Track B's rises 7→9.
- /testing updates the two `// defect:` locus lines in the Track-B pin
  change-set: `class=uaf locus=crates/cranelisp-backend let-bind-alias /
  closure-capture consume seam (FIXME 0668) found=S111 owner=/dev`.
- The 0668 /design(backend) contract's consume-position enumeration MUST
  carry the closure-capture row (it already names it); Track A makes **no**
  `transfer.rs` capture-provenance change this sprint.
- **Re-attribution rider (MC-E1 protocol — a non-flip is evidence):** if the
  analysis-ON capture face survives the backend contract fix while G/F/B
  flip, a residual typecheck provenance face exists and re-attributes to
  /dev(typecheck) `transfer.rs` THEN — with the backend fix landed as the
  discriminating experiment, not before it.

FIXME 0669 is fully actioned by this section + §2 and is deleted; this file
is the durable record.

## 2. Track B — binding-indirection consume family (the 0669 pin rows)

The family file exists (`tests/binding_indirection_consume.rs`, authored
S113 6b): A on/off + E on/off born-green fences; G, F/B-merged, C-off RED.
Flip trigger for every RED row: the 0668 /design(backend) contract's /dev
change-set(s). Fences that must HOLD through them: A/E ×2, cell-H bare-match
behaviour, `ownership_reuse::l_c3_*` ×2 (escape-gated reuse), the CLIF
golden lane, `vec_lifecycle`.

| Row | Cell | Status / directive |
|---|---|---|
| BI-G | `(let [q v] [q])` let-bind alias | RED committed (`let_bind_alias_into_container_neg`); flips with the contract |
| BI-F | `(match (match v [r r]) [q q])` nested-match forward, no COW | RED committed (`nested_match_forward_alias_neg`); flips |
| BI-C-off | B-2 shape under `CRANELISP_NO_OWNERSHIP=1` — the toggle-off face 0669 item 1 named | RED committed (`b2_match_cow_var_pattern_toggle_off_neg`); flips. The analysis-ON twins (`false_fresh_provenance_residual.rs::match_scrutinee_cow_var_pattern_*`) stay GREEN through the fix |
| BI-B-cow | **NEW** — nested-match WITH COW: `(match (match (vec-set v 0 5) [r r]) [q q])` (0668 cell B verbatim; the 0669-named probe cell not yet committed), both toggles | NEW ×2, RED; flips |
| BI-I1 | capture face ×2 (re-attributed per §1) | existing REDs join this family's flip set; locus update rides the pin change-set |
| BI-M | **NEW mode-axis completion**: the RED faces G and C-off each gain a `--link` twin (repl face optional — `--run` + `--link` is the divergence-bearing pair per MS-P7's lesson); born-green A gains a `--link` fence | NEW ×3 (G-link, C-off-link, A-link) — landed W1 |
| BI-T | Twin discipline: every RED names its GREEN twin in-file. **W1 finding accepted (/qa disposition item 4): the planned "H bare-match" HEAP green twin does not exist — heap-forward-through-match is broken WHOLESALE** (`(match [7 8 9] [r r])` returns garbage both inline and across a fn return), so /testing's SCALAR control substitution stands: `bare_match_forward_scalar_green` (`(match 7 [r r])` → 7) proves the match machinery (var-pattern bind + arm forward) correct and isolates the consume seam as the RC-accounting site | maintenance — scalar control accepted |
| BI-H-heap | **NEW row (item-4 completion): the INLINE/single-match heap-forward face.** The committed family rows cover the nested (F, B-cow) and COW/toggle faces, but the minimal single bare match forwarding a fresh heap vec — `(defn f [] (match [7 8 9] [r r]))` inline, and its across-fn-return sibling — had no committed row despite being RED. /testing authors ×2 RED cells in a **pre-W4 rider** (`class=rc-miscount`, 0668 consume seam; GREEN twin = the scalar control); flips with the same Track-B contract change-set | NEW ×2 RED (rider) |

`[oracle]` — the whole family graduates through `assert_safety_matrix`
where the lane supports the toggle axis; until then env-pair cells as today.

### 2.1 F-R1 + MS-P8 seam adjudication (FIXME 0688, /qa, 2026-07-20 — discriminators RUN)

Both discriminators from `design/backend/binding-indirection-consume.md` §6
were executed against a fresh build (post-c962f133). **Verdict: BOTH are
`cranelisp-backend`. The intrinsics surface is exonerated on both** — the
`s114-test-plan.md` §2 owner placement (backend Track-B /dev change-sets)
STANDS, now evidence-grounded instead of presumed. Reading note for the
evidence: `CRANELISP_RC_TRACE` shows intrinsics-side ops only (backend
inline RC is untraced `atomic_rmw`/load-add-store); the dec line prints the
POST-dec count.

**F-R1 — verdict (a): backend `protect_return_value` over-inc on entry-`main`'s
IO result.** Evidence on the 2-line repro
(`(defn main [] (let [s "hi"] (Pure 9)))`, PrimitivesOnly, `--run`):

- RC_TRACE: `[RC]   dec 0x…8f40 rc=1 tag@16=0` — the trampoline dec observed
  the `Pure` box at rc=2 (post-dec 1) ⇒ rc=2-at-return, the (a) signature.
  Hypothesis (b) is REFUTED by the same line: `consume_io_tree` DID dec the
  root `Pure` leaf.
- CLIF (`CRANELISP_CODEGEN_DUMP=user::main`): after the `Pure` alloc (`v5`),
  main emits the non-atomic protect inc (`v9 = load v5+8; v10 = iadd v9, 1;
  store v10`) BEFORE the `s` scope-dec, and returns `v5` at rc=2.
- RC_STATS: `rc_inc=2 rc_dec=1 allocs=2 deallocs=1 rc_nonatomic=2`.
- Controlled contrast: the MS-P8 fixture's `main` (no heap `let` ⇒ no
  cleanup target ⇒ no protect inc) shows its `Pure` box dec'd to 0 and
  FREED by `consume_io_tree` — the protect inc fires iff a heap cleanup
  target exists in `main`'s frame, exactly the §13.3 G2/item-26 class
  localized to the entry frame.

**MS-P8 — verdict (a): backend TCO — missing release of the superseded heap
loop-param at the tail-jump slot overwrite** (the PARAM sibling of the §13.3
B3.1a let-scope dead-block leak; `flush_let_scopes_before_tail_jump` covers
`let` bindings only). Evidence on the 3-iteration CONJ_LOOP (workspace
stdlib, `--run`):

- CLIF `main::go` block3 (recur arm): inc old `v` (arg-pass), call `conj`,
  then `jump block1(v9, v16)` — the param slot is overwritten with the
  fresh box and the superseded value's slot reference is NEVER dec'd.
- CLIF `main::collections.vec/conj$…` block3 (copy arm): the source release
  IS emitted (`atomic_rmw sub` at source+8 + drop-glue call on zero) —
  hypothesis (b) (copy-branch polarity) REFUTED; and since the emitted
  backend release is the source-struct accounting site, hypothesis (c)
  (intrinsics `vec-push-copy` non-accounting) is refuted with it.
- RC_TRACE/RC_STATS at N=3: `allocs=5 deallocs=2` (leak 3 = 1/iter);
  `reuse_hit=0 reuse_miss=3` (every `conj` took the copy arm — the go-side
  arg-pass inc guarantees rc≥2 at the site); each superseded vec ends at
  rc=1 (alloc 1, +1 go inc, −1 conj source release), never freed. The
  INT_LOOP control balances (non-heap params — nothing to flush).

**Phase-4 wave assignment (binding):** both F-R1 ×2 and MS-P8 ×2 stay in the
Track-B backend `/dev` wave — same crate as the 0668 consume-contract
change-sets, as separate leak-direction items with their seams now NAMED:
F-R1 = `compiler/rc_emission.rs::protect_return_value` at the entry-`main`
IO-return (single-consumer trampoline contract); MS-P8 = the tail-jump
heap-param flush seam beside `flush_let_scopes_before_tail_jump`. No
`/dev`(runtime/intrinsics) deployment is needed for either. FIXME 0688
resolved and deleted; this section is the durable record.

**`// defect:` locus updates (/testing, rides the Track-B pin change-set,
with the BI-I1 locus edits):**

- `adt_drop_glue_underkey.rs` F-R1 family lines: `locus=entry-main
  IO-teardown seam` → `locus=crates/cranelisp-backend
  compiler/rc_emission.rs::protect_return_value — entry-main IO-return
  over-inc (0688 verdict a)`. `class=rc-miscount owner=/dev` unchanged.
- `ms_p8_conj_leak.rs` lines: `locus=crates/cranelisp-backend vec
  persistent-op (conj/assoc) RC path …` → `locus=crates/cranelisp-backend
  TCO tail-jump loop-param slot overwrite — superseded heap param never
  released (0688 verdict a; conj copy path is the exposure, not the seam)`.
  `class=rc-miscount owner=/dev` unchanged.

Both-polarity fence unchanged and binding on both fixes: `allocs==deallocs`
EXACTLY (a fix must not convert leak → under-count; for F-R1, suppressing
the protect must be licensed ONLY by the entry-`main` single-consumer
contract, not weaken the general G2/item-26 protect; for MS-P8, the flush
must balance in BOTH conj arms — in-place returns the same box, so the
superseded slot ref still needs exactly one dec). The exemplar parity
expectation updates when both faces close (S113 §3.6 MS-P8
characterization datum).

**B-2 fix ownership fence (F4):** the 0668 contract must NOT absorb the B-2
escape-fact half — the analysis-ON fact correction is typecheck work already
landed S113; its *cache-coherence* half (stale persisted `Some(false)`)
rides the Track-A schema window (§3.3). The backend gate is correct (R14)
and stays untouched by any "distinguish wrong-Some(false)" workaround.

## 3. Track A — typed carrier + settlement-consumer family

### 3.1 Existing REDs and their flip waves

| RED set | Flip trigger |
|---|---|
| F-D2-10 ×4 (nullary no-impl check-gate-leak) | **RIDES the carrier change-set** (F1) — never a pre-carrier interim gate patch. See §3.2 re-shape |
| MC-X4 + MC-X4b (P26-temporal consumer harvest, two faces) | The settlement-consumer /dev(typecheck) change-set — orthogonal to the carrier, may land before/interleaved (F2). The face PAIR is the fence against a partial fix |
| MC-X5 (raw-name overload gates) | Same deployment, distinct mechanism row (MC-V1 verdict stands) |
| PS-SH1 residual (multi-sig value-ref matrix) | §3.5 completion cells + the typecheck drain |
| MS-P7 | **ADJUDICATED (W3): W7 /dev(typecheck) rider, priority over the conditional 0590 slot** — §3.6 adjudication record |
| ~~0641 I-1 ×2~~ | moved to Track B per §1 |

### 3.2 Carrier-wave cells (the F-D2-10 re-shape + totality)

The carrier makes "unresolved" unrepresentable; the phase-boundary gate is a
**located typecheck-phase error** (`ViewBuildError::Unresolved{span,name}`,
carrier doc §4). The flip change-set therefore RE-SHAPES the F-D2-10
assertions, and new totality cells pin what the constructor now guarantees:

| Row | Cell | Directive |
|---|---|---|
| CA-1 | F-D2-10 ×4 re-shape | The flips assert a **located typecheck-family error naming the owning trait** (§7.11.2(c)), uniform across REPL/`--run`/`--link` (F-D2-9 discipline) — NOT merely "no `undefined function` leak". The negative facet (no codegen-phase symbol leak, no panic) is RETAINED through the flip (preserved-facet discipline) |
| CA-2 | **Totality positive — all-local body** | `(defn f [x] (let [y x] y))`-class program, ×3 modes: the retired "empty maps for all-local bodies" license means every local now takes the `VarRef::Local` path end-to-end. Born-green fence; guards the flip against over-gating legal locals |
| CA-3 | **Totality positive — local shadowing a global** | A param/`let` name equal to an in-scope global (and to a prelude-importable name): resolves Local, correct value, no phantom Global dispatch — the `Option`-conflation's sharpest cell, now decided by constructor. Born-green ×2 (defn-param, let), + the match-var sibling |
| CA-4 | **ViaCallee positive** | HOF/computed-callee apply (callee is a param) runs correctly — `ApplyRef::ViaCallee` is a positive verdict, not a default. Born-green |
| CA-5 | **No-codegen-`undefined function`-for-check-decidable-faults standing negative** | Covered by CA-1 + the MC-X3d §2.7 annotation becoming true; /qa audits at Phase 6 that zero suite REDs surface codegen-phase resolution errors on typecheck-decidable inputs |

### 3.3 The ONE schema window (21→22) — cache-invalidation cells (S111 0621 precedent)

| Row | Cell | Directive |
|---|---|---|
| CS-1 | **Warm-cache correctness twin of the B-2 shape** | Compile the B-2 program `--run` with a cache dir, run again warm: cold == warm == 99 (both toggles once BI-C-off flips). Guards the escape-fact correction's persistence: a stale `Some(false)` served from cache would reproduce the UAF post-fix — the exact hazard F7 names |
| CS-2 | **Schema-gate refusal fence** | The stale-`CACHE_SCHEMA_VERSION` wholesale-refusal behaviour (AG-1 class): verify the existing gate fence covers the 21→22 bump (re-point the existing cell if present; author one if the S111-era cell was version-pinned). One cell — the mechanism, not per-version |
| CS-3 | **Window-count verification** (/qa, Phase 6/7 audit — not a test) | Exactly ONE bump lands this sprint, in the carrier flip change-set, with the B-2 fact correction in the same window. A second invalidation event is reported to /sprint |

### 3.4 Unit-tier obligations (/dev, enumerated — the deferral names its cases)

E2e cannot reach `from_expr`'s error arm or the lenient seam assert
directly. The carrier wave's /dev change-sets MUST land unit tests for, at
minimum (each fails on revert of its half):

1. `from_expr` with a missing `var_refs` entry for a real-span `Var` →
   `ViewBuildError::Unresolved{span,name}` (and the Apply sibling).
2. `lenient_from_expr` resolution miss → tier-3 seam assertion fires (never
   a silent manufactured `Local`); the legitimate-miss population question
   escalates to /arch as a FIXME if evidence names one (carrier doc §3.5).
3. Binder-identity provenance: `VarRef::Local.binding_span` = the binding
   FORM's span for each binder kind (param, `let`, match-arm) — the shadow
   frames disambiguation grain.
4. Backend consumer: `VarRef::Local` scope-stack miss = hard invariant
   failure carrying the binder identity; `is_self_call` keys on
   `VarRef::Global == current fn's storage FQ` (the S25 TCO read stays
   keyed).
5. B-2 escape fact: match-var-pattern transfer records `escapes` truthfully
   (the S113 fix's unit pin — confirm it exists; author if the fix landed
   e2e-only).

### 3.5 PS-SH1 completion — as-built (W1; /qa disposition item 5 ACCEPTED)

The S113 residual: {let-shadowed} × {single-sig defn, multi-sig base} ×
**value-ref** cells (call cells landed + flipped S113). /testing completed
the shape as **matrix-missing POSITIONS, not net-new scenarios** — the
right reading of the residual (the matrix pressures ONE codepath; a
per-position fix that greens one value-ref position but not a sibling
names a divergent resolver). As built in `tests/shadowing_scope_lookup.rs`:

- **+2 RED positions**: multi-sig-base value-ref **returned**
  (`…value_ref_returned…`) and **stored-in-container**
  (`…value_ref_in_container…`) — both resolve to the module overload base
  today; flip with the Track-A typecheck drain.
- **+1 GREEN control**: the single-sig value-ref HOF twin
  (`let_shadowed_single_sig_defn_value_ref_hof_resolves_to_local`) —
  proves the bug is the overload-base gate, not value-ref resolution
  generally; must stay green.

Counts: ×3 as built (2 RED + 1 born-green control), vs the planned "NEW
×2"; the in-file call cells remain the flipped-S113 GREEN twins.

### 3.6 MS-P7 — evidence gate (F5; do NOT pre-commit a wave)

MS-P7 (`safety_lane_cow_set_read_returns_set_value_abort_free_red`):
REPL/`--run` correct both toggles; `--link` aborts. 0664 localizes the
divergence to the per-turn-JIT vs ObjectModule mode seam. **Wave assignment
is gated on call-chain evidence** (S98/S102 discipline), specifically:

1. **CLIF identity check**: dump the failing fn's IR on both paths
   (per-turn JIT vs the `--link` ObjectModule build). Identical IR ⇒ the
   defect is downstream of codegen input (relocation/layout/runtime — owner
   backend-link or int); divergent IR ⇒ the producer INPUT differs per mode —
   name which (escape facts, mono-view instance, check-run pairing per
   `backend-keyed-consumer.md` §1.1.3) and why.
2. **First-divergent-frame naming**: the evidence brief names the first
   frame where the two mode paths consume different data, not the symptom
   frame (the abort).
3. Only then: typecheck if the recorded facts differ at production; backend
   if identical facts are consumed differently; int if the view/pairing
   assembly differs per mode.

Until the brief exists, MS-P7 stays an attributed-RED carry in no wave's
flip set. The /design(typecheck) or /design(backend) narrow deployment that
touches the mode seam first produces the evidence; /qa adjudicates the
attribution from it.

**ADJUDICATION (/qa, W3, 2026-07-20 — from the W3 evidence brief, commit
`078d324b`).** The brief discharged the gate with a result the §3.6
dichotomy did not enumerate: **CLIF is BYTE-IDENTICAL across `--run` and
`--link`, and the shared IR itself contains the defect** — a double-dec on
the COW in-place `vec-set` arm (the in-place branch returns the SAME heap
pointer as the input vec; both the result temp and the param get dec'd).
Not "identical IR ⇒ downstream of codegen input": the IR is identically
WRONG in both modes; `--run` silently tolerates the corruption in-process,
`--link`'s glibc allocator aborts. The mode axis was only the DETECTOR.

- **Class (plan-level re-label): `mode-divergence` framing RETIRED → `uaf`**
  (double-dec/premature free on the COW in-place arm — the vec-assoc UAF
  class `design/typecheck/ownership-inference.md` names). The pin's
  `// defect:` line already carries `class=uaf`; it is the PLAN's F5
  red-flag-class framing (and SPRINT §Goals line) that was wrong. The S98/
  S102 mode-divergence discipline did its job — the call-chain evidence is
  exactly what refuted the class.
- **Owner: /dev(cranelisp-typecheck), ownership analysis** — CONFIRMS the
  S113 provisional attribution (third reaching context of the S111 §3.7
  `MayAliasOf` family: {match var-binding, vec-literal element store} +
  **{projection-out}**, 0641-adjacent) and the pin's locus. The R14
  two-halves frame decides it: **"result may-alias input" is an
  ANALYSIS-side fact** — the analysis half owns its truth for every
  reaching context; the Track B consume contract (0668) explicitly does
  NOT re-derive analysis facts. A double-dec present in the emitted IR
  means the consume seam was fed absent/wrong facts for the direct
  COW-set→project shape (`(vec-get (vec-set v 0 9) 0)` — the vec-set
  result released as an ARG-TEMP, a site the §3.7 fix's protect/publish
  discipline did not cover), not that identical facts were consumed
  differently per mode.
- **Falsifiability (dev's first act)**: confirm at the publication seam
  (`ownership/transfer.rs` `ResultMode::MayAliasOf` arm → the temp's
  origin fact as delivered to backend) that the fact chain is
  absent/undelivered for the projection-out temp. If the facts prove
  present-and-correct at the consume input, RE-ATTRIBUTE to the backend
  consume half and the fix joins the W4 family (MC-E1 protocol: a
  non-flip is evidence, not a failed fix).
- **Wave: W7 /dev(typecheck) rider, PRIORITY over the conditional 0590
  slot** (a memory-safety RED outranks a convergence refactor; 0590 keeps
  its defers-with-`_hkt`-note clause). NOT W4 — wrong crate, and the
  consume contract must not absorb an analysis-gap workaround (fence
  below). NOT a bare carry — owner + seam are attributed and the fix is
  single-crate; only if W7 capacity fails does it become an attributed
  carry (the failing pin is the record + trigger; no FIXME).
- **Flip**: `safety_oracle_lane.rs::safety_lane_cow_set_read_returns_set_value_abort_free_red`
  (all three legs), verified under the lane BOTH toggles ×3 modes.
- **Flip hazard (/testing rider, same change-set as the flip)**: the MS-P6
  capability cell `safety_lane_detects_cow_set_read_corruption_capability_green`
  uses the LIVE defect as its planted fault — it INVERTS to RED the moment
  MS-P7 is fixed. /testing re-plants it on a synthetic fault (or retires
  the cell with rationale) in the flip change-set. Also refresh the pin's
  stale comments at flip time: the "W5 0641/§3 increment" flip-trigger
  reference and the "`--link` mode-divergent double-free" locus
  parenthetical (now known: shared-IR double-dec, `--run` tolerates
  in-process).
- **W4 fences (backend dispatch must now include)**: (1) the consume
  change-sets MUST NOT absorb an MS-P7 workaround — no pointer-equality
  runtime guard, no unconditional single-dec on the COW in-place path
  (the F4/B-2 anti-pattern sibling: backend compensating for a missing
  analysis fact); (2) cheap in-seam unit confirmation while in the consume
  code: the `MayAliasOf` consume arm's protect/release discipline for an
  ARG-TEMP (projection-out) consumer — the backend half of the
  discriminator; (3) any color change on the MS-P7 pin under W4's
  change-sets is REPORTED to /qa as attribution evidence, not treated as
  a win or regression.

### 3.7 Sweep acceptance (no new cells)

The P26 full typecheck sweep + the 0653 helper-classification sweep run
AFTER the carrier (F2) and ARE its acceptance check: /qa verifies at wave
close that (a) the sweep inventory was classified post-reshape, (b) zero
keyed-read-else-resolver hybrids appear (the Rev-2 REJECT), (c) the two
camps of bare-name helpers (legitimate pre-resolution vs re-resolvers to
delete) are dispositioned. Register updates, not tests.

**Sweep inventory additions (/qa, W3 — from the W2 review Important-3 +
Minor-2 findings):**

| Row | Inventory item | Directive |
|---|---|---|
| SW-1 | **`try_resolve_trait_method` Err-disposition family** — classify EVERY caller by what it does with the `Err` (the located no-impl reject): propagate / justified-benign (rationale comment in code) / swallow-defect. Known members: the W2-fixed settlement re-attempt (propagates); `infer.rs::resolve_value_position_trait_methods` (~1274) and `program/mono_collect.rs::resolve_auto_curry` re-attempt (~768) — both `if let Ok(Some(..))` swallows, dispositioned §3.8 as propagation candidates | The sweep confirms the family is CLOSED: zero unclassified swallows remain; any new member found joins §3.8's disposition |
| SW-2 | **Minor-2 invariant** — no producer writes `var_refs`/`apply_refs` at `Span::SYNTHETIC` (the W2 SYNTHETIC carve-out, review-verified at the flip) | Sweep row: mechanical check (grep + the carve-out's single licensed site) that the invariant still holds post-drain; a violation is a carrier-provenance defect, not a style nit |

### 3.8 W2-review Important-3 — the two surviving no-impl swallow siblings (/qa disposition, W3)

Both sites repeat the exact shape whose call-position instance WAS the
F-D2-10 root cause (W2: "the settlement re-attempt SWALLOWED the located
no-impl error via `if let Ok(Some(..))`"): same `try_resolve_trait_method`,
same discarded `Err`. Neither is a benign swallow — both are **propagation
candidates**, same family, different severity than F-D2-10:

1. **`infer.rs::resolve_value_position_trait_methods` (~1274)** — a trait
   method used as a first-class VALUE (let-binding, HOF argument) whose
   concrete types have no impl: the located no-impl `Err` is dropped, the
   Var keeps no resolution, and the reject (if any) surfaces later from a
   generic gate naming the METHOD, not the owning trait — a
   diagnostic-phase gap against the CA-1/§7.11.2(c) standard (located
   typecheck-family error naming the owning trait, uniform ×3 modes).
   Structural note for the fix: the fn returns `()` — propagation needs
   the same Result-widening the W2 fix gave the call path; that is why
   the swallow survived the W2 change-set.
2. **`program/mono_collect.rs::resolve_auto_curry` re-attempt (~768)** —
   partial application of a trait method whose late-pinned types have no
   impl: `Err` is swallowed AND control falls through to the
   `resolve_primitive_jit_name` fallback, so a definitive no-impl can be
   masked by a primitive-name resolution (a `wrong-accept`-shaped hazard,
   not just a diagnostic gap) or else ships an `AutoCurry` with no inner
   resolution for a later gate to reject generically.

**Disposition — probe-first (the BD-A3/0670 lesson), then RED cells:**

- **/testing probes** (small rider, before/with W7): (P1) value-position
  no-impl — e.g. bind `=` at a type with no `Eq` impl via a let/HOF and
  force resolution; (P2) auto-curry no-impl — partially apply a trait
  method at an impl-less concrete type. Each probe ×3 modes; record WHICH
  layer rejects and WHETHER the error names the owning trait.
- If a probe shows a trait-naming-less generic error, a wrong-layer leak,
  or (P2) a primitive-fallback wrong-accept: author the RED cells
  **F-D2-11** (value-position) / **F-D2-12** (auto-curry), asserting the
  CA-1 standard; they flip with the W7 typecheck rider (behind MS-P7 in
  priority, ahead of 0590).
- If a probe shows the surface is already conformant (some other path
  produces the trait-naming located error): pin it as a born-green fence
  and the SW-1 sweep row records the site as justified-benign WITH the
  fence as evidence — that is the only acceptable "benign swallow"
  closure; an undocumented swallow is not one.
- If W7 capacity does not reach the fix: attributed carry with the RED
  cells as record + trigger (no FIXME), reported into the Phase 7
  RED-vs-known-defect accounting.

## 4. Track C — src/ (0638 + riders + 0604)

### 4.1 Flips

- **0638 ×5** (`macro_expansion_interior_alias_double_free.rs` ×3 modes +
  the M1-ON/M1-OFF mode-axis twins): flip with the /dev(src) macro-clause
  invoke/marshal fix. Both mode-faces must green in one change-set (the
  §2.2 R-1 rule — a partial fix greening one face is caught by the other).
- **PS-D1 ×1** (0671 impl-confirmation stamps asking module): flips with
  the /dev(src) fix reading the RESOLVED homes (P26; never a display-side
  re-derivation). NEW +1: the asking-module ≠ canonical-home twin if the
  committed pin covers only one composition (per 0671's brief; /testing
  verifies in-file at authoring).
- **Riders 0674/0675**: one display cell each (startup restore notice
  appears on restore and NOT on a fresh dir — pos+neg one cell; cheatsheet
  multi-sig settled-facts line present). NEW ×2, born-RED-or-green per
  current behaviour; author with the rider change-sets, not Stage 1.

### 4.2 0604 — the foreground-writer prelude race (SHIPS this sprint; user, Phase 1)

Re-scoped disposition (FIXME §S110): the phantom
`bit-and → primitives/bit-and` public write into the live `prelude` table is
a **foreground concurrent-compile writer** (eval thread + priority/nice
workers building `num.bits` + `num.bits.test` + `prelude` + its ~13
re-exported domain modules concurrently) — the index feed is proven inert
under the recipe. There is still **no stable RED** (the sanctioned
exception); the ship gate is therefore **structural**, not a flip.

**What the twin guards already give** (`tests/spec_08_prelude_outer_scope.rs`,
both GREEN, must-hold):

- `super_import_wrapper_over_specific_prelude_compiles_clean` — the correct
  pole; goes RED if the phantom ever turns deterministic in the reduced
  fixture (a free tripwire).
- `super_import_wrapper_collides_when_prelude_globs_primitive_neg` — the
  deterministic §8.6.5 poison twin with the exact live signature; fences
  the fix from "solving" the symptom by weakening
  `insert_detecting_ambiguity` (the poison-consumer is CORRECT — do not
  touch).

**The attack (what /dev(src) needs — narrow-deploy to src/ int surface):**

1. **Foreground writer census** (the 0660 enumeration discipline): every
   seam on the foreground path (`src/imports.rs` installers,
   `src/process_form/`, `src/worker.rs`) that can insert a PUBLIC entry
   into a module's live symbol table — each either routes through the
   chokepoint below or carries a named legal-skip. The
   `prelude-import-convergence.md` §3.4 writer census (writers =
   `ensure_prelude_bit` + `install_module_session_env`) is the seed; the
   census extends it to every concurrent-compile-path insert.
2. **Structural contract — terminal-table freeze / export-closure gate at
   ONE chokepoint**: a module that has reached terminal never accepts a new
   public entry outside its export closure. The S113 PS-R7 rider landed
   `debug_assert!` + `MODULE_TRACE` at insertion seams (observability);
   this sprint consolidates insertion onto one guarded chokepoint and
   **promotes the closure check there to an unconditional diagnosed error**
   (trust-boundary tier, `safety-invariants.md` §2) — a firing then names
   its caller in production, not just debug. Isolation by construction,
   per the S61→S93 precedent — no per-interleaving patch.
3. **Prime suspect to check first**: a concurrent worker's prelude
   transparent-fallback hit being MATERIALIZED as a table entry with public
   visibility (§8.6.4 says materialise-or-not is zero-semantic-weight —
   that holds ONLY if a materialized entry is never public/exported; a
   public materialization IS the phantom). Second suspect: an
   import-direction write landing in the wrong table under the concurrent
   build of prelude's re-export closure (`bit-and`-only fingerprint =
   whichever symbol's install interleaves, not deterministic logic).
4. **Unit test at the chokepoint** (METHOD §2.2, fail-on-revert): an
   attempted out-of-closure public insert into a terminal table is
   rejected + diagnosed.
5. **/design(int) records the isolation contract** (already named in the
   FIXME's routing).

**Verification set (acceptance):** chokepoint unit test; census table in
the change-set (every writer dispositioned); ≥25× deterministic-recipe
sweep vs the real stdlib, `--run` + REPL (behavioural verification — the
pre-fix baseline is 0-fire in this environment, so the sweep is a
no-regression check, not the guard); twin guards GREEN; the
`concurrency_capacity` threshold defect stays SEPARATE (effect-concurrency
track — do not fold). **FIXME 0604 retires when the chokepoint + census +
guards land**; if a firing occurs first anywhere, the assert names the seam
and the fix narrows to it.

### 4.3 0670 chain cells (F8 — three waves, strict order) — **RE-BASED post-W1 (/qa disposition item 1, 2026-07-20)**

Wave 1 (int fix, Track C) → wave 2 (frontend §5 value-level reject
re-lands, Track D) → wave 3 (cells authored Stage 1, W1 — done).

**W1 finding (verified /testing, post-c962f133): the 0670 mis-qualification
does NOT reproduce e2e at HEAD.** Every IQ-P shape — including the verbatim
FIXME repro `(defn greet [name] (str "hello, " name))` — compiles and runs:
`qualify_expanded_sexp`'s incidental "hold verbatim if the symbol is
available in the current module" skip guard, plus the narrow
`defining_modules` seeding, suppress the mis-qualification for today's
documented shapes.

**Disposition: C1 SHIPS AS DESIGNED (architectural fix), with the
expansion-seam UNIT tests as its acceptance instead of an e2e flip.**
Grounds: (a) the S113 NOTE recorded a real observed breakage — the W3
revert of the frontend reject happened *because* valid programs broke;
non-reproduction with today's shapes is not mechanism soundness. (b) The
suppressor is **table-state-dependent** — "available in the current module"
is a symbol-table lookup, so whether a binder is mis-qualified turns on
what happens to be visible/imported, not on scope. Correctness resting on
incidental table state is the 0604 heisenbug-lineage class; a fragile
suppressor is not a fix. (c) The scope-blind re-walk remains the P7 mirror
the /arch path-1 ruling condemns, and the frontend NOTEs still block W-D2
on the wave-1 invariant ("int never produces a qualified binder") — the
reject's soundness argument needs that invariant **by construction**; the
suppressor cannot supply it (its failure mode is exactly the configuration
that forced the W3 revert). (d) The live-defect demonstration moves to the
unit tier, where it is *reachable*: precisely because the guard is
table-state-dependent, a pure fixture (design doc §3) can pin the state in
which suppression fails and show the scope-blind walk mis-qualify a binder
— RED before the fix, GREEN after. No prior live e2e demonstration is
required.

**W5-C1 acceptance (binding):**

1. The mandatory expansion-seam unit tests
   (`design/int/expansion-qualification-scope.md` §3):
   `qualify_skips_value_binders_and_local_reads`,
   `qualify_skips_let_and_match_binders`, plus one completeness cell per
   binder form (defn/fn/let/match — the shared-enumeration matrix).
   Authored **failing-first** against the scope-blind pass, with the
   fixture's `defining_modules`/table state constructed so the incidental
   availability skip-guard does NOT fire — this RED→GREEN unit flip is the
   live-defect demonstration replacing the evaporated e2e flip.
2. IQ-P1..P3 + the repl_persist `name`-param programs stay GREEN
   (must-hold fences; they are no longer flip targets).
3. The binder predicates promote to ONE shared home consumed by both walks
   (/review structural check — a second private enumeration is the P7
   mirror re-grown).

**Escalation clause:** if /dev(src) cannot construct a unit fixture in
which the scope-blind pass mis-qualifies a binder (i.e. the suppression
proves structural rather than table-state-dependent), C1 pauses and
returns to /qa with that evidence before landing — that outcome would be
the first genuine evidence against the live defect, and the C1/W-D2
sequencing would be re-adjudicated then.

**W6-W-D2 acceptance (binding; gate unchanged — C1 committed first):**
IQ-N1..N4 flip RED→GREEN (located value-level qualified-binder reject at
the three seams, span on the user's written form) while IQ-P1..P3 and the
IQ-N bare twins stay GREEN (the reject fires on the qualified SPELLING,
never on collision, and never on int's output).

| Row | Cell | As-built status (W1) |
|---|---|---|
| IQ-P1 | `(defn f [label] (wrap label))` — colliding defn param + foreign macro, compiles + runs | **BORN-GREEN fence** (`tests/qualified_binder_expansion_0670.rs::colliding_defn_param_with_foreign_macro_compiles_and_runs`) |
| IQ-P2 | `let` sibling | **BORN-GREEN fence** (`…::colliding_let_binder_with_foreign_macro_compiles_and_runs`) |
| IQ-P3 | verbatim FIXME repro via workspace stdlib (sanctioned exception) | **BORN-GREEN fence** (`…::greet_name_param_with_str_macro_compiles`) |
| IQ-N1..N4 | value-level qualified-binder negatives: defn param, fn param, `let` name, match var-pattern (+ bare twin) | **RED** (silent-accept today); flip = W-D2 acceptance |

The expansion-seam unit tests are /dev(src)'s to author (W5-C1 item 1
above; enumerated so nothing falls through the deferral — METHOD §2.2).

## 5. Track D — frontend: standing matrices (0676), BD-A flips, 0682 cells

### 5.1 The 0676 standing matrices (the class mechanism)

These two matrices are STANDING plan rows — they outlive the six known
cells and are the audit instrument for the class ("no matrix ⇒ each parser
grows its own subset"). /qa re-audits them whenever a new expression-position
or head parser appears (the rolling coverage-by-variants category).

**M1 — operand-position × {bare, ascribed, trailing-junk}.** Row per
expression-position parser; columns: bare accept (GREEN twin), `:Type form`
ascribed accept (spec §2.3.8 MUST — "an annotation MAY appear in EVERY
expression position"), trailing-form reject (located). Structural
acceptance beyond the cells: **every row routes its body through
`build_one_expr_at`** — the fix criterion is the ONE seam, and the /review
check is the grep (no expression-position parser calling raw `build_expr`
or hand-rolling its tail check).

| Operand position | bare | ascribed | trailing-junk |
|---|---|---|---|
| defn body (`parse_defn`) | GREEN | pinned family | GREEN (rejects, `:467`) — spot-fence |
| fn body | GREEN | spot-pin | NEW spot cell |
| if branches | GREEN | spot-pin | NEW spot cell |
| match arm body | GREEN | spot-pin | NEW spot cell |
| let VALUE | GREEN | spot-pin | NEW spot cell |
| **let BODY** (`build_let`) | GREEN twin in-file | **BD-A1 RED** | **NEW** |
| **impl-method body** (`build_impl_method`) | GREEN twin | **BD-A1 RED** | **BD-A2 RED** |
| **trait default-method body** (`build_method_sig`) | GREEN twin | **BD-A1 RED** | **BD-A2 RED** |
| **trace operand** (`build_trace`) | GREEN twin | **BD-A1 RED** | **NEW** |
| apply arg / vec element / top-level | GREEN | spot-pin | NEW spot cells |

New-cell directive: the two bold NEW trailing cells (let-body, trace) are
required; the spot cells land where /testing's authoring audit finds no
existing pin (expected ~4–6; report the audit table with the batch — a
position already covered by a committed cell cites it instead of
duplicating).

**M2 — head-parser × {bare arm, list arm} × {case accept/reject}.**

| Head parser | bare arm uppercase | bare arm lowercase reject | list arm uppercase | list arm lowercase reject |
|---|---|---|---|---|
| `build_type_head` (deftype) | GREEN | GREEN (`:599`) — spot-fence | GREEN | **BD-A3 probe → pin** (`:606` skips the check) |
| `parse_trait_head_shape` (deftrait) | GREEN twin | GREEN twin | GREEN twin | GREEN twin (checks both arms — the P7 mirror the fix copies) |

BD-A3's probe-first discipline stands (silent-accept vs late-incidental
determines the pin's class); the type-params any-case cell rides the probe.

**M2 type-param case ruling (/qa disposition item 3, 2026-07-20 —
SPEC-MANDATED REJECT, ruled from spec text, no user question needed).**
The W1 probe found `(deftype (Box A) …)` — an UPPERCASE type param —
silently accepted (`build_type_head` params loop, `ast_builder.rs:607-613`,
takes any symbol, any case). Spec §2.2.2 is decisive: *"Type parameters
MUST be lowercase symbols"*, with the EBNF `type_param = SYMBOL
(* lowercase *)`; §2.4.2 gives the semantic ground (lowercase = type
variable; an uppercase symbol is a named-type reference, which is not a
parameter binder). The silent accept is therefore a `class=silent-accept`
defect against a spec MUST — the same audit-R1 Done criterion the user
accepted at Phase 1 ("both `build_type_head` arms enforce the same case
rule") already covers it. New standing M2 rows:

| Head parser | type-param uppercase reject |
|---|---|
| `build_type_head` (deftype) | **M2-TP1: RED cell required** — `(deftype (Box A) …)` MUST be a located reject; /testing authors it in a **W-D1 rider** (`class=silent-accept locus=…build_type_head params loop`) |
| `parse_trait_head_shape` (deftrait) | **M2-TP2: probe-first twin** — §2.2.3 uses the same `type_param` production; probe `(deftrait (Functor F) …)`, pin per outcome in the same rider (green fence if already rejected, RED sibling if silently accepted) |

The fix rides the W-D1 case-mirror change-set (same wave as the BD-A3
list-arm name-case fix); the deftrait twin is the P7-mirror pressure.

Flips: the BD-A ×6 REDs + deftype-ctor-trailing ×1 flip with the
/dev(frontend) one-seam change-set (route the four positions through
`build_one_expr_at` + mirror the trailing rejection + mirror the case
check). A fix that greens the pinned cells but leaves any matrix row
un-routed does NOT close the class — the structural grep is part of the
wave's /review acceptance.

### 5.2 The 0682 conformance cells (user-ruled 2026-07-20; /spec scribes next, /dev(frontend) actions Phase 5)

Ruling: `:` is a `^`-style reader macro — whitespace between `:` and its
form ALLOWED (`: Int` ≡ `:Int`); the bound form MUST be a type expression;
`:foo/` ERRORS; bare `foo/` ERRORS anywhere; bare `/` (division) stands.

**As-built polarity (W1 verified, /qa disposition item 2, 2026-07-20)** —
the corrected polarity is absorbed here; the file is
`tests/ra_annotation_qualifier_0682.rs`:

| Row | Cell | As-built polarity (W1) |
|---|---|---|
| RA-P1 | Space tolerance, param position: `(defn f [: Int x] :Int x)` ≡ the no-space spelling — one test, both spellings, same result | **BORN-GREEN fence** (already works at HEAD) |
| RA-P2 | Space tolerance, expression position: `(let [x 1] : Int x)` ≡ `:Int x`; incl. list-form type `: (Fn [Int] Int)` | **BORN-GREEN fence** |
| RA-N1 | `:foo/` → located error (today: `read_qualified_tail` silently degrades to `:foo` — `class=silent-accept`) | NEG, **RED**; flips W-D1 |
| RA-N2 | `:a.b/` → located error (the dotted-loop swallow mirror; the S87 F5 consolidation removes the second swallow site) | NEG, **RED**; flips W-D1 |
| RA-N3 | bare `foo/` in value + operand position → located error | **BORN-GREEN ×2** (already errors located "expected local name after '/'"; fences through W-D1) |
| RA-N4 | bare `/` division GREEN fence: `(/ 6 2)` → 3 (Principle 16 stands — the reject must not over-reach) | POS fence, must stay GREEN through the fix |
| RA-N5 | bound form not a type expression → located error (`:3`) — asserts only the non-type-form reject (0589 family separate) | NEG, **RED via incidental-artifact assertion** (`:3` errors today, but only via the incidental "defn has extra forms" from the degraded tokens; the cell asserts that artifact ABSENT + a located reject); flips W-D1 |
| RA-N6 | `/bar` (empty-module-half) → located error, value + operand twins (user confirmation 2026-07-20; 0686/0687) | NEG, **RED ×2 via incidental-artifact assertion** (`/bar` errors today only as the `/`+`bar` split artifacts — "extra forms" / "undefined variable: /"; the cells assert those ABSENT + the located qualifier reject); flips with W-D1's `read_operator` guard |

Sequencing: cells authored QA-first in Stage 1 (done, W1); the five REDs
(RA-N1, RA-N2, RA-N5, RA-N6 ×2) flip with the /dev(frontend) W-D1
change-set; /spec's scribe (§1.4.5/§2.4/§8.5 — landed, incl. the 0686
`/bar` enumeration) precedes the fix so `// spec:` anchors resolve. The
"consume_dotted_module_path exists once" structural criterion joins the
wave's /review check.

### 5.3 0660 reserved rows

/design(frontend)'s enumeration (ctor/field/platform binder rows across all
three sides) lands this sprint; its output feeds cells into the BD-M1
family. Rows reserved — /qa adds them when the enumeration table exists
(coordinate with the M2 deftype rows; do not pre-guess the enumeration).

## 6. Track E

- **0590** (resolver-mirror convergence onto mint capability) is sequenced
  LAST among typecheck deployments and defers with a note if the carrier
  consumes the sprint. Acceptance if it lands: the four type-position
  mirror sites converge (structural grep) + existing mint-family pins
  (0589/BD-M5 rows, QQ negatives) stay green.
  **`_hkt` probe outcome (W1; /qa disposition item 6, recorded):** the
  never-error `Named` arm suspicion does NOT reproduce e2e — the
  `form.rs::check_type_expr` pre-walk errors FIRST (`unknown type
  \`Bogus\``), masking the `_hkt`/`_hkt_impl` `Named` mint from every
  source-reachable shape. Pinned as a **born-green fence**
  (`tests/hkt_named_arm_probe.rs::hkt_sig_unknown_named_type_rejected_not_silently_minted`
  + valid-Functor green control): if the 0590 convergence (or any
  refactor) removes the pre-walk barrier, the never-error arm surfaces and
  the fence flips RED. **The fence stands; the latent defect is a
  UNIT-TIER obligation for the 0590 deployment** — its /design+/dev
  deployment MUST either retire the never-error `Named` arms in the
  convergence or land a unit pin exercising them directly (the pre-walk is
  the only barrier; enumerated here per the deferral discipline so it
  cannot fall through).
- Archive-demo de-rot + "in expansion of" finalize-path: /repl-side and
  display-side items — no plan rows beyond the existing demo gates.

## 7. Wave-flip ledger (Phase-4 input; **RE-BASED post-W1 as-built, /qa 2026-07-20**)

| Wave (per SPRINT §Required sequencing) | REDs that flip | Must-hold fences |
|---|---|---|
| Carrier wave (types+typecheck+backend+bump, ONE change-set) | F-D2-10 ×4 (re-shaped per CA-1) | CA-2..4 born-green, F-D2-8 declaration gate, F-D2-4, MC-N1 inversion set, CS-1/CS-2, golden lane |
| Typecheck settlement-consumer drain (before/interleaved) | MC-X4, MC-X4b, MC-X5, PS-SH1 residual + §3.5 new ×2 (returned + container value-ref) | MC-X4 typed-field twin, MC-G1 fences, standalone twins, §3.5 single-sig value-ref GREEN control |
| Track B consume-contract change-set(s) (behind §1 disposition — now discharged) | BI-G (+link twin), BI-F, BI-C-off (+link twin), BI-B-cow ×2, BI-I1 ×2, BI-H-heap ×2 (rider, §2), then F-R1 ×2 (backend `protect_return_value` entry-main seam) + MS-P8 ×2 (backend TCO tail-jump param-flush seam) per their own backend fixes — both adjudicated backend per §2.1, no intrinsics deployment | A/E ×2 + A-link fence, H scalar control, l_c3 ×2, `vec_lifecycle`, match-cow ON twins, golden |
| Track C: 0638 fix | 0638 ×5 (both mode-faces in one change-set) | marshal sustained-repetition guards |
| Track C: 0604 chokepoint | none (structural gate — census + unit test + sweeps) | twin guards ×2 GREEN |
| Track C: 0670 int fix (W5-C1; F8 wave 1) | **none e2e — acceptance is the §4.3 expansion-seam UNIT flip** (RED-first fixture defeating the availability skip-guard) | IQ-P1..P3 born-green fences + repl_persist `name`-param programs stay GREEN |
| Track D: frontend one-seam + case-mirror (W-D1) | BD-A ×6, deftype-ctor ×1, M1/M2 new cells incl. M2-TP1 (uppercase type-param reject, rider) | M1 GREEN column + M1 spot fences, M2-TP2 deftrait twin per probe, structural grep |
| Track D: 0670 wave 2 (W-D2, reject re-lands; requires C1 committed) | IQ-N1..N4 | IQ-P1..P3 + IQ-N bare twins stay GREEN (the reject must not re-break the valid program) |
| Track D: 0682 fix (rides W-D1) | RA-N1, RA-N2, RA-N5, RA-N6 ×2 | RA-P1/P2 + RA-N3 ×2 born-green, RA-N4 division fence |
| Track E: 0590 (if it lands) | none | `_hkt` born-green fence ×2 (§6) + mint-family pins; unit-tier `Named`-arm obligation |
| W7: /dev(typecheck) rider (adjudicated W3; priority over the conditional 0590 slot) | MS-P7 (§3.6 adjudication: typecheck ownership, `MayAliasOf` projection-out reaching context; class re-labeled `uaf`) + F-D2-11/F-D2-12 IF the §3.8 probes confirm RED | Safety-lane clean/green cells both toggles; MS-P6 capability cell re-planted in the flip change-set (§3.6 flip hazard); W4 fences: no backend workaround, pin color-change reported to /qa |

## 8. Stage-1 battery — AS BUILT (W1 delivered 2026-07-20; /qa re-base)

**Delivered: 45 new tests — 17 RED defect cells + 28 born-green fences.**
Suite at W1 close: **5033 run / 4985 passed / 48 failed / 1 skipped** —
the 48 = the 31 S113-close originals (all present, zero drift) + the 17
intended new REDs; zero regressions, zero born-green false-REDs. RED
reconciliation was EXACT (31/31); BI-I1 + F-R1/MS-P8 `// defect:` locus
updates done; corpus check CLEAN (the `/bar` guard breaks no fixture).

Notable polarity deltas from the planned battery (dispositioned §4.3,
§5.2, §2, §3.5, §6): IQ-P1..P3 born-green (not RED — 0670 e2e
non-reproduction; C1 acceptance moved to the unit tier); RA-N3/P1/P2
born-green, RA-N5/N6 RED via incidental-artifact assertions; the BI-T heap
green twin replaced by the scalar control; PS-SH1 = +2 positions + control;
the `_hkt` probe pinned born-green.

**Outstanding /testing riders (post-Stage-1, small):**

| Rider | Cells | Wave |
|---|---|---|
| M2 type-param case (§5.1 ruling) | M2-TP1 RED ×1 (`(deftype (Box A) …)` located reject) + M2-TP2 deftrait probe/pin ×1 | with/before W-D1 (W6) |
| BI-H-heap (§2) | ×2 RED (bare single match forwarding a fresh heap vec: inline + fn-return) | pre-W4 rider |
| 0671 asking-module twin, riders 0674/0675 | per §4.1 | with their Track-C change-sets |
| Swallow-sibling probes (§3.8, W3 disposition) | P1 value-position no-impl + P2 auto-curry no-impl, ×3 modes each; author F-D2-11/F-D2-12 RED only where a probe demonstrates the gap | before/with W7 |
| MS-P6 capability re-plant (§3.6 flip hazard) | re-plant `safety_lane_detects_cow_set_read_corruption_capability_green` on a synthetic fault (or retire with rationale) + refresh the MS-P7 pin's stale flip-trigger/locus comments | same change-set as the MS-P7 flip (W7) |

Unit-tier (/dev, enumerated so nothing falls through the deferral): §3.4
items 1–5 (carrier + escape-fact), §4.2 item 4 (0604 chokepoint), the
0670 expansion-seam tests (**now W5-C1's acceptance**, §4.3), the 0590
`Named`-arm obligation (§6), per-fix unit tests per METHOD §2.2 throughout.

## 9. Traceability

- §7.11.2 bands flip to `[Tested+Neg …]` at the carrier-wave close (CA-1).
- §2.3.8 / §5 binder bands flip at the Track-D closes; §1.4.5/§2.4/§8.5
  annotation bands flip after /spec's 0682 scribe + the RA flips.
- `spec/12-runtime.md` §12.1 rows upgrade `+Neg` as the BI family flips.
- Run `spec_link_check.py` + `spec_coverage_reconcile.py` before any
  annotation flip; re-run at Phase 6.
- Phase-6/7 audit: every remaining RED traces to an open owner+trigger;
  expected end-state = the 31-RED ledger drained except explicit carries
  (MS-P7 if evidence arrives late; anything Phase 4 defers with rationale).

## 10. W1 findings disposition record (Phase 5 post-W1, /qa, 2026-07-20)

The six /testing findings (SPRINT.md §Notes, W1 DELIVERED entry), each
dispositioned in place above — this section is the index:

1. **0670 e2e non-reproduction** → §4.3 re-base. **C1 ships as designed**;
   the architectural fix stands (scope-blind walk = the wrong mechanism;
   the availability skip-guard is a table-state-dependent suppressor, the
   0604-heisenbug class, not a fix). W5-C1 acceptance = the RED-first
   expansion-seam UNIT flip + IQ-P/repl_persist fences + shared
   binder-predicate home; W6-W-D2 acceptance = IQ-N1..N4 flip with IQ-P +
   bare twins green; C1-before-W-D2 gate unchanged. Escalation clause
   recorded (§4.3) if the unit fixture cannot defeat the suppressor.
2. **RA polarity** → §5.2 absorbed (RA-N3/N4/P1/P2 born-green; RA-N1/N2
   RED; RA-N5/N6 RED via incidental-artifact assertions; 5 REDs flip
   W-D1).
3. **BD-A3 uppercase type param** → §5.1 RULED spec-mandated (spec §2.2.2
   "Type parameters MUST be lowercase symbols" + §2.4.2; audit R1 Done
   criterion). M2-TP1 RED + M2-TP2 deftrait probe twin, /testing W-D1
   rider. No user question — the spec text is decisive.
4. **BI-T cell-H** → §2 scalar control substitution ACCEPTED;
   heap-forward-through-match broken wholesale; NEW row BI-H-heap ×2 RED
   (inline face was unaccounted) as a pre-W4 rider.
5. **PS-SH1** → §3.5 matrix-completion shape ACCEPTED (+2 positions +
   single-sig control); counts updated.
6. **0590 `_hkt`** → §6 recorded: e2e mask = `form.rs::check_type_expr`
   pre-walk; born-green fence stands; `Named`-arm latent defect is an
   enumerated unit-tier obligation on the 0590 deployment.

Ledger (§7) and counts (§8) re-based to the as-built battery: 45 tests,
17 RED + 28 born-green; suite 5033/4985/48/1.

## Next skills

- `/testing` — riders (§8): M2-TP1/TP2 (with/before W-D1), BI-H-heap ×2
  (pre-W4), the §3.8 swallow-sibling probes (before/with W7), and the
  MS-P6 capability re-plant with the MS-P7 flip (W7).
- `/dev`(typecheck, W7 rider) — MS-P7 fix per the §3.6 adjudication
  (ownership `MayAliasOf` projection-out; falsifiability check first),
  priority over the conditional 0590 slot; then F-D2-11/12 if the probes
  confirmed RED.
- `/dev`(backend, W4) — carry the three §3.6 W4 fences into the dispatch
  brief: no MS-P7 workaround in the consume contract, the ARG-TEMP
  `MayAliasOf` consume-arm unit confirmation, pin color-change reporting.
- `/dev`(src, W5-C1) — the expansion-seam unit tests are the wave's
  acceptance (§4.3), authored RED-first; escalate to /qa per the §4.3
  clause if the suppressor cannot be defeated in a fixture.
- `/spec` — 0682 ruling scribe (queued in the serial order; before the
  Track-D 0682 fix so anchors resolve).
- `/design`(typecheck) — carrier doc §3–§5 elaboration; §3.4 unit items
  1–3/5 named in its plan; MS-P7 evidence if its deployment reaches the
  mode seam.
- `/design`(backend) — 0668 contract, UNBLOCKED by §1 (the capture row is
  yours; B-2's fact half is not); 0664 §13.5/§13.7 correction first-within.
- `/design`(int) — 0604 isolation contract record (§4.2 item 5).
- `/testing` — Phase 5 Stage 1: verify the RED inventory live, then author
  §8's battery QA-first; report any inventory drift to /qa.
- `/sprint` — Phase 4 wave assignment consumes §1, §3.6, and §7.
