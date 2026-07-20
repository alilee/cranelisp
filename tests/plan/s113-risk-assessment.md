# S113 W0 — global correctness-risk assessment (USER GATE artifact)

`/qa`, 2026-07-19, Phase 3. **Purpose (user-directed, risk-first)**: assess
memory-safety soundness *in the context of the global solution risk* — is it
the biggest risk to correctness? — and only if the assessment confirms it,
recommend how deep the W5 reliability build goes. The USER decides depth at
the gate; this document recommends with grounds.

Landed as its own file (not folded into `memory-safety-coverage.md`): that
document is the *standing strategy* and stays sprint-independent; this is the
one-shot gate artifact the user rules on. The strategy doc is cited, never
restated.

Method: each live risk family is ranked on four axes — **worst-case
severity**, **live evidence** (confirmed reachable defects), **detection
posture** (can the suite see the *next, unknown* instance of the class?), and
**managed state** (pins + a scheduled wave). The ranking orders *residual,
unmanaged* risk — a family the suite can see and a wave will fix is lower
risk than a family with fewer known defects that nothing can detect.

No test run was performed for this assessment (Phase-3 constraint); all
suite-state citations are to committed records (`PLAN.md` §S111 I.1–I.5,
§S112; `sprints/archive/sprint-112.md` §Outcome; `memory-safety-coverage.md`
§5).

## §1. The ranking

| # | Risk family | Worst-case severity | Live evidence | Detection posture (the deciding axis) | Managed state |
|---|---|---|---|---|---|
| 1 | **Memory-safety soundness** (`uaf` / `rc-miscount` / `drop-glue-underkey` / false-`Fresh` elision / macro-clause marshalling) | **Silent heap corruption, wrong values, UB** — the only family whose failure face can be *undiagnosed wrong output* or delayed corruption rather than an error | 4+ distinct live mechanisms, all confirmed reachable: 0641 family **8 committed REDs** (`tests/false_fresh_provenance_residual.rs` — B-1/B-2/I-1/I-2 × REPL/`--link`; B-2/I-2 additionally yield **wrong VALUES with the analysis off** — 55-for-99, 190-for-9, no crash, no error: PLAN §I.4); 0633 drop-glue under-key **3 committed REDs** (concrete-args axis ×3 modes) with the module-axis cell currently **unguarded** (DG-R2 was re-attributed to a separate entry-`main` teardown leak — itself a live `rc-miscount`); 0638 deterministic heap corruption on the macro-clause JIT path (garbage header tags in RC trace; repro preserved in the FIXME, **not yet committed**); 0637 latent cache-trust UB obligation | **Structurally blind.** ≈97% of the suite cannot see a UAF that does not perturb output; >98% cannot see a leak; `RC_DEC_CHECK` (the strongest deterministic UAF signal) asserted **nowhere**; the oracle covers ≈0.6%; the ≈2,670-test unit tier executes no JIT code (§5 of the strategy doc). **Every S111 member was found incidentally** — adversarial review or a stdlib migration — and the only working detector demonstrably does not scale: each fix needed *another* adversarial pass to find the next layer (CS-1.1 → 0640; CS-5 → 0641) | **Unmanaged**: no standing gate exists; the strategy is designed (`memory-safety-coverage.md`) but unbuilt; the 0641 fix is deliberately held behind the gate (user directive, §1.5) |
| 2 | **Mono/carrier family** (R1 ×2, R2, D3, TB-24, D1, D2 — `wrong-reject` / `carrier-loss` / `check-gate-leak` / display) | Valid programs fail **loudly** at compile/codegen (incl. idiomatic prelude `+`); D1 is display-only | 6 pinned defects — every one a committed failing-not-ignored RED | **Good.** The suite sees every known member; S112's twin/equivalence discipline caught the unknown members (B1, I1, R1, Pin-4 entanglement). The confirmed gap is the **carrier × reaching-context** matrix (R2 + D3 = two producer misses in one family — the §11 ruling-1 trigger has now fired) — a scoped sweep, not structural blindness | **Managed**: W2 dispatch, fences + twins planned (`s113-test-plan.md` §3). Residual = wrong-accept inversion during the fix (the S112-1 class) — guarded by inversion fences |
| 3 | **REPL persistence data-loss** (RT-4 ×2 — impls dropped from regenerated `user.cl`) | User work silently lost; surfaces at reload, possibly sessions later | 2 pinned REDs; class `enumeration-miss` with a settled fix model (D45-as-amended storage) | Good — deterministic, pinned; the risk is enumeration *completeness*, cured by the matrix discipline (`resolve-home-enumeration.md` §3) | Managed: W4, design rooted at the settled model (arch seam flag iv) |
| 4 | **Cache/persisted-trust boundary** (R6, 0637) | Latent UB / silently-resurrected stale judgment (schema-20 B-2 entries falsified the S112 no-bump rationale — the class is live-adjacent) | No live defect; one open forward obligation (0637, co-lands with its first consumer) | Partial — `callable_got_slot` asserted; other persisted indices unvalidated | Managed-by-discipline: single-bump window held S112; W5 owns the sprint's only bump; tier-3 generalization is §6 task 3 |
| 5 | **Shared-state write race** (0604 / R7 `unasserted`) | Stdlib module unimportable when it fires (spec-correct poison on a phantom write) | ~320 cumulative no-fires; unlocatable; fired only in one S109-era environment | Poor for the *seam* (no assertion exists — the register's named hole) but the *blast* is loud when it fires | Being converted: the W4 rider lands the R7 `debug_assert!` + trace at every live-table insertion seam — observability before fix (S111 P5 conclusion) |
| 6 | **Binder/frontend silent-accepts** (binder ×3, 0589) | Name pollution / deferred incidental errors — low severity, but silent | 3 pinned REDs + 0589 pin | Good — pinned; the W1 corpus sweep bounds the flip blast radius | Managed: W3, one shared seam (arch Q3) |
| 7 | **Stdlib-gate blindness** (0605) | A stdlib-breaking compiler regression ships with zero signal (the S109 lesson: 27 self-tests failing invisibly) | Historical instance (0604 blast); no current known breakage | Structural gap until the gate lands | Managed: W1, gate design settled in the FIXME |

## §2. Verdict — YES, memory-safety soundness is the top correctness risk

The ranking is not close. Family 1 uniquely combines:

1. **The worst severity face** — every other family fails *loudly* (a
   diagnostic, a hang, a visible data loss at reload); this one corrupts
   silently or returns plausible-wrong values.
2. **Structurally-zero detection of unknown members.** Families 2–7 are
   pinned or boundable; the suite would go RED on their recurrence. For
   family 1 the S111 quantification stands: the safety-signal surface is two
   orders of magnitude thinner than the output-assert surface, and the
   sole effective detector (refute-instructed adversarial review) has a
   demonstrated one-layer horizon — each fix required a fresh adversarial
   pass to find the next laundering site.
3. **Multiple confirmed-reachable live mechanisms** — provenance laundering
   (0641), identity under-keying (0633 + the unguarded module axis),
   macro-clause marshalling corruption (0638), entry-`main` teardown leak,
   and the latent trust-boundary obligation (0637). These are not one bug;
   they are one *class* (P25's unsound-narrowing shape) surfacing at five
   seams in two sprints.

**The honest counterweight**, stated so the gate is a real decision: family 2
causes more *user-visible pain today* (six defects, prelude `+` among them)
and family 3 loses user data. But both are pinned, scheduled (W2/W4), and
detectable — their residual risk is fix-regression, which the twin fences
carry. Choosing depth on family 1 does not trade against them: the defect
waves run regardless (W1 fences are explicitly ungated on this decision).

**Confirmation: go deeper.** The assessment confirms the premise of the
carried track — proceed to the W5 build at the depth recommended below.

## §3. Depth recommendation for W5 (tier selection over the mechanism palette)

The palette maps 1:1 onto the `safety-invariants.md` §2 ladder (arch Q1 — no
parallel taxonomy). Recommendation per tier, in **build order**:

| Order | Ladder tier | Palette item | Recommendation | Grounds |
|---|---|---|---|---|
| 1 | **Tier 4** — differential oracle | oracle vs default mode | **BUILD, FIRST change-set of W5** — the `assert_safety_matrix` combinator + `tests/safety_oracle_lane.rs` + seed corpus + retro-wrap (strategy §1.3/§6 items 1+3) | The class-closing gate: the whole false-`Fresh` family fails it *mechanically*, no enumeration needed. The user's own binding sequencing (§1.5) gates the 0641 fix on it. Fully designed; ~1 `/testing` dispatch; ≤60s added wall. Acceptance is pre-stated: the committed 0641 B-1 RED goes RED **under the lane** on day one |
| 2 | **Tier 5** — dynamic lanes | diagnostic modes: no-reuse-after-free quarantine, scrub-freed poisoning, paired alloc/free hard-check | **BUILD** — intrinsics-internal, env-gated allocator behavior; the modes join the lane's signal set | They convert layout-luck UAF into *deterministic* RED — multiplying tier 4's teeth — and make 0638/0633-class faults name their seam at the faulting op instead of N crossings later. No ABI/types change (arch revision 2: `alloc.rs` already owns the metadata and detects double-frees). Counters largely exist (`RC_STATS`); the delta is the hard-check face + standing `RC_DEC_CHECK` positive assertions (today: zero) |
| 3 | **Tier 3** — seam assertions | assertion density at RC/alloc seams | **BUILD** (small) | Heap-header-integrity / negative-RC / free-of-untracked asserts at the intrinsics alloc/dealloc seams; cheap, always-on in debug. The int-side R7 asserts already ride W4 **ungated** (arch revision 7) — correctly outside this gate |
| 4 | **Tiers 1–2** — static analysis per P25 | compile-time invariant narrowing | **BUILD** — the `/design`(typecheck) §3 frame: origin lattice with explicit ⊤ + enumerated/classified transfer-rule table (§15) + the P20 conditional/unconditional origin split (§3b), then the 0641 B-1/I-1/I-2 fixes *as rule-table corrections inside it*; schema 21→22 if the §3b split lands (W5 owns the sprint's only bump, arch revision 4). **Plus the paired `/dev`(backend) B-2/I-2 consume fix** — those two carry an ownership-INDEPENDENT wrong-value factor (PLAN §I.4); the typecheck axis alone cannot flip them | The only *preventive* tier — everything above detects. The 8 committed 0641 REDs cannot flip without it, and the user directive forbids instance-patching ahead of the mechanism. Capacity fallback if W5 runs heavy: land the lattice + rule table + B-1/I-1 corrections; the §3b origin split (and its schema bump) may slip to S114 — at the cost that register row R1 stays `example-tested` on the producer seam another sprint |
| — | (Tier-4 extension) | generative harness v1 (strategy §2) | **DEFER → S114** (stretch goal only if W5 runs light) | The oracle lane + seed corpus captures most of the near-term value; the generator's marginal contribution is composition coverage of *future* unknowns, and it is explicitly the second dispatch **after** the lane exists. Deferring it does not leave a live defect unguarded |

Also inside W5 per this ordering: the 0633 re-key fix (R4 register row —
`/dev` backend, with the module-axis battery cell re-authored under the lane,
see `s113-test-plan.md` §2), and the R4 symbol-mint census + R6 trust-boundary
census as the `/design`(backend) §6 tasks 2–3 — design work, no gate needed.
0637 stays a forward obligation co-landing with its first consumer (arch
register note: do NOT let it force a consumer into W5 the gate doesn't
justify).

**What this depth buys, stated as acceptance:** at S113 close the §5 exposure
table re-grades — oracle + RC-balance + DEC_CHECK + `--link` faces standing
over the seed corpus and every `[oracle]`-marked row; the 0641 family flips
under the gate (not around it); the next false-`Fresh`-class defect is found
by a RED, not by a reviewer.

## §3a. Gate outcome + day-one confirmation (addendum, 2026-07-19 W1)

**The user approved the §3 depth recommendation AS-IS** (tiers 4+5+3+1–2;
generative harness → S114); the MS-P probe slice was ungated into W1.

**The verdict's structural-blindness argument was confirmed empirically on
the lane's first day**: MS-P2 caught a previously-unknown member of the
class — the direct COW-set→project shape (`(vec-get (vec-set v 0 9) 0)`)
runs correctly under `--run` and JIT modes but deterministically aborts
under `--link` ("corrupted double-linked list"); the §3.7 `MayAliasOf` fix
does not cover it. Pinned RED
(`safety_oracle_lane.rs::safety_lane_cow_set_read_link_corruption_red`,
`found=S113`); attribution + flip trigger in `s113-test-plan.md` MS-P7. This
is row-1's detection-posture claim made concrete: a defect no one enumerated,
invisible to the entire output-assert suite (its `--run` face is *correct
output*), found mechanically by the gate within hours of the gate existing.
The §1 ranking's evidence column for family 1 now reads **5+ live
mechanisms**.

## §4. What the gate does NOT block

Per arch seam flag v, dispatched so the user decision never delays defect
work: W1's D2 fences, fence-inversion sweep, binder matrix, qualified-head
corpus sweep, 0605 gate, and the 0638 repro capture are **ungated** (0638 is
an ordinary deterministic defect pin, not a probe). Only the W1
memory-safety-probe slice (lane scaffolding pulled early) and the W5 build
itself wait on the ruling. The W4 R7 seam asserts ride ungated (arch
revision 7 — they are the "assertion density" palette item at a seam whose
ghost has cost ~320 diagnostic runs).

## §5. Cross-references

- `tests/plan/memory-safety-coverage.md` — the standing strategy this
  recommendation instantiates (§1 gate design, §2 generator, §5 exposure).
- `design/arch/safety-invariants.md` — §2 ladder, §4 register (R1–R13), §6
  cascade; Principle 25.
- `tests/plan/PLAN.md` §S111 I.1–I.5 — the committed defect/attribution
  records cited per row.
- `tests/plan/s113-test-plan.md` — the sprint plan consuming this verdict.
- `tests/plan/risks.md` §"S113 risk read" — the compact register form.
