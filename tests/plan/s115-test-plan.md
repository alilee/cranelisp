# Sprint 115 — sprint-wide test plan (Phase 3, 2026-07-20, /qa)

Scope: SPRINT.md Tracks A–D as revised by the Phase-2 /arch review
(sign-off-with-revisions: GOT-slot conditional two-owner split + carrier-state
dump; 0604 `prelude_write_is_closure_valid` comment rider; R6 →
/dev(backend, cache)). This plan is the continuation of
`s114-test-plan.md` §11/§12 — the carry attributions and fix constraints
recorded there are BINDING here and are not restated in full; each row cites
its section. Companion: `s115-instrumentation-matrix.md` (Track B — the
owed-instrumentation items O1–O5 whose test rows live in §3/§6 here).

**Live baseline (this session, ONE sanctioned run at HEAD `5ba28de8`):
5164 run / 5153 passed / 11 failed / 1 skipped.** The 11 REDs are exactly
the attributed carry set (§1) — zero unattributed REDs, zero drift from the
S114 close accounting. Neither named flap manifested in this run (0694
nullary GREEN in-suite; agent lane runs separately via its launcher). Per
the standing counting convention: **stable-REDs-exact = 11 + named flap set
{0694 nullary load-flap, agent-lane spawn-contention (`agent::yes_flag`
class)}** — one observation; certification needs ≥2 identical runs (SPRINT
exit) and ≥3 for the 0694 verification (§2).

## 0. Risk read (shapes depth)

1. **Instance-patching the MS-P7 family** — the named anti-pattern (a 5th
   per-consumer arm; the W7 arm was the 4th). The §1.1 rows carry the
   family-grain invariant as their acceptance wording, and /review's
   structural check (rule-table rows, no new consumer arm) is part of the
   flip acceptance, not a separate nicety.
2. **A leak fix converting to an under-count** — the RC-release sweep touches
   protect/release polarity at two seams. The both-polarity fence
   (`allocs == deallocs` EXACTLY, s114 §2.1) binds every §1.4 flip; the
   tier-4 lane + RC_STATS pins are the acceptance instrument.
3. **Wrong-owner GOT-slot fix** — the pair sits on opposite sides of the
   carrier contract (arch §3); fixing both at the backend without the
   carrier-state evidence would be the guess-and-patch the dump exists to
   prevent. No §1.5 fix wave opens before the dump exists.
4. **0604 gate false-fire** — the corrected predicate rejects MORE than the
   landed one; the false-fire fence (§3.2 cell 2, the declared-in-closure
   positive incl. the subtree-private re-export shape) is authored WITH the
   trigger, and the ≥25× no-regression sweep + the two GREEN twins guard the
   real stdlib.
5. **Wrong-polarity 0702 pins** — polarity is gated on the /spec user ruling
   (running in parallel this phase); §4 pre-authors BOTH polarities so no
   pin is committed against a contested reading (S109 lesson).

## 1. Track A — the 11 carry REDs: flip constraints

Live-verified inventory (test names exact, from this session's run). Every
fix lands with its unit test per METHOD §2.2; flip-verify against the cited
attribution.

### 1.1 MS-P7 chained-face family ×2 — /dev(typecheck) via /design(typecheck)

- `safety_oracle_lane::safety_lane_chained_nested_cow_projection_returns_set_value_abort_free_red`
- `safety_oracle_lane::safety_lane_chained_let_bound_cow_projection_returns_set_value_abort_free_red`

Binding (s114 §3.6 second adjudication + /arch P2 §2 — no further /arch
ruling needed):

1. **Family-grain invariant stated by the fix**: *every may-alias link whose
   accounting includes a consumer-emitted release needs its protect*. The
   fix lands as **§16.2 rule-table rows/corrections** in
   `design/typecheck/ownership-inference.md` — NEVER a 5th
   per-consumer/per-context arm. /review acceptance includes the structural
   check.
2. **0693 fence lands BEFORE/WITH** (re-anchored trigger fires here): the
   R3-gate mirror consolidation (ONE shared predicate or
   producer-recorded retain decision) + the unit disagreement fence over the
   §13.5-style matrix (builtin/user-named × live/non-live × escapes
   true/false/absent × return-source × both toggles, asserting
   `mirror == producer-emitted-inc?`). The chained-face escape-fact
   correction reopens 0693's masked channel — landing the fix without the
   fence is a plan violation to report.
3. **Conditional-container face is probe-first**: /testing probes the
   If/Match-shaped container feeding the projection; pin ONLY a
   demonstrated RED (s114 §3.6 face 3). A green probe pins as a born-green
   fence with the probe recorded.
4. **Must-hold fences**: the whole-value nested-transfer negative control
   (caller-projects) stays GREEN; the immediate-face W7 flip
   (`…cow_set_read_returns_set_value…`) stays GREEN; lane clean/green cells
   both toggles; golden CLIF lane (re-baseline only in the fixing
   change-set, extension ≠ re-baseline).
5. **Flip verification**: both cells under the lane, both toggles × 3 modes
   (the combinator does this by construction).
6. **Carrier-enrichment contingency**: if the family rule needs a new
   `ResultMode` shape / advisory fact, that is a `cranelisp-types` edit —
   FIXME `target: /arch` + approval + ONE schema window (22→23), surfaced AT
   Phase 3/4, never mid-wave (arch §2 constraint 2). This plan assumes NO
   bump; a second invalidation event is reported, not absorbed.

### 1.2 0719 wrapper-indirection carrier-loss ×1 — /dev(typecheck)

- `mc_x4_consume_at_distance_0719::multi_sig_return_through_wrapper_indirection_infers`

Binding (s114 §12 item 5): the acceptance bar is the **§5.1.2
equivalence-TWIN assertion** — the collapsed multi-sig form and its
two-function twin must BOTH compile AND agree on output. "Monomorphise OR
reject cleanly" (the X4b bar) is too weak — it lets a §5.1.2 wrong-reject
read as green. /testing's reduction work continues to name the
discriminating axis (free-var-through-bound-parameter distance is the named
axis; the exemplar-combination remains unreduced — partial reductions commit
with the FIXME note). The three born-green single/double-axis controls
landed S114 must stay GREEN. Exemplar rider on flip: /port's
`make-grid`/`peers` collapse trigger re-words per s114 §12 item 5 (owner
/port, at next touch).

### 1.3 0709 occurrence-rule enforcement ×2 — /dev(typecheck)

- `nondispatchable_trait_method_0709::nondispatchable_method_rejected_at_declaration_with_occurrence_reason`
- `nondispatchable_trait_method_0709::nondispatchable_method_call_neg_no_codegen_undefined_function`

Binding (s114 §12 item 2 — spec-settled, no user question): rejection at
DECLARATION with the §7.1-pinned reason substring ("no occurrence of the
implementing type"); the negative twin (no codegen `undefined function`
leak) flips as a consequence. Seam: `check_form_register` TraitDecl arm.
**GREEN control must hold**: `(deftrait Zero (z [] self))` stays accepted
(§7.1's own example). Unit test at the registration arm (accept/reject pair)
per METHOD §2.2. Located error uses existing error machinery (arch §7 — no
types edit).

### 1.4 Backend RC-release sweep ×3 — /dev(backend), ONE change-set

- `adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2`
- `adt_wrapped_supersede_leak_0720::adt_wrapped_supersede_loop_does_not_leak`
- `adt_wrapped_supersede_leak_0720::adt_wrapped_supersede_residue_does_not_scale_with_n`

Binding (s114 §11 item 4 + §11.1 item 2 + §12 item 6): ONE sweep covering
(a) the entry-`main` IO-return heap-payload leak — **BOTH toggle faces**
(the pinned toggle-off face is oracle-lane-critical; the toggle-ON face is
also unguarded per the drift note — the fix covers both, and /testing
assesses a cheap ON-face pin in the same change-set); (b) the 0720
ADT-wrapped COW supersede release (TCO tail-jump superseded-param, the
MS-P8 sibling — bare-vec twin GREEN control must hold). Fences binding on
BOTH fixes: `allocs == deallocs` EXACTLY (never leak→under-count); the
entry-protect suppression licensed ONLY by the entry-`main` single-consumer
contract — the general G2/item-26 protect must not weaken (§2.1 fence);
the MS-P8 flush balances in both conj arms. Acceptance instrument: the
tier-4 safety lane + the RC_STATS pins (arch sequencing item 4). Unit tier
per METHOD §2.2 at each seam (enumerated: the tail-jump flush arm for the
ADT-wrapped param shape; the entry-frame protect license under both
toggles). Exemplar parity expectation updates when both closes (s114 §2.1).

### 1.5 GOT-slot carrier-loss pair ×2 — conditional two-owner split (arch §3)

- `fn_as_value_carrier_loss::trait_operator_partial_app_impl_present_has_got_carrier`
  (fn-as-value `'='` — provisionally typecheck PRODUCER gap)
- `shadowing_scope_lookup::let_shadowed_trait_operator_auto_curry_resolves_to_local`
  (0705 AutoCurry-over-local — CONSUMER totality gap, backend)

Binding: **no fix wave opens before /design(backend) produces the
carrier-state evidence dump** — per repro, ONE keyed-read trace at the
wrapper-emission seam (`VarRef` verdict + `ApplyRef` + slot presence). The
dump DECIDES:

- `'='` arrives `ViaCallee` → both collapse into ONE backend totality
  change-set (the wrapper-emission seam total over the closed carrier sum
  {`Dispatch(FQ)`-slotted, `ViaCallee`+`VarRef::Local`}; anything else = a
  located producer error).
- `'='` arrives `Global`/`Dispatch` with no slot carrier → its fix is
  typecheck-side (mono_collect fn-value rewrite seam, s114 §11 item 5's
  provisional attribution) and rides a typecheck wave; Phase 4 holds the
  conditional slot.

Either way: 0705's fix adds the curry-the-local-closure-value emission arm
(backend). **MC-E1 protocol**: any pin color-change under either change-set
is REPORTED to /qa as attribution evidence, not treated as a win or
regression. Unit tier: the emission-seam totality (each carrier state → its
arm; the illegal state → located error) per METHOD §2.2. **Mask note
carried from s114 §11 item 5**: when the fn-as-value pin flips, /qa
re-probes the true late-pinning auto-curry shape and authors the deep
F-D2-12 cells then.

### 1.6 Impl-redefinition hot-reload ×1 — /dev(src)

- `impl_redefinition_dispatch::reimpl_either_dispatches_new_or_notices_not_replaced`

Binding (user ruling S114 close; arch §5): **the pin's hot-reload branch is
the REQUIRED behavior** — a same-type re-impl takes effect (GOT-patch path,
same slot re-pointed); a type-changing re-impl REJECTS (defn's §18 rule at
the impl registration seam, against the existing method's scheme).
Sequencing: **/spec scribes 0714 FIRST** (so the pin's `// spec:` anchor
resolves and the flip asserts spec text, not a ruling memo); **0604 early
wave lands BEFORE this fix** (same src seams — arch sequencing item 3).
Structural acceptance (/review): the impl seam routes through the SAME
redefinition commit path as defn (`commit_staging_to_live` →
`commit_slotted_def`) — an impl-specific parallel path is a P11/P7 REJECT;
the impl-specific residue is only the `TraitImpl` shell overwrite at the
trait's home + the mangled method Def re-staging. Unit tier: the same-type
check at the registration seam (accept same-type / reject changed-type)
per METHOD §2.2. /testing rider at flip: sharpen the pin's either/or
assertion to the ruled branch (dispatches-new), retiring the
"notices not replaced" alternative arm.

### 1.7 0707 restore-notice count — /dev(src), fix task (no RED)

Not in the RED set (minor display defect: count derived by re-parse instead
of from the record). Fix = read the count from the record; unit test at the
counting seam per METHOD §2.2; e2e assessment: the existing restore-notice
display cell (s114 §4.1 rider 0674) covers presence/absence — add the
count-correctness assertion to it only if the fix is observable e2e with a
deterministic fixture (multi-def restore dir), else the unit pin carries it
with the e2e face enumerated as covered-by-existing-cell.

## 2. The 0694 nullary-flap root-cause row (/qa-owned, Track A)

Scope (s114 §11 item 2): `nullary_return_dispatch_method_only_import_no_codegen_leak`
— 14/14 GREEN in isolation, RED only under full-suite parallel load;
in-suite failure output never yet captured. GREEN in this session's single
run. Plan of attack, in order:

1. **Standing convention first**: the flap stays OUT of the exact scalar in
   every certification statement (stable-exact = 11 + named flaps). A flap
   RED is never "flake" — it reopens as this row.
2. **Passive capture (free)**: the ≥2 SPRINT-exit runs + the ≥3-run 0694
   verification are the sampling instrument. On ANY in-suite RED, nextest's
   captured output is preserved verbatim (the first-ever captured failure
   is the single highest-value datum — it names WHAT assertion failed:
   wrong stdout, timeout, or spawn failure, which discriminates
   compiler-defect vs harness-contention).
3. **Stabilization hypothesis check**: this sprint's 0709/fallback-seam
   typecheck work (§1.3) touches the no-impl gate family the S114 record
   expected to stabilize this test. After the typecheck wave lands, run the
   file's binary ×20 under concurrent suite load (one time-boxed rig; see
   below) — green ×20 post-fix vs the pre-fix flap history is attribution
   evidence toward the check-gate seam.
4. **Shared load rig (one build, two consumers)**: the time-boxed
   load-amplified rig serves BOTH this characterization and 0604's
   re-induction attempt (§3.4) — suite-load pressure alongside the target
   (repeated full-suite run in a loop is sufficient pressure; no bespoke
   harness). Time-boxed; abandoned without prejudice if quiet.
5. **Disposition forks** (owner assigned by what the root cause names):
   captured output shows a compiler-visible wrong result → attribute by the
   §"Isolating Cross-Crate Failures" protocol (candidate class
   `shared-state-write-race` — demonstrated, not presumed); shows harness
   resource exhaustion (spawn/timeout) → harness-contention mechanism,
   /testing owns a rig fix; ≥3 consecutive certification runs green AND the
   post-fix ×20 green → FIXME 0694 closes with the watch clause (any future
   in-suite RED reopens this row by name).

## 3. The 0604 wave — test design (Track B, O1; /dev(src) + /testing)

### 3.1 The synthesized-trigger unit test (/testing; the fail-on-revert guard)

**Design constraint discovered at Phase 3 (matrix R7 row): the existing
chokepoint test cannot serve.** `src/imports/tests.rs::check_terminal_closure_rejects_out_of_closure_public_write`
injects a public import whose source LACKS the name — a shape that the
current provider-existence predicate AND the corrected
declared-export-closure predicate both reject. It fails on revert of the
CHOKEPOINT but not on revert of the CORRECTION. The new trigger must be the
discriminating cell:

1. **Trigger cell (RED against today's predicate by construction, GREEN
   with the correction — authored failing-first)**: synthetic tables where
   the source module genuinely PROVIDES the name publicly (the live
   phantom's shape — e.g. `primitives` providing `bit-and`, which it really
   does: `cranelisp-primitives/src/lib.rs:412`), injected as a PUBLIC
   import entry into a terminal `prelude` table whose DECLARED export
   closure does NOT include it → assert the diagnosed error; assert the
   message self-identifies as an internal R7 invariant breach naming the
   seam + module + name + source edge (the arch §4 tier-3 sub-form ruling —
   never mistakable for a user diagnostic). Interleaving-independent: a
   direct call against constructed tables, no session, no threads.
2. **False-fire fence (same change-set)**: a public write INSIDE the
   declared closure passes — including the subtree-private re-export shape
   the current rustdoc names as the deliberate permit (`collect_specific`
   already vetted it), and prelude's own public definition (§8.4). The
   corrected predicate must not reject the legal population.
3. **Census-row guard**: if `commit_staging_to_live` is ROUTED through the
   gate (vs a named legal-skip), one unit at that seam pins the routing
   (an out-of-closure public staged entry is rejected at commit — fails on
   revert of the routing). If a legal-skip is ruled, the skip's rationale
   is asserted in the census table (rustdoc/artifact), and the plan records
   WHY no test exists (enumerated deferral).
4. **Existing test retained** as the provider-existence negative sibling;
   /testing corrects its falsified comment ("primitives has NO bit-and",
   `imports/tests.rs:904–942`) in the same rider — the fixture mechanics
   stay valid as a synthetic; only the claims-to-mirror-reality narrative
   is false. /dev(src) corrects the `src/imports.rs:251` predicate comment
   (arch revision 2) in the wave.

### 3.2 The demoted sweep (no-regression, NOT acceptance)

≥25× deterministic-recipe sweep vs the real workspace stdlib (`--run` +
REPL, the FIXME's recipe), expect 0-fire. The pre-wave baseline on this VM
is already 0-fire (the determinism evaporated at S114 6a), so the sweep is
a behavioural no-regression check only. The two GREEN twins
(`tests/spec_08_prelude_outer_scope.rs` ×2) are must-hold; the poison
consumer (`insert_detecting_ambiguity`) is CORRECT and untouched.

### 3.3 MODULE_TRACE observability assertion

The wave adds emission at `commit_staging_to_live`. Verification is by the
census + code review (an eprintln under env var is not unit-assertable
cheaply); the DIAGNOSED-ERROR path (3.1) is the tested guard. The trace is
the observability deliverable: any future firing names its writer.

### 3.4 The load-amplified re-induction attempt (time-boxed)

One /testing attempt to re-induce the fire under suite-load pressure
(shared rig with §2 step 4), abandoned without prejudice if quiet. The
structural gate does not wait for it. FIXME 0604 retires when: census
CLOSED incl. `commit_staging_to_live`; corrected predicate unconditional +
unit-pinned per 3.1; twin guards GREEN; /design(int) §2.2 + both comment
corrections landed. Writer identification is desired, not required.

## 4. 0702 dotted-binder cells — both polarities pre-authored (gated on the /spec ruling)

The M3 standing matrix is s114 §5.1; the three-way disagreement (spec §5
prose vs table per-row wording vs design de-scope) is being framed by /spec
in parallel THIS phase. No cell is committed before the ruling. To land
same-day post-ruling, /testing authors from the following pre-built shapes —
only SELECTION remains after the user rules:

**Invariant under EITHER polarity (author first, with the batch):**

- **The sharpest face is a defect under every reading**: `(deftype A.B
  [:Int v])` today silently accepts AND mints ctor `user/B` (corrupted
  identity). Cell: assert the incoherence ABSENT — either a located
  binder-position reject (polarity A) or a coherent mint (echo, ctor name,
  introspection, and pattern-position use all agree on ONE identity)
  (polarity B). The negative face ("no silently-corrupted mint") is
  polarity-safe; the positive assertion sharpens post-ruling.
- **§6.2.1 positive fence**: ctor-pattern HEAD `Maybe.Some` in match
  position stays LEGAL — born-green, rides the batch under both polarities.
- **Qualified-type-param row (the never-drawn design §3.2 row)**:
  `(deftype (Pair prim/a b) …)` must produce a LOCATED binder-position
  error, not the incidental `module 'prim' not found` at a degenerate
  `0..0` span — the incidental-artifact-absent assertion (RA-N5/N6
  precedent) is polarity-safe; both polarities agree this row rejects
  (the table's own wording includes type-params).

**Polarity A (spec §5 prose is the authority — dotted rejects everywhere):**
the `.` column mirrors the landed `/` column — one located-reject cell per
M3 row (defn head, defn/fn param, let name, match var-pattern, deftype
head, deftype field, deftype type param, deftrait head + method names,
defmacro head), each with its bare GREEN twin, asserting the reject fires
on the dotted SPELLING with span on the user's written form. Mechanism
acceptance: ONE predicate widening at the shared helper +
`read_dotted_name`-fed head sites — /review greps for per-position copies.

**Polarity B (table per-row wording is the authority — dotted rejects only
type-params/con_var/mod/platform; dotted value-level binders legal):** the
value-level rows become COHERENT-ACCEPT cells: `(defn a.b [x] x)` /
`(let [a.b 5] a.b)` / `(match 1 [a.b a.b])` each asserts bind + read + echo
agree on the dotted local (and that resolution does NOT split at `.`); the
deftype-field accessor-suppression warning face asserts per the ruling's
field-row text; the reject rows (type-param etc.) get their located-reject
cells as in polarity A.

Either way the batch is ONE /testing change-set post-ruling; the /dev
(frontend) predicate widening (or coherent-accept fix) follows with the
flip; spec §5 annotation bands flip at close (§7).

## 5. /testing batch riders

| Rider | Directive | Status |
|---|---|---|
| **0724 hkt probe comment** | Rewrite `tests/hkt_named_arm_probe.rs:1-18` narrative per the FIXME: the observed reject IS the S110 converged resolver (`resolve_named` errors on unknown name; the never-error arms were DELETED S110) — there is no `check_type_expr` pre-walk mask. **Test KEPT** as the born-green fence over the convergence's guarantee; only the narrative changes. FIXME 0724 deletes with the commit. | rides the S115 batch |
| **Examples 119→120 reconciliation** | **VERIFIED ALREADY DISCHARGED at Phase 3**: `tests/examples.rs:150–153` carries `("29-annotations.cl", &[120])` + the S114 breakdown comment ("verified 120 both modes by /examples"). Counted as an executed expectation reconciliation; no action remains. (Recorded here because the S114 binding named it a rider — the record now matches source, per the C-track lens.) | done |
| **0712 GREEN guards** | `tests/ctor_as_value.rs` exists at HEAD (landed with the S114 batch). Verify at Phase 5 the three shapes + retro-tag are as directed (s114 §12 item 3); no re-authoring. | verify only |
| **0708 polarity-safe pin** | After/with the /spec framing (user ruling): the free-standing macro-arg annotation repro asserting `returned malformed sexp`/arity-artifact ABSENT (RED at HEAD, GREEN under both rulings); sharpen the positive face post-ruling (s114 §12 item 1). Fix lands this sprint only if attribution resolves in-scope; otherwise the pin is the attributed carry record. | with the ruling |
| **MS-P7 Conditional-container probe** | §1.1 item 3 — probe-first, pin only a demonstrated RED. | before/with the Track-A fix wave |
| **0693 disagreement fence** | §1.1 item 2 — the unit matrix fence rides the /dev(backend or typecheck-adjacent) consolidation change-set; /testing supplies the e2e twin verification that the committed family shapes hold through it. | before/with the Track-A fix |

## 6. New-instrumentation coverage rows (METHOD §2.2 — every owed matrix item that lands gets its tests)

### 6.1 R6 validation seam (/dev(backend, cache) change-set)

Unit tier (enumerated; each fails on revert of its validation arm):

1. Corrupt sibling-slot index (out of range) → diagnosed `CacheStale`, never
   trusted into emission.
2. Corrupt summary param index — a persisted `MayAliasOf(k)` with `k` ≥
   arity → `CacheStale` (the `arg_origins[k]` OOB hazard the register
   names).
3. Corrupt span key / malformed `callees` FQ → per-family `CacheStale`
   class asserted distinct (the class taxonomy is the census's).
4. Valid meta round-trips untouched (false-fire fence).

E2e (assessed BEFORE the fix, per METHOD §2.2 — warranted: observable
end-to-end and crosses the cache boundary): ONE cell — tamper a persisted
`.meta.json` field (summary index) in a warm cache dir, re-run → recompile
+ correct output, no crash, no stale-summary elision (extends the CS-1/AG-1
schema-gate family with a FIELD-level face). /review verifies census
completeness against the rustdoc artifact (arch revision 3).

### 6.2 R4 census witnesses (/design(backend) census → /dev per family)

Rows RESERVED until the census names the final family set (do not
pre-guess — the 0660 discipline). Per family the census keeps: either a
round-trip decoder-witness unit (the CS-1.2 model: encode → decode → equal,
over the family's full input space by construction) or a
disambiguator-presence pin (the mono inner-fn span-key model — assert two
colliding-name identities mint distinct symbols). Candidate families for
sizing: impl$FQType$FQTrait method keys, inner-fn discriminators
(span-keyed — verify), GOT data symbols, platform export names. /qa adds
the concrete rows when the census artifact exists.

### 6.3 0604 chokepoint — §3.1 above (trigger + false-fire fence + census-row guard).

### 6.4 Generative harness v1 (if the OWED recommendation is accepted at Phase 4)

Acceptance: deterministic enumeration (stable, nameable cells — the
no-flaky rule); always-on core ≤60s serialized through `SafetyMatrix`;
failure protocol wired (a generated failure reduces to a named committed
lane cell, pinned into the core permanently); the S115 chained-face fix
shapes (`set∘project`, `set∘set∘project`, `let∘set∘project`) present in
the enumerated space as the self-check that the generator covers the class
that motivated it. If DEFERRED at Phase 4: the deferral is user-sanctioned
and recorded on the matrix row + here — not silent.

### 6.5 Fix-wave unit obligations (enumerated so nothing falls through)

- §1.1: each corrected/added §16.2 rule-table row exercised at the unit
  tier (chained-link protect present in the emitted accounting).
- §1.3: TraitDecl registration arm accept/reject pair.
- §1.4: tail-jump flush ADT-wrapped-param arm; entry-frame protect license
  both toggles.
- §1.5: wrapper-emission totality per carrier state + illegal-state located
  error.
- §1.6: impl registration same-type accept / changed-type reject.
- §1.7: restore-notice count-from-record seam.
- 0604: §3.1 cells.

## 7. Certification + traceability

1. **Exit arithmetic (standing convention)**: at SPRINT exit, suite green
   except REDs that are NEW, probe-discovered, and attributed this sprint
   (candidates: the Conditional-container probe §1.1.3; the 0708 pin §5;
   the entry-payload toggle-ON pin §1.4 if authored and the sweep slips) —
   each named exactly. **≥2 identical full-suite runs**; the 0694
   verification needs **≥3** (§2). Stable-exact scalar + named flap set,
   never one number.
2. **Flip-driven annotation-band updates** (/qa edits in place, no FIXME
   cycle): spec §7.1 occurrence-rule rows → `[Tested+Neg …]` at the §1.3
   flip; spec §5 binder bands per the 0702 ruling + batch; spec §5.1.2 rows
   upgrade with the equivalence-twin cells; `spec/12-runtime.md` §12.1 RC
   rows on the §1.4 flips. Run `plan/spec_link_check.py` +
   `plan/spec_coverage_reconcile.py` before any band flip and again at
   Phase 6.
3. **Schema-window watch (CS-3 sibling)**: the sprint plans NO
   `CACHE_SCHEMA_VERSION` bump; the sole contingency is §1.1 item 6. Any
   bump outside that contingency, or a second invalidation event, is
   reported to /sprint as a plan violation.
4. **Phase-6 audit**: every remaining RED traces to owner+trigger; the
   matrix (`s115-instrumentation-matrix.md`) exit check re-runs against
   source — no Track-B row may close on a landing CLAIM (the same lens that
   opened this sprint).

## Next skills

- `/spec` — 0714 scribe FIRST (gates §1.6's flip assertion), 0702 + 0708
  framings (gate §4 + §5 rows). Running in parallel this phase.
- `/design`(typecheck) — §1.1 rule-table design at the family grain
  (carrier-enrichment contingency surfaced at Phase 3 if needed).
- `/design`(backend) — the §1.5 carrier-state dump BEFORE any pair fix;
  the R4 census (§6.2); W-B5 + 0696/0697 ride its touch.
- `/dev`(src) — 0604 early wave (§3) BEFORE the impl-redefinition fix
  (§1.6); then §1.7.
- `/dev`(backend, cache) — R6 seam (§6.1).
- `/testing` — §5 riders; the §3.1 trigger cells; §4 batch post-ruling;
  the §2/§3.4 shared load rig (time-boxed).
- `/sprint` — Phase 4: wave the fixes per the arch sequencing constraints;
  take the §6.4 generative-harness OWED-vs-defer recommendation (matrix O4)
  to the user.
