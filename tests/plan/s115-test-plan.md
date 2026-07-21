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

## 8. Mid-Phase-5 disposition batch (post-W3, 2026-07-21, /qa)

Evidence-only batch (no suite run — /review(backend) held the run token).
Every verdict below was checked against SOURCE at the W3 tree, not against
the wave reports.

### 8.1 FIXME 0745 — ATTRIBUTION: the entry-`main` heap-payload leak is the
### PROGRAM-RESULT-VALUE lifetime seam, owned by int

**Falsification claims VERIFIED.** /dev's two measurements are consistent
with source:

- `crates/cranelisp-intrinsics/src/panic.rs::cranelisp_run_program` (step 4)
  calls `io::drive_io(main_result)` then `drop::consume_io_tree(main_result)`
  and returns `ProgramOutcome { exit_code: inner, .. }`.
- `io.rs:236-243` (and the `:986` twin): the `IO_TAG_PURE` arm reads
  `field0` and returns it **without an inc**.
- `drop.rs:303-307`: the `IO_TAG_PURE` arm is a deliberate no-op on the
  payload ("Pure's payload is opaque — the trampoline returns it to the
  caller as the final value"), while the box itself is freed.

So the payload's single reference **transfers to the returned value**, and
the accounting inside the compiled code is coherent. `protect_return_value`
is NOT the seam, mechanism (a) has no referent (the leak reproduces with no
`let`), and §2.1 is re-scoped to faces 3 (0720) only. **The re-attribution
is ACCEPTED.**

**Owner (my placement): `/design`(int) → `/dev`(src), with a REQUIRED
`/arch` consult on the release mechanism.** Grounds:

1. **Nobody releases the program result value, in any mode.** Verified by
   absence: `src/` contains no rc-dec / value-release call site at all
   (`grep -rn "release_value\|consume_value\|rc_dec" src/` → only a
   `src/CLAUDE.md` prose hit). `--run`/`--link` route
   `main` → `cranelisp_run_program` → `ProgramOutcome.exit_code` →
   `src/main.rs:331` (truncate to exit code); the REPL routes
   `src/pipeline.rs:148-151` → `program_outcome_to_result` →
   `ExprOutcome::Value` → `display::result_value_doc` (which DEREFERENCES a
   heap result). Neither path decs.
2. **Only int knows the result TYPE.** The driver's whole type knowledge is
   `main_returns_io: bool`; `src/main.rs:331` already branches on
   `ty == Type::Int`. The heap-vs-immediate judgment and the drop-glue
   selection can only be made where `ty` lives.
3. **This is Decision 24 (consuming convention) at the ONE call boundary
   whose caller is Rust host code rather than generated code.** Framing the
   defect that way is what makes it a single seam instead of an IO quirk.

**Defect class: `rc-miscount`** (leak). Not `carrier-loss`, not `uaf` — the
accounting is coherent, the final owner simply does not exist. Locus for
the pin's `// defect:` re-locus (a /testing rider, since the current locus
`compiler/rc_emission.rs::protect_return_value` is now falsified):
`src/` program-result-value lifetime seam (`pipeline.rs::
program_outcome_to_result` + `main.rs` exit conversion + the REPL display
consumer), `owner=/dev` unchanged, `found=S114` unchanged.

**Fix constraints (binding on whoever takes it):**

- **Release strictly AFTER consumption.** Decing the payload inside
  `consume_io_tree`'s `Pure` arm, or backend-side before the return, is a
  **UAF on the LIVE REPL path** — not merely the defensive one. Correction
  to 0745's citation: `src/repl/format.rs:598` is documented-unreachable for
  current callers; the live dereference is `pipeline.rs:149` →
  `ExprOutcome::Value` → `display::result_value_doc`. The UAF conclusion is
  unchanged and now stronger (it is on the ordinary path).
- **Mode-uniform by construction.** REPL / `--run` / `--link` must reach the
  release through ONE path (P11); a `--run`-only release is a
  `mode-divergence` defect in waiting. Note the asymmetry that makes this
  easy to get wrong: under `--run`/`--link` the leak is harmless in effect
  (process teardown reclaims it) and is observable ONLY through the M3
  parity mode / the tier-4 oracle lane; at the REPL it is a real
  per-expression accumulating leak. The oracle lane is the acceptance
  instrument precisely because the `--run` face is otherwise invisible.
- **A type-erased release does not exist today.** `HeapHeader`
  (`crates/cranelisp-types/src/heap.rs:18-24`) is `{alloc_size, rc}` — no
  drop-glue pointer. Releasing an arbitrary typed result therefore needs
  either (a) a type-directed release entry int can call (glue lookup —
  trivial in JIT, NOT free under `--link`), or (b) a scoped mechanism
  covering the shapes a program result can take. **Choosing between these
  is an `/arch` call, not a `/dev` one** — it is the cross-crate half of
  this attribution.
- **Do not add a second ownership model at `consume_io_tree`.** The
  opaque-payload contract there is correct as documented; the symmetric
  hygiene option (inc in `drive_io`'s Pure arm + dec in the `consume_io_tree`
  Pure arm) is accounting-neutral and does NOT fix the leak — it must not be
  mistaken for the fix.

**Scope question (open; decides fix size, NOT the owner).** Is the class
IO-specific or general result-value ownership? Source says general (see 1
above — no release exists for any result). Confirming one-liner, for the
owning skill, not a blocker for placement: at the REPL with
`CRANELISP_RC_STATS=1`, compare `(let [s "hi"] s)` (heap result, non-IO)
against `(let [s "hi"] 9)` (immediate result). If the former leaks 1 and the
latter balances, the entry-payload pin is ONE FACE of a general seam and the
fix must be authored at that grain (and `/testing` owes a non-IO sibling pin
in the same change-set).

**Routing verdict for /sprint: this RED does NOT flip in S115.** It needs a
`/design`(int) pass plus an `/arch` mechanism ruling; W3/W4 are backend and
typecheck; W6 is a scheduled src window but is scoped to impl-redefinition +
0718 and has no design input for this. Carry
`adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2`
into certification as an **attributed carry with a NEW owner** (the S115
exit statement must say so explicitly — a carry whose attribution moved is
not the same carry). §1.4's "ONE sweep, three faces" acceptance is
**re-scoped to the two 0720 faces, both of which flipped**; the
entry-payload face leaves that row. Do NOT author the toggle-ON sibling pin
now (0745 is right: a second RED for one unfixed defect).

### 8.2 FIXME 0746 — m3 re-plant: §4.1 prong-2 lifecycle case, CONFIRMED;
### re-plant SYNTHETIC

**Confirmed, on source.** `tests/ms_p6_mode_self_tests.rs`'s `LEAK_PROG`
(`(defn g [] (let [s "hi"] (Pure 9)))`) plants exactly the general
G2/item-26 `protect_return_value` over-inc that W3 change-set 2 fixed. The
test's own FLIP-HAZARD comment predicted this verbatim, and this is the
**second** staleness of the same plant (first: S114 FIXME 0690, when the F-R1
fix balanced the entry-`main` shape). **Not a regression** — the compiler
moved in the correct direction and the fence's stimulus evaporated.

This is `memory-safety-coverage.md` §4.1 **prong 2** (an e2e capability
fence whose plant is a live compiler defect) reaching its end of life. Both
compliant dispositions are available; I rule the order:

1. **PREFERRED — re-plant SYNTHETIC** (the S114 MS-P6 precedent,
   `safety_lane_detects_falsified_clean_expectation_capability_green`,
   `7c2d5168`): a test-only injected imbalance at the intrinsics allocator /
   diagnostics seam, behind an env gate that is inert unless set. This makes
   the fence fail-on-revert of **the MODE** rather than of an unrelated fix
   — the only shape with a non-expiring half-life. Requires a small
   `/dev`(intrinsics) hook + a `/testing` re-plant, and the hook MUST join
   `diagnostics/tests.rs::all_gates_default_off` (the byte-identical-off
   fence) in the same change-set.
2. **FALLBACK (compliant, no user sign-off needed) — retire
   `m3_parity_catches_planted_leak` with a §4.1 tombstone.** Prong 1 is
   already in place (four parity self-tests at
   `crates/cranelisp-intrinsics/src/diagnostics/tests.rs:100/:108/:116/:124`)
   and prong 3 is already in place (`m3_parity_no_false_abort_on_clean` keeps
   the M3 env wiring exercised end-to-end). The tombstone must name the
   drained fault set (0690 F-R1 entry-`main`; S115 W3 item-26 general
   protect), the unit-tier successor, and the surviving wiring face.

**REJECTED: 0746's candidate 1** (re-plant on the entry-`main` heap-payload
leak). Per §8.1 that defect is real, live, and owned outside backend — but
planting on it repeats the exact anti-pattern for a third time, and it now
has an owner and a fix path. A capability fence must not be collateral of
someone else's fix.

**Routing: W7, and it must NOT reach certification RED.** 0746 stays
`target: /testing` with the ruling appended and a named `/dev`(intrinsics)
dependency for shape 1; if W7 capacity does not admit the hook, `/testing`
takes shape 2 in the same slot. Either way the RED is gone before the ≥2
certification runs, and the outcome is recorded on this row.

**Standing rule (added to `memory-safety-coverage.md` §4.1):** a prong-2
plant drawn from a live defect is **self-expiring** — prefer a synthetic
plant whenever a test-only injection hook is constructible at the seam the
mode instruments; draw from a live defect only when it is not.

### 8.3 FIXME 0741 — SharedState field-count guard: RATIFIED (16→17)

**Ratified.** The `declared_exports` addition is mechanical and
designed-to-admit: int-internal, unserialized, `prelude_fallback` model, no
types/schema/public-api impact, and the guard's actual purpose — that
`module_sexps`/`suspend_states` do not creep back — is untouched. The
in-body comment at `tests/regression.rs:3287-3294` documents the addition
alongside the two prior sanctioned ones. No parking-map creep. The
cross-boundary edit into a `/testing`-owned test was correct in substance;
the ratification is the process step, now discharged.

**Residual (NOT mine to execute — routed to `/testing`, 0741 re-targeted):**
the guard function is named `shared_state_field_count_at_target_14` while
guarding 17 — doubly stale, and the file's preceding comment block still
narrates the 14/15/16 lineage. A rename alone only defers the next stale
numeral, so the specified re-shape is:

- assert the two forbidden fields are **ABSENT by name**
  (`module_sexps`, `suspend_states`) — a direct, non-rotting statement of
  what the guard actually protects;
- **retain** the count as a creep tripwire, under a name carrying no
  numeral (e.g. `shared_state_pub_field_count_guard`), with the sanctioned
  additions listed in-body as they are today.

That kills the bump-and-stale-name cycle rather than paying it again.
0741 is NOT deleted: it carries the /testing residual.

### 8.4 FIXME 0705 — RETIRES (fully spent)

All three requested dispositions are discharged:

1. **Re-locus DONE** — `tests/shadowing_scope_lookup.rs:367` already reads
   `class=carrier-loss locus=crates/cranelisp-backend AutoCurry-over-local-target
   fn-as-value wrapper …`; the falsified typecheck locus is gone.
2. **Backend fix LANDED and the cell FLIPPED** (W3 change-set 3: totality
   enum over the closed carrier sums, no `_ =>`, `ViaCallee`+`Global` = a
   located producer-contradiction error).
3. **Typecheck side confirmed complete** by the same evidence (the carrier
   arrives correct; /design(backend)'s dump verdict said so before the fix).

The fn-as-value `'='` sibling is **separately tracked and needs no FIXME**:
its record and trigger are the committed RED
`fn_as_value_carrier_loss::trait_operator_partial_app_impl_present_has_got_carrier`
(plan §1.5), its owner is `/dev`(typecheck) per the /design(backend)
carrier dump (producer gap at `mono_collect.rs::resolve_auto_curry`), and it
is scheduled in **W4**. Per the no-FIXME-with-a-failing-test rule the pin IS
the record. **0705 resolved and deleted.**

`/testing` riders at this flip (batch, W7):
- strip the present-tense "DEFECT (open)" framing from the auto-curry cell's
  comment block per `tests/CLAUDE.md` (a GREEN repro must read past-tense, or
  a future regression poses as a known guard);
- add the born-green non-trait control 0705 asked for —
  `(defn f [] (let [g (fn [a b] 0)] ((g 1) 2)))` — which isolates
  AutoCurry-over-local from trait dispatch and would have named this gap
  without the trait-shadow cell. It is a **coverage-by-definition-variants**
  cell (the local-closure variant of the auto-curry family), not a nice-to-have.

### 8.5 FIXME 0604 — does NOT retire yet; exactly ONE residual

**Everything on the re-based acceptance is discharged except census
closure.** Verified: corrected destination-keyed declared-export-closure
predicate at the chokepoint, unconditional diagnosed error self-identifying
as an R7 breach, `commit_staging_to_live` routed with `D(M)` precomputed
before the `get_mut` guard (deadlock hazard honored), MODULE_TRACE at the
seam, `SharedState.declared_exports`, falsified-comment rider, synthesized
trigger RED-on-revert demonstrated, twin guards GREEN,
`/design`(int) §2.2 correction landed in Phase 3.

**Writer identification is NOT a residual** — the re-based acceptance
demoted it to DESIRED. The 0/30 deterministic sweep and the 0/496
load-amplified attempt discharge the no-regression check; the
load-amplified line of attack is **closed without prejudice and no further
attempt is scheduled** (quiet sweeps have been spent evidence since ~320
cumulative no-fires). The landed trace + diagnosed error are the
observability deliverable: any future firing names its seam.

**The one residual is /review's FIXME 0740** — the census closure claim is
materially false while `src/bootstrap.rs:446` and `src/platform.rs:407`
(public own-def `PlatformEffect`) are neither routed nor legal-skipped.
Re-based acceptance item 4 says "census CLOSED including
`commit_staging_to_live`", and the census IS the acceptance instrument; a
closure claim that a `/review` grep falsifies is precisely the S114 lesson
this wave was meant to end. **So yes: 0604's retirement WAITS on 0740**,
which is `/design`(int)'s and scheduled W6.

> **CORRECTION (W7, 2026-07-21, /qa) — the bootstrap characterisation above
> was FALSE, and it was mine.** The paragraph as first written described
> `src/bootstrap.rs:446` as a *"cross-module PUBLIC `Import` edging into the
> live `macros` table — the exact phantom shape"*. It is not. `/dev` and
> `/review` independently verified that the entry carries
> **`Visibility::Private`** (`src/bootstrap.rs:451`) at HEAD **and** at the
> reviewed commit `d9f2caea` — it never drifted; the characterisation was
> wrong when it was written. A private `Import` returns `Ok` before any arm of
> the gate is reached, so it is not a public write, not the phantom shape, and
> not a soundness question. Bootstrap's one genuinely public `Import`
> (`:812`) is intra-module and takes the self-alias arm.
>
> This is the **third** record to repeat the same misdiagnosis: `/review`
> filed it in 0740, `/sprint` copied it into `sprints/SPRINT.md` (since
> corrected), and **this plan and my 0604 retirement ruling repeated it
> without checking `refers_to` against source** — the exact failure METHOD
> §3.3's new first-act rule was written to stop, committed by the skill that
> asked for the rule. The residual itself survives correction: the census is
> still not closed, because a legal skip must be *named as one*, and
> `src/platform.rs:407` is still undispositioned. What changes is that
> bootstrap's disposition is **"private, therefore out of the gate's domain —
> a named legal skip"**, not "an unrouted public write".

**Retirement is mechanical**, on these two checks (no further /qa analysis
owed, and — per `/dev`'s W6 report — **no further `/dev` work is owed
either**: the code half is complete, with `platform.rs` ROUTED through the
chokepoint, `bootstrap.rs` a named legal-skip carrying an asserting sweep,
and the `src/imports.rs` census-comment mirror updated for both rows):

1. **`/design`(int) lands the census rows** in
   `design/int/prelude-table-write-isolation.md` §2.1/§2.4 — both seams
   dispositioned (scope-boundary statement and/or named legal-skip rows,
   bootstrap's row stating the PRIVATE ground above, not the phantom-shape
   ground), **plus the 0793 `PRIMITIVES_TABLE` session-init install rider**,
   which is part of the same census and not a separate gate;
2. the twin guards + the trigger / false-fire / routing pins are still GREEN
   in the certification runs — **satisfied**, verified in both W7 runs.

Check 2 is discharged. **0604 retires the moment /design(int) lands the check-1
rows — nothing else gates it, and no further work is owed by any other skill.**

`/testing` rider at retirement (W7): `tests/index_race_foreground_0604.rs`
keeps its 8-iteration sweep as the standing no-regression lane, but its
module banner must move to past tense and point at the landed structural
gate — the inline `FIXME(/testing): the exact foreground write seam is
UNLOCATED` block and the assertion's "This is FIXME 0604" text outlive the
FIXME otherwise. The `// defect:` line stays (a GREEN repro still carries
its class/locus for frequency analysis).

Not orphaned by retirement: `concurrency_capacity::same_token_capacity_…`
(0604's VERIFY-AFTER-FIX family row) already has a home — SPRINT §Scope
carries it as a sanctioned effect-concurrency-track deferral.

### 8.6 Instrumentation-matrix O-row status (see the matrix for the rows)

O1 DELIVERED (W2), O2 DELIVERED (W3, 6 cells), **O3 BLOCKED at W3** with a
finding routed to `/arch` (FIXME 0748 — `got_data_symbol_name` is
duplicated and the TYPES copy is the definer's, so the injectivity fix
cannot land backend-side), O4 unchanged (W7, per the accepted OWED
recommendation), O5 done at Phase 3. The matrix's Track-B exit check is
amended accordingly: **O3 can no longer close as VERIFIED this sprint** —
its honest exit state is the census artifact plus the routed cross-crate
finding, and the matrix now says so.

## 9. CERTIFICATION — the S115 suite state (W7, 2026-07-21, /qa)

This section is the durable record of what the sprint's suite state IS. It is
written to the standing counting convention (s114 §11 item 3): **a certification
is never one scalar** — it is stable-REDs-exact PLUS a named flap set, and a
run-dependent guard is never folded into the exact count.

### 9.1 The numbers

**Suite at HEAD `9088c82e`: 5351 run / 5346 passed / 5 stable REDs / 1 skipped.**

Evidence: **six full `cargo nextest run --no-fail-fast` runs this sprint**, four
of which landed exactly on this stable set. The two runs bracketing the
certification window are logged verbatim:

| Run | Tree | Result | Log |
|---|---|---|---|
| W6b | `99bd23a8` | 5333 run / 5328 passed / **5 REDs** / 1 skipped, 105.8s | `…/scratchpad/w6b/suite.log` |
| W7 | `9088c82e` | 5351 run / 5346 passed / **5 REDs** / 1 skipped, 104.1s | `…/scratchpad/w7testing/suite1.log` |

The run totals differ (5333 → 5351) because W7 *added* 18 cells; the RED set is
**byte-identical between the two runs** — same five test names, same binaries.
That is the ≥2-identical-runs SPRINT exit condition, met on the RED set rather
than on a scalar, which is the stronger reading.

### 9.2 The 5 stable REDs — each re-verified as attributed

Every RED traces to an open defect with a named owner. **Zero unattributed REDs;
zero genuine regressions.**

| # | Test | Defect | Owner | Class | Fix constraint for S116 |
|---|---|---|---|---|---|
| 1 | `adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2` | 0745 | **/design(int) + /arch** | `rc-miscount` | Re-attributed at W3 (§8.1): this is the **program-result-value lifetime seam** — nobody releases the program result in ANY mode — not the `protect_return_value` gap it was first filed as. Needs an `/arch` mechanism ruling on where a program result's lifetime ends before int can implement. The pre-registered exclusion in `gen_ownership_flows.rs` lifts when it lands. |
| 2 | `annotation_fold_macro_arg_0708::annotation_folds_in_macro_argument_position` | 0708 | **/arch → /dev(frontend+types)** | `silent-accept` | Flips with the S116 implementation, per `/arch`'s landed contract `annotated-sexp-node.md`: `:Type <form>` folds at READ time into `Sexp::Annotated`, ONE fold rule in `read_colon_prefix` covering every position — the macro-arg case fixed **by construction**, not by a macro-arg arm. Staged W0 types → W1 frontend → W2 int/fixture → W3 flip, one `CACHE_SCHEMA_VERSION` window. This pin is the flip trigger. |
| 3 | `capture_drop_glue_strands_nested_heap_0760::closure_capturing_adt_with_string_field_does_not_leak` | 0760 | **/design(backend)** | `rc-miscount` | All three await ONE ruling: (a) borrowed-builder-parameterised type-directed release vs (b) per-type named drop-glue functions called from every release site. **0796 widens the census (b) must collapse** — see §10.1. |
| 4 | `capture_drop_glue_strands_nested_heap_0760::closure_capturing_vec_of_strings_does_not_leak` | 0760 | **/design(backend)** | `rc-miscount` | as above |
| 5 | `capture_drop_glue_strands_nested_heap_0760::nested_adt_chain_past_glue_depth_limit_does_not_leak` | 0760 | **/design(backend)** | `rc-miscount` | as above; this is the `MAX_DROP_GLUE_DEPTH = 4` cliff face |

Three of the five are one defect. **The sprint carries three distinct open
defects into S116, each with an owner and a named next act** — and two of the
three (0708, 0760) are blocked on a *design ruling that has been framed*, not on
undiagnosed behaviour.

### 9.3 The named flap set — FIVE members

Not folded into the exact count, per the convention. Each passes in isolation
and fails only under full-suite parallel load; none may be dispositioned as
"flaky" (`tests/CLAUDE.md` §Failing-test discipline).

| # | Test | First seen | In-suite output captured? |
|---|---|---|---|
| 1 | `nullary_return_dispatch_method_only_import::…_no_codegen_leak` | S114 | **YES** (W6 r2) — `Error: codegen error at 14..15: undefined function: z` |
| 2 | `agent::y_short_flag_errors_on_non_agent_build` | S115 W3c | no |
| 3 | `multi_sig_module_locality::imported_multi_sig_base_direct_call_repl` | S115 W3c | no |
| 4 | `macro_expansion_interior_alias_double_free::macro_clause_interior_alias_double_free_run` | S115 W6 | **YES** (W6 r3) — `free(): chunks in smallbin corrupted`, exit `None` |
| 5 | `repl_persist::imported_trait_impl_survives_restart` | S115 W6 | no — lost to a summary-only tail (self-disclosed; mitigated by 34/34 ×5 in-binary and no recurrence across four subsequent full runs) |

Adjudication of this set is §9.5.

### 9.4 The sprint arc

**30 REDs at W1 → 5 at close. Every S114 carry either flipped or was
re-attributed with evidence** — none was carried on a scheduling claim, and none
was hidden behind `#[ignore]`.

- S114 closed at 11 attributed carries. W1 opened at **30** (11 carries + 19
  deliberately-authored new REDs: the 18-cell 0702 dotted-binder matrix and the
  0708 fold pin), with the arithmetic exact and zero unattributed drift — the
  spike is QA-first authoring working as designed, not decay.
- The fix waves drained it to 5. Of the original 11: MS-P7 chained ×2, 0719 ×1,
  0709 ×2, the RC-release sweep, the GOT-slot carrier-loss pair, and
  impl-redefinition all **flipped**; the entry-payload leak was **re-attributed**
  from backend to int with a carrier-state evidence dump (§8.1); 0708 was
  **re-attributed** to an S116 structural implementation with a landed `/arch`
  contract.
- The 0760 triple is NEW this sprint, probe-discovered and attributed on
  discovery — the SPRINT exit clause ("REDs that are NEW, probe-discovered, and
  attributed this sprint") covers it exactly.
- Along the way, four instrumentation items landed with detection proofs (O1,
  O2, O4, plus the backend structural fence) and O3 was honestly blocked and
  routed.

### 9.5 FIXME 0694 — the flap family adjudicated: TWO phenomena, not one

The evidence that was missing for three sprints arrived at W6: two in-suite
failures captured **verbatim**. They are not the same kind of event, and the
single most consequential thing this section says is that **treating them as one
"flap family" would have sent one investigation after two different bugs**.

**Member 4 — `macro_clause_interior_alias_double_free_run`** (`…/scratchpad/suite_r3.log:1235`):

```
thread 'macro_clause_interior_alias_double_free_run' panicked at
tests/macro_expansion_interior_alias_double_free.rs:132:5:
… → `main` returns `(Pure 3)` → exit 3; got exit None:
free(): chunks in smallbin corrupted
```

`free(): chunks in smallbin corrupted` is **glibc's own heap-consistency
detector aborting the subprocess**. Exit `None` = killed by signal, no exit
code. This is not a threshold, not a timeout, not a slow machine: it is the
allocator finding its free-list metadata overwritten. **A memory-safety datum.**
Note what else that run shows — the file's four sibling faces (`_repl`, `_link`,
`_m1_on_quarantine_face`, `_m1_off_assert_face`) all PASSED in the same run, so
this is per-process and per-mode, not a machine-wide condition.

**Member 1 — `nullary_return_dispatch_method_only_import_no_codegen_leak`** (`…/scratchpad/suite_r2.log:1299`):

```
Error: codegen error at 14..15: codegen failed for /:
codegen error at 14..15: undefined function: z
```

A **compile-time diagnostic**, produced by a subprocess that then exited
cleanly. Nothing was corrupted; a symbol the compiler needed was not there when
it looked. This is the signature of a **publication/enrolment ordering
question** — the `shared-state-write-race` class, the same class 0604 hardened.

**Verdict: TWO phenomena, sharing ONE enabling condition.**

The shared enabling condition is real and explains why both look like "load
flaps": every e2e test spawns its own `cranelisp` subprocess, and each subprocess
is itself multi-threaded (index worker, rayon sparks, IO reactor). Host CPU
oversubscription under a full nextest run changes *intra-subprocess* thread
interleaving. That is one condition, and it is why both families surface only
under suite load.

But what breaks is different, the owners are different, and the severity is not
comparable:

- **Class I — heap-invariant violation** (member 4). A memory-safety defect.
  Candidate mechanism: concurrent RC/drop on a shared cell, or a
  double-release/overrun, in a subprocess whose workers interleave differently
  under contention. Note the aggravating history: this test is the repro for
  0638, a double-free *fixed* at S114 W5 (`58ac8e46`). Either the fix was
  incomplete, or a *second* mechanism reaches the same heap — and the S98 lesson
  is binding here: **a "fix" verified by symptom absence under one condition may
  be a false green from perturbation**. Severity: highest in the set.
- **Class II — publication/enrolment ordering** (members 1 and 3; both are
  REPL-mode cells of the SAME multi-sig / no-impl-fallback seam family, which is
  itself a discriminating datum and argues one bug, not two). A correctness
  defect with no memory-unsafety. If it happened deterministically it would be a
  plain `carrier-loss`/`wrong-reject`.
- **Class III — unclassified** (members 2 and 5). One observation each, no
  captured output. Member 2 explicitly is NOT explained by the 0615
  binary-provenance race (the `cfg(not(feature = "agent"))` face runs in the
  DEFAULT suite). **Honest status: unclassified.** Two observations do not make a
  class, and I decline to assign them to I or II.

**Which parts of the above are hypothesis.** Per METHOD §2.2, an attribution
needs a **discriminating control** and a **seam observation**. Stating it plainly:

- **Established (observed):** the two failure signatures, verbatim; that they are
  categorically different kinds of event; that sibling faces passed in the same
  run; that members 1 and 3 sit on the same seam family; that all five pass in
  isolation.
- **Hypothesis (NOT established):** that intra-subprocess thread interleaving is
  the mechanism for either class; that Class II is a publication-order race;
  that Class I is a data race rather than a latent deterministic overrun whose
  manifestation is layout-dependent. **I have symptom captures and zero seam
  observations.** No part of the mechanism story below should be cited as
  attributed until S116 runs the experiments.

### 9.6 S116 attack plan for 0694, and the discriminating experiment

The experiments are ordered so that the cheapest one can invalidate the shared
premise before anyone builds a rig on it.

**D1 — the primary discriminator (cheap, run it first). Does the fault need the
SUBPROCESS to be concurrent, or only the HOST to be loaded?**
Run the single test binary in isolation ~200× while the host carries an equal
CPU load from a **non-cranelisp** source (`stress`/`yes` on N−1 cores).

- Reproduces → host CPU contention alone suffices; the fault is *intra-subprocess*
  interleaving, and the shared premise holds. Proceed to D2.
- Does NOT reproduce, but the full suite does → something about *other cranelisp
  subprocesses* matters, and the premise is wrong. That points at inter-process
  shared state (cache dir, `CRANELISP_LIB`, tmpdir reuse, `user.cl` in a shared
  cwd — the repo-root pollution that bit twice this sprint), which is directly
  testable and a completely different fix.

This single experiment is worth more than any amount of repeated full-suite
sampling, because it can **falsify the framing** rather than accumulate more
symptom counts.

**D2 — separates Class I from Class II at the seam (the seam observation METHOD
§2.2 requires).**

- *Class I face:* re-run member 4 under (a) the M1/M3 diagnostic modes +
  `CRANELISP_RC_DEC_CHECK=1`, and (b) with the subprocess forced
  single-threaded (rayon threads = 1, spark budget 0). If forcing the subprocess
  single-threaded eliminates it **under identical host load**, the mechanism is
  intra-subprocess concurrency on the heap — a real data race, seam named. If it
  survives single-threaded, the corruption is a latent deterministic
  overrun whose manifestation is layout-dependent, and the S98 rule applies:
  **do not accept symptom absence under a perturbing tool as a fix.**
- *Class II face:* run members 1 and 3 under load with `CRANELISP_MODULE_TRACE=1`
  captured to a file. **This is newly possible** — the 0604 wave landed
  MODULE_TRACE emission at the staging→live commit seam, which is exactly the
  publication edge in question. If a failing run's trace shows the eval read
  preceding the publication of the missing symbol, Class II is *demonstrated* as
  a publication-order race and the owner is /dev(src) at the seam 0604 hardened.

**D3 — the anti-vacuity control that converts hypothesis into attribution.**
Env-gated, dev-only: inject an artificial delay at the publication seam and show
member 1 goes RED **deterministically, with the same error text**
(`undefined function: z`). A planted fault reproducing the exact observed
signature is a demonstrated mechanism; anything less is a story that fits.
This is the same discipline as the capability fences in §9.5's matrix — and note
that if D3 succeeds it also *becomes* the standing regression guard.

**Standing hygiene, binding on all three:** every run is `tee`'d. The W6 loss of
member 5's output to a summary-only tail cost the single highest-value datum for
that member, and it is not recoverable after the fact.

**Sequencing note:** D1 gates everything. If D1 falsifies the premise, D2 and D3
are re-designed, not merely re-run.

### 9.7 Would I certify this suite state as stable?

**Yes for the 5 REDs. No for the flap set — and the flap set is what I would not
sign.** Full statement in §11.

## 10. New dispositions (W7, /qa)

### 10.1 FIXME 0796 — capture stranding also reached by curried partial application: ACCEPTED as evidence; does NOT get a fourth pin

`/testing`'s judgment is right and I am ratifying it explicitly so nobody
"corrects" it later: **do not add a fourth failing-not-ignored pin for 0760 now.**
Three pins already carry one unfixed defect through every certification run;
a fourth buys no signal and costs a triage cycle each time. The measured
`balance_exclusion` in `gen_ownership_flows.rs`, carrying its rates, is the
better record — and removing the exclusion is the post-fix acceptance check,
which a pin would not give.

**What 0796 changes is the ruling's obligation, and it is not small.** 0760 asks
`/design`(backend) to choose between (a) borrowed-builder-parameterised
type-directed release and (b) per-type named drop-glue functions at every
release site. 0796 shows the stranding is reached from a **compiler-synthesised**
capture set — auto-curry's implicit closure env (§4.6.3), with no `fn` anywhere
in the user's source — at the **identical per-iteration rate** as an explicit
capture, for every owning type, under both toggles. Therefore:

> **"Fix the `fn` capture path" is not a scoping option.** The site census the
> ruling must satisfy includes every site that mints a capture set, whether or
> not the user wrote a closure. `/design`(backend) states the census
> explicitly in the ruling.

This is additional weight behind option (b), on the same argument as the
`MAX_DROP_GLUE_DEPTH = 4` cliff. **Disposition: 0796 CARRIES to S116, folded into
the 0760 ruling — not a separate work item.** Its acceptance cell lands with the
fix wave.

Worth recording for the method: the harness found this **on its first run**,
because it enumerates {owning type × position} rather than a hand-written shape
list. A reaching context nobody thought to enumerate showed up as a cell. That
is the argument for generative coverage, made concrete inside one wave.

### 10.2 FIXME 0787 — dotted-reference over-reach cells: RETIRED

`/review`'s finding was correct and material: of the 13 "fences" claimed as the
over-reach control for the `.` axis, **10 carry no dot at all** and would stay
GREEN under a coarse `name.contains('.')` over-reach. They discriminate a real
and different thing (the reject did not eat legal bare binders); they do not
discriminate the `.` axis. The design's own named hazard — `core.io/pure`, a
qualified reference whose MODULE half is dotted — was unfenced in both tiers.

`/testing` landed all four proposed cells at W7. **Disposition, all four items:**

1. **The matrix records them** — PLAN rows in `PLAN.md` §"Sprint 115" (§10.6
   below), five cells: `--run` and REPL faces of the dotted-module-half
   reference, the `export` twin, the alias form, and the degenerate case.
2. **The unit tier is NOT the agreed home for the degenerate case.** `/testing`
   pinned `a.` / `.b` / bare `.` e2e as located reader errors, and that is the
   right call — it is a Principle-16 twin of bare `/`, and bare `/` is pinned
   e2e. Keep both tiers.
3. **The REPL face earns its place** by asserting the *rendered* type keeps the
   whole dotted home (`:user.util/Wid`), so a truncating splitter fails on
   display as well as on resolution. Two independent observations of one fault
   is what the reference column was missing.
4. **The missing mutation proof is noted, not waived.** `/testing` could not run
   one (it requires editing `crates/cranelisp-frontend/`, outside its boundary).
   The cells are structural over-reach controls by construction, but per §9.5's
   bar that is *argument*, not *demonstration*. **`/dev`(frontend) confirms
   fail-on-revert in one line at its next touch of that seam** — carried as a
   rider, not a gate.

**0787 retires.** Its ask is discharged.

**Its undispositioned tail is NOT discharged, and it is a defect** — see §10.3.
`/testing` correctly flagged `(u/helper)` as "outside this FIXME's ask" and
routed it to me rather than silently dropping it. That routing is what caught a
spec violation.

### 10.3 NEW DEFECT — a module alias is not usable as a qualifier (spec §8.3.4/§8.3.6 violation)

Probed live at HEAD `9088c82e` (scratchpad cwd, `PrimitivesOnly`):

```clojure
;; main/util.cl
(defn helper [] 7)

;; alias-only import — the spec's own "qualified access only" case
(import [(main.util u) []])
(defn main [] (Pure (u/helper)))
;; => error: module 'u' referenced by 'u/...' not found     EXIT 1
```

The spec is not ambiguous about this. §8.3.4: *"registers `str` as an alias for
`core.string`. **The alias can then be used for qualified references:
`str/split`.**"* §8.3.6: *"Registers `opt` as an alias for `core.option` without
importing any bare names. **Useful when you only want qualified access:
`opt/Some`.**"*

**Controls (all at the same HEAD, same fixture):**

| Program | Result |
|---|---|
| `(import [(main.util u) []])` + `(u/helper)` — alias-only | **exit 1**, alias not found |
| `(import [(main.util u) [helper]])` + `(u/helper)` | **exit 1**, alias not found |
| `(import [(main.util u) [helper]])` + `(helper)` — bare | exit 7 ✓ |
| `(import [main.util [helper]])` + `(main.util/helper)` — full path | exit 7 ✓ |

So the alias form imports its *names* correctly; the alias itself is simply never
registered as a referenceable qualifier. In the alias-only form — where
qualified access is the **entire** purpose of the import — the feature is
non-functional end to end.

**Attribution: `wrong-reject`** (a spec-conforming program rejected), at
qualified-name resolution. I have a discriminating control (bare vs
alias-qualified vs full-path, one variable) but **no seam observation**, so the
owning crate is *not* attributed here — `/testing` reduces and the seam names the
owner, per the standard protocol.

**This is a textbook coverage-by-definition-variants miss** — the standing lens,
exactly as `tests/CLAUDE.md` describes it: the family is *import shape × reference
form*, the suite is dense on `(bare import × bare ref)` and `(bare import ×
full-path ref)`, and the `(alias import × alias-qualified ref)` cell is empty.
A whole documented language feature sat unexercised because no cell asked for it.
**Filed as FIXME 0798 (`/testing`).**

### 10.4 FIXME 0797 — auto-curry over an unconstrained generic parameter: adjudicated as a DEFECT (`wrong-reject`), not a spec fork

`/testing` asked whether this is a `wrong-reject` or deliberate-and-needs-a-spec
sentence, and correctly declined to decide it alone. **I rule: `wrong-reject`, a
defect. No user ruling is needed for the case as filed** — and the probes below
also sharpen the repro axis materially, which changes the handoff.

**Re-verified at HEAD `9088c82e`, then extended.** 0797's table reproduces
exactly. The extension:

| # | Program (`x` unannotated ⇒ free type var) | Result |
|---|---|---|
| a | `(defn g [x y] (add-i64 y 0))` → `((g 5) 3)` | **rejected**: `expected (Fn [Int] Int), got Int` |
| b | same `g`, full application `(g 5 3)` | exit 3 ✓ |
| c | `(defn g [:Int x :Int y] …)` → `((g 5) 3)` — annotated twin | exit 3 ✓ |
| e | `(defn g2 [:Int x y] (add-i64 x 0))` → `((g2 5) 3)` — free var in the **residual** | rejected, but by the **§3.11 ambiguity gate** ("a residual unbound type variable reached a codegen position") — a *different, principled* rejection |
| f | `(defn g3 [x :Int y] …)` → `((g3 5) 3)` — free var in the **supplied** position only | **rejected**, same message as (a) |
| h | `(defn g4 [x :Int y :Int z] …)` → `((g4 5 3) 4)` — 3-arity | **rejected**, same message — not arity-specific |
| **j** | same `g` as (a), curried value used as a **non-callee**: `(add-i64 (g 5) 1)` | rejected with `expected Int, got (Fn [Int] Int)` — **the curry DID form** |
| m | same `g`, let-bound then applied: `(let [h (g 5)] (h 3))` | **rejected**, same message as (a) |
| n | annotated twin of (m) | exit 3 ✓ |

**Two findings, and the second supersedes 0797's own characterisation.**

**(1) The rejection has no semantic content.** Compare (c) and (f): identical
bodies, identical residual closure type `(Fn [Int] Int)` — fully determined,
containing no type variable — and one is accepted, one rejected. The only
difference is whether a type *nobody reads* was written down. A boundary
invisible in the residual type is an implementation artifact, not a semantics
call. §4.6.3's "currying is only defined where the residual is determinable"
reading does not even carve this case out, because the residual **is**
determined: the supplied argument pins `a := Int` at the curry point.

**(2) The discriminator is NOT "partial application is rejected".** Cell (j)
shows the curry **forms correctly** over the very same unconstrained parameter
when its result flows to a non-application use — the checker reports
`(Fn [Int] Int)`, which is right. The curry fails only when the curried result
is subsequently **applied** (immediately in (a)/(f)/(h), or via a let binder in
(m)); there `(g 5)` types as `Int`, i.e. the inner node was accepted as a *full*
application of a 2-parameter function to 1 argument. So the implementation
already supports currying over a free-var parameter — it just loses it under an
application demand. That is an internal inconsistency, which settles the
adjudication: **you cannot call a boundary deliberate when the implementation
observably crosses it in the adjacent cell.**

**Candidate seam (NOT an attribution).** `infer.rs::try_auto_curry:1040` guards
on `Type::Fn(params, ret) if arg_types.len() < params.len()`, with a **silent**
`_ => return Ok(None)` fallthrough for any other callee shape; the deferred
settlement machinery is `mono_collect.rs::resolve_auto_curry` +
`AutoCurryDrain`. A callee type not yet resolved to `Fn` at that guard would
fall through silently, after which an ordinary-apply unification against a bare
type variable cannot enforce arity — which fits every observation, including why
the error surfaces at the *outer* node with a message describing the
application rather than the curry. **This is a hypothesis. It has a
discriminating control (the table above) and NO seam observation.** Per METHOD
§2.2 the first act of the owning `/dev` is to observe which arm is taken —
before any fix.

Note the adjacency: FIXME 0779 already records that **five of six**
`resolve_auto_curry` drain seams have no cell that reddens on a flip. If the
seam observation lands in that machinery, these are one finding, and 0779's
detection gap is why it was invisible.

**The genuinely normative residue — framed, not ruled.** Cell (e) — currying
where the **residual** carries a free type variable — is rejected by the §3.11
ambiguity gate. Whether that is the intended interaction between §4.6.3
("auto-currying applies at any depth", extended to *constrained* polymorphism
with monomorphisation at the supplying call site) and §3.11 (pin the type) is a
question the spec does not answer, and it is **not** what 0797 asked. That one is
the user's. Routed to `/sprint` for an S116 `/spec` slot (outside my 0798–0799
band); it blocks nothing.

**Disposition: 0797 RETIRES** (its ask — adjudication — is discharged here).
The work it generates is **FIXME 0799 (`/testing`)**: the failing repro at the
sharpened axis, plus the free-type-variable column the §4.6.3 matrix lacks. All
twelve existing auto-curry tests curry over a determined type — another
coverage-by-definition-variants cell, and the second one this wave (§10.3 is the
first).

### 10.5 FIXME 0740 — the four-record misdiagnosis chain: my two records are CORRECTED

`/dev` and `/review` independently verified that `src/bootstrap.rs:451` carries
`Visibility::Private` at HEAD **and** at `d9f2caea` — it never drifted. The
"cross-module PUBLIC Import … the exact phantom shape" characterisation is
**false**, and it propagated through four records before anyone checked it
against source.

Two of the four are mine, and both are corrected in place:

1. **`design/arch/fixmes/0604-…md`** — my S115 retirement ruling (§"/qa S115
   pre-W7 disposition"). Corrected.
2. **`tests/plan/s115-test-plan.md` §8.5** — this plan. Corrected, with the
   correction stated as a correction rather than a silent edit (§8.5 blockquote).

0740's body is `/design`(int)'s to correct; `sprints/SPRINT.md` is already
corrected by `/sprint`.

**The lesson is about me, and I am recording it as such.** METHOD §3.3's new
rule — *a FIXME disposition or carry decision verifies the claim against
`refers_to` source as its FIRST act* — was adopted this sprint at my own
prompting, and I then wrote a retirement ruling that repeated an unverified
`/review` characterisation without opening `bootstrap.rs`. A ruling that decides
whether a three-sprint carry retires is precisely the artifact that cannot
inherit a premise. The residual survives the correction (the census still is not
closed; `platform.rs:407` still needed disposition), which is exactly why the
error was cheap to miss and would have been expensive to keep: **a true
conclusion resting on a false premise reads as verified.**

### 10.6 PLAN rows for the W7 cells

Landed in `tests/plan/PLAN.md` §"Sprint 115 — W7 cells". Three groups: the 10
`gen_ownership_flows` fns + the product statement; the 3 new + 1 sharpened
`impl_redefinition_dispatch` cells; the 5 dotted reference-column controls.

## 11. PHASE-5 EXIT STATEMENT (/qa, for the user)

**What shipped.** Sprint 115 set out to flip 11 attributed carries and close the
gap between the safety recommendations and what is actually in place. Both
happened. The suite is **5351 run / 5346 passed / 5 stable REDs / 1 skipped**,
verified over six full runs with the RED set byte-identical across the two
certification runs. The RED count went **30 at W1 → 5 at close**; of the 11
S114 carries, nine flipped and two were re-attributed with evidence rather than
excuses. On the instrumentation side, the 0604 structural gate landed with a
demonstrated fail-on-revert trigger (a three-sprint carry, finally gated on
merits), the cache trust-boundary got its ONE validation seam with per-variant
proofs, impl-redefinition hot-reload works and was verified behaviourally
(12 → 7 → 99 across three re-impls), and the generative flow harness landed —
45 cells, four synthetic capability fences, an anti-vacuity guard, and a real
finding on its first run.

**What carries, with owners.** Three defects: **0745** (program-result-value
lifetime — /design(int), needs an /arch mechanism ruling first), **0708** (the
`:Type` fold — /arch's contract is landed, S116 implements it in four staged
waves), **0760 ×3** (capture drop-glue stranding — awaiting /design(backend)'s
a-vs-b ruling, now widened by 0796 to include compiler-synthesised captures).
Two instrumentation items: **O3** mangle-family injectivity is **owed, not
delivered**, routed to /arch as 0748; and the four differential-oracle rows
demoted in this sprint's matrix re-audit need one planted fence to close.
Plus **0694**, the flap set, below.

**Would I certify this suite state as stable? A qualified yes — with one
explicit exception that I will not sign.**

The five REDs are not a stability concern and I certify them without
reservation. Every one traces to an open defect with a named owner, a named
class, and a named next act; three of the five are one defect; two are blocked
on design rulings that are *framed and waiting*, not on undiagnosed behaviour.
A suite whose failures are this well-characterised is doing its job — these are
guards, not decay, and the discipline that keeps them un-`#[ignore]`d is why we
can read them at all.

**The flap set is a different matter, and I would not certify it.** Five tests
that pass in isolation and fail under load is not a stability profile I will
call clean, and one of them is qualitatively worse than the rest: `free():
chunks in smallbin corrupted` is glibc detecting that its own free-list metadata
has been overwritten. That is a memory-safety event, in a test that is the repro
for a double-free we already believed we fixed at S114. It has been observed
once, under load, with no seam observation and no mechanism. I cannot bound it:
I do not know whether it is rare-and-narrow or common-and-lucky, and the
honest reading of "we saw it once in six runs" is that we do not know the rate.

So the certification I am willing to give is: **the deterministic state of this
suite is stable and well-attributed; the load-dependent state contains an
uncharacterised memory-safety event and is not.** Those should not be averaged
into a single verdict, which is exactly why the counting convention forbids one
scalar. I would not let the heap-corruption member ride into S116 as one of five
"flaps" — it needs to be pulled out by name and given the D1/D2/D3 experiments in
§9.6 as first-class sprint work, ahead of the flap family as a whole.

One further note in fairness to the sprint: the reason I can say any of this is
that W6 captured the failures verbatim instead of counting them. Three sprints
of "the nullary flap" produced no progress; two captured stderr blocks produced
a two-class adjudication, an attack plan, and a discriminating experiment in one
sitting. The lesson generalises past 0694 — **capture the output, always tee**;
a symptom count is not evidence, and the fifth flap member's output was lost to a
summary-only tail this sprint and is not recoverable.

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
