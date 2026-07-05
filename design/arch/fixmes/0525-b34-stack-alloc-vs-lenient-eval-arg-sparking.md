---
number: 0525
target: /dev (cranelisp-backend)
filed_by: /dev
filed_at: 2026-07-05
sprint_filed: 102
ruled_by: /arch
ruled_at: 2026-07-05
retargeted: /arch → /dev (cranelisp-backend) at the 0525 ruling (direction (d), backend-local emission gate)
refers_to: design/backend/ownership-codegen.md §4 (B3.4 stack slots) + §4.1 gate 3 + §4.3 (ParBind/spark interaction), design/arch/ownership-inference.md §2.2 (escape axis — the frame-restructuring boundary note added by this ruling), design/typecheck/ownership-inference.md §5.2 (confinement over-approximation), crates/cranelisp-backend/src/compiler/fn_compiler.rs (constructor_call_stack_eligible / STACK_ALLOC_ESCAPE_FACT_SOUND), crates/cranelisp-backend/src/compiler/apply.rs:222-296 (the apply-arg spark site)
status: open
---

# B3.4 stack-alloc is structurally incompatible with lenient-eval arg-sparking — the escape fact is insufficient and the confinement fact is too coarse to gate on

## Issue

B3.4 (Increment-I Cranelift stack slots for `NoEscape` scalar-payload ADT
constructors) cannot activate. This is the THIRD distinct blocker the B3.4
re-activation attempts have surfaced, but unlike 0523 (capture) and 0524
(lambda/HOF-return) it is **NOT an escape-classifier gap** — the escape fact is
correct. It is a structural mismatch between stack allocation and the backend's
own **lenient-eval** transformation, and it needs an /arch ruling because neither
of the two available facts yields a sound-and-non-dead activation.

### What happens

With `STACK_ALLOC_ESCAPE_FACT_SOUND = true`, the escape classifier (post-0523/
0524, comprehensively sound) correctly proves the two lambda/HOF-return
regressions stay heap — those PASS. But a third regression fails HARD:

- `tests/spec_06_pattern_matching.rs::nested_match_in_arm_body` →
  `runtime error: match failed` (a hard dangling read / UAF signature).

Minimal repro (REPL, `PreludeVariant::PrimitivesOnly`):

```
(defn d [a b] (match a [None 0 (Some x) (add-i64 x 1)]))
(d (Some 10) (Some 32))          ; => "runtime error: match failed"  (should be 11)
```

Isolation ladder (all under the default lenient REPL, flag ON):

| shape | result |
|---|---|
| `(f (Some 5))` — ONE ADT arg | OK (5) |
| `(add-i64 (f (Some 10)) (f (Some 32)))` — two ADT args, **separate** calls | OK (42) |
| `(d (Some 10) (Some 32))` — **two ADT args to ONE call** | **match failed** |

Discriminators, established by ablation:

- `CRANELISP_NO_OWNERSHIP=1` → correct (heap path). So stack-alloc is causal.
- `CRANELISP_NO_LENIENT=1` → correct (`11`). **The bug is lenient-eval-specific.**
- Single ADT arg → correct; **two-or-more ADT args to one call** → UAF.

### Root cause

Under lenient evaluation the backend sparks a call's arguments onto separate
strands (`compile_let_lenient` / IVar sparks). This spark placement is
**codegen-internal** — it does not exist in the strict `MonoExpr` the escape
analysis runs over. So a stack slot built to satisfy a lenient-sparked arg lives
in a thunk frame that is popped at the join; a call with two live stack slots
hands one (or both) freed slots to the callee, which reads a garbage tag →
`match failed`. The `v.cl` CLIF dump confirms both `stack_addr ss0/ss1` (with the
`0x4000_0000_0000_0000` immortal header) AND lenient heap-thunk allocs coexist
for the same two constructors — a confused double-representation across the
spark/join. The single-arg case "works" only by luck (the scalar payload is
extracted before the popped slot is reused — a `feedback_verify_fix_not_symptom_absence`
false-green, not a real safety property).

### Why neither available fact gives a sound activation

1. **Trust `escapes` alone (current mechanism):** UAF, as above. The strict
   `escapes` fact is correct for strict semantics but blind to the backend's own
   lenient sparking.

2. **Also require `confined = Some(true)` (decline crossing, per §4.3):** SOUND,
   but the confinement analysis **over-approximates every apply-arg and every
   let-RHS to `PotentialFork` → `confined = Some(false)` (crossing)**
   (`ownership-inference.md` §5.2, and the B3.3 review that dropped the
   `confined_bindings` half for exactly this reason). A `NoEscape` scalar-ADT
   constructor is essentially ALWAYS in an apply-arg or let-RHS position, so this
   gate declines the entire win and makes B3.4 dead code — the Principle-8
   anti-pattern the B3.3 through-binding half was already removed for. I
   implemented and measured this gate: the golden corpus diff went EMPTY (nothing
   stack-allocates anywhere), confirming the win vanishes.

The escape fact under-constrains (misses the codegen-introduced crossing); the
confinement fact over-constrains (marks everything crossing). There is no
backend-local gate on the current facts that is both sound and non-dead.

## Proposed resolution (for /arch to rule)

This is a cross-boundary design question — it touches the typecheck confinement
precision, the backend lenient-spark codegen, and possibly a mode-gated
activation. Candidate directions, for /arch to weigh (I am not choosing):

1. **Precision on the confinement/crossing fact so a genuinely-local
   (non-sparked-in-practice) constructor is `Some(true)`.** The §5.2
   over-approximation ("every lenient-eligible position is PotentialFork") is what
   makes the sound gate dead. If lenient placement were modelled more precisely —
   or if the analysis distinguished "may be sparked" from "is stack-address-taken
   AND sparked" — gate 5 (decline crossing) would preserve the win. Likely a
   typecheck change; coordinates with the confinement stratum.

2. **Fix the lenient multi-arg codegen so stack slots survive the spark/join.**
   e.g. lenient arg-sparking must copy a stack-allocated arg to a spark-owned /
   heap location before crossing (the slot cannot be shared across strands), or
   decline sparking for stack-address-taken args. Backend-local but non-trivial;
   needs to not reintroduce the double-representation.

3. **Mode-gate B3.4 to non-lenient compilation (`--link` / `--release` /
   `NO_LENIENT`).** The win is real and safe there (the isolation ladder and the
   golden corpus both compile clean under `NO_LENIENT`). If the compiled artifact
   is mode-specialised, B3.4 could activate for the non-lenient path only. Needs a
   ruling on whether the flag can be per-mode rather than a compile-time const,
   and on whether lenient is ever the shipping runtime for compiled binaries.

4. **Defer B3.4 to a later increment** (region arena / thread-local RC / escape→
   stack under the Phase-H memory-model spine), if the lenient interaction is
   better solved there.

## /arch ruling (2026-07-05) — direction (d): a backend-local emission gate ("gate 5"), mirroring gate 3

**Chosen direction: (d).** Add one backend-local eligibility gate to
`constructor_call_stack_eligible` — **decline stack-alloc for any construction the
backend is about to relocate across a spark barrier** (i.e. any construction compiled
inside a backend-synthesized spark-thunk body). This is a **small, contained,
backend-only change** requiring **no typecheck / confinement work and no mode
divergence**. Retargeted to `/dev (cranelisp-backend)`.

### Why (d), and why NOT the others

**Confinement is the WRONG AXIS (rejects (a)).** The /arch scrutiny the dispatch
brief asked for lands squarely: confinement and stack-alloc-soundness are *distinct
properties*.
- Confinement (spine §2.3) answers **"may RC ops on this cell run *concurrently* on
  >1 thread?"** — a property of *where RC operations execute*, protecting the refcount
  word so it can be non-atomic.
- Stack-alloc soundness asks **"does the value's backing STORAGE outlive every use?"**
  — a property of *where the storage frame lives and when it pops*.

  These come apart in both directions: a `Confined` cell (all RC ops parent-strand)
  stack-allocated in a thunk frame that pops early still dangles → UAF; a `Crossing`
  cell is perfectly safe to stack-allocate if its storage frame outlives all uses.
  The reason confinement *appears* to flag the lenient case is **incidental**: the
  confinement analysis over-approximates every apply-arg / let-RHS to
  `PotentialFork`→`Crossing` (§5.2) precisely because those are the lenient-*sparkable*
  positions — so its over-approximation set is a coarse SUPERSET of the real signal
  (the *actually-sparked* constructions). Gating on it is therefore both semantically
  wrong AND fatally imprecise (declines every apply-arg ⇒ dead win, Principle 8).
  Worse, making confinement precise enough to distinguish "actually-sparked" from
  "not-sparked" would require **typecheck to predict codegen's spark placement** —
  which both design docs state is codegen-internal and invisible to typecheck
  (`lenient-eval.md` §2; typecheck spine §5.2). Direction (a) asks the analysis to
  compute a fact it structurally cannot see, at large cost, on the wrong axis. Rejected.

**Direction (b) is strictly worse than (d).** Copying a stack arg to the heap before
crossing pays TWO allocations (stack slot + heap copy) to undo a stack allocation the
backend never needed to make. Since the backend *decides* the spark placement, the
clean move is to **not stack-allocate the relocated construction in the first place**
(decline → one heap alloc), not stack-then-copy. Medium-sized and wasteful. Rejected.

**Direction (c) is the mode-gating "cancer" class.** Mode-gating B3.4 to non-lenient
splits the emission path on a runtime-eval-strategy flag: the same program would
stack-allocate under `--link`/`NO_LENIENT` and heap-allocate under lenient REPL/`--run`.
Per `memory/feedback_investigate_suspected_dual_path.md`, mode-keyed codegen divergence
is a serious red flag — enforcement belongs at the *shared seam*, not a mode-specific
gate. (d) is NOT a mode divergence: it is ONE gate reading ONE local fact
("is-this-construction-in-a-spark-thunk") that is present on both paths — under
`NO_LENIENT` no thunk is synthesized, so the gate never fires and the full stack-alloc
win still lands; under lenient, only the relocated constructions decline. Rejected.

### (d) is the SAME shape as the existing gate 3 (the frame-restructuring pattern)

Gate 3 (§4.1) already declines stack-alloc inside a TCO loop body, because a TCO
back-edge is a **frame-lifetime transformation the per-frame escape analysis cannot
see** — the value's iteration-frame is reused under a live reference. Lenient
arg-sparking is the *identical shape one level over*: the backend synthesizes a spark
thunk (`MonoExpr::Lambda`, `apply.rs:224`) whose frame pops at the join, relocating the
arg computation — and its stack allocations — out of the frame the escape fact was
computed against. **The escape fact is CORRECT for the strict `MonoExpr` frame
structure; the backend then rewrites that structure underneath it.** The cure is the
same as gate 3: a backend-local, always-sound decline at exactly the sites the backend
itself relocates. The backend is the only actor that can compute this signal (it owns
the spark-placement decision), which is why it is a backend-local gate, not an analysis
fact. This is the "backend-local emission sharpening" boundary property now recorded in
the spine (`design/arch/ownership-inference.md` §2.2).

### Precise implementation guidance (for `/dev (cranelisp-backend)`)

1. **The invariant to enforce:** *a stack slot must not cross a spark boundary.* A
   construction compiled inside a backend-synthesized spark-thunk body must NOT
   stack-allocate — the thunk frame pops at the join while the value is consumed after
   it.

2. **The gate.** Add **gate 5** to `constructor_call_stack_eligible`
   (`fn_compiler.rs:730`), symmetric to gate 3's `self.fn_has_self_call` read: an
   `in_spark_thunk` (name /dev's) boolean on `FnCompiler`, checked
   `if self.in_spark_thunk { return false; }`. Declining is always sound.

3. **Setting the flag — single-sourced across ALL three spark sites.** The flag must be
   true while compiling any spark-thunk body, covering all backend spark emitters so the
   gate is single-sourced (Principle 7):
   - apply-arg sparks — `apply.rs:245` (`this.compile_expr(&thunk_expr)` in the Phase-1
     loop);
   - independent `let`-binding sparks — `compile_let_lenient` (`let_if.rs`);
   - dependent `let`-binding sparks (§2.6 of `lenient-eval.md`).

   **Propagation precedent is one line away:** `spark_capture_borrow` (`apply.rs:243-246`)
   already does the exact save-set-restore-around-thunk-compile dance for the analogous
   borrow-capture concern, and already reaches the inner `FnCompiler` that compiles the
   thunk `Lambda` body (the construction `(Some 10)` lives in the lambda body, so gate 5
   must be observed by the inner `FnCompiler`, not the outer one — mirror how
   `spark_capture_borrow` crosses that boundary). Prefer factoring a single
   "compile-this-expr-as-a-spark-thunk-body" helper that both raises `in_spark_thunk`
   (and `spark_capture_borrow`) and restores them, so no spark site can forget the gate.

4. **Scope for increment I: decline ALL stack-alloc inside a spark thunk.** Do NOT
   attempt the tighter "decline only constructions reaching the thunk's tail/return"
   refinement (the 0524 lambda-frame analogue) now — declining is always sound, the
   thunk body is typically a single expensive `Apply` (spark cost heuristic), so
   thunk-internal stack wins are marginal, and increment I ships the zero-obligation
   class. The refinement is an increment-II option, not a blocker.

5. **Activation.** With gate 5 in place, flip `STACK_ALLOC_ESCAPE_FACT_SOUND = true`
   (`fn_compiler.rs:1156`) in the SAME change-set. Re-run the full killer/win/adversarial
   + full-suite behavioral verification INCLUDING the multi-arg lenient shape, under
   `MALLOC_PERTURB_`.

### Acceptance

- **The killer stays cured:** `nested_match_in_arm_body` (and the 2+-stack-ADT-arg
  lenient shape generally) stays HEAP — its sparked-arg constructions decline via gate 5
  — no UAF, value-correct (`(d (Some 10) (Some 32))` ⇒ `11`) under `MALLOC_PERTURB_`.
- **The 0523/0524 killers stay cured** (`constructor_wrapped_in_lambda_applied_indirectly_works`,
  `polymorphic_higher_order_returning_adt`) — unaffected by gate 5.
- **B3.4 ACTIVATES:** the flag is `true`; the win fires.
- **The WIN survives:** genuinely-frame-local single-use constructors NOT inside a spark
  thunk still stack-allocate (`(MkBox 5)`, scalar lookup-table vecs). Under `NO_LENIENT`
  gate 5 never fires — the full corpus win lands. `07_trait_dispatch`'s `(MkBox 5)`
  stack-allocates in the golden.
- **Byte-identical-OFF** holds (gate 5 is downstream of the `STACK_ALLOC_ESCAPE_FACT_SOUND`
  early-return; with the flag off nothing changes).
- Unit matrix: extend `fn_compiler::b34_stack_eligibility_tests` with a gate-5 cell
  (in-spark-thunk ⇒ ineligible) alongside the existing gate-3 (TCO) cells.

### Size / sprint disposition

**CONTAINED — do-now (this sprint, if the ladder reaches it), NOT a defer-to-S103.**
This is a backend-local emission gate mirroring an already-landed gate (gate 3), riding
an already-landed propagation precedent (`spark_capture_borrow`), with the whole B3.4
mechanism already implemented and held off behind one flag. No `cranelisp-types` change,
no typecheck change, no confinement-precision work, no cache-schema bump, no
mode divergence. `/sprint`: dispatch to `/dev (cranelisp-backend)`; B3.4 activation is a
**small backend-local change**, not a large typecheck/confinement effort. (Per the S102
best-judgment note, if the ladder has already moved past B3.4 toward the measurable
increment when this lands, activating B3.4 with gate 5 remains a self-contained
change-set that can land whenever scheduled — it no longer blocks on any other skill.)

## Operational implication / Context

- **B3.4 stays held off** (`STACK_ALLOC_ESCAPE_FACT_SOUND = false`), byte-identical
  to pre-B3.4. Baseline unchanged: **3900 / 3897 / 3 / 1** (the 3 REDs are the
  standing `display_exact` W13 bug + `h2`/`h3` counter-surface guards, unchanged
  by name). The full mechanism (four gates + `emit_stack_alloc` immortal header)
  remains landed and unit-tested; it activates unchanged once this ruling lands.
- **Recurrence note:** B3.4 activation has now been blocked THREE times (0523
  capture, 0524 lambda/HOF-return, 0525 lenient-spark). The first two were escape-
  classifier gaps (cured). This one is architectural: the escape fact alone can
  never be a sufficient stack-alloc precondition while the backend introduces
  strand crossings the strict analysis can't see. Per
  `feedback_review_root_cause_and_duplication`, the recurrence itself is the
  signal that the fact set / gating model needs a structural decision, not another
  one-off patch.
- **No /qa repro owed separately** — the failing shape is already a committed,
  green (flag-off) e2e regression (`nested_match_in_arm_body`); it flips to a
  guard the moment B3.4 activates, so it is the durable record of this blocker.
