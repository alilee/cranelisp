---
number: 0525
target: /arch
filed_by: /dev
filed_at: 2026-07-05
sprint_filed: 102
refers_to: design/backend/ownership-codegen.md §4 (B3.4 stack slots) + §4.3 (ParBind/spark interaction), design/typecheck/ownership-inference.md §5.2 (confinement over-approximation), crates/cranelisp-backend/src/compiler/fn_compiler.rs (STACK_ALLOC_ESCAPE_FACT_SOUND)
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
