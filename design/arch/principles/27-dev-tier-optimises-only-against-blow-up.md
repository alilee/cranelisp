---
number: 27
title: The dev tier optimises only against asymptotic blow-up
---

# Principle 27 — The dev tier optimises only against asymptotic blow-up

> User-directed on 2026-11-16 (S123 W3 rulings "Dev-path optimisation" and
> "Principle 27 questions") and authored at S123 W4. **Ratified at S123
> Phase-7 close (user-approved 2026-11-16).** The user's words: "simplify the dev
> path. we just need enough optimisations to avoid exponential time.
> otherwise we'll defer to release build. however, we should be retaining the
> type annotations that release optimisations might rely on, even if dev does
> nothing with them." The user confirmed that "exponential" means any change
> of growth rate.

**Statement.** The dev tier is every lowering the compiler performs today:
`--run`, `--link` and the REPL, on Cranelift. It emits the simplest correct
lowering of each program. It keeps an optimisation only when, without it, a
program's running time or memory would grow at a faster rate than the
program's own algorithm implies. The test is a change of growth rate, not of
constant factor. Every other optimisation belongs to the release tier
([release proposal](../release-llvm-backend.md)). Parallel evaluation is the
one carve-out (below). The facts a release optimisation relies on keep being
computed, published on the codegen boundary and tested where they are
produced, even when the dev lowering reads none of them.

**Scope.** The principle governs the code the compiler emits and the runtime
representation of values. Compile-time machinery, such as the module cache and
incremental JIT compilation, is outside it.

**What the dev tier keeps.**

- **An optimisation that holds a complexity class.** For example, the last-use
  move and the in-place update at count 1
  ([uniform counting](../../backend/uniform-counting.md) §2, rules U1 and U2)
  keep a loop that updates a uniquely held vector linear. Without either rule,
  every update copies the vector and the loop becomes quadratic. Doubling a
  vector's capacity when it grows keeps a push loop linear in the same way.
- **A lowering the language requires.** This is not an optimisation in this
  principle's sense. The constant-stack tail self-call is one example.
- **The direct lowering of a primitive.** This is not an optimisation either.
  For example, the inline scalar primitive table lowers `add-i64` to one
  instruction rather than a call. A call would not be the simpler lowering.

**What it defers.** An optimisation whose absence costs a constant factor,
however large, belongs to the release tier. Examples include stack placement,
non-atomic counting, value flattening and elided or fused RC operations.

**The parallelism carve-out.** Lenient evaluation stays on the dev tier, even
though its gain is bounded by core count and is therefore a constant factor.
The parallelisation goal of the [ownership spine](../ownership-inference.md)
§0 also stays in force. The reasons are these:

- **The language requires it.** `spec/12-runtime.md` §12.4.3 requires
  independent `let` bindings to be evaluated in parallel where a cost
  heuristic finds it beneficial. Parallel evaluation is part of the language
  every tier implements, not a lowering choice.
- **It must be tested where it is checked.** The dev tier is the correctness
  oracle. Concurrent evaluation exercises a spark's capture and release rules,
  the panic rule and the create-gate budget. A dev tier that never sparked
  would leave those rules unchecked until a release tier exists.

The carve-out covers parallel evaluation and its admission heuristic. It does
not keep the tuning mechanisms already ruled for retirement, such as the
spark-density axis and confined non-atomic counting.

**Retained facts.**

- **A fact outlives its dev consumer.** A fact that typecheck computes for an
  optimisation keeps being produced, persisted and tested when its dev
  consumer retires. Examples are the escape, confinement and uniqueness site
  facts, the per-parameter modes, and the value-layout predicate. The release
  tier reads the same facts through the same boundary
  ([Principle 07](07-single-source-of-truth.md)).
- **This is the one exception to "no analysis without a consumer".** A
  mechanism without a consumer is still excluded
  ([Principle 08](08-no-interim-implementations.md)).
- **New facts stay narrow.** A new fact still answers to the narrowness
  counterweight ([ownership spine](../ownership-inference.md) §3.3).
- **Grade.** The producer's tests measure what the analysis computes. They do
  not establish that a fact is sound for the optimisation it serves. That
  claim is not made until a consumer exists, and the consumer then carries
  its own check ([Principle 25](25-narrowing-carries-its-check.md)).
  Falsifier: the release consumer's differential against the conservative
  lowering.

**Admitting a dev optimisation.**

- **Only against a blow-up.** No optimisation joins the dev tier for a
  constant factor.
- **Name the blow-up and measure it.** A proposal names a workload whose
  growth rate changes without the optimisation, and shows the measurement.
  The measurement happens inside the design window (root `CLAUDE.md`
  §Assurance).
- **It carries its check.** The optimisation is checked against the
  conservative lowering, which stays reachable (Principle 25).

**Acid test.** *Remove the optimisation and scale the input. Does the cost's
growth rate change, or only its constant?* If only the constant changes, the
optimisation belongs to the release tier, unless it is parallel evaluation.

**Relationship to existing principles and rulings.**

- **Principle 25.** The dev tier ships Principle 25's conservative reference
  semantics, except for the narrowings this principle admits.
- **Principle 06.** This is Principle 06 applied to emitted code: every
  optimisation on the dev tier is a cost to every correctness argument made
  there.
- **Earlier placements.** This principle supersedes the S100 placement of the
  memory-model mechanisms in the shared lowering
  ([ownership spine](../ownership-inference.md) §3.4). It also replaces the
  2026-11-15 ruling that kept stack placement pending a cost measurement.

**Motivating context (S123).** Uniform counting (reading U′) removed the only
consumer of confined non-atomic counting. Keeping the classifier would have
meant code with no caller, and the cost measurement could not inform the
choice, because both arms emitted the same code. The user ruled that the
backend classifier retires and that typecheck keeps producing its confinement
and escape facts.
