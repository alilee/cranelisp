# QA risk register

Owner: QA. This register names the solution risks QA carries as standing
concerns, the control that currently answers each, and the residual that
remains. It is read when allocating evidence or judging whether a control
earns its cost. Sprint-scoped risk reads are dated allocations and live in
Git; the [safety-invariant register](../../design/arch/safety-invariants.md)
owns invariant grades and the [memory-safety strategy](memory-safety-coverage.md)
owns lane mechanics. Each entry is judged under the shared
[risk-weighted control standard](../../.agents/skills/quality-standards/SKILL.md):
a retained control names the credible failure it discriminates and its cost;
a historical gate is not a current requirement.

The per-sprint reads S109–S118 and the ring-era baseline (Risks 1–10 and the
prototype spec-coverage table) are retired to Git
(`git show 7b1220c7:tests/plan/risks.md`); the S113 global ranking that the
S113 read summarised is the S113 risk assessment at Git revision `7b1220c7`.
Their standing rules live where a reader needs them: relational coverage axes
(carrier × reaching context, shadowing × callee kind, storage model × persisted
kind, module locality) in [PLAN](PLAN.md#standing-coverage-audit--definition-variants);
suite-count and leak-scaling conventions in [PLAN](PLAN.md#traceability-and-authoring);
mode uniformity, defect classes and the failing-test discipline in the
[tests memory](../CLAUDE.md); the spec-change annotation-clearing rule in the
[delivery method](../../sprints/METHOD.md#22-phase-notes); the differential
oracle, capability-fence and adversarial-authorship rules in the strategy.
Rankings, counts and wave statuses in those reads describe their sprint, not
the current tree.

## Memory-safety signal blindness (standing since S111)

- **Credible failure.** A leak, use-after-free or elided safety operation that
  does not perturb printed output passes every output-asserting test. A UAF
  often returns plausible values under REPL and `--run` and is deterministic
  only under `--link` (glibc abort), `CRANELISP_RC_DEC_CHECK`, or the
  analysis-off differential oracle.
- **Current control.** The nextest-visible oracle lane and `SafetyMatrix`
  combinator (`tests/safety_oracle_lane.rs`, `tests/helpers/e2e.rs`), graded
  `gated` with a live catch in register row R9; the tier-5 diagnostic modes of
  row R8; the ownership-flow generator (`tests/gen_ownership_flows.rs`) with
  its own capability fences per strategy §4.1; refute-instructed review on
  safety surfaces (strategy §3).
- **Residual.** Coverage is bounded by the lane's cells and the generator's
  actual types, positions and modes. The suite-wide reach quantification in
  strategy §5 is an S111 measurement and no later re-grade is recorded there;
  reuse it as a dated figure, not a current share. The strategy names the
  retirement condition: the class becomes mechanically RED at the gate rather
  than found incidentally.

## Risk 11 — slow-accumulating FFI/platform-ABI heap corruption (standing since S86)

- **Credible failure.** A host↔platform-DLL marshalling contract mismatch
  (payload versus base pointer, omitted header offset, reordered field)
  overruns adjacent heap metadata by a fixed few bytes per crossing. It is
  invisible below a crossing threshold and a glibc abort above it, and it is
  distinct from an RC miscount: every RC-driven free still hits `rc = 0`
  cleanly on a correctly located object. The instance is DEF-6 (S86, `--link`
  only), class `marshal-overrun` in the [defect vocabulary](../CLAUDE.md#defect-repro-notation--defect).
- **Current controls.** Constructive: both hosts build their callbacks
  through one builder, `cranelisp_intrinsics::host_callbacks()`
  (`src/platform.rs`, `crates/cranelisp-exe-bundle/src/lib.rs`), so the
  JIT/link wiring divergence that produced DEF-6 has no second source.
  Measured: the sustained-repetition, link-then-run guard
  `tests/link.rs::link_repeated_platform_adt_marshal_does_not_corrupt_heap`
  (200 crossings, well above the observed ~40 threshold); the
  [tests memory](../CLAUDE.md#diagnostic-env-vars--assertions) states the
  sustained-repetition and run-under-load rules for every marshalling
  boundary. Diagnostic: the intrinsics allocator's dealloc-time
  header-integrity check (`crates/cranelisp-intrinsics/src/alloc.rs`,
  debug builds) and the release-gated A4 header pre-check.
- **Residual.** No checking-allocator (ASan/valgrind) lane exists; the
  strategy defers a `--link`-with-ASan lane to a provisioned toolchain lane
  (§2.2) and no current risk earns building one sooner. A per-crossing
  header assertion at the marshal seam itself was not verified at source in
  the S122 read; the dealloc-time check is the located detector.

## Standing coverage lenses from risk (S118 origin)

- **Eliminator/consumer axis.** For every construct that consumes a value it
  owns while handing a projection onward — `match` on constructor and
  variable patterns, field accessors, `vec-get` on a temporary container,
  destructuring `let` — the coverage question is a
  `{provenance: fresh | let-bound | borrowed param} × {projection escapes:
  yes | no} × {payload: scalar | heap}` matrix, both polarities, asserting
  absolute `allocs == deallocs` with a `--link` face: the differential face is
  blind to this toggle-independent class and the double-free polarity is
  `--link`-visible only. Framing risk by origin alone (return, capture,
  container, loop-carry) misses the eliminator. For a loop-coupled release
  seam the matrix carries a fourth factor,
  `{eliminator in its own frame | eliminator is the loop body}`: an
  eliminator wrapped in its own function and driven by a repeater never
  reaches the tail-jump seam, so a green row in the wrong frame is vacuous.
  The generator's eliminator rows (`tests/gen_ownership_flows.rs`) are the
  mechanical fence; `tests/match_owned_temporary_scrutinee_0810.rs` pins the
  cells the generator cannot yet reach.
- **Arm-order and operand-order twins for join-shaped seams.** Any
  join/merge/fold operation — `if` arms, `match` arm sequence, element-fold
  accumulation, lattice joins — takes order-swapped twin cells (same
  contract, orders swapped, same assertion) plus, at the seam, algebraic
  property cells over the operand lattice (commutativity, union
  preservation) rather than example cells over one syntax tree; a shape cell
  fixes the order and cannot fail on an order asymmetry. The model cells are
  `join_lattice_*` in `crates/cranelisp-typecheck/src/ownership/transfer/tests.rs`.
  QA checks new join-shaped seams for this at every Phase-3 plan.
