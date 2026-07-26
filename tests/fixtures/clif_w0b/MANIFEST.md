# W0.b lenient-class golden-CLIF corpus — MANIFEST

**Gate:** KC-W0-2 (`tests/plan/PLAN.md §S110`) — the CLIF byte-identity
shippability gate for the W0.b totalization flip
(`design/arch/backend-keyed-consumer.md` §4 W0.b + §5).
**Owner:** `/testing` (corpus + goldens + this manifest + the harness
`tests/golden_clif_w0b.rs`).

## Why this gate exists

W0 landed the producer carriers WRITE-ONLY. The **W0.b flip** makes typecheck
the SOLE mono-view producer for every codegen-reached body — including the
LENIENT/synthetic classes that legitimately fail strict `MonoExpr::from_expr` —
and turns the backend's `lenient_mono_from_expr` arm into a hard error (design
§4 W0.b, §5 ruling). W0.b is *specified* behaviour-invariant, but a passing
suite proves only that the code still RUNS, not that the generated code is
UNCHANGED. This corpus captures the current (pre-W0.b) CLIF for the lenient
classes as the golden so the flip can be ASSERTED byte-identical. The harness
`golden_clif_w0b_*` is the `/dev` W0.b wave's named acceptance.

## The lenient entry classes (design §5 finding 1; backend lib.rs:654-657)

The backend lenient arm is taken when a codegen-reached entry has
`codegen_view: None` OR its kind is not `UserFn{Concrete}`
(`requires_codegen_view == false`). Six classes reach it.

| # | Entry | Class | Focus frame(s) | Live-reachable e2e |
|---|---|---|---|---|
| 01 | `corpus/01_ctor_def.cl` | ctor `Def` synthetic body (`DefKind::Constructor`) | `user::Box.MkBox` | yes |
| 02 | `corpus/02_synth_accessor.cl` | synthesised field accessor (`Concrete{slot}`, `codegen_view: None`) | `user::Point.x`, `user::Point.y` | yes |
| 03 | `corpus/03_multisig_variant.cl` | `f$Var` multi-sig variant body | `user::pick$Int`, `user::pick$Int+Int` | yes |
| 04 | `corpus/04_expr_disposition3.cl` | `__expr` §3.11.2-disposition-3 body | `user::__expr` | yes |
| 05 | `corpus/05_macro_clause.cl` | non-concretized macro-clause body | `user::__macro_twice_clause_0` | yes |
| 06 | — | generic template reached by direct compile | — | **NO — backend-unit-only** |

### Class 06 — generic template (not an e2e golden; the KC-W0-6 boundary)

The sixth class is structurally **not live-reachable** by a free-standing
program, so it has no e2e golden here:

- Pure `Polymorphic` / `Constrained` templates (and `Overloaded` bases) are
  EXCLUDED from the codegen name-set (`src/worker.rs:896-902`) and produce no
  `.o` (`src/session_v4/nice_worker.rs:171`, `src/scheduler.rs:204`). A REPL
  `/clif` on a bare template answers "no CLIF IR available" — the template is
  slot-less/code-less until a concrete use mints a mono instance (which is a
  `UserFn{Concrete}` on the CONCRETE-view path, not lenient).
- The only path that lowers a bare template is the backend-crate unit helper
  `crates/cranelisp-backend/src/jit.rs::compile_defn` (its rustdoc: "the GENERIC
  defn template … that the REPL calls directly" — STALE; corrected W3). Every
  caller is `#[cfg(test)]` (verified by call-site grep 2026-07-15; design §5
  finding 3). `tests/` is e2e-only (two tiers, no middle), so this class cannot
  live here.

**Guard ownership:** class 06's byte-identity is the **backend unit suite's**
concern (KC-W0-6), not this e2e gate. When W0.b/W3 delete `lenient_mono_from_expr`
+ `compile_defn`, the `compile_defn`-based unit tests migrate onto
typecheck-built / `from_expr`-built views (design §5 finding 3 / W3 residual);
those unit tests are the class-06 golden.

## Capture contract (binding on any (re)capture)

- **Mechanism:** `CRANELISP_CODEGEN_DUMP='*'`, cold-cache `--run --no-cache`,
  one invocation per corpus entry in an isolated tmpdir (self-importing —
  `(import [primitives [*]])`, no prelude file). `--no-cache` structurally
  eliminates the nice-worker `.o` cache-write pass, so each symbol dumps exactly
  ONCE (the JIT pass). A **duplicate frame is a hard error** (config drift),
  never deduped.
- **Frames** are extracted per `; === CLIF <module>::<symbol> ===` block, sorted
  by `module::symbol`, content **byte-verbatim, NO canonicalization**. **Zero
  frames is a hard error** (empty-vs-empty false green). Dump channel is STDERR.
- **Normalization decision (byte-verbatim, /testing's call):** SSA value numbers,
  block labels, GOT-slot operands, and wrapper identity are LOAD-BEARING for this
  gate — masking them would blind it to exactly the carrier-vs-code drift W0.b
  must not introduce. Byte-identity is admissible because the dump is
  DETERMINISTIC — the harness double-captures and asserts identity BEFORE the
  golden compare. This follows the L-B1 precedent
  (`tests/fixtures/clif_baseline/MANIFEST.md` §Capture contract). If a future
  change ever makes a class nondeterministic, that is a real ordering bug to
  investigate, not a reason to canonicalize.
- **Determinism self-test:** the harness (`assert_golden_clif`) double-captures
  per entry and byte-compares BEFORE the golden compare — always on, every run.
- **Config pins (emission-affecting env UNSET — keep in lockstep with the L-B1
  smoke's `env_remove` list and `tests/scripts/clif_golden.sh dump()`):**
  `CRANELISP_NO_OWNERSHIP`, `CRANELISP_NO_LENIENT`, `CRANELISP_CAPTURE_BORROW`,
  `CRANELISP_NONATOMIC_RC`, `CRANELISP_RC_STATS`, `CRANELISP_RC_DEC_CHECK`,
  `CRANELISP_NO_IO_SCHEDULE`, plus the compile-time trace vars
  (`CRANELISP_RC_TRACE`, `CRANELISP_CODEGEN_TRACE`, `CRANELISP_GOT_TRACE`,
  `CRANELISP_MODULE_TRACE`, `CRANELISP_SCHEDULER_TRACE`, `CRANELISP_IO_TRACE` —
  they write to the stderr dump channel).
- **Extension ≠ re-baseline; scoped re-baseline only** for emission-affecting
  changes, delta attributed to the change's seam in the same commit. W0.b is
  behaviour-invariant, so the expected W0.b delta is EMPTY. Wholesale re-capture
  without attribution is forbidden.

## Green witness (capture, 2026-07-15, HEAD `144828d1` producer state)

| Entry | Frames | Lines |
|---|---|---|
| 01_ctor_def | 2 | 54 |
| 02_synth_accessor | 4 | 170 → **148** (S118 W3 re-baseline, below) |
| 03_multisig_variant | 3 | 52 |
| 04_expr_disposition3 | 1 | 20 |
| 05_macro_clause | 2 | 121 |

Determinism self-test passes 5/5 (double-capture byte-identical).

## Re-baselines (scoped, attributed — §"Extension ≠ re-baseline")

- **02_synth_accessor** — re-captured S118 (FIXME 0908) for the **W3 consumer
  migration onto canonical drop glue**, change-set `2df95c41..966d298e`
  (`c6234398` S1 `emit_typed_rc_dec` becomes the canonical glue-call emitter is
  the emitting seam). **Release-family reshape only, in the two accessor frames
  and nowhere else.** In `user::Point.x` and `user::Point.y` the self-param
  release site changes from the inline sequence `iadd_imm self,8; iconst 1;
  atomic_rmw sub; icmp eq; brif; fence; call dealloc(self)` (two blocks) to ONE
  `call fn1(self)` where `fn1 = colocated u0:41` carries the **VOID `(i64)`
  signature** of the canonical per-concrete drop glue — the guard, the fence and
  the teardown now live inside the generated glue body
  (`design/backend/transitive-drop-glue.md`). The signature-table and
  value-renumbering deltas are consequences of the removed instructions; the
  other two frames of this entry (`user::Point`, `user::main`) and all four other
  entries are **byte-identical** (verified: an independent capture of 01/03/04/05
  reproduced their committed goldens exactly). No RC op is dropped without a glue
  call taking it over, no retain count changes, and no arithmetic, allocation,
  dispatch or control-flow hunk appears outside the release family. Determinism
  self-test 5/5; both golden binaries green post-capture.
