# S110 P5-S1 attribution — SG-1 (`derive` gate catch) + SG-2 (agent-lane interleave)

/qa attribution dispatch, 2026-07-15. Both findings surfaced by the `/testing`
P5-S1 pass (`c31b6050`, SPRINT.md §Skill plans → /testing). Method: read-only
investigation + binary probes (existing `target/debug/cranelisp`, no rebuild,
no suite run — a source-touching wave was concurrent). FIXMEs filed:
0613 (/dev), 0614 (/stdlib), 0615 (/testing).

## §1 SG-1 verdict: REAL DEFECT (layered — two defects, two owners), NOT an enumeration refinement

The gate (`tests/stdlib_conformance.rs::stdlib_all_public_modules_compile_and_run`)
is doing exactly its job: `derive` is a public stdlib module (planned
importable surface, `plan-stdlib.md` §3.3 rows 33–36) that does not compile.
Excluding it would recreate the 0605 blindness. The error signature masks a
LAYERED bug — the named failure mode the attribution role exists for:

### Layer 1 — compiler defect (owner /dev; FIXME 0613)

Quote/quasiquote are NEVER desugared outside macro-clause compilation.
Minimal repro (stdlib-free, mode-uniform REPL ≡ `--run`, verified on HEAD):

```clojure
(defn helper [x] `(if ~x 1 0))
;; => parse error: unexpected quasiquote form — should have been expanded
```

`'(1 2)` (top level or in a `defn` body) dies identically. Control: the same
template inside a `defmacro` clause works. Evidence chain:

- Sole production caller of `cranelisp_frontend::expand_quasiquotes` is
  `src/process_form/macro_clause.rs:53`; the general form path never desugars.
- The stated contract is desugar-on-every-form: frontend `lib.rs:48`,
  `design/frontend/frontend.md:127` ("runs unconditionally on every form,
  before macro-call dispatch"), `s76-syntactic-only.md` cascade row. The
  `ast_builder.rs:1171` error is a backstop for a pass that never ran —
  likely dropped in the S76 W-Macro migration.
- Spec §9.4 defines quasiquote as general reader-level sugar (no
  macro-body-only restriction); the desugared raw-ctor equivalent compiles
  fine in `defn` bodies. A one-line /spec confirmation is requested at the
  next user gate (0613 §Spec basis); default disposition is the fix.
- Gate linkage: `derive.cl` fails at byte 5306 = line 166, the first
  quasiquote in a plain `defn-` body — no macro invocation in the probe.

### Layer 2 — stdlib defect (owner /stdlib; FIXME 0614)

Fixing layer 1 does NOT green the gate: `derive.cl`'s four macros call ~30
same-module `defn-` helpers, which spec §9.3.4 forbids ("define the helper in
a dependency module"). Enforcement verified by cross-module probe — the
compiler emits the clean §9.3.4 diagnostic. The module's S87 tail comment
(derive.cl:405–421) mis-attributed the failure to same-module-MACRO
availability; in fact the module has never compiled on the v4 pipeline
(nothing in tests/examples/exemplar imports it — the exact blindness 0605
was filed to expose).

### Disposition

- **Gate treatment: stays RED, failing-not-ignored**, tracing to 0613 + 0614
  (RED-vs-known-defect integrity preserved). No exclusion, no `#[ignore]`.
  The aggregated report still names any NEW failing module loudly, so the
  standing RED does not blind the gate to fresh breakage.
- **Fix-vs-carry (Phase-5 conclusion): CARRY both to S111** — `derive` is
  uninvoked, S110 is already broad, and 0613 wants a small seam ruling
  (desugar at int's chokepoint vs inside frontend `build_form`). The 0613 fix
  is small; `/sprint` may pull it into W-SRC if slack. In-sprint obligation
  regardless: `/testing` commits the 1-line narrow repro (+ quote sibling,
  form×position matrix — 0613 §/testing request) so the compiler defect has
  its own durable failing record independent of the stdlib module.

## §2 SG-2 verdict: build-artifact provenance race (owner /testing; FIXME 0615) — in-sprint, W-GATE lane

NOT flaky/pre-existing (forbidden dispositions): the outcome is a pure
function of which binary sits at the hardcoded harness path at spawn time.

- Harness spawns `workspace_root()/target/debug/cranelisp` for every test
  (`tests/helpers/e2e.rs:368–371`); the agent lane
  (`cargo nextest run --features agent --test agent`) rebuilds the SAME path
  with the agent feature. A concurrent agent-lane build swaps the binary
  mid-default-suite; feature-OFF guards (`tests/agent.rs:143` asserts exit-1
  rejection of `--agent`) then exec an agent-capable binary that accepts the
  flag → fail. Single-profile runs are safe — matches /testing's
  non-reproduction under `cargo nextest run`.
- **Recommended fix shape** (0615): agent-lane `CARGO_TARGET_DIR=target/agent`
  isolation via a committed `tests/scripts/run-agent-lane.sh` + lane-aware
  binary resolution in `materialise()` + docs. A nextest setup-script
  ordering fix alone is INSUFFICIENT — it orders within one invocation; the
  race is between invocations.
- **Owner: /testing** (harness + scripts + config only; no compiler source →
  not /dev). Acceptance: agent family 3× consecutive full-suite passes, no
  retry, PLUS the deliberate dual-build clobber check (0615 §Acceptance).
- **Separate root from 0604** (build substrate vs runtime SharedState
  write-race) — recorded, not folded. Risk row: `risks.md` S110-11.
- **Fix-vs-carry: FIX in-sprint** — it already rides the planned W-GATE lane;
  the only scheduling constraint is running the acceptance sweeps when no
  other agent is testing.
