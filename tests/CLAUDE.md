# tests/

Test infrastructure for the Cranelisp reimplementation.

**Ownership.** `tests/plan/` is owned by `qa` (strategy, risk, coverage
process and attribution; its [current assurance plan](plan/PLAN.md) supplies
evidence policy, navigation and active allocation without replacing the specs).
Everything else here — `tests/*.rs`, `tests/helpers/`, `tests/fixtures/`,
`tests/scripts/`, `// defect:` notation upkeep, and this file — is owned by
`test`. Per-crate `#[cfg(test)]` unit tests are `dev`'s and live in
`crates/{crate}/src/`, not here.

## Two tiers, no middle

Cranelisp tests follow the [current QA tier strategy](plan/PLAN.md#strategy--two-tiers-no-middle)
and fall into exactly two tiers:

1. **e2e tests** — `tests/*.rs`. Run the `cranelisp` binary directly: REPL
   via stdin, `--run file.cl`, or `--link` then run the produced executable.
   Helpers are process-spawn + stdout/stderr/exit capture + isolated tmpdir +
   on-disk fixture files. **This is the release gate.**
2. **Unit tests** — `crates/{crate}/src/` `#[cfg(test)]` modules, authored by
   `dev` alongside the implementation.

Both tiers observe the *compiler*. A third, small and closed category observes
the **repository** instead — the standing gates that make root `CLAUDE.md`
§Assurance's mechanisms run on every `cargo nextest run` rather than when
someone remembers (`citation_drift.rs`, `role_wiring.rs`). They spawn a
stdlib-only checker under `scripts/`, take no position on language behaviour,
and trace to `CLAUDE.md` rather than to a `plan/PLAN.md` row. Each carries its
own detection proof against planted faults in the same file, because a gate that
cannot fire is indistinguishable from one that finds nothing.

There is **no middle integration tier.** Tests do NOT construct `Sess`,
`SharedState`, `SymbolTable`, or any internal session primitive. If a feature
cannot be expressed e2e, that is a gap in the binary's testability surface —
file an action for `qa` or `arch`; do not bridge with an internal-API helper.

## Plan documents (`plan/`, owned by `qa`)

| File | Purpose |
|---|---|
| `PLAN.md` | Current assurance policy, evidence navigation and active allocation. Fine-grained traceability remains in specs and test sources. |
| `risks.md` | Qualitative risk register. |
| `helpers.md` | E2E helper API design (contract for `tests/helpers/`). |
| `qa-retained-evidence-records` | Dated QA measurement, lane-baseline and coverage-analysis records retained because current designs, test sources and harnesses cite them by section. |
| `qa-support-documents` | Current QA support contracts, active evidence and retained checker reconciliation. |

The support collection comprises [isolation evidence](plan/0488-isolation.md),
[agent context tuning](plan/agent-context-tuning.md),
[agent strategy](plan/agent-testing-strategy.md), [helper design](plan/helpers.md),
[helper reference](plan/helpers-api.md), [memory-safety coverage](plan/memory-safety-coverage.md),
[risks](plan/risks.md), [S122 evidence](plan/s122-evidence-delta.md), and
[checker reconciliation](plan/s122-document-checker-reconciliation/README.md).

Retained `plan/s{NN}-*.md` files are dated records listed in
[PLAN retention](plan/PLAN.md#evidence-currency-and-retention); new working
plans are retired into it at close.

## Test file organisation

All active test files are e2e and live flat under `tests/`. Naming is by
convention — list them with `ls tests/*.rs`; do not maintain a count here.

- `spec_NN_*.rs` — one file per spec chapter (`spec_04_expressions.rs`,
  `spec_10_io.rs`, …). The primary spec-coverage suite.
- `repl_*.rs` — REPL experience (introspection, lifecycle, persistence, …).
- `concurrency_*.rs` — the effect/concurrency track.
- Concern-named files — `cache.rs`, `regression.rs`, `link.rs`,
  `examples.rs`, `exemplar*.rs`, `trace.rs`, plus targeted repro files named
  after the defect or property they pin (`tco_tail_arg_alias_uaf.rs`,
  `vec_cow_value_use_leak.rs`, …).

Supporting directories:

```
tests/
  CLAUDE.md              — this file
  plan/                  — qa's plan + tooling (see above)
  helpers/
    mod.rs               — module declarations only (pub mod e2e; marginal; regex;)
    e2e.rs               — the e2e harness: `Cranelisp` builder + subprocess
                            primitives + tmpdir/fixture management. Source of truth.
    marginal.rs          — the marginal-balance harness (see below)
    regex.rs             — named regex library for matching compiler output
  fixtures/              — on-disk fixtures (preludes/, stdlib_project/, golden/, …)
  scripts/               — build-link-prereqs.sh and other suite-level scripts
  perf/                  — measurement harnesses (per-sprint attribution/perf)
```

### Fixture and lane contracts (`test-fixture-contracts`)

Capture and run contracts for golden-CLIF fixture corpora and the checking-allocator fence lane.
Keep each beside the artifacts it governs:

- [L-B1 golden-CLIF corpus](fixtures/clif_baseline/MANIFEST.md) and its
  [exclusion register](fixtures/clif_baseline/EXCLUSIONS.md) —
  `clif_golden_lane.rs`, `ownership_fences.rs` smoke, `scripts/clif_golden.sh`;
- [W0.b synthetic-body golden-CLIF corpus](fixtures/clif_w0b/MANIFEST.md) —
  `golden_clif_w0b.rs`;
- [checking-allocator fence lane](scripts/asan/README.md) —
  `scripts/asan/run_fences_checked.sh`.

## Test helpers

Two sanctioned helper APIs, and no others: the `Cranelisp` builder in
`tests/helpers/e2e.rs` (below) and the marginal-balance harness in
`tests/helpers/marginal.rs` (§"Allocator balance is measured marginally").
`e2e.rs` is the source of truth for everything else. Every test file imports
what it needs:

```rust
mod helpers;
use helpers::e2e::{Cranelisp, PreludeVariant};
```

The builder composes in three stages: **construct + configure**, **select
mode**, **capture + assert**.

- `Cranelisp::new()` — fresh builder backed by a per-test `tempfile::TempDir`.
- Mode (mutually exclusive): `.repl()` (default), `.run(file)`, `.link(file)`,
  `.link_then_run(file)`.
- Fixture composition: `.file(rel, contents)`, `.user(contents)`,
  `.prelude(contents)`, `.with_prelude(variant)`, `.fixture(src, dst)`,
  `.fixture_tree(src_dir, dst_dir)` (copies from `tests/fixtures/`).
- Input/env: `.stdin(lines)`, `.stdin_lines(&[…])`, `.env(k, v)`, `.timeout(d)`,
  `.expects_exit_without_reading_stdin()` (opt-in EPIPE tolerance for a child
  whose contract is to reject the invocation and exit before reading; never a
  blanket swallow, see the method's rustdoc).
- Terminal: `.output()` → `CrOutput` (panics on spawn/timeout error);
  `.try_output()` returns the error instead.
- `CrOutput` carries fluent assertions: `.assert_ok()`, `.assert_exit(code)`,
  `.assert_stdout_contains(…)`, `.assert_stdout_does_not_contain(…)`,
  `.assert_golden(name)`, and more.
- Shortcuts for piped-REPL captures: `Cranelisp::repl_capture(lines)` (bare
  REPL) and `Cranelisp::repl_prims_capture(lines)` (with `PrimitivesOnly`).
- Cross-mode equivalence: `run_through_all_modes(program, prelude)` runs a
  program through REPL + `--run` + `--link` and asserts mode-equivalence.

Consult `tests/helpers/e2e.rs` for exact signatures — do not treat the summary
above as complete; it drifts, the source does not.

### Prelude variants

Tests select the prelude through `.with_prelude(PreludeVariant)`. Variants
materialise a file from `tests/fixtures/preludes/`:

- **`PreludeVariant::None`** — no prelude. Core language, slash commands, error
  handling that need no operators or ADTs.
- **`PreludeVariant::PrimitivesOnly`** — bare primitive imports, no traits/ADTs
  (`preludes/primitives-only.cl`).
- **`PreludeVariant::TestStandard`** — Option, Result, Num, Eq, Ord
  (`preludes/test-standard.cl`). Use when the test needs operators, `Option`/
  `Result`, or trait dispatch.

## Allocator balance is measured MARGINALLY, never absolutely

**Rule:** a cell asserting allocator balance over a child that loads a prelude
MUST measure a control/subject **pair** and assert on the difference. Absolute
`allocs == deallocs`, and thresholds like `residue <= 1400`, are both banned for
this class.

**Why:** every stdlib-prelude child carries a program-independent compile-time
residual from the macro-turn marshal boundary (FIXME 0889). An absolute cell
over such a child measures **only** that residual: it reads RED regardless of
the runtime behaviour it is named after, and it would read GREEN again the
moment 0889 is fixed even if that behaviour had rotted meanwhile. Either way it
is not an instrument. A threshold is worse than useless in the same situation —
it encodes today's ambient number as slack, silently absorbing new leaks up to
it, and it has to be re-derived every time the baseline moves.

**How:** `helpers::marginal` — `MarginalPair::new(label, control, subject)`, two
`Child`s that differ in exactly ONE thing (the program, or one macro invocation
in the library tree), `.instrument(…)`, `.measure()`, then `assert_balanced` (the
workload leaked nothing) or `assert_residual(n)` (an exact documented residual).
Both children are spawned identically by construction: same lane binary, fresh
private tempdirs, `--run --no-cache`, `env_clear()` + one enumerated allow-list,
instrument armed per-child. Every term common to both — prelude load, macro
expansion, the 0889 residual — cancels, and the instrument stays valid unchanged
after 0889 is fixed (the common term simply goes to zero).

**The harness has its own capability fence**
(`tests/marginal_harness_capability.rs`) and it is not optional reading: a
marginal that cannot see a real leak is a false green in every cell built on it.
It pins the resolution at one block (the M3 plant's single suppressed dealloc),
the zero-marginal polarity for identical children, and — load-bearing — that the
ambient residual is *deterministic run-to-run*, so subtracting it is exact rather
than approximate.

Worked callsites: `tests/ms_p8_conj_leak.rs`,
`tests/intrinsics_m3_detection_s116.rs`, `tests/macro_turn_marshal_leak_0889.rs`.

## Test isolation (prelude & stdlib)

Tests MUST NOT depend on `stdlib/` (root `CLAUDE.md` §"Design Principles" —
Stdlib separation). The suite uses its own QA-owned fixtures under
`tests/fixtures/` to validate language features independently of stdlib
evolution. The single named exception among suite tests is stdlib
conformance, gated behind the verbosely-named
`.use_workspace_stdlib_for_stdlib_conformance_only()` so misuse is visible in
review and `git grep`. Outside the suite, the REPL-agent eval runner copies
`stdlib/` into each run under QA's
[eval policy](plan/s122-evidence-delta.md#runnable-eval-corpus-and-policy).

## Fresh temp directory per test

**Rule:** filesystem-writing tests MUST use a fresh per-test tmpdir and MUST
NOT write to checked-in paths (`exemplar/`, `examples/`, `stdlib/`,
`tests/fixtures/`, `src/`, …) or to `workspace_root()`.

**Why:** `user.cl` persistence in a shared working directory accumulates
across runs and has masked a defect's disposition; cross-test state pollution
also hides races that fire only under specific filesystem preconditions.

**How:** `Cranelisp::new()` allocates a `tempfile::TempDir` and manages its
lifetime for the duration of the builder — compose fixtures into it with
`.file` / `.fixture` / `.fixture_tree`, never into the source tree. A test that
is genuinely read-only on checked-in paths may reference `workspace_root()` (to
locate the binary, `CRANELISP_LIB`, or a fixture), but the callsite MUST carry a
`// read-only on project_root` comment so audits can distinguish intentional
from accidental use.

## Test standards

- **Names describe behaviour, not implementation.**
  `let_polymorphism_infers_identity`, not `test_case_47`.
- **Language-semantics tests run through all modes.** Use
  `run_through_all_modes` (REPL + `--run` + `--link`) — a REPL/`--run`/`--link`
  divergence is always a defect.
- **RC tests run serially.** `--test-threads=1` for any test reading
  `CRANELISP_RC_TRACE`.
- **Error tests use substring matching**, not exact message comparison.
- **E2E tests invoke the binary only.** No Rust-API calls, no internal state
  inspection; the `Cranelisp` builder is the only sanctioned harness.
- **No test is silently dropped.** Every test traces to a spec section via
  `// spec:`; the [current coverage navigation](plan/PLAN.md#current-coverage-navigation)
  identifies the owning evidence family without duplicating every test name.
- **Negative tests verify absence, not just presence** (see below).

## Negative test convention

Positive tests verify correct behaviour; negative tests verify **incorrect
behaviour does not occur**. Both are required for full coverage — a suite that
only checks "the right thing appears" passes green while the system also does
wrong things.

- **Naming:** negative test names carry `_neg_` or `_not_`
  (`e2e_s3_3_list_neg_no_primitives_in_user`).
- **Spec annotation:** when negatives exist alongside positives, the spec tag
  upgrades `[Tested …]` → `[Tested+Neg …]`, making gaps visible at spec level.
- **Priority areas:** module boundaries (`primitives` symbols must NOT appear
  as `user/` entries), category boundaries (`/list` categories must not
  cross-contaminate), error boundaries (valid input must not error; invalid
  input must not succeed silently), display format (no unqualified names where
  qualified are required).

## Coverage by definition variants

`qa` owns this lens: [standing coverage audit — definition variants](plan/PLAN.md#standing-coverage-audit--definition-variants)
decides which variant families and relational axes a change must enumerate.
When authoring a cell for it, prefer the **twin fixture**: one invariant
satisfied two ways under the same assertion, so a variant that grew its own
codepath diverges the pair and the failing twin names the site.

## `--link` / platform prerequisites (nextest setup script)

The `--link` path links five workspace members it has **no Cargo dependency
edge to** — it resolves them by scanning `target/debug/` at runtime. A plain
`cargo nextest run` never compiles them, so `--link` fails with
`could not find libcranelisp_exe_bundle.a`. The fix is a nextest **setup
script** (`.config/nextest.toml` → `tests/scripts/build-link-prereqs.sh`) that
builds all of them in one `cargo build -p` invocation before any test runs —
one snapshot, no rlib-vs-bundle skew.

- **A test MUST NOT shell out to `cargo build`.** The artifact set is a
  suite-level invariant owned by the setup script.
- **A new platform/link fixture extends the script**, not a per-test build —
  add the crate to `tests/scripts/build-link-prereqs.sh`.
- `CRANELISP_PLATFORM_PATH` wiring is per-test runtime config (in the harness),
  not a build step.

## The agent lane (`--features agent`) — isolated target dir

The `--features agent` e2e lane MUST be run through the committed launcher, NOT
a bare `cargo nextest run --features agent --test agent`:

```bash
bash tests/scripts/run-agent-lane.sh
```

The launcher sets `CARGO_TARGET_DIR=target/agent` so the agent-featured binary
lives at `target/agent/debug/cranelisp` and can never clobber the default
`target/debug/cranelisp` mid-suite. The e2e harness (`helpers/e2e.rs::binary_path`)
resolves the binary root from `CARGO_TARGET_DIR`, so each lane execs its own
binary — isolation by construction. A shared target directory lets a
differently-featured build replace the binary a feature-off test then spawns.

### REPL-agent evals

`scripts/run-agent-evals.py` runs the task corpus in `fixtures/agent-evals/`
against the isolated binary. QA's [eval policy](plan/s122-evidence-delta.md#runnable-eval-corpus-and-policy)
defines the tasks, graders, result classes and report contents.

- Build the binary with `cargo build --features agent --target-dir target/agent`.
- Run `run-agent-evals.py self-check --out <new-dir>` to check the harness. It
  uses the stub provider, makes no network calls and exits 1 on any case
  mismatch. Stub results are harness evidence, not a model baseline.
- Run `run-agent-evals.py run --out <new-dir> --autonomy yes --provider stub
  --stub-script <file> [--task <id>] [--repeats N] [--timeout S]` to run the
  corpus. A live provider (`anthropic`, `ollama`) also needs `--allow-live`
  and a separately approved model, disclosure and budget. The runner refuses
  a live launch without `CRANELISP_AGENT_MODEL`, or for `anthropic` without a
  credential. Reports record only whether credentials are present, never their
  values.
- Each invocation needs a new or empty `--out` directory, so earlier attempts
  are never overwritten. `report.json` holds the provenance and per-run
  results; `runs/<run-id>/` retains that run's inputs, outputs, logs and
  project.
- `tasks/<id>.json` holds one versioned task. Change its `version` whenever you
  change the task. `self-check/cases.json` lists the parser and process cases
  and the report fields each case must produce.

## Diagnostic env vars & assertions

Silent by default, controlled by environment variables — set them on the
spawned subprocess via `.env(…)`, or export before `cargo nextest run`:

| Variable | Shows (stderr) | Reader |
|---|---|---|
| `CRANELISP_CODEGEN_DUMP=<name>\|*` | Framed CLIF for each matching compiled function; the golden-CLIF lanes' channel | `cranelisp-backend` `lib.rs` |
| `CRANELISP_RC_TRACE=1` | Every alloc, free, inc and dec with pointer (debug builds) | `cranelisp-intrinsics` `rc.rs` |
| `CRANELISP_OWNERSHIP_TRACE=1` | Per-cluster callable summaries and per-site ownership verdicts | `cranelisp-typecheck` `ownership/trace.rs` |
| `CRANELISP_MODULE_TRACE=1` | Module cache restore, dependency-record and save decisions | `src/` cache and session code |
| `CRANELISP_SCHEDULER_TRACE=1\|<modules>` | Scheduler registration and state transitions | `src/observability.rs` |
| `CRANELISP_IO_TRACE=1` | IO trampoline events | `src/io_trace.rs` |
| `CRANELISP_GOT_TRACE=1` | GOT slot writes (JIT, linker, redefinition) | `src/got_trace.rs` |
| `CRANELISP_CODEGEN_TRACE=1` | Nice-worker object-emission failures only | `src/session_v4/nice_worker.rs` |

The allocator diagnostic modes (`CRANELISP_ALLOC_PARITY`, quarantine, scrub,
`CRANELISP_RC_DEC_CHECK`) are documented in the
[CLI reference](../user/cli-reference.md#memory-safety-diagnostics-developer-tools).

A few-bytes-per-crossing overrun at the host↔platform marshalling boundary is
silent under the system allocator until it trips a glibc abort many crossings
later. Every marshalling boundary therefore needs a **sustained-repetition**
guard (drive it 200–2000 crossings in both directions, assert exit 0), and
`--link` capabilities guard link-then-run-under-load, not link success alone —
for example
`tests/link.rs::link_repeated_platform_adt_marshal_does_not_corrupt_heap`.

## Spec traceability

Every `#[test]` carries a `// spec:` comment naming the section it validates:

```rust
// spec: repl/spec.md §1.2 — Int display format
```

`test` adds the test-side `// spec:`; `qa` audits the two-sided match and
adds the spec-side `[Tested …]` annotation. Two structural verifiers live in
`plan/` (owned by `qa`; run them before landing annotation changes):

- `plan/spec_link_check.py` — test → spec: every `// spec:` anchor must match a
  real heading in the cited file.
- `plan/spec_coverage_reconcile.py` — spec → test: every `[Tested tests/FILE::name]`
  citation must resolve to an existing file + `fn name`. Guards against
  citation rot after suite reorgs.

## Public-API enforcement

`tests/public_api_relocations.rs` is the executing drift guard for the seven
library crates enumerated in that file. It compares live `cargo-public-api`
output with each committed `crates/<crate>/public-api.txt`; the retired
`tests/facade_compliance.rs` is a tombstone and carries no public-surface
authority.

The baselines require `cargo-public-api >= 0.52`. Version 0.52 stopped emitting
function parameter names, so 0.51 and older create large phantom diffs. The
guard checks the installed version before reading any baseline and contains
both a planted-old-version detection proof and a supported-version control.

Regenerate one affected baseline with exactly:

```bash
cargo +nightly public-api -s --omit auto-derived-impls -p <crate> > crates/<crate>/public-api.txt
```

Never enable `cranelisp-types`'s `test-support` feature for this operation.
Install the required tools with `rustup toolchain install nightly` and
`cargo +nightly install cargo-public-api`. The public-surface change, its
baseline, source rustdoc and bounded-context record land together under the
`dev` + `design` + `review` discipline in `design/arch/CLAUDE.md` §Baseline-diff
discipline.

## Defect-repro notation (`// defect:`)

Every **repro test** — a test born from a defect, committed per root
`CLAUDE.md` §"Usability Findings and Defects" — carries ONE greppable
`// defect:` line beside its `// spec:` comment:

```rust
// spec: repl/spec.md §4.1.2 — bare nullary-ctor lookup classification
// defect: class=wrong-scope-lookup locus=src/repl/format_type.rs::format_type_display found=S108 owner=/dev
#[test]
fn nullary_constructor_bare_lookup_shows_deftype_and_qualified_home() { ... }
```

The notation is the substrate for defect frequency, locus and recurrence
analysis. It rides the permanent corpus, so analysis works over **GREEN repros
too**: a fixed defect keeps contributing to the class-frequency and hotspot
signals.

**Fields** (the four below required; single line; no free text):

- `class=<class>` — the defect class, from the controlled vocabulary below.
  Free-text fragments defeat `uniq -c`; if no class fits, request a vocabulary
  addition from `qa` — adding a class is a `qa` edit to this list.
- `locus=<file:line-or-seam>` — where the bug lived: `file.rs:NNN` at fix
  time, or a stable seam name (`src/repl/format_type.rs::format_trait_display`,
  `host<->platform marshal boundary`). Prefer the seam form — line numbers rot.
- `found=S<NN>` — the sprint the defect was found in.
- `owner=/<role>` — the role that owned the **fix** (not the discoverer).

**Optional fifth field — `fixed=S<NN>/<sha>`.** Names the sprint and commit
that closed the defect. Present ⇒ the repro is a GREEN regression guard;
absent ⇒ still open, so `grep -L` over the corpus separates the two without
running anything.

The locus **never moves when a fix lands**. It records where the bug LIVED,
which is what the hotspot recipe below counts; rewriting it to the post-fix
seam would erase the history the notation exists to keep. When the fix deleted
the seam, keep the historical seam as the `locus=` token and say so in the
prose after it, naming what a reader should read today.
`grep -o "locus=[^ ]*"` stops at the first space, so prose after the token
never pollutes the frequency counts.

**Controlled `class=` vocabulary** (owned by `qa`):

| Class | Meaning (evidence) |
|---|---|
| `wrong-scope-lookup` | Lookup rooted at the wrong scope/module, e.g. `current_module_path()` instead of the symbol's resolved home (S108 D1/D2; FIXME 0558) |
| `display-envelope-mirror` | Two formatter paths for one display concept diverge (S108 D2 dual-path; the FIXME 0321 mis-qualify class) |
| `resolver-mirror` | Two resolution paths for one name-resolution concept diverge — the P7 divergent-duplication defect at a resolution seam, e.g. backend `lookup_constructor`'s one-hop copy vs `resolve_driven`'s multi-hop chain-follow producing the silent nullary-ctor-as-closure wrong value (S109 AN-2). The resolution-seam sibling of `display-envelope-mirror` (added S109, /qa) |
| `rc-miscount` | Refcount inc/dec imbalance — leak or premature free (S97 ADT-wrapping-Vec; S101 vec-COW copy-branch leak; S94 catch-runtime-error leak) |
| `uaf` | Use-after-free / dangling pointer (TCO tail-arg alias; S97–98 grid Vec double-free) |
| `marshal-overrun` | Byte-level over/under-write at the host↔platform marshalling boundary (S86 DEF-6 base-vs-payload pointer) |
| `mode-divergence` | REPL / `--run` / `--link` behaviour divergence — always a defect (S98 0499; S102 0484) |
| `prelude-scope-miss` | Prelude-provided symbol unreachable or mis-resolved via the implicit outer-scope fallback (S59 prelude-parity; FIXME 0558 sibling). Resolution-time mechanism — an enumeration/census error is `enumeration-miss`, not this |
| `enumeration-miss` | A reachable-set enumeration omits, double-counts, or otherwise mis-counts a symbol source — e.g. the bootstrap-seeded modules absent from the `/search` index (S108 E1), or a seeded-vs-file module-name collision double-counted into a permanently-wedged `pending_count` (S108 I-1). **Not restricted to symbol-table censuses** (ratified S121, /qa): a dataflow reach-set walk whose visited set is keyed on a NAME drops a member when a binder shadows one of the entities that set reaches, so the published claim is narrower than the truth — `ownership/transfer.rs::param_roots` answers one reaching parameter for `(let [a (if a b)] …)` and publishes `MayAliasOf(0)` where `MayAliasAny` is true. Class the MECHANISM here even when the downstream face would be `uaf`/`rc-miscount`, as `artifact-underkey` does |
| `silent-accept` | Invalid input accepted without error (S107 deftype trailing-form-after-field-bracket class) |
| `null-got-slot` | Call through an unpopulated/NULL GOT slot → SIGSEGV (S100–101 vec-query value-use family) |
| `routing-misclassify` | Input dispatched to the wrong destination arm by a classifier/router — e.g. NL prose containing a reader-macro char (`'` in `doesn't`) misrouted to eval as "code" (S108 E6); a single FQ symbol routed to the agent instead of introspection (S108 candidate B). Distinct from `mode-divergence` (same input, different behaviour PER MODE) — here one mode picks the wrong arm |
| `error-swallow` | A raised diagnostic is dropped or clobbered between its raise site and the display boundary — e.g. the multi-form REPL eval arm wrapping a per-form error as a fake `Val{0}` warning that a later warnings overwrite discards, surfacing silent `:Int 0` (S108 E7). Distinct from `silent-accept` (nothing was ever raised) |
| `check-gate-leak` | A source-level fault typecheck must decide (resolve or reject check-side) leaks past the check boundary and surfaces as a codegen/backend-layer error — e.g. the slot-less generic value-position FQ ref reaching `backend/literals.rs` as an opaque codegen error (S108, 0571 D1). Distinct from `silent-accept` (nothing raised anywhere) and `error-swallow` (raised then dropped): here the wrong LAYER raises (added S109, /qa) |
| `wrong-reject` | A spec-conforming program REJECTED — an over-strict gate or mis-scoped semantic model; the inverse of `silent-accept` (S109 W6.2 rigid-bare written vars rejecting §3.3 rows 2/4/11) (added S109, /qa) |
| `shared-state-write-race` | A background/concurrent actor writes substrate a foreground consumer reads — correctness resting on undo/cleanup discipline or scheduling luck instead of isolation-by-construction (S109 index-feed phantom-prelude write, FIXME 0604; the S61→S93 heisenbug lineage). Distinct from `mode-divergence` (deterministic per mode) — here one mode's outcome varies by interleaving (added S110, /qa) |
| `wrong-accept` | A spec-VIOLATING program ACCEPTED by the type judgment — typecheck passes where the spec demands rejection, often with memory-unsafe downstream consequence (S110 vec-instantiation unpinned-`(Vec a)` accept; S111 §5.1.2 multi-arity clause-param pinning vectors B-1/B-2 — String heap ptr read as Int). The judgment-level inverse of `wrong-reject`. Distinct from `silent-accept` (malformed INPUT accepted at the parse/definition boundary — no type judgment involved) (ratified S111, /qa) |
| `artifact-underkey` | A compiled artifact is cached, deduplicated or validated under a key that omits a determinant of its content, so a lookup serves an artifact built from different inputs. Instances: per-instantiation ADT drop glue and vec elem-dec functions keyed by bare `fqtn.name` without module and concrete arguments (S111 FIXME 0633/0640; faces `uaf`, `rc-miscount`); a module cache entry validated on its own source hash with an empty dependency-hash map, so an unchanged importer is restored against a changed dependency (S122 CD-1; faces: an ill-typed program runs, a call dispatches through a reassigned GOT slot). Class the MECHANISM here, not the face. Distinct from `binder-name-underkey` (compiler facts about a lexical binder, not an emitted or persisted artifact). Named `drop-glue-underkey` S111–S122; comments outside `tests/` may still use that name (generalized S122, /qa) |
| `binder-name-underkey` | A **lexical binder's** compiler-side facts (its `Variable`, type, release obligation, borrowed mark, spark record) are keyed by the binder's NAME, so two binders that share a name are one entry: the later overwrites the earlier, a scope pop removes rather than restores, and an insert-only name set never clears. Symptom faces span `uaf`, `rc-miscount` (displaced/outer value never released) and plain wrong VALUE (a lenient dependent forced against the displaced binder's IVar); class the MECHANISM here, as `artifact-underkey` does. Distinct from `artifact-underkey` (an emitted or persisted ARTIFACT keyed under-determined) and from `wrong-scope-lookup` (lookup rooted at the wrong scope — here the scope is right and the key cannot tell two binders apart). Evidence: six S121 REDs across `tests/same_form_rebinding.rs` and `tests/shadowed_param_reach_stale_rc_dec.rs`, resolved by per-binder scope slots plus exact-slot tail transfer (`design/backend/binding-scope.md`; ratified S121, /qa); supersedes the provisional `enumeration-miss` / `wrong-scope-lookup` / `rc-miscount` tokens on the five original cells. |
| `carrier-loss` | A keyed producer→consumer carrier (the S110 0583 architecture: typecheck-published, backend keyed-read, e.g. `resolved_target`) is NEVER WRITTEN for a reachable consumer site, so the loud keyed-consumer miss surfaces as a backend/codegen error on a spec-VALID program (S112 R2: multi-sig-base dispatch call inside a monomorphised instance body — the minted body's call sites get no carrier derivation). Distinct from `check-gate-leak` (INVALID program raised at the wrong layer — here nothing should be rejected at all) and from the forbidden soft-fallback (the loud miss is the consumer working as designed; the PRODUCER is the owner). Fix shape is P26-constrained: derive from settled state at the site that mints the reaching context, never patch-after-record (added S112, /qa) |
| `scalar-as-pointer` | A scalar-typed value RC-manipulated or dereferenced as a heap pointer because its category is unknown at emission — e.g. a generic trait-method instance's residual-`Var` slot RC-inc'd behind the nullary-tag guard, so an `Int` payload with value ≥ `NULLARY_TAG_THRESHOLD` takes a wild atomic write at payload+8 (S118, FIXME 0916; boundary measured exactly 1023/1024). The nullary-tag guard discriminates tags from pointers, never scalars from pointers. Distinct from `rc-miscount` (counts on real heap values) and `uaf` (a real pointer, wrong lifetime): here the operand was never a pointer at all (added S118, /qa) |
| `release-path-bypass` | Retained session state whose release the spec ties to one named condition is discarded by an unrelated lifecycle action — e.g. `/reset` clearing `failed_forms`, so the next regeneration silently dropped unrepaired startup-failed source that §15.2.3 releases only on a successful same-name definition or reload (S122, `tests/repl_persist.rs` reset cell; the S102 W5R M-1 coupling invariant was kept by clearing both carriers instead of retaining both). Class the release SITE, not the symptom face (authored-source loss). Distinct from `error-swallow` (a raised diagnostic dropped in flight) and `enumeration-miss` (the carrier is enumerated correctly — it was emptied). A sibling face is an error-set membership lifted by a command the §14.4–§14.6 repair exit does not name (added S122, /qa) |
| `requirement-conflict` | Two requirement texts prescribed conflicting behaviour; the implementation and its covering test followed the one the user's later ruling rejected, so both encoded the wrong behaviour. Example: `spec/10-io.md` §10.6.2 said the REPL shows only an executed `IO` result's inner value, while `repl/spec/01-display-format.md` §1.2 requires `:(primitives/IO InnerType) (IO.Pure inner_value)`. The user ruled on 2026-09-25 that §1.2 governs (S122, `tests/spec_10_io.rs` IO display cells). Class the conflict that admitted the defect, not the source site that realizes it. Distinct from `wrong-accept` and `wrong-reject`, where the implementation departs from one requirement that does not conflict with another (added S122, /qa) |

**Rules:**

- ONLY defect-repro tests carry `// defect:`. Ordinary spec-coverage tests do
  not — the signal is defect density, and tagging everything erases it.
- The notation is applied by `test` at repro time (and retro-tagged
  opportunistically); the vocabulary is `qa`'s.
- A repro's comment states its defect in the PAST tense once fixed. A GREEN
  repro carrying present-tense "DEFECT (open)" framing lets a future
  regression pose as a known guard — strip the framing when the fix lands.

**Analysis recipes** (the point of the structure):

```bash
# recurring-class frequency — the arch-escalation signal (a class that
# keeps recurring is an architecture problem, not an instance problem)
grep -rh "// defect:" tests/ | grep -o "class=[a-z-]*" | sort | uniq -c | sort -rn

# hotspot seams
grep -rh "// defect:" tests/ | grep -o "locus=[^ ]*" | sort | uniq -c | sort -rn

# per-sprint defect trend
grep -rh "// defect:" tests/ | grep -o "found=S[0-9]*" | sort | uniq -c
```

## Failing-test discipline (migrated from the retired ledger)

Regression triage runs on the inline convention (root `CLAUDE.md` §Testing):
every intentional RED — a failing-not-ignored defect guard — traces to an
open defect (FIXME or annotation) naming the owner; a RED that does not so
trace is a **genuine regression**. `#[ignore]` on a spec violation hides the
fact and is itself a defect.

**Forbidden dispositions** — these words close investigation prematurely and
forfeit the regression guard; they are banned in test comments, FIXMEs,
triage notes, and reports:

- `flaky` — never. Local tests are deterministic; if a test fails
  intermittently, the cause is a real race, ordering bug, or uninitialised
  state. Per user directive 2026-04-21: *"we need to be really clear about
  'flaky' — that is not a thing in local tests."*
- `timing-sensitive` — equivalent to flaky. Tests that assume a particular
  scheduling order are either testing something real (name it and pin it) or
  they are incorrectly written (fix them).
- `documented race` — the race is the bug. Fix it.
- `pre-existing` — not a disposition; it relies on commit-SHA amnesia. A
  failure either traces to an open defect with a named owner and a target
  sprint, or it is a regression to fix now.

## Isolating Cross-Crate Failures

When an e2e test fails and the root cause could be in any crate (typecheck?
backend? integration wiring?), isolate before fixing. Do NOT guess-and-patch —
that creates workarounds that mask the real problem.

**Step 1 — Minimal e2e repro.** Write the smallest test that reproduces the
failure. Strip everything: `PreludeVariant::None`, no stdlib, no imports unless
required. It should fail with the same error as the original.

```rust
#[test]
fn defmacro_rest_splice() {
    Cranelisp::repl_capture(
        "(defmacro my-begin ([] 0) ([x &rest] `(begin ~x ~@rest)))\n\
         (my-begin 42)\n",
    )
    .assert_stdout_contains("42");
}
```

**Step 2 — Inspect compiler state at the failure point.** The error names a
symbol (e.g. "undefined function: macros/sconcat"). Use REPL introspection
inside a capture (`/info`, `/sig`, `/list`, `/sexp`, `/clif`, `/ast`) combined
with the trace env vars to determine whether the data is **missing** (never
created), **incomplete** (created but missing a field like `got_slot`), or
**present but not reached** (in the symbol table but the code path doesn't look
it up). Small repros produce small CLIF that can be read by eye.

**Step 3 — Unit test in the owning crate.** Write a `#[cfg(test)]` test in the
crate that should produce the correct output. Build the AST from source with
`cranelisp_frontend::parse` + `build_program` (via `[dev-dependencies]`) — do
not hand-construct `Expr` trees.

**Step 4 — Interpret.** Unit passes but e2e fails → bug is in integration wiring
(`src/worker.rs`, `src/pipeline.rs`, `src/session_v4.rs`). Unit fails → bug is
in the crate; fix there. Unit can't be written → add the crate's test
infrastructure first.

**Step 5 — Fix at the right level.** Don't patch integration to work around a
crate bug, or patch a crate to compensate for integration wiring. Each crate's
output must be correct independently.

## Coverage

Code coverage is measured with `cargo-llvm-cov` (LLVM source-based
instrumentation; `rustup component add llvm-tools-preview` + `cargo install
cargo-llvm-cov`).

```bash
cargo llvm-cov --html --output-dir coverage/all     # combined, root crate
cargo llvm-cov --lib --html --output-dir coverage/unit
cargo llvm-cov --test spec_04_expressions --html --output-dir coverage/one
cargo llvm-cov report                               # text summary
```

Name real `--test` targets (see `ls tests/*.rs`); there are no `ringN` binaries.
No standing per-crate gap register is kept; measure when a question needs it.

**Known limitation — JIT code not covered:** Cranelisp compiles user code via
Cranelift JIT at runtime; LLVM instrumentation covers only the Rust compiler
code, not the generated machine code. Coverage numbers reflect how much of the
*compiler* is exercised, not how much of the *language surface* is tested. E2E
subprocess coverage likewise reflects only harness code unless the subprocess is
built with `LLVM_PROFILE_FILE` set. `coverage/` is gitignored.

## Build & run

Always use `cargo nextest run --no-fail-fast` (never `cargo test`; alias
`cargo nt`). Root `CLAUDE.md` §Testing owns the suite's time budget and the
background/one-agent run rules.

```bash
cargo nextest run --no-fail-fast                       # full suite
cargo nextest run --test spec_04_expressions           # one binary
cargo nextest run --test cache cache_multi_module_transitive_imports  # one test
CRANELISP_RC_TRACE=1 cargo nextest run --test spec_12_runtime         # with a trace
```

## Adding a test

1. **Choose the file** by spec section (`spec_NN_*.rs`) or concern
   (`repl_*.rs`, `cache.rs`, `regression.rs`, a defect-named repro file).
2. **Use the harness** — `Cranelisp::new()` (or a `repl_capture` shortcut).
3. **Pick a prelude variant** — `None` for core-language tests,
   `PrimitivesOnly` or `TestStandard` when operators/ADTs are needed.
4. **Name after the behaviour** validated.
5. **Run through all modes** if it asserts language semantics.
6. **Add `// spec:`** on every `#[test]`; ask `qa` to update active allocation
   or [current coverage navigation](plan/PLAN.md#current-coverage-navigation)
   when the new evidence is not already discoverable there.

## Unit-test-per-fix discipline

Every fix lands with a unit test, and the e2e need is assessed
**before** the fix is written; failing test(s) first, fix flips them green, both
in the same change-set. This is stated canonically in root `CLAUDE.md`
§Testing and `sprints/METHOD.md` §2.2 — follow those; not restated here.

## QA-first targeting and deferral discipline

A correctness defect first caught by `review` is a QA-first and unit-test
miss: review is the last line of defence, tests the first.

- **Author guards for spec MUSTs and `arch`-flagged boundaries first** —
  before the happy path. A design outcome that says "watch this
  collision/accounting/gate" is a test row, not a footnote.
- **A deferral to unit tests enumerates its cases**, per QA's
  [traceability and authoring policy](plan/PLAN.md#traceability-and-authoring):
  the specific boundaries, negatives and spec MUSTs `dev` must pin, each with
  a guard that fails on revert of its fix. A bare "unit-pinned" is a hole.
