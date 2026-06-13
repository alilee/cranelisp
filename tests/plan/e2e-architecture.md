# E2E Test Architecture — `--link` / platform reliability

Owner: `/qa`. Authored Sprint 80 Wave 3a (2026-06-13) per user directive:
*"fix it, but don't just hack a fix — think about how we should be
organising these end-to-end tests to properly address the quality risk,
and make the tests reliable and easy to maintain."*

This document is the design + phased implementation plan for making the
`--link` / platform e2e tests reliable under a vanilla `cargo nextest run`.
It is subordinate to `PLAN.md` (the spec→tests bridge) and complements
`helpers.md` / `helpers-api.md` (the harness API).

---

## 1. Root cause — diagnosed precisely

### 1.1 The observed symptom

`--link` and platform e2e tests fail under a plain `cargo nextest run` on
this Linux VM with:

```
error: codegen error at 0..0: could not find libcranelisp_exe_bundle.a
  — build it with `cargo build -p cranelisp-exe-bundle` or set CRANELISP_BUNDLE_PATH
```

or, for platform-using programs, `platform 'stdio' not found`. They pass
under the manual protocol "one `cargo build --workspace`, then a scoped
`-E` run with no intervening rebuild."

### 1.2 The actual mechanism (corrected from the Wave-3a hypothesis)

The Wave-3a task framing hypothesised a **profile desync** — nextest
rebuilding platform cdylibs in the *test* profile while `exe-bundle` stays
*dev*. That is **not** the active failure. The real mechanism is simpler
and was confirmed empirically (move-artifacts-aside reproduction, below):

**Plain `cargo nextest run` never builds the `--link` prerequisite crates
at all.**

The `cranelisp` binary's `--link` path links five workspace members:

| Crate | Artifact resolved at runtime | Resolver |
|---|---|---|
| `cranelisp-exe-bundle` (`staticlib`) | `target/debug/libcranelisp_exe_bundle.a` | `src/exe.rs::find_bundle_lib` |
| `cranelisp-stdio` (`cdylib`+`rlib`) | `target/debug/libcranelisp_stdio.{rlib,so}` | `find_platform_rlibs` / `platform::resolve_platform_path` |
| `cranelisp-test-capture` | `target/debug/libcranelisp_test_capture.{rlib,so}` | same |
| `cranelisp-shapes` (ADT fixture) | `target/debug/libcranelisp_shapes.{rlib,so}` | same |
| `cranelisp-shapes-badabi` | `target/debug/libcranelisp_shapes_badabi.{rlib,so}` | same |

The binary resolves these **at runtime by scanning `target/debug/`** — there
is **no Cargo dependency edge** from the `cranelisp` binary (or any test
target) to any of them. Verified:

```
$ grep -rn "cranelisp-exe-bundle\|cranelisp-stdio\|cranelisp-test-capture" --include=Cargo.toml .
# → only the crates' own [package] name lines. No dependency edges.
```

`cargo nextest run` builds **test targets + their transitive dependencies**.
These five crates are leaf workspace members with no test targets and no
inbound dependency edges, so nextest never compiles them. On a clean tree
`target/debug/libcranelisp_exe_bundle.a` simply does not exist → the
`--link` path fails immediately.

The manual protocol works only because `cargo build --workspace` *does*
build every member (workspace members are always built by `--workspace`),
populating `target/debug/` as a side effect that the later scoped nextest
run reuses.

### 1.3 Empirical confirmation

Reproduced on unmodified HEAD (`4109c3e`) without editing any source:

1. `cargo nextest list` — does **not** rebuild the artifacts (timestamps
   unchanged) and does not error. It does not touch the prereq crates.
2. Move the 5 artifacts aside (`mv libcranelisp_exe_bundle.a → .s80hidden`,
   etc.) to simulate a clean tree, then `cargo nextest run --test link`:
   **5 of 14 link tests fail** with `could not find
   libcranelisp_exe_bundle.a`. The 9 that pass are error-path /
   negative-path tests that never reach the bundle link step.
3. Restore the artifacts (or run `cargo build -p` on the five) → **14/14
   pass**. No source change, no profile change — only artifact presence.

This pins the root cause to **artifact absence under nextest's
build-what-the-tests-depend-on model**, not to a profile mismatch.

### 1.4 The secondary (latent) concern: snapshot skew

There is a *real but distinct* skew hazard, recorded as the Wave-2D "D2
build-skew caveat" and the Wave-2E "D4" Linux `--link` finding in
`sprints/SPRINT.md`:

> verify only after `cargo build --workspace` (one invocation) — piecemeal
> `cargo build -p` skews platform rlib vs exe-bundle snapshots → spurious
> `--link` failures.

The hazard arises when the platform rlibs and the exe-bundle are built by
**separate sequential `cargo build -p` invocations against different
intermediate source states** of the shared `cranelisp-primitives` /
`cranelisp-platform` crates — e.g. an interactive session that rebuilds
one crate, edits a shared dep, then rebuilds another. Each invocation
re-resolves the graph independently, so the two artifacts can capture
different monomorphisation snapshots of the shared crates, and the
whole-archive `-force_load` / `--whole-archive` link then references a
symbol the bundle compiled differently.

The fix for the absence problem (below) also closes this: building **all
five prerequisites in a single `cargo build` invocation** resolves the
dependency graph once, so all five capture one consistent snapshot of the
shared crates. The remaining residue is the D4 Linux `--link`
`-force_load` driver bug (a real link-subsystem defect handled by the
Wave-2E `LinkRequest`/`Linker` refactor), which is orthogonal to the
test-infra artifact-provisioning problem this document solves.

---

## 2. Reliability — deterministic, profile-consistent artifacts

### 2.1 Options evaluated

| Option | Mechanism | Verdict |
|---|---|---|
| **A. nextest setup script** | `.config/nextest.toml` `[scripts.setup.*]` runs `cargo build -p <5 prereqs>` once before any test in the profile. | **RECOMMENDED.** |
| B. `build.rs` on the binary crate | Add a `build.rs` that shells out to `cargo build -p` for the prereqs. | Rejected — recursive cargo-in-build-script is fragile, runs on every `cargo build` (not just tests), and risks build-graph cycles. |
| C. once-cell in-harness build | Keep / generalise `ensure_platform_cdylibs_built()` — a `std::sync::Once` per test binary. | Rejected as the primary mechanism — duplicated per binary, races across nextest's parallel binaries (each test binary is a separate process, so `Once` does not coordinate across them), and couples build policy into test code. |
| D. add Cargo dependency edges | Make a test target `[dev-dependencies]` the prereq crates so nextest builds them. | Rejected — a `staticlib`/`cdylib` is not consumable as a normal Rust dep; an rlib could be pulled in but pollutes the link graph and does not produce the `.a`/`.so` the runtime scanner needs at the expected path. |
| E. pin profiles | Force test-profile == link-path profile. | Not applicable — there is no profile mismatch (§1.2); the artifacts are simply absent. |

### 2.2 Recommended mechanism — nextest setup script

`cargo-nextest` (>= 0.9.59; the repo ships 0.9.137) supports **setup
scripts**: a command that runs once, before the test phase, gated by a
profile + filter. This is the canonical nextest answer to "the tests need
a build artifact that the Cargo graph does not produce."

Prototyped + validated this wave:

**`.config/nextest.toml`**
```toml
experimental = ["setup-scripts"]   # setup scripts are still gated behind opt-in

[scripts.setup.link-prereqs]
command = 'bash tests/scripts/build-link-prereqs.sh'

[[profile.default.scripts]]
filter = 'all()'
setup = 'link-prereqs'
```

**`tests/scripts/build-link-prereqs.sh`**
```bash
set -euo pipefail
cargo build \
  -p cranelisp-exe-bundle \
  -p cranelisp-stdio \
  -p cranelisp-test-capture \
  -p cranelisp-shapes \
  -p cranelisp-shapes-badabi
```

Properties:

- **Single invocation → consistent snapshot.** All five prerequisites
  resolve the shared-crate graph once, closing the §1.4 skew hazard.
- **Right profile, right directory.** A bare `cargo build` is the dev
  profile → `target/debug/`, exactly what the `--link` runtime path scans.
- **Runs once per `nextest run`, not per binary.** Validated: a run across
  `examples` + `platform_errors` (2 binaries) emitted one `SETUP PASS
  link-prereqs`, then both binaries' tests.
- **Cheap when current.** `cargo` no-ops in ~0.02s when artifacts are
  fresh; the setup line costs ~0.03s of overhead.
- **No manual protocol.** A clean `git clone` + `cargo nextest run` now
  builds the prereqs before the tests, with no `cargo build --workspace`
  pre-step.

### 2.3 Prototype validation result (this wave)

From a simulated clean tree (5 artifacts moved aside):

- `cargo nextest run --test link` → `SETUP PASS link-prereqs`, then **14/14
  link tests pass** (was 5 failed without the script).
- `cargo nextest run --test examples --test platform_errors` → one setup
  run shared across both binaries, **7/7 pass** including
  `platform_dll_resolves_on_current_platform` and the `examples` 8th-red
  `every_example_runs_with_documented_exit` — both of which were red purely
  because the current-platform DLLs were not built.

The prototype change (`.config/nextest.toml` +
`tests/scripts/build-link-prereqs.sh`) is committed as part of this design
pass because it is small, self-contained, and demonstrably fixes the
reliability problem without touching `src/`.

### 2.4 `/arch` vs `/qa` ownership of the config

`.config/nextest.toml` and `tests/scripts/` are **test-infra** owned by
`/qa` — they change no crate's public surface, no `cranelisp-types` type,
and no build output consumed by the shipped binary. The setup script
merely pre-builds existing workspace members. **No `/arch` sign-off is
required** for the config or the script.

One adjacent item *is* `/arch`/`/dev`-owned and is explicitly **out of
scope** for this `/qa` change: the D4 Linux `--link` `-force_load` driver
bug (Wave-2E `LinkRequest`/`Linker` refactor). That is a real
link-subsystem defect in `src/exe.rs`; the setup script makes the
artifacts present but cannot fix a broken linker driver. The two are
independent and both must land for a fully-green Linux `--link` suite.

---

## 3. Organization — isolate e2e from fast tests

### 3.1 The two cost classes

| Class | Examples | Cost | Build prerequisite |
|---|---|---|---|
| **Fast** | `/clif`, `/sig`, REPL introspection, parse errors, typecheck conformance — anything driven by `repl_capture` or `--run` without linking | sub-second; binary only | binary only (built as a test dep) |
| **Slow e2e** | `--link` round-trips, platform `dlopen`, `link_then_run`, `run_through_all_modes` (which includes the two link permutations) | hundreds of ms to seconds each; spawns a linker | binary + the five prereq artifacts |

### 3.2 Grouping design — nextest `test-group` + a naming/filter convention

The setup script in §2 already makes the slow class *correct* regardless
of grouping. Grouping is then an optimisation + a concurrency-control
lever, not a correctness requirement. Design:

1. **Keep the spec-section-anchored file layout** (`PLAN.md §"Sprint 64
   reorganisation strategy"`). Do NOT re-shard tests into a separate
   `tests/e2e_link/` tree — that would fragment the spec-coverage read the
   project deliberately chose. The slow `--link` tests live in the same
   spec-section files as their fast siblings (`spec_10_io.rs` has both
   `repl_capture` IO tests and `--link` IO round-trips).

2. **Add a nextest `[test-groups]` + `[[profile.*.overrides]]` entry** to
   serialise the linker-spawning tests if linker contention becomes a
   runtime problem. The `--link` tests spawn an external linker
   (`cc`/`ld`); under high parallelism these can contend on the same
   `target/debug/` object outputs and on system linker resources. A
   `test-group` with bounded `max-threads` is the nextest-native answer:

   ```toml
   [test-groups.link-e2e]
   max-threads = 4   # cap concurrent linker spawns

   [[profile.default.overrides]]
   filter = 'test(/^link_/) or test(/link_then_run/) or binary(link)'
   test-group = 'link-e2e'
   ```

   This is a **tuning lever held in reserve** — the current Linux suite
   runs clean in ~39s with full parallelism (per the SPRINT.md Linux
   refresh), so the group is not needed for correctness today. Document it
   here so the lever is known when/if linker contention regresses runtime.

3. **A `slow` profile for the full e2e gate.** Define a
   `[profile.e2e]` that runs the whole suite (the release gate). The
   `default` profile already carries the setup script, so `cargo nextest
   run` is correct out of the box; `--profile e2e` is reserved for a future
   CI split (fast-feedback profile that skips the linker round-trips vs.
   full-gate profile). Not required this sprint; noted as the extension
   point.

### 3.3 Fast/slow coexistence — no segregation needed

Because the setup script is cheap-when-current and runs once, fast tests
pay only the ~0.03s setup overhead per `nextest run`, not per test. There
is **no need to physically segregate** fast and slow tests into separate
binaries or trees. The cost the user worried about ("keep the fast suite
quick") is already met: a `cargo nextest run --test repl_introspection`
pays one no-op setup line and runs the fast tests unchanged.

---

## 4. Maintainability — kill setup duplication

### 4.1 The duplication today

Two hand-rolled `ensure_platform_cdylibs_built()` copies — one in
`tests/examples.rs:68`, one in `tests/platform_errors.rs:43` — each a
`std::sync::Once` shelling `cargo build -p cranelisp-stdio -p
cranelisp-test-capture`. Plus `tests/examples.rs` and the e2e harness each
independently set `CRANELISP_PLATFORM_PATH=target/debug`. The `justfile
run-example` recipe carries a third copy of the same `cargo build -p`
line. Three sources of the same truth, drifting independently (the
`justfile` copy omits `shapes`/`shapes-badabi`; the `Once` copies omit the
exe-bundle entirely).

### 4.2 The consolidation

The setup script is the **single owner** of the build-prerequisite
lifecycle. Once it lands:

- **Delete** `ensure_platform_cdylibs_built()` from `tests/examples.rs`
  and `tests/platform_errors.rs` and their call sites. The artifacts are
  guaranteed present by the setup script before any test runs. (Keep the
  `CRANELISP_PLATFORM_PATH` env wiring — that is per-test runtime
  configuration, not a build step, and legitimately lives in the harness /
  test.)
- The `justfile run-example` recipe can call the same
  `tests/scripts/build-link-prereqs.sh` (or stay as-is for the
  interactive `cargo run` path — it is not a test path and is out of the
  reliability contract).

### 4.3 Declarative `--link` tests via the shared harness

The e2e harness (`tests/helpers/e2e.rs`) already owns the
build+link+capture lifecycle behind the `Cranelisp` builder
(`.link()`, `.link_then_run()`, `run_through_all_modes`,
`run_through_all_modes_output`). With the artifact-consistency guarantee
moved to the setup script, the builder no longer needs to carry any
build-prerequisite logic — it is purely "spawn the binary against a
guaranteed-present artifact set." Individual `--link` tests are already
declarative (program + expected output/exit); the only change is that they
no longer depend on a per-binary `Once` having fired.

**Design rule (record in `tests/CLAUDE.md`):** a `--link` / platform e2e
test MUST NOT shell out to `cargo build`. The artifact set is a
suite-level invariant owned by the nextest setup script. A test that needs
an artifact not in the prereq set extends
`tests/scripts/build-link-prereqs.sh`, it does not add a per-test build.

---

## 5. Quality-coverage contract

The `--link` / platform / output-equivalence e2e tests are the **release
gate** (`qa.md §"Working build requirement"`). They MUST cover:

### 5.1 Mode-output equivalence (spec/10-io.md §10.6.3)

A program's observable `print` output MUST be byte-for-byte identical
across `--run` (JIT), a `--link`-produced standalone binary, and the REPL.
Covered by `run_through_all_modes_output` (`tests/helpers/e2e.rs`) +
`tests/output_equivalence.rs`. The harness runs all six mode×cache
permutations (repl/run/link × fresh/cached) and asserts byte-equality.

**Gap (named, owned elsewhere):** on Linux the `--link` permutations are
blocked by the D4 `-force_load` driver bug (Wave-2E). Until that lands, the
link permutations of the output-equivalence corpus ride red. This is a
**compiler defect, not a test-infra gap** — the setup script makes the
artifacts present; the linker driver still rejects `-force_load`. Tracked
in `ledger.md` under the Wave-2E entry.

### 5.2 Platform load + ABI/layout-hash gate (spec/10-io.md §10.10, §8.9.3)

- Platform `dlopen` + dispatch across the DLL boundary (`--run`):
  `platform_errors.rs::platform_fn_dispatches_across_dll_boundary`.
- ABI-version mismatch refusal: `platform_abi_version_mismatch_e2e` (the
  `shapes-badabi` DLL, ABI=2 vs host=3).
- Layout-hash drift dual gate — `--run`/`--link` REFUSE, REPL
  warns-and-loads: the `spec_platforms_adt.rs` hash-gate trio.
- ADT-typed platform round-trip across `--run`/`--link`/cache-restore:
  the `spec_platforms_adt.rs::platform_adt_roundtrip_*` trio.

### 5.3 `--link` standalone correctness (spec/12-runtime.md §12.6)

- Produced binary exits with `main`'s value: `link.rs::link_hello_*`,
  `link_main_returning_zero_exits_zero`.
- Multi-module cross-call in a linked binary:
  `link_multi_module_project_with_cross_module_call_exits_with_main_value`.
- Cache-restore re-emits the exe: `link_second_invocation_reuses_cached_*`.
- Bundle-missing error names the bundle (negative):
  `link_error_when_bundle_library_missing_names_it`.

### 5.4 Coverage gaps the scattered tests miss (the quality risk)

The user's "quality risk" is that the `--link` surface was **never
reliably exercised by CI** — every green claim depended on an
out-of-band manual build. With the setup script, the gate becomes
real. Two concrete coverage gaps surface once the gate is reliable:

1. **No clean-tree CI assertion.** There is no test that asserts "from a
   clean `target/`, `cargo nextest run` greens the `--link` suite." The
   setup script makes this true; a build-confidence smoke entry should
   assert the binary + a minimal `--link` round-trip work without any
   pre-build. **Add** `build_confidence.rs::link_smoke_runs_from_clean_tree`
   (a minimal `(defn main [] (pure 0))` `--link` → exit 0) as the gate's
   canary that the prereq mechanism fired.
2. **No negative coverage that the prereq set is complete.** If a future
   platform fixture is added without an entry in
   `build-link-prereqs.sh`, the failure mode is a confusing `platform 'X'
   not found` deep in a test. **Add** a doc-comment contract in the script
   + a `tests/CLAUDE.md` rule (§4.3) so new fixtures extend the script.

These two are the durable closure of the quality risk: the gate is real,
and the prereq set has a named owner + extension protocol.

---

## 6. Phased implementation plan

### Phase S80-now (lands this sprint — makes the convergence green-up reliable)

1. **[DONE this wave — prototype validated]** `.config/nextest.toml` with
   the `link-prereqs` setup script + `tests/scripts/build-link-prereqs.sh`.
   Validated: clean-tree `cargo nextest run --test link` → 14/14;
   `examples`+`platform_errors` → 7/7 (one shared setup run).
2. **Delete the band-aids.** Remove `ensure_platform_cdylibs_built()` +
   call sites from `tests/examples.rs` and `tests/platform_errors.rs`
   (keep the `CRANELISP_PLATFORM_PATH` env wiring). `/qa`-only, `tests/`.
3. **Add the clean-tree canary.**
   `build_confidence.rs::link_smoke_runs_from_clean_tree`. `/qa`-only.
4. **Record the contract.** Add to `tests/CLAUDE.md`: the setup-script
   mechanism, the "no `cargo build` in a test" rule, and the "new platform
   fixture → extend `build-link-prereqs.sh`" protocol. `/qa`-only.
5. **Ledger.** Note in `ledger.md` that the `--link`/platform reds were an
   artifact-provisioning gap (not a profile desync), now closed by the
   setup script; the residual Linux `--link` reds are the D4 driver bug
   (Wave-2E), owner `/dev` (`src/exe.rs`).

### Phase follow-up (next sprint — optimisation + CI split, not required for green)

6. **`test-group` link concurrency cap** (§3.2.2) — add only if linker
   contention regresses runtime. Held in reserve.
7. **`[profile.e2e]` fast/full split** (§3.2.3) — a fast-feedback profile
   that skips link round-trips for inner-loop runs, plus the full gate
   profile. CI-shape decision; coordinate with `/sprint`.
8. **CI integration of the setup script** — wire `cargo nextest run` (which
   now carries the setup script) into CI as the actual gate, replacing any
   implicit `cargo build --workspace` pre-step. Coordinate with whoever
   owns CI config.

### What needs `/arch` / `/dev` (NOT `/qa`)

- **D4 Linux `--link` `-force_load` driver bug** — `src/exe.rs`
  link-driver dispatch routes platform-rlib linking through the Apple
  `-force_load` path on Linux. `/arch` (LinkRequest/Linker refactor,
  Wave-2E) + `/dev` int. The setup script does not and cannot fix this;
  it is the residual blocker for green Linux `--link` output-equivalence.
- **`PLATFORM_EXT` / current-platform DLL discovery** — already resolved
  (`cfg`-conditional per the Linux porting arc); the setup script now also
  builds the current-platform `.so`/`.rlib` so the `examples` discovery
  path is satisfied. No further `/dev` work for the artifact side.

### Cost honesty

The **reliability fix is small** — two new files (config + script),
already prototyped and green. The band-aid deletion + canary + doc are
~an hour of `/qa` work. The genuinely large item (D4 link-driver
encapsulation) is **already separately scoped** as Wave-2E and is not part
of this test-infra change. So: the principled design is *not* a large
migration; the test-infra surface converges this sprint, and the one large
adjacent item is owned elsewhere and already planned.

---

## 7. Summary

| Question | Answer |
|---|---|
| Root cause | Plain `cargo nextest run` never builds the 5 `--link` prereq crates (no Cargo dep edge; leaf workspace members); the runtime `target/debug/` scan then fails. NOT a profile desync. |
| Mechanism | nextest setup script: one `cargo build -p <5>` before the suite. Single invocation → consistent snapshot (also closes the §1.4 skew hazard). |
| Needs nextest config? | Yes — `.config/nextest.toml` (`experimental = ["setup-scripts"]`). `/qa`-owned test-infra; no `/arch` sign-off. |
| E2E isolation | Keep spec-section file layout; setup script makes the slow class correct; `test-group` concurrency cap held in reserve. |
| Shared harness | `Cranelisp` builder already owns build+link+capture; setup script removes the per-binary `Once` band-aids; tests stay declarative. |
| Coverage contract | §10.6.3 mode-output equivalence, §10.10 platform load + ABI/hash gate, §12.6 `--link` standalone; gaps = no clean-tree canary (add), residual D4 link-driver red (Wave-2E, `/dev`). |
| Prototype made? | Yes — config + script committed, validated clean-tree 14/14 link + 7/7 examples/platform. |

## 8. Test-output pruning discipline (FIXME 0326, S81)

The "clean & green" standard requires the working tree to stay flat
run-over-run: repeated `cargo nextest run` invocations MUST NOT accumulate
artifacts on disk. FIXME 0326 (filed S81) flagged the risk. The audit and
the chosen discipline:

### 8.1 Where output lands — audit result

The active e2e harness (`tests/helpers/e2e.rs`, the `Cranelisp` builder) is
the only test-side mechanism that writes to disk, and it is **already
RAII-clean by construction**:

- **Per-test scratch is a `tempfile::TempDir`.** `Cranelisp::new()` allocates
  a fresh `tempfile::tempdir()` (system `$TMPDIR`, not the source tree). The
  handle is carried through `CrInvocationOwned` into the resulting
  `CrOutput._td: Option<TempDir>`, and the `TempDir` `Drop` impl recursively
  removes the directory when the test's `CrOutput` goes out of scope —
  including on the failure/panic path (a panicking test still unwinds and
  drops `CrOutput`).
- **Everything the child writes lands inside that tmpdir.** The child's cwd
  is the tmpdir (`cmd.current_dir(&self.cwd)`); the module cache
  (`.cranelisp-cache/`) resolves relative to cwd; the `--link` produced
  executable and its intermediate `.o` files are emitted at
  `self.tmpdir.path().join(stem)`. All of it is reclaimed with the TempDir.
- **Empirical confirmation.** A full `cargo nextest run` (1231 tests) with a
  `/tmp/.tmp*` count snapshot before and after shows **0 → 0** leaked temp
  dirs. No accumulation in the source tree, no accumulation in `$TMPDIR`.

The historical accumulation vector — the persistent
`tests/{suite}/.runs/{RUN_TS}/` trees (one timestamped subdir per run, never
pruned) — belonged to the **quarantined legacy suites** (Sprint 23, v4_*,
sprint59/60, examples_run, wave6). Those files are NOT compiled
(`tests/legacy/`), and no active test or the harness references `.runs/` or
`RUN_TS` any longer. The matching `.gitignore` entries are stale (they guard
trees the active suite never creates) but harmless.

The remaining on-disk footprint is the **five `--link` prereq artifacts** in
`target/debug/` built by the nextest setup script (§2.2). These are
**bounded, not accumulating**: the setup script rebuilds them in place (one
`cargo build -p` snapshot), it does not append. They are reclaimed by the
normal `cargo clean` / `rm -rf target` that already governs all build output.

### 8.2 Discipline (the smallest mechanism that holds)

Because the harness is already RAII-clean and the only persistent footprint
is bounded `target/` build output, **no new pruning mechanism is required** —
the discipline is to PRESERVE the existing one:

1. **Per-test scratch MUST be a `tempfile::TempDir` carried in `CrOutput`.**
   Never use the source-tree `.runs/{RUN_TS}/` pattern in a new active test —
   that pattern accumulates and is reserved for the frozen legacy archive. A
   test that needs a project on disk uses `Cranelisp::new()` +
   `with_project(...)` / `file(...)`, which writes under the auto-cleaned
   tmpdir.
2. **No test may write outside its tmpdir.** Reaffirms `tests/CLAUDE.md
   §"Fresh Temp Directory per Test"`. Writes to `project_root()`,
   `exemplar/`, `examples/`, `stdlib/`, `tests/fixtures/`, or a bare relative
   path leak past the RAII boundary and are forbidden.
3. **Bounded `target/` build output is reclaimed by `cargo clean`,** not by a
   per-run teardown. Adding a nextest teardown that `rm`s the five prereq
   artifacts would only force a rebuild on the next run (slower, no cleaner),
   so it is deliberately NOT done.
4. **A new platform/link fixture extends the setup script** (§2.2), keeping
   its artifact in the same bounded `target/debug/` set — it does not
   introduce a new persistent scratch root.

This keeps the tree flat run-over-run with zero new harness code: the
`TempDir` drop is the pruning mechanism, and it already runs on every test.
