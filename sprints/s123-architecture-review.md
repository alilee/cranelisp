# S123 Phase 2 architecture review

Date: 2026-11-15. Reviewer: `arch` (Claude Code subagent, claude-opus-5-5).
Checkpoint: HEAD `f747990f` plus the uncommitted coordination edits, with
`sprints/archive/sprint-123.md` new and untracked. The review was read-only: no source,
test, specification or design edits, no test runs, no commits and no network
calls. One measurement build ran in an isolated directory under `target/`,
which was then deleted (§8). This report is a proposal for the user. It
approves nothing and is not a public-API approval packet until the user
approves the exact deltas in §5.

## Status after the Phase 2 rulings (amended 2026-11-15, Phase 3)

The user's rulings and two measured pre-checks changed this review. Where a
section below is superseded, the replacement is named here and the section is
kept only as the record of what was proposed.

- **§3.2 was falsified by measurement and is corrected in place.** The
  toggle does not keep the copy-on-write exemption for direct update loops
  ([carry triage](../tests/plan/s123-carry-triage.md) §8).
- **§3.3 ran.** Both discriminators' results are in triage §7 and §8, and the
  amended [option paper](../design/arch/ownership-stratum-options.md) §3.3
  draws the consequences. The user chose reading U′.
- **§1.3 is decided:** the privacy interaction is accepted as it stands.
- **§2.3 is superseded:** link-time parameters are baked into the executable
  ([environment supply](../design/arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) §4b invariant 18).
- **§3.5's last bullet, §4, §5 rows A and A′, and §7 items 3–4 are
  withdrawn:** panics end the process, so option A, its
  `runtime/panic_pending` delta and the empty-slot invariant leave the scope
  ([process-ending panics](../design/arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics) §4b invariant 13).
  ACT-1033's derivation stays in scope on its own merit, without a gate.
- **§5 is replaced** by the [S123 API packet](s123-api-packet.md).

## Verdict

The approved S123 scope fits the existing boundaries. It needs no new crate,
no new service and no new cross-crate type. Four of its five strands stay
within one context or use an existing seam:

- **Agent on by default.** A Binary/int packaging change with no
  public-API delta. The linked-executable boundary keeps the agent out of
  shipped artifacts by construction.
- **Environment files.** These fit as a startup supply into the process
  environment, which stays the single source every crate reads. There is no
  cross-crate API delta.
- **Panic option A.** Fits on design's seam. It needs one additive intrinsics
  export, which goes through the user gate (§5), and one new safety invariant
  on the panic slot (§4).
- **Option-2 measurement.** The framing does not fit as currently written.
  The option paper's definition of option 2 is ambiguous, and the measurement
  as planned cannot detect the cost that is most likely to decide it (§3).
  This is the material risk in the sprint. Two cheap discriminators must run
  before the measurement.

Required scope adjustments are listed in §7, and decisions only the user can
make are listed in §9.

---

## 1. Agent compiled in and enabled by default

### 1.1 Findings

- **Shipped artifacts stay agent-free by construction.**
  `crates/cranelisp-exe-bundle` depends only on intrinsics, primitives and
  platform, never on the root crate. So `rig-core` cannot reach a `--link`
  output, and the "not part of any shipped artifact" non-goal (NG4) still
  holds structurally ([agent boundary](../design/arch/repl-embedded-agent.md)
  §1.3).
- **No public-API delta.** `src/lib.rs` already declares `pub mod agent`
  under `#[cfg(feature = "agent")]`. Its only consumer outside the library is
  the binary target (`src/main.rs` uses `cranelisp::agent`). No test,
  benchmark or other crate imports it, and no `rig` type appears in a public
  signature. Turning the feature on by default adds no item, signature,
  visibility or consumer edge. It changes only which configuration compiles
  the existing items, so the user gate does not apply.
- **Dependency footprint, measured.** A cold default build of the binary was
  followed by an incremental build with the agent feature, in an isolated
  `target/` subdirectory on this 14-core host:

  | | Default | With agent |
  |---|---|---|
  | Unique packages, normal edges (`cargo tree`) | 112 | 211 |
  | Debug binary | about 170 MB | 257 MB |
  | Wall time | 17.8 s cold | 21.4 s more, incremental |

  These are single-shot, order-of-magnitude figures. The release binary and
  the test-binary link cost were not measured.
- **New prerequisite on Linux build hosts.** `native-tls` brings in
  `openssl-sys`. A plain `cargo build` on Linux will now need `pkg-config`
  and the OpenSSL development headers. Today only the agent lane needs them.
  The rustls alternative is still the one rejected in
  [agent design](../design/int/agent.md) §6.4: under reqwest 0.13 it brings in
  `aws-lc-rs` and needs a C toolchain.
- **Dormant routing is unchanged.** Under the "active ⇒ route; dormant or off
  ⇒ deterministic display" rule
  ([agent boundary](../design/arch/repl-embedded-agent.md) §5.3), an enabled
  agent with no explicit provider diverts no input. For users without a
  provider, the only visible change is the startup banner.
- **The provider fallback must go.** `src/agent/provider.rs:74` defaults an
  unset `CRANELISP_AGENT_PROVIDER` to `anthropic`. The user's ruling makes
  that case dormant. This is interior work for `design`(int), then `dev`(src).

### 1.2 Architecture position

- **Keep the `agent` Cargo feature and add it to the default set.** Do not
  delete the feature. The `#[cfg]` cuts sit at seams (classifier arm, `/ask`
  body, allowlist rows, the module), so an LLM-free build remains
  structurally the original REPL at no ongoing source cost. Only its
  evidence costs anything.
- **An LLM-free build stays supported only if a lane exercises it.** Under
  the root assurance rule, a configuration that nothing builds or runs is
  graded by inspection. The cheapest adequate control is `qa`'s to choose. A
  plausible minimum is `cargo check --no-default-features` plus the existing
  feature-off cells in `tests/agent.rs` run under `--no-default-features`.
  These are the inverse of today's lanes. They cover the feature-off rules
  for `--agent` and `--yes`, which are no longer the default.
- **Default suite cost.** Every `#[cfg(feature = "agent")]` test in
  `tests/agent.rs` (91 gated items) and in `src/` joins the default suite.
  This is unmeasured. Named falsifier: the first default-suite run after the
  change, compared with the 170 s post-build baseline in root `CLAUDE.md`.
  `qa` records it.
- **Carriers to update after approval.**
  - `arch`: [agent boundary](../design/arch/repl-embedded-agent.md) §1.2
    G-light, §1.3 NG2, §7.2, §7.3, §7.4 and the U6 row in §10. "Opt-in twice"
    becomes "on by default; an explicit provider is the single opt-in to
    transmission".
  - `design`(int): [agent design](../design/int/agent.md) §1 and §6.4.
  - `dev`(src): the feature comment in `Cargo.toml` and the header of
    `src/agent/provider.rs`.
  - `spec` and `docs`: their carriers, as SPRINT.md already lists.

### 1.3 A privacy interaction between two rulings (user decision)

- **The rulings combine.** One ruling makes `CRANELISP_AGENT_PROVIDER` the
  single opt-in to transmission. Another lets a project `.env` supply every
  variable. Together they mean that a project `.env` written by someone else
  can opt the user in. This repository ignores `.env`, but third-party
  Cranelisp projects may commit one. If the user's shell also holds
  `ANTHROPIC_API_KEY`, which the third ruling's own rationale says is common,
  REPL source would go off the machine without the user's own
  Cranelisp-specific choice. Avoiding that was the reason for the ruling.
- **Existing mitigations.** The banner states "active" with provider and
  model. The first-use disclosure in `repl/spec/17-embedded-agent.md` §17.8.1
  is a notice, not a gate. It prints before the first transmission, and that
  transmission still happens on the same turn.
- **Options:**
  - (a) Accept the banner and disclosure as sufficient.
  - (b) **Recommended.** Turn §17.8.1's existing "MAY require an explicit
    per-session acknowledgement" into MUST for any endpoint off the local
    host. It applies whichever source supplied the setting, so it fits the
    ruling that sources are not reported. Declining keeps the agent dormant,
    as §17.8.1 already says.
  - (c) Accept the provider variable only from the process environment or the
    user file. This contradicts the ruling that all variables are read the
    same way.
- **Owners.** `spec` frames the wording and the user decides.

---

## 2. Environment supplied from files

### 2.1 Reader census

About 58 distinct `CRANELISP_*` names are read in source, plus `NO_COLOR`,
`ANTHROPIC_API_KEY` and `OLLAMA_API_BASE_URL`. About 23 are documented in
`user/`, `repl/` and `spec/`. They are read in:

- the binary (`src/`);
- backend (`heap.rs`, `sparkability.rs`, `lib.rs`);
- intrinsics (`rc.rs`, `ivar.rs`, `diagnostics.rs`, `reactor.rs`,
  `alloc.rs`);
- typecheck (`ownership/trace.rs`);
- types (`ownership.rs::ownership_analysis_off`, which also feeds the cache
  manifest key).

Many are memoised in `LazyLock` or `OnceLock`. Several are read on every
call. One example is `CRANELISP_CODEGEN_DUMP` in
`crates/cranelisp-backend/src/lib.rs:1083`. No production code writes the
environment; every `set_var` is in test modules.
`CRANELISP_BUILD_ID` is compile-time (`env!`) and outside the ruling.

### 2.2 Decision within architecture: supply once, then read only the process environment

- **The process environment stays the single source** (Principle 07, single
  source of truth). Every library-crate reader stays as written. The binary
  is the only supplier: as its first act it reads the project `.env` and the
  user file and sets each admitted key that the process environment does not
  already define. This gives the precedence the user ruled: process
  environment, then `.env`, then the user file. No library crate reads a
  configuration file.
- **Why not a typed configuration value.** Threading one through the crates
  would change every reading crate's public API. It would also have to reach
  runtime readers called from JIT code in intrinsics, which have no caller
  parameter to carry it. It would duplicate the environment the test suite
  already uses for per-child control. Principle 02 (narrow interfaces) and
  Principle 06 (complexity has a budget) both favour the supply.
- **Ordering is a design constraint, and soundness depends on it.** The crate
  is on edition 2024, where `std::env::set_var` is `unsafe`. It is sound only
  while no other thread reads or writes the environment. So the supply must
  run:
  - before any thread starts. `sched_dump` starts one at install, and the
    workers start later.
  - before the earliest reader, `CRANELISP_RC_STATS` at `src/main.rs:174`,
    which today runs before argument parsing.

  Argument parsing and project-root resolution are pure and may run first.
  Where the supply sits inside that window is `design`(int)'s choice.
- **Admitted keys.** Admit the `CRANELISP_` namespace plus the named foreign
  keys the compiler reads itself (`NO_COLOR`, `ANTHROPIC_API_KEY`,
  `OLLAMA_API_BASE_URL`), and ignore every other key. A project `.env` is
  shared with other tools. Injecting keys such as `PATH`, `LD_LIBRARY_PATH`,
  `CC` or proxy variables would change the system-linker invocation under
  `--link` and the agent's HTTP client. Injected keys are inherited by child
  processes, including the linker, which is the conventional behaviour. A
  prefix rule covers the 35 or so undocumented switches without keeping a
  registry. `spec` records the rule, and the user confirms it as the reading
  of "every variable the compiler reads".
- **Repeated reads do not need to become startup values.** In production the
  environment does not change after the supply, so repeated reads already
  return the startup value. Turning a repeated read into a parameter (for
  example `CRANELISP_CODEGEN_DUMP` in a public backend function) would be a
  public-API change with no correctness benefit. A crate may still memoise a
  read inside its own interior without any API effect. That is the crate's
  `design` decision, made on cost alone. The backend audit's note is a
  hygiene question, not a requirement of this ruling.

### 2.3 Linked executables read only the process environment (user confirmation)

- **The question.** Compiled programs run intrinsics runtime code that reads
  runtime knobs: `CRANELISP_SPARK_BUDGET`, `CRANELISP_DEGREE`,
  `CRANELISP_RC_STATS` and the drive mode. Under `--run` and in the REPL,
  that code runs inside the compiler process, so file-supplied values reach
  it. A `--link` executable runs as its own process.
- **Recommendation.** Linked executables read only their process
  environment. A shipped program that silently reads a `.env` in its working directory and
  `~/.config/cranelisp/` on the machine where it runs would let local files
  configure deployed software. That is a deployment-boundary choice the
  program's author should make, and none has. The ruling says "the compiler
  reads", and the linked executable is not the compiler.
- **Consequence the user must accept.** With the same project directory, a
  runtime knob set only in `.env` affects `cranelisp --run` but not the linked executable run from that directory.
  Both read their own process environment, but the two environments differ.
  Under root `CLAUDE.md`'s divergence rule this is a defined difference, not
  a pipeline divergence: the compilation is identical and the supplier is
  not. `docs` must state it.
- **Alternative.** The linked executable also loads the files. The loader
  would then have to live in a crate the bundle links, intrinsics or
  platform. That adds a public function and two consumer edges (binary and
  startup stub), which go through the user gate, plus a specification of
  program-runtime configuration. Not recommended.

### 2.4 Test isolation needs a structural control (for `qa`, with the loader shaped to allow it)

- **A material residual.** Tests run with the repository root as working
  directory. The user has just added `.env` to `.gitignore`, which suggests
  a root `.env` is intended. With the files ruling, every spawned compiler
  would read the developer's repository-root `.env` and user file.
- **The worst case is egress, not a wrong result.** Suppose a developer's
  user file sets `CRANELISP_AGENT_PROVIDER=anthropic` and a key. Any agent
  test that does not pin the provider would then transmit to a live
  endpoint.
- **What the loader must offer.** The file locations must be overridable,
  and the loader must be disableable, from the process environment only.
  Examples are the conventional `XDG_CONFIG_HOME`/`HOME` resolution plus one
  disable switch that a file cannot set.
- **Who decides what.** `qa` then picks one repository-level declaration
  (for example the `[env]` table of the nextest or Cargo configuration). A
  per-test discipline would decay. Placing the declaration is `qa`'s;
  providing the override is `design`(int)'s.

### 2.5 Specification questions this raises (`spec`)

- What "project" means. The resolved project root (`resolve_target_from` in
  `src/main.rs`), which is the working directory in the default case, or the
  working directory always. Recommended: the resolved root.
- The user file's name and syntax, and whether `XDG_CONFIG_HOME` is honoured.
- What a malformed line does.

---

## 3. Option-2 measurement: the framing needs correcting before the number is taken

This is the sprint's largest architectural risk. The
[option paper](../design/arch/ownership-stratum-options.md) is `arch`'s, and
the corrections below are its Phase 3 amendment.

### 3.1 Option 2 has two readings, and the paper uses both

- **Reading R: the reference lowering.** Section 3.1 defines option 2 as
  promoting "the conservative all-Owned lowering", which is the analysis-off
  toggle (`crates/cranelisp-types/src/ownership.rs:335`), to the default
  emission. Principle 25 (narrowing carries its check) treats that lowering
  as the reference semantics.
- **Reading U: fully uniform emission.** Section 3.1 also describes it as
  collapsing the move and copy-on-write exemptions, borrowed-alias elision,
  tail-call carry-forward, match release gates and "control-flow protection"
  into "every binding occurrence incs, every scope exit decs". That is
  fully uniform emission.
- **The two differ by exactly the "structural elisions"** that `PLAN.md`
  says the toggle leaves in place. Audit F3 adds that `tail_arg_protect`,
  branch forwarding and the flushes run in both polarities.

### 3.2 Why the toggle number cannot decide reading U

- **Copy-on-write in place depends on uniqueness.** A `vec-set` or
  `vec-push` picks the in-place arm or the copy arm by a runtime `rc == 1`
  probe (`crates/cranelisp-backend/src/compiler/vec_codegen.rs:209` and the
  COW-arm documentation above it).
- **Uniform emission breaks that uniqueness.** If every binding occurrence
  takes a reference, as reading U says, a vector held in a variable reaches
  the update with a count of at least 2, so every update copies. An in-place
  update loop becomes quadratic.
- **The paper's expectation fails under reading U.** Section 3.3 expects "a
  measurable constant-factor cost, not a cliff". For direct update loops,
  reading U predicts a cliff. (This review named the exemplar's Sudoku solve
  as such a workload; triage §8 shows it never updates in place, so its cliff
  is already present today.)
- **Corrected (triage §8): the toggle already shows it on direct loops.**
  This review claimed that the toggle keeps the move and COW exemptions and
  so cannot observe this cost. That is false for the one shape that updates in
  place: with `CRANELISP_NO_OWNERSHIP` set, a direct self-tail update loop
  copies 1,000 of 1,000, against 0 of 1,000 under current emission. The
  toggle number is still the exact cost of reading R, but it already contains
  the quadratic term for direct loops. The exemplar cannot show the term
  either way, because it takes the in-place arm zero times under both
  polarities.

### 3.3 Two discriminators that should run before the measurement (cheap, `qa` then `test`)

1. **Does the defect class survive the toggle?** Run the ACT-1030
   use-after-free reproduction and the ACT-1026 and ACT-1028 REDs under
   `CRANELISP_NO_OWNERSHIP`, armed with `CRANELISP_RC_DEC_CHECK`. Audit F1
   lists this as the open unknown.
   - If they still fail, the faults live in rules both polarities share.
     Reading R does not remove them, and only reading U, or instance repair,
     does.
   - If they pass, reading R is a real candidate.
2. **How much in-place COW does the exemplar rely on?** Count the in-place
   arm against the copy arm on the warm solve under current emission. The
   number decides whether the COW exemption has to be part of the reference
   semantics for any variant of option 2 to be usable.

### 3.4 How the measurement should be framed

- **`design`(backend) classifies each structural rule** from audit F4's
  thirteen deciders and the toggle's retained elisions:
  - *count arithmetic*: safe to replace by uniform inc/dec;
  - *semantics-bearing*: it preserves complexity or placement. Examples are
    last-use move into a COW operation and stack placement.

  That classification defines **reading U′**: uniform emission except for a
  closed, named list of semantics-bearing rules, each carrying its check
  under Principle 25. Reading U′ is the only uniform variant that can be
  adopted.
- **Measure reading R exactly with the toggle**, using `PLAN.md`'s method:
  the exemplar warm solve's wall time and RC counts, the contention
  benchmark, and the full suite's wall time and failures by name.
- **Estimate the extra cost of reading U′** from the classified list. Use
  per-site counts where `CRANELISP_RC_STATS` attributes them. A measurement
  build of reading U′ is admissible only as a throwaway spike that is never
  merged (Principle 08, no interim implementations).
- **Measure in every mode, `--link` included.** No `--release` tier exists:
  the [release proposal](../design/arch/release-llvm-backend.md) is
  unratified, and LLVM is excluded. The
  [ownership inference](../design/arch/ownership-inference.md) §3.4 tier
  statement places the mechanisms in the one shared Cranelift lowering. So
  the paper's "dev tier" and §3.5's "elision moves to `--release`" have no
  current referent. Adopting option 2 changes emission for the REPL,
  `--run` and shipped `--link` executables alike.
  - **Do not keep tuned emission only for `--link`.** That splits emission
    by mode, against Principle 11 (single pipeline, mode parameters) and the
    root rule that a REPL/`--run`/`--link` divergence is a defect. The
    elisions would then live in the mode the suite exercises least.
- **Hold the concurrency floor up against it.** The contention benchmark
  must be read against the floor in [effect concurrency](../design/arch/effect-concurrency.md)
  §3. The floor is already scoped down for RC-heavy parallel work, and
  option 2 raises exactly that term.
- **Agree the decision rule before the number exists.** The user should fix
  the threshold for each variant before seeing the result, for example "the
  exemplar warm solve no worse than N×, and no asymptotic change". This
  follows the root rule that a ruling not yet tested by measurement does not
  bind, and it stops the number from anchoring the threshold.

### 3.5 What adoption would change in the architecture

- **Assurance improves for the reference half.** Under reading R or U′, the
  emitted code *is* the reference lowering for everything outside the named
  list. Principle 25's equivalence property becomes structural for that part
  rather than measured, and the R9 differential lane becomes vacuous for it.
- **Ownership-analysis output loses its emission consumers.** It would be
  kept only for a future elision tier. Keeping it as "landed with zero
  consumers" is the failure state the root assurance rule names. If it is
  retired or narrowed, that changes `cranelisp-types` (`Mode`,
  `ModeSummary` and related items) and typecheck, and goes through the user
  gate. **No such delta is proposed for S123.** If the user adopts option 2,
  `arch` frames it as a follow-on packet.
- **Order of work on the shared call sites** (`compiler/apply.rs`): panic
  option A lands first, the decision second, and the ACT-1030 fix third, in
  the shape the decision selects. A is independent of the option-2 decision
  and small, and it closes a blocking defect.

---

## 4. Panic propagation, option A

- **Does A fit?** Yes. A extends A0's seam
  ([s122 closure](../design/backend/s122-closure.md) §10.3) in backend
  emission. It adds one new intrinsic, a read-only query on the panic slot.
- **Is it a change to the panic ABI? Ruling: no.** That ABI consists of:
  - `runtime/panic`'s signature and its raise semantics;
  - the zero-sentinel return convention;
  - the rule that a boundary owns draining the slot.

  A query that does not clear the slot changes none of these. The query
  **must not clear the slot**. Draining stays with the boundaries, which are
  the single drain owner (Principle 07).
- **A raises one existing property to a safety invariant (for `design`).**
  - **The hazard.** Under A, a stale slot left set by an earlier evaluation
    would make a later, correct zero result propagate as a panic. That
    silently cuts the evaluation short, the same harm A0's non-null premise
    guards against.
  - **The new invariant.** "The slot is empty when every boundary is
    entered" stops being a convenience and becomes a safety invariant.
    `s122-closure.md` §10.3 already records one boundary that may leave
    guard state behind: the trace guard in the int hosts.
  - **Assert it at the seam** (Principle 25, clause 3). Structurally, every
    boundary clears the slot on entry, as `cranelisp_run_program` already
    does. A debug assertion at each boundary entry is the measured
    companion. Owners: `design`(intrinsics) for the boundaries in that
    crate, `design`(int) for the hosts.
- **Making the catalog entry safe depends on ACT-1033.**
  - **How the import is declared.** The backend declares every import from
    the catalog's hand-copied `(param_count, has_return)` pair
    (`crates/cranelisp-backend/src/jit.rs` reads
    `intrinsics_table()`).
  - **The panic module's entry is already wrong.** ACT-1033 found three
    wrong pairs. One is in the panic module A extends: `runtime/panic`
    declares a return (`crates/cranelisp-intrinsics/src/catalog.rs`, the
    `runtime/panic` entry), but the function returns nothing
    (`crates/cranelisp-intrinsics/src/panic.rs`, `runtime_panic`). This was
    re-checked against source for this review.
  - **Why it matters for A.** A is the first new emitter that **reads** a
    catalogued return value. An error in its entry would read an unwritten
    register at every zero result.
  - **Recommendation.** Take ACT-1033's preferred control (derive each
    entry's pair from the function's type, so a disagreement does not
    compile) into S123 with A, in the same intrinsics visit. A
    crate-private derivation keeps `IntrinsicEntry`'s public fields
    unchanged, so the control needs no gate. Retiring
    `runtime/rc_underflow_check` or `runtime/string_read` would remove public
    items and is a separate decision (§9 item 8).
- **Cost.** The query is an extern call that borrows a thread-local, paid
  only on a zero result of a non-`AlwaysHeap` call. `false`, `0` and nullary
  tag 0 are common results, so `design` measures how often the query runs
  inside the design window, as §10.3 already requires. If the cost is
  material, the filter is a process-wide pending indicator read inline. That
  is a different exported symbol, so the user approves it as a separate,
  pre-stated delta (§5 row A′) rather than through an open-ended second trip
  to the gate.
- **Thread placement.** The slot is thread-local. A callee runs on its
  caller's thread. A spark's panic reaches the forcing thread through the
  IVar ferry before `cranelisp_ivar_force` returns. So the query on the
  calling thread is correct. `design` should confirm the ferry ordering
  against source.
- **Evidence note for `qa`.** Propagation leaks frame-owned values, which
  §12.7.4.1 and §12.7.8 item 4 permit. Balance lanes, including the marginal
  pair and the differential lane, must classify panicking cells as permitted
  leaks rather than imbalances.
- **First-error-wins is optional.** `runtime/panic` overwrites the slot,
  while `set_runtime_error` keeps the first error. Under A the overwrite can
  no longer replace a pending message on the JIT path. Aligning the two is
  optional hygiene for `design`(intrinsics). It is not a change to the panic
  ABI.

---

## 5. Proposed public-API deltas

Only option A's packet is proposed. The exact name and signature below are
`arch`'s proposal for the user gate. `design` may propose a different name
before the user approves, and any difference returns to the gate.

| Row | Producer | Exact delta | Consumers | Compatibility, schema and ABI | Expected `public-api.txt` effect |
|---|---|---|---|---|---|
| A | `cranelisp-intrinsics` | Add `#[unsafe(export_name = "runtime/panic_pending")] pub extern "C" fn cranelisp_intrinsics::panic::runtime_panic_pending() -> i64`. It returns 1 when the calling thread's runtime-error slot is set and 0 otherwise, and never clears the slot. Add one `IntrinsicEntry` row: `name: "runtime/panic_pending"`, `param_count: 0`, `has_return: true`, `is_runtime: true`. | New consumer edge: backend emission imports the symbol (A0's slow path in `compiler/apply.rs` and the `cranelisp_ivar_force` sites). The `--link` bundle exports it through the existing `pub use cranelisp_intrinsics::panic` re-export, with no source change. | Additive. Emitted-call ABI: one new import, with existing imports unchanged. No `CACHE_SCHEMA_VERSION` bump, per §10.3: old objects never import the symbol, and the runtime ships with its compiler. The evidence must show that no sidecar persists a table derived from the catalog. Not a panic-ABI change (§4). | `crates/cranelisp-intrinsics/public-api.txt`: +1 line (the function). Catalog rows are data, and no line changes for them. Other baselines: 0. Root and exe-bundle: no baseline, no source API change. |
| A′ (conditional, only if the query rate is measured as material) | `cranelisp-intrinsics` | Add one exported process-wide pending indicator that backend emission reads inline before calling `runtime/panic_pending`. Its exact type and symbol are stated by `design` with the measurement, before implementation. | Backend emission | Additive | +1 or +2 lines; stated with the packet |

Nothing else proposes a delta:

- agent default: none (§1.1);
- environment files: none (§2.2);
- option-2 measurement: none (§3.5);
- ACT-1033's derivation control: none if crate-private (§4).

---

## 6. Second-deferral triage: structural observations in `arch`'s remit

`qa` owns the per-item carry triage and is preparing it alongside this
report. The observations below are the architecture half, limited to items
that wait on `arch` or on a boundary decision.

- **Packets that are never prepared keep blocking their own scheduling.**
  - **The items.**
    - K5 N1 needs a change to `ImportNames`. That type lives in the types
      crate (`crates/cranelisp-types/public-api.txt`, `ImportNames`), which
      `arch` owns.
    - K11's baseline batch is ACT-0955, ACT-0963 item 2 and ACT-0971, each
      `to: arch`.
    - Audit R10 is a consumer-less surface disposition.
    - ACT-1033 is `to: arch`.

    Each needs an exact `arch` packet before the user can decide whether it
    is worth doing.
  - **Why they recur.** Phase 2 reviews only the approved scope, so excluded
    items never get a packet. They then come back to the next Phase 1 as
    "needs the gate" again. The deferral is caused by process placement, not
    by size: every packet is small.
  - **Recommendation.** In Phase 3, `arch` prepares packets only, not the
    implementation, for K5 N1 (carrying ACT-0997's impl-identity obligation),
    the K11 batch and R10. They are presented to the user together, so that
    any third deferral is decided on an actual delta.
- **ACT-1033 has become load-bearing.** Option A makes it so (§4). Pull it
  in with A (§7).
- **K7 R1 (launched-work cancellation, ACT-0977).** An approved requirement
  whose realisation needs an architecture decision. The decision is who owns
  cancellation and what the completion witness is, under Principle 21
  (actors and functions before mechanism). It keeps deferring because it is
  sequenced behind memory-safety work, and this sprint is memory-safety work
  again. A third carry needs the user's sign-off under METHOD §2.4.5.
  `arch` cannot reduce it to a packet without a design pass. The truthful
  options are to schedule that pass in S124 or for `spec` to frame a
  narrowing.
- **K9 C6 (ACT-0986 item 1).** The missing warning needs a diagnostic channel
  from in-language `discover-tests` to the host. Intrinsics is
  diagnostics-free by charter (bounded contexts §4b), so this is a new
  boundary mechanism rather than a fix. The host runner already warns, so
  the cheapest truthful repair may be to narrow the requirement through
  `spec`. The user decides.
- **K6 C4.** Unchanged from the S122 review: a precise collision refusal at
  the existing load boundary is preferred over a naming restriction. It
  needs no `arch` action until `test`'s falsifier fixture establishes
  reachability.

---

## 7. Required scope adjustments

1. **Run the two option-2 discriminators (§3.3) before the measurement.**
   `qa` allocates them and `test` runs them. Without them the measurement
   cannot tell readings R and U apart.
2. **Amend the option paper in Phase 3** (`arch`):
   - define readings R and U′ and their classified list;
   - replace §3.3's constant-factor expectation with the COW analysis;
   - restate §3.5 for a single emission tier;
   - add the decision rule the user agrees before the number exists.

   `design`(backend) supplies the classification.
3. **Pull ACT-1033's derivation control into S123** with option A, in the
   same intrinsics visit. No gate is needed if the derivation stays
   crate-private.
4. **Add the boundary-entry slot invariant (§4) to option A's design and
   evidence**, owned by `design`(intrinsics) and `design`(int).
5. **The environment loader must offer a process-environment-only override
   and disable (§2.4).** `qa` places the suite's declaration in the same
   change-set that introduces the loader.
6. **Prepare the K5 N1, K11 and R10 packets in Phase 3, without
   implementation** (§6). This is optional and the user decides. It is the
   structural remedy for their recurring deferral.

---

## 8. Evidence and method

- **Sources opened.** I opened every claim above at `f747990f` plus the
  coordination edits:
  - `Cargo.toml`, `src/lib.rs` and `src/main.rs`, including its `fn main`
    ordering;
  - `src/agent/provider.rs`, `src/sched_dump.rs`, `src/exe.rs` and
    `crates/cranelisp-exe-bundle/Cargo.toml`;
  - `crates/cranelisp-intrinsics/src/panic.rs`, its `catalog.rs` and its
    `public-api.txt`;
  - `crates/cranelisp-backend/src/compiler/vec_codegen.rs` and
    `crates/cranelisp-types/src/ownership.rs`;
  - the agent boundary and design documents, the option paper, ownership
    inference §3.4, the release proposal's status, the backend audit (F1,
    F3, F4, R1–R12), `PLAN.md`'s option-2 method, `s122-closure.md` §10,
    ACT-0997, ACT-1033 and ACT-1040, and the S122 carry table.
- **The environment census** is a source search over `src/`, `crates/` and
  `platforms/` for `env::var`, `env::var_os` and `env!`, with test modules
  excluded by inspection.
- **The dependency figures** come from:
  - `cargo tree --offline -e normal` with and without `--features agent`;
  - one cold default build and one incremental agent build into
    a scratch directory under `target/`, deleted afterwards.

  Single-shot timings on a 14-core host: order of magnitude only.
- **Incidental.** During the measurement I ran `touch src/main.rs`. It
  changed the file's modification time only; its content and `git status`
  are unchanged. The next build in `target/debug` will recompile the root
  crate once.
- **Not measured, with falsifiers named above:**
  - the default suite's wall time with the agent compiled in (§1.2);
  - option A's query rate (§4);
  - every option-2 number (§3).

---

## 9. Decisions only the user can make

1. **Option 2.**
   - First, the threshold for each variant, agreed before the number exists
     (§3.4).
   - Then, with the number: adopt reading R, adopt reading U′, or reject.
     Adoption changes emission in every mode, shipped executables included,
     because no release tier exists.
2. **Option A's gate packet.** Approve row A as stated in §5, and decide
   whether to pre-approve row A′ subject to measurement.
3. **The privacy interaction (§1.3).** Recommended: acknowledgement becomes
   mandatory for endpoints off the local host. Alternatives: accept the
   banner and disclosure, or restrict the source of the provider variable.
4. **Linked executables read only the process environment (§2.3)**, with the
   documented difference between `--run` and a linked executable for runtime knobs.
5. **The admitted key set (§2.2).** The `CRANELISP_` prefix plus
   `NO_COLOR`, `ANTHROPIC_API_KEY` and `OLLAMA_API_BASE_URL`, as the
   reading of "every variable the compiler reads".
6. **A new prerequisite for the default build (§1.1).** On Linux, OpenSSL
   development headers and `pkg-config` are needed for a plain
   `cargo build`, and the debug binary grows by about 50%. Accept, or revisit
   the TLS backend.
7. **Whether the LLM-free build stays a supported configuration (§1.2).**
   Recommended: yes, with one cheap lane.
8. **Optional: retiring `runtime/rc_underflow_check` and
   `runtime/string_read`** (ACT-1033). These are public removals and would
   need their own exact packet.
9. **Optional: the packet-only Phase 3 work** for K5 N1, K11 and R10 (§7
   item 6).

## Next

After the user's decisions:

- **Phase 3 for `arch`:** the option-paper amendment and the agent-boundary
  carrier updates, plus the packets from §9 item 9 if the user wants them.
- **`qa`:** allocate the §3.3 discriminators and the §2.4 control.
- **`design`(backend):** the structural-rule classification and A's interior.
- **`design`(intrinsics):** ACT-1033's derivation and the slot invariant.
- **`design`(int):** the loader and the provider dormancy.
- **`spec`:** the §1.3, §2.3 and §2.5 wording.
