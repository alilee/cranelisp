# cranelisp-intrinsics — S125 whole-context assessment

## 1. Verdict

**Would a lean second implementation look like this? In its ownership core,
largely yes; in its repeated execution logic and accumulated explanation, no.**
One allocator, typed ownership transfers, layout owners, type-directed disposal,
one effect driver and a reactor for suspended work are credible. Two manually
maintained trampoline loops, production recording machinery with only test
readers, and overlapping accounts of delivered migrations add avoidable weight.

| Attribute | Grade | Basis |
|---|---|---|
| Design quality | B | Cohesive runtime boundary; shared ownership and teardown mechanisms. Cancellation ownership does not reach detached work. |
| Design realisation | C | Most mechanisms have consumers and executable evidence; cancellation contexts and reusable launch descriptions are incomplete. |
| Simplicity and volume optimality | C | Core mechanisms earn their place; repeated trampoline transitions, dormant production recording and extensive historical explanation create bounded recurring cost. |
| Duplication | C | Layout and disposal converge; synchronous/asynchronous walk orchestration remains duplicated. |
| Risk-weighted production-path coverage | C | Real-funnel detector triplets and deterministic handoff tests improve substantially on S115; cancellation composition, reuse and concurrent fault protection remain weak spots. |
| Maintainability | C | Ordinary changes mostly stay in this context, but ownership changes require parallel walk/evidence edits and reconciliation of several documentary accounts. |
| Memory and contract freshness | C | Current contracts still contain superseded layout and fault-path claims; the handle's public documentation omits its debug-only drop behavior. |

**Requirement fulfilment: partial.** The recorded full run contains three
intrinsics cancellation failures. Source also contradicts unrestricted IO reuse
for `Launch`. Trace output retains explicitly deferred semantic divergences.
The remaining sampled normal paths have implementation and evidence, but this
assessment does not certify every requirement or execution mode.

**Maintenance-economy grade: C, independently of correctness.** Avoidable
weight is material within the runtime and its maintained explanations, while
ordinary evolution remains mostly local. This assessment found no comparable
system-wide multiplication across persisted compiler products that would justify
D. Useful tests, prior approval and removal cost do not improve this grade.

## 2. Checkpoint, requirements and posture

| Field | Value |
|---|---|
| Context | `crates/cranelisp-intrinsics/`, `design/intrinsics/`, shared contracts in `design/runtime/`, relevant boundary contracts and evidence |
| Date/increment | 2026-11-27; Sprint 125, Phase 6a |
| Checkpoint | `main` at `4c844f62` plus the current S125 working tree; intrinsics source and its two design directories had no local changes on inspection |
| Owner/readers | `audit`; coordinator and user deciding disposition |
| Authority | [Audit contract](../.agents/skills/audit/SKILL.md), composed quality/document support, [rotation method](../sprints/METHOD.md#27-rolling-whole-context-audit), [collection](AGENTS.md) |
| Restrictions | Read-only outside `audits/`; no builds, tests, commits or destructive Git operations performed |
| Disposition | New recommendations pending the user's next scope disposition; existing decisions below remain identified separately |

In ordinary language, this runtime must keep language values alive while in
use and release them afterwards, preserve immutable-value behavior, execute
deferred effects in their specified order, respect resource limits, cancel
abandoned work, and finish outstanding detached work before normal termination.
It must support concurrent evaluation without changing results, report runtime
panics and platform faults consistently, and supply the values recorded by
language tracing. IO descriptions must be reusable.

Requirement sources read before assessing the realization were
[IO](../spec/10-io.md), [runtime](../spec/12-runtime.md) and the
[non-functional requirements](../spec/appendix-c-nfr.md), especially memory
management, consuming calls, atomic RC and layout containment. The
[bounded context](../design/arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)
and [safety register](../design/arch/safety-invariants.md) define the chosen
boundary and its assurance claims. Architecture and tests do not enlarge the
language's required purpose.

Delivery posture is one native release compiler, used interactively, in files
and as linked executables. Heap lifetimes are process-local; no runtime data
migration or service deployment is owned here. Foreign platforms are trusted
native components, not a sandbox boundary. Existing users and workload fixtures
make a runtime replacement expensive; that affects disposition, not economy.
No new workload scale or latency measurement was taken in this audit.

The smallest credible realization would retain one allocation/header model,
atomic RC, typed ownership transfers at Rust boundaries, concrete drop glue,
one shared set of IO transitions, bounded admission and a readiness driver.
Blocking work needs a worker boundary and a join acknowledgment; poll work needs
owned suspension state. Neither requires copying every common transition.
Diagnostics should attach to those existing seams. This is an economic
counterfactual, not an approved replacement design or a proposal to replace the
current executor with another framework.

## 3. Aggregate weight and important paths

The source inventory is 41 Rust files and 25,311 raw lines. Nineteen separate
test/helper carriers account for 12,667 lines; the remainder includes inline
tests, comments and blanks, so it is not a production-code count. `io.rs` has
1,703 lines and `reactor.rs` 2,463. Eight intrinsics design/memory documents
total 2,910 lines; the two runtime-pair contracts add 768. These are navigation
and change-cost observations, not size limits.

| Structure | Provenance and value | Current cost/assessment |
|---|---|---|
| Allocation, RC, heap layouts, `Owned`/`Borrowed`, disposal | Required memory behavior and least-cost enabling machinery; handle moves prevent double discharge through the typed surface | Keep the constructive core. Raw adoptions, emitted calls and eventual disposer identity remain a trusted boundary, not an exactly-once proof. |
| Reactor, permits, suspended-state owner, blocking bridge, supervisor | Required deferred effects, bounded resources, cancellation and launch; response to observed lifetime and wakeup defects | Real responsibilities with executing consumers. A synchronous-only driver would block readiness progress; a reactor-only driver would block on foreign blocking work. Removing either boundary is not a credible simplification. |
| Two trampoline loops and two `Par` paths | Worker execution has a distinct blocking boundary; common node transitions are repeated | Material change/review amplification, F4. The boundary earns separation; duplicated common orchestration does not follow from it. |
| M1/M2/M3, A1–A4, fault plants and child isolation | Response to observed memory defects and detectors that previously passed without detecting | Eight plants distinguish different failures and exercise production seams. No evidence here justifies deleting the set as redundant merely from its volume. Release-profile detection remains a limit, not a newly proven property. |
| Strand recording buffer and unused event vocabulary | Future production tooling; present tests observe admission/cancellation events | Current test value is real. Unconditional production mutex acquisition and future-only variants carry avoidable current weight, F4. |
| Catalog signature derivation and layout constants | Constructive prevention of wrong ABI arity/return and duplicate layout ownership | Small, local mechanisms; retain. Name/export agreement and literal offset escapes remain separate limits. |
| Trace descriptor walk and thread-role gate | Required trace values and isolation of recording from concurrent calls | Position-relative descriptors serve JIT and object output without per-link rewriting; no alternative encoding is warranted by this audit. Known semantic gaps remain deferred. |
| Memories, facade prose, seven interior designs, two pair contracts | API obligations, current mechanisms and cross-pair ownership | Useful homes exist, but repeated migration narrative and stale state require reconciliation, F5. |

Paths traced directly in source:

- **Heap value:** `alloc_with_rc` initializes the header; `rc_inc` applies
  the nullary guard and Release increment; shallow or type-specific release
  performs the last-reference fence before disposal. Vec buffers are separate
  allocations and use their own tail. `host_callbacks()` supplies the payload
  allocator rather than exposing the header to a platform writer.
- **Sequential IO:** `cranelisp_run_io` borrows the tree during `drive_io`,
  then consumes the caller's reference. Fresh `Bind` descent acquires its two
  children before structurally releasing the parent. `ProducedValue` owns a
  result until handoff; cancellation disposes an armed result rather than a
  numeric cancellation sentinel. `Pure` retains heap payloads and `Effect`
  borrows its repeatable thunk.
- **Suspension/cancellation:** `await_poll_node` retains the state closure;
  `EffectPoll` reads the ready result before releasing that reference.
  `ReactorInterest` releases permits and deregisters interest on drop.
  `AcquirePermit` removes cancelled waiters and forwards a freed permit when
  a woken waiter is cancelled before claiming it.
- **Blocking overlap:** `run_blocking_branch` acquires admission, starts a
  worker-owned lease, and receives an owned result through a oneshot.
  `CancelBridgeGuard` marks cancellation; the executor returns only after the
  worker lease count reaches zero. This retains the caller tree while a worker
  can still read it. The deterministic bridge and queued-result tests exercise
  distinct lifetime questions, so neither is redundant evidence.
- **Faults:** the platform force guard enters one terminator, which claims
  termination once, flushes stdout, composes one report and exits. Linked
  startup installs the captured runtime-switch table before readers. The
  per-call process-global signal installation has the concurrency gap in F2.
- **Tracing:** one thread-role predicate gates formatting and declines new
  sparks on the recording thread; collect marshals the root's result. The
  pure descriptor walker still renders function values as `<closure>`.

## 4. Findings and routing

### F1 — detached work escapes a losing branch's cancellation context

**High impact; reproduced in the recorded run; existing defect 0977.**
[IO cancellation](../spec/10-io.md#10129-structured-cancellation) and launch
item 5 require cancellation to reach detached work executed within the losing
context. `tests/concurrency_cancellation.rs::{s124_0977_race,
s124_0977_select,s124_0977_timeout}` assert the winner's result and absence of
the launched `L` output; winner, launched and inline controls distinguish
ordinary launch from losing-context cancellation.

`io.rs::run_select_node` drops only its remaining branch futures.
`launch_continue` moves subtrees into `reactor.rs::Supervisor`, which holds
one flat future set. Neither `ReactorEnv` nor supervisor entries carry a
cancellation-context relationship. The supervisor drains those detached
futures after the branch is gone. Strand ids are observation data, not
cancellation ownership. This source trace supports QA's attribution; this
audit did not rerun the reproductions.

**Route:** coordinator → `qa`, retaining the existing three guards; then
`design` on the runtime surface when scheduled, with `arch` for any boundary
delta. **Cost:** medium-to-large context design/implementation change; do not
estimate it as three unrelated fixes. **Disposition:** existing non-focus
carry; this audit grants no repair authorization or new current-sprint gate.

### F2 — concurrent platform calls can restore each other's trap handlers

**High-impact source-derived risk; no behavioral reproduction in this audit.**
`io_guard.rs::force_effect_thunk_protected` installs signal dispositions before
each foreign call and restores its saved set on normal return. Jump buffers
are thread-local, but `install_signal_handlers` and `restore_signal_handlers`
change process-global dispositions with no shared lifetime protocol.

Concrete source interleaving: A saves the default and installs the handler;
B saves that handler and starts another force; A returns and restores the
default while B remains inside foreign code. A trap in B then has no guard.
If B returns normally, it restores the handler after both protected extents
have ended. The inline unit tests cover one install/restore and one trap,
each in an isolated process; they do not exercise overlapping force extents.
`io.rs` deliberately runs blocking effects on multiple workers, so concurrent
entry is an existing production path, not a proposed extension.

This threatens the named, non-signal dispatch-fault outcome required by
[runtime faults](../spec/12-runtime.md#1276-interaction-with-io-model).
The interleaving is established by source; an actual missed report or stale
handler jump is **not observed** here. It is not added to the RED count.

**Route:** coordinator → `qa` intake, requesting a minimal discriminating
overlap reproduction through `test` before attributing a repair. **Cost:**
small-to-medium investigation; repair cost unknown. **Disposition:** pending.
No general signal-hardening catalogue or new control stack is recommended.

### F3 — reusable IO is narrower than its language contract

**Material requirement gap in source; second-force behavior unmeasured.**
[IO reuse](../spec/10-io.md#1081-task-tree-construction) permits repeated
forcing. `io.rs::launch_continue` writes zero into the published launch node's
subtree field after taking its first subtree. A second force reads that zero
as the next subtree; it cannot repeat the first force's work through this
path. Concurrent forces also have an unsynchronized write to that field.
`await_poll_node` reuses a single mutable state closure, whose repeated-force
semantics are likewise unmeasured. That latter observation alone does not
prove a poll-leaf defect.

The [safety register](../design/arch/safety-invariants.md) R20 already names
both residuals. Source confirms its qualification; `Pure` and `Effect` reuse
evidence must not be generalized to every node. This is not evidence that
S125 introduced the gap.

**Route:** coordinator → `qa` to reconcile the R20 intake with a permanent
minimal reuse reproduction and control; `design` only after attribution and
disposition. **Cost:** small reproduction, potentially substantial lifecycle
repair. **Disposition:** pending; no new failing test was authored by audit.

### F4 — duplicated execution and dormant production observation add recurring cost

**Medium maintenance priority; cost exists now, performance magnitude unknown.**
`io.rs::run_io_trampoline_inner_async` and `run_io_trampoline_inner` each
maintain frame initialization, edge-disposer selection, tag dispatch, the
`Bind` event/push sequence and step advancement. Shared helpers already own
the difficult release transitions, proving some convergence is practical.
A common transition change still has two orchestration edits and corresponding
evidence to review. The worker's need to avoid suspending on the reactor
justifies its execution boundary, not duplicate frame bookkeeping.

Separately, `strand.rs::sink::emit_strand_event` always locks the global
`Mutex<Option<Vec<StrandEvent>>>`. Recording controls are reachable only
inside the crate, and inspected callers are tests; the crate memory and
reactor design explicitly confirm no external production reader. Several
event/accessor variants await future tooling. Calling this "costs nothing"
is false even when no buffer is populated. No latency or contention penalty
has been measured here.

The cheaper credible shape preserves worker/reactor separation and test
observations while single-sourcing common transitions and making the
test-only recording cost absent from ordinary execution. It need not add
another public observer API or a `/strand` command. **Route:** coordinator →
`design`; `arch` if an interface change is proposed. **Cost:** medium for
walk convergence, small-to-medium for recording placement. **Disposition:**
pending economic decision, not a prescribed implementation. Retain existing
discriminating evidence; no blanket test reduction is recommended.

### F5 — current explanatory surfaces still describe superseded states

**Medium maintenance priority; directly verified document/source disagreements.**

| Carrier | Claim and source-first check | Owner |
|---|---|---|
| `design/arch/bounded-contexts.md`, intrinsics invariant 2 | Says R10-9 is not in source and backend defines ADT/closure layouts again. `alloc.rs` publishes `HeapAdt`/`HeapClosure`; backend's `heap.rs` has neither definition; the intrinsics heap-layout design already records delivery. | `arch` |
| `crates/cranelisp-intrinsics/Cargo.toml` | Says a blocking program constructs no `mio::Poll` through lazy initialization. `reactor.rs::block_on_reactor_capped` unconditionally calls `Reactor::new`; current reactor design and crate memory correctly say eager. | `dev` (intrinsics) |
| `design/intrinsics/diagnostic-modes.md` | Still calls FIXME 0857 open, although the S125 evidence delta records the R8 regrade and deletion. Its layout-ownership section describes the pre-convergence state. | `design` |
| `design/intrinsics/ownership-and-disposal.md` | Its fault-path explanation correctly says no abort returns; later evidence prose still calls the abort-path leak and severed join pending intakes. `reactor.rs` and its deterministic join tests now retain the tree until worker acknowledgment. These stale summaries must be reconciled with the precise surviving residual, not copied forward as an open defect. | `design` |
| `design/runtime/s119-typed-consume-funnel.md` and `handle.rs` | The contract explicitly records an open public-rustdoc obligation: the drop bomb is debug-only. Source has `#[cfg(debug_assertions)] impl Drop` but the public `Owned` explanation still omits that behavior. | `dev` for rustdoc; `design` for its obligation record |

The burden is wider than a handful of broken links: source commentary and
facade prose retain migration inventories that duplicate the boundary and
interior accounts. In the non-test-path source carriers, 5,515 lines are
comment-only, including essential safety arguments. That is not a deletion
target. Remove obsolete delivery narrative and duplicate inventories when
repairing the named claims; preserve caller obligations and non-obvious
unsafe/lifetime rationale.

**Route:** coordinator sequences the named owners. **Cost:** small factual
repair batch; no API or semantic change is implied. **Disposition:** pending;
audit did not edit those owners' files.

## 5. Existing decisions, predecessor calibration and limits

- **Trace gaps remain explicit.** `trace_format.rs` renders a function as
  `<closure>`, against `#closure` in runtime §12.9.1. Its descriptor set has
  no dedicated opaque-IO case. `trace-runtime.md` also names skipped-root
  behavior under ACT-1110. The [S125 trace deferral](../tests/plan/s125-evidence-delta.md#3-the-trace-deferral)
  records the user's decision to wait for the built-ins/primitives focus
  sprint, including TR-1, ACT-1110 and ACT-1111. Existing 1087/1090 failures
  are attributed to the binary, not silently added to intrinsics. Reuse those
  carriers and that decision; no new trace implementation is recommended now.
- **S115 detectors improved materially.** The
  [predecessor at Git 57253cf2](https://github.com/alilee/cranelisp/blob/57253cf2/audits/cranelisp-intrinsics-s115.md) described modes exercised only
  in isolation. Current `diagnostics/tests.rs` contains eight production-funnel
  plant triplets with clean and detector-off controls; M3 has a compiler-child
  e2e. S125's evidence records them passing and R8 regraded. This audit inspected
  the wiring and assertions, but did not repeat mutation/detection experiments
  or certify release-profile parity. Do not reopen 0848/0857 as missing tests.
- **ACT-0969's monolith lead is rejudged.** The action's `io.rs` claim was
  checked first: 1,703 lines now, against its earlier 1,847. The source contains
  identifiable helper groups and external tests. No file split is justified
  by that count alone. F4 identifies actual repeated behavior and current
  runtime cost; it is not a reissue of the retired size finding.
- **Constructive gains survive inspection.** Layout constants derive from
  their owners; catalog arity/return derives from checked function-pointer
  types and has malformed-row compile controls. `Owned` is not `Copy` or
  `Clone`; raw-site allow-lists measure a lexical trusted base, not provenance
  of every raw word. An emitted-layout literal or permitted adoption with the
  wrong owner remains a named falsifier, not a structurally impossible state.
- **Do not expand latent mechanisms now.** Root-tag `Par` partitioning and
  nested supervisor launch have recorded limits in reactor design §5. Without
  a reachable failing program this audit recommends no general async-graph
  classifier, reentrant supervisor framework or new probe matrix. Reconsider
  when lowering emits such a branch, or a real nested-launch use reproduces
  failure; `qa` then distinguishes reachability from an artificial raw-node
  fixture. Public allocation redesign remains the existing ACT-0959 decision.

## 6. Evidence, owned edits and completion

**Behavioral evidence reused, not executed by audit:** the latest recorded
[S125 full run](../tests/plan/s125-evidence-delta.md#253-the-full-run) reports
8,383 run, 8,301 passed, 82 failed and one skipped, with the failing set
unchanged from its attribution table: three intrinsics cells, all 0977.
The record reports no workspace build warnings. Those are QA's observations
at its named checkpoint, not measurements newly made by audit.

**Direct audit evidence:** requirements and canonical contracts; current
source traces above; module/e2e test bodies; line/file inventory; predecessor
retrieved from Git; action and filing sources reopened before disposition.
No compiler probes, Cargo commands or source mutations were performed.
F2 and the second-force consequences in F3 need behavioral reproduction;
they are visibly separate from the recorded REDs. No claim is made about a
complete platform/architecture matrix or measured runtime overhead.

**Requested older-record repairs:**

- Opened ACT-1022, its retained S122 evidence and S125 §2.1 disposition.
  The reconstructed pairs balance; the original program was never committed.
  Repointed `audits/cranelisp-backend-s122.md`'s live filing link to that
  disposition, preserving its historical lead and uncertainty.
- Opened FIXME 0785 and the exact trait process test in
  `tests/spec_07_traits.rs`; compared S125's passing evidence. Updated
  `audits/cranelisp-frontend-s123.md`'s row to the completed evidence and retained
  disposition rather than the deletable filing. Their owners may now remove
  the two filings; audit did not delete them.

**Document checker:** ran
`python3 .agents/tools/check_documents.py --root . --config standing-documents.toml`
after the three audit-file edits: **exit 1; 509 unsuppressed findings, all
`ignored-path`, zero sourced in `audits/`**. A preceding pass reported 510
outside-audit findings while other roles worked concurrently. Neither result
accepts or suppresses those findings. Coordinator/owning roles retain its
disposition; repair outside `audits/` is outside this dispatch. `git diff
--check -- audits` passed. Checker output is an ephemeral local measurement,
not retained authority.

**Next invocation:** return to `sprint` for disposition with the user. F1 reuses
0977; F2/F3 route to QA intake; F4 to design/arch as necessary; F5 to the named
document/source owners. No action files are authored by audit, and no finding
advances a phase or blocks the current sprint by itself.
