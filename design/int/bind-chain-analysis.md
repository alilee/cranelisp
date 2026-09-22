# Bind-Chain Independence Analysis — int Design

Owner: `design` (int). This document states the compile-time pass that turns
`bind!`-expanded chains into `Expr::ParBind` (structured fork-join) and
`Expr::LaunchContinue` (detached launch) nodes.

- **Required behaviour** is `spec/10-io.md` §10.12: automatic scheduling
  (§10.12.1–§10.12.4), launch-and-continue (§10.12.7) and structured
  cancellation (§10.12.9).
- **The concurrency model** — the inferred-launch predicate, the resource-token
  model and where ordering lives — is `/arch`'s
  `design/arch/effect-concurrency.md` (§4.1, §4.1.1, §8.2).
- **Runtime execution** of the nodes this pass emits belongs to the
  intrinsics runtime (`design/intrinsics/reactor.md`), with backend lowering in
  `design/backend/io-scheduling.md`. This pass is a single-threaded AST
  transform inside the pipeline; it spawns nothing and touches no scheduler
  state.
- **Section numbers are pinned** by source, test and plan citations. Retired
  numbers are not reused.

## 1. Contract

- **Input:** the post-expansion program of one cluster, before typechecking.
  A chain appears as nested
  `Apply(Var("bind"), [io_expr, Lambda([name], body)])`.
- **Output:** the same program with eligible bind steps rewritten. Two or more
  independent schedulable steps become one `ParBind`; a single eligible
  discarded step becomes `LaunchContinue`; every other step stays an ordinary
  sequential `bind`.
- **Invariants:**
  - A `ParBind` always has at least two bindings.
  - The pass recurses into lambdas, match arms, `let` bodies, binding
    expressions and existing `ParBind` and `LaunchContinue` nodes.
  - Re-running the pass on its own output is a no-op (§5.2).
  - Declining to rewrite is always sound: an unrewritten chain is the
    sequential program. Every analysis gap therefore defaults to sequential.

## 3. Algorithm (`src/bind_chain_analysis.rs`)

### 3.1 Pattern recognition

`is_bind_chain_start` matches an `Apply` whose callee is `bind` or ends in
`/bind`, with a one-parameter lambda as its second argument.

### 3.2 Chain collection

`collect_bind_chain` flattens the nesting into ordered steps (name, effect,
parameter annotation, span, callee spelling) and the terminal body. Parameter
annotations and the callee's spelling survive reconstruction.

### 3.3 Scheduling classification

`classify_expr` reads a scheduling class only for a direct call to a platform
effect (§4). Anything else — a user-function wrapper, a nested bind, a `let`,
a literal — is `Sequential`. The pass never looks inside function bodies.

### 3.4 Data independence

A step is independent when no name bound earlier in the chain is free in its
effect expression. The earlier names include committed sequential steps and
the current parallel group. Free variables come from
`cranelisp_types::free_vars_expr`. The analysis tracks only names the chain
binds, not aliases.

### 3.5 Grouping

`rebuild_chain` scans left to right. It accumulates consecutive steps that are
non-`Sequential` and independent. A step failing either test flushes the
group: two or more steps become a parallel segment, one step is demoted to
sequential, and none is a no-op. The failing step stands alone as sequential.

### 3.6 Reconstruction

Segments fold right to left: a sequential segment becomes a `bind` with a
lambda (`make_bind`), and a parallel segment becomes
`ParBind { bindings, body }`. Effect expressions and the final body are
transformed recursively.

### 3.7 Launch-and-continue

A step that stays sequential after grouping lowers to
`LaunchContinue { launched, continuation }` only when `launch_eligible` holds;
otherwise it remains a `bind`. The predicate is the local, conservative check
of `design/arch/effect-concurrency.md` §4.1. It is the same for a single
launched step and for a launched sub-tree (an inlined handler chain):

1. **E1 — result discarded.** The step's binder is not free in the
   continuation.
2. **E2 — value locality.** The launched expression and the continuation share
   no free variable. Sharing a handle implies sharing its dynamic token, so
   detaching could reorder two same-token effects. For example, with
   `(_ (send-conn conn r1))` followed by `(send-conn conn r2)`, the two share
   `conn`, so the step is refused.
3. **E3 — no shared-singleton token.** Every effect position is a
   `ResourceSerial` platform leaf (`is_launchable_leaf`). `Commutative` (token
   0), `Sequential` (token 1), a poll-shape leaf with a literal-`0` leading token,
   and any opaque user function are refused. A `sleep` timer leaf is accepted
   as a member of a launched sub-tree (`is_sleep_timer_leaf`), never as the
   launched root.

A `ParBind` is never re-lowered as a launch: a launch is one detached arm, and
a `ParBind` is a structured join.

**Cancellation neutrality.** Function calls, sequencing and inferred
scheduling neither establish nor cancel a cancellation context
(`spec/10-io.md` §10.12.9). The pass therefore emits no context boundary. A
launched strand runs in the context in which its launch executes, whether it
runs detached or inline. Realising that ownership belongs to the runtime; see
§7.

## 4. Platform scheduling data

- **One entry per platform function.** Platform load installs each manifest
  function in its `platform.{name}` module as a callable whose
  `CallableOrigin::PlatformEffect { scheduling_class, poll_shape }` carries the
  manifest's scheduling facts. There is no side registry.
- **Lookup follows resolution.** For a direct call, a slashed name is looked up
  in its named module; otherwise the name resolves from the current module
  through import and re-export chains to its terminal entry
  (`cranelisp_types::resolve_terminal_entry_and_home`). Only a terminal
  `PlatformEffect` yields a class; anything else, including an unresolved name,
  classifies `Sequential`.
- **No bare-name fallback.** Matching an unqualified symbol would let two
  platforms that export the same name collide.
- **One record for both decisions.** `effect_descriptor` supplies both the
  class for grouping (§3.3) and `poll_shape` for the E3 token-0 refusal
  (§3.7), so classification and launch eligibility cannot disagree about which
  entry was called.

## 5. Pipeline seam

### 5.1 One mode-uniform seam

- `finalize_cluster` (`src/process_form.rs`) calls
  `session_setup::apply_bind_chain_analysis` over `final_working`, after
  expression wrapping and default-method appending and before
  `check_program_compat`.
- **After expansion:** `bind!` is a macro, and the pattern exists only after
  expansion.
- **Before typecheck:** `ParBind` and `LaunchContinue` are expression variants
  the typechecker must see.
- **Mode-uniform by construction.** `--run`, `--link` and REPL evaluation all
  pass through `process_cluster_once` to this one call, so no mode can skip it.
  A second hook in any mode would be a defect.

### 5.2 Retry and idempotency

A dependency gap makes `finalize_cluster` return a gap. The cluster then
retries from the top with freshly expanded forms, discarding the previous
transformed tree, so the pass normally sees each tree once. It is also
idempotent: `recurse_children` descends existing `ParBind` and
`LaunchContinue` nodes without regrouping them. A caller that reuses a
transformed tree remains safe.

### 5.3 Entry and genericity

- `apply_bind_chain_analysis` transforms each single-signature `Defn` and each
  single-signature trait-impl method through `auto_schedule_defn`.
- Multi-signature definitions and methods are skipped; `auto_schedule_defn`
  treats reaching one as an invariant violation (`unreachable!`). §7 records
  the consequence.
- The pass is generic over the table's store parameters
  (`SymbolTables<C, L>`). It reads only fields independent of `C` (callable
  origin and import resolution), so it runs directly against the session's
  live tables with no projection and no `cranelisp-types` change.

### 5.4 Cost

Without loaded platform effects every step classifies `Sequential` and no node
is rewritten, leaving one AST walk per body. Add a presence guard only if a
measured regression appears. Any guard must test table contents, never scan
source syntax.

### 5.5 Kill switch

`CRANELISP_NO_IO_SCHEDULE` disables the pass when present; the default is on.
It is read once per cluster at the seam, and unit tests call the pass
directly. It is deliberately separate from the lenient-evaluation switch
(`CRANELISP_NO_LENIENT`), which governs pure `let` parallelism: the two
features have different safety arguments and are debugged separately.

## 6. Guarantees and where each is witnessed

| Case | Required outcome | Enforced by | Witness |
|---|---|---|---|
| C1 independent non-`Sequential` pair | `ParBind` | `rebuild_chain`, `flush_par_group` | unit tests; `tests/spec_10_io.rs` diff-token parallelism |
| C2 data-dependent step | stays sequential | `is_independent` over `free_vars_expr` | unit tests (application-argument and `let`-RHS forms) |
| C3 same-handle pair | never independent | E2-style value sharing: same handle ⇒ shared free variable ⇒ dependent | `tests/spec_10_io.rs` same-token serialisation |
| C4 `Sequential` pair | stays sequential | the class gate in `rebuild_chain` | unit tests; `tests/spec_10_io.rs` sequential-class e2e |
| C5 single eligible step | no `ParBind` (sequential or launch) | `flush_par_group` | unit tests |
| C6 non-platform effect | `Sequential` | `classify_expr` | unit tests |
| Mode uniformity | same grouping in every mode | the single seam (§5.1) | `auto_io_par_grouping_uniform_across_modes` observes run and linked execution |

- **Ordering between effects on one handle is the inference's job.** Under the
  handle model of `design/arch/effect-concurrency.md` §4.1.1 the runtime does
  not see tokens and cannot re-serialise branches. Two effects on the same
  explicit handle share that handle as a free variable, so the pass never
  makes them independent; they lower in source order. The permit supplies
  exclusion; the chain supplies order.
- **Deferred, not promised:** two effects on different handles that the
  platform projects onto one shared token look independent, so the pass may
  group them. The runtime still provides exclusion, but source order across
  distinct handles is deferred to a future API
  (`design/arch/effect-concurrency.md` §8.2).
- The REPL leg of mode uniformity rests on the shared seam rather than a
  REPL-mode witness; `tests/plan/PLAN.md` records that evidence limit.

## 7. Open obligations

- **G1 — free-variable completeness.** C2 soundness depends on
  `free_vars_expr` reporting every free variable in every expression variant.
  Unit coverage exercises the application-argument and `let`-RHS forms only.
  The `If`, `Match`, `Lambda`, vector-literal, annotation,
  constructor-argument and nested `ParBind` forms are unpinned, and
  `cranelisp-types` has no direct `free_vars_expr` tests. The function is
  `/arch`-owned; evidence allocation is `qa`'s.
- **Launched-work cancellation.** This pass emits no context boundary (§3.7),
  and nothing here changes for cancellation. Realising the ownership rules of
  `spec/10-io.md` §10.12.7 items 5–6 and §10.12.9 is a runtime obligation,
  tracked by
  `sprints/actions/ACT-0977-scoped-launched-work-cancellation-evidence.md`.

- **Multi-signature bodies are never scheduled.** A `bind!` chain inside a
  multi-clause definition or impl method is left sequential (§5.3). Sequential
  execution is observationally safe, but `spec/10-io.md` §10.12 says the
  compiler MUST insert `Par` nodes for eligible pairs, so this is a
  conformance gap for `qa` intake.
