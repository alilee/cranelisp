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
  A chain appears as nested `Apply(callee, [io_expr, Lambda([name], body)])`
  whose callee resolves to the `bind` primitive (§3.1), under whatever
  spelling reaches it.
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
  - **The pass mints no span.** Every node it builds carries the span of the
    written node it replaces in the same role, and no span appears on two
    nodes of its output (§3.6). Typecheck records expression types by span, so
    two nodes sharing one span share one type: the rewrite would hand a
    continuation the application's type.

## 3. Algorithm (`src/bind_chain_analysis.rs`)

### 3.1 Pattern recognition

A chain step is an `Apply` with two arguments, the second a one-parameter
lambda, whose callee is the `bind` primitive. The callee's identity is a
resolution, never its spelling (Principle 24): spec §4.6 makes an application
call what its callee resolves to, and spec §8.6.4 lets a module declare any
unqualified name, `bind` included (ACT-1065).

**One callee resolution for every identity the pass reads.** The pass asks one
question of a callee `Var`: what does it resolve to here? The bind primitive
(§3.1), a platform effect's descriptor (§4) and the `sleep` timer leaf (§3.7)
are each read from that one answer. The pass keeps no other spelling test and
no other chain walk. The answer comes from three layers, in order:

1. **Lexical binders.** A bare spelling bound by any binder in the definition
   being transformed resolves to that local. The binders are the parameters,
   lambda parameters, `let` bindings, match-pattern binders, `ParBind`
   bindings and chain binders. The set is collected once per definition and
   ignores nesting, so a local `bind` in one arm also declines the primitive
   in another. That over-approximation is sound (§1) and removes scope
   threading from a pass that otherwise needs none.
2. **The cluster's own declarations.** A bare spelling, or one qualified by
   the current module, that the cluster's program declares resolves to that
   declaration. The program reaches the pass before typecheck commits it, so
   the committed table cannot answer for it. Its declared names are every
   `Defn` name, trait-declaration method and type-definition constructor and
   accessor in `final_working`.
3. **The committed scope.** Otherwise the callee is resolved by
   `cranelisp_types::ResolutionScope::resolve` over the committed scope that
   macro-head recognition builds (`expander::committed_scope`). That gives the
   imports, renamed imports, re-exports, module aliases, qualification and the
   prelude fallback typecheck applies, through the same types-owned chain.
   The root already consumes `ResolutionScope`, so this needs no
   public-API change.

The callee is the primitive only when layer 3 answers and the resolved
canonical identity is the one int's bootstrap installs for `bind`. That
identity is defined once, beside the installer in `src/bootstrap.rs`, and the
installer and the pass both read it. Its literal names a synthetic module at
its construction site, which Principle 19 permits. Every other outcome
declines: a local, a cluster declaration, a different terminal, an
ambiguous spelling, a private name, an unknown module or a miss. Declining
leaves the application as the user wrote it, which is sound (§1).

- **Typecheck agrees by construction, except where the pass declines.**
  Typecheck resolves the rebuilt callee node, the user's own (§3.6), through
  the same scope chain, with its staged view adding exactly layer 2. Layers 1
  and 2 can therefore only turn a primitive answer into a decline, never the
  reverse.
- **Asserted with a named falsifier:** the cluster's imports are in the
  committed table before the cluster finalises
  ([int §6.10](int.md#610-the-import-generation)). If one were only staged,
  layer 3 would miss it and could fall back to the prelude's `bind`. The
  falsifier is a module that imports a user `bind` and whose prelude exports
  the primitive, compiled in one cluster: the user's function must run.
- **No import is uncommitted because of a cycle.** An imported module is
  compiled before its importer (spec §8.10.3), and a cycle among modules
  still loading is refused at the import that closes it
  ([int §6.2](int.md#62-cluster-orchestration)), before the importer's
  cluster finalises. A cycle closed against modules already loaded imports
  only committed names, and its generation is refused at publication
  ([int §6.11](int.md#611-module-cycles-at-publication)), so the pass's
  output is discarded. The falsifier above therefore covers every imported
  name the pass reads, and no cycle case needs a cell of its own.

Rejected alternatives:

- **Keep the spelling test and exclude user names.** Every exclusion is a
  second, partial resolver, and a renamed import of the primitive (row D3)
  would still go unscheduled, against spec §10.12.1.
- **Run the pass after typecheck and read the call's resolution.** `ParBind`
  and `LaunchContinue` must themselves be typechecked (§5.1), so the pass
  would need a second typecheck.
- **Have typecheck refuse a rewrite whose callee is not the primitive.** The
  sequential program is the correct answer in that case, so the refusal
  would need a fallback carried on the published `Expr`, which is a types
  change for a decision the pass can make itself.
- **Resolve with `resolve_terminal_entry_and_home` from a split spelling**,
  as §4 did. It ignores module aliases and locals, and it is a second chain
  beside the one typecheck uses.

### 3.2 Chain collection

`collect_bind_chain` flattens the nesting into ordered steps and the terminal
body. Each nested step passes the §3.1 test on its own; the first application
that fails it is the terminal body, transformed recursively. A step records the binder, its parameter annotation, the effect
expression, and the three written nodes it consumes: the `bind` application's
span, the callee node itself (its spelling and span together), and the
continuation lambda's span. Reconstruction reads each node's identity from
that record (§3.6).

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

**Node identity.** A sequential step is rebuilt as the triple the user wrote:
the application under its own span, the recorded callee node, and the lambda
under its own span, with only the lambda body replaced. Reconstruction takes
no span argument, so it cannot give a rebuilt node any span but the one its
step recorded. A `ParBind` or `LaunchContinue` takes the span of the first
application it consumes; that application, its callee and its lambda leave
the tree, so the span stays unique. Nodes the pass does not consume keep their
own spans.

At `4b58ab93` the source does not hold this: `make_bind` gives the callee, the
lambda and the application one span, the application's. Typecheck's type for
the application then overwrites the lambda's, the lambda's parameter reaches
the backend untyped, and a parameter the body never reads is never released
(ACT-1050). The correction is this section; it changes no published type.

Rejected alternatives:

- **Fresh synthetic spans for rebuilt nodes.** They are unique, but they move
  diagnostics and the lambda's span-derived symbol off the written source,
  while the written spans are already in hand.
- **Mutating the written nodes in place.** Grouping removes applications and
  lambdas from the tree, so a retained shell needs a placeholder body, a
  fictitious state the step record avoids. Before typecheck the application
  and the lambda carry nothing but their span, so rebuilding them from the
  record loses nothing.
- **Keying typecheck's tables by node identity.** It changes the published
  `Expr` and every span-keyed sidecar across crates to repair one producer.
- **A collision check in typecheck's recorder.** The recorder legitimately
  re-records one node's span, and a span alone cannot tell that from two nodes.
- **Typing the parameter in the backend from `bind`'s scheme.** It fabricates a
  category the producer did not supply (release contract R-2).

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
   launched root. The leaf is the callee whose §3.1 resolution is the
   identity bootstrap installs for `sleep`. It is not identified by its
   lifecycle state: `bind`, `race`, `select` and `sleep` are installed as
   host-promised with no host symbol behind them (see
   [int §16.0](int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21),
   ACT-1063). The sub-tree's steps are found with §3.1's test, so a user's
   `bind` inside a launched sub-tree is an effect position and is refused.

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
- **Lookup follows resolution.** A direct call's callee is resolved once, by
  §3.1's three layers. Only a terminal `PlatformEffect` yields a class.
  Anything else, including a local, a cluster declaration or a failed
  resolution, classifies `Sequential`. At `4b58ab93` the source resolves a
  split spelling with `cranelisp_types::resolve_terminal_entry_and_home` and
  no lexical layer. A local that shadows a platform function's name would
  then be classified as that effect and grouped. That is predicted from
  source, not observed, and is `qa` intake. The ACT-1065 change-set removes
  that lookup (§7).
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
  `check_program_compat`. The seam supplies the cluster's committed
  resolution scope (§3.1, layer 3).
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
  (`SymbolTables<C, L>`), as `ResolutionScope` is. It reads only fields
  independent of `C` (callable origin and resolution), so it runs directly
  against the session's live tables with no projection and no
  `cranelisp-types` change.

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
| C7 node identity | no output span on two nodes; each rebuilt node's span is its written node's | the step record and a reconstruction with no span argument (§3.6) | owed: a module row over every rewrite shape, on fixtures whose nodes have distinct spans; `tests/bind_unused_heap_argument.rs` end to end |
| C8 callee identity | a step only where the callee resolves to the primitive; every other callee left as written | §3.1's three layers and the one bootstrap identity | owed: module rows below (§7); REPRO-1065 end to end |

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

- **ACT-1050 — node identity (designed S124, not in source at `4b58ab93`).**
  `dev` realises §3.6 in `src/bind_chain_analysis.rs` and adds C7's module
  row. The row's detection proof is the current `make_bind`: the rebuilt
  callee and lambda share the application's span. Its fixtures must give every
  input node its own span; the existing fixtures put `Span::SYNTHETIC` on
  every node, which no uniqueness check can pass. Shapes: one step, a
  two-step chain, a parallel group followed by a sequential step, a launched
  step, a chain inside an effect expression, and a chain under a lambda,
  match arm and `let`. Order: [int §16.0](int.md#160-open-binaryint-obligations-verified-against-source-2026-09-21).
- **ACT-1065 — callee identity (designed S124, not in source at
  `4b58ab93`).** `is_bind_var` takes any `Var` spelled `bind` or ending
  `/bind` for the primitive, so a user's `bind` is grouped or launched and
  the program changes. `qa` classified it a defect: a silent wrong value and a
  wrong reject. §3.6 alone removes the reject but not the wrong value, as
  `qa` observed; §3.1 removes both.
  - `dev` realises §3.1 in `src/bind_chain_analysis.rs` in the same
    change-set as ACT-1050, because both edit chain collection and
    reconstruction. The pass takes the committed scope from the seam
    (§5.1), built once per cluster with the construction macro recognition
    uses. The one bootstrap identity for `bind` and `sleep` sits beside their
    installers.
  - Deleted in that change-set: the spelling test, `effect_descriptor`'s
    split-spelling lookup, `resolves_to_sleep_extern` and the test-only
    `scheduling_of`. §4's lookup and §3.7's timer leaf read §3.1's answer.
  - Module rows (C8), each with distinct-span fixtures. Subjects that must
    decline: a user `bind` declared in the cluster, the same `bind` committed
    by an earlier turn, a parameter or `let` named `bind`, a self-qualified
    user `bind`, and an ambiguous spelling. Subjects that must be recognised:
    the primitive through a glob import, the prelude fallback, a qualified
    `primitives/bind` and a module alias, and once row D3 lands a renamed
    import. Detection proof: the present `is_bind_var` recognises every
    declining subject. Negative leg: each recognised subject still groups
    as it does today.
  - Emission acceptance adds to ACT-1050's: a function whose callee is not
    the primitive must emit its call unchanged from the user's source, and
    no function that calls the primitive may change for this reason.

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
