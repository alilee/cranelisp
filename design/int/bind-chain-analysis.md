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

1. **Lexical binders.** A bare spelling resolves to a local when a binder
   whose region contains the callee spells it (§3.8). A binder is always
   bare (spec §4.3, §4.5.2), so a qualified spelling is never a local.
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
  That is `qa`'s cell T-1065-f, which cannot yet execute this clause: its
  program is refused in every mode by ACT-1075, a separate
  typecheck-to-codegen defect carried by its failing tests
  ([register](../../tests/plan/s124-evidence-delta.md#1415-defects-carried-by-failing-tests)),
  with the pass disabled. Until
  ACT-1075 is corrected the assertion remains a debt. The C8 module rows do
  not discharge it: their fixtures commit the imports themselves, so they
  show only that the pass declines once an import is committed.
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
  as the platform-effect lookup once did. It ignores module aliases and
  locals, and it is a second chain beside the one typecheck uses.

### 3.2 Chain collection

Chain collection flattens the nesting into ordered steps and the terminal
body. Each nested step passes the §3.1 test on its own; the first application
that fails it is the terminal body, transformed recursively. A step records
the binder, its parameter annotation, the effect expression, and the three
written nodes it consumes: the `bind` application's span, the callee node
itself (its spelling and span together), and the continuation lambda's span. Reconstruction reads each node's identity from
that record (§3.6).

### 3.3 Scheduling classification

A step's effect has a scheduling class only when it is a direct call whose
callee resolves to a platform effect (§4). Anything else — a user-function
wrapper, a nested bind, a `let`, a literal — is `Sequential`. The pass never looks inside function bodies.

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
own spans. No published type depends on this rule.

Why it binds: when one span named the application, its callee and its
lambda, typecheck's type for the application overwrote the lambda's, the
lambda's parameter reached the backend untyped, and a parameter the body
never read was never released (ACT-1050). A pre-typecheck rewrite that mints
or shares a span is a standing review reject
([int §12.1](int.md#121-standing-review-rejects), item 19).

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
   as a member of a launched sub-tree, never as the launched root. The leaf
   is the callee whose §3.1 resolution is the identity bootstrap installs
   for `sleep`. It is not identified by its
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

### 3.8 Binder scope (ACT-1077)

The pass carries the binders in scope as it recurses. Every callee read —
chain recognition (§3.1), effect classification (§3.3), and the launch leaf
and sub-tree positions (§3.7) — uses the scope of the written position it
reads. A local therefore declines a callee only where the program itself
would resolve that spelling to it.

| Binder | Region |
|---|---|
| A definition variant's parameters | that variant's body |
| A lambda's parameters | the lambda's body |
| A `let` binding | the later bindings' values and the body (spec §4.3) |
| A match arm's pattern binders | that arm's body only |
| A `ParBind` binding | the `ParBind`'s body only |
| A chain step's binder | the later steps and the terminal body: the lambda row, read through the nesting the user wrote |

Every other expression form binds nothing. The binders are stated in the
same exhaustive match over `Expr` that the recursion uses, so a new
expression variant does not compile until its binders are stated.

- **A chain's scopes are prefixes.** Step *k*'s application and effect sit
  under the outer scope and binders 1 to *k*−1; the terminal body sits under
  all of them. A scope that grows on entry to a region and is truncated on
  exit gives each step its prefix without copying. Copying a whole set at
  each binder is quadratic in chain length and is not used. The
  representation is otherwise `dev`'s.
- **Shadowing needs no case of its own.** A spelling is local when any
  enclosing binder spells it.
- **The rewrite keeps every callee's scope.** A grouped effect has no group
  or earlier binder free (§3.4), and a callee `Var` is a free variable, so
  grouping moves no callee out from under a binder that spells it. A launch
  drops only its own binder, which E1 requires to be unused. Typecheck,
  which resolves the rebuilt nodes, therefore sees the locals the pass read.

Rejected alternatives:

- **One binder set per definition**, as built from `32e434dc` to S124's
  correction. It is sound but declines a callee in chains the local cannot
  reach; it caused ACT-1077, a regression against the earlier spelling
  test.
- **Renaming locals apart before the pass.** It rewrites user spellings that
  diagnostics and typecheck's span-keyed records read.

## 4. Platform scheduling data

- **One entry per platform function.** Platform load installs each manifest
  function in its `platform.{name}` module as a callable whose
  `CallableOrigin::PlatformEffect { scheduling_class, poll_shape }` carries the
  manifest's scheduling facts. There is no side registry.
- **Lookup follows resolution.** A direct call's callee is resolved once, by
  §3.1's three layers. Only a terminal `PlatformEffect` yields a class.
  Anything else, including a local, a cluster declaration or a failed
  resolution, classifies `Sequential`. A local spelled like a platform
  function is therefore never taken for the effect; the spelling lookup this
  replaced grouped two calls of such a local and aborted at run time
  (REPRO-1065-e).
- **No bare-name fallback.** Matching an unqualified symbol would let two
  platforms that export the same name collide.
- **One record for both decisions.** The one callee answer supplies both the
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
- **Precondition: the module's table exists.** The scope's first hop is the
  module's committed table. Both entries to `process_cluster_once`, the
  worker's cluster driver (`src/cluster.rs`) and REPL evaluation
  (`src/eval.rs`), ensure that table before the cluster runs, so the pass
  always runs. The seam does not create a table: with none it declines and
  the cluster compiles sequentially, which is sound (§1). This holds by
  reading the two entries, not by construction. A third entry that skipped
  the ensure would compile its clusters unscheduled, and its falsifier is a
  scheduling witness (C1) driven through that entry.
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

- `apply_bind_chain_analysis` transforms every `Defn` and every trait-impl
  method through `auto_schedule_defn`, which transforms each variant's body
  separately with that variant's parameters as the root scope (§3.8). A
  multi-signature definition is therefore scheduled clause by clause, as
  spec §10.12.1 requires of every body (ACT-0981). No caller filters by
  signature count, and the pass has no multi-signature invariant to assert.
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
| C6 non-platform effect | `Sequential` | the callee resolution (§3.1, §4) | unit tests; C8's platform-spelled local row |
| Mode uniformity | same grouping in every mode | the single seam (§5.1) | `auto_io_par_grouping_uniform_across_modes` observes run and linked execution |
| C7 node identity | no output span on two nodes; each rebuilt node's span is its written node's | the step record and a reconstruction with no span argument (§3.6) | C7 module rows in `src/bind_chain_analysis/identity_tests.rs`, one per rewrite shape on distinct-span fixtures; `tests/bind_unused_heap_argument.rs` end to end |
| C8 callee identity | a step only where the callee resolves to the primitive; every other callee left as written | §3.1's three layers and the one bootstrap identity | C8 module rows in `src/bind_chain_analysis/identity_tests.rs`; `bootstrap.rs`'s row pinning both identities to the installed entries; REPRO-1065-a to c and e in `tests/spec_10_io.rs`. Owed: T-1065-d (renamed import, after row D3) and T-1065-f (§3.1's import assertion, masked by ACT-1075) |
| C9 binder scope | a local declines a callee only inside its region; elsewhere in the definition the callee resolves through layers 2 and 3 | scope carried through the recursion (§3.8) | C9 module rows (§7); `tests/spec_10_io.rs::s124_1077_unrelated_bind_local_keeps_overlap` |
| C10 every body | each clause of a multi-signature definition is scheduled like a single-signature body | per-variant entry (§5.3) | the C10 module row (§7); `tests/spec_10_io.rs::s124_0981_multi_signature_overlap` |

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

- **ACT-1065 — the renamed import (row D3).** §3.1 and §3.6 are in source
  at `32e434dc` (ACT-1050, ACT-1065). One recognition remains: once row D3
  lets the primitive be imported under another name, that name must group
  as the primitive does (spec §10.12.1). §3.1 needs no change for it,
  because layer 3 resolves a renamed import to its target. `dev` adds the
  C8 module row for that subject in D3's change-set, and `qa`'s T-1065-d
  observes it end to end.
- **§3.1's import assertion is unwitnessed end to end** until ACT-1075 is
  corrected and T-1065-f executes (§3.1, *Asserted with a named falsifier*).
- **S124 correction: binder scope and every body (ACT-1077, ACT-0981).**
  Designed 2026-11-19; not in source at `e6ad49f1`. ACT-1077 is a
  regression S124 caused, owed under *no decay*
  ([delivery principles](../../sprints/METHOD.md#delivery-principles)).
  ACT-0981 is taken under *clean house*: once the scope is rooted per
  variant (§3.8), scheduling a multi-signature body is the removal of two
  signature-count guards and an `unreachable!`.
  - **`dev`(`src/`) builds**, in one change-set, failing rows first:
    §3.8's scope in `src/bind_chain_analysis.rs`, replacing
    `collect_binders` and the pass's per-definition set; §5.3's
    per-variant entry there; and the removal of the two guards in
    `session_setup::apply_bind_chain_analysis`.
  - **C9 module rows**, in `src/bind_chain_analysis/identity_tests.rs`, one
    per region rule that differs from "the whole body". Each fixture has a
    local spelled `bind` and an independent platform pair:
    1. the local bound by a `let` in one `if` arm, the pair in the other:
       the pair groups (ACT-1077's subject);
    2. a `let` whose first binding's value holds the pair and whose second
       binding is the local: the pair groups; the same chain in the body
       stays as written;
    3. a match arm binding the local, the pair in another arm: the pair
       groups; the same chain in the binding arm stays as written;
    4. a chain whose first step's binder is the local: its later
       `(bind …)` stays as written.
  - **C10 module row**, same file: a two-clause definition with the pair in
    each clause and the local as a parameter of one clause only. The other
    clause's pair groups, and the clause with the parameter stays as
    written.
  - **Turn green:** `tests/spec_10_io.rs::s124_1077_unrelated_bind_local_keeps_overlap`
    (`qa`'s cell beside REPRO-0981) and
    `tests/spec_10_io.rs::s124_0981_multi_signature_overlap`.
  - **Stay green:** the C7 and C8 module rows, including
    `parameter_named_bind_is_not_the_primitive`,
    `let_named_bind_is_not_the_primitive`,
    `parameter_named_like_a_platform_effect_is_not_scheduled` and
    `local_named_sleep_is_not_the_timer_leaf`; REPRO-1065-a to c and e;
    `auto_io_par_grouping_uniform_across_modes`; and
    `tests/bind_unused_heap_argument.rs`.
  - **Stop rule for the ACT-0981 half.** Typecheck and the backend already
    accept `ParBind` and `LaunchContinue` in any body; this is asserted, and
    REPRO-0981's checked values and exit status are its falsifier. If a
    clause's rewritten body is refused or yields a wrong value, `dev`
    restores the two guards and the `unreachable!`, deletes the C10 row,
    and reports. ACT-0981 then stays carried on its failing test,
    ACT-1077's correction lands without it, and `design`(int) restates
    §5.3.

- **G1 — free-variable completeness.** C2 soundness depends on
  `free_vars_expr` reporting every free variable in every expression variant.
  Unit coverage exercises the application-argument and `let`-RHS forms only.
  The `If`, `Match`, `Lambda`, vector-literal, annotation,
  constructor-argument and nested `ParBind` forms are unpinned, and
  `cranelisp-types` has no direct `free_vars_expr` tests. The function is
  `/arch`-owned; evidence allocation is `qa`'s.
- **Launched-work cancellation.** This pass emits no context boundary (§3.7),
  and nothing here changes for cancellation. Realising the ownership rules of
  `spec/10-io.md` §10.12.7 items 5–6 and §10.12.9 is a runtime obligation:
  defect ACT-0977, carried by the failing `s124_0977_*` cells in
  `tests/concurrency_cancellation.rs`
  ([register](../../tests/plan/s124-evidence-delta.md#1415-defects-carried-by-failing-tests)).
