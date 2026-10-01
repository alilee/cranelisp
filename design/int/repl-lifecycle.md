# REPL lifecycle

Int's design for the file watcher, the session lock and REPL exit, `/reset`,
the `/sh` shell escape, REPL cache use, `--link` wiring and project-root
resolution. The normative
experience is `repl/spec/00-cli-invocation.md`, `13-shell-escape.md`,
`14-file-watching.md` and `15-session-persistence.md`. Project configuration
is [cranelisp-toml.md](cranelisp-toml.md).

## 1. File watching

`src/watch.rs::FileWatcher` wraps notify's `RecommendedWatcher`. The session
holds it as `CompilerSession.watcher`, which is absent if the OS watcher cannot
start.

### 1.1 What is watched

The watcher watches the parent directory of every loaded source file,
non-recursively. It watches directories rather than files, because editors
that save by atomic rename would lose a per-file watch.

- `init_watcher` arms it once modules have loaded at start-up.
- `sync_watcher` runs after every REPL or agent turn and adds the directories
  of newly loaded files.

### 1.2 Poll and reload

- **Poll points.** `sync_watcher` then `poll_and_reload`, which drains queued
  events with a non-blocking `try_recv`, run at two points, and their
  notifications print at each:
  - **Before each turn is admitted** (review N1): once a complete input has
    been read and before anything dispatches it, the agent route, slash
    commands, admission and the end-of-input flush included. A save made
    while the REPL sat idle at the prompt is therefore reloaded before the
    turn runs: the turn observes the rebuilt module, a failure locks the
    session before admission, and a definition then regenerates from the
    rebuilt generation (`14-file-watching.md` §14.2, "a save between turns is
    reloaded before the next evaluation"). Without it, a definition turn
    regenerated first, its own write became the watcher's baseline, and the
    user's save was lost.
  - **After each turn and before the next prompt**, as before, so a save
    made during a turn is reported eagerly at the prompt boundary.

  A poll with no queued event costs one `try_recv`, so the extra point is
  cheap. It cannot see a save whose event is not yet delivered, or one that
  lands during the turn; the write chokepoint covers those
  ([§1.3.1](#131-session-lock), Write chokepoint).
- **Filter.** The watcher keeps only create and modify events on `.cl` files,
  excluding `.cl.tmp`, with canonical paths.
- **Content hash: one record of what the session last saw** (review N2;
  Principle 7). `SharedState.recorded_sources` maps each source file the
  session has loaded or written to its state: its source hash, or
  **unreadable**. It is the only such record. The watcher keeps no baseline
  of its own, and the write chokepoint reads the same map
  ([§1.3.1](#131-session-lock), Write chokepoint).
  - **Writers.** Every read that loads a module's source records the state
    it read, on whichever thread reads it: entry registration, the shared
    dependency prologue `register_dep` (an `import` or `export`, a qualified
    reference, a `mod` child, the prelude), the cache-hit restore, which
    already reads and hashes the source it validates against, and the
    rebuild's read in `reload_module`. A failed read records unreadable.
    Regeneration records the state it wrote. Nothing else writes it; a scan
    that reads a file without loading it, such as the static import-closure
    walk or the index worker, does not.
  - **The watcher compares, it does not record.** A candidate is changed when
    its on-disk state differs from its recorded state. The poll does not
    update the record: the reload's own read does, so the record always
    names the source the session's generation was built from or wrote. A
    file with no recorded state was never loaded and is not a change (§14.1:
    a new file does nothing until it is referenced). `sync_watcher` adds
    directory watches and records no file state.
  - **First sight is a check** (as built 2026-10-02). A save that lands
    before a file's directory is watched queues no OS event. So a file the
    watcher sees for the first time is a candidate at the next poll, and is
    compared with its record like any event's file. The watcher keeps only
    which files it has seen and which it first saw since the last poll; an
    unchanged file is not reloaded.
  - **Why one record.** With a watcher baseline recorded at first sight, a
    save landing between a load's read and the first `sync_watcher` became
    that baseline: it was never reloaded, while the chokepoint, comparing
    against the load's record, refused every later write with a false
    "will be reloaded" warning, and the session's definitions were lost at
    exit (N2). With one record, that save differs from the load's read, the
    next poll reloads it, and the chokepoint and the watcher always agree.
    The same record answers R1: an entry unreadable at startup is recorded
    unreadable, so its first readable save is a change and releases the
    lock.
  - **An unreadable save is a change.** A candidate that exists but cannot
    be read, for example invalid UTF-8 or permission denied, differs from a
    recorded hash. Its rebuild fails at the read, after the prologue, and
    records unreadable, so the module stands failed with a located read
    error and the session locks; the chokepoint then keeps its bytes (R3;
    `14-file-watching.md` §14.5, a save that leaves the loaded program
    uncompilable, with the user's 2026-10-01 ruling that an uncompilable file
    change locks). A repeated unreadable event matches the record and does
    nothing.
  - **A missing file is not a change.** A candidate that no longer exists is
    skipped, as before: a delete, or the moment between an editor's write and
    rename. The module keeps its generation. Spec §14 names no behaviour for
    deleting a loaded file; that question is routed to `spec` through
    `sprint` and this rule stands until it is answered.
- **Reload edges.** One private predicate answers "module A depends on module
  B" for selection, ordering and the order check (Principle 7). A's edges are:
  - each `import` target that loads and each `export` target, resolved
    through A's declared children
    ([int §6.9](int.md#69-bare-module-names-in-import-and-export)). A null
    import loads nothing (spec §8.3.7) and is no edge; a use through it is
    recorded below;
  - `prelude`, when A's fallback bit is on
    ([int §6.12](int.md#612-the-implicit-prelude-dependency)). A module the
    prelude reaches with its bit on is a cycle that the static gate or the
    publication check refuses, so the edge never makes a live order
    unsettleable;
  - A's recorded edges, `cache::dependency_record::recorded_edges`: callee
    modules and lookup dependencies. These carry qualified function, type,
    trait, constructor, pattern, accessor and macro-head references, including
    through a re-exporter ([int §7.6.1–§7.6.2](int.md#76-dependency-record-and-validity));
  - while A holds an established reference, the same edges of that reference
    ([session transaction §7.3.2](session-transaction.md#732-the-established-reference)).
    A failed compile records neither callees nor lookup dependencies, so this
    keeps a failed module reachable from the dependency whose repair releases
    it;
  - A's **failure dependencies** (§1.2.1): each module through which one of
    A's attempts failed since A last compiled. A module that has never
    compiled holds no reference, so without these its dependency's fix would
    never select it (ACT-1011).

  Declared children are not reload edges: a `mod` declaration drives loading
  and compiles no reference into the child. They remain cache-validity edges.
  Over-selection through a stale edge costs only a recompile. The graph covers
  every module that has a table or a failure-dependency record, because a
  startup-failed dependency has no table (§1.3.1).
- **Reload set.** The changed modules plus every module that reaches one of
  them transitively over reload edges. A dependent is admitted when
  `file_to_module` maps a file to it; any other is skipped
  ([session transaction §7.3.3](session-transaction.md#733-slot-reuse-and-the-plan-invariant)
  names the residual).
- **Order.** Condense the plan over the same edges and emit components
  dependency first; lexical order applies only inside a component and between
  unrelated components. The order is load-bearing: a whole-file rebuild
  reuses GOT slot indices, so a module compiled before a dependency the same
  plan rebuilds would call through reused slots.
- **Order check.** The plan is ordered from edges recorded before it runs. A
  changed root whose new source adds a reference to another plan member can
  therefore compile before it. After the plan runs, check each module it
  rebuilt successfully against its new edges. One that reaches a module this
  plan rebuilt later is rebuilt again, with its dependents, in a follow-on
  plan, until no such module remains. Each module's last outcome is its
  notification. With no new cross-reference it adds no work.
- **Cycles.** The publication check rejects the attempt that would close a
  module cycle ([int §6.11](int.md#611-module-cycles-at-publication)), so two
  cycle members never both compile. Each rebuild tells that check which
  modules this pass rebuilds after it; their pre-plan edges are not yet
  settled. A cycle created in a pass is therefore rejected at its
  last-rebuilt member. The follow-on then rebuilds the earlier members, and
  each ends as a restart on the saved files ends it:
  - a member that depends on the failed member waits (Waiting, below). It
    reaches the failed member over its reload edges, or its attempt is
    refused at the scheduler's fail-fast
    ([int §6.11](int.md#611-module-cycles-at-publication), Pass-0
    fail-fast on a failed module). A qualified reference that still resolves
    against the failed table is the exception: until int §6.11's
    failed-dependency refusal is realised, such a member compiles, and the
    session diverges from a restart (ACT-1016 Face 1);
  - a member that reaches the failed member only through the implicit prelude
    edge waits, because the injection refuses it against the failed
    prelude, at a restart as in the session. A member the failed prelude
    reaches is on the cycle and is attempted
    ([int §6.12](int.md#612-the-implicit-prelude-dependency), Refusal by a
    failed prelude);
  - a member that the follow-on rebuilds ahead of the failed member can
    compile, because the failed member is then unsettled. The failed member is
    then refused again, the follow-on recurs, and the recurrence stop fails
    both.
- **Recurrence stop.** A follow-on root set that recurs cannot arise from an
  acyclic set of successes; reaching it is the
  [§7.3.3](session-transaction.md#733-slot-reuse-and-the-plan-invariant)
  falsifier. The executor then fails every module of the recurring set, each
  joining the failed set (§1.3), with an error saying the reload order did
  not settle, and returns. It
  never reports success for them. The stop also bounds the loop, because the
  root sets are finite.
- **One executor.** Every reload of a saved file runs as a plan through one
  private executor: the watcher poll, `/mod`'s recompile of a cache-installed
  module (`session-persistence.md` §2.4.5), and the superseded T1 and T2
  residue ([session transaction §10](session-transaction.md#10-t1-and-module-grain-reload-superseded-residue)).
  A caller supplies roots; the executor adds dependents, orders, reloads each
  module, runs the order check and returns each module's outcome. The watcher
  prints every notification, `/mod` reports each failed module's, and T1 and
  T2 read their root's outcome. `reload_module` is visible only to the
  session's own modules, so no other caller can rebuild outside a plan.
- **Three outcomes.** Each plan member ends **rebuilt**, **failed** or
  **waiting**, and its last outcome in the pass is its status (§1.3). A
  rebuilt module notifies `[updated: <file>]`; a failed one notifies
  `[errors: <file>]` and joins the failed set; a waiting one notifies nothing
  and leaves the failed set (`14-file-watching.md` §14.5). Every module that
  comes to stand failed during the pass is reported, including one that is
  not a plan member: a module the pass newly loaded that fails
  ([§1.3.1](#131-session-lock), Set sites) notifies `[errors: <file>]` with its own error, after the plan's own
  outcomes (LQ-4, derived from §14.5's naming rule). Only a rebuilt
  outcome counts as success for the order check, `/mod`, T1 and T2.
- **Waiting.** A member waits when it depends on a module that stands
  failed. Two paths reach the one waiting state:
  - **Before its attempt.** A member that is not one of the caller's roots,
    and that reaches another module standing failed over the reload edges as
    they stand when its turn comes, is not attempted. A member standing
    failed itself is attempted when it reaches no other, because the change
    may repair it. Edges recorded by failures earlier in the same pass
    count, and so do a waiting module's failure dependencies, so waiting is
    transitive. The implicit prelude edge is followed like any import
    (spec §8.8.1), so a failing prelude makes every module with the fallback
    bit on wait (§14.5). The one exception is a cycle through the prelude:
    when the failed module is the prelude and the prelude reaches the member
    over the same reload edges, the member is a cycle member, not a
    dependent. It is attempted, and the cycle rules above decide it, as a
    restart does ([int §6.12](int.md#612-the-implicit-prelude-dependency),
    Refusal by a failed prelude).
  - **At its attempt.** A root is always attempted, because its saved
    source, not its previous edges, decides what it depends on. A save that
    removes the dependency, such as one that breaks a cycle, then compiles.
    An attempt refused because a dependency already stands `Failed` in the
    scheduler waits ([§1.3.1](#131-session-lock), Dependency refusal). That covers a root whose
    saved source still depends on a failed module, and any member whose new
    edge was not visible before the pass.
  - **Refused by a later member.** A refusal by a member that the same pass
    rebuilds later is not yet a settled fact: that member's failure is not
    its outcome, as the publication check also treats it
    ([int §6.11](int.md#611-module-cycles-at-publication)). The refused
    member's outcome is therefore deferred until the refusing member
    settles, and recorded only then (Principle 26):
    - the refusing member rebuilt: the refused member joins the follow-on
      roots beside the order check's, and is attempted again against the
      rebuilt generation. One save that repairs B and makes A newly import
      B therefore ends with both rebuilt, as a restart does;
    - the refusing member failed or waits: the refused member is classified
      by the refusal chain as it then stands (§1.3.1), so it waits when the
      chain ends at a module standing failed and otherwise stands failed.

    A deferred member is reported only by its final outcome. The recurrence
    stop bounds re-attempts, because a deferred member's follow-on set is
    one of the root sets it tracks. When the stop fires, each member of the
    recurring set reports that the reload order did not settle, with one
    exception: a member re-attempted after a deferral whose last attempt
    failed on a **cycle** keeps that error.
    - **Why the exception is sound.** The stop must report only what is true
      of the saved files. A refusal by a member that has since rebuilt is
      usually stale: the refuser's failure was a state of the pass, which its
      rebuild refuted. A cycle is a property of the saved sources. A rebuild
      does not refute it, and the recurrence confirms it, so a cycle error is
      true when the stop fires. This is what makes the ACT-1014 helper end
      (`helper_save_dropping_its_prelude_opt_out_is_refused_as_a_cycle`)
      name `x -> prelude -> x` as a restart does, where a uniform "did not
      settle" did not.
    - **Typed, not textual.** An attempt failed on a cycle when its failure
      came from a cycle site (the scheduler's wait-graph check, the static
      import-closure gate, the publication cycle check, cycle precedence at
      the failure exit, where the cycle diagnostic replaces the attempt's
      error ([int §6.12](int.md#612-the-implicit-prelude-dependency)), and a
      refusal chain that returns to the module), or from a refusal by a
      module whose own failure did. The scheduler records that fact per
      generation beside the refusing dependency and sets it at those sites.
      Every dependency refusal (the dependency-wait and Pass-0 fail-fast, the
      barrier fail-fast and the cascade) records through one shared site,
      which copies the flag from the refuser as it copies the refuser's
      error (as built 2026-10-02). Registration clears it. No error text is read.
    - **Not taken.** Classifying the recurring set by its refusal chain
      instead (option b) makes the refuser stand failed and the member wait,
      so the cycle is named in another file than a restart names. Changing
      the row (option c) would weaken ACT-1014's acceptance.
    - **Deferred only on each other.** Members whose refusing members are
      all deferred members of the same pass refused each other; none will
      settle first. They are classified from the last in plan order: it
      fails with the cycle diagnostic of the refusal chain, and the others
      then wait on it (§1.3.1, A refusal chain must end at a failure). The
      order is the plan's, so the outcome is deterministic.

  The waiting state is the same on both paths. The module's previous
  generation is displaced by the rebuild prologue
  ([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)),
  which pools its compiled owners. The failed dependency is recorded as its
  failure dependency (§1.2.1) and as its refusing dependency, and the
  scheduler holds it `Failed`, so a later load that reaches it is refused in
  turn. When the dependency compiles, its plan selects the waiting module
  through that record and rebuilds it.
  - **Why displace.** A failed rebuild's partial table can publish macro
    clauses into GOT slots that the failed module's previous generation
    used. Compiled code that still calls through those slots would reach a
    different callable, possibly of a different ABI. Macro expansion stays
    available while the session is locked, through `/mod` loads, `/type` and
    `/expand`, so a waiting module's previous code must not remain reachable
    by name. Keeping it would also leave introspection describing a
    generation compiled against a module that no longer holds it.
  - **Why roots are attempted.** Judged by its previous edges, a root whose
    save drops its reference to a failed module, for example to break a
    cycle, would wait on the very module its save releases, and the save
    would never take effect.
- **Reload.** `reload_module` waits for the module's in-flight pass to
  settle and runs the whole-file rebuild's prologue
  ([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild))
  before anything that can fail. It then re-reads the file, replaces the
  module's typecheck product with it, keeping the backing path and recording
  that text for verbatim slices, parses it, captures the preamble onto the
  fresh table, re-registers the module with whole-source provenance, and
  waits for that module's own outcome (§1.3). Regeneration writes to the recorded path
  (`session-persistence.md` §3.2), so a reload must not drop it.
- **Guards (module).**
  - A module whose only edge to the changed module is a recorded edge is
    selected, transitively; a module with no edge is not.
  - A dependent whose last rebuild failed on a qualified reference to the
    changed module is still selected when that module changes.
  - A qualified-reference-only dependent whose name sorts before its
    dependency is ordered after it.
  - Order check: two roots changed together, where the earlier-sorting one's
    new source adds a qualified call into the other, end with the caller
    rebuilt after the callee.
  - After startup recovery of the chain `user` → `lib` → `base` with `base`
    failing, the plan for `base` selects `lib` and `user`, in that order. The
    same holds when `lib` failed in its own source against `base` at any
    stage (§1.2.1): in Pass 0 on a name `base` lacks, in Pass 1 on a macro
    from `base`, and in its type pass, reaching `base` by `import`, by
    qualified reference and by an alias.
  - A plan whose root closes a qualified cycle ends with the refused member
    failed and every member that depends on it waiting; the acyclic twin
    succeeds.
  - When ACT-1016 Face 1 is realised, the same holds when a member rebuilt
    after the refused one uses only a name that the refused member's failed
    table still holds. In QA's shape, `a` re-exports `c/k`, `b` calls `a/k`,
    and a save of `a` adds a call to `b/g`. Then `a` ends failed and `b` and
    their dependent `user` wait, as a restart leaves them. The row pair is
    ACT-1016's.
  - A plan in which a follow-on member reaches the refused member only
    through the implicit prelude edge ends with that member waiting, as a
    restart leaves it; one the failed prelude reaches is attempted. Int
    §6.12's helper end is the cycle case.
  - Two roots changed together, where one drops its reference back to the
    other and the other adds a reference to it, both succeed: the later
    member's pre-plan edge does not reject the earlier one.
  - The recurrence stop, factored as a pure step, fails a planted recurring
    set and passes a non-recurring one.
  - Waiting (§1.3.2 lists the rows).
  - The prelude edge follows the fallback bit alone, and a null import adds
    no edge; the rows are in
    [int §6.12](int.md#612-the-implicit-prelude-dependency).

  End to end: FQR-1
  (`tests/repl_persist.rs::watch_qualified_caller_fails_on_removed_callee_until_it_is_restored`),
  FQR-2
  (`tests/repl_persist.rs::watch_qualified_type_dependent_locked_until_its_module_compiles`),
  FL-3,
  `tests/repl_persist.rs::watch_fix_of_dependency_failed_at_startup_recompiles_its_dependents`,
  `tests/repl_persist.rs::watch_fix_of_module_newly_imported_by_failing_save_recompiles_importer`,
  the own-source twins
  `tests/repl_persist.rs::watch_dependency_save_recompiles_importer_failed_at_startup_in_own_source`
  and `watch_dependency_save_recompiles_qualified_caller_failed_at_startup_in_own_source`,
  and `tests/repl_persist.rs::watch_save_closing_qualified_module_cycle_reports_circular_dependency`,
  each with its control.

#### 1.2.1 Failure dependencies

A failed attempt publishes nothing, and startup recovery purges a table that
never compiled (§1.3.1). The modules a failed attempt depended on must
therefore be recorded where selection can read them.

- **The fact.** The modules one attempt of module A depended on and failed
  with:
  - the dependency A waited on when that dependency failed (the cascade);
  - an already-failed dependency A met: the fail-fast at a dependency wait, at
    the signature barrier or at a Pass-0 declaration, or the publication
    check's failed-dependency refusal
    ([int §6.11](int.md#611-module-cycles-at-publication));
  - the next module on a cycle A closed (the scheduler's wait-graph check,
    the static import-closure gate, and the publication check of
    [int §6.11](int.md#611-module-cycles-at-publication));
  - for a whole-source attempt of A that fails, the attempt's dependencies
    (below). This covers a failure in A's own source at every stage.

  The last kind over-approximates, which selection tolerates: an extra module
  costs a recompile. It derives no compile-necessary identity, so Principle
  24's ban on identity scans does not apply. Without it, a module that never
  compiled and failed in its own source against `base` holds no edge to
  `base` once recovery purges its table (ACT-1011, own-source face), whatever
  stage failed and however it reached `base`.
- **The attempt failure exit.** Every stage of a cluster attempt returns
  through the one exit of `process_cluster_once`, in every mode:
  - the prologue: the static gate, Pass 0 and the barrier;
  - Pass 1 expansion and its macro checkpoints;
  - the final type pass and commit planning.

  When a whole-source attempt (a fresh load or a rebuild) fails, that exit
  adds the attempt's dependencies to A's scheduler record, once, before the
  error leaves. An increment's failure changes nothing and locks nothing, so
  it records nothing. The attempt's dependencies are the union of:
  - **Declarations in the attempt's forms.** Each `import` target that loads
    and each `export` target, resolved through the forms' declared children
    by the static gate's extraction, which reads exports for this reader.
    The forms are read, not the table, because Pass 0 records a declaration
    only after it resolves: a failing import is never on the table
    (FIXME 0548).
  - **The prelude**, when A's bit is on.
  - **A's live-table reload edges.** They hold macro clauses published at
    this attempt's earlier checkpoints, whose source a resumed attempt no
    longer carries.
  - **Qualified symbols.** The module of each qualified symbol written in
    the attempt's forms or in its expanded prefix, read through the alias
    carrier as qualified auto-loading reads it. The prefix holds each
    expansion made so far, so a reference a macro generated counts.
    Reader-quoted data is shielded by `cranelisp_types::quote_head`, the one quote
    classifier. Int §6.12's cycle precedence uses this one enumeration for
    each walked file, but substitutes through that file's own aliases rather
    than the carrier.
  - **Macro heads.** The macro-head modules the attempt accumulated
    ([int §7.6.2](int.md#762-lookup-dependencies)).

  The type pass keeps no lookup record on failure, so the exit reads what the
  attempt holds. The checked program is not needed: its qualified references
  are those of the expanded forms. The same exit applies int §6.12's cycle
  precedence, which can replace the error it returns.
  The cascade site stays, because a parked waiter runs no attempt. The cycle
  and fail-fast sites also stay and record their precise module; the exit's
  set contains it.
- **Scheduler record.** The scheduler keeps the set on A's module state for
  A's current generation, as it keeps the structural type refusal: each site
  above adds to it, and every registration or re-registration clears it. It
  is read only after A's own outcome.
- **Session record.** The session keeps, beside the failed set (§1.3) and
  the established reference, the union of A's failure dependencies since A
  last compiled.
  - `reload_module`'s failure branch adds the scheduler record of the
    reloaded module, whether it failed or waits.
  - A waiting member that the executor does not attempt adds the dependency
    it waits on (§1.2, Waiting).
  - A failed load's record (§1.3.1), at startup or from `/mod`, adds the
    record of every module its reset returns, including the entry, before
    anything forgets them.
  - Only `reload_module`'s success branch clears it. `/reset` keeps it.
- **Why a union.** A module blocked by `base`, then by `c`, still depends on
  `base`; over-selection costs a recompile, under-selection strands a
  failed or waiting module.
- **Module evidence (`dev`).** Arm each positive row RED on the pre-fix
  source where its seam exists.
  - Each of these failures of `lib` leaves `base` in `lib`'s scheduler record:
    - a Pass-0 failure through `(import [base [c]])` and through
      `(export [base [c]])`, while `base` lacks `c`;
    - a Pass-1 expansion failure on a macro imported from `base`;
    - a type failure reached by `(import [base [b]])`, by `base/b`, and
      through an import alias;
    - a type failure on `base/b` that only a macro's expansion wrote;
    - a macro-checkpoint type failure.
  - A failed load's record carries each record into the session record past
    the purge.
  - A qualified symbol inside quoted data adds no module.
  - An increment's failure leaves the record unchanged.
  - Planted absent at the exit, the §1.2 plan rows for the own-source twins
    and for the Pass-0 case go RED.

  End to end: the own-source twins and T4-p0
  (`tests/repl_persist.rs`, beside them;
  [QA allocation](../../tests/plan/s122-evidence-delta.md#design-residuals--adjudication-2026-09-30)).

### 1.3 Failed module and the session lock

A module whose attempt fails **stands failed**: it joins the session's
failed set, and the session is **locked** while that set is non-empty
([§1.3.1](#131-session-lock); `14-file-watching.md` §14.4–§14.6). A module
whose attempt waits ([§1.2](#12-poll-and-reload)) does not stand failed.

- **No last-known-good.** Every failure cause, a read or parse failure
  included, leaves the module with the fresh table the rebuild prologue
  installed, holding at most what the failed attempt published
  ([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)).
  Its previous definitions are unavailable (`14-file-watching.md` §14.5
  items 1–2).
- **Release of one module.** A later successful reload removes the module
  from the failed set and clears its established reference and failure
  dependencies.

**Outcome.** A reload's outcome, success or failure, is the reloaded module's
own terminal state, never another module's.

- **Wait.** `reload_module` waits on the reloaded module alone, through the
  scheduler's existing single-module in-memory wait. It fails with that
  module's own error when the module stands `Failed`, and succeeds once the
  module's in-memory publication is complete.
- **Why not the every-module wait.** That wait returns the first `Failed`
  module in map order. While another module still stands `Failed` from an
  earlier plan, it reports that module's error, possibly before this module
  settles, and turns a successful reload into a failure.
- **Other failed modules.** A module that still stands `Failed` is not this
  reload's outcome. It keeps its place in the failed set until its own
  reload, which the plan orders after its dependencies (§1.2).
- **Ordering.** The wait cannot end before the reloaded module settles. The
  worker publishes before it notifies in-memory completion, and it records a
  structural refusal before it reports the module failed (§1.3.1).
- **Coverage.** Every module the reload registers is a dependency of the
  reloaded module. The module's body waits at the signature barrier until each
  such dependency reaches a terminal typecheck pool. A source-compiled
  dependency notifies in-memory completion before it reaches `TypecheckDone`,
  so the single-module wait also covers it. Falsifier: a reload that adds an
  import of an unloaded module returns while that module's in-memory codegen
  is incomplete.
  - **Limit: a cache-restored dependency is not covered.** It enters
    `TypecheckDone` before its object is loaded into memory
    (`ModuleState::new_cached` in `src/scheduler.rs`). The barrier therefore
    opens, and the reload can return `Ok`, while that load is still pending.
    The eval path's per-module dependency wait has the same shape for a
    cache-restored transitive dependency. Grade: asserted with a named
    falsifier. The window is observed from source; its consequence, a
    `null-got-slot` crash, is unobserved. Falsifier: a reload that adds an
    import of a cache-restored module, then immediately calls that module's
    function through the reloaded module, crashes or observes an unloaded
    slot.
- **Liveness.** The wait ends because every path that would wait on a `Failed`
  module fails fast
  ([error cascade §4.1](step9-error-cascade.md#41-cascade-construction)). A
  stranded reloaded module would hang the reload in every session, not only
  in some map orders.
- **Guards.** In `src/session_v4/persistence_tests.rs`,
  `reload_beside_a_failed_module_succeeds_and_lifts_its_restart_marker`
  is the deterministic discriminator: a successful reload beside a `Failed`
  module succeeds and clears its marker.
  `structural_reload_beside_a_failed_module_reports_its_own_refusal` checks
  a refusal beside `Failed` modules. It detects the wrong outcome only when
  map order puts another failed module first. Neither
  exercises the coverage falsifier.

#### 1.3.1 Session lock

The session lock realises `14-file-watching.md` §14.5 (Session lock), with
§14.2 step 4 and §14.8 of that file, `15-session-persistence.md` §15.1 and
§15.2.3, `03-slash-commands.md` §3.9 and `00-cli-invocation.md` §0.1. One
record and one admission site serve every trigger.

- **State: the failed set.** The session holds one crate-private map,
  ordered by module, from each module standing failed to its record: the
  file whose save the session awaits, and the cause.
  - **Restart-required** carries the refused type: the reload was refused
    under §14.8 (the guard is
    [session transaction §2.6](session-transaction.md#26-type-re-establishment-repl-185-148)).
  - **Failed source** is every other failure.

  The session is locked exactly when the map is non-empty. No lock flag is
  stored, so "locked" and "a module stands failed" cannot disagree
  (Principle 20). The map replaces the former error set, per-module lock map
  and startup failed forms. It is session state and never persisted, so a
  restart compiles the saved source afresh (§14.6).
- **Status is the last attempt.** Each attempt of a module sets its entry.
  Rebuilt removes it, failed replaces it with this attempt's file and cause,
  and waiting removes it. A cause never carries over from an earlier attempt:
  a parse failure after a §14.8 refusal records failed source, and the
  refusal returns, naming its type, once the file parses again.
- **Failure and waiting.** An attempt fails for any cause in the module's
  own source or plan: a read, parse, type, codegen or publication failure, a
  §14.8 refusal, a cycle, or the recurrence stop (§1.2). An attempt refused
  because a dependency already stands `Failed` in the scheduler waits
  instead (§14.5: such a module "is not recompiled, reported or locked").
- **Dependency refusal.** The scheduler records, for the module's current
  generation, the dependency whose `Failed` state refused the attempt. Each
  site that refuses on that ground records it beside the failure dependency
  it already records (§1.2.1):
  - the dependency-wait and Pass-0 fail-fast, `refuse_failed_dependency`;
  - the signature-barrier fail-fast on a failed closure member. The eval
    thread's form refuses only increments, whose failure records nothing,
    so it needs no record;
  - the cascade to a failed module's waiters;
  - int §6.11's failed-dependency refusal at publication, once it is
    realised (ACT-1016 Face 1).

  Every registration clears the record, as it clears failure dependencies
  and the structural refusal record, and a reset carries it out. Cycle
  refusals, the publication cycle check, the recurrence stop and every
  failure in the module's own source record none. The record is the typed
  discriminator: nothing reads error text.
  - **A refusal chain must end at a failure.** An attempt waits only when its
    refusing dependency stands failed, or itself waits on a chain that ends at
    a module standing failed. A chain that returns to the refused module is a
    cycle whose check never ran, because a fail-fast fired first. The module
    then fails with the cycle diagnostic that `scheduler::CycleError::render`
    renders for the chain. A chain that stops at a module that neither
    stands failed nor was refused, or loops without returning to the module,
    is broken: the module stands failed with its own error. So every waiting
    module reaches a module standing failed, and the lock holds while any
    module waits.
- **Set sites.**
  - `reload_module`'s failure branch, which every executor caller reaches
    (§1.2): failed or waiting, from the dependency refusal record. It first
    runs the failed load's record (below) over the modules the attempt newly
    left `Failed`: those `Failed` after the attempt that were not `Failed`
    before it, other than the attempted module. A module the rebuild newly
    loaded that fails in its own source therefore stands failed, and the
    attempted module, refused by it, waits. Startup, `/mod` and a reload
    classify the same program state alike (Principle 7), the refusal names
    the file that needs the fix, and the scheduler holds no `Failed` module
    that the failed set does not account for.
  - The executor's recurrence stop, and its waiting members that it does not
    attempt.
  - A failed load's record, at startup and for `/mod` (below).

  A code turn's failure records nothing, including an import turn whose
  module fails to load: an increment's failure changes nothing (§15.1).
- **A dependency that fails before it registers (PF-1).** A dependency
  load reads and parses the dependency's file in `register_dep`, inside the
  attempt of the module that loads it and before the scheduler registers
  it. A read or parse failure there returned as the loader's own error, so
  the loader was named and the dependency was never `Failed`. That reached
  startup (the entry named for a failing `prelude.cl` or `lib.cl`), a reload
  that newly loads the module, and `/mod`.
  - **Spans (R2).** The dependency's error is located in the dependency's
    file. A parse error keeps its own span, which is an offset in that file.
    A read error has no position in that file, so its span is empty at the
    file's start; the loader's span is never carried into the dependency's
    file. The two are told apart by the error's kind, not by its file. The
    loader receives the same located error once, without a second wrapper,
    whether it is a startup load, a reload, a `/mod` load or a code turn.
  - **Rule.** A read or parse failure in `register_dep` is the
    dependency's failure. `register_dep`, the one prologue every dependency
    load shares (an `import` or `export`, a qualified reference, a declared
    `mod` child, the prelude injection and the cache-restore fallback),
    records the dependency `Failed` in the scheduler with that error. The
    error's location carries the dependency's file. It then refuses the
    loader through `refuse_failed_dependency`, which records the dependency
    as the loader's failure and refusing dependency. A rebuilt module whose
    read or parse fails is already recorded `Failed` the same way
    ([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)),
    so every pre-registration failure leaves one state.
  - **Effect.** The dependency is then an ordinary failed module that nothing
    refused: startup's reset, `/mod`'s reset and a reload's newly-`Failed`
    set each make it stand failed and name its file, and its loader waits.
    Its file is mapped for the watcher before the read, so its own save
    reloads it. Deviation 3, the `/mod` target that never registered, is
    the same case reached directly; `dev` may fold its special branch into
    this rule once the rows below stay green.
  - **Batch.** `--run`, `--test` and `--link` still exit 1 at `startup?`.
    Every fail-fast refusal keeps the refusing dependency's file in its
    location. The whole-world wait reports the root failure: a `Failed`
    module that nothing refused, the least by name among such modules, else
    the least `Failed` module by name. So the diagnostic is the dependency's
    own error in its own file, for example `lib.cl`, and it no longer
    depends on map order ([error cascade §3](step9-error-cascade.md#3-batch-propagation)).
- **A failed load's record.** One session operation handles a load that
  failed, in this order:
  1. **Reset only what the load left `Failed`.** A module that already stood
     `Failed` before the load, standing failed or waiting, keeps its
     scheduler record, so a later load that reaches it is still refused.
     Every failed load resets the modules it newly left `Failed`, whether or
     not it reached a dependency wait: a code turn and a `/mod` load that
     fail before the wait included, because a pre-registration failure
     (above) leaves the dependency `Failed` before any wait. The eval
     thread's dependency retry resets with the same exclusion. A code turn
     then discards the reset modules; it records nothing.
  2. Add each reset module's failure dependencies to the session record
     (§1.2.1).
  3. Classify each reset module by its dependency refusal record and the
     refusal-chain rule above: with no record it joins the failed set,
     keeping its recorded error for the report as the error value itself,
     with its own location, never a string rebuilt at a synthetic span
     (review A2); with one it waits. Every
     chain is judged against the failed set as it stands after the modules
     with no record have joined it, not as later classifications change it,
     so the outcome does not depend on the reset's order. A module whose
     chain is broken stands failed, but grounds no wait for another module
     classified in the same record.
  4. Purge the never-compiled tables, other than the entry's, by the one
     purge rule (`purge_never_compiled`). A kept never-compiled table reads
     as loaded to the `import` fast path and to qualified resolution, and
     the re-load from source then reports a different error from `--run`
     (ACT-1013).

  A purged module keeps its failed-set entry or failure dependencies and its
  watcher mapping, so its own save and its dependency's fix both select it.
- **Startup** (§15.2.3). When the REPL's startup load fails:
  1. **Entry outcome.** Before the reset, an entry the scheduler does not
     track failed before it registered, because its file does not parse. It
     stands failed with the startup error. A registered entry may still be
     settling when the start reports its first failed module, so recovery
     waits for the entry's own outcome before the reset; that outcome
     decides whether it compiled. An entry file
     that exists but cannot be read still registers as empty
     ([int §6.1.1](int.md#611-a-missing-entry-source-file), Not decided
     here; ACT-1019, carried to S123).
  2. **The failed load's record** runs over every module the start left
     `Failed`. A dependent of a module that failed at startup waits, as
     §14.5 requires.
  3. **Entry without a generation.** When the entry did not compile, failed
     or waiting, the rebuild prologue replaces its table with a fresh one
     that keeps its GOT
     ([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)).
     No definition survives, including a slot assignment or scheme that
     entry registration preloaded from the cache. The entry never compiled,
     so it holds no established reference
     ([session transaction §7.3.2](session-transaction.md#732-the-established-reference)).
     It is then re-registered empty as an increment. Recovery waits for that
     registration's in-memory outcome and then for the entry's terminal pool,
     because a worker marks in-memory completion before the pass settles, so
     the entry is eval-owned as on a healthy start.
  4. **Report.** Before the banner, print one notification per module
     standing failed, `[errors: <file>]` and its own error, in the failed
     set's order, built by the reload notice (§1.4). A waiting module is not
     reported.
  5. **Restore notice** (§15.2.2). It is emitted only when the entry
     compiled. Then every definition of the backing file restored, so its
     count is the file's definitions.

  The batch load is the only startup load, as it is for `--run`
  (Principle 11). There is no form-by-form re-drive, no failed-form record
  and no repair at the prompt. `--run`, `--test` and `--link` still exit 1
  at the same failure; only what follows it differs.
- **`/mod` load** (§3.9; [int §8.5.1](int.md#851-mod-target)). A failed load
  of a module `/mod` names runs the failed load's record. The target stands
  failed for a failure in its own source and waits when a dependency refused
  it. A target that never registered, because its file does not parse,
  stands failed with the load error, as an unregistered entry does at
  startup. `/mod` reports the target's load error and leaves the active
  module unchanged. A cache-installed module's recompile is a reload plan, so the
  executor's outcomes apply.
- **Turn admission.** `process_commands` is the one admission site. Typed
  input, the agent's submit (`submit_clean_form`) and the agent's pulls
  route through it. While the session is locked it refuses, leaving the
  session and every file unchanged:
  - every definition, expression and structural turn, whatever the current
    module;
  - a slash command that executes the program's code: `/time` and `/mem`
    with an expression, `/run-tests` and `/run-all-tests`.

  The classification is one exhaustive match over `ReplCommand` with no
  wildcard arm, so a new command cannot compile unclassified. Every other
  command is admitted, including the introspection commands, `/mem`
  without an expression, `/sh`, `/mod`, `/reset`, `/ask`, `/help` and
  `/quit`, as is bare special-form feedback.
  - **Criterion.** Running the program's code is refused; compiling and
    expanding are not. `/type` and `/expand` can run macro clauses, as a
    `/mod` load does. Waiting displaces every generation compiled against a
    failed module (§1.2), so each clause they can reach was compiled against
    the live generations it calls.
  - The agent's document edits bypass admission, so `run_document_edit` asks
    the lock before asking for consent.
- **Refusal.** The refusal names the file of each module standing failed,
  in the failed set's order and in the notification's file form (§1.4; §7
  gap 1), with each cause's remedy. Failed source: save a version that
  compiles. Restart-required: the type's saved structure takes effect only
  after a restart; restart, or save the live structure. The refusal is the
  same in every module. The wording is `dev`'s; as built it begins
  `Cannot evaluate: the session is locked while these files have errors:`
  and lists the files.
- **Write chokepoint.** `regenerate_backing_file` returns before reading or
  writing while the session is locked, whatever the current module. This
  covers every regeneration caller, including any that admission does not
  enumerate: `main.rs`, `agent/pull.rs` and the `redefine.rs` residue.
  - **Unseen save (review N1).** When the backing file exists and its state on
    disk, its content hash or unreadable, differs from the state the session
    last recorded for it (§1.2, Content hash), the chokepoint writes nothing.
    It warns on the write-failure channel that the file changed on disk and
    is kept, and leaves the file to the watcher: the next poll reloads it,
    or locks the session if it does not compile. The turn's definition stays
    in the session until that reload rebuilds the module from the saved
    file, and the warning says so. The user's bytes always win over the
    session's regeneration.
  - **The race guarded.** A save the pre-turn poll could not see: one whose
    event was not yet delivered when the turn was admitted, and one that
    lands during the turn's compile, evaluation or IO. Both reach the write
    with a recorded state that predates them.
  - **A missing file is written.** A backing file that does not exist is
    regenerated as before, so a first session creates it; deletion is the
    open `spec` question of §1.2.
  - **The recorded state.** It is `recorded_sources`, the one record the
    watcher also compares against (§1.2, Content hash). It exists whether or
    not the OS watcher started, so the check holds without a watcher.
  - **Cost.** One read and one hash of the backing file per regenerating
    turn. Regeneration already reads that file to rehydrate authored-form
    records ([session persistence §2.4.2](session-persistence.md#242-backing-file-rehydration))
    and hashes its own output, so the check reuses that read and adds one
    hash of a source file. Shown against the turn's compile, that is
    negligible.
  - **Residual.** A save landing between the check's read and the atomic
    rename is overwritten. Grade: asserted with a named falsifier; the
    window is one rename. Falsifier: a probe that writes the file in that
    window and finds its bytes replaced.
- **Why both.** Admission keeps the session unchanged; the chokepoint keeps
  every file intact whatever the caller.
- **Release.** The lock releases when a reload pass leaves the failed set
  empty. A waiting module reaches a module standing failed, so the plan that
  compiles that module selects the waiting one and rebuilds it after it in
  the same pass, or in the follow-on when a later member refused it (§1.2);
  the lock cannot release while a module still waits.
  `/reset` and `/mod` leave the failed set unchanged. Process exit ends the
  session.
- **Exit** (§0.1). `/quit` and EOF exit with status 0 and reprint nothing,
  locked or not.
  - The REPL epilogue returns no error, so nothing at exit reaches `main`'s
    error path, which would print the error and exit 1.
  - An incomplete form pending at EOF is dropped unevaluated and unreported
    while the session is locked. Otherwise it is flushed through `eval` for
    its parse diagnostic (`05-error-presentation.md` §5.1).
  - The object wait at exit returns at the first `Failed` module it meets.
    That module's error has been reported already, so the epilogue ignores
    the answer.
  - **Accepted residual.** That early return abandons the object writes of
    the modules still pending, so a locked exit can leave cache entries
    unwritten. The next session compiles those modules from source. Grade:
    asserted with a named falsifier. The manifest records a source hash only
    when the module's object is written, so a missing write is a cache miss.
    Falsifier: a session after a locked exit that loads an object whose
    source hash differs from its file.
- **Invariants.**
  - Locked exactly when a module stands failed: by representation.
  - Every waiting module reaches a module standing failed, and every module
    the scheduler keeps `Failed` stands failed or waits: by the
    classification rules above. Falsifier: an unlocked session holding a
    module the scheduler keeps `Failed`.
  - No generation compiled against a failed module stays reachable by name:
    every plan member rebuilds, fails or waits, and each runs the rebuild
    prologue ([session transaction §7.3.3](session-transaction.md#733-slot-reuse-and-the-plan-invariant)).
- **Imported modules.** A failure in a non-entry module that another module
  imports is reported after parsing, inside a worker. An importer the plan
  attempts is refused through the barrier's fail-fast on an already-failed
  member
  ([error cascade §4.1](step9-error-cascade.md#41-cascade-construction)), so
  the reload plan returns. The watcher prints its notifications only after
  the whole plan returns, so any wait that never ends withholds the
  diagnostic. The end-to-end guards are
  `tests/repl_persist.rs::watch_imported_type_field_reorder_fails_requiring_restart`
  and `tests/repl_watch.rs::watch_type_error_reload_of_imported_module_blocks_without_hanging`.
  A `/mod` into a failed cache-installed module reaches the same barrier, so
  the fail-fast covers it by construction. No cell exercises that route.
- **End-to-end guards.** For the restart-required cause, in
  `tests/repl_persist.rs`:
  `persist_external_edit_changing_field_type_fails_requiring_restart`
  checks the refusal,
  `persist_structural_reload_failure_keeps_saved_edit_until_restart` the
  retained file and the restart, and
  `persist_compatible_save_after_structural_reload_failure_releases_the_file`
  the release. QA allocates the session-lock cells SL-1 to SL-11 and the
  ACT-1044 cell
  ([evidence delta](../../tests/plan/s122-evidence-delta.md)).

- **As built (2026-10-01).** `dev`(src) implemented this section with six
  deviations from the first draft, each verified against source and folded
  into the text above:
  1. A refusal by a member the same pass rebuilds later makes the refused
     module stand failed (§1.2, Waiting, at its attempt).
  2. The waiting check before an attempt ignores the implicit prelude edge,
     including a recorded failure dependency on the prelude for a module
     whose fallback bit is on (§1.2, Waiting, before its attempt).
  3. A `/mod` target that never registered stands failed (`/mod` load).
  4. Startup recovery waits for the entry's outcome before the reset and for
     its terminal pool after the empty re-registration, which closed a test
     race (Startup, steps 1 and 3).
  5. A broken refusal chain makes the module stand failed (Dependency
     refusal).
  6. A startup entry that did not compile holds no established reference
     (Startup, step 3).

  **Review rulings (2026-10-01).** Independent review found three required
  items; this section now carries the rulings, for `dev` to re-implement.
  - *Deviation 2 narrowed.* The prelude exception covered every reach
    check, so a failing project prelude left its implicit dependents
    compiling against the empty fresh prelude, reported and locked. The
    implicit edge is now an ordinary dependency for waiting, and the
    injection refuses against a failed prelude
    ([int §6.12](int.md#612-the-implicit-prelude-dependency)); only a cycle
    through the prelude keeps the exception (§1.2, Waiting).
  - *Deviation 1 deferred, not replaced.* A member refused by a later member
    no longer stands failed at once: its outcome waits for that member to
    settle, and a rebuilt refusing member puts it back in the follow-on
    (§1.2, Refused by a later member). This closes the false lock after one
    save repairs B and makes A newly import B.
  - *Residual resolved.* The failure branch classifies the modules an
    attempt newly left `Failed` before it classifies the attempted module
    (Set sites). The second invariant holds again. A consequence, shared
    with startup and `/mod`: a newly loaded module that fails stands failed
    until its own save compiles, even after a save drops the import that
    loaded it; a restart, which loads only reachable modules, releases it.
    Potential extension, triggered by a user finding that this friction
    matters: release a failed module that nothing loaded in the session
    reaches and that no caller named.
  - *Order independence.* The failed load's record judges every chain
    against one snapshot (step 3).

  **As built after the rulings (2026-10-01).** `dev`(src) implemented the
  three rulings, PF-1, LQ-4 and ACT-1019, with five further choices it needed
  for these rows and the existing cells. Four were checked against source;
  each is folded into the text above:
  1. Members deferred only on each other are classified from the last in
     plan order (§1.2, Deferred only on each other).
  2. The recurrence stop reported a re-attempted deferred member's own
     error. Review found that error can be stale, a refusal by a member since
     rebuilt. A uniform "did not settle" then failed ACT-1014's helper-end
     row. Ruled 2026-10-02: the member keeps its own error only when it is a
     cycle failure, typed (§1.2, Refused by a later member).
  3. Every failed load resets the modules it newly left `Failed`, a code turn
     and a `/mod` load failing before the dependency wait included (A failed
     load's record, step 1). Recorded from `dev`'s report; review is
     re-checking it.
  4. Fail-fast refusals keep the dependency's file, and the batch wait
     reports the root failure, least by name (PF-1, Batch).
  5. The refusal's leading sentence (Refusal).

#### 1.3.2 Module evidence (`dev`)

Arm each positive row RED on the pre-fix source where its seam exists. The
seam unit is the submodule: lifecycle rows sit with
`src/session_v4/persistence_tests.rs`, admission rows with `src/repl`'s test
module, and scheduler rows with `src/scheduler/tests.rs`.

| Seam | Row |
|---|---|
| Rebuild, parse failure (ACT-1044) | A module holding `sq` is reloaded from source that does not parse. No record of `sq` remains in its table or introspection, the scheduler holds it `Failed` with the parse error, and it stands failed with failed source. The type-failure leg of `reload_replaces_declaration_records_and_failed_reload_clears_them` is the control. A read failure leaves the same state |
| Waiting, before the attempt | After `math` fails, a plan member that imports it and is not a root is not attempted. It holds a fresh table, the scheduler holds it `Failed` with `math` as its refusing dependency, `math` is among its failure dependencies, it is not in the failed set and it has no notification. An unrelated member of the same plan rebuilds |
| Waiting, at the attempt | A saved root that still imports a failed module waits and leaves the failed set if it stood there. Control: a saved root whose new source drops that import, breaking a cycle, rebuilds |
| Release | Once `math` compiles, its waiting dependents rebuild after it in the same pass, each notifying `[updated:]`, and the failed set is empty |
| Refusal chain | Two modules refused only by each other, with no module standing failed, end with the later one failed with the circular-dependency diagnostic, so the session is locked |
| Last attempt | A parse failure after a §14.8 refusal records failed source; a successful reload removes the entry |
| Dependency refusal record | Each refusing site records its dependency; a registration clears it; a reset carries it; a cycle refusal records none |
| Load reset | A failed `/mod` load while `math` stands failed resets only the modules the load left `Failed`; `math` stays `Failed` in the scheduler |
| `/mod` load | A target failing in its own source stands failed, the active module is unchanged and no table remains. A target that imports a module standing failed waits. A code turn importing a failing module, with the session unlocked, records nothing |
| Startup | (a) An entry type failure: the entry stands failed, holds no definition (a cache-preloaded scheme included), is terminal and eval-owned, and the report holds `[errors: <file>]` and the error. (b) A parse failure: the entry stands failed with that error, and the file is unchanged after a definition is refused. (c) A failing dependency: it stands failed, the entry waits and holds it as a failure dependency. (d) A startup cycle: the refused member stands failed and the other waits. (e) No restore notice when the entry did not compile |
| Admission | While any module stands failed, a definition, an expression and a structural turn are refused in a module that does not stand failed. Each `ReplCommand` variant has its expected classification, with `/mem` and `/time` both with and without an expression. The refusal lists every failed file in order with its cause's remedy |
| Chokepoint | `regenerate_backing_file` writes nothing while any module stands failed, for a current module that does not |
| Failing prelude (review finding 1) | A save of a project prelude that fails to parse, and separately to typecheck, leaves every module with the fallback bit on waiting: not attempted, no notification, not in the failed set; only the prelude stands failed. Control: the same shape through an explicit `import` of a failing module. The prelude's compiling save rebuilds them |
| Injection refusal | A module with the bit on attempted while the prelude stands `Failed` is refused through the fail-fast, with the prelude as its refusing dependency, at a reload and at a fresh load (`/mod`). Negative: a null-importing module is not refused |
| Cycle through the prelude | The helper end (`helper_save_dropping_its_prelude_opt_out_is_refused_as_a_cycle`) ends as a restart on the saved files ends it; a member the failed prelude reaches is attempted, not held waiting |
| Refused by a later member (review finding 2) | One pass with roots `a` and `b`, `b` failed beforehand, whose save repairs `b` while `a` newly imports it, ends with both rebuilt and the failed set empty. Twin: when `b` still fails, `a` waits and only `b` is named |
| Newly loaded failure (review finding 3) | A reload of `user` whose new import loads `n`, failing in its own source, leaves `n` standing failed with `n.cl` and `user` waiting. A later save of `user` dropping the import rebuilds `user` and leaves `n` standing failed, so the session stays locked naming `n.cl`; `n`'s compiling save releases it. The scheduler holds no `Failed` module outside the failed set at any step |
| Record order | A failed load's record over the same reset modules in two orders, one module refused through a module whose chain is broken, gives the same failed set |
| Pre-registration failure (PF-1) | For a dependency whose file does not parse, loaded through each `register_dep` caller (`import`, qualified reference, `mod` child, prelude injection): the scheduler holds it `Failed` with its parse error located in its file, and the loader's attempt is refused with it as refusing dependency. Type twin: the dependency registers and fails in its own pass, with the same classification. A read failure takes the same path |
| Watcher state (R1, R3) | Against `recorded_sources`: a file recorded unreadable at its load, then written readable, is a change, also when `sync_watcher` runs before the poll. A recorded file rewritten unreadable is a change, and once the rebuild records unreadable a second unreadable event is not. A deleted file is not a change. A same-content rewrite is no change |
| Unreadable save (R3) | A reload of a module whose saved file is not valid UTF-8 leaves it standing failed with a read error located in its file at an empty span, and a refused definition leaves the bytes unchanged. Its readable compiling save releases it |
| Recurrence stop | A recurring set whose re-attempted deferred member last failed on a cycle reports that cycle; the helper-end row names `x -> prelude -> x`. A recurring set whose member's last failure was a refusal by a since-rebuilt module on a non-cycle error reports "did not settle". The cycle record is set at each cycle site, copied through a refusal, and cleared at registration |
| Newly failed report (A2) | A module newly loaded by a reload that fails to typecheck reports `[errors: n.cl]` with its own error at its own span in `n.cl`, not at `0..0` |
| Pre-turn poll (N1) | In the read loop's turn step: a save queued before the turn is reloaded before the turn dispatches. A definition turn after an idle readable save keeps the saved definition in the file and the session; after an idle unreadable save the turn is refused and the bytes are unchanged. An expression and a slash command observe the rebuilt module. With no queued event the turn is unchanged |
| Unseen-save chokepoint (N1) | `regenerate_backing_file` with the file's on-disk content differing from the recorded state, and separately with it unreadable, writes nothing, warns, and leaves the bytes unchanged; the next poll reloads, or locks for the unreadable leg. A matching state writes. A missing file is written. Without an OS watcher the check still refuses |
| One record (N2) | A save landing after entry registration's read and before the first `sync_watcher` is a change at the next poll: it is reloaded, and a later definition writes with no warning. The same for a dependency loaded by `register_dep` and for a cache-hit restore. The watcher keeps no baseline: `sync_watcher` after an external write records nothing, and the poll still reports the write. A file never loaded is not a change. A reload's read, not the poll, updates the record; an unreadable rebuild records unreadable and a repeated unreadable event is no change |
| Span rule (R2) | A dependency failing to parse at a non-zero offset is recorded and reported at that offset in its own file; a dependency failing to read is located in its own file at an empty span, not at the loader's import span; the loader's error is wrapped once. Covers a code turn, a reload and a batch start |
| PF-1 classification | Startup with `prelude.cl`, and separately an imported `lib.cl`, failing to parse: the dependency stands failed and is reported, the entry waits and is not reported. A reload of `user` newly importing an unparseable `n`: `n` stands failed and notifies `[errors: n.cl]`, `user` waits (LQ-4). `/mod m` where `m` imports an unparseable `n`: `n` stands failed, `m` waits, the active module is unchanged |

`/quit`, EOF and the dropped pending form are process behaviour; their
evidence is QA's end-to-end allocation. The epilogue's infallible signature
makes the exit status structural.

### 1.4 Notification

Each rebuilt or failed module prints one dim metadata line: `[updated:
<file>]`, or `[errors: <file>]` followed by the module's own indented error
(§1.3 Outcome). A waiting module prints nothing (§1.2). The startup report
and the session-lock refusal use the same file form (§1.3.1). `<file>` is the
file's bare name (§7, gap 1).

## 2. `/reset` Command

**Status: not implemented.** `/help` lists it as `(not yet available)`, and no
REPL specification section defines it.

### 2.1 Current behaviour

`/reset` replies `command not yet available in v4 REPL` and changes only two
things:

- **It clears the watcher.** It unwatches every directory, drops the stored
  hashes and drains pending events. Watching resumes at the next
  `sync_watcher`, with hashes re-baselined.
- **It keeps the failed set.** `/reset` is not a repair, so the session
  lock stands (§1.3.1; `14-file-watching.md` §14.5).

Symbol tables, compiled code, macros, the prelude and the disk cache are
untouched.

### 2.2 Open question

A full reset has no requirement and no design. Clearing the watcher can hide an
external repair made before the next turn. Whether `/reset` should keep the
watcher, gain a full-reset design or be withdrawn is a `spec` question routed
through `sprint`.

### 2.3 Prelude reload after reset

None. `/reset` reloads no prelude. `tests/cache.rs::cache_repl_writer_survives_slash_reset`
observes that the session and its cache keep working after `/reset`, which
holds because nothing is cleared.

## 3. Shell escape

`/sh <command>` runs the command through `sh -c` with inherited stdio and
waits for it to finish (`src/repl/mod.rs::run_shell_command`). Its input line is
exempt from paren-balance accumulation.

| Case | Output |
|---|---|
| Empty command | `Usage: /sh <command>` |
| Non-zero exit | `exit status: N` |
| Killed by a signal | `killed by signal: N` |
| Spawn failure | `error: <e>` |

Environment and working-directory changes in the child do not affect the
session.

## 4. REPL cache integration

The REPL uses the same cache path as `--run` (`int.md` §7).

### 4.1 Cache write after module compilation

The nice workers write each loaded module's `.meta` and `.o` and record its
manifest entry ([dependency record](int.md#76-dependency-record-and-validity)).
There is no separate cache-writer thread.

- A defining turn regenerates the backing file, records its new source hash
  and marks the module's object stale, so a nice worker rewrites it.
- The manifest flushes in `wait_object_complete`, after deferred entries are
  retried. The REPL calls it at exit, after the final persist.

### 4.2 Cache load on startup/reset

Every dependency, prelude and submodule handler calls `try_cache_hit_load`
before a fresh build ([cache-hit flow](int.md#71-cache-hit-flow-inside-register_module)).
The restore recurses through the restored module's dependencies. The CLI
target itself is always compiled fresh. `/reset` loads nothing (§2). A
cache-installed module is recompiled from source before `/mod` makes it
current (`session-persistence.md` §2.4.5).

## 5. `--link`

- **Arguments.** `--link` selects the link action and `-o`/`--output` names
  the output. Each of these is an argument error with exit 1:
  - `--link` with `--run`;
  - `--link` with `--no-cache`;
  - `-o` without `--link`;
  - `-o` without a path.
- **Flow.** Start-up compiles exactly as `--run` does and then waits for
  object codegen. `link_by_name` then:
  1. validates that `main` is `(Fn [] (IO _))`;
  2. rejects development-session externs;
  3. finds the runtime bundle;
  4. links the cached objects with the startup stub (`exe::link_executable`).
- **Output path.** The default output is `{project_root}/<entry-stem>` plus
  the platform's executable suffix. An `-o` path is used verbatim. An output
  path that is an existing directory is rejected with a diagnostic.

## 6. Project root resolution

`main.rs::resolve_target_from` derives the project root and the entry module
from the working directory and the CLI target (`00-cli-invocation.md`
§0.5.1):

| Target | Project root | Entry module |
|---|---|---|
| None | the working directory | `user` |
| Contains `/` | the target's parent directory, made absolute | the target's stem |
| An existing directory with no `<target>.cl` beside it | that directory | `user` |
| Otherwise | the working directory | the target |

- Only the third case triggers `Cranelisp.toml` scaffolding
  (`cranelisp-toml.md` §4).
- The cache directory is `{project_root}/.cranelisp-cache`, created eagerly.
  There is none under `--no-cache`.
- Library directories and platform directories are assembled as in
  `cranelisp-toml.md` §2.
- The prelude resolves from `{project_root}/prelude.cl` first, then from each
  library directory.
- No search walks up to parent directories.

## 7. Open conformance gaps

Each gap was read from source on 2026-09-25 and has no failing test. `qa` owns
attribution.

1. **Notification path.** `14-file-watching.md` §14.3 requires `<file>` to be
   relative to the project root. The source prints the bare file name, which
   differs for any file below the root.
   - Falsifier: edit a watched `lib/m.cl` and observe `[updated: m.cl]`.
