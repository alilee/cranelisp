---
id: ACT-0952
title: Complete `/search` through the normal compiler in an isolated semantic indexing realm
status: open
priority: required
from: arch
to: design
sprint: 121
filed_at: 2026-09-03
refers_to:
  - repl/spec.md §17.19
  - design/int/index-worker-isolation.md
  - design/arch/macro-availability-model.md
  - design/arch/resolve-home-enumeration.md
  - src/session_v4/index_worker.rs
  - src/session_v4/nice_worker.rs
  - src/scheduler.rs
  - src/worker.rs
  - src/process_form/cache_restore.rs
---

## Request

Sprint 121 deliberately narrows `/search`: every feed omits macro declaration
rows, and the unloaded-source feed removes direct `defmacro` forms before it
checks the remaining ordinary cluster. It MUST NOT construct a macro parent
`Binding` unless the complete active clause set has typechecked, codegenerated
and published with it. In particular, the old index-only
`Decl::Group(GroupKind::Macro)` carrying a placeholder type and no callable
clauses is not a legal approximation of compiler state.

This interim behaviour is intentionally incomplete. A legitimately compiled
loaded or cached table can still contribute an ordinary public declaration
created by macro expansion, while the same not-yet-compiled source cannot.
That history-dependent edge is not a promise. The current `repl/spec/17a-agent-language-awareness.md`
expressly excludes macro declarations from every feed (§17.19.2a) and
describes source indexing as typechecking only the remaining non-macro forms.
That wording supersedes the pre-S121 requirement for seeded macros to be
discoverable and to render a canonical `; defmacro` result row. Restoring that
stronger semantic-search promise requires the future user rulings and complete
compiler path in this action, not another metadata-only exception.

The future implementation must produce a **full semantic index** by running
the normal module compiler in an isolated indexing realm and harvesting only a
terminal module table. It must not grow a second parser, macro interpreter,
typechecker, code generator, scheduler protocol, or authoritative symbol
store. The intended flow is:

```text
nice-worker slack
      |
      v
isolated compilation realm for root M
      |
      +--> normal dependency discovery/cache validation
      |          |
      |          +--> valid .meta + .o -> normal Linker/GOT restore
      |          `--> source -> normal module scheduler/worker pipeline
      |
      +--> source-ordered macro checkpoint
      |          dependency code ready
      |          parent + every active private clause checked and JIT'd
      |          complete checkpoint published inside the realm
      |          later forms may execute that committed macro
      |
      `--> one ordinary expanded HM cluster -> JIT -> terminal table
                                                |
                                                v
                                  harvest public semantic rows, then drop realm
```

The smallest safe first shape is an **ephemeral per-root dependency closure**.
Refactor the existing root-private orchestration so the same
`cluster::process_cluster`, worker publication, `CompileScheduler`, cache
restore and backend paths can target either the foreground session or this
isolated realm. Do not clone a live table and then codegenerate into its shared
`Arc<GotTable>`: live completed dependencies may be borrowed read-only while
their session owners remain alive, but every module published by the indexing
realm needs its own table and GOT. The realm retains, as one lifetime domain:

- its scheduler module states and source-only continuations; aliases,
  prelude-fallback and declared-export state; fresh type-id authority; module
  sources/typecheck products; and fresh per-module symbol tables/GOTs;
- every dependency table needed by root checking or macro execution;
  `Code::Jit` owners on freshly compiled callables, `Code::Linker` owners on
  restored callables, platform/DLL owners, retained superseded code, and drop
  glue state; and
- the source and dependency hashes used for cache validation.

No half-finished typecheck candidate is retained across a dependency gap. The
realm keeps the same scheduler packet used by ordinary compilation: the source
continuation plus `generation_started`; stack-local staging is discarded, the
dependency finishes, and the module retries against the larger committed realm.
A successful macro checkpoint is committed inside that realm and remains
available to its later source forms. The fully expanded non-macro forms then
enter the existing one-call HM cluster. Harvest only after the root reaches its
normal terminal typecheck and in-memory-code state; include public macro
parents and public ordinary declarations produced by expansion, while excluding
private clause rows and all compiler-generated internal keys. On success,
failure or abandonment, dropping the realm must release all realm-only tables,
GOTs, JIT/linker owners and platform handles together.

Index work remains nice work. A claimed root may give its own unresolved
dependencies dependency-first priority **inside that realm**, but must not put
them on the foreground priority ladder and thereby turn `/search` warm-up into
foreground work. It must cooperatively yield at module/gap/checkpoint boundaries
when object codegen appears, workers are promoted for link, or shutdown is
requested. Existing scheduler cycle detection and failed-dependency propagation
remain the one mechanism: a cycle, source/typecheck/codegen/macro error, or
caught panic makes the root absent from the index and changes no foreground
compiler state.

Per-root closures deliberately permit two concurrent index tasks to compile a
shared uncached dependency twice. This buys simple ownership, deterministic
discard and no cross-root invalidation protocol. Bound concurrent realms by the
nice-worker count and measure duplicate work and peak retained code. A shared
background compiled-module world is a later optimization only if measurement
requires it: it would need single-claim module states, waiters, source-change
invalidation, failure fan-out and reference-counted closure lifetime, and would
otherwise become the parallel authoritative compiler store this action forbids.

The first implementation stage reads valid normal cache artifacts but writes
none. Cache restore must use the existing complete path: validate source,
dependency hashes, schema/build identity and macro parent-to-active-clause
bijection; install the decoded table into the realm; load `.o` through the
normal Linker; register intrinsics, host primitives, platform pointers,
already-compiled symbols and per-module GOT data symbols; wire the restored
module GOT; and retain the `Arc<Linker>` through each callable's `Code` owner.
A JIT-only semantic index is not evidence that a reusable `.o` exists.

A later cache-write stage needs separate user approval. A background result is
trustworthy for foreground reuse only if it ran the exact complete compiler,
object emission and dependency-hash protocol, writes the normal `.meta`/`.o`
pair, and makes the manifest entry visible only after all required artifacts
exist. It must also coordinate ownership with a concurrent foreground compile.
Until those conditions and their race tests hold, branch-(c) semantic indexing
must not publish cache artifacts.

No cross-crate public API, platform interface, persisted index schema or cache
schema change is presently required: the compiler and backend capabilities
already exist, and the realm/orchestration abstraction can remain root-private.
Any implementation that discovers a necessary public item, generated
`public-api.txt` delta, cache-format change or platform contract change returns
to `arch` and the user before source work.

Before this action enters implementation scope, the user must separately rule:

1. that `/search` may execute arbitrary reachable modules' compile-time macro
   code in the background, and that failures remain silent per-module skips;
2. that the complete index promises history-independent macro declarations and
   macro-generated public ordinary declarations, and whether both participate
   in every existing name/docstring result rule; and
3. whether successful isolated compilation may ever write foreground-reusable
   cache artifacts, after the non-writing stage is measured.

## Completion evidence

- `spec` has reconciled the interim macro exclusion, and the user has approved
  the three stronger semantic-index decisions above before implementation.
- One normal compiler path serves foreground and isolated indexing; review can
  point to no index-specific macro registration, expansion, HM checking,
  codegen, cache-restore or publication implementation.
- A source-order acceptance case proves an imported helper is compiled, a
  macro checkpoint is completely published, that macro creates an ordinary
  public declaration, and `/search` reports both the macro and generated name
  only after whole-module success.
- Negative cases prove no parent-without-clauses state, no partial rows on
  macro/typecheck/codegen failure, deterministic cycle failure, dependency-gap
  retry from source-only continuation, and byte-unchanged foreground tables,
  aliases, fallback state, GOTs, scheduler and cache in the non-writing stage.
- Cache-hit cases prove complete `.meta` plus `.o` restoration, macro-clause
  bijection validation, non-null GOT wiring and code-owner retention through
  dependent macro execution. If cache writes are later approved, race tests
  prove foreground/index concurrency cannot publish a partial or stale pair.
- A measured representative library run records cold/warm latency, duplicate
  dependency compilations, peak concurrent realms and retained-code memory.
  The owning sprint either accepts the bounded per-root posture or obtains a
  new user-approved design for sharing; it does not silently introduce one.
- Shutdown, link promotion and foreground object work demonstrate cooperative
  yield/abandon at safe boundaries, with no stranded work, deadlock, leaked
  code owner or corrupted artifact.
