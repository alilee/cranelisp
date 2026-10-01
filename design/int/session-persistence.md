# REPL Session Persistence — int Design

Owner: `design` (int). This document states how the REPL keeps a module's
backing `.cl` file equal to its live definitions: regeneration, the write,
watcher suppression and restore.

- **Required behaviour** is `repl/spec/15-session-persistence.md`; the
  redefinition persistence rules are `repl/spec/18-redefinition.md` §18.8.
- **Section numbers are pinned** by source and test citations. Retired
  numbers are not reused, so gaps are deliberate.
- The code lives in `src/save.rs` (generation, the atomic write) and
  `CompilerSession::regenerate_backing_file` (`src/session_v4/lifecycle.rs`).

## 1. Regeneration

### 1.1 Trigger

The session regenerates the current module's backing file after every
successful definition-like turn: a definition, a structural form (`import`,
`mod`, `platform`), an accepted agent write (`design/int/agent.md` §15.3,
§17.1) or a committed redefinition. Expression turns and failed turns never
trigger it, and nothing regenerates while the session is locked
([§2.4.4](#244-failed-source)).

### 1.2 Stateless generation

`generate_module_source(table, introspection, module)` is a pure function of
the current table and its introspection. It keeps no history. A redefinition
replaces the binding, so the file carries only the latest successful
definition.

### 1.3 Section order

Sections are emitted in a fixed order, separated by blank lines:

0. the module preamble (`module_preamble`, re-emitted byte-stably);
1. `(mod …)` declarations;
2. `(platform …)` declarations;
3. `(import …)` — merged by module, implicit prelude filtered, specific names
   deduplicated, a glob winning over specific names;
4. `(export …)` — merged;
5. traits, alphabetical;
6. types, alphabetical;
7. impls written in this module (§12);
8. macros, then functions, each dependency-sorted (§1.4).

The structural sections read the table's own fields (`submodules`,
`platforms`, `imports`, `exports`); there is no separate structure store.
After a whole-file rebuild, these fields hold exactly the saved source's forms
([int §6.10](int.md#610-the-import-generation)).

### 1.4 Dependency ordering

- Macros precede functions, because a macro must be defined before use and
  macro calls are not callee edges.
- Within each group, `dependency_sort` runs Kahn's algorithm over the
  intra-module `callees` recorded by typechecking. There is no scan of source
  for references. Ties and cycles resolve alphabetically.
- Traits and types need no ordering: they precede all functions and may
  reference each other freely.
- Records that share one authored form are emitted once, at its first
  position. A macro expansion or a literal `(begin …)` records the same outer
  form under several names.

## 2. What is persisted — definition-like inputs only

### 2.1 Content

The file holds definitions and structural forms only
(`repl/spec/15-session-persistence.md` §15.7). The synthetic `__expr` wrapper,
internal `$`-mangled entries and compiler-generated keys are never written.
A file whose module failed is never regenerated, so its saved text, broken
forms included, stays on disk as saved (§2.4.4).

### 2.2 Render source per kind

| Kind | Render source |
|---|---|
| Structural forms | the table's structural fields |
| Traits, types | the entry's introspection record (`emit_decl_or_source`) |
| Impls | the introspection record keyed `Trait.Type` (§12) |
| Functions | the entry's introspection record |
| Macros | the entry's introspection record, else the cache-surviving `macro_sexp` |

Every record read here is the entry's **authored form**: the top-level form
the user wrote (for an expansion or a literal `begin`, the outer form), plus
its verbatim text when known. §2.4 states how each install path supplies it.

- **Authored text first.** A record's verbatim `source` is emitted when it
  re-parses to the recorded `sexp` (`sexp_matches_source`) and, for a
  function, already carries the live docstring (§11.3a). Otherwise the
  reconciled `sexp` render is used. A stale or malformed source can therefore
  never corrupt the file.
- **No qualification at save time.** Stored forms keep the names the user
  wrote, so the generator needs no typecheck state.

### 2.3 Inline submodule guard

A module whose file holds an authored inline `(mod child form…)` body is not
regenerated (`should_regenerate`): the child's definitions live in the child's
table, and regeneration would reduce the body to a bare `(mod child)`.

### 2.4 Authored-form records

**Invariant.** When regeneration reads a module, every live entry that a
section generator selects has an authored-form record that is its latest
successful definition. Otherwise that module is not written (§2.4.3).

#### 2.4.1 Who writes a record

| Install path | Writer |
|---|---|
| Ordinary definitions — REPL turn, file load or reload | the **publication writer**: form processing stages one record per definition it builds, and the shared publication step installs the staged records only after that generation publishes. A successful REPL turn then records its verbatim text for every definition it published |
| Macro publication, from any path | the macro checkpoint writer, after the checkpoint publishes |
| Cache restore | none at install; [backing-file rehydration](#242-backing-file-rehydration) supplies the record when a reader first needs it |

- **Settled state only.** A record is written from published state
  (Principle 26). A candidate never reaches the live record, so a rejected
  redefinition, at typecheck or at the commit gate, a codegen or publication
  failure and a failed reload each leave every record at its last published
  generation (`repl/spec/18-redefinition.md` §18.8,
  `repl/spec/15-session-persistence.md` §15.6). The staged records ride the
  cluster's publication carrier with its other presentation products
  (`s117-conformance-recovery.md` §1.1), including a cluster with nothing to
  compile, and are dropped with it; a dependency gap drops them before the
  retry.
- **Whole replacement.** Both writers replace the record's authored carriers
  together: the form, the expansion (cleared when the new generation has
  none), the checked AST of a function, and the text. The text is the
  verbatim slice when the module file is the source, otherwise the form's
  render until the REPL turn records its input. No carrier can therefore keep
  an earlier generation. CLIF and code size are codegen facts, written by the
  same publication step.
- **Removal.** A whole-file rebuild's prologue deletes the record of every
  definition of the displaced generation; the rebuild's publication then
  installs its own
  ([session transaction §7.3.1](session-transaction.md#731-the-whole-file-rebuild)).
- **Every kind, one key.** The publication writer covers functions, types,
  traits and impls alike. Each record is keyed by the live-turn projection
  (`definition_result_symbol`), which rehydration also uses; a `begin` member
  or expansion product takes the outer authored form (§1.4).

#### 2.4.2 Backing-file rehydration

An entry installed from the object cache has no record, and its backing file
supplies one when a reader first needs it: `/source`, the redefinition residue,
and regeneration. Regeneration finds nothing to fill, because it never writes a
cache-installed generation (§2.4.5). A later turn or reload replaces a filled
record through the publication writer.
A cache hit requires the file's hash to equal the manifest
`source_hash`, so the file is exactly the source of the restored table
(`int.md` §7.3). Rehydration is lazy and reads the file once.

- **Scope.** Rehydration applies to every top-level native definition form:
  `defn`, `deftype`, `deftrait` and `defmacro`, each with its private variant,
  and `impl`. Each member of a top-level `begin` counts as a form, and each
  member's record takes the outer `begin` as its form, as a live turn does
  (§1.4). Structural forms are excluded.
- **Key.** A form's key is the one a live turn records for it, so the two
  paths share one derivation. A name-slot form keys by its name. An `impl`
  keys by the live-turn projection (`definition_result_symbol`) over its
  trait and target slots; no second rule derives impl identity from surface
  spelling. A form that cannot be keyed is skipped, and §2.4.3 reports it.
- **Liveness.** A keyed form is rehydrated only if the key names a live
  entry. For an ordinary entry, the key is in the module's table. For an
  `impl`, it is in the table's `written_trait_impls`, which also covers impls
  of imported traits whose shells live elsewhere.
- **Absence.** A key is filled only when its record has neither form nor
  text. A record written by codegen alone, such as CLIF metadata, counts as
  absent. The record takes the form and its consistency-gated verbatim slice.
- **Enumeration.** An impl is rehydrated under its `Trait.Type` label, which
  §12.3 rows 2 and 3 both enumerate.
- **Macro calls.** A top-level macro call has no native head, so the
  definitions it produced stay unrecorded for readers of a cache-installed
  module. §2.4.5 keeps them out of regeneration.

The metadata carries no authored text or form attribution: it holds checked
ASTs, `macro_sexp`, structural records and the preamble. Carrying either would
be a `cranelisp-types` and cache-schema change, and `--run` writes the same
cache. Attribution by source span would also be wrong for REPL-introduced
definitions, whose spans are turn-relative. The certified file and §2.4.5 make
that change unnecessary. `repl/spec/15-session-persistence.md` §15.4 rule 6
requires rules 1–4 to hold whether definitions were compiled from source or
restored from the object cache; it places no content obligation on the
metadata.

#### 2.4.3 No silent omission

Each section generator reports every entry it selected but could not render,
because no record or `macro_sexp` fallback existed after rehydration. A
record whose authored form another emitted entry already carried is rendered,
not missing (§1.4). If any entry is unrendered, the session writes nothing,
keeps the existing backing file and warns on the write-failure channel (§3.3),
naming the entries. The in-memory state remains the ground truth. Dropping an
entry would lose authored source irreversibly once the next restart reloads
the file.

#### 2.4.4 Failed source

A failed reload publishes nothing, so it changes no record (§2.4.1). While
any module stands failed the session is locked
([REPL lifecycle §1.3.1](repl-lifecycle.md#131-session-lock)): turn
admission and the regeneration chokepoint withhold every write to every
backing file until a save leaves no module standing failed
(`repl/spec/14-file-watching.md` §14.5; `15-session-persistence.md` §15.1).
Each saved file, including the one that does not compile, therefore stays on
disk as saved.

- **Every cause.** The lock covers a §14.8 refusal; a read, parse,
  typecheck, codegen or publication failure; a dependent that fails in its
  own source after its dependency compiled; and a failure at startup or in a
  `/mod` load. Candidate records are never restored to fill a file.
- **Startup.** A module that fails at startup holds no definition and its
  file is not regenerated. There is no repair at the prompt and nothing is
  re-emitted: the remedy is a save that compiles
  (`repl/spec/15-session-persistence.md` §15.2.3).
- **Restart.** The lock is session state. A restart compiles the saved
  source ([§3.4](#34-restore)), so source that compiles is established and
  source that still fails locks the restarted session.

#### 2.4.5 Editing a cache-installed module

Regeneration writes only the current module. A module becomes current and
editable through `/mod M`; the entry module is always compiled from source over
its preloaded table.

- **Rule.** When `/mod M` names a module whose live generation was installed
  from the object cache, the session first recompiles M from its backing file
  through a reload plan rooted at M (`repl-lifecycle.md` §1.2). A failed
  load locks the session ([§2.4.4](#244-failed-source)). A generation
  that regeneration writes for a loaded module is therefore compiled from
  source this session, and each of its definitions has a publication record
  ([§2.4.1](#241-who-writes-a-record)), including those a top-level macro
  call produced.
- **Effect.** The cache hit certified that the file is the restored table's
  source (`int.md` §7.3). The recompile is a whole-file rebuild, which may
  number slots differently from the cached generation, so the plan rebuilds
  M's dependents too; from unchanged sources they compile to the same
  definitions. `/mod` reports each failed module's notification. Persisted macro
  calls re-expand with the macro current at the recompile, as the template
  qualification of `repl/spec/15-session-persistence.md` §15.4 permits.
- **No recompile otherwise.** `/mod` to the entry module or to a module
  compiled from source this session switches without recompiling. `/mod`
  never creates a module: it loads a module not yet loaded from its file,
  or refuses a name with no module ([int §8.5.1](int.md#851-mod-target)).
- **Failure.** A failed recompile has the outcome of a failed reload of that
  module (`repl-lifecycle.md` §1.3–§1.4).
- **Rejected alternatives.** Re-expansion during rehydration would run macros
  in a second, save-time expansion path (Principles 7 and 11). Cache-carried
  attribution is excluded by
  [§2.4.2](#242-backing-file-rehydration).

## 3. Write, failure and restore

### 3.1 Atomic write

`save::atomic_write` writes `{file}.cl.tmp` in the target directory, fsyncs it
and renames it over the target, so a crash never leaves a partial file. An
empty generation is not written.

### 3.2 Backing path

The path is the typecheck product's recorded `file_path`, else
`{project_root}/{module}.cl`. The same resolution serves the restore notice.

### 3.3 Write failure

On failure, including a §2.4.3 refusal, the session prints a warning and
continues. The in-memory state is the ground truth; the file is a convenience,
and the REPL never aborts because a save failed.

### 3.4 Restore

- Start-up loads the entry module through the normal module pipeline, so a
  cache hit is a fast restart. There is no REPL-specific restore path.
- With no backing file, the module starts empty and the file is created by
  the first regeneration.
- A backing file that fails to compile, whether it does not parse or a form
  fails, loads no definition. Its module stands failed, the session is
  locked until a save of it compiles, and the file is never rewritten or
  deleted ([§2.4.4](#244-failed-source)).
- The start-up restore notice is emitted only when the entry module
  compiled. Every definition of the file then restored, so the file's
  definitions are the count (`repl/spec/15-session-persistence.md`
  §15.2.2).

## 4. Watcher self-write suppression

The watcher compares each file's state on disk with the session's one record
of what it last loaded or wrote (`recorded_sources`;
[REPL lifecycle §1.2](repl-lifecycle.md#12-poll-and-reload), Content hash).
After a successful write, `regenerate_backing_file` records the written
content's state there and maps the file to its module before returning. The
watcher polls at the next prompt boundary, sees a matching hash, and skips the
reload; repeated events for one write are each hash-checked. An external edit
changes the hash and triggers an ordinary reload, which unifies interactive and
file-based development. An external save that the session has not yet
reloaded is never overwritten: the watcher polls before each turn, and the
write chokepoint refuses when the file on disk differs from the recorded
state ([REPL lifecycle §1.2, §1.3.1](repl-lifecycle.md#131-session-lock)).

## 10. Inline `(mod …)` extraction path

### 10.1 Rule

`write_inline_mod_to_disk` (`src/process_form/dependency.rs`) writes an
extracted inline body beside the parent module's own file:
`{parent_dir}/{parent_stem}/{name}.cl`. The parent is located with the same
`pipeline::resolve_module_file` rules the loader uses, including lib
directories, and never relative to the process working directory.
`project_root` joined with the dotted path is only a fallback when the parent
file cannot be found. An existing extraction-stable file is recognised and
not rewritten.

### 10.2 Annotation spacing

The regeneration renderer suppresses the separator after a bare `:` marker, so
`:(Option String)` is never written as `: (Option String)`.

### 10.3 Evidence

- Unit tests pin the lib-dir placement, the no-stray-file guard and the
  recognise-existing no-op (`src/process_form/dependency.rs`,
  `src/process_form/tests.rs`).
- Annotation spacing is pinned in `src/save.rs`.
- The repository `.gitignore` still ignores `/collections/`, `/compare/`,
  `/fn/`, `/num/` and `/text/` at the root, residue of the old
  working-directory bug. Whether to retire those entries is the repository
  owner's decision.

## 11. Docstring authority

### 11.3a The renderer contract

The live `Def.docstring` is authoritative for a function's docstring, and a
`set-doc` edit changes only that field (`design/int/agent.md` §17.2).
Regeneration reads it:

1. `generate_fns_and_macros` passes each plain function's live docstring to
   the renderer; macros pass none.
2. `render_decl_sexp(sexp, docstring)` places the docstring in the `defn`
   docstring slot. The slot sits between the name and the parameter vector,
   or the first variant for a multi-signature function, and the renderer uses
   the parser's slot rule.
3. **Reconciliation.** With `Some(text)`, the renderer emits `text` and drops
   any docstring already in the stored form, so the form never carries two.
   With `None`, the stored form's own docstring, if any, round-trips unchanged,
   and no empty literal is invented.
4. The stored form is never mutated. `/source` and macro-clause recompilation
   keep seeing authored source.

The rejected alternative, rewriting the stored form when an edit is made,
would create a second writer and break the rule that the stored form equals
authored source. The preamble follows the same shape: the regenerator reads a
live field.

## 12. Impl regeneration

### 12.2 Storage model

For an impl written in module M (Decision 45 as amended;
`design/arch/backend-keyed-consumer.md` §1.1.1):

- the `TraitImpl` shell lives in the trait's defining module and records
  `impl_module = M`;
- the method definitions and their GOT slots live in M's table;
- the impl form's verbatim source lives in M's introspection under
  `Trait.Type`.

So "impls written in M" is not "shells in M's table".

### 12.3 Enumeration

`generate_impls` collects `Trait.Type` keys from three rows into one sorted
set, and renders each through the same gated reader the declaration sections
use:

| Row | Source | Covers |
|---|---|---|
| 1 | shells in M's table with `impl_module == M` | impls of M's own traits written in M |
| 2 | M's introspection records whose dotted key names an `(impl …)` form (`record_is_impl_form`) | impls of imported traits written in M |
| 3 | M's table's `written_trait_impls` | every impl written in M, including one restored from cache, so a missing record is reported under §2.4.3 rather than skipped |

An impl reachable by several rows yields the same key and renders once. An
impl of M's trait written in another module N is legally excluded: rows 1 and
3 omit it, and its source is recorded under N. Rows 1 and 3 take the key from the settled trait and `impl_type` names. Row
2 and rehydration use the live-turn key, built from the written head names.
The two keys agree because a written head name is the declared name:
`TypeRef` and `TraitRef` hold the qualifier apart from the name, the
language has no type synonyms, and renamed import and export entries
(spec §8.3.5) are not yet accepted
([ACT-0997](../../sprints/actions/ACT-0997-renamed-import-entries-rejected-intake.md)).
Accepting renames breaks that premise, and impl identity must then come from
one determinant; otherwise every regeneration of a module holding such an
impl is refused. A disagreement surfaces as a §2.4.3 refusal, never as a
silent drop.

### 12.3.1 Completeness guard

`section_entry_claimed_or_excluded` matches every declaration kind
exhaustively, so a new persisted kind cannot compile until it is either
claimed by a section generator or listed as a legal exclusion. The runtime
sweep `assert_section_completeness` remains as a `debug_assert!` and a
`CRANELISP_MODULE_TRACE` hook for a misclassification.
