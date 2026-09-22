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
§17.1) or a committed redefinition. Expression turns and failed forms never
trigger it.

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
Forms that failed to load during a degraded start-up are re-emitted verbatim
until repaired, so regeneration never silently deletes the user's text
(`append_failed_forms`).

### 2.2 Render source per kind

| Kind | Render source |
|---|---|
| Structural forms | the table's structural fields |
| Traits, types | the defining turn's introspection record (`emit_decl_or_source`) |
| Impls | the introspection record keyed `Trait.Type` (§12) |
| Functions | the introspection record; for a cache-restored module, rehydrated first from the backing file (`rehydrate_userfn_introspection_from_source`) |
| Macros | the introspection record, else the cache-surviving `macro_sexp` |

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

### 2.4 Open obligation — cache-restored declarations without a record

Introspection is REPL-only; a cache-restored module has none. Functions are
rehydrated from the backing file (§2.2), but traits, types and impls are not.
`emit_decl_or_source` drops an entry with no record, so regenerating a
cache-restored module after an edit could omit its trait, type and impl
declarations. No test establishes whether a supported REPL flow reaches this.
Evidence ownership is `qa`'s. A reproduction would reopen the choice between
extending rehydration to these kinds and a cache-surviving source field, the
latter a `cranelisp-types` and cache-schema change for `/arch`.

## 3. Write, failure and restore

### 3.1 Atomic write

`save::atomic_write` writes `{file}.cl.tmp` in the target directory, fsyncs it
and renames it over the target, so a crash never leaves a partial file. An
empty generation is not written.

### 3.2 Backing path

The path is the typecheck product's recorded `file_path`, else
`{project_root}/{module}.cl`. The same resolution serves the restore notice.

### 3.3 Write failure

On failure the session prints a warning and continues. The in-memory state is
the ground truth; the file is a convenience, and the REPL never aborts because
a save failed.

### 3.4 Restore

- Start-up loads the entry module through the normal module pipeline, so a
  cache hit is a fast restart. There is no REPL-specific restore path.
- With no backing file, the module starts empty and the file is created by
  the first regeneration.
- A backing file with broken forms loads its good forms and retains the
  failed ones for re-emission (§2.1); the file is never deleted
  (`repl/spec/14-file-watching.md` §14.4–§14.5).
- The start-up restore notice counts definitions from the restore record, not
  from a re-parse of the file (`repl/spec/15-session-persistence.md` §15.2.2).

## 4. Watcher self-write suppression

The watcher compares content hashes before reloading. After a successful
write, `regenerate_backing_file` records the written content's hash
(`update_content_hash`) and maps the file to its module before returning. The
watcher polls at the next prompt boundary, sees a matching hash, and skips the
reload; repeated events for one write are each hash-checked. An external edit
changes the hash and triggers an ordinary reload, which unifies interactive and
file-based development.

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

`generate_impls` collects `Trait.Type` keys from two rows into one sorted set,
and renders each through the same gated reader the declaration sections use:

| Row | Source | Covers |
|---|---|---|
| 1 | shells in M's table with `impl_module == M` | impls of M's own traits written in M |
| 2 | M's introspection records whose dotted key names an `(impl …)` form (`record_is_impl_form`) | impls of imported traits written in M |

An impl reachable by both rows yields the same key and renders once. An impl
of M's trait written in another module N is legally excluded: row 1 filters
it out and its source is recorded under N. The key comes from the settled
`impl_type`, not from surface syntax.

### 12.3.1 Completeness guard

`section_entry_claimed_or_excluded` matches every declaration kind
exhaustively, so a new persisted kind cannot compile until it is either
claimed by a section generator or listed as a legal exclusion. The runtime
sweep `assert_section_completeness` remains as a `debug_assert!` and a
`CRANELISP_MODULE_TRACE` hook for a misclassification.
