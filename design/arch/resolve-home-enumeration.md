# Resolve home before enumeration

Current architecture contract owned by `arch`. It states the class rule that
closed the `enumeration-miss` / wrong-scope-lookup defect family and the
obligations that rule places on REPL display and the `/search` importable
index. Both consumers are interior to the binary crate; their mechanisms belong
to [the int design](../int/int.md) and source rustdoc. Reference resolution
itself is [the prelude and explicit-import contract](prelude-import-convergence.md);
candidate storage is [the symbol-table lifecycle](symbol-table-lifecycle.md#3-resolution-and-canonical-bindings).
The S108 sightings and their per-instance fixes are delivery history in Git.

## 1. The class

A lookup or enumeration is rooted at the scope the question was asked from
when the question is about a resolved home, or an enumeration covers some
sources of its kind and reports itself complete. Every recorded instance was
one of those two errors: a formatter that dropped the home it had been given
and asked again from the current module, a view walk that omitted
prelude-provided names, or an index source marked done with no rows.

## 2. Actors

- **Types** stores, per spelling, terminal `NameCandidate` references whose
  `source` is the canonical `FQSymbol`. A candidate names its terminal
  directly; no import chain remains to follow.
  `cranelisp_types::resolve_terminal_entry_and_home` answers only when the
  spelling has exactly one candidate in the asked table, then reads that
  terminal's binding from its home table. The `*_chain` readers
  (`lookup_type_def_chain`, `lookup_trait_decl_chain`,
  `get_impls_for_type_chain`, `get_implementing_types_chain`) are projections
  over that one read; the name suffix is historical.
- **The display gate** is the one place REPL introspection turns a spelling
  into declarations. It yields every candidate of the spelling, each as its
  terminal binding with its canonical `FQSymbol`, so each candidate's home is
  its own `canonical.module`. The candidate set, its agreement with resolution
  are stated in [REPL introspection](prelude-import-convergence.md#35-repl-introspection).
- **Formatters** receive one `(binding, home)` per candidate from the gate and
  render that candidate's sections.
- **The importable index** is binary-private, unserialized and rebuildable. Its
  sources are seeded modules, loaded or registered modules, and file-only
  modules.

## 3. The rule

1. **Resolve the home once, at the gate; enumerate at the home.** A display or
   introspection formatter takes each candidate's binding and home from the
   gate and roots every section lookup at that home, where the declaration is
   local. A formatter must not resolve the name again from the current module:
   for a spelling with several candidates a second resolution has no single
   answer.
   A genuine **view question** is the deliberate exception: "which traits does
   this type implement, as visible from here" is scope-rooted by meaning.
   Scope-rooting governs the frame of the answer, not the candidate set: a
   module whose `prelude_fallback` bit is on has every public prelude name in
   scope, so a view walk's candidate set falls under rule 2.
2. **An enumeration covers every source of its kind through one reader per
   source kind, and no source is complete without contributing its rows.**
   A zero-row completion is legal only for a genuinely row-less outcome: no
   source file, an empty module, an error skip, or a registered module that
   failed. It is never legal because another path is presumed to own the
   source. Every enumerated source reaches completion by rows or by a legal
   zero-row skip, including through the failure edge; an outcome with neither
   wedges the burn-down.

[Principle 24](principles/24-resolve-once.md) states the general resolve-once
rule this specialises.

## 4. The `/search` index covers loaded modules

Spec authority is [agent language awareness](../../repl/spec/17a-agent-language-awareness.md)
§17.19. The obligations on
[the index worker](../../src/session_v4/index_worker.rs):

- A mounted module's rows come from its live symbol table through the single
  table-to-rows projection `public_entries_from_table`. An unmounted module's
  rows come from its `.meta` or a typecheck.
- Three feeds use that one reader: the arm-time sweep of registered modules
  already in a terminal typecheck state, the worklist branch for a registered
  module popped in a terminal state, and the publication-edge hook
  `on_module_published`, called beside `notify_typecheck_done`. The hook covers
  a module in flight at arm time, a later `/import` or FQ autoload, and a
  watcher reload, without polling.
- An in-flight registered module has three exits and each lands accounting:
  publication records rows; failure records a legal zero-row skip through
  `on_module_failed`; shutdown abandons the burn-down with the session.
- Re-recording a module replaces its rows (`record_loaded_replace`), so a
  reload or redefinition neither duplicates nor serves stale rows.
- Accounting: `pending_count` is `enumerated_total` less the indexed set, never
  negative, reaches zero, and is independent of feed order. A module outside
  the file-enumerated set counts in both tallies exactly once.
- Both hooks are no-ops until the index is armed, so batch modes stay
  index-inert.
- **Unhooked terminal entry.** `register_module_cached` and
  `register_module_cached_no_object` install a cache-hit module directly in a
  terminal state without the publication hook. This is covered by construction
  while library directories are fixed after arming: such a module's source lies
  under the enumerated roots, so its `.meta` rows already landed, and a valid
  cache's `.meta` equals its live table. A change that mutates library
  directories mid-session, or a cache-hit path that skips `.meta` projection,
  must hook this edge in the same change-set. This is asserted with that named
  falsifier; it is not measured.

[ACT-0952](../../sprints/actions/ACT-0952-complete-semantic-search-indexing.md)
carries the open indexing work. Current evidence navigation is
[the QA plan](../../tests/plan/PLAN.md).

## 5. Trait sections root at the home

`format_trait_display` takes the trait's resolved `home` as a parameter. The
primary line qualifies with it, and the `; defn:` and `; impl:` section lookups
root there, where the `Decl::Trait` binding is local. Rooting the implementing-type
enumeration at the trait's home is complete by construction, because
[bounded contexts §7 "TraitImpl storage"](bounded-contexts.md#7-cross-crate-types--cratescranelisp-types) (Decision 45)
stores every implementation shell in the trait's defining module: "which types
implement this trait" is a home question, not a view question.

## 5a. The type-side `; impl:` view includes prelude-provided traits

`get_impls_for_type_chain` builds its candidate traits from the spellings in the
asked table and probes each candidate's home. A module receives the implicit
prelude through its fallback bit, not through entries in its own table, so an
enumeration over the inner table alone omits every prelude-provided trait.

The one session wrapper `impls_for_type_in_view` in
[the type formatter](../../src/repl/format_type.rs) feeds both
`format_type_display` and `format_builtin_type_display`. It unions:

- the run rooted at the asking module; and
- when that module's bit is on and it is not `prelude`, the same reader rooted
  at `prelude`, keeping only traits whose prelude binding is public. The types
  reader takes no visibility parameter, so this filter is applied by the
  wrapper.

Rows are canonical `(FQTraitName, FQTypeName)` pairs filtered by the queried
fully-qualified type, then deduplicated. A rendered or bare name is never the
identity, so a same-named type in another module contributes nothing. A
suppressed prelude contributes no prelude rows, and a type with no rows omits
the section ([self-documentation](../../repl/spec/04-self-documentation.md) §4.1.3).

## 6. Boundary

- Both mechanisms consume the existing types readers unchanged. This contract
  implies no public-API, cache or schema effect.
- The index feed lifecycle in §4 has no int design home yet. `design` (int) may
  fold it into the int design and reduce §4 to the cross-context obligations;
  until then this section is its only statement.
