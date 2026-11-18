# Module-alias scoped lookup — the referring-module contract

**Status: current contract, implemented.** `arch` ruled it at S121 Phase 3; it
is realized in `cranelisp-types`, `cranelisp-typecheck` and the binary.
Alias-only import registration (spec §8.3.6), the last functional gap, was
repaired in `bc675d86`. One obligation remains, a rustdoc repair `arch` owns
(§5).

This document states how module aliases are keyed, written and looked up across
crates. Exact signatures and caller obligations are the rustdoc of
`cranelisp_types::module_alias_key`, `cranelisp_types::substitute_module_alias`
and `cranelisp_types::ModuleAliases`.
[BC 7](bounded-contexts.md#7-cross-crate-types-cratescranelisp-types) and
[interfaces](interfaces.md#resolution) summarize it.

## 1. The spec-derived model

Spec §8.6.6 (worked example §8.4.4) resolves a `module_path` **segment by
segment**:

- The leading segment resolves against the **referring module's own alias
  table**.
- Each subsequent segment is looked up in the resolved-so-far module's alias
  table. Only **public** entries (§8.4.4 export mounts) are traversable from
  outside.
- §8.6.6's closing rule fixes the visibility split.

Aliases are declarations owned by a module, not entries in a global namespace.
The contract below states that model as keyed reads.

## 2. The contract

### 2.1 Storage — one key shape, one mint

- Every alias entry is stored under `<owner>.<name>`, where `owner` is the
  **declaring** module. This covers import aliases (§8.3.4, §8.3.6), export
  mounts (§8.4.4) and submodule short names (§8.2.5).
- `cranelisp_types::module_alias_key` is the one key mint. An empty owner yields
  the bare alias.
- `ModuleAliases` is the session-level map. It is derived state: the same
  writers rebuild it at restore from the persisted table fields that record
  the declarations: `imports`, `submodules` and `exports`. The map is **not serialized**, so aliases
  themselves have no cache-schema contact.
- A `ModuleAliases` newtype with a private interior was declined (Principle 6).
  It is the named successor if a writer ever appears outside the writer
  families in §3.

### 2.2 Lookup — a scoped segment walk of keyed probes

`substitute_module_alias(module_aliases, referring_module, module_path)` applies
§8.6.6 as keyed reads, with no iteration over the map:

1. **Leading segment, referring scope.** Probe
   `module_alias_key(referring_module, first_segment)`. This makes `u/helper`
   resolve after `(import [(main.util u) []])`, and `util/x` after
   `(mod util)`, from the declaring module and only from it.
2. **Segment walk.** After any substitution, and for each further dot segment,
   probe `module_alias_key(resolved_prefix, next_segment)`. On a hit,
   substitute the entry's target for the matched prefix and continue. This is
   the §8.4.4 mount walk (`A.str/split` → `core.string/split`) and gives
   §8.6.6's multi-hop "walks the alias chain" by construction. The shared
   `CHAIN_FOLLOW_DEPTH_LIMIT` bounds the walk: an alias cycle refuses rather
   than spins.
3. **One visibility rule.** A probe whose owner equals `referring_module`
   admits any visibility, because a module always sees its own declarations,
   including its own private aliases spelled in full. Any other probe admits
   `Visibility::Public` only (export mounts).
4. **No match → unchanged.** The path falls through to ordinary module
   resolution, so an *undeclared* alias stays the located
   `module '<x>' … not found` error. A blanket accept-before-slash is never
   admissible.

Precedence follows the spec:

- An alias declared by the referring module shadows a same-named real module,
  because §8.6.6 substitutes aliases before module lookup.
- Duplicate-alias, duplicate-mount and mount-vs-submodule collisions are
  declaration-time §8.6.4-family errors owned by the definition seam: the
  binary's writer for that alias family (§3), which alone sees every
  declaration across forms and REPL turns. At most
  one entry per key therefore reaches the lookup, and the lookup carries no
  ambiguity arm. A re-run declaration upserts its own key as ordinary session
  redefinition.
- Whether the import-alias writer enforces the duplicate-alias error is
  unverified; the writer is a plain insert. `qa` holds this as lead R-A2
  ([review leads](../../tests/plan/s122-evidence-delta.md#review-leads--candidates-not-defects)).

### 2.3 Identity ownership

- `cranelisp-types` owns the map type, the key format (the mint) and the walk.
- Writers own only *which* aliases exist. The binary declares them (imports,
  submodule declarations and their restore); nothing else inserts.
- Consumers own only the referring module they pass.
- No caller re-derives the key format or re-walks segments (Principle 24
  corollary — the resolution product travels; Principle 7 — one mint).

## 3. Writers and consumers

Writers verified against source on 2026-11-18 (`1790531f`); consumers on 2026-09-25.

| Site | Kind | Notes |
|---|---|---|
| `src/imports.rs::install_import_alias` | writer — import aliases | The one import-alias writer; the named (`install_imports`), name-less (`handle_import`) and restore (`install_declared_aliases`) routes all call it. Writes `Private` entries; an alias the module also mounts to the same module stays the mount's `Public` entry. Keys through `module_alias_key`. |
| `src/imports.rs::install_export_mount` | writer — export mounts (§5.1) | The one mount writer; the fresh (`src/process_form/dependency.rs`) and restore (`install_declared_aliases`) routes both call it. Writes `Public` entries. Keys through `module_alias_key`. |
| `src/process_form/dependency.rs::register_submodule_alias` | writer — submodule short names, fresh | Keys through `module_alias_key`. |
| `src/imports.rs::install_declared_aliases` | writer — submodule short names, restore | Keys through `module_alias_key`. |
| `crates/cranelisp-types/src/resolve.rs::resolve_qualified`, `resolve_qualified_candidates` | consumer (types-internal) | Pass the query's current module. |
| `crates/cranelisp-typecheck/src/checker.rs::normalize_self_qualified` | consumer | Passes the checker's current module. |
| `src/process_form/macro_resolution.rs::recognize` | consumer — FQ-autoload boundary | Passes the module whose form is being processed. |
| `src/repl/mod.rs::resolve_symbol_arg` | consumer | Passes the session's current module. |

## 4. Evidence

`qa` owns allocation and adequacy. The alias-only correction's adequacy record
is [alias-only import registration](../../tests/plan/s122-evidence-delta.md#alias-only-import-registration-fixme-0798--correction-adequacy-2026-09-25).

- **Export mounts.** The walk is pinned in the types tier below. The writer's
  refusals and the shared-key rule (§5.1) are pinned in `src/imports/tests.rs`
  (`mount_installs_one_public_route_on_both_routes`,
  `mount_alias_equal_to_a_declared_child_refuses`,
  `second_mount_to_a_different_module_refuses`,
  `import_alias_and_mount_to_one_module_leave_one_public_entry`,
  `import_alias_and_mount_to_different_modules_refuse_in_either_order`). A
  qualified reference through a mount whose declaring module is not yet loaded
  is an open defect:
  [ACT-1079](../../sprints/actions/ACT-1079-qualified-reference-through-a-mount-needs-its-owner-loaded-intake.md).
- **Types unit tier** (`crates/cranelisp-types/src/resolve/tests.rs`):
  - `module_alias_key_is_owner_scoped`;
  - `scoped_alias_exact_and_undeclared_passthrough`;
  - `two_referrers_cannot_borrow_each_others_local_alias`;
  - `public_submodule_mount_walks_by_resolved_prefix`;
  - `private_submodule_mount_is_not_traversed_downstream`;
  - `referring_module_may_traverse_its_private_full_path_mount`;
  - `alias_walk_refuses_more_than_the_shared_depth_limit`;
  - `qualified_resolution_uses_referring_module_alias`;
  - `referring_alias_precedes_same_spelled_real_module`.
- **Binary unit tier** (`src/process_form/tests.rs`):
  `alias_only_import_registers_alias_without_loading` and
  `null_import_registers_no_alias_and_loads_nothing`.
- **Solution tier:**
  - `tests/spec_08_modules.rs::alias_only_import_alias_resolves_qualified_call`;
  - `tests/spec_08_modules.rs::undeclared_alias_qualifier_is_not_resolved_neg`;
  - `tests/spec_08_modules.rs::null_import_does_not_load_its_module`;
  - `tests/cache.rs::cache_alias_only_import_target_reached_by_qualified_call_restores_and_matches_uncached_run`
    (restore parity);
  - `tests/dotted_binder_reject_0702.rs::dotted_module_alias_form_in_import_stays_legal_green`.
- **Allocated elsewhere:** the type-annotation position (`:u/T`) belongs to the
  fresh FQ type-only loading group
  ([evidence delta](../../tests/plan/s122-evidence-delta.md#fresh-fq-type-only-loading--evidence-delta-2026-09-25)).
- **Not observed at solution level**, per a 2026-09-25 search of `tests/`, and
  `qa`'s to allocate or accept:
  - two referring modules binding one alias name to different targets (unit
    tier only);
  - a bare submodule short-name reference (`(mod util)` then `util/x`),
    fresh and warm.

## 5. Outstanding obligation — `module_alias_key` rustdoc

The rustdoc on `module_alias_key` describes the alias walk rather than the
mint and contains a broken sentence. `arch` owns that source-rustdoc repair.
It needs no public-API signature change.

### 5.1 Export mounts

- §2.1 stores a §8.4.4 export mount as a public alias entry and §2.2 walks
  it. The carrier is `ExportSpec::alias`
  ([import and export entries](interfaces.md#import-and-export-entries)).
- **Writer.** The binary installs one `Public` entry per aliased export under
  `module_alias_key(<exporting module>, <alias>)`, targeting the exported
  module. It is the third writer family in §3, in two routes: fresh, when the
  export form is processed, and restore, from the persisted `exports` field.
  Both routes call one function, as the import-alias routes do.
- **Lookup has no mount-specific rule.** Mounts add no probe, visibility rule
  or precedence.
- **Declaration-time errors stay at the definition seam, which is the
  binary's mount writer.** A duplicate mount and a mount that collides with a
  submodule short name are §8.6.4-family errors raised by that one function,
  on both routes, so the walk still meets at most one entry per key (§2.2).
  The frontend raises neither, even within one form: it sees one form and no
  table, and a second check there would be a partial copy of the rule.
- **An import alias and a mount of one spelling share a key** (user ruling
  S124-Q4, 2026-11-17; spec §8.4.4 and §8.6.4).
  - Different targets: the second declaration is refused, in either order, by
    whichever of the two writers meets the occupied key.
  - Equal canonical targets: the pair is one route, and the key holds one
    `Public` entry in either order. The mount writer raises an existing
    private entry to public; the import-alias writer leaves an existing
    public entry as it is.
  - An export with an empty name list and no alias installs nothing and is
    not an error.
- `design`(int) owns the writer's interior; `design`(frontend) owns the
  parser.

## 6. Falsifiers

- **One mint.** A `module_aliases.insert`, or an alias-key construction,
  outside the writer families of §3 or not produced by `module_alias_key` is a
  `review` reject; the check is one grep.
- **No ambiguity arm needed.** A lookup that observes two declarations
  competing for one key would falsify the declaration-seam premise. The cure
  lands at the §8.6.4 definition seam, never in the walk.

## 7. Rejected alternatives

- **Key bare, globally** (store `u` unscoped so lookup matches). One flat
  namespace causes silent cross-module collisions and widens the submodule
  wrong-accept instead of closing it.
- **Retain the global longest-prefix walk as a fallback leg.** Two lookup
  mechanisms for one question is the mirror class (Principle 24). It preserves
  both wrong-accepts and makes the scoped leg untestable in isolation.
- **A parallel scoped map beside the bare map.** A Principle 7 violation: the
  split is representational (`<owner>.` prefix), not a second store.
- **Per-`SymbolTable` alias fields instead of the session map.** This is
  closest to the spec's mental model. However, paths that hold
  `&ModuleAliases` without table access consult the map (the FQ-autoload
  boundary, before loading). The declarations already persist on the table as
  `imports` and `submodules`, so moving the derived map adds a serialization
  surface for no new capability.
