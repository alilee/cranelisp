# Resolve-Home-Then-Enumerate — closing the `enumeration-miss` class (E3 + FIXME 0558 + E8)

**Status: DESIGN (S108 Increment 3, Phase 2; E8 extension added after the Stage-1
repro confirmed the prelude-VIEW gap) — IMPLEMENTED Wave B** (E3 + 0558 + E8 landed;
§3 rule 2 + §4 amended at Inc3 close per FIXMEs 0562/0563 — the in-flight FAILURE
exit / `on_module_failed` zero-row skip and the cache-hit terminal-entry edge). The unifying
ruling for the recurring `class=enumeration-miss` / wrong-scope-lookup defect family,
so the class cannot recur again. Consumers: Wave B (`/dev`, src/int) for the
three live instances (E3, 0558, E8); `/qa`/`/testing` for the guards.

> **Model note (S108 Wave G reframe).** The prelude is *just*
> `(import [prelude [*]])` (spec §8.8.1); a prelude-provided name is in a
> module's scope on identical terms to an explicit import, and **"outer
> scope" is not a language concept** — consulted-on-miss is a resolution
> *mechanism* (the per-module `prelude_fallback` bit, S78). Where this doc
> says "prelude fallback" / "prelude hop" it names that mechanism, never a
> scoping level with its own rules. The CHECK-path counterpart — ONE lookup
> with the fallback intrinsic + ONE §8.6.4 definition seam — is ruled in
> **`prelude-import-convergence.md`**; the E9 sighting recorded below is
> confirmed, fixed (S108, `lookup_trait_decl_or_prelude`), and folds into
> that convergence's collapse map.

## 1. The class and its register

One defect class, five confirmed sightings (+ one suspected) — each fixed
per-instance until now:

| Instance | Site | Symptom |
|---|---|---|
| S108 Inc1 **D1** (fixed) | `src/repl.rs::format_type_display` + `format_def_entry` ctor arm | constructor chain-lookup rooted at `current_module_path()` instead of the type's resolved home → prelude-globbed seeded ADTs dropped `; match:` / mis-qualified |
| S108 Inc2 **E1/E2** (fixed) | `src/session_v4/index_worker.rs` seeded modules | seeded `primitives`/`macros` absent from the `/search` index → direct live-table read added at arm time |
| **E3** (open, this increment) | `index_worker.rs:548` branch (a) | `is_registered(module) → mark_skipped` records ZERO rows for a loaded module → its importable-not-in-scope symbols invisible to `/search` (spec §17.19 R10 violated) |
| **FIXME 0558** (open, this increment) | `src/repl.rs::format_trait_display` (~L2750) | trait section-lookups rooted at `current_module_path()` → a prelude-globbed trait can drop `; defn:`/`; impl:` (D1's shape in the trait path) |
| **E8** (open, this increment) | `src/repl.rs::format_builtin_type_display` (~L2807) + `format_type_display` `; impl:` arm (~L2737) | the type-side `; impl:` VIEW's candidate-trait enumeration walks only the asking module's own table entries → prelude-globbed traits (no inner-table `Import` under S78) never enter the candidate set → bare `Int` shows NO `; impl:` (spec §4.1.3 requires `; impl: Display Eq Num Ord`). RED: `repl_introspection::type_impl_section_includes_prelude_globbed_trait_impls_probe` |

Sixth sighting (S108 E9): the `impl`-form's CHECK-time trait-name resolution
(`cranelisp-typecheck` `impl_check.rs` → the then-fallback-less
`lookup_trait_decl_with_state`) → `(impl <prelude-globbed-trait> <local-type>)`
failed `unknown trait`. **Confirmed and fixed in S108** (the
`lookup_trait_decl_or_prelude` sibling; pinned by
`repl_introspection::impl_of_prelude_globbed_trait_resolves_trait_name`) —
and the fix's shape (one more `_or_prelude` variant) is itself the disease
one level up: the CHECK path had grown SIX per-site fallback variants, each
new site free to forget the hop. That whole family is converged by
**`prelude-import-convergence.md`** (ONE lookup, fallback intrinsic; E9's
variant ceases to exist as a distinct function).

The common premise error (Principle 21): a lookup/enumeration is rooted at *the scope
the question was asked from* when the question is actually about *a resolved home* —
or an enumeration covers *some* sources of its kind and marks itself complete anyway.
E8 shows the second half in a *view* walk: the view's candidate SET was incomplete
(missing the prelude-fallback names visible from the asking module) even though
its per-candidate rooting was correct.

## 2. Actors and the functions between them

**Display side** (0558): the resolution **gate** — `lookup_with_prelude_fallback`
(repl.rs, the S87 Principle-7 canonical three-tier walk: current module → prelude
fallback hop (bit-gated) → root) + `resolve_entry_for_display` (chain-follow to the
terminal Def) — produces `(entry, resolved_home)`. Downstream **formatters**
(`format_def_entry` → `format_type_display`/`format_trait_display`) render sections by
calling the `cranelisp-types` chain helpers (`lookup_type_def_chain`,
`lookup_trait_decl_chain`, `get_implementing_types_chain`, `get_impls_for_type_chain`).
The function between gate and formatter is *"here is the entry AND its home."*
Every past instance of the class is a formatter that dropped the home half and
re-resolved from scope — where the prelude-provided name has no inner-table
`Import` entry (S78: the fallback bit carries it, not a materialised edge), so
the chain-follow misses.

**Index side** (E3): the **importable-source set** is `seeded ∪ loaded/registered ∪
file-only`. Actors: the nice index worker (`index_one_module`), the scheduler registry
(`is_registered`, pool states), the **live symbol tables** (`SharedState.symbol_tables`
— a mounted module's published public surface), the `.meta` cache + source files
(an UNmounted module's surface), and `ImportableIndices` (the derived index; int-
private, `Mutex`-guarded, NOT serialized, rebuildable — no `CACHE_SCHEMA_VERSION`
involvement). The publication edge for a mounted module's signatures is the terminal
typecheck-pool transition (`notify_typecheck_done`, Invariant PP — happens-after the
Defs are installed). The one table→rows projection already exists:
`public_entries_from_table`.

## 3. The ruling (the class rule)

Two halves, both bindings on future work in these paths:

1. **Resolve the home ONCE, at the gate; enumerate AT the home.** A display/
   introspection formatter takes `(entry, home)` from the canonical gate and roots
   every section chain-lookup at `home` — where the definition is LOCAL, so the chain
   terminates at depth 0 and the prelude-fallback question can never arise.
   Formatters MUST NOT re-resolve from `current_module_path()`. (The deliberate
   exception is a genuine **view question** — Decision-45 Pattern B, e.g. the
   type-side `; impl:` "which traits does this type implement *as visible from
   here*" — which is scope-rooted by semantics, not by accident. **Scope-rooted
   governs the per-candidate ROOTING and the answer's frame, not the candidate
   SET**: the asking module's scope *includes every prelude-provided name*
   whenever its `prelude_fallback` bit is ON (S78 §2 — the bit is the §8.8.1
   implicit `(import [prelude [*]])`, realised as a fallback), so a view
   walk's candidate enumeration falls under rule 2 and must cover the prelude hop.
   E8 is the defect of reading "scope-rooted" as "inner table only". See §5a.)
2. **An enumeration covers ALL sources of its kind, through ONE reader per source
   kind; no source is marked complete without contributing its rows.** For the
   `/search` index: seeded, loaded/registered, and file-only modules must each land
   rows; a mounted module's rows come from the live table via
   `public_entries_from_table` (the single projection — Principle 7); an unmounted
   module's from `.meta`/typecheck (branches b/c). `mark_skipped`-with-zero-rows is
   legal only for genuinely row-less outcomes (no source file, empty module, CF.2
   error skip, a registered-and-**FAILED** module — the `on_module_failed`
   failure-edge skip, FIXME 0562/0563) — never for "someone else owns it". The
   completion-accounting obligation: **every enumerated source reaches `indexed`
   either by contributing rows or by a legal zero-row skip — including via the
   failure edge**; an outcome with neither wedges the burn-down. For a **view walk** (Pattern B),
   the sources of kind "name visible from here" are the module's inner table ∪ the
   prelude-provided names (bit ON, public heads only — the I-1 discipline); an
   enumeration that walks only the inner table is incomplete (E8).

## 4. Mechanism — E3 (`/search` covers loaded modules)

Branch (a) (`index_worker.rs:544-551`) is replaced by a **live-table feed for mounted
modules**, the same reader the Inc2 seeded feed already uses:

- **At arm time** (`arm_burndown`): after the seeded direct-read, sweep the scheduler
  registry for already-registered modules in a TERMINAL typecheck state and record
  their rows from the live table (`public_entries_from_table`). Accounting uses the
  `record_preindexed` dual-tally shape (module counted in both `enumerated_total` and
  `indexed`) for modules outside the file-enumerated set; a module that WAS
  file-enumerated records via the ordinary single-tally path.
- **At the publication edge**: when the index is armed, the terminal-transition site
  (`notify_typecheck_done`, or its immediate caller) feeds the same recorder for the
  transitioning module. This covers all three timing cases uniformly — a module
  in-flight at arm time, a module loaded LATER by `/import`/FQ-autoload, and a module
  RELOADED by the watcher (index refresh) — with no polling and no worker respin.
  (These three are the publish-path timings; the fourth in-flight outcome —
  failure — never reaches this hook and is covered by the `on_module_failed`
  zero-row skip, below.)
- **Branch (a) proper** then reduces to: `is_registered(module)` → if terminal, record
  from the live table now; if in-flight, do nothing (leave pending — one of the
  module's exit edges completes it). An in-flight module has THREE exits, all of
  which must land accounting (FIXME 0562/0563 — the original two-exit wording wedged
  `pending_count` for a registered-and-failed module): **publish**
  (`notify_typecheck_done` — the publication hook records its rows), **fail**
  (`notify_module_failed` → `ModulePool::Failed` — never publishes, never reaches the
  publication hook; the symmetric failure-edge hook `on_module_failed` records a
  legal zero-row skip so the burn-down completes), and **shutdown** (burn-down
  abandoned with the session). The misleading "its `.meta` is read later" path is
  deleted.
- **Refresh semantics**: re-recording a module REPLACES its rows (a
  `replace/re-record` variant beside `record_entries` — remove the module's existing
  `IndexedEntry` rows, insert the new set, idempotent on `indexed`/`enumerated_total`
  tallies). Required so watcher reloads and REPL redefinition don't duplicate or
  stale-serve rows.
- **Accounting invariants** (guarded by unit scenarios per Principle 23):
  `pending_count = enumerated_total − indexed.len()` stays ≥ 0, reaches 0 (the
  completion notice fires), and is unaffected by feed order (arm-vs-hook, the S-1
  order-independence property already established for the seeded feed).
- **Terminal-entry edges** (FIXME 0563 note): `notify_typecheck_done` is hooked, but
  it is NOT the only entry into a terminal pool — `register_module_cached` /
  `register_module_cached_no_object` (`scheduler.rs`) install a cache-hit module
  directly in `TypecheckDone`, bypassing the hook. This edge is covered **by
  construction** today: a cache-hittable module necessarily has its `.cl` under the
  arm-time enumeration roots (`lib_dirs` are startup-fixed), so branch (b) already
  landed its `.meta` rows, and for a valid cache the `.meta` content equals the live
  table. **Precondition: lib-dirs immutable after arm.** A future change — mid-session
  lib-dir mutation, or a cache-hit path that skips `.meta` row projection — reopens an
  enumeration miss through this unhooked edge and must hook it (or feed the recorder
  at registration) in the same change-set.

Negative pins (the S108-Inc2 lesson, for `/qa`/`/testing`): loaded-not-in-scope symbol
IS found post-fix; the R13 in-scope exact match still marked-but-shown; an UNloaded
module still indexes via b/c; a mid-flight module's rows appear after its terminal
transition without a second `/search` note.

## 5. Mechanism — FIXME 0558 (trait sections root at the home)

`format_trait_display` currently re-resolves (`resolve_terminal_entry_and_home` rooted
at scope, no prelude hop) and roots `lookup_trait_decl_chain` +
`get_implementing_types_chain` at `scope`. Its ONLY session caller,
`format_def_entry`'s `TraitDecl` arm, **already holds the resolved home** — the
`module` parameter produced by the gate (`lookup_with_prelude_fallback` →
`resolve_entry_for_display`). The D1-shaped fix:

- `format_trait_display(name, docstring, full_impl_section, home: &ModuleFullPath)` —
  the home is passed in; the internal re-resolution and its scope fallback are
  DELETED.
- The primary line qualifies with `home` (`:{home}/{trait_name} ; deftrait`), and both
  section lookups root at `home`, where the `TraitDecl` is local (depth-0) — so the
  §4.1.4 unconditional `; defn:`/`; impl:` sections survive the prelude glob.
- Rooting the impl enumeration at the trait's home is COMPLETE by construction:
  Decision 0045 writes every `impl$Type$Trait` entry into the **trait's defining
  module**, so "implementing types of trait T" is a home question, not a view question
  (impl reachable ⟺ trait reachable — Principle 17 shape 3).

## 5a. Mechanism — E8 (type-side `; impl:` view includes the prelude hop)

The former Pattern-B note deferred this as a `/qa` repro question; the repro is now
CONFIRMED (Stage-1 RED
`repl_introspection::type_impl_section_includes_prelude_globbed_trait_impls_probe`:
bare `Int` under the test-standard prelude renders `:primitives/Int ; type` with NO
`; impl:` section; spec §4.1.3 requires `; impl: Display Eq Num Ord`). This section
is the binding extension.

**Why it misses.** `cranelisp_types::get_impls_for_type_chain` (module.rs:2633)
builds its candidate-trait set by walking the ASKING scope's own table entries
(`TraitDecl` | `Import`, module.rs:2644-2653), then — correctly — resolves each
candidate's home and probes the home's `TraitImpl` rows (Decision 0045). Under S78
the prelude fallback contributes NO inner-table `Import` entries — that is the
design — so every prelude-globbed trait is absent from the candidate set. The
per-candidate home-rooting was never the bug; the candidate SET was (§3 rule 2).

**The fix (int-side; the two readers consumed unchanged).** When the asking scope's
`prelude_fallback` bit is ON (and scope ≠ `prelude` — the `prelude_fallback_target`
guard semantics), the candidate-trait enumeration is the UNION of:

- the inner-scope run — `get_impls_for_type_chain(tables, scope, tn)` as today; and
- the prelude-hop run — the same reader rooted at the `prelude` module's path,
  restricted to prelude heads that pass the **I-1 public-only filter** (a PRIVATE
  prelude trait must not leak into a user view; same discipline as
  `recognize_macro_head`'s post-filter and typecheck's `prelude_terminal_visible`).
  Since the reader takes no visibility parameter and `cranelisp-types` does NOT
  change, the filter is an int-side POST-filter: drop any prelude-run trait name
  whose head entry in prelude's own table is not `is_public()` (existing lookup
  readers suffice).

Results merge by bare `TraitName`, sorted + deduped (name-dedup is safe: a
scope-local trait and a distinct prelude trait sharing a bare name is a poisoned
name upstream per spec §8.6.5, so the union cannot silently conflate two live
traits). Per-candidate probing is UNCHANGED — resolve the candidate's home,
enumerate `TraitImpl` rows AT the home (rule 1 stands; Decision 0045 makes the
per-trait answer complete by construction).

**The seam — ONE wrapper, both formatters.** Both call sites live in `src/repl.rs`:
`format_type_display`'s `; impl:` arm (~L2737) and `format_builtin_type_display`
(~L2807). The fix routes BOTH through one session-side helper (e.g.
`impls_for_type_in_view(&self, tn) -> Vec<TraitName>`) that performs the union —
never two hand-rolled hops (Principle 7; the Inc1-D1/D2 mirror lesson — fixing one
formatter and not its sibling is how this class recurs). The session already reads
the bit session-side (`SharedState.prelude_fallback`; precedent: `describe_symbol`'s
prelude hop, `handle_imports`' "Prelude (implicit)" group).

**Negative pins (for `/qa`/`/testing`, beside §4's):** prelude-globbed trait impls
DO appear on bare `Int` and on a user deftype; a suppressed prelude
(`(import [prelude []])`) shows NO prelude-trait rows; a private prelude trait's
impl does NOT appear; the empty-`; impl:`-omitted rule for types (§4.1.3, unlike
the trait display's unconditional sections) is unchanged.

## 6. Boundary confirmations

- **No `cranelisp-types` public-API change.** The chain helpers are consumed
  unchanged — home-rooting (0558) is a call-site argument change in int, and the E8
  prelude hop is int-side enumeration over the EXISTING readers (a second
  `get_impls_for_type_chain` run rooted at `prelude` + an int-side public-head
  post-filter; §5a). No new resolution primitive is needed: the gate already exists
  (`lookup_with_prelude_fallback`, S87), and the bit is already session-side
  (`SharedState.prelude_fallback`).
- **No cache/schema impact.** `ImportableIndices` is int-private, unserialized,
  rebuildable (its own rustdoc); 0558 and E8 are display-only. The publication-edge
  hook reads live state only.
- **Ownership**: all three fixes (E3, 0558, E8) are `/dev` (src/, int) on this
  design; `format_*` display strings are also inside the E4 styling-seam migration
  (`repl-styling-seam.md`) — Wave B (this doc) lands BEFORE Wave D (styling) per the
  sprint sequencing, so the styling conversion picks up the corrected section
  content.
- **E9 is NOT this design.** It reproduced, was fixed in `cranelisp-typecheck`
  (S108, the `lookup_trait_decl_or_prelude` sibling), and its variant folds into
  the CHECK-path convergence — see `prelude-import-convergence.md` §3.3 (the
  collapse map) and the §1 register note above.

## Next skills

- `/testing` — QA-first failing repros: E3 loaded-module search (recipe in
  `sprints/SPRINT.md` §E3, + the negatives in §4), 0558 prelude-globbed trait
  sections (recipe in the FIXME; confirm it reproduces — if not, record that and
  close), E8 negatives (§5a; the positive RED is already committed), and the E9
  minimal repro (§1 footnote — repro precedes any fix dispatch).
- `/qa` — PLAN rows; E9 attribution confirm (expected: `cranelisp-typecheck`,
  `lookup_trait_decl_with_state`).
- `/dev` (src/, int) — Wave B implementation (E3 + 0558 + E8).
- `/design` (int) — fold the index-feed lifecycle into `design/int/agent.md` §25 (the
  index-worker design home) at implementation time.
