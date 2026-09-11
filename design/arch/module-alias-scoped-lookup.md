# Module-alias scoped lookup — the referring-module contract

**Status: RULING (S121 Phase 3, `/arch`, 2026-09-01) — pre-implementation.**
This is the binding cross-crate contract for FIXME 0798 (a module alias is
never usable as a qualifier; spec §8.3.4/§8.3.6 violation), discharging the C6
blocker H2 (`design/int/s121-c6-visit.md` §5.3, §15). It rules the lookup
contract, its `cranelisp-types` signature, the writers' keying, and the exact
C1→C3→C6 allocation inside the S121 one-visit reservations.

**Archive trigger:** the C1/C3/C6 change-sets land, the 0798 discriminators
flip, and the contract folds into `substitute_module_alias`'s rustdoc +
`interfaces.md` §"Resolution" + BC §7; then this file moves to `archive/`.

## 1. The defect, verified at HEAD (2026-09-01)

Three verified facts, one keying inconsistency:

- **Import aliases are stored scoped, matched unscoped.** `install_imports`
  (`src/imports.rs:63-72`) and its restore mirror (`src/imports.rs:505-511`)
  key an §8.3.4 alias as `<owner>.<alias>` via the int-private `alias_key`
  (`src/imports.rs:542`). `substitute_module_alias`
  (`crates/cranelisp-types/src/resolve.rs:961-995`) matches alias-table keys
  only as dot-segment prefixes of the **queried** module part. For `u/helper`
  the queried part is `u`, the stored key is `main.u` — no match, and the
  §8.3.6 alias-only import form is entirely non-functional (FIXME 0798's
  discriminating control).
- **Submodule aliases are stored bare, matched globally.**
  `register_submodule_alias` (`src/process_form/dependency.rs:921`, invoked at
  `:994`) and the restore mirror's arm (c) (`src/imports.rs:514-522`) key a
  `(mod util)` short name as bare `util`. One flat session map means any
  module's bare reference matches any other module's submodule alias — a
  silent global collision (two parents each declaring `(mod util)` share one
  key) and a cross-module wrong-accept the spec does not license.
- **Visibility is carried but never consulted.** `ModuleAliasEntry` carries
  `Visibility` with rustdoc stating a `Private` alias "is visible only to the
  owning module's own qualified-name lookups"
  (`crates/cranelisp-types/src/module.rs:398-418`), and spec §8.6.6 states it
  normatively — yet the walk reads no visibility, so a private alias's full
  `<owner>.<alias>` spelling is traversable from any module.

The iterate-all longest-prefix walk is an ambient scan deriving a
compile-necessary identity — Principle 24's banned shape. The cure is keyed.

## 2. The spec-derived model

Spec §8.6.6 (worked example §8.4.4) resolves a `module_path` **segment by
segment**: the leading segment resolves against the **referring module's own
alias table**; each subsequent segment is looked up in the
resolved-so-far module's alias table, where only **public** entries (§8.4.4
export mounts) are traversable from outside; §8.6.6's closing rule fixes the
visibility split. Aliases are declarations owned by a module, not entries in a
global namespace. The contract below is that model, stated as keyed reads.

## 3. The contract

### 3.1 Storage — one key shape, one mint

Every alias entry — import alias (§8.3.4/§8.3.6), export mount (§8.4.4),
submodule short name (§8.2.5) — is stored under `<owner>.<name>` where
`owner` is the **declaring** module. The mint is ONE `cranelisp-types`
function hoisted from int's private `alias_key` (the `member_key`/
`trait_impl_key` pattern):

```rust
pub fn module_alias_key(owner: &ModuleFullPath, alias: &str) -> ModuleFullPath
```

with `alias_key`'s existing empty-owner branch preserved. **Bare keys retire**;
every writer and every probe routes through the mint. `ModuleAliases` remains
the session-level map (`src/session_v4.rs:209`) — it is derived state, rebuilt
at restore from the persisted `imports`/`submodules` table fields, and is
**not serialized** (no cache-schema contact). A `ModuleAliases` newtype with a
private interior was considered and declined for this window (Principle 6 —
the C1 wash is already the sprint's largest window); the standing check is the
grep falsifier in §7, and the newtype is the named successor if a writer ever
appears outside the two blessed families.

### 3.2 Lookup — a scoped segment walk of keyed probes

`substitute_module_alias` gains the referring module:

```rust
pub fn substitute_module_alias(
    module_aliases: &ModuleAliases,
    referring_module: &ModuleFullPath,
    module_path: &ModuleFullPath,
) -> ModuleFullPath
```

Semantics — §8.6.6 as keyed reads, no iteration over the map:

1. **Leading segment, referring scope.** Probe
   `module_alias_key(referring_module, first_segment)`. This is what makes
   `u/helper` resolve after `(import [(main.util u) []])`, and `util/x` after
   `(mod util)`, from the declaring module and only from it.
2. **Segment walk.** After any substitution, and for each further dot
   segment, probe `module_alias_key(resolved_prefix, next_segment)`; on a hit
   substitute the entry's target for the matched prefix and continue with the
   remaining segments. This is the §8.4.4 mount walk (`A.str/split` →
   `core.string/split`) and gives §8.6.6's "walks the alias chain"
   multi-hop conformance by construction. The walk is bounded by the
   established `CHAIN_FOLLOW_DEPTH_LIMIT` (alias cycles refuse, they do not
   spin).
3. **One visibility rule.** A probe whose owner equals `referring_module`
   admits any visibility (a module always sees its own declarations,
   including its own private aliases spelled in full); any other probe admits
   `Visibility::Public` only (export mounts). This enforces the §8.6.6
   private/public split the entry rustdoc already asserts.
4. **No match → unchanged.** The path falls through to ordinary module
   resolution, so an *undeclared* alias stays the existing located
   `module '<x>' … not found` error (FIXME 0798's negative twin; C6 §16
   reject 5 — never a blanket accept-before-slash).

Precedence facts, unchanged from spec: an alias declared by the referring
module shadows a same-named real module (§8.6.6 step order — alias
substitution precedes module lookup); duplicate-mount and mount-vs-submodule
collisions are **declaration-time** §8.6.4-family MUST-errors owned by the
definition seam, so at most one entry per key reaches the lookup — a re-run
declaration upserts its own key (ordinary session redefinition), and the
lookup contract carries no ambiguity arm.

### 3.3 Identity ownership

`cranelisp-types` owns the map type, the key format (the mint), and the walk.
Writers own only *which* aliases exist: int declares them (imports, submodule
decls, restore mirrors); nothing else may insert. Consumers own only the
referring module they pass. No caller re-derives the key format or re-walks
segments (Principle 24 corollary — the resolution product travels; Principle 7
— one mint).

## 4. Consumers and writers, exhaustively (verified at HEAD)

| Site | Kind | Change | Stream |
|---|---|---|---|
| `crates/cranelisp-types/src/resolve.rs:799` (`resolve_qualified`) | consumer (types-internal) | pass its existing `current_module` | C1 |
| `crates/cranelisp-typecheck/src/checker.rs:1476` (`normalize_self_qualified`) | consumer | pass `state.current_module` | C3 (mechanical call-site flip in the wash; no design re-open) |
| `src/repl/mod.rs:680` | consumer | pass the session's current module | C6 |
| `src/process_form/macro_resolution.rs:106` (FQ-autoload boundary) | consumer | pass the module whose form is being processed | C6 |
| `src/imports.rs:63-72`, `:505-511` (import aliases, fresh + restore) | writer | already scoped; re-point onto the types mint, delete int's private `alias_key` | C6 |
| `src/process_form/dependency.rs:921`/`:994` + `src/imports.rs:514-522` (submodule aliases, fresh + restore) | writer | flip bare key → `module_alias_key(parent, short)` | C6 |

The C1↔C6 interim (scoped lookup landed, submodule writers not yet flipped)
lies entirely inside the S121 C1-led wash, whose landing model is already
"compilation and the tests stream enumerate the downstream wash"
(the S121 lifecycle migration, retained in Git history); no transitional bare-key fallback arm is
built (Principle 8).

## 5. Allocation and order (H2 discharged)

- **C1 (types, the one S121 window):** the re-signatured
  `substitute_module_alias`, the segment-walk + visibility rule, the hoisted
  `module_alias_key` mint, the internal `resolve_qualified` flip. Rides the
  single S121 `cranelisp-types/public-api.txt` regeneration. **No schema
  contact** — the map is unserialized derived state; `CACHE_SCHEMA_VERSION`
  24→25 remains C1's lifecycle bump, untouched by this contract.
- **C3 (typecheck):** the one `checker.rs:1476` call-site flip, riding the
  existing typecheck wash change-set. Zero typecheck public-API delta.
- **C6 (int, bundle N3):** the writer flips, the two int consumer sites, the
  `alias_key` deletion, and the evidence flips — exactly the §5.3 slot the C6
  visit reserved, now unblocked.

## 6. Public API, schema and ABI effects

| Surface | Effect |
|---|---|
| `cranelisp-types` `public-api.txt` | one changed signature (`substitute_module_alias`) + one added fn (`module_alias_key`), inside C1's single regeneration |
| `cranelisp-typecheck`, backend, runtime pair, platform baselines | none |
| `CACHE_SCHEMA_VERSION` | none (map not serialized; alias declarations already persist as `imports`/`submodules` fields) |
| `ABI_VERSION` | none |

## 7. Acceptance evidence and falsifiers

Evidence (rows are `qa`'s to place — C6 H3 already routes them):

- FIXME 0798's own matrix, both polarities: import shape × reference form,
  including the alias-only form, `:u/T` annotation position, and the dotted
  target column.
- **Scoped isolation:** module A aliases `u`→X, module B aliases `u`→Y — each
  resolves its own; B spelling A's alias bare is the located not-found error.
- **Negative twin:** an undeclared `(v/helper)` remains the located
  "module not found".
- **Submodule parity:** `(mod util)` + bare `util/x` from the declaring parent
  resolves fresh AND warm (the restore-mirror flip is covered, not just the
  fresh writer).
- Unit tier in `cranelisp-types`: leading-segment scoped hit; foreign-probe
  Public filter; multi-hop mount walk; depth-limit refusal; no-match
  passthrough.

Falsifiers of the ruling's premises:

- *"Blast radius is small"* — grounded in the corpus grep (2026-09-01: zero
  `.cl` alias-import or export-mount usage outside the 0702 test family) and
  falsified by the wash's tests stream: a green test that relied on a
  **cross-module bare submodule reference** breaks under scoping. Disposition
  if it fires: the test conforms to spec §8.6.6/§8.5.4 or the question routes
  to `spec` — the unscoped behaviour is not silently preserved.
- *"One mint"* — a `module_aliases.insert` (or key construction) outside the
  writer families of §4 is a `/review` reject; the check is one grep.
- *"No ambiguity arm needed"* — a lookup observed with two entries under one
  key would falsify the declaration-seam premise; the cure lands at the
  §8.6.4 definition seam, never in the walk.

## 8. Rejected alternatives

- **Key bare, globally** (make lookup match by storing `u` unscoped) — the
  hazard C6 §5.3 already named: one flat namespace, silent cross-module
  collision; and it widens the existing submodule wrong-accept instead of
  closing it.
- **Retain the global longest-prefix walk as a fallback leg** — two lookup
  mechanisms for one question is the mirror class (P24); it preserves both
  wrong-accepts indefinitely and makes the scoped leg untestable in isolation.
- **A parallel scoped map beside the bare map** — P7 violation; the split is
  representational (`<owner>.` prefix), not a second store.
- **Per-`SymbolTable` alias fields instead of the session map** — closest to
  the spec's mental model, but the alias map is consulted on paths that hold
  `&ModuleAliases` without table access (the FQ-autoload boundary, pre-load),
  and the declarations already persist on the table (`imports`/`submodules`);
  moving the derived map would add a serialization surface for no new
  capability, in the sprint's one frozen schema window.
