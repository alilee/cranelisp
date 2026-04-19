# Private Submodule Import Enforcement (Step 5d (i))

Implementation design for the import-resolver check that rejects peer-module imports of names declared inside a `(mod- internal ...)` private submodule.

Spec anchor: `spec/08-modules.md §8.2.3` ("Other modules MUST NOT import from or reference names in a private submodule"). Test contract: `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` (currently failing).

## 1. Problem Statement

The spec specifies private submodules as `(mod- internal)` (or `(mod- internal forms...)` for inline form). A private submodule is accessible only within its parent's subtree — peer modules of the parent MUST NOT import from it.

The test sets up:

```
main.cl              (mod host) (mod consumer) (defn main [] (consumer/run))
main/host.cl         (mod- internal) (defn public-fn [] 1)
main/host/internal.cl (defn private-leaf [] 42)
main/consumer.cl     (import [main.host.internal [private-leaf]])
                     (defn run [] (private-leaf))
```

The `(mod- internal)` declaration in `main/host.cl` makes `main.host.internal` a private submodule of `main.host`. The peer `main/consumer.cl` attempts `(import [main.host.internal [private-leaf]])` — this MUST error.

Today the import resolver (in `src/worker.rs::handle_import`) treats `main.host.internal` as a regular module path, resolves it via the standard module-search order (§8.11.2), loads `main/host/internal.cl`, and proceeds. There is no privacy check at the inter-module boundary because nothing on the resolved path tells the resolver that `internal` was declared private by its parent.

Step 5a adds the missing piece: the parent's `(mod- internal)` declaration is recorded as `ModDecl { name: "internal", is_private: true, ... }` on `SymbolTable.submodules` (per Decision 33). With that record in place, the import resolver can ask "is the module being imported a private submodule of someone other than the importing module?" and reject if yes.

## 2. Key Design Decisions

### 2.1 Privacy-record source-of-truth

**Choice**: `SymbolTable.submodules: Vec<ModDecl>` (Step 5a) is the authoritative record. `ModDecl::is_private` distinguishes `(mod- name)` from `(mod name)`.

The check at import time queries the *parent module's* `submodules` for an entry matching the trailing component of the imported module path:

- Importing `main.host.internal` from `main.consumer`.
- Parent of `internal` is `main.host`.
- Look up `symbol_tables["main.host"].submodules` for `ModDecl { name: "internal", is_private: true, .. }`.
- If found and `is_private` is true: reject the import.

### 2.2 Where the check fires

**Choice**: in `src/worker.rs::handle_import`, immediately after parent-module resolution and before file-system resolution.

Sequence in `handle_import` per spec (post-Step-5d):

1. Null-import shortcut (`ImportNames::None`) — unchanged.
2. **NEW**: derive the parent module path of `spec.module_path`. If the parent is a known module in `symbol_tables`, look up its `submodules`. If the trailing component matches a `ModDecl` with `is_private: true`, AND the importing `module` is not the parent itself or a descendant of the parent, reject with a spec-cited error.
3. Already-loaded shortcut — unchanged.
4. File resolution and load — unchanged.

### 2.3 "Descendant of the parent" rule

Per spec §8.2.3: "accessible only within the declaring module and its submodule subtree". So `main.host` itself can import `main.host.internal`; `main.host.public-leaf` (a hypothetical other public submodule of `main.host`) can also import; `main.host.internal.deeper` can import. Only modules outside the `main.host.*` subtree are rejected.

Algorithm: importing module path is `consumer_path`; the parent of the private submodule is `parent_path`. Allow if `consumer_path == parent_path` OR `consumer_path` starts with `parent_path + "."`. Otherwise reject.

Edge case: `main` (the root) imports `main.host.internal`. Parent of `internal` is `main.host`. `consumer_path = "main"`. `"main"` is not equal to `"main.host"` and does not start with `"main.host."`. Reject. (This is correct per spec — `main` is a peer of `host`, not within `host`'s subtree.)

### 2.4 Parent-loaded-yet check

The check requires the parent module to be loaded so its `submodules` field is populated. Two cases:

1. **Parent already loaded**: most common case (the `main.cl` entry point typically references the parent first). Check fires.
2. **Parent NOT loaded** when the private import is encountered: rare but possible if the importer file is processed first. In this case the parent isn't in `symbol_tables` yet and we can't check. Two options:

   - **Option A (preferred)**: trigger the parent's load before resolving the private-import question. The scheduler's existing `block_for_typecheck` path is exactly the right primitive — block the importer until the parent's signatures (including `submodules`) are registered.
   - **Option B**: skip the check if the parent isn't loaded; allow the import to proceed. Spec violation.

Option A is correct; the cost is one extra dep in the scheduler graph for the parent. Implementation: in `handle_import`, if we want to consult `parent_path.submodules` and `parent_path` is not in `symbol_tables`, register it for typecheck and `BlockAction::Block` on it (same pattern handle_import already uses for the import target itself).

### 2.5 Error shape

The error MUST be spec-cited and clearly indicate why the import was rejected. Suggested form:

```
ModuleError: cannot import from private submodule
  module 'main.host.internal' was declared private by 'main.host' via (mod- internal)
  the import in 'main.consumer' is rejected because 'main.consumer' is not within
  the 'main.host' subtree (spec §8.2.3)
  at <span>
```

Exact wording is implementation choice; the assertion in the test uses `result.is_err()` with no message check, so latitude is wide.

## 3. Data Flow

```
consumer.cl: (import [main.host.internal [private-leaf]])
   │
   ▼
src/worker.rs handle_import(ctx, "main.consumer", spec={ module: "main.host.internal", ... })
   │
   ├─ NEW STEP: privacy check
   │   ├─ parent_path = parent_of("main.host.internal") = "main.host"
   │   ├─ trailing_component = "internal"
   │   ├─ ensure parent_path is loaded (block on it if not — Option A above)
   │   ├─ peek symbol_tables["main.host"].submodules
   │   ├─ find ModDecl { name: "internal", is_private: true, .. } — MATCH
   │   ├─ check importing_module ("main.consumer") within parent_path subtree:
   │   │   "main.consumer" != "main.host" and !startswith("main.host.")
   │   │   ⇒ NOT within subtree
   │   └─ ⇒ return Err(ModuleError { ... spec §8.2.3 ... })
   │
   └─ (if check passes) — proceed to existing flow (already-loaded shortcut, etc.)
```

## 4. Affected Files

| File | Change |
|---|---|
| `src/worker.rs` | Insert the privacy check in `handle_import`. ~30 lines: parent_path extraction, parent-load gate (reuse existing `block_for_typecheck`), submodules lookup, subtree containment check, error emission. |
| `crates/cranelisp-types/src/module.rs` | Already gets `submodules: Vec<ModDecl>` in Step 5a. No additional changes for 5d (i). |
| `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` | Currently failing; flips green when the check lands. |

## 5. Edge Cases & Invariants

- **Importer is the parent**. `(import [main.host.internal [...]])` from `main.host`. `consumer_path = parent_path`. Allowed.
- **Importer is a descendant of the parent**. `(import [main.host.internal [...]])` from `main.host.other`. `consumer_path` starts with `parent_path + "."`. Allowed.
- **Importer is a deeper descendant of the private module**. `(import [main.host.internal [...]])` from `main.host.internal.sub`. Starts with `main.host.`. Allowed.
- **Root-level import of a private submodule**. `(import [main.host.internal [...]])` from `main`. Rejected (correct — `main` is peer to `host`, not within its subtree).
- **Private submodule with no parent module loaded**. Block on parent load. If the parent doesn't exist as a file, the import still fails — the existing module-resolution error fires first, before the privacy check matters.
- **Top-level mod-** — `(mod- internal)` at the root project module. `parent_path = "main"` (the root). Standard subtree rule applies.
- **Multi-level private**. `(mod- internal)` declared in `main.host`; `(mod- private)` declared in `main.host.internal`. Importing `main.host.internal.private` from `main.host`: `parent_path = "main.host.internal"`, which is itself private. The recursive check is implicit — the privacy check on `main.host.internal.private` succeeds for the inner-most check (importer within subtree), but the importer also imports `main.host.internal` as a transitive dep, which triggers a privacy check for `main.host.internal` (private to `main.host`); since `consumer_path = "main.host"` IS the parent, that check passes too. So nested private modules work correctly under the per-level check; no recursion needed.
- **Re-export laundering**. If `main.host` has `(export [internal/private-leaf])`, the spec says the public name is now `main.host/private-leaf` (re-exported). Importing `main.host` and getting `private-leaf` IS allowed — it's the parent's authored choice to publicise the inner name. The privacy check fires only on imports of the inner module *path itself*, not on imports of names re-exported from the parent.

## 6. Cross-Skill Coordination

| Skill | Coordination |
|---|---|
| `/spec` | Spec §8.2.3 already exists; the test annotation at the spec section references this implementation. Once the test passes, `/qa` updates the annotation from `[Tested+Neg ... — FAILING]` to `[Tested+Neg]`. |
| `/typecheck` | The Step 5a `submodules` field is the data input. Confirms in `ast-annotation.md` §11 that `is_private` is preserved through the form-handler write. |
| `/qa` | Confirms `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` flips from failing to passing. Optional: add positive-path companion (a peer import of a *public* submodule succeeds — likely already covered, sanity-check). |

## 7. Sketch Comparison

The sketch did enforce private-module visibility but at a different level: `defn-` (private function) was checked at import-resolution time by inspecting the per-symbol `visibility` field on `ModuleEntry::Def`. Private submodules (`mod-`) were less consistently enforced — the sketch's module loader did parse the `mod-` form but treated the privacy as advisory at the symbol level rather than gating the module load itself. This was a known sketch gap (referenced in `sketch/audits/` though not by an audit number); the reimplementation tightens the contract to gate at the module-load boundary, matching the spec's "MUST NOT import from or reference names in" wording.

The sketch's per-symbol-visibility check still applies for individual `defn-` private functions (`Visibility::Private` on `ModuleEntry::Def`); that path is unchanged here. Step 5d (i) closes the orthogonal gap of module-level privacy.

The reimplementation's mechanism (parent-table `submodules` field with `is_private: bool`, checked at import time against subtree containment) is structurally simpler than the sketch's: one source of truth (the parent's structural-decl record), one check (subtree string-prefix), no recursion. The sketch would have to walk a per-module privacy graph to handle nested cases; the per-level check above handles them implicitly.

## 8. Open Questions

- **Should the error message name the original `(mod- internal)` declaration's span?** Nice-to-have; the parent's `submodules` records the span (`ModDecl.span`). If easy to plumb through, include it; otherwise omit. Not required for the test to pass.
- **Behaviour when the parent module fails to typecheck**. Today's `handle_import` blocks waiting for the parent; if the parent then errors, the importing module errors transitively. The privacy check inherits this behaviour — no additional special-casing.

## 9. Next Skills

- `/typecheck` — `ast-annotation.md` §11 confirms `submodules` carries `is_private` correctly.
- `/qa` — verify test flips green; consider positive-path companion test for public submodule peer-import (sanity check).
- `/spec` — update `[Tested+Neg ... FAILING]` annotation at §8.2.3 to `[Tested+Neg]` after the test passes.
