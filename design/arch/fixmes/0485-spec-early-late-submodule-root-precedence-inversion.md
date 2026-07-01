---
number: 0485
target: /spec
filed_by: /sprint
filed_at: 2026-07-01
sprint_filed: 97
refers_to: spec/08-modules.md §8.11.2, src/process_form/dependency.rs (resolve_current_module_relative, handle_import/handle_export early), src/imports.rs (install_imports late), src/process_form/... (install_exports late)
status: open
---

# Bare-name module resolution: early (submodule-first) vs late (root-first) precedence inversion

## Issue

Surfaced by `/review` (S97 Wave 3b re-review of `cd8025d`). Bare current-module-relative
module-name resolution (spec §8.11.2 step 1) now runs at TWO stages, and they disagree on
precedence for a dual-name shape:

- **Early stage** (`handle_import`/`handle_export` → `resolve_current_module_relative`,
  `dependency.rs`): prefers the **submodule** candidate `<current>.<name>` whenever it exists
  ("submodule-first", per its own units + §8.11.2).
- **Late stage** (`install_imports`/`install_exports`, `imports.rs`): tries the name **as-is
  (root)** first, only falling back to `<current>.<name>`.

They diverge **only** in the dual-name shape: a root module `child` AND a submodule
`parent.child` are both loaded, with `(import [child …])` (or the export analogue) written
inside module `parent`. The early stage loads/binds the **submodule**; the late stage
re-resolves and collects from the **root** → the binding is sourced from the wrong module.

This is **pre-existing** — it existed on the export side before Wave 3b; the Wave-3b import
mirror faithfully copied the already-inverted late-stage pattern (it did NOT introduce the
inversion). It needs an unusual project shape (colliding root+submodule names) to trigger, so
it is **non-blocking** and was correctly not expanded into Wave 3b.

## Proposed resolution

1. **/spec** — ratify the intended precedence in `spec/08-modules.md §8.11.2`: is a bare name
   inside module `M`, where both a root `name` and a submodule `M.name` exist, resolved
   **submodule-first** (current-module-relative wins — the early stage's behavior, and the
   natural "nearest scope" reading) or **root-first**? State it normatively so both stages
   agree.
2. **/int** — align the late `install_imports`/`install_exports` stage to the ratified
   precedence (submodule-first, if that is the ruling — swap the try-order).
3. **/qa** — add a dual-name guard pinning the ratified precedence (both import and export).

## Operational implication / Context

- Minor sibling (`/review` noted): `direct_import_deps` (`dependency.rs` ~:530, the static-
  closure **cycle gate**) uses bare `spec.module_path` raw, so a bare-submodule import resolves
  as an edge-free leaf there. This is the gate's documented conservative behavior (unresolvable
  dep → leaf, never a false cycle; a real cycle is still caught by the dynamic
  `block_for_typecheck` acyclicity scan). Not a defect — noted for completeness.
