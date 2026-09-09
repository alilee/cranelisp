# design/platform/

Solution design for `cranelisp-platform` — the C-ABI contract crate between the
cranelisp host and every platform DLL. Owned by `design`, narrow-deployed to
this surface.

These documents describe *how* the platform layer solves its problems and what
it commits to. They are distinct from:

- `design/arch/bounded-contexts.md` §5 and `design/arch/platform-interface.md` —
  the boundary contract (what crosses, and in which direction);
- `crates/cranelisp-platform/src/**` rustdoc — per-item public truth;
- `crates/cranelisp-platform/CLAUDE.md` — the code's own voice: marshalling
  traps, layout invariants, the submodule seam map;
- `spec/10-io.md`, `spec/12-runtime.md` — what runtime behaviour is correct.

## Live documents

| File | Carries |
|---|---|
| `platform.md` | The master: bounded context, public surface shape, internal shape, the ABI and node layouts, the context invariants, quality attributes, triggered extensions. |
| `platform-dlls.md` | Authoring and loading mechanics — the manifest, the wrappers, the capture-RC protocol, the search path, the reference platforms. |
| `poll-leaf-authoring.md` | The ctx-vtable poll-leaf contract and the `poll_support` scaffolds. |
| `adt-marker-binding.md` | The marker-binding mechanism decision, `arch`-approved. |
| `s121-c7-platform-visit.md` | The Sprint 121 C7 stream design. A visit record: it retires at sprint close, and what it settles lands in `platform.md`. |
| `archive/` | Superseded records, indexed in `archive/README.md`. |

## Conventions

- **Current-state, not changelog.** A design document states what is true now and
  why. Per-sprint pass logs, "what changed this sprint" sections and stacked
  dated banners are the named decay smell; sprint history lives in
  `sprints/archive/` and in git.
- **No censuses.** File counts, line counts and public-item inventories are not
  design invariants, decay silently, and duplicate what `public-api.txt` and the
  source already carry. A design document names shapes and responsibilities.
- **One home per fact.** Boundary narrative goes to `design/arch/`; mechanical
  conventions and API gotchas go to the crate's `CLAUDE.md`; per-item truth goes
  to rustdoc. What is left here is direction, structure and trade-offs.
- **Record rejected alternatives briefly** — considered X, chose Y because Z —
  and record deferred extensions with the **trigger** that would require them. A
  deferral without a trigger is a decision nobody can revisit.
- **Superseded records move to `archive/`** with an index row saying what
  superseded them. Deleting loses provenance; leaving them beside current design
  makes a reader guess which is live.
- **Cite, do not restate.** When a fact belongs to `arch`, `spec` or a
  neighbouring crate, cite it in that owner's language.
