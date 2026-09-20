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

## Document collection

| Collection | Purpose | Boundary |
|---|---|---|
| `platform-current-designs` | Current platform interior designs for the host/DLL ABI, DLL authoring and loading, poll leaves and ADT marker binding. | The four live Markdown products directly under `design/platform/`. |

This is a maintained design collection with live reference checking. It holds
current design only; superseded records are deleted rather than archived, and
git history carries them.

## Live documents

| File | Carries |
|---|---|
| `platform.md` | The master: bounded context, public surface shape, internal shape, the ABI and node layouts, the context invariants, quality attributes, triggered extensions. |
| `platform-dlls.md` | Authoring and loading mechanics — the C-ABI types, the wrappers, the capture-RC protocol, loading, the search path, the reference platforms. |
| `poll-leaf-authoring.md` | The ctx-vtable poll-leaf contract and the `poll_support` scaffolds. |
| `adt-marker-binding.md` | The marker-binding mechanism decision, `arch`-approved. |

A sprint visit record is scratch, not a product here: what it settles lands in
the document that owns the fact, and the visit record goes.

## Conventions

- **Current-state, not changelog.** A design document states what is true now and
  why. Per-sprint pass logs, "what changed this sprint" sections and stacked
  dated banners are the named decay smell; sprint history lives in
  `sprints/archive/` and in git.
- **No censuses.** File counts, line counts, public-item inventories and dated
  call-site surveys are not design invariants, decay silently, and duplicate what
  `public-api.txt` and the source already carry. A design document names shapes
  and responsibilities.
- **One home per fact.** Boundary narrative goes to `design/arch/`; mechanical
  conventions and API gotchas go to the crate's `CLAUDE.md`; per-item truth goes
  to rustdoc. What is left here is direction, structure and trade-offs.
- **Record rejected alternatives briefly** — considered X, chose Y because Z —
  and record deferred extensions with the **trigger** that would require them. A
  deferral without a trigger is a decision nobody can revisit.
- **Delete superseded records; keep no archive.** When a record is superseded,
  fold any detail the current documents still need into the document that owns
  that fact, then delete the record. Git is the provenance store, and a retained
  copy competes with the live document for a reader's trust.
- **Grade a claim that is neither structural nor measured.** Where this surface
  asserts a property it does not enforce or observe — the crate has no capability
  vocabulary, the DLL writes no glue word — the claim carries its falsifier and
  says what grade it holds (root `CLAUDE.md` §Assurance).
- **Cite, do not restate.** When a fact belongs to `arch`, `spec` or a
  neighbouring crate, cite it in that owner's language.
