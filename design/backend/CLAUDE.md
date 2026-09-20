# design/backend/

Interior design for the Cranelisp backend — Cranelift code generation, RC and
heap management, JIT lifecycle, caching and linking. Owned by `design`,
narrow-deployed to this crate.

**Start at [backend.md](backend.md).** It is the context master: what the crate
is, its reading discipline, its internal shape, and the index to every
subordinate design. This memory is navigation only and does not restate design
content.

## What lives where

Three carriers, and keeping them distinct is what stops this directory decaying:

| Question | Carrier |
|---|---|
| What crosses the boundary, and what the crate promises the workspace | `design/arch/bounded-contexts.md` §3 |
| What the Rust surface exactly is | Per-item `///` rustdoc in `crates/cranelisp-backend/src/`, with `public-api.txt` as its evidence |
| What runtime behaviour is *correct* | `spec/12-runtime.md` |
| How the crate solves its problems | Here |
| How to work in the code — seam map, debug hooks, conventions | `crates/cranelisp-backend/CLAUDE.md` (`dev`-owned) |

Cite these rather than restating them. The recurring failure in this directory
has been a design doc carrying its own copy of a boundary fact, a signature or a
line-count inventory, and then decaying against it silently.

## Document collection

| Collection | Purpose | Boundary |
|---|---|---|
| `backend-current-designs` | Current backend interior designs and the retained design evidence that cannot be re-derived from source. | The Markdown products directly under `design/backend/`, excluding this memory. |
| `backend-archive-records` | A live IO trace contract retained at its legacy path until the contract and its citations move together. | Markdown products under `design/backend/archive/`. |

Membership is discoverability, not approval: each document's own status decides
whether it is an adopted contract, an open proposal or retained evidence.

## Maintaining these documents

- **Every fact has one home.** Before adding a claim, find its canonical carrier
  and cite it. A second account of a boundary fact is a future contradiction.
- **Retain for a reader, not for a link.** A document earns its place by being
  the canonical source of a current rule, an unresolved obligation, or evidence
  that cannot be re-measured. Executed plans, landed migration steps and
  comparisons against superseded alternatives are Git's job.
- **Extract before deleting.** A still-useful rule or rationale moves into its
  destination in that destination's form first; only then does the original go.
  Deleting a record never resolves an obligation it carried — re-home the
  obligation explicitly.
- **Keep status honest.** Say what is landed, what is open and what is merely
  asserted. A "Live" banner over an executed work-order misroutes the next
  reader, which has cost real sprint time here.
- **Grade claims, don't assert them.** Prefer a property that cannot be
  constructed wrongly; failing that, one an executing check observes; failing
  that, say plainly that it is asserted and name what would falsify it.
- **Verify against source before citing it.** Line numbers decay fastest, then
  file paths, then symbol names. Prefer naming the symbol and its module over
  pinning a line.
- **Cited sections are anchors.** Source and tests cite these documents by
  section number. Check before renumbering or removing one, and repair the
  citation in the same change when it must move.
