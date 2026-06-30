---
number: 0483
target: /arch
filed_by: /sprint
filed_at: 2026-06-30
sprint_filed: 97
refers_to: design/arch/principles.md, design/arch/principles/ (new principle file), .claude/commands/arch.md §"manifestation-site"
status: open
---

# Add an /arch principle — make actors + the functions between them explicit BEFORE synthesising a mechanism

## Issue

(User-directed, S97, 2026-06-30 — filed after the model redesign settled.) The S97
"v9 descriptor cut" (FIXME 0482) was a **mechanism synthesised from an inherited frame
with no actor model**. It refined locally-valid step by step (0465 → 0482), passed an
/arch Phase-2 sign-off, and then hit a real heap-overrun blocker in `/dev` — because the
premise (scheduling state carried on user values) was never challenged, only its shape.

The faithful, simple model surfaced only after backing up to an explicit **3-column actor
table** (program / trampoline / platform) plus the **functions between them** (calls,
returns, callbacks). That made the minimal mechanism obvious: opaque handles + a
trampoline-owned `ctx` vtable that is the existing waker GENERALISED (`acquire`/`register`/
`retire`). The generalisation was latent in the existing design; only the explicit
actor/function model surfaced it. The descriptor cut was a net *addition* (header slot,
`desc_out`, a trait); the actor-first model was a net *deletion*.

The methodology has a structural bias: skills optimise *locally* against a pre-framed
input, and no one owns "is this whole approach right?" unless explicitly tasked.
`/arch` — the cross-boundary arbiter — is the right owner of the corrective, but in
practice gets invoked reactively ("rule this shape").

## Proposed resolution

Add an `/arch` principle (one file under `design/arch/principles/NN-*.md`, indexed in
`principles.md`): **establish a clear model of the actors and the functions/contracts
between them BEFORE synthesising a mechanism.** Rationale — actor/interface clarity is the
precondition for a solution that is:
- **faithful** — it maps cleanly onto the real interaction structure;
- **simple** — the minimal mechanism becomes visible once the boundaries are explicit;
- **innovative** — better / more-general designs only become *seeable* once the actors and
  their calls are laid bare (e.g. "the waker is already a platform→tramp callback —
  generalise it").

**Trigger smell to name in the principle:** a design arriving **pre-framed, carried
through multiple incremental FIXMEs** — the lineage signals the *premise*, not the shape,
is overdue for challenge. Before ratifying such a design, run a first-principles /
actor-model / "what would unix / the stdlib do" pass; do not carry the inherited framing
forward as "rule this shape."

## Operational implication / Context

- This is /arch's own principles surface — /arch authors the principle file + index entry
  in its own voice and deletes this FIXME (manifestation-site discipline).
- Captured durably in `/sprint`'s memory `feedback_actors_functions_before_synthesis.md`.
- The triggering redesign is itself the worked example (S97 model pivot;
  `effect-concurrency.md §4.1.1`).
