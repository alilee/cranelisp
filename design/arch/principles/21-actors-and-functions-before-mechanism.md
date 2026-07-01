---
number: 21
title: Model the actors and the functions between them before synthesising a mechanism
---

# Principle 21 — Model the actors and the functions between them before synthesising a mechanism

**Statement.** Before synthesising a mechanism for a cross-boundary problem, make the **actors** explicit (who participates — program, trampoline, platform, host, reactor, worker, …) and the **functions between them** explicit (every call, return, and callback that crosses an actor boundary, named with its direction and its contract). Only once the actor/interface model is laid bare do you choose the mechanism. The model is the precondition for the solution, not a diagram drawn after it.

**Rationale.** A mechanism synthesised without an explicit actor model is optimised *locally* against whatever framing it inherited. It refines step by step — each increment locally valid — while the **premise** (which actor owns which state, which function carries which guarantee) is never challenged, only its shape. This is a structural bias of the methodology: skills optimise against a pre-framed input, and no one owns the question "is this whole approach right?" unless explicitly tasked. `/arch` — the cross-boundary arbiter — is the right owner of that question, but is too often invoked reactively ("rule this shape") when the shape is already downstream of an unexamined premise.

Making the actors and their functions explicit delivers a solution that is:

- **faithful** — it maps cleanly onto the real interaction structure, because the interaction structure was written down first;
- **simple** — the minimal mechanism becomes *visible* once the boundaries are explicit; the accidental additions (extra header slots, side-tables, new traits) that a locally-refined design accretes are revealed as unnecessary;
- **innovative** — better and more-general designs only become *seeable* once the calls are laid bare. A generalisation latent in the existing design surfaces (e.g. "the waker is already a platform→trampoline callback — generalise it into acquire/register/retire" rather than inventing a parallel mechanism).

**Trigger smell — name it and stop.** A design arriving **pre-framed and carried through multiple incremental FIXMEs** is the smell. The lineage itself is the signal: when a shape has been refined 0465 → 0482 → … each step locally valid, the *premise* is overdue for challenge, not the shape. Before ratifying such a design, run a first-principles pass: draw the actor table (one column per participant) and the functions between the columns (calls / returns / callbacks, with direction and contract); ask "what would unix / the stdlib / a from-scratch design do here?" Do **not** carry the inherited framing forward as "rule this shape."

**Worked example — the S97 concurrency model pivot (`design/arch/effect-concurrency.md §4.1.1`).** The S97 "v9 descriptor cut" (FIXME 0482) was a mechanism synthesised from an inherited frame with no actor model. It refined locally-valid step by step (0465 → 0482), passed an `/arch` Phase-2 sign-off, and then hit a real heap-overrun blocker in implementation — because the premise (scheduling state carried on user values) was never challenged, only its shape. The faithful, simple model surfaced only after backing up to an explicit **3-column actor table** (program / trampoline / platform) plus the **functions between them** (calls, returns, callbacks). That made the minimal mechanism obvious: opaque handles + a trampoline-owned `ctx` vtable that is the existing waker *generalised* (`acquire`/`register`/`retire`). The generalisation was latent in the existing design; only the explicit actor/function model surfaced it. The descriptor cut was a net *addition* (header slot, `desc_out`, a trait); the actor-first model was a net *deletion*. FIXME 0486 is the same lesson one layer down: the arg-lifetime-across-suspension **function** between the backend (emits the state-closure) and the runtime (defers the poll) was never written down as a contract, so a use-after-free fell in the unnamed crack between two locally-correct actors.

**Consequence.**

- When `/arch` reviews a proposed mechanism at Phase 2, it asks first: *are the actors and the functions between them written down?* If the review input is a mechanism with no actor/interface model behind it — especially one carried through multiple FIXMEs — the review backs up to the model before ratifying the shape.
- A design whose novelty is a net *addition* (new slot, new field, new trait) invites the actor-first pass most strongly: the addition is often a symptom of an unexamined premise, and the actor model frequently reveals a net *deletion* instead.
- The actor/function model is a first-class review artefact, not scaffolding discarded after the design lands. When it clarifies a cross-surface contract, it manifests at the relevant `facades`/`bounded-contexts`/`sequences` home (the functions between actors ARE the boundary contracts the canonical set records).

**Cross-references.**

- Principle 01 — Decoupling over convenience (the actors are the decoupling boundaries; naming the functions between them is naming the coupling that remains).
- Principle 02 — Narrow interfaces (an explicit function-between-actors is a candidate interface; the model reveals which are load-bearing).
- Principle 06 — Complexity has a budget (the actor-first pass is the cheapest way to find the accidental additions a locally-refined design accretes).
- Principle 07 — Single source of truth (an unnamed function between actors is a guarantee with no home; naming it gives the contract one owner).
- FIXME 0483 — the filing that motivated this Principle (S97 model pivot); `/sprint` memory `feedback_actors_functions_before_synthesis.md` carries the durable lesson.
