---
number: 0482
target: /arch
filed_by: /sprint
filed_at: 2026-06-30
sprint_filed: 96
refers_to: design/arch/platform-interface.md §6.8 (ABI_VERSION), design/arch/effect-concurrency.md §4.1, design/platform/poll-support.md §3.5, crates/cranelisp-platform (PollFn/Poll), crates/cranelisp-intrinsics/src/io.rs+reactor.rs (await_poll_node/acquire), crates/cranelisp-backend (compile_poll_effect / poll-node bake)
status: open
---

# Make the resource (token, capacity) descriptor trampoline-owned representation overhead — not user-visible value data (tuple leaf-return ABI v9)

## Issue

The per-connection scheduling metadata `(token, capacity)` leaks into **user
source**. As shipped (S96, FIXME 0465 resolution), `web/Connection` is
`[token capacity fd]` and the poll leaves take them as explicit positional args:
`read-conn : (Fn [Int Int Int] (IO Request))` = `(token, capacity, fd)`,
`send-conn : (Fn [Int Int Int Response] (IO Int))`. The user destructures
`[(Connection token capacity fd) …]` and threads them into every leaf.

For the web connection this is egregiously redundant: `accept-conn` mints
`token == conn fd` and `capacity == 1`, so the user is literally writing
`(read-conn fd 1 fd)` — one piece of real data (`fd`) plus two pieces of
scheduling metadata they neither choose nor should see. `capacity` is a per-leaf
**constant** already declared in the manifest descriptor (`[conn_token, 1, conn_fd]`);
`token` is the reactor's acquire-around-poll serialization key. Both are
trampoline bookkeeping. This directly contradicts the sprint thesis
("throughput is free… concurrency written by nobody"): the user is hand-writing
the scheduling metadata the model is supposed to keep out of source.

Why it's currently exposed: the backend bakes the poll-node's `(token@32,
capacity@40)` slots from the **first two positional leaf args** (`io.rs`
await_poll_node reads them for the gate; `compile_poll_effect` bakes them). Putting
them in the `Connection` ADT + leaf args was the path-of-least-resistance wiring,
not a necessity.

Two intermediate fixes were considered and rejected as still-suboptimal:
(1) move `capacity` to the manifest, keep `token` as a positional arg — half-measure;
(2) hide `token` in an **opaque ADT field** — still makes the descriptor part of the
value's logical shape, and the backend still needs per-ADT "token is field N"
knowledge.

## Proposed resolution (the target shape — /arch to arbitrate)

Treat the resource descriptor `(token, capacity)` as **trampoline-owned runtime
representation overhead, like the RC/heap header** — type-invisible, not part of any
ADT's logical shape — carried across the leaf boundary as a **tuple on the poll-fn
return ABI**. This is a **poll-fn C-ABI bump (ABI v8 → v9)**: the `Poll::Ready`
return widens from `value:i64` to `(value:i64, desc: ResourceDesc)` where
`ResourceDesc = { token: u64, capacity: u32, role: Produce | Consume | None }`.

**The producing/consuming asymmetry (the load-bearing subtlety):**
- A resource-**producing** leaf (`accept-conn`) returns `(value, Produce{token,
  capacity})`. The trampoline **stamps** the descriptor into the produced value's
  header side-band and hands the bare value onward. (The token VALUE is the
  platform's internal choice — e.g. `token == fd` — invisible to user + backend.)
- A resource-**consuming** leaf (`read-conn`/`send-conn`) returns
  `(value, None)`. BEFORE it polls, the trampoline **reads** the descriptor off the
  leaf's incoming handle (its consumed arg) to do acquire-around-poll. Its result
  (Request/Int) carries no descriptor.
- The descriptor must be RE-ATTACHED to the produced value (header slot, not a
  fragile pointer-keyed side table) because the consuming leaf needs the producing
  resource's token before it establishes — "strip from the user's view" yes,
  "discard" no.

The manifest declares each leaf's **role** (Produce/Consume/None) + the capacity
default; the **token value** comes from the platform at production. The backend
**stops baking `(token, capacity)` from positional args entirely** — it reserves the
header descriptor slot and emits produce/consume per the manifest. `Connection`
slims to opaque (or `[fd]`); leaves become `read-conn : (Fn [Connection] (IO Request))`,
`send-conn : (Fn [Connection Response] (IO Int))`.

(A full user-program / trampoline / platform sketch of the target shape is in the
S96 close conversation; reproduce it in the design doc when actioned.)

**Inference (E1–E3) is unaffected/cleaner:** value-locality reasons about the
`conn` handle being born fresh at `accept` (it already does); the descriptor riding
inside its representation doesn't change the disjointness proof.

## Operational implication / Context

- Cross-surface ABI change (platform + intrinsics/trampoline + backend) ⇒ /arch is
  the arbiter; manifests in `platform-interface.md §6.8` (ABI v9 + the widened
  `Poll`/`ResourceDesc` artifact), `effect-concurrency.md §4.1` (descriptor as
  representation overhead; produce/consume role), and BC §3/§5/§6.
- **Cascade to /design** (the named follow-on, AFTER /arch rules the shape):
  `poll-support.md §3.5` — slim `Connection` to opaque, leaf signatures take the
  handle, descriptor sourced from manifest-role + the value side-band; the
  per-platform leaf reshape (/platform) + the poll-node-emit reshape (/backend) +
  the trampoline split/stamp/read (/int) follow from the /design pass.
- Tradeoffs to weigh in the ruling: a few header bytes on resource handles; loses an
  advanced explicit-token knob (deliberately co-serializing two resources by shared
  token — relegate to a separate advanced API if ever wanted); a v9 bump so soon
  after the S96 v8 cutover (but "no users" — the S96 rationale for jumping ABIs
  cleanly still applies).
- Not blocking anything shipped; this is an abstraction-quality improvement that
  completes the "concurrency written by nobody" promise at the VALUE level, not just
  the source level.
