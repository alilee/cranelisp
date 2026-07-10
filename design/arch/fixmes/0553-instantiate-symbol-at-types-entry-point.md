---
number: 0553
target: /typecheck
filed_by: /arch
filed_at: 2026-07-10
sprint_filed: 106
refers_to: design/int/session-transaction.md §10 CS-1; src/redefine.rs::capture_instantiation_drivers; design/arch/ownership-inference.md §3.3 (ModeSummary implementing sprint opens cranelisp-types); design/backend/ownership-codegen.md §8.3 (pinned backend interface)
status: open
---

# "Instantiate symbol at these types" entry point — the general SET-capture the T1 reload cure wants

## Issue

The S106 T1 full-cure reload (FIXME 0552) re-mints orphaned same-module
polymorphic mono variants after a from-source reload by **replaying the single
last `__expr` driver expression** (`redefine.rs::capture_instantiation_drivers`
+ `reload_module`'s `extra_forms`). `/arch` accepted this for S106 (FIXME 0552,
Ruling 1) — it is correct for the reachable case and at parity with prior
robustness. But it carries two structural limitations that the blessed §10 CS-1
SET-capture design would have avoided, and that a proper entry point would cure:

1. **Multiple past instantiations are not covered.** Each REPL expression turn
   overwrites the single `__expr` introspection record, so if a session minted
   `g$Int` then `g$Bool` from two separate top-level expressions, only the last
   survives to replay. (Sound today only because unreplayed variants are dead or
   re-minted at durable call sites — Principle 17 — but that is a reachability
   argument, not a general guarantee.)
2. **The stale-`__expr` wart.** `introspection[__expr].sexp` is session-persistent
   (never cleared on a defn turn). A T1 cure firing on an unrelated later defn
   turn can re-inject a now-ill-typed `__expr`, making `reload_module` fail and
   spuriously degrading a clean cure to the §10 CS-3 error-blocked floor. Replaying
   a *form* re-runs whatever ill-typedness the form has acquired.

Both dissolve if the reload can **request instantiation of a named symbol at a
recorded set of concrete types** — the `$`-mangled mono-variant SET §10 CS-1
originally specified — instead of replaying a source form. That capture is a
**compiled-state** concern (the live table already holds the `$`-mangled variant
schemes; the `.meta`/`.o` channel already persists them); the missing piece is a
capability to re-request their instantiation post-reload without going through
source re-evaluation. That capability is **not int-side** — it needs
typecheck+backend to instantiate a polymorphic scheme at given concrete type
arguments and codegen the mono variant.

## Proposed resolution

Design + expose a narrow entry point — "given an FQSymbol naming a polymorphic
`UserFn` and a set of concrete type-argument tuples, instantiate + monomorphise +
codegen each variant into the module" — usable by `src/redefine.rs`'s reload
driver in place of the `__expr` form replay. Shape TBD by `/typecheck` (the
instantiate/monomorphise half) + `/backend` (the codegen half); the reload driver
would then:
- capture the live `$`-mangled `UserFn` mono-variant SET (their type-argument
  tuples) before the Replace commit — data, not a form;
- after the from-source reload settles, re-request instantiation of that SET
  through the new entry point.

`redefine.rs::capture_instantiation_drivers` + the `reload_module(extra_forms)`
form-replay path retire when this lands.

## Operational implication / Context

- **Future work — do NOT build in S106.** The driver-replay is accepted as the
  stage-M endpoint (FIXME 0552). This is the generalisation, sequenced when the
  cost of the two limitations is felt or when the enabling seams open anyway.
- **Natural co-landing:** the increment-I `ModeSummary` implementing sprint
  already opens `cranelisp-types` and the typecheck/backend monomorphisation
  seams (`design/arch/ownership-inference.md` §3.3; backend §8.3). An
  "instantiate at types" entry point is close in spirit to the machinery that
  sprint touches — evaluate co-scheduling it there rather than as a standalone
  effort.
- **Cross-skill:** `/typecheck` owns the instantiate/monomorphise half; a paired
  `/backend` change codegens the variants (this FIXME targets `/typecheck` as the
  entry; `/backend` co-resolves the codegen half — `/sprint` to schedule the pair).
- Delete when the entry point exists and `redefine.rs` re-requests the mono-variant
  SET through it, retiring the `__expr` driver-replay.
