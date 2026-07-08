---
number: 0537
target: /design (src/)
filed_by: /arch
filed_at: 2026-07-08
sprint_filed: 105
refers_to: design/int/session-transaction.md §10 T1 (CS-1 reload driver), §8 (persistence pins), §4.2 (per-symbol re-typecheck input); src/save.rs::generate_fns_and_macros; src/session_v4/lifecycle.rs::reload_module
status: open
---

# Decouple the T1 reload's mono-instantiation trigger from the persisted `__expr` wrapper (the /arch ruling on FIXME 0532)

## Origin

Supersedes FIXME 0532 (`target: /arch`, filed by `/sprint` S103). 0532 asked `/arch`
to rule the right seam for a within-crate coupling discovered during S103 Wave 4:
`src/save.rs::generate_fns_and_macros` writes the synthetic `__expr` eval wrapper into
the persisted backing `.cl` file, and the T1 reload path (`reload_module`, which re-reads
that backing file and re-runs typecheck+codegen from source) was found to **depend** on
that persisted expression to force same-module mono-instantiation of the reloaded module.
A Wave-4 filter to omit `__expr` regressed polymorphic reload and was reverted. This is not
a correctness bug today — it is a maintainability/soundness smell: persistence fidelity and
mono-instantiation-triggering are entangled through a user-visible synthetic artifact, and a
future change to either regen or the reload path can silently break the other.

`/arch` has ruled. This FIXME carries the ruling as the design input for `/design (src/)`
to manifest at its natural home (`design/int/session-transaction.md §10 / §8`) and to route
the `src/` change-set to `/dev (src/)`. `/arch` records rulings; it does not edit
`design/int/` or `src/`.

## The /arch ruling — the target seam

Two concerns are coupled through the `__expr` artifact and must be decoupled. The evidence
that grounds the decoupling:

- `generate_fns_and_macros` **skips `$`-mangled names** (`save.rs:732`), so mono variants
  (`id$Int`, `t$Int`, …) are **not** written to `.cl` source — they ride the *compiled*
  channel (`.meta`/`.o`). The backing `.cl` is SOURCE = the module's **definitions**.
- `__expr` is a `Public` zero-arg `UserFn` Def with no `$`, so it is the **one synthetic
  non-definition** the fn-section writer leaks into source. Its de-facto role on reload is
  to re-drive the same-module mono mint that a from-source reload would otherwise lose (a
  cross-module dependent re-mints its own instances at the caller site — Principle 17 module
  locality; only the *same-module* mint, originally driven by a REPL `__expr`, has no other
  minter on reload).

### Q1 — mono-instantiation on reload: trigger it EXPLICITLY

The T1 reload's same-module mono-instantiation requirement SHALL be carried as an **explicit
reload-path input**, not smuggled through persisted source text. The instantiation set is
knowable at the reload site without the artifact: the live table being replaced holds exactly
the `$`-mangled `UserFn` mono variants that were minted; the reload captures them **before**
the Replace commit and re-requests their instantiation after the from-source reload settles
(or re-derives them from the `.meta` compiled-state channel that already carries them). The
mono-instantiation set is a **compiled-state** concern; it must travel the compiled-state /
explicit-request channel, never the `.cl` source channel. This is a direct application of
Principle 1 (decoupling over convenience), Principle 7 (single source of truth — the source
file stops doubling as an instantiation ledger), and Principle 20 (model the reload's
instantiation obligation by representation — an explicit request — not implicitly by file
content the writer should not be emitting).

### Q2 — persistence fidelity: OMIT `__expr` from the backing file

Once Q1 lands, `generate_fns_and_macros` (and any sibling regen section) SHALL **omit the
`__expr` wrapper** and any synthetic non-definition. A backing `.cl` is the faithful source
of the module's *definitions*; a transient REPL expression is not a definition and must not
round-trip as one. This is the same regen-fidelity discipline as the S102 D1/D2 cures
(source-first, no expansion-artifact / origin double-persist — `src/CLAUDE.md` §"Degraded
startup load") extended to the last leaking synthetic artifact. `__expr` is already
gate-exempt at classification and `__expr`-excluded at the ReverseIndex feed (§9.1.1 F3);
excluding it at the **persistence writer** completes the story — the wrapper never becomes
durable state in any channel it does not belong in.

### Sequencing — Q1 strictly precedes Q2

The writer cannot omit `__expr` until the reload path no longer depends on it. So Q1 (explicit
reload-time instantiation trigger) is the load-bearing prerequisite; Q2 (the writer omission)
is a trivial filter that lands **only after** Q1 makes the persisted expression dead weight.
Landing both in one change-set is acceptable and cleaner (the omission is one predicate), but
the Q1 trigger MUST be in place first or in the same change-set — never Q2 alone (that is the
reverted Wave-4 filter). Acceptance: the two coherent-stale reload pins and the polymorphic-
reload path that regressed under the Wave-4 filter stay green with `__expr` absent from the
regenerated `.cl`.

## Scope boundary — what this is NOT

- **No cross-crate interface, no ABI, no facade, no public-API change.** This is entirely a
  `src/` interior seam (save/regen + the reload driver). The canonical arch set
  (overview/BC/principles/facades/sequences/`cranelisp-types`) needs no edit; `/arch`
  confirmed the audit sweep is empty. No new principle — this is an application of
  Principles 1/7/17/20, not an addition to the register.
- **Not a correctness bug at stage M.** Deferrable past S105 as `/dev (src/)` implementation
  work. The value delivered now is the explicit target so the coupling is a documented,
  scheduled decoupling rather than an undocumented trap the next reload/regen change springs.

## Relationship to sibling regen-fidelity FIXMEs

- **0530** (`target: /design`) — regen sections 5–7 (traits/types) not source-first. Both
  0530 and this are regen-fidelity gaps under the T1 reload path, but they are **distinct**:
  0530 is sections 5–7 (`generate_traits`/`generate_types` reformatting user source); this is
  section 8's (`generate_fns_and_macros`) `__expr` non-definition leak + its reload coupling.
  `/design (src/)` may co-schedule them (same file, same discipline) but they are separately
  actionable.
- **§9.1.1 F3 / FIXME 0507** — the `__expr`-only ReverseIndex feed exclusion is a *different*
  `__expr` mechanism (caller-suppression in the reverse index); this FIXME is the
  *persistence + reload-trigger* coupling. Do not conflate the two `__expr` seams.

## Proposed manifestation + routing

1. `/design (src/)` records the target decoupling in `design/int/session-transaction.md`
   — §10 T1 (the CS-1 reload driver gains an explicit pre-reload mono-variant capture /
   re-instantiation step) and §8 (persistence: `__expr` omitted from the backing file,
   completing the source-is-definitions-only invariant), mirroring how §10/§13 already carry
   the T1 full-cure design + its `/dev (src/)` change-set list.
2. `/design (src/)` routes the implementation to `/dev (src/)` via the doc's Next-skills
   (Q1 trigger in `lifecycle.rs::reload_module` / the CS-1 driver, then the Q2 filter in
   `save.rs::generate_fns_and_macros`), with the acceptance above.

Delete this FIXME when the §10/§8 design increment lands (the `/dev (src/)` change-set is then
tracked by that design's Next-skills, per the 0507 precedent).
