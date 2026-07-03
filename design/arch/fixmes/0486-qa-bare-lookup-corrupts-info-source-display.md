---
number: 0486
target: /qa
filed_by: /docs
filed_at: 2026-07-03
sprint_filed: 101
refers_to: repl/spec.md §3.6 (/info definition source), §18.4 (/info on a broken symbol MUST include the definition source), §3.1 (/source — "Show original source text"); src/ info_definition_source seam (S101 FIXME 0480 resolution)
status: open
---

# Bare lookup overwrites a symbol's introspection source — `/info` and `/source` then show the bare name instead of the definition

## Issue

Evaluating a defined symbol **bare at the prompt** corrupts that symbol's
in-session introspection source. Every subsequent `/info <name>` and
`/source <name>` renders the definition source as the bare name instead of the
`(defn …)` form. This contradicts `repl/spec.md` §3.6 (`/info` MUST display the
definition source — the new S101 surface from FIXME 0480) and §18.4 (`/info` on
a broken symbol MUST include the definition source), and breaks `/source`'s
"original source text" contract.

## Repro (deterministic; verified 2026-07-03 on `target/debug/cranelisp`, with and without stdlib prelude)

```
user> (defn solo [x] (* x 3))
:(Fn [primitives/Int] primitives/Int) user/solo ; defn
user> solo                          ; ← the corrupting turn
:(Fn [primitives/Int] primitives/Int) user/solo ; defn
user> /info solo
:(Fn [primitives/Int] primitives/Int) user/solo ; defn
  solo                              ; ← MUST be (defn solo [x] (* x 3))
  12 bytes
user> /source solo
; source for solo
solo                                ; ← same corruption at the /source seam
```

Narrowing already done (all verified by hand):

- **Trigger is the bare-lookup turn only.** A call form `(solo 2)` does NOT
  corrupt; `/sig solo` does NOT corrupt. Immediately after `defn`, `/info` and
  `/source` are correct.
- **No redefinition machinery needed** — the minimal repro above has none. But
  the defect also hits the new S101 §18.4 surface: after a signature-changing
  redefinition, `k` (bare lookup) then `/info k` shows the provenance line
  correctly but the source line degrades to `  k` — for **broken and healthy
  (recompiled) symbols alike**.
- **The backing file stays correct** — `(defn solo …)` persists; the bare
  lookup is not persisted. The corruption is in-session introspection metadata
  only (the bare-lookup turn appears to record the lookup form as the symbol's
  latest source/sexp, which `info_definition_source`'s introspection-first
  precedence then serves).
- **Session restart self-heals** (verified): after `/quit` + relaunch in the
  same directory, `/source solo` shows the correct `(defn …)` form again — the
  corruption is live-session state only; the persisted truth is intact.

## Proposed resolution

`/qa` authors a narrow failing-not-ignored e2e test (defn → bare lookup →
`/info` + `/source` assert the defn form, `// spec: repl/spec.md §3.6`), plus
the §18.4 broken-symbol sibling if cheap. Likely owner `/int` (src/ session
introspection recording on the bare-lookup evaluation path); the display seam
itself (`info_definition_source`, S101 0480) looks correct — it renders what
introspection hands it.

## Operational implication / Context

Found during S101 Phase-6a `/docs` audit. Bare lookup is the first thing the
self-documenting-REPL principle teaches users to do, so in practice `/info`'s
new definition-source display (S101 headline UX) shows the wrong source for
exactly the symbols a user has just inspected. `/docs` will not document the
`/info` source display in the 6b redefinition guide with a transcript that
includes a prior bare lookup until this is resolved.

## /qa guard batch (S101 6b, 2026-07-03): guards LANDED — this file is now redundant as a record

3 guards: healthy arm RED + no-lookup green control in
`tests/repl_introspection.rs`
(`bare_lookup_does_not_corrupt_info_and_source_definition_display`,
`info_and_source_show_defn_form_without_prior_bare_lookup_control`); §18.4
broken-symbol arm RED in `tests/repl_redefinition.rs`
(`bare_lookup_broken_symbol_info_still_shows_definition_source`). RED-first
verified. Resolver likely /int. Ledger: `tests/plan/ledger.md` §"Sprint 101
Phase 6a/6b defect set".
