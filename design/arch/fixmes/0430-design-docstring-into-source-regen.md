---
number: 0430
target: /design
filed_by: /dev
filed_at: 2026-06-22
sprint_filed: 89
refers_to: src/save.rs::generate_fns_and_macros, design/int/agent.md §17, repl/spec.md §17.15
status: deferred
deferred_by: /dev
deferred_at: 2026-06-27
sprint_deferred: 93
target_sprint: 94
recommended_candidate: "1 — docstring-aware render_decl_sexp"
---

> **DEFERRAL (S93 Wave 4, /dev int).** Genuine design fork — not actioned this
> sprint. See the `## /dev S93 assessment` section at the bottom for the
> recommended candidate, rationale, and re-land scope. `/design` ratifies the
> renderer contract; the re-land is a future agent Document-write-mode wave.


# Document-mode `set-doc` — spec the docstring-into-source regen increment

## Issue

The Document-mode `set-doc <symbol> <text>` tool was **descoped in S89 W3** (the
`/review` 3R Blocker). It set the live `ModuleEntry::Def.docstring` field, but the
backing-file regen path (`save::generate_fns_and_macros` → `render_decl_sexp`,
which re-renders each def from its **stored sexp**) never reads the `docstring`
field — so a `set-doc` docstring silently vanished on session restart, breaking
§17.15.3's durable-memory promise ("memory is the code"). A non-persisting
half-feature is worse than no feature: it claims durability it does not deliver.

`set-preamble` (the Document keystone) IS correct and ships — its edit is a
byte-stable section-0 round-trip (`save::apply_preamble_edit`) the regen path
honours. Only the **docstring** facet has no persistence path.

What was removed in S89 W3 (`src/agent/pull.rs`, `src/agent/stub.rs`):
- the `SET_DOC_TOOL` const + its `tool_defs` registration + the `run_pull`-head
  routing arm;
- `apply_docstring_edit` (the live-field setter);
- `run_document_edit` simplified to preamble-only (the `is_preamble` branch dropped);
- the `set_doc_consultative_gate_sets_docstring` unit test + the `set-doc`
  assertions in `tool_defs_are_read_only_plus_submit` /
  `document_tools_refused_by_read_only_allowlist_neg` / the stub parse test.

No failing-not-ignored repro is owed (nothing broken ships — the half-feature is
removed, not carried). This FIXME is the durable record of the descoped increment.

## Proposed resolution

Spec the docstring-into-source increment so a future `/dev` wave can re-land
`set-doc` with real persistence. Two candidate designs (pick one, or another):

1. **Docstring-aware `render_decl_sexp`** — teach the regen renderer to emit the
   `ModuleEntry::Def.docstring` as the canonical docstring form on re-render, so
   the live field round-trips through `generate_fns_and_macros` to disk.

2. **Re-inject at edit time** — at `set-doc` apply time, rewrite the def's
   *stored sexp* to carry the docstring (so the existing sexp-based regen path
   picks it up unchanged). Keeps the regen renderer simple at the cost of
   mutating stored AST.

Either way the acceptance is: a `set-doc` then session-restart preserves the
docstring (observable via `/doc <symbol>` after restart) — the §17.15.3 durable
promise the preamble keystone already satisfies.

## Operational implication / Context

Document mode ships preamble-only in S89. The `set-doc` re-land is gated on this
design decision (regen renderer vs. stored-sexp rewrite) — it is a `/design`
call (the regen-path shape crosses the `save.rs` renderer contract), not a `/dev`
implementation choice. Until specced, the agent's Document write surface is
`set-preamble` alone.

## /dev S93 assessment (deferral rationale)

Confirmed this is a genuine design fork, not a small obvious-approach increment,
so it is deferred per the `/dev` dispatch rather than guessed:

**Why it is a fork, not a one-liner.** The regen path
(`save::generate_fns_and_macros`) re-renders each def from its **stored source** —
preferring the introspection record's *verbatim REPL text*
(`introspection_sexp`) and falling back to `DefKind::Macro.macro_sexp` — via
`render_decl_sexp(&Sexp)`. The renderer receives **only a `&Sexp`**; it has no
access to the symbol-table entry, and therefore no access to the live
`ModuleEntry::Def.docstring` field a `set-doc` writes. Closing the gap changes
the `render_decl_sexp` contract (the FIXME's stated reason this is a `/design`
call). Additionally, the `set-doc` surface itself was fully descoped in S89 W3
(tool const + `tool_defs` registration + `run_pull` routing + `apply_docstring_edit`
+ `run_document_edit`'s `is_preamble` branch + 4 test sites) — re-landing is a
multi-file, `#[cfg(feature = "agent")]` Document-write-mode increment, not a
renderer tweak.

**Recommended candidate: 1 — docstring-aware `render_decl_sexp`.** Rationale:

- **Single source of truth (Principle 7).** `set-doc` already sets the live
  `ModuleEntry::Def.docstring`. Making regen *read* that field keeps ONE
  authoritative docstring. Candidate 2 (re-inject into the stored sexp/verbatim
  text at edit time) duplicates the docstring into a second location that can
  drift from the live field.
- **Candidate 2 is the brittle path.** The regen prefers the introspection
  **verbatim text** over the symbol-table sexp, so candidate 2 would have to do
  string-level surgery on the captured REPL source to be picked up on regen —
  exactly the `include_str!`-style "lexical text vs. resolved truth" brittleness
  `/arch` rejected for the platform-schema design (`platform-interface.md`).
- **Candidate 1 localizes the change.** Thread the entry's `docstring`
  (`Option<&str>`) from the `generate_fns_and_macros` loop — which already holds
  the `entry` — into `render_decl_sexp`; the renderer inserts/replaces the
  docstring form immediately after the param vector.

**The one question `/design` must settle** (the reconciliation rule): when the
stored sexp ALREADY carries a docstring form (from the original `(defn name [..]
"doc" ..)` source) AND the live field is `Some`, which wins? Recommendation: the
live `Def.docstring` is authoritative — always emit it when `Some`, and drop any
sexp-embedded docstring so it is never duplicated; emit the sexp's own docstring
only when the live field is `None`. That rule makes `set-doc` → restart →
`/doc` round-trip the live edit (the §17.15.3 durable promise) without a
double-docstring hazard.

**Target sprint: S94** (or whenever the agent Document-write-mode track next
opens), gated on `/design` ratifying candidate 1 + the reconciliation rule above.
The re-land then re-adds the S89-W3-removed `set-doc` surface against the ratified
renderer contract, with a `/qa` e2e pinning set-doc→restart→`/doc` persistence and
a `save.rs` unit test on the renderer's docstring insert/replace/reconcile arms.
