---
number: 0430
target: /design
filed_by: /dev
filed_at: 2026-06-22
sprint_filed: 89
refers_to: src/save.rs::generate_fns_and_macros, design/int/agent.md §17, repl/spec.md §17.15
status: open
---

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
