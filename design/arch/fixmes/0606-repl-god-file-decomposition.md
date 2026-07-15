---
number: 0606
target: /dev
filed_by: /sprint
filed_at: 2026-07-15
sprint_filed: 110
scheduled: S110
refers_to: src/repl.rs — the 5,103-line god-file (~185 production functions, six
  mixed responsibilities). Narrow-deploy /dev to src/ (int); /design (int) signs off
  the cut FIRST (the 0580 program.rs template), mechanical move LAST, public-api.txt
  zero-diff.
status: open
---

# Decompose `repl.rs` (5,103-line god-file); extract the search subsystem first

## Source

S109 `src/` whole-context audit (`audits/src-s109.md` R-1), **ACCEPTED** S110 Phase 1.

## Evidence (quoting the assessment §2.3)

`repl.rs` is the new god-file: 5,103 lines, ~185 production functions, one flat module
mixing (a) slash dispatch (`dispatch_command`, :512, 155 lines); (b) ~25 `handle_*`
command handlers; (c) an entire **search subsystem** (`handle_search` :1158,
`collect_name_and_docstring_hits`, `render_search_row*`, `wait_for_index_settled`,
`try_search_by_scheme`, `scan_referers` — the UI half of
`session_v4/index_worker.rs`, embedded inline); (d) the introspection-display formatter
family (`format_def_entry_doc` :2738, `format_eval_result*` :2579-2611,
`format_type_display`, `format_trait_display`); (e) prompt/banner/line-editor;
(f) typecheck-only + macro-expansion entry points. It absorbed S108's search UI and
S109's display unification without ever being re-cut.

## Shape (assessment §3 R-1)

- `repl/search.rs` — the UI half, beside its `session_v4/index_worker.rs`.
- `repl/format.rs` — the `_doc` producer family (coherent sibling of `display.rs`).
- `repl/commands.rs` — the `handle_*` battery (fold in the S87-unchanged `handle_imports`).
- residual `repl.rs` — dispatch + prompt/banner + line-editor (the §3.3 Wave-D
  allocation it was supposed to be).

## Done

No file in the family exceeds ~1,500 lines; behaviour-invariant (golden REPL e2e green;
**zero `public-api.txt` diff**); `design/int/int.md` module map updated in the same
change-set. `/design` (int) signs off the cut before the move (0580 template).

## Sequencing

src/-side hygiene track (parallel to the 0583 backend centrepiece, but src-touching work
is SERIAL — coordinate with R-4/R-3 which touch the same files). Couples with 0607 (R-3
`int.md` module-map currency) — the decomposition and the doc-map update land together.
