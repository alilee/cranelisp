---
number: 0607
target: /design
filed_by: /sprint
filed_at: 2026-07-15
sprint_filed: 110
scheduled: S110
refers_to: design/int/ — int.md (S81-era tree cited as current), agent.md §2.2
  (documents the RETIRED resolution classifier with a now-wrong normative warning), and
  the 44-doc sprawl with no staleness triage. Narrow-deploy /design to int.
status: open
---

# `design/int/` currency pass: rewrite `int.md` to as-built; fix `agent.md §2.2`; triage the 44-doc sprawl

## Source

S109 `src/` whole-context audit (`audits/src-s109.md` R-3), **ACCEPTED** S110 Phase 1.

## Evidence (quoting the assessment §2.2/§2.3)

1. **`int.md` §3.2/§3.3** presents the S81-era tree as current: "Wave D (carried)",
   "Total today: 28,592 LOC", `observability.rs` "renames to `src/scheduler_trace/`"
   (never happened), `expander.rs` "517 LOC" (now 1,683), `save.rs` "493" (now 2,306).
   The submodule directories (`session_v4/`, `process_form/`, `worker/tests.rs`)
   post-date every row. A reader planning int work gets a two-restructures-old map.
2. **`agent.md §2.2`** documents the *retired* symbol-resolution classifier (a bare
   `Symbol` is known iff `symbol_is_known(name)`) with a bolded "future reader MUST NOT"
   warning — but the code implements the **form-count rule** (user ruling 2026-07-12):
   `forms.len() == 1 → Repl` else `Agent`, `symbol_is_known` explicitly NOT consulted
   (`src/agent/mod.rs:70-148`). **The doc's normative warning protects the wrong
   invariant.** This is the surgical, actively-misleading correction — do it even if the
   full `agent.md` restructure (3,124-line accretion) waits.
3. **44 docs** in `design/int/` with no currency triage; the `step*.md`/`s7*.md`/
   `wave-*.md` slice docs are superseded narrative.

## Shape (assessment §3 R-3) — the S109 typecheck 0578 template

As-built rewrite of `int.md`'s structural sections; doc-sprawl banners on superseded
slice docs; a doc-index in `design/int/CLAUDE.md`; a surgical §2.2 correction in
`agent.md` (form-count rule + its "MUST NOT" warning now protecting the LIVE invariant).

## Done

`int.md`'s module map matches the tree (spot-check `session_v4/`, `process_form/`,
`repl.rs` reality); every superseded doc carries a banner; `agent.md §2.2` describes the
form-count rule. Couples with 0606 (R-1 repl.rs decomposition — the doc map updates with
the cut) and 0608 (R-4 — narrative relocation needs a current doc home).
