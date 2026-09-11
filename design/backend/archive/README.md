# design/backend/archive/

Frozen historical backend design docs — incident-debug residue and pivot
artefacts that no longer reflect live design intent. Kept for reproduction
context only; **do not cite as authoritative design**. Live design docs stay at
the `design/backend/` top level (see `backend.md` §8).

Archived S75 W5 — the five firmly-stale "stale as live design" docs flagged in
`backend.md` §8. Mirrors the `design/arch/archive/` precedent.

| Doc | Origin | What it captured | Why archived |
|---|---|---|---|
| `cache-repl-loads-triage.md` | pre-S58 | REPL cache-load triage before Decision 37's "no swallowed failures" landed | Superseded — live design lands in `module-caching.md` (Decision 37 outcome) |
| `defect-8-repro-notes.md` | incident | Defect-8 reproduction notes | Incident-debug residue; kept as cross-skill repro example |
| `defects-456-reduction.md` | Sprint 59 W1 | Reduction of defects 4/5/6 (RC last-use) | Sprint-59 incident-debug residue |
| `slice-4-21-hello-io-investigation.md` | Sprint 61 | Closure double-free reduction for the 4.21 hello-IO slice | Sprint-61 era reduction; kept for repro |
| `io-trampoline-trace.md` | Wave 1 IO | IO-scheduling trampoline debug trace | Wave-1 IO-scheduling debug residue; live design is `io-trampoline.md` + `io-scheduling.md` |

**Not archived (residual live content, stay at top level):** `hkt-codegen.md`
and `ast-sourced-codegen.md` — the latter partially superseded by Decision 25's
`Def.ast` field. Both are cite-with-care references, not pure history.

**Retired instead of archived (S122):** the S51 FQTypeName/cache migration
design, listed here until now as partially live, carried nothing current
against source and was deleted under the extract-then-delete rule
(`sprints/METHOD.md` §3.1). Its one surviving rule is in `backend.md` §4.5, and
the disposition is recorded at `backend.md` §8. **This directory takes frozen
records that remain the canonical context for something. Executed work whose
content has landed is deleted, not moved here.**
