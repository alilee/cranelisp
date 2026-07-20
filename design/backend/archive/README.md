# design/backend/archive/

Frozen historical backend design docs — incident-debug residue and pivot
artefacts that no longer reflect live design intent. Kept for reproduction
context only; **do not cite as authoritative design**. Live design docs stay at
the `design/backend/` top level (see `backend.md` §8).

Archived S75 W5 per FIXME 0096 (the 5 firmly-stale "Stale as live design" docs
flagged in `backend.md` §8). Mirrors the `design/arch/archive/` precedent.

| Doc | Origin | What it captured | Why archived |
|---|---|---|---|
| `cache-repl-loads-triage.md` | pre-S58 | REPL cache-load triage before Decision 37's "no swallowed failures" landed | Superseded — live design lands in `module-caching.md` (Decision 37 outcome) |
| `defect-8-repro-notes.md` | incident | Defect-8 reproduction notes | Incident-debug residue; kept as cross-skill repro example |
| `defects-456-reduction.md` | Sprint 59 W1 | Reduction of defects 4/5/6 (RC last-use) | Sprint-59 incident-debug residue |
| `slice-4-21-hello-io-investigation.md` | Sprint 61 | Closure double-free reduction for the 4.21 hello-IO slice | Sprint-61 era reduction; kept for repro |
| `io-trampoline-trace.md` | Wave 1 IO | IO-scheduling trampoline debug trace | Wave-1 IO-scheduling debug residue; live design is `io-trampoline.md` + `io-scheduling.md` |
| `implementation-slice-s66.md` | Sprint 66 | The S66 facade→source delta slice (`compile_to_module` per-symbol JIT, D41/D43 rotation) | One-shot executed slice; its last-open row 1(d) (`Jit::compile_defn` deletion) became true at S111 CS-1. Cites five retired facade docs. Archived S113 (FIXME 0635 I4) |

**Not archived (residual live content, stay at top level):**
`sprint51-fqtypename-cache.md` (partially stale — Sprint-51 era; Decision 34's
`schema_version` replaces the pre-S58 manifest hashing but the cache-shape
narrative is still partly live) and `ast-sourced-codegen.md` (partially
superseded by Decision 25's `Def.ast` field; cite cautiously). Both remain
cite-with-care references, not pure history.
