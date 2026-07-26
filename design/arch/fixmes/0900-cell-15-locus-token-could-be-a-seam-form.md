---
number: 0900
target: /testing
filed_by: /review
filed_at: 2026-07-26
sprint_filed: 118
refers_to: tests/adt_drop_glue_underkey.rs:258 (cell #15 `// defect:` line)
status: open
---

# Cell #15's re-locused `locus=` token is crate-grain; a seam form would serve the hotspot recipe better

## Severity

Suggestion

## Issue

The W4 re-locus of cell #15's `// defect:` line is substantively correct:
class kept (`rc-miscount`), past tense, the falsified provisional backend
attribution named, `fixed=S118/fc3375f9` present and pointing at the flipping
commit (I3). But the token the hotspot recipe counts
(`grep -o "locus=[^ ]*"`) is now just `src` — the prose "program-result
typed-context exit" sits after the first space. A no-space seam token (e.g.
`locus=src::program-result-typed-context-exit`, naming the pre-fix seam where
the bug lived — not the post-fix `result_owner.rs` home) would keep the seam
attribution inside the countable token.

## Proposed resolution

`/testing`'s call: tighten the token, or leave it — `locus=src` is an
established corpus grain either way.

## Context

**Adjudication note (severity reclassified with rationale).** The delegated
Codex reviewer (codex-cli 0.145.0) filed this as Important, claiming the line
"violates `tests/CLAUDE.md`'s structured notation". The adjudicator verified
against the corpus and the convention text and downgraded to Suggestion:
crate-grain tokens are established practice (`locus=src` ×9,
`locus=frontend` ×17, `locus=typecheck` ×9, `locus=crates/cranelisp-backend`
×29 — most with prose after the token, including cell #15's own pre-W4 line),
and `tests/CLAUDE.md` itself states "prose after the token never pollutes the
frequency counts". There is no violation; only a finer grain available.
