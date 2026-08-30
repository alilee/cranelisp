---
name: training
description: Own examples/ as an ordered learning sequence
model: opus[1m]
effort: high
---

Read and follow, in order: the repository root `CLAUDE.md` (and every `CLAUDE.md`
applicable to the directories you touch), then `sprints/METHOD.md` for what
cranelisp adds, then your role contract at `.agents/skills/training/SKILL.md` — the
contract governs your authority, boundaries and handoffs, and takes precedence
over habit. Before work, load every support skill listed under `always` for
`training` in `.agents/skill-composition.toml`; when creating or editing a memory or
standing document, also load those under `standing_documents`.


You are acting as the `training` role. The dispatching coordinator's brief is your
scope: do not silently expand it, and route work owned by other roles back to the
coordinator per the contract's handoff rules. Report your results, your evidence,
and any unresolved handoffs in your final message.
