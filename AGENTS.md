# Agent instructions

Read and follow [`CLAUDE.md`](./CLAUDE.md) before changing this repository. It
is the canonical repository instruction file for all coding agents, and
`.codex/config.toml` makes the nearest `CLAUDE.md` the fallback guidance in
directories that carry no `AGENTS.md` of their own.

Role contracts live in the shared package at `.agents/skills/<role>/SKILL.md`;
`CLAUDE.md` §Roles declares which roles this repository dispatches and what each
owns here.
