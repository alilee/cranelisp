---
id: ACT-0967
title: Decide whether the personal Claude allowlist stays tracked
status: open
priority: advisory
from: audit
to: sprint
sprint: 122
filed_at: 2026-09-21
refers_to:
  - .claude/settings.local.json
  - .claude/settings.json
---

## Request

Provenance: the S120 shared-role integration assessment
([historical assessment](https://github.com/alilee/cranelisp/blob/57253cf2/audits/shared-role-integration-s120.md), §4 F-9, second
observation). F-9 sat outside R-1…R-8, so ACT-0957 (closed 2026-09-11) did not
cover it and it has no disposition.

`.claude/settings.local.json` — a personal permission allowlist containing
absolute local paths — is tracked (`git ls-files .claude`), alongside the
shared `.claude/settings.json`. A `.local` settings file is conventionally
per-user and untracked; tracked, it publishes one contributor's paths and
allowlist to every clone and churns on unrelated work. The question is only
whether that is intended.

## Completion evidence

One of: the file is untracked and ignored (shared permissions, if any, moved
to `.claude/settings.json`); or the user's reason for tracking it is recorded
in the host-entry guidance `sprint` owns.
