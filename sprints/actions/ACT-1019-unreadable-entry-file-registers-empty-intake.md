---
id: ACT-1019
title: Decide and evidence the outcome for an entry file that exists but cannot be read
status: open
priority: advisory
from: qa
to: qa
sprint: 122
filed_at: 2026-09-30
refers_to:
  - src/session_v4/lifecycle.rs::register_entry_module
  - design/int/int.md §6.1.1
  - repl/spec/00-cli-invocation.md
---

## Request

Find out whether an entry file that exists but cannot be read gets a
diagnostic naming it. Establish the governing requirement first, then a
reproduction.

## Observation

- **Source (read 2026-09-30, `fefd41e8…`).** `register_entry_module` reads a
  resolved entry with `std::fs::read_to_string(&path).unwrap_or_default()`.
  A read error therefore becomes an empty source in every mode.
- **Expected faces (design(int) read, int §6.1.1 residual lead).** `--run`
  reports a missing `main`. `--test` reports an empty run and exits 0. Neither
  is reproduced.
- **Requirement gap.** CLI §0.5.5 rule 2 governs a missing file, not an
  unreadable one. No located requirement names this case. Class **L**: the
  source fact is confirmed, but whether the behaviour is a defect is not
  established.

## Disposition

- **Not an S122 package item and not carried.** No user decision exists.
  `sprint` should put the carry question in the Phase 5 → 6a presentation,
  not in a separate question cycle.
- **When resumed:**
  - `spec` locates or asks for the governing requirement;
  - `test` then reduces the reproduction, a mode-000 entry file under
    `--run` and `--test`, with the existing-readable-entry control;
  - the owner is `dev`(src), at the same registration seam as K1.
- **Refuted if** an unreadable entry already fails with a located read error
  in every batch mode.
