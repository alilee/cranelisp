---
id: ACT-1004
title: Verify missing-entry filename diagnostics in normal batch modes
status: open
priority: advisory
from: sprint
to: qa
sprint: 122
filed_at: 2026-09-28
refers_to:
  - repl/spec/00-cli-invocation.md
  - src/exe.rs
  - src/session_v4/lifecycle.rs
  - tests/link.rs
  - tests/cli_missing_entry.rs
  - design/int/int.md §6.1.1
---

## S122 K1 adequacy (qa, 2026-09-30): adequate

**Judgment.** The K1 correction has adequate evidence for CLI §0.5.5 rule 2 in
`--run` and `--link`. `review`(src) found no blocking or required item
(`.local/s122-k1-review-result.md`). Delete this action when the fix is
committed; K4's full run re-verifies.

- **The full run tripped `mode_gating_guard` (2026-09-30).** The fix adds the
  guard's mode-bit origin `None if self.shared.run_mode.is_repl() =>`.
- **QA classes this as allowlist maintenance.** CLI §0.5.5 rule 2 requires
  the branch.
- **Required with the fix.** `test`'s allowlist entry and its rationale must
  land in the same commit
  ([final intake](../../tests/plan/s122-evidence-delta.md#act-1021-amendment--final-intake-2026-09-30)).

- **Source.** HEAD `e4062202` plus the uncommitted diff `fefd41e8…` (re-hashed
  2026-09-30). The fix is at `src/session_v4/lifecycle.rs::register_entry_module`
  ([int §6.1.1](../../design/int/int.md#611-a-missing-entry-source-file)).
- **Red, then green, for the intended reason.**
  - Before the fix, `cli_missing_entry::run_missing_entry_file_is_named_on_stderr`
    and `…link_missing_entry_file_is_named_on_stderr` failed with
    `entry module has no 'main' function`
    (`.local/s122-final-test/k1-red.log`).
  - On `fefd41e8…` both pass. So do the `--test`, REPL and predicate controls,
    `test_runner::test_mode_neg_missing_entry_file_errors_without_report`
    and `link::link_error_when_entry_file_not_found`
    (`.local/s122-final-src-dev/k1-e2e.log`).
- **Module evidence.** The five `lifecycle::entry_registration_tests` rows of
  int §6.1.1 exist. The Run and Link rows went RED, then GREEN; the other three
  are controls (`dev` report).
- **Held by construction, not asserted end to end.** int §6.1.1 also lists
  two absences: no `no 'main'` text, and no executable under `--link`. Both
  follow from the refusal preceding registration (unit-pinned) and from
  `main.rs`'s `startup?` preceding every wait, `trampoline` and
  `link_by_name`. Ignoring the error there would print nothing, which the
  positive cells already catch. No further cell is allocated.
- **Band.** The CLI §0.5.5 `--run` and `--link` rows now cite the two cells
  and their unit rows.
- **Separate intake.**
  - The unreadable-entry lead is
    ACT-1019, closed 2026-10-02
    ([record](../../tests/plan/s122-evidence-delta.md#act-1019--unreadable-entry-file-closed)).
  - Review A3, the dotted-target file mapping, is
    [ACT-1020](ACT-1020-dotted-entry-target-file-mapping-intake.md).

## Request

Reproduce the reported missing-entry diagnostic gap in `--run` and `--link`.
CLI §0.5.5 requires the error to name the missing source file. The existing
link test checks exit status only. The shared-runner work covers the `--test`
leg; it does not establish conformance of the other two modes.

## Evidence and limits

S122 dev and independent review report that entry registration leaves an empty
module and normal batch execution reaches `validate_main`, which emits
`entry module has no 'main' function`. Sprint reopened `src/exe.rs` and
verified that diagnostic, and read the owning CLI requirement. QA classifies
this as a pre-existing conformance lead; no independent reproduction has yet
been recorded. The mechanism attribution remains provisional.

## Completion

Establish a narrow unignored regression for both modes and the filename on
stderr before assigning a fix. If confirmed, design the missing-source check
once for batch callers rather than adding a separate check to each mode.
Retain the `--test` behavior and the REPL's ability to start an empty module.
This intake does not authorize changing the shared runner or expanding its
current correction basket.
