---
number: 0586
target: /testing
filed_by: /dev
filed_at: 2026-07-14
sprint_filed: 109
refers_to: five tests/agent.rs e2e tests assert the PRE-§17.2.1 "pull renders as a
  visible command" behaviour (the `agent> {cmd}` echo + inline result). W2/0577-A
  implements §17.2.1 (probe traffic is PRIVATE — routed to the log/trace, never the
  user session; OB-9). These tests now assert removed behaviour and go RED. They
  are the inverse of the new OB-9/OB-10 guards and need INVERT / regen, not fix.
status: open
---

# /testing → pull-visible-command e2e tests superseded by the §17.2.1 probe channel (W2/0577-A, OB-9)

## What changed (landed this wave, `src/agent/`)

`repl/spec.md §17.2.1` (landed by `/repl`) ruled that **a probe MUST NOT scroll the
user session** as an `agent> {command}` echo followed by its result — probe traffic
routes to the **private working channel** (the §17.20 activity log + §17.21 trace);
the user sees only the agent's conclusions (`▌` gutter prose) and the landed
definitions. W2 implements this: `pull.rs::run_pull`'s read-command arm now runs the
probe against a THROWAWAY sink (nothing to stdout) and records the result only in the
log. The new guards `agent_probe_traffic_not_echoed_to_session_neg` (OB-9) and
`agent_probe_conclusions_and_definition_still_shown` (OB-10) are GREEN.

## The superseded tests (tests/agent.rs — `/testing`-owned, hence this FIXME not a silent edit)

These five assert the OLD visible-command behaviour and now FAIL for the right reason
(the echo they require is gone). They are the direct inverse of OB-9/OB-10:

| Test | What it asserts (now removed) | Suggested action |
|---|---|---|
| `stub_pull_renders_as_visible_command` | `/source target` renders as-typed | INVERT → assert the probe command is NOT echoed (dup of OB-9) OR delete (OB-9 covers the contract) |
| `agent_issued_pull_shows_agent_prompt` | the pull carries the `agent>` prompt + `/source target` | delete / fold into OB-9 (the `agent>` probe echo is gone) |
| `agent_pulls_syntax_renders_as_command` | `/syntax hkt` renders as-typed with `agent>` | delete / fold into OB-9 |
| `agent_tool_call_turn_not_streamed` | the pull renders unframed with `agent>` echo + unframed result | rewrite: the "not streamed/not framed" intent survives, but the pull no longer renders at all — re-pin against the conclusion prose instead, or delete |
| `agent_session_render_golden_transcript` | full-transcript golden that INCLUDES the probe echoes | REGEN the golden (`CRANELISP_TEST_UPDATE_GOLDENS=1`) — the new transcript omits the probe lines |

The `/dev`-owned lib tests in `src/agent/pull.rs` (`run_pull_source_captures_command_output`,
`pull_result_no_mangled_sgr_for_user_or_model`) were already updated in this change-set
to assert the private-channel behaviour (the sink stays empty; the model-fed copy stays
clean).

## Not this FIXME (pre-existing, flag to `/qa` separately)

`set_doc_non_function_target_e2e_refused_not_recorded_neg` also fails, but it fails on
the **pre-W2 tree too** (verified by stashing the W2 change-set): its refusal now reads
`no such definition: Red` instead of `only function definitions persist a docstring`.
That is a pre-existing set-doc resolution defect unrelated to the probe channel — do
NOT fold it into this INVERT; it needs its own triage/owner.
