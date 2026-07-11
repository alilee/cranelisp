---
number: 0559
target: /design
filed_by: /review
filed_at: 2026-07-11
sprint_filed: 108
refers_to: design/int/agent.md §6.1 (neutral→rig field mapping); src/agent/provider.rs AGENT_MAX_TOKENS
status: open
---

# agent.md §6 does not carry the max_tokens request-assembly contract the D3 guard cites

## Severity

Suggestion

## Issue

The S108 D3 fix (FIXME 0554) established a binding request-assembly fact: every
assembled rig `CompletionRequest` MUST carry `max_tokens` (Anthropic's Messages
API rejects a request that omits it — every turn 400s), satisfied by
`AGENT_MAX_TOKENS: u64 = 65536` on the single shared `build_request` builder
(`src/agent/provider.rs`), sized for the streaming transport per the S108 arch
approval.

The guard test `build_request_sets_max_tokens_for_anthropic` cites
`// spec: design/int/agent.md §6` as the requirement's home — but agent.md
nowhere states it. `max_tokens` does not appear in the doc; the neutral→rig
field mapping in §6.1 lists preamble/context/transcript/tools and omits the
completion budget entirely. The doc's only "budget" content is the §5 *harvest*
token budget ("a runtime config knob (§6.4), not a constant") — a distinct
concept that, read carelessly, even appears to contradict the new named
constant. The two-sided traceability convention wants the cited doc side to
actually carry the requirement; today the constant's rustdoc is the sole
durable record.

## Proposed resolution

/design's call, per the drift-resolution boundary in `.claude/commands/review.md`:

- Preferred: add one entry to §6.1's neutral→rig field mapping — completion
  budget → `max_tokens`, MANDATORY for Anthropic (omission 400s before a token
  streams), `AGENT_MAX_TOKENS` = 64K streaming-sized default (full rationale on
  the constant's rustdoc), explicitly distinct from the §5 harvest token budget.
- Alternatively: direct /dev to re-point the test's `// spec:` citation at
  whatever home /design designates.

## Context

Surfaced by /review during the S108 Wave 2 D3 change-set review. The fix itself
is correct and CLEAR; this FIXME records only the doc-side traceability gap.
