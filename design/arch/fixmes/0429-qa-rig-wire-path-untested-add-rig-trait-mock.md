---
number: 0429
target: /qa
filed_by: /sprint
filed_at: 2026-06-22
sprint_filed: 88
refers_to: src/agent/provider.rs (RigModel + block_on bridge), src/agent/request.rs (rig request build + response/tool-call mapping), tests/agent.rs, tests/plan/agent-testing-strategy.md §1, design/int/agent.md §6
status: deferred
target_sprint: 89
---

# The rig wire-path (`provider.rs` / `request.rs`) has no automated test — add a rig-trait-level mock

## Issue

The S88 Wave-3 agent MVP is tested deterministically via a **stub that implements
the `AgentModel` membrane** (one layer *above* rig). That covers `agent_turn`,
the harvester, the primer, pull-as-visible-commands, and the read-only consent
gate (~49 tests, all offline). It does **not** cover the rig integration itself:

- `src/agent/provider.rs` — `RigModel<M: CompletionModel>`, the current-thread
  tokio `block_on` bridge, and the actual call into rig's `CompletionModel`.
- `src/agent/request.rs` — building rig's `CompletionRequest` from our
  `AgentRequest`, and mapping rig's response / tool-calls back to `ModelResponse`.

Both are **compile-checked only**. Because the stub sits above rig, no automated
test drives a real provider — the first time the rig wire-path actually runs is
against a live Anthropic/Ollama endpoint. This is a real (fixable) coverage gap.

**User decision (S88 Wave 3, 2026-06-22):** accept the gap for the MVP (option
(b)) — it is a default-off, feature-gated, dev-only capability — and file the
test as an S89 follow-up. The Wave-3 cleanup already removed the one panic in
this path (FIXME-I1: `RigModel::new` now returns `Result` and falls back to
dormant instead of `.expect()`).

## Proposed resolution (S89)

1. **Add a Lane-A rig-trait-level mock.** Implement
   `rig_core::completion::CompletionModel` with a canned response (and a canned
   tool-call response), inject it as the provider, and assert deterministically
   (no network):
   - `request.rs` builds the rig request correctly from an `AgentRequest`
     (system primer + harvested context + transcript + user turn present);
   - `provider.rs` maps rig's response → `ModelResponse::Done(prose)` and rig's
     tool-calls → `ModelResponse::ToolCalls(...)` correctly;
   - the `block_on` bridge returns cleanly (no nested-runtime panic).
   This closes the mapping gap without a live endpoint.
2. **One-time manual Lane-C smoke** (user-owed — the S88 environment had no
   `ANTHROPIC_API_KEY` and no local Ollama): run `/ask` against a real
   Anthropic key AND/OR a local Ollama once, confirm a grounded answer + a
   shown-not-submitted `(defn …)`. This is the eval lane, not CI.
3. **Doc correction (one line):** `tests/plan/agent-testing-strategy.md §1`
   currently says "the stub implements the same rig trait the real providers
   do" and references `Box<dyn rig::completion::CompletionModel>`. As-built the
   stub implements the **`AgentModel` membrane**, not rig's trait directly;
   the rig-trait-level mock (step 1) is what covers the rig wire-path. Reconcile
   to match `design/int/agent.md §6` (the `AgentModel` membrane; FIXME 0427).

## Operational implication / Context

- Not a defect, no failing test — a coverage gap for an integration path that is
  hard to exercise without a mock. A design FIXME (not a failing test) is the
  right record per `memory/feedback_no_fixme_with_failing_test.md`.
- Scoped to S89 (the agentic-REPL Build/Document/validator sprint), where the
  rig path gets exercised harder anyway (Build mode submits real model output).
