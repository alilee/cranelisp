---
id: ACT-0960
title: Project agent configuration and multi-model eval comparison
status: open
priority: advisory
from: sprint
to: arch
sprint: 122
filed_at: 2026-09-19
refers_to:
  - src/agent/provider.rs
  - src/session_setup.rs
  - repl/spec/17-embedded-agent.md
  - tests/scripts/run-agent-evals.py
---

## Request

Schedule these related extensions in future sprints. The user deferred them
on 2026-09-19 so S122 can run the existing eval corpus against the latest Haiku:

- Project-TOML configuration for the embedded agent's provider, model and
  endpoint, with credential handling and override precedence settled explicitly.
- GPT/OpenAI support through the embedded agent's Rig integration.
- A configurable multi-model eval campaign and combined comparison report,
  including more capable Claude models and GPT models. Reuse tasks, prompts,
  fixtures, compiler and graders; record model versions, inference settings,
  repeats, all outcomes and available timing/tool/token/cost observations.
  Latest Haiku remains the reference quality benchmark.

Source verified on filing: provider construction reads environment variables
and wires Anthropic, Ollama and stub; the project loader reads library and
platform paths. The embedded-agent specification explicitly forbids TOML
provider/model/key configuration, so the new direction requires specification
reconciliation. The eval runner accepts one provider/model per invocation and
records provenance and repeated task results, but has no combined comparison
report or OpenAI route.

## Completion evidence

Coordinate spec, design, QA and test around the agreed configuration contract
and provider support. Deliver project configuration with precedence and
credential behavior documented and tested, GPT execution through the same
agent path, and comparable multi-model reports over the same corpus. Live
campaign scope and spend remain separately bounded. Preserve the existing
Haiku baseline and explain any changed comparison dimension.

This future work is not a prerequisite for the current Haiku run. Filing it
does not authorize live comparison spending or an inter-crate public API delta.
