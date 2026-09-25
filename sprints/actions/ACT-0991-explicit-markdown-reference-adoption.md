---
id: ACT-0991
title: Adopt explicit Markdown links for document and source references across consumers
status: deferred
priority: required
from: sprint
to: arch
sprint: 122
filed_at: 2026-09-25
refers_to:
  - .agents/CONSUMING.md
  - .agents/tools/check_documents.py
  - standing-documents.toml
---

## Request

Schedule a future increment to adopt explicit Markdown links for file references
and treat code examples as literal text. The user requests this direction to
avoid guessing whether an inline code span names a file or a language symbol.
Establish the convention and checker behavior in se-agentic for coordinated
adoption by Cranelisp, feedback-dev and magic.

- Assess live implicit citations in each consumer; migrate real references to
  explicit links while preserving readable labels, relative resolution, section,
  line/range and symbol checks. Decide the supported representation of those
  selectors before changing extraction.
- Include root establishment and source-comment citation conventions in the
  assessment. A syntax change must not silently drop either reference checking
  or the establishment chain to root CLAUDE.md.
- Sequence migration and checker cutover so existing citations remain checked
  until their replacement is verified. Keep historical records in Git or their
  existing historical policy; do not rewrite them merely for new syntax.
- Retire obsolete literal annotations and implicit extraction only when the
  corresponding consumer migration is complete. Use the shared package's
  contribution/publication and consumer adoption process.

Verified at filing: the shared checker excludes fenced examples and extracts
comments/docstrings from configured source files, but inline code also carries
real citations. A read-only census found 3,066 resolving standalone code-span
path occurrences across 283 live Cranelisp documents, excluding historical
records. This is a planning estimate, not a classified migration inventory;
refresh it and assess the other consumers at intake.

Interim: retain existing reference detection and the approved line-scoped
literal annotation mechanism. The user approved annotations on the nine example
lines responsible for the eight remaining language-name findings; those
annotations are applied. The relaxed bare-path heuristic is not adopted.

## Completion evidence

- A shared convention with tested selector semantics and explicit code-example
  exclusions, applied through each consumer's own adoption scope.
- Before/after citation and establishment reconciliation demonstrating that real
  missing paths, invalid selectors and orphans remain detectable, while literal
  examples no longer produce reference findings.
- Planted-fault and valid-example tests for the changed extraction boundary;
  unnecessary annotations and transitional machinery removed.

This action defers migration; it does not authorize publication, sibling edits
or an S122 phase transition.
