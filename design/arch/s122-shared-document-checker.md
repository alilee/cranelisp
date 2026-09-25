# Shared document checker

**Status: delivered S122 integration contract.** The user approved the direction
on 2026-09-10. The shared checker is installed and the project's local checker
is retired. This document states the project boundary the integration keeps;
retire it at S122 close, once the sprint and QA records that cite it are
archived, after confirming that each rule below still has a canonical home.

## Boundary and ownership

- **The mechanism is shared.** `.agents/tools/check_documents.py` — one offline
  Python standard-library command — owns discovery, inventory graph
  validation, reference resolution and findings. Its CLI, declaration schema,
  establishment rules, reference resolution, historical policy, exit statuses
  and finding identities are the package's
  [shared document checking contract](../../.agents/CONSUMING.md#shared-document-checking).
- **Policy is the project's.** `standing-documents.toml` (owned by `sprint`)
  supplies ownership, classification and reference roots; project memories
  establish documents. Cranelisp keeps no competing local schema, resolver or
  fork, and a local launcher, if one is ever added, may only delegate to the
  shared command.
- **Nothing project-specific enters the shared tool**: no project names, fixed
  exclusion lists, generators, network access, plugin interface or Rust
  parser.
- **Source files are reference inputs, not documents.** Source path, line and
  symbol-presence checks apply to citations; code files never become standing
  documents.
- Document owners repair their own declarations and prose.

## Findings are not debt by default

- The project invocation applies no baseline
  ([root assurance guidance](../../CLAUDE.md#records-are-claims-too)).
  Outstanding findings are repaired or explicitly dispositioned; installing the
  checker accepted none of them.
- The retired checker's baseline and the complete old-to-new identity mapping
  are retained as
  [reconciliation evidence](../../tests/plan/s122-document-checker-reconciliation/README.md),
  never as suppression input.
- A proposed exception or retained debt goes to the user specifically; scope
  approval does not approve residual exceptions. Historical-record policy
  preserves an archive's outgoing references and creates no live-reference
  waiver.
