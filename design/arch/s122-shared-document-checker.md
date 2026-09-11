# Shared document checker

Approved D7 direction: [S122 scope](../../sprints/SPRINT.md), user decision
2026-09-10. This is the implementation contract. Phase 5 implementation and evidence work
are approved and underway. The user directed implementation/integration first
and exception processing second (2026-09-11); unresolved findings remain visible. No compiler or
public Rust API changes.

## Boundary and ownership

One offline Python 3.11+ standard-library command belongs to the shared `.agents`
package: `tools/check_documents.py`. It owns discovery, inventory graph
validation, reference resolution and findings. Project-owned
`standing-documents.toml` supplies policy; project memories establish products.
No project names, fixed project exclusion lists, generators, network requests,
plugin interface or Rust parser belong in the shared mechanism.

Extract/adapt the adjacent Magic repository's check-standing-documents.py graph
checks and check_references.py reference handling (both in its scripts directory);
incorporate Cranelisp's
[source checker](../../scripts/verify-citations.py) rules and useful fixtures.
Do not preserve Magic's declaration-limited discovery or silent ambiguous
resolution. Shared-tool dev owns implementation and unit fixtures; test owns
Cranelisp script integration, migration observations and CLI acceptance evidence.
Document owners repair their own declarations and prose.

## Shared contract and project adoption

The package's [Shared document checking contract](../../.agents/CONSUMING.md#shared-document-checking)
is the canonical home for the CLI, TOML declaration schema, independent
discovery and nearest-memory establishment, reference resolution, historical
policy, exit statuses and ratchet identities. The
[package memory](../../.agents/CLAUDE.md) establishes the tool. This project
uses that contract without a competing local schema or resolver specification.

Cranelisp's declaration must retain its existing source-path, line/range and
symbol-presence checks during cutover. Source comment extraction is separate
from document establishment; code files do not become standing documents.
Exact products/memories require path evidence in their establishing memory;
only collection classes also require repetition of their declared purpose.
The approved archive policy preserves historical outgoing references; no new
live-reference waiver or retained debt follows from adopting the command.

## Evidence, ratchet and cutover

Test first uses representative temporary fixtures, then runs full discovery and
validation against Cranelisp and Magic with an explicit corpus/config/rule
manifest. Magic uses an external temporary declaration if adaptation is needed;
its working tree stays unchanged. Compare old/new Cranelisp source checks on the
same inputs; inspect differences rather than accepting a lower count. Map every
existing ratchet identity explicitly to a new identity, a demonstrated repair,
or an explained coverage difference. Unmatched/new findings are not grandfathered.
Any proposed retained debt/exception is presented specifically for approval;
user scope approval is not approval of residual exceptions or wholesale baseline
migration. Reference exemptions cannot silently reset establishment debt.

Build and validate the shared candidate under the existing
[package contribution workflow](../../.agents/CONSUMING.md). The current shared
pin remains held during this design work; no foreign package update, Magic edit
or upstream publication follows from this contract. Cranelisp adoption follows
candidate validation and the planned local package change workflow. Cut over the
project invocation and inventory, then retire the local checker implementation.
The user-directed sequence is implementation/integration first, then exception
and debt processing. Do not install pending historical policies or turn mapped
old baseline identities into suppressions merely to obtain exit 0. Preserve the
complete input/output reconciliation in the
[QA migration carrier](../../tests/plan/s122-document-checker-reconciliation/README.md).
Its legacy baseline bytes are historical evidence, never suppression input. The production
document gate reports all unsuppressed findings and fails on them; integrating
the mechanism does not establish that the later debt gate is clear.
A compatibility launcher may only
delegate to the shared CLI. Do not retain two permanent tools or a local fork.
QA owns the acceptance allocation in the
[S122 evidence plan](../../tests/plan/s122-evidence-delta.md).
