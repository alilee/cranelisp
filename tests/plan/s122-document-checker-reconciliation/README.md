# S122 document-checker reconciliation evidence

QA owns this immutable historical reconciliation carrier. The parent
[S122 evidence plan](../s122-evidence-delta.md#d7-project-gate-cutover-allocation)
establishes its purpose and current limits.

`legacy-baseline.txt` preserves the retired checker baseline byte for byte,
including historical policy comments. Those comments are provenance, not current
suppression authority. `legacy-mapping.json` preserves the completed mapping:
605 entries in original order, 507 mapped entries (506 identities), 69 repairs,
29 explained old-only entries, zero unexplained. Mapping identities describe the
recorded candidate observation, not guaranteed current findings after repairs.

Neither file is a runnable checker baseline or permission to suppress findings.
Project integration must not pass either file to the shared checker. Retire the
old executable and its active baseline path; preserve these records independently.
New exceptions require their own specific approval. This carrier does not claim
a clean corpus, approve pending historical proposals, or accept all Phase5 work.
