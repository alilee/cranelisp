---
id: ACT-0974
title: Investigate discharge of only-read String primitives used as function values
status: open
priority: normal
from: design
to: qa
sprint: 122
filed_at: 2026-09-21
refers_to:
  - design/backend/non-concrete-release-contract.md
  - crates/cranelisp-backend/src/compiler/control_flow/fn_as_value.rs
  - design/primitives/primitives.md
---

## Observation and limit

The primitives consolidation rechecked backend design §7.6 against
`emit_d24_adaptation`: the GOT wrapper applies adaptation to non-conservative
summaries and discharges `Mode::Borrowed` parameters. The six only-read String
externs also consume their arguments at the extern boundary. This suggests a
possible double discharge when used as function values; source reading alone
does not establish a runtime defect or its attribution.

The design names `str-len`, `str-eq`, `neq-string`, `starts-with?`, `ends-with?`
and `contains?`. The previously planned `primitive_value_d24_s121` evidence
was not found in the current tests during this pass.

## Required disposition

Verify current source and existing evidence first. Establish a minimal
function-value call and a discriminating control before attribution. The
source-read candidate is `(defn call1 [f s] (f s))` applied to `str-len` with
heap String arguments; `string-identity` is a candidate control whose ownership
semantics differ. QA determines the required controls and instrumentation.
If confirmed, retain a permanent failing, unignored spec-traced reproduction
and route the repair to the owning context. Preserve the declarations as the
authority; do not alter them merely to accommodate a wrapper.

Provenance: design (primitives) session
`06f57330-4f77-42bf-8b84-368a4954bd4a`, S122 documentation consolidation.
