---
number: 0502
target: /dev (cranelisp-platform)
filed_by: /sprint
filed_at: 2026-07-03
sprint_filed: 101
refers_to: tests/plan/coverage-audit-s101.md §3 (platform row), sprints/METHOD.md §2.2
status: open
---

# Platform thin-submodule drain — declare.rs + concurrency.rs (v9 ABI vtable) zero-inline coverage

## Issue

The S101 coverage audit's submodule map rates cranelisp-platform ADEQUATE overall (~60 tests / 6k LOC) with two named zero-inline-coverage submodules: **declare.rs** (the platform declaration macro surface — every platform DLL's correctness flows through it) and **concurrency.rs** (the v9 ABI ctx-vtable: HostCtx acquire/retire, Acquire enum, role byte — layout-affecting per the Principle-14 analogue, currently pinned only by cross-crate/e2e paths).

## Proposed resolution

Per METHOD §2.2: derive strategy scenarios per submodule — declare.rs: manifest-order = GOT-slot-order invariant, malformed-declaration negatives, FQ-sig rendering; concurrency.rs: vtable layout pins (size/offset stability across the v9 contract), acquire/retire pairing, role-byte semantics, negative cases (double-retire, use-after-retire under the debug tripwires). Land as per-submodule test modules.

## Operational implication / Context

Sibling of 0495–0498/0500/0501. Natural carrier: effect-concurrency slice-2 (which lands the reactor against exactly this vtable) or any next platform touch.
