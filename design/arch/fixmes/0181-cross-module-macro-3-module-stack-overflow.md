---
number: 0181
target: /typecheck
filed_by: /sprint (autonomous mode)
filed_at: 2026-05-14
sprint_filed: 66
refers_to: tests/spec_09_macros.rs (4 cross_module_macro_* tests), spec/09-macros.md §9.1.3 (hygiene), spec/08-modules.md §8.10
status: open
---

# Cross-module macro 3-module chain stack-overflows worker thread

## Issue

When a 3-module chain participates in a macro expansion (consumer → macro_module → helper_module, where the macro body references a symbol from a third module), worker-thread compilation stack-overflows.

## Minimal repro

```bash
mkdir -p /tmp/mac_repro && cd /tmp/mac_repro

cat > main.cl <<'EOF'
(import [macmod [wrap-seven]])
(defn main [] (wrap-seven))
EOF

cat > macmod.cl <<'EOF'
(import [helper [make-seven]])
(defmacro wrap-seven [] `(make-seven))
EOF

cat > helper.cl <<'EOF'
(defn make-seven [] 7)
EOF

/path/to/cranelisp --run main.cl
```

Output:
```
thread 'priority-worker-0' has overflowed its stack
fatal runtime error: stack overflow, aborting
```

## Narrowing

- **2-module case works**: drop the third module — `(defmacro seven [] `7)` in macmod.cl, called from main.cl — exits with 7 correctly. No overflow.
- **3-module case overflows reliably**: macro body references a symbol that lives in a third (helper) module.
- The overflow happens on `priority-worker-0`, not the main thread — i.e., during the worker's typecheck or codegen of the expanded macro, not during the synchronous orchestrator pass.

## Hypothesis

The macro body `(make-seven)` is bare. Per spec/09-macros.md §9.1.3 hygiene, macro expansion should qualify the bare reference to its home-module form (`helper/make-seven`) so the expansion result resolves independently of the call site's imports. If the expander instead emits the bare symbol AND the call-site retry loop doesn't recognise the gap-resolution boundary, the loop may recurse.

Plausible recursion sites (priority-worker-0 frames):
1. **Frontend `expand`** re-entering itself on the expanded form because the bare `make-seven` triggers another macro-resolution attempt.
2. **Worker's gap-retry loop** in `process_cluster` / `check_program_compat`: gap fires → loads helper module → retries cluster → bare symbol still not visible from main → gap again → recurse.
3. **Typecheck's chain-follow** through module imports: an import-binding chain that doesn't terminate cleanly when crossing the macro-expansion boundary.

## Test coverage (regression guard already present)

The following e2e tests in `tests/spec_09_macros.rs` currently fail with this overflow:
- `cross_module_macro_calls_helper_in_other_module` (2-module + helper)
- `cross_module_macro_drives_transitive_call_graph`
- `cross_module_macro_emits_qualified_reference`
- `cross_module_macro_transitive_via_reexport_chain` (A → B → C → D re-export chain)

These are failing-not-ignored per `memory/feedback_failing_not_ignored.md`. No additional regression guard needed — the e2e suite already pins the failure mode.

## Proposed investigation path

Same isolation technique as today's poly-fix (Wave 3a-tail commit `7680bc9`):

1. Reproduce in a `crates/cranelisp-frontend` or `crates/cranelisp-typecheck` unit test that drives a 3-module setup without int's worker. If the overflow reproduces in the unit test, the bug is contained in frontend/typecheck. If it doesn't, the bug is in int's worker orchestration.
2. Instrument suspect recursion sites (counter on `expand` entry; counter on `check_forms` entry; bounded recursion depth in chain-follow).
3. Find the loop and fix it.

## Cluster scope

4 failing e2e tests cluster on this single root. Fixing 0181 likely clears all 4 plus any related multi-module macro flows. Estimated effort: comparable to today's poly fix (~hour of isolation + targeted fix).

## Architectural context

The 2-module case working confirms the basic macro expansion path is sound. The 3-module case introduces the specific hygiene complication: the macro body references a symbol that ISN'T in the consumer's import set. Per Principle 17 (module locality) and spec §9.1.3, the expander must FQ-qualify such references at expansion time. The bug is either in that qualification step or in how the consumer-side machinery interacts with FQ-qualified references that point to modules not directly imported by the consumer.
