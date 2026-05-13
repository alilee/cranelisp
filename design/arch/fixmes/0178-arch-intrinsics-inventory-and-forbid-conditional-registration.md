---
number: 0178
target: /arch
filed_by: /dev
filed_at: 2026-05-13
sprint_filed: 66
refers_to: design/arch/facades/intrinsics.md, design/arch/facades/backend.md, src/session_v4.rs::int_intrinsics, src/worker.rs::inline_jit_codegen_for_names, src/pipeline.rs::compile_and_execute_expr
status: open
---

# Inventory `discover-tests` / `run-test` / `cranelisp_trace_format` as int-owned intrinsics, and forbid conditional registration of intrinsics

## Issue

Pre-Sprint 66 Wave 3a-γ, three runtime extern functions in `src/session_v4.rs`
were registered with the JIT conditionally — per-compilation, gated on
syntactic scans of the program for direct references:

| JIT symbol | Rust fn | Pre-S66 gate |
|---|---|---|
| `discover-tests` | `discover_tests_extern` | `Self::program_uses_test_forms(program)` |
| `run-test` | `run_test_extern` | `Self::program_uses_test_forms(program)` |
| `cranelisp_trace_format` | `repl_trace_format` | `Self::program_needs_trace(program)` |

Per the definition in `design/arch/facades/intrinsics.md`, these ARE intrinsics
— backend-emitted-call targets invoked from JIT-emitted CLIF, same category as
`heap_alloc`, `runtime/panic`, primitive arithmetic, vec ops. They should be
registered uniformly with all other intrinsics, unconditionally, at JIT setup.

The conditional registration is an architectural wart with concrete failure
modes:

1. **Cross-compilation regression** — After the Wave 3a-β int refactor moved
   typecheck dispatch through `worker::check_program_compat`, the
   conditional `extra_jit_symbols` plumbing stopped reaching every JIT
   build site. The prelude's `stdlib/testing/runner.cl::run-tests-report`
   declares `run-test` as `Linkage::Import` whenever it's compiled, so the
   first REPL eval after prelude load panicked with
   "can't resolve symbol run-test" at JIT finalize.

2. **Transitive-reference invisibility** — The pre-S66 syntactic scan only
   matched direct references in the program being compiled. A user-level
   `(my-run-tests)` defn whose body calls `discover-tests` is invisible to
   this scan when the program in question is just `(my-run-tests)`. Defect
   8 (Sprint 59) papered over this with `any_compiled_defn_uses_test_forms`
   — a session-wide scan of every previously-compiled defn — which is
   strictly worse than just registering the intrinsic unconditionally.

3. **Multiple registration paths drift** — The plumbing had to be threaded
   through `codegen_and_execute` (codegen pre-step), then through
   `compile_and_execute_expr` (expression JIT), then through the trace
   variant `compile_and_execute_expr_with_trace`. Each of these sites had
   its own gate; the codegen-pre-step gate and the eval-JIT gate were
   independently maintained and drifted apart in the Wave 3a-β refactor.

This is the same principle as `design/arch/facades/backend.md` §"no goals"
clause forbidding operator special-casing: uniform dispatch through a single
mechanism, no per-feature branches.

## Proposed resolution

### Inventory update (`design/arch/facades/intrinsics.md`)

Add `discover-tests`, `run-test`, `cranelisp_trace_format` to the int-owned
intrinsics list. Note:

- These intrinsics dereference thread-local state (`TestRunnerState`,
  `TraceDisplayState`) set just-in-time by the REPL eval path. The state
  pointer is null when no eval is active; the intrinsics null-check and
  return harmless defaults (`alloc_io_pure(SNil)`, `"?"`).
- The `TestRunnerState` allocation is owned by `SharedState` (built once in
  `CompilerSession::new`, stable for session lifetime); `/mod` updates only
  the `current_module` field through its `Mutex`.
- The Rust source for the externs currently lives in `src/session_v4.rs`
  (int crate). FIXME 0176 (D43 source migration) is the broader move to
  `crates/cranelisp-intrinsics/` — independent of this inventory-and-rule
  change.

### Forbidden patterns clause

Add to `design/arch/facades/intrinsics.md` a "Forbidden patterns" section
mirroring `design/arch/facades/backend.md`:

- **No conditional registration of intrinsics.** Every intrinsic enumerated
  in the inventory MUST be registered unconditionally at JIT setup
  (`JITBuilder::symbol()` or equivalent platform path). A syntactic scan of
  the current program to gate `JITBuilder::symbol(...)` calls is a Blocker
  finding for `/review`.
- **Rationale**: the JIT declares `Linkage::Import` for every intrinsic
  referenced anywhere in the compiled code — direct references in the
  current program, transitive references through previously-compiled
  defns, prelude defns loaded at session startup. The "current program"
  is not the right scope; the JIT's import set is. The cost of
  registering an unused intrinsic is one `HashMap` entry. The cost of
  missing one is a JIT-finalize panic.

### Pre-S66 helpers to retire

The following helpers and their call sites were deleted in this change set
and should not return:

- `CompilerSession::program_uses_test_forms`
- `CompilerSession::any_compiled_defn_uses_test_forms`
- `CompilerSession::program_needs_trace`
- `CompilerSession::any_expr_in_program`
- `CompilerSession::expr_uses_test_forms`
- `CompilerSession::expr_needs_trace`

These were the conditional-scan machinery; their architectural purpose
(deciding whether to register an intrinsic) is now answered by "always".

## Operational implication / Context

**Sprint 66 Wave 3a-γ status**: the implementation half of this FIXME has
landed — `inline_jit_codegen_for_names` and both `compile_and_execute_expr`
variants now call `crate::session_v4::int_intrinsics()` unconditionally, and
the conditional helpers are deleted. What remains for `/arch` is the
**inventory update** (write the three symbols into
`design/arch/facades/intrinsics.md`) and the **forbidden-patterns clause**
(codify the rule). Without these, a future refactor could regress to
conditional gating with no design-doc anchor to prevent it.

**Interaction with FIXME 0176** (D43 source migration to
`cranelisp-intrinsics`): orthogonal. FIXME 0176 moves *where* the Rust
source for these externs lives; this FIXME (0178) codifies *how* they're
registered with the JIT. The forbidden-patterns clause survives the source
migration unchanged.

**Interaction with FIXME 0177** (typecheck cross-form state regression):
this FIXME (0178) unblocks REPL eval for any program that doesn't trigger
the constrained-polymorphism stack-overflow path. With FIXME 0178 resolved,
`(defn id [x] x)` is accepted at the REPL; with FIXME 0177 still open,
`(id 7)` then overflows. The two failures were entangled pre-fix; they
unmask cleanly now.

**Test surface**: the minimal repro is in the FIXME 0177 carry; a narrow
regression test (`echo '(defn id [x] x)' | cranelisp` must not panic)
should be added once `/qa` next sweeps. The wider 93-failure baseline
is unchanged by this fix — the failures are downstream of 0177's
constrained-polymorphism regression, not of intrinsic registration.
