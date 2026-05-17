---
number: 0205
target: /design (int)
filed_by: /dev (int)
filed_at: 2026-05-16
sprint_filed: 67
refers_to: design/arch/facades/int.md §"Int-owned JIT intrinsics", design/arch/facades/int.md Wave-4 PIF row 648, src/CLAUDE.md §"Int-owned JIT intrinsics", src/session_v4.rs::int_intrinsics, src/trace.rs, src/io_trace.rs, design/arch/decisions/0040-runtime-trace-io-trace-relocate-to-int.md
status: open
---

# Refresh `facades/int.md` for the relocated trace edifice (int_intrinsics table grew from 3 to 14)

## Issue

Sprint 67 Wave 4 — FIXMEs 0197 + 0202 + 0204 — landed the Decision-40
Path-B1 relocation of the trace edifice from `cranelisp-intrinsics` to
`int`. The implementation change-set:

1. **Hosted** the 12 `cranelisp_trace_*` JIT-emitted-call bodies in
   `src/trace.rs`.
2. **Hosted** the io_trace ring buffer + observer-record + flush guard +
   panic hook in `src/io_trace.rs` (the pre-existing forwarder shell
   absorbed the bodies; see also FIXME 0201 — the io.rs trampoline now
   emits through `io_observer::emit`).
3. **Registered** the 12 trace symbols via
   `src/session_v4.rs::int_intrinsics()`. The map grew from 3 entries to
   14 (= 3 prior + 11 new — `cranelisp_trace_format` was already there
   pointing at `repl_trace_format`; the 11 additions are
   `cranelisp_trace_enter`, `_exit`, `_swap_got`, `_restore_got`,
   `cranelisp_collect_trace`, `_first_child_nanos`, `_name`, `_params`,
   `_result`, `_children`, `_nanos`).
4. **Wired** the frontend `link_mode::validate_*` validator into
   `worker::build_program_compat`, threading `CodegenBehaviour` from
   `SharedState` (newly carries `codegen_behaviour: CodegenBehaviour`).

`facades/int.md` §"Int-owned JIT intrinsics" presently inventories the
3-entry int_intrinsics shape Wave 3a-γ established and the Wave-4 PIF
row 648 cites only 1 of the 12 trace fns (per /arch's earlier scan
note). The facade needs to refresh to:

- Name the int-intrinsics inventory at 14 entries (or rephrase as
  "trace edifice complete: 12 `cranelisp_trace_*` + 2 test extern fns,
  registered uniformly via `int_intrinsics()`").
- Either enumerate all 12 trace fns in the inventory table or absorb
  them under a "trace edifice (12 fns)" entry.
- Document the new `CodegenBehaviour` thread on `SharedState` and the
  `build_program_compat(&[Sexp], CodegenBehaviour)` signature change
  (the validator-wiring path).
- Cite `src/trace.rs` + `src/io_trace.rs` as Int-side homes for the
  relocated edifice (the Decision 40 cross-reference is already
  there; the facade body needs to match).

## Proposed resolution

Edit `design/arch/facades/int.md`:

1. §"Int-owned JIT intrinsics" — refresh the inventory table to 14
   entries (or "trace edifice complete: 12 + 2"). Cite `src/trace.rs`
   as the home for the 12 `cranelisp_trace_*` bodies and
   `src/io_trace.rs` as the home for the ring buffer + observer.

2. Wave-4 PIF row 648 — update the row to either name all 12 trace
   fns or absorb them under a "trace edifice complete" summary.

3. Add a §"Build-mode validation" subsection (or fold into existing
   §"process_cluster") noting that `build_program_compat` runs
   `cranelisp_frontend::link_mode::validate_parsed_entry_for_build_mode`
   / `validate_expr_for_build_mode` per parsed entry / expr before
   typecheck dispatch, gated on `SharedState.codegen_behaviour`.

4. Note the `SharedState.codegen_behaviour: CodegenBehaviour` field
   addition (captured at session construction from
   `SessionSettings.codegen_behaviour`).

## Operational implication / Context

**Sequencing**: Lands after FIXMEs 0197 + 0202 + 0204 (the
implementation change-set in S67 W4). `/dev (int)` does not edit
`facades/int.md` (file-ownership boundary).

**Public-API impact**: `int` is a binary crate — no public-api shift.
The facade refresh is documentation-only.

**Unit-of-work**: small (~30 lines of facade text), entirely scoped
to two §-sections and one PIF table row.

**Cascade closure**: With this and FIXME 0206 (backend facade refresh
for the deleted IntrinsicSymbol entries) landed, the Decision-40 /
Path-B1 cascade closes on the facade side. FIXME 0198 (intrinsics
body deletion) remains as the final relocation cleanup.
