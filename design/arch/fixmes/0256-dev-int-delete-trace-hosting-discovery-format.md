---
number: 0256
target: /dev (int)
filed_by: /arch
filed_at: 2026-06-04
sprint_filed: 76
refers_to: design/arch/tracing.md §4.3 §5, design/arch/bounded-contexts.md §6, src/trace.rs, src/session_v4.rs, design/arch/facades/int.md §"Observability" + §"Int-owned JIT intrinsics"
status: open
---

# Delete int's trace hosting — bodies, discovery, formatter, and the trace half of int_intrinsics()

## Issue

Per the 2026-06-04 trace ruling (`design/arch/tracing.md` TARGET STATE + BC §6), int hosts **no**
`(trace ...)` runtime code. D40's relocation of the trace bodies to int is retracted. int's S76 trace
work is **deletion only** — the bodies go to intrinsics (FIXME 0254), discovery + descriptor baking go
to backend (FIXME 0255).

## Proposed resolution

Delete from int (`tracing.md` §4.3 is the inventory):

1. **`src/trace.rs`** — delete in full (12 bodies + `TRACE_STACK` + `TRACE_THREAD_ID` +
   `THIS_THREAD_ID` + `consume_trace_call` + the unit-test fallback `cranelisp_trace_format`). Target home
   is `crates/cranelisp-intrinsics/src/trace.rs` (FIXME 0254). Remove the `mod trace;` declaration.

2. **`src/session_v4.rs::build_traced_fns`** (`:2727`) — delete. Discovery is now backend's (FIXME 0255).
   Delete the call site (`:2663`) + the `traced_fns` local + its threading into
   `crate::pipeline::compile_and_execute_expr` (the `&traced_fns` argument). `compile_and_execute_expr` +
   any `inline_jit_codegen_for_names` trace plumbing lose the `traced_fns` parameter (coordinate with the
   S76 `Jit::new(symbol_tables)` collapse — these call paths are being reworked there anyway).

3. **`src/session_v4.rs::repl_trace_format`** (`:5154`) + **`TraceDisplayState`** + the **`TRACE_DISPLAY`
   thread-local** + **`set_trace_display_state` / `clear_trace_display_state`** (`:5127`–`:5170`) —
   delete. The formatter is now the descriptor-driven intrinsic (FIXME 0254). Delete the
   `set_trace_display_state` / `clear_trace_display_state` call sites around eval (`:2665`–`:2680`).

4. **`src/session_v4.rs::int_intrinsics()`** (`:4938`) — delete the **trace half** (the 12 trace entries +
   the `cranelisp_trace_format` entry). It reduces from 14 to **2 entries**: `discover-tests` + `run-test`
   (the test intrinsics are PARKED — out of scope per the user, left as-is). Update the array type
   `[(&'static str, *const u8); 14]` → `; 2]` and the `src/CLAUDE.md` §"Int-owned JIT intrinsics" table
   (drop the `cranelisp_trace_format` row).

5. **`src/display.rs` is UNTOUCHED** — `format_result_value` (REPL result display with `:Type` prefix)
   is not part of trace capture and stays. (Backend/intrinsics reimplement the `format_value` *logic* as
   the descriptor walker; int's copy stays for REPL results.)

6. The exe-bundle `pub use cranelisp_intrinsics::trace;` force-link restoration is logically backend's
   reason (FIXME 0255) but exe-bundle is int's file — make the one-line edit when 0255/0254 land so the
   trace symbols are in the staticlib for `--link`.

7. Run the int test suite (the owning-changes agent runs tests) + regenerate `src/`-side baselines if any
   public surface changed (the `int_intrinsics` visibility / `clear_trace_display_state` pub fn removal).
   Fix introduced warnings.

## Operational implication / Context

Pure subtraction for int — the entire trace burden in S76 is these deletions (the design summary's
"int wave's trace burden becomes: nothing but deletions"). Must land in concert with FIXME 0254 (bodies
arrive in intrinsics) and 0255 (discovery + format arrive in backend) so the build is not left with
dangling references; expect a transient red build during the wave, resolved when all three land.
Sequencing is **/sprint + user's call**. The facade `design/arch/facades/int.md` §"Observability" +
§"Int-owned JIT intrinsics" tables also need the trace rows struck — file a paired `/design int` note or
fold into this change-set's facade update per the baseline-diff discipline (the int facade is the one
still-live facade; `/arch` will update its trace sections once the deletions land — flag in the commit).
