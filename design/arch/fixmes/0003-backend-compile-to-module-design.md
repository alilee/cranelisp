---
number: 0003
target: /design
filed_by: /arch
filed_at: 2026-04-25
sprint_filed: 63
refers_to: design/arch/facades/backend.md (Public surface, compile_to_module entry); design/backend/{backend}.md (planned, M2)
status: open
---

# Elaborate `compile_to_module` return shape per Decision 35

## Issue

`compile_to_module` is the canonical codegen entry point for `cranelisp-backend` (single entry per Decision 24, refined by Decision 35). Its return shape is currently `(Arc<Jit>, HashMap<Symbol, *const u8>)` — JIT handle + symbol-to-fn-pointer map. The facade spec at `design/arch/facades/backend.md` lists this signature as the as-designed surface.

The shape is correct but underexplained. Several questions need elaboration in the per-crate design doc once `/design` (narrow to `cranelisp-backend`) authors `design/backend/{backend}.md` (M2 deliverable):

- **Lifecycle of `Arc<Jit>`** — Decision 31 Sc.1 + Sc.2 specifies per-eval and per-redefinition reclaim; how does the consumer (the binary `int` surface) participate in keeping the Arc alive across REPL evaluations? Is the trampoline a co-owner?
- **Stability of `*const u8`** — pointers into the JIT memory are valid for as long as the `Arc<Jit>` is alive. What's the contract for "I'm done with these pointers"? Is there a separate handle type that releases the slot back to GOT reclaim?
- **Failure mode** — does `compile_to_module` return `Result<(Arc<Jit>, HashMap), CompileError>`? Today's signature in code may not reflect this.
- **Multi-module batches** — Decision 31 says "one JITModule per compile batch"; what's the consumer's view when a batch contains 5 modules? One Arc, five name maps? One name map keyed by `FQSymbol`?

## Proposed resolution

When `/design` (narrow to `cranelisp-backend`) authors `design/backend/{backend}.md` in M2 (S64–S65), include a "compile_to_module contract" section answering the four questions above. The facade spec's signature may need refinement based on the answers — file a return FIXME `target: /arch` if the signature changes.

## Context

Surfaced during S63 W2 facade-spec authoring. Decision 35 introduced the current return shape; Decision 31 governs Arc lifecycle. The facade spec captures the *as-designed* surface but the design doc owns the *why* and *invariants*.
