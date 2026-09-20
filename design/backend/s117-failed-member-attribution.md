# Failed batch-member attribution

> **Owner**: `design` (backend). **Status**: delivered. Retained for the
> negative design list and for the unit obligations its committed tests cite.
>
> The contract statement is `backend.md` §5; this document carries the parts a
> summary would lose.

## 1. What the attribution must NOT be

The seam is the private body loop, where the current module path and the
definition being compiled are both still in hand. Every rejected alternative
below reconstructs a fact the loop already had — a second resolver for an
identity typecheck and the loop already agree on:

- attribution derived from the failing body's callee, or from punctuation;
- a "last name" side channel threaded outside the iterator;
- a scan of the requested names, or of the symbol tables;
- message parsing, in the backend or in the binary;
- a new error variant, or a shared carrier, to hold the identity.

The existing conversion stays the single source of the cause and the location,
and **the helper must not format and re-parse either field**.

Deliberately out of scope: the generic collapse of *non-body* batch errors is
not reclassified here, and the body helper must not attribute them.

## 2. Atomicity — no new responsibility

A later-member failure may leave declarations, or even a definition, inside the
caller-owned Cranelift module. That module is unpublished, so the failure
**cannot publish a function pointer to the live GOT**. The backend therefore
gains no rollback, retention or transaction responsibility from partial batch
failure; the existing phase order already provides the only atomicity property
that matters.

## 5. Unit scenarios

*(Numbered §5 deliberately: the committed tests cite §5.1 and §5.2 by name.)*

The orchestration tests belong in the existing crate-root
`module_assembly_tests.rs` exception because they exercise the private
`compile_to_module` phase sequence, not an expression-lowering submodule
(Principle 23 — Unit tests mirror module composition).

### 5.1 Required multi-name failure

Build one module containing at least two named definitions in a deterministic
`names = [earlier, later]` request:

- `earlier` compiles successfully;
- `later` reaches `compile_defn_in_module` and fails with a deliberately
  located backend error at a non-synthetic source span.

Assert the returned value is exactly:

```text
CompilationError::CodegenFailed {
    module: requested module_path,
    symbol: later,
    cause: original cause,
    location: original source ErrorLocation,
}
```

The assertion must distinguish the later definition from both the earlier
definition and the callee/name mentioned by the underlying cause. It must
also assert the source file/span, not merely rendered text.

### 5.2 Controls

1. Reverse or otherwise vary the two names while keeping the failing
   definition explicit; attribution follows the failing loop member, never a
   first/last convention.
2. A single-name body failure receives the same exact module/name/location.
3. A non-body batch error (for example target collection or declaration)
   retains the pre-S117 generic conversion and is not spuriously attributed
   by the body helper.
4. The success control still returns the same `CompilationArtifacts`.
5. In JIT mode, record the live GOT values before the failing multi-name call
   and assert they are unchanged after failure.

The failure fixture should use an existing production body-codegen error seam
and production `compile_to_module`; no test-only public hook or alternate
compiler path is warranted (Principle 5 — Testability is structural).
