# Sprint 117 — failed batch-member attribution

## 1. Scope

Sprint 117 W3a needs a backend codegen failure to name the exact member of a
multi-name `compile_to_module` request whose body failed. This is an
observability correction inside `cranelisp-backend`; it does not change
codegen, transaction ownership, or publication.

The current loss occurs at the public boundary:

1. `compile_module_bodies` iterates explicit `(defn, body, summary)` triples.
2. `compile_defn_in_module` returns a located `CranelispError`.
3. The loop propagates that error without attaching the current `defn`.
4. `compile_to_module` converts the batch-level error with
   `CompilationError::from`, whose fallback identity is empty module + empty
   symbol.

The loop already has the authoritative identity. Reconstructing it later from
the cause string, a callee, or iteration state would create a second resolver.
The correction therefore consumes `module_path` and `defn.name` exactly where
the per-body call fails (Principle 24 — Resolve once).

## 2. Actors and functions

| Actor | Function | Contract |
|---|---|---|
| Binary/int | `compile_to_module(module_path, names, ...)` | Supplies the batch and owns the surrounding transaction. |
| Backend batch driver | `compile_module_bodies` | Iterates the already-collected definitions in batch order; at each call it knows the exact module and definition name. |
| Backend body compiler | `compile_defn_in_module` | Returns the original codegen cause and `ErrorLocation`; it does not own batch attribution. |
| Backend public boundary | `compile_to_module` | Returns the existing `CompilationError`; it does not parse a cause to discover identity. |

No new actor, callback, or cross-crate carrier is needed (Principles 2 and 21
— Narrow interfaces; Actors and functions before mechanism).

## 3. Minimal private error lift

### 3.1 Error channel

Change the private `compile_to_module_impl` result error from
`CranelispError` to the already-public `CompilationError`. Rust's existing
`From<CranelispError> for CompilationError` keeps every non-member-specific
`?` conversion exactly as it behaves today. The public
`compile_to_module` signature and enum are unchanged; its final
`.map_err(CompilationError::from)` becomes unnecessary.

Change private `compile_module_bodies` to return
`Result<(String, usize), CompilationError>`. Only the
`compile_defn_in_module` call gets the narrower conversion below. Errors from
target collection, declaration, drop-glue preparation, GOT-data emission, and
finalisation continue through the existing generic
`From<CranelispError>` mapping. In particular, this sprint does not attempt to
reclassify the existing generic `ModuleError` collapse.

### 3.2 Attribution helper

Add one private helper beside the compilation-loop helpers, conceptually:

```rust
fn attribute_body_codegen_error(
    module_path: &ModuleFullPath,
    defn: &Defn,
    error: CranelispError,
) -> CompilationError
```

Its implementation first applies the existing
`CompilationError::from(error)`, then replaces only the
`CodegenFailed.module` and `CodegenFailed.symbol` fields with
`module_path.clone()` and `defn.name.clone()`. The existing conversion remains
the single source for `cause` and `location`; the helper must not format and
reparse either field.

At the exact source seam:

```text
compile_module_bodies
  for current defn
    compile_defn_in_module(...)
      .map_err(|error| {
          attribute_body_codegen_error(module_path, defn, error)
      })?
```

This is deliberately not:

- attribution from the failing AST's callee or punctuation;
- a `last_name` side channel outside the iterator;
- a scan of `names` or symbol tables;
- message parsing in backend or Binary;
- a new `CompilationError` variant or shared carrier.

The explicit loop variable is the settled batch identity and is independent
of incidental collection order (Principles 7 and 24 — Single source of truth;
Resolve once).

## 4. Source seams

All implementation seams are private in
`crates/cranelisp-backend/src/lib.rs`:

1. `compile_to_module` — return the private implementation result directly;
   no signature change.
2. `compile_to_module_impl` — return `CompilationError`; existing `?`
   expressions retain their current conversion through the existing `From`.
3. `compile_module_bodies` — return `CompilationError`.
4. The `compile_defn_in_module(...)` call inside the definition loop — attach
   current `module_path` + `defn.name` while preserving the converted cause
   and location.
5. A small private `attribute_body_codegen_error` helper near the loop.

`crates/cranelisp-backend/src/error.rs` needs documentation cleanup only if
the implementer chooses to remove the now-obsolete “best-effort/follow-up”
wording. The enum, its fields, `Display`, and both conversion impls remain
unchanged.

No change is permitted to:

- `compile_to_module`'s public signature;
- `CompilationError`'s public variants or fields;
- `cranelisp-types`;
- cache schema or serialized metadata;
- `CodeFinalizer`, `CompilationArtifacts`, or public API baselines.

The structural witness is a zero diff in
`crates/cranelisp-backend/public-api.txt` (Principle 18 — Enforce
architectural invariants structurally).

## 5. Unit scenarios

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

## 6. Atomicity and GOT non-impact

The change does not move any phase. `compile_module_bodies` still completes
before:

1. `emit_module_got_data`;
2. `finalize_for_code_read`;
3. `write_finalized_got_slots`.

A later-member body failure may leave declarations or a definition inside the
caller-owned, unpublished Cranelift module, but it cannot publish a function
pointer to the live GOT. Binary/int owns disposal of that prepared module and
the wider symbol-table transaction, as specified in
`design/int/s117-conformance-recovery.md`. Backend does not gain rollback,
retention, or transaction responsibilities.

Consequently there is no change to atomicity, GOT layout, GOT write timing,
ABI-preserving redefinition policy, or code retention. The diagnostic carrier
is orthogonal to publication.

## 7. Quality attributes

- **Simplicity:** one private helper and one private error-channel lift; no
  new abstraction or variant (Principle 6 — Complexity has a budget).
- **Maintainability:** only the per-body loop can attach a per-body identity;
  future body compilers pass through the same chokepoint.
- **Observability:** exact unit identity and the original location survive as
  structured data.
- **Concurrency-safety:** unchanged; all values are call-local and immutable.
- **Performance:** failure-path-only field replacement; success CLIF and
  machine code are byte-identical.
- **Testability:** production batch entry and a multi-member fixture expose
  the defect without a new public hook.

## Next skills

- `/dev` — narrow to `cranelisp-backend`; implement the five private source
  seams and unit scenarios above.
- `/review` — narrow to `cranelisp-backend`; verify exact identity/location
  preservation, unchanged generic mappings, zero public API drift, and no
  phase/GOT movement.
- `/sprint` — continue W3a after backend review; Binary remains the
  transaction owner.
