> **HISTORICAL — sprint-scoped working doc (macro-deps step assessment).** A completed assessment, retained for the audit trail; NOT a durable subsystem reference. The durable design lives in `typecheck.md`. Verify any detail here against current source before relying on it. (Triaged S109, FIXME 0578.)

# Step 4 Macro Dependencies: Typecheck Assessment

Sprint 42, Wave 1 assessment for `/typecheck`. Revised to incorporate Decision 21 (TC-sourced call graph).

## 1. Call-Graph Edge Population (Decision 21)

### Current State

`FormCheckResult` and `ModuleCheckAccumulator` both have a `call_graph_edges` field. The plumbing through `merge_form_result` exists. However, the field is **never populated** — every construction site returns `Vec::new()`.

The infrastructure skeleton exists; the population logic does not.

### Decision 21 Approach

Decision 21 replaces the previously proposed `collect_call_graph` on-demand AST walk with a simpler approach: populate `call_graph_edges` as a side effect of Pass 2 body checking, accumulate in `ModuleCheckAccumulator`, and write to `ModuleEntry.callees` during `finalize_check_result()`.

This is preferred because:
- The typechecker already resolves all calls during Pass 2 — the information is available at zero additional cost.
- No separate AST walk or on-demand traversal is needed.
- The edges are written to `ModuleEntry` (persistent, serializable), making them available for cross-module queries without re-typechecking.
- The scheduler reads callees from the symbol table via `tc.symbol_table(module).get(name).callees` — the same path used for type resolution.

### Type Changes

The `call_graph_edges` type changes from `Vec<(Symbol, Symbol)>` to `Vec<(Symbol, FQSymbol)>`:

- **Caller** is a local `Symbol` (always in the current module during Pass 2).
- **Callee** is an `FQSymbol { module: ModuleFullPath, symbol: Symbol }` — fully qualified, because the callee may be in a different module.

This change must be applied in:
1. `FormCheckResult.call_graph_edges: Vec<(Symbol, FQSymbol)>`
2. `ModuleCheckAccumulator.call_graph_edges: Vec<(Symbol, FQSymbol)>`

The `interfaces.md` design book already specifies this type. The implementation in `program.rs` still uses the old `Vec<(Symbol, Symbol)>` and must be updated.

### Where Edges Are Extracted: `ResolvedCall` Variants

During `check_form(CheckBody)`, when inferring a function body, the typechecker resolves each call site and records the resolution in `method_resolutions: HashMap<Span, ResolvedCall>`. The same resolutions are the source of call graph edges.

For each `ResolvedCall` in the form's method resolutions, derive the callee `FQSymbol` as follows:

| `ResolvedCall` variant | Produces edge? | Callee derivation |
|---|---|---|
| `TraitMethod { trait_name, method_name, impl_type, mangled_name }` | **Yes** | The callee is the *impl method* — the mangled name (e.g., `Num.+$Int`) in the module that defines the impl. The module is looked up from the trait impl registry: the typechecker knows which module provides the impl for `(trait_name, impl_type)`. For Step 4 (single-module), this is the current module. For Step 5, it may be a different module (e.g., `core.numerics`). The `FQSymbol` is `{ module: impl_module, symbol: mangled_name.into() }`. |
| `SigDispatch { mangled_name }` | **Yes** | The callee is the dispatch target variant. The mangled name (e.g., `foo$Int+Bool`) is in the current module (multi-sig variants are always local). `FQSymbol { module: current_module, symbol: mangled_name.into() }`. |
| `AutoCurry { target_name, trait_resolution, .. }` | **Yes** | The callee is the curry target function. If `trait_resolution` is `Some(inner)`, derive the edge from the inner `ResolvedCall` (recursively). Otherwise, look up `target_name` in the module's symbol table to determine its module. `FQSymbol { module: target_module, symbol: target_name }`. |
| `BuiltinFn { name }` | **No** | Builtins are always available — they have no codegen dependency. Skip. |

**Additionally**, direct function calls that do *not* go through method resolution (i.e., calls to plain user-defined functions that resolve as `Expr::Var` to a known `Def` entry) also produce edges. These are not in `method_resolutions` because they require no special dispatch. For these calls, the edge is `(caller, FQSymbol { module, symbol })` where the module and symbol come from name resolution (the `lookup_via_modules` path that resolves qualified and bare names to their defining module).

### Population Site

The edges should be collected during `check_defn_body` (or the equivalent Pass 2 body-checking code path). The natural integration point is where `method_resolutions` entries are recorded — each `insert` into the method resolutions map is an opportunity to also emit a call graph edge.

For direct (non-dispatched) calls, the integration point is `infer_apply` (or `infer_expr` for `Expr::Var` in call position) — wherever the callee is resolved to a known user-defined symbol.

The caller symbol is the defn whose body is being checked — this is known from the `check_form(CheckBody)` invocation context and can be threaded through the inference calls (it is already implicitly available as the "current defn" during body checking).

### `finalize_check_result` Changes

After all forms have been checked and `merge_form_result` has accumulated all edges, `finalize_check_result()` must:

1. **Group edges by caller**: Build a `HashMap<Symbol, Vec<FQSymbol>>` from `accumulator.call_graph_edges`.
2. **Deduplicate**: Each caller's callee list should be deduplicated (a function may call the same callee at multiple call sites).
3. **Write to `ModuleEntry`**: For each caller symbol in the grouped map, look up the corresponding entry in `self.current_symbol_table_mut().symbols` and write the callee list:
   - `ModuleEntry::Def { callees, .. }` — set `callees` to the grouped `Vec<FQSymbol>`.
   - `ModuleEntry::Macro { callees, .. }` — set `callees` to the grouped `Vec<FQSymbol>`.
   - Other variants — ignore (constructors, imports, type defs don't have callees).

This write happens after the post-passes (monomorphisation, overload resolution, auto-curry) so that edges from synthesized mono defns are also captured. Note: post-pass resolutions are swept into the accumulator's `method_resolutions` but not into `call_graph_edges`. If mono defns or multi-sig defns need their own callee lists, their edges should also be emitted during the post-passes. For Step 4 (single-module macros), this is not critical — macro clause defns are ordinary defns and their edges are captured in Pass 2.

### ModuleEntry Changes Required

`ModuleEntry::Def` and `ModuleEntry::Macro` each need a `callees: Vec<FQSymbol>` field. This field:
- Defaults to `Vec::new()` (for entries created before `finalize_check_result`, and for entries that have no body — primitives, constructors, imports).
- Is populated by `finalize_check_result()`.
- Is serialized/deserialized (for module caching).
- Is queryable via `tc.symbol_table(module).get(name)` — the scheduler reads it to discover macro dependencies.

### Transitive Walk (S-3)

The `/typecheck` side of this work is limited to populating the per-symbol `callees` field. The **transitive closure walk** — starting from a macro's callees, recursively following each callee's own callees to discover all uncompiled dependencies — is a consumer concern belonging to `/int` or a shared utility on `SymbolTable`. The typechecker provides the data; the scheduler uses it.

This aligns with S-3 from the architecture review: "Extract the transitive callee walk as a utility on `SymbolTable` so both the worker and future incremental recompilation can reuse it."

## 2. `check_form(CheckBody)` for Macro Clause Defns

### Question

Does `check_form(CheckBody)` work correctly for a synthetic defn derived from a macro clause body, when called outside the normal Pass 2 sequence?

### Analysis

`check_form_body_single_defn` requires that the defn's name exists in `accumulator.defn_type_vars` (populated during Pass 1). It then calls `check_defn_body` which:

1. Pushes a scope frame with the defn's parameters.
2. Infers the body expression type.
3. Unifies with the declared return type.
4. Resolves deferred trait calls.
5. Detects constraints and returns.

**For a macro clause defn specifically**: the synthesized defn has a known signature — it takes `(SList Sexp)` and returns `Sexp`. Both `SList` and `Sexp` are types from the synthetic `macros` module. As long as:

- The `macros` module types are registered (they should be — they are compiler-seeded).
- The defn's signature was registered in Pass 1 (i.e., the `defmacro` was encountered and the clause defn was registered).
- `accumulator.defn_type_vars` contains the clause defn's entry.

...then `check_form(CheckBody)` will work correctly.

### Complication: on-demand typechecking of a macro body

The sprint plan (Scope A, step 2a) says: "When a macro call is encountered in Pass 2 and the function pointer doesn't exist, typecheck the macro body (if not already done)."

This means `check_form(CheckBody)` for the macro clause defn may be called *during* another defn's Pass 2 processing — not in the normal sequential Pass 2 flow. This is fine because:

- `check_form(CheckBody)` is stateless with respect to ordering. It reads `accumulator.defn_type_vars` (populated in Pass 1) and the TypeChecker's scope/substitution state.
- The TypeChecker's substitution state is module-global. Checking the macro body may add new substitutions, but these won't conflict with the calling defn's inference because the macro clause defn has its own fresh type variables (allocated during Pass 1 registration).
- The snapshot/extraction logic (saving `mr_before`/`et_before` and computing deltas) works correctly regardless of call order.

**Requirement**: The macro clause defn must have been registered in Pass 1 before its body can be checked. The sprint plan handles this: Pass 1 registers all forms including `defmacro`, which registers each clause's synthesized defn. When Pass 2 encounters a macro call, the clause defn's signature is already in `accumulator.defn_type_vars`.

### Checking a defn registered in Pass 1 but not yet body-checked

This is exactly the normal flow. Pass 1 registers signatures; Pass 2 checks bodies. Checking a body out of source order (skipping ahead to check the macro clause before checking other defns) is safe because:

- Pass 1 has already registered ALL signatures in the module.
- `check_defn_body` only needs the current defn's parameter types and the module's symbol table (for name resolution).
- Other defns' bodies being unchecked does not matter — body checking only needs type signatures, not body-level information.

**Important for call graph**: When a macro clause defn is body-checked out of order, its `call_graph_edges` are still emitted into the `FormCheckResult` and accumulated normally. The `callees` field on its `ModuleEntry::Macro` will be populated during `finalize_check_result()`. However, the *scheduler* needs the callees *before* `finalize_check_result` runs (it needs them during Pass 2 to block for macro codegen). Two options:

- **(a) Read edges from the accumulator directly**: After `check_form(CheckBody)` for the macro clause, the worker reads `call_graph_edges` from the returned `FormCheckResult` to discover dependencies. This is immediate and doesn't require `finalize_check_result`.
- **(b) Write callees eagerly**: Write to `ModuleEntry.callees` immediately after body-checking the macro clause, not waiting for `finalize_check_result`. This duplicates the write but makes the symbol table consistent.

Option (a) is simpler and avoids writing `ModuleEntry` twice. The worker has the `FormCheckResult` in hand and can extract the callee list directly for the blocking request. `finalize_check_result` writes the canonical version later.

**Verdict**: `check_form(CheckBody)` works correctly for macro clause defns called outside normal Pass 2 sequence. No API changes needed. The worker reads edges directly from `FormCheckResult` for immediate scheduling; `finalize_check_result` writes the persistent version.

## 3. Macro Body as a Defn: `check()` vs `check_form()`

### Current Path (compile_single_clause)

In `src/expander.rs`, `compile_single_clause`:

1. Calls `synthesize_macro_clause_defn` to create a synthetic defn Sexp.
2. Expands quasiquotes.
3. Calls `build_program` to get `Vec<TopLevel>`.
4. Calls `tc.check()` with `Additive` strategy — runs the full multi-pass pipeline on a one-element program.
5. Compiles and extracts the function pointer.

### v4 Path (using check_form)

The v4 worker would:

1. During Pass 1, when encountering a `defmacro`: synthesize each clause defn, build AST, and call `check_form(Register)` to register its signature.
2. During Pass 2, when a macro call is encountered and function pointer is missing: call `check_form(CheckBody)` on the clause defn to typecheck its body. Read `call_graph_edges` from the returned `FormCheckResult` to discover dependencies. Block for codegen of uncompiled callees. Then compile the macro clause and proceed with expansion.

### Complications

**a. Synthesized defn registration**: The v4 Pass 1 must handle `defmacro` forms specially. The frontend's `build_program` with `NoOpExpander` will see the `defmacro` sexp and should produce a `TopLevel` representation (probably `TopLevel::Defmacro` or similar). The worker then synthesizes clause defns and registers them. This is a `/frontend` + `/int` concern, not a typecheck concern — `check_form(Register)` on a synthetic `TopLevel::Defn` works as-is.

**b. Module context**: `compile_single_clause` calls `tc.check()` which sets the module context, clears for replace, etc. In v4, the module context is already set by `process_module_forms`. The clause defn is checked in the same module context. No conflict.

**c. `finalize_check_result` timing**: In the old path, `tc.check()` runs the full pipeline including `finalize_check_result` (overload resolution, monomorphisation, etc.) for the one-element clause program. In v4, `finalize_check_result` runs once at the end of the whole module. The macro clause defn's body check results are accumulated into the module's accumulator and finalized with everything else.

This is actually **better** than the old path because:
- The macro clause defn participates in the module's monomorphisation pass (if it calls constrained functions).
- No redundant `finalize_check_result` per clause.

**d. CheckResult for codegen**: The old path gets a `CheckResult` from `tc.check()` and passes it directly to codegen. In v4, the `BlockingJitCodegen` handler needs the per-symbol portion of the `CheckResult` (method resolutions, expr types). These are available in the accumulator after `check_form(CheckBody)` runs. The worker can construct a minimal `CheckResult` from the accumulator's state for the codegen handler.

**Verdict**: Using `check_form` instead of `check()` is straightforward for macro clause defns. The main difference is that `finalize_check_result` is deferred to module completion, which is the correct behavior in v4.

## 4. Cross-Module Concerns (Step 5 Preview)

For Step 5 (multi-module), macro dependencies may span modules. Key concerns:

**a. Cross-module call graph**: The `callees: Vec<FQSymbol>` field already supports cross-module edges. When a macro body calls `core.syntax/sfold`, the callee is `FQSymbol { module: "core.syntax", symbol: "sfold" }`. The scheduler follows this edge by reading `core.syntax`'s symbol table: `tc.symbol_table("core.syntax").get("sfold").callees`. If the called module is not yet at TypecheckDone, the scheduler must block for that module's typecheck first.

**b. Cached modules**: Symbols from cached modules have their `callees` persisted in `.meta.json` (since `Vec<FQSymbol>` is `Serialize`/`Deserialize`). The codegen status indicates they are already compiled — no transitive walk needed for cached dependencies.

**c. Prelude macros**: Many user macros call prelude functions. The prelude is typically cached, so its symbols should already be compiled. The priority queue's duplicate handling (section 4.2 of `concurrent-pipeline.md`) means re-requesting already-compiled symbols is a no-op.

These concerns are noted but do not affect Step 4 design.

## Summary

| Question | Answer |
|----------|--------|
| Call-graph edge population | Decision 21: populate `call_graph_edges` during Pass 2 body checking as a side effect of name/call resolution. No separate `collect_call_graph` method. Edges are `Vec<(Symbol, FQSymbol)>`. |
| `finalize_check_result` changes | Group `call_graph_edges` by caller, deduplicate, write `Vec<FQSymbol>` to `ModuleEntry::Def.callees` and `ModuleEntry::Macro.callees`. |
| Edge extraction from `ResolvedCall` | `TraitMethod` → impl method FQSymbol. `SigDispatch` → mangled variant FQSymbol. `AutoCurry` → target FQSymbol (recurse on inner resolution). `BuiltinFn` → skip. Direct calls also produce edges. |
| `check_form` for macro clause defns | Works correctly. Worker reads edges from `FormCheckResult` for immediate scheduling; `finalize_check_result` writes the persistent version to `ModuleEntry`. |
| Macro body via `check_form` vs `check()` | Straightforward. `check_form(Register)` + `check_form(CheckBody)` replaces `tc.check()`. Better behavior: clause participates in module-level finalization. |
| Transitive walk (S-3) | Not a `/typecheck` concern. TC populates per-symbol `callees`; the transitive walk is a scheduler/utility concern (`/int` or `SymbolTable` utility). |
| Cross-module (Step 5) | `FQSymbol` callees already support it. Cached modules serialize their callees. Scheduler follows cross-module edges via `tc.symbol_table(module).get(name).callees`. |

### Implementation Checklist

1. **Type change**: Update `FormCheckResult.call_graph_edges` and `ModuleCheckAccumulator.call_graph_edges` from `Vec<(Symbol, Symbol)>` to `Vec<(Symbol, FQSymbol)>` in `program.rs`.
2. **`ModuleEntry` change**: Add `callees: Vec<FQSymbol>` to `ModuleEntry::Def` and `ModuleEntry::Macro` in `cranelisp-types/src/module.rs`. Update all construction sites and match arms.
3. **Edge emission**: In the Pass 2 body-checking code path, emit `(caller, FQSymbol)` edges for each resolved call (method resolutions) and direct user-function calls.
4. **`finalize_check_result`**: After post-passes, group accumulated edges by caller, deduplicate, and write to `ModuleEntry.callees` in the symbol table.
5. **No new public API needed**: No `collect_call_graph` method. Edges are a side effect of existing Pass 2 inference.
