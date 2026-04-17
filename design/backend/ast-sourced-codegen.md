# AST-Sourced Codegen (Sprint 55, Steps 1c + 1d)

Design for switching the backend to read AST bodies, resolved calls, and expression types from `ModuleEntry` and AST nodes instead of `CheckResult` side maps. This eliminates `CheckResult` as a boundary type between typecheck and backend.

**Status**: Design document (Sprint 55, Wave 1).

**References**:
- `design/backend/compile-to-module.md` Section 10 (CodegenInput simplification, Option A) -- prior analysis establishing that `CodegenInput` wraps `CheckResult + Program` and should be eliminated
- `design/arch/pipeline-v4.md` Section 9.1 (target data model: symbol table as single store)
- `design/arch/pipeline-v4.md` Section 9.3 (target `compile_to_module` signature: `(path, names, symbol_tables, module)`)
- `design/arch/pipeline-v4-roadmap.md` Phase 1 (step descriptions and exit criteria)

## 1. Problem Statement

The backend currently reads typecheck outputs from two separate sources that are passed alongside each other:

1. **`program: &Program` (Vec\<TopLevel\>)** -- AST bodies (the function definitions to compile).
2. **`typecheck: &CheckResult`** -- side maps keyed by `Span`:
   - `method_resolutions: HashMap<Span, ResolvedCall>` -- how each call site was resolved
   - `expr_types: HashMap<Span, Type>` -- inferred type of expressions (for heap classification, RC, match codegen)
   - `mono_defns: Vec<MonoDefn>` -- monomorphised specializations with per-specialization resolutions
   - `default_method_defns: Vec<Defn>` -- default trait method implementations
   - `constrained_fn_names: HashSet<Symbol>` -- template functions to skip (only their mono variants compile)

This creates a fragile coupling: the program and the side maps must be kept in sync (they're keyed by `Span`, which must match between the AST in `program` and the maps in `CheckResult`). The `CodegenInput` struct in `session_v4.rs` bundles these together for stashing between typecheck and codegen workers, adding an intermediate type that duplicates `CheckResult` fields.

After Steps 1a and 1b (owned by `/typecheck`), the AST bodies and their annotations live directly on `ModuleEntry::Def` and `Expr` nodes:
- `ModuleEntry::Def.ast: Option<Defn>` -- the typechecked function body
- `Expr::Apply` gains `resolved_call: Option<Box<ResolvedCall>>` -- how this call was resolved
- Every `Expr` variant gains `inferred_type: Option<Box<Type>>` -- the inferred type of this expression

Types and resolved calls are on the AST nodes themselves — no `HashMap<Span, _>` side maps. The backend reads directly from the nodes it is compiling, eliminating both `CheckResult` as a boundary type and Span as a lookup key.

### Prior analysis

`design/backend/compile-to-module.md` Section 10 analyzed `CodegenInput` simplification and recommended **Option A**: a slim `CodegenInput { check: CheckResult, program: Program }` as an interim step. This sprint goes further -- the target is to eliminate both `CodegenInput` AND `CheckResult` as boundary types, because the data they carry now lives on the symbol table entries (the v4 target data model).

## 2. Step 1c: Backend Reads from AST Nodes

### 2.1 What changes in CompileContext

`CompileContext` currently holds two references sourced from `CheckResult`:

```rust
pub struct CompileContext<'a> {
    pub method_resolutions: &'a HashMap<Span, ResolvedCall>,
    pub expr_types: &'a HashMap<Span, Type>,
    // ... other fields unchanged ...
}
```

After Step 1b, the same data is available directly on AST nodes:
- **Old**: `CheckResult.method_resolutions` and `CheckResult.expr_types` (Span-keyed side maps)
- **New**: `Expr::Apply.resolved_call` and `Expr.inferred_type` (per-node)

Step 1c switches the backend to read from AST nodes. This is a deeper change than simply re-pointing references — the access pattern changes from map lookup to node field access:

```rust
// Current (side-map lookup by Span):
let ty = self.ctx.expr_types.get(&expr.span()).cloned();

// Target (read from node):
let ty = expr.inferred_type().cloned();
```

The `method_resolutions` and `expr_types` fields on `CompileContext` are **deleted** (not re-pointed). Every site that currently does `self.ctx.expr_types.get(&span)` or `self.ctx.method_resolutions.get(&span)` changes to read from the `Expr` node being compiled. This eliminates Span as a lookup key entirely.

**Impact on expression compilers**: Each expression compiler method (`compile_apply`, `compile_let`, `compile_match`, etc.) already has the `Expr` node in scope — it's the argument they're dispatching on. Reading `.inferred_type()` or `.resolved_call` from the node they're already holding is simpler than looking up a side map by span.

### 2.2 resolved_call on Expr::Apply

`Expr::Apply` gains `resolved_call: Option<Box<ResolvedCall>>`. `FnCompiler::compile_apply` reads directly from the node:

```rust
// Current (side-map lookup):
if let Some(resolved) = self.ctx.method_resolutions.get(&span) { ... }

// Target (AST-node read):
// In Expr::Apply { callee, args, span, resolved_call, inferred_type }
if let Some(resolved) = resolved_call.as_deref() { ... }
```

All call sites that currently look up `method_resolutions.get(&span)` switch to reading from the `Apply` node. This includes:
- TCO check for constrained-poly self-recursion (`apply.rs`)
- Trace codegen resolution lookup (`trace_codegen.rs`)
- Closure codegen (`closure_codegen.rs`)

Each of these already has the `Expr::Apply` node in scope at the lookup site.

### 2.3 inferred_type on Expr Nodes

Every `Expr` variant gains `inferred_type: Option<Box<Type>>`. The backend reads types directly from the expression node being compiled:

```rust
// Current (side-map lookup):
let ty = self.ctx.expr_types.get(&expr.span());

// Target (node read):
let ty = expr.inferred_type();
```

For heap classification (RC emission), the `HeapCategory` analysis currently uses `expr_types.get(&span)`. After Step 1c, it reads from the `Expr` node directly. Since heap classification walks the AST recursively, each node is already in scope.

For mono specializations, each mono `Defn`'s AST nodes carry their own `inferred_type` values (populated by typecheck during monomorphisation). No merge logic needed — the types are already on the nodes.

### 2.4 How compile_to_module changes (Step 1c)

The compilation loop in `compile_to_module` currently builds `CompileContext` with references into `CheckResult`:

```rust
let compile_ctx = CompileContext {
    method_resolutions: &typecheck.method_resolutions,
    expr_types: &typecheck.expr_types,
    // ...
};
```

After Step 1c, `method_resolutions` and `expr_types` are **removed from `CompileContext`**. The compiler reads directly from AST nodes during compilation. No per-defn context setup needed for type/resolution data.

For mono specializations, the current `merged` clone (O(n) in module-wide resolutions) is eliminated — each mono defn's AST nodes carry their own types and resolutions.

### 2.5 What happens to CompilationEnv

`CompilationEnv` is **unchanged**. It resolves GOT entries and function arities -- concerns orthogonal to where type/resolution data comes from. The `ObjectCompilationEnv` (introduced in `compile-to-module.md` Section 12) reads GOT slots from `symbol_tables`, which is unaffected by the AST annotation changes.

### 2.6 Dual-write verification in Step 1c

During Step 1c, both sources are available (Step 1b's dual-write is still active). Before switching each read site, add debug assertions that the old and new sources agree:

```rust
debug_assert_eq!(
    expr.inferred_type().as_deref(),
    self.ctx.expr_types.get(&expr.span()),
    "inferred_type disagree for span {:?}", expr.span()
);
```

Once all assertions pass across the full test suite, remove `method_resolutions` and `expr_types` from `CompileContext` and delete the old source references.

## 3. Step 1d: New compile_to_module Signature

### 3.1 Current signature

```rust
pub fn compile_to_module<M: Module>(
    module_path: ModuleFullPath,
    program: &Program,
    typecheck: &CheckResult,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError>
```

### 3.2 Target signature (this sprint)

```rust
pub fn compile_to_module<M: Module>(
    module_path: ModuleFullPath,
    program: &Program,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError>
```

The `typecheck: &CheckResult` parameter is removed. The function reads everything it needs from the defn bodies in `program` (which carry `method_resolutions`, `expr_types`, and `resolved_call` on their AST nodes).

**Note**: This is an intermediate target. The pipeline-v4.md Section 9.3 ultimate target replaces `program: &Program` with `names: &[Symbol]` (reading bodies from `symbol_tables`). That is Phase 2 work (Step 2a). This sprint removes `CheckResult` only; `program` stays.

### 3.3 What moves out of CheckResult

| CheckResult field | Where it goes | How backend finds it |
|---|---|---|
| `method_resolutions` | `Expr::Apply.resolved_call` | Read from each Apply node during compilation |
| `expr_types` | `Expr.inferred_type` | Read from each Expr node during compilation |
| `mono_defns` | `program` (as additional `TopLevel::Defn` entries) OR separate `ModuleEntry::Def` entries on the symbol table | See Section 3.4 |
| `default_method_defns` | `program` (as additional `TopLevel::Defn` entries) OR separate `ModuleEntry::Def` entries on the symbol table | See Section 3.4 |
| `constrained_fn_names` | Derived from `Defn` metadata (e.g., a `constrained: bool` flag) OR from `ModuleEntry::Def.kind` | See Section 3.4 |
| `warnings` | Remains on typecheck-internal `CheckResult` (not a codegen concern) | N/A |
| `display` | Remains on typecheck-internal `CheckResult` (not a codegen concern) | N/A |

### 3.4 Extra defns: mono_defns and default_method_defns

This is the key dependency identified in the `/arch` review (Section 5: Hidden Dependencies).

Currently, `compile_to_module` receives these as separate vectors on `CheckResult` and compiles them alongside the regular program. After `CheckResult` elimination, they must come from somewhere.

**Two options** (per `/arch` review):

**(A) Inline into program (minimal change)**: Typecheck appends mono defns and default method defns to the `program: Vec<TopLevel>` before handing it to codegen. Each mono defn becomes a regular `TopLevel::Defn` whose AST nodes carry `inferred_type` and `resolved_call` (no Defn-level maps). The `constrained_fn_names` filter becomes a `constrained: bool` field on `Defn` (or a `DefKind` check in the symbol table).

**(B) Separate ModuleEntry::Def entries on symbol table (target)**: Per pipeline-v4.md Section 9.1, mono specializations and default method implementations are separate `ModuleEntry::Def` entries with their own `ast` fields. This is the Phase 2 approach (when `compile_to_module` takes `names: &[Symbol]`).

**Decision for this sprint**: Option (A). The `program` parameter still exists in this sprint's signature, so appending extra defns to it is natural and avoids a Phase 2 dependency. Typecheck builds the full defn list (regular + mono + defaults) and puts them all in `program`. The backend's defn collection loop (Step 1 in `compile_to_module`) processes them uniformly.

Concretely:
- `mono_defns` are appended to `program` as `TopLevel::Defn(mono.defn)`. Each mono defn's AST nodes carry their own `inferred_type` and `resolved_call` fields (populated by typecheck during monomorphisation). No Defn-level maps.
- `default_method_defns` are appended to `program` as `TopLevel::Defn(defn)`. Each default method defn's AST nodes carry their own `inferred_type` and `resolved_call` fields. No Defn-level maps.
- `constrained_fn_names`: the defn collection loop identifies constrained templates by checking `ModuleEntry::Def.kind` in the symbol table (which already distinguishes `UserFn { constrained_fn: Some(_) }` from regular `UserFn`). No separate `HashSet` needed.

### 3.5 Trait impl methods: symbol table entries, not TopLevel traversal

After the data model change, trait impl methods follow the same pattern as mono specializations, default method defns, and multi-sig variants: each method is a first-class `ModuleEntry::Def` on the symbol table under its mangled name (e.g., `Display.show$Option$Int`), with `ast: Some(annotated_defn)` carrying concrete types and resolved calls on its AST nodes.

**How the backend finds them**: The same way it finds any regular defn — by name in the symbol table. There is no special trait-impl iteration path. When `compile_to_module` processes defns (either from `program` entries or from the symbol table's name list in Phase 2), mangled trait method defns appear alongside regular defns and mono specializations.

**Why `TopLevel::TraitImpl` is skipped**: The `TopLevel::TraitImpl` form in the program is a structural declaration — it records which trait is implemented for which type. The compilable method bodies are already extracted by typecheck and placed on the symbol table as separate `ModuleEntry::Def` entries. The `compile_to_module` defn collection loop skips `TopLevel::TraitImpl` because there is nothing to compile from the structural form; the methods are compiled individually by their mangled names.

**Consistency with other mangled defns**: This is the established pattern:
- **Mono specializations** (`add$Int+Int`): separate `ModuleEntry::Def` entries by mangled name.
- **Default method defns** (`Num.negate$Int`): separate `ModuleEntry::Def` entries by mangled name.
- **Multi-sig variants** (`map$Vec+Fn`, `map$List+Fn`): separate `ModuleEntry::Def` entries by mangled name.
- **Trait impl methods** (`Display.show$Option$Int`): same — separate `ModuleEntry::Def` entries by mangled name.

All are compiled uniformly by the defn collection loop. No special-case handling per category.

**Cross-module resolution**: For the `compile_to_module` object codegen path, cross-module references to trait impl methods resolve through the symbol table the same way as any other cross-module function reference — via GOT slot lookup in `ObjectCompilationEnv`. The mangled name is the key; the origin (trait impl vs regular defn) is irrelevant to the backend.

### 3.6 What happens to CodegenInput

`CodegenInput` in `session_v4.rs` is **deleted**. Its fields were:

```rust
pub struct CodegenInput {
    pub method_resolutions: MethodResolutions,     // now on Expr nodes
    pub expr_types: HashMap<Span, Type>,           // now on Expr nodes
    pub mono_defns: Vec<MonoDefn>,                 // now in program
    pub default_method_defns: Vec<Defn>,           // now in program
    pub program: Vec<TopLevel>,                    // passed directly
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,  // already eliminated
}
```

The `/int` skill deletes:
- `CodegenInput` struct definition
- `SharedState.codegen_inputs: DashMap<ModuleFullPath, CodegenInput>`
- `stash_codegen_input()` calls in `worker.rs`
- All code that constructs `CodegenInput` from `CheckResult`

### 3.7 What happens to CheckResult

`CheckResult` is **not deleted** -- it becomes a typecheck-internal type. After Step 1d, it carries only:
- `warnings: Vec<Warning>` -- consumed immediately by the integration layer
- `display: Option<DisplayInfo>` -- used by REPL for output formatting

The fields removed from `CheckResult`:
- `method_resolutions` -- moved to `Expr::Apply.resolved_call`
- `expr_types` -- moved to `Expr.inferred_type`
- `mono_defns` -- inlined into `program`
- `default_method_defns` -- inlined into `program`
- `constrained_fn_names` -- derived from symbol table

Per `/arch` review, `/typecheck` should consider renaming to `CheckOutput` since it stops being a boundary type.

## 4. Object Codegen (Nice Workers)

Nice workers currently take `CodegenInput` from a `DashMap`, extract the `CheckResult` fields, and pass them to `compile_to_module`. After Step 1d:

1. Nice worker takes the `program: Program` (stashed by the typecheck worker after form processing).
2. Calls `compile_to_module(module_path, &program, &symbol_tables, &mut obj_module)`.
3. `compile_to_module` reads `resolved_call` and `inferred_type` from AST nodes in each defn.

The `ObjectCompilationEnv` is unchanged -- it still resolves GOT slots from `symbol_tables`. The GOT data symbol setup (`declare_got_data_symbols`, `define_got_data`) remains ObjectModule-specific pre-work done by the nice worker before calling `compile_to_module`, exactly as `compile-to-module.md` Section 5 specifies.

## 5. Backward Compatibility and Incremental Transition

The transition can be done incrementally within this sprint because Steps 1a and 1b establish a dual-write period:

1. **Step 1c starts**: Both sources available. Add debug assertions comparing old (side-map) and new (AST node) sources. Switch each read site from `ctx.expr_types.get(&span)` / `ctx.method_resolutions.get(&span)` to `expr.inferred_type()` / `apply.resolved_call`. Run tests. Assertions validate correctness.
2. **Step 1c completes**: All backend reads come from AST node fields. `method_resolutions` and `expr_types` are deleted from `CompileContext`. `CheckResult` fields are no longer read by the backend. Tests pass.
3. **Step 1d starts**: Remove `CheckResult` parameter from `compile_to_module`. Update all callers (3 call sites: priority worker JIT, nice worker object, REPL eval). Delete `CodegenInput`. Tests pass.

Each sub-step leaves the test suite green. No flag day.

### Call site inventory for Step 1d

The `compile_to_module` function is called from:
1. `src/worker.rs` -- `codegen_module_symbols()` (JIT batch path)
2. `src/worker.rs` -- nice worker object compilation path
3. `src/session_v4.rs` -- `compile_and_execute_expr()` (REPL eval path)

All three currently pass `&check` (a `CheckResult`). In Step 1d, all three drop that parameter.

## 6. Sketch Comparison

The sketch (`sketch/src/codegen.rs`) uses the same side-map pattern: `FnCompiler` receives `method_resolutions: &MethodResolutions` and `expr_types: &HashMap<Span, Type>` as constructor parameters (lines 135, 149). These maps are passed through from the top-level compilation functions (`compile_program`, `compile_defn_jit`, `compile_module_to_object` -- lines 1701-1912) which receive them from `CheckResult`.

The sketch does not annotate AST nodes with type information. Resolved calls and expression types are always in side maps, keyed by `Span`. This works in the sketch because:
- There is no concurrent pipeline (no need to co-locate data for cache serialization).
- The `CheckResult` is always immediately available alongside the program.

The reimplementation diverges from the sketch by moving this data onto the AST. The rationale:
- **Cache serialization**: when the symbol table is the single store (v4 target), AST bodies must carry their own type annotations -- there is no separate `CheckResult` to serialize alongside.
- **Concurrent codegen**: workers reading from self-contained defns is simpler than workers reading from shared side maps that must be kept in sync.
- **Elimination of Span-keyed coupling**: the side-map pattern requires Span identity between the AST and the maps, which is fragile across clone/transform operations.

The access pattern inside `FnCompiler` changes from the sketch's side-map lookup (`self.ctx.method_resolutions.get(&span)`, `self.ctx.expr_types.get(&span)`) to direct node field reads (`expr.inferred_type()`, `apply.resolved_call`). This is a deeper change than the sketch — both the data source and the access pattern change. The `method_resolutions` and `expr_types` fields are deleted from `CompileContext` entirely.

## 7. Risk Assessment

### Low risk

- **CompilationEnv unchanged**: GOT resolution is orthogonal to type annotation sourcing.
- **Intrinsic declaration unchanged**: `declare_intrinsics_generic` does not touch `CheckResult`.

### Medium risk

- **Access pattern change**: Every expression compiler method changes from side-map lookup (`self.ctx.expr_types.get(&span)`, `self.ctx.method_resolutions.get(&span)`) to node field read (`expr.inferred_type()`, `apply.resolved_call`). This touches every codegen file that reads types or resolved calls. The dual-write assertions in Step 1c mitigate this — each read site is validated before the old source is removed.
- **CompileContext field deletion**: `method_resolutions` and `expr_types` are deleted from `CompileContext`, not re-pointed. All downstream code (`FnCompiler`, expression compilers) must be updated. Any missed site will fail to compile (field no longer exists), so this is caught at build time.
- **mono_defns merge semantics**: Currently, mono specializations merge their per-specialization resolutions with the global `method_resolutions` map. After Step 1c, each mono defn's AST nodes carry their own `resolved_call` and `inferred_type` fields (populated during monomorphisation). If typecheck's dual-write doesn't produce identical annotations, assertions will catch it in Step 1c.
- **constrained_fn_names derivation**: The defn collection loop currently uses `typecheck.constrained_fn_names.contains(&defn.name)` to skip template definitions. After Step 1d, this must be derived from `ModuleEntry::Def.kind` in the symbol table. If the symbol table lookup fails (defn not registered), the template would be compiled and produce incorrect code. Mitigation: the symbol table is populated before codegen starts (invariant from form-by-form processing).

### Higher risk

- **Step 1d hidden dependency**: If `/typecheck` does not inline mono defns and default method defns into the program (Section 3.4, Option A), Step 1d cannot proceed. This is the dependency identified in the `/arch` review. Mitigation: Step 1c can complete independently; Step 1d waits for `/typecheck` to confirm the approach.
- **REPL eval path**: The REPL wraps expressions in synthetic defns. These synthetic defns' AST nodes must carry `inferred_type` and `resolved_call` after Step 1b. If the REPL path doesn't populate these node fields, codegen will have no type or resolution data and produce incorrect code (no trait dispatch, no heap classification). Mitigation: the dual-write assertions in Step 1c will catch this -- if the node fields disagree with the old `CheckResult` side maps, the assertion fires.

## 8. Acceptance Criteria

**Step 1c**:
- All backend code reads resolved calls and expression types from AST node fields (`resolved_call` on Apply, `inferred_type` on Expr), not from `CheckResult` side maps.
- Debug assertions confirm old and new sources agree across the full test suite.
- All 1595 passing tests continue to pass. 9 deferred tests unchanged.

**Step 1d**:
- `compile_to_module` signature drops `typecheck: &CheckResult` parameter.
- `CodegenInput` type deleted from `session_v4.rs`.
- `codegen_inputs` DashMap deleted from `SharedState`.
- All callers updated to new signature.
- All 1595 passing tests continue to pass. 9 deferred tests unchanged.
