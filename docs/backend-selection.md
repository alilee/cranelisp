# Backend Selection: Abstracting the Code Generator

## 1. Motivation

Cranelisp currently compiles exclusively through Cranelift. The codegen is already well-contained — seven files totalling ~3,800 lines behind the `Jit` facade — but the abstraction isn't formalized. Cranelift-specific naming leaks through struct names, field names, and REPL commands. Formalizing the backend boundary enables:

- **Alternative backends** — LLVM ORC for optimised code, or a lightweight interpreter for debugging
- **Testing** — a mock backend that records IR without emitting machine code
- **AOT compilation** — an object-file backend sharing the same trait surface
- **Clean module boundaries** — private implementation details stay private; consumers depend on an interface, not an implementation

The existing architecture already pushes Cranelift types inward: `batch.rs`, `repl/mod.rs`, and `macro_expand.rs` interact with the backend exclusively through `Jit`'s public methods. The refactoring proposed here makes that boundary explicit and renames the few leaking identifiers.

## 2. Current State

### File Inventory

All Cranelift-dependent code lives in seven files:

| File | Lines | Responsibility |
|---|---|---|
| `src/jit.rs` | 823 | Facade: `JITModule` lifecycle, symbol registration, function compilation, execution |
| `src/codegen/mod.rs` | 1,303 | Entry points: `compile_function`, `compile_function_indirect`, types (`FnSlot`, `CallMode`, `TypeDefInfoCg`) |
| `src/codegen/expr.rs` | 263 | Expression-level IR generation |
| `src/codegen/apply.rs` | 349 | Function application IR (direct calls, indirect calls, builtins, closures) |
| `src/codegen/closures.rs` | 741 | Lambda compilation, closure allocation, env-passing wrappers |
| `src/codegen/match_compile.rs` | 265 | Pattern match compilation to branches |
| `src/codegen/primitives.rs` | 100 | Inline primitive IR (arithmetic, comparisons) |
| **Total** | **3,844** | |

### The `Jit` Facade

Consumers interact with the backend through nine public methods on `Jit`:

| Method | Used by |
|---|---|
| `Jit::new()` | `batch.rs:61`, `repl/mod.rs:34` |
| `compile_and_run()` | `batch.rs:62` |
| `compile_defn()` | `repl/input.rs` (via `ReplSession`) |
| `compile_defn_with_resolutions()` | `repl/input.rs` (via `ReplSession`) |
| `eval_expr()` | `repl/input.rs` (via `ReplSession`) |
| `register_trait_method()` | `repl/mod.rs` (via `ReplSession`) |
| `register_type_defs()` | `repl/mod.rs` (via `ReplSession`) |
| `get_def()` | `repl/handlers.rs`, `macro_expand.rs:362` |
| `find_specializations()` | `repl/handlers.rs` |

Data flows strictly inward: consumers pass AST and type information in, and receive execution results or `DefEntry` metadata out. No consumer constructs Cranelift types.

### Consumers

Three files import `Jit`:

| File | Usage |
|---|---|
| `src/batch.rs:3` | `use crate::jit::Jit` — creates `Jit`, calls `compile_and_run()` |
| `src/repl/mod.rs:13` | `use crate::jit::Jit` — stores `Jit` in `ReplSession`, calls compilation methods |
| `src/macro_expand.rs:18` | `use crate::jit::{DefKind, Jit}` — receives `&mut Jit` for macro compilation |

## 3. Cranelift-Specific Leakage

Despite the clean containment, four identifiers expose backend-specific naming to the rest of the codebase:

### 3.1. `Jit` struct name

The struct is named after JIT compilation, a Cranelift capability, not a backend-neutral concept. Used in `batch.rs`, `repl/mod.rs`, and `macro_expand.rs`.

### 3.2. `DefEntry.clif_ir` field

The field name `clif_ir` is Cranelift-specific ("CLIF" = Cranelift IR Format). Accessed by `repl/handlers.rs:467,476` to implement the `/clif` command. An LLVM backend would store LLVM IR in the same role.

### 3.3. `/clif` REPL command

The REPL command `/clif <name>` (`src/repl/commands.rs:39`) and its help text (`src/repl/handlers.rs:36`) reference "Cranelift IR" directly. A backend-neutral command would show whatever IR the active backend produces.

### 3.4. Codegen types visible to `jit.rs`

`FnSlot` and `TypeDefInfoCg` from `src/codegen/mod.rs` are used by `jit.rs`. These are implementation details of how the Cranelift backend compiles functions, not part of the backend interface.

## 4. Phase 1: Backend Trait Extraction

The actionable refactoring — rename leaking identifiers and extract a trait. No new backends yet.

### 4.1. Define the `Backend` trait

A trait capturing the nine public methods of `Jit`, with backend-neutral names:

```rust
// src/backend/mod.rs

pub trait Backend {
    fn new() -> Result<Self, CranelispError> where Self: Sized;

    /// Compile and run a complete program (batch mode).
    fn compile_and_run(
        &mut self,
        program: &Program,
        multi_defns: &[Defn],
        result: &CheckResult,
        tc: &TypeChecker,
    ) -> Result<i64, CranelispError>;

    /// Compile a single function definition (REPL mode).
    fn compile_defn(
        &mut self,
        defn: &Defn,
        scheme: &Scheme,
        method_resolutions: &MethodResolutions,
        source: Option<&str>,
        sexp: Option<&Sexp>,
        expr_types: &HashMap<Span, Type>,
    ) -> Result<(), CranelispError>;

    /// Compile a defn with per-function method resolutions (monomorphised specializations).
    fn compile_defn_with_resolutions(
        &mut self,
        defn: &Defn,
        scheme: &Scheme,
        method_resolutions: &MethodResolutions,
        fn_specific_resolutions: Option<&MethodResolutions>,
        source: Option<&str>,
        sexp: Option<&Sexp>,
        expr_types: &HashMap<Span, Type>,
    ) -> Result<(), CranelispError>;

    /// Evaluate a bare expression (REPL mode).
    fn eval_expr(
        &mut self,
        expr: &Expr,
        method_resolutions: &MethodResolutions,
        expr_types: &HashMap<Span, Type>,
    ) -> Result<i64, CranelispError>;

    /// Register a trait method name as a global (for captures analysis).
    fn register_trait_method(&mut self, name: &str);

    /// Register type definitions for ADT codegen.
    fn register_type_defs(&mut self, tc: &TypeChecker);

    /// Look up a definition by name.
    fn get_def(&self, name: &str) -> Option<&DefEntry>;

    /// Find all specializations of a definition (mangled names).
    fn find_specializations(&self, prefix: &str) -> Vec<(&str, &DefEntry)>;
}
```

### 4.2. Rename identifiers

| Current | Proposed | Reason |
|---|---|---|
| `Jit` (struct) | `CraneliftBackend` | Identifies the implementation; consumers use `Backend` trait |
| `DefEntry.clif_ir` | `DefEntry.ir_dump` | Backend-neutral: any backend produces some IR text |
| `DefEntry.disasm` | `DefEntry.asm_dump` | Parallel naming with `ir_dump` |
| `/clif` (REPL command) | `/ir` | Shows whatever IR the active backend produces |
| `ReplCommand::Clif` | `ReplCommand::Ir` | Matches command rename |

### 4.3. Move files into `src/backend/cranelift/`

```
src/
├── backend/
│   ├── mod.rs              # Backend trait + DefEntry + DefKind
│   └── cranelift/
│       ├── mod.rs           # CraneliftBackend (was jit.rs)
│       ├── codegen/
│       │   ├── mod.rs       # compile_function, compile_function_indirect
│       │   ├── expr.rs
│       │   ├── apply.rs
│       │   ├── closures.rs
│       │   ├── match_compile.rs
│       │   └── primitives.rs
│       └── ...
├── batch.rs                 # uses Backend trait
├── repl/                    # uses Backend trait
└── macro_expand.rs          # uses Backend trait
```

### 4.4. Encapsulate implementation details

After the move, these types become private to `backend::cranelift`:

| Type | Currently in | Visibility after |
|---|---|---|
| `FnSlot` | `codegen/mod.rs:21` | `pub(super)` within `backend::cranelift` |
| `CallMode` | `codegen/mod.rs:27` | `pub(crate)` within `backend::cranelift` (unchanged) |
| `TypeDefInfoCg` | `codegen/mod.rs:48` | `pub(super)` within `backend::cranelift` |
| `ConstructorInfoCg` | `codegen/mod.rs:39` | `pub(super)` within `backend::cranelift` |
| `FN_TABLE_SIZE` | `jit.rs:19` | Private to `CraneliftBackend` |
| `fn_table` field | `jit.rs:55` | Private (already is) |

### 4.5. What stays unchanged

- `DefKind::Function { code_ptr }` — any JIT backend must provide callable function pointers for macro execution
- `DefEntry` — metadata about compiled definitions is backend-neutral (just rename the IR fields)
- The `extern "C"` all-`i64` calling convention — this is a language-level decision, not a backend one
- Symbol registration for platform, intrinsic, and primitive functions — every backend needs this

## 5. Phase 2: Alternative Backends

### 5.1. LLVM ORC Backend

The primary alternative. LLVM ORC (On-Request Compilation) provides incremental JIT compilation suitable for REPL use, plus LLVM's full optimization pipeline.

**Scope**: reimplement the ~3,800 lines of IR generation using the `inkwell` crate (safe Rust bindings to LLVM's C API). The translation is mechanical — the same AST-to-IR logic, targeting LLVM IR instead of Cranelift IR.

**Benefits**:
- Optimization passes (inlining, constant propagation, loop unrolling) for better runtime performance
- Mature debug info emission (DWARF) for source-level debugging
- Broader target support (WebAssembly, GPU, exotic architectures)

**Tradeoffs**:
- Heavy build dependency: LLVM adds minutes to compile times and ~100MB to the build tree
- Slower JIT compilation (LLVM optimisation passes take time)
- More complex API surface than Cranelift

**Build integration**: Cargo features or workspace members:

```toml
[features]
default = ["cranelift"]
cranelift = ["cranelift-jit", "cranelift-module", "cranelift-native", "cranelift"]
llvm = ["inkwell"]
```

A factory function selects the backend:

```rust
pub fn create_backend(kind: BackendKind) -> Result<Box<dyn Backend>, CranelispError> {
    match kind {
        BackendKind::Cranelift => Ok(Box::new(CraneliftBackend::new()?)),
        #[cfg(feature = "llvm")]
        BackendKind::Llvm => Ok(Box::new(LlvmBackend::new()?)),
    }
}
```

### 5.2. Interpreter Backend (Testing)

A minimal backend that interprets the AST directly without generating machine code. Useful for:

- Testing the type checker and AST builder without a native code dependency
- Running cranelisp in environments where JIT is unavailable (e.g. some CI containers)
- Providing a reference implementation to validate JIT output

This backend would not support macro compilation (which requires `code_ptr`) but could support batch execution and expression evaluation.

## 6. Design Constraints

Properties that any `Backend` implementation must preserve:

| Constraint | Reason |
|---|---|
| **Uniform `i64` value representation** | The type system, pattern matching, and all runtime conventions assume every value fits in an `i64`. Bool is 0/1, String is a heap pointer, Float is bitcast f64. |
| **`extern "C"` calling convention** | Platform functions, intrinsics, and primitives are registered as `extern "C"` symbols. The backend must call them with the SystemV (or equivalent) ABI. |
| **Symbol registration for FFI** | `Jit::new()` currently registers ~30 symbols (platform, intrinsics, primitives, operator wrappers). Any backend must accept these registrations. |
| **REPL function redefinition** | The Cranelift backend uses a function pointer table (`fn_table`) for this. Other backends may use different mechanisms (LLVM ORC's replace-materializer, interpreter's lookup table). The `Backend` trait doesn't prescribe the mechanism. |
| **IR/asm dump for introspection** | The `/ir` and `/disasm` REPL commands expect `DefEntry.ir_dump` and `DefEntry.asm_dump` to be populated. Each backend fills these with its own representation. |
| **`code_ptr: *const u8` for macros** | `DefKind::Function { code_ptr }` is used by `macro_expand.rs` to call compiled macros at expansion time. Any backend that supports macros must provide executable function pointers. |
| **Heap layout compatibility** | Heap objects follow `[i64 size][i64 rc][payload...]` layout. Backends generate code that reads/writes this layout for strings, closures, and ADT values. |

## 7. Interaction with Platform DLL Loading

The backend abstraction and the platform DLL loading design (`docs/platform.md`) both affect how external symbols are registered at startup:

- **Current**: `Jit::new()` hard-codes `builder.symbol("cranelisp_print", ...)` calls for each platform function
- **Platform DLL design**: a `PlatformManifest` provides function descriptors dynamically
- **Backend abstraction**: the `Backend::new()` method (or a separate `register_symbols()` method) must accept symbol registrations from either source

These two designs compose naturally: the platform layer produces a list of `(name, type_sig, ptr)` tuples, and the backend layer consumes them via its symbol registration mechanism. Neither layer needs to know the other's implementation details.

The recommended implementation order is:
1. Backend trait extraction (this document, Phase 1) — formalizes the backend boundary
2. Platform abstraction (`docs/platform.md`, Phase 2) — generalizes symbol registration within the existing Cranelift backend
3. Alternative backends (this document, Phase 2) — new implementations of the `Backend` trait

## 8. Open Questions

| Question | Context |
|---|---|
| **Trait object vs generic** | Should consumers hold `Box<dyn Backend>` or be generic over `B: Backend`? Trait objects are simpler but prevent inlining. Generics propagate through `ReplSession`, `batch::run()`, etc. A type alias `type ActiveBackend = CraneliftBackend` is a third option — zero overhead, one line to change. |
| **Backend selection at runtime vs compile time** | Cargo features (compile-time) are simpler and avoid dynamic dispatch. Runtime selection (via CLI flag) is more flexible but adds `dyn` overhead. |
| **Shared `DefEntry` vs per-backend metadata** | `DefEntry` currently stores `ir_dump` and `asm_dump` as `Option<String>`. This works for any backend. If a backend needs richer metadata (e.g. optimization reports), it could use `HashMap<String, String>` for extensibility. |
| **Macro compilation across backends** | The interpreter backend cannot provide `code_ptr`. Should `Backend` have a `supports_macros() -> bool` method, or should macro compilation be a separate optional trait? |
