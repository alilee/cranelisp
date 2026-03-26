# Pipeline v2 Design

**Author:** `/arch`
**Date:** 2026-03-25
**Status:** Proposed — awaiting user review
**Prerequisite:** `design/arch/pipeline-convergence-review.md` (defect analysis)

## 1. Overview

This document designs the unified v2 compilation pipeline that replaces the three parallel v1 pipelines. The design follows Principles 11 (single pipeline, mode parameters), 12 (design for full spec surface), and 13 (auditable interfaces).

The v2 pipeline has seven stages. Every input — batch file, REPL line, module compilation — flows through the same stages with the same types. Mode differences are expressed as parameters, never as separate types or separate functions.

```
Source text + CompileContext
    |           (module, strategy, compile_mode, codegen_target)
    v
[1. Parse]          source text -> Vec<Sexp>
    |
    v
[2. Extract]        Vec<Sexp> -> (ModuleDecls, Vec<Sexp>)
    |                Module declarations (mod, import, export, platform)
    v                extracted before expansion. NOT AST nodes.
[3. Expand]         Vec<Sexp> -> Vec<Sexp>
    |                defmacro interception, macro expansion,
    v                begin flattening
[4. Build AST]      Vec<Sexp> -> Vec<TopLevel>
    |
    v
[5. Typecheck]      (CompileContext, Vec<TopLevel>) -> CheckResult
    |                ctx.module = target module for definitions
    v                ctx.strategy = Additive | Replace
[6a. Codegen]       (CompileContext, Vec<TopLevel>, CheckResult) -> ()
    |                JitAndCache: JIT to memory (hot)
    |                ObjectOnly:  ObjectModule to .o (hot)
    v
[6b. Cache write]   JitAndCache only: queue background .o via CacheWriter
    |                ObjectOnly: skipped (.o already written in 6a)
    v
[7. Execute]        Mode-dependent: call entry / update GOT / display
```

### Key design decisions

1. **One `TopLevel` enum** with an `Expr` variant — no `ReplInput`.
2. **One `CheckResult` struct** with `display: Option<DisplayInfo>` — no `ReplCheckResult`.
3. **One `check()` entry point** with no mode parameter — no `check_repl_input`, no `CheckMode`. The multi-pass pipeline (register all signatures, then check all bodies) works identically regardless of slice length. A REPL line is a one-element slice; a batch program is a multi-element slice. See §5 for the rationale.
4. **`CompileMode`** controls codegen strategy (GOT-indirect vs direct calls). **`CodegenTarget`** controls codegen output (JIT+cache vs object-only). They are orthogonal parameters on `CompileContext`. See §8.4.
5. **Call graph** is a cross-cutting data structure populated during typecheck, consumed by codegen and analysis passes.
6. **`CompileContext`** makes the module context explicit. Every pipeline invocation declares which module definitions land in, whether the invocation is additive or replacing, and what codegen produces. See §14.
7. **Background `.o` writer** (`CacheWriter`) decouples cache persistence from the hot path. `JitAndCache` queues background writes; `ObjectOnly` writes synchronously. See §16.12.

## 2. Pipeline Stages

### 2.1 Parse (Stage 1)

**Input:** Source text (`&str`)
**Output:** `Vec<Sexp>`
**Owner:** `cranelisp-frontend`

The PEG parser converts source text to S-expressions. No changes from v1.

```
parse(source: &str) -> Result<Vec<Sexp>, CranelispError>
```

### 2.2 Extract (Stage 2)

**Input:** `Vec<Sexp>`
**Output:** `(ModuleDecls, Vec<Sexp>)`
**Owner:** `cranelisp-frontend`

Module-level declarations (`mod`, `import`, `export`, `platform`) are extracted from the raw S-expression stream before macro expansion. These forms are NOT AST nodes (spec §5.8–5.10 explicitly state they are processed during the module loading phase). The remaining sexps proceed to expansion.

This stage exists in v1 as `extract_module_decls()`. No changes needed.

```
extract_module_decls(sexps: Vec<Sexp>) -> Result<ModuleDecls, CranelispError>
```

### 2.3 Expand (Stage 3)

**Input:** `Vec<Sexp>` (remaining after extraction)
**Output:** `Vec<Sexp>`
**Owner:** `cranelisp-frontend` (trait) + binary crate (implementation)

Three sub-steps:
1. **defmacro interception** — `defmacro` forms are compiled and registered, not passed through.
2. **Macro expansion** — known macro invocations are expanded. The `MacroExpander` trait (defined in frontend, implemented in binary crate) enables this without a circular dependency.
3. **begin flattening** — `(begin ...)` forms are spliced into the enclosing sequence.

Bare-symbol macro expansion happens here too (spec §5.5.1).

This stage exists in v1 spread across `CompilationSession::process_and_build_program()` and `ReplSession::eval_sexp()`. The v2 design extracts it into a standalone function:

```
expand_forms(
    sexps: Vec<Sexp>,
    expander: &mut dyn MacroExpander,
) -> Result<Vec<Sexp>, CranelispError>
```

### 2.4 Build AST (Stage 4)

**Input:** `Vec<Sexp>` (expanded)
**Output:** `Vec<TopLevel>`
**Owner:** `cranelisp-frontend`

Each sexp is classified and converted to a `TopLevel` variant. The `build_top_level` function handles ALL top-level forms including bare expressions (which become `TopLevel::Expr`). There is no separate `build_repl_input`.

```
build_top_level(sexp: &Sexp) -> Result<TopLevel, CranelispError>
```

Called in a loop over the expanded sexps to produce `Vec<TopLevel>`.

### 2.5 Typecheck (Stage 5)

**Input:** `(&CompileContext, &[TopLevel])`
**Output:** `CheckResult`
**Owner:** `cranelisp-typecheck`

The single entry point for all type checking:

```rust
impl TypeChecker {
    pub fn check(
        &mut self,
        ctx: &CompileContext,
        program: &[TopLevel],
    ) -> Result<CheckResult, CranelispError>;
}
```

The pipeline is always multi-pass:

1. Register all type defs, trait decls, trait impls, and function signatures.
2. Check all function bodies (forward references work).
3. Detect constrained fns.
4. Monomorphise (scanning both defn bodies AND bare expressions).
5. Resolve auto-curry.
6. Populate `DisplayInfo` for the last `Expr` or `Defn` in the input (if any).

There is no mode parameter. The multi-pass pipeline works identically regardless of the number of input forms. A REPL line produces a one-element slice; a batch program produces a multi-element slice. The passes degenerate correctly on small inputs: registering one signature then checking one body is the same work as doing both inline.

The `Expr` variant is handled by wrapping it in a synthetic zero-arg `Defn` internally (moved from the backend where `compile_expr_with_got` currently does this wrapping). The synthetic defn is checked normally, and its inferred type populates `CheckResult.display`.

### 2.6 Codegen (Stage 6)

**Input:** `(&CompileContext, &[TopLevel], &CheckResult)`
**Output:** Side effects — depends on `CodegenTarget` (see §8.4)
**Owner:** `cranelisp-backend`

Stage 6 has two sub-stages. Which sub-stages run depends on `ctx.codegen_target`:

**Stage 6a — Compile.** The core codegen step. What it produces depends on the target:

- **`JitAndCache`**: JIT compilation to memory. Each defn is compiled via Cranelift's `JITModule` and registered in the GOT. `CompileMode` controls the strategy within JIT (GOT-indirect for Interactive, direct calls for Batch).
- **`ObjectOnly`**: ObjectModule compilation to `.o` file. Each defn is compiled via Cranelift's `ObjectModule` with PIC mode. The `.o` file is written as the hot-path output. No GOT pointers are produced.

**Stage 6b — Background cache write (JitAndCache only).** After JIT compilation completes, the module's functions are re-emitted through `ObjectModule` to produce a `.o` file + `.meta.json`. This write is queued on the background `CacheWriter` thread (§16.12) and never blocks the pipeline. `ObjectOnly` mode skips 6b entirely — it already wrote the `.o` in 6a.

`CompileMode` controls the codegen *strategy* (GOT-indirect vs direct calls). `CodegenTarget` controls the codegen *output* (JIT memory vs object file). See §8.4 for the full relationship.

The backend takes `CheckResult` directly — no adapter, no conversion. The `display` field is ignored by the backend.

### 2.7 Execute (Stage 7)

**Input:** JIT-compiled code + `CheckResult`
**Output:** Mode-dependent

- **Batch**: Find `main`, call it, run IO trampoline, exit with result.
- **Interactive/REPL**: Execute the compiled expression/defn, use `CheckResult.display` to format and show the result.
- **Module loading**: No execution — registration only.

This stage is owned by the binary crate's orchestration layer.

## 3. Unified `TopLevel`

### 3.1 Design rationale

The spec defines the following top-level forms:

| Form | Spec section | Notes |
|------|-------------|-------|
| `defn` / `defn-` | §5.1 | Function (single or multi-signature) |
| `deftype` / `deftype-` | §5.2 | Algebraic data type |
| `deftrait` / `deftrait-` | §5.3 | Trait declaration |
| `impl` | §5.4 | Trait implementation |
| `defmacro` / `defmacro-` | §5.5 | Macro definition — intercepted in Stage 3, NOT an AST node |
| `const` / `const-` | §5.6 | Prelude macro — expands in Stage 3, NOT an AST node |
| `def` / `def-` | §5.7 | Prelude macro — expands in Stage 3, NOT an AST node |
| `mod` / `mod-` | §5.8 | Extracted in Stage 2, NOT an AST node |
| `import` | §5.9 | Extracted in Stage 2, NOT an AST node |
| `export` | §5.9 | Extracted in Stage 2, NOT an AST node |
| `platform` | §5.10 | Extracted in Stage 2, NOT an AST node |
| bare expression | §4.* | REPL: evaluated; batch: only in entry module as side effects |

Forms that are NOT AST nodes (`defmacro`, `const`, `def`, `mod`, `import`, `export`, `platform`) are handled before the AST builder runs. They never appear as `TopLevel` variants. This is the correct design per Principle 10 (parser keywords for distinct syntax only).

### 3.2 Type definition

```rust
/// Function definition. spec: §5.1
///
/// Covers both single-signature (§5.1.1) and multi-signature (§5.1.2)
/// functions. A single-signature function has exactly one variant.
/// The spec uses the same `defn` keyword for both forms — the AST
/// makes no structural distinction.
///
/// Also used for trait method implementations (TraitImpl.methods),
/// where exactly one variant is always present.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Defn {
    pub name: Symbol,
    pub docstring: Option<String>,
    pub variants: Vec<DefnVariant>,
    pub visibility: Visibility,
    pub span: Span,
}

impl Defn {
    /// Returns true if this is a multi-signature function (more than one variant).
    pub fn is_multi_sig(&self) -> bool {
        self.variants.len() > 1
    }

    /// Convenience: params of the single variant. Panics if multi-sig.
    /// Use only when the caller has verified `!is_multi_sig()`.
    pub fn params(&self) -> &[Symbol] {
        assert!(!self.is_multi_sig(), "use variants for multi-sig defns");
        &self.variants[0].params
    }

    /// Convenience: body of the single variant. Panics if multi-sig.
    pub fn body(&self) -> &Expr {
        assert!(!self.is_multi_sig(), "use variants for multi-sig defns");
        &self.variants[0].body
    }

    /// Convenience: param_annotations of the single variant. Panics if multi-sig.
    pub fn param_annotations(&self) -> &[Option<TypeExpr>] {
        assert!(!self.is_multi_sig(), "use variants for multi-sig defns");
        &self.variants[0].param_annotations
    }
}

/// Top-level form: the unit of compilation.
///
/// Every form the spec defines at the top level that survives to
/// type checking. Forms handled earlier (mod, import, export,
/// platform, defmacro, const, def) are NOT represented here.
///
/// spec: §5 (Definitions), §4 (Expressions)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum TopLevel {
    /// Function definition (single or multi-signature).
    /// spec: §5.1
    Defn(Defn),

    /// Algebraic data type definition.
    /// spec: §5.2
    TypeDef {
        name: TypeName,
        docstring: Option<String>,
        type_params: Vec<Symbol>,
        constructors: Vec<ConstructorDef>,
        visibility: Visibility,
        span: Span,
    },

    /// Trait declaration.
    /// spec: §5.3
    TraitDecl(TraitDecl),

    /// Trait implementation.
    /// spec: §5.4
    TraitImpl(TraitImpl),

    /// Bare expression.
    /// REPL: evaluated and displayed.
    /// Batch: side effect in entry module (e.g., top-level IO expression).
    /// spec: §4 (all expression forms)
    Expr(Expr),
}

/// A complete compilation unit: all top-level forms from one module.
pub type Program = Vec<TopLevel>;
```

**What changed from v1:**
- `Defn` struct merged with `DefnMulti`: the old `Defn` had `params`, `param_annotations`, `body` directly; the new `Defn` has `variants: Vec<DefnVariant>`. A single-signature function is a `Defn` with one variant. Multi-signature functions have multiple variants. The `DefnMulti` variant of `TopLevel` is eliminated.
- `TopLevel` has 5 variants instead of 6 (no `DefnMulti`).
- Added `Expr(Expr)` variant (was only in `ReplInput`).
- `ReplInput` deleted entirely — `TopLevel` is used everywhere.
- `toplevel_to_repl_input()` deleted — no conversion needed.
- Convenience methods `params()`, `body()`, `param_annotations()` on `Defn` provide ergonomic access for single-variant code paths, panicking if called on multi-sig (a programming error).

**Rationale for the merge:** The spec uses the same `defn` keyword for single-sig (§5.1.1) and multi-sig (§5.1.2). Having two separate representations in the AST created a structural split that propagated through every pipeline stage: every `match` on `TopLevel` needed both a `Defn` arm and a `DefnMulti` arm with near-identical logic. Worse, the split made it easy to handle `Defn` and silently skip `DefnMulti` — which is exactly what happened (see `collect_defns`, `compile_checked_program`, `check_repl_input`). The merge makes `DefnMulti` handling impossible to forget: there is only one variant to match.

**`TraitImpl.methods` impact:** Trait method bodies are always single-signature (spec §5.4.5). Under the merged design, each method is a `Defn` with `variants.len() == 1`. This is slightly redundant (a one-element Vec) but eliminates the alternative of maintaining a separate `MethodDef` type — one function-definition type is better than two.

**Why no `Loop` or `Recur` variants?** The spec says `loop`/`recur` are future features. When they arrive, they will be `Expr` variants (they are expression forms, not top-level definitions), so `TopLevel` does not need to change.

## 4. Unified `CheckResult`

### 4.1 Design rationale

The v1 `CheckResult` and `ReplCheckResult` differed by two fields: `ty: Type` and `scheme: Option<Scheme>` (for REPL display). The v2 design folds these into an optional `DisplayInfo`:

### 4.2 Type definition

```rust
/// Result of type checking a compilation unit.
///
/// The single boundary type between typecheck and backend.
/// Self-contained: the backend produces code from CheckResult + Program alone.
///
/// The `display` field carries REPL display data. The backend ignores it.
/// It is populated from the last Expr or Defn in the input (if any).
#[derive(Debug)]
pub struct CheckResult {
    // --- Codegen payload (consumed by backend) ---

    /// How each call site was resolved (trait dispatch, overload, auto-curry, builtin).
    pub method_resolutions: MethodResolutions,

    /// Names of constrained polymorphic functions requiring monomorphisation.
    pub constrained_fn_names: HashSet<Symbol>,

    /// Monomorphised function definitions generated during checking.
    pub mono_defns: Vec<MonoDefn>,

    /// Type of every expression, keyed by span (for codegen heap classification).
    pub expr_types: HashMap<Span, Type>,

    /// Default trait method implementations expanded during checking.
    pub default_method_defns: Vec<Defn>,

    /// All ADT definitions encountered in this compilation unit.
    /// Backend needs this for constructor allocation, match discrimination, drop glue.
    pub type_defs: HashMap<TypeName, TypeDefInfo>,

    /// Maps each constructor name to its parent type name.
    /// Backend uses this to look up tag, field count, field types.
    pub constructor_to_type: HashMap<Symbol, TypeName>,

    // --- Diagnostics ---

    /// Non-fatal warnings accumulated during checking.
    pub warnings: Vec<Warning>,

    // --- REPL display (ignored by backend) ---

    /// Display information for REPL feedback. None in batch/module mode.
    pub display: Option<DisplayInfo>,
}

/// REPL display payload: type and scheme for the checked input.
#[derive(Debug, Clone)]
pub struct DisplayInfo {
    /// Inferred type of the expression or definition.
    pub ty: Type,
    /// Generalized scheme (for defn display). None for bare expressions.
    pub scheme: Option<Scheme>,
}
```

**What changed from v1:**
- `ReplCheckResult` deleted.
- `display: Option<DisplayInfo>` added to `CheckResult`.
- `build_check_for_backend()` (both copies) deleted — backend takes `CheckResult` directly, ignores `display`.

## 5. Why There Is No `CheckMode`

### 5.1 The multi-pass pipeline works on any slice length

The original v2 draft introduced `CheckMode::WholeProgram` vs `CheckMode::Incremental` as a parameter on `check()`. Review revealed this distinction is unnecessary.

The multi-pass pipeline (register all signatures first, then check all bodies) degenerates correctly on a single-element input:

- **One `Defn`**: Pass 1 registers one signature. Pass 2 checks one body. Same work as the v1 `check_single_defn`, just in two loop iterations over a one-element slice instead of one inline sequence.
- **One `Expr`**: Wrapped in a synthetic defn. Pass 1 registers it. Pass 2 checks it. No different from batch.
- **One `TypeDef` / `TraitDecl` / `TraitImpl`**: Immediate registration. The pass structure is irrelevant — these are registered in Pass 1 and have no body to check in Pass 2.

There is no case where multi-pass produces wrong results on a short input. Forward references within a single element are impossible (there's only one element), so the register-all-then-check-all pattern is vacuously correct.

### 5.2 `begin` expansion benefits from multi-pass

A REPL input `(begin (defn a [...] ...) (defn b [x] (a x)))` expands to multiple forms. With the single multi-pass pipeline, both `a` and `b` are registered in Pass 1, then both bodies are checked in Pass 2. Forward references between them work correctly — `b` can call `a` AND `a` can call `b`.

Under the v1 incremental approach, each form was processed individually, so `b` calling `a` worked (because `a` was registered in a prior iteration), but `a` calling `b` would fail. The multi-pass approach is strictly better.

### 5.3 Performance is negligible

The overhead of multi-pass on a one-element slice is two iterations (register + check) vs one (register-and-check inline). The registration primitives are the same either way. For a single REPL form, this is unmeasurable.

### 5.4 REPL-specific concerns are orthogonal

The only REPL-specific behavior in typechecking is populating `DisplayInfo` — the type of the last expression or definition for REPL feedback. This is not a mode difference in the checking *strategy*; it is a post-check step that looks at the input to decide whether to populate an optional field. It happens unconditionally: batch programs get `display: None` because their last form is a `Defn` in a non-entry module; REPL inputs get `display: Some(...)` because their last form is typically an `Expr` or `Defn` the user wants feedback on.

The v1 REPL path also had `monomorphise_expr_calls` (scanning a single expression for constrained-fn calls) while the batch path had `pass4_monomorphise` (scanning all defn bodies). The batch path had a bug: it only scanned defn bodies, not bare `Expr`s. A unified `check()` fixes this by scanning both — the correct behavior regardless of input source.

### 5.5 `Expr` handling

A bare `Expr` is wrapped in a synthetic zero-arg `Defn`:

```rust
fn wrap_expr_as_defn(expr: &Expr) -> Defn {
    Defn {
        name: Symbol::from("__repl_expr__"),
        docstring: None,
        variants: vec![DefnVariant {
            params: vec![],
            param_annotations: vec![],
            body: expr.clone(),
            span: expr.span(),
        }],
        visibility: Visibility::Private,
        span: expr.span(),
    }
}
```

The synthetic defn is type-checked normally. Its inferred return type populates `DisplayInfo.ty`. The backend compiles and executes it as a zero-arg function.

This wrapping happens inside `TypeChecker::check()`, not in the binary crate. It is invisible to callers.

### 5.6 Multi-signature `Defn` handling

A `Defn` with `variants.len() > 1` (i.e., `defn.is_multi_sig()`) is expanded into individual single-variant `Defn` entries during type checking. Each variant becomes a separate `Defn` with a mangled name (`name$Type1+Type2`). The base name gets an `Overloaded` `DefKind` entry in the symbol table.

All multi-sig variants are collected alongside regular single-variant defns in Pass 1, then their bodies are checked in Pass 2. The backend receives the expanded variants as regular single-variant `Defn` entries via `CheckResult.mono_defns` (or as top-level defns if not constrained-polymorphic). The backend does not need to know about multi-sig — it only sees the expanded single-variant defns.

### 5.7 `CompileMode` within `CompileContext`

`CompileMode` controls codegen strategy (GOT-indirect vs direct calls). It is carried inside `CompileContext` alongside the module target and strategy. See §14 for the full `CompileContext` design.

```
              CompileMode
              Interactive    Batch       Release
             ┌──────────────────────────────────────────┐
REPL         │ GOT-indirect  (unused)     (unused)      │
Batch        │ multi-module  single-file  standalone    │
             │ compile       test exec    binary        │
             └──────────────────────────────────────────┘
```

### 5.8 Multi-pass pipeline (unified)

```
// ctx: &CompileContext determines target module and strategy

if ctx.strategy == Replace:
  clear_module_state(ctx.module)     // wipe existing definitions

set_active_module(ctx.module)        // definitions register into this module

for each form:
  register_type_def (if TypeDef)
  register_trait_decl (if TraitDecl)
  register_trait_impl (if TraitImpl)
  register_defn_signature (if Defn, single-variant)
  expand_and_register_defn_multi (if Defn, multi-variant)
  wrap_expr_as_defn (if Expr) + register signature

for each defn (including synthetic expr-defns and expanded multi-sig variants):
  check_defn_body

detect_constrained_fns
monomorphise (scan defn bodies AND synthetic expr-defns)
resolve_auto_curry
populate display (from last Expr or Defn, if any)
build_check_result
```

This is the same pipeline regardless of whether the input is a batch program (many forms), a module (many forms), or a REPL line (one or few forms). The `CompileContext` makes the differences explicit: a file load uses `Replace` to define the module's complete contents; a REPL line uses `Additive` to extend the current module.

## 6. Call Graph

### 6.1 Purpose

The call graph serves three current and future use cases:

1. **Incremental recompilation** (future): When a function changes, identify its callers and recompile them. Requires: caller→callee edges, reverse index (callee→callers).

2. **Mutual recursion SCC detection** (future): Identify strongly connected components for loop-merge optimisation. Requires: caller→callee edges with Tarjan's algorithm.

3. **Non-tail recursion warnings** (current): Detect self-recursive calls not in tail position. Requires: caller→callee edges with tail-position flag.

### 6.2 Data structure

```rust
/// An edge in the call graph.
#[derive(Debug, Clone)]
pub struct CallEdge {
    /// The callee being called.
    pub callee: Symbol,
    /// Whether this call is in tail position (for TCO analysis).
    pub tail_position: bool,
    /// Source location of the call (for diagnostics).
    pub span: Span,
}

/// Per-function call information.
#[derive(Debug, Clone, Default)]
pub struct CallInfo {
    /// Functions this function calls.
    pub callees: Vec<CallEdge>,
}

/// Program-wide call graph. Adjacency list representation.
///
/// Populated during type checking (Stage 5). Consumed by:
/// - Analysis passes (SCC detection, recursion warnings)
/// - Incremental recompilation (callee→caller reverse index)
/// - Backend (tail-call information)
#[derive(Debug, Clone, Default)]
pub struct CallGraph {
    /// Forward edges: caller → list of callees.
    pub edges: HashMap<Symbol, CallInfo>,
}

impl CallGraph {
    /// Record a call from `caller` to `callee`.
    pub fn add_edge(&mut self, caller: &Symbol, callee: Symbol,
                     tail_position: bool, span: Span) {
        self.edges
            .entry(caller.clone())
            .or_default()
            .callees
            .push(CallEdge { callee, tail_position, span });
    }

    /// Build the reverse index (callee → set of callers).
    /// Used for incremental recompilation.
    pub fn reverse_index(&self) -> HashMap<Symbol, HashSet<Symbol>> {
        let mut reverse = HashMap::new();
        for (caller, info) in &self.edges {
            for edge in &info.callees {
                reverse
                    .entry(edge.callee.clone())
                    .or_insert_with(HashSet::new)
                    .insert(caller.clone());
            }
        }
        reverse
    }

    /// Find strongly connected components (Tarjan's algorithm).
    /// Used for mutual recursion detection and loop-merge candidates.
    pub fn sccs(&self) -> Vec<Vec<Symbol>> {
        todo!("Tarjan's SCC — implemented when mutual recursion support arrives")
    }

    /// Find self-recursive calls not in tail position.
    /// Returns (function_name, call_span) pairs for warning generation.
    pub fn non_tail_self_recursion(&self) -> Vec<(Symbol, Span)> {
        let mut warnings = Vec::new();
        for (caller, info) in &self.edges {
            for edge in &info.callees {
                if &edge.callee == caller && !edge.tail_position {
                    warnings.push((caller.clone(), edge.span));
                }
            }
        }
        warnings
    }
}
```

### 6.3 Population

The call graph is populated during type checking (Stage 5) as a side effect of `infer_apply`. When the typechecker resolves a call, it records the edge:

```
TypeChecker::infer_apply(callee, args, span)
    → resolve call target
    → record in call_graph: (current_fn, target, tail_position, span)
    → continue with normal inference
```

The call graph is stored on `TypeChecker` during checking and transferred to `CheckResult` when checking completes:

```rust
pub struct CheckResult {
    // ... existing fields ...
    pub call_graph: CallGraph,
}
```

### 6.4 Module system interaction

The call graph uses `Symbol` identifiers (local names within a module). Cross-module calls use qualified names (`module/function`). The call graph does not track module boundaries — it records whatever name the typechecker resolved. For incremental recompilation, the reverse index must be filtered by module to determine which module's functions need recompiling.

### 6.5 Sketch comparison

The sketch does not have a call graph. Tail-call detection is done inline during codegen (checking if a call is in `in_tail_position`). The sketch has no incremental recompilation or SCC detection.

The v2 call graph separates the analysis from the consumer. The typechecker builds the graph; codegen and analysis passes read it. This is cleaner than threading `in_tail_position` through every codegen path.

**Note:** The current v1 backend already tracks `in_tail_position` during codegen. The call graph does not replace this — TCO loop-header emission must still happen during codegen. The call graph enables *warnings* about non-tail recursion and *future* SCC analysis. The `in_tail_position` flag in codegen remains the mechanism for actually emitting TCO code.

## 7. Crate Allocation

### 7.1 Does the 7-crate DAG survive?

Yes. The v2 pipeline changes do not alter the crate boundaries. The seven crates retain their responsibilities:

```
cranelisp (binary: v2 pipeline orchestration)
  |
  +-- cranelisp-frontend (parse, extract, build AST, MacroExpander trait)
  |     |
  |     +-- cranelisp-types
  |
  +-- cranelisp-typecheck (check(), call graph)
  |     |
  |     +-- cranelisp-types
  |
  +-- cranelisp-backend (codegen with CompileMode)
  |     |
  |     +-- cranelisp-types
  |     +-- cranelisp-runtime
  |
  +-- cranelisp-runtime
  |     |
  |     +-- cranelisp-platform
  |     +-- cranelisp-types
  |
  +-- cranelisp-platform
  |
  +-- cranelisp-types (TopLevel, CheckResult, CallGraph, ...)
```

### 7.2 Type ownership

| Type | Crate | Rationale |
|------|-------|-----------|
| `TopLevel` (with `Expr`, merged `Defn`) | `cranelisp-types` | Boundary type between frontend and typecheck |
| `CheckResult` (with `DisplayInfo`) | `cranelisp-types` | Boundary type between typecheck and backend |
| ~~`CheckMode`~~ | ~~deleted~~ | Not needed — multi-pass pipeline works on any slice length (see §5) |
| `CompileMode` | `cranelisp-types` | Pipeline configuration — codegen strategy: GOT-indirect vs direct calls (unchanged) |
| `CodegenTarget` | `cranelisp-types` | Pipeline configuration — codegen output: JIT+cache vs object-only (see §8.4) |
| `ModuleStrategy` | `cranelisp-types` | Pipeline configuration — additive vs replacement (see §14) |
| `CompileContext` | `cranelisp-types` | Pipeline configuration — module + strategy + compile_mode + codegen_target (see §14) |
| `CallGraph`, `CallEdge`, `CallInfo` | `cranelisp-types` | Cross-cutting data structure — frontend populates, typecheck builds, backend and binary crate consume |
| `DisplayInfo` | `cranelisp-types` | Part of `CheckResult` |
| `ModuleDecls` | `cranelisp-types` | Extracted by frontend, consumed by binary crate |

### 7.3 What moves

- `ReplInput` — **deleted** from `cranelisp-types`
- `ReplCheckResult` — **deleted** from `cranelisp-types`
- `TopLevel::DefnMulti` — **deleted** from `TopLevel` enum (merged into `Defn`)
- `CodegenTarget` — **added** to `cranelisp-types` (§8.4)
- `Defn` struct — **changed**: `params`/`body`/`param_annotations` replaced by `variants: Vec<DefnVariant>`
- `Expr` variant — **added** to `TopLevel` in `cranelisp-types`
- `DisplayInfo` — **added** to `cranelisp-types`
- `CallGraph` etc. — **added** to `cranelisp-types`

## 8. Orchestration: Callers and Module Loading

### 8.1 Production callers

There are two production paths into the compiler: `--run` (batch) and the REPL. Both start the same way — load an entry file, which triggers recursive dependency resolution via `compile_unit()`. They diverge only after loading completes.

```
--run file.cl:
    1. Load entry file → recursive compile_unit() for all transitive dependencies
    2. Find main, run IO trampoline, exit

REPL:
    1. Load entry file (defaults to `user` module) → recursive compile_unit()
    2. Enter interactive loop: each line → compile_unit() in Additive mode
       (new imports in REPL lines can trigger further recursive module loads)
```

A test helper `compile_and_run()` also exists. It calls `compile_unit()` directly with no lib_dirs on the session, making imports unresolvable. This is deliberate — tests are self-contained. `compile_and_run()` is not a production path and is not discussed further in this section.

### 8.2 What `compile_unit()` owns

`compile_unit()` is the single pipeline entry point for all compilation. It owns **all seven stages** from parse through execute:

```rust
pub fn compile_unit(
    session: &mut CompilationSession,
    source: &str,
    ctx: &CompileContext,
) -> Result<CompileUnitResult, CranelispError>
```

**Input:** source text (`&str`) and a `CompileContext`. NOT pre-parsed sexps. The reason: if callers parse before calling compile_unit(), each caller must implement its own parse-error handling, its own extract logic, and its own expansion loop. That is the parallel-callers problem we are eliminating.

**Stages owned by `compile_unit()`:**

1. **Parse** — `cranelisp_frontend::parse(source)` → `Vec<Sexp>`
2. **Extract** — `cranelisp_frontend::extract_module_declarations()` → `(ModuleDecls, Vec<Sexp>)`. Registers imports/exports on the TypeChecker. **Imports of fully-qualified names trigger recursive `compile_unit()` calls** (see §8.3).
3. **Expand** — `process_forms_sequentially()` on remaining sexps: defmacro interception (compile + register via `MacroExpander`), macro expansion, begin-flattening. → `Vec<Sexp>`
4. **Build AST** — `cranelisp_frontend::build_program()` → `Vec<TopLevel>`
5. **Typecheck** — `TypeChecker::check(&ctx, &program)` → `CheckResult`
6. **Codegen** — mode-dependent: batch (direct calls) or interactive (GOT-indirect)
7. **Execute** — mode-dependent: call entry fn, or return for display

**What `compile_unit()` does NOT own:**

- Slash command dispatch (REPL-only, pre-pipeline)
- REPL interception (bare-symbol introspection, annotation expressions)
- Session persistence (saving user.cl)
- Error recovery (snapshot/restore)
- File I/O (reading source files — callers read and pass source text)

### 8.3 Recursive module loading

`compile_unit()` is recursive. When Stage 2 (Extract) encounters an import of a module that is not yet compiled, it resolves the module via `session.lib_dirs`, reads the source file, and calls `compile_unit()` recursively for the dependency. The dependency's own imports trigger further recursion until all transitive dependencies are compiled.

```
compile_unit(session, "user.cl", ctx_user)
  Stage 2: extract finds (import [core.option [Some None]])
    → core.option not yet compiled
    → resolve "core/option.cl" via lib_dirs
    → read source
    → compile_unit(session, core_option_source, ctx_core_option)  ← recursive
        Stage 2: extract finds (import [primitives [Int]])
          → primitives already registered (built-in) → no recursion
        Stages 3-7: compile core.option
    → core.option now available
  Stages 3-7: compile user.cl (can now reference core.option symbols)
```

This is the **module walk** — the recursive loading of all transitive dependencies. It is not a separate discovery mechanism; it IS `compile_unit()` calling itself. The same mechanism operates whether the initial load comes from `--run` or from a REPL `(import ...)`.

**Cycle detection:** The session tracks which modules are currently being compiled (on the call stack). If `compile_unit()` encounters an import of a module that is already on the stack, it reports a circular dependency error.

**lib_dirs controls import capability.** `CompilationSession` carries a `lib_dirs: Vec<PathBuf>` that determines where to search for module source files. If lib_dirs is empty (as in test helpers), imports cannot resolve and compilation is self-contained. This is how tests work without needing a separate code path — the same `compile_unit()` function handles both cases; the session configuration determines whether recursive loading is possible.

**Cache interaction:** Before recursively calling `compile_unit()` for a dependency, the session checks whether a cached `.o` file exists with a matching source hash. A cache hit restores the module's symbol table and codegen state without re-running the pipeline.

### 8.4 Two-pass model and `CodegenTarget`

The pipeline naturally divides into two passes:

**Pass 1 — Typecheck (stages 1–5, sequential, recursive).** The module walk runs parse through typecheck. Each module's imports trigger recursive loading (typecheck-only) of dependencies. GOT slots are assigned as functions are registered during typecheck. After the recursive walk completes, all modules are typechecked and all GOT slots are settled. Pass 1 is identical across all scenarios.

**Pass 2 — Codegen (stage 6, per-module).** With all slot assignments stable, codegen runs for each module. What codegen *produces* depends on the scenario:

| Scenario | Pass 2 target | `.o` generation |
|----------|--------------|-----------------|
| REPL / `--run` | JIT to memory (hot) | Background, nice priority, async (§16.12) |
| `--link` | ObjectModule to `.o` (hot) | This IS the codegen — no JIT step |

`CodegenTarget` replaces the earlier `PipelineDepth` draft and makes the distinction precise:

```rust
/// What codegen produces in Pass 2. Carried inside `CompileContext`.
pub enum CodegenTarget {
    /// JIT to memory (hot) + .o to disk (background, nice priority).
    /// Used by REPL and --run. Stage 6a produces live function pointers
    /// in the GOT; stage 6b queues a background .o write via the
    /// CacheWriter (§16.12). The user is never blocked by .o generation.
    JitAndCache,

    /// ObjectModule to .o file (hot). No JIT, no execution.
    /// Used by --link. Stage 6 compiles directly to a relocatable .o
    /// via Cranelift's ObjectModule backend. No GOT pointers are produced.
    ObjectOnly,
}
```

**Relationship to `CompileMode`.** `CompileMode` (Interactive / Batch / Release) controls codegen *strategy* — GOT-indirect vs direct calls. `CodegenTarget` controls codegen *output* — JIT memory vs object file. They are orthogonal:

- REPL / `--run`: `CompileMode::Interactive` + `CodegenTarget::JitAndCache`
- `--link`: `CompileMode::Interactive` + `CodegenTarget::ObjectOnly`
- Test helpers: `CompileMode::Batch` + `CodegenTarget::JitAndCache` (no cache_state, so no .o written)

Both are carried inside `CompileContext` (§14).

**Current implementation.** Currently `compile_unit()` runs all seven stages sequentially for each module. The two-pass separation (typecheck all modules, then codegen all modules) is a future optimisation for parallel codegen (§12.5). What is implementable NOW:

- Sequential Pass 1 (recursive typecheck) — already works.
- Sequential Pass 2 with appropriate target: `JitAndCache` compiles to JIT memory and queues background `.o` writes; `ObjectOnly` compiles directly to `.o` files.
- Background `.o` writer for `JitAndCache` mode (§16.12).

**Future parallel codegen.** When parallel codegen is implemented, Pass 2 fans out across modules. Each module gets its own `Jit` or `ObjectModule` instance, reads its `CheckResult` and slot assignments (both read-only), and produces output independently. The `CodegenTarget` determines what each parallel worker produces. This is marked as future work — the current implementation compiles one module at a time.

### 8.5 Production flow: `--run`

The `--run` path loads a file and executes its `main` function:

```rust
fn run_batch(entry_file: &Path, session: &mut CompilationSession) -> Result<i64, CranelispError> {
    let source = std::fs::read_to_string(entry_file)?;
    let module_path = derive_module_path(entry_file);
    let ctx = CompileContext {
        module: module_path,
        strategy: ModuleStrategy::Replace,
        compile_mode: CompileMode::Interactive, // GOT-indirect for multi-module
        codegen_target: CodegenTarget::JitAndCache,
    };

    // This call recursively loads all transitive dependencies via lib_dirs.
    // Stage 6a JITs to memory; stage 6b queues background .o writes.
    let result = compile_unit(session, &source, &ctx)?;

    // After loading: find main, run IO trampoline, exit.
    let main_ptr = session.lookup_main()?;
    run_io_trampoline(main_ptr)
}
```

The `compile_unit()` call triggers the entire module walk. When it returns, all transitive dependencies are compiled and registered. The orchestrator's only job after that is to find `main` and execute it.

### 8.6 Production flow: REPL

The REPL loads an entry file (defaulting to a `user` module), then enters an interactive loop. Each line is a `compile_unit()` call in Additive mode.

**REPL pre-pipeline interception.** Before calling `compile_unit()`, the REPL handles concerns that are not compilation:

1. **Skip blanks/comments** — return early for empty input.
2. **Slash command dispatch** — if input starts with `/`, dispatch to the command handler. Not compilation.
3. **Snapshot for error recovery** — `tc.snapshot()` before attempting compilation; `tc.restore()` on error.
4. **Bare-symbol introspection** — macros and special forms entered as bare symbols at the REPL produce helpful self-documentation instead of type errors. This is a REPL-only UX concern.
5. **Annotation expression handling** — `:Type expr` parses as multiple sexps; the REPL detects this and combines them.

**REPL imports flow through compile_unit().** Unlike the previous design, imports are NOT intercepted by the REPL as a special case. An `(import [core.option [Some None]])` in a REPL line flows into `compile_unit()` normally. Stage 2 (Extract) finds the import, resolves the module via lib_dirs, and recursively calls `compile_unit()` to load the dependency. This is the same mechanism as batch loading — the REPL does not need a separate module-loading path.

After interception checks pass, the REPL calls `compile_unit()`:

```rust
pub fn eval(&mut self, source: &str) -> Result<ReplResult, CranelispError> {
    // Pre-pipeline interceptions (slash commands, blanks, snapshot, etc.)
    // ...

    // Classify the input for REPL-specific routing:
    let sexps = cranelisp_frontend::parse(source)?;
    if is_bare_introspection(&sexps) { return self.introspect_symbol(...); }
    if is_annotation_prefix(&sexps[0]) { return self.eval_annotation_expr(sexps); }

    // Normal compilation — through the unified pipeline:
    let ctx = CompileContext {
        module: self.current_module.clone(),
        strategy: ModuleStrategy::Additive,
        compile_mode: CompileMode::Interactive,
    };
    let result = compile_unit(&mut self.core, source, &ctx)?;

    // Post-pipeline: display, session persistence, DefCodegen storage
    self.process_compile_result(result, source)
}
```

**Note on the pre-parse for classification.** The REPL parses the input to classify it (bare-symbol introspection, annotation expression). This is not a pipeline violation — the REPL is parsing *to decide whether to compile*, not to partially pre-process. The parse result is consumed by the interception handler, not passed to `compile_unit()`. When the input is a normal compilation, `compile_unit()` re-parses the source text. The double-parse is negligible for REPL-length input.

### 8.7 Macro compilation inside `compile_unit()`

Macro compilation is the most complex part of the expansion stage. A `(defmacro ...)` form must be:
1. Parsed (by the frontend — `parse_defmacro`)
2. Compiled to native code (by the backend — via `Jit`)
3. Registered in the expander (for subsequent expansions)
4. Registered in the TypeChecker's symbol table (for cross-module import visibility)

This crosses the frontend→backend boundary, which is why the `MacroExpander` trait exists in `cranelisp-types`. The trait provides dependency inversion: the frontend calls `expand()` without knowing about the backend. The binary crate's `CraneliftExpander` implements the trait by wiring frontend parsing + backend JIT compilation.

**Inside `compile_unit()`**, macro compilation flows through `CompilationSession::process_single_form()`:

```
compile_unit(session, source, ctx)
  → parse(source)
  → extract_module_declarations(sexps) → register imports/exports
    → recursive compile_unit() for unresolved imports (via lib_dirs)
  → process_forms_sequentially(remaining_sexps)
      for each sexp:
        if is_defmacro(sexp):
          → compile_and_register_macro(sexp)    ← backend JIT + expander registration
        else:
          → expander.expand_sexp(sexp)           ← uses MacroExpander trait
          → flatten_begin(expanded)
          → for each sub-form:
              if is_defmacro: compile_and_register_macro
              else: accumulate
  → build_program(accumulated_sexps)
  → check(ctx, program)
  → codegen + execute
```

`compile_and_register_macro()` is a method on `CompilationSession`. It:
- Calls `cranelisp_frontend::parse_defmacro()` to get the macro's clause info.
- Creates a fresh `Jit` instance, declares intrinsics, and calls `expander.compile_macro()`.
- Stores the JIT in `session.jit_modules` (keeping function pointers alive).
- Registers the macro in the TypeChecker's symbol table for cross-module visibility.

This is the same mechanism as v1 — `process_single_form()` already does this work. The change is that `compile_unit()` calls it as an internal step, rather than each caller calling it separately.

**The `MacroExpander` trait remains the dependency inversion mechanism.** The frontend crate defines the trait. The binary crate's `CraneliftExpander` implements it. `CompilationSession` owns the `CraneliftExpander` instance. No circular dependencies are introduced.

### 8.8 Convergence diagram

```
    ┌──────────────────────────────────────────────────────────┐
    │                     --run file.cl                         │
    │  1. Read entry file                                      │
    │  2. compile_unit(session, source, ctx) ──────────────┐   │
    │     (recursive: loads all transitive dependencies)   │   │
    │  3. Find main, IO trampoline, exit                   │   │
    └──────────────────────────────────────────────────────┘   │
                                                               │
    ┌──────────────────────────────────────────────────────┐   │
    │                        REPL                          │   │
    │  1. Load entry file via compile_unit() ──────────┐   │   │
    │  2. Interactive loop:                            │   │   │
    │     • slash commands → dispatch (not compilation) │   │   │
    │     • bare-symbol introspection (not compilation) │   │   │
    │     • annotation expr (REPL-specific routing)    │   │   │
    │     • everything else:                           │   │   │
    │       compile_unit(session, source, ctx) ────┐   │   │   │
    │       (Additive mode; imports trigger loads)  │   │   │   │
    │  3. Display result                           │   │   │   │
    └──────────────────────────────────────────────┘   │   │   │
                                                       │   │   │
    ═══════════════════════════════════════════════════╪═══╪═══╪═══
                                                       │   │   │
                                                       v   v   v
                    ┌─────────────────────────────────────────────┐
                    │     compile_unit(session, source, ctx)       │
                    │                                             │
                    │  1. Parse        source → Vec<Sexp>         │
                    │  2. Extract      → ModuleDecls +            │
                    │                    remaining sexps           │
                    │     register imports/exports                 │
                    │     ┌─────────────────────────────────────┐ │
                    │     │ For each unresolved import:         │ │
                    │     │   resolve via session.lib_dirs      │ │
                    │     │   read source file                  │ │
                    │     │   compile_unit(session, dep, ctx')  │◄┤ recursive
                    │     └─────────────────────────────────────┘ │
                    │  3. Expand       defmacro intercept,        │
                    │                  macro expansion,           │
                    │                  begin-flatten               │
                    │  4. Build AST    → Vec<TopLevel>            │
                    │  5. Typecheck    → CheckResult              │
                    │  6. Codegen      mode-dependent             │
                    │  7. Execute      mode-dependent             │
                    └─────────────────────────────────────────────┘
                                         │
                                         v
                                CompileUnitResult {
                                  check_result,
                                  value,
                                  result_type,
                                  warnings
                                }
    ═══════════════════════════════════════════════════════════════
```

**Boundary rule:** Everything above the double line is caller-specific. Everything below is shared. No caller ever calls parse, extract, expand, build_program, check, or codegen directly for normal compilation. Callers only interact with `compile_unit()`.

**The module walk is not a separate mechanism.** The recursive `compile_unit()` calls during Stage 2 are the module walk. There is no separate discovery pass, no separate graph orchestrator. The dependency graph is implicitly walked by the recursion. Topological order is guaranteed by the recursion itself — a module's dependencies are always compiled before the module (because the recursive call returns before Stage 3 begins).

### 8.9 Migration order

The migration proceeds in five steps, each independently testable:

**Step 1: Add v2 types (additive, nothing breaks)** — DONE

Merge `Defn` struct (replace `params`/`body`/`param_annotations` with `variants: Vec<DefnVariant>`). Delete `TopLevel::DefnMulti` variant. Add `Expr` variant to `TopLevel`. Add `DisplayInfo` and `display` field to `CheckResult`. Add `CallGraph` types.

**Step 2: Implement `check()` (new code, nothing breaks)** — DONE

Add `TypeChecker::check(&mut self, &[TopLevel], &CompileContext) -> Result<CheckResult, CranelispError>`. Old entry points remain.

**Step 3: Build v2 orchestration (new code, nothing breaks)** — PARTIAL

Added `src/pipeline_v2.rs` with `compile_unit()`, but currently takes pre-parsed `&[Sexp]` and covers only stages 4-7. Must be extended to own stages 1-3 and recursive module loading (see Step 4).

**Step 4: Complete `compile_unit()` and switch over**

This is the critical migration step. It proceeds in sub-steps:

**Step 4a: Extend `compile_unit()` to own stages 1-3 with recursive loading.**

Change the signature from `compile_unit(session, sexps, ctx)` to `compile_unit(session, source, ctx)`. Move parse, extract, expand, and recursive module loading inside:

```rust
pub fn compile_unit(
    session: &mut CompilationSession,
    source: &str,
    ctx: &CompileContext,
) -> Result<CompileUnitResult, CranelispError> {
    // Cycle detection: check if this module is already on the compile stack.
    if session.compile_stack.contains(&ctx.module) {
        return Err(CranelispError::circular_dependency(&ctx.module));
    }
    session.compile_stack.push(ctx.module.clone());

    // Stage 1: Parse
    let sexps = cranelisp_frontend::parse(source)?;

    // Stage 2: Extract module declarations
    let (structure, remaining) = cranelisp_frontend::extract_module_declarations(
        ctx.module.clone(), None, sexps,
    )?;

    // Resolve and load dependencies recursively.
    for import in &structure.import_specs {
        let dep_module = import.module_path();
        if !session.is_module_compiled(&dep_module) {
            if let Some(dep_source_path) = session.resolve_module(&dep_module)? {
                let dep_source = std::fs::read_to_string(&dep_source_path)?;
                let dep_ctx = CompileContext {
                    module: dep_module,
                    strategy: ModuleStrategy::Replace,
                    compile_mode: ctx.compile_mode,
                };
                compile_unit(session, &dep_source, &dep_ctx)?;  // recursive
            }
            // If resolve returns None and lib_dirs is empty: import will fail
            // during typecheck (unresolved symbol). This is the test-mode path.
        }
    }

    // Register imports and exports from extracted declarations.
    session.tc.register_imports(&structure.import_specs)?;
    if !structure.export_specs.is_empty() {
        session.tc.register_exports(&structure.export_specs)?;
    }

    // Stage 3: Expand (defmacro interception + macro expansion + begin-flatten)
    let accumulated = session.process_forms_sequentially(remaining)?;

    // Stage 4: Build AST
    let program = cranelisp_frontend::build_program(&accumulated, &mut session.expander)?;

    // Stage 5: Typecheck
    let check_result = session.tc.check(&program, ctx)?;

    // Stages 6-7: Codegen + Execute (existing code, mode-dependent)
    // ... (unchanged from current implementation)

    session.compile_stack.pop();
    Ok(result)
}
```

Acceptance criteria for Step 4a:
- `compile_unit()` takes `&str`, not `&[Sexp]`.
- All seven stages are inside `compile_unit()`.
- Recursive module loading works (an import triggers `compile_unit()` for the dependency).
- Cycle detection reports circular dependencies.
- With empty lib_dirs (test mode), imports that reference external modules fail at typecheck, not during resolution.
- New tests: a multi-form source string with `(defmacro ...)` followed by macro usage compiles correctly through `compile_unit()`.

**Step 4b: Wire REPL through `compile_unit()`.**

Replace `eval_sexp()` → `eval_flattened_forms()` → manual AST build + check + compile/execute with a call to `compile_unit()`. The REPL's `eval()` becomes:

```rust
pub fn eval(&mut self, source: &str) -> Result<ReplResult, CranelispError> {
    // Pre-pipeline interceptions (unchanged):
    // - blank/comment skip
    // - slash commands
    // - snapshot for error recovery

    // Classify the input for REPL-specific routing:
    let sexps = cranelisp_frontend::parse(source)?;
    if is_bare_introspection(&sexps) { return self.introspect_symbol(...); }
    if is_annotation_prefix(&sexps[0]) { return self.eval_annotation_expr(sexps); }

    // Normal compilation — through the unified pipeline.
    // Imports inside the source flow through compile_unit's Stage 2,
    // which recursively loads dependencies via lib_dirs.
    let ctx = CompileContext {
        module: self.current_module.clone(),
        strategy: ModuleStrategy::Additive,
        compile_mode: CompileMode::Interactive,
    };
    let result = compile_unit(&mut self.core, source, &ctx)?;

    // Post-pipeline: display, session persistence, DefCodegen storage
    self.process_compile_result(result, source)
}
```

Acceptance criteria for Step 4b:
- All REPL tests pass through `compile_unit()`.
- `eval_sexp()`, `eval_flattened_forms()` are unused (but not yet deleted).
- REPL imports work through `compile_unit()`'s recursive loading (no separate import handler).
- REPL defmacro works (macro defined in one line, used in the next).
- REPL `(begin ...)` works (multiple forms in one input).
- Bind chain analysis (auto IO scheduling) runs on the AST inside `compile_unit()` (moved from the REPL's per-form loop).
- Session persistence still stores the original sexp for `/source` display. `compile_unit()` returns enough information for this, or the REPL re-parses the source to get the sexp (cheap for REPL-length input).

**Step 4c: Wire `--run` through `compile_unit()`.**

Replace the module graph orchestrator's separate discovery + topo-sort + per-module compilation with a single `compile_unit()` call on the entry file:

```rust
fn run_batch(
    entry_file: &Path,
    session: &mut CompilationSession,
) -> Result<i64, CranelispError> {
    let source = std::fs::read_to_string(entry_file)?;
    let module_path = derive_module_path(entry_file);

    // Inject prelude import if applicable.
    if session.prelude_loaded {
        inject_prelude_import(&mut session.tc, &module_path)?;
    }

    let ctx = CompileContext {
        module: module_path,
        strategy: ModuleStrategy::Replace,
        compile_mode: CompileMode::Interactive, // GOT-indirect for multi-module
    };

    // This recursively loads all transitive dependencies.
    let result = compile_unit(session, &source, &ctx)?;

    // After loading: find main, IO trampoline, exit.
    let main_ptr = session.lookup_main()?;
    run_io_trampoline(main_ptr)
}
```

Acceptance criteria for Step 4c:
- All multi-module batch tests pass.
- The separate module graph discovery pass (`discover_module_graph()`) is eliminated.
- `compile_single_module()` is eliminated — recursive `compile_unit()` replaces it.
- Cache-hit path still works (checked inside `compile_unit()` before running stages).

**Step 4d: Bind chain analysis integration.**

The bind chain analysis (auto IO scheduling) currently runs in three places: `compile_and_run()`, `compile_single_module()`, and `eval_flattened_forms()`. Move it inside `compile_unit()`, between stage 4 (Build AST) and stage 5 (Typecheck):

```rust
// Inside compile_unit(), after build_program():
if !session.scheduling_registry.is_empty()
    && std::env::var("CRANELISP_NO_IO_SCHEDULE").is_err()
{
    apply_bind_chain_analysis(&mut program, &session.scheduling_registry);
}
```

Acceptance criteria for Step 4d:
- Bind chain analysis runs once inside `compile_unit()`, not in callers.
- All IO scheduling tests pass.
- The three caller-side analysis calls are removed.

**Step 5: Delete v1 artifacts**

After Step 4 is complete and all tests pass, delete dead code:

**Step 5a: Delete dead REPL code.**
- Delete `eval_sexp()`, `eval_flattened_forms()`, `compile_and_execute()` from `src/repl/mod.rs`.
- Delete `build_repl_input()`, `build_repl_input_from_sexps()` from `cranelisp-frontend`.
- Delete `build_check_for_backend()` from `src/repl/mod.rs`.
- Delete the separate REPL import handler (imports now flow through `compile_unit()`).

**Step 5b: Delete dead pipeline code.**
- Delete `discover_module_graph()`, `compile_single_module()`, and the topo-sort orchestration from `src/pipeline.rs`.
- Delete `process_and_build_program()` from `CompilationSession` (callers now use `compile_unit()`).
- Delete `build_check_for_backend()` from `src/pipeline.rs`.

**Step 5c: Delete dead type artifacts.**
- Delete `ReplInput` from `cranelisp-types`.
- Delete `ReplCheckResult` from `cranelisp-types`.
- Delete `check_repl_input()` from `cranelisp-typecheck`.
- Delete `check_program()` from `cranelisp-typecheck` (replaced by `check()`).
- Delete `toplevel_to_repl_input()` from `cranelisp-frontend`.

**Step 5d: Final cleanup.**
- Verify no code references deleted types/functions (compiler will catch this).
- Run full test suite.
- Update `design/arch/interfaces.md` to remove references to deleted types.
- Move `src/pipeline_v2.rs` content into `src/pipeline.rs` (or rename the file).

Acceptance criteria for Step 5:
- Zero references to `ReplInput`, `ReplCheckResult`, `check_repl_input`, `check_program`, `build_repl_input`, `build_check_for_backend`.
- Full test suite passes.
- `interfaces.md` reflects only v2 types.

### 8.10 Adapters during transition

During Steps 2-4, thin adapters bridge v2 types to v1 stage implementations:

```rust
// In cranelisp-typecheck, during Step 2:
// check(ctx, program) uses ctx.module as the active module and ctx.strategy to decide
// whether to clear existing state. Internally converts TopLevel::Expr → synthetic defn.
// No new types needed — just routing.

// In binary crate, during Step 3/4:
// compile_unit(session, source, ctx) calls check(ctx, &program).
// No mode parameter on check() — check() always uses multi-pass.
// The CheckResult is the same type (with new optional fields) — backend takes it directly.
```

The key insight is that the *stage implementations* (inference, codegen) do not change. Only the *orchestration* (which function calls which, what types cross the boundary) changes. Adapters are thin routing layers, not type converters.

### 8.11 Risk assessment

- **Step 1** (types): Zero risk. Additive. DONE.
- **Step 2** (check): Low risk. New entry point calling existing logic. DONE.
- **Step 3** (partial orchestration): Low risk. New code, nothing breaks. DONE (partial).
- **Step 4a** (extend compile_unit with recursive loading): Medium risk. The recursive module loading is the most significant change — it replaces the separate discovery + topo-sort mechanism with implicit recursion. Key risk: cycle detection must be correct, and the recursion must handle all edge cases (missing files, cache hits, prelude injection).
- **Step 4b** (REPL switchover): Medium risk. The REPL has pre-pipeline interception logic. Key risk: REPL-specific concerns (defmacro-in-results, original sexp tracking for session persistence, annotation expressions) must still work through compile_unit. The elimination of the separate REPL import handler simplifies this step relative to the previous design.
- **Step 4c** (batch switchover): Medium risk. Replaces the explicit module graph with recursive loading. Key risk: compilation order must produce the same results as the previous topo-sort approach. The recursion guarantees this (dependencies are compiled before dependents), but cache invalidation patterns may differ.
- **Step 4d** (bind chain analysis): Low risk. Mechanical move.
- **Step 5** (cleanup): Zero risk. Mechanical deletion — compiler catches any missed references.

## 9. Multi-Sig `Defn` as Canary

### 9.1 Trace through v2 pipeline

**Source:**
```clojure
(defn size "Return element count"
  ([:Vec v] (vec-len v))
  ([:List l] (list-len l)))
```

**Stage 1 (Parse):** Produces `Sexp::List` with `defn`, `size`, docstring, two variant lists.

**Stage 2 (Extract):** No module declarations — passes through unchanged.

**Stage 3 (Expand):** Not a macro — passes through unchanged.

**Stage 4 (Build AST):** `build_top_level` recognizes the multi-variant syntax and produces:
```
TopLevel::Defn(Defn {
    name: "size",
    docstring: Some("Return element count"),
    variants: [
        DefnVariant { params: ["v"], annotations: [Some(Vec)], body: (vec-len v) },
        DefnVariant { params: ["l"], annotations: [Some(List)], body: (list-len l) },
    ],
    visibility: Public,
    span: ...,
})
```

**Stage 5 (Typecheck):**

Pass 1: Register `size` as an `Overloaded` defn with two variants. Register each variant's signature with mangled names (`size$Vec`, `size$List`). Fresh type vars for each variant's params.

Pass 2: Check each variant's body. `(vec-len v)` unifies `v` with `Vec`, infers return type `Int`. `(list-len l)` unifies `l` with `List`, infers return type `Int`. Both variants return `Int` — the overload base records return type `Int`.

Pass 3–5: Constrained fn detection, monomorphisation, auto-curry — standard passes.

Result: `CheckResult` contains `method_resolutions` with `SigDispatch` entries at call sites, and the expanded variant defns are either in the program (as synthesized `Defn` entries) or in `mono_defns`. When entered at the REPL, `display` is populated with the overloaded type signature.

This is the same pipeline whether the input is a batch program containing `size` among many definitions, or a single REPL line defining `size` alone. The multi-pass structure degenerates correctly on one form.

**Stage 6 (Codegen):**

The backend sees the expanded variant defns (via CheckResult or the program). Each variant is compiled as a regular function with its mangled name. Call sites use `SigDispatch` to dispatch to the correct variant. No multi-sig-specific codegen needed — the expansion happened in typecheck.

**Stage 7 (Execute):**

- REPL: displays `:Multi size :: (Fn [Vec] Int) | (Fn [List] Int)` using DisplayInfo.
- Batch: `(size my-vec)` dispatches to `size$Vec` at runtime.

### 9.2 Validation

The multi-sig trace demonstrates:
1. **One path** — single-sig and multi-sig both flow through `TopLevel::Defn`. Every `match` on `TopLevel` handles function definitions in one arm — multi-sig handling is a branch within that arm (check `defn.is_multi_sig()`), not a separate arm that can be forgotten.
2. **No silent skip** — because there is no separate `DefnMulti` variant, it is structurally impossible to handle `Defn` and silently skip multi-sig. The v1 code had exactly this bug: `collect_defns`, `compile_checked_program`, and `check_repl_input` all matched `TopLevel::Defn` but silently ignored `TopLevel::DefnMulti`.
3. **No adapter** — CheckResult goes directly to the backend.
4. **No mode parameter** — the multi-pass pipeline (register in Pass 1, check in Pass 2) works identically for a batch program with many forms or a REPL line with one form.

## 10. Unified Pipeline Flow Diagram

### 10.1 Per-module flow (current, REPL, and single-module batch)

```
             Source text (batch file or REPL line)
             + CompileContext { module, strategy, compile_mode }
                                      |
                                      v
                            +---------+---------+
                            |    1. Parse       |  cranelisp-frontend
                            |    -> Vec<Sexp>   |
                            +---------+---------+
                                      |
                                      v
                            +---------+---------+
                            |    2. Extract     |  cranelisp-frontend
                            |    -> ModuleDecls |  (mod, import, export, platform)
                            |    -> Vec<Sexp>   |  (remaining forms)
                            +---------+---------+
                                      |
                                      v
                            +---------+---------+
                            |    3. Expand      |  MacroExpander trait
                            |    defmacro       |  (frontend defines, binary implements)
                            |    macro calls    |
                            |    begin flatten  |
                            |    -> Vec<Sexp>   |
                            +---------+---------+
                                      |
                                      v
                            +---------+---------+
                            |    4. Build AST   |  cranelisp-frontend
                            |    -> Vec<TopLevel>|
                            +---------+---------+
                                      |
                                      v
                            +---------+---------+
                            |    5. Typecheck   |  cranelisp-typecheck
                            |    check(ctx, ..) |  ctx.module = target
                            |    -> CheckResult |  ctx.strategy = Add/Replace
                            +---------+---------+
                                      |
                                      v
                      +---------------+---------------+
                      |                               |
                      v                               v
           ctx.compile_mode           ctx.compile_mode
             = Batch                    = Interactive
           (single-file test)          (REPL, multi-module)
                      |                               |
                      v                               v
                            +---------+---------+
                            |    6. Codegen     |  cranelisp-backend
                            |    compile defns  |
                            |    -> JIT / .o    |
                            +---------+---------+
                                      |
                                      v
                            +---------+---------+
                            |    7. Execute     |  cranelisp (binary)
                            |    call main /    |
                            |    eval + display |
                            +---------+---------+
```

### 10.2 Multi-module batch flow (parallel codegen, future)

When compiling a multi-module project, the recursive module walk (§8.3) naturally typechecks modules in dependency order. The future two-pass model (§8.4) separates Pass 1 (stages 1–5, sequential recursive typecheck) from Pass 2 (stage 6, parallel codegen). The `CodegenTarget` determines what each parallel worker produces. See §12.5 for the parallelism properties that enable this.

```
     Pass 1: Recursive module walk (stages 1-5)
                      |
   ═══════════════════╪══════════════════════════
   Typecheck          │  (sequential, recursive topo order)
   ═══════════════════╪══════════════════════════
                      |
        for each module (topo order via recursion):
            Stages 1-5 (Parse → Typecheck)
            GOT slots assigned as functions are registered
            (ensure_slot_for — reuses existing, allocates new)
                      |
                      v
        Vec<(ModuleFullPath, CheckResult)>
        + ModuleCodegenState has stable slot assignments
                      |
   ═══════════════════╪══════════════════════════
   Pass 2: Codegen    │  (parallel across modules)
   ═══════════════════╪══════════════════════════
                      |
        ┌─────────────┼─────────────┐
        │             │             │
     Module A      Module B      Module C
     (own Jit/     (own Jit/     (own Jit/
      ObjectModule) ObjectModule) ObjectModule)
     Stage 6       Stage 6       Stage 6
        │             │             │
        └─────────────┼─────────────┘
                      |
                      v
        JitAndCache: Finalize JITs, write ptrs into GOT, bg .o writes
        ObjectOnly:  Collect .o paths for linker
                      |
                      v
                 Stage 7: Execute (JitAndCache only)
```

## 11. Sketch Comparison

### 11.1 Sketch pipeline structure

The sketch has the same dual-pipeline defect documented in `pipeline-convergence-review.md`. It defines `TopLevel` and `ReplInput` as structurally identical enums with a mechanical conversion function. `check_program` and `check_repl_input` are parallel implementations with duplicated logic.

The v2 pipeline deliberately diverges from the sketch's structure. The sketch's type duplication was listed in its own audit as a debt (`sketch/CLAUDE.md`: "Dual batch/REPL pipelines with divergent code paths"). The v2 design eliminates this debt by construction.

### 11.2 Sketch solutions preserved

The v2 pipeline preserves the sketch's *solutions to language-level problems*:

- **Synthetic defn wrapping for expressions**: The sketch wraps REPL expressions in a zero-arg function for compilation. v2 does the same, but moves the wrapping into the typecheck stage (inside `check()`) rather than the backend.
- **Multi-pass checking**: The sketch's `check_program` uses multiple passes (register first, check second). v2 preserves this as the single `check()` pipeline — always multi-pass, no mode parameter needed.
- **Registration primitives**: The sketch's `register_type_def`, `register_trait_decl`, etc. are shared between batch and REPL paths. v2 preserves this — the shared primitives remain the same.
- **Multi-sig variant expansion**: The sketch expands multi-sig defns into mangled variants during type checking. v2 follows the same approach.

### 11.3 Sketch solutions rejected

- **Separate types for batch/REPL input**: Replaced by unified `TopLevel`.
- **Adapter functions**: `build_check_for_backend` eliminated.
- **Separate typecheck entry points**: Replaced by `check()` — a single entry point with no mode parameter.

## 12. Future Accommodation

### 12.1 `loop`/`recur`

When `loop`/`recur` arrives, it adds `Loop` and `Recur` variants to `Expr` (they are expression forms, not top-level definitions). No changes to `TopLevel`, `CheckResult`, or the pipeline stages needed.

### 12.2 ANF / defunctionalised continuations

If an ANF transformation pass is added, it slots in between typecheck (Stage 5) and codegen (Stage 6) as a new Stage 5.5. The pipeline's linear structure accommodates this without redesign.

### 12.3 Mutual recursion loop-merge

The call graph's SCC detection (`sccs()`) enables identifying groups of mutually recursive functions. The implementation is `todo!()` until needed. The data structure (adjacency list with reverse index) is already sufficient.

### 12.4 Incremental recompilation

The call graph's reverse index (`reverse_index()`) maps callee → callers. When a function changes, its callers are identified and recompiled. Module-level granularity comes from filtering the reverse index by module path.

### 12.5 Parallel codegen: the GOT as persistent session state

This section describes the future parallel codegen optimisation. The two-pass model (§8.4) and `CodegenTarget` enum make this possible; this section explains the underlying invariants and thread-safety properties. The current implementation compiles one module at a time — parallel codegen is future work.

#### 12.5.1 `ModuleCodegenState` is session infrastructure

The GOT is not a pipeline output — it is persistent session state that lives for the lifetime of the compiler session. The implementation (`cranelisp-backend/src/got.rs`) makes this clear:

- `got_table: Box<[*const u8; GOT_TABLE_SIZE]>` — function pointer array, lives for the session
- `next_got_slot: usize` — monotonically increasing, never resets
- `def_codegen: HashMap<Symbol, DefCodegen>` — maps names to slot indices and code pointers

`ensure_slot_for(name)` reuses existing slots and allocates new ones at the end. Slots are assigned when functions are first registered — during typecheck or when a new definition is encountered. By the time codegen runs, all slots are already assigned.

The key invariant: **GOT slot indices are stable**. Once a function is assigned slot N, it keeps slot N forever. Compiled code has the slot index hardcoded as an immediate offset from the GOT base pointer. Moving a slot would invalidate all code that calls that function.

#### 12.5.2 Why codegen is parallelisable

Codegen for module A needs:
1. **Module A's `CheckResult`** — method resolutions, expr types, type defs (read-only, self-contained)
2. **GOT slot assignments** — the `def_codegen` map in `ModuleCodegenState` that maps function names to slot indices (read-only by the time codegen starts, because slots were assigned during typecheck registration)

Multiple modules can be compiled in parallel because they are reading stable data, not mutating shared state. The only mutation is writing the resulting code pointer into the GOT slot, which happens after codegen completes and can be done sequentially.

Pass 1 (stages 1–5, sequential recursive typecheck) settles all GOT slot assignments. Pass 2 (stage 6, parallel) fans out across modules. The `CodegenTarget` (§8.4) determines what each worker produces: `JitAndCache` workers create `Jit` instances and produce live function pointers + background `.o` writes; `ObjectOnly` workers create `ObjectModule` instances and produce `.o` files directly.

```
     Recursive module walk (Pass 1: stages 1-5)
                      |
   ═══════════════════╪══════════════════════════
   Pass 1: Typecheck  │  (sequential, recursive topo order)
   ═══════════════════╪══════════════════════════
                      |
        for each module (topo order via recursion):
            Stages 1-5 (Parse → Typecheck)
            GOT slots assigned via ensure_slot_for()
                      |
                      v
        Vec<(ModuleFullPath, CheckResult)>
        + ModuleCodegenState with stable slot assignments
                      |
   ═══════════════════╪══════════════════════════
   Pass 2: Codegen    │  (parallel across modules)
   ═══════════════════╪══════════════════════════
                      |
        CodegenTarget::JitAndCache:
          Each module creates its own Jit instance
          Produces live function pointers
          Queues background .o write (§16.12)
        CodegenTarget::ObjectOnly:
          Each module creates its own ObjectModule instance
          Produces .o file directly (hot path)
                      |
                      v
        JitAndCache: Finalize JITs, write ptrs into GOT (sequential)
        ObjectOnly:  Collect .o paths for linker
```

There is no separate "GOT declaration phase" or module graph discovery pass. GOT slot allocation happens naturally as functions are registered during the recursive typecheck walk. The separation between typecheck and codegen is already the separation that enables parallelism.

#### 12.5.3 Thread safety for parallel codegen

For parallel codegen, the following constraints apply:

| Type | Status | Notes |
|------|--------|-------|
| `CheckResult` | `Send + Sync` (automatic) | All fields are owned, plain data. Read-only during codegen. |
| `Program` (`Vec<TopLevel>`) | `Send + Sync` (automatic) | Plain data throughout. Read-only during codegen. |
| `Jit` (wraps `JITModule`) | NOT `Send` or `Sync` | Not shared — each thread creates its own `Jit` instance. |
| `ModuleCodegenState` | Manual `Send + Sync` (has raw pointers) | Slot indices are read-only during codegen. Code pointer writes happen sequentially after codegen finishes. |

Each parallel codegen task creates its own `Jit` instance. After all tasks complete, the orchestration layer finalizes each `Jit` and writes the resulting code pointers into the shared GOT table sequentially.

#### 12.5.4 Incremental recompilation

GOT slot stability is the key invariant for incremental recompilation. When a function is recompiled:

1. It gets the **same GOT slot** (stable — `ensure_slot_for` returns the existing slot).
2. A **new code pointer** is written into that slot.
3. All callers with GOT-indirect calls **automatically see the new code** — no relinking needed.
4. Callers with inlined code need recompilation (the call graph's `reverse_index()` identifies them).

The full incremental recompilation flow:

1. **Detect change**: Module C's source file changes.
2. **Re-typecheck**: Re-run `check()` for module C with `ModuleStrategy::Replace`. The `CheckResult` for C is updated. Any new functions get new GOT slots via `ensure_slot_for`. Existing functions keep their existing slots.
3. **Identify affected callers**: Use `call_graph.reverse_index()` to find functions in other modules that call functions in C. If C's function signatures have not changed, no callers need recompilation — only C's GOT slots need updating with new code pointers.
4. **Re-codegen**: Recompile C (and any affected callers identified in step 3). Write new code pointers into the GOT slots.

Removed functions' slots become dead but are not reclaimed — slot indices are stable. New functions get new slots at the end of the allocation sequence.

#### 12.5.5 REPL interaction

The REPL operates per-form and is fundamentally incremental. Each `defn` flows through the same mechanism:

1. Typecheck the form — GOT slot assigned via `ensure_slot_for` (reuses existing slot if redefining).
2. Compile the function.
3. Write the code pointer into the GOT slot via `update_def`.

Redefining a function in the REPL works because the GOT slot is stable: the new code pointer replaces the old one, and all existing callers (which use GOT-indirect calls) automatically dispatch to the new implementation.

The `cross_module_got` field on `CompileContext` remains for the REPL: when module B calls a function from module A, the REPL needs to know which GOT table and slot to use.

#### 12.5.6 Cache serialisation

Between sessions, `meta.json` in the module cache serialises slot assignments (via `DefCodegen`'s `got_slot` field) so that cached `.o` files reference correct offsets when reloaded. This works because `DefCodegen` is `Serialize + Deserialize` and the slot index is a plain `usize`.

#### 12.5.7 Sketch comparison

The sketch processes modules sequentially: typecheck, codegen, and GOT population happen one module at a time via `compile_module_graph`. The sketch's `ModuleCodegenState` (same name) uses the same `ensure_slot_for` / `update_def` pattern for slot stability.

The v2 design diverges from the sketch by recognising that the sequential typecheck + stable GOT slots already provide the invariants needed for parallel codegen — no new types or phases are required. The sketch does not exploit this property because it never separates typecheck from codegen at the orchestration level.

#### 12.5.8 Implementation timeline

This is a future capability. The v2 spike does not implement parallel codegen. The design ensures the existing types accommodate it without redesign:

- `ModuleCodegenState` already provides stable slot assignments — no new type needed.
- `CompileContext.got_slots` / `got_base_ptr` already carry the information codegen needs.
- `CodegenTarget` (§8.4) already distinguishes JIT vs ObjectModule output — each parallel worker uses the same target.
- The main implementation work is: (a) separating the recursive module walk to run stages 1-5 only (Pass 1, see §8.4), (b) collecting the `CheckResult` from each module during the typecheck walk, (c) making each module's codegen independent (own `Jit` or `ObjectModule` instance per `CodegenTarget`), (d) adding `rayon::par_iter` for the codegen loop.

The parallel codegen capability can be adopted incrementally: the `CodegenTarget` dispatch and two-pass structure (§8.4) clarify the stage separation even without parallelism; parallel dispatch is added when benchmarking shows it matters.

## 14. Compilation Context

### 14.1 The problem

The v2 pipeline has `check(&[TopLevel])` but no parameter telling the pipeline:

1. **Which module** the forms belong to — what module are definitions registered into?
2. **Additive vs replacement** — is this adding to an existing module (REPL line, incremental) or defining the complete contents of a module (loading a file)?

In v1, both are implicit mutable state on `TypeChecker`: `current_module_path` is set/restored around every compilation, and whether to clear existing state is determined by caller convention. This produces a save/set/restore pattern that appears ~20 times across `pipeline.rs` and `repl/mod.rs`, is error-prone (forgetting to restore on error paths), and makes it impossible to determine the compilation target from the function signature alone.

### 14.2 Scenarios

| Scenario | Target module | Strategy | CompileMode | Notes |
|----------|--------------|----------|-------------|-------|
| REPL line | `tc.current_module` (set by `/mod`) | Additive | Interactive | Definitions extend the current module |
| `--run` entry file | Derived from file path | Replace | Interactive | Entry module's contents = file's contents |
| Recursive dependency load | The imported module | Replace | Interactive | Recursive `compile_unit()` call from Stage 2 |
| Hot-reload | Module being reloaded | Replace | Interactive | File changed; invalidate + re-load |
| Test helper (`compile_and_run`) | `"user"` | Additive | Batch | No lib_dirs; self-contained, direct calls |
| `begin` expansion | Same as enclosing context | (inherited) | (inherited) | Multiple forms, same module |

### 14.3 Design

```rust
/// Compilation context: makes module target and strategy explicit.
///
/// Passed to `check()` and `codegen()` as an immutable parameter.
/// Constructed by the binary crate's orchestration layer before
/// invoking the pipeline. Not stored as mutable state on TypeChecker.
///
/// Lives in `cranelisp-types` (stable data, no logic).
#[derive(Debug, Clone)]
pub struct CompileContext {
    /// The module that definitions from this compilation unit are registered into.
    pub module: ModuleFullPath,

    /// Whether this compilation unit defines the module's complete contents
    /// (Replace) or adds to existing state (Additive).
    pub strategy: ModuleStrategy,

    /// Controls codegen strategy (GOT-indirect vs direct calls).
    pub compile_mode: CompileMode,

    /// Controls codegen output: JIT to memory + background .o (JitAndCache)
    /// or ObjectModule to .o directly (ObjectOnly). See §8.4, §16.2.
    pub codegen_target: CodegenTarget,
}

/// Whether a compilation unit replaces or extends the target module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleStrategy {
    /// File load: these forms ARE the module. Clear existing definitions
    /// for this module before registering new ones. Used when loading a
    /// `.cl` file or hot-reloading a changed file.
    Replace,

    /// REPL line: add to existing module state. Existing definitions are
    /// preserved. A re-definition of an existing name overwrites it (same
    /// as v1 REPL behavior). Used for REPL input and incremental
    /// compilation.
    Additive,
}
```

### 14.4 How stages use the context

**Stage 5 (Typecheck):** `check()` receives `&CompileContext`. At the start of the multi-pass pipeline:

1. If `ctx.strategy == Replace`, clear all existing symbol table entries, type defs, trait decls, and trait impls for `ctx.module`. This ensures the module's compiled state reflects exactly the forms in this compilation unit.
2. Set the active module to `ctx.module` so that all registrations (type defs, trait decls, defn signatures) go into the correct module.
3. Proceed with the normal multi-pass pipeline.

The TypeChecker no longer exposes `set_current_module()` / `current_module_path()` as public API. The active module is derived from the `CompileContext` passed to `check()`. The TypeChecker may still track the active module internally during checking, but it is set from `ctx.module` at the entry point, not by the caller.

**Stage 6 (Codegen):** `codegen()` receives `&CompileContext`. It uses `ctx.codegen_target` to determine what to produce: `JitAndCache` compiles to JIT memory (stage 6a) and queues a background `.o` write (stage 6b); `ObjectOnly` compiles directly to `.o` (stage 6a only). Within JIT codegen, `ctx.compile_mode` controls the GOT vs direct-call decision (same as before). `ctx.module` determines which module's codegen state (GOT table, def_codegen map) to update.

**Stages 1-4 (Parse, Extract, Expand, Build AST):** These stages do not need the context. They are pure transformations on syntax that do not interact with module state.

**Stage 7 (Execute):** The binary crate's orchestration layer uses `ctx.compile_mode` to decide whether to call `main`, display a REPL result, or do nothing (module loading). It already knows the mode because it constructed the context.

### 14.5 Construction sites

The `CompileContext` is constructed at three sites:

**1. REPL line evaluation (`src/repl/mod.rs`)** — the external caller for interactive input.

```rust
let ctx = CompileContext {
    module: self.current_module.clone(),  // set by /mod command
    strategy: ModuleStrategy::Additive,
    compile_mode: CompileMode::Interactive,
    codegen_target: CodegenTarget::JitAndCache,
};
let result = compile_unit(&mut self.core, source, &ctx)?;
```

The REPL session owns `current_module: ModuleFullPath` (moved out of TypeChecker). The `/mod` command updates this field on the REPL session, not on the TypeChecker.

**2. Batch entry (`--run`)** — the external caller for batch execution.

```rust
let ctx = CompileContext {
    module: derive_module_path(entry_file),
    strategy: ModuleStrategy::Replace,
    compile_mode: CompileMode::Interactive, // GOT-indirect for multi-module
    codegen_target: CodegenTarget::JitAndCache,
};
let result = compile_unit(session, &source, &ctx)?;
```

**2b. Link entry (`--link`)** — the external caller for executable generation.

```rust
let ctx = CompileContext {
    module: derive_module_path(entry_file),
    strategy: ModuleStrategy::Replace,
    compile_mode: CompileMode::Interactive,
    codegen_target: CodegenTarget::ObjectOnly,
};
let result = compile_unit(session, &source, &ctx)?;
```

**3. Recursive module loading (inside `compile_unit()`)** — the internal construction site for dependency resolution.

```rust
// When compile_unit encounters an unresolved import during Stage 2:
let dep_ctx = CompileContext {
    module: dep_module_path.clone(),
    strategy: ModuleStrategy::Replace,
    compile_mode: ctx.compile_mode,       // inherit from parent
    codegen_target: ctx.codegen_target,   // inherit from parent
};
compile_unit(session, &dep_source, &dep_ctx)?;  // recursive
```

Each recursive call creates its own `CompileContext` on the stack. No save/restore of module state is needed — the context is a parameter, not mutable state. The recursion naturally handles nested dependencies: module A imports B, B imports C, so C is compiled first (innermost recursive call returns first).

### 14.6 Eliminating save/restore

The v1 save/restore pattern:

```rust
// v1: ~20 occurrences across pipeline.rs and repl/mod.rs
let saved_module = session.tc.current_module_path().clone();
session.tc.set_current_module(new_module);
// ... compile ...
session.tc.set_current_module(saved_module);
```

With `CompileContext`, this becomes:

```rust
// v2: no save/restore needed
let ctx = CompileContext {
    module: new_module,
    strategy: ModuleStrategy::Replace,
    compile_mode: CompileMode::Interactive,
    codegen_target: CodegenTarget::JitAndCache,
};
tc.check(&ctx, &program)?;
```

The context is a stack-allocated value passed by reference. Recursive module loading is naturally handled: each recursive call creates its own `CompileContext` on the stack. No mutable state to save or restore.

### 14.7 Sketch comparison

The sketch uses the same `set_current_module` / `current_module_path` pattern as v1. It has no equivalent of `CompileContext`. The save/restore pattern appears in `compile_module_graph`, `load_module_into_session`, `recompile_module`, and REPL import handling.

The v2 `CompileContext` replaces implicit mutable state with an explicit parameter, following the same principle that motivated the elimination of `CheckMode` (§5): make differences explicit in the interface, not hidden in mutable state. The sketch's approach works but is fragile -- a missing restore on an error path silently corrupts the module context for subsequent compilations.

### 14.8 Impact on `TypeChecker` API

The following TypeChecker methods change:

| v1 method | v2 replacement | Notes |
|-----------|---------------|-------|
| `set_current_module(path)` | Removed (public) | Active module derived from `ctx.module` |
| `current_module_path()` | Removed (public) | Callers use the context they constructed |
| `check_repl_input(input)` | `check(ctx, program)` | Already planned for deletion |
| `check_program(program)` | `check(ctx, program)` | Already planned for deletion |

The TypeChecker may retain a private `active_module: ModuleFullPath` field that is set from `ctx.module` at the start of `check()`. But this is an internal implementation detail, not a public API.

### 14.9 Interaction with `begin` expansion

A `(begin ...)` form at the REPL expands to multiple top-level forms. These all share the same `CompileContext` -- they are part of a single pipeline invocation. The context's `module` and `strategy` apply uniformly to all forms in the expansion. This is correct: a `begin` block at the REPL adds multiple definitions to the current module (Additive), while a `begin` block in a file adds them to the file's module (Replace, as part of the file's full contents).

### 14.10 `ModuleStrategy::Replace` semantics

`Replace` means: before registering any definitions from this compilation unit, clear the module's existing state. Specifically:

- Clear the module's `SymbolTable` (all `ModuleEntry` entries for this module).
- Clear the module's type definitions, trait declarations, and trait implementations.
- Clear the module's `ModuleCodegenState` (GOT slots, code pointers).

This is equivalent to "delete the module and re-create it from scratch." It ensures that removing a definition from a file and reloading causes the definition to disappear, rather than persisting as stale state.

The clear happens at the start of `check()`, before Pass 1 registration. Imports from other modules are not cleared -- they are re-registered from the `ModuleDecls` extracted in Stage 2.

## 13. Open Questions

1. **Shared vs per-module GOT table in parallel codegen.** §12.5 describes parallel codegen reading stable slot assignments from `ModuleCodegenState`. The current design uses per-module GOT tables. An alternative for batch compilation is a single shared GOT table whose base address is baked into all modules' IR. The shared table is simpler (one allocation, one base pointer) but limits the program to `GOT_TABLE_SIZE` total functions. Per-module tables scale better but require the `CrossModuleGot` indirection. Decision deferred until parallel codegen is implemented.

## 15. Remaining v1 Paths

This section provides prescriptive design for v1 code paths not yet covered by the `compile_unit()` migration in §8.9. Each subsection describes the current v1 implementation, the v2 design, the concrete migration steps, and the risks.

### 15.1 Trace and run-tests in REPL

#### 15.1.1 Current implementation

The REPL has special handling for two expression forms that manipulate GOT entries around compilation and execution:

**`(trace expr)`** — When the REPL detects a `(trace ...)` form in the input expression (via `expr_contains_trace()`), it performs three pre/post actions around compilation:

1. **Pre-compile: build traced function info.** `build_traced_fns()` iterates all GOT entries with code pointers and type information, producing a `Vec<TracedFnInfo>` that the backend uses to generate wrapper functions. These wrappers intercept calls via GOT-swap: the wrapper saves the original GOT entry, replaces it with the tracing wrapper's code pointer, and restores it after the traced expression completes.

2. **Pre-execute: set display state.** `set_trace_display_state()` sets a thread-local `Cell<*const TraceDisplayState>` that the JIT-callable `repl_trace_format` function reads to access `type_defs` and `type_modules` for value formatting. The `repl_trace_format` function is registered as an extra JIT symbol to override the runtime's fallback `cranelisp_trace_format`.

3. **Post-execute: clear display state.** `clear_trace_display_state()` nulls the thread-local pointer.

The compilation itself goes through `compile_expr_with_traced_fns()` in `src/repl/trace.rs`, which creates a fresh `Jit`, declares intrinsics, wraps the expression in a synthetic zero-arg `Defn`, and compiles it with `traced_fns` set on the compile context. This is a parallel compilation path — it replicates the zero-arg wrapping and Jit setup that `compile_unit()` does internally.

**`(run-tests init pass-fn fail-fn)`** — This is an `Expr::RunTests` AST node. `expr_contains_trace()` returns `true` for `RunTests` because the test discovery mechanism uses the same GOT infrastructure. The `/run-tests` slash command (`src/repl/run_tests.rs`) is a separate, simpler mechanism that discovers `test-*` functions directly from GOT entries and calls their code pointers — no compilation involved.

#### 15.1.2 v2 design

The GOT manipulation is a **pre/post concern around pipeline invocation**, not part of the compilation pipeline itself. `compile_unit()` compiles the expression; the REPL wraps the GOT entries before and restores them after. This separation is already present in the v1 code — the issue is that `compile_expr_with_traced_fns()` replicates pipeline internals instead of calling through `compile_unit()`.

The v2 design has three parts:

**Part A: Trace info is a compile_unit parameter, not a parallel path.**

`compile_unit()` already receives a `CompileContext`. Trace information can be passed as an optional field on the session or as an additional parameter to `compile_unit()`. The preferred approach is a session-level field:

```rust
// On CompilationSession:
pub traced_fns: Option<Vec<TracedFnInfo>>,
pub extra_jit_symbols: Vec<(String, *const u8)>,
```

Before calling `compile_unit()`, the REPL sets `session.traced_fns` and adds `repl_trace_format` to `session.extra_jit_symbols`. `compile_unit()` passes these through to its internal codegen step. After the call returns, the REPL clears both fields.

This eliminates the parallel compilation path in `compile_expr_with_traced_fns()` entirely. The trace-specific compilation (wrapper generation, GOT-swap code emission) remains in the backend, triggered by the presence of `traced_fns` on the session — it is not duplicated in the REPL.

**Part B: Display state lifecycle is REPL-owned.**

`set_trace_display_state()` and `clear_trace_display_state()` remain in `src/repl/trace.rs`. They bracket the *execution* of the compiled expression (the `unsafe { compiled.execute() }` call), not the compilation. Since `compile_unit()` owns stage 7 (Execute), the REPL must either:

1. Set display state before calling `compile_unit()` and clear it after (simple, slightly wasteful — display state is active during compilation when it is not needed), or
2. Split execution out of `compile_unit()` — have `compile_unit()` return a callable handle instead of executing immediately.

Option 1 is correct for the current design. The display state is a thread-local `Cell` with negligible cost. Setting it before `compile_unit()` and clearing it after is safe because `repl_trace_format` is only called during JIT execution (stage 7), and the display state is valid for the entire REPL eval call.

**Part C: `/run-tests` slash command is unchanged.**

The `/run-tests` slash command (`handle_run_tests`) does not compile anything — it discovers test functions from GOT entries and calls them directly. It is entirely outside the compilation pipeline and requires no changes.

The `Expr::RunTests` AST node (the `(run-tests ...)` special form) flows through `compile_unit()` like any other expression. The backend's `RunTests` codegen already handles the GOT manipulation internally. The REPL's only responsibility is ensuring `traced_fns` is populated (because `expr_contains_trace` returns `true` for `RunTests`).

#### 15.1.3 Migration step

1. Add `traced_fns: Option<Vec<TracedFnInfo>>` and `extra_jit_symbols: Vec<(String, *const u8)>` to `CompilationSession`.
2. Modify `compile_unit()` to pass `session.traced_fns` and `session.extra_jit_symbols` through to codegen.
3. In `ReplSession::execute_expr()`, replace the call to `compile_expr_with_traced_fns()` with:
   - Set `session.traced_fns` and `session.extra_jit_symbols` if `has_trace`.
   - Set trace display state.
   - Call `compile_unit()`.
   - Clear trace display state.
   - Clear `session.traced_fns` and `session.extra_jit_symbols`.
4. Delete `compile_expr_with_traced_fns()` and `TracedCompiledExpr` from `src/repl/trace.rs`.

**Acceptance criteria:**
- `(trace (factorial 5))` produces the same trace output through `compile_unit()`.
- `(run-tests ...)` works through `compile_unit()`.
- `/run-tests` slash command is unchanged and still works.
- No parallel Jit creation in `src/repl/trace.rs` — all compilation flows through `compile_unit()`.

#### 15.1.4 Risk

**Medium.** The trace wrapper generation in the backend depends on `traced_fns` being available during codegen. The current path sets it on a local `CompileContext` struct; the v2 path must ensure it reaches the same backend code. The risk is that the backend's trace codegen expects to find `traced_fns` in a location that `compile_unit()` does not populate. Mitigation: verify the backend's `trace_codegen` entry point and ensure the session fields are threaded through.

### 15.2 `build_check_for_backend()` elimination

#### 15.2.1 Current implementation

`build_check_for_backend()` exists in two places:

1. **`src/pipeline.rs` line 990** — a free function.
2. **`src/repl/mod.rs` line 1330** — a method on `ReplSession`.

Both do the same thing: clone every field of a `CheckResult` into a new `CheckResult`, with two differences from a pass-through copy:
- `mono_defns` is set to `Vec::new()` (empty) instead of being cloned. The comment says "MonoDefn is not Clone; backend handles mono."
- `display` is set to `None`.

#### 15.2.2 v2 design

This function is an adapter that exists because the v1 architecture had two structurally identical types (`CheckResult` and the now-deleted `ReplCheckResult`). With the unified `CheckResult` (§4), the backend already receives `CheckResult` directly and ignores the `display` field.

The function can be deleted outright. The two concerns it addressed are handled differently:

- **`display: None`** — The backend ignores `CheckResult.display`. No stripping is needed. The field is `Option<DisplayInfo>` and the backend never reads it.
- **`mono_defns: Vec::new()`** — This is the only non-trivial behavior. The function empties `mono_defns` because the REPL compiles monomorphised definitions separately via `compile_mono_defns()` before compiling the expression. In the v2 pipeline, `compile_unit()` handles mono defn compilation as part of its codegen stage (stage 6). The caller does not need to strip mono defns from the CheckResult — `compile_unit()` processes them internally.

**Verdict: delete both copies.** Callers pass `CheckResult` directly to codegen. The `mono_defns` separation is an internal detail of `compile_unit()`'s codegen stage.

#### 15.2.3 Migration step

1. Remove calls to `build_check_for_backend()` in `ReplSession::execute_expr()` and any other callers. Pass `check_result` directly instead.
2. Delete `build_check_for_backend()` from `src/pipeline.rs`.
3. Delete `build_check_for_backend()` from `src/repl/mod.rs`.
4. Verify that `compile_unit()`'s codegen stage compiles `mono_defns` before the main expression.

**Acceptance criteria:**
- Zero references to `build_check_for_backend` in the codebase.
- All REPL tests pass (constrained polymorphic functions still monomorphise correctly).
- All batch tests pass.

#### 15.2.4 Risk

**Low.** The function is a mechanical field-by-field clone with two overrides. The `display: None` override is unnecessary (backend ignores it). The `mono_defns: Vec::new()` override must be verified: if any call site relied on the stripping to prevent double-compilation of mono defns, that call site needs adjustment. The `compile_unit()` codegen stage must compile mono defns exactly once. Mitigation: check that `compile_unit()`'s codegen processes `check_result.mono_defns` and that no separate `compile_mono_defns()` call exists after `compile_unit()` returns.

### 15.3 `load_module_into_session()` in REPL

#### 15.3.1 Current implementation

`load_module_into_session()` in `src/pipeline.rs` (line 2200) is called from two sites in `src/repl/mod.rs`:

1. **REPL import handling** (line 312) — when a REPL line contains `(import [some.module [...]])` and the root module is not yet loaded, the REPL calls `load_module_into_session()` to load it before the import can resolve.
2. **Auto-loading qualified references** (line 854) — when a REPL expression references a qualified name like `core.option/Some` and the module is not loaded, lazy auto-loading triggers `load_module_into_session()`.

The function performs:
1. Resolve the module file via project root + lib dirs.
2. `discover_module_graph()` — walk the file system to find all transitive dependencies.
3. `toposort()` — order modules by dependency.
4. For each module in topological order (skipping already-loaded ones):
   - Parse, extract, expand, build AST, typecheck, codegen via `compile_single_module()` or the inline loop.

This is a self-contained mini-pipeline with its own discovery, ordering, and per-module compilation loop — exactly the kind of parallel path that the v2 design eliminates.

#### 15.3.2 v2 design

Replace `load_module_into_session()` with a single `compile_unit()` call. The recursive module loading inside `compile_unit()` (§8.3) handles everything that the explicit graph discovery + topo-sort does:

```rust
// REPL: when module "core.option" needs loading
fn load_module(session: &mut CompilationSession, module_path: &ModuleFullPath) -> Result<(), CranelispError> {
    let source_path = session.resolve_module(module_path)?;
    let source = std::fs::read_to_string(&source_path)?;
    let ctx = CompileContext {
        module: module_path.clone(),
        strategy: ModuleStrategy::Replace,
        compile_mode: CompileMode::Interactive,
    };
    compile_unit(session, &source, &ctx)?;
    Ok(())
}
```

`compile_unit()`'s Stage 2 (Extract) encounters the module's own imports and recursively loads them. The topological ordering is implicit: dependencies are compiled before dependents because the recursive call returns before the caller's Stage 3 begins. No explicit `discover_module_graph()` or `toposort()` is needed.

Both REPL call sites replace their `load_module_into_session()` call with this `load_module()` helper (or inline the equivalent). The save/restore of `current_module_path()` that currently surrounds these calls is eliminated — `compile_unit()` uses `CompileContext` (§14), so no mutable module state needs saving.

#### 15.3.3 Migration step

1. Implement `CompilationSession::resolve_module(module_path) -> Result<PathBuf, CranelispError>` that searches project root + lib dirs for the module file. (This logic already exists inside `load_module_into_session`; extract it.)
2. At both REPL call sites, replace `load_module_into_session(...)` with:
   ```rust
   let source_path = session.resolve_module(&root_path)?;
   let source = std::fs::read_to_string(&source_path)?;
   let ctx = CompileContext {
       module: root_path,
       strategy: ModuleStrategy::Replace,
       compile_mode: CompileMode::Interactive,
   };
   compile_unit(&mut self.core, &source, &ctx)?;
   ```
3. Remove the `saved_module` / `set_current_module` save/restore at both call sites.
4. Delete `load_module_into_session()` from `src/pipeline.rs`.
5. If `discover_module_graph()` and `toposort()` have no other callers (check `compile_for_link` — see §15.4), they can be deleted or marked for link-only use.

**Acceptance criteria:**
- REPL `(import [core.option [Some None]])` loads the module and its transitive dependencies through `compile_unit()`.
- REPL auto-loading of qualified references (`core.option/Some`) works through `compile_unit()`.
- No `load_module_into_session` calls remain.
- Module loading works without explicit topo-sort — recursive `compile_unit()` handles ordering.

#### 15.3.4 Risk

**Medium.** Two concerns:

1. **Cache interaction.** `load_module_into_session()` uses `compile_single_module()` which has cache-hit logic (check hash, restore from cache, recompile macros). `compile_unit()` must implement the same cache-hit path — checking whether a cached module can be restored before running the full pipeline. This is already designed in §8.3 ("Before recursively calling `compile_unit()` for a dependency, the session checks whether a cached `.o` file exists with a matching source hash"). The risk is that the cache path is not yet implemented in `compile_unit()`, so module loading will be slower (always recompiling) until cache support is added.

2. **Prelude injection.** `load_module_into_session()` injects implicit prelude imports for non-prelude modules. `compile_unit()` must do the same — likely in Stage 2 after extracting module declarations, before registration. The risk is forgetting this step, which would cause loaded modules to lack access to prelude symbols (operators, traits, types).

### 15.4 `--link` (executable generation)

#### 15.4.1 Current implementation

`compile_for_link()` in `src/pipeline.rs` (line 2962) compiles a multi-file project and produces `.o` object files for linking into a standalone executable. It:

1. Calls `discover_module_graph()` to find all transitive dependencies.
2. Calls `toposort()` to determine compilation order.
3. Loads platforms and prelude.
4. Does a two-pass compilation: first restores cache hits, then compiles cache misses.
5. Each module is compiled via `compile_single_module()`, which calls `session.compile_module_batch()`.
6. `compile_module_batch()` uses `CompileMode::Batch` — all functions are compiled into a **shared `Jit` instance** with direct function calls (not GOT-indirect). The shared Jit accumulates all modules' code.
7. After all modules are compiled, `finalize_batch_jit()` freezes the Jit, producing native code.
8. The cache writes `.o` files (object file bytes extracted from the finalized Jit).
9. Returns `LinkCompileResult` with `.o` paths, entry symbol table, and module structures.

The caller (`link_file()` in `main.rs`) then validates `main`, generates a startup object, and invokes the system linker to produce an executable.

#### 15.4.2 v2 design

`--link` uses `compile_unit()` for compilation, just like `--run`. The compilation is identical — recursive loading of the entry file and all dependencies. The difference is only in the post-processing: instead of executing `main` and running the trampoline, `--link` generates a startup bridge object and invokes the system linker.

**`.o` files are a mandatory output of every `compile_unit()` call.** Compilation is expensive; repeating it later (e.g., at link time) is unacceptable. Every module compiled by `compile_unit()` produces a `.o` file in the cache as part of stage 6 (codegen). This is not an optional caching feature — it is part of the pipeline contract. `--no-cache` may skip *reading* the cache (forcing recompilation), but *writing* `.o` files always happens.

Currently `.o` files are only written during `compile_module_batch()` (batch mode). This must be extended so that interactive-mode codegen also writes `.o` files. Cranelift can emit object code from the same IR it uses for JIT — the `ObjectModule` and `JITModule` backends share the same function-building API. After interactive codegen finalizes each module's functions, an `ObjectModule` pass extracts the corresponding `.o` bytes and writes them to the cache.

```
--run flow:
  compile_unit(entry)       → recursive, all deps compiled, .o files written
  find main, execute, IO trampoline, exit

--link flow:
  compile_unit(entry)       → recursive, all deps compiled, .o files written
  collect .o paths from cache for all compiled modules
  validate main exists in entry module
  generate startup object   → _main entry, libc bridge (argc/argv → cranelisp main),
                               runtime init, exit code mapping
  invoke system linker      → startup.o + all module .o files + platform rlibs → executable
```

The compilation step is literally the same function call. The two modes diverge only in what happens after compilation completes.

**No separate graph discovery.** `compile_unit()`'s recursive loading handles dependency discovery and ordering. The explicit `discover_module_graph()` + `toposort()` is eliminated.

**Direct calls vs GOT-indirect.** The current `--link` uses `CompileMode::Batch` with direct inter-module calls. `compile_unit()` uses `CompileMode::Interactive` with GOT-indirect calls. The `.o` files from interactive mode contain GOT-indirect code; the linker resolves GOT entries at link time. This is slightly less optimal than direct calls but eliminates the need for a separate compilation path. If direct-call performance matters for linked executables, the future two-pass model (§8.4) enables a batch codegen pass after the typecheck walk — but this is an optimisation, not a correctness requirement.

#### 15.4.3 Migration step

1. **Make `.o` writing mandatory in `compile_unit()`.** After interactive-mode codegen finalizes a module, emit an `ObjectModule` for that module and write the `.o` to the cache. This requires `CompilationSession` to carry a `CacheState` (currently only `compile_for_link` and `compile_module_graph_cached` create one). Add `cache_state: Option<CacheState>` to `CompilationSession`; when present, `compile_unit()` writes `.o` files. Production callers (`--run`, `--link`, REPL with prelude) initialize it; test helpers leave it `None`.
2. **Replace `compile_for_link()` body:** session setup → `compile_unit()` on entry file → collect `.o` paths → validate main → generate startup object → return `LinkCompileResult`.
3. **Startup object generation** remains in `main.rs` / `link_file()` — it is not part of `compile_unit()`. It generates the libc bridge: `_main` symbol calling `cranelisp_main`, runtime initialization (allocator, platform setup), and exit code mapping.
4. The system linker invocation and platform rlib collection remain in `link_file()`.

**Acceptance criteria:**
- Every `compile_unit()` call with an active `CacheState` writes a `.o` file.
- `--link examples/hello.cl` produces a working executable via `compile_unit()` + linker.
- `--run` also writes `.o` files (enabling a subsequent `--link` to skip recompilation).
- No separate module graph discovery or topo-sort.

#### 15.4.4 Risk

**Medium.** The `.o` file generation from interactive-mode codegen is the main risk. The current backend emits one `ObjectModule` per `compile_module_batch()` call (shared JIT, all functions in one object). Interactive mode compiles per-function. The `.o` writer needs to collect all functions compiled for a given module during a `compile_unit()` call and emit them as one object file. This may require tracking which functions belong to which module during interactive codegen — information that `compile_unit()` has (it knows the `ctx.module`) but the backend currently doesn't.

### 15.5 `compile_and_run()` test helper

#### 15.5.1 Current implementation

`compile_and_run()` in `src/pipeline.rs` (line 1022) is the entry point for hundreds of test call sites. It currently:

1. Parses source text.
2. Creates a fresh `CompilationSession`.
3. Calls `process_forms_sequentially()` for macro expansion.
4. Calls `compile_unit()` (the v2 pipeline function) with the expanded sexps.
5. Wraps the result in `PipelineResult`.

This is *almost* correct — it already uses `compile_unit()` for stages 4-7. The issue is that it handles stages 1-3 externally, which means `compile_unit()` receives pre-expanded sexps rather than raw source text. This was a transitional state from Sprint 27.

However, the test helpers in `tests/helpers/mod.rs` do NOT call this function. They use `ReplSession::eval()` via `eval_all_forms()`, processing each top-level form through the REPL pipeline. The `compile_and_run()` function in `src/pipeline.rs` appears to be an older path that the test helpers have migrated away from.

#### 15.5.2 v2 design

`compile_and_run()` becomes a thin wrapper around `compile_unit()` that takes raw source text:

```rust
pub fn compile_and_run(
    source: &str,
    mode: CompileMode,
) -> Result<PipelineResult, CranelispError> {
    let mut session = CompilationSession::new();
    let ctx = CompileContext {
        module: ModuleFullPath::from("user"),
        strategy: ModuleStrategy::Additive,
        compile_mode: mode,
    };
    let result = compile_unit(&mut session, source, &ctx)?;
    Ok(PipelineResult {
        value: result.value.unwrap_or(0),
        ty: result.result_type.unwrap_or(Type::Int),
        warnings: result.warnings,
    })
}
```

All parsing, expansion, AST building, typechecking, codegen, and execution happen inside `compile_unit()`. No stages are handled externally.

The test helpers in `tests/helpers/mod.rs` (`compile_and_run_simple`, `compile_and_run_typed`, etc.) already use `ReplSession::eval()`. Once the REPL itself is wired through `compile_unit()` (Step 4b in §8.9), these test helpers automatically use the v2 pipeline without any changes to `tests/helpers/mod.rs`.

#### 15.5.3 Migration step

1. Once `compile_unit()` takes `&str` (Step 4a in §8.9), update `compile_and_run()` to pass source text directly:
   - Remove the `parse()` call.
   - Remove the `process_forms_sequentially()` call.
   - Pass `source` directly to `compile_unit()`.
2. Verify all tests pass (the function's signature and return type do not change).
3. If `compile_and_run()` has no remaining callers (because test helpers use `ReplSession::eval()` instead), consider deleting it. If it still has callers, keep it as the documented test entry point.

**Acceptance criteria:**
- `compile_and_run()` body is 10 lines: create session, build context, call `compile_unit()`, wrap result.
- No external parse/expand/build steps.
- All test call sites pass without changes.

#### 15.5.4 Risk

**Low.** This is a mechanical simplification. The function's external interface (`source: &str, mode: CompileMode`) does not change. The internal implementation gets simpler. The only risk is if some test relies on the specific session configuration (e.g., no lib_dirs, no prelude) that `CompilationSession::new()` provides. Since `compile_unit()` with empty `lib_dirs` makes imports unresolvable — which is the desired test behavior — this should be transparent.

## 16. Cache and `.o` Generation in the v2 Pipeline

### 16.1 Problem Statement

The v2 pipeline routes all compilation through `compile_unit()`, which uses Interactive mode (per-function JIT, GOT-indirect calls). Interactive mode produces live function pointers in the GOT but does NOT produce `.o` files. Three consumers need `.o` files:

1. **`--link`** — collects `.o` paths for all modules and passes them to the system linker to produce a standalone executable.
2. **Session cache** — persists compiled modules to disk so future sessions (or hot-reload cycles) can skip re-compilation by loading the `.o` via the Linker.
3. **REPL restore** — when the REPL restores a `user.cl` session, cached `.o` files provide function code without re-running the pipeline.

Currently, `compile_for_link_v2()` works around the gap by re-parsing each module's source after `compile_unit()` completes, rebuilding the AST, and calling `compile_module_to_object()` as a separate pass. This works but is wasteful (double parse, double expand, double AST build) and violates the single-pipeline principle — it is a parallel compilation path that replicates stages 1-4 outside `compile_unit()`.

### 16.2 Design Decision

**`.o` generation is integrated into stage 6, not a separate pass.** How it is integrated depends on the `CodegenTarget` (§8.4):

| `CodegenTarget` | Stage 6a (compile) | Stage 6b (cache write) |
|-----------------|-------------------|----------------------|
| `JitAndCache` | JIT to memory (hot) | Background `.o` + `.meta.json` via `CacheWriter` (§16.12) |
| `ObjectOnly` | ObjectModule to `.o` (hot) | Skipped — `.o` already written in 6a |

**`JitAndCache` (REPL / `--run`):**

```
compile_unit(session, source, ctx)       ctx.codegen_target = JitAndCache
  Stages 1-5: Parse → Typecheck → CheckResult
  Stage 6a:   JIT codegen (per-function, GOT-indirect)
  Stage 6b:   Queue background .o + .meta.json write via CacheWriter (§16.12)
  Stage 7:    Execute (mode-dependent)
```

Stage 6a produces live function pointers in the GOT — the hot path that the user waits on. Stage 6b queues the `.o` write on the background `CacheWriter` thread (§16.12). `compile_unit()` returns immediately after stage 7 without waiting for the `.o`. The `.o` file is produced by re-emitting the module's functions through Cranelift's `ObjectModule` backend — the same IR used for JIT compilation is compiled a second time with PIC mode enabled.

**`ObjectOnly` (`--link`):**

```
compile_unit(session, source, ctx)       ctx.codegen_target = ObjectOnly
  Stages 1-5: Parse → Typecheck → CheckResult
  Stage 6a:   ObjectModule codegen → .o file + .meta.json (hot, synchronous)
  Stage 7:    No execution (module registration only)
```

Stage 6a compiles directly to a relocatable `.o` file via `compile_module_to_object()`. This is the hot path — no JIT step, no GOT pointers, no background write. The `.o` and `.meta.json` are written synchronously because they ARE the primary output. Stage 7 is a no-op (no code to execute).

**Stage 6b is conditional on both target and cache state.** For `JitAndCache`, stage 6b runs only when `session.cache_state` is `Some(...)`. Test helpers (which use `CompilationSession::new()` with no cache configuration) skip it. Production callers (`--run`, REPL with prelude) initialize the cache state at session creation.

**All `compile_unit()` calls write `.o`** — both Additive (REPL line) and Replace (module load), in both targets. The only case that skips `.o` generation is a cache hit, where the `.o` already exists and is current. For Additive mode with `JitAndCache`, the `.o` contains the module's complete accumulated state at that point (all definitions entered so far). Since `.o` generation is background, the cost of re-emitting the full module on each REPL line is acceptable — the REPL is not blocked.

### 16.3 What Data Does `.o` Generation Need?

`ObjectCompileInput` requires:

| Field | Source | Available at stage 6b? |
|-------|--------|------------------------|
| `module_path` | `ctx.module` | Yes |
| `defns` with `Scheme`s | `Program` (from stage 4) + typechecker's `Scheme` per defn | Yes — `compile_unit()` has `program` and `check_result` in scope |
| `method_resolutions` | `CheckResult` | Yes |
| `fn_slot_assignments` | `session.got_state.def_codegen` | Yes — populated during stage 6a |
| `fn_to_module` | Session's module→function mapping | Yes — populated during stage 6a |
| `intrinsics` | `IntrinsicTable` built from session state | Yes — same table used for JIT |
| `type_defs` | `CheckResult.type_defs` | Yes |
| `constructor_to_type` | `CheckResult.constructor_to_type` | Yes |
| `expr_types` | `CheckResult.expr_types` | Yes |
| `next_got_slot` | `session.got_state.next_got_slot` | Yes |
| `cross_module_fns` | Cumulative list of prior modules' exported functions | **Requires accumulation** — see §16.4.3 |

All data except `cross_module_fns` is already available inside `compile_unit()` at the point between stage 6a and stage 7. The `cross_module_fns` list requires tracking which functions were defined by previously-compiled modules — this is a session-level accumulation, not a per-invocation concern.

### 16.4 Per-Scenario Design

#### 16.4.1 Module Load (Replace mode — `--run`, recursive dependency loading)

**Trigger:** `compile_unit()` called with `strategy: Replace`, `codegen_target: JitAndCache`, and `session.cache_state` is `Some(...)`.

**Pass 1 (stages 1–5):** Sequential recursive typecheck. Imports trigger recursive `compile_unit()` calls for dependencies. GOT slots are assigned as functions are registered.

**Pass 2 (stage 6a):** JIT compilation to memory — hot path, produces live function pointers.

**Stage 6b:** Background `.o` + `.meta.json` write via `CacheWriter` (§16.12):

1. Build `CacheMetadata` from the typechecker's symbol table for `ctx.module`, the `ModuleStructure` extracted in stage 2, and a `CacheCodegenState` derived from the program and check result.
2. Build `ObjectCompileInput` from the program, check result, and session state.
3. Build `CacheWritePacket` (owned, `Send`-safe data).
4. Send the packet to the `CacheWriter` channel. `compile_unit()` does not wait.
5. Record the `.o` path in `session.compiled_o_paths: Vec<PathBuf>` for later collection.

**Cache hit path:** Before running stages 1-7, `compile_unit()` checks whether the module has a valid cache entry (source hash matches, dependency hashes match). On cache hit:
- Restore the symbol table from `.meta.json` (skip stages 1-5).
- Load the `.o` via the Linker, register function pointers in the GOT (skip stages 6-7).
- Recompile macros from source (macro function pointers are not serializable).
- Return early with a minimal `CompileUnitResult`.

This is the existing `try_restore_from_cache()` logic, moved inside `compile_unit()`.

#### 16.4.2 REPL Line (Additive mode)

**Trigger:** `compile_unit()` called with `strategy: Additive`, `codegen_target: JitAndCache`.

**Pass 1 (stages 1–5):** Sequential typecheck of the REPL input (typically one or a few forms). New imports may trigger recursive `compile_unit()` calls.

**Pass 2 (stage 6a):** JIT compilation to memory — produces live function pointers for immediate execution.

**Stage 6b:** Background `.o` write via `CacheWriter` (§16.12). The `.o` contains the module's complete accumulated state (all definitions entered so far). The REPL is not blocked.

**Rationale:** Every `compile_unit()` call produces a `.o`. For Additive mode, this means the `.o` is regenerated after each REPL line, containing the full module. This is O(n) in the number of definitions, but since it runs in the background, the REPL remains responsive. The `.o` is always current — session restore can load it directly instead of replaying `user.cl`.

**Background task lifecycle:** If the user enters a new line before the previous `.o` write completes, the `CacheWriter` supersedes the pending write for the same module (§16.12). Only the most recent `.o` matters.

**Session persistence interaction:** The `user.cl` source regeneration mechanism remains as the primary persistence format (human-readable, diffable). The `.o` cache provides fast restore — on session startup, if a valid `.o` exists for `user`, it is loaded directly (cache hit path). If the `.o` is stale or missing, `user.cl` is compiled through `compile_unit()` (Replace mode), which produces a new `.o` in the background.

#### 16.4.3 `--link` (Executable Generation)

**Trigger:** `compile_for_link_v2()` calls `compile_unit()` with `codegen_target: ObjectOnly`.

**Pass 1 (stages 1–5):** Sequential recursive typecheck — identical to `JitAndCache`. GOT slots are assigned as functions are registered. (Even though `--link` does not execute code, GOT slot assignments are needed for the `.o` files' GOT data symbol references.)

**Pass 2 (stage 6a):** ObjectModule codegen to `.o` file — hot path, synchronous. Each module's functions are compiled via `compile_module_to_object()` directly in stage 6a. No JIT step, no GOT function pointers. The `.o` and `.meta.json` are written immediately as part of the hot path.

**Stage 6b:** Skipped — `ObjectOnly` already wrote the `.o` in 6a.

**No background writer for `--link`.** The `.o` file IS the primary output of `--link`, so it must be written synchronously in the hot path. The `CacheWriter` background thread (§16.12) is not used for `ObjectOnly` codegen. However, if the session started with prelude loading in `JitAndCache` mode (which queues background writes), `compile_for_link_v2()` calls `session.flush_cache_writes()` before collecting `.o` paths to ensure all background writes from the prelude loading phase have completed.

**Cross-module references:** The `ObjectCompileInput.cross_module_fns` field tells the ObjectModule compiler which functions from other modules may be called by this module's code. This list must grow as modules are compiled. The session maintains a cumulative `cross_module_func_sigs: Vec<(Symbol, usize)>` that is extended after each module completes stage 6a. When building `ObjectCompileInput` for a module, the current cumulative list is used as `cross_module_fns`.

**Elimination of the re-parse pass:** With `.o` generation integrated into stage 6a, the current `generate_object_file()` function in `pipeline_v2.rs` (which re-parses source, re-expands, and re-builds the AST) is deleted. The program and check result are already in scope when stage 6a runs — no re-parsing needed.

**Elimination of `discover_module_graph()` + `toposort()`:** The recursive module loading inside `compile_unit()` (§8.3) handles dependency ordering. `compile_for_link_v2()` calls `compile_unit()` once on the entry file; all transitive dependencies are compiled recursively. After the call returns, all modules are compiled and their `.o` files are written. The only remaining task is to collect the paths and invoke the linker.

```rust
fn compile_for_link_v2(
    entry: &Path,
    lib_dirs: &[PathBuf],
    cache_dir: &Path,
) -> Result<LinkCompileResult, CranelispError> {
    let mut session = CompilationSession::new_with_cache(cache_dir);
    session.lib_dirs = compute_lib_dirs(entry, lib_dirs);
    load_platforms(&mut session, entry)?;

    let source = std::fs::read_to_string(entry)?;
    let ctx = CompileContext {
        module: derive_module_path(entry),
        strategy: ModuleStrategy::Replace,
        compile_mode: CompileMode::Interactive,
        codegen_target: CodegenTarget::ObjectOnly,
    };

    // Single call: recursively compiles all dependencies.
    // Each compile_unit() invocation writes its .o file in stage 6a (ObjectOnly).
    let result = compile_unit(&mut session, &source, &ctx)?;

    // Flush any background writes from prelude loading (JitAndCache phase).
    session.flush_cache_writes();

    // Collect .o paths written during the recursive compilation.
    let module_o_paths = session.compiled_o_paths.clone();

    // Collect entry module info for main validation.
    let entry_symbols = session.tc.module_table(&ctx.module)
        .cloned()
        .unwrap_or_default();

    Ok(LinkCompileResult {
        module_o_paths,
        entry_symbols,
        module_structures: session.compiled_module_structures.clone(),
        warnings: result.warnings,
    })
}
```

#### 16.4.4 File-Watcher Recompilation (Hot Reload)

**Trigger:** The file watcher detects a source change. `reload_single_module()` recompiles the changed module.

**Action:** The reload path calls `compile_unit()` with `strategy: Replace`, `codegen_target: JitAndCache`. Pass 1 re-typechecks the module. Stage 6a JIT-compiles to memory (updating GOT pointers). Stage 6b queues a background `.o` write via the `CacheWriter` (§16.12), replacing the stale cache entry.

**Cascade invalidation:** After the directly-changed module is recompiled, `reload_changed_modules()` identifies transitive dependents (modules that import from the changed module) using the `module_dependency_map`. Each dependent is also recompiled via `compile_unit()` with Replace mode and `JitAndCache`. Their stale `.o` files are superseded by new background writes.

**Cache manifest update:** After each successful reload, the module's source hash in the manifest is updated. Dependent modules' hashes are also updated after their cascade recompilation. The manifest is flushed to disk after the full cascade completes.

**Interaction with REPL additive state:** A file-watcher reload uses Replace mode for the module being reloaded — it re-defines the module's complete contents from the file. This correctly handles definitions that were removed from the file. The REPL's additive definitions in the `user` module are NOT affected by file-watcher events (the user module comes from `user.cl` or REPL input, not from watched library files).

### 16.5 Session State for Caching

`CompilationSession` gains the following cache-related fields:

```rust
pub struct CompilationSession {
    // ... existing fields ...

    /// Cache state for .o and .meta.json writing. None = caching disabled.
    /// Initialized by production callers (--run, --link, REPL with prelude).
    /// Left as None by test helpers.
    pub cache_state: Option<CacheState>,

    /// Background .o writer. Created when cache_state is Some.
    /// See §16.12 for the full design.
    pub cache_writer: Option<CacheWriterHandle>,

    /// .o file paths written during this session, in compilation order.
    /// Used by --link to collect all .o files for the system linker.
    pub compiled_o_paths: Vec<PathBuf>,

    /// Module structures extracted during compilation, in compilation order.
    /// Used by --link for platform rlib discovery and startup object generation.
    pub compiled_module_structures: Vec<(ModuleFullPath, ModuleStructure)>,

    /// Cumulative cross-module function signatures for .o generation.
    /// Each entry is (qualified_name, param_count). Extended after each
    /// module completes stage 6 (6a for ObjectOnly, 6b for JitAndCache).
    /// Used as `ObjectCompileInput.cross_module_fns` for subsequent modules.
    pub cross_module_func_sigs: Vec<(Symbol, usize)>,
}
```

**`cache_state` ownership.** The cache state moves from being a local variable in `compile_for_link()` / `compile_module_graph_cached()` to being a session-level field. This is necessary because `compile_unit()` is recursive — the cache state must be accessible in recursive calls without being passed as a parameter. Since `compile_unit()` already takes `&mut CompilationSession`, the cache state is naturally reachable.

**`cache_writer` lifecycle.** Created alongside `cache_state` during session initialization. Owned by `CompilationSession`. Dropped when the session is dropped — the `Drop` impl joins the writer thread (§16.12). For `ObjectOnly` codegen, the `CacheWriter` is still present (it may have been used during prelude loading in `JitAndCache` mode) but is not used for the main `.o` generation.

**`compiled_o_paths` accumulation.** Each `compile_unit()` call that writes a `.o` file appends the path to this list. For `JitAndCache`, the path is recorded when the background write is *queued* (the path is deterministic from the module name and cache directory). For `ObjectOnly`, the path is recorded when the `.o` is *written*. The list grows monotonically during a session. `--link` reads it after the entry file's `compile_unit()` returns (at which point all recursive dependencies have also been compiled and their paths accumulated).

### 16.6 Cache-Hit Path Inside `compile_unit()`

Before running stages 1-7, `compile_unit()` checks for a cache hit:

```
compile_unit(session, source, ctx):
  // Pre-pipeline: cache check
  if ctx.strategy == Replace && session.cache_state.is_some():
    let source_hash = hash_source(source)
    if cache_hit(session, &ctx.module, &source_hash):
      restore_from_cache(session, &ctx.module)
      session.compiled_o_paths.push(cached_o_path)
      return Ok(minimal_result)

  // Stages 1-7: normal pipeline
  ...
  // Stage 6b: cache write
  if session.cache_state.is_some():
    write_cache(session, &ctx.module, &program, &check_result)
```

**Additive mode skips the cache check.** A REPL line with `strategy: Additive` does not check the cache — it always runs the full pipeline (the module is being built up incrementally, so no cached `.o` can be current). Cache-hit logic applies only to Replace mode (module file loads). However, both modes write `.o` in the background after compilation — only a cache *hit* skips `.o` generation.

**Dependency hash validation.** A cache hit is valid only if the module's source hash AND all dependency hashes match. Dependency hashes are checked via the manifest. If a dependency was recompiled (its hash changed), the dependent's cache entry is invalid and the module is recompiled.

### 16.7 `.o` File Lifecycle

| Event | `.o` file action | `.meta.json` action |
|-------|-----------------|---------------------|
| Module first compiled (JitAndCache) | Background write via CacheWriter (§16.12) | Background write with `.o` |
| Module first compiled (ObjectOnly) | Written synchronously in stage 6a | Written synchronously in stage 6a |
| Module loaded from cache | Read by Linker, pointers into GOT | Read, symbol table restored |
| Module source changed (file watcher) | Superseded by new background write | Superseded with `.o` |
| Dependent cascade recompilation | New background write | New background write |
| `--link` invocation | Read by system linker | Not used |
| REPL line entered | Queued as background write via CacheWriter (§16.12) | Queued with `.o` |
| REPL session save | Flush `CacheWriter` to ensure latest `.o` is on disk | Flushed with `.o` |
| `--no-cache` flag | Stage 6b skipped (cache_state is None) | Skipped |
| Cache format version bump | All `.o` files invalidated on next load | All `.meta.json` invalidated |

### 16.8 `.meta.json` Content

The `.meta.json` file stores everything needed to restore a module without re-running stages 1-5:

```rust
pub struct CacheMetadata {
    /// Complete symbol table (types, functions, constructors, imports, exports).
    /// Restored into the TypeChecker on cache hit.
    pub symbol_table: SymbolTable,

    /// Module structure (import specs, export specs, submodule list).
    /// Used for dependency tracking and --link module structure collection.
    pub module_structure: ModuleStructure,

    /// Codegen state (GOT slot assignments, function parameter counts).
    /// Used to restore GOT slot mappings on cache hit so the Linker can
    /// wire loaded .o function pointers to the correct slots.
    pub codegen_state: CacheCodegenState,
}
```

This structure already exists in `cranelisp-backend/src/cache/serialize.rs`. No changes to its fields are needed. The change is where it is built and written — moving from `write_module_cache()` in `pipeline.rs` to stage 6b inside `compile_unit()`.

### 16.9 Sketch Comparison

The sketch's cache infrastructure lives in `sketch/src/pipeline.rs` (`try_load_cached_module`, `write_module_cache`) and `sketch/src/cache/`. The sketch writes cache files after the batch compilation pass (`compile_single_module`) completes, as a post-compilation step — similar to the v1 reimplementation.

The sketch has the same structural issue: cache writing is done by the orchestration layer (pipeline.rs) rather than by the compilation function itself. This means every new calling pattern (REPL, file-watcher, link) must independently remember to write the cache. The sketch's file-watcher path (`reload_module`) does NOT write cache files — a known gap.

The v2 design diverges by moving cache writing into `compile_unit()` itself (stage 6b). This ensures that every compilation — regardless of the caller — produces a cache entry when caching is enabled. The caller does not need to remember to write the cache; `compile_unit()` does it automatically.

### 16.10 Implementation Priority

The `.o`-in-pipeline integration has dependencies on the ongoing pipeline migration (§8.9):

1. **Prerequisite: `compile_unit()` owns all 7 stages** (Steps 4a-4c in §8.9). Stage 6 dispatch on `CodegenTarget` can only be added when `compile_unit()` has the `program` and `check_result` in scope at the right point.

2. **Phase 1: Add `CodegenTarget` and `CacheWriterHandle`** — add `CodegenTarget` enum to `cranelisp-types`, add `codegen_target` field to `CompileContext`, add `CacheWriterHandle` to `CompilationSession`, add `cache_state` and accumulation fields (`compiled_o_paths`, `cross_module_func_sigs`). Additive — nothing breaks.

3. **Phase 2: Add `CodegenTarget` dispatch to stage 6** — `JitAndCache` runs JIT codegen (stage 6a) then queues background `.o` write (stage 6b) via `CacheWriter`. `ObjectOnly` runs ObjectModule codegen directly (stage 6a only). This replaces both `write_module_cache()` in pipeline.rs and `generate_object_file()` in pipeline_v2.rs.

4. **Phase 3: Add cache-hit check at `compile_unit()` entry** — before running stages 1-7, check the manifest. On hit, restore from cache and return early. This replaces `try_restore_from_cache()` in pipeline.rs.

5. **Phase 4: Simplify `compile_for_link_v2()`** — remove the separate `generate_object_file()` pass. Use `CodegenTarget::ObjectOnly` in the `CompileContext`. The single `compile_unit()` call on the entry file now produces all `.o` files via recursive loading + stage 6a (ObjectOnly). Call `flush_cache_writes()` to drain any prelude-phase background writes. Collect paths from `session.compiled_o_paths`.

6. **Phase 5: Delete v1 cache orchestration** — `write_module_cache()`, `generate_object_file()`, `build_codegen_state_for_cache()`, the `cache_state` parameter threading through `compile_single_module()` and `load_module_into_session()`.

### 16.11 Open Questions

1. **~~Background cache writing.~~** RESOLVED. Background writing is now the design for `JitAndCache` mode (§16.12). `ObjectOnly` mode writes synchronously in the hot path. The `CacheWritePacket` is `Send`-safe by design, enabling the channel-based `CacheWriter`.

2. **`CompileMode::Batch` interaction.** The current `compile_and_run()` test helper uses `CompileMode::Batch` (direct calls, shared JIT). Batch mode does not use the GOT and produces different code (direct call instructions vs GOT-indirect loads). Should stage 6b emit `.o` files from Batch-mode codegen too? **Recommendation:** No. Batch mode is for single-file test execution where caching is irrelevant (`cache_state` is None for test helpers). `.o` files are only needed for Interactive mode (`JitAndCache`) and linking (`ObjectOnly`). If a future `CompileMode::Release` is added, it would use `CodegenTarget::ObjectOnly` as its primary output, but that is a separate design concern.

3. **Macro function pointers.** The `.o` + `.meta.json` cache restores symbol tables and compiled code, but macro function pointers (JIT-compiled functions stored in the `MacroExpander`) are not serializable. On cache hit, macros must be recompiled from source (`recompile_macros_for_cached_module()`). This is a known limitation of the current cache design and is orthogonal to the codegen target integration — it remains unchanged.

### 16.12 Background `.o` Writer (`CacheWriter`)

#### 16.12.1 Purpose

When `CodegenTarget::JitAndCache` is active, stage 6b must write `.o` + `.meta.json` files without blocking the pipeline. The user sees JIT results immediately (stage 6a); the `.o` file is persisted in the background for future cache hits.

`CodegenTarget::ObjectOnly` does NOT use the `CacheWriter` — it writes `.o` files synchronously in stage 6a because the `.o` IS the primary output.

#### 16.12.2 Design

```rust
/// Handle to the background cache writer thread.
/// Owned by CompilationSession. Created when cache_state is initialized.
pub struct CacheWriterHandle {
    /// Channel sender for queueing write requests.
    sender: mpsc::Sender<CacheWriteRequest>,
    /// Join handle for the writer thread. Joined on Drop.
    thread: Option<std::thread::JoinHandle<()>>,
}

/// A request to write a .o + .meta.json for a module.
struct CacheWriteRequest {
    /// Module being written. Used for supersession detection.
    module: ModuleFullPath,
    /// Monotonically increasing sequence number. Used to detect
    /// superseded requests (newer request for same module wins).
    seq: u64,
    /// The Send-safe packet containing all data needed to produce the .o.
    /// This is the existing CacheWritePacket — owned data, no references.
    packet: CacheWritePacket,
}
```

#### 16.12.3 Writer thread behaviour

The writer thread is a single `std::thread` that drains an `mpsc::Receiver<CacheWriteRequest>` in a loop:

1. **Receive** a `CacheWriteRequest` from the channel.
2. **Check supersession**: if a newer request for the same module is already in the channel (peek/drain), skip the older request. Implementation: maintain a `HashMap<ModuleFullPath, u64>` of the latest sequence number seen per module. If the incoming request's `seq` is older than the recorded latest, skip it.
3. **Compile** the `.o` via `compile_module_to_object()` using the packet's data.
4. **Write** the `.o` and `.meta.json` atomically (write to temp file, rename).

**Nice priority.** The writer thread sets its scheduling priority to below-normal (via `setpriority(PRIO_PROCESS, 0, 10)` on Unix, `SetThreadPriority(THREAD_PRIORITY_BELOW_NORMAL)` on Windows). This ensures the background writer does not compete with the hot compilation path for CPU time. If the platform API is unavailable, the thread runs at normal priority — correctness is unaffected, only latency characteristics change.

**Supersession.** When a REPL user types quickly, multiple `compile_unit()` calls for the same module (e.g., `user`) may queue background writes faster than they can be processed. Supersession ensures only the latest state is written. The sequence number is a session-wide counter incremented on each `CacheWriteRequest` creation.

#### 16.12.4 API

```rust
impl CacheWriterHandle {
    /// Create a new background writer. Spawns the writer thread.
    pub fn new(cache_dir: PathBuf) -> Self;

    /// Queue a .o + .meta.json write for a module. Non-blocking.
    /// Returns immediately. The packet is moved to the writer thread.
    pub fn queue_write(&self, module: ModuleFullPath, packet: CacheWritePacket);

    /// Block until all pending writes have completed.
    /// Called by:
    /// - `compile_for_link_v2()` to flush prelude-phase background writes
    ///   before collecting .o paths.
    /// - Session persistence (REPL save) to ensure the latest .o is on disk.
    /// - CompilationSession::drop() implicitly (via thread join).
    pub fn flush(&self);
}

impl Drop for CacheWriterHandle {
    fn drop(&mut self) {
        // Send a shutdown sentinel, then join the thread.
        // This ensures all queued writes complete before the session exits.
    }
}
```

#### 16.12.5 Interaction with `ObjectOnly`

`--link` uses `CodegenTarget::ObjectOnly`, which writes `.o` files synchronously in stage 6a. The `CacheWriter` is not used for these writes. However, the `CacheWriter` may have been created during session initialization (alongside `cache_state`) and may hold pending writes from an earlier `JitAndCache` phase (e.g., prelude loading before `--link` switches to `ObjectOnly` for the user's modules). `compile_for_link_v2()` calls `flush()` before collecting `.o` paths to ensure those earlier background writes have landed.

#### 16.12.6 Thread safety

- `CacheWritePacket` is already `Send` by design (owned data, no raw pointers, no `Jit` references).
- `mpsc::Sender` is `Send + Sync` — `queue_write()` can be called from the main thread.
- The writer thread has exclusive access to the `Receiver` end — no shared mutable state.
- File writes use atomic rename — concurrent reads (cache-hit checks) see either the old file or the new file, never a partial write.

#### 16.12.7 Implementation priority

The `CacheWriter` is implementable now — it depends only on `CacheWritePacket` (which already exists and is `Send`-safe) and `compile_module_to_object()` (which already exists). The implementation sequence:

1. Add `CacheWriterHandle` struct with spawn/queue/flush/drop.
2. Add `cache_writer: Option<CacheWriterHandle>` to `CompilationSession`.
3. In `compile_unit()` stage 6b (`JitAndCache` path): build packet, call `queue_write()`.
4. In `compile_for_link_v2()`: call `flush()` before collecting paths.
5. Test: verify `.o` files appear after `flush()`, verify supersession skips stale writes.
