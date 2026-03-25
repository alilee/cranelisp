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
    |           (module, strategy, compile_mode)
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
[6. Codegen]        (CompileContext, Vec<TopLevel>, CheckResult) -> ()
    |                ctx.compile_mode = Interactive | Batch | Release
    v                Side effect: functions compiled into JIT / object
[7. Execute]        Mode-dependent: call entry / update GOT / display
```

### Key design decisions

1. **One `TopLevel` enum** with an `Expr` variant — no `ReplInput`.
2. **One `CheckResult` struct** with `display: Option<DisplayInfo>` — no `ReplCheckResult`.
3. **One `check()` entry point** with no mode parameter — no `check_repl_input`, no `CheckMode`. The multi-pass pipeline (register all signatures, then check all bodies) works identically regardless of slice length. A REPL line is a one-element slice; a batch program is a multi-element slice. See §5 for the rationale.
4. **`CompileMode`** controls codegen strategy (GOT-indirect vs direct calls). It is the only mode parameter in the pipeline.
5. **Call graph** is a cross-cutting data structure populated during typecheck, consumed by codegen and analysis passes.
6. **`CompileContext`** makes the module context explicit. Every pipeline invocation declares which module definitions land in and whether the invocation is additive (REPL line) or replacing (file load). See §14.

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
**Output:** Side effects (JIT compilation, GOT updates)
**Owner:** `cranelisp-backend`

`CompileMode` controls the codegen strategy:
- **`Interactive`**: GOT-indirect calls. Each defn is compiled individually and registered in the GOT. Used for REPL and multi-module batch.
- **`Batch`**: Direct function calls. All defns declared first, then compiled. Used for single-file test execution.
- **`Release`**: Whole-program optimisation (future).

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
| `CompileMode` | `cranelisp-types` | Pipeline configuration — stable data (unchanged) |
| `ModuleStrategy` | `cranelisp-types` | Pipeline configuration — additive vs replacement (see §14) |
| `CompileContext` | `cranelisp-types` | Pipeline configuration — module + strategy + compile_mode (see §14) |
| `CallGraph`, `CallEdge`, `CallInfo` | `cranelisp-types` | Cross-cutting data structure — frontend populates, typecheck builds, backend and binary crate consume |
| `DisplayInfo` | `cranelisp-types` | Part of `CheckResult` |
| `ModuleDecls` | `cranelisp-types` | Extracted by frontend, consumed by binary crate |

### 7.3 What moves

- `ReplInput` — **deleted** from `cranelisp-types`
- `ReplCheckResult` — **deleted** from `cranelisp-types`
- `TopLevel::DefnMulti` — **deleted** from `TopLevel` enum (merged into `Defn`)
- `Defn` struct — **changed**: `params`/`body`/`param_annotations` replaced by `variants: Vec<DefnVariant>`
- `Expr` variant — **added** to `TopLevel` in `cranelisp-types`
- `DisplayInfo` — **added** to `cranelisp-types`
- `CallGraph` etc. — **added** to `cranelisp-types`

## 8. v1 → v2 Adapter Strategy

### 8.1 Approach

The transition builds v2 orchestration alongside v1, using the existing stage implementations (TypeChecker, FnCompiler, etc.) through thin adapters. The stages themselves (inference engine, codegen) do not change — only their entry points and the types they operate on.

### 8.2 Migration order

The migration proceeds in five steps, each independently testable:

**Step 1: Add v2 types (additive, nothing breaks)**

Merge `Defn` struct (replace `params`/`body`/`param_annotations` with `variants: Vec<DefnVariant>`). Delete `TopLevel::DefnMulti` variant. Add `Expr` variant to `TopLevel`. Add `DisplayInfo` and `display` field to `CheckResult`. Add `CallGraph` types.

The `Defn` merge is a mechanical refactor: ~30 match sites on `TopLevel::Defn(defn)` need updating (most just add `.params()` / `.body()` convenience calls), ~5 match sites on `TopLevel::DefnMulti` are deleted and folded into the `Defn` arm. `TraitImpl.methods: Vec<Defn>` callers wrap method params/body in a single-element `variants` Vec. All changes are localized to the match sites — no algorithm changes.

**Step 2: Implement `check()` (new code, nothing breaks)**

Add `TypeChecker::check(&mut self, &[TopLevel]) -> Result<CheckResult, CranelispError>`. This method:
- Uses the multi-pass pipeline from `check_program()` extended to handle `Expr` (wrap as synthetic defn) and multi-sig `Defn` variants.
- Populates the `display` field from the last `Expr` or `Defn` in the input.
- Populates `call_graph`.
- Monomorphisation scans both defn bodies and bare expressions (fixing a gap in the v1 batch path).

Old entry points (`check_program`, `check_repl_input`) remain for now. `check()` is a parallel entry point.

**Step 3: Build v2 orchestration (new code, nothing breaks)**

Add `src/pipeline_v2.rs` with `compile_unit()`. This function:
1. Receives a `CompileContext` from the caller
2. Calls `parse()`
3. Calls `expand_forms()` (extracted from current preprocessing)
4. Calls `build_top_level()` in a loop
5. Calls `TypeChecker::check(&ctx, &program)`
6. Calls backend codegen with `&ctx`
7. Returns the result

Wire a comparison test harness that runs programs through both v1 and v2 pipelines, asserting identical results.

**Step 4: Switch over**

Point REPL and batch at `compile_unit()`. Verify all tests pass.

**Step 5: Delete v1 artifacts**

- Delete `ReplInput` from `cranelisp-types`
- Delete `ReplCheckResult` from `cranelisp-types`
- Delete `check_repl_input` from `cranelisp-typecheck`
- Delete `toplevel_to_repl_input` from `cranelisp-frontend`
- Delete `build_check_for_backend` (both copies) from `src/pipeline.rs` and `src/repl/mod.rs`
- Move v1 `interfaces.md` to `v1/` (already done)

### 8.3 Adapters during transition

During Steps 2–4, thin adapters bridge v2 types to v1 stage implementations:

```rust
// In cranelisp-typecheck, during Step 2:
// check(ctx, program) uses ctx.module as the active module and ctx.strategy to decide
// whether to clear existing state. Internally converts TopLevel::Expr → synthetic defn.
// No new types needed — just routing.

// In binary crate, during Step 3:
// compile_unit(ctx, source) calls check(ctx, &program) — the CompileContext flows through.
// No mode parameter on check() — check() always uses multi-pass.
// The CheckResult is the same type (with new optional fields) — backend takes it directly.
```

The key insight is that the *stage implementations* (inference, codegen) do not change. Only the *orchestration* (which function calls which, what types cross the boundary) changes. Adapters are thin routing layers, not type converters.

### 8.4 Risk assessment

- **Step 1** (types): Zero risk. Additive.
- **Step 2** (check): Low risk. New entry point calling existing logic. Can be tested independently.
- **Step 3** (orchestration): Medium risk. New pipeline must produce identical results to v1 for all existing tests.
- **Step 4** (switch): Low risk. If Step 3 passed all tests through comparison, switchover is safe.
- **Step 5** (cleanup): Zero risk. Mechanical deletion.

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

When compiling a multi-module project in batch mode, the orchestration layer can exploit the parallelism properties described in §12.5:

```
     Module graph (N modules in topo order)
                      |
   ═══════════════════╪══════════════════════════
   Typecheck          │  (sequential, topo order)
   ═══════════════════╪══════════════════════════
                      |
        for each module in topo order:
            Stages 1-5 (Parse → Typecheck)
            GOT slots assigned as functions are registered
            (ensure_slot_for — reuses existing, allocates new)
                      |
                      v
        Vec<(ModuleFullPath, CheckResult)>
        + ModuleCodegenState has stable slot assignments
                      |
   ═══════════════════╪══════════════════════════
   Codegen            │  (parallel across modules)
   ═══════════════════╪══════════════════════════
                      |
        ┌─────────────┼─────────────┐
        │             │             │
     Module A      Module B      Module C
     (own Jit)     (own Jit)     (own Jit)
     Stage 6       Stage 6       Stage 6
        │             │             │
        └─────────────┼─────────────┘
                      |
                      v
            Finalize all JITs
            Write code pointers into GOT slots
                      |
                      v
                 Stage 7: Execute
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

```
     Module graph (N modules in topo order)
                      |
   ═══════════════════╪══════════════════════════
   Typecheck          │  (sequential, topo order)
   ═══════════════════╪══════════════════════════
                      |
        for each module in topo order:
            Stages 1-5 (Parse → Typecheck)
            GOT slots assigned via ensure_slot_for()
                      |
                      v
        Vec<(ModuleFullPath, CheckResult)>
        + ModuleCodegenState with stable slot assignments
                      |
   ═══════════════════╪══════════════════════════
   Codegen            │  (parallel across modules)
   ═══════════════════╪══════════════════════════
                      |
        Each module reads its CheckResult + slot indices
        Each module creates its own Jit instance
        No shared mutable state during compilation
                      |
                      v
            Finalize all JITs
            Write code pointers into GOT slots (sequential)
```

There is no separate "GOT declaration phase". GOT slot allocation happens naturally as functions are registered during typecheck. The separation between typecheck and codegen is already the separation that enables parallelism.

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
- The main implementation work is: (a) separating the typecheck-all-modules loop from the codegen-all-modules loop in the orchestration layer, (b) making each module's codegen independent (own `Jit` instance), (c) adding `rayon::par_iter` for the codegen loop.

The parallel codegen capability can be adopted incrementally: first separate the typecheck and codegen loops (which improves code clarity even without parallelism), then add parallel dispatch when benchmarking shows it matters.

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
| File load (module graph) | Derived from file path | Replace | Interactive | Module's contents = file's contents |
| Hot-reload | Module being reloaded | Replace | Interactive | File changed; invalidate + re-load |
| Single-file batch test | `"main"` | Replace | Batch | Direct calls, no GOT |
| `begin` expansion | Same as enclosing context | (inherited) | (inherited) | Multiple forms, same module |
| Recursive module load (import triggers load) | The imported module | Replace | Interactive | Recursive pipeline call |

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

**Stage 6 (Codegen):** `codegen()` receives `&CompileContext`. It uses `ctx.compile_mode` for the GOT vs direct-call decision (same as before), and `ctx.module` to determine which module's codegen state (GOT table, def_codegen map) to update.

**Stages 1-4 (Parse, Extract, Expand, Build AST):** These stages do not need the context. They are pure transformations on syntax that do not interact with module state.

**Stage 7 (Execute):** The binary crate's orchestration layer uses `ctx.compile_mode` to decide whether to call `main`, display a REPL result, or do nothing (module loading). It already knows the mode because it constructed the context.

### 14.5 Construction sites

The `CompileContext` is constructed at three sites in the binary crate:

**1. REPL line evaluation (`src/repl/mod.rs`)**

```rust
let ctx = CompileContext {
    module: self.current_module.clone(),  // set by /mod command
    strategy: ModuleStrategy::Additive,
    compile_mode: CompileMode::Interactive,
};
let check_result = self.core.tc.check(&ctx, &program)?;
```

The REPL session owns `current_module: ModuleFullPath` (moved out of TypeChecker). The `/mod` command updates this field on the REPL session, not on the TypeChecker.

**2. Module graph compilation (`src/pipeline.rs`)**

```rust
for module_path in &compile_order {
    let ctx = CompileContext {
        module: module_path.clone(),
        strategy: ModuleStrategy::Replace,
        compile_mode: CompileMode::Interactive, // or Batch for single-file
    };
    let check_result = tc.check(&ctx, &program)?;
    // ...
}
```

Each module in the graph gets its own `CompileContext` with `Replace` strategy. No save/restore of module state needed -- the context is a parameter, not mutable state.

**3. Lazy module loading from REPL (`src/repl/mod.rs` — import handling)**

```rust
// When a REPL import triggers loading a module:
let ctx = CompileContext {
    module: imported_module_path.clone(),
    strategy: ModuleStrategy::Replace,
    compile_mode: CompileMode::Interactive,
};
let check_result = tc.check(&ctx, &program)?;
// No need to save/restore current_module -- the REPL session's
// current_module was never changed.
```

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
