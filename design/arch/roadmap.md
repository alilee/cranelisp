# Phased Progression Roadmap

Ring-by-ring plan for the Cranelisp reimplementation. Each ring establishes a stable foundation before the next begins. Within each ring, compiler skills work in parallel against interface stubs.

For the full reimplementation strategy, skill definitions, and risk analysis, see `design/reimplementation.md`. For boundary types, see `design/arch/interfaces.md`. For crate structure and architectural decisions, see `design/arch/architecture.md`.

## Ring 0: Core

**Property**: Expressions, types, functions, let, if, match. No heap allocation, no reference counting.

| Skill | Deliverables | Depends On |
|---|---|---|
| `/arch` | Crate scaffolding (`Cargo.toml`s), `CLAUDE.md` files per source directory, `interfaces.md` | — |
| `/frontend` | Reader (source -> Sexp), AST builder (Sexp -> Expr/TopLevel) | `interfaces.md` |
| `/typecheck` | Core inference: `Int`, `Bool`, `Float`, simple `Fn`, `let`-polymorphism, basic `match` over enums | `interfaces.md` |
| `/backend` | Codegen for scalars, functions, `if`/`let`/`match` (no heap), JIT execution, `CompileMode` | `interfaces.md` |
| `/qa` | Batch pipeline wiring (`compile_unit()`), ~50 integration tests | all compiler skills |
| `/examples` | Simple integer/boolean programs | `/qa` pipeline |
| `/docs` | Getting started tutorial | `/qa` pipeline |
| `/repl` | Basic REPL experience tests: prompt, `/help`, value+type display, error messages | `/qa` pipeline |
| `/review` | Ring 0 completion review | all above |

**Acceptance criteria**:
- `(+ 1 2)` returns `3 :: Int`
- `(defn id [x] x)` infers `id :: (Fn [:a] :a)`
- `(if true 1 2)` returns `1 :: Int`
- `(let [x 5] (+ x 1))` returns `6 :: Int`
- `(deftype Color Red Green Blue)` + `(match Red (Red 1) (Green 2) (Blue 3))` returns `1 :: Int`
- `(defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))` runs correctly with TCO
- Batch and REPL produce identical results for all tests
- ~50 integration tests green
- REPL experience tests pass: discoverability, value+type feedback
- `cargo clippy` clean, no `unwrap()` in pipeline code

## Ring 1: Heap

**Property**: Strings, ADTs with fields, closures, reference counting. Heap management established as a clean layer over Ring 0.

| Skill | Deliverables | Depends On |
|---|---|---|
| `/typecheck` | ADT type checking (product + sum types), exhaustiveness checking, `String` type | Ring 0 |
| `/backend` | Heap allocation (`alloc_with_rc`), RC emission (inc/dec/drop glue), closure compilation, consuming calling convention | Ring 0 |
| `/qa` | RC correctness tests (no leaks, no double-frees), ADT integration tests, closure tests | Ring 1 compiler |
| `/examples` | String manipulation programs, ADT programs (Option, List) | Ring 1 `/qa` |
| `/platform` | `cranelisp-runtime` crate (alloc, RC primitives, panic handler), begin platform C-ABI contract | Ring 1 `/backend` |
| `/repl` | ADT display tests (`(Some 42) :: (Option Int)`), string display, error message quality assertions | Ring 1 compiler |
| `/review` | RC correctness focus: drop glue, consuming conventions, scope cleanup | all above |

**Acceptance criteria**:
- `"hello"` returns `"hello" :: String`
- `(deftype (Option a) None (Some [:a val]))` type-checks with polymorphic constructors
- `(Some 42)` returns `(Some 42) :: (Option Int)`
- `(match (Some 1) (Some x) x (None 0))` returns `1 :: Int`
- `(fn [x] (+ x 1))` creates a closure; `((fn [x] (+ x 1)) 5)` returns `6 :: Int`
- `(let [f (fn [x] (+ x 1))] (f 5))` — closure captured correctly
- `CRANELISP_RC_TRACE=1` shows balanced inc/dec for all tests
- No memory leaks detected by runtime tracking
- ~100 additional integration tests green

## Ring 2: Abstraction

**Property**: Traits, modules, imports/exports, constrained polymorphism, multi-signature dispatch. Name resolution and dispatch established.

| Skill | Deliverables | Depends On |
|---|---|---|
| `/typecheck` | Trait declarations and implementations, method resolution, constrained polymorphism detection, monomorphisation, module-scoped type environments | Ring 1 |
| `/backend` | Mangled name dispatch (`add$Int+Int`), GOT-based cross-module calls, module linking | Ring 1 |
| `/qa` | Module graph tests, trait dispatch tests, constrained poly tests, cross-module tests | Ring 2 compiler |
| `/stdlib` | Begin trait definitions (`Num`, `Eq`, `Ord`, `Display`), collection functions (`map`, `filter`, `fold`) | Ring 2 `/typecheck` |
| `/platform` | Stdio platform DLL | Ring 2 `/backend` |
| `/repl` | Module navigation tests (`/mod`, `import`), trait introspection (`/info`), `/list` categories | Ring 2 compiler |
| `/port` | Validate exemplar module patterns against Ring 2 compiler, refine design | Ring 2 compiler |
| `/review` | Name resolution correctness, GOT/symbol-table separation, no god objects | all above |

**Acceptance criteria**:
- `(deftrait (Num a) (+ [a a] a) (- [a a] a) (* [a a] a))` — trait declaration type-checks
- `(impl Num Int ...)` — trait implementation
- `(defn add [x y] (+ x y))` infers `add :: (Fn [:Num a :a] :a)`, monomorphised at call sites
- `(import [core.option [*]])` — cross-module import
- Multi-sig: `(defn show ([Int x] ...) ([Bool x] ...))` dispatches correctly
- Auto-curry: `(map (+ 1) [1 2 3])` returns `[2 3 4]`
- `/stdlib` trait definitions compile and pass library tests
- ~150 additional integration tests green

## Ring 3: Meta

**Property**: Macros, derive, standard library completeness. Metaprogramming layer.

| Skill | Deliverables | Depends On |
|---|---|---|
| `/frontend` | Full macro system: `MacroExpander` implementation (mini-pipeline: parse -> typecheck -> compile -> execute), multi-clause `defmacro`, bracket destructuring, quasiquote | Ring 2 |
| `/stdlib` | Complete prelude using macros (`list`, `do`, `bind!`, `vec`, `cond`, `case`, threading macros), all `lib/core/` modules | Ring 3 `/frontend` |
| `/qa` | Macro integration tests, prelude tests, standard library tests | Ring 3 compiler |
| `/docs` | Language guide (feature-by-feature reference) | Ring 3 `/stdlib` |
| `/repl` | Macro expansion viewing (`/expand`), prelude discoverability, full `/list` taxonomy | Ring 3 compiler |
| `/port` | Implement pure core logic (data types, algorithms, unit tests) | Ring 3 `/stdlib` |
| `/review` | Macro pipeline structure (no god functions), `MacroExpander` impl cleanliness | all above |

**Acceptance criteria**:
- `(defmacro when [test body] \`(if ~test ~body nil))` — user macro compiles and expands
- Multi-clause macros: `(defmacro list () ... (x & xs) ...)` dispatches correctly
- `(list 1 2 3)` expands to nested `Cons`/`Nil`
- `(do (print "hello") (print "world"))` expands correctly (requires IO from Ring 4 for execution)
- Prelude macros all compile: `cond`, `case`, `->`, `->>`, `vec`
- `lib/prelude.cl` compiles fully
- ~100 additional integration tests green

## Ring 4: Effects

**Property**: IO model, platforms, parallelism, REPL, caching, executable generation. Side effects and build infrastructure.

| Skill | Deliverables | Depends On |
|---|---|---|
| `/typecheck` | IO ADT typing, `par-let`/`par-bind!` type checking | Ring 3 |
| `/backend` | IO trampoline, platform DLL loading and effect dispatch, parallel evaluation, module caching, linker, standalone executable generation | Ring 3 |
| `/qa` | IO tests, platform tests, E2E transcript tests, performance benchmarks, REPL implementation, `run-tests` special form | Ring 4 compiler |
| `/stdlib` | IO helpers (`pure`, `bind!`, `do`), trace display functions, complete standard library | Ring 4 |
| `/platform` | Test-capture platform DLL, platform documentation | Ring 4 `/backend` |
| `/examples` | IO programs, multi-file project examples | Ring 4 `/qa` |
| `/docs` | Complete tutorials, error message catalog | Ring 4 |
| `/repl` | Full experience test suite: all slash commands, trace, run-tests, hot-reload, performance benchmarks | Ring 4 compiler |
| `/port` | Complete exemplar project with IO, tests, walkthrough document, findings report | Ring 4 `/platform` |
| `/review` | JIT/cache path parity (single ISA construction), no duplicate code paths between batch and REPL | all above |

**Acceptance criteria**:
- `(print "hello")` produces IO effect
- `(do (print "hello") (print "world"))` chains IO effects
- `(par-let [x (compute-a) y (compute-b)] (+ x y))` — parallel evaluation
- Platform DLLs load and function (`cranelisp-stdio`, `cranelisp-test-capture`)
- Module caching: second compilation of unchanged module hits cache
- Standalone executable generation: `cranelisp --compile examples/hello.cl` produces executable
- REPL: all slash commands work (`/sig`, `/doc`, `/type`, `/info`, `/list`, `/expand`, `/mod`, etc.)
- Hot-reload: file changes auto-reload in REPL
- `(trace (fib 5))` — execution tracing
- `(run-tests ...)` — test runner with trace integration
- All ~470 portable integration tests from prototype pass
- All E2E transcript tests pass
- Performance within 2x of prototype on representative benchmarks
- REPL experience test suite passes (discoverability, self-documentation, performance targets)
- Exemplar project compiles, runs, and passes its own test suite
- `cargo clippy` clean across all crates

## Post-Ring 4: Release Compiler (Phase H)

**Property**: Tier 2 release backend for optimized builds. Optional — depends on full pipeline stability.

| Skill | Deliverables | Depends On |
|---|---|---|
| `/backend` | Tier 2 release backend (LLVM via inkwell or C code emission) | Ring 4 stable |
| `/qa` | Release build correctness tests (same semantics as JIT), performance benchmarks | Phase H `/backend` |
| `/docs` | Release build documentation, deployment guide | Phase H |

## Parallel Work Strategy

Within each ring, skills work against interface stubs:

1. **Frontend** produces stub AST for typechecker tests
2. **Typechecker** produces stub `CheckResult` for backend tests
3. **Backend** can test IR generation by constructing typed AST manually
4. **QA** wires stages as they become ready and runs integration tests
5. **User-proxy skills** engage as soon as their ring's compiler features are testable

Ring transitions are gated by `/review` completion review. All skills within a ring must pass review before the next ring begins.

## Dependency Summary

```
Phase B ─── Ring 0 ─── Ring 1 ─── Ring 2 ─── Ring 3 ─── Ring 4
  │           │           │           │           │           │
  │           │           │           │           │           ├── /qa (REPL, E2E, perf)
  │           │           │           │           │           ├── /stdlib (IO helpers)
  │           │           │           │           │           ├── /platform (test-capture)
  │           │           │           │           │           ├── /examples (IO programs)
  │           │           │           │           │           ├── /docs (tutorials, errors)
  │           │           │           │           │           ├── /repl (full experience suite)
  │           │           │           │           │           └── /port (exemplar complete)
  │           │           │           │           │
  │           │           │           │           ├── /frontend (macros)
  │           │           │           │           ├── /stdlib (prelude)
  │           │           │           │           ├── /docs (language guide)
  │           │           │           │           └── /port (core logic)
  │           │           │           │
  │           │           │           ├── /stdlib (traits, collections)
  │           │           │           ├── /platform (stdio DLL)
  │           │           │           ├── /repl (modules, traits)
  │           │           │           └── /port (validate design)
  │           │           │
  │           │           ├── /platform (runtime crate)
  │           │           └── /repl (ADT display)
  │           │
  │           ├── /examples (simple programs)
  │           ├── /docs (getting started)
  │           └── /repl (test harness + basic tests)
  │
  ├── /repl (experience spec)
  └── /port (project selection + design)
```
