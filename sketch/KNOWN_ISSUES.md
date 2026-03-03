# Known Issues

Implementation compromises and quality concerns in the current codebase,
from the perspective of a user. Each issue describes behavior that is
incorrect, surprising, or unreliable in code that has already been
implemented.

This is not a feature roadmap — missing features and planned work are
tracked in ROADMAP.md. Design documents in docs/ describe per-feature
limitations and future extensions.

Tests for these issues are in tests/integration.rs and tests/rc.rs,
marked with "KNOWN ISSUE" comments.

## Runtime safety

### Stack overflow protection is partial
Execution runs with a 64 MB stack (set via `build.rs` with
`cargo:rustc-link-arg-bins`, applying only to binary targets).
Self-recursive functions are safe via TCO. Deep mutual or indirect recursion
that exceeds the stack still silently crashes; no depth counter or user-facing
error is emitted. A proper depth counter is deferred to reimplementation.
Source: build.rs, ROADMAP.md item D

## Memory management (reference counting)

> Step 11 (Sound Memory Management) established the core RC model:
> consuming calling convention for cranelisp calls (callee owns params),
> borrowed convention for extern calls (caller decs temps), match scrutinee
> dec, constructor Var arg inc, closure drop glue, accessor field inc,
> liveness-based last-use optimization, atomic RC, uniqueness tracking
> with borrowed reads from unique owners, and static COW bypass.

### Borrowed reads conservative in branches and TCO
Uniqueness-based borrowed reads (Steps 11J-K) are disabled when `branch_depth > 0`
(inside if/match arms). This means field reads inside branches always emit inc/dec
even when the owner is known-unique. Additionally, TCO iterations do not re-establish
uniqueness for loop parameters — a non-last-use inc in the body permanently removes
uniqueness for subsequent iterations.
Source: src/codegen.rs (mark_unique, is_var_unique), src/codegen/vec_ops.rs,
src/codegen/apply.rs, src/codegen/match_compile.rs

### Wrapper closure bodies don't follow consuming convention
`compile_builtin_as_closure` and `compile_accessor_as_closure` generate
hand-compiled IR wrapper bodies without FnCompiler infrastructure. These
wrappers don't track their own params in scope_stack, so consumed heap-typed
params may leak. Rare in practice (only triggered when a builtin or accessor
is used as a first-class function value).
Source: src/codegen/closures.rs

### Per-use wrapper allocation
Each time a named function appears as a value, a new wrapper closure is
allocated. These are never cached or reused.
Source: docs/closures.md

## Trait system limitations

### No default methods on higher-kinded traits
Default method implementations are supported on regular traits but not on
higher-kinded traits (those with type constructor parameters like `(Functor f)`).
Attempting to add a default body to an HKT trait method produces a parse error.
This avoids complex type constructor application in default bodies.
Source: docs/spec/07-traits.md section 7.1.5

### Trait method resolution bypasses normal symbol lookup
`find_trait_for_method()` is a parallel lookup path that searches the
current module's trait declarations for a matching method name. This
duplicates what `lookup()` already does and does not respect local
shadowing — if a local variable shadows a trait method name, the trait
resolution still fires and pushes a spurious `pending_resolution`. The
multi-step pipeline (`find_trait_for_method` → `pending_resolutions` →
`MethodResolutions` string map → codegen string matching in
`compile_inline_primitive`) should be collapsed so that symbol lookup
resolves directly to a fully qualified dispatch target (GOT + slot),
with no intermediate string-based maps. This would also eliminate the
string pattern matching in codegen for inline primitives.
Source: src/typechecker.rs (`find_trait_for_method`),
src/typechecker/inference.rs (Apply tracking),
src/codegen/primitives.rs (`compile_inline_primitive`)

## IO model limitations

### `do` is IO-specific
The `do` macro now expands to `bind` chains (previously `let` chains). This means
all expressions in a `do` block must have type `IO _`. For pure sequencing, use
`let [_ expr1] expr2`.
Source: lib/core/syntax.cl, docs/io.md

### Effect thunk captures managed via CLOwned
Platform `Effect` nodes contain opaque Rust closures that may capture cranelisp
values (e.g. CLString pointers). These captures are now tracked via `CLOwned<T>`
in the platform crate — `CLOwned::new()` atomically incs the RC header, and
`Drop` atomically decs it (freeing if rc reaches 0). Platform functions use
`s.own()` to wrap captured values before moving them into Effect closures.
This ensures captured values survive caller-side dec after the call returns.
Source: cranelisp-platform/src/lib.rs (CLOwned, CLString::own)

### Trampoline continuation stack not RC-tracked
The `IoTask::run()` trampoline maintains an explicit `Vec<Continuation>` stack.
Continuation closures on this stack are not RC-incremented on push or decremented
on pop. Now that closure drop glue is implemented, these closures could
potentially be tracked, but the trampoline operates in Rust space outside the
compiler's codegen.
Source: src/intrinsics.rs

## Lenient evaluation (automatic parallelism)

### IVar drop glue not implemented
IVar cells (used for lenient evaluation of independent `let` bindings) have no
drop glue. If an IVar were freed without being forced, the contained thunk closure
and any captured values would leak. This is safe in practice because the barrier-force
model guarantees all IVars are forced before scope exit — no IVar is ever freed
without its value being extracted. A future per-use-site forcing model would need
IVar drop glue.
Source: src/codegen/expr.rs, cranelisp-runtime/src/intrinsics.rs

### Barrier-force instead of per-use-site forcing
Lenient evaluation uses a barrier model: all sparkable bindings in a `let` block are
created and sparked, then all are forced in binding order before the body executes.
This is simpler than true per-use-site forcing (where each IVar is forced only at its
first use in the body/subsequent bindings) but may reduce parallelism — the body
cannot begin until all sparked bindings have resolved, even if some are used late.
Source: docs/concurrency.md (Phase 7)

## Surprising behavior

### ADT accessor name collisions
Accessor functions for ADT fields use a "first wins" rule within a single
compilation unit. Two types with the same field name: the first type's
accessor wins. Use dotted syntax (`Type.field`) to disambiguate.
Source: docs/adt.md

### Dotted trait method dispatch with same-named methods
When two traits define the same method name (e.g. `Display.show` and
`Debug.show`), dotted syntax like `(Display.show 42)` type-checks
correctly but `resolve_methods` does not track which trait the call
belongs to. If both traits have implementations for the same type,
the wrong implementation may be dispatched. Bare `show` correctly
errors as ambiguous with qualified alternatives listed.
Source: docs/name-resolution.md, tests/integration.rs (ignored test:
`ambiguous_trait_method_dotted_name_works`)

### Closure capture order is non-deterministic
Captures are collected via HashSet iteration, so closure layout may vary
between compilations. Semantically correct but non-deterministic.
Source: docs/closures.md

### Macro error spans point to call site
Errors inside macro expansions report the macro call site, not the
location within the macro definition body.
Source: docs/macros.md

### Sexp/SList types bypass reference counting
The `Sexp` and `SList` types (used only during compile-time macro expansion)
are classified as `NeverHeap` to avoid RC double-dec bugs during macro execution.
This means Sexp/SList values are never reference-counted and will leak their
allocations. Since macros only execute at compile time with bounded input,
this is acceptable until Phase 5's integrated memory management rewrite.
Source: src/codegen.rs (`heap_category`, `classify_heap_type`)

### User file name collides with library module name
If a user file has the same name as a library module (e.g., `derive.cl`
colliding with `lib/core/derive.cl`), the module system may load the wrong
file, causing ambiguous name errors. Workaround: avoid naming user files
after core library modules (`derive`, `syntax`, `numerics`, `io`, etc.).
Source: src/module.rs (`resolve_module`)

## Module system limitations

- **Multi-file error formatting**: When an error occurs in a dependency module, the error context may reference the wrong source file.
- **No subtree access for private names**: Private definitions (`defn-`, `deftype-`) are hidden from all other modules. The plan specifies child modules should access parent private names, but this is not yet implemented.
- **No `mod-` (private submodule)**: The `mod-` form for declaring private submodules is not yet implemented.
- **Single-file programs without `(mod)` or `(platform)` declarations don't support `import`/`export`**: Files with no `(mod ...)` or `(platform ...)` declarations use the simple `run()` path which does not process `(import)` or `(export)` forms. Multi-file projects (those with `(mod)` declarations), platform-using programs, and the REPL support imports/exports fully. Workaround: add a trivial `(mod name)` or `(platform ...)` declaration to trigger ModuleGraph.build().
- **Cross-module constrained polymorphism**: Monomorphised specializations are now compiled into the defining module's GOT (not the calling module's). This works across modules in both batch and REPL. However, constrained fns combined with multi-sig dispatch are not yet supported.
- **Module hot-reload cascade is BFS-ordered**: The REPL watches loaded `.cl` files, reloads changed modules, then cascade-reloads all transitive dependents in BFS order. Type-incompatible changes (signature changes, removed definitions/types/traits/constructors) trigger rollback — the old code stays active and the module is locked until the file is fixed. If a dependent fails during cascade, it is locked and cascade stops for its sub-dependents.
- **REPL type-breaking redefinitions refused**: Redefining a previously compiled function with a different type signature at the REPL prompt is refused with an error. This prevents silently corrupting callers that were compiled against the old type. To change a function's type, edit the source file — file changes trigger cascade recompile.
- **Macros are session-wide**: Macros compiled during module loading are available regardless of current namespace. Module-scoped macro visibility is not yet implemented.
- **REPL module loading requires project root**: `/mod <name>` and auto-loading of qualified references discover modules relative to the project root (CWD for bare REPL, parent of entry file for `cranelisp foo.cl`). Modules outside the project root tree are not discoverable.
- **Root module ambiguity**: A file `b.cl` at the project root is findable as both `b` (root module via import) and `a.b` (submodule if `a` has `(mod b)` and `b.cl` is a sibling of `a.cl`). The same file could appear in the graph under two module IDs.
- **No REPL prelude opt-out**: Modules created via `(mod foo)` at the REPL automatically receive implicit prelude imports. There is no way to create a prelude-free module interactively. An explicit `(import [prelude []])` does not remove already-installed prelude names. Future fix: detect prelude import override at the REPL and force a full module recompile to remove stale bare names.

## Compiled module cache limitations

### Interactive definitions cached only on save
Interactive definitions entered at the REPL prompt are written to cache when the
module source file is saved (after each definition). However, the cache is rebuilt
from the saved `.cl` source, so transient REPL state (expressions, intermediate
let bindings) is not cached — only persisted definitions.
Source: src/repl.rs, src/cache.rs

### Constrained fn specializations cached with defining module
Monomorphised specializations (e.g. `add$Int+Int`) are now compiled into their
defining module's `.o` file via deferred cache writes. When a later module calls
a constrained fn, the specialization is generated and written back into the
defining module's cache. However, if the defining module was loaded from cache
and a new specialization is needed, the defining module's `.o` is re-written.
Source: src/batch.rs, src/repl.rs, docs/constrained-polymorphism.md

### Stale caches from incompatible versions
The cache manifest records the cranelisp version string and a SHA-256
fingerprint of the running binary. Any `cargo build` that changes the
compiler binary automatically invalidates all cached modules on next run.
This covers code changes, dependency updates (`cargo update`), and
debug/release mode switches. If `current_exe()` fails (rare), the
fingerprint check is skipped and only version/triple/format checks apply.
Source: src/cache.rs, src/linker.rs

## Flaky tests

### `dotted_field_accessor_resolution` kills the test process
The `dotted_field_accessor_resolution` integration test sometimes kills the
entire test process when running in parallel with other tests. The test
exercises a runtime panic path (non-exhaustive match or similar) that calls
`process::exit(1)` from the JIT, which terminates the OS process rather than
just the test thread. When this test runs concurrently with others, the exit
kills the whole `cargo test` harness, producing a spurious failure. Running
tests with `--test-threads=1` avoids the issue.

## Test coverage gaps

Areas where missing tests may mask user-facing bugs.

### Checked arithmetic panic tests require `--ignored --test-threads=1`
Tests for checked arithmetic (overflow, division by zero) are `#[ignore]`
because `cranelisp_panic` calls `process::exit(1)`, which kills the test
harness. Run them with `cargo test -- --ignored --test-threads=1`.
Stack overflow has no test (the 64 MB stack makes it hard to trigger
without intentionally exhausting it).

### Vec out-of-bounds tests are `#[ignore]`
Tests for vec-get and vec-set on invalid indices exist (`vec_get_out_of_bounds_panics`
and related in tests/integration.rs) but are marked `#[ignore]` because
`cranelisp_panic` calls `process::exit(1)`, killing the test harness.
Run with `cargo test -- --ignored --test-threads=1`.

### Thin error-path coverage
~20 dedicated error tests now exist (added in pre-reimplementation item B),
exercising parse errors, type inference failures, wrong-arity calls, and
trait method errors. Coverage remains thin relative to total tests; module
resolution errors, macro expansion errors, and import validation could use
additional coverage.

### REPL command tests are partial
8 of 16 slash commands are now tested (`/sig`, `/info`, `/type`, `/list`)
in tests/integration.rs. Still untested: `/doc`, `/source`, `/sexp`,
`/ast`, `/clif`, `/disasm`, `/time`, `/mem`, `/expand`, `/mod`,
`/reload`, `/run-tests`.
