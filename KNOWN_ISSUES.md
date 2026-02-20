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

### Division by zero traps the process
`(/ x 0)` crashes the process via Cranelift's `sdiv` trap. No runtime check or error value.
Source: ROADMAP.md "Known rough edges"

### No stack overflow protection
Deep recursion silently crashes the process.
Source: ROADMAP.md "Known rough edges"

### No integer overflow checks
`iadd`/`isub`/`imul` wrap silently (64-bit two's complement).
Source: ROADMAP.md "Known rough edges"

### Non-exhaustive match panics at runtime
The compiler does not check match exhaustiveness. A missing arm causes a
runtime panic ("match failed") rather than a compile-time error.
Source: docs/adt.md, src/codegen/match_compile.rs

## Memory leaks (reference counting omissions)

### Match scrutinee not decremented
The scrutinee value is not dec'd after the match completes. Var-pattern
arms inc it (for safe multi-arm use) and scope exit decs the binding,
but the original reference leaks.
Source: docs/data-structures.md

### Closure drop glue deferred
When a closure is freed, its captured heap values are not decremented
because closures don't encode captured value types. Captures leak.
Source: docs/data-structures.md, docs/closures.md

### Function arguments not decremented by callee
Heap-typed values passed as arguments are not dec'd by the callee.
Source: docs/data-structures.md

### Let bindings embedded in return values use-after-free
When a `let` binding holds a heap value and that value is embedded inside
the return value (not the return value itself), `pop_scope_for_value`
still decrements it — causing use-after-free. Workaround: avoid `let`
bindings for values that will be embedded in the result; use inline
expressions or function parameters instead. Encountered in macro bodies
(e.g. `def` macro uses inline `make-def-name` calls instead of a `let`).
Source: lib/core.cl, src/codegen/expr.rs

### Per-use wrapper allocation
Each time a named function appears as a value, a new wrapper closure is
allocated. These are never cached or reused.
Source: docs/closures.md

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

## Module system limitations

- **Multi-file error formatting**: When an error occurs in a dependency module, the error context may reference the wrong source file.
- **No subtree access for private names**: Private definitions (`defn-`, `deftype-`) are hidden from all other modules. The plan specifies child modules should access parent private names, but this is not yet implemented.
- **No `mod-` (private submodule)**: The `mod-` form for declaring private submodules is not yet implemented.
- **No `super` references**: The `super` keyword for parent module access is not yet implemented.
- **Single-file programs don't support `import`/`export`**: These forms are only processed in multi-file projects via `run_project()`. The REPL supports `(import ...)` interactively.
- **Cross-module constrained polymorphism**: Monomorphised specializations are now compiled into the defining module's GOT (not the calling module's). This works across modules in both batch and REPL. However, constrained fns combined with multi-sig dispatch are not yet supported.
- **Module hot-reload is single-module only**: The REPL watches loaded `.cl` files and incrementally reloads changed modules. Type-incompatible changes (signature changes, removed definitions/types/traits/constructors) trigger rollback — the old code stays active and the module is locked until the file is fixed. Cascade recompilation of dependent modules is not yet supported; only the changed module is recompiled.
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

### No RC tests for closures capturing heap values
tests/rc.rs has 13 tests but none exercise closures that capture
strings, ADTs, or other closures. Leaks or use-after-free in captured
values would go undetected.

### No tests for runtime safety rough edges
Division by zero (process trap), integer overflow (silent wrap), and
stack overflow (silent crash) have zero tests documenting or guarding
their behavior.

### No tests for non-exhaustive match at runtime
No test exercises a match that falls through to the "match failed" panic
path. Regressions in the panic codegen would be invisible.

### No tests for Vec out-of-bounds access
vec-get and vec-set on invalid indices have no tests. The behavior
(crash? panic? undefined?) is undocumented and unverified.

### Thin error-path coverage
Only ~8 of 326 integration tests exercise error paths. Parse errors,
wrong-arity calls, unbound variables, and type inference failures are
lightly tested at the integration level.

### No tests for user-defined recursive ADTs with RC
List is prelude-defined and tested, but user-defined recursive types
(trees, etc.) have no tests verifying correct drop-glue generation or
reference counting.

### No REPL command tests
The 14 REPL slash commands (/sig, /doc, /type, /info, etc.) have no
integration tests.
