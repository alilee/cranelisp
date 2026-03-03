# Pure Tracing

## Overview

`(trace expr)` is a special form that evaluates `expr` while recording function call
boundaries, returning a `Trace` ADT representing the execution tree.

Tracing is pure — the trace tree is a return value, not a side-effect.

## Trace ADT

Built-in synthetic ADT (like `Sexp`) — defined by the compiler, populated by the runtime,
manipulated as a regular Cranelisp value.

```clojure
(deftype Trace
  (TraceCall [:String tname
              :(SList String) tparams    ;; formatted argument values (one string per arg)
              :String tresult            ;; formatted return value
              :(SList Trace) tchildren   ;; nested calls made during this call
              :Int tnanos]))             ;; wall-clock duration in nanoseconds
```

Field names use the `t` prefix to avoid collision with user-defined ADT fields (mirroring
the `s` prefix on `SList` fields).

Heap indices (tag=0 at ptr[0]): tname=1, tparams=2, tresult=3, tchildren=4, tnanos=5.

Formatting uses `cranelisp_trace_format` — a JIT symbol that calls `format_result_value`
from `src/repl/format.rs` via a thread-local `TRACE_TC_PTR: *const TypeChecker`. This
handles ADTs, Vecs, closures, and all other types correctly.

## Syntax

```clojure
;; Trace current module (default)
(trace (factorial 4))

;; Bind and manipulate
(def t (trace (factorial 4)))
(trace-depth t)
(trace-flatten t)
```

## Module-scoped tracing

The module system provides natural trace scoping:

- **Primitives** (`+`, `-`, `*`): Inlined as Cranelift IR — no function call, invisible
  to trace.
- **Platform functions** (`print`, `read-line`): Excluded (no GOT slot in user modules).
- **User module functions**: Traced — all loaded modules with GOT entries are instrumented.
- **Stdlib functions**: Traced if loaded into the session.

## Runtime mechanism: GOT copy-swap

Functions are called via per-module GOT indirection. Tracing works by swapping GOT
entries with thin JIT-compiled wrapper functions:

1. **Wrapper compilation** (at `trace` JIT compile time): For each user function with a
   GOT slot, compile a thin wrapper that calls `cranelisp_trace_enter`, the original via
   `call_indirect` (embedding the original code_ptr as a constant), then
   `cranelisp_trace_exit`.

2. **GOT swap** (at `trace` evaluation time):
   - `cranelisp_trace_swap_got` allocates a saved-GOT copy (memcpy), builds a debug-GOT
     with wrapper pointers substituted, then installs it via a single atomic memcpy.
   - Pushes a synthetic `"::trace::"` root frame on the trace stack.
   - Returns the saved-GOT pointer for later restoration.

3. **Evaluate**: Run the traced expression. Wrappers push/pop `TraceFrame` entries,
   building a call tree on the `TRACE_STACK`.

4. **Restore**: `cranelisp_trace_restore_got` memcpy's the saved GOT back and frees it.

5. **Collect**: `cranelisp_collect_trace` pops the root frame, builds the `TraceCall` ADT
   tree, releases the trace role, and returns the heap pointer.

### GOT swap atomicity

The debug-GOT is built in a temporary buffer. Installation is a single `memcpy` of
`GOT_TABLE_SIZE * 8` bytes (8 KiB). There is no partial-swap window where some slots
point to wrappers and others to originals.

### Wrapper call-through

Wrappers embed the original code_ptr as a Cranelift `iconst`. This means recursive calls
within the original function still go through the GOT (now pointing to wrappers), building
the nested call tree naturally.

## Thread safety

A process-global `TRACE_THREAD_ID: AtomicU64` tracks which OS thread owns the trace
role. Thread IDs are assigned via a monotonic counter stored in `thread_local!` storage
(stable across call depths on the same thread).

- `cranelisp_trace_swap_got`: CAS `0 → my_tid`. On failure, pushes a `"::skipped::"` frame
  and returns a sentinel so `restore_got` is a no-op.
- `cranelisp_trace_enter` / `cranelisp_trace_exit`: no-op if calling thread ≠ trace thread.
- `cranelisp_collect_trace`: CAS `my_tid → 0` to release the role.

This handles:
- Concurrent traces on different threads (first CAS wins; other threads skip).
- Nested `(trace (trace body))` (inner trace's swap fails; outer collects the tree).

## Lenient evaluation interaction

Lenient evaluation (`let` binding sparking) runs independent bindings on rayon thread-pool
threads. Since those threads do not own the trace role, their calls are absent from the
trace tree. Lenient evaluation is disabled inside `trace` bodies via the `in_trace_body`
flag on `FnCompiler`, making the body fully sequential.

Explicit `par-let` inside a `trace` body is a known limitation: sparked computations are
not traced (documented in `KNOWN_ISSUES.md`).

## Stdlib helpers (`lib/core/trace`)

Standard library functions for working with trace trees:

```clojure
;; Accessors
(trace-name     :: Trace -> String)
(trace-params   :: Trace -> (SList String))  ;; formatted parameter values
(trace-result   :: Trace -> String)          ;; formatted return value
(trace-children :: Trace -> (SList Trace))
(trace-nanos    :: Trace -> Int)

;; Tree operations
(trace-depth    :: Trace -> Int)           ;; maximum call depth
(trace-flatten  :: Trace -> (SList Trace)) ;; all nodes in pre-order

;; Display
(trace-params-string :: (SList String) -> String)  ;; " p1 p2 ..."
(trace-call-string   :: Trace -> String)            ;; "(name p1 p2 ...)"
(trace-show          :: Trace -> String)            ;; "(name p1 ...) => result [Xms]"
(trace-show-children :: (SList Trace) -> String -> String) ;; recursive tree display
(trace-show-tree     :: Trace -> String)            ;; full tree, skips ::trace:: root
```

Example output of `(println (trace-show-tree (trace (factorial 5))))`:

```
(factorial 5) => 120 [0ms]
  (factorial 4) => 24 [0ms]
    (factorial 3) => 6 [0ms]
      (factorial 2) => 2 [0ms]
        (factorial 1) => 1 [0ms]
```

## Design properties

- **Pure**: Trace is a return value, not a side-effect.
- **Composable**: Trace ADT is a regular value — bind it, pass it, transform it.
- **Zero-cost when off**: No overhead in non-trace execution paths.
- **Module-scoped**: All loaded user modules are instrumented; stdlib optionally traced.
- **Thread-safe**: `TRACE_THREAD_ID` ensures only one thread traces at a time.
