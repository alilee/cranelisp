# test-capture Platform Specification

**Name**: test-capture
**Version**: 0.1.0
**ABI Version**: 1 (cranelisp-platform ABI_VERSION)
**Purpose**: Drop-in replacement for stdio that captures output and scripts input for deterministic testing. No console IO occurs.

## Consumer Requirements

### From /qa

- Same function signatures as stdio (`print`, `read-line`) -- drop-in substitution so tests exercise the same IO code paths without console side effects.
- `test_capture_set_input` -- Queue input lines before a test run so `read-line` returns predictable values.
- `test_capture_get_output` -- Retrieve all captured print output after a test run for assertion.
- `test_capture_reset` -- Clear both input queue and output buffer between tests to prevent cross-test contamination.
- `test_capture_free_output` -- Free the output buffer returned by `test_capture_get_output`.

## Platform Functions

These are registered with the JIT via `declare_platform!` and are visible to Cranelisp code as ordinary IO functions.

| Cranelisp Name | Type Signature | Scheduling Class | JIT Symbol | Description |
|---|---|---|---|---|
| `print` | `(Fn [String] (IO Int))` | Sequential | `cranelisp_print` | Append the string to the captured output buffer (no console output). Returns `(IO Int)` with value 0. |
| `read-line` | `(Fn [] (IO String))` | Sequential | `cranelisp_read_line` | Pop and return the first queued input line. Returns empty string if the queue is empty. |
| `commutative-noop` | `(Fn [] (IO Int))` | Commutative | `cranelisp_commutative_noop` | No-op that returns 0. Enables testing that the compiler correctly identifies commutative pairs and inserts Par nodes. |
| `commutative-sleep-ms` | `(Fn [Int] (IO Int))` | Commutative | `cranelisp_commutative_sleep_ms` | Sleep for the specified milliseconds and return the duration. Enables timing-based parallelism verification. |
| `resource-serial-noop` | `(Fn [Int] (IO Int))` | ResourceSerial | `cranelisp_resource_serial_noop` | No-op that sets the resource token on its Effect node. Enables testing resource token serialization. |
| `fault-now` | `(Fn [] (IO Int))` | Sequential | `cranelisp_fault_now` | Panics inside the deferred IO Effect body when forced, so the S81 fault funnel raises a `PlatformError::DispatchError { fn_name: "platform.test-capture/fault-now" }` DURING the IO trampoline. Enables witnessing the during-IO dispatch-fault path end-to-end (FIXME 0401). Never returns the clean `(IO Int)` value — the body always faults. |

### Heap Parameter Ownership

The compiler uses a consuming calling convention (`compile_consuming_arg_list`): callers transfer ownership of heap-typed arguments to the callee. The caller does NOT decrement the reference count after the call returns. This means every platform function MUST consume every heap-typed parameter it receives, regardless of whether it needs to retain the value.

**Rules for platform function implementors:**

1. **If you capture the value** (e.g., storing it in a buffer): call `.own()` on the `CL*` wrapper. This takes ownership without incrementing the reference count, since the caller already transferred its count to you.
2. **If you do not capture the value** (e.g., you read it and discard): call `.own()` to take ownership, then let the owned value drop normally. The `Drop` impl will decrement the reference count and free the allocation if it reaches zero.
3. **Never borrow without `.own()`**: A platform function that reads a heap parameter without calling `.own()` will leak the allocation. The caller has already relinquished its reference count, so nobody will free the value.

**Example — `print`**: The `print` function receives a `CLString` parameter. It calls `.own()` to take ownership, reads the string content to append to the capture buffer, and then the owned value is dropped at function exit, decrementing the reference count.

### Behavioral Differences from stdio

- `print` appends to an in-memory `Vec<String>` instead of writing to stdout. Each call is one entry; entries are joined with newlines by `test_capture_get_output`.
- `read-line` pops from a `VecDeque<String>` instead of reading from stdin. Returns empty string on exhaustion (does not block).

## Test Utility Functions (C-ABI Exports)

These are **NOT** platform functions -- they are not in the `declare_platform!` manifest and are not registered with the JIT. They are exported from the cdylib for direct use by Rust test code via `libloading`.

| C Symbol | Signature | Description |
|---|---|---|
| `test_capture_set_input` | `(lines: *const *const u8, lens: *const usize, count: usize)` | Queue `count` input lines. Clears any previously queued input. Each `lines[i]` must point to `lens[i]` bytes of valid UTF-8. |
| `test_capture_get_output` | `(out_ptr: *mut *const u8, out_len: *mut usize)` | Write pointer and length of captured output (newline-joined) to `out_ptr`/`out_len`. Caller must free via `test_capture_free_output`. |
| `test_capture_free_output` | `(ptr: *mut u8, len: usize)` | Free a buffer previously returned by `test_capture_get_output`. |
| `test_capture_reset` | `()` | Clear both the captured output buffer and the input queue. |

### Thread Safety

Both `OUTPUT` and `INPUT` are protected by `Mutex`. Poison recovery uses `into_inner()` so tests never deadlock on a panicked predecessor.

### Test Lifecycle

A typical test sequence:

1. `test_capture_reset()` -- clean state
2. `test_capture_set_input(...)` -- queue expected inputs (if testing `read-line`)
3. Execute Cranelisp code that calls `print`/`read-line`
4. `test_capture_get_output(...)` -- retrieve and assert on captured output
5. `test_capture_free_output(...)` -- free the output buffer

## Conformance

test-capture conforms to the stdio platform interface for core IO:

1. Exports `print` with signature `(Fn [String] (IO Int))` -- same as stdio
2. Exports `read-line` with signature `(Fn [] (IO String))` -- same as stdio
3. Uses the same scheduling classes for stdio-compatible functions (Sequential for both)
4. Respects the capture-RC protocol for heap parameters
5. Substitutable for stdio in any program that does not depend on console I/O behavior

Additionally, test-capture provides scheduling-class test functions (`commutative-noop`, `commutative-sleep-ms`, `resource-serial-noop`) and a fault-injection function (`fault-now`) that are not part of the stdio interface. These exist solely for testing auto IO scheduling and dispatch-fault surfacing, and are not expected to be present in other platforms.
