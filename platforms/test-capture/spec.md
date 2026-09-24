# test-capture Platform Specification

**Name**: test-capture
**Version**: 0.1.0
**ABI Version**: the host's current `ABI_VERSION`, as for [stdio](../stdio/spec.md)
**Purpose**: Drop-in replacement for stdio that captures output and scripts input for deterministic testing. No console IO occurs.

## Consumer Requirements

### Test harness (`qa`, `test`)

- Same function signatures as stdio (`print`, `read-line`) -- drop-in substitution so tests exercise the same IO code paths without console side effects.
- `test_capture_set_input` -- Queue input lines before a test run so `read-line` returns predictable values.
- `test_capture_get_output` -- Retrieve all captured print output after a test run for assertion.
- `test_capture_reset` -- Clear both input queue and output buffer between tests to prevent cross-test contamination.
- `test_capture_free_output` -- Free the output buffer returned by `test_capture_get_output`.

## Platform Functions

These are registered with the JIT via `declare_platform!` and are visible to Cranelisp code as ordinary IO functions. `pure-int` and `pure-string` return `Pure` nodes; every other function returns a blocking `Effect` node whose work happens each time the node is forced.

| Cranelisp Name | Type Signature | Scheduling Class | JIT Symbol | Description |
|---|---|---|---|---|
| `print` | `(Fn [String] (IO Int))` | Sequential | `cranelisp_print` | Append the string to the captured output buffer (no console output). Yields `0`. Consumes its argument as [stdio's `print`](../stdio/spec.md#heap-parameter-ownership) does. |
| `read-line` | `(Fn [] (IO String))` | Sequential | `cranelisp_read_line` | Pop and return the first queued input line. Returns empty string if the queue is empty. |
| `commutative-noop` | `(Fn [] (IO Int))` | Commutative | `cranelisp_commutative_noop` | No-op that returns 0. Enables testing that the compiler correctly identifies commutative pairs and inserts Par nodes. |
| `commutative-sleep-ms` | `(Fn [Int] (IO Int))` | Commutative | `cranelisp_commutative_sleep_ms` | Sleep for the specified milliseconds and return the duration. Enables timing-based parallelism verification. |
| `resource-serial-noop` | `(Fn [Int] (IO Int))` | ResourceSerial | `cranelisp_resource_serial_noop` | No-op that sets the given resource token on its Effect node. Enables testing resource token serialization. |
| `resource-serial-sleep-ms` | `(Fn [Int Int] (IO Int))` | ResourceSerial | `cranelisp_resource_serial_sleep_ms` | Set the given resource token (first argument), sleep for the given milliseconds (second) and return the duration. Enables timing-based verification that same-token effects serialize and different-token effects run concurrently. |
| `fault-now` | `(Fn [] (IO Int))` | Sequential | `cranelisp_fault_now` | Panics inside the deferred IO Effect body when forced, so the host raises `PlatformError::DispatchError { fn_name: "platform.test-capture/fault-now" }` during the IO trampoline. Enables witnessing the during-IO dispatch-fault path end-to-end. Never returns the clean `(IO Int)` value — the body always faults. |
| `pure-int` | `(Fn [] (IO Int))` | Sequential | `cranelisp_pure_int` | Returns a DLL-constructed `Pure` node holding `121`. Enables testing scalar `Pure` adoption at the platform return. |
| `pure-string` | `(Fn [] (IO String))` | Sequential | `cranelisp_pure_string` | Returns a DLL-constructed `Pure` node holding `"s121-platform-pure"`. Enables testing owning `Pure` adoption at the platform return. |

`print` is the only function taking a heap argument.

### Behavioral Differences from stdio

- `print` appends to an in-memory `Vec<String>` instead of writing to stdout. Each force appends one entry; entries are joined with newlines by `test_capture_get_output`.
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

Both `OUTPUT` and `INPUT` are protected by `Mutex`. Poison recovery uses `into_inner()`, so a panicked predecessor does not make later calls fail.

### Test Lifecycle

A typical test sequence:

1. `test_capture_reset()` -- clean state
2. `test_capture_set_input(...)` -- queue expected inputs (if testing `read-line`)
3. Execute Cranelisp code that calls `print`/`read-line`
4. `test_capture_get_output(...)` -- retrieve and assert on captured output
5. `test_capture_free_output(...)` -- free the output buffer

## Conformance

test-capture meets [stdio's conformance requirements](../stdio/spec.md#conformance) 1–4, and is substitutable for stdio in any program that does not depend on console I/O behavior.

Additionally, test-capture provides scheduling-class test functions (`commutative-noop`, `commutative-sleep-ms`, `resource-serial-noop`, `resource-serial-sleep-ms`), a fault-injection function (`fault-now`) and `Pure`-returning functions (`pure-int`, `pure-string`) that are not part of the stdio interface. These exist solely for testing auto IO scheduling, dispatch-fault surfacing and platform-return adoption, and are not expected to be present in other platforms.
