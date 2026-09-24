# stdio Platform Specification

**Name**: stdio
**Version**: 0.1.0
**ABI Version**: the host's current `ABI_VERSION` (the [version gate](../../design/platform/platform-dlls.md#1-the-version-gate); the constant's rustdoc carries its value)
**Purpose**: Standard input/output platform for interactive and batch programs. Provides console IO via stdin/stdout.

## Consumer Requirements

- **REPL**: `print :: (Fn [String] (IO Int))` for user-visible output at the prompt. The REPL forces the IO tree after each evaluation ([spec/10-io.md](../../spec/10-io.md) §10.6.2), so print output appears immediately.
- **Exemplar** (`exemplar/`): `print` for solution output in `bind!` chains.
- **Examples** (`examples/`): `print` to demonstrate the effect system — `bind!`, `do` and raw IO tree construction.

## Function Table

| Cranelisp Name | Type Signature | Scheduling Class | JIT Symbol | Description |
|---|---|---|---|---|
| `print` | `(Fn [String] (IO Int))` | Sequential | `cranelisp_print` | Blocking effect. When forced, prints the string followed by a newline to stdout and yields `0`. Consumes its argument (§Heap Parameter Ownership). |
| `read-line` | `(Fn [] (IO String))` | Sequential | `cranelisp_read_line` | Poll-shape leaf. When forced, reads one line from stdin, suspending on stdin readiness rather than blocking, and yields it with the trailing newline/carriage return removed. |

### Heap Parameter Ownership

A platform function consumes every heap-typed argument: the caller transfers its reference and does not release it after the call ([bounded contexts](../../design/arch/bounded-contexts.md) §4b invariant 6). Reading an argument without taking over that reference leaks it.

`print`'s `String` argument is read when the returned `Effect` node is forced, which may be later and more than once ([spec/10-io.md](../../spec/10-io.md) §10.8.1). The node therefore holds the transferred reference for its whole life and releases it once, when the node is freed — not when `print` returns and not per force. The implementation mechanism is the [capture-RC protocol](../../design/platform/platform-dlls.md#4-the-capture-rc-protocol): capture the argument as the `CLOwned` from `into_owned_consuming`, which takes over the transferred reference without incrementing. `own()` increments, so on a transferred argument it leaks one reference per call.

### Scheduling Rationale

Both functions are `Sequential` because they share global resources (stdout, stdin). Two `print` calls in one `bind!` chain must not interleave output. Two `read-line` calls must consume input lines in program order ([spec/10-io.md](../../spec/10-io.md) §10.12.2–10.12.3).

`print` declares the class directly. `read-line` declares a descriptor instead: a manifest-static stdin token at capacity 1 with the `Consume` role ([singleton resources](../../design/platform/poll-leaf-authoring.md#3-the-four-roles)). The host derives `Sequential` from its non-zero token, and the token admits at most one in-flight read.

### Return Conventions

- `print` yields `0` (success). The value exists so `bind!` chains can sequence print with other IO operations. A non-zero value is reserved for future error reporting.
- `read-line` yields the input line with its trailing newline/carriage return removed. End of input or a read error ends the current line: an unterminated remainder is yielded as the line, and an empty string when nothing remains.

## ABI Contract

The C calling convention is [spec/10-io.md](../../spec/10-io.md) §10.10. `declare_platform!` registers both functions, and the host loads them through the DLL's manifest entry point; the authoring and loading mechanics are [platform DLLs](../../design/platform/platform-dlls.md). `print` is an `extern "C"` function over `CL*` wrapper types returning a `CLIO` node; `read-line` is a poll-fn ([poll-leaf authoring](../../design/platform/poll-leaf-authoring.md)).

## Conformance

Any platform that exports the same function names with the same type signatures can substitute for stdio. The test-capture platform is the canonical substitute for deterministic testing. A conforming substitute:

1. MUST export `print` with signature `(Fn [String] (IO Int))`
2. MUST export `read-line` with signature `(Fn [] (IO String))`
3. MUST use the same scheduling classes (Sequential for both)
4. MUST consume `print`'s heap argument as §Heap Parameter Ownership states
5. MAY differ in observable behavior (e.g., capturing output instead of printing)
