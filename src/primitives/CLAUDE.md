# Primitives, Platform, and Intrinsics — Naming Conventions

Three categories of Rust `extern "C"` functions are registered with the JIT:

## 1. Intrinsics (`src/intrinsics.rs`) — language-internal machinery

Rust fn names do **not** use `cranelisp_` prefix. JIT symbol strings **do** use the prefix.

| Rust function | JIT symbol |
|---|---|
| `alloc` | `"cranelisp_alloc"` |
| `panic` | `"cranelisp_panic"` |
| `free` | `"cranelisp_free"` |

These are never visible to the user. They implement internal concerns (heap allocation, match exhaustiveness failure, refcount lifecycle). Also exports `alloc_with_rc` (not `extern "C"`) for use by Rust primitives that allocate heap objects.

## 2. Platform (`src/platform.rs`) — user-visible side effects

Rust fn names do **not** use `cranelisp_` prefix. JIT symbol strings **do** use the prefix.

| Rust function | JIT symbol |
|---|---|
| `print_string` | `"cranelisp_print"` |
| `read_line` | `"cranelisp_read_line"` |

These implement IO effects exposed to the language (`print`, `read-line`). The JIT prefix namespaces them away from user-defined functions.

## 3. Primitives (`src/primitives/`) — pure bootstrap functions

Rust fn names and JIT symbol strings **neither** use the `cranelisp_` prefix.

| Rust function | JIT symbol |
|---|---|
| `int_to_string` | `"int-to-string"` |
| `float_to_string` | `"float-to-string"` |
| `bool_to_string` | `"bool-to-string"` |
| `string_identity` | `"string-identity"` |
| `parse_int` | `"parse-int"` |
| `op_add` | (registered via loop) |

These are pure functions called from prelude trait impls. They have no prefix because they are resolved by the trait/method system (mangled names like `show$Int`), not by user code directly.

**Exception — operator wrappers**: `op_add`, `op_fadd`, etc. live in `primitives/` with no Rust prefix, but their JIT symbols use `cranelisp_` (`"cranelisp_op_add"` etc.) to namespace them. This is because operators can be used as first-class values (`(let [f +] ...)`), so they need dedicated JIT symbols distinct from user functions.

## When adding new functions

- **Internal to the compiler** (alloc, GC, panic) → intrinsics, no prefix on Rust fn, `cranelisp_` on JIT symbol
- **User-visible IO effect** (print, read, write-file) → platform, no prefix on Rust fn, `cranelisp_` on JIT symbol
- **Pure computation** (type conversions, string ops) → primitives, no prefix on either

The `cranelisp_` prefix exists only in JIT symbol strings — never on Rust function names. Its purpose is to namespace compiler-internal and platform symbols away from user-defined functions in the JIT symbol table.
