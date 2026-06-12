---
number: 0318
target: /spec
filed_by: /sprint
filed_at: 2026-06-12
sprint_filed: 79
refers_to: spec/08-modules.md §8.11 (line 783 — "Platform functions that perform side effects MUST return IO _"), spec/10-io.md §10.10 (Platform ABI), src/platform.rs::register_platform_in_tc / parse_and_check_platform_type_sig, platforms/shapes/src/lib.rs
status: open
---

# All platform functions MUST return `IO _` (tighten the conditional; foreign purity is unverifiable)

## Issue (user-decided 2026-06-12, S79)

`spec/08-modules.md:783` currently states the IO requirement **conditionally**:
*"Platform functions that perform side effects MUST return `IO _`."* This presumes
the compiler can know whether a foreign function performs side effects — it cannot.
A platform DLL is foreign native code; the compiler must **trust the declared
signature**. A platform fn typed pure `(Fn [a] b)` is therefore treated as pure by
the typechecker — memoized, reordered, elided, sparked under lenient eval
(`compile_let_lenient`, `ivar_spark`) — while the host does whatever it wants.
Treating unverifiable foreign code as pure is **unsound**.

Every existing platform already returns `IO _` without exception — `stdio`
(`print : (Fn [String] (IO Int))`, `read-line : (Fn [] (IO String))`),
`test-capture` (incl. the literal no-op `commutative-noop : (Fn [] (IO Int))`).
The S79 `shapes` ADT-marshaling fixture introduced the **only** non-IO platform fn
(`area : (Fn [shapes/Rectangle] Int)`) — a design error on two counts: unsound, and
a genuinely-pure computation has no business crossing the FFI boundary (you would
write it in pure cranelisp).

## Resolution (user: "Tighten: all platform fns MUST be IO")

1. **`/spec`** — rewrite `spec/08-modules.md:783` from the conditional to the
   **unconditional**: *"Platform functions MUST return `IO _`."* Add the rationale
   (foreign purity is unverifiable; the compiler trusts the declared signature, so
   the only sound treatment of foreign code is to sequence its effects). Cross-ref
   `spec/10-io.md §10.10` (Platform ABI). A trusted-pure-FFI escape hatch, if ever
   wanted, is a separate explicit feature — NOT the default.
2. **Cascade — enforcement (`/dev`, int — `src/platform.rs`)**: `register_platform_in_tc`
   (after `parse_and_check_platform_type_sig`) MUST reject a platform fn whose
   checked return type is not `IO _`, with a clear diagnostic naming the platform +
   fn + the requirement. **Low-ripple — all existing platforms are already IO**, so
   enforcement breaks nothing once the `shapes` fixture is fixed. Folds into the S79
   Wave-A int work (same `src/platform.rs` surface as R1).
3. **Cascade — fixture (`/platform`, S79 Wave A)**: `platforms/shapes/` `area` →
   `(Fn [shapes/Rectangle] (IO primitives/Int))` (Rust impl follows the `stdio`
   IO-returning pattern). This also makes the round-trip program's `main` return
   `IO Int` — spec-conformant, resolving S79 Wave-0 reconciliation item #1.
4. **Test (`/qa` / `/dev` unit)**: a forcing test that a platform declaring a non-IO
   fn sig is rejected (a unit test over `register_platform_in_tc` with a `(Fn [Int] Int)`
   sig — no DLL needed; the check is on the sig string). Failing-not-ignored if
   authored before the enforcement lands.
5. **Annotation**: trace the (now unconditional) requirement at `spec/08-modules.md §8.11`
   to the enforcement test.

## Operational implication / Context

Surfaced when the user questioned the value of a pure platform fn in the S79 `shapes`
fixture. Unlike the `main : IO _` enforcement (FIXME 0317 — suite-wide sweep), this
is low-ripple: one fixture fix (already in S79 Wave A) + one enforcement check, no
existing platform violates the tightened rule. Candidate to land fully in S79.
