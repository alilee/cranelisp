---
number: 0095
target: /arch
filed_by: /design
filed_at: 2026-05-01
sprint_filed: 64
refers_to: design/arch/facades/backend.md §"Linker — the cache-load retention newtype", design/arch/decisions/0037-cache-hit-integration-inside-register-module.md
status: open
---

# Pin `Linker::get_symbol` typed-Result shape in the backend facade

## Issue

The facade `design/arch/facades/backend.md` §"Linker — the cache-load retention newtype" specifies:

```rust
pub fn get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>;
```

A typed Result with a typed `LinkerError`. The current source (`crates/cranelisp-backend/src/cache/linker.rs:183`) implements:

```rust
pub fn get_symbol(&self, name: &str) -> Option<*const u8>
```

An `Option`-returning method with a bare `&str` argument.

Decision 37 ("no swallowed failures") specifies that callers MUST treat resolution failure as `CacheLoadError`, not silently push NULL. The pre-Sprint-58 `worker.rs:2810-2823` regression came from the `Option → silent skip` pattern. The facade's typed-Result shape makes the safety contract facade-visible to integration-layer reviewers — they cannot accidentally `.ok()` away a None.

The contract is **correct** as the facade states it; the source has not yet caught up. But unless the facade names the `LinkerError` variants and `cranelisp-types` defines the enum, this remains aspirational documentation rather than a compile-time-enforceable contract.

## Proposed resolution

1. `/arch` defines `LinkerError` in `cranelisp-types` (likely a small enum: `SymbolNotFound { module, symbol }`, `RelocationFailed { … }`, etc.). Owner: `cranelisp-types` is `/arch`-only.
2. `/arch` confirms the `LinkerSymbol` newtype usage in `get_symbol`'s signature (newtype already exists per `design/arch/CLAUDE.md` §"String Newtypes"). The current `&str` is a Principle-7-violation candidate (bare strings where typed identifiers belong).
3. `/arch` either (a) tightens the facade with the explicit `LinkerError` enum variants, or (b) confirms the current loose facade text is intentional and the enum definition will be added when implementation lands. Either way, the facade stops being silent on the typed shape.

Once landed, backend's `cache/linker.rs::get_symbol` refactors to the typed shape (a `/dev` task). `int`'s callers refactor from `match get_symbol(name) { None => skip }` to `let ptr = get_symbol(name)?` (which is the pre-S58 regression net per Decision 37).

## Operational implication / Context

This is a contract-tightening question, not a contract-correctness question. The current facade text is internally consistent (it states the typed shape; the source does not yet match); but absent the `LinkerError` definition in `cranelisp-types`, the typed shape is unbuildable.

The risk of leaving this open: the next implementation pass at the linker may follow the source-current `Option` shape rather than the facade-target `Result` shape, perpetuating the divergence and weakening Decision 37's regression net.

Resolution is a small `cranelisp-types` addition + a facade pin. Estimated `/arch` cost: 30 min.
