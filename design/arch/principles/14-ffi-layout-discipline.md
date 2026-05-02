---
number: 14
title: FFI boundary types are governed by layout discipline
---

# Principle 14 — FFI boundary types are governed by layout discipline

**Statement.** Public DTOs that cross the C ABI — those carrying `#[repr(C)]` or `#[repr(transparent)]` — are layout-stable contracts, not source-stable contracts. The `#[non_exhaustive]` rule (Facade convention item 3) does NOT apply to them; their evolution is governed by an explicit version field — typically an `ABI_VERSION` const bumped on any layout-affecting change. `#[repr(transparent)]` is included because, although the type system forbids most field additions, the underlying primitive type IS the ABI: a change from `i64` to `u64` (or any other underlying-type swap) is binary-breaking against JIT-emitted code that reads the wrapper as raw bits, and `#[non_exhaustive]` would not catch that change either.

**Rationale.** `#[non_exhaustive]` guards source-level breakage: external consumers cannot construct or exhaustively destructure, so a new field doesn't force a callsite update. That is the wrong protection at the C ABI. Cranelift JIT-emitted code, host-loaded platform DLLs, and the IO trampoline all read these structs by hard-coded byte offsets. Adding a field is *source-non-breaking* in Rust but *binary-breaking* against the JIT and the loaded DLLs — every offset past the new field shifts, and code that was generated against the old layout reads garbage or crashes.

A `#[non_exhaustive] #[repr(C)]` struct misleads maintainers: the source-level annotation says "safe to add fields," but the layout annotation means the opposite. The two regimes belong to two different audiences (Rust callers vs. JIT-emitted code or DLL hosts), and conflating them produces silent corruption — the worst failure mode.

**Consequence.**

- `#[repr(C)]` and `#[repr(transparent)]` DTOs do NOT carry `#[non_exhaustive]`. The absence of `#[non_exhaustive]` IS the signal that this is a layout contract: any change is a breaking change requiring an explicit `ABI_VERSION` bump. For `#[repr(transparent)]` wrappers specifically, this also preserves direct-construction ergonomics for external consumers (DLL authors writing `CLInt(42)` at every fn boundary).
- `ABI_VERSION` is checked by the loader (`platform::load_manifest` for platform DLLs; equivalent gates wherever a layout-versioned interface lands). Mismatch produces a clean refusal, not silent corruption.
- The Facade convention §3 carries the exemption inline so future contributors hit the rule at the point they would otherwise apply `#[non_exhaustive]` mechanically.
- Per-facade `#[non_exhaustive] DTOs` sections enumerate exempt types with a one-line "governed by `ABI_VERSION`" note so the exemption is auditable from the facade spec, not just inferred from the absence of an annotation.

*(Sprint origin: Sprint 64 — FIXME 0001 resolution.)*
