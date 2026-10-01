---
id: ACT-1033
title: Make each intrinsics-catalog signature agree with its Rust function, and retire or give an emitter to runtime/rc_underflow_check
status: open
priority: advisory
from: qa
to: arch
sprint: 122
filed_at: 2026-09-30
refers_to:
  - crates/cranelisp-intrinsics/src/catalog.rs
  - crates/cranelisp-intrinsics/src/rc.rs
  - crates/cranelisp-intrinsics/src/heap_string.rs
  - crates/cranelisp-intrinsics/src/panic.rs
  - crates/cranelisp-intrinsics/src/catalog/tests.rs
  - crates/cranelisp-intrinsics/public-api.txt
  - crates/cranelisp-backend/src/jit.rs
  - design/arch/bounded-contexts.md
---

## Request

Decide whether `runtime/rc_underflow_check` is retired or kept, then have
`dev`(intrinsics) make the catalog, the function and the records agree.
Retirement removes a public item, so it goes through the inter-crate
public-API user gate.

The same applies to the two siblings below. `runtime/string_read` has no
emitter either, so BC §4b invariant 1 also puts its catalog entry in question.

## Observation

Verified against source on 2026-09-30 at `88bbbd12`. Provenance: `arch`
reported the lead in its R22 visit; QA confirmed each claim below.

- **The arity is false.** The catalog entry (`catalog.rs`) declares
  `param_count: 1`. The Rust function `rc::rc_underflow_check(ptr, old_rc)`
  takes two parameters, as `public-api.txt` records.
- **Nothing emits a call.** No backend source names the symbol. It reaches
  codegen only through the generic walks over `intrinsics_table()`: JIT
  symbol registration and `declare_intrinsics_generic` (`jit.rs`). Both
  declare the import with one parameter. Its `runtime/` prefix keeps it out
  of user code.
- **Three records claim otherwise.**
  - The function's rustdoc says the backend calls it after an inline
    decrement.
  - `crates/cranelisp-intrinsics/src/catalog/tests.rs::arity_matches_historical_signature` pins the false
    arity of 1. It checks the historical expectation, not the Rust signature.
  - The [named-intrinsic conventions table](../../design/arch/bounded-contexts.md#4b-intrinsics-cratescranelisp-intrinsics)
    lists the entry as a target of emitted calls. The catalog is meant to
    hold only such targets (BC §4b invariant 1).

## Two sibling entries (widened 2026-09-30)

`review` reported these outside its diff. QA verified them against source at
`88bbbd12`; neither is observable today.

| Entry | Catalog | Rust | Callers |
|---|---|---|---|
| `runtime/string_read` | 1 param, returns | `string_read(s, out_ptr, out_len)`, returns nothing | Rust only (`src/marshal.rs`). No backend site emits it, so only the generic declaration and JIT registration reach the entry |
| `runtime/panic` | 2 params, returns | `runtime_panic(msg_ptr, msg_len)`, returns nothing | Four backend sites (`vec_codegen.rs`, `match_codegen.rs`, `primitives_inline.rs`, `lib.rs`). Each discards the declared result and returns its own sentinel |

- **Hazard.** An emitter trusting the catalog would, for `string_read`, pass
  one argument to a function that writes through two uninitialized pointers.
  For `panic`, it would use an unwritten return register.
- **Falsifiers for "unreachable today":** a backend site emitting
  `runtime/string_read`, or a `runtime/panic` call whose result is read.
- **Common cause.** Each entry's `param_count` and `has_return` are
  hand-maintained copies of its Rust signature. `arity_matches_historical_signature`
  pins those copies, not the functions. Three of the catalog's copies are
  wrong.
- **Preferred control (for `arch` to choose):** derive each entry's signature
  from its function's type, so a disagreement does not compile. A test
  comparing the copies with a second hand-written list would repeat the
  current weakness.

## Class

Neither a defect nor a residual. No program can observe it today, so no
reproduction is possible. It is a latent hazard. An emitter that trusts the
catalog would pass one argument. The callee would then read an undefined
`old_rc` and either raise a false underflow panic in debug or miss a real
underflow.

Falsifier for "unreachable today": any backend site that emits a call to
`runtime/rc_underflow_check`. The siblings' falsifiers are stated above.

## Completion evidence

- **If retired:** the entry, the function and the arity-test row are removed.
  The BC table row is dropped. The user has confirmed the `public-api.txt`
  removal.
- **If kept:** the catalog declares two parameters, and the arity test pins
  the Rust signature. The emitting site exists and carries its own module
  test.
- Either way, no record claims an emitter that does not exist.
- Every remaining catalog entry's parameter count and return agree with its
  Rust function, preferably by construction. `runtime/string_read` is
  corrected or removed from the catalog, and `runtime/panic` declares no
  return.
