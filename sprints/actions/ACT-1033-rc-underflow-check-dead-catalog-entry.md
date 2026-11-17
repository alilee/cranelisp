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

## Catalog part resolved (qa, 2026-11-15, S123 W1)

The signature half of this action is closed; the retirement decision for
`runtime/rc_underflow_check` remains with `arch`.

- **Source opened.** Every row of `crates/cranelisp-intrinsics/src/catalog.rs`
  is a `catalog_row!` naming its function and its function-pointer type, and
  `(param_count, has_return)` derives from that type, so a row cannot disagree
  with its function and compile. `runtime/panic` declares
  `(2, false)` with a diverging type, `runtime/string_read` `(3, false)` and
  `runtime/rc_underflow_check` `(2, true)`.
- **Evidence.** `crates/cranelisp-intrinsics/src/catalog/tests.rs::corrected_rows_carry_their_functions_signatures`
  pins the three corrected rows; the compile-fail rows
  `derivation_refuses_a_wrong_arity`, `derivation_refuses_a_wrong_return` and
  `derivation_refuses_narrow_words`, each with the matched control
  `derivation_accepts_matched_rows`, are the detection proof. Grade:
  structural.
- **Still open.** No backend or root source emits `runtime/rc_underflow_check`,
  and its rustdoc in `crates/cranelisp-intrinsics/src/rc.rs` still says the
  backend calls it after an inline decrement. The completion evidence below
  stands, except its last bullet, which is met.

## Disposition proposed (arch, 2026-11-16, S124 Phase 3)

Source opened at `4b58ab93`: `catalog.rs` holds both rows; no backend, root or
primitives source names `rc_underflow_check`; `string_read`'s only caller is
`src/marshal.rs`, a Rust-path call.

- **Retire `runtime/rc_underflow_check`**, function and row.
- **Take `runtime/string_read` out of the catalog** and drop its export name;
  the function stays public for the binary.
- Both are [S124 packet](../s124-api-packet.md) row D11, approved by the user
  on 2026-11-17. This action closes when D11 lands.

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
  - The catalog's arity test pinned the false arity of 1. It checked the
    historical expectation, not the Rust signature.
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
  hand-maintained copies of its Rust signature. The arity test pinned those
  copies, not the functions. Three of the catalog's copies are
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
