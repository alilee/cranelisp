---
number: 0180
target: /arch
filed_by: /dev
filed_at: 2026-05-14
sprint_filed: 66
refers_to: design/arch/facades/primitives.md, design/arch/facades/intrinsics.md, crates/cranelisp-primitives/src/{lib,string,vec}.rs, crates/cranelisp-intrinsics/src/string.rs, crates/cranelisp-backend/src/jit.rs
status: unblocked
---

> **2026-05-14 status update (Wave 4a.retire)** — The `cranelisp-runtime` crate has been retired (FIXME 0150 Phase 5 closed). The structural cycle blocking route (1) is now gone: `cranelisp-intrinsics` no longer has any consumer reaching `str_concat`/etc. through a runtime shim. A subsequent `/dev` (primitives) fire can now physically lift the string + vec bodies from `cranelisp-intrinsics` into `cranelisp-primitives` and add the shim in `cranelisp-intrinsics` (or, cleaner per route (1)'s spirit, retire that side entirely since no consumer remains). `/arch` review per the original three-way decision (now reduced to two: keep route (3) as terminal, OR execute route (1) — route (2) is done) is still required before the relocation lands. Leaving open for that disposition.


# Physical primitives relocation is blocked by the runtime-shim chain

## Issue

Wave 3b-2d.2 was scoped to lift user-callable Rust extern fns (kebab-case JIT
names, addressable via the synthetic `primitives` module) out of
`cranelisp-intrinsics` and into `cranelisp-primitives`. β-1 used the pattern:
"move bodies to new crate, leave thin re-export shims in old crate so legacy
consumers compile until β-3." For β-2 that pattern is **architecturally
unavailable** as currently structured. Three crates couple here:

```
cranelisp-runtime  -> pub use cranelisp_intrinsics::string::{str_concat, ...};   (existing shim, β-1 era)
cranelisp-intrinsics                                                              (host of impls today)
cranelisp-primitives -> cranelisp-intrinsics                                      (this wave's new edge — for alloc helpers)
```

If the wave moves impls physically into `cranelisp-primitives` and adds a
shim `pub use cranelisp_primitives::string::* ;` in `cranelisp-intrinsics`,
that introduces `cranelisp-intrinsics -> cranelisp-primitives`. Combined
with the wave's required `cranelisp-primitives -> cranelisp-intrinsics` (for
the alloc / rc / drop helpers that the moved fns call into, e.g.
`alloc_string`, `consume_shallow`), this is a Cargo crate cycle. Cargo
rejects it at workspace resolution.

The cycle can be broken three ways. Each requires action outside `/dev`'s
narrow-deployment scope for this wave:

1. **Edit `cranelisp-runtime/src/lib.rs`** to point its shims at
   `cranelisp-primitives` instead of `cranelisp-intrinsics`, and add the
   `cranelisp-primitives` dep to `cranelisp-runtime/Cargo.toml`. Out of
   scope: this wave's boundary forbids editing runtime.
2. **Retire `cranelisp-runtime` entirely** (FIXME 0150 Phase 5). The
   backend's `IntrinsicSymbol` table in `crates/cranelisp-backend/src/jit.rs`
   then imports `cranelisp_primitives::*` directly. That is multi-crate work
   beyond a single `/dev` wave.
3. **Hold impls in `cranelisp-intrinsics`** and have
   `cranelisp-primitives` re-export from there. Acyclic, doesn't break
   runtime, but inverts the moving direction.

This wave took route (3) as the only path that respects the boundary. The
Rust public-API surface of `cranelisp-primitives` now reflects the target
user-callable set (15 string fns + `vec_len`) via re-exports; the bodies
remain in `cranelisp-intrinsics`. JIT symbol-name registrations are
unchanged (still keyed off `cranelisp_runtime::*`).

`design/arch/facades/primitives.md` §"Consumed surface" states:
"primitives does NOT depend on `cranelisp-intrinsics`. The two crates are
siblings under the runtime-split-decision and have independent evolution
drivers." Route (3) adds the `cranelisp-primitives → cranelisp-intrinsics`
edge in the *transitional* shape, contradicting this. The facade is
target-stating, not target-stated-and-also-currently-true; consumers
reading the facade may infer the wave's transitional dep is a defect.

## Proposed resolution

`/arch` decides which of (1) (2) (3) is the intended end state and updates
the facades accordingly:

- If (1) — runtime-shim repoint — file a `/dev`-target FIXME for the runtime
  edit. Bodies migrate to `cranelisp-primitives`; the
  `cranelisp-intrinsics → cranelisp-primitives` shim is unnecessary because
  no consumer reaches the moved fns via `cranelisp_intrinsics::string::*`
  any longer.
- If (2) — runtime retirement — clarify in `facades/primitives.md` that the
  transitional `cranelisp-primitives → cranelisp-intrinsics` edge is
  intended to persist until runtime retires (FIXME 0150 Phase 5). Existing
  facade text reading "primitives does NOT depend on cranelisp-intrinsics"
  is post-Phase-5 target state; the transitional state has the dep.
- If (3) — re-export-only relocation accepted as terminal — revise
  `facades/primitives.md` §"Consumed surface" to explicitly sanction the
  dep, and revise the facade's surface description from "bodies live here"
  to "re-export presentation of the user-callable surface defined in
  `cranelisp-intrinsics`." The cleanest framing: `cranelisp-primitives` is
  a *categorical facade* over the impl substrate in intrinsics, mirroring
  the way `cranelisp-types` is a categorical facade over scattered Rust
  types.

The cleanest end state under FIXME 0150's stated intent is (2) — once
runtime retires, route (1) becomes trivially executable, the cycle goes
away, and the bodies physically reside where the facade says. Until then,
the facade and the source need to acknowledge each other's transitional
shape.

## Operational implication / Context

- Backend's `IntrinsicSymbol` registration in `jit.rs` continues to import
  `cranelisp_runtime::str_concat as *const u8` etc. — unchanged across this
  wave. No JIT-symbol-name semantics changed.
- The `cargo-public-api` baseline of `cranelisp-primitives` (post-wave: 35
  lines) records the as-presented Rust surface. Future Rust-API drift on
  the user-callable set will surface there.
- Test counts: `cranelisp-primitives` runs 0 unit tests (the surface is
  pure re-export — there is nothing to unit-test from this crate that
  isn't already covered by `cranelisp-intrinsics`'s 119 tests against the
  underlying bodies). If `/arch` chooses (1) or (2), tests migrate with
  the bodies.
- This FIXME is not a release blocker — the wave's stated functional goal
  (a primitives crate with the user-callable surface visible) is achieved.
  It is a documentation/intent drift surfacing the wave's structural
  constraint. β-3 closes it.
