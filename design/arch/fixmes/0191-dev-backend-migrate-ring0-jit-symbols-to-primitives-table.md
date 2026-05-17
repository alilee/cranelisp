---
number: 0191
target: /dev (primitives) — primitives-side gaps must close first; /dev (backend) follows
filed_by: /dev (primitives)
filed_at: 2026-05-15
sprint_filed: 67
refers_to: crates/cranelisp-backend/src/jit.rs::intrinsic_symbols, crates/cranelisp-primitives/src/lib.rs (PRIMITIVES_TABLE), design/arch/fixmes/0182-dev-primitives-ring0-jit-symbols-narrow-or-delete.md
status: open — re-targeted Sprint 67 Wave 4 by /dev (backend) after surveying structural blockers; see "Sprint 67 Wave 4 disposition" below
sprint_partial: 67
partial_residue: backend `intrinsic_symbols()` still reads via `ring0_jit_symbols()` (23 Ring 0 entries) + 22 non-Ring-0 direct Rust paths; primitives-side migration prerequisites unmet
---

# Migrate `intrinsic_symbols()` primitives enumeration from Rust-path access to `PRIMITIVES_TABLE`

## Issue

`crates/cranelisp-backend/src/jit.rs::intrinsic_symbols()` enumerates **two**
classes of `cranelisp-primitives` items by direct Rust path — preventing the
facade's stated single-published-item target for `cranelisp-primitives`:

**(a) Ring 0 shims via the free function:**

```rust
for (name, ptr) in cranelisp_primitives::ring0::ring0_jit_symbols() {
    // …push IntrinsicSymbol { name, ptr, … }
}
```

**(b) ~22 non-Ring-0 primitive shims by direct Rust path (lines 121–148):**

```rust
IntrinsicSymbol { name: "str-concat", ptr: cranelisp_primitives::string::str_concat as *const u8, … },
IntrinsicSymbol { name: "vec-len",    ptr: cranelisp_primitives::vec::vec_len as *const u8, … },
IntrinsicSymbol { name: "int-to-string", ptr: cranelisp_primitives::int::int_to_string as *const u8, … },
// …str_eq, str_len, string_identity, parse_int, float_to_string, bool_to_string,
//    str_substring, str_char_at, str_split, str_join, str_replace, str_trim,
//    str_starts_with, str_ends_with, str_contains, str_to_upper, str_to_lower,
//    sconcat, quote_sexp
```

Both classes require the underlying extern fns to remain `pub`. Sprint 67 W3
`/dev (primitives)` attempted to demote the 21 extern fns to `pub(crate)` per
the facade's stated post-FIXME-0159 target and produced 22 `E0603 function is
private` errors in backend — all from class (b). The demotion was reverted;
the extern fns remain `pub` for this consumer.

Sprint 67 Wave 3 introduced `cranelisp_primitives::PRIMITIVES_TABLE` (FIXME 0159
close) as the single source of truth for primitive symbol-table entries +
GOT-stored fn ptrs. Wave 3 migrated `src/session_v4.rs::populate_ring0_got_slots`
to read from the static table. Backend's `intrinsic_symbols()` still reads via
classes (a) and (b) because Wave 3's narrow-deployment scope was
`cranelisp-primitives` + `src/`; editing backend was out of scope.

While these Rust paths remain `pub` for this consumer, the facade's stated
post-FIXME-0159 target is one published Rust API item on
`cranelisp-primitives` (`PRIMITIVES_TABLE`). FIXME 0182 — currently blocked by
both classes of this remaining backend consumption — narrows
`ring0_jit_symbols` to `pub(crate)` or deletes it once the migration lands;
the broader extern-fn demotion is blocked the same way.

## Proposed resolution

In `crates/cranelisp-backend/src/jit.rs::intrinsic_symbols()`, replace the
loop body with a walk of `PRIMITIVES_TABLE`:

```rust
let static_table = &*cranelisp_primitives::PRIMITIVES_TABLE;
for (name, entry) in static_table.symbols.iter() {
    let cranelisp_types::ModuleEntry::Def {
        got_slot: Some(slot),
        kind,
        scheme,
        ..
    } = entry
    else {
        continue;
    };
    let ptr = static_table.got.load_slot(*slot);
    if ptr.is_null() {
        continue;
    }
    let param_count = match scheme.ty {
        cranelisp_types::Type::Fn(ref params, _) => params.len() as u32,
        _ => continue,
    };
    intrinsics.push(IntrinsicSymbol {
        name: name.as_ref(),  // may need `&'static str` lifetime hoisting
        ptr,
        param_count,
        is_runtime: false,
        has_return: true,
    });
}
```

The `&'static str` lifetime constraint on `IntrinsicSymbol::name` is the
load-bearing detail: `Symbol::as_ref()` is `&str` with the table's lifetime,
not `'static`. Either (a) leak the strings, (b) use a pre-allocated lookup
table mirroring the `ring0_jit_symbols` return type but built from
`PRIMITIVES_TABLE` once, or (c) change `IntrinsicSymbol::name` to
`Cow<'static, str>` / `String`.

## Operational implication / Context

- After this migration both classes (a) Ring 0 free fn + (b) direct Rust paths
  for non-Ring-0 primitives resolve through `PRIMITIVES_TABLE`. Backend imports
  only one item from `cranelisp-primitives`: the static `PRIMITIVES_TABLE`.
- After this migration:
  - `cranelisp_primitives::ring0_jit_symbols` can be narrowed to
    `pub(crate)` (or deleted entirely if backend was the last consumer),
    closing FIXME 0182.
  - The 21 extern fns can be demoted to `pub(crate)`, matching the facade's
    target (`facades/primitives.md §"Internal extern fns (pub(crate))"`).
  - `cranelisp-primitives`'s `public-api.txt` baseline drops from 56 lines
    to ~2 lines (one for the crate root `pub mod`, one for `PRIMITIVES_TABLE`),
    matching the facade's stated "single published Rust item" target.
- No JIT-symbol-name semantics change — backend registers the same names
  with the same fn ptr addresses; only the source of the (name, ptr) pairs
  changes.
- Wave 4 (backend) is the natural home for this migration alongside the
  intrinsic_symbols cleanup also tracked there.

## Sprint 67 Wave 3 disposition

`/dev (primitives)` reverted the extern-fn demotion after class (b) consumers
in backend produced E0603 errors. Both demotion (extern fns to `pub(crate)`)
and ring0_jit_symbols narrowing (to `pub(crate)`) are deferred to /dev (backend)
Wave 4 — once backend consumes only `PRIMITIVES_TABLE`, primitives can
narrow in a same-change-set follow-up. FIXME 0182 + this FIXME (0191) close
together when backend's migration lands.

## Sprint 67 Wave 4 disposition (/dev (backend))

`/dev (backend)` surveyed the migration scope in Wave 4 and identified two
structural blockers that prevent backend-side migration in isolation:

1. **Ring 0 coverage gap — `neq-*` triplet missing from `PRIMITIVES_TABLE`.**
   `PRIMITIVES_TABLE` is populated from `cranelisp_types::ring0_primitives()`
   which enumerates **20** Ring 0 entries; `ring0_jit_symbols()` surfaces
   **23** entries (the extra `neq-i64`, `neq-f64`, `neq-bool` shims that
   `traits.rs::primitive_for_trait_method` resolves `Eq.!=` to). The
   primitives-crate test
   `primitives_table_entries_carry_got_slot_and_ptr` already documents the
   delta (`assert!(checked >= ring0::ring0_jit_symbols().len() - 3 /* allow
   for entries without ptr */)`). Backend migrating the Ring 0 loop in
   isolation loses these three JIT registrations and breaks `Eq.!=`
   trait-method dispatch.

2. **Non-Ring-0 coverage gap — ~22 primitive shims absent from
   `PRIMITIVES_TABLE`.** Lines 121-148 of
   `crates/cranelisp-backend/src/jit.rs::intrinsic_symbols()` register
   user-callable, non-Ring-0 primitives (`str-concat`, `str-eq`, `vec-len`,
   `int-to-string`, `parse-int`, `float-to-string`, `bool-to-string`,
   `substring`, `char-at`, `split`, `join`, `replace`, `trim`,
   `starts-with?`, `ends-with?`, `contains?`, `to-upper`, `to-lower`,
   `sconcat`, `quote-sexp`, `vec-set-copy`, `vec-push-copy`,
   `vec-push-grow`, `string-identity`). None of these have
   `ModuleEntry::Def` entries in `PRIMITIVES_TABLE` today — the table is
   Ring-0-only by construction (`build_primitives_table()` walks only
   `cranelisp_types::ring0_primitives()`). Migrating these would require
   `PRIMITIVES_TABLE` to grow to cover the non-Ring-0 primitives first.

Both blockers are **primitives-side** changes (the FIXME is re-targeted
from `/dev (backend)` to `/dev (primitives)`):

- Add the 3 `neq-*` entries to `cranelisp_types::ring0_primitives()` (or
  to the `PRIMITIVES_TABLE` builder directly), so `PRIMITIVES_TABLE` covers
  the full 23-entry surface that `ring0_jit_symbols()` returns.
- Extend `PRIMITIVES_TABLE` to cover the ~22 non-Ring-0 primitive shims —
  add corresponding `ring0_primitives`-style metadata for them (Symbol,
  Type, JIT name) and seed GOT slots with the shim addresses at the same
  build step. This subsumes the `ring0_jit_symbols`-shaped table for the
  non-Ring-0 set.

After both gaps close on the primitives side, `/dev (backend)` migrates
`intrinsic_symbols()` to a single PRIMITIVES_TABLE walk (the proposed
resolution shape above) in a single follow-on change-set. FIXME 0182 +
this FIXME (0191) close together at that point.

Recorded in code via a multi-paragraph comment block at the head of the
Ring 0 loop in `crates/cranelisp-backend/src/jit.rs::intrinsic_symbols()`
naming both blockers (see commit landing this FIXME update).
