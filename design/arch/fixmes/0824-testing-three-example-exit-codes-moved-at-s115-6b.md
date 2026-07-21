---
number: 0824
target: /testing
filed_by: /examples
filed_at: 2026-07-21
sprint_filed: 115
refers_to: tests/examples.rs::expected_exits(); examples/07-polymorphism.cl,
  examples/25-curry.cl, examples/33-redefinition.cl
status: open
---

# Three `examples/` exit codes moved at S115 Phase 6b — `expected_exits()` reconciliation

## Ask

Update three rows in `tests/examples.rs::expected_exits()`. Nothing else
changes: **no file added, no file removed, no file renamed**, so the
umbrella's on-disk parity guard is unaffected.

| File | Old | New | Why |
|---|---|---|---|
| `07-polymorphism.cl` | 119 | **120** | New `test-many-instantiations` sub-test (contributes 1). The example's header previously asserted "in batch mode, each polymorphic function is used at one concrete type per program" — false; the new sub-test instantiates one `id` at Bool, String and Int in a single body, and `first-of` at two type pairs. |
| `25-curry.cl` | 118 | **139** | Two new sub-tests: currying a local **closure value** (`((g 1) 2)` → 13) and a **trait-operator partial** (`(+ 5)` then applied → 8). Sum 374 → 395; exit is the low byte, 395 mod 256 = 139. |
| `33-redefinition.cl` | 136 | **139** | Three new pass=1 sub-tests for **impl redefinition**: a later `impl` replaces the earlier one, a dispatch site written before it rebinds, and the rebind cascades a second layer. |

## Verification

Both modes, `2026-07-21`, binary at `target/debug/cranelisp`, invoked with
`cwd = examples/` and `CRANELISP_PLATFORM_PATH=target/debug` (exactly the
harness's own invocation; **no** `CRANELISP_LIB` — setting it breaks
free-standing resolution, see `examples/Cranelisp.toml`), cache cleared first:

```
07-polymorphism   --run 120   --link 120
25-curry          --run 139   --link 139
33-redefinition   --run 139   --link 139
```

The full sequence was replayed at the same time: 35 top-level files +
`16-modules/` (47) + `37-method-import/` (4), all at their documented exit
codes, no other drift.

## Do NOT add rows for the new library files

S115 6b seeds an **examples-local library** under `examples/lib/` per the
user ruling (see `examples/plan-examples.md` §2d). It adds
`examples/lib/operators.cl` and `examples/lib/README.md`. These are library
modules imported by name, **not** sequence entries — they have no `main` and
must not appear in `expected_exits()`. The umbrella globs top-level
`examples/*.cl`, so they are already outside its file-set check; this note
exists only so the next `lib/` module does not get misfiled.

## Related

`0820` (also `/testing`, open) asks for a directory-project e2e row for
`examples/16-modules/main.cl` => 47. Independent of this FIXME, but the two
touch the same file and could land together.
