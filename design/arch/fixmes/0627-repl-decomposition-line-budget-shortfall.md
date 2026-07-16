---
number: 0627
target: /design
filed_by: /dev
filed_at: 2026-07-16
sprint_filed: 110
refers_to: design/int/repl-decomposition.md §1.6 + §4 (line-budget acceptance) — the
  0606 cut's per-file budget under-counts the total; format.rs/commands.rs land over ~1,500.
status: open
---

# `repl.rs` decomposition (0606) — the §1.6 line budget is infeasible; needs a finer cut

## Source

S110 Phase 5 `/dev` execution of the 0606 mechanical move (the signed-off cut in
`design/int/repl-decomposition.md`). The move landed behaviour-invariant (golden REPL e2e
byte-identical; baseline unchanged at 7 RED; zero library `public-api.txt` movement;
`cargo check`/clippy clean). But the **§1.6 line-budget acceptance criterion — "no file in
the family exceeds ~1,500 lines" — is not met** and cannot be met by the cut as designed.

## Evidence (measured, as-built)

| File | as-built LOC | §1.6 budget |
|---|---:|---:|
| `repl/mod.rs` (residual) | ~1,050 | 850 |
| `repl/search.rs` | ~730 | 710 |
| `repl/format.rs` | **~1,900** | 1,480 |
| `repl/commands.rs` | **~1,650** | 1,490 |
| **total** | **~5,320** | **~4,530** |

The budget table sums to ~4,530 lines, but the source (`repl.rs` = 5,237 LOC production +
tests) plus the split overhead (fq-helper handling, per-file glob preambles, file docs,
impl-block wrappers) is ~5,320. The budget under-counts the **total** by ~750–800 lines, so
two files must exceed ~1,500 regardless of apportionment. The per-file **test** estimates are
the largest source of the gap (design: format 430 / commands 200; measured before dedup:
format 809 / commands 438 — and the sum of all four test estimates, 940, is already less than
the original ~1,470 test lines the split must redistribute).

## The pre-authorised valve does not resolve it

§1.6's layout-render valve was measured both ways (with the shared `test_support` dedup
already applied — the fq helpers live once in `mod.rs`, saving ~275 lines):

- **valve OFF** (landed): format 1,900 / commands 1,645
- **valve ON**: format 1,653 / commands 1,894

The valve only relocates ~250 lines between the two heavy files — it never brings both under
~1,500, and taking it makes `commands.rs` the worst file (1,894) while still leaving
`format.rs` over (1,653). Its stated purpose ("keep format under budget") is unmet at 1,653,
so I landed the **valve OFF** (the §1.2 default placement, which keeps `commands.rs` at its
natural 1,645). What was applied within `/dev`'s remit: the shared `test_support` module
(Principle 7 — the split would otherwise duplicate ~275 lines of session/entry-builder
helpers across the four `fq_arg_*` cells).

## Ask

A **finer cut is a `/design` decision** (§1.6 pre-authorises only the layout valve; any further
split contradicts the §1.2/§1.3 file boundaries). Candidate directions for `/design` to weigh:

- Split `format.rs` along the value-vs-type axis: a `repl/format.rs` (eval-result + def-entry
  + span helpers, the value/echo formatters) and a `repl/format_type.rs` (`format_type_display`
  / `format_trait_display` / `format_builtin_type_display` / `impls_for_type_in_view` /
  the related-section builders — the type/trait introspection family). Each ~950.
- Or split `commands.rs`: the introspection commands (`/info`/`/sig`/`/doc`/`/source`/`/sexp`/
  `/ast`/`/clif`/`/disasm`) vs the action commands (`/mod`/`/expand`/`/time`/`/mem`/`/run-tests`
  /`/imports`/`/exports`/`/platform-schema`).
- Or ratify a higher budget for this family (accept ~1,900 given the display formatter and
  command-handler families are cohesive) and update §1.6 / the FIXME 0606 Done criterion.

Whichever `/design` picks, the re-cut is another mechanical `/dev` move on the already-landed
`src/repl/` tree (behaviour-invariant, same acceptance contract).
