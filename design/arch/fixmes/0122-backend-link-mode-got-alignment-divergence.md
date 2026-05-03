---
number: 0122
target: /backend
filed_by: /qa
filed_at: 2026-05-03
sprint_filed: 64
refers_to: tests/build_confidence.rs::mode_equiv_adt_option_match, tests/build_confidence.rs::mode_equiv_pattern_match_nested, tests/build_confidence.rs::mode_equiv_macro_user_defined, tests/build_confidence.rs::mode_equiv_io_pure_primitive
status: open
---

# `--link` mode diverges from `--run`/REPL on certain feature shapes — GOT atom alignment / linker failure

## Issue

Defect surfaced during Sprint 64 Wave 2.5 (mode-equivalence subset
landing). Four representative programs in
`tests/build_confidence.rs` produce equivalent observable Int values
through REPL fresh, REPL cached, `--run` fresh, and `--run` cached —
but FAIL through `--link` (both fresh and cached) with a linker
diagnostic of the form:

```
; Linking: __startup.o prelude.o user.o __main_alias.o -lcranelisp_exe_bundle -o user
error: codegen error at 0..0: linker failed:
ld: warning: alignment (1) of atom '___cranelisp_got_user' (/private/var/folders/.../user.o)
  is too small and may result in unaligned pointers
```

The four affected programs (each landed un-ignored as a regression
guard per `memory/feedback_repros_join_suite.md`):

1. `mode_equiv_adt_option_match` — `(defn main [] (match (Some 7) [(Some x) (if (= x 7) 0 1) None 2]))` (with TestStandard prelude).
2. `mode_equiv_pattern_match_nested` — `(defn main [] (match (Ok 42) [(Ok x) x (Err _) -1]))` (with TestStandard prelude).
3. `mode_equiv_macro_user_defined` — `(import [primitives [add-i64]]) (defmacro twice [x] (add-i64 ~x ~x)) (defn main [] (twice 21))` (no prelude — uses primitives + a user defmacro).
4. `mode_equiv_io_pure_primitive` — `(import [primitives [Pure]]) (defn main [] (Pure 7))` (no prelude — uses the `Pure` IO primitive).

By contrast, these programs of comparable shape PASS all six
permutations through `--link`:

- `(defn main [] 0)` — constant
- `(import [primitives [add-i64]]) (defn main [] (add-i64 1 2))` — primitive arithmetic
- `(defn main [] (+ 1 2))` with TestStandard prelude — operator dispatch
- `(import [primitives [add-i64 sub-i64]]) (defn main [] (sub-i64 (add-i64 10 5) 3))` — multi-import single-file
- `(defn main [] (let [x 10 y 5] (- x y)))` with TestStandard prelude — let
- `(defn main [] (if (< 5 10) 1 0))` with TestStandard prelude — if/else
- `(defn main [] (if (= 1 1) 0 1))` with TestStandard prelude — Eq dispatch

The pattern is: `--link` succeeds on plain primitive + operator code,
but fails when the program uses ADT constructors / `match` / a
user-defined `defmacro` / a `Pure` IO primitive. The alignment
diagnostic points at the GOT data symbol (`___cranelisp_got_user` or
`___cranelisp_got_prelude`).

## Proposed resolution

Investigation focus: the GOT data atom emitted into the user/prelude
`.o` for `--link` mode declares alignment 1, while the linker expects
pointer-aligned (8 on the target platform). The path differs from
`--run` (JIT, no `.o`) and REPL (also JIT) — both of which work, so
the codegen for the dynamic case is correct. The question is whether
the AOT object writer in `--link` is missing an alignment directive
on the GOT data symbol when the GOT contains certain shapes (ADT
constructor table entries? defmacro clause function pointers? IO
trampoline entries?).

## Operational implication / Context

Per `tests/plan/PLAN.md §"Defect rule"` and the parity rule
recorded in `tests/CLAUDE.md`, this is a parity-rule landing: four
failing tests committed un-ignored as the durable repros + regression
guards. Until `/backend` resolves, the tests ledger under
`tests/plan/ledger.md` as `out-of-scope (owner=/backend)` with target
sprint TBD.

The mode-equivalence subset (per `tests/plan/PLAN.md §"Mode
canonicalisation"`) was authored specifically to surface defects of
this shape — the empirical validation that REPL / `--run` / `--link`
share the single pipeline (Principles 11–13; Decisions 22, 25, 41).
This FIXME is the first concrete output of that validation; without
the subset the divergence would have remained invisible because the
Wave 2 batches tested each mode independently (the anti-pattern Wave
2.5 corrected).

Wave 1 (`smoke_link_then_run_executable_matches_run_exit`) demonstrates
that simple primitive + add-i64 programs DO link successfully — so
the link path is not categorically broken; the defect is shape-specific.
