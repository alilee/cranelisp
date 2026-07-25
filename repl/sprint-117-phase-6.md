# Sprint 117 REPL assessment and action plan

**Phase 6a status:** complete
**Phase 6b status:** complete

## Assessment

Sprint 117 materially improves the self-documenting REPL in three places:

1. A constrained function's definition echo, bare lookup, `/sig`, and `/info`
   now agree on one scheme and name every constraint trait by its canonical
   home. For example, the TestStandard `Num` constraint is displayed as
   `:prelude/Num`, never as the ambiguous bare `:Num`.
2. Trait and type introspection now show inverse views of the same live
   implementation relation. `/info <Type>` includes both local and imported
   traits, local first; `/info <Trait>` includes the corresponding target
   types. Both views deduplicate a replaced `impl` rather than presenting edit
   history as if it were live state.
3. A genuine code-generation failure no longer poisons the interactive
   session. The diagnostic names the actual failed compilation subject rather
   than `/`; a following literal or definition can compile and run; a clean
   same-name definition has no stale failed-turn metadata in `/info`.

The cache-restored macro repair is also user-significant even though it adds no
new display: the same user-defined macro program now behaves identically in
REPL, Run, and Link modes with cache both cold and restored. This preserves the
single-pipeline promise rather than creating a cache-dependent dialect.

The generic zero-argument-macro presentation work did **not** ship. A stdlib
`def` may still echo its generated `*-def` thunk and `/info` or `/sig` may
describe the macro carrier instead of the public value. This is an existing,
known non-conformance recorded by FIXME 0800 and deferred implementation FIXME
0863. The rejected Sprint 117 implementation was removed; this assessment does
not treat its temporarily green output as delivered and does not reopen or
duplicate FIXME 0863.

## Standing-quality verdict

The REPL is more truthful after Sprint 117, but its learning surface does not
yet demonstrate the whole delivered improvement:

- `05-traits.demo` already causes the newly canonical constrained scheme to be
  printed, and it demonstrates canonical homes in `impl` confirmation. It does
  not deliberately ask both inverse introspection questions, so a user is not
  shown that `/info Sizeable` and `/info Box` describe the same live relation.
- `10-redefinition.demo` demonstrates trait-side deduplication after re-`impl`
  but likewise omits the type-side twin.
- There is no appropriate showcase story for the failed-codegen transaction
  fix: its current production trigger is another known compiler failure. A
  release demo should not teach users to invoke a defect merely to prove that
  recovery works. The permanent e2e guards are the right evidence until a
  natural user error reaches this exact backend boundary.
- The `def` forms in the Sudoku demo still expose the deferred presentation
  defect in live output. Demo commentary must not bless that output as the
  intended experience. The durable fix remains 0863; Phase 6b must not paper
  over it with output filtering or a special demo-only spelling.

The normative experience requirements are already clear. No new REPL-spec
prose and no new cross-owner FIXME are needed from this assessment.

## Phase 6b action plan

1. Extend `05-traits.demo` immediately after the user-defined `Sizeable` impl:
   show `/info Sizeable` and `/info Box` as paired questions, explaining that
   they are inverse live views and that repeated impl entries are not history.
2. Keep `10-redefinition.demo` focused on editing, but add `/info Box` beside
   its existing `/info Sizeable` so replacement is visibly deduplicated from
   both directions.
3. Replay every showcase demo with `DEMO_FAST=1`, read every captured line
   against `repl/spec.md`, and record the known `def` presentation lines as
   0800/0863 rather than filing a duplicate. Any different non-conformance
   becomes a new numbered FIXME with a narrow failing-not-ignored handoff
   before Phase 6b closes.
4. Re-run the two changed demo stories after editing and verify the added
   drawers use the specified local-before-imported ordering and contain one
   row per live `(trait, target-type)` pair.
5. Do not add a failed-codegen showcase segment or a cache-specific UI. Retain
   the existing production REPL and six-permutation tests as the honest
   evidence for those invisible lifecycle improvements.

## Phase 6b results

All five actions were completed.

- `05-traits.demo` now asks `/info Sizeable` and `/info Box` together after
  the first implementation. `10-redefinition.demo` asks the same inverse pair
  after replacement. Both live replays show one matching implementation row
  from each direction.
- Every demo listed by `./repl/showcase --list` was replayed with
  `DEMO_FAST=1` and
  `TMPDIR=/home/alilee/cranelisp/target/s117-tmp`: 12 current/under-the-hood
  demos and 26 archived regression demos, 38/38 in total. Every harness
  command completed in 2–9 seconds; none approached the 55-second per-command
  stop.
- Line-by-line review found stale demo syntax rather than new compiler
  regressions: parenthesized nullary constructors, repeated field binders
  across constructors, hidden primitives used without imports, `/type` used
  where `/sig` teaches constrained definitions, and historical `;#!` lines
  that the current player correctly treats as comments. Those REPL-owned
  scripts were updated to current language and command syntax and replayed
  green. Intentional error demonstrations—type mismatch, unknown name,
  private-module rejection, runtime division by zero, and an explicitly
  failing test—remain visible and recover correctly.
- The Sudoku `def` echoes still expose `puzzle-def`, `answer-def`, and
  `contradiction-def`. They remain the known 0800/0863 presentation defect;
  no filtering, special spelling, duplicate FIXME, or product workaround was
  introduced.
- One distinct gap was found and filed as FIXME 0867: a polymorphic product
  such as `(Pair a b)` mints neither the canonical `Pair.fst` accessor nor its
  unique bare `fst` alias, although the corresponding concrete-product
  behavior is specified and tested. The Ring 4K historical demo now teaches
  the same polymorphic product through pattern extraction; `/qa` owns the
  narrow failing-first handoff.

No product source, language specification, or REPL specification was changed
in Phase 6b.

## Evidence reviewed

- `sprints/SPRINT.md`, Sprint 117 W3a, W3b, W3c, and W7 records
- `design/int/s117-conformance-recovery.md`
- `design/arch/fixmes/0863-cluster-wide-prepared-macro-presentation-transaction.md`
- `repl/spec.md` §§1.4, 4.1.3, 4.1.4, 5.2, and 18.9
- `tests/repl_introspection.rs` canonical-constraint and inverse-impl guards
- `tests/spec_11_stdlib.rs` failed-turn recovery and deferred `def`
  presentation guards
- `tests/build_confidence.rs::mode_equiv_macro_user_defined`
- `repl/demos/05-traits.demo` and `repl/demos/10-redefinition.demo`

## Next skills

- `/sprint` — record the completed REPL Phase 6a/6b assessment and action.
- `/qa` and `/testing` — attribute and reproduce FIXME 0867 with a narrow
  failing-not-ignored generic-product accessor guard.
- `/dev` — implement deferred FIXME 0863 in its target sprint; no Phase 6
  workaround is requested.
- `/qa` and `/testing` — retain the shipped recovery, introspection, and macro
  cache evidence.
