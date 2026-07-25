# Sprint 117 standard-library assessment and action plan

**Phase 6a status:** complete
**Phase 6b status:** implementation complete; warm-cache self-test enrolment
handoff pending

## Assessment

Sprint 117 shipped no new standard-library function or text type. Its
stdlib-visible effects are narrower:

1. `split` and `join` retain their existing String and `(Vec String)`
   behavior. Their implementation now crosses a runtime-owned Vec-of-String
   boundary rather than reading or writing Vec offsets in the primitives
   crate. The change is therefore a stability and ownership improvement, not a
   new String-specialized collection API. The runtime helpers remain Rust-path
   operations; they do not become Cranelisp functions for String or for
   `(Vec a)`.
2. User-defined macros behave consistently after cache restoration across
   REPL, Run, and Link. This matters to stdlib consumers because the library's
   surface includes macros such as `str`, `def`, `derive-*`, threading, and
   control forms. No stdlib macro needed a cache-specific variant and no cache
   behavior became part of its API.
3. The proposed text direction is design only. Cranelisp still has native
   `String`; it did not gain `Byte`, `(Vec Byte)` text storage,
   `Utf8Literal`, transparent one-field products, or a stdlib
   `int-to-string`. The accepted recommendation is a future native `Byte`
   represented in one word initially, an ordinary wide-slot `(Vec Byte)`, and
   a compiler-certified UTF-8 literal candidate whose payload is
   representation-identical to that Vec. Code points, graphemes,
   normalization, alternate encodings, and text algorithms would live in
   stdlib. Compact Byte storage remains a later general Vec-layout project,
   not a Byte-only representation fork.
4. The existing `def` presentation defect did not ship a fix. Echo still
   exposes the generated `*-def` thunk and `/info` or `/sig` still describes
   the macro carrier. The rejected post-publication projection was removed;
   FIXME 0863 records the cluster-wide prepared-transaction fix for Sprint
   118. This assessment does not propose a stdlib formatter workaround.

The W5 runtime work is deliberately not a specialization mechanism for
stdlib collection algorithms. General Vec operations remain the reusable
Cranelisp surface. The two new Rust helpers express only the ownership
boundary needed while host `split` and `join` construct and inspect
`(Vec String)`; a future stdlib text implementation should build on ordinary
`(Vec Byte)` and generic Vec functions rather than copying those helpers into
the language.

## Standing-quality verdict

The current stdlib remains usable on the native-String model, and the full
38-module conformance gate passed after the cache repair. The delivered work
does not justify changing `text.string`'s public vocabulary or claiming the
future byte-backed design as available.

Three user-proxy gaps remain to be handled explicitly:

- `text.string.test` exercises its higher-level helpers but does not directly
  pin the public `split`/`join` edge cases whose runtime ownership changed.
- The full conformance pass establishes broad stdlib health, while a compact
  warm-cache replay of representative stdlib macro families would make the
  cache-parity benefit visible at the library boundary.
- FIXME 0800 face 3 is still a stdlib API question: the current zero-argument
  macro model makes a `def`-bound function value readable as a value but not
  callable with arguments. Fixing faces 1–2 in the compiler transaction does
  not itself choose whether `def` should support function-valued application.

The first two are Phase 6b verification/coverage actions. The third needs a
small options note and user choice before any stdlib implementation. No new
FIXME is required: 0800 owns the API question and 0863 owns the compiler-side
presentation transaction.

## Phase 6b action plan

1. Add backing self-tests under `text.string.test` for public `split`/`join`
   behavior: empty input, empty Vec, multi-character delimiter, round trip,
   and use of the returned String after the source inputs have been consumed.
   Test through language-level primitives and ordinary Vec access; do not
   expose or imitate the Rust runtime helpers.
2. Run a small cold-cache/restored-cache user-proxy matrix for representative
   macro families: `str` (value-producing expansion), one control or threading
   macro, `derive-*` (multi-form expansion), and `def` (zero-argument public
   subject). Compare REPL, Run, and Link results. Record 0800/0863 as the known
   `def` presentation exception rather than treating it as cache divergence.
3. Add a future-text section to `plan-stdlib.md` that clearly labels the
   Byte/`Utf8Literal` track unimplemented. Sketch the eventual module split
   between byte validation, code-point decoding, grapheme algorithms,
   alternate encodings, and formatting. Keep native `String` modules and
   primitives live until separately approved migration and parity gates.
4. In that plan, retain the negative-accumulator `int-to-string` algorithm so
   `INT_MIN` is representable, and specify its future self-test matrix:
   zero, positive, negative, `INT_MAX`, and `INT_MIN`. Do not implement it
   until Byte/literal construction and the validated-text result boundary are
   settled.
5. Write a narrow `def` face-3 options note for user decision. At minimum
   compare retaining value-only zero-argument substitution, teaching the macro
   to forward application to its thunk result, and introducing a distinct
   stdlib binding macro for callable values. Judge ordinary values, closures,
   currying, evaluation count, diagnostics, and compatibility. Do not turn
   `def` into a core special form and do not couple the choice to the 0863
   presentation implementation.
6. Re-run the changed stdlib self-test module and the targeted cache matrix.
   Escalate only a newly observed compiler/runtime defect through a narrow
   failing-not-ignored `/testing` repro; do not duplicate 0800 or 0863.

## Phase 6b execution

- Added seven language-level `split`/`join` guards covering nonempty and empty
  inputs, empty Vec, multi-character delimiter, round trip, and returned
  String lifetimes. Added `str` macro guards in the same backing module.
- Added `defs.test` with `const` and `def` value guards, making the
  zero-argument binding family part of the stdlib macro probe.
- Added the unimplemented future-text plan to `plan-stdlib.md`, including the
  prospective module split and negative-domain `int-to-string` matrix.
- Added `def-face-3-options.md`; no option is selected.
- Cold-cache `/run-tests` results: `text.string.test` 26/26,
  `control.test` 13/13, `fn.threading.test` 14/14, `derive.test` 28/28, and
  `defs.test` 2/2.
- The existing six-permutation REPL/Run/Link fresh/cached macro guard,
  `build_confidence::mode_equiv_macro_user_defined`, passes.

The restored-cache replay exposed a separate harness limitation: after the
same named public imports in a second REPL process, `/run-tests` reports no
test functions for all five private test children. The modules themselves
load without a macro error, so this is not evidence of macro semantic
divergence. It requires a narrow `/testing` discriminator for cached private
test-child enrolment before attribution or a new FIXME; none is filed here.

## Evidence reviewed

- `sprints/SPRINT.md`, especially W5 and W7
- `design/arch/byte-backed-text.md`
- `crates/cranelisp-primitives/src/string.rs` and its split/join tests
- `stdlib/text/string.cl` and `stdlib/text/string/test.cl`
- `stdlib/defs.cl`
- `design/arch/fixmes/0800-def-macro-expansion-leaks-internal-thunk-name-and-blocks-call.md`
- `design/arch/fixmes/0863-cluster-wide-prepared-macro-presentation-transaction.md`
- `tests/build_confidence.rs::mode_equiv_macro_user_defined`
- `tests/spec_11_stdlib.rs` deferred `def` presentation guards

## Next skills

- `/stdlib` — execute the six Phase 6b actions above, stopping for the user's
  `def` face-3 API choice before implementation.
- `/sprint` — record this Phase 6a assessment and coordinate it with the other
  user-proxy plans.
- `/testing` — author a narrow repro only if Phase 6b reveals a new language
  defect; first discriminate the observed restored-cache private test-child
  enrolment gap, and retain the existing split/join, macro-cache, and deferred
  `def` evidence.
- `/dev` — implement FIXME 0863 in its target sprint without a stdlib-specific
  presentation path.
- `/arch` and `/spec` — retain the Byte-backed text work as design-only until
  the unresolved semantic gates are brought to the user.
