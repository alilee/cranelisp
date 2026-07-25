# Sprint 117 documentation assessment and action plan

**Phase 6a status:** complete

**Phase 6b status:** complete

## Assessment

Sprint 117 shipped two user-facing language/REPL improvements that need
documentation work:

1. An `impl` trait position is a **reference**, not a binder. Conventional and
   higher-kinded impls may name the trait with either a bare name or a
   module-qualified name. Resolution uses the trait's canonical identity, so
   the written qualifier does not become part of a method name. This is now
   implemented and tested, but the traits guide currently teaches only the
   bare examples and says merely that the trait must be "in scope." That
   wording obscures the useful fully-qualified route and sits too close to the
   later, correct rule that a `deftrait` declaration head is a bare binder.
2. REPL type displays and introspection are more consistent. Constraints retain
   the trait's canonical home in definition echoes, bare lookups, and `/sig`.
   `/info <Trait>` and `/info <Type>` are inverse views of the same live impl
   relation, including imported impls and replacement de-duplication. A genuine
   code-generation failure also discards the whole failed turn: the diagnostic
   names the actual failing compilation subject, and a later expression or
   clean same-name definition can proceed without stale code or metadata.
   Existing trait and live-development guides cover adjacent behavior, but not
   these delivered guarantees as one discoverable user workflow.

The runtime work does not create a new language or standard-library surface.
`split` and `join` still accept and return the same native `String` and
`(Vec String)` values. The two new Rust-path intrinsics are an internal
ownership boundary, not functions users can call and not String-specialized
alternatives to general `(Vec a)` operations. The R-2 ownership evidence is
likewise compiler assurance rather than a documentation feature. FIXME 0859
records the one deferred `ProjectionOf` production-evidence question; user
documentation must not turn that evidence gap into a language-level ownership
promise.

The Byte-backed text track is **design only**. Cranelisp still has native
`String`; it did not gain `Byte`, `(Vec Byte)` text, `Utf8Literal`, transparent
one-field products, code-point or grapheme ADTs, or stdlib `int-to-string`.
The future recommendation—initially word-sized `Byte`, ordinary wide-slot
`(Vec Byte)`, a compiler-certified UTF-8 literal with the same representation,
and Unicode policy in stdlib—must not appear in live guides as available
behavior. Compact Byte storage is also deferred; it is a future general Vec
representation migration, not a shipped Byte-specific feature.

Finally, generic zero-argument-macro presentation did **not** ship. A stdlib
`def` can still echo its generated `*-def` thunk, and `/info` or `/sig` can
describe the macro carrier instead of the public value. FIXME 0800 remains the
user-visible symptom and stdlib face-3 API question; FIXME 0863 records the
rejected Sprint 117 attempt and the proposed cluster-wide prepared transaction
for Sprint 118. Documentation must neither present the rejected behavior as
fixed nor teach the leaked implementation form as intended.

## Standing-quality verdict

The current docs remain truthful about native `String`, definition binders,
trait dispatch, and live redefinition. They do not falsely advertise the
design-only text model. The principal drift is omission rather than
contradiction:

- `guide/traits.md` does not say explicitly that conventional impl slot 1,
  HKT impl slot 1's trait component, and the HKT pairing head are trait
  references that may be qualified. Its phrase "needs the trait in scope"
  can incorrectly suggest that a bare import is mandatory.
- The traits and live-development guides show trait-side `/info` after
  re-`impl`, but do not teach the paired type-side view or canonical
  constraint display.
- The live-development guide describes recoverable redefinition failures, but
  does not state the broader atomic-turn guarantee now delivered for a genuine
  code-generation failure.
- No live user guide needs to expose the primitives declaration inventory,
  ownership summaries, Rust Vec-of-String helpers, or Byte-backed design.

No new cross-owner FIXME is needed. The only visible unshipped behavior found
by this assessment is already covered by 0800/0863, and the internal evidence
limit is already covered by 0859.

## Phase 6b action plan

1. Amend `guide/traits.md` immediately after the basic `impl` example with a
   qualified conventional example such as `(impl shapes/Describe Dog …)`.
   Explain in plain language that impl slot 1 reaches an existing trait, while
   `(deftrait Describe …)` introduces a bare name. Link to spec §§5.4 and 7.3
   rather than restating all resolution rules.
2. Update the HKT section with the qualified shapes:
   `(impl (collections/Functor f) (Functor Option) …)` and a qualified
   same-identity pairing head. Make clear that trait references compare by
   resolved identity while the constructor variable `f` is the echoed binder.
   Do not imply that the target constructor itself may be qualified where the
   current grammar requires it bare.
3. Add a compact introspection walkthrough to `guide/traits.md`: define one
   constrained function and one impl, show the canonical trait home in the
   function's lookup or `/sig`, then ask both `/info Trait` and `/info Type`.
   Explain that these are inverse views of live state, that local rows precede
   imported rows, and that replacing an impl does not create a history row.
4. Extend `guide/live-development.md` with the atomic failed-turn guarantee:
   a code-generation failure names the real failed subject, publishes none of
   that turn's definitions or introspection, and does not poison the next
   expression or clean same-name definition. Keep this as a recovery rule and
   link to `repl/spec.md §18.4`; do not teach a known compiler defect merely to
   manufacture a failing example.
5. Re-read all changed transcripts against the production tests and current
   binary. If a claimed qualified impl, canonical constraint, inverse drawer,
   or recovery transcript disagrees, request a narrow failing-not-ignored
   `/testing` repro before closing the item.
6. Leave live String/collection documentation unchanged in this phase. Do not
   add `Byte`, `Utf8Literal`, transparent wrappers, compact `(Vec Byte)`, or
   `int-to-string` to the guide index until their own implementation and
   normative gates ship. Do not document the Rust-path Vec-of-String helpers.
7. Where Phase 6b encounters `def` output, label it as known 0800/0863 behavior
   in the assessment evidence rather than copying the internal `*-def` shape
   into teaching prose or filing a duplicate FIXME.

## Phase 6b result

All seven actions are complete:

- `guide/traits.md` now distinguishes the bare `deftrait` binder from bare or
  module-qualified trait references in conventional and HKT impl heads. It
  explains resolved-identity matching for the HKT pairing head without
  relaxing the bare target-constructor rule.
- The same guide now shows canonical constraint display and the paired
  `/info <Trait>` / `/info <Type>` views, including live-row de-duplication and
  local-before-imported ordering.
- `guide/live-development.md` now records whole-turn recovery and
  cold/restored-cache macro parity without exposing transaction carriers or
  teaching a known failure trigger.
- That guide also identifies 0800/0863 as the known `def` presentation gap and
  warns against relying on the generated thunk name.
- The Phase 6b replay found three separate user-visible limitations. The
  polymorphic-product accessor gap is noted narrowly in
  `guide/field-accessors.md` under FIXME 0867. The two fresh/cache divergences
  are noted in `guide/live-development.md` under FIXMEs 0868 and 0869, with
  `--no-cache` described only as an affected Run-workflow workaround and no
  promised repair date.
- Live String and collection docs remain unchanged. No internal unsafe helper
  is described as callable, and no guide claims `Byte`, `Utf8Literal`,
  transparent products, compact `(Vec Byte)`, or `int-to-string` exists.

The conventional qualified impl, inverse introspection, canonical constraint,
and qualified HKT shapes were replayed against
`target/debug/cranelisp --no-cache --no-color` in an isolated `/tmp` workspace
with the repository stdlib on `CRANELISP_LIB`; all produced the documented
behavior. The existing six-permutation user-defined-macro guard also passed
with workspace `TMPDIR`:

```text
cargo nextest run --no-fail-fast --test build_confidence mode_equiv_macro_user_defined
1 test run: 1 passed, 17 skipped
```

## Evidence reviewed

- `sprints/SPRINT.md`, especially W2, W3a–W3c, W4b, W5, and W7
- `spec/05-definitions.md` §5.4 and `spec/07-traits.md` §7.3
- `design/typecheck/qualified-trait-impl.md`
- `design/int/s117-conformance-recovery.md`
- `design/arch/byte-backed-text.md`
- `design/arch/fixmes/0800-def-macro-expansion-leaks-internal-thunk-name-and-blocks-call.md`
- `design/arch/fixmes/0859-primitives-ownership-facts-production-witnesses.md`
- `design/arch/fixmes/0863-cluster-wide-prepared-macro-presentation-transaction.md`
- `design/arch/fixmes/0867-polymorphic-product-bare-field-alias-missing.md`
- `design/arch/fixmes/0868-cache-restored-parent-does-not-enrol-private-child.md`
- `design/arch/fixmes/0869-cache-restoration-loses-sibling-written-trait-impls.md`
- `tests/repl_introspection.rs` and `tests/spec_11_stdlib.rs`
- `user/guide/traits.md`, `user/guide/live-development.md`, and
  `user/errors/trait-impl-diagnostics.md`
- `repl/sprint-117-phase-6.md` and `stdlib/sprint-117-phase-6.md`

## Next skills

- `/sprint` — record docs Phase 6b complete and reconcile FIXMEs 0867–0869 with
  the other user-proxy findings before the sprint gate.
- `/qa` — attribute 0867 and add the required plan rows/disposition for the
  already-reproduced 0868 and 0869 defects.
- `/dev` — address 0868/0869 only after sprint disposition, and implement
  deferred 0863 in its target sprint; no documentation workaround is requested.
- `/repl` and `/stdlib` — keep their completed Phase 6 work aligned with the
  same 0800/0863 distinction.
- `/arch` and `/spec` — retain the Byte-backed text track as design-only until
  its future user gates and implementation increment are approved.
