---
number: 0833
target: /testing
filed_by: /repl
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/05-definitions.md §5.4.5 ("The method parameter count and types
  MUST conform to the trait's declared signature") + repl/spec.md §18.9
  (impl redefinition — a re-`impl` is rejected at the conformance seam);
  resolver /dev (typecheck — impl conformance check)
status: open
---

# An `impl` method with MORE parameters than the trait declares is silently accepted; the extra binder is simply never bound

## Severity

Defect. §5.4.5's parameter-count MUST is unenforced in one direction. The form is
accepted, dispatch proceeds, and the user's extra parameter vanishes without a
word. When the body *does* reference it, the error names the binder
(`undefined variable: junk`) rather than the mismatch, and the failed batch then
poisons the next REPL turn with an internal-looking codegen message.

Found while authoring the S115 Phase-6b impl-redefinition demo beat — I reached
for "a non-conforming re-`impl` is rejected" and an arity mismatch turned out
**not** to be non-conforming as far as the compiler is concerned. It is not
re-`impl`-specific: the **first** `impl` behaves identically, so this is a
plain conformance hole that impl redefinition merely walked into.

## Minimal repro — REPL, unused extra param: silently accepted

```clojure
(deftype Box (MkBox [:Int w]))
(deftrait Sizeable (size [x] Int))     ;; ONE parameter declared
(impl Sizeable Box (defn size [b junk] 3))   ;; TWO written — accepted
(size (MkBox 5))
```

Observed (`target/debug/cranelisp`, clean scratch cwd, 2026-07-21, HEAD
`233ad7b4`):

```
user> (impl Sizeable Box (defn size [b junk] 3))
impl user/Sizeable for user/Box
user> (size (MkBox 5))
:primitives/Int 3
```

Expected: a located conformance error naming the trait's declared arity and the
impl's, in the shape of the existing `impl Sizeable for Box: missing required
method tag` message (which *is* emitted for the completeness half of the same
rule).

## Second face — used extra param: the diagnostic blames the binder, then poisons the next turn

```clojure
(impl Sizeable Box (defn size [b junk] (+ junk 1)))
(size (MkBox 5))
```

```
Error: type error at 42..46: undefined variable: junk
Error: codegen error at 0..16: codegen failed for /: codegen error at 0..16:
  resolved_target 'user/Sizeable.size$user/Box' for call 'Sizeable.size$user/Box'
  fetched no symbol-table entry (S110 W1 entry-miss; backend-keyed-consumer.md §1.3)
```

The first line tells the user their own parameter is undefined — the extra binder
is dropped rather than rejected, so the body cannot see it. The second line is a
*subsequent turn* failing on the wreckage of the first (cf. FIXME 0817, sticky
failed codegen batch); it names an internal symbol-table invariant, which no user
can act on.

## Isolation

| Variant | Result |
|---|---|
| First `impl`, extra param **unused** | **accepted**, dispatches (returns `3`) |
| First `impl`, extra param **used** | `undefined variable: <binder>`, then next turn poisoned |
| Re-`impl`, extra param unused | **accepted**, dispatches — same as first `impl` |
| Re-`impl`, **omitting** a required method | correctly rejected (`missing required method tag`) |

So the completeness half of §5.4.5 is enforced and the arity half is not.

## Ask

A narrow failing-not-ignored repro of the unused-extra-param cell (the silent
one — it is the soundness-relevant face: a form that violates a spec MUST and
produces a working dispatch), `// spec:` annotated to
`spec/05-definitions.md §5.4.5`, with `FIXME(/dev)` naming typecheck's impl
conformance check as the resolver. The used-extra-param cell is worth a second
row for the diagnostic quality, but the silent cell is the defect.

Worth pairing with the standing coverage-by-definition-variants category: the
conformance check needs an `{arity too high, arity too low, wrong param type,
wrong return type, missing method, extra method}` × `{first impl, re-impl}`
matrix. This finding is one empty cell in it; `missing method` is the only cell
I probed that is filled.
