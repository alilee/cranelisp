---
number: 0832
target: /testing
filed_by: /examples
filed_at: 2026-07-21
sprint_filed: 115
refers_to: spec/07-traits.md §7.1.5 (default method implementations) +
  the S115 impl-redefinition ruling; resolver /dev (typecheck/backend —
  redefinition machinery vs default-method body linkage)
status: open
---

# Re-`impl`ing a trait for a type breaks the trait's DEFAULT method: its body can no longer reach a sibling method (`undefined function`)

## Severity

Defect. Two shipped S115 surfaces intersect here — trait default methods
(§7.1.5) and impl redefinition — and their intersection does not compile.
It is silent until you write the second `impl`, and the error is reported
inside the **`deftrait`**, which is not where the reader made a change.

## Minimal repro (7 lines, free-standing, `primitives` only)

```clojure
(deftrait Sized
  (size [x] Int)
  (tag [x] Int (add-i64 (size x) 1000)))     ;; default body calls sibling `size`
(deftype Box [:Int n])
(impl Sized Box (defn size [b] (match b [(Box v) v])))
(impl Sized Box (defn size [b] (match b [(Box v) (mul-i64 v 10)])))   ;; re-impl
(defn main [] (Pure (tag (Box 5))))
```

Observed (`target/debug/cranelisp --run`, `cwd = examples/`, 2026-07-21):

```
error: codegen error at 58..62: codegen failed for /:
       codegen error at 58..62: undefined function: size
```

Span `58..62` is the `size` **inside the default body of `tag`**, i.e. the
diagnostic points at the trait declaration, which the program never
changed.

Expected: `1050`, reported as exit `1050 mod 256` = **26** — the re-impl
wins (`5 * 10 = 50`), the default adds `1000`.

## It is the RE-IMPL that breaks it — isolated

Each of these compiles and runs correctly; only their combination fails.

| Variant | Result |
|---|---|
| Default body calls a sibling, **one** impl | **exit 237** (`1005 mod 256`) — correct |
| Default body is a constant (`(tag [x] Int 7)`), **two** impls | **exit 7** — correct |
| Default body calls a sibling, **two** impls | **FAILS** — `undefined function: size` |
| No default method at all, **two** impls (dispatch + dependents + cascade) | correct — this is `examples/33-redefinition.cl` at HEAD, exit 139 |

So the redefinition transaction re-links plain methods and their dependents
correctly (the S115 R3 behaviour example 33 now teaches), but a **default
method body's reference to a sibling method** is left pointing at something
the re-impl invalidated.

## Ask

A narrow failing-not-ignored repro, `// spec:` annotated to §7.1.5 + the
S115 impl-redefinition ruling, with `FIXME(/dev)` naming the resolver.
The repro above is already minimal — 7 lines, zero stdlib, zero platform.

## Note on the default-method spelling

The repro uses the **Disambiguation** spelling
(`(method [params] ret_type body)`), which is the only one the compiler
accepts today. The spelling itself is contested — **FIXME 0825** (Blocker,
`/spec`) records that `spec/02-grammar.md:200` and §7.1.5 specify the *other*
form and that the spec's own worked `Ord` example does not compile. If 0825
settles on the EBNF/§7.1.5 form, this repro's first three lines need
respelling; **the defect it isolates is independent of that choice** — it is
about impl redefinition invalidating a default body's sibling reference, not
about how the default is written.

## Why `/examples` did not work around it

`examples/33-redefinition.cl` teaches impl redefinition at S115 6b and does
**not** hit this, because it has no default methods — the planned
"omitting a method from a re-impl reverts it to the trait default" sub-test
was deferred behind 0825 and would have landed straight on this bug. See
`examples/plan-examples.md` §2c.6.
