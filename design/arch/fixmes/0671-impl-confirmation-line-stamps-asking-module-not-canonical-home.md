---
number: 0671
target: /dev
filed_by: /repl
filed_at: 2026-07-19
sprint_filed: 113
refers_to: src/repl/format.rs:497-501 (bare-lookup path) + :707-710
  (definition-echo path) — the impl-confirmation line `impl Trait for Type`;
  governed by design/arch/resolve-home-enumeration.md (Principle 24 "resolve
  once"); same CLASS as the S112-guarded `impl user/Functor for user/Functor`
  defect (src/eval.rs:67/:886)
status: open
---

# impl-confirmation line stamps the asking module on trait AND type, not each name's canonical home

## Finding (S113 Phase 6a, /repl outside-in sweep)

The REPL's `impl Trait for Type` confirmation line (both the definition echo
and bare lookup of a `Trait.Type` TraitImpl entry) qualifies **both** the trait
name and the target type with the **asking module** (`module`, the module the
impl record lives in — `user` for a REPL impl), regardless of where the trait
or the type actually lives. It does not chain-follow either name to its
canonical home.

Minimal repro (clean scratch dir, `CRANELISP_LIB=<stdlib>`):

```clojure
(deftype W (MkW [:Int n]))
(impl Display W (defn show [w] "x"))
;; ACTUAL:   impl user/Display for user/W
;; EXPECTED: impl text.display/Display for user/W   (Display's home is text.display)

(deftrait Foo (bar [a] Int))
(impl Foo Int (defn bar [x] (* x 2)))
;; ACTUAL:   impl user/Foo for user/Int
;; EXPECTED: impl user/Foo for primitives/Int        (Int's home is primitives)
```

`Display` bare-lookup correctly resolves to `:text.display/Display`; `Int` is
`primitives/Int` everywhere else. Only the impl-confirmation line mis-qualifies.
**Dispatch and persistence are unaffected** — `(bar 21)` → 42, impls survive
restart (RT-4 verified), and `user.cl` preserves the bare authorship. The defect
is display-only, but the output is a **wrong fully-qualified name**, which the
self-documenting-REPL principle forbids (root CLAUDE.md §Design Principles).

**Reproduced live in a shipping demo:** `repl/demos/05-traits.demo` renders
`impl user/Zeroable for user/Int` / `impl user/Zeroable for user/Float` — the
flagship traits demo shows the mis-qualification as if it were correct output.

## Root cause

`src/repl/format.rs`, both TraitImpl arms:

```rust
if let Some((trait_name, target_type)) = name.split_once('.') {
    doc.plain("impl ");
    push_fq_name(&mut doc, module, trait_name);   // <- stamps asking `module`
    doc.plain(" for ");
    push_fq_name(&mut doc, module, target_type);  // <- stamps asking `module`
}
```

`push_fq_name(doc, module, name)` composes `module/name` from the asking module,
never resolving `trait_name`'s home (chain-follow the trait reference to its
defining module per Decision 45 / the `TraitImpl.impl_module` back-pointer) nor
`target_type`'s home (the type's canonical module). This is the
`resolve-home-enumeration.md` §3 rule-1 discipline unapplied at this seam:
resolve each name's home ONCE, root the display at that home.

## Requested action (/dev, resolve-home-enumeration.md authority)

Resolve the trait and the type each to its canonical home before rendering the
impl-confirmation line (both format.rs sites), so `impl <trait-home>/Trait for
<type-home>/Type`. A minimal repro should become a **/testing pin** first
(failing, `// spec:` repl/spec.md §1.3) per the defect protocol; once pinned,
this FIXME can be deleted (the test is the record + trigger).

## Companion spec elaboration (/repl-owned, 6b)

repl/spec.md §1.3's only impl example uses a same-module trait+type
(`impl user/Sizeable for user/Circle`), so the cross-module home rule is
unspecified. /repl tightens §1.3 in Phase 6b to state that the impl line
qualifies the trait and the type each by its **canonical home module**, not the
asking module — the prose the pin annotates.
