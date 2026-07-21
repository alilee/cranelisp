---
number: 0718
target: /dev (int)
filed_by: /design (int)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: src/process_form/macro_resolution.rs (qualify_scoped family, :466–674)
  + src/expander.rs (expand_scoped defn body scope) +
  design/int/expansion-qualification-scope.md §2.4/§2.5/§2.6
status: open
---

# Qualify-walk residual code fixes — quote shield + defn self-name + defmacro shield

## Origin

The design rulings landed in `design/int/expansion-qualification-scope.md`
§2.4–§2.6 (S115, resolving FIXME 0699 — the design half, now deleted). This
FIXME carries the **code** half. Each ruling is verified against source in the
design doc; the shapes below are the binding contract, not a re-derivation.

## The three fixes (one wave, `qualify_scoped` in `macro_resolution.rs`)

1. **Quote shield (Important — §2.4).** `qualify_scoped` recurses into
   `(quote …)`/`quasiquote` templates as ordinary lists and rewrites a quoted
   DATUM (`'(name)` → `'(dm/name)`, a different runtime value). Add the Rule Q /
   Rule QQ equivalent, structurally identical to `expand_scoped`'s shield: hold
   `(quote X)` fully verbatim; walk a `quasiquote` body verbatim except live
   `unquote`/`unquote-splicing` bodies (re-entered through `qualify_scoped`),
   tracking qq nesting depth. Recognize the family with the SAME
   `quasiquote.rs::is_quote`/`is_quasiquote` the expander shield + fold use —
   never a private copy (Principle 7). **/qa cell:** a foreign macro expanding to
   `'(name)` where `name` collides with a defining-module symbol; assert the
   quoted datum stays bare.

2. **defn self-name in body scope (Minor — §2.5).** `qualify_defn` pushes the
   name verbatim but omits it from the body scope, so a first-definition
   recursive self-call (`(defn f [x] (f x))`, `f` also in a defining module)
   mis-qualifies to `dm/f`. Seed the body scope with the defn name (body under
   `params ∪ {name}`). `expand_scoped`'s `expand_defn` shares the shape — mirror
   the fix there in the SAME change-set (shared enumeration, Principle 7). **/qa
   cell:** the first-definition self-recursion collision.

3. **defmacro shield (Minor — §2.6).** A macro-emitted `(defmacro name …)`
   recurses as ordinary children and can qualify the NAME/params on collision →
   frontend wrong-reject. Mirror `expand_scoped`'s CS-D1 defmacro shield: hold
   the `defmacro`/`defmacro-` head + name + param bracket(s) verbatim; qualify
   only clause bodies. **/qa cell:** a macro emitting a defmacro whose name
   collides with a defining-module symbol; assert the emitted name stays bare and
   the def registers.

## Acceptance

Unit-tier per METHOD §2.2 at the `qualify_scoped` seam (fail-on-revert), plus the
three /qa e2e cells above. The shared binder/quote enumeration stays single-
sourced across `qualify_scoped` and `expand_scoped` (no second copy — the P7
mirror this whole F8 chain removes).
