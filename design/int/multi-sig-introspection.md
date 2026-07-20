# Multi-Sig REPL Bare-Symbol Display (Step 5d (ii))

Implementation design for the REPL bare-symbol introspection that displays one line per variant for an overloaded (multi-sig) function.

Spec anchors: `repl/spec.md §1.3` (definition results — overloaded fn shows all variants) + `§4.1.1` (function symbol lookup — overloaded fn shows all variant signatures, one per line). Test contract: `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants` (currently failing).

## 1. Problem Statement

Per `repl/spec.md §4.1.1`:

> Overloaded functions show all variant signatures, one per line:
>
> ```
> user> map
> :(Fn [(Fn [a] b) (user/Vec a)] (user/Vec b)) user/map ; defn - Transform elements
> :(Fn [(Fn [a] b) (user/List a)] (user/List b)) user/map
> ```

Today the REPL prints only the first variant (the base entry's `scheme.ty`), which carries the type of one specific variant only. The other variants — stored on `DefKind::Overloaded.variants` as `Vec<OverloadVariant>` — are silently dropped.

The failing test:

```rust
fn display_overloaded_fn_shows_all_variants() {
    let mut session = repl_session();
    session.eval("(defn pick ([:Int x] x) ([:Int x :Int y] (add-i64 x y)))").unwrap();
    let display = repl_eval_display(&mut session, "pick");
    let has_1_arg = display.contains("[primitives/Int]") || display.contains("[Int]");
    let has_2_arg = display.contains("[primitives/Int primitives/Int]") || display.contains("[Int Int]");
    assert!(has_1_arg && has_2_arg, "...");
}
```

Both signatures must appear in the display output.

## 2. Key Design Decisions

### 2.1 Where the change lands

**Choice**: `format_def_entry` in `src/session_v4.rs` (around line 3150). This is the single function that produces the bare-symbol display string for `ModuleEntry::Def` entries. It already classifies `DefKind::Overloaded` (the `format_entry_sig` helper at line 349 already treats it as `"defn (multi)"`); the change is to enumerate variants instead of printing one line.

The `format_def_entry` function is called from two paths:

- `eval` returning a definition (the REPL prints `format_def_entry(&entry, name, &module)`).
- Bare-symbol lookup via `describe_symbol`-equivalent path (line 3122).

Both paths share the function — one fix lights up both.

### 2.2 Format per variant

Each variant gets its own primary line, identical in structure to a regular defn:

```
:(Fn [param-types...] return-type) user/name ; defn{ - docstring}
```

The docstring (if present) attaches to the *first* line only. Subsequent variant lines omit the `; defn - docstring` suffix and just show the type:

```
user> pick
:(Fn [primitives/Int] primitives/Int) user/pick ; defn - Pick one or sum two
:(Fn [primitives/Int primitives/Int] primitives/Int) user/pick
```

This matches the `map` example in the spec (`§4.1.1` quoted above): first line carries `; defn - Transform elements`, second line is type+name only.

### 2.3 Variant ordering

**Choice**: source order — the order variants appeared in the `defn` form. `OverloadVariant` is stored in a `Vec` (preserves insertion order); the registration path (`register_multi_sig`-equivalent in `cranelisp-typecheck`) populates the vec in source order. The display walks the vec in order.

Rationale: matches the user's mental model of "the order I wrote the clauses." Alternatives (sort by arity, sort by some canonical type ordering) add complexity without clear benefit.

### 2.4 What about constraints? — CORRECTED (S113, D1 defect)

> **This subsection's original claim was WRONG and is the D1 defect.** The
> original text asserted "a constrained variant's constraints would already be
> reflected in `param_types` themselves … no new constraint formatting needed."
> That is false: a constrained-poly variant `(Fn [:Num a :Num a] a)` has the
> constraint `:Num` on the **type var `a`**, which is a `Scheme`-level fact — the
> bare `Type::Fn` reconstructed from `{param_types, ret_type}` carries only the
> var `a`, NOT its `:Num` bound. So the current render at
> `src/repl/format_type.rs:42` (`Type::Fn(v.param_types.clone(), box
> v.ret_type.clone())` → `format_type_qualified`) prints `(Fn [a a] a)` where the
> settled scheme is `(Fn [:Num a :Num a] a)` — the pinned D1 defect
> (`tests/multi_sig_variant_display_constraint_drop.rs`, `class=display-envelope-mirror`).
> The single-sig echo (which renders the full `Scheme`) and the multi-sig variant
> render diverge for the same inferred scheme — the classic envelope-mirror.

**The D1 fix — keyed read-follow of the recorded template `Scheme` (S113 W4,
arch-confirmed).** `/arch` ruled the fix is int-side (option B — a P7 second home
+ the forbidden schema bump were rejected; D1 moved W2→W4 on this re-attribution).
The constraint-bearing scheme is **already recorded by typecheck** on the mangled
variant `Def`: `register.rs:345` builds each variant entry via
`ModuleEntry::def(scheme.clone(), DefKind::UserFn { … })`, where `scheme` carries
the `:Num` constraints for a genuinely-poly variant. `OverloadVariant.mangled_name`
is the key. So the render **fetches the recorded scheme and renders IT**, never
re-deriving from the bare `param_types`:

```
for each variant v in variants:
    match st.get(v.mangled_name) {
        Some(ModuleEntry::Def { scheme, .. }) => render scheme    // constraints intact
        _ => { debug_assert!(false, "multi-sig variant {mangled} has no template scheme");
               render bare Type::Fn(v.param_types, v.ret_type) }  // release fallback ONLY
    }
```

This reads typecheck's **settled record** (Principle 26 — render from settled
state, never re-derive at the echo; the same discipline the eval.rs
`impl_echo_type_name` defect taught). A concrete (unconstrained) variant's scheme
has empty constraints and renders byte-identical to the current bare `Type::Fn`, so
the change is constraint-restoring for poly variants and a no-op for concrete ones.

**Binding arch pin (confirmed here).** The fetch miss is an **invariant breach**,
not a normal path: `debug_assert!` fires in dev (an `OverloadVariant.mangled_name`
that resolves to no scheme means the variant table and the symbol table
disagree), and the release fallback is the **bare render** (current behaviour) —
NEVER a silent constraint-stripped render treated as correct, and NEVER a
re-derivation dressed up as the answer. The scheme is rendered via the existing
`format_scheme_display` (constraint-aware); `format_type_qualified` on a bare
`Type::Fn` is retained ONLY as the asserted-against fallback.

**Signature impact (int-only, no `cranelisp-types`, no schema bump).**
`format_overloaded_variants_doc` (`format_type.rs:42`) currently takes `(name,
module, variants, docstring)` and has no table access. It gains the symbol-table
view for the keyed lookup (or the caller `format_def_entry`, which already holds
the entry+table, pre-resolves `Vec<&Scheme>` and passes it). Either shape stays
inside `src/repl/` — the D1 defect and its fix are wholly int-surface. The
`/typecheck` §7 note below (which said "no change required — the existing fields
suffice") stands: typecheck already records the constraint scheme; the miss was
int **not reading it**.

### 2.5 What about `format_entry_sig` (the `/sig` slash command path)?

`format_entry_sig` at line 342 is a shorter, single-line formatter used by `/sig`. It currently classifies multi-sig as `"defn (multi)"` and returns one line. Per `repl/spec.md` §4.1.1, the same multi-line behaviour should apply to `/sig` output. Step 5d (ii) updates BOTH formatters in lockstep:

- `format_def_entry` — bare-symbol lookup display (multi-line per variant).
- `format_entry_sig` — `/sig <name>` output (multi-line per variant).

Both call into a shared helper `format_overloaded_variants(name, module, variants, docstring)` to keep the formatter DRY.

## 3. Format Example

For the test's `pick` definition:

```
(defn pick
  ([:Int x] x)
  ([:Int x :Int y] (add-i64 x y)))
```

Current output (one line, broken):

```
:primitives/Int user/pick ; defn
```

Target output (two lines, one per variant):

```
:(Fn [primitives/Int] primitives/Int) user/pick ; defn
:(Fn [primitives/Int primitives/Int] primitives/Int) user/pick
```

For an overloaded `map` with a docstring:

```
:(Fn [(Fn [a] b) (user/Vec a)] (user/Vec b)) user/map ; defn - Transform elements
:(Fn [(Fn [a] b) (user/List a)] (user/List b)) user/map
```

## 4. Affected Files

| File | Change |
|---|---|
| `src/session_v4.rs` `format_def_entry` (around line 3150) | Branch on `DefKind::Overloaded { variants }`; if non-empty, return multi-line output joined by `\n`. The first line carries the docstring suffix; subsequent lines do not. |
| `src/session_v4.rs` `format_entry_sig` (around line 342) | Same multi-line treatment; replace `"defn (multi)"` with the per-variant enumeration. |
| `src/session_v4.rs` (new helper) | `fn format_overloaded_variants(name: &str, module: &ModuleFullPath, variants: &[OverloadVariant], docstring: Option<&str>) -> String`. ~20 lines. |
| `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants` | Currently failing; flips green when the formatter lands. |

## 5. Implementation Sketch

```rust
fn format_overloaded_variants(
    name: &str,
    module: &ModuleFullPath,
    variants: &[OverloadVariant],
    docstring: Option<&str>,
) -> String {
    let mut lines = Vec::with_capacity(variants.len());
    for (i, v) in variants.iter().enumerate() {
        let fn_ty = Type::Fn {
            params: v.param_types.clone(),
            ret: Box::new(v.ret_type.clone()),
        };
        let type_str = format_type_qualified(&fn_ty);
        let line = if i == 0 {
            // First variant carries classification + docstring.
            let base = format!(":{type_str} {module}/{name} ; defn");
            append_docstring_comment(base, docstring)
        } else {
            // Subsequent variants are type+name only.
            format!(":{type_str} {module}/{name}")
        };
        lines.push(line);
    }
    lines.join("\n")
}
```

The two callers swap their existing `Overloaded` branches for a call into this helper.

## 6. Edge Cases & Invariants

- **Single-variant `Overloaded`**. Should not occur in practice (the typechecker creates `Overloaded` only when a base name has 2+ variant signatures), but if it does: emit one line — correct degenerate behaviour.
- **Zero variants** (`variants: vec![]`). Current code guards via `format!(":{} ...", scheme.ty)` — returns the base scheme. Step 5d (ii) preserves this fallback: if `variants.is_empty()`, fall back to single-line `format_def_entry` behaviour. (Should never happen — `Overloaded` with empty variants is a typecheck bug — but defensive.)
- **Variants with type vars**. `format_type_qualified` already handles `Type::Var`; emits lowercase letters (`a`, `b`, ...). Polymorphic variants display correctly.
- **Variants whose `ret_type` is itself a function** (curried definition). `format_type_qualified` handles nested `Type::Fn`. `(Fn [Int] (Fn [Int] Int))` displays as expected.
- **Constructor entries that happen to be multi-sig** (e.g., a parameterised ADT constructor). `Constructor` is a separate `ModuleEntry` variant, not `Def { kind: Overloaded, ... }`. Out of scope.
- **Trait method impls with multiple specialisations**. Trait methods are stored as separate `Def` entries per impl (mangled name `Trait.method$Type`), not as variants on a single `Overloaded`. Bare-symbol lookup of a trait method name (`+`) hits the `TraitDecl` entry, which has its own display format. Not affected by Step 5d (ii).
- **Newline ordering in multi-line REPL output**. The display string is returned as `\n`-joined; the REPL println adds a trailing newline. Consistent with the existing single-line behaviour.

## 7. Cross-Skill Coordination

| Skill | Coordination |
|---|---|
| `/repl` | Owns `repl/spec.md`. The §4.1.1 example (with `map`) is the canonical format target; Step 5d (ii) implements to match. If the spec's exact wording needs tightening (e.g., docstring placement), `/repl` adjusts the spec; `/int` mirrors. |
| `/qa` | Confirms `tests/repl_experience.rs::display_overloaded_fn_shows_all_variants` flips green. Optional: companion negative test (single-variant defn does NOT emit duplicate lines). |
| `/typecheck` | Owns `OverloadVariant` shape. No change required for Step 5d (ii) — the existing fields (`param_types`, `ret_type`, `mangled_name`) suffice. |

## 8. Sketch Comparison

The sketch had multi-sig functions and displayed them in `/sig` and bare-symbol lookup. Its display approach was very similar to the target here: enumerate variants, one line per variant, with the first line carrying the classification and docstring. The sketch's `format_overloaded_variants` (or equivalently named function — exact name varies in the sketch) was a single helper called from both `/sig` and bare-symbol display, exactly as proposed here.

This is a case where the reimplementation directly follows the sketch's solution. The reimplementation lost the multi-line behaviour at some point during the v4 pipeline migration (`format_entry_sig` shows the symptom — `"defn (multi)"` is a placeholder classification, not the per-variant enumeration). Step 5d (ii) restores the sketch's correct behaviour to the new structure.

The only structural divergence: the sketch read variants from a `multi_signatures: HashMap<Symbol, Vec<MultiSigVariant>>` side table; the reimplementation reads them directly from `DefKind::Overloaded.variants`. The data is structurally identical; the reimplementation's storage is more cohesive (one entry per name, variants on the entry).

## 9. Open Questions

- **Docstring on which variant?** The current `Def` entry has one `docstring: Option<String>` field at the entry level; per the spec example, the docstring attaches to the entry as a whole, displayed on the first variant line. No per-variant docstrings exist (and the spec doesn't ask for them). If a future feature adds per-variant docstrings (e.g., per-clause), the format extends naturally — first variant gets entry-level + per-variant; subsequent variants get per-variant only.
- **Ordering when source order is ambiguous** (e.g., variants registered out-of-order via `defn-extension` macro or REPL incremental redefinition). Source order is "order in the most recent registration"; for incremental REPL additions this is "order they were entered." Acceptable; matches user mental model.

## 10. Next Skills

- `/qa` — verify test flips green; consider negative test for single-variant defn (does NOT print duplicate).
- `/repl` — confirm display matches §4.1.1 spec example; refresh demo if applicable.
