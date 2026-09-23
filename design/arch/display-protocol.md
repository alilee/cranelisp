# Display protocol — type-directed value render for the built-in collections

**Status: design, not implemented.** Mechanism settled at architecture level (S106) with both
user-visible choices ruled by the user on 2026-07-10 (§7). Nothing below is landed: the intrinsics
descriptor ABI has no `Collection` kind, `TypeDefInfo` carries no render marker, and
`repl/spec/01-display-format.md` §1.5 still declares the generic ADT form normative. The
implementation is unscheduled; its obligation is FIXME 0050 (`design/arch/fixmes/`, target the
binary's display layer). This document is the design an implementing sprint builds against and the
record of the two rulings, so neither is re-litigated.

## 1. Requirement

`repl/spec/01-display-format.md` §1.5 renders stdlib `List` and `Seq` through the generic ADT
formatter — `(List.Cons 1 (List.Cons 2 List.Nil))`, `(Seq.SeqCons h <closure>)` — and names the
surface forms `(list 1 2 3)` and `(seq h +more)` as the aspirational target, promoted to MUST only
when a mechanism exists. The render is type-directed: the value's nominal type selects a fold that
collapses the cons/nil spine. Nothing structural distinguishes `List` from any other two-constructor
recursive ADT, so selection is by type identity, never by shape.

## 2. Two render paths, one output

| Path | Code | Substrate |
|---|---|---|
| REPL result echo (`:Type value`) | `src/display.rs::format_result_value` / `format_value` | live heap value + live `TypeDefInfo` from the session tables |
| Trace capture (`(trace …)`) | `cranelisp-intrinsics` `cranelisp_trace_format(value, descriptor)` | backend-baked `DisplayDescriptor` blob; no symbol tables, `--link`-safe ([tracing](tracing.md) §3.4) |

There is no third path: `--run`/`--link` program output goes through in-language `print`, never the
compiler's ADT display. **Invariant: the same value renders byte-identically on both paths.** A
mechanism that only the REPL learned would print `(list 1 2 3)` at the prompt and `(List.Cons …)`
inside a trace of the same session, so the mechanism lives in the shared descriptor vocabulary, not
in a REPL-only table.

## 3. Dispatch: a compiler-internal render marker on the type definition

Both formatters read one datum, a render marker on `TypeDefInfo`
([Principle 7](principles/07-single-source-of-truth.md)). The REPL path reads it off the live
record; the backend reads the same record when it bakes the trace descriptor and emits a
`Collection` descriptor instead of an `Adt` one.

- **The marker is data, not code.** It says "spine-shaped collection with surface keyword K;
  spine constructor tag C with head field H and tail field T; nil tag N; lazy tail?". The
  formatter performs the fold. No method is resolved and no user code runs at render time, which
  keeps typecheck a passthrough (§6) and keeps the pure trace walk pure.
- **The marker is set only by a compiler-internal seed for the built-in `List` and `Seq`**
  (user ruling, §7.1). There is no language surface for it: no `deftype` annotation, and no way
  for a user type to opt in. The seed sits with the existing compiler-seeded type registrations
  (`src/bootstrap.rs::register_option_type` is the shape) and stamps the marker when those
  types are registered.
- **Principle 19 disposition.** Recognising `List`/`Seq` by identity is a bounded, user-ratified
  narrowing of [no module privileged by name](principles/19-no-module-privileged-by-name.md):
  one seed, the built-in collections only, no general mechanism. A user with custom inspection
  needs is routed to a future code-bearing `Display`-style trait (§8), not to a structural
  annotation that would reopen name-privileging for arbitrary types.

Carrier shape, to be authored in `cranelisp-types` by the implementing sprint (a serde-visible
field: `CACHE_SCHEMA_VERSION` bump and `public-api.txt` regeneration under the API gate):

```
TypeDefInfo.render: Option<CollectionRender>
CollectionRender { keyword: Symbol, spine_tag: i32, nil_tag: i32,
                   head_field: u32, tail_field: u32, lazy_tail: bool }
```

## 4. Descriptor ABI: extend, do not wrap

The design extends the landed `DisplayDescriptor` arena-blob ABI
(`crates/cranelisp-intrinsics/src/trace_format.rs`) and reuses its encoding unchanged: the
position-independent self-relative `i32` offsets, `BlobStr` strings, the 24-byte record, JIT and
object-mode baking, and the `cranelisp_trace_format(value, descriptor)` signature and arity.

Added:

1. `DescriptorKind::Collection = 8` — appended after `TypeVar = 7`; discriminants are the
   backend↔intrinsics contract and are never renumbered.
2. A `CollectionSpec` sub-block referenced from one of the record's reserved offset words
   (`_pad`/`_pad2`; `child0_off` carries the element descriptor as `Vec` does):
   `[ keyword: BlobStr | spine_tag | nil_tag | head_field | tail_field | lazy_tail | elem_child_off ]`.
   The element descriptor nests recursively, so `(List (Option Int))` bakes
   `Collection → Adt(Option) → Int`.
3. One arm in the `cranelisp_trace_format` walk: from the spine pointer, while the constructor tag
   equals `spine_tag`, render `head_field` through the element descriptor and advance through
   `tail_field`; stop at `nil_tag` or at an unforced lazy tail; emit `(<keyword> e…)`, appending
   `+more` when the walk stopped on a thunk.
4. The symmetric arm in `src/display.rs`, walking the live value and `TypeDefInfo` with the same
   fold and the same `+more` rule.

A `List` whose marker is absent still renders through the `Adt` arm; the change is strictly
additive. Wrapping — a `Collection` descriptor containing an `Adt` descriptor and post-folding its
text — was rejected: it double-encodes the constructor table and walks the value twice for no gain.

The fold is specified once (item 3) and implemented twice against two substrates, mirroring how
`format_value` and the trace formatter already share their heap-walking logic conceptually. A shared
crate for ~30 lines is not warranted; the consistency test in §9 is what pins the two together.

## 5. Seq laziness: the render never forces

A `Seq` tail is a thunk. The trace formatter is a pure descriptor walk with no evaluation, so it
structurally cannot force one; forcing on the REPL path alone would break the §2 invariant. Both
paths therefore render only the already-materialised spine and emit `+more` at the first unforced
tail: a fully-forced finite `Seq` renders `(seq 1 2 3)`, an infinite or partially-forced one
`(seq 1 2 +more)`, and both terminate. This preserves the existing §1.5 MUST that display never
force-evaluates a lazy tail (user ruling, §7.2).

## 6. Surfaces touched by the implementation

| Surface | Work |
|---|---|
| `arch` | `DescriptorKind::Collection`, `CollectionSpec` layout, `TypeDefInfo.render` carrier; API gate |
| `dev` (typecheck) | passthrough only — carry `TypeDefInfo.render` into the symbol table; no trait resolution or dispatch |
| `dev` (backend) | descriptor baker `Collection` arm |
| `dev` (intrinsics) | `cranelisp_trace_format` `Collection` arm |
| `dev` (`src/`) | `format_value` collection arm reading the live marker; the bootstrap seed for `List`/`Seq` |
| `dev` (`stdlib/`) | owns the `List`/`Seq` `deftype` sites the seed keys on; no source change to opt in |
| `spec` | promote §1.5 to MUST; `qa` restores the traceability band |

Typecheck's passthrough is the containment litmus: the declarative-data choice means there is no
compile-time dispatch to resolve. The code-bearing trait (§8) is exactly what would widen it.

## 7. User rulings (2026-07-10) — settled, not open

1. **No language-visible render-annotation surface.** The architecture had recommended a
   declarative, type-local annotation the type author writes. The user overruled it: the language
   does not grow such a surface; the built-in collections are recognised compiler-internally (§3),
   and user extensibility is the future `Display`-style trait (§8).
2. **No forcing of a lazy `Seq` tail at display time**, even to a small bound. Confirmed as the
   architecture recommended (§5): non-forcing `+more`, byte-identical to the trace path, no
   REPL-only forcing capability.

The aspirational note in `repl/spec/01-display-format.md` §1.5 reflects these rulings;
the generic ADT display remains normative until the mechanism lands.

## 8. Out of scope: a code-bearing custom-printer trait

A `Display`-like trait whose method renders arbitrary user types is the sanctioned route for user
extensibility and a separate, later design: typecheck must resolve the trait and method, the backend
must bake or call it, and the trace walk would have to invoke a language closure — a capability it
deliberately lacks. It is not gated by, and must not be pulled into, the collection mechanism, which
serves `List`/`Seq` fully without it.

## 9. Exit gate for the implementing sprint

1. `DescriptorKind::Collection` + `CollectionSpec` in the intrinsics ABI with the backend baker and
   trace-walk arms; `TypeDefInfo.render` in `cranelisp-types` with its schema bump and baseline
   cascade.
2. The seed populates the marker on stdlib `List` and `Seq`; no spec-level language surface.
3. **Consistency guard green:** the same `List`/`Seq` value renders byte-identically in the REPL
   echo and inside a `(trace …)` of the same session — the acceptance that proves the mechanism is
   shared, not a REPL fork.
4. An infinite `Seq` renders `(seq … +more)` and terminates.
5. Empty forms `(list)` / `(seq)` (or as `spec` specifies); a user two-constructor ADT still renders
   generic-ADT.
6. §1.5 restated as MUST with the surface forms and `[Tested …]` annotations; FIXME 0050 deleted by
   its target.

## Cross-references

- `crates/cranelisp-intrinsics/src/trace_format.rs` — the `DisplayDescriptor` ABI extended here.
- [Execution tracing](tracing.md) §3.4 — descriptor bake and emit contract.
- [REPL styling](repl-styling-seam.md) — orthogonal; the collection renderer is one more span
  producer when it lands.
- [Bounded contexts](bounded-contexts.md) §3, §4b (invariant 12: intrinsics hosts the formatter) and
  §6 — the contexts the two render paths sit in.
- `repl/spec/01-display-format.md` §1.5; `design/arch/fixmes/0050-promote-list-seq-pretty-printer-aspirational.md`.
