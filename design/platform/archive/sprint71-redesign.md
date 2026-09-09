# Sprint 71 — `cranelisp-platform` Phase A redesign

**Owner**: `/design` (cranelisp-platform narrow deployment).
**Date**: 2026-05-27.
**Scope**: Phase A of Sprint 71 — author the new platform-boundary API surface (CLAdt + field-traversal + marker-type DSL + cranelisp-S-expr schema + grown `HostCallbacks` + `ABI_VERSION` bump) entirely target-stated in design before Phase B `/dev` lands it in source.

**Inputs grounding this doc**: `sprints/SPRINT.md` (Reading-3 + facade-retirement + DSL scope, /arch's PASS WITH REVISIONS verdict R1–R5, arbitrations A1/A4/A5/A7 ruled + A2/A3/A6/A8 deferred-to-me); `design/arch/facades/cranelisp-platform-audit-s69.md` (F1–F9 absorption); `design/arch/facades/platform.md` (337-line facade to retire); `design/arch/bounded-contexts.md` §5; `design/arch/principles/{06,08,14,15,18}.md`; `crates/cranelisp-platform/src/lib.rs` (1139 LOC current source); `crates/cranelisp-platform/public-api.txt` (S67 baseline).

**Companion**: this doc co-exists with `design/platform/platform.md` (the master crate doc — touched lightly with a forward-reference at top); the §"Facade-fold plan" at the end of this doc is the input to Phase C.

---

## Executive summary

This sprint introduces the platform-DLL ADT-marshaling surface as a layer-1 marker-type pattern: a compile-time-zero `CLAdt<T: CLAdtType>` generic over per-type marker structs (one per declared cranelisp ADT, auto-emitted by the macro from a schema literal), backed by a per-DLL parsed `Schema` value resolved at runtime via a per-marker-type `GetSchema` trampoline. Field-access reads (`read_field<F>`, `own_field<F>`) are callback-free — the DLL computes byte offsets locally from its parsed schema and transmutes at the offset. Construction (`CLAdt<T>::construct(...)`) is the only path that touches host state and panics under a single `R1` wired-or-panic gate against `HostCallbacks::alloc_with_tag` until the host-wiring sprint populates it. `HostCallbacks` grows by exactly two named-null-callback fields (`alloc_with_tag`, `validate_schema`); both default to in-crate panic-emitting stubs per A6 (named-null) so DLL-side code is statically callable without an `is_null` ceremony at every site. `ABI_VERSION` bumps from 1 to 2 because the layout-affecting growth of `HostCallbacks` per A4 mandates it. Sum-type field lookup discipline per A8 ruled: **dot-qualified (`"Some.val"`)** for variant-scoped fields — verbose but unambiguous, mirroring the `read_tag` dispatch the DLL author has already performed. Audit findings F1–F9 fold dispositions follow the audit memo's §5 edit plan with two exceptions: F2 is a confirmed source-move (Phase B `/dev`); F5 is explicitly non-renaming per R3.

The DSL grammar is a cranelisp-S-expression literal embedded in the `declare_platform!` macro `schema:` arm, parsed once at DLL init via a small in-crate recursive-descent S-expr lexer/parser (no `cranelisp-frontend` dep — wrong DAG direction). The schema's resolution trampoline picks **option (ii) — `GetSchema` per marker type** (one schema per DLL trivially mirrors one set of markers per DLL; no globals, no init-order hazard); `read_field` is parametric over `T: CLAdtType + GetSchema`.

One new FIXME is named for the host-wiring follow-up sprint: **FIXME 0229**.

---

## 1. Schema format finalisation

### 1.1 BNF

```
schema      := top-form
top-form    := type-decl+                            ; naked sequence of decls
                                                     ; no wrapping `(schema ...)` form — see §1.6
type-decl   := "(" type-name product-or-sum ")"
product-or-sum
            := field-list                            ; product: single bracketed list
             | variant-clause+                       ; sum: one or more variant clauses
field-list  := "(" field-spec* ")"                   ; possibly empty for a marker-only product
field-spec  := "(" field-type field-name ")"
variant-clause
            := variant-name                          ; nullary variant
             | "(" variant-name field-list ")"      ; data variant
field-type  := type-name                             ; either a CL wrapper or another declared type-name
type-name   := uppercase-ident                       ; per cranelisp convention; ASCII; UpperCamel
variant-name:= uppercase-ident
field-name  := lower-ident                           ; ASCII; lower_snake or camelCase tolerated
                                                     ; canonical form is lower_snake

uppercase-ident := [A-Z][A-Za-z0-9_]*
lower-ident     := [a-z][A-Za-z0-9_]*

; lexical
whitespace  := ' ' | '\t' | '\n' | '\r'              ; arbitrary
comment     := ';' .* '\n'                           ; line comment, S-expr convention
```

Worked example (the canonical sprint scope, all four shapes):

```
((Point ((CLInt x) (CLInt y)))
 (Rectangle ((CLInt w) (CLInt h)))
 (Bounds ((Point tl) (Point br)))
 (OptionInt None (Some ((CLInt val))))
 (ListInt Nil (Cons ((CLInt head) (ListInt tail)))))
```

### 1.2 Reserved field-type names (the CL wrapper family — canonical list)

The grammar's `field-type` non-terminal admits two disjoint families: **reserved CL wrappers** (the cranelisp value types crossing the FFI boundary) and **declared ADTs** (any `type-name` defined elsewhere in the same schema). The reserved set this sprint:

| Reserved name | Maps to | Notes |
|---|---|---|
| `CLInt` | `cranelisp_platform::CLInt` | i64 primitive |
| `CLBool` | `cranelisp_platform::CLBool` | i64 0/1 |
| `CLFloat` | `cranelisp_platform::CLFloat` | f64 bitcast |
| `CLString` | `cranelisp_platform::CLString` | base ptr to `[hdr | len | bytes]` |
| `CLIO` | `cranelisp_platform::CLIO<CL>` | IO node tree — but **not yet usable as a field type** (no Decision; deferred) |

`CLIO` is reserved but **not parseable as a schema field type this sprint** — the language doesn't yet permit `IO a` inside an ADT field, and the parser rejects it with `SchemaParseError::ReservedFieldTypeNotYetSupported { name: "CLIO", position }`. Reserving the name now prevents a future spec amendment from colliding with a user-named type.

A DLL author may NOT declare an ADT with one of the reserved names. The parser rejects `(CLInt ...)` as a top-level `type-decl` with `SchemaParseError::ReservedTypeName { name, position }`.

### 1.3 Polymorphic-instantiation naming convention

**Selected: `OptionInt`-style — concatenated UpperCamel, no separator.** Rationale: this matches cranelisp's own monomorphisation-mangling convention at the spec level (`Option<Int>` → `Option$Int` internally; the schema reflects the user-monomorphised form without the `$` separator since the schema is hand-authored DSL, not compiler-generated text). `Option_Int` adds a separator with no disambiguation gain (`type-name` is `[A-Z][A-Za-z0-9_]*` — no underscore disambiguates from a user-named `Option_Int` type either). `Option<Int>` as a string would force the lexer to accept `<` and `>`, opening a parsing path for arbitrary generic-application syntax the schema is explicitly not the place for (the schema mirrors the *monomorphised* heap layout; polymorphic abstraction is the cranelisp typechecker's job, upstream of schema emission).

Future `/abi` emitter (deferred) constructs polymorphic instantiation names from `(type-base, concrete-args)` by concatenating UpperCamel-cased forms: `(Option, [Int])` → `OptionInt`; `(Map, [String, Int])` → `MapStringInt`. Collisions with user-named ADTs are the user's responsibility — the spec/typecheck reject ambiguous monomorphisations upstream.

### 1.4 Recursion shape

Recursion is supported via type-name self-reference within `field-type` — `(ListInt Nil (Cons ((CLInt head) (ListInt tail))))` references `ListInt` inside its own declaration. **Verified.** The parser accepts forward references within a schema (the second-pass field-type-resolution after all top-level decls are parsed handles self-references and forward references uniformly).

Indirect recursion: `(A ((B b))) (B ((A a)))` is also accepted; the parser does not topologically sort declarations.

Mutual recursion bounded by the field's heap layout (each recursive field is a heap pointer; the runtime layout is bounded). The schema parser does NOT verify acyclic types — that's a layout question, not a grammar question, and infinite types `(A ((A inner)))` are legal at the schema level (a DLL author would never write one because no constructor can ever build a value).

### 1.5 Whitespace + comment policy

Standard S-expr conventions:

- Whitespace is `' '`, `'\t'`, `'\n'`, `'\r'`; arbitrary amounts between any tokens.
- Line comments: `;` to end of line. Matches the cranelisp source language. Useful in multi-line schema literals.
- No block comments. No `#|...|#`. The grammar is tiny; line comments suffice.
- No string escapes (no string literals in the grammar — only bare identifiers).

### 1.6 Top-level wrapping — naked list

**Selected: naked sequence of `type-decl`s — no `(schema ...)` wrapper form.** Rationale: the schema is always embedded in the `declare_platform!` macro's `schema:` arm as a single string literal; the macro arm's grammar already provides the "this is a schema" context. A wrapping `(schema ...)` form would add one keyword for zero parse-disambiguation gain (the macro arm is the unambiguous parse context). Compare:

```rust
// Selected: naked top-level
declare_platform! {
    name: "stdio", version: "0.1.0", host: HOST,
    schema: "
        ((Rectangle ((CLInt w) (CLInt h))))
    ",
    functions: [ ... ],
}

// Rejected: wrapping form
schema: "(schema (Rectangle ((CLInt w) (CLInt h))))",
```

Grounding: Principle 6 (complexity budget — wrapping adds zero disambiguation).

### 1.7 Error grammar

`SchemaParseError` variants (the parser type, §2):

```rust
pub struct ParseLoc { pub line: u32, pub col: u32, pub offset: usize }

#[derive(Debug)]
pub enum SchemaParseError {
    UnexpectedEof { expected: &'static str, at: ParseLoc },
    UnexpectedToken { found: String, expected: &'static str, at: ParseLoc },
    UnclosedParen { opened_at: ParseLoc },
    ExtraCloseParen { at: ParseLoc },
    InvalidIdentifier { found: String, at: ParseLoc, reason: &'static str },
    ReservedTypeName { name: String, at: ParseLoc },                 // user-declared `CLInt` etc.
    ReservedFieldTypeNotYetSupported { name: &'static str, at: ParseLoc },  // `CLIO` field
    DuplicateTypeName { name: String, at: ParseLoc, first_at: ParseLoc },
    UnknownFieldType { name: String, at: ParseLoc },                 // field-type names neither a CL wrapper nor a declared type
    EmptyVariantClause { at: ParseLoc },                              // `()` as a variant — disallowed
}
```

All variants carry a `ParseLoc` (line/col/offset within the schema string). `UnknownFieldType` is the most likely DLL-author-encountered error; the message names the unknown name explicitly so the author sees "did I misspell `CLInt`?" immediately. `DuplicateTypeName` carries both occurrences for the same reason.

What does **not** count as malformed:

- Empty schema (`""` or `"  ;; just a comment\n"`) — parses to an empty schema. A platform DLL with zero ADT-marshaling functions has nothing to declare.
- Empty product (`(MarkerOnly ())`) — a tag-only type with no fields. The DLL author would use this for marker types in a tagged enumeration where one variant carries no data; the runtime layout is just a tag, no heap allocation. Valid; emits a marker type with `CLAdtType::TYPE_NAME = "MarkerOnly"` and zero-field schema entries.

---

## 2. Schema parser design

### 2.1 Location in source layout

New file: `crates/cranelisp-platform/src/schema.rs`. Re-exported from `lib.rs` via `pub mod schema;` followed by `pub use schema::{Schema, TypeShape, Variant, Field, FieldType, SchemaParseError, ParseLoc};`.

Rationale for new file (not folded into `lib.rs`): `lib.rs` is at 1139 LOC and grows further with `CLAdt`. A new `schema.rs` of ~300–400 LOC (lexer + parser + types + tests) is a natural module split — same crate, separate compilation unit, easier audit reading.

### 2.2 Types produced

```rust
pub struct Schema {
    types: Vec<TypeShape>,                            // owned, ordered as declared
    by_name: ahash::AHashMap<String, usize>,          // type_name → index into `types`
}

pub struct TypeShape {
    pub name: String,                                 // e.g. "Rectangle"
    pub variants: Vec<Variant>,                       // 1 variant = product; N variants = sum
}

pub struct Variant {
    pub name: String,                                 // for products: same as TypeShape.name;
                                                     // for sums: variant identifier
    pub fields: Vec<Field>,                           // possibly empty (nullary variant)
}

pub struct Field {
    pub name: String,                                 // field identifier
    pub field_type: FieldType,
}

pub enum FieldType {
    CLInt, CLBool, CLFloat, CLString,                 // reserved wrapper set per §1.2
    Adt(String),                                      // declared type-name; resolved after parse
}
```

`Schema::lookup_field_offset(type_name: &str, field_name: &str) -> Option<usize>` is the runtime accessor used by `CLAdt::read_field` to compute the heap byte offset (see §4).

`Schema::lookup_variant_field_offset(type_name: &str, variant_name: &str, field_name: &str) -> Option<usize>` is the sum-type accessor per A8 (§4.4).

### 2.3 Strategy

Handwritten recursive-descent over an inline lexer:

```rust
struct Lexer<'a> { src: &'a str, pos: usize, line: u32, col: u32 }
enum Token<'a> { LParen, RParen, Ident(&'a str), Eof }

struct Parser<'a> { lex: Lexer<'a> }

impl<'a> Parser<'a> {
    fn parse_schema(&mut self) -> Result<Schema, SchemaParseError>;
    fn parse_type_decl(&mut self) -> Result<TypeShape, SchemaParseError>;
    fn parse_field_list(&mut self) -> Result<Vec<Field>, SchemaParseError>;
    fn parse_variant_clause(&mut self) -> Result<Variant, SchemaParseError>;
    // field-type resolution is a second pass after all type-decls are read.
}
```

Two-pass parse:

- **Pass 1**: read all `type-decl`s; record names; reject duplicates; reject reserved-name top-level decls. Field-type names captured as raw strings.
- **Pass 2**: resolve field-type strings against (reserved CL wrappers) ∪ (declared type names). Emit `UnknownFieldType` for unresolved names.

### 2.4 Isolation from `cranelisp-frontend`

`cranelisp-platform` MUST NOT depend on `cranelisp-frontend` — the DAG direction is wrong (frontend is upstream of platform per `bounded-contexts.md`'s implicit ordering; making frontend a dep would invert and platform would need to load frontend to parse its own DLL-init schema). The in-crate parser is ~250 LOC of straightforward recursive-descent — no shared infrastructure with frontend's sexp.rs is structurally accessible, and even if it were, the schema grammar is a strict subset of cranelisp's general S-expr (no nested string literals, no escapes, no operator symbols, no dotted symbols). The cost of duplication is bounded; the gain in DAG cleanliness is substantial. Principle 3 grounds this.

The future host-wiring sprint (FIXME 0229) may route platform sig parsing through `cranelisp-frontend` — that's a different parser (cranelisp source code, not schema text), accessed by `int` (which can depend on frontend). Schema parsing stays in-crate.

---

## 3. Marker-type pattern formal definition

### 3.1 Trait + default

```rust
/// Marker trait for typed CLAdt parameters.
///
/// Implemented by the `declare_platform!` macro for each ADT declared in
/// the schema. DLL authors do not implement this directly.
pub trait CLAdtType: 'static {
    /// The cranelisp type name as it appears in the schema and at runtime.
    /// Schema lookups use this string to find the type's field layout.
    const TYPE_NAME: &'static str;
}

/// Default marker for untyped CLAdt — used when the DLL author works
/// generically over heap-ADT values without committing to a specific
/// type at compile time.
pub struct AnyAdt;
impl CLAdtType for AnyAdt {
    const TYPE_NAME: &'static str = "";   // sentinel — see §4.6
}
```

### 3.2 The `CLAdt<T>` generic

```rust
#[repr(transparent)]
pub struct CLAdt<T: CLAdtType = AnyAdt>(i64, std::marker::PhantomData<T>);
```

**`#[repr(transparent)]` preservation with `PhantomData<T>`**: Rust's transparent-repr rule permits at most one non-zero-sized field; `PhantomData<T>` is zero-sized for any `T`. The wrapper's ABI is exactly `i64` — JIT-emitted code and the host see a single i64 payload at every CLAdt call site. The marker `T` is a host-side typing convenience, invisible to the JIT calling convention. This mirrors `CLIO<CL: CLType>` (`lib.rs:218`+) which uses the same `i64 + PhantomData<CL>` shape and is already cleared by Principle 14.

The `T::TYPE_NAME` lookup is performed inside Rust code at runtime (DLL-side); the type name itself never crosses the FFI boundary — it lives in DLL-local static `&'static str` storage.

### 3.3 Type-witness mismatch behaviour (per A1 — PANIC)

Mismatch occurs when a `CLAdt<Rectangle>` value's runtime heap-layout type-tag refers to a non-Rectangle type — i.e., the DLL author cast through `CLAdt::<Rectangle>::from(some_i64)` (or accepted it as an `extern "C" fn` parameter) when the heap allocation at that pointer was actually shaped as something else. **By the ABI invariant this cannot happen in correctly-built DLLs**: the caller (cranelisp typecheck, downstream) has already checked that the value crossing the boundary has the declared type.

Per A1: panic, not Result. Message format:

```
CLAdt type-witness mismatch:
  expected: {T::TYPE_NAME} (from CLAdt<{T}> at {site})
  found:    type-tag {tag_u32} at heap base {hex_ptr}
  cause:    DLL built against stale ABI_VERSION, or DLL author wrote wrong code
  see:      ABI_VERSION at lib.rs (current = {ABI_VERSION}); was the DLL rebuilt?
```

Where the witness check fires: **only inside type-coercing API points** (e.g., `CLAdt::<T>::from_any(any: CLAdt<AnyAdt>) -> Self`). The common-case path — DLL author writes `extern "C" fn area(r: CLAdt<Rectangle>) -> CLInt` — doesn't witness-check at every read; it witnesses *once at API boundary if at all*. **Decision (Phase A)**: the witness check is performed lazily on the **first field-access call** per CLAdt value, not on every call. Implementation: a thread-local `last_checked: (ptr, tag)` cache wouldn't be sound across DLL re-entry; instead, the witness check is performed inline at the head of each `read_field` / `own_field` / `read_tag` body. The check cost is one byte-load + one integer compare per access; the schema lookup that follows dominates, so the marginal cost is sub-percent.

(Rationale for in-line per-call check rather than once-per-value: a CLAdt may be persisted in host state across DLL calls; the "first call" boundary isn't well-defined; the simplest robust shape is to check at every method entry. Principle 6 is satisfied — the cost is a load + compare per field access; the schema lookup is the dominant cost anyway.)

Construction-side mismatch is impossible by construction: `CLAdt::<T>::construct(...)` writes the tag from `T::TYPE_NAME` lookup; the produced CLAdt is correctly tagged.

---

## 4. CLAdt API surface — final shape

### 4.1 Method set (target signatures)

```rust
impl<T: CLAdtType + GetSchema> CLAdt<T> {
    /// Read the runtime tag at a fixed offset (offset 0 of payload).
    /// No schema lookup; no callback.
    pub fn read_tag(&self) -> u32;

    /// Read a primitive field by name. Schema lookup computes the byte offset
    /// from T::TYPE_NAME + field_name; transmute the i64 at that offset to F.
    ///
    /// Panics if the field name is not in T's schema, or if the runtime
    /// type-witness mismatches T (per A1).
    pub fn read_field<F: CLType>(&self, field_name: &str) -> F;

    /// Read a heap field by name with inc-on-read. Returns a CLOwned<F>
    /// (which will dec on drop, mirroring Decision 24).
    ///
    /// F must be `CLHeap` — CLString, or another `CLAdt<U: CLAdtType>`.
    /// Panics on schema miss or type-witness mismatch.
    pub fn own_field<F: CLHeap>(&self, field_name: &str) -> CLOwned<F>;
}

impl<T: CLAdtType + GetSchema> CLAdt<T> {
    /// Construct a new CLAdt value from a tag + field array.
    ///
    /// `tag` MUST be the discriminant of one of T's variants (for sums) or
    /// 0 (for products). `fields` is a flat array of raw i64 values matching
    /// the field declaration order for the chosen variant; their count must
    /// equal the variant's field count.
    ///
    /// This path calls `HostCallbacks::alloc_with_tag`; panics under the R1
    /// wired-or-panic gate if the callback is not yet wired by the host.
    pub fn construct(tag: u32, fields: &[i64]) -> CLOwned<CLAdt<T>>;
}
```

Notes:

- `read_field`'s `F: CLType` constraint covers `CLInt`, `CLBool`, `CLFloat` (the primitive wrappers); `CLString` and `CLAdt<U>` go through `own_field` because they're heap.
- The return type of `construct` is `CLOwned<CLAdt<T>>` — Decision 24's consuming-convention shape: the just-allocated heap value has RC=1 (set by `alloc_with_tag`); wrapping in `CLOwned` adds no inc, drops dec to 0 + free. (Same as `CLString::from(&str)` which returns the bare `CLString` and relies on the caller to `into_owned_consuming` if they want a `CLOwned`.) Construction returns `CLOwned` directly because the typical use is "build it, hand it back as the function return value" — the caller's return path holds the `CLOwned`, drops it after the host has copied the i64 into the IO trampoline. We could mirror `CLString::from(&str)` and return bare `CLAdt<T>` — but the asymmetry is unjustified; the construction allocates, and ownership transfer wants RAII at the call site. **Selected: `CLOwned<CLAdt<T>>`.**

### 4.2 Type-witness manifestation (per A1)

Per §3.3, every method on `CLAdt<T>` performs a type-tag-vs-T witness check inline at method entry. Cost: one i64 load + one u32 compare. The check reads the tag at payload+0; matches against T's schema's tag-for-T (always 0 for products; for sums where T is the whole sum type, the check passes for any of T's variants — `read_tag` returns the actual variant id; for sums where the DLL author has used a narrower marker like `OptionIntSome`, the check requires the runtime tag to match the Some variant). **The sprint's marker emission is at the sum-type level (one marker per `type-decl`, not per variant)** — so for `OptionInt` the witness passes for None or Some; the variant discrimination is up to the DLL author via `read_tag`. (Adding per-variant markers is layer-2 work, deferred.)

### 4.3 Construction shape (per A2 — RULED HERE)

**Ruled: direct constructor `CLAdt::<T>::construct(tag, fields)` returning `CLOwned<CLAdt<T>>`.**

Considered alternatives:

- **Builder pattern** (`CLAdtBuilder::<T>::new().field("x", v).field("y", w).build()`). Rejected: the field names are already in T's schema; the builder's `field(name, value)` either accepts wrong names (runtime panic) or duplicates the schema's name set (compile-time check via macro emission). Either way, the builder adds verbosity per call without an invariant gain. The direct constructor's field order is unambiguous (variant's declared field order); a builder's named-field interface would help only in the presence of optional fields, which the schema doesn't support.
- **Variant-named constructor** (`Rectangle::new(w, h)` — emitted by the macro per declared product type). Rejected: this is layer-2 (typed-newtype-emission) per A7's deferral. Layer 1 stays with the generic `CLAdt::<T>::construct(...)` form; layer 2 may add ergonomic newtype constructors on top if measurement shows the call sites are verbose enough to warrant the macro emission.

Per A2 constraints (i)–(iii):

- **(i) Construction MUST NOT require the host to be wired**. Phase B Land: `construct(...)` calls `HostCallbacks::alloc_with_tag`; under the R1 gate (§9 below), the host-side stub-null callback (per A6, §5.5) panics with a clear FIXME-pointing-forward message. Test surface (§10) installs synthetic non-panicking callbacks via per-test `HostContext::init`.
- **(ii) Must compose with `CLOwned<CLAdt<T>>`**. The return type IS `CLOwned<CLAdt<T>>`. RC discipline: `alloc_with_tag` writes RC=1; `CLOwned::new` would re-inc to 2 (wrong); instead the constructor returns via `CLOwned { inner: CLAdt(alloc_base_ptr, PhantomData) }` (no inc; the i64 stored in `CLAdt` is the alloc base, matching `CLString`'s convention — see §5.1), mirroring `CLHeap::into_owned_consuming`. Decision 24 grounds the no-inc-on-construction shape.
- **(iii) Must compose with the DSL spec**. `Rectangle::new(w, h)` (layer 2) wraps `CLAdt::<Rectangle>::construct(0, &[w.to_raw(), h.to_raw()])`. The DSL emission cleanly produces a `construct` call.

### 4.4 Sum-type field lookup discipline (per A8 — RULED HERE)

**Ruled: dot-qualified — `"Some.val"`.**

For `(OptionInt None (Some ((CLInt val))))`, the DLL author writes:

```rust
match opt.read_tag() {
    0 => /* None — no field access */,
    1 => {
        let val: CLInt = opt.read_field::<CLInt>("Some.val");
        // use val ...
    }
    _ => unreachable!(),
}
```

For a product type `Rectangle`, the qualifier is unnecessary because there's exactly one (anonymous) variant. The grammar admits both forms uniformly:

- Product field access: `read_field::<CLInt>("w")` — schema searches the single variant (also expressible as `"Rectangle.w"` for symmetry; both are accepted).
- Sum field access: `read_field::<CLInt>("Some.val")` — schema looks up variant `Some`, then field `val`. Unqualified `"val"` is rejected with `SchemaLookupError::AmbiguousField { name: "val", in_type: "OptionInt", variants: ["Some"] }` (even when only one variant has the field — the rule is uniform, not contextual).

Rationale (constraints (i)–(iii) per A8):

- **(i) Uniformity**: dot-qualification works for both single-variant (product) and multi-variant (sum) types; the unqualified form works for products only. Selecting dot-qualified for sums + permitting unqualified for products would split the rule contextually. Selecting dot-qualified universally is uniform — the cost on products is a redundant qualifier the DLL author can omit (the parser accepts both `"w"` and `"Rectangle.w"` for products). The qualified form is canonical; the unqualified is shorthand for products only.
- **(ii) Worked examples**: `Bounds.tl.x` chain doesn't compose with unqualified lookup; the chained version is `b.own_field::<CLAdt<Point>>("Bounds.tl").read_field::<CLInt>("Point.x")` (or omitting the product qualifier on `tl`: `b.own_field::<CLAdt<Point>>("tl")`).
- **(iii) Layer-2 composition**: a future `match-on-tag` macro emits `CLAdt<Rectangle>::area()` inherent methods that compute offsets at macro-expand time — the macro consumes the schema and knows which variant each field belongs to. Layer 2 stays cleanly buildable on top of dot-qualified lookup.

The unqualified-walk-all-variants option (A8 option a) was rejected because the "unique-match wins; ambiguous panics" rule introduces a hidden coupling: adding a new variant with the same field name to a previously-unique-named sum type silently breaks DLL author code at the call site. Dot-qualification keeps the source code stable across schema evolution.

### 4.5 Schema-miss behaviour

Schema misses (field name not in the type's schema; variant name not in the sum) are programmer errors at the DLL-author level — the schema literal is authored by the DLL author in the same crate as the function bodies that read it; a typo or stale-field-rename is the only way to hit a miss. Disposition: **panic** with a precise message:

```
CLAdt::read_field schema lookup miss:
  type:        {T::TYPE_NAME}
  asked for:   {field_name}
  schema has:  [{available_field_names_for_type}]
  did you mean: {top_3_levenshtein_matches_or_none}
```

The "did you mean" hint adds ~50 LOC of fuzzy-match code; worth it for DLL author ergonomics. Phase B may defer the fuzzy-match to a follow-on if Phase A test scope is large.

### 4.6 Untyped escape hatch — `CLAdt<AnyAdt>`

`AnyAdt::TYPE_NAME = ""` is the sentinel for "no static type binding." `CLAdt<AnyAdt>` represents a heap-ADT value whose specific type is determined at runtime (e.g., a generic walker that traverses a polymorphic shape).

**Does it support field access?** **No** — `read_field::<F>("name")` on `CLAdt<AnyAdt>` would have no schema to consult. The compile-time `T::TYPE_NAME` is `""` and the runtime tag alone is insufficient (the tag is variant-id-within-type; the type binding is what `T::TYPE_NAME` supplies).

API exposed on `CLAdt<AnyAdt>`:

```rust
impl CLAdt<AnyAdt> {
    /// Read the runtime tag. Same as the generic implementation.
    pub fn read_tag(&self) -> u32;

    /// Coerce to a typed CLAdt<T>. Performs the type-witness check (A1)
    /// using T's schema; panics on mismatch.
    pub fn into_typed<T: CLAdtType + GetSchema>(self) -> CLAdt<T>;
}
```

Field access requires `into_typed::<SomeType>()` first; the typed CLAdt then has full API. This is the **safe** escape-hatch shape: the type binding is explicit at the witness boundary; field access is statically restricted to typed CLAdts.

Rejected alternative: a `read_field_named(type_name: &str, field_name: &str)` method on `CLAdt<AnyAdt>`. Cost: doubles the API surface; opens a path where the DLL author hard-codes type names and a future renaming of the cranelisp ADT silently breaks the DLL at runtime instead of at compile time. The `into_typed` discipline binds the type name to a marker type, which the macro emits from the schema literal — schema-driven renaming flows correctly.

---

## 5. HostCallbacks growth — final signatures

### 5.1 Two new fields (per A3)

```rust
#[repr(C)]
pub struct HostCallbacks {
    pub alloc: extern "C" fn(size: i64) -> i64,       // existing — unchanged

    // -- new fields, Sprint 71 (ABI_VERSION 2) --

    /// Allocate a tagged heap ADT and write the variant tag + fields.
    ///
    /// Called by `CLAdt::<T>::construct(...)`. The host:
    /// 1. Allocates `total_size` bytes via the runtime allocator (`alloc`).
    /// 2. Writes the 16-byte heap header (`[total_size: i64][rc: i64]`).
    /// 3. Writes the 4-byte tag at payload+0 (payload = alloc_base + 16).
    /// 4. Writes `field_count` i64 values from `fields_ptr` at sequential
    ///    8-byte offsets starting payload+8 (8-byte align after the u32 tag
    ///    with 4 bytes pad).
    /// 5. Returns the **alloc base pointer** as i64 (matches the `CLString`
    ///    convention — `CLString` stores `payload - HEAP_HEADER_SIZE`;
    ///    `CLAdt<T>::from_raw` likewise expects alloc base; `read_tag` /
    ///    `read_field` add `HEAP_HEADER_SIZE` to reach the payload).
    ///
    /// **Wired-or-panic**: until populated by the host-wiring sprint
    /// (FIXME 0229), this field points at `null_alloc_with_tag` (in this
    /// crate, §5.5), which panics with the R1-gate message. The R1 gate
    /// is removed in the host-wiring sprint by replacing the null-callback
    /// pointer with the wired host implementation.
    pub alloc_with_tag: extern "C" fn(
        tag: u32,
        field_count: u32,
        fields_ptr: *const i64,
    ) -> i64,

    /// Validate the DLL's shipped schema against cranelisp's actual deftype
    /// data for the named types. Called once at DLL load.
    ///
    /// `schema_ptr`/`schema_len` deliver the schema literal exactly as the
    /// DLL's `declare_platform!` invocation embedded it. Host parses and
    /// cross-references against the active typecheck symbol table.
    ///
    /// Returns:
    /// - 0 — validation passed
    /// - non-zero — validation failed; an error message has been written
    ///   to `err_msg_ptr` (host-owned buffer of capacity `err_msg_capacity`);
    ///   `*err_msg_len_out` is set to the message length
    ///
    /// **Wired-or-panic**: this sprint, the field points at
    /// `null_validate_schema` (in this crate, §5.5), which returns 0
    /// unconditionally (no validation; the load path completes). When the
    /// host-wiring sprint populates this with a real validator, schema
    /// mismatches surface as DLL-load failures.
    pub validate_schema: extern "C" fn(
        schema_ptr: *const u8,
        schema_len: usize,
        err_msg_ptr: *mut u8,
        err_msg_capacity: usize,
        err_msg_len_out: *mut usize,
    ) -> i32,
}
```

Signature rationale:

- `alloc_with_tag` takes the tag + field array — the host knows the heap-layout convention (tag at payload+0; fields at payload+8+); the DLL doesn't need to compute total_size. Out-of-band: `fields_ptr` is non-owning (the values are i64s; if a field is a heap reference, the DLL has already incremented RC before passing). The host doesn't re-inc — it just writes the i64s into the new allocation's field slots.
- `validate_schema` returns `i32` for C-ABI clarity (avoids the `bool`/`u8` ambiguity); 0 == ok, non-zero == failed. The error-message out-param avoids a `*mut *const u8` return type that the DLL would have to free; instead, the host writes into a DLL-provided buffer (allocated stack-side in the DLL at call site). Capacity is typically 1KB for diagnostic messages.

### 5.2 Null-pointer policy (per A6 — RULED HERE)

**Ruled: named-null-callback functions (A6 option b).**

In `cranelisp-platform`:

```rust
/// Panic-emitting placeholder for `HostCallbacks::alloc_with_tag`.
///
/// `HostCallbacks` initialized by the host this sprint sets this as the
/// `alloc_with_tag` field value (until the host-wiring sprint populates
/// the real callback). Calling this panics under the R1 gate; the message
/// names FIXME 0229 explicitly.
///
/// **Will be removed** in the host-wiring sprint: the host's
/// `HostCallbacks` initializer site (in `int`) switches from
/// `cranelisp_platform::null_alloc_with_tag` to the wired callback.
pub extern "C" fn null_alloc_with_tag(_tag: u32, _field_count: u32, _fields_ptr: *const i64) -> i64 {
    panic!(
        "CLAdt construction requires HostCallbacks::alloc_with_tag, \
         which is not yet wired by the host. See FIXME 0229 \
         (host-side ADT marshaling — host-wiring sprint scope).\n\
         If you are running tests inside cranelisp-platform, install a \
         synthetic callback via HostContext::init in test setup."
    )
}

/// No-op placeholder for `HostCallbacks::validate_schema`. Returns 0
/// (passes) unconditionally — schemas are not validated against the
/// host's actual deftype data until the host-wiring sprint populates
/// this. Until then, schema typos surface at field-access call sites
/// (via `SchemaLookupError`) rather than at DLL load time.
pub extern "C" fn null_validate_schema(
    _schema_ptr: *const u8,
    _schema_len: usize,
    _err_msg_ptr: *mut u8,
    _err_msg_capacity: usize,
    _err_msg_len_out: *mut usize,
) -> i32 {
    0  // pass — no validation
}
```

Rationale (option b over option a): the named-null-callback approach makes the panic happen *at the callback body* (one specific code site) rather than at *every CLAdt method call* (one `is_null` check per dispatch point). The R1 gate's "removal" in the host-wiring sprint is one line per callback in `int`'s `HostCallbacks` initializer — replace `cranelisp_platform::null_alloc_with_tag` with the wired-host function. The clean-removal shape is the structural enforcement Principle 18 prefers (the gate IS a named function pointer, addressable and replaceable).

Option (a) — runtime `is_null()` check — was rejected because (i) it introduces a per-call branch in the read paths' performance envelope (mitigated by branch prediction, but still measurable), (ii) the dead-code path (the null-panic body) is colocated with the live-code path (the call), making the "interim" surface less visible to future readers, and (iii) the R1 removal becomes a structural source change in many sites rather than one line per callback.

Per Principle 18: option (b)'s "the field is always non-null; null-state-is-not-representable" is the structural form; option (a)'s runtime check is behavioral. /arch's A6 ruling noted "slightly preferred but not binding" — I'm taking it.

---

## 6. `ABI_VERSION` policy

### 6.1 Bump rules (per A4)

Documented as inline rustdoc on the `ABI_VERSION` constant in `lib.rs`:

```rust
/// Platform ABI version — bump on any layout-affecting change to the
/// platform DLL boundary.
///
/// **Bump rules** (per Decision A4 / Sprint 71):
///
/// (i)  Any field added/removed/reordered in `HostCallbacks`,
///      `PlatformFn`, `PlatformManifest`: BUMP.
/// (ii) Any change to `HEAP_HEADER_SIZE`, `STRING_HEADER_BYTES`,
///      `IO_TAG_*`, `IO_EFFECT_RESOURCE_OFFSET`: BUMP.
/// (iii) Any new `CL_TYPE_TAG_*` const value: BUMP (DLLs built against
///      the old ABI don't know to populate the new tag).
/// (iv) Adding a new pub `CL<T>` wrapper variant — alone — does NOT
///      bump (Principle 14 `#[repr(transparent)]` exemption).
/// (v)  Adding a method on `CLAdt` (no new `HostCallbacks` field, no new
///      const) does NOT bump.
///
/// Every bump rides with a `public-api.txt` regeneration and a narrative
/// update naming the changed item (S67 close baseline-diff discipline).
///
/// **History**: v1 (Sprint <pre-71>) — initial ABI; v2 (Sprint 71) —
/// `HostCallbacks` grows `alloc_with_tag` + `validate_schema` for the
/// ADT-marshaling surface.
pub const ABI_VERSION: u32 = 2;
```

### 6.2 DLL-side read

The DLL reads `ABI_VERSION` as a `const u32` at compile time — the macro embeds `cranelisp_platform::ABI_VERSION` into the emitted `PlatformManifest.abi_version` field. The DLL author does NOT see a static; the macro takes the const at the DLL-side compilation, baking the value into the manifest.

Mismatch behaviour at DLL load (host side): `int::load_platform_dll` reads `manifest.abi_version` and compares against `cranelisp_platform::ABI_VERSION`. If they differ, `PlatformError::AbiVersionMismatch { dll, expected, found, location }` is constructed and surfaced. This path is unchanged from S67 — the bump rule simply ensures the check fires for the right scenarios.

The `validate_schema` callback (when wired post-host-wiring-sprint) adds a second compatibility check at load time: even if the ABI version matches, the schema's structural shape must match the host's actual deftype data. This is finer-grained than version (one DLL might ship schema v3.4 against host v3.5 of "Point"; ABI version is unchanged because no layout-affecting struct/const change).

### 6.3 Bump 1 → 2 this sprint

Confirmed. `HostCallbacks` grows by two fields; rule (i) fires; ABI_VERSION goes from 1 to 2. The public-api.txt baseline regeneration shows: two new `pub` fields on `HostCallbacks`; the const value flips `pub const cranelisp_platform::ABI_VERSION: u32 = 1` → `... = 2`; two new functions (`null_alloc_with_tag`, `null_validate_schema`).

---

## 7. `declare_platform!` macro arm grammar — final shape

### 7.1 The new arm

```rust
declare_platform! {
    name: "stdio",
    version: "0.1.0",
    host: HOST,
    schema: r#"
        ((Rectangle ((CLInt w) (CLInt h)))
         (OptionInt None (Some ((CLInt val)))))
    "#,
    functions: [
        rectangle_area {
            cl_name: "rectangle-area",
            sig: "(Fn [Rectangle] Int)",
            doc: "Compute the area of a rectangle",
            params: [r],
            scheduling: SchedulingClass::Commutative,
        },
        // ...
    ],
}
```

The new `schema:` key sits between `host:` and `functions:` (the natural reading order: identity, ABI partner, types, fns). It is **optional** — DLLs that don't use ADT marshaling (e.g., current `stdio`, `test-capture`) omit the key; the macro emits an empty `Schema`. Backwards compatibility: existing DLLs that don't add `schema:` continue to compile against the new `cranelisp-platform`; their absent schema means they declare no marker types and never call any `CLAdt::<T>` method.

### 7.2 What the macro emits per schema entry

For each `(TypeName ...)` declaration in the schema literal:

1. **A marker type struct**:
   ```rust
   pub struct Rectangle;
   ```
   Zero-sized; no fields; public visibility (DLL author needs to name it in `CLAdt<Rectangle>` signatures).

2. **A `CLAdtType` impl**:
   ```rust
   impl ::cranelisp_platform::CLAdtType for Rectangle {
       const TYPE_NAME: &'static str = "Rectangle";
   }
   ```

3. **A `GetSchema` impl** (the trampoline — see §7.4):
   ```rust
   impl ::cranelisp_platform::GetSchema for Rectangle {
       fn schema() -> &'static ::cranelisp_platform::Schema { &*DLL_SCHEMA }
   }
   ```
   Where `DLL_SCHEMA` is the static-initialized `Schema` value (§7.3).

4. **(Sum types only) An optional `#[repr(u32)]` tag enum**:
   ```rust
   #[repr(u32)]
   pub enum OptionIntTag {
       None = 0,
       Some = 1,
   }
   ```
   /design ruling: **emit for sum types, skip for products.** Rationale: for products there's only one variant; an enum with a single `Rectangle = 0` adds clutter without disambiguation. For sums, the enum lets the DLL author write `match opt.read_tag() { x if x == OptionIntTag::None as u32 => ... }` more cleanly than against raw `0`/`1` literals. Layer-2 ergonomic helpers (deferred) could add a `tag_enum(&self) -> OptionIntTag` method on `CLAdt<OptionInt>` via the same emission path.

### 7.3 The static `Schema`

The macro emits at the call site:

```rust
static DLL_SCHEMA: ::std::sync::LazyLock<::cranelisp_platform::Schema> =
    ::std::sync::LazyLock::new(|| {
        ::cranelisp_platform::Schema::parse(include_str!(...) /* or the literal */)
            .expect("schema literal failed to parse — this is a build-time bug; \
                     fix the schema in declare_platform! and rebuild")
    });
```

`LazyLock` resolves to the parsed schema on first access; threadsafe; one-time cost. The expect message names the failure path explicitly — DLL authors get a clear panic-at-init if they typo the schema literal.

The schema is **DLL-local**: each loaded platform DLL has its own `DLL_SCHEMA` static (separate compilation unit per DLL crate; the macro emits a fresh static per invocation). This means a `CLAdt<Rectangle>` from DLL A and a `CLAdt<Rectangle>` (same name, same shape, different DLL) from DLL B are distinct types at the Rust level (different marker types), and each consults its own schema. Cross-DLL `CLAdt` passing isn't possible at the FFI boundary — the value crosses as bare `i64`; the marker type is host-side only.

### 7.4 Trampoline mechanism — `GetSchema` per marker type (option ii)

**Selected: option (ii) — `GetSchema` trait, per marker type.**

```rust
pub trait GetSchema {
    fn schema() -> &'static Schema;
}
```

The macro emits one `GetSchema` impl per marker type in the schema (every marker type, products + sums uniformly). All impls point at the same `DLL_SCHEMA` static. `CLAdt::read_field` is generic over `T: CLAdtType + GetSchema` and calls `T::schema()` to look up offsets.

Rationale for (ii) over (i) (global static + register-on-init hook):

- **No init-order hazard.** Option (i) requires the macro's emitted manifest extern to call a registration function — which would have to write to a global before any DLL fn runs. The macro already calls `HOST.init(callbacks)` at manifest time; another global write would compound the init-order surface. Option (ii) is pure-type-level: the `T::schema()` call resolves to the same DLL_SCHEMA static via Rust's monomorphisation, no init protocol.
- **One schema per DLL trivially mirrors one set of markers per DLL.** The DLL author can't accidentally use a marker type from DLL A in DLL B's code — the marker types are crate-private to their declaring DLL (the macro emits `pub struct Rectangle` only inside the DLL's lib.rs scope; nothing exports markers across DLLs).
- **No `GetSchema` global registry inside `cranelisp-platform`** — keeping the crate state-free per BC §5 ("owns no runtime state"). Option (i)'s register-on-init would require a `static SCHEMA_REGISTRY: OnceLock<HashMap<&'static str, &'static Schema>>` in `cranelisp-platform`; option (ii) keeps that out.
- **Generic dispatch cost is zero at runtime.** `T::schema()` monomorphises to a direct call to `<Rectangle as GetSchema>::schema()` which inlines to `&*DLL_SCHEMA`. No dynamic dispatch, no map lookup keyed by type name.

`CLAdt<AnyAdt>` does NOT implement `GetSchema` — `AnyAdt` is the untyped marker (§4.6), and method calls on `CLAdt<AnyAdt>` are restricted to `read_tag` + `into_typed::<T>()`. The trait bound `T: CLAdtType + GetSchema` on field-access methods excludes `AnyAdt` structurally (compile-time error rather than runtime panic).

### 7.5 F6 absorption — the rewritten macro-arm narrative

For Phase C fold into `lib.rs:716–740`'s rustdoc-above-example block. Draft text (suitable for direct insertion above the existing `# Example` block):

> ## Macro arm structure
>
> `declare_platform!` has six top-level keys, applied positionally:
>
> | Key | Required | Shape | Purpose |
> |---|---|---|---|
> | `name:` | yes | `&'static str` literal | Platform name; surfaces in `PlatformManifest.name` and at REPL `/imports` |
> | `version:` | yes | `&'static str` literal | Platform version; surfaces in `PlatformManifest.version` |
> | `host:` | yes | identifier of a `static HOST: HostContext` | Where the macro calls `init(callbacks)` |
> | `schema:` | optional | `&'static str` literal (cranelisp S-expr) | ADT shape declarations; absent ⇒ no ADT marshaling |
> | `functions:` | yes | `[ fn { ... }, ... ]` array | Per-fn descriptors (see below) |
>
> ### Per-function block shape
>
> Each entry in `functions:` is `fn_ident { ... }` where `fn_ident` is the Rust `extern "C"` function pointer in scope, and the brace block declares:
>
> | Sub-key | Shape | Purpose |
> |---|---|---|
> | `cl_name:` | `&'static str` literal | The kebab-case user-visible name (e.g. `"read-line"`) — what cranelisp source code calls |
> | `sig:` | `&'static str` literal | The type signature as S-expression text (e.g. `"(Fn [String] (IO Int))"`); parsed by `int` at load time |
> | `doc:` | `&'static str` literal | Docstring; surfaces in REPL `/sig` and `/doc` |
> | `params:` | `[ident, ...]` | Parameter names; surfaces in REPL `/sig`/`/doc`; matches the function pointer's parameter count |
> | `scheduling:` | `SchedulingClass` expression | Per Decision 0026: `Sequential` (default for IO-ordered fns), `Commutative` (reorderable), `ResourceSerial` (token-serialised); MUST be declared per-fn (no default) |
>
> ### Macro emission — internal phases
>
> Macro expansion proceeds in three phases (visible in the macro body):
>
> 1. **Phase 1 — capture per-fn data**: per-fn block iterates once to capture the function pointer (`fn_ident as *const u8`), build the parallel `param_names` arrays (each `&'static [u8]`), and lift the `SchedulingClass` expression to its `u32` discriminant. Each `let $fn_ident = (...)` shadows the original function identifier with a tuple of captured data; subsequent phases use the tuple form.
> 2. **Phase 2 — derive jit_names**: for each fn, compute `derive_jit_name(cl_name)` (kebab → `cranelisp_<snake>`) and `Box::leak` the bytes for `'static` lifetime. Result joined with phase-1 data into a tuple.
> 3. **Phase 3 — build `&'static [PlatformFn]`**: emit the `PlatformFn` array literal, length-prefixed strings keyed against `cl_name.as_ptr()`/`.len()` and the leaked jit_name bytes; `Box::leak` for `'static`. The C-ABI struct's `scheduling_class: u32` is read from phase 1.
>
> If `schema:` is present, phases 1–3 are preceded by **phase 0 — schema emission**: the macro parses the schema literal at expand time only enough to enumerate the type names (the field-list parse is deferred to runtime in `LazyLock::new`), emits one marker-type struct per declared type, the `CLAdtType` impl, the `GetSchema` impl pointing at the `DLL_SCHEMA` static, and (for sum types) a `#[repr(u32)]` tag enum.
>
> The macro DOES NOT validate the schema against `HostCallbacks::validate_schema` at expansion time — validation is runtime (DLL load time) via the host callback. The macro's expansion is purely syntactic; the schema literal's validity is a parse problem (caught at first `Schema::parse` call inside the `LazyLock`).

---

## 8. Audit findings F1–F9 — fold disposition mapping

Per the S69 audit memo (§5 edit plan + §6 verdict). All findings resolve as facade-moves; the destination is now source rustdoc + BC §5 because the facade is retiring.

| F# | Topic | Disposition | Narrative landing site |
|---|---|---|---|
| **F1** | `CLOwned::into_inner` speculative facade method | Remove (do not introduce) | per-item `///` on `CLOwned<T>` in `lib.rs`: rustdoc names only `new`/`Deref`/`Drop`; no `into_inner`. The marker-type pattern doesn't need it (confirmed). |
| **F2** | `impl Default for HostContext` unannounced | **Source-move — DELETE the impl** | Source change in Phase B (zero callers per S69 P2 walkthrough, confirmed). Per-item `///` on `HostContext` after deletion lists only `const fn new()` + `unsafe fn init(...)`. No narrative needed elsewhere — the deleted impl simply ceases to appear in public-api.txt. |
| **F3** | `unsafe impl Send/Sync for PlatformFn` unannounced | Annotate in source rustdoc | per-item `///` on `PlatformFn`: the existing inline `// Safety:` comment (lib.rs:94–98) expands to a full rustdoc paragraph covering Principle 18 grounding + BC §5 invariant 6 (no DLL unloading mid-session) + the cross-thread dispatch use case (Decision 0026 + spec §10.12 Par). |
| **F4** | Send/Sync projections on `HostContext` + `OwnedPlatformFnDescriptor` + `PlatformManifest` | Annotate in source rustdoc | (a) `HostContext` rustdoc adds: "Send + Sync via auto-trait projection from `AtomicPtr<HostCallbacks>`; load-bearing for cross-thread platform-fn dispatch per BC §5 invariant 5." (b) `OwnedPlatformFnDescriptor` rustdoc adds: "!Send + !Sync via `ptr: *const u8` auto-projection; correct for single-threaded session ownership per BC §6.1." (c) `PlatformManifest` rustdoc adds: "!Send + !Sync — intentional asymmetry with `PlatformFn`'s explicit `unsafe impl Send/Sync`; manifest is read once at load and not retained, per-descriptor PlatformFn values cross threads via GOT registration." |
| **F5** | `CLHeap` method names + receiver | **No-rename per R3.** Source uses `inc_rc`/`dec_rc` with `&self` receiver. Rustdoc records this as authoritative. | per-item `///` on `CLHeap` trait declaration: methods documented as `fn inc_rc(&self)` + `fn dec_rc(&self)` with the inline note explaining the asymmetric spelling matches `cranelisp-intrinsics`' historical names. No rename. |
| **F6** | `declare_platform!` macro arm shape | Rewritten narrative folded into the macro's `///` rustdoc | See §7.5 draft text. Lands above the existing example block at `lib.rs:716–740`. The existing example block is correct per S67 W1 PFR + Phase A's `schema:` arm addition; the rewritten narrative explains arm semantics for DLL-author reading. |
| **F7** | `CLOwned` `#[non_exhaustive]` speculative | Source unchanged (no annotation); rustdoc records the disposition | per-item `///` on `CLOwned<T>`: "Not annotated with `#[non_exhaustive]` — single-field RAII over `T: CLHeap` (transparent inner); private `inner` field prevents external direct construction; `#[non_exhaustive]` would add no semantic protection." |
| **F8** | `CLHeap: CLType + Copy` super-bound consistent | No action | Trait declaration documents the super-bound naturally; no special narrative. |
| **F9** | Principle 15 external-audience exception scope narrow | No action | Crate-root `//!` preamble mentions the exception's narrow scope as part of the re-exports paragraph. |

**Source-move count: 1** (F2). All others are documentation-fold.

---

## 9. R1 wired-or-panic gate design

### 9.1 Scope (revised per Phase 2 marker-type pattern revision)

The R1 gate applies ONLY to construction paths. Read paths are callback-free.

Single gate: `CLAdt::<T>::construct(...)` (the only method that calls `alloc_with_tag`). All other CLAdt methods (`read_tag`, `read_field`, `own_field`, `into_typed`) are gate-free.

### 9.2 Implementation

The "gate" is implemented structurally via the named-null-callback pattern (per §5.5 / A6 ruling). No runtime check is added to `construct()`'s body — the panic happens inside `null_alloc_with_tag` if it's still pointed-to by `HostCallbacks::alloc_with_tag`.

No explicit `check_alloc_with_tag_wired() -> Result<(), &'static str>` API. Rationale: the named-null-callback IS the gate; adding a separate check API would duplicate the structural enforcement. Principle 18.

The future host-wiring sprint removes the gate by replacing `cranelisp_platform::null_alloc_with_tag` with the wired host callback in `int`'s `HostCallbacks` initializer:

```rust
// In int's HostCallbacks init (current; this sprint):
HostCallbacks {
    alloc: cranelisp_intrinsics::cranelisp_alloc,
    alloc_with_tag: cranelisp_platform::null_alloc_with_tag,    // R1 gate active
    validate_schema: cranelisp_platform::null_validate_schema,  // permissive
}

// In int's HostCallbacks init (future, host-wiring sprint):
HostCallbacks {
    alloc: cranelisp_intrinsics::cranelisp_alloc,
    alloc_with_tag: cranelisp_intrinsics::cranelisp_alloc_with_tag,        // wired
    validate_schema: cranelisp_int::platform::validate_schema_against_typecheck,  // wired
}
```

The diff to remove the gate is two lines in one file — clean per Principle 18 ("the panic-on-null surface is named, enumerable, and removable as a coherent unit").

### 9.3 Panic message format

Already drafted in §5.5 — repeated here for completeness as the contract:

```
CLAdt construction requires HostCallbacks::alloc_with_tag, which is not
yet wired by the host. See FIXME 0229 (host-side ADT marshaling — host-
wiring sprint scope).

If you are running tests inside cranelisp-platform, install a synthetic
callback via HostContext::init in test setup.
```

The message satisfies the /arch requirement (R1): names the method (CLAdt construction), names the missing callback (alloc_with_tag), names the FIXME (0229), and instructs tests on the workaround (synthetic callback).

### 9.4 The FIXME number

**Proposed: FIXME 0229.** (Next available after Phase 3 `/qa` filed 0224–0228 for the C1–C5 coverage holes; `fixmes/` directory now goes to `0228-qa-pif-unsafe-impl-send-sync-presence.md`.)

The FIXME file (to be authored Phase B by `/dev platform` per the SPRINT.md table — N+1 to N+7 — N=223; this one is N+1):

```yaml
---
number: 0229
# (Originally drafted as 0224; collided with /qa's Phase 3 FIXMEs 0224–0228; renumbered post-Phase-3.)
target: /int
filed_by: /dev (platform)
filed_at: 2026-05-2X       # Phase B date
sprint_filed: 71
refers_to: design/platform/sprint71-redesign.md §9, design/arch/bounded-contexts.md §5, crates/cranelisp-platform/src/lib.rs (HostCallbacks)
status: open
---

# Wire host-side ADT marshaling callbacks

## Issue
... [defers narrative to host-wiring sprint design phase]
```

(Other FIXMEs N+2 through N+7 enumerated in SPRINT.md §"New FIXMEs filed by Sprint 71" land in Phase B/C with sequential numbers 0230–0235 — post-Phase-3 renumber after `/qa`'s 0224–0228 reservations.)

---

## 10. Facade-fold plan (Phase C)

For each chunk of `design/arch/facades/platform.md` (the 337-line facade being retired):

| Facade section | Lines | Destination | Phase C action |
|---|---|---|---|
| Top preamble (bounded-context citation, target-stating note) | 1–7 | `bounded-contexts.md` §5 narrative | Fold the "shared interface contract" framing + "owns no runtime state" claim into BC §5. Already partially there; light reinforcement. |
| §"Public surface (as-designed)" preamble | 9–11 | `lib.rs //!` preamble | Crate-root `//!` declares the dual-audience purpose (host + DLL); current preamble at lib.rs:1–9 expands. |
| §"Marshaling — CL value wrappers" | 13–63 | per-item `///` on `CLType`, `CLInt`/`CLBool`/`CLFloat`/`CLString`, `CLIO<T>`, plus a paragraph in `lib.rs //!` summarising the family | The `to_raw` S67 W1 PFR narrowing rationale (lines 17–27) goes into the `CLType` trait rustdoc; per-wrapper conversion lists go into each wrapper's `///`. |
| §"Heap-typed values crossed" (CLHeap + CLOwned + CLString accessor) | 67–96 | per-item `///` on `CLHeap`, `CLOwned<T>`, `CLString::as_str` | F1 + F5 + F7 dispositions land here (per §8 above). |
| §"Platform manifest and fn descriptor" | 98–135 | per-item `///` on `PlatformFn`, `PlatformManifest`, `derive_jit_name` | F3 + F4(c) annotations land here. The PFR length-prefixed-strings rationale folds into `PlatformFn`'s rustdoc. |
| §"Host-side descriptors" | 137–159 | per-item `///` on `OwnedPlatformFnDescriptor`, `manifest_to_descriptors` | F4(b) annotation lands here. The FIXME-0155 resolution narrative (load_manifest/parse_type_sig are pub(crate) / int-side) folds into the `manifest_to_descriptors` rustdoc. |
| §"Host context" | 161–172 | per-item `///` on `HostContext` | F2 (after F2 source-move: deletion of Default impl, rustdoc records only `new` + `init`) + F4(a) annotation. |
| §"Host callbacks" | 176–197 | per-item `///` on `HostCallbacks` + per-field rustdoc on each callback | Sprint 71 adds `alloc_with_tag` + `validate_schema` per-field docs (see §5.1). The Decision-31 "Callback support (forward commitment)" narrative for the `Fn a b` row goes into `bounded-contexts.md` §5 (cross-surface; not crate-internal). |
| §"Type signature parser — internal only" | 200–201 | `bounded-contexts.md` §5 + crate-root `//!` | Note that `parse_type_sig` lives in `int`; not a platform crate item; BC §5 invariant statement. |
| §"declare_platform! macro" | 203–216 | per-item `///` on the macro | F6 absorption — see §7.5 draft text for the full rewritten narrative. |
| §"Errors" (PlatformError re-export) | 218–231 | per-item `///` on the `pub use cranelisp_types::PlatformError` re-export | Decision 0042 grounding + the four variants enumerated; Principle 15 external-audience exception note (cross-ref to crate-root). |
| §"Public consts" | 233–244 | per-item `///` on each const | ABI_VERSION's rustdoc gets the §6.1 bump-rule text. The IO_TAG_* + HEAP_HEADER_SIZE + STRING_HEADER_BYTES rustdocs stay narrow ("layout constant; see facade fold for full discussion"). |
| §"Free functions" | 246–253 | per-item `///` on `call_effect_thunk` + `derive_jit_name` | Existing rustdoc on `call_effect_thunk` (lib.rs ~300) expands with the "single-shot contract" + "trampoline-only audience" narrative from the facade. |
| §"Re-exports from cranelisp-types" | 257–269 | crate-root `//!` paragraph on the external-audience exception + per-item `///` on each `pub use` | F9 disposition. The crate-root narrative explains the exception's narrowness (Principle 15 four-clause test). |
| §"FQTypeName migration" | 273–275 | `bounded-contexts.md` §5 invariant table (or §7 cross-ref) | "Zero hits; no migration" stays as a one-line BC §5 entry. |
| §"Consumed surface" | 277–286 | crate-root `//!` (deps narrative) | "Depends only on `cranelisp-types`; external dep `libloading` is `int`-side." |
| §"Sealed traits" | 290–303 | per-item `///` on `CLType` + `CLHeap` | F5 + F8 dispositions land here. |
| §"#[non_exhaustive] DTOs" | 307–318 | `lib.rs //!` paragraph on the layout-discipline rule + per-item rustdoc on the `#[non_exhaustive]`-carrying types | Principle 14 grounding; F7 disposition for `CLOwned`. |
| §"Bounded-context invariants" 1–7 | 322–337 | `bounded-contexts.md` §5 invariant list | The 7 invariants migrate verbatim to BC §5 (where they already partially exist; this consolidates). The Decision 0026 GOT-dispatch invariant + Decision 0031 callback-row forward-commitment + Decision 0042 PlatformError adoption + spec §10.10.1 calling convention all stay grounded in BC §5. |

**Cross-references to sweep** (Phase C):

- `design/arch/facades/*.md` for `facades/platform.md` mentions (target replacement: source rustdoc / BC §5).
- `design/arch/principles/*.md` — likely unaffected; check for "the platform facade …" phrasing.
- `design/arch/sequences/*.mmd` — exec-flow-runtime.mmd mentions the IO trampoline + platform fn dispatch; check for facade citations.
- `design/arch/decisions/*.md` — Decisions 0026, 0031, 0040, 0041, 0042, 0043 mention platform facade by name; sweep.
- `design/platform/*.md` (this directory) — `platform.md` master, `platform-dlls.md`, `implementation-slice-s66.md`, `platform-registry-removal.md` — check for `facades/platform.md` citations.
- `design/{frontend,typecheck,backend,int}/*.md` — likely have a handful of citations.
- `crates/cranelisp-platform/Cargo.toml` — no metadata reference; check anyway.
- `README.md` — does not currently cite the facade; check.
- `design/arch/CLAUDE.md` exception list — add `facades/platform.md` alongside `facades/types.md` (S69) and `facades/frontend.md` (S70).

---

## 11. Open questions / things I could not decide

**None requiring /arch arbitration.** All A2/A6/A8 deferred-to-me arbitrations have rulings in §4.3, §5.2, §4.4 respectively. The F1–F9 dispositions follow the audit memo + R3 (no-rename) + R1 (host-wiring-sprint-removable gate) + R4 (ABI bump committed).

The construction-side type-witness check timing decision in §3.3 (witness check at every method entry, not once-per-value) is my call as /design — no /arch dependency, no cross-crate impact.

The "named-null-callback functions in `cranelisp-platform`" choice for A6 is unambiguously preferred over runtime `is_null()` checks per Principle 18; /arch's A6 framing said "slightly preferred but not binding"; I'm taking the preference.

---

## 12. Next skills

- `/qa` — failing-first unit test plan for the schema parser, `CLAdt` API surface, marker-type emission, sum-type lookup discipline, R1 gate panic message format, ABI_VERSION bump verification, F2 source-move compile fence. SPRINT.md §"Scope inside this sprint — Phase A" enumerates the test surface; /qa authors the test plan against this design doc.
- `/dev platform` — Phase B implementation: F2 source-move; ABI_VERSION = 2; `Schema` + `SchemaParseError` types + parser; `CLAdtType` + `AnyAdt` + `GetSchema` traits; `CLAdt<T>` struct + methods; `null_alloc_with_tag` + `null_validate_schema`; HostCallbacks growth; declare_platform! `schema:` arm; F2 deletion + minimal int patch + public-api.txt regen + new FIXMEs 0229–0235.
- `/review platform` — after Phase B; verifies design intent + no source-side drift from this doc.
- `/design platform` — Phase C: facade-fold execution (the §10 plan above), cross-reference sweep, exception list update.
- `/dev platform` — Phase C: fold execution alongside /design.

---

## Cross-references

- `sprints/SPRINT.md` — sprint scope (binding)
- `design/arch/facades/cranelisp-platform-audit-s69.md` — audit being absorbed
- `design/arch/facades/platform.md` — facade retired S71 Wave 4 (folded into `crates/cranelisp-platform/src/lib.rs` rustdoc + `bounded-contexts.md` §5)
- `design/arch/bounded-contexts.md` §5 — receives folded narrative
- `design/arch/principles/06-complexity-has-a-budget.md`, `08-no-interim-implementations.md`, `14-ffi-layout-discipline.md`, `15-facade-types-live-with-behavior.md`, `18-enforce-invariants-structurally.md`
- `design/arch/CLAUDE.md` §"Baseline-diff discipline (Sprint 67 close)" — public-api.txt + facade catch-up rule (S71 mutates rule slightly because the facade is retiring: catch-up lands in source rustdoc + BC §5 instead)
- `crates/cranelisp-platform/src/lib.rs` — current source (1139 LOC; Phase B target)
- `crates/cranelisp-platform/public-api.txt` — S67 frozen baseline (gets regenerated in Phase B per R4)
- `platforms/stdio/src/lib.rs`, `platforms/test-capture/src/lib.rs` — existing DLLs that must continue to compile (they don't use the new `schema:` arm; backward-compatibility via optional key)
