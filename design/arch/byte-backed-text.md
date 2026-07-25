# Byte-backed text — architecture exploration

**Status:** WORKING DESIGN, NON-NORMATIVE (Sprint 117).

**Authority boundary.** This document is an architecture feasibility record.
It does not define Cranelisp language semantics and does not amend `spec/`.
Names, literal syntax, conversion behavior, transparent-product eligibility,
and the migration from native `String` remain subject to explicit user rulings
followed by `/spec` work. The recommended direction below is decision-ready,
not settled.

**Archive trigger.** After the user settles the normative questions in §14 and
an implementation sprint lands the selected model, fold the enduring
cross-crate contracts into `interfaces.md`, `bounded-contexts.md`, source
rustdoc, the relevant sequence diagrams, and `overview.md`; then move this
exploration to `design/arch/archive/`. If the direction is rejected, archive it
when the replacement design records why.

## 1. Problem

Cranelisp currently has a native, immutable UTF-8 `String`. It is a distinct
heap allocation with a reference-counted header, byte length, and byte buffer.
String literals lower directly to that representation. Host-implemented
primitives provide concatenation, byte length, slicing, a nominally named
`char-at` that returns a one-character `String`, parsing, case conversion,
split/join, and scalar-to-string conversion.

This arrangement has three architectural costs.

1. Text policy is embedded in Rust primitives. Unicode scalar traversal,
   grapheme behavior, normalization, error handling, and encoding conversion
   cannot evolve as ordinary library code.
2. The primitive surface contains policy that is library-composable. The
   motivating example is `int-to-string`: decimal decomposition requires
   integer arithmetic and a way to append digit bytes, not host formatting.
3. The current names blur byte and character operations. `String` length is
   bytes; `substring` indexes bytes; `char-at` accepts a byte index but returns
   a `String`. Existing stdlib helpers inherit that ambiguity.

`Vec` is the existing general sequence type, but its current data buffer uses
one `i64` slot per element. A byte sequence represented as `(Vec Byte)` is
therefore semantically suitable but initially space-inefficient.

The design question is not merely “add Byte.” It is how to provide:

- an irreducible byte substrate;
- compiler-certified source text literals;
- nominal library text types without redundant wrapper allocations;
- exact ownership across representation-identical nominal types; and
- a later path to compact byte storage without inventing a temporary language
  type or a second vector abstraction.

## 2. Goals

- Make `Byte` the smallest native text-storage scalar, with the proposed
  semantic domain 0–255 and an initially permissible `i64` runtime word.
- Use ordinary `(Vec Byte)` as the byte-sequence substrate. Do not introduce a
  native `Bytes`.
- Give source literals a compiler-certified nominal type backed
  representation-identically by `(Vec Byte)`.
- Put code-point, grapheme, normalization, alternate-encoding, and most text
  algorithms in `stdlib/`.
- Provide a general representation-transparent mechanism for eligible
  one-constructor, one-field products. Text is its first motivating consumer,
  not a privileged backend case.
- Preserve nominal type and trait identity even when two types share one
  runtime word.
- Preserve exact-once RC and drop behavior across construction, access,
  pattern matching, calls, capture, containers, and return.
- Keep Run, Link, and REPL on the same pipeline and ABI.
- Demonstrate that `int-to-string` can move to stdlib, including `MIN_INT`.
- Decide whether compact `(Vec Byte)` belongs in the first implementation
  increment from actual seam and risk evidence.

## 3. Non-goals

- This document does not select language syntax or change the specification.
- It does not define a native `Char`, grapheme, code point, `Bytes`, or second
  String representation.
- It does not make UTF validation, normalization, segmentation, or locale
  behavior compiler responsibilities beyond source decoding and literal
  certification.
- It does not promise packed byte storage in the first implementation.
- It does not make transparent representation a source-level coercion.
- It does not expose Vec buffer pointers, offsets, or element stride to
  language programs.
- It does not remove native `String` or its primitives before a complete,
  separately approved migration.
- It does not reopen the paused memory-protection, ownership-instrumentation,
  or detector work.

## 4. Options explored

### 4.1 Native `Char` as a Unicode scalar

A native scalar-value `Char` gives strong invalid-state exclusion and natural
character literals, comparisons, and String traversal. It also makes
`int-to-string` straightforward through digit characters.

It does not solve grapheme behavior, normalization, or encoding policy.
`Vec Char` is not packed UTF-8, and materializing it changes String traversal
and storage costs. It also assigns Unicode scalar semantics to the compiler
when the desired direction is to move Unicode policy into stdlib.

**Disposition:** not recommended for the assumed direction. It remains a
possible future library abstraction over decoded values, not a required native
type.

### 4.2 Native `Char` as a grapheme

Grapheme clusters are variable-length sequences whose boundaries depend on a
versioned Unicode algorithm. Treating them as a scalar native value would put a
large, evolving policy surface in the compiler and make representation,
comparison, indexing, and literal identity unstable.

**Disposition:** rejected. Grapheme views and iterators belong in stdlib.

### 4.3 Native `Bytes` only

A dedicated packed `Bytes` type gives efficient storage and a convenient FFI
surface. It duplicates the sequence role of `Vec`, requires a second operation
family, and does not explain why `(Vec Byte)` should behave differently. Text
wrappers would then depend on a privileged collection instead of the ordinary
generic one.

**Disposition:** rejected under Principles 7 and 8. No second native byte
collection is justified.

### 4.4 Keep native `String` as the UTF-8 container

This is the least disruptive option. It preserves current literals, compact
bytes, and host primitives.

It leaves text construction and much Unicode policy behind a special native
representation. A nominal stdlib text model would either wrap String, retain a
large host primitive surface, or require privileged access to its buffer.

**Disposition:** viable compatibility state, not the recommended long-term
substrate. Native String must remain during migration until replacement
coverage is complete.

### 4.5 Native `Byte` + ordinary `(Vec Byte)` + certified UTF literal

This separates three concerns:

- `Byte` supplies the bounded storage scalar;
- `Vec` supplies ordinary sequence ownership and operations;
- the literal type records compiler certification of source text.

Stdlib may then define nominal validated text, decoded code-point iterators,
grapheme iterators, normalization, and alternate encodings. A general
transparent-product rule removes redundant wrapper allocations without
weakening nominal identity.

The initial wide-slot Vec costs eight bytes per Byte, but does not leak into
language semantics. Packing can later change storage without changing the
language type or stdlib algorithms.

**Disposition:** recommended direction, subject to the user gates in §14.

### 4.6 Native encoding-specific code-unit or character types

Examples include `Utf8CodeUnit`, `Utf16CodeUnit`, and `Utf32Scalar`.
Encoding-specific types can make individual conversion APIs precise, but they
multiply native scalar types and move encoding vocabulary into the compiler.
UTF-8 code units are exactly bytes plus validation context; UTF-16 code units
are bounded integers plus pairing policy; Unicode scalar validity can be a
stdlib validated newtype.

**Disposition:** rejected as native types. Stdlib nominal wrappers and checked
constructors can express these domains when a concrete use requires them.

## 5. Recommended direction

The decision-ready architecture is:

1. A native `Byte` with proposed semantic domain 0–255. Its first
   representation may be an `i64` word; representation is opaque.
2. Ordinary `(Vec Byte)`, initially using the current eight-byte Vec element
   slots.
3. A compiler-certified source-literal nominal type whose runtime word is the
   same Vec pointer as its `(Vec Byte)` payload.
4. `Utf8Literal` as the truthful candidate name when the exposed payload is the
   exact UTF-8 bytes produced after escape processing. `UtfLiteral` would imply
   encoding independence that an inspectable byte payload does not have.
5. A general transparent one-field-product mechanism. The literal type and
   stdlib text wrappers use it; the compiler does not special-case their names.
6. Stdlib owns decoding, code-point iteration, grapheme segmentation,
   normalization, alternate encodings, and presentation policy.
7. Native `Bytes` and native `Char` are not assumed.
8. Compact `(Vec Byte)` is deferred until the paused memory-layout safety
   frontier resumes.

The compiler's irreducible UTF responsibility is narrow: decode source, process
escapes, certify the literal byte sequence, and construct its payload. It does
not interpret arbitrary runtime byte vectors as text.

## 6. General transparent one-field products

### 6.1 Why this is not the existing Copy flattening

Cranelisp already value-flattens a conservative family of single-constructor,
single-field products. The types-owned `value_layout` predicate admits only a
fully concrete, recursively value-eligible field. Typecheck classifies the
result `Copy`; backend `HeapCategory::Value` emits no heap allocation, RC, or
drop glue.

That mechanism cannot simply admit `(Vec Byte)`. A Vec pointer is owned. If a
wrapper over Vec were classified `Copy`, calls and bindings could duplicate
the pointer without incrementing its RC, producing a use-after-free.

The architecture therefore requires two distinct representation answers:

- **Copy value:** the word contains no owned heap identity. Copying the word is
  ownership-neutral.
- **Transparent product:** the wrapper word is the field word, but ownership,
  heap category, and drop behavior are inherited from the field.

This distinction must be represented by one types-owned classifier and
consumed by typecheck and backend. It must not be independently re-derived at
constructor, match, drop, or call sites.

### 6.2 Eligibility

Subject to future user approval of automatic versus explicit eligibility, the
structural candidate rule is:

- exactly one constructor;
- exactly one field;
- the concrete field representation occupies one ABI word;
- the instantiated field type is known before backend lowering;
- the transparency walk contains no direct or mutual representation cycle;
- no constructor tag is needed;
- representation or pointer identity is not language-observable.

The classifier operates on a concrete instantiation. For a polymorphic product
such as `(Identity a)`, it substitutes the concrete argument into the field
before classifying. The resulting wrapper inherits the representation and
ownership category of that instantiation.

A direct or mutual transparent cycle is ineligible and falls back to the
ordinary boxed ADT. Recursion through an already pointer-represented container,
such as `Vec (Node a)`, terminates the representation walk at the Vec pointer
and is not itself an infinite inline representation.

### 6.3 Construction

An eligible constructor:

1. compiles its single field under the ordinary consuming convention;
2. performs no wrapper allocation and stores no tag;
3. returns the field word unchanged.

For an owned heap field, the field's existing reference transfers into the
nominal wrapper. Construction neither increments nor decrements it. Direct
constructor calls and constructors used as function values must use the same
core lowering.

### 6.4 Accessors

An accessor returns the same word. Its ownership summary must describe an
alias/projection, not a fresh ADT allocation.

- Consuming the wrapper may transfer the payload reference to the result.
- Borrowing a live wrapper and returning an independently owned payload must
  retain according to the ordinary call/result convention.

Generated accessor bodies and their first-class callable forms must agree.
The summary is derived from the representation classifier; a name-based list
of transparent accessors is forbidden.

### 6.5 Pattern matching

A constructor pattern for an eligible transparent product is irrefutable once
the scrutinee's nominal type is established. Backend emits no tag comparison
and no field dereference; the field binding receives the scrutinee word.

The binding is a projection/alias of the scrutinee root. Match cleanup must
release the root exactly once. Scrutinee cleanup and field-binding cleanup must
not both release the same reference, and moving the binding out of the arm must
transfer the reference rather than leave a later scrutinee decrement.

This is the highest-risk seam because current ownership analysis already
distinguishes whole-value match bindings, projections, COW results, and
escaping values.

### 6.6 Nominality and traits

Static identity remains the wrapper's fully-qualified type:

- trait impls on the wrapper do not apply to its field;
- overload and method resolution do not coerce;
- inference does not unify wrapper and field;
- REPL type prefixes name the wrapper;
- introspection shows the wrapper's constructors, fields, and impls.

Construction and access are explicit language operations even when backend
lowers them to identity moves.

### 6.7 Exact-once RC and drop

There is no wrapper header and no wrapper-specific recursive allocation.
Dropping the wrapper is dropping the concrete field exactly once:

- scalar/Copy field: no action;
- String, Vec, closure, or boxed ADT field: use that field's drop path;
- nested transparent wrappers: collapse transitively to one underlying drop;
- transparent wrapper stored in Vec: element glue is the underlying field's
  glue, still invoked once;
- transparent wrapper captured or returned: retain/transfer follows the field
  category while static type remains nominal.

The compiler must never emit both “drop wrapper” and “drop payload.” A
representation carrier must select one drop identity at monomorphisation.

## 7. Literal construction and stdlib boundary

The certified literal type must exist with an empty prelude. Literal lowering
cannot call a stdlib constructor or depend on optional modules.

The prospective flow is:

```text
source token
  -> frontend escape processing and source decoding
  -> certified byte payload on the literal AST/mono node
  -> backend allocates an ordinary Vec data buffer
  -> writes Byte values
  -> returns the Vec pointer typed nominally as Utf8Literal
```

Certification is the privileged operation; storage is ordinary Vec storage.
There is no second UTF heap layout.

Programmatically constructed `(Vec Byte)` remains arbitrary bytes. A checked
runtime/library conversion to the certified or validated nominal type, if any,
requires a future semantic ruling. It must not be an unchecked public
constructor accidentally exposed by ordinary ADT generation.

Stdlib can build:

- validated UTF-8 text newtypes;
- decoded code-point streams;
- grapheme streams;
- normalization transforms;
- UTF-16/UTF-32 conversion;
- byte and code-point indexing APIs with explicit names.

None of these abstractions require new compiler representations.

## 8. Compact `(Vec Byte)` feasibility

### 8.1 Current assumptions

The Vec object is:

```text
[HeapHeader | len:i64 | cap:i64 | data_ptr:i64]
```

The separate buffer is `cap * 8` bytes and every live element is an `i64`.
That assumption appears in:

- backend `HeapVec`;
- Vec literal stores and `vec-get` loads;
- inline `vec-set` and `vec-push`;
- first-class Vec primitive wrappers;
- intrinsics `vec_new`, set-copy, push-copy, grow, and drop;
- COW copy and source-release branches;
- per-element inc/dec callback signatures;
- data-buffer allocation and free layouts;
- primitives `split`/`join`;
- runtime consumers such as IO `select`;
- int-side Vec display and test readers;
- cache-generated object code and the runtime ABI;
- runtime specification prose that describes contiguous `i64` elements.

There is no element stride in the Vec header and `runtime/vec_new(cap)` receives
no layout descriptor.

### 8.2 Final mechanisms considered

A compact design needs either:

1. **Layout-parametric Vec.** Element size, alignment, and RC policy reach
   allocation, access, COW, growth, and drop. This may require a header layout
   field or monomorphised helper parameters.
2. **A monomorphic Byte specialization.** Every Vec operation selects a Byte
   helper family from resolved concrete type.

The second option appears smaller but risks a parallel Vec pipeline and a
growing family of privileged element types. A final design should instead have
one element-layout classification with Byte as its first compact case.

### 8.3 Seam inventory

Compact Byte storage changes:

- types-owned element layout/width classification;
- frontend/mono literal payload representation;
- backend i8 store/load and zero-extension to the `i64` register ABI;
- Vec literal, get, set, push, len, wrapper, and function-value paths;
- allocation byte-size and overflow checking;
- runtime copy, grow, mutate, and drop pointer arithmetic;
- COW behavior for both unique and shared vectors;
- element callback selection (Byte has no RC callback);
- R-3 runtime-owned Vec construction/read operations;
- String compatibility helpers that currently assume `Vec String`;
- display and test inspection;
- cache schema, object invalidation, and runtime ABI documentation;
- Run, Link, and REPL parity.

This is at least six bounded implementation slices across types, backend,
intrinsics, primitives, and int, with verification spanning raw allocation,
COW, and drop.

### 8.4 Recommendation: defer

Compact `(Vec Byte)` should not ship with the first Byte/literal increment.
It materially expands raw buffer allocation, pointer arithmetic, COW copying,
growth, and drop while the memory-protection and ownership-instrumentation
frontier is paused. Packing does not inherently require instrumentation, but
adding an under-certified second element-width path would route around the
reason that frontier is gated.

Deferral is not an interim implementation:

- the language type is ordinary `(Vec Byte)` before and after packing;
- `Byte` is explicitly permitted to occupy one `i64` initially;
- the public register ABI is already one `i64` per value;
- stdlib observes values and indices, not storage stride;
- the literal wrapper remains representation-identical to the Vec pointer;
- no native `Bytes` or temporary UTF representation is introduced.

The future specification must not promise eight-byte Byte slots. Existing
blanket `i64`-element layout prose must be separated into language semantics
and current implementation architecture before packing lands.

## 9. Relationship to R-3 / FIXME 0860

R-3 removes cross-crate Vec offset arithmetic from
`cranelisp-primitives::string::{split,join}` and delegates construction/read
discipline to `cranelisp-intrinsics::vec_runtime`.

That work helps this design by establishing a runtime-owned Vec boundary, but
it is not compact-Vec implementation:

- R-3 should expose the narrow wide-slot operations required today;
- it must not expose general mutable offsets or freeze `i64` element stride as
  a public semantic contract;
- its names and rustdoc should leave room for a later layout-derived operation;
- completing R-3 neither starts nor partially closes packed `(Vec Byte)`;
- compact Vec later revisits the runtime API and cache/ABI as a coordinated
  migration.

FIXME 0850 is separate again: it concerns intrinsics-internal raw reads in
drop code and remains tied to the blocked safety batch.

## 10. Native String migration

Native String remains live until the replacement is complete. The migration
must be accretive:

1. add Byte and the literal/text substrate;
2. establish stdlib text construction, display, parsing, and algorithms;
3. migrate stdlib and exemplar consumers;
4. compare behavior and performance in all modes;
5. only then propose primitive removals and String compatibility disposition.

R-3 should improve current String/Vec ownership independently. No String
primitive is removed merely because a future stdlib equivalent is designed.
Literal syntax transition, compatibility aliases, and the final status of
native String are normative user decisions.

## 11. Future implementation strategy

The following is staged work for a later, explicitly approved sprint.

### Stage A — architecture and types

Owner: `/arch`.

- Add Byte to cross-crate type carriers.
- Add a single representation classifier distinguishing Copy value,
  Transparent(field representation), and boxed ADT.
- Implement concrete substitution and cycle detection in the classifier.
- Record drop identity and ABI-surface consequences.
- Update `interfaces.md`, bounded contexts, overview, source rustdoc, public
  baselines, and cache schema plan together.

### Stage B — frontend

Owner: narrow `/design(frontend)` then `/dev(frontend)`.

- Parse the user-ratified literal and Byte syntax.
- Process escapes once.
- Carry certified bytes structurally; do not round-trip through native String
  policy.
- Keep macro S-expression representation and quote behavior explicit.

### Stage C — typecheck

Owner: narrow `/design(typecheck)` then `/dev(typecheck)`.

- Infer Byte and the literal nominal type.
- Enforce Byte construction/range rules selected by the user.
- Apply transparent representation only after concrete substitution.
- Derive constructor/accessor alias summaries.
- Preserve nominal trait and overload identity.
- Include representation changes in ABI-surface/redefinition classification.

### Stage D — backend

Owner: narrow `/design(backend)` then `/dev(backend)`.

- Lower Byte as an `i64` value initially.
- Lower literal payloads through ordinary wide-slot Vec allocation.
- Implement transparent constructor and constructor-as-value identity moves.
- Implement accessor and irrefutable-pattern identity lowering.
- Reuse underlying heap category, retain, projection, capture, and drop
  behavior.
- Keep one Run/Link/REPL code path.

### Stage E — intrinsics

Owner: narrow backend/runtime deployment.

- Reuse the R-3-approved runtime Vec construction boundary.
- Keep wide-slot allocation/COW/drop unchanged for the first increment.
- Add no Byte-specific allocation family.
- Add checked certification support only if the user selects a runtime
  conversion boundary.

### Stage F — primitives

Owner: narrow backend/runtime deployment.

- Register Byte type and only irreducible operations approved by the user.
- Keep primitive registration complete by construction under R-1.
- Do not add Unicode policy primitives.
- Retain current String primitives through migration.

### Stage G — integration / int

Owner: narrow `/design(src)` then `/dev(src)`.

- Render Byte and literal values according to the future REPL contract.
- Keep nominal type names visible.
- Teach display to traverse transparent wrappers without reading a nonexistent
  ADT header.
- Invalidate stale cache/object pairs under one schema window.

### Stage H — stdlib

Owner: `/stdlib`.

- Define validated text and explicit byte/code-point/grapheme views.
- Implement encoding conversion and invalid-input policy.
- Implement `int-to-string`.
- Migrate consumers only after equivalent coverage exists.

### Stage I — QA

Owners: `/qa` plan, `/testing` e2e sources.

- Establish the matrix in §13 before implementation.
- Require failing-first guards for every semantic and ownership seam.
- Treat packing as a later, independent matrix extension.

## 12. Stdlib `int-to-string`

No native Char is required. With existing integer arithmetic, comparisons,
`str-concat` or a future byte-vector builder, and a ten-entry ASCII digit table,
stdlib can:

1. return the zero digit for zero;
2. keep the working value non-positive;
3. derive each digit from remainder by 10;
4. map `0..9` to certified digit bytes;
5. prepend or reverse the accumulated digits;
6. add `'-'` for negative input.

Keeping the working value negative avoids computing `abs(MIN_INT)`, which is
not representable in signed 64-bit Int. Conceptually:

```text
n > 0  -> recurse on -n
n == 0 -> "0"
n < 0  -> repeatedly:
          q = n / 10
          digit = -(n - q * 10)
          n = q
```

The exact collection builder and final validated-text constructor depend on
future rulings, but the algorithm needs no host integer formatter and no native
character type.

## 13. Verification matrix

### Byte

- endpoints 0 and 255;
- every selected rejection path for -1 and 256;
- checked Int conversion;
- comparison/arithmetic behavior once ruled;
- register ABI and zero extension;
- Run, Link, and REPL parity.

### Certified literal

- empty, ASCII, non-ASCII, escape, and embedded-NUL payloads;
- exact post-escape UTF-8 bytes if selected;
- invalid source encoding and malformed escapes;
- arbitrary `(Vec Byte)` is not silently certified;
- empty-prelude compilation;
- nominal REPL type and display.

### Transparent products

- scalar, String, Vec, closure, and boxed-ADT fields;
- nested transparent products;
- polymorphic scalar and heap instantiations;
- direct and mutual recursive fallback;
- direct constructor and constructor-as-value;
- accessor direct and function-value calls;
- let, match, return, capture, and container storage;
- nominal trait separation and no implicit coercion;
- exact-once RC under ownership analysis on and off;
- cache fresh build, hit, and stale-schema rejection;
- mode parity.

### Wide `(Vec Byte)`

- literal/get/set/push/len;
- empty, capacity growth, COW unique and shared arms;
- Byte element has no RC callback;
- wrappers inside Vec and Vec inside wrappers;
- no dependence on packed storage.

### Future compact extension

- wide-versus-packed behavioral differential;
- i8 load zero-extension;
- allocation-size overflow;
- byte-count versus element-count capacity;
- unique/shared COW and grow;
- exact buffer free;
- unchanged heap-element Vec callbacks;
- R-3 consumer compatibility;
- all modes and stale cache rejection.

### Stdlib text

- valid and invalid UTF;
- code-point and grapheme iteration;
- normalization policy once selected;
- alternate encodings;
- byte-versus-code-point indexing;
- `int-to-string` for zero, positive, negative, `INT_MAX`, and `INT_MIN`;
- migration equivalence against native String behavior where promised.

## 14. Public API, cache, and ABI consequences

Potential future public changes include:

- Byte variants in `Type` and `ConcreteType`;
- literal variants or payload changes in S-expression/AST/MonoExpr carriers;
- a types-owned representation classification;
- source rustdoc and public-api baselines for every exposed carrier;
- primitive table rows for Byte and checked conversions;
- optional runtime certification operations;
- display/type-renderer cases.

Serde-visible carrier changes and representation changes require one deliberate
`CACHE_SCHEMA_VERSION` bump. Automatic transparency also changes emitted ABI
for pre-existing eligible products; every cached caller must invalidate.
Redefinition ABI classification must treat a type entering or leaving
transparent eligibility as an ABI change.

No multiword function ABI is required: Byte, Vec pointers, and transparent
products remain one `i64`. Compact Vec changes buffer layout and runtime helper
ABI even though the language call ABI remains one word; it therefore needs its
own schema/ABI review.

## 15. Risks and mitigations

| Risk | Consequence | Required mitigation |
|---|---|---|
| Transparent heap wrapper classified Copy | missing retain, UAF | distinct Transparent-versus-Copy carrier |
| Constructor/accessor/match derive eligibility separately | representation drift | one types-owned classifier |
| Match binds payload and drops both names | double release | projection-root ownership, exact-once tests |
| Automatic transparency changes existing ADTs | cache/ABI mismatch | user gate, schema bump, full invalidation |
| Generic field not concretely substituted | wrong layout/drop | classify only concrete instantiations |
| Recursive wrapper flattened | non-terminating classification or lost node | path cycle guard, boxed fallback |
| Literal depends on stdlib | empty-prelude failure | compiler-known nominal type and direct payload lowering |
| `UtfLiteral` hides observable encoding | misleading API | prefer `Utf8Literal` if bytes are UTF-8 |
| Packing becomes a Byte-only Vec fork | parallel runtime paths | later general element-layout mechanism |
| Packing lands without safety evidence | buffer corruption | defer to resumed safety frontier |
| String removed before parity | ecosystem regression | accretive migration and user approval |

## 16. Unresolved normative questions and future gates

No question in this section is answered by this document.

1. Is the native Byte semantic domain exactly 0–255?
2. What Byte literal and checked-conversion syntax/result shape are used?
3. Do Byte arithmetic operations wrap, check, widen, or remain library-only?
4. Is every source text literal encoded as exact UTF-8 bytes after escape
   processing?
5. Is the nominal literal type named `Utf8Literal` or `UtfLiteral`?
6. Does existing string-literal syntax change, coexist during migration, or
   remain native String while a new syntax is introduced?
7. Is the certified literal constructor compiler-only?
8. Is there a checked runtime `(Vec Byte)` conversion, and what failure type
   does it return?
9. Is the literal payload accessor public?
10. Are eligible one-constructor/one-field products transparent automatically,
    or only with explicit declaration metadata?
11. Is transparent representation entirely unobservable, with no pointer or
    allocation identity guarantee?
12. Do representation-cycle products silently retain boxed layout or produce a
    declaration diagnostic?
13. What is the public stdlib validated-text type called?
14. What invalid-UTF, normalization, code-point, grapheme, and indexing
    contracts does stdlib expose?
15. What is the compatibility and removal policy for native String and each
    String primitive?

The future gate order is:

1. user rulings on the semantic questions;
2. `/spec` records settled semantics and invalidates affected coverage;
3. `/arch` promotes the selected cross-crate contracts into the canonical set;
4. narrow per-crate designs;
5. `/qa` approves the implementation matrix;
6. implementation with failing-first tests;
7. user approval before native String removal or compact Vec activation.

## 17. Design verdict

The recommended direction is architecturally coherent:

- native Byte;
- ordinary, initially wide-slot `(Vec Byte)`;
- a compiler-certified nominal UTF-8 literal candidate;
- general transparent one-field products with inherited ownership;
- Unicode policy in stdlib;
- no assumed native Bytes or Char.

The transparent-product mechanism is feasible but is an ownership feature, not
just an allocation optimization. It requires a distinct representation
classification and a coordinated types/typecheck/backend/cache change.

Compact `(Vec Byte)` is also feasible, but it is not bounded to the Byte
feature. It crosses the whole Vec allocation/COW/drop runtime and should wait
for the paused memory-layout safety frontier. Wide-slot delivery is the final
language architecture at lower storage precision, not an interim type design.
