# Data Structures

## Motivation

Cranelisp needs container data structures (Vec, List) and a polymorphic iteration interface (map, fold) to be useful for real programs. Today, the only compound data types are ADTs and closures — both leak-allocated via `cranelisp_alloc` with no deallocation. Containers amplify this problem: a `(vec-push xs 42)` in a loop allocates on every iteration with no reclamation.

These two problems are coupled: containers need memory management to be practical, but memory management needs containers to justify the infrastructure work. This document designs both together and proposes an incremental implementation path. (See roadmap items "persistent data structures" and "GC or reference counting".)

Target code:

```clojure
;; Vec with bracket syntax
(let [xs [1 2 3 4 5]]
  (vec-map (fn [x] (* x x)) xs))     ; => [1, 4, 9, 16, 25]

;; List with ADT + sugar
(let [ys (list 1 2 3)]
  (list-reduce + 0 ys))               ; => 6

;; Multi-sig map dispatching on container type (returns lazy Seq)
(to-list (map (fn [x] (+ x 1)) [10 20 30]))       ; => (list 11 21 31)
(to-list (map (fn [x] (+ x 1)) (list 10 20 30)))  ; => (list 11 21 31)
(to-list (take 3 (map inc (range-from 0))))        ; => (list 1 2 3)
```

## Strategy Comparison: Memory Management

Three approaches to memory management in a JIT-compiled functional language:

**Tracing GC**: The most powerful approach — handles cycles, requires no compiler cooperation for inc/dec. However, tracing GC needs stack maps to identify live heap pointers in JIT'd frames. Cranelift does not provide stack maps, so we would need to implement a shadow stack or conservative collector. Significant runtime complexity (stop-the-world pauses or concurrent marking). Haskell, OCaml, and most Lisps use this approach.

**Reference counting (recommended)**: Deterministic, compiler-inserted `inc`/`dec` on every copy and scope exit. Enables copy-on-write (COW) for Vec — mutate in place when refcount is 1. Fits our monomorphisation model well: the compiler always knows concrete types at every point, so `inc`/`dec` decisions are static (no runtime type dispatch). Carp uses this approach successfully for a typed Lisp without GC. The main weakness is cycles, but cranelisp has no mutable references — all values are semantically immutable — so reference cycles cannot form.

**Region/arena allocation**: Efficient (bulk free), but requires lifetime/region analysis beyond Hindley-Milner. Would need significant type system extensions (region polymorphism). Rust achieves this with ownership + borrows, but that's a different language design. Not a good fit for HM inference.

We choose reference counting: it's the simplest approach that gives deterministic deallocation, it enables COW optimization for Vec, and it requires no type system changes — only codegen changes.

## Object Header Design

All heap-allocated values get a 16-byte header containing size and reference count. `cranelisp_alloc` returns a pointer **past** the header (`base + 16`), so **all existing payload offsets are unchanged**. The rc header lives at `ptr - 8`, the size at `ptr - 16`, both invisible to all existing codegen, Rust primitives, and REPL display code.

```
Memory:   [size: i64 | rc: i64 | payload...]
                                  ^
                                  |
                    ptr returned by alloc (points here)
```

The `size` field stores the total allocation size (header + payload) and is used by `free()` to reconstruct the layout for deallocation. The `rc` field at `ptr - 8` stores the reference count.

Payload layouts are unchanged:

| Object | Layout (from ptr) |
|---|---|
| String | `[len \| bytes...]` |
| Closure | `[code_ptr \| cap0 \| ...]` |
| ADT data ctor | `[tag \| field0 \| ...]` |

To access the rc header: `load [ptr - 8]` / `store [ptr - 8]`.

Values that remain as bare i64 (no header):
- Scalars: Int, Bool, Float (bitcast f64)
- Nullary ADT constructors: bare i64 tag (0, 1, 2, ...)

Initial refcount is 1 on allocation. This is the natural "one owner" state — the binding that receives the freshly allocated value.

## Compiler-Inserted Inc/Dec

Reference counting is invisible to the user — the compiler inserts all `inc` and `dec` operations.

### Rules

**Increment** (refcount += 1):
- Assign to a new binding: `(let [y x] ...)` — inc `x`
- Capture in a closure: `(fn [a] (+ a x))` — inc `x` when closure is allocated
- Store into a container: `(vec-push xs x)` — inc `x`
- Pass as argument: `(f x)` — inc `x` (callee may store it)

**Decrement** (refcount -= 1):
- Scope exit: when a let binding goes out of scope, dec the value
- Function return: dec all local bindings except the return value
- Closure drop: when a closure's refcount hits 0, dec all captured values
- Container drop: when a Vec/List refcount hits 0, dec all elements

### Monomorphisation advantage

Because cranelisp monomorphises all constrained polymorphic functions, the compiler always knows the concrete type at every `inc`/`dec` site. This means:
- No runtime type tags needed for refcounting
- `inc` on an `Int` is a no-op (not heap-allocated) — the compiler statically elides it
- `inc` on a `String` generates a heap load+add+store — the compiler statically emits it
- Per-type drop functions for ADTs recursively dec heap-pointer fields

### Codegen patterns

Since `ptr` points past the header, rc is accessed at `ptr - 8`:

```
inc(ptr):    load rc = [ptr, offset=-8]
             rc' = iadd rc, 1
             store [ptr, offset=-8] = rc'

dec(ptr):    load rc = [ptr, offset=-8]
             rc' = isub rc, 1
             brif rc' == 0, free_block, store_block
  store_block: store [ptr, offset=-8] = rc'
               jump continue
  free_block:  <drop fields recursively> (future)
               call cranelisp_free(ptr) (no-op for v1)
               jump continue
```

For ADT types with mixed nullary/data constructors, a runtime guard skips inc/dec when the value is a bare nullary tag (small integer, not a heap pointer): `if ptr < 1024 then skip`.

### Scope and current status (Sub-Phases 2A-2F complete)

The RC system is implemented in six sub-phases:

- **2A** (done): `alloc_with_rc()` allocates `size + 16` bytes, stores total size at `base+0`, rc=1 at `base+8`, returns `base+16`. All existing payload offsets unchanged.
- **2B** (done): Expression type map (`expr_types: HashMap<Span, Type>`) threaded from typechecker through codegen. `FnCompiler` has `variable_types` tracking.
- **2C** (done): `emit_inc()` and `emit_dec()` methods on `FnCompiler` with inline Cranelift IR. `HeapCategory` enum classifies types as NeverHeap/AlwaysHeap/Mixed. Inc inserted at closure captures and let-binding variable aliases.
- **2D** (done): Scope-level dec via `scope_stack: Vec<Vec<(String, Variable, Type)>>` on FnCompiler. `push_scope()` / `pop_scope_for_value(result)` emit dec for each binding in the scope, using runtime value comparison to skip the return value. Applied to let scopes, match arm scopes, lambda return, and do intermediate cleanup.
- **2E** (done): Per-type drop functions generated at compile time. `resolve_drop_fn()` lazily generates Cranelift functions that load heap-typed fields from ADT constructors and recursively dec them before freeing. Handles recursive types (e.g., List) via pre-caching FuncId before building body. `drop_fn_cache: HashMap<String, FuncId>` on FnCompiler. Closure drop glue deferred (closures don't encode captured value types).
- **2F** (done): Real deallocation. Header expanded from 8 to 16 bytes (`[size | rc | payload]`). `free()` reads total_size from `ptr - 16`, reconstructs layout, calls `std::alloc::dealloc`. Diagnostic counters (`ALLOC_COUNT`, `DEALLOC_COUNT`) for testing. REPL `/mem` command shows allocation stats.

### Known limitations

- **Match scrutinee lifetime**: The scrutinee value in match expressions is not dec'd after the match completes. Match var patterns inc the scrutinee (for safe multi-arm use) and the scope exit decs the binding, but the original reference leaks. Future work.
- **Closure drop glue**: Closures that capture heap values leak those captures when the closure is freed, since closures don't encode their captured values' types. Future work.
- **Function argument lifetime**: Heap-typed values passed as arguments are not dec'd by the callee. Future work (callee vs caller responsibility).

## Vec — Built-in Type

### Why built-in

Vec needs contiguous resizable memory (`realloc` on the backing buffer) which cannot be expressed as an ADT. ADTs are fixed-size — they have a statically known number of fields. Vec has a dynamic number of elements and must manage a separate data buffer.

### Type

Reuse the existing `Type::ADT("Vec", vec![elem_type])` representation. The typechecker special-cases "Vec" in constructor lookup to provide `vec-get`, `vec-push`, etc. as typed operations rather than ADT constructor calls.

### Syntax

```clojure
;; Bracket literal in expression position
[1 2 3]

;; Equivalent function form
(vec 1 2 3)

;; Operations
(vec-get xs 0)          ; O(1) index, bounds-checked
(vec-set xs 0 99)       ; returns new Vec (COW: mutates if rc==1)
(vec-push xs 42)        ; returns new Vec with element appended
(vec-len xs)            ; length
```

**Parser**: `[` in expression position triggers Vec literal parsing. The parser already uses `[` for parameter lists and field definitions — disambiguation is by context:
- After `defn name` or `fn` → parameter list
- After `let` or `bind!` → binding list
- After `deftype` constructor → field list
- Otherwise → Vec literal

`(vec ...)` is parser sugar equivalent to the bracket form. The bracket literal collects comma-free elements until `]`.

### Runtime representation

```
Vec value (i64 pointer) → [rc: i64 | len: i64 | capacity: i64 | data_ptr: i64]
                                                                      ↓
                                                          [elem0 | elem1 | ... | elemN | <unused capacity>]
```

- Header: 4 slots (32 bytes) — refcount, length, capacity, data pointer
- Data buffer: separate allocation, `capacity * 8` bytes
- Elements are i64 (same uniform representation as everything else)
- Empty Vec: `len=0, capacity=some_default, data_ptr=alloc(capacity*8)`

### Implementation

Extern primitives in `primitives/vec.rs`, registered via `JITBuilder::symbol`:
- `cranelisp_vec_get(vec_ptr: i64, index: i64) -> i64` — bounds check, load from data buffer
- `cranelisp_vec_set(vec_ptr: i64, index: i64, val: i64) -> i64` — COW, returns new/same Vec ptr
- `cranelisp_vec_push(vec_ptr: i64, val: i64) -> i64` — COW, may realloc data buffer
- `cranelisp_vec_len(vec_ptr: i64) -> i64` — load length field

### Copy-on-write

`vec-set` and `vec-push` check `rc == 1`:
- **Unique (rc==1)**: mutate the data buffer in place, return the same pointer
- **Shared (rc>1)**: allocate new header + data buffer, copy elements, apply mutation, return new pointer; dec the original

This preserves pure functional semantics — callers never observe mutation of shared values.

## List — Recursive ADT

### Why ADT (not built-in)

List fits the existing ADT system naturally — it's a recursive sum type with two constructors. Defining it as an ADT demonstrates that the type system is expressive enough for real data structures and avoids special-casing in the compiler.

### Prerequisite: Recursive Types

Currently, `TypeExpr` (in `src/ast.rs:96-103`) cannot express parameterized type references in field positions. The variants are:

```rust
pub enum TypeExpr {
    Named(String),      // e.g., "Int", "Point"
    SelfType,           // self in trait methods
    IO(Box<TypeExpr>),  // IO a
    FnType(Vec<TypeExpr>, Box<TypeExpr>),  // (fn [a b] c)
    TypeVar(String),    // a, b (lowercase)
}
```

To write `(deftype (List a) Nil (Cons [:a head :(List a) tail]))`, we need `:(List a)` as a field type — a parameterized type constructor applied to type arguments. This requires a new variant:

```rust
TypeExpr::Applied(String, Vec<TypeExpr>)  // e.g., Applied("List", [TypeVar("a")])
```

Changes needed:
- `src/ast.rs` — add `Applied(String, Vec<TypeExpr>)` to `TypeExpr`
- `src/parser.rs` — `type_expr()` rule: parse `(Name arg1 arg2)` as `Applied`
- `src/typechecker/unification.rs` — `resolve_type_expr_with_vars`: handle `Applied` by looking up the type name and recursively resolving args to produce `Type::ADT(name, resolved_args)`

### Definition

```clojure
(deftype (List a)
  Nil
  (Cons [:a head :(List a) tail]))
```

Defined in `prelude.cl` alongside `Option`.

### `(list ...)` sugar

Parser desugars `(list ...)` to nested constructor calls:

```clojure
(list 1 2 3)
;; desugars to:
(Cons 1 (Cons 2 (Cons 3 Nil)))
```

This is O(n) — the parser walks the elements right-to-left, wrapping each in `Cons`. Similar to the existing `bind!` desugaring pattern.

### Runtime representation

Follows existing ADT conventions:
- `Nil` = 0 (bare i64 tag, nullary constructor)
- `(Cons head tail)` = heap pointer → `[rc | tag=1 | head | tail_ptr]`

With refcounting, each Cons cell is 4 slots (32 bytes). The tail is an i64 that's either 0 (Nil) or a pointer to another Cons cell.

### Standard operations

Defined as regular cranelisp functions (not extern primitives):

```clojure
(defn head [xs]
  (match xs
    [(Cons h _) h]))

(defn tail [xs]
  (match xs
    [(Cons _ t) t]))

(defn nil? [xs]
  (match xs
    [Nil true
     _ false]))
```

`cons` is just the `Cons` constructor.

### TCO dependency

Recursive list operations (map, reduce, filter) will overflow the stack on large lists without tail-call optimization. TCO is a hard prerequisite for practical List usage beyond small examples. Without TCO, list operations are limited to lists that fit within the default stack depth (~thousands of elements).

## Seq — Lazy Sequences

### Why thunk-based

Lazy sequences reuse existing language features — ADTs for the structure and closures for deferred computation. No new primitives or runtime support is needed. A `SeqCons` cell holds a value and a thunk (zero-argument closure) that produces the rest of the sequence when called. This is the same approach used by Haskell's lists and Clojure's lazy-seq.

### Definition

```clojure
(deftype (Seq a)
  SeqNil
  (SeqCons [:a head :(Fn [] (Seq a)) rest]))
```

Defined in `prelude.cl` alongside `List` and `Option`.

### Runtime representation

Follows existing ADT conventions:
- `SeqNil` = 0 (bare i64 tag, nullary constructor)
- `(SeqCons head thunk)` = heap pointer → `[rc | tag=1 | head | thunk_ptr]`

The thunk is a closure `(fn [] (Seq a))` — a heap pointer to `[code_ptr]` (or `[code_ptr, captures...]` if it captures variables). Forcing the thunk is a regular closure call.

### Internal operations

These functions work directly on Seq values. All are defined in `prelude.cl` as recursive cranelisp functions:

- `lazy-map [f s]` — apply `f` to each element, returning a new Seq (lazy)
- `lazy-filter [pred s]` — keep elements where `pred` returns true (lazy, but may force multiple elements to find a match)
- `lazy-take [n s]` — first N elements as a Seq (lazy)
- `lazy-drop [n s]` — skip first N elements (eager — forces N thunks immediately)
- `lazy-reduce [f init s]` — eager left fold over entire Seq

### Producers

Infinite sequence generators:

```clojure
(range-from 0)          ; (seq 0 1 2 3 4 ...)
(iterate inc 0)         ; (seq 0 1 2 3 4 ...)
(repeat 42)             ; (seq 42 42 42 42 ...)
```

- `range-from [n]` — integers starting at `n`, incrementing by 1
- `iterate [f x]` — `x`, `(f x)`, `(f (f x))`, ...
- `repeat [x]` — infinite repetition of `x`

### Conversion and materialization

- `seq [v]` / `seq [l]` — convert Vec or List to Seq (multi-sig, 2 variants)
- `to-list [s]` — force entire Seq to a List (eager — will not terminate on infinite Seq)
- `vec-to-seq [idx v]` — internal: convert Vec to Seq starting at index `idx`
- `list-to-seq [xs]` — internal: convert List to Seq

## Polymorphic Map and Reduce

### The HKT problem

A generic `Functor` trait would need higher-kinded types:

```clojure
;; Hypothetical — NOT supported
(deftrait (Functor f)
  (defn map [(fn [a] b) (f a)] (f b)))
```

This requires `f` to be a type constructor (kind `* -> *`), which our HM type system doesn't support.

### Phase 1: Type-specific functions

```clojure
(defn vec-map [f xs] ...)       ; (fn [(fn [a] b) (Vec a)] (Vec b))
(defn vec-reduce [f init xs] ...) ; (fn [(fn [b a] b) b (Vec a)] b)

(defn list-map [f xs] ...)      ; (fn [(fn [a] b) (List a)] (List b))
(defn list-reduce [f init xs] ...) ; (fn [(fn [b a] b) b (List a)] b)
```

These are regular polymorphic functions. `vec-map` and `vec-reduce` would be extern primitives (they need to allocate/iterate over Vec internals). `list-map` and `list-reduce` would be cranelisp functions operating on the ADT.

### Phase 2: Multi-sig collection API

```clojure
(defn map
  ([f v] (lazy-map f (vec-to-seq 0 v)))   ; v : (Vec a)
  ([f l] (lazy-map f (list-to-seq l)))     ; l : (List a)
  ([f s] (lazy-map f s)))                  ; s : (Seq a)

(defn filter
  ([pred v] (lazy-filter pred (vec-to-seq 0 v)))
  ([pred l] (lazy-filter pred (list-to-seq l)))
  ([pred s] (lazy-filter pred s)))

(defn take
  ([:Int n v] (lazy-take n (vec-to-seq 0 v)))
  ([:Int n l] (lazy-take n (list-to-seq l)))
  ([:Int n s] (lazy-take n s)))

(defn drop
  ([:Int n v] (lazy-drop n (vec-to-seq 0 v)))
  ([:Int n l] (lazy-drop n (list-to-seq l)))
  ([:Int n s] (lazy-drop n s)))

(defn reduce
  ([f init v] (lazy-reduce f init (vec-to-seq 0 v)))
  ([f init l] (lazy-reduce f init (list-to-seq l)))
  ([f init s] (lazy-reduce f init s)))
```

This uses the existing multi-sig dispatch system. The typechecker disambiguates variants by the container argument's type — `(Vec a)` vs `(List a)` vs `(Seq a)` have different type constructors, so unification picks the correct variant. All `map`/`filter`/`take`/`drop` operations convert their input to Seq and return Seq (lazy). `reduce` is eager — it forces the entire sequence.

### Future: HKT or associated types

A proper `Functor` abstraction requires higher-kinded types or type classes with associated types. This is a major type system extension — not for now. The multi-sig approach covers the practical need.

> **Naming**: We use `reduce` rather than `fold` to follow the Clojure standard library naming convention.

## Hidden Mutability / Copy-on-Write

All values in cranelisp are semantically immutable. `(vec-push xs 42)` returns a "new" Vec — the caller's `xs` binding is unchanged.

COW optimization: when `rc == 1` (sole owner), mutate the backing storage in place and return the same pointer. This is safe because:
- No other reference can observe the mutation (rc==1 means sole owner)
- Pure functional semantics means the old binding goes out of scope after rebinding
- The caller wrote `(let [ys (vec-push xs 42)] ...)` — `xs` is not used after this point (or if it is, the push already copied)

Where COW applies:
- **Vec operations** (`vec-set`, `vec-push`): check rc on the Vec header; if unique, also check whether the data buffer needs realloc
- **List**: naturally persistent — `(Cons x xs)` shares the tail `xs` without copying. No COW needed

Future direction: uniqueness types or linear types could guarantee COW at the type level, making the optimization a compile-time certainty rather than a runtime check. This is what Clean does with uniqueness typing and what Roc is exploring.

## Stack vs Heap / Box

### Current model

- Scalars (Int, Bool, Float) live on the stack as i64 Cranelift SSA values
- All compound values (String, Closure, ADT data ctors) live on the heap as i64 pointers
- No explicit Box — the uniform i64 representation means pointers ARE machine words

### Nested containers

`(Vec (Vec Int))` stores i64 pointers to inner Vec headers in the outer data buffer. Each inner Vec is independently refcounted. Decrementing the outer Vec to 0 recursively decrements each inner Vec.

### Deterministic drop

Refcount decrement at scope exit IS deterministic drop — when rc hits 0:
1. Recursively dec all heap-pointer fields (closures dec captures, ADTs dec data fields, Vec decs elements)
2. Free the header allocation
3. For Vec: also free the data buffer

This gives Rust-like deterministic destruction without ownership types.

### Future: Escape analysis

Escape analysis could identify heap allocations that don't escape their scope and stack-allocate them instead. For example, a Vec created and consumed within a single function could avoid heap allocation entirely. This is a compiler optimization for later.

## Tuples, Quote Syntax, and Homoiconicity

In Lisp, `'(expr)` (quote) prevents evaluation — the result is the raw form, which is a tuple of its elements. This connects to a broader question about cranelisp's identity as a Lisp:

- `'(list 1 2 3)` would have type `(Tuple Symbol Int Int Int)` — the unevaluated form
- Tuples and product ADTs are the same concept: anonymous products with positional access (`.0`, `.1`, `.2`)
- But `'(3 4)` is NOT type-equivalent to `(Point 3 4)` — Point has named fields and a nominal type; tuples are structural

Quote syntax, tuples, reader macros, homoiconicity, and an eventual macro system are deeply interconnected. Tuples describe "the type of a form before it is applied." This is deferred — the current priority is containers and iteration.

## Incremental Implementation Phases

| Phase | Feature | Prerequisite | Key files |
|-------|---------|-------------|-----------|
| Phase | Feature | Status | Key files |
|-------|---------|--------|-----------|
| **0** | Recursive ADTs (`TypeExpr::Applied`) | Done | `ast.rs`, `parser.rs`, `typechecker/unification.rs` |
| **1** | List type + `(list ...)` sugar | Done | `prelude.cl`, `parser.rs` |
| **2A** | RC header infrastructure | Done | `intrinsics.rs` (alloc_with_rc), `primitives/mod.rs`, `primitives/string.rs` |
| **2B** | Type context in codegen | Done | `typechecker/` (expr_types), `codegen/mod.rs` (FnCompiler fields), `jit.rs` |
| **2C** | Inc/dec emission | Done | `codegen/mod.rs` (emit_inc/dec, HeapCategory), `codegen/expr.rs`, `codegen/closures.rs`, `intrinsics.rs` (cranelisp_free) |
| **2D** | Scope-level dec | Done | `codegen/mod.rs` (scope_stack, pop_scope_for_value) |
| **2E** | Drop glue | Done | `codegen/mod.rs` (resolve_drop_fn, drop_fn_cache) |
| **2F** | Actual deallocation | Done | `intrinsics.rs` (real free, 16-byte header, alloc/dealloc counters) |
| **3** | Vec type + `[...]` syntax | Done | `parser.rs`, `primitives/vec.rs`, `jit.rs`, `codegen/expr.rs` |
| **4** | Type-specific map/reduce | Done | `primitives/vec.rs` (vec-map, vec-reduce), `prelude.cl` (list-map, list-reduce) |
| **5** | Multi-sig collection API + Seq | Done | `prelude.cl` (map, filter, take, drop, reduce, Seq type) |

**Phases 0-1 are complete.** Recursive types and List work.

**Phase 2A-2F are complete.** Full reference counting: 16-byte headers (`[size | rc | payload]`), inline inc/dec emission, scope-level dec with runtime return-value comparison, per-type drop glue for ADTs, and real deallocation with diagnostic counters. REPL `/mem` command. All 263 tests pass (including 9 dedicated RC tests in `tests/rc.rs`).

**Phase 3 is complete.** Vec type with `[...]` syntax, `vec-get`/`vec-set`/`vec-push`/`vec-len` operations, RC drop glue with loop-based element cleanup. COW deferred — `vec-set` and `vec-push` always copy. COW requires function argument RC (inc on call) or liveness analysis to be correct, since a Vec passed to `vec-set` has rc==1 even when the caller still holds a reference.

**Phase 4 is complete.** Type-specific `vec-map`, `vec-reduce` (extern primitives in `primitives/vec.rs`), `list-map`, `list-reduce` (cranelisp functions in `prelude.cl`).

**Phase 5 is complete.** Multi-sig `map`/`reduce`/`filter`/`take`/`drop` dispatching on Vec, List, and Seq. Plus the `Seq` ADT type with thunk-based lazy evaluation, `seq` converter, producers (`range-from`, `iterate`, `repeat`), and materializer (`to-list`). All functions defined in `prelude.cl`.

## REPL Behavior

Following the self-documenting REPL principle:

```
cranelisp> [1 2 3]
[1, 2, 3] :: (Vec Int)

cranelisp> (list 1 2 3)
(Cons 1 (Cons 2 (Cons 3 Nil))) :: (List Int)

cranelisp> Vec
Vec :: type (Vec a)

cranelisp> Nil
Nil :: (List a)

cranelisp> Cons
Cons :: (fn [a (List a)] (List a))

cranelisp> vec-get
vec-get :: (fn [(Vec a) Int] a)

cranelisp> vec-push
vec-push :: (fn [(Vec a) a] (Vec a))
```

Vec display uses `[elem, elem, ...]` with commas — visually distinct from the bracket literal syntax (which has no commas). List display follows the existing ADT display convention.

Seq display forces up to 20 elements, showing `+more` for longer/infinite sequences:

```
cranelisp> (take 5 (range-from 0))
(seq 0 1 2 3 4) :: (Seq Int)

cranelisp> (range-from 0)
(seq 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 ... +more) :: (Seq Int)

cranelisp> SeqNil
SeqNil :: (Seq a)

cranelisp> SeqCons
SeqCons :: (fn [a (Fn [] (Seq a))] (Seq a))
```

## Limitations and Future Extensions

| Limitation | When addressed |
|---|---|
| No cycle collection | When/if mutable references are added (reference cycles cannot form without mutation) |
| No TCO — List recursion overflows | Separate TCO feature; hard prerequisite for Phase 4 |
| No HKT — can't express Functor generically | Major type system extension |
| No linear/uniqueness types — COW is runtime-only | Future type system extension |
| Vec is built-in — can't define Vec-like types in user code | When raw memory primitives exist |
| No Seq memoization — thunks re-evaluate on each force | When caching infrastructure is added |
| No TCO for Seq consumers — `lazy-reduce`, `to-list` etc. overflow on large Seqs | Separate TCO feature |
| Vec COW deferred — always copies on vec-set/vec-push | When function argument RC (inc on call) or liveness analysis is added |
| No quote syntax / tuples | Deferred — see Tuples section above |
| Match scrutinee not dec'd after match completes | Future (match arm var patterns inc but original ref leaks) |
| Closure drop glue — captured heap values not dec'd | Future (closures don't encode captured value types) |
| Function argument lifetime — heap args not dec'd by callee | Future (callee vs caller responsibility) |
