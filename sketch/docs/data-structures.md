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
| Closure | `[code_ptr \| drop_ptr \| cap0 \| ...]` |
| ADT data ctor | `[tag \| field0 \| ...]` |

To access the rc header: `load [ptr - 8]` / `store [ptr - 8]`.

Values that remain as bare i64 (no header):
- Scalars: Int, Bool, Float (bitcast f64)
- Nullary ADT constructors: bare i64 tag (0, 1, 2, ...)

Initial refcount is 1 on allocation. This is the natural "one owner" state — the binding that receives the freshly allocated value.

## Compiler-Inserted Inc/Dec

Reference counting is invisible to the user — the compiler inserts all `inc` and `dec` operations.

### Calling Convention: Split Convention (Consuming + Borrowed)

Two calling conventions coexist, classified at compile time by call site:

**Consuming convention** (cranelisp-to-cranelisp calls):
The callee **owns** all heap-typed parameters — they are tracked in `scope_stack` and dec'd at scope exit via `pop_scope_for_value(result)`. The caller prepares arguments via `emit_consuming_caller_rc`:
- **Var at last-use and in scope_stack** → `mark_consumed` (transfer ownership, skip scope-exit dec on caller side)
- **Var not at last-use, or capture variable** → `emit_inc` (callee's scope-exit dec won't destroy caller's ref)
- **Temp expression** → nothing (callee takes ownership of rc=1 value)

Capture variables (loaded from closure env, not in `scope_stack`) are never eligible for last-use transfer — the closure env holds an implicit reference that drop glue will dec.

Accessor extraction (product and sum type field access) emits `emit_inc` on heap-typed field results, creating an owning reference independent of the parent ADT (which will be dec'd at callee scope exit).

Consuming call sites: `TraitMethod`, `SigDispatch`, known top-level fn, closure call.

**Borrowed convention** (extern/platform calls):
Extern callees do not track params. After the call, `emit_post_call_rc` decs **all heap-typed temporary** (non-Var) args, guarded against the result value. This is safe because extern functions don't extract sub-components via cranelisp ADT layout.

Borrowed call sites: `BuiltinFn` via `builtin_methods`, `BuiltinFn` via module entry, operator wrapper.

Platform functions that capture cranelisp values in Effect closures use `CLOwned<T>` (from the platform crate) to inc the RC on capture and dec on drop, ensuring the value survives the caller-side dec.

### Rules

**Increment** (refcount += 1):
- Assign to a new binding: `(let [y x] ...)` — inc `x`
- Capture in a closure: `(fn [a] (+ a x))` — inc `x` when closure is allocated
- Store into a container: `(vec-push xs x)` — inc `x`
- Store Var arg in constructor: `(Some x)` — inc `x` (constructor holds a separate reference)
- Match var pattern: `(match scrut [(Some s) ...])` — inc extracted field value
- Consuming call with non-last-use Var: callee takes ownership, caller inc's to keep its own ref
- Accessor extraction: `(field_name adt_value)` — inc heap-typed field result

**Decrement** (refcount -= 1):
- Scope exit: when a let binding goes out of scope, dec the value
- Function return: dec all local bindings except the return value (includes params under consuming convention)
- Closure drop: when a closure's refcount hits 0, dec all captured values via drop glue
- Container drop: when a Vec/List refcount hits 0, dec all elements
- Match merge: when a temporary (non-Var) scrutinee exits the match, dec it
- Extern call cleanup: `emit_post_call_rc` decs all heap-typed temps after borrowed calls

### Monomorphisation advantage

Because cranelisp monomorphises all constrained polymorphic functions, the compiler always knows the concrete type at every `inc`/`dec` site. This means:
- No runtime type tags needed for refcounting
- `inc` on an `Int` is a no-op (not heap-allocated) — the compiler statically elides it
- `inc` on a `String` generates a heap load+add+store — the compiler statically emits it
- Per-type drop functions for ADTs recursively dec heap-pointer fields

### Codegen patterns

Since `ptr` points past the header, rc is accessed at `ptr - 8`. All inc/dec operations use atomic read-modify-write instructions for thread safety with `par-let`/`par-bind!`:

```
inc(ptr):    rc_addr = isub ptr, 8
             atomic_rmw Add rc_addr, 1     ; atomically: rc += 1

dec(ptr):    rc_addr = isub ptr, 8
             old_rc = atomic_rmw Sub rc_addr, 1  ; atomically: rc -= 1, returns old value
             brif old_rc == 1, free_block, cont_block
  free_block:  <drop fields via drop glue>
               call cranelisp_free(ptr)
               jump cont_block
```

For ADT types with mixed nullary/data constructors, a runtime guard skips inc/dec when the value is a bare nullary tag (small integer, not a heap pointer): `if ptr < 1024 then skip`.

For closures (`Type::Fn`), the dec path performs runtime dispatch via the closure's `drop_ptr` field (see Closure Layout in `docs/closures.md`).

### Scope and current status (Sub-Phases 2A-2F + Step 11 complete)

The RC system was implemented in six sub-phases (2A-2F) and then hardened with Step 11 (Sound Memory Management):

- **2A** (done): `alloc_with_rc()` allocates `size + 16` bytes, stores total size at `base+0`, rc=1 at `base+8`, returns `base+16`. All existing payload offsets unchanged.
- **2B** (done): Expression type map (`expr_types: HashMap<Span, Type>`) threaded from typechecker through codegen. `FnCompiler` has `variable_types` tracking.
- **2C** (done): `emit_inc()` and `emit_dec()` methods on `FnCompiler` with inline Cranelift IR. `HeapCategory` enum classifies types as NeverHeap/AlwaysHeap/Mixed. Inc inserted at closure captures and let-binding variable aliases.
- **2D** (done): Scope-level dec via `scope_stack: Vec<Vec<(String, Variable, Type)>>` on FnCompiler. `push_scope()` / `pop_scope_for_value(result)` emit dec for each binding in the scope, using runtime value comparison to skip the return value. Applied to let scopes, match arm scopes, lambda return, and do intermediate cleanup.
- **2E** (done): Per-type drop functions generated at compile time. `resolve_drop_fn()` lazily generates Cranelift functions that load heap-typed fields from ADT constructors and recursively dec them before freeing. Handles recursive types (e.g., List) via pre-caching FuncId before building body. `drop_fn_cache: HashMap<String, FuncId>` on FnCompiler.
- **2F** (done): Real deallocation. Header expanded from 8 to 16 bytes (`[size | rc | payload]`). `free()` reads total_size from `ptr - 16`, reconstructs layout, calls `std::alloc::dealloc`. Diagnostic counters (`ALLOC_COUNT`, `DEALLOC_COUNT`) for testing. REPL `/mem` command shows allocation stats.
- **11A-E** (done): Core RC model — match scrutinee dec, constructor Var arg inc, closure drop glue with per-lambda drop functions, atomic inc/dec for par-let/par-bind!.
- **11F** (done): Caller-side temp cleanup — `CLOwned<T>` in platform crate for Effect closure captures.
- **11I** (done): Consuming calling convention — cranelisp-to-cranelisp calls use consuming convention (callee owns heap-typed params, tracked in `scope_stack`). `emit_consuming_caller_rc` handles caller-side arg preparation (last-use transfer for scope_stack vars, inc for non-last-use/captures, nothing for temps). Extern/platform calls use borrowed convention with `emit_post_call_rc` deccing all heap-typed temps. Accessor extraction inc's heap-typed field results. Capture variables (not in `scope_stack`) are never eligible for last-use transfer.
- **11G** (done): Liveness-based last-use optimization — `src/liveness.rs` computes which Var references are the last use of their binding in evaluation order. At two codegen sites (let Var alias, constructor Var arg), when a variable is at its last use in straight-line code (`branch_depth == 0`), ownership transfers instead of copying: the inc is skipped and the variable is marked consumed so scope-exit dec is also skipped. Net savings: 2 RC operations per occurrence. Conservative in branches (if/match arms increment `branch_depth`, disabling the optimization). Uses `Variable::as_u32()` as key for `consumed_vars: HashSet<u32>`.

- **11H** (done): Vec element RC + COW — `vec-get`, `vec-set`, `vec-push` are compiled inline (not extern calls) by `src/codegen/vec_ops.rs`. `vec-get` emits bounds check + element load + `emit_inc` (caller gets a new reference). `vec-set` and `vec-push` implement COW: when `is_last_use(vec_arg)` and runtime `rc==1`, mutate in place (dec old element, store new); when shared, call new `vec-set-rc`/`vec-push-rc` Rust externs that receive an element inc function pointer for copied elements. Per-element-type standalone inc functions (like drop fns) are generated and cached in `vec_elem_inc_cache`. New value RC follows the constructor Var arg pattern (last-use → ownership transfer, not-last-use → inc). `vec-push` COW also handles capacity growth via `vec-push-cow-grow` extern.
- **11J-L** (done): Uniqueness tracking + borrowed reads + static COW. See the "Uniqueness and Borrowed Reads" section below.

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

Vec operations use a hybrid inline codegen + extern fallback approach (`src/codegen/vec_ops.rs`):

**Inline (compiled as Cranelift IR):**
- `vec-get` — bounds check, load element from data buffer, `emit_inc` for heap-typed elements (caller gets a new reference)
- `vec-set` COW path — when `is_last_use(vec_arg)` + runtime `rc==1`: dec old element, store new value, return same Vec
- `vec-push` COW path — when `is_last_use(vec_arg)` + runtime `rc==1`: store at `data[len]`, update len; if capacity exhausted, call `vec-push-cow-grow`

**Extern fallback (Rust functions in `primitives/vec.rs`):**
- `vec-set-rc(vec_ptr, index, val, inc_fn)` — allocates new Vec, copies elements with per-element RC inc via function pointer
- `vec-push-rc(vec_ptr, val, inc_fn)` — allocates new Vec with appended element, copies with per-element RC inc
- `vec-push-cow-grow(vec_ptr, val)` — reallocs data buffer when COW push exhausts capacity (doubles capacity, raw memcpy)
- `vec-len(vec_ptr)` — loads length field (remains a simple extern call)

**Element inc function pointers:**
Per-element-type standalone Cranelift functions (like drop fns) are generated and cached in `vec_elem_inc_cache`. For `AlwaysHeap` types: atomic inc at `val-8`. For `Mixed` types: guard `val < 1024` (nullary tag), then atomic inc. For `NeverHeap` types: `null` pointer (externs skip the call).

**New value RC:**
Same pattern as constructor Var arg inc (apply.rs:66-83): Var + last-use → mark consumed (ownership transfers to Vec); Var + not-last-use → emit_inc (Vec gets a new reference); temp expression → nothing (fresh rc=1 transfers).

### Copy-on-write

`vec-set` and `vec-push` use a two-level COW check:

1. **Compile-time**: `is_last_use(vec_arg)` — liveness analysis determines if this is the last use of the Vec variable in evaluation order (straight-line code only, disabled in branches)
2. **Runtime**: `rc == 1` — the Vec header's reference count confirms sole ownership

When both checks pass, the operation mutates in place:
- `vec-set`: dec the old element at the index, store the new value, return the same Vec pointer
- `vec-push`: store at `data[len]`, increment len; if `len >= cap`, call `vec-push-cow-grow` to realloc the data buffer

When either check fails, the copy path allocates a new Vec and calls `vec-set-rc` / `vec-push-rc`, which copy all elements with per-element RC inc via the function pointer.

For last-use Vecs that take the copy path (runtime `rc > 1`): the caller's consumed reference to the old Vec is dec'd after the copy.

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

## Uniqueness and Borrowed Reads (Steps 11J-L)

### Problem

Every field read (ADT accessor, vec-get, match extraction) emits an atomic inc on the extracted value and an atomic dec at scope exit. This means **every read causes two atomic writes** — expensive, and worse, it bumps the element's RC from 1→2, **defeating COW** (copy-on-write) optimizations.

### Solution: Uniqueness Tracking

`FnCompiler` tracks three sets keyed by `Variable::as_u32()`:

- **`unique_vars`**: Variables known to be the sole owner (rc==1). Marked unique when:
  - Consuming function parameter (callee is sole owner)
  - Fresh heap allocation bound in `let` (constructor, string/vec literal, closure, function call result)
  - Last-use transfer from a unique source (let Var alias)
  - Removed when `emit_inc` is called (another reference created)

- **`borrowed_vars`**: Let-bound variables holding borrowed values (skip scope-exit dec). Created when a borrowed read is let-bound.

- **`borrowed_temps`**: Temp Values from inline reads not bound via `let` (skip post-call dec in `emit_post_call_rc`). Created at ADT accessor and vec-get sites.

### Borrowed Reads

When reading a field from a **unique** owner at `branch_depth == 0`:

1. **ADT accessor** (`apply.rs`): Skip `emit_inc`, mark result as `borrowed_temp`
2. **Vec-get** (`vec_ops.rs`): Skip `emit_inc` for heap-typed elements, mark as `borrowed_temp`
3. **Match field extraction** (`match_compile.rs`): Skip `emit_inc`, mark as `borrowed_var`

Borrowed values skip dec at scope exit (`pop_scope_for_value`) and TCO cleanup (`emit_scope_cleanup_for_tco`). Borrowed temps skip dec in `emit_post_call_rc`.

### Auto-Upgrade: Borrowed → Owned

When a borrowed value **escapes** its owner's scope, an inc is emitted to create an independent reference:

- **Returned as result**: `pop_scope_for_value` checks if the result is a borrowed temp/var
- **Passed to consuming call**: `emit_consuming_caller_rc` emits inc for borrowed args
- **Stored in constructor**: Constructor arg RC loop emits inc for borrowed vars
- **Used as TCO arg**: `compile_tail_self_call` emits inc before scope cleanup

### Static COW (Step 11L)

When `vec-set` or `vec-push` targets a known-unique Vec AND last-use, the runtime `rc==1` check is skipped entirely — the compiler statically knows the Vec is unique. This eliminates the `atomic_rmw` load + branch for the COW decision.

Three-level COW:

1. **Static COW** (compile-time): `is_last_use(vec_arg) && is_var_unique(name)` → mutate in place unconditionally
2. **Runtime COW** (compile-time + runtime): `is_last_use(vec_arg) && runtime rc==1` → mutate in place
3. **Copy** (always safe): Allocate new Vec, copy elements with per-element inc

### Conservative Limitations

- **No borrows in branches**: `branch_depth > 0` disables uniqueness-based optimizations (if/match arms might not execute)
- **TCO loses uniqueness**: Parameters are marked unique on function entry but uniqueness is not re-established between TCO iterations. A non-last-use inc in the body removes uniqueness permanently.
- **Only Var owners**: Borrowed reads require the owner to be a named variable (not a temp expression), since uniqueness is tracked by variable.

### Performance Impact

For a typical `reduce` with Vec accumulator reading elements from a unique container:
- **Before**: 2 atomic writes per element read (inc + dec), plus 1 atomic_rmw for COW check
- **After**: 0 atomic writes per element read (borrowed), 0 for COW (static)
- **Savings**: ~67% reduction in atomic operations for read-heavy loops

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
| ~~Vec COW deferred — always copies on vec-set/vec-push~~ | Done — inline COW with liveness + runtime rc==1 check (Step 11H) |
| ~~Vec element RC in copies — heap-typed elements not inc/dec'd~~ | Done — inline codegen with per-element inc fn pointers (Step 11H) |
| No quote syntax / tuples | Deferred — see Tuples section above |
| Temporary compound arg leak | String temps dec'd; ADT/closure temps not dec'd (sub-component aliasing) |
