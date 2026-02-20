# Codify Heap Object Layouts as Complete `#[repr(C)]` Structs

## Context

Heap object layouts are expressed as magic offset numbers scattered across ~50 sites. The header (size + rc) lives before the payload pointer, requiring negative offsets (`ptr - 8` for RC). This plan replaces the hack with clean `#[repr(C)]` structs that include the header, making all offsets positive and derived from struct layout. It also introduces codegen emit helpers so representation changes (e.g., Vec becoming a persistent trie) are contained to three files.

**ABI change**: `alloc` returns a base pointer (start of struct), not a payload pointer. `free` receives a base pointer. All offsets become positive.

## Data structure name

The persistent Vec design (cache-line pages, bitfield discriminating data vs sub-pages, per-page RC, structural sharing) is a **persistent array mapped trie** (Bagwell/Hickey family, same as Clojure's `PersistentVector`). The bitfield variant is a **CHAMP** (Compressed Hash-Array Mapped Prefix-tree).

## Architecture

### Layer 1: `src/layout.rs` — Full `#[repr(C)]` struct types

All offsets derived via `std::mem::offset_of!` — tied directly to struct fields, no manual arithmetic.

```rust
use std::mem::{self, offset_of};

#[repr(C)]
pub struct HeapHeader {
    pub alloc_size: i64,
    pub rc: i64,
}

impl HeapHeader {
    pub const SIZE: usize = mem::size_of::<Self>();
    pub const ALLOC_SIZE_OFFSET: i32 = offset_of!(Self, alloc_size) as i32; // 0
    pub const RC_OFFSET: i32 = offset_of!(Self, rc) as i32;                 // 8
}

/// Complete heap string: [alloc_size | rc | len | bytes...]
#[repr(C)]
pub struct HeapString {
    pub header: HeapHeader,
    pub len: i64,
}

impl HeapString {
    pub const LEN_OFFSET: i32 = offset_of!(Self, len) as i32;       // 16
    pub const DATA_OFFSET: i32 = mem::size_of::<Self>() as i32;     // 24 (bytes follow struct)
    pub const fn payload_size(byte_len: usize) -> usize {
        mem::size_of::<i64>() + byte_len  // len field + bytes
    }
}

/// Complete heap vec: [alloc_size | rc | len | cap | data_ptr]
#[repr(C)]
pub struct HeapVec {
    pub header: HeapHeader,
    pub len: i64,
    pub cap: i64,
    pub data_ptr: i64,
}

impl HeapVec {
    pub const PAYLOAD_SIZE: usize = mem::size_of::<Self>() - HeapHeader::SIZE;
    pub const LEN_OFFSET: i32 = offset_of!(Self, len) as i32;          // 16
    pub const CAP_OFFSET: i32 = offset_of!(Self, cap) as i32;          // 24
    pub const DATA_PTR_OFFSET: i32 = offset_of!(Self, data_ptr) as i32; // 32
}

/// ADT fixed prefix: [alloc_size | rc | tag] + variable fields
#[repr(C)]
pub struct HeapAdt {
    pub header: HeapHeader,
    pub tag: i64,
}

impl HeapAdt {
    pub const TAG_OFFSET: i32 = offset_of!(Self, tag) as i32;          // 16
    pub const FIELDS_START: usize = mem::size_of::<Self>();             // 24
    pub const fn field_offset(i: usize) -> i32 {
        (Self::FIELDS_START + i * mem::size_of::<i64>()) as i32
    }
    pub const fn payload_size(field_count: usize) -> usize {
        mem::size_of::<i64>() + field_count * mem::size_of::<i64>()  // tag + fields
    }
}

/// Closure fixed prefix: [alloc_size | rc | code_ptr] + variable captures
#[repr(C)]
pub struct HeapClosure {
    pub header: HeapHeader,
    pub code_ptr: i64,
}

impl HeapClosure {
    pub const CODE_PTR_OFFSET: i32 = offset_of!(Self, code_ptr) as i32; // 16
    pub const CAPTURES_START: usize = mem::size_of::<Self>();            // 24
    pub const fn capture_offset(i: usize) -> i32 {
        (Self::CAPTURES_START + i * mem::size_of::<i64>()) as i32
    }
    pub const fn payload_size(capture_count: usize) -> usize {
        mem::size_of::<i64>() + capture_count * mem::size_of::<i64>()  // code_ptr + captures
    }
}
```

Compile-time assertions verify `offset_of!` produces expected values:
```rust
const _: () = assert!(HeapHeader::SIZE == 16);
const _: () = assert!(HeapHeader::RC_OFFSET == 8);
const _: () = assert!(HeapString::LEN_OFFSET == 16);
const _: () = assert!(HeapString::DATA_OFFSET == 24);
const _: () = assert!(HeapVec::LEN_OFFSET == 16);
const _: () = assert!(HeapVec::DATA_PTR_OFFSET == 32);
const _: () = assert!(HeapAdt::TAG_OFFSET == 16);
const _: () = assert!(HeapAdt::FIELDS_START == 24);
const _: () = assert!(HeapClosure::CODE_PTR_OFFSET == 16);
const _: () = assert!(HeapClosure::CAPTURES_START == 24);
const _: () = assert!(mem::align_of::<HeapVec>() == 8);
```

### Layer 2: `src/codegen/emit.rs` — Codegen emit helpers

**Generic heap access** (free functions — work in both FnCompiler and drop fn contexts):
```rust
pub fn heap_load(builder: &mut FunctionBuilder, ptr: Value, offset: i32) -> Value {
    builder.ins().load(types::I64, MemFlags::trusted(), ptr, offset)
}
pub fn heap_store(builder: &mut FunctionBuilder, val: Value, ptr: Value, offset: i32) {
    builder.ins().store(MemFlags::trusted(), val, ptr, offset);
}
```

Callers combine these with layout constants — the type knowledge is in the offset, not the load:
```rust
let tag = heap_load(&mut builder, ptr, HeapAdt::TAG_OFFSET);
let field = heap_load(&mut builder, ptr, HeapAdt::field_offset(i));
let rc = heap_load(&mut builder, ptr, HeapHeader::RC_OFFSET);
heap_store(&mut builder, new_rc, ptr, HeapHeader::RC_OFFSET);
```

**Future-ready**: when field types become variable-size, `heap_load` gains a `ty: types::Type` parameter — one function changes.

**Per-type construction methods** (on FnCompiler — need `self.compile_alloc`):
- `emit_string_alloc(&mut self, bytes: &[u8], span) -> Result<Value>` — alloc + store len + store bytes
- `emit_adt_alloc(&mut self, tag: i64, field_vals: &[Value], span) -> Result<Value>` — alloc + store tag + fields
- `emit_closure_alloc(&mut self, code_ptr: Value, captures: &[Value], span) -> Result<Value>` — alloc + store code_ptr + captures
- `emit_vec_header_alloc(&mut self, len: Value, cap: Value, data_ptr: Value, span) -> Result<Value>` — alloc + store fields

These compose `heap_store` with layout constants internally. They are the **only** codegen code that imports from `layout.rs`.

### How this contains a Vec representation change

If Vec becomes a persistent array trie:
1. `layout.rs`: `HeapVec` struct changes to describe trie root node
2. `codegen/emit.rs`: `emit_vec_header_alloc` emits runtime call instead of inline stores; `vec_len_load` emits call to `cranelisp_vec_len`
3. `primitives/vec.rs`: implements trie traversal + path copying, uses new `HeapVec` struct
4. **Nothing else changes**

### Future: trait/enum strategy

If pluggable representations are needed later, emit helpers promote to trait methods returning a strategy enum:
```rust
enum FieldAccess { InlineLoad { offset: i32 }, RuntimeCall { symbol: &'static str } }
```

## Implementation Steps

### Step 1: Create `src/layout.rs` and `src/codegen/emit.rs`
- Add `pub mod layout;` to `src/lib.rs`
- Create layout.rs with full structs, constants, compile-time assertions
- Create `codegen/emit.rs` with emit helper functions
- Add `pub(crate) mod emit;` to `src/codegen/mod.rs`
- `just test` to verify compilation

### Step 2: Change alloc/free ABI (`src/intrinsics.rs`)
- `alloc_with_rc(payload_size)`: still takes payload_size, adds `HeapHeader::SIZE` internally, writes header via `*mut HeapHeader` cast, returns **base pointer** (not `base.add(16)`)
- `alloc(size) -> i64`: returns base pointer
- `free(ptr)`: receives base pointer, reads `alloc_size` at offset 0 (no more `ptr.sub(16)`), deallocates
- `LIVE_ALLOCS`: tracks base pointers
- `panic`: string read via `*const HeapString` cast with new offsets
- `just test` — **tests will break here** because all other code still expects payload pointers; continue immediately to Steps 3-4

### Step 3: Wire up emit helpers in codegen (all at once — ABI change)
Must update all codegen together since the pointer meaning changed:

**`codegen/mod.rs`** (~14 sites):
- RC inc/dec: `val, -8` -> `heap_load/heap_store(builder, ptr, HeapHeader::RC_OFFSET)`
- ADT drop: tag/field loads via `heap_load(builder, ptr, HeapAdt::TAG_OFFSET)` and `heap_load(builder, ptr, HeapAdt::field_offset(fi))`
- Vec drop: `heap_load(builder, ptr, HeapVec::LEN_OFFSET)`, `heap_load(builder, ptr, HeapVec::DATA_PTR_OFFSET)`

**`codegen/expr.rs`** (~7 sites):
- StringLit: entire alloc+store sequence -> `self.emit_string_alloc(bytes, span)`
- Vec literal: header alloc+stores -> `self.emit_vec_header_alloc(len, cap, data_ptr, span)`

**`codegen/apply.rs`** (~12 sites):
- ADT constructor -> `self.emit_adt_alloc(tag, &fields, span)`
- Accessor loads -> `heap_load(builder, ptr, HeapAdt::field_offset(i))`, tag via `HeapAdt::TAG_OFFSET`
- Closure call -> `heap_load(builder, ptr, HeapClosure::CODE_PTR_OFFSET)`
- Panic strings -> `self.emit_string_alloc`

**`codegen/closures.rs`** (~15 sites):
- Lambda -> `self.emit_closure_alloc` for construction, `heap_load(builder, ptr, HeapClosure::capture_offset(i))` for loads
- Constructor-as-closure -> `self.emit_adt_alloc`
- Accessor-as-closure -> `heap_load` with `HeapAdt::` offsets
- Auto-curry -> `heap_load/heap_store` with `HeapClosure::` offsets

**`codegen/match_compile.rs`** (~6 sites):
- Tag/field loads -> `heap_load` with `HeapAdt::TAG_OFFSET` / `HeapAdt::field_offset(fi)`
- Panic string -> `self.emit_string_alloc`

### Step 4: Wire up layout types in Rust-side code (all at once — ABI change)

**`src/primitives/vec.rs`** (~20 sites):
- Cast `ptr as *const HeapVec` / `*mut HeapVec`, access `.len`/`.cap`/`.data_ptr`
- Closure code_ptr: cast to `*const HeapClosure`, read `.code_ptr` field

**`src/primitives/mod.rs`** (3 sites):
- `alloc_string`: payload size via `HeapString::payload_size()`, write len/bytes via struct offsets

**`src/primitives/string.rs`** (4 sites):
- `parse_int`: cast to `*const HeapString`, read `.len` and bytes at `HeapString::DATA_OFFSET`
- ADT for `Some(n)`: use `HeapAdt::payload_size(1)`

**`src/platform.rs`** (2 sites):
- `print_string`: cast to `*const HeapString`, read fields

**`src/marshal.rs`** (~8 sites):
- String/ADT reads via layout structs and named offsets

### Step 5: Documentation
- `docs/architecture.md` — add `layout.rs` to module map
- `docs/codegen.md` — document new heap layout (all positive offsets from base pointer)
- `docs/data-structures.md` — update heap layout diagrams
- `src/CLAUDE.md` — update "All types -> i64" note to mention layout.rs
- `ROADMAP.md` — note progress

### Step 6: Post-implementation sweep
Grep for remaining magic numbers:
- `- 8`, `+ 8`, `- 16`, `+ 16` in pointer arithmetic contexts
- `.add(1)`, `.add(2)` in struct field access (should now be struct field access)
- `* 8)` in ADT/closure field computations
- Literal `24` for vec size, `16` for header size

## Verification
- `just test` — all tests pass
- `just check` — clippy clean
- `just hello` and `just factorial` — end-to-end runs
- Grep sweep confirms no remaining magic offset numbers
- No negative offsets anywhere in codebase
