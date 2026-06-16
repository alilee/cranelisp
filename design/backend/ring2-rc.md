# Ring 2 Reference Counting Design

## Overview

Ring 2 activates the RC scaffolding laid down in Ring 1 (see `ring1-codegen.md` for foundation). It implements automatic memory management for all heap-allocated values: Strings, ADTs with data constructors, closures (Fn types), and Vecs. The key contribution is the **uniform consuming calling convention** (Decision 24) — every call site compiles identically for RC management, with the callee responsible for dec'ing heap parameters it does not return — plus the **scope cleanup** protocol that ensures no leaks on function exit.

This document is the authoritative reference for Ring 3 implementers. If you are compiling functions (macros, auto-curry wrappers, trace instrumentation), you must follow these conventions exactly or introduce leaks or use-after-free.

## 1. Heap Layout

All heap objects share a common header defined in `cranelisp-types::HeapHeader`:

```
Offset 0:  alloc_size  (i64)   -- total bytes (header + payload)
Offset 8:  rc          (i64)   -- reference count, initial = 1
Offset 16: ... payload ...
```

**Base-pointer convention**: pointers point to offset 0 (where `alloc_size` lives). All field accesses use positive offsets from the base. This is enforced by the representation containment rule: only `heap.rs` may import layout constants. All other codegen code calls `heap_load`, `heap_store`, `emit_alloc`, `emit_rc_inc`, `emit_rc_dec`.

### 1.1 HeapHeader (cranelisp-types)

```rust
#[repr(C)]
pub struct HeapHeader {
    pub alloc_size: i64,   // ALLOC_SIZE_OFFSET = 0
    pub rc: i64,           // RC_OFFSET = 8
}
// HeapHeader::SIZE = 16
```

### 1.2 HeapAdt (cranelisp-backend)

ADT data constructors (values with at least one field):

```
[header(16) | tag(8) | field_0(8) | field_1(8) | ... | field_n(8)]
 ^-- base pointer
```

- `TAG_OFFSET = 16`
- `FIELDS_START = 24`
- `field_offset(i) = 24 + i * 8`
- `payload_size(n_fields) = 8 + n_fields * 8`

Nullary constructors (e.g., `None`, `Red`) are **not** heap-allocated. They are bare i64 tags (0, 1, 2, ...). This means a value of a Mixed ADT type (e.g., `Option`) might be either a bare tag or a heap pointer. The `NULLARY_TAG_THRESHOLD` constant (1024) discriminates: values below the threshold are bare tags; values at or above are heap pointers.

### 1.3 HeapClosure (cranelisp-backend)

Closures carry a drop glue pointer embedded in the struct:

```
[header(16) | code_ptr(8) | drop_glue_ptr(8) | cap_0(8) | ... | cap_n(8)]
 ^-- base pointer
```

- `CODE_PTR_OFFSET = 16`
- `DROP_GLUE_PTR_OFFSET = 24`
- `CAPTURES_START = 32`
- `capture_offset(i) = 32 + i * 8`
- `payload_size(n_captures) = 16 + n_captures * 8`

The `drop_glue_ptr` is 0 when no captures are heap-typed. When non-zero, it points to a JIT-compiled function `(closure_ptr: i64) -> ()` that dec's each heap-typed capture before the closure itself is freed.

### 1.4 HeapVec (cranelisp-backend)

Vecs use a two-allocation design:

```
Vec struct: [header(16) | len(8) | cap(8) | data_ptr(8)]   = 40 bytes
Data buffer: [elem_0(8) | elem_1(8) | ... | elem_{cap-1}(8)]  (plain allocation, no header)
```

- `LEN_OFFSET = 16`
- `CAP_OFFSET = 24`
- `DATA_PTR_OFFSET = 32`

Only the Vec struct has an RC header. The data buffer is a plain `alloc`/`dealloc` allocation. `vec_drop` frees both the data buffer and the Vec struct.

### 1.5 HeapCategory

The `HeapCategory` enum classifies types for RC decisions:

| Category | Types | RC treatment |
|---|---|---|
| `NeverHeap` | Int, Bool, Float, pure-enum ADTs | No RC ops |
| `AlwaysHeap` | String, Fn, ADTs with only data constructors, Vec | Unconditional inc/dec |
| `Mixed` | ADTs with both nullary and data constructors (e.g., Option) | Guarded inc/dec: skip if value < `NULLARY_TAG_THRESHOLD` |

`HeapCategory::classify(ty, type_defs)` is the single source of truth. When `type_defs` is available (after typechecking), classification is exact. Without it, ADTs conservatively classify as Mixed.

#### The two historical sources of `Mixed` — and their post-S84 disposition

`classify` has, historically, returned `Mixed` for **two structurally distinct reasons**, collapsed into one verdict (the enum carries no discriminator):

1. **Legitimate, type-known nullary-tag discrimination.** A `Type::ADT(fqtn, _)` whose constructor set is genuinely mixed — some nullary (bare-tag), some data (heap pointer), e.g. `Option`. Here the `<1024` guard is **sound**: the type is known, the tags are bounded (`tag < NULLARY_TAG_THRESHOLD` by construction — nullary constructors get small sequential tags), and the runtime value really is *either* a bare tag *or* a heap pointer. The guard is the correct discriminator. (`classify_from_ctor_names` → `(true, true) => Mixed`, heap.rs ~552.)

2. **Unsound fallback from a non-concrete type.** The `Type::Var(_) | Type::TyConApp(_, _)` arm (heap.rs ~456), plus the conservative `Type::ADT`-without-tables / ADT-not-in-tables fallbacks (heap.rs ~485, ~491). Here `classify` has **no static knowledge** and guesses `Mixed`. On the `Type::Var` path the `<1024` guard is **unsound** (BC §3 invariant 9): a negative or `≥ 1024` `Int` flowing through a polymorphic position is misread as a heap pointer, and the dec path frees it — use-after-free. The guard's tag-vs-pointer dichotomy does not hold for an arbitrary monomorphic instantiation.

**The reasons are NOT separable at the RC-emission call sites.** Every guarded-RC site (7 `emit_rc_inc_guarded`, 8 `emit_rc_dec_guarded(guard_nullary=true)` — inventory in §1.6) follows the identical shape `match classify(ty, …) { … Mixed => guarded … }` and never re-inspects `ty` to ask *why* it was `Mixed`. The collapse is in the **verdict**, not in the inputs: the call sites all still hold the original `&Type`, so the distinction is **recoverable at `classify` itself** — reason (1) is exactly `matches!(ty, Type::ADT(..))` reaching the `(true,true)` arm; reason (2) is every other path that yields `Mixed`. This recoverability is what makes the S84 change a `classify`-local change, not a call-site rewrite (see §1.6).

**Post-S84 invariant (gated on FIXME 0374).** Once typecheck's Tier-2 full-monomorphisation-from-roots guarantees that **no `Type::Var` reaches codegen** (BC §2 + §3 invariant 9), reason (2)'s `Type::Var` path is *unreachable by construction*. The only surviving producer of `Mixed` is reason (1) — the type-known mixed ADT — for which the `<1024` guard is sound. `Mixed` then means exactly "a known ADT with both nullary and data constructors," nothing more. The table row above is already written to that target state (the "unresolved type vars" entry is struck).

### 1.6 S84 / FIXME 0375 — retire the unsound guard from the `Type::Var` path

**Gating (hard, directional — restated from BC §3 invariant 9 and /arch Phase-2 point 1).** This change is a **strict downstream of FIXME 0374** (typecheck Tier-2). It MUST NOT land before 0374 is green. Landing the panic (below) while a residual `Type::Var` can still reach codegen is **strictly worse** than today: today a residual `Type::Var` falls through to the (unsound-but-non-crashing) `Mixed` fallback; with the panic in place it would crash at codegen instead. The non-crashing fallback is the *operatively load-bearing* safety net that only total concreteness retires. In the S84 wave plan this is **Wave 2**, after Wave 1's 0374. The typecheck-side complement (the unconstrained-top-level-var **ambiguity error**, 0373 part ii, raised at the post-inference generalisation boundary) and this codegen-side assert together make a residual `Type::Var` at codegen structurally impossible (Principle 18 — enforce invariants structurally).

#### Change 1 — `classify(Type::Var)` becomes an assert/panic

The `Type::Var(_)` arm of `HeapCategory::classify` is no longer a silent `Mixed` fallback. A `Type::Var` reaching codegen classification is, post-0374, a **compiler bug** (concreteness is an upstream guarantee), so it must fail loud, not silently emit an unsound guard.

**Assert form (specification for /dev).** A bare `panic!` with a diagnostic that names the invariant, the violating type, and the upstream owner of the guarantee — so a future regression points the reader straight at typecheck, not at the backend:

```rust
Type::Var(_) => unreachable!(
    "HeapCategory::classify: Type::Var reached codegen heap-classification — \
     full monomorphisation (typecheck Tier-2, FIXME 0374 / BC §2) must make all \
     types concrete before the codegen boundary; a Type::Var here is a compiler \
     bug, not a fallback (BC §3 invariant 9). ty = {ty:?}"
);
```

Rationale for `unreachable!` over `debug_assert!`: the existing pre-codegen tripwire `Type::contains_var()` (cranelisp-types, used in `debug_assert!`) is *debug-only*; this arm is the **release-mode** structural backstop at the exact point where the unsound guard would otherwise be emitted. It must hold in release builds too (the use-after-free it guards against is a release-mode hazard). `unreachable!` panics in all build profiles and documents the "cannot happen" intent at the type level. Cost is nil on the hot path — it replaces an arm that is, post-0374, never taken.

**`Type::TyConApp` disposition.** The current arm is `Type::Var(_) | Type::TyConApp(_, _) => Mixed`. **Split the arm.** `TyConApp` is a separate question (a partially-applied type constructor at the HKT boundary; not a free var) and is NOT covered by 0374's concreteness guarantee in the same way. `/dev` must split: `Type::Var` → the `unreachable!` above; `Type::TyConApp(_, _)` → **keep** its current `Mixed` fallback for now, with a `// FIXME(0375): TyConApp concreteness is a separate question from Var; revisit if HKT codegen monomorphises through it` note. Folding `TyConApp` into the panic would be an over-reach beyond 0374's guarantee — flag this explicitly so /dev does not collapse both into the panic. If, during implementation, /dev finds `TyConApp` also cannot reach codegen post-0374, that is a follow-up (file `target: /typecheck` or `target: /arch`), not part of 0375.

#### Change 2 — retire the `<1024` guard from the `Type::Var`-originated path; KEEP it for nullary-tag ADT discrimination

The crux of 0375 is the **retire-vs-keep** split. State of the code (verified S84 Phase 3):

- **KEEP** — the guard's sound origin. The 15 guarded-RC call sites that fire on a `classify` verdict of `Mixed` derived from **reason (1)** — a `Type::ADT` that is genuinely mixed (`(has_nullary, has_data) == (true, true)`). These are the within-known-`Mixed`-ADT nullary-tag discriminators. They MUST keep the guard: at these sites the runtime value really is tag-or-pointer and the `<1024` test is the correct discriminator. The kept path is genuinely the **type-known / tags-bounded** case — confirmed: the `(true,true)` arm is only reachable from `classify_adt` → `classify_from_ctor_names`, both of which require a `Type::ADT(fqtn, _)` *and* a resolvable constructor set in the symbol tables; a `Type::Var` can never reach that arm.

- **RETIRE** — the guard on the `Type::Var`-originated path. Post-Change-1, this path **no longer produces a `Mixed` verdict at all** — it panics. Therefore the unsound guard is retired **by construction at its source**: with no `Mixed` flowing from `Type::Var`, no guarded-RC op is ever emitted for a `Type::Var`-originated value. There is no separate call-site edit required to "remove" the unsound guard — making `classify(Type::Var)` unreachable removes every downstream unsound `emit_rc_inc_guarded` / `emit_rc_dec_guarded` it would have fed.

**Are the two paths cleanly separable in the current code? YES — at `classify`, NOT at the call sites.** This is the key design finding. The call sites cannot tell the two `Mixed` reasons apart (they never re-inspect `ty`), but they do not need to: the separation lives entirely in `classify`'s arms. Reason (1) flows from the `Type::ADT` arms; reason (2)'s `Type::Var` sub-path is severed by Change 1. **No call-site refactor is required, and no new `HeapCategory` discriminator variant is needed.** The 15 guarded sites are unchanged — they keep firing for reason (1), and simply never receive a reason-(2) `Mixed` anymore. This is the minimal, containment-respecting form (Principle 6 — complexity has a budget; Principle 7 — single source of truth: the retire/keep decision stays inside the one `classify` SSOT, not scattered across 15 call sites).

**The remaining `Type::ADT`-without-tables / ADT-not-in-tables fallbacks (heap.rs ~485, ~491) stay `Mixed` — and that is correct.** They are reason-(2)-flavoured (conservative, no static knowledge), but they are NOT on the `Type::Var` path and are NOT made unsound by 0374: an ADT-without-tables `Mixed` value is still genuinely tag-or-pointer (it IS an ADT, just one whose ctor set we could not resolve at this call), so the `<1024` guard remains sound for it. 0375 does **not** touch these. (If a future audit shows tables are *always* present at codegen heap-classification — making these fallbacks themselves dead — that is a separate cleanup, not 0375.) Be exact: 0375 retires the guard from the **`Type::Var`** sub-path only, by making that sub-path panic; it does not touch the conservative-ADT fallbacks.

#### Testability — backend-seam unit tests (per the per-fix discipline)

Two backend unit tests in `heap.rs`'s `heap_category_tests` module pin the change at the seam where the bug lived (mandatory per `memory/feedback_unit_test_per_fix.md` — write failing-first, fix flips green, same change-set):

- **(a) The kept path still works — `Mixed` ADT still discriminates nullary tags.** The existing `test_mixed_adt_with_tables` already pins `classify(Option<Int>, Some(&tables)) == Mixed` (the `(true,true)` arm). Keep it; it is the regression guard that the *sound* `Mixed` path is intact after the `Type::Var` arm changes. No new positive test is strictly required, but /dev should add an explicit `// regression: kept path (0375)` annotation so the guard's role is legible. The `(true,true)`→`Mixed`→`emit_rc_*_guarded` chain is what must NOT break.

- **(b) The `Type::Var` arm now panics — the assert is the structural guard.** Replace the existing `test_var_mixed` (which asserts `classify(Type::Var(0), None) == Mixed`) with a `#[should_panic(expected = "Type::Var reached codegen")]` test asserting `classify::<(), ()>(&Type::Var(0), None)` panics. This is the negative/structural guard: it pins that a `Type::Var` is now rejected at the seam, not silently mis-classified. (Note: this test is **gated** — it must land in the same Wave-2 change-set as Change 1, after 0374; before 0374 it would be a true statement of an unsound behaviour and must not be asserted as desired. /qa and /dev coordinate the wave timing.)
- **`TyConApp` arm** — add/keep a test pinning `classify(Type::TyConApp(..), None) == Mixed` so the split (Change 1) is explicit and the `TyConApp` fallback is not accidentally swept into the panic.

#### Testability — e2e (coordinate with /qa)

An e2e is **warranted**. The original 0373 defect was a `--run` SIGSEGV (use-after-free on the unsound guard). The durable guard is the cross-mode concreteness e2e /qa authors sprint-wide in Wave 0 (Tier-2 mono concreteness + SIGSEGV-class repros across `--run`/`--link`/REPL — SPRINT.md §Waves Wave 0). 0375's specific e2e expectation: the previously-SIGSEGV-ing polymorphic-`Int`-through-a-`Mixed`-position repro **runs clean** under `--run` and `--link` once 0374 + 0375 land. This is /qa's to author (cross-skill: /backend names the expectation, /qa writes the test per the user-proxy/defect protocol). The unit test (b) is the backend-seam guard; the e2e is the end-to-end witness — they answer different questions (the panic-reachability at the seam vs. the absence of the runtime crash), so both are needed.

#### Risk

- **Premature landing (the gating risk).** If 0375 lands before 0374 is *fully* green, a residual `Type::Var` crashes at codegen. Mitigation: the wave ordering (Wave 2 strictly after Wave 1) plus the typecheck-side ambiguity error (0373 ii). /dev(backend) must confirm 0374's concreteness guard is green before merging Change 1 — the cheapest confirmation is that /qa's Wave-0 concreteness e2e (and the `Type::contains_var()` debug-assert) pass with Tier-2 in place.
- **Over-reach on `TyConApp`.** Folding `TyConApp` into the panic exceeds 0374's guarantee and would crash valid HKT codegen. Mitigation: the explicit arm-split instruction in Change 1.
- **No baseline move.** `classify` / `emit_rc_inc_guarded` / `emit_rc_dec_guarded` are backend-internal (`pub(crate)` / `pub` for in-crate intrinsics consumers, not boundary surface). No `crates/cranelisp-backend/public-api.txt` move expected, no BC §3 *shape* change (invariant 9 already states the retire direction in prose). Confirmed against /arch Phase-2 point 4.

## 2. Reference Counting Protocol

### 2.1 Atomic Operations

RC operations are emitted as **inline atomic instructions**, not extern function calls:

- **Increment** (`emit_rc_inc`): `atomic_rmw(Add, ptr + RC_OFFSET, 1)` with `MemFlags::trusted()`.
- **Decrement** (`emit_rc_dec`): `atomic_rmw(Sub, ptr + RC_OFFSET, 1)` with `MemFlags::trusted()`. The old value is compared to 1: if equal (last reference), an Acquire fence is emitted, optional drop glue is called, and `runtime/dealloc` frees the object.

The atomics use `MemFlags::trusted()` (Cranelift's ordering for single-threaded code with potential future multi-threaded extension). The Acquire fence on the free path ensures all prior writes to the object are visible before deallocation.

### 2.2 Guarded Operations

For `Mixed` types, guarded variants skip the RC operation entirely when the value is a bare nullary tag:

```
if value < NULLARY_TAG_THRESHOLD:
    skip (bare tag, not a heap pointer)
else:
    perform rc_inc / rc_dec
```

- `emit_rc_inc_guarded`: branches around the inc.
- `emit_rc_dec_guarded(guard_nullary=true)`: branches around the dec.

Post-S84 / FIXME 0375 (gated on Tier-2 monomorphisation), the guarded variants fire **only** for the type-known mixed-ADT path — reason (1) in §1.5. The unsound `Type::Var`-originated guard is retired at its source by making `classify(Type::Var)` panic (§1.6); guarded RC is no longer emitted for any value whose `Mixed` verdict came from a non-concrete type. The `<1024` discriminator is therefore sound everywhere it still fires: the value is provably tag-or-pointer.

### 2.3 When Inc Happens

An `rc_inc` is emitted whenever a new reference to a heap value is created:

1. **Consuming call arguments** (variable args): caller inc's before the call so the caller's binding survives the callee's dec.
2. **Closure capture**: each heap-typed capture is inc'd when stored into the closure env.
3. **Match field extraction**: when binding a field from a data constructor in a match arm, the field is inc'd to give the new binding its own reference.
4. **`vec-get` element read**: the loaded element is inc'd (it now has an independent reference outside the Vec).
5. **Return value protection**: `protect_return_value` inc's the body result before scope cleanup if the return value might alias a scope binding.

### 2.4 When Dec Happens

An `rc_dec` is emitted when a reference is released:

1. **Scope cleanup** (`pop_scope_with_cleanup`): at the end of a `let` body or function body, all heap-typed bindings are dec'd (except the return value). For user-defined functions, this includes all heap-typed parameters (the consuming convention).
2. **Callee-side extern dec**: extern primitives implemented in Rust (`str-concat`, `string-length`, Vec ops, Sexp marshaling, IO trampolines, etc.) dec any heap argument they do not return. This is part of the uniform consuming convention — there is no caller-side post-call temporary dec.
3. **Temporary closure callee**: after calling a closure expression (not a named variable), the closure is dec'd.
4. **Match scrutinee temporary**: if the scrutinee is a non-variable expression, it is dec'd after all arms have been compiled.
5. **Vec COW mutate-in-place**: the old element is dec'd before storing the new value.

### 2.5 What Triggers Free

When `rc_dec` brings the old RC to 1 (meaning it was the last reference):

1. **Acquire fence** to ensure write visibility.
2. **Drop glue** (if provided) is called to recursively dec any heap-typed sub-values.
3. **`runtime/dealloc`** reads `alloc_size` from offset 0 and frees the allocation.

## 3. Calling Convention

**Historical note**: Prior to Sprint 56 Step 2c, this section described a split convention (Decision 20, retracted) with three classifications — consuming for user functions, borrowing for builtins/externs, and none for data constructors — plus a caller-side `dec_temporary_args` helper. The current target is **Decision 24** — a uniform consuming convention applied to every call type. The split form is gone; data constructors are reclassified as consuming (the ADT inherits ownership of field values); extern primitives now dec their own heap arguments before return.

There is exactly one calling convention, applied identically to direct user-function calls, closure calls (named or temporary callee), trait method dispatch (user impls and primitive/extern impls), sig-dispatch, data constructors, inline builtin operators, Vec primitives, and every extern Rust function that takes heap arguments.

### 3.1 The Uniform Consuming Convention

**Protocol**:
1. **Caller** compiles args via `compile_consuming_arg_list`:
   - For each argument that is a variable reference (`Expr::Var`), check its type via `variable_types`. If heap-typed, emit `rc_inc` (or `rc_inc_guarded` for Mixed). This gives the callee its own reference to the caller's binding while preserving the caller-side binding. (Future optimisation: skip this inc when last-use analysis proves the variable is not reused after the call — direct transfer.)
   - For each argument that is a temporary expression (not a Var), no caller-side action is needed. The temporary starts at rc=1 from its allocation; ownership transfers to the callee.
2. **Callee** owns all heap parameters. It is responsible for dec'ing anything it does not return. The form of that dec depends on what the callee is:
   - **User-defined function**: `pop_scope_with_cleanup` at function exit dec's all heap-typed parameters (and let-bindings) except the return variable. This is automatic — the backend emits it for every user function.
   - **Extern Rust primitive**: the Rust implementation itself dec's its heap arguments before returning. See §3.3 Extern Consumption Audit.
   - **Data constructor**: the field-store implicitly consumes the argument (the new heap object holds the only reference to the transferred value; the ADT's own drop glue will dec each heap-typed field when the ADT itself reaches rc=0). The constructor emits no explicit dec because the dec happens later through the ADT's lifetime.
   - **Inline builtin operator**: operators whose operands are NeverHeap (integers, booleans, floats, comparison results) need no dec — there is nothing to free. Operators whose operands are heap-typed (e.g., a hypothetical string arithmetic) behave like externs: they dec their heap args inline before producing the result.
   - **Closure call**: the code pointer leads to a user function body, so `pop_scope_with_cleanup` in the target applies. When the closure callee is a temporary expression, the caller additionally dec's the closure value itself after the call (it was a one-shot temporary, not a named binding).

**Why this works**: With uniform consuming semantics, every heap-typed argument has exactly one dec responsibility — the callee. The caller's inc for variable args preserves the caller-side binding; the callee's dec matches it. Temporary args transfer rc=1 directly; the callee's dec releases them. There is no divergent code path, no attribute annotation on extern symbols, no `dec_temporary_args` post-call cleanup.

### 3.2 Variable-into-Constructor Ownership

Consider `(let [s "hello"] (Some s))`. At the `(Some s)` call site, `compile_consuming_arg_list` emits an `rc_inc` on `s` (it is a heap-typed Var). The constructor stores the string pointer as a field; the ADT now holds one reference. Two things now reference the string: the variable `s` (held by the enclosing `let` scope) and the `Some` ADT's field.

- The variable `s` is owned by its scope. When `s` goes out of scope, `pop_scope_with_cleanup` dec's it.
- The ADT `(Some s)` is itself a new heap allocation at rc=1. It is tracked by whatever scope or calling convention governs the ADT value. The ADT's drop glue will dec the field when the ADT reaches rc=0.

Between these two dec paths, the underlying string stays alive as long as either reference exists. If the ADT is later passed to a user function, the inc at *that* call site is on the ADT pointer itself.

For temporary-into-constructor (e.g. `(Some (str-concat a b))`): the temporary result of `str-concat` has rc=1, no caller-side inc is emitted (it is not a Var), and the field store transfers ownership directly to the ADT. No extra inc/dec is required.

### 3.3 Extern Consumption Audit (Sprint 56 Step 2c)

Under Decision 24, every extern primitive implemented in Rust that takes a heap argument MUST dec that argument before returning, unless the argument is returned unchanged (in which case ownership flows out through the return value) or stored in a runtime-owned structure that will outlive the call (in which case the extern has inc'd it and the caller's passed-in reference must not be dec'd by the extern — use the "retains" column).

The authoritative per-extern table is:

| Extern name | Crate/file | Heap arg(s) | Returns arg unchanged? | Retains arg? | Action (Sprint 56 Step 2c) |
|---|---|---|---|---|---|
| `str-concat` | runtime/string.rs | `a`, `b` (String) | No (returns new String) | No | **DONE**: dec both via `rc::consume_shallow` before return; caller uses `compile_consuming_arg_list` |
| `str-eq` | runtime/string.rs | `a`, `b` (String) | No (returns Bool) | No | **DONE**: dec both |
| `str-len` | runtime/string.rs | `s` (String) | No (returns Int) | No | **DONE**: dec |
| `string-identity` | runtime/string.rs | `s` (String) | Yes (returns same ptr after inc) | Yes (inc'd) | **DONE** (semantics-preserving): inc-and-return is already consuming — the returned pointer carries the caller's consumed reference plus a fresh inc. Caller uses `compile_arg_list` (no inc) because inc-and-return would double-up otherwise. |
| `substring` | runtime/string.rs | `s` | No (returns new String) | No | **DONE**: dec |
| `char-at` | runtime/string.rs | `s` | No (returns new String) | No | **DONE**: dec |
| `split` | runtime/string.rs | `s`, `sep` | No (returns Vec of Strings) | No | **DONE**: dec both |
| `join` | runtime/string.rs | `sep`, `vec` | No (returns new String) | No | **DONE**: `consume_shallow` on sep; `drop::consume_vec_of_string` on vec (walks String elements, frees data buffer, frees Vec struct). |
| `replace` | runtime/string.rs | `s`, `from`, `to` | No | No | **DONE**: dec all three |
| `trim` | runtime/string.rs | `s` | No | No | **DONE**: dec |
| `starts-with?` | runtime/string.rs | `s`, `prefix` | No | No | **DONE**: dec both |
| `ends-with?` | runtime/string.rs | `s`, `suffix` | No | No | **DONE**: dec both |
| `contains?` | runtime/string.rs | `s`, `needle` | No | No | **DONE**: dec both |
| `to-upper` | runtime/string.rs | `s` | No | No | **DONE**: dec |
| `to-lower` | runtime/string.rs | `s` | No | No | **DONE**: dec |
| `int-to-string` | runtime/primitives/int.rs | none (Int arg) | — | — | no heap arg |
| `float-to-string` | runtime/primitives/float.rs | none (Float bits) | — | — | no heap arg |
| `bool-to-string` | runtime/primitives/bool.rs | none (Bool arg) | — | — | no heap arg |
| `parse-int` | runtime/primitives/int.rs | `s` (String) | No (returns Option Int) | No | **DONE**: dec |
| `sconcat` | runtime/marshal.rs | `xs`, `ys` (SList) | Sometimes (ys if xs empty — inc'd) | Sometimes (ys deep inc; xs items shallow inc) | **DONE**: after building result (which shares items from xs and reuses ys as tail with deep inc), `drop::consume_slist` releases both inputs — on the last-ref path it recursively walks SCons nodes and Sexp heads. |
| `quote-sexp` | runtime/marshal.rs | `val` (Sexp) | No (returns new Sexp) | No | **DONE**: split into `quote_sexp` (extern entry — builds then `drop::consume_sexp(val)`) and `quote_sexp_build` (internal, non-consuming, used by `quote_slist` recursion since sub-items are owned by the parent SList). |
| `vec-len` | runtime/vec.rs | `vec` (Vec) | No (returns Int) | No | handled inline in vec codegen via `emit_vec_drop_if_temporary` (Vec-op caller handling — see below). Not routed through the extern-primitive consuming path. |
| `vec-set-copy` | runtime/vec.rs | `vec` | No (returns new Vec) | No | handled by caller (`emit_vec_drop_if_temporary`) — no change here; vec-codegen path is already correct |
| `vec-push-copy` | runtime/vec.rs | `vec` | No (returns new Vec) | No | handled by caller (`emit_vec_drop_if_temporary`) |
| `vec-push-grow` | runtime/vec.rs | `vec` | Yes (returns same pointer) | Yes (keeps ownership) | ok — mutation in place; semantically consuming-then-re-returning |
| `heap_alloc_string` | runtime/string.rs | none (raw bytes ptr, len) | — | — | no heap arg (raw, not a Cranelisp heap) |
| `string_read` | runtime/string.rs | `s` | out-params only, no return | borrowed for the call | ok — called from Rust side (ValueFormatter), not from JIT |
| `cranelisp_trace_name` | runtime/trace.rs | `trace` (Trace ADT) | No (returns field value) | No | **DONE**: inc the returned field (heap-typed — now has its own reference), then `drop::consume_trace_call` releases the Trace (walks sub-refs tname/tparams/tresult/tchildren on last ref). |
| `cranelisp_trace_params` | runtime/trace.rs | `trace` | No | No | **DONE**: same as cranelisp_trace_name |
| `cranelisp_trace_result` | runtime/trace.rs | `trace` | No | No | **DONE**: same as cranelisp_trace_name |
| `cranelisp_trace_children` | runtime/trace.rs | `trace` | No | No | **DONE**: same as cranelisp_trace_name |
| `cranelisp_trace_nanos` | runtime/trace.rs | `trace` | No | No | **DONE**: Int return — no inc; `drop::consume_trace_call` on the Trace. |
| `cranelisp_trace_first_child_nanos` | runtime/trace.rs | `trace` | No | No | **DONE**: Int return — no inc; `drop::consume_trace_call` on the Trace. |
| `cranelisp_run_io` | runtime/io.rs | `io_ast` (IO ADT) | No | No (evaluates to completion) | **TOP-LEVEL DONE**: after `run_io_trampoline` returns the final value, `drop::consume_io_tree(io_ptr)` releases the whole tree (tag-dispatched: Pure/Effect are leaves, Bind recurses into inner + consumes the continuation closure, Par walks all branches). **INTERNAL-LOOP OPEN (Sprint 57 Phase 4 G8 fix)**: intermediate Pure/Effect/Bind/Par nodes produced or replaced during the trampoline walk, and continuation closures popped from `cont_stack` and invoked, are leaked. See §3.5. |
| IVar intrinsics | runtime/ivar.rs | various | varies | varies | separately reviewed — IVar code already has RC management for its specific semantics |
| `print_string` (stdio) | `platforms/stdio/src/lib.rs` | `s: CLString` | No (returns `IO Int`) | Yes (captured into Effect thunk) | **DONE (Sprint 59 Workstream C-i)**: uses `CLHeap::into_owned_consuming` (Form B) — takes the caller's transferred ref directly into a `CLOwned` without inc'ing; the `CLOwned` dec's on closure drop, matching Decision 24's per-call balance. |
| `capture_print` (test-capture) | `platforms/test-capture/src/lib.rs` | `s: CLString` | No (returns `IO Int`) | Yes (captured into Effect thunk) | **DONE (Sprint 59 Workstream C-i)**: uses `CLHeap::into_owned_consuming` (Form B) — same pattern as `print_string`. |
| `read_line` / `scripted_read_line` | `platforms/{stdio,test-capture}/src/lib.rs` | none | — | — | no heap arg |
| `commutative_*`, `resource_serial_noop` (test-capture) | `platforms/test-capture/src/lib.rs` | none (CLInt args) | — | — | no heap arg |
| Other platform DLL functions | `cranelisp-platform/src/lib.rs` | varies per DLL | varies | varies | default rule: any new extern that captures a heap param into an Effect thunk MUST use `into_owned_consuming` (not `own()`). See §10.4 Form B. Platform-author checklist in `crates/cranelisp-platform/CLAUDE.md`. |

**Full migration complete**: all externs consume correctly under Decision 24 (Sprint 56 Step 2c; platform-DLL capture-Effect pattern closed Sprint 59 Workstream C-i). Caller-side inc runs via `compile_consuming_arg_list` (apply.rs) for every heap-typed Var argument. Callee-side dec runs via:

- `rc::consume_shallow` — simple-heap externs whose heap args have no heap sub-refs (all 14 string externs + `parse-int`).
- `drop::consume_slist` / `consume_sexp` — SList/Sexp runtime marshaling (`sconcat`, `quote-sexp`).
- `drop::consume_vec_of_string` — Vec of Strings (`join`).
- `drop::consume_trace_call` — Trace ADT accessors (6 functions).
- `drop::consume_io_tree` — IO trampoline (`cranelisp_run_io`).

Each `drop::consume_*` function mirrors the backend's `emit_rc_dec_with_inline_drop_glue` in Rust: atomic dec with Release ordering; on last-ref path, Acquire fence → walk heap-typed fields → recursively consume each → dealloc the outer allocation. Non-last-ref paths short-circuit after the outer dec, matching the inline-drop-glue invariant that sub-refs are dec'd only when the outer reaches rc=0.

RC balance is: Var arg → caller +1, callee −1 = net 0 (Var's own scope still holds its original ref); Temp arg → caller +0 (no inc), callee −1 = net −1 (frees the temp, which started at rc=1).

**`string-identity`**: the one exception remains consuming-compatible. Semantically it is "inc and return" — the input pointer flows out through the return value with a fresh inc. Callers use `compile_arg_list` (no caller-side inc) because inc-and-return on an already-inc'd arg would double-count.

**Vec-op caller handling**: `compile_vec_op` in backend emits `emit_vec_drop_if_temporary(vec_arg)` for the old Vec when the copy path is taken. This is a caller-side dec that predates Decision 24 and is tied to COW semantics (the old Vec is structurally replaced). It is NOT a post-call `dec_temporary_args` — it is a COW-specific cleanup that runs in the copy branch only. Keep it as is.

**Data constructor calls** (`compile_var_apply` → `compile_data_constructor_call`): now uses `compile_consuming_arg_list` for its args. Variable args get inc'd at the call site so the caller's scope still holds a reference while the ADT holds its own independent reference (released via the ADT's drop glue at destruction). Previously used plain-arg compilation, which caused use-after-free when the ADT outlived the caller's scope (the field stored a pointer to a heap object whose only reference was about to be dec'd by scope cleanup). Fixed in Step 2c.

**Operator wrappers (`cranelisp_op_add` etc.)**: No heap args — Int/Bool/Float bit-patterns only. No action.

**Guidance for adding new externs**: default to consuming. For each heap-typed parameter decide: (a) does it flow out unchanged through the return? If yes, inc-and-return or just return-as-is with ownership transfer. (b) does it get stored/retained? If yes, inc it into the storage. (c) otherwise: dec it before return. Write a test per §4 of this doc.

### 3.4 Temporary Closure Callee

When the callee itself is a temporary expression (e.g., `((make-adder 5) 3)`), the result of the callee expression is a closure at rc=1. After the call:

1. The return value is **protected**: if heap-typed, emit `rc_inc` on the result before dec'ing the closure. This prevents premature deallocation if the result aliases a captured value.
2. The temporary closure is dec'd via `emit_closure_dec`.

### 3.5 IO Trampoline Intermediate-Node Leak (Sprint 57 Wave 3 — LANDED)

The IO trampoline in `crates/cranelisp-runtime/src/io.rs` is the Ring 4 counterpart to the user-function consuming convention: it executes an IO ADT tree built by the frontend/prelude (Pure / Effect / Bind / Par) and returns the final value. Under Decision 24, the extern entry `cranelisp_run_io(io_ptr)` consumes the **top-level** IO argument via `crate::drop::consume_io_tree(io_ptr)` after the trampoline returns. Before Sprint 57 Wave 3, intermediate Pure/Effect nodes produced by continuations during the walk were leaked: each continuation's returned node became the new `current` and the prior `current` was dropped from the local without a matching dec/dealloc.

Before the Wave 3 fix, this was a real leak, not cosmetic (per `/arch` review condition 6). Every Bind-chain step through a continuation produces a fresh IO node (typically a Pure or Effect) that replaces the previous `current`; the previous `current` — an earlier intermediate produced by an earlier continuation — had no further reference and no matching dec. Under a Ring-4 program doing many binds, the leak was O(binds).

The Wave 3 fix distinguishes **caller-tree** nodes (reachable from the original `io_ptr`, released by the top-level `consume_io_tree`) from **fresh** nodes (produced by continuations during the walk, released inline by the trampoline). See §3.5.4 for the landed implementation.

#### 3.5.1 What `run_io_trampoline` does

`run_io_trampoline(io_ptr: i64) -> i64` walks the IO ADT iteratively with an explicit `cont_stack: Vec<i64>` of continuation closures. On each iteration, it reads `current`'s tag (offset 16) and dispatches:

| Tag | Action | How `current` is replaced |
|---|---|---|
| Pure | Read field0 (payload). Pop a continuation or return. | If cont popped: `current = call_continuation(cont_ptr, val)` — the continuation returns a fresh IO node. If no cont: return val to caller (Pure node is not consumed here; dec'd by `cranelisp_run_io` via `consume_io_tree` on the top-level root — but only if `current` IS the top-level root at return time, which it is not after the first continuation). |
| Effect | Read field0 (thunk ptr), invoke the thunk via `call_effect_thunk`. Pop a continuation or return. | Same as Pure — continuation returns a fresh IO node, or trampoline returns the result value directly. |
| Bind | Read field0 (inner), field1 (cont). Push cont on stack. | `current = inner` — the Bind node itself has no further use; its inner pointer is now the new current. The Bind node is leaked unless later consumed. |
| Par | Read count + branch pointers. Dispatch rayon parallel evaluation. Allocate results buffer. Pop a continuation or return. | `current = call_continuation(cont_ptr, results_ptr)` or return results_ptr. |

#### 3.5.2 Where the intermediate nodes come from

Two sources:

1. **Continuation returns.** A Cranelisp continuation is a lambda `(fn [x] <expr>)` where `<expr>` builds and returns an IO value — typically `(pure (+ x 1))` or `(bind <another-io> <next-cont>)`. The returned IO node is a fresh heap allocation at rc=1 (the continuation allocated it via the backend's normal allocation path). The trampoline assigns it into `current` and proceeds. When the NEXT iteration replaces `current` again, the previous IO node — a fresh Pure / Effect / Bind / Par at rc=1 — has no remaining reference.

2. **Bind dispatch.** When `current.tag == IO_TAG_BIND`, the trampoline reads `field0` (inner IO) and `field1` (continuation closure), pushes the closure on `cont_stack`, and replaces `current = inner`. The Bind node itself is now unreferenced by the trampoline. The top-level `consume_io_tree` call in `cranelisp_run_io` does dec the Bind node — but only if the Bind node is still reachable from the top-level root pointer at that time. The dec is only correct for Bind nodes directly on the root's spine; a Bind node produced by a continuation mid-walk is NOT on the root's spine.

Combined effect: every continuation-produced node and every mid-walk Bind node is leaked. The rc=1 reference is never dec'd.

#### 3.5.3 The RC-balance rule

Under Decision 24, the extern `cranelisp_run_io(io_ptr)` is a consuming callee: it fully releases the IO tree handed in. The internal trampoline (`run_io_trampoline`) is a non-consuming helper — it walks the caller-owned tree read-only and dec's only the nodes IT allocates (continuation-produced intermediates). The extern wrapper handles the caller's tree via `consume_io_tree(io_ptr)` post-return.

Stated as an invariant:

- Caller-tree nodes (reachable from the original `io_ptr` by following Bind spines, Par branches, and Bind continuations) are owned by the top-level extern caller. They are released by one transitive `consume_io_tree(io_ptr)` call after the trampoline returns.
- Fresh nodes (allocated during the trampoline's walk by invoked continuations) are owned by the trampoline. They are released inline via `rc::dec_shallow_io` at the point of replacement, and a final shallow dec on the no-continuation return path.
- Continuations popped from `cont_stack` carry their parent Bind's freshness. Caller-tree closures are not dec'd by the trampoline (the tree walks them); fresh closures are `consume_closure`-dec'd after invocation (one-shot semantics).
- The trampoline returns a scalar `i64` — whatever payload the final Pure/Effect/Par yielded. If that payload is a heap pointer (e.g., a String from `Pure "hello"`), its rc is managed by the caller's scope, as for any heap-typed return value.

See §3.5.4 for the landed implementation of these rules.

#### 3.5.4 Fix shape — LANDED Sprint 57 Wave 3

The minimal fix is to dec the replaced node inside each loop iteration WHEN the trampoline owns it (not when the caller does). The earlier formulation of this section proposed unconditional shallow-dec at every replace site — that turned out to double-dec the caller's tree because `cranelisp_run_io` still needs to run `consume_io_tree(io_ptr)` post-return to release the top-level tree (closures embedded in caller-tree Binds are transitively released by that walk). The correct discipline is ownership-aware shallow dec: shallow-dec only the nodes and closures the trampoline itself produced.

**Landed implementation (Approach 4)**. `run_io_trampoline` is non-consuming of `io_ptr`:

- The trampoline tracks `current_is_fresh: bool` — initially false (the caller's tree). It flips to true after the first `call_continuation` (continuation returns a freshly-allocated IO node) and stays true for the rest of that subtree (stepping into a fresh Bind's inner descends to another fresh node because the continuation allocated the whole subtree).
- At every transition where `current` is replaced (Bind → inner, Pure/Effect/Par pop → continuation result), shallow-dec the old `current` via `rc::dec_shallow_io` **only if `current_is_fresh` was true**.
- `cont_stack` stores `(cont_ptr, cont_is_fresh)` — the freshness inherited from the enclosing Bind at push time. When popped, `call_continuation(cont_ptr, val, cont_is_fresh)` invokes the closure and, if `cont_is_fresh`, `drop::consume_closure(cont_ptr)` after the call to dec the continuation-produced closure. Caller-tree closures (is_fresh=false) are left alone; `consume_io_tree(io_ptr)` releases them post-return.
- `cranelisp_run_io(io_ptr)` wrapper: runs the trampoline, then `drop::consume_io_tree(io_ptr)` to transitively release the caller's tree.

**Ownership invariant**. Every IO ADT node is dec'd exactly once:
- Caller-tree nodes (Pure/Effect/Bind/Par and their cont closures) — released by the post-return `consume_io_tree(io_ptr)` transitive walk.
- Fresh nodes (allocated by a continuation during the trampoline's walk) — released inline by the trampoline's ownership-aware shallow dec.

The two sets are disjoint: caller-tree nodes are reachable only via `io_ptr`; fresh nodes are reachable only via `current` after the first `call_continuation`. There is no overlap, so no node gets double-dec'd, and none leaks.

**Primitives introduced in Wave 3**:

- `rc::dec_shallow_io(ptr)` — landed in `crates/cranelisp-runtime/src/drop.rs` (Decision 29). Atomically dec's the RC with Release ordering; on last-ref, emits an Acquire fence and deallocs the outer allocation only — no field walk. Safe on bare nullary tags.
- `call_continuation(cont_ptr, val, cont_is_fresh: bool)` — existing helper gains the freshness flag; when true, invokes `consume_closure(cont_ptr)` post-call.

**Rejected alternatives**:

- **Unconditional shallow-dec at every replace site** (the earlier §3.5.4 recommendation): double-dec's caller-tree closures because `consume_io_tree(io_ptr)` still walks them. The pre-landing analysis missed this because the two dec paths (inline + post-return) were not modelled together.
- **Track-and-drop** (keep a `Vec<i64>` of owned nodes and dec them at returns): allocates a Vec per trampoline invocation; the `current_is_fresh` bool is a simpler invariant.
- **Consume io_ptr at the trampoline level** (make `run_io_trampoline` consuming): cleanest in theory but changes the contract of a public Rust function, breaking all direct Rust-level callers (tests in `tests/io.rs` that call `run_io_trampoline` then `heap_dealloc(value)`). Keeping the post-return `consume_io_tree(io_ptr)` at the extern wrapper preserves backward compat.

**Freshness flag is viral within a subtree**. Once set to true (by a continuation returning a fresh node), freshness is inherited by Bind's inner (same continuation allocated both), Par's branches (same), and popped continuations (stored with their enclosing Bind's freshness). Freshness never flips back to false — a fresh subtree cannot contain a caller-tree node.

#### 3.5.5 Why `call_effect_thunk` is NOT affected

`call_effect_thunk` consumes its thunk pointer by design (the `Box<Box<dyn FnOnce>>` is taken out and dropped by the invocation). The Effect node's field0 (thunk ptr) is a raw Rust heap pointer, not a Cranelisp heap allocation with an RC header; it is outside the RC regime and does not interact with this fix. The Effect node's field1 (resource token) is a scalar Int; likewise no RC. Only the Effect node's OWN allocation (the wrapping heap slot with header + tag + thunk_ptr + token) is a Cranelisp heap object requiring an RC-dec — and that dec is the shallow one from §3.5.4.

#### 3.5.6 Par-specific note

`dispatch_par_branches` invokes `run_io_trampoline` recursively on each branch. Under the fix, each recursive trampoline call is itself RC-balanced — every intermediate node produced inside the branch walk is dec'd inline by the branch's own trampoline instance. The outer trampoline then allocates a fresh `results_buf` via `alloc_with_rc` to hold the scalar results; this buffer is passed to the continuation and eventually dec'd by whatever scope owns it (typically the continuation's `pop_scope_with_cleanup`). The outer Par node itself is shallow-dec'd at the point where `current` is replaced with the continuation's return (or at the `return results_ptr` path at the top-level).

#### 3.5.7 Testing — RC balance required, not just "tests pass"

Per `/arch` review condition 6, the acceptance criterion for this fix is NOT "IO platform tests pass" but a real RC-balance integration test. `/qa` owns the integration test; the backend/runtime-side unit test is:

```text
Setup:  record alloc_count / dealloc_count; build an IO tree with N
        intermediate Bind steps, each continuation producing a Pure node.
Act:    call cranelisp_run_io on the root.
Assert: (alloc_count - baseline) == (dealloc_count - baseline) + returned-heap.
        For scalar-payload programs, returned-heap == 0, so alloc delta == dealloc delta.
```

The existing `decision24_run_io_pure_rc_balanced` test (at `io.rs:554`) already exercises the no-continuation path and is balanced. The fix MUST enable analogous tests for bind-chains and par-chains to pass with the same alloc/dealloc invariant.

Pre-existing `test_run_io_deep_bind_chain` (1000 binds) is a natural stress test — under the fix, it must run with `(alloc_count - baseline) == (dealloc_count - baseline)` at the end. Today it leaks 1000+ intermediate nodes; post-fix, zero.

#### 3.5.8 Sketch comparison

The sketch (`sketch/src/intrinsics.rs` line ~157, `IoTask::run()`) has the same trampoline shape and **the same leak**. The sketch operates under a different overall convention (per-call borrowing in the sketch's codegen, per `sketch/docs/codegen.md`) which masked the leak in early Ring 4 prototyping — the sketch did not universally claim that extern entry points consume their heap arguments, so a leak of intermediate IO nodes was not obviously a convention violation. In the reimplementation under Decision 24, the leak IS a convention violation: the trampoline's extern entry commits to consuming, and the internal loop must honour that commitment. The divergence from sketch is: we fix the leak; the sketch did not.

Rationale for divergence: Decision 24's uniform consuming convention makes every extern's RC balance auditable (§3.3 is the audit table). An unaudited leak inside `cranelisp_run_io` breaks the audit's credibility. The sketch's per-call borrowing convention did not have the same audit story, so the sketch could tolerate the leak in practice. The reimplementation cannot.

#### 3.5.9 Cross-references

- `crates/cranelisp-runtime/src/io.rs` — the landed fix (non-consuming trampoline + `current_is_fresh` flag).
- `crates/cranelisp-runtime/src/drop.rs` — `consume_io_tree` (transitive) for caller-tree release; `consume_closure` for fresh-closure release; `dec_shallow_io` (Decision 29, Wave 3) for fresh IO-node release.
- `§3.3 Extern Consumption Audit` — the row for `cranelisp_run_io` that describes the top-level `consume_io_tree(io_ptr)` behaviour; remains accurate after the fix.
- `design/arch/CLAUDE.md` Decision 24 — the uniform consuming convention.
- `design/arch/CLAUDE.md` Decision 29 — `rc::dec_shallow_io` primitive introduced by the Wave 3 fix.
- `sprints/SPRINT.md` §"Architecture Review" condition 6 — the `/qa` RC-balance integration test (Wave 3 acceptance criterion).
- `repl/demos/…` — platform demos that exercise the trampoline (behaviour-preserving; memory behaviour fixed).

## 4. Drop Glue

Drop glue is the mechanism by which composite heap values recursively release their sub-values when freed.

### 4.1 Closure Drop Glue

Closure drop glue is generated by `build_closure_drop_glue` when a lambda has heap-typed captures. The generated function:

1. Receives the closure base pointer.
2. For each heap-typed capture at offset `capture_offset(i)`, loads the value and emits `rc_dec` (guarded for Mixed types).

The drop glue pointer is **embedded** in the closure at `DROP_GLUE_PTR_OFFSET` (offset 24). This is essential because the caller often does not know the closure's capture layout at compile time (e.g., when a `Fn` parameter is received from another module).

At dec time, `emit_closure_dec_inline`:
1. Atomically decrements RC.
2. If old RC was 1 (last reference):
   a. Acquire fence.
   b. Loads `drop_glue_ptr` from offset 24.
   c. If non-zero, calls it via `call_indirect`.
   d. Calls `runtime/dealloc`.

### 4.2 ADT Inline Drop Glue

ADT field cleanup uses two approaches:

**Inline drop glue** (`emit_inline_drop_glue` on FnCompiler): Emitted directly into the caller's function body. Used by `pop_scope_with_cleanup` (the historical `dec_temporary_args` helper was deleted in Sprint 56 Step 2c — see §3 historical note). For each data constructor with heap-typed fields:
- Single data constructor: directly load and dec each heap-typed field.
- Multiple data constructors: load the tag, branch to the correct constructor's field-dec block.
- For Mixed ADTs, the entire drop glue is guarded by a heap-pointer check.

**Standalone drop glue** (`build_adt_drop_glue_fn`): A separate JIT function `(ptr: i64) -> ()`. Used by Vec element dec functions. The generated function has the same tag-dispatch logic but lives as an independent function that can be referenced by function pointer.

### 4.3 Vec Drop Glue

Vec uses a two-level approach:

1. **Element-level**: `build_elem_dec_fn` generates a standalone `(val: i64) -> i64` function per element type. If the element type is an ADT with heap fields, `build_adt_drop_glue_fn` generates a nested drop glue function that is passed to `emit_rc_dec_guarded` inside the element dec function.

2. **Vec-level**: `vec_drop(vec_ptr, elem_dec_fn_ptr)` in the runtime iterates over live elements (indices 0..len), calls the element dec function on each, then frees the data buffer and the Vec struct.

Element inc/dec functions are generated by:
- `build_elem_inc_fn`: emits `rc_inc` (or guarded inc for Mixed) on the element value.
- `build_elem_dec_fn`: emits `rc_dec_guarded` (with optional ADT drop glue) on the element value.

Both are called from the runtime via function pointer during Vec copy operations and Vec drop.

## 5. Scope Cleanup

### 5.1 pop_scope_with_cleanup

`pop_scope_with_cleanup(skip_var)` is the workhorse of automatic memory management. Called at the end of every `let` body and every function body:

1. Iterates over the current scope frame's bindings.
2. Skips the `skip_var` (the binding whose value is being returned -- its ownership transfers to the caller).
3. Skips consumed variables (already transferred to a callee).
4. For each remaining heap-typed binding:
   - `Type::Fn`: calls `emit_closure_dec_inline` (runtime drop glue dispatch).
   - ADT types: calls `emit_inline_drop_glue` then `emit_rc_dec` (or guarded variants for Mixed).
   - Other heap types (String): calls `emit_rc_dec` directly.
5. Pops the scope frame, removing bindings from `variables` and `variable_types`.

### 5.2 return_var_in_scope

Determines which variable (if any) should be skipped by scope cleanup:

```rust
fn return_var_in_scope(body: &Expr, scope_frame: Option<&Vec<Symbol>>) -> Option<Symbol>
```

If the body is a direct `Expr::Var` reference to a name in the current scope frame, that name is returned as the skip_var. Scope cleanup then dec's everything except this binding, whose ownership is transferred to the parent.

### 5.3 protect_return_value

When `skip_var` is `None` (the body is not a direct variable reference -- e.g., it's an `if`, `match`, or function call), the return value might alias a scope binding. For example:

```clojure
(let [s "hello"]
  (if cond s "world"))
```

Here the `if` expression's result might be `s`, but `return_var_in_scope` returns `None` (the body is `if`, not a `Var`). Scope cleanup will dec `s`, which could free it before the result is returned.

`protect_return_value` handles this by emitting `rc_inc` on the result value before scope cleanup runs, but only when:
1. `skip_var` is `None`.
2. The body is not a fresh allocation (`Lambda` or `StringLit`) that cannot alias scope bindings.
3. The current scope has at least one heap-typed binding.
4. The result type is heap-typed.

The caller's subsequent dec (at its own scope exit) restores the net count.

### 5.4 Match Interaction with Scope Cleanup

Match arms introduce their own scope frames:

1. **Variable pattern** (`x`): binds the scrutinee to `x`, pushes a scope. The arm body is compiled, then `pop_scope_with_cleanup` dec's the binding (unless it's the return value).

2. **Constructor pattern** (`(Some val)`): pushes a scope, binds each extracted field. Extracted fields get `rc_inc` at extraction time (they need their own reference independent of the scrutinee). The arm body is compiled, then `pop_scope_with_cleanup` dec's the field bindings.

3. **Scrutinee temporary**: After all arms converge at the merge block, if the scrutinee was a temporary expression (not a Var), inline drop glue is emitted and the scrutinee is dec'd.

The scope cleanup per arm ensures that field bindings extracted in constructor patterns are properly released even when the arm body doesn't return them.

### 5.5 Captured and Borrowed Variables and Last-Use

Three rules modify scope cleanup behavior:

- **Captured variables** (`captured_vars`): Variables closed over by a lambda are NEVER eligible for last-use transfer. The closure env holds its own inc'd reference, and the enclosing scope must dec its own reference at scope exit regardless.

- **Borrowed variables** (`borrowed_vars`): Variables introduced by match-arm constructor-pattern field bindings (e.g. `v` in `(match b [(Box v) ...])`). These extract a field from the scrutinee and skip both inc (at extraction) and dec (at scope exit) — the scrutinee still owns the value. Consequently, borrowed variables are NEVER eligible for last-use transfer, structurally symmetric with `captured_vars`: neither owns the value, so neither may transfer ownership. Violating this rule causes Vec COW mutate-in-place on an aliased Vec, followed by use-after-free when the scrutinee's drop glue independently dec's the field.

  **Regression history**: Sprint 61 Slice 2 Layer 3 (`exemplar/repro-slice2.cl`). `(consume (Box [0]))` where `consume` does `(match b [(Box v) (Box (vec-set v 0 1))])` read the inner Vec length as `0` instead of `1`. Root cause: `is_last_use` did not gate on `borrowed_vars`, so the textually-last reference to `v` in `(vec-set v 0 1)` was treated as an ownership transfer. Vec COW saw `is_last_use + rc==1` and mutated in place, aliasing the original Box's field. When inline `(Box [0])` reached rc=0 and its drop glue fired, the mutated Vec was double-dec'd. The Layer 2 Sudoku backtracking regression (`try-digits`/`solve` on valid puzzles under the Layer 1 eliminate fix) was the same root cause — the `(match g [(Grid v) ...])` pattern bound `v` and passed it to `vec-set`, triggering the same aliasing. Fix landed 2026-04-22 at `crates/cranelisp-backend/src/compiler/mod.rs:1204`.

- **Last-use analysis** (`compute_last_uses`): Walks the expression tree in pre-order to determine the final use of each variable. The last use of a variable reference is a candidate for ownership transfer (skip the inc at the call site because the callee gets the caller's last reference). Currently used by Vec COW to determine mutate-in-place eligibility, but the general mechanism is available for future optimization. Must be gated on both `captured_vars` and `borrowed_vars` — neither owns the value, so neither may transfer ownership.

#### 5.5.1 Sketch comparison

The sketch was aware of match-arm borrowed bindings: `mark_borrowed_var` in `sketch/src/codegen.rs:247` records the same concept, set from `sketch/src/codegen/match_compile.rs:231–235` when the scrutinee is a known-unique local. But the sketch's gating strategy diverges — rather than gating `is_last_use` on the borrowed set, the sketch took an orthogonal route: `emit_consuming_caller_rc` at `sketch/src/codegen.rs:295–303` short-circuits borrowed vars by emitting an unconditional inc ("auto-upgrade") and skipping `mark_consumed` entirely, which prevents last-use transfer as a side effect. Both designs reach the same invariant (borrowed binding never transfers ownership); the reimplementation's explicit `is_last_use` gate (§7 table row) is arguably clearer for future readers since the rule is named where the decision is made, rather than implied by the absence of a `mark_consumed` call. The sketch additionally predicated the borrow on a scrutinee-uniqueness check (`scrutinee_is_unique` at `match_compile.rs:37–42`, eliding both inc at extraction and dec at scope exit when safe) — an optimisation the reimplementation has not adopted; this sketch feature is tracked as a possible future refinement rather than a bug.

### 5.6 Capture-return inc

**Rule (Slice 4, Sprint 61 Wave 4 — LANDED 2026-04-21).** When a lambda body's return expression resolves to a captured heap variable (i.e. `Expr::Var { name: cap }` where `cap ∈ captured_vars` and the capture's type is `AlwaysHeap` or `Mixed`), the body MUST emit `rc_inc` on the returned value before `return`.

This is structurally sibling to §5.5's rules — all three arise from the same discipline that `scope_stack` tracks owning references only, and that captured/borrowed variables live outside that discipline. The prior rules handle cleanup (no dec on exit for borrowed; no last-use transfer for either). This rule handles the mirror case: the *return value* must be inc'd when it originates outside the scope frame, because the closure's drop-glue WILL dec the capture after the body returns.

**Why `protect_return_value` does not cover this case.** The gate in `protect_return_value` examines `scope_stack` for heap-typed cleanup targets and emits an inc only when at least one is present. Captures are deliberately absent from `scope_stack` (their release is the closure env's responsibility, handled by the drop-glue emitted in `build_closure_drop_glue`). For a `(fn [_] b)` where `_` is non-heap and `b` is a heap capture, `scope_stack.last() = [_]` — no heap-typed targets, no inc emitted. The returned value then flows out at the rc it came in with, the drop-glue runs on closure consumption and dec's the capture to zero, and the caller is left with a pointer to freed memory.

**Why captures are consumed after return.** One-shot closure call sites (the IO trampoline's `consume_closure`; analogous fresh-closure paths) dec the closure after invocation. The closure's drop-glue iterates its heap captures and dec's each. That dec is structurally correct (the closure env owns its captures), and this rule does not change it. Instead, we ensure that when the returned value IS one of those captures, the ownership transfer to the caller is balanced by an inc inside the body.

**Implementation.** Helper `emit_capture_return_inc` in `crates/cranelisp-backend/src/compiler/control_flow.rs`, called from `compile_lambda_body` between `protect_return_value` and `pop_scope_with_cleanup`. The helper is a no-op unless (a) the body is `Expr::Var`, (b) the name is in `captured_vars`, and (c) the capture's type (from `variable_types`, seeded from the enclosing scope) is heap-categorised. This preserves `protect_return_value`'s existing semantics for all other return shapes.

**Regression history.** Sprint 61 Slice 4 (`tests/sprint61/race-evidence/21-hello-io-failing-min-776a6cf.log`). A 7-line repro exercising `(defn then [a b] (bind a (fn [_] b)))` + a second user-defined `bind` layer consuming `then`'s output via the IO trampoline reproduced at 100% as `cranelisp_run_io: unknown IO tag ...` (a pointer read from freed memory that happened to dereference mid-object, yielding a garbage tag byte). H(4-1'') ruling by /arch at `design/backend/archive/slice-4-21-hello-io-investigation.md §4d`: backend-only fix, trampoline (`consume_closure` + `current_is_fresh`) protocol unchanged. Unit test: `cranelisp-backend::tests::lambda_return_captured_heap_var_emits_inc`. Integration test: authored by `/qa` at step 4f against the 7-line minimum repro.

#### 5.6.1 Sketch comparison

The sketch does NOT have an explicit capture-return inc rule, and its closure-body cleanup path has the same latent bug as the pre-fix reimplementation. Lambda-body entry at `sketch/src/codegen/closures.rs:184–199` loads captures from the env pointer but deliberately does not `track_binding` them into `scope_stack` (see the inline comment "don't track in scope_stack — captures are owned by the closure env, not by this invocation"). The body then exits through `pop_scope_for_value` (`sketch/src/codegen.rs:576–626`), whose borrowed-return-upgrade loop iterates only `frame` — the popped scope-stack frame — so captures are never examined. For a lambda shape `(fn [_] b)` where `_` is non-heap and `b` is a heap capture, no inc is emitted before return; the caller-side closure drop-glue subsequently dec's `b`, freeing it while the return value still references it. The sketch likely did not encounter this in practice because its test suite's IO-trampoline compositions differ from S61's `then` shape, but the defect is latent rather than absent. Divergence is justified: the reimplementation's explicit `emit_capture_return_inc` helper (`crates/cranelisp-backend/src/compiler/control_flow.rs`, called between `protect_return_value` and `pop_scope_with_cleanup`) closes the gap that the sketch leaves open, at the cost of one extra helper rather than extending `scope_stack` tracking — the narrower fix is preferable because it leaves the invariant "`scope_stack` tracks owning references only" undisturbed.

## 6. Invariants

These invariants must hold at all times. Violation indicates a bug.

### 6.1 RC Invariants

1. **RC never negative**: Every `rc_dec` that brings RC to 0 triggers deallocation. If RC would go below 0, `rc_underflow_check` fires a debug assertion.

2. **RC starts at 1**: `alloc_with_rc` initializes RC to 1. The allocating expression is the initial owner.

3. **Every inc has a matching dec**: Inc-dec pairs are balanced across ownership transfers. A calling convention violation (wrong convention for a call type) will cause either a leak (missing dec) or a use-after-free (extra dec).

4. **Drop glue runs before dealloc**: When a value reaches rc=0, its drop glue recursively dec's sub-values before the object is freed. Skipping drop glue causes field leaks.

### 6.2 Calling Convention Invariants

5. **All call sites use consuming convention (Decision 24)**: The caller incs heap-typed variable arguments before the call; the callee is responsible for dec'ing heap arguments it does not return. This applies uniformly to user functions, trait methods, sig-dispatch, data constructors, closure calls, inline builtins, Vec ops, and extern primitives.

6. **Extern primitives dec their own heap args**: A Rust-implemented extern that takes a heap pointer MUST dec that pointer before returning (unless it returns the pointer unchanged, i.e. ownership flows out through the return value, or it stores the pointer in a runtime-owned structure). The caller emits no post-call dec. See §3.3 Extern Consumption Audit.

7. **Data constructor fields are owned by the ADT**: The caller incs variable args (consuming convention); the constructor stores the field values into the new heap object and emits no explicit dec. Drop glue handles fields at destruction time when the ADT itself reaches rc=0.

### 6.3 Debugging Invariants

8. **LIVE_ALLOCS tracking** (debug builds): Every `alloc_with_rc` call adds the pointer to a `HashSet`. Every `dealloc` removes it (asserting it was present). A double-free triggers a debug assertion.

9. **RC trace logging**: `CRANELISP_RC_TRACE=1` enables per-operation logging to stderr, showing pointer address and RC value for every alloc, free, inc, and dec.

## 7. Implementation Locations

| Component | File | Key functions |
|---|---|---|
| HeapHeader | `cranelisp-types/src/heap.rs` | `HeapHeader`, `HeapCategory::classify` |
| Heap layout structs | `cranelisp-backend/src/heap.rs` | `HeapAdt`, `HeapClosure`, `HeapVec` |
| RC emission | `cranelisp-backend/src/heap.rs` | `emit_rc_inc`, `emit_rc_inc_guarded`, `emit_rc_dec`, `emit_rc_dec_guarded` |
| Last-use analysis | `cranelisp-backend/src/heap.rs` | `compute_last_uses` |
| Last-use ownership gate | `cranelisp-backend/src/compiler/mod.rs` | `is_last_use` (gates on both `captured_vars` and `borrowed_vars`) |
| Calling convention | `cranelisp-backend/src/compiler/apply.rs` | `compile_consuming_arg_list`, `compile_arg_list` (plain args; consuming dispatch applies uniformly — no caller-side `dec_temporary_args`) |
| Scope cleanup | `cranelisp-backend/src/compiler/mod.rs` | `pop_scope_with_cleanup`, `return_var_in_scope`, `protect_return_value` |
| Inline drop glue | `cranelisp-backend/src/compiler/mod.rs` | `emit_inline_drop_glue`, `emit_field_decs` |
| Closure drop glue | `cranelisp-backend/src/compiler/control_flow.rs` | `build_closure_drop_glue`, `emit_closure_dec_inline` |
| Standalone ADT drop glue | `cranelisp-backend/src/compiler/vec_codegen.rs` | `build_adt_drop_glue_fn`, `emit_standalone_field_decs` |
| Vec element inc/dec | `cranelisp-backend/src/compiler/vec_codegen.rs` | `build_elem_inc_fn`, `build_elem_dec_fn` |
| Runtime allocator | `cranelisp-runtime/src/alloc.rs` | `alloc_with_rc`, `dealloc`, `heap_alloc`, `heap_dealloc` |
| Runtime Vec | `cranelisp-runtime/src/vec.rs` | `vec_new`, `vec_drop`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow` |
| RC debug/trace | `cranelisp-runtime/src/rc.rs` | `rc_trace`, `rc_underflow_check`, `consume_shallow` |
| Runtime drop glue | `cranelisp-runtime/src/drop.rs` | `consume_slist`, `consume_sexp`, `consume_vec_of_string`, `consume_vec_with`, `consume_trace_call`, `consume_io_tree`, `consume_closure` |
| Intrinsic registration | `cranelisp-backend/src/jit.rs` | `register_intrinsics` |

## 8. Guidance for Ring 3 Implementers

### 8.1 Compiling a New Function

If you are generating a JIT function (e.g., a macro expansion helper, a trace wrapper):

1. **Parameters**: All user-defined functions are called with consuming convention — their parameters are owned. You MUST ensure `pop_scope_with_cleanup` runs at function exit with the return variable excluded.
2. **Calling any function (user, extern, trait method, data constructor, closure)**: Use `compile_consuming_arg_list` for the args. The callee is responsible for dec'ing anything it does not return.
3. **Writing an extern primitive in Rust**: Decide per heap-typed parameter — return unchanged (ownership flows out), retain/store (inc it into storage), or consume (dec before return). See §3.3 for the audit table.
4. **Allocating closures**: Call `build_closure_drop_glue` and store the result at `DROP_GLUE_PTR_OFFSET`. Inc heap-typed captures.

### 8.2 TCO and RC

Self-recursive tail calls currently do NOT emit scope cleanup before jumping to the loop header. This means heap-typed parameters from the previous iteration may leak. TCO+RC interaction is a known gap: the sketch's `emit_scope_cleanup_for_tco` was not carried forward to the reimplementation. Ring 3 should either implement this or document the restriction.

### 8.3 Common Pitfalls

- **Missing inc for variable args in consuming calls**: Causes use-after-free. The callee dec's the parameter at exit; without the caller's inc, the caller's binding is freed.
- **Missing dec in a new extern primitive**: Causes leaks. Under Decision 24 the extern owns its heap args — write the dec before return, or verify the arg flows out through the return value.
- **Extra dec in an existing extern primitive**: Causes use-after-free / double-free. Since Decision 24 the caller no longer emits `dec_temporary_args`; if an extern was previously dec'ing AND the caller was dec'ing, removing one without fixing the other flips the balance wrong.
- **Forgetting protect_return_value**: Causes use-after-free when the return value aliases a scope binding that gets dec'd by scope cleanup.
- **Captured variables treated as last-use**: Captured variables must NEVER skip inc at consuming call sites. The closure env needs its reference to remain valid.

## 9. Rejected Alternatives

### 9.1 Drop Function Side Table (Ring 1)

Ring 1 considered using a `HashMap<code_ptr, drop_fn>` for closure drop glue instead of embedding the pointer in the closure struct. This was rejected because:
- The side table requires locking or thread-local storage for lookups.
- Embedding the pointer costs 8 bytes per closure but makes closure dec a self-contained operation.
- Critical benefit: `emit_closure_dec_inline` can handle closures from any module without a global side table lookup.

### 9.2 Unified Calling Convention (ADOPTED — Sprint 56 Step 2c, Decision 24)

This is now the implemented convention — see §3. Historical context: it was initially rejected in favour of a split convention (Decision 20) because requiring builtins/externs to dec their own heap args was seen as adding overhead and complexity. In practice:

- Inline builtins operate on NeverHeap operands (Int/Bool/Float) — no dec required.
- Extern Rust primitives that take heap args are a finite, enumerable set (§3.3 audit). Adding a dec before return is a small, localised change per extern.
- The complexity saved on the caller side (no `dec_temporary_args`, no per-call-type classification, no `Option<dealloc_func_id>` conditional) dwarfs the per-extern cost. Every call site now compiles identically for RC management; the code path no longer branches on callee classification.

The split convention created a divergent compile path at every application site, exactly the kind of parallel structure Principle 7 (single source of truth) and Principle 11 (single pipeline) exist to prevent.

### 9.3 Deferred Reference Counting

Considered deferring RC operations to epoch boundaries (like Nim). Rejected because:
- Deterministic destruction is a language design goal.
- Deferred RC complicates reasoning about when side effects (via destructors/drop glue) occur.
- The inline atomic approach has acceptable overhead for the current single-threaded model.

## 10. Addendum — String-literal RC residual through `print` (Sprint 58 Wave 3)

**Status**: PRESCRIPTIVE for Sprint 58 Wave 3. This addendum specifies the fix for the FIXME(/backend) at `crates/cranelisp-runtime/src/io.rs:28` carried from Sprint 57 Wave 3. Per `/arch` Sprint 58 review condition 6, this MUST land in Wave 3 alongside other RC work, OR be deferred with explicit rationale and a named regression-test symptom for `/qa`. Disposition selected: **fix in Wave 3** (one-deferral-permitted policy is held in reserve only if implementation surfaces unexpected scope).

### 10.1 The leak

Observable via REPL-compiled `(print "a")` flowing through the IO trampoline. Allocations exceed deallocations by the size of the string literal allocation per call. Sprint 57 Wave 3 closed the trampoline-internal IO-node leak via §3.5.4 (`current_is_fresh` discipline + `dec_shallow_io`); this string-literal leak is in a different code path and was identified as separate at Wave-3 close.

### 10.2 Root cause

The `print` extern at `platforms/stdio/src/lib.rs:18-25` follows the capture-RC pattern:

```rust
#[unsafe(export_name = "cranelisp_print")]
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.own();           // inc s's RC, owned drops at thunk-drop
    CLIO::effect(move || {
        println!("{}", owned.as_str());
        CLInt::from(0i64)
    })
}
```

This pattern is correct for the deferred-execution discipline: `s.own()` calls `inc_rc` so the captured `owned: CLOwned<CLString>` keeps the string alive across the gap between `print_string` returning the IO Effect node and the trampoline later forcing the thunk. When the thunk runs and the closure drops, `CLOwned::drop` calls `dec_rc` and the string's RC returns to its pre-capture level.

The leak is at the **input boundary**, not the capture boundary. Decision 24's uniform consuming convention says: every extern with a heap-typed parameter dec's that parameter before return (unless it's returned unchanged or retained as a runtime-owned reference). For `print_string`:

1. The caller (JIT-emitted CLIF for `(print "a")`) emits `compile_consuming_arg_list` for the String literal, which inc's it (or transfers ownership of the literal allocation if it's a temporary). After `print_string` returns, the caller's RC view of the string is balanced — the inc was consumed by transferring to `print_string`.
2. `print_string` receives `s: CLString` with an extra reference (from the caller's transfer). It calls `s.own()` — inc again — and captures `owned`. So the string now has two references attributable to this call: one from the caller's transfer, one from `s.own()`.
3. `print_string` returns. The local `s: CLString` drops at end of scope, but `CLString` is `Copy` (it's just an `i64` base pointer wrapper) — its `Drop` is a no-op. The caller's transferred reference is **never** dec'd. **Leak: one reference per `(print "a")` call.**
4. When the trampoline later forces the Effect thunk, the closure runs `println!`, drops, and `CLOwned::drop` dec's once. That dec balances `s.own()`'s inc — but the original transferred reference from the caller is still leaked.

The pattern works for the *capture* lifetime (between Effect-node creation and thunk-force) but does not honour the *input-boundary* contract that Decision 24 added in Sprint 56. The capture-RC pattern was designed before Decision 24 was unified.

### 10.3 Why the Sprint 57 Wave 3 IO trampoline fix did not close this

Sprint 57 Wave 3 (§3.5.4) targeted the trampoline's internal node leak — Pure/Effect/Bind/Par nodes produced and replaced *during* the trampoline walk, plus continuation closures popped from `cont_stack`. The fix added the `current_is_fresh` discipline + `dec_shallow_io` for trampoline-owned intermediates, and updated `cranelisp_run_io` to call `consume_io_tree(io_ptr)` post-return for the caller's tree.

That fix is correct for IO ADT nodes. It does not extend to *captures* held by Effect-thunk closures — closures are dec'd by the trampoline's `consume_closure` (which runs the embedded drop_glue_ptr per Decision 11), and the drop-glue handles closure-captured heap references. The drop-glue runs `dec_rc` on every captured heap reference; for `print_string`'s closure, the captured `owned: CLOwned<CLString>` calls its own `Drop` which dec's once.

So the trampoline-side and capture-side are both correct. What's wrong is the missing dec on the input parameter `s: CLString` before `print_string` returns — outside both the trampoline's responsibility and the closure's responsibility, in extern-boundary territory per Decision 24.

The Wave-3 audit (§3.3) listed `cranelisp_run_io` and a generic note "Platform DLL functions" but did NOT walk every individual platform extern under Decision 24's lens. `print_string` slipped through because the capture-RC pattern looked locally correct (it balances `s.own()`'s inc with the closure's drop). Decision 24's contract requires the *additional* dec for the caller's transferred reference, which the capture-RC pattern does not provide.

### 10.4 The fix shape

Two equivalent forms; either is acceptable. Pick the one with the smaller code-volume impact across all platform externs (a sweep is required because the same pattern appears wherever a platform fn captures a heap arg into an Effect closure).

**Form A — extern dec's the input after own()**:

```rust
#[unsafe(export_name = "cranelisp_print")]
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.own();           // inc — for the capture
    s.dec_rc();                     // dec — for the caller's transfer (Decision 24)
    CLIO::effect(move || {
        println!("{}", owned.as_str());
        CLInt::from(0i64)
    })
}
```

This is the minimal local change. The `s.dec_rc()` matches the caller's `compile_consuming_arg_list` inc, satisfying Decision 24. The `owned` capture continues to keep the string alive for the deferred thunk-force; its `Drop` dec's at thunk-drop time, balancing `s.own()`. Net references attributable to one call: caller +1, `print_string`-extern -1 + 1 (`own`) - 1 (`Drop` later) = 0.

**Form B — capture-helper takes ownership, extern uses it inline**:

Refactor `s.own()` into `s.into_owned_consuming()` — a method on `CLHeap` that inc's once for the capture AND dec's the caller's transferred ref in one call. The extern stops calling `s.own()`; it calls `into_owned_consuming()`. Net effect identical to Form A; the consuming dec is hidden inside the helper so platform authors can't forget it.

```rust
impl<T: CLHeap + Copy> T {
    /// Consuming-convention version of `own()`: caller owns one transferred
    /// reference (per Decision 24); this helper takes ownership of that
    /// reference (no inc needed for it) and inc's an additional reference
    /// for the returned CLOwned. Symmetric: caller's transferred ref +
    /// CLOwned's inc'd ref = exactly one ref will be dropped by CLOwned::drop.
    fn into_owned_consuming(self) -> CLOwned<Self> {
        // No inc — the caller's transferred ref becomes the CLOwned's ref.
        // Just construct the wrapper directly without the inc that own() does.
        CLOwned { inner: self }
    }
}
```

```rust
#[unsafe(export_name = "cranelisp_print")]
pub extern "C" fn print_string(s: CLString) -> CLIO<CLInt> {
    let owned = s.into_owned_consuming();
    CLIO::effect(move || {
        println!("{}", owned.as_str());
        CLInt::from(0i64)
    })
}
```

Form B has the architectural advantage of making the capture-RC pattern aware of Decision 24 by construction. Form A is one line per affected extern. Recommend Form B if the platform-extern audit (§10.5) reveals more than 2–3 functions with the capture-Effect pattern; Form A if `print_string` is essentially alone.

### 10.5 Audit — every platform extern that captures a heap arg

Sprint 58 Wave 3 implementation MUST include an audit pass over every `extern "C"` function in `platforms/*/src/lib.rs` AND in the platform-bridge layer of `crates/cranelisp-platform/src/lib.rs`. For each function with a heap-typed parameter (CLString, CLVec-equivalent, etc.):

- If the param is captured into a closure (Effect/Bind continuation): apply Form A or Form B fix.
- If the param is consumed inline (e.g. printed without capture, as in a hypothetical `print-and-return-int`): add `s.dec_rc()` before return per Decision 24 (no capture-RC pattern at all).
- If the param is returned unchanged: no fix needed (caller's transferred ref flows out through the return).

Initial pass (verify during implementation):

| Extern | Heap arg | Captures? | Fix |
|---|---|---|---|
| `print_string` (`platforms/stdio/src/lib.rs:18`) | `s: CLString` | Yes (into Effect thunk) | Form A or B |
| `read_line` (`platforms/stdio/src/lib.rs:32`) | none | — | no fix needed |
| `test-capture::*` (`platforms/test-capture/src/lib.rs`) | TBD — audit | TBD | per row |

The §3.3 audit table in this document MUST gain a "Platform DLL functions" expansion sub-section enumerating each platform function individually after Wave 3 lands.

### 10.6 User-visible regression-test symptom (per /arch Condition 6)

Per `/arch` Sprint 58 review condition 6, the deferral-or-fix policy requires naming the specific user-visible symptom under which the leak manifests, so `/qa` can write a regression test before any deferral.

**Symptom**: when a Cranelisp program executes `(print "hello")` (or any string-emitting platform call) repeatedly under the IO trampoline, `cranelisp_runtime::alloc_count() - dealloc_count()` grows monotonically with the call count. Specifically:

- **Positive coverage** (program runs and prints correctly):
  ```text
  Setup:  let allocs_before = cranelisp_runtime::alloc::alloc_count();
          let deallocs_before = cranelisp_runtime::alloc::dealloc_count();
  Act:    run a Cranelisp program that does `(do (print "a") (print "b") (print "c"))`,
          drained through `cranelisp_run_io`.
  Assert: alloc_count - allocs_before == dealloc_count - deallocs_before.
          (Pre-fix: alloc delta exceeds dealloc delta by 3 — one leaked CLString
           reference per print call.)
  ```

- **Negative coverage** (bytes do not grow unbounded):
  ```text
  Setup:  baseline alloc/dealloc counters.
  Act:    run `(loop 1000 (print "x"))` (or hand-build a 1000-bind chain
          repeatedly forcing print) through `cranelisp_run_io`.
  Assert: dealloc_count - allocs_before is within ±1 of alloc_count - allocs_before
          across the entire run. (Pre-fix: gap grows by ~1000.)
  ```

`/qa` writes both tests. The negative test is the "headline" diagnostic — catches any future regression where the fix is correct on a single call but breaks on N calls (e.g. if Form B's `into_owned_consuming` accidentally inc's twice, the symptom would invert and dealloc would exceed alloc; the assertion catches that direction too).

The unit-test variant (in `crates/cranelisp-runtime/src/io.rs::tests`) must use a synthetic heap-string-capturing extern to exercise the same code path without depending on the platform DLL — see `decision24_run_io_pure_rc_balanced` for the existing pattern. Naming convention: `decision24_print_string_input_rc_balanced` (positive) + `decision24_print_string_repeated_rc_no_growth` (negative).

### 10.7 Why this is small and Wave-3-scoped

The fix is one line per affected extern (Form A) or one helper-method addition + one-line edit per affected extern (Form B). The audit is an enumeration over a small number of files (`platforms/*/src/lib.rs` plus any platform helpers in `crates/cranelisp-platform/src/lib.rs`). The IO-trampoline code in `crates/cranelisp-runtime/src/io.rs` is unchanged — the trampoline correctly dec's IO ADT nodes per §3.5.4; only the platform-extern boundary needs adjustment. Total estimated work: <1 day for the fix + audit + two regression tests.

### 10.8 Deferral fallback (one-deferral-permitted policy)

If implementation surfaces unexpected scope (e.g. the platform-extern audit reveals 20+ functions all needing rework, OR the capture-RC pattern in `crates/cranelisp-platform/src/lib.rs:CLOwned` requires deeper design work that exceeds Wave 3 budget), the one-deferral-permitted disposition is available. Required artefacts for deferral:

1. The user-visible symptom from §10.6 above (positive + negative regression test) MUST land in `/qa`'s Wave-5 work as `#[ignore]`'d tests with a comment naming the FIXME and the deferral rationale. The tests themselves are NOT `#[ignore]`'d to hide spec violations (per `feedback_failing_not_ignored.md`); they're `#[ignore]`'d only because the symptom is documented as a known leak. `/qa` removes the `#[ignore]` when the fix lands.
2. The FIXME(/backend) at `io.rs:28` is rewritten to name the deferral sprint and the explicit deferral rationale (not just "still open").
3. `/sprint` records the deferral in §Outcome → §Deferred with the rationale.

Default disposition: ship the fix in Wave 3. Deferral is held in reserve only if scope discovery during implementation makes Wave 3 untenable.

### 10.9 Cross-references

- `crates/cranelisp-runtime/src/io.rs:28` — the FIXME being closed.
- `platforms/stdio/src/lib.rs:18-25` — the `print_string` extern.
- `crates/cranelisp-platform/src/lib.rs:478-482` — `CLHeap::own()` (Form B's `into_owned_consuming` would land here).
- `design/arch/CLAUDE.md` Decision 24 — the consuming convention contract being enforced.
- `design/backend/ring2-rc.md` §3.3 — the extern consumption audit table; this addendum's §10.5 audit feeds back into §3.3.
- `sprints/SPRINT.md` §"Architecture Review" condition 6 — the disposition policy.
