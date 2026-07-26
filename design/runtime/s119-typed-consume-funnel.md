# Sprint 119 — the typed consume funnel (option 1, tranche A)

**Status:** DESIGN — pre-implementation. Phase-3 deliverable for Spine 2,
tranche A. Binding on the `/dev`(runtime pair) wave; the `public-api.txt` delta
in §8 goes to `/arch` at the Phase-3 exit gate.
**Scope:** the runtime pair — `cranelisp-intrinsics` (the discharge funnel and
the new handle vocabulary) + `cranelisp-primitives` (the extern shim generator
and the implementation bodies it reaches).
**Authority:** elaborates `design/arch/bounded-contexts.md` §4a/§4b; sibling of
`design/runtime/s117-primitives-integrity.md` and
`design/runtime/s118-structural-embedding-ownership.md`, which established this
directory as the home for a contract that spans the pair.
**Inputs:** `design/arch/ownership-stratum-options.md` §1.5, §2.1–§2.4 (as
amended `3232a061`); `sprints/SPRINT.md` §Architecture review gates G3 + G4;
FIXME 0768 (an instrument is unverified until proven to detect); FIXME 0859
(declaration facts vs production witnesses — **not** discharged here, §10.4).

---

## 1. The question, and the answer

> The pair's heap handles are raw `i64`. Whether a given parameter is
> **consumed**, **borrowed**, or **stored** is stated only in prose that a
> caller must re-derive at every site (§1.5a–b of the option paper). What makes
> the wrong reference count *unwritable* rather than merely untested?

**Ruled: a closed two-type handle vocabulary over the discharge funnel, with
exactly one raw entry and one raw exit, and the extern shim's ownership fact
derived — not re-asserted — from the primitives declaration table.**

Three properties follow, and they are the whole value:

1. **Double-discharge stops compiling.** `Owned` is not `Copy` and not `Clone`;
   passing it to two consumers is a move-checker error. The hand-written
   analogue of the 0782 shape is unwritable.
2. **A minted-and-abandoned reference becomes a located failure.** `Owned` is
   `#[must_use]` and carries a debug-profile drop bomb naming the handle value
   and the frame. The RE-1 class (0835 — a walk minting `n + h − 1` references
   no owner holds) produces one bomb per surplus reference at the exact frame
   that minted it, instead of an integer nobody audits.
3. **The consuming convention stops being rustdoc.** `cargo check` enforces it
   at every call site including future ones — Principle 18 (enforce invariants
   structurally) and Principle 20 (model invariants by representation) applied
   to the one surface that never received them.

What it does **not** buy is stated at §10 and is not softened anywhere in this
document.

---

## 2. The vocabulary

New module `crates/cranelisp-intrinsics/src/handle.rs`. It is `pub` because
tranche A forces it public (`consume_*` are `pub` and the types appear in their
signatures), which is what makes tranche B-int possible; the Principle-15 home
is intrinsics because the *discharge behaviour* lives there.

### 2.1 `Owned` — a counted reference the holder must discharge

```rust
#[repr(transparent)]
#[must_use = "an Owned heap reference must be discharged (consumed, stored, or \
              returned across the ABI shim) — dropping it on the floor leaks"]
pub struct Owned(i64);          // NO Copy, NO Clone, NO public field
```

`#[repr(transparent)]` over `i64` is required, not cosmetic: it keeps the type
layout-identical to the ABI value so no representation question can arise at
the shim, and it is the same discipline Principle 14 (FFI layout) already
applies to the header consts.

**The closed operation set.** These are all of them. Adding an operation to this
list is an `/arch`-visible change to the trusted base, not a convenience edit.

| Operation | Signature | Role |
|---|---|---|
| `from_abi` | `unsafe fn from_abi(raw: i64) -> Owned` | **The one raw entry.** The shim's assertion that the ABI transferred a reference. Nullary-tag-safe (the guard stays inside the consume fns, unchanged). |
| `into_raw` | `#[must_use] fn into_raw(self) -> i64` | **The one raw exit.** Returning across the ABI shim. Disarms the bomb; contains the crate's only `mem::forget`. |
| `as_borrowed` | `fn as_borrowed(&self) -> Borrowed<'_>` | Read access without discharging. The brand ties the borrow to this frame's `Owned`. |
| `raw_for_read` | `fn raw_for_read(&self) -> i64` | Feed the raw layout accessors (`heap_access::read_i64`, `HeapString` reads). Takes `&self`, so it cannot discharge. |
| `is_nullary_tag` | `fn is_nullary_tag(&self) -> bool` | The `< NULLARY_TAG_THRESHOLD` predicate, single-sourced. |

`Drop` (debug only):

```rust
#[cfg(debug_assertions)]
impl Drop for Owned {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            panic!("LEAKED Owned heap handle {:#x} — dropped without discharge …", self.0);
        }
    }
}
```

The `thread::panicking()` clause is load-bearing and is proven by a dedicated
row (§5, leg 3): without it, an `Owned` alive during an unrelated panic turns
every such unwind into a double-panic **abort**, which would break the crate's
existing `#[should_panic]` detection triplets in `diagnostics/tests.rs`. This is
the same failure shape as the S118 W2a precheck-hoist discovery — an instrument
whose ordering, not whose logic, was wrong.

### 2.2 `Borrowed<'a>` — read access with no discharge obligation

```rust
#[derive(Clone, Copy)]
pub struct Borrowed<'a>(i64, PhantomData<&'a ()>);
```

| Operation | Signature | Role |
|---|---|---|
| `from_abi` | `unsafe fn from_abi(raw: i64) -> Borrowed<'static>` | Shim entry for a **retained** (non-consumed) ABI parameter. Exactly one row uses it today (§4.3). |
| `to_owned` | `fn to_owned(self) -> Owned` | **The single home of `rc_inc`.** Every new reference in the pair's Rust bodies is minted here. |
| `raw_for_read` | `fn raw_for_read(self) -> i64` | Feed the layout accessors. |

`Borrowed` has **no discharge operation at all** — the type has no way to reach
a `consume_*`. That is the enforceable half of the paper's "cannot be stored".

**Honest limit, stated up front (§10.2):** a `Copy` newtype can always be
stored in a struct; "cannot be stored" is not a property Rust gives us for free.
The lifetime brand prevents a `Borrowed` derived from an `Owned` via
`as_borrowed` from *outliving* that `Owned`, which is the hazard that actually
occurs in the pair (reading a node's fields across its own dec). The
`from_abi` form is `'static`-branded and therefore unbranded in practice — that
is the shim's honest limit, not a modelling error.

### 2.3 Why not a lifetime-free `Borrowed`, and why not a callback-only borrow

The paper's `Borrowed(i64)` is lifetime-free; the S117 Vec-of-String precedent
uses a callback-scoped borrow (`with_vec_strings`) that cannot escape at all.
Ruled: **brand the lifetime, keep the callback form where it already exists.**
The callback form is the stronger guarantee but costs a closure and a
control-flow inversion at every site; it is right for a Vec view spanning many
elements and wrong for `let head = node.as_borrowed()` in the middle of
`consume_slist`. The brand costs one `<'_>` in signatures and buys the escape
check on exactly the reads the funnel performs. `with_vec_strings` is unchanged
by this tranche.

---

## 3. The trusted base, counted

§2.2 of the option paper states the honest limit: Rust cannot enforce
exactly-once. What the discipline buys is a *narrowing* of the trusted base
from "every call site in two crates" to a small enumerable set. Tranche A makes
that set countable, and countable means checkable:

| Trusted item | Where | Count |
|---|---|---|
| `Owned::from_abi` — asserts an incoming ABI value is a transferred reference | `handle.rs` | 1 definition |
| `Owned::into_raw` — the only `mem::forget` in the pair's non-test code | `handle.rs` | 1 definition |
| `Borrowed::from_abi` — asserts an incoming ABI value is retained by the caller | `handle.rs` | 1 definition |
| `impl Drop for Owned` | `handle.rs` | 1 definition |
| Shim wrapping (derived, §4) | `declaration_macro.rs` | 1 generator |
| Hand-written intrinsics extern shims that wrap (§10.3) | `trace.rs`, `io.rs` | 6 call sites |

**Structural guard (a `/review` reject criterion, and a unit row).** The
crate's established grep-gate pattern applies:

- `impl Clone for Owned` / `impl Copy for Owned` / `derive(Clone` on `Owned`
  — must not appear.
- `mem::forget` must appear exactly once in `crates/cranelisp-intrinsics/src`
  outside `*/tests.rs`, and that occurrence must be inside `Owned::into_raw`.
- `Owned::from_abi` / `Borrowed::from_abi` call sites outside `handle.rs`,
  `declaration_macro.rs`, and the six enumerated intrinsics shims must be zero
  in non-test code.

The third row is the one that keeps the base from silently widening: without
it, "just wrap it here too" is a one-line edit that re-opens the class. This is
the same shape as the S110 `resolve_driven` grep gate — the count *is* the
contract (Principle 13, interfaces are auditable).

---

## 4. The shim-fact derivation (gate G4)

> The shim can lie: an extern wrapper that wraps a borrowed parameter as
> `Owned` mis-declares just as prose can. The mitigation is that the shim
> annotations are **generated from, or checked against, the declaration-table
> facts — not hand-written twice** (option paper §2.2, Principle 7).

### 4.1 Three statements of one fact; rustc enforces two, a unit row the third

For every user-callable primitive there are three places the ownership fact
appears, and after this tranche all three are mechanically tied together:

1. **The implementation signature** — `fn str_concat(a: Owned, b: Owned) -> Owned`.
   Enforced by **rustc against the body**: an `Owned` that is neither
   discharged nor returned bombs; a `Borrowed` cannot be discharged at all.
2. **The shim tokens** — the Rust types written in the row's `shim:` clause.
   Enforced by **rustc against (1)** at the macro's
   `$implementation($($callarg),*)` expansion — a row whose shim tokens
   disagree with its implementation does not compile.
3. **The declared Cranelisp type** — the row's `Type::Fn(params, result)`,
   already present and already the input to
   `ownership_facts::{copy_fresh_for_type, uniform_for_type}`. Tied to (2) by
   **one new unit row** over `declarations()`.

The derivation is one function, and it is a function the crate already
computes twice by hand:

```rust
// crates/cranelisp-primitives/src/abi_facts.rs   (new; ~30 lines)

pub(crate) enum AbiKind { Scalar, OwnedHandle, BorrowedHandle }

/// Is this declared Cranelisp parameter type carried as a heap handle at the ABI?
/// SINGLE SOURCE — `ownership_facts::{copy_fresh_for_type, uniform_for_type}`
/// stop open-coding `matches!(ty, Int | Bool | Float)` and call this.
pub(crate) fn is_heap_carried(ty: &Type) -> bool { !matches!(ty, Type::Int | Type::Bool | Type::Float) }

/// The ABI handle kinds a row's declared type + declared ParamFlow imply.
pub(crate) fn abi_kinds_for(ty: &Type, flow: &[ParamFlow]) -> Vec<AbiKind>;
```

The two-axis rule, stated once:

```
kind(i) = Scalar          if !is_heap_carried(param_type[i])
        = BorrowedHandle  if flow[i] == ParamFlow::IntoResult   // retained by the caller
        = OwnedHandle     otherwise                              // Decision-24 consuming
```

**`Mode` is deliberately NOT an input.** The S102 CS-B split ruling stands: an
only-read heap parameter (`str-eq`, `str-len`, the `?`-predicates, `vec-len`) is
declared `Mode::Borrowed` — the *analysis* fact — while the extern body still
consumes, because the Decision-24 ABI is unchanged. Deriving the shim kind from
`Mode` would flip five rows to `Borrowed` and silently delete five decs. The
ABI axis is `ParamFlow`, and the check must read `ParamFlow`. Recording this is
half the point of writing the derivation down: it is exactly the kind of
plausible-but-wrong single-sourcing that a hand-written second assertion would
have hidden.

### 4.2 How the macro emits both manifestations from one token

`declaration_macro.rs` changes the shim generator so the *declared Rust
parameter type* is the annotation, consumed twice from the same token:

```rust
// The shim's own signature stays i64 — the ABI is byte-identical (§7 class 2).
#[unsafe(export_name = $ename)]
pub(crate) extern "C" fn $shim($($arg: i64),*) -> i64 {
    // SAFETY: the ABI contract for this row, single-sourced from its
    // declared type + ParamFlow and unit-checked by `shim_abi_kinds_match_declared_facts`.
    $implementation($(unsafe { <$argty as AbiHandle>::from_abi($arg) }),*).into_abi()
}
```

and, in the same expansion, emits the fact as **data**:

```rust
declarations.push(PrimitiveDecl::UserExtern {
    …,
    abi_param_kinds: vec![$(<$argty as AbiHandle>::KIND),*],   // ← same $argty token
    abi_result_kind: <$retty as AbiHandle>::KIND,
});
```

with

```rust
pub(crate) trait AbiHandle { const KIND: AbiKind; unsafe fn from_abi(raw: i64) -> Self; }
impl AbiHandle for Owned              { const KIND: AbiKind = AbiKind::OwnedHandle;    … }
impl AbiHandle for Borrowed<'static>  { const KIND: AbiKind = AbiKind::BorrowedHandle; … }
impl AbiHandle for i64                { const KIND: AbiKind = AbiKind::Scalar;         … }
```

**One derivation**: the `$argty` token produces the wrapping code *and* the
`AbiKind` datum through the same trait. There is no second hand-written
assertion anywhere.

### 4.3 The check, and the one row that proves it bites

New unit row in `declarations/tests.rs`:

```
shim_abi_kinds_match_declared_facts:
  for every UserExtern row:
    assert_eq!(row.abi_param_kinds, abi_kinds_for(&row.scheme.ty, &row.ownership.param_flow));
    assert_eq!(row.abi_result_kind, result_kind_for(&row.scheme.ty));
```

To lie at a shim you must now write `a: Borrowed<'static>` for a parameter the
row's own declared type and `ParamFlow` say is consumed — and the row fails.

**`string-identity` is the deviation that proves the check is not a tautology.**
Its `ownership_facts::alias_of_zero()` declares `ParamFlow::IntoResult`, i.e.
*not consumed*, and its body matches: it `rc_inc`s and returns, and never decs.
Under a `Mode`-blind or a flow-blind derivation it would be `Owned` and the
typed body would be forced to either leak the incoming handle or delete the
inc — a real arithmetic change smuggled in as churn. The two-axis rule assigns
it `Borrowed`, and the byte-identical typed body is:

```rust
pub(crate) fn string_identity(s: Borrowed<'_>) -> Owned { s.to_owned() }
```

one `rc_inc`, no dec — arithmetic identical to today's
`rc::rc_inc(s); s`. It is also the tranche's proof that `Borrowed` is not
landed with zero consumers.

### 4.4 Coverage and the named exemption

The derivation covers **every row in the primitives declaration table** — all
`user_extern` and `user_inline` rows, i.e. 100% of the user-callable surface.

Not covered, and enumerated rather than hand-waved:

- **`harvest_only` rows** carry no declared Cranelisp type and no `ownership:`
  summary (`declarations.rs` tail). Three of the four — `neq-i64`, `neq-f64`,
  `neq-bool` — are all-scalar and the check asserts exactly that. The fourth,
  **`sconcat`**, is the one genuine exemption: its type is seeded into the
  synthetic `macros` module by int's `bootstrap.rs`, outside the pair. Its shim
  kinds are therefore tied only by legs (1) and (2) — rustc against the body,
  which for `sconcat` means `consume_slist(xs)`/`consume_slist(ys)` force
  `Owned` — with no third leg. The exemption is a **named allow-list of one**
  in the check, mirroring the existing
  `tests.rs::extern_shims_harvest_covers_full_inventory` allow-list pattern.
  Growing that list past one name is a `/review` reject.
- **The 81 hand-written `cranelisp-intrinsics` extern shims** have no
  declaration table. G4's text scopes the derivation to *the* declaration
  table, which is primitives'; intrinsics' externs are §10.3 and tranche C.

---

## 5. The drop-bomb detection proof (gate G4, FIXME 0768)

> An instrument is unverified until it is proven to detect.

The proof obligation applies to the **drop bomb** and not to the move-checker
half, and the asymmetry is principled, not convenient: rustc's move checker
cannot silently fail to detect — its failure mode is a build failure, which is
loud. The drop bomb *can* silently fail (a `Drop` impl removed, the `cfg`
inverted, the `thread::panicking()` clause swallowing everything), so it needs
positive evidence. The compile-time half's guard is the §3 structural gate,
which is what actually keeps it from being widened away.

**A triplet, not a row** — matching the crate's existing A1–A4 detection
triplets in `diagnostics/tests.rs`. All three live in
`crates/cranelisp-intrinsics/src/handle/tests.rs`, are ordinary
non-`#[ignore]`d tests, and are `#[cfg(debug_assertions)]`-gated because the
instrument is:

1. **Positive detection — the deliberate leak on the floor.**
   `#[should_panic(expected = "LEAKED Owned heap handle")]`. Body: allocate a
   real `HeapString`, wrap it as `Owned`, drop it without discharging. The bomb
   must fire, and the expected-message match must include the *located* prefix,
   not just "panic". Nextest's process-per-test isolation means the genuinely
   leaked allocation cannot contaminate any sibling balance row.
2. **No false positive — the same fixture, discharged.** The identical fixture
   passed to `rc::consume_shallow` must not panic **and** must satisfy the
   crate's `assert_balanced` alloc==dealloc helper. This is the leg the W2a
   precheck-hoist arc showed is routinely missing: a detector that fires on
   correct code is not a working detector, and only this row distinguishes the
   two.
3. **Survivable under an unrelated unwind.** A live `Owned` in scope when an
   unrelated `panic!` unwinds:
   `#[should_panic(expected = "<the unrelated message>")]`. If the
   `thread::panicking()` clause were absent the bomb would fire during the
   unwind, the process would abort, and the row would fail rather than pass with
   the expected message. This row fails on deletion of the *clause alone*, not
   only of the check — the S118 ordering lesson applied.

**Attribution rule for `/dev` and `/review`:** each of the three must be
observed RED against a deliberately broken instrument before the tranche is
declared landed (bomb deleted ⇒ 1 REDs; bomb made unconditional ⇒ 3 REDs;
`cfg` inverted ⇒ 1 and 3 RED). Recording those observations in the change-set
is the proof; asserting the capability is not.

---

## 6. The slice — exact before/after counts (gate G3)

### 6.1 The baseline measurement, pinned

The sprint's **136** is reproducible by exactly this command, and the change-set
must record the before/after pair from it verbatim:

```bash
P="crates/cranelisp-primitives/src crates/cranelisp-intrinsics/src"
grep -rnE '^\s*(pub(\(crate\))?\s+)?(unsafe\s+)?fn\s+\w+\(.*i64' $P \
  | grep -v 'extern "C"' | grep -v '/tests.rs:' | grep -v 'rc_balance.rs:' | wc -l
# 136 at 5520186d
```

**Finding, and it changes how G3 must be read.** That number is *syntactic* —
"non-extern declarations whose signature line mentions `i64`" — while G3's
acceptance is *semantic*: "raw-`i64` **heap-handle** internal declarations".
The two differ materially:

- **30 of the 136 are `ring0.rs` scalar arithmetic** (`add_i64`, `lt_f64`, …).
  They take `i64` as `Int`/`Float`/`Bool`, never as a handle. They will never
  flip, in any tranche.
- **3 more** (`float_to_string`, `bool_to_string`, `int_to_string`) take a
  scalar and return a handle. Their *return* flips to `Owned`, but their
  signature line still mentions `i64`, so the syntactic count does not move for
  them even though the tranche did its job.

Reporting only the syntactic delta would therefore under-report the tranche and
make the gate unfalsifiable in both directions. **Ruled: the change-set records
both numbers, with the semantic one as the acceptance quantity.**

### 6.2 The semantic baseline

Define **N_heap** = declarations in the 136 that take or return a heap handle.
Enumerated against the pinned list, the pair's N_heap at `5520186d` is **103**
(136 − 30 `ring0.rs` − 3 non-handle helpers: `alloc::freed_info`,
`alloc::live_alloc_snapshot`, `diagnostics::header_size_plausible`). `/dev`
re-derives and records the enumeration in the change-set; the classification,
not the arithmetic, is the auditable artifact.

### 6.3 Tranche A's exact slice — 42 declarations

| Slice | Declarations | Flip to |
|---|---|---|
| **A1 — the intrinsics discharge funnel** | `rc::consume_shallow`, `drop::{consume_slist, consume_sexp, consume_vec_with, consume_vec_of_string, consume_io_tree, consume_closure, dec_shallow_io, free_io_branches}`, `trace::consume_trace_call` | 10 |
| **A2 — primitives implementation fns reached by an extern shim** | `string.rs` ×16, `int.rs` ×2 (`int_to_string`, `parse_int`), `marshal.rs` ×2 (`sconcat`, `quote_sexp`), `vec.rs` ×1 (`vec_len`), `float.rs` ×1, `bool.rs` ×1 | 23 |
| **A3 — the marshal interior forced by A2** | `alloc_adt_2`, `alloc_adt_3`, `build_runtime_list`, `read_slist`, `alloc_runtime_string`, `make_sexp_sym`, `shallow_rc_inc`, `quote_sexp_build`, `quote_slist` | 9 |
| **Total** | | **42** |

**N_heap: 103 → 61.** Syntactic 136 → ~100 (the 3 scalar-param/heap-result rows
and the `tag: i64` parameters of `alloc_adt_*` keep their lines counted).

**Deliberately NOT flipped, with reasons** — these are the residue G3 must not
be read as covering:

- `drop::atomic_dec_rc(ptr: i64) -> i64` and `rc::nonatomic_rc_rmw` — *beneath*
  the abstraction. Each `consume_*` destructures its `Owned` into a raw at the
  top and hands the raw to the RMW; typing the RMW would require an `Owned` to
  survive its own dec.
- `heap_access::{read_i64, write_i64}`, `marshal.rs`/`trace.rs`'s local
  `read_i64`/`write_i64` — the mechanical accessor layer (MED-1 / FIXME 0370).
  They take a base and an offset, not a handle.
- `rc::rc_inc(ptr: i64)` — stays `pub` and raw. It is the *mechanism*;
  `Borrowed::to_owned` is the only typed mint and delegates to it. Retiring it
  to `pub(crate)` would touch `design/intrinsics/rc-inc-entry-point.md`'s
  blessed-entry-point ruling and reaches `io.rs`/`trace.rs` — tranche C.
- Everything in `io.rs`, `reactor.rs`, `ivar.rs`, `vec_runtime.rs`,
  `trace_format.rs` beyond the funnel entries above — tranche C.

### 6.4 The 36 `consume_*` call sites, decomposed

The sprint's **36** is the grep-token count of `consume_` in non-test primitives
sources (`string.rs` 27, `marshal.rs` 8, `int.rs` 1). Its production
decomposition, which is what `/dev` and `/review` should count:

| File | Actual call sites | Doc/`use` mentions |
|---|---|---|
| `string.rs` | 25 | 2 |
| `marshal.rs` | 3 | 5 (incl. the `use` line) |
| `int.rs` | 1 | 0 |
| **production total** | **29** | 7 |

Plus **30 test-tier call sites** in the pair's primitives-side tests
(`string/tests.rs` 4, `marshal/tests.rs` 26) and **~110** in intrinsics tests,
all of which the flip reaches. G3's "36 call sites flipped" is satisfied by 29
production + the test tier; the number to report is the pair of counts, not the
grep token.

---

## 7. Churn safety — how "byte-identical instrument re-run" is made checkable

The acceptance criterion is that the S118 instrument set re-runs byte-identically
across the signature churn. That cannot be literally true of every file (some
instruments are *deliberately illegal* under the discipline), so the criterion
is ruled as **three graded classes, each with its own check**. This is the
acceptance criterion for churn masking a behaviour change; a `/review` that
cannot name which class a diff hunk falls in has not checked it.

**Class 1 — zero diff, absolutely.** Everything outside the pair. These call
through the ABI and must not be touched at all:
`tests/marginal_harness_capability.rs`, `tests/slist_sconcat_ownership_0835.rs`,
`tests/ownership_fences.rs`, `tests/detector_arming_discipline_guard.rs`,
`tests/s99_fixtures.rs`, and the golden-CLIF corpus.
**Check:** `git diff --stat` names none of them. This is the strong leg, and it
is the one that actually proves the ABI is byte-identical — an ABI change would
surface here or nowhere.

> One known out-of-pair exception, flagged for `/sprint` because it is *not* in
> the pair and therefore not this tranche's to edit under the narrow-deployment
> rule: `crates/cranelisp-backend/src/compiler/control_flow/launch.rs:452`
> (inside that file's `#[cfg(test)] mod tests`) calls
> `cranelisp_intrinsics::drop::consume_closure(cont_ptr)` with a raw `i64`. It
> will not compile after A1. It needs a one-line `unsafe { Owned::from_abi(…) }`
> wrap by `/dev`(backend), or an explicit dispensation for `/dev`(runtime pair)
> to touch that one line. **This is the only known out-of-pair source impact of
> tranche A** (verified workspace-wide; `src/` has no `consume_*` call, matching
> `/arch`'s Phase-2 finding).

**Class 2 — types-only diff.** The in-pair instruments whose *assertions* must
be unchanged: `crates/cranelisp-primitives/src/marshal/tests.rs` (the RE-1
fences, the 0885 inc-tally fence, the shared-tail negative cell),
`crates/cranelisp-intrinsics/src/drop/rc_balance.rs`,
`crates/cranelisp-intrinsics/src/diagnostics/tests.rs` (the A1–A4 triplets and
the fault-plant rows).
**Check, mechanical:** for each of these files, every diff hunk must be
explicable as a type/path change. Any hunk that changes a numeric literal, a
comparison operator, or the text inside an `assert*!` is a `/review` reject.
`git diff -U0 -- <files> | grep -E '^[+-].*(assert|[0-9])'` is the screen.

**Design move that makes Class 2 cheap:** keep the *call syntax* stable by
flipping the fixtures' return types, not the call expressions. When
`make_scons(...)` returns `Owned`, the line `consume_slist(result);` is
unchanged text. Most of the 30 primitives-side and ~110 intrinsics-side test
call sites survive verbatim on this basis.

**Class 3 — the enumerated deliberately-illegal rows.** Instruments that assert
a *double* discharge or discharge a *stale* pointer cannot compile as written.
Enumerated now so `/review` can check the count did not grow:

| Row | Today | Typed re-expression |
|---|---|---|
| `marshal/tests.rs:456-458` | `shallow_rc_inc(cell); consume_sexp(cell); consume_sexp(cell);` | Legal and *more truthful*: `let a = Owned::…; let b = a.as_borrowed().to_owned(); consume_sexp(a); consume_sexp(b);` — the type now names which reference is which. |
| `rc/tests.rs:61-64` | `rc_inc(base); consume_shallow(base); consume_shallow(base);` | Same shape. |
| `rc/tests.rs:52`, `diagnostics/tests.rs` plants | stale inc/dec of a freed pointer | `unsafe { Owned::from_abi(raw) }` — the raw entry, which is what a stale-pointer plant genuinely is. |
| `rc/tests.rs:77-80`, `drop/tests.rs:438-440,536-540` | `consume_*(0 / 1 / THRESHOLD-1)` bare tags | `unsafe { Owned::from_abi(0) }` — legitimate; the ABI does hand nullary tags in as owned values. |

**Ruled: no new escape hatch is minted for Class 3.** Every row re-expresses
through `from_abi` or through the legal two-reference form. If `/dev` finds a
row that needs something else, that is a design gap and returns here as a FIXME
`target: /design` — it is **not** grounds for adding an operation to §2.1's
closed set.

---

## 8. Public-API delta (for `/arch` at the Phase-3 exit gate)

### `cranelisp-intrinsics` — additive

```
pub mod cranelisp_intrinsics::handle
pub struct cranelisp_intrinsics::handle::Owned
pub struct cranelisp_intrinsics::handle::Borrowed<'a>
impl cranelisp_intrinsics::handle::Owned
    pub unsafe fn from_abi(raw: i64) -> Owned
    pub fn into_raw(self) -> i64
    pub fn as_borrowed(&self) -> Borrowed<'_>
    pub fn raw_for_read(&self) -> i64
    pub fn is_nullary_tag(&self) -> bool
impl<'a> cranelisp_intrinsics::handle::Borrowed<'a>
    pub unsafe fn from_abi(raw: i64) -> Borrowed<'static>
    pub fn to_owned(self) -> Owned
    pub fn raw_for_read(self) -> i64
impl core::marker::Copy for cranelisp_intrinsics::handle::Borrowed<'a>
impl core::clone::Clone for cranelisp_intrinsics::handle::Borrowed<'a>
impl core::ops::Drop for cranelisp_intrinsics::handle::Owned     // debug profile only
```

Note for the baseline diff: the `Drop` impl is `#[cfg(debug_assertions)]`, so
`cargo public-api` output differs between profiles. **Ruled: the committed
baseline is generated in the default (debug) profile, as today**, and a comment
in `public-api.txt`'s companion rustdoc names the conditionality. `/arch` should
confirm; if a profile-invariant baseline is required, the alternative is a
`#[cfg(not(debug_assertions))] impl Drop for Owned { fn drop(&mut self) {} }`
so the item exists in both — additional code for a documentation property, which
this design does not recommend.

### `cranelisp-intrinsics` — changed signatures (10)

```
- pub fn cranelisp_intrinsics::rc::consume_shallow(ptr: i64)
+ pub fn cranelisp_intrinsics::rc::consume_shallow(h: Owned)
- pub fn cranelisp_intrinsics::drop::consume_slist(ptr: i64)
+ pub fn cranelisp_intrinsics::drop::consume_slist(h: Owned)
- pub fn cranelisp_intrinsics::drop::consume_sexp(ptr: i64)
+ pub fn cranelisp_intrinsics::drop::consume_sexp(h: Owned)
- pub fn cranelisp_intrinsics::drop::consume_vec_with(ptr: i64, elem_consume: fn(i64))
+ pub fn cranelisp_intrinsics::drop::consume_vec_with(h: Owned, elem_consume: fn(Owned))
- pub fn cranelisp_intrinsics::drop::consume_vec_of_string(ptr: i64)
+ pub fn cranelisp_intrinsics::drop::consume_vec_of_string(h: Owned)
- pub fn cranelisp_intrinsics::drop::consume_io_tree(ptr: i64)
+ pub fn cranelisp_intrinsics::drop::consume_io_tree(h: Owned)
- pub fn cranelisp_intrinsics::drop::consume_closure(ptr: i64)
+ pub fn cranelisp_intrinsics::drop::consume_closure(h: Owned)
- pub fn cranelisp_intrinsics::drop::dec_shallow_io(ptr: i64)
+ pub fn cranelisp_intrinsics::drop::dec_shallow_io(h: Owned)
- pub fn cranelisp_intrinsics::trace::consume_trace_call(ptr: i64)
+ pub fn cranelisp_intrinsics::trace::consume_trace_call(h: Owned)
  (private: drop::free_io_branches(ptr: i64, tag) → (h: Borrowed<'_>, tag))
```

`ElemConsumeFn` is `pub(crate)` today (a private type alias over `fn(i64)`); it
becomes `fn(Owned)`, which appears in `consume_vec_with`'s public signature.
`/arch` should rule whether the alias is promoted to `pub` for readability or
the signature spells the fn-pointer type inline. **Recommendation: spell it
inline** — a `pub` alias adds a name to the surface for no consumer.

### `cranelisp-primitives` — zero delta

The crate's entire public surface is `PRIMITIVES_TABLE`, `PRIMITIVES_GOT_SLAB`,
and seven `pub mod` (`CLAUDE.md` §"The public Rust surface is ONE item"). Every
implementation fn and every generated shim is `pub(crate)`. **The primitives
`public-api.txt` is expected byte-identical.** The sprint's "primitives delta
confined to its two shims if `pub`" resolves to *no delta* — the two `extern "C"`
occurrences are inside `declaration_macro.rs`'s expansion and are `pub(crate)`.

### ABI — byte-identical

Every generated shim keeps `extern "C" fn(i64, …) -> i64`. Handle types appear
only *inside* the shim body. No `export_name` changes, no arity changes, no
`repr` change reaching a symbol. **`cranelisp-types`: zero delta**, as
authorized.

---

## 9. Implementation order for `/dev`

Five change-sets, each independently `cargo check`-clean. The ordering is chosen
so the compiler enumerates the next step's worklist — the option paper's own
"signatures flip, `cargo check` enumerates every affected call site" discipline.

**CS-1 — the vocabulary, dormant.** `handle.rs` + `handle/tests.rs` (the §5
triplet) + the §3 structural grep gate. Nothing consumes the types yet; the
crate compiles unchanged. The triplet is RED-observed against a broken bomb
here, before any consumer exists, so the instrument is proven before it is
relied on. *This is the change-set that answers "landed with zero consumers is
not landed" — it does not land alone; CS-2 is in the same wave.*

**CS-2 — A1, the intrinsics discharge funnel.** The 10 signatures. `cargo check`
then enumerates every in-crate caller (io.rs 9, trace.rs 12, panic.rs 2,
reactor.rs 2, vec_runtime.rs 1, drop.rs 20 internal, plus ~110 test sites) and
the 6 hand-written extern shims that must wrap. Class-2/Class-3 rules from §7
govern the test edits. `free_io_branches` takes `Borrowed<'_>` — the first
non-shim `Borrowed` consumer.

**CS-3 — A3 then A2, primitives.** A3 first (`marshal.rs`'s interior: this is
where the 0835 contract becomes a signature — `read_slist` returns
`Vec<Borrowed<'_>>`, `alloc_adt_3` takes `Owned` fields, and RE-1's "one inc on
the node stored" is spelled as a single `to_owned()`), then A2's 23
implementation fns. The 29 production consume sites flip here.

**CS-4 — the derivation.** `abi_facts.rs`, the `AbiHandle` trait, the
`declaration_macro.rs` shim generator, the two `PrimitiveDecl::UserExtern`
fields, `ownership_facts.rs` hoisted onto `is_heap_carried`, and the
`shim_abi_kinds_match_declared_facts` row with its one-name allow-list.
`string-identity` flips to `Borrowed` here and its arithmetic must be shown
unchanged.

**CS-5 — the counts and the gate.** Re-run the §6.1 command; record the
before/after pair and the N_heap enumeration in the change-set; run the §7
Class-1 zero-diff check and the §7 Class-2 screen; regenerate both crates'
`public-api.txt` (intrinsics changes, primitives must not).

**Wave constraint (from `/arch`, restated because it binds `/dev`):** the
Spine-1 backend implementation and this signature churn **never share a wave**.
Each needs its own byte-identical instrument re-run for drift to stay
attributable.

---

## 10. Honest limits

**10.1 Exactly-once is not enforced.** `mem::forget` exists; a shim can lie.
What tranche A delivers is the §3 narrowing — a trusted base of 4 definitions +
1 generator + 6 hand-written sites, guarded by a grep gate that makes its
growth visible. It is a large reduction from "every call site in two crates",
not an elimination, and this document does not claim otherwise anywhere.

**10.2 "Cannot be stored" is partly aspirational.** §2.2. The enforceable
properties are: `Borrowed` has no discharge operation, and a `Borrowed` derived
via `as_borrowed` cannot outlive its `Owned`. A `Borrowed` obtained from
`from_abi` is `'static`-branded and can be stored. Tranche D may revisit if a
real storing hazard appears.

**10.3 The 81 intrinsics extern shims are not derived.** They are hand-written
and carry no declaration table, so their ownership facts are asserted at the
`from_abi` call and backed only by rustdoc. Six of them wrap after CS-2. The
natural second derivation home is `intrinsics_table()`
(`design/intrinsics/intrinsics-table.md`) — a tranche-C/D candidate, not
authorized here, and **not** claimed under G4, whose text scopes the derivation
to the declaration table.

**10.4 FIXME 0859 is not discharged.** 0859's undischarged residual is a
*production-artifact* witness for `ProjectionOf(0)` on the **inline** `vec-get`
row — inline rows have no shim, so the derivation never touches them. What §4.3
does add is a declaration-sensitive check for a different class: a false
`ParamFlow` on any extern row now breaks a unit row. That narrows 0859's surface
by one class and is worth recording in its file; it does not close it, and the
`ProjectionOf` question is untouched. `/qa` retains the disposition.

**10.5 A parameter's *storage* obligation is still prose.** The type says
consumed-or-borrowed. It does not say "this handle is stored into a structure
whose drop glue will later discharge it" versus "this handle is discharged
here". `alloc_adt_3(tag, field0: Owned, field1: Owned) -> Owned` expresses the
transfer, which is the load-bearing half, but the *identity* of the eventual
discharger is not in the type. That is drop-glue identity — Spine 1's territory,
not this tranche's.

---

## 11. Principles applied

- **Principle 7 (single source of truth)** — §4. One derivation from the
  `$argty` token to both the wrapping and the `AbiKind` datum; `is_heap_carried`
  hoisted out of the two open-coded copies in `ownership_facts.rs`.
- **Principle 18 (enforce invariants structurally)** — the move checker replaces
  the "dec every heap arg you do not return" rustdoc paragraph.
- **Principle 20 (model invariants by representation)** — "this reference has an
  outstanding discharge obligation" becomes a type, not a comment.
- **Principle 25 (narrowing carries its check)** — the drop bomb is the check
  that accompanies the narrowing "this frame is done with this reference".
- **Principle 13 (interfaces are auditable)** — §3's counted trusted base and
  its grep gate.
- **Principle 6 (complexity has a budget)** — two types, eight operations, one
  new file in each crate. The lifetime brand is the single concept added beyond
  the paper's sketch, and §2.3 states what it buys.
- **Principle 8 (no interim implementations)** — the `i64` extern shim is the
  permanent ABI boundary, not a bridge; the A-landed / C-pending split is
  module-aligned, so no seam is left half-typed.

---

## 12. References

- `design/arch/ownership-stratum-options.md` §1.5, §2.1–§2.4 (as amended `3232a061`)
- `sprints/SPRINT.md` §Architecture review — gates G3, G4, and the wave constraint
- `design/runtime/s118-structural-embedding-ownership.md` — RE-1/RE-2/RE-3; the
  contract §6.3's `marshal.rs` interior now spells in types
- `design/runtime/s117-primitives-integrity.md` — the Vec-of-String boundary precedent
- `design/primitives/primitives.md` §3.2, §4 invariants 7 + 14
- `design/intrinsics/rc-inc-entry-point.md` — `rc_inc` stays the blessed mechanism;
  `Borrowed::to_owned` becomes its only typed caller
- `design/intrinsics/diagnostic-modes.md` §7.5 — the precheck-hoist precedent for §5 leg 3
- `crates/cranelisp-platform/src/lib.rs` — the `CLOwned<T>` family (tranche-D naming alignment)
- FIXME 0768 (detection proofs), FIXME 0859 (§10.4), FIXME 0885 (assert the rule, not the point)

## 13. Next skills

- `/arch` — the §8 `public-api.txt` delta at the Phase-3 exit gate; three
  specific rulings requested: the `ElemConsumeFn` spelling, the
  debug-profile-conditional `Drop` impl in the baseline, and the
  `launch.rs:452` cross-crate dispensation (§7 Class 1).
- `/dev` (runtime pair) — CS-1..CS-5 per §9, after the Spine-1 backend wave.
- `/qa` — the §5 triplet and the §7 three-class churn check want plan rows;
  §10.4 is a note for 0859's file, not a resolution.
- `/design` (int) — tranche B-int consumes this vocabulary; note that
  `src/marshal.rs:316` carries its own **non-atomic** `rc_inc` copy
  (`*rc_ptr += 1`), which the typed mint would replace.
