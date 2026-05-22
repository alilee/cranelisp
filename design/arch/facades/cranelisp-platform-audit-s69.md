# cranelisp-platform — Sprint 69 facade audit (per-item analysis, re-authored)

**Audit triple**: `crates/cranelisp-platform/src/lib.rs` (1140 LOC) × `design/arch/facades/platform.md` (337 LOC, binding contract) × `crates/cranelisp-platform/public-api.txt` (253 LOC, frozen baseline).

**Date**: 2026-05-19 (S69 Phase 3 Wave 1, second re-authoring).
**Auditor**: `/design` (cranelisp-platform narrow deployment).
**Inputs frozen at**: current commit on `main` (post-S68 close `9516dfc`).

**Discipline**. Per `memory/feedback_audit_per_item_analysis.md` (2026-05-18 user direction; 2026-05-19 follow-up). The prior re-author of this memo gave each finding the four blocks but disposed of them **without reading the architectural configuration that grounds the facade**. The user's correction:

> "the issue is that the audit did not read the architectural configuration and derived design docs."

This re-author reads the configuration first and grounds each disposition explicitly. The five-block structure per finding:

1. **What the facade expects** — quoted prescription with §section reference.
2. **What the source does** — as-built shape (`crates/cranelisp-platform/src/lib.rs` line numbers + `public-api.txt` lines).
3. **What is the design intent** — Decision / Principle / FIXME that grounds the facade text. If no grounding exists, name that explicitly. **Without intent, the disposition is unprincipled "whichever side is settled wins."**
4. **What the difference implies** — downstream cost; which side breaks if either moves.
5. **Disposition** — facade moves / source moves / both / arbitration. **Default: source moves to match facade when the facade is target-stating per Decision/Principle/FIXME.** "Facade moves" is correct only when the facade is genuinely stale (a later Decision retracted; source has evolved past) or sloppy authoring.

Companion exemplar: `design/arch/facades/types-audit-s69.md`.

---

## 0. Configuration grounding read first

Before any finding is dispositioned the audit reads:

- **Principles**: 03 (dependency direction), 06 (complexity budget), 07 (single source of truth), 14 (FFI layout discipline), 15 (facade types live with their behavior — platform external-audience exception), 18 (enforce invariants structurally).
- **Decisions (active)**: 0026 (`scheduling_class` on `PrimitiveKind::PlatformEffect` variant; platform fn ptrs reached via `ModuleEntry::Def.got_slot`; `PlatformRegistry` deleted; S66 amendment + rollback `1dc57ae` — GOT is the single source of truth for callable addresses), 0031 (per-batch JIT; callback support forward-commitment — `Fn a b` row reserved per spec §10.10.1), 0041 (`Code` moves to `cranelisp-backend`; per-symbol JIT cardinality), 0042 (`PlatformError` is `cranelisp-types`-hosted with `ErrorLocation` carriers; surfaces via `CranelispError::Platform`; pre-implementation when filed, now **landed in source** per six-test pin), 0043 (runtime split; backend has no trait knowledge), 0048 (primitives' SymbolTable + GOT static in crate; structural dep-ban as worked example of Principle 18).
- **Decisions (legacy — embodied)**: 0011 (heap closure layout — forward-commitment for callback row), 0013 (atomic RC `SeqCst`), 0024 (consuming calling convention; `into_owned_consuming`).
- **Bounded contexts**: `bounded-contexts.md` §5 Platform — shared interface contract crate; owns no runtime state; DLL lifecycle is `int`'s job per BC §6.
- **Sequences**: `sequences/exec-flow-runtime.{mmd,svg}` — IO trampoline + Effect-thunk consumption.
- **Per-crate design doc**: `design/platform/platform.md` — master design overview; §3 enumerates as-built vs as-designed drift the previous platform-pass recorded (now mostly resolved).
- **FIXMEs**: `design/arch/fixmes/` — 0104 (PlatformError adoption — pre-implementation when filed; **now closed in substance** per source six-test pin and §"Errors" facade alignment; the FIXME file at `fixmes/0104-dev-types-platform-int-platformerror-adoption.md` still exists but the `cranelisp-platform`-side work it tracked has landed). 0106 (archive `platform-registry-removal.md`). 0107 (add `#[non_exhaustive]` to `OwnedPlatformFnDescriptor` — **closed**: source carries the annotation per public-api line 168, FIXME file no longer present in `fixmes/`). 0155 (clarify `load_manifest`/`parse_type_sig` placement — **closed**: not present in `fixmes/`; facade now states these are `pub(crate)`/`int`-side per §"Host-side descriptors" + §"Type signature parser — internal only").

Grounding outcome: the platform crate's substantive architectural commitments (Decision 0042; the §10.10.1 callback row forward-commitment per Decision 0031; the GOT-dispatch model per Decision 0026 + 0048; Principle 14 layout discipline + Principle 15 external-audience exception) are **landed in source and faithfully reflected in the facade's authoritative sections**. The drift the prior audit catalogued is real, but its disposition shape differs once the configuration is loaded. §1 below works each finding under the five-block discipline; §2 compares this audit's dispositions to the prior audit's and explicitly flags every flip.

---

## 1. Findings (F1–F9) — per-item five-block analysis

### Finding F1 — `CLOwned::into_inner(self) -> T` named in facade; absent in source

**1. What the facade expects.** `facades/platform.md` §"Heap-typed values crossed between platform and runtime", lines 80–83:

```rust
impl<T: CLHeap> CLOwned<T> {
    pub fn new(val: T) -> Self;          // takes ownership — drops invoke rc_dec via HostCallbacks
    pub fn into_inner(self) -> T;        // release ownership without dec'ing
}
```

Prose at line 88: "`CLOwned<T>` lets platform DLL code hold heap-typed Cranelisp values across multiple host-callback invocations with correct RC discipline."

Two methods on `CLOwned<T>`: `new` (constructor with inc-on-wrap) and `into_inner` (release without dec).

**2. What the source does.** `lib.rs:517–533`:

```rust
pub struct CLOwned<T: CLHeap> { inner: T }

impl<T: CLHeap> CLOwned<T> {
    pub fn new(val: T) -> Self { val.inc_rc(); CLOwned { inner: val } }
}
impl<T: CLHeap> Drop  for CLOwned<T> { fn drop(&mut self) { self.inner.dec_rc(); } }
impl<T: CLHeap> Deref for CLOwned<T> { type Target = T; fn deref(&self) -> &T { &self.inner } }
```

`public-api.txt:100–114`: only `new`, `drop`, `deref` (+ auto-trait impls). No `into_inner`. The complementary "skip the inc" entry point lives on `CLHeap`, not on `CLOwned`: `fn into_owned_consuming(self) -> CLOwned<Self>` (`lib.rs:502–506`).

**3. What is the design intent.** Two grounds to check:

- **Decision 0024 (consuming calling convention)** — `lib.rs:489–501` doc-comment cites `design/backend/ring2-rc.md` §10.4 Form B as the rationale: the platform extern receives a transferred reference (caller's +1), and `into_owned_consuming` constructs a `CLOwned` *without* inc'ing (because the caller's ref already counts as the wrapper's). The capture-Effect pattern (`lib.rs:1108–1138` test `decision24_capture_effect_pattern_balanced`) pins the exit: closure drops → `CLOwned::drop` → `dec_rc` → balances the caller's +1. **The exit is `Drop`**, not a name.
- **Principle 06 (complexity has a budget)** — abstractions that anticipate features the spec does not yet require are debt. `into_inner` is exactly such an abstraction: there is no current pattern that requires "release without dec'ing" (`Drop` discharges the dec; `Deref` exposes `&T` for borrowed reads; ownership transfer downstream goes via `Drop` of the surrounding scope; the symmetric inverse of `into_owned_consuming` is moot because the consuming caller already holds the transferred ref).

**No grounding for `into_inner` exists** in Decision 24, Decision 11, Decision 31's callback forward-commitment, or any FIXME. The facade text is a speculative addition predating Decision 24's resolution of the capture-RC protocol.

**4. What the difference implies.** A DLL author reading the facade today reaches for `into_inner` in one of two scenarios:

- Returning a stored heap value back across the DLL boundary at a later tick. With no `into_inner`, the closest source-level patterns are: `Deref` + clone (works for `Copy` wrappers; `CLString: Copy` because the underlying `i64` is `Copy`), or `*owned` (works since `T: Copy`). Either takes a copy and then `CLOwned::drop` runs at scope end and decs the original. That is a +1/−1 net on the wrapper at the right time. The realistic workaround is **not** `std::mem::forget(owned)` (the prior audit's claim) — it is `let inner: T = *owned;` followed by the natural `Drop`. The wrapper exists precisely so the author does not have to manage RC by hand; absence of `into_inner` is not user-hostile, it is "you do not need this entry point."
- Defusing `Drop` because the caller has already transferred ownership downstream. There is currently no such pattern in the workspace.

The current `new` + `Drop` pair plus `into_owned_consuming` covers the capture-Effect pattern that Decision 24 pinned. `into_inner` adds an entry point with no grounding and no consumer.

**5. Disposition. Facade moves — remove the speculative line.** Grounding: Principle 06 (premature abstraction is debt; no current consumer); Decision 0024 (capture-RC pinned by `into_owned_consuming` + `Drop`, not by `into_inner`). If a future Decision adds a consumer (e.g., a Decision 0031 callback-row pattern that needs "skip the dec" at thunk-exit), the facade re-introduces `into_inner` with a tested implementation at that point. Speculative inclusion ahead of consumer demand is the failure mode the facade-truth-telling discipline (§2.13) was authored against.

The prior audit reached the same disposition; the **grounding** is the new contribution.

**Closes F1.**

---

### Finding F2 — `impl Default for HostContext` unannounced in facade

**1. What the facade expects.** §"Host context — runtime ↔ platform bridge" (lines 164–172). Two methods named: `HostContext::new() -> Self` (const) and `HostContext::init(&self, callbacks: *const HostCallbacks)` (unsafe). No `Default` impl.

**2. What the source does.** `lib.rs:553–557`:

```rust
impl Default for HostContext {
    fn default() -> Self { Self::new() }
}
```

`public-api.txt:159–160` confirms: `impl core::default::Default for cranelisp_platform::HostContext` + `pub fn cranelisp_platform::HostContext::default() -> Self`.

**3. What is the design intent.** Grounding sources:

- **Decision 0042's consequences** do not name `HostContext`. Decision 0026's invariant 1 (BC §5) speaks to where platform fn ptrs live but not to `HostContext`'s impl set.
- The macro doc-comment example (`lib.rs:716–740`) uses `static HOST: HostContext = HostContext::new();` — the const-fn `new()` is the load-bearing constructor (statics require const-fn). `Default::default()` does **not** satisfy const-context; it cannot construct a `static`. So the `Default` impl serves no DLL-author surface.
- **Principle 06 (complexity has a budget)** — the impl is idiomatic Rust trait-bound satisfier (e.g., for `T: Default`-bounded generic code; for `#[derive(Default)]` on a struct containing `HostContext`). It has zero current consumer in-tree, but it is a near-free idiom-conformance impl.

No Decision either *requires* the `Default` impl or *forbids* it. The facade's omission is sloppy authoring rather than the facade telling-source-to-move-back.

**4. What the difference implies.** The impl is publicly visible per `public-api.txt:159–160`. Per the S67 close baseline-diff discipline (`design/arch/CLAUDE.md` §"Baseline-diff discipline (Sprint 67 close)"): "every pub-api line in the baseline is named in the corresponding facade (or marked internal-but-exposed with rationale). Skipping the facade update breaks the test." `Default` is in the baseline; the facade does not name it; the test fails.

The semantic surface added by the `Default` impl is zero — it delegates to `new()`. The cost of leaving the facade silent is a baseline-diff test failure and an audit drift signal. The cost of removing the impl from source is a non-trivial decision (do we keep idiom-conformance? what does removal break for downstream consumers we haven't enumerated?). Re-engaging the principle: the facade is the binding intent; the source is settled and idiomatic; the facade should catch up.

**5. Disposition. Facade moves — annotate the impl in §"Host context".** Add one line: "`impl Default for HostContext` delegates to `new()` (idiomatic Rust convenience; no semantic surface beyond `new()`)." Grounding: facade-truth-telling per S67 close discipline + `design/arch/CLAUDE.md` baseline-diff convention; no source-side movement warranted (Principle 06's complexity-budget test passes — the impl is one line, no abstraction).

Bundle the edit with F4 (HostContext Send + Sync annotation) as one §"Host context" pass.

**Closes F2.**

---

### Finding F3 — `unsafe impl Send/Sync for PlatformFn` unannounced in facade

**1. What the facade expects.** §"Platform manifest and fn descriptor (DLL ABI)" (lines 98–135) describes `PlatformFn` as a `#[repr(C)]` struct with its fields. No Send/Sync impl mention.

**2. What the source does.** `lib.rs:94–98`:

```rust
// Safety: PlatformFn is a C-ABI struct with raw pointers; it is only
// constructed and accessed within unsafe blocks during DLL loading.
// The pointers must remain valid for the lifetime of the manifest.
unsafe impl Send for PlatformFn {}
unsafe impl Sync for PlatformFn {}
```

`public-api.txt:199–200` confirms — **explicit `unsafe impl`** (the raw `*const u8` / `*const PlatformFn` fields would auto-project to `!Send + !Sync` per Rust's marker-trait rules; the impls had to be asserted by hand).

**3. What is the design intent.** Grounding sources:

- **Bounded contexts §5 — Platform**: "owns no runtime state and no cadence." `PlatformFn` is part of the shared interface contract crossing the DLL boundary. The contract is read at DLL-load time and held in `int`'s `SharedState.kept_dlls` (BC §6 — `Vec<OwnedPlatformFnDescriptor>` per platform).
- **Decision 0026** post-rollback platform-fn registration: the descriptor's pointer is written into `symbol_table.got().store_slot(slot, desc.ptr)`. From that point JIT-emitted code in any worker can load the fn ptr via the GOT and indirect-call. The trampoline (in `cranelisp-intrinsics` per Decision 0043) runs on the IO thread pool when scheduling class is `Sequential`/`Commutative`/`ResourceSerial` per spec §10.12 (Par scheduling forward-commitment).
- **Decision 0031** + **Decision 0041** — per-symbol JIT cardinality; `Arc<Jit>` reclaim. Workers hold pointers into JIT-finalised pages; those workers run across threads. The platform fn ptrs, once installed in the GOT, are read by JIT-emitted code that itself runs across threads.
- **Principle 18 (enforce invariants structurally)** — Send/Sync is an example of a type-system mechanism that **structurally** enforces a cross-thread-shareability invariant. The `unsafe impl` asserts the safety conditions the compiler cannot verify (raw pointers); the assertion is checked by `cargo build` against every cross-thread use of `PlatformFn`.

**The Send + Sync claim IS load-bearing.** The grounding is the cross-thread dispatch path the IO trampoline + `Par` scheduling already implement (and §10.12 will exercise more aggressively when Par lands). The DLL-loaded code segments are mapped for the session lifetime per BC §5 invariant 6 ("No DLL unloading mid-session"); the safety justification at `lib.rs:94–96` covers exactly that.

**4. What the difference implies.** Two scenarios:

- A future PR adds a non-Send-Sync field to `PlatformFn` (e.g., a `Cell<…>` for "remember last-call timestamp", or a `Rc<…>` for some descriptor-side caching). The `unsafe impl Send for PlatformFn` line is what silently breaks the auto-trait projection. The breakage *will* be caught by the compiler at the *consumer* site (intrinsics' trampoline; backend's JIT-emitted code calling through the GOT after marshalling) — but it surfaces as a Send-bound compilation error far from the offending field addition.
- The opposite: a future PR removes the `unsafe impl` line because someone thinks "the auto-trait projection should suffice." The compiler will catch that immediately *if* something actually depends on Send/Sync, but if no current crate-internal test exercises cross-thread `PlatformFn` use, removal would silently pass `cargo build` and break later.

**Per Principle 18's worked example pattern**, this is a structural enforcement that *should be visible in the facade* — the facade is the public-surface auditable contract per Principle 13. The facade's current silence loses the Principle-18 enforcement's visibility.

**5. Disposition. Facade moves — annotate the impls in §"Platform manifest and fn descriptor".** Add a paragraph after the `PlatformFn` struct:

> `unsafe impl Send for PlatformFn {}` + `unsafe impl Sync for PlatformFn {}` (see `crates/cranelisp-platform/src/lib.rs:94–98`). Safety: the raw pointers in `PlatformFn` point at length-prefixed string buffers and the platform fn's code segment, both of which outlive the session per BC §5 invariant 6 (no DLL unloading mid-session). The IO trampoline + Par-scheduling (spec §10.12) hold platform fn descriptors across worker threads; the Send + Sync claim is the structural invariant (Principle 18) that makes the cross-thread dispatch path well-typed.

Grounding: Principle 18 (structural invariant must be facade-visible), Principle 13 (`interfaces.md` is auditable — the facade IS the public-surface audit-of-record), BC §5 invariant 6 (DLL lifetime grounds the safety claim), Decision 0026 + 0031 (cross-thread dispatch use case).

**Closes F3.**

---

### Finding F4 — `Send + Sync` on `HostContext` (auto-derived); `!Send + !Sync` on `OwnedPlatformFnDescriptor` + `PlatformManifest` (auto-projected)

**1. What the facade expects.** §"Host context" (lines 161–172): no Send/Sync mention. §"Host-side descriptors" (lines 137–159) on `OwnedPlatformFnDescriptor`: no Send/Sync mention. §"Platform manifest" (lines 98–135) on `PlatformManifest`: F3 already covered the explicit-impl asymmetry vs `PlatformFn`; no Send/Sync mention for `PlatformManifest`.

**2. What the source does.**

- `HostContext { callbacks: AtomicPtr<HostCallbacks> }` — `AtomicPtr` is `Send + Sync`, so `HostContext: Send + Sync` auto-projects. `public-api.txt:162–164` confirms `impl core::marker::Send for cranelisp_platform::HostContext` + `impl core::marker::Sync for cranelisp_platform::HostContext`.
- `OwnedPlatformFnDescriptor { ptr: *const u8, … }` — the raw `*const u8` field auto-projects to `!Send + !Sync`. `public-api.txt:178–179`: `impl !core::marker::Send for cranelisp_platform::OwnedPlatformFnDescriptor` + `impl !core::marker::Sync`.
- `PlatformManifest` — `public-api.txt:215–216` shows `impl !core::marker::Send for cranelisp_platform::PlatformManifest` + `impl !core::marker::Sync`. The raw `*const u8` and `*const PlatformFn` fields auto-project to `!Send + !Sync` (unlike `PlatformFn` which has explicit `unsafe impl` lines).

**3. What is the design intent.** Grounding:

- **HostContext Send + Sync** — BC §5 invariant 5 ("`HostContext` initialised once per session. `int` constructs `HostCallbacks` … and calls `HostContext::init` exactly once. Subsequent platform fn calls see the same callbacks for the session's lifetime."). The static `HOST: HostContext` (macro doc-comment example) is read concurrently by every thread invoking a platform fn that calls back into the host. The `AtomicPtr<HostCallbacks>` is what makes the cross-thread access safe; the auto-trait projection rides on `AtomicPtr`'s contract. **Same Principle-18 + Principle-13 grounding as F3** — load-bearing cross-thread invariant; must be facade-visible.
- **OwnedPlatformFnDescriptor !Send + !Sync** — held by `int`'s `SharedState.kept_dlls` per BC §5 + §6.1 (compilation cadence's worker subsystem). Per BC §6.3 within-cadence access, "access primitive is the window … windows are partitioned along cadence lines." The session is currently single-threaded per session; the descriptor's !Send/!Sync projection is a correct conservative default that matches the cadence partitioning. *If* the session ever becomes cross-thread (W3 forward-watch), the auto-trait projection would need to be re-evaluated; for now it is correct as-is and does not break any consumer.
- **PlatformManifest !Send + !Sync** — same auto-projection mechanic. The `PlatformManifest` is read on the DLL-load path (single-threaded; `int::load_platform_dll`) and converted to `OwnedPlatformFnDescriptor` via `manifest_to_descriptors`. After that point the raw manifest is not retained; the owned descriptors are. The !Send/!Sync projection is correct — `PlatformManifest` does not need to cross threads.

**Asymmetry with `PlatformFn` (F3)**: `PlatformFn` carries explicit `unsafe impl Send/Sync`; `PlatformManifest` does NOT (auto-projects to !). The asymmetry is intentional: `PlatformFn` is what crosses the per-descriptor cross-thread boundary (its pointer fields land in the GOT); `PlatformManifest` is the *batch container* read once at load time and not retained.

**4. What the difference implies.**

- **HostContext Send + Sync**: same scenario as F3 — a future field addition that is not `Send + Sync` (e.g., `RefCell<…>`) would silently break the projection, and concurrent platform-fn calls would fail to compile against the changed crate. The facade's silence loses the structural-invariant visibility.
- **OwnedPlatformFnDescriptor !Send + !Sync**: today's session is single-threaded so the projection is moot. Forward-watch item W3 if `int` becomes multi-threaded — at that point the !Send/!Sync becomes a real constraint.
- **PlatformManifest !Send + !Sync**: structurally correct; no scenario currently exercises a different shape.

**5. Disposition.**

- **HostContext Send + Sync — facade moves (annotate, Principle 18 + 13 grounded).** Add to §"Host context": "`HostContext` is `Send + Sync` via auto-trait projection from `AtomicPtr<HostCallbacks>`. The projection is load-bearing for cross-thread platform-fn dispatch per BC §5 invariant 5 (subsequent calls share the static for the session lifetime); any future field addition must preserve `Send + Sync`." Bundle with F2 as one §"Host context" edit pass.
- **OwnedPlatformFnDescriptor !Send + !Sync — facade moves (annotate succinctly).** One line in §"Host-side descriptors": "Auto-projects to `!Send + !Sync` (the `ptr: *const u8` field). Correct for single-threaded session ownership per BC §6.1; re-evaluate if cross-thread descriptor retention is introduced." Lighter weight than HostContext because the projection is not currently load-bearing.
- **PlatformManifest !Send + !Sync — facade moves (annotate the asymmetry with `PlatformFn`).** One line in §"Platform manifest and fn descriptor": "`PlatformManifest` auto-projects to `!Send + !Sync` (intentional asymmetry with `PlatformFn`'s explicit `unsafe impl Send/Sync` — the manifest is read once at DLL-load time and not retained; per-descriptor `PlatformFn` values cross thread boundaries via GOT registration)."

Grounding throughout: Principle 18 (structural invariant should be facade-visible), Principle 13 (`interfaces.md` is auditable), Principle 6 (annotations are cheap and explain the visible asymmetry), BC §5 + §6.

**Flip vs prior audit**: prior dispositioned OwnedPlatformFnDescriptor's !Send/!Sync as "no action; auto-trait noise." This audit's grounding via Principle 18 + 13 (the facade is the public-surface audit-of-record; every public marker-trait projection visible in the baseline should be facade-visible too) flips that to "facade moves, annotate." The prior audit also did not consider `PlatformManifest`'s asymmetry-with-`PlatformFn`; this audit adds it as the third sub-finding under F4.

**Closes F4.**

---

### Finding F5 — `CLHeap` method names + receiver shape: internal facade contradiction

**1. What the facade expects.** TWO mutually inconsistent specifications in the same facade document.

§"Heap-typed values crossed between platform and runtime" (lines 69–73):

```rust
pub trait CLHeap: CLType + Copy {
    fn rc_inc(self);
    fn rc_dec(self);
    /* … */
}
```

Method names: `rc_inc` + `rc_dec`. Receiver: `self` (consuming).

§"Sealed traits" (lines 294–302):

```rust
pub trait CLHeap: CLType + Copy {
    fn rc_inc(&self);
    fn dec_rc(&self);    // method name in source is `dec_rc` (asymmetry intentional)
    fn raw_ptr(&self) -> i64;
    fn own(&self) -> CLOwned<Self>;
    fn into_owned_consuming(self) -> CLOwned<Self>;
}
```

Method names: `rc_inc` + `dec_rc` (asymmetric). Receiver: `&self`.

**2. What the source does.** `lib.rs:432–507`:

```rust
pub trait CLHeap: CLType + Copy {
    fn raw_ptr(&self) -> i64;
    fn inc_rc(&self) { /* atomic fetch_add(1) on rc field at base+8 */ }
    fn dec_rc(&self) { /* atomic fetch_sub(1); free if old_rc==1 */ }
    fn own(&self) -> CLOwned<Self> { CLOwned::new(*self) }
    fn into_owned_consuming(self) -> CLOwned<Self> { CLOwned { inner: self } }
}
```

Names: `inc_rc` + `dec_rc` (fully reversed, symmetrically). Receiver: `&self`. `public-api.txt:229–234` confirms.

**3. What is the design intent.** Grounding:

- **Decision 0013 (atomic RC `SeqCst` from Ring 1; legacy — embodied)** — the RC operation is a borrowed-receiver atomic on the `rc` field at `base + 8`. The receiver must be `&self`; `self`-by-value would consume the wrapper and prevent the borrow-then-atomic pattern. **`&self` is mandated by the atomic-RC contract; `self`-by-value is incorrect.**
- **Decision 0043 (runtime split)** + the inline source comment at `lib.rs:298` quoted in §"Sealed traits" line 298: "method name in source is `dec_rc` (not `rc_dec` — the asymmetry in spelling vs `rc_inc` is intentional, matching the historical name from `cranelisp-intrinsics`)." The pair `inc_rc` / `dec_rc` is reversed-prefix; the asymmetry-direction matches `cranelisp-intrinsics`' naming. The note IS in the facade today, applied to `dec_rc` only — and applied alongside the still-wrong `rc_inc` (forward-prefix) name.
- **Principle 07 (single source of truth)** — two facade blocks specifying the same trait, with different shapes, is a definitional break. One trait, one shape; the facade must agree with itself.

The §"Sealed traits" block (lines 294–302) is materially closer to source (`&self` receiver is correct; `dec_rc` name is correct) but still gets `rc_inc` wrong. The §"Heap-typed values crossed" block (lines 69–73) is wrong on both axes (`self` receiver; `rc_inc`/`rc_dec` non-reversed naming).

**Source is settled and correct.** The asymmetric `inc_rc` / `dec_rc` spelling is intentional per the comment at line 298; the `&self` receiver is mandated by Decision 0013. Both facade blocks must move to match.

**4. What the difference implies.** A DLL author reading the document top-to-bottom encounters `rc_inc(self)` in §"Heap-typed values crossed" first, then `rc_inc(&self)` in §"Sealed traits" 220 lines later. They have no way to know which is binding. If they write code against the first block:

- `(&val).rc_inc()` against `fn rc_inc(self)` — type error (consuming-self call from a borrow).
- They look up the method name `rc_inc` against the source's `inc_rc` — method-not-found error.

Both errors are compile-time and recoverable, but they cost the author a debugging session. Principle 15's external-audience exception (§"Re-exports from `cranelisp-types`") names DLL authors as the explicit external audience; facade truth-telling matters more here than for facades whose audience is in-tree.

**5. Disposition. Facade moves (both blocks).** Source is settled and correct; both facade blocks must normalise:

- §"Heap-typed values crossed" (lines 69–73): change `fn rc_inc(self)` → `fn inc_rc(&self)`; change `fn rc_dec(self)` → `fn dec_rc(&self)`. Add the inline note about the asymmetric `dec_rc` spelling and the `&self` receiver rationale (Decision 0013 atomic-RC borrow).
- §"Sealed traits" (lines 294–302): change `fn rc_inc(&self)` → `fn inc_rc(&self)`. The `dec_rc(&self)` and the inline note at line 298 are already correct.

Grounding: Decision 0013 (`&self` receiver), Decision 0043's inline-name discipline (`cranelisp-intrinsics` historical names), Principle 7 (one trait, one shape; two facade blocks must agree), Principle 15 external-audience exception (DLL authors deserve facade truth-telling).

**Closes F5.**

---

### Finding F6 — `declare_platform!` macro arm shape out-of-date (the DLL-author surface)

**1. What the facade expects.** §"`declare_platform!` macro (DLL-author API)" (lines 203–216):

```rust
#[macro_export]
macro_rules! declare_platform {
    (
        name: $name:literal,
        host: $host:ident,
        fns: { $($fn_name:literal => $fn_pointer:expr),* $(,)? }
    ) => { /* generates the PlatformManifest static + extern symbol */ };
}
```

Three top-level keys (`name`, `host`, `fns`); `fns` is a brace-delimited list of `"name" => fn_pointer` pairs.

**2. What the source does.** `lib.rs:741–836`:

```rust
#[macro_export]
macro_rules! declare_platform {
    (
        name: $platform_name:literal,
        version: $platform_version:literal,
        host: $host:ident,
        functions: [
            $(
                $fn_ident:ident {
                    cl_name: $cl_name:literal,
                    sig: $sig:literal,
                    doc: $doc:literal,
                    params: [$($param:ident),* $(,)?],
                    scheduling: $scheduling:expr,
                }
            ),* $(,)?
        ]
    ) => { /* … */ };
}
```

Doc-comment example (`lib.rs:716–740`):

```rust
declare_platform! {
    name: "stdio",
    version: "0.1.0",
    host: HOST,
    functions: [
        print_string {
            cl_name: "print",
            sig: "(Fn [String] (IO Int))",
            doc: "Print a string followed by a newline",
            params: [s],
            scheduling: SchedulingClass::Sequential,
        },
    ]
}
```

Five differences from facade: (a) new top-level key `version` (required between `name` and `host`); (b) `fns` → `functions`; (c) `{}` → `[]` on the function list; (d) `"name" => fn_pointer` pair → `fn_ident { cl_name: …, sig: …, doc: …, params: […], scheduling: … }` structured block; (e) five per-fn fields where facade has one.

**3. What is the design intent.** This is the load-bearing case for grounding because the macro IS the DLL-author entry point. Grounding sources:

- **Principle 15 (facade types live with their behavior — external-audience exception)** — `cranelisp-platform` is the *only* implementation crate whose facade is read by an external audience (out-of-tree DLL authors per the exception at line 21). The macro arm is *their* contract surface. Facade truth-telling is uniquely high-cost-of-drift here.
- **Decision 0026** — `scheduling_class` lives inside the `PrimitiveKind::PlatformEffect` variant; `lib.rs:90–91` exposes it on `PlatformFn.scheduling_class: u32` for the C-ABI traversal; the macro's per-fn `scheduling: $scheduling:expr` field is the DLL-author-side authoring path. The macro arm exists *because* Decision 0026 requires the DLL author to declare scheduling class per-fn (it cannot be defaulted; it cannot be inferred). **The five per-fn fields are not optional or default-able** — `sig` is required for typecheck-side type checking of platform fn calls; `doc` flows into `/sig`/`/doc` REPL introspection (`design/arch/facades/platform.md` lines 122–123); `params` are the named-parameter S67 W1 PFR addition that surfaces in REPL introspection (lines 124–127); `scheduling` is Decision 0026's per-fn class; `cl_name` is the kebab-case user-visible name.
- **Decision 0042's adopted error-construction shape** — `manifest_to_descriptors` returns `PlatformError`; UTF-8 validation failures construct `LoadFailed { dll: PathBuf::new(), cause, location: ErrorLocation::unknown() }` (per the test `manifest_to_descriptors_utf8_failure_returns_load_failed_with_unknown_location` at `lib.rs:984–1029`). The macro-emitted manifest is what `manifest_to_descriptors` reads; the per-fn fields are what end up as the descriptor's parsed Rust strings + ptr + class. **The facade's macro arm shape and the manifest shape must agree** — they describe two ends of one C-ABI channel.

The S67 W1 PFR (Platform Facade Refinement) work (`facades/platform.md` § lines 105–127's "S67 W1 PFR" annotations) reshaped `PlatformManifest` and `PlatformFn` to the 5-key + per-fn-block + length-prefixed-strings shape. The facade text at §"Platform manifest and fn descriptor" reflects the S67 W1 PFR shape; the facade text at §"`declare_platform!` macro" does NOT — it was not updated alongside.

The facade text at lines 203–216 is **historically stale** — it predates the S67 W1 PFR. The grounding for the current source-side shape is Decision 0026 + the S67 W1 PFR + the load-bearing `/sig`/`/doc` REPL introspection contract.

**4. What the difference implies.** A DLL author reading the current `facades/platform.md` and writing to it would produce code that **does not compile against the current crate**:

```rust
// What the facade tells them to write:
declare_platform! {
    name: "stdio",
    host: HOST,
    fns: { "print" => print_string }
}
// Compiler output: `macro_rules` "no rules expected this token" diagnostic,
// deep inside macro expansion. Useful for a Rust expert; bewildering for a
// DLL author whose first contact with the crate is the facade.
```

The fix path requires the author to: add `version: "x.y.z"`; rename `fns` → `functions`; replace `{}` with `[]`; replace the `"name" => fn_pointer` pair with the full `fn_ident { cl_name: …, sig: …, doc: …, params: […], scheduling: … }` block; *discover* the four new required fields by reading source (since the facade does not mention them). None of the five per-fn fields has an optional / default branch in the macro arm; all five must be supplied.

**Per Principle 15 the external audience is named** — DLL authors writing out-of-tree crates that depend only on `cranelisp-platform`. The facade IS their first contact with the crate. Drift here has the steepest user cost in the entire workspace. This is the audit's highest-priority finding.

**5. Disposition. Facade moves — replace lines 203–216 with the current 5-key shape, mirroring `lib.rs:741–757`.** Include a worked example block reproducing `lib.rs:716–740` (the `static HOST: HostContext`, the `pub extern "C" fn print_string`, the macro invocation). Grounding: Decision 0026 (per-fn scheduling class declaration), Principle 15 external-audience exception (DLL authors are the explicitly-named external audience; facade truth-telling required), S67 W1 PFR (the as-built shape that the facade authored at §"Platform manifest and fn descriptor" but did NOT propagate to §"`declare_platform!` macro" in the same pass).

The specific replacement text:

```rust
#[macro_export]
macro_rules! declare_platform {
    (
        name: $platform_name:literal,
        version: $platform_version:literal,
        host: $host:ident,
        functions: [
            $(
                $fn_ident:ident {
                    cl_name: $cl_name:literal,
                    sig: $sig:literal,
                    doc: $doc:literal,
                    params: [$($param:ident),* $(,)?],
                    scheduling: $scheduling:expr,
                }
            ),* $(,)?
        ]
    ) => { /* generates `cranelisp_platform_manifest` extern + leaked PlatformManifest */ };
}
```

Plus the doc-comment example block reproduced verbatim (or substantively equivalent) from `lib.rs:716–740`.

**Sourced from**: the §"`declare_platform!` macro" section IS sourced from the S67 W1 PFR `PlatformFn` shape (Decision 0026's per-fn fields). It is NOT a free-floating authoring artefact; the macro arm exists *because* the manifest shape exists. The facade's macro section drift is exactly an out-of-band update — the §"Platform manifest" section was updated, the §"`declare_platform!` macro" section was not.

**Closes F6.** Highest priority Wave-2 edit.

---

### Finding F7 — Speculative `#[non_exhaustive]` on `CLOwned` in facade; absent in source

**1. What the facade expects.** §"Heap-typed values crossed" (lines 75–78):

```rust
#[non_exhaustive]
pub struct CLOwned<T: CLHeap> { inner: T }
```

The §"`#[non_exhaustive]` DTOs" enumeration (lines 307–318) lists DTOs into "Exempt (layout contracts; governed by `ABI_VERSION`)" and "Carry `#[non_exhaustive]`" — `CLOwned` appears in **neither** list (enumeration gap).

**2. What the source does.** `lib.rs:515–519`:

```rust
pub struct CLOwned<T: CLHeap> { inner: T }
```

No `#[non_exhaustive]`. `public-api.txt:100` confirms: `pub struct cranelisp_platform::CLOwned<T: cranelisp_platform::CLHeap>` (no annotation prefix). The single field `inner: T` is private; the struct is constructed only via `CLOwned::new()` or by `CLHeap::into_owned_consuming`'s `CLOwned { inner: self }`.

**3. What is the design intent.** Grounding sources:

- **Principle 14 (FFI layout discipline)** — `#[non_exhaustive]` discipline applies to public DTOs EXCEPT those carrying `#[repr(C)]` or `#[repr(transparent)]`. `CLOwned` carries NEITHER (not `#[repr(transparent)]`; the wrapper is a plain Rust RAII over a single field of type `T: CLHeap`, where `T` itself is `#[repr(transparent)]` over i64). Principle 14's exemption-by-FFI-layout does NOT apply.
- **Standard facade convention (per `facades/types.md` and other facades)** — plain-Rust public DTOs carry `#[non_exhaustive]` by default. `OwnedPlatformFnDescriptor` (which is plain-Rust) correctly carries it per `public-api.txt:168`. The convention applies to `CLOwned` by default unless an explicit grounding exempts it.
- **Field-set evolution analysis** — `CLOwned`'s public surface is `new`, `Drop`, `Deref`. The private `inner: T` field is the only field; field-set evolution is anticipated only if drop-glue customisation is ever needed beyond what `CLHeap::dec_rc` provides (currently no Decision anticipates this). External code is locked out of direct construction by the private field; `#[non_exhaustive]` would add no semantic protection beyond what privacy already provides.

The facade's `#[non_exhaustive]` on `CLOwned` is either: (a) speculative (someone intended to add it but source-side did not land); or (b) aspirational without a grounding Decision. **No Decision or FIXME grounds the `#[non_exhaustive]` on `CLOwned`.** The previously-cited FIXME 0107 (which added `#[non_exhaustive]` to `OwnedPlatformFnDescriptor`) does NOT extend to `CLOwned`; FIXME 0107 is closed (no longer in `fixmes/`); the per-crate design doc `design/platform/platform.md` §3 divergence #7 (line 93) says the CL-wrapper family (including `CLOwned`) is treated as layout-bound and exempt-from-`#[non_exhaustive]` per `/arch`'s "Option A" resolution. **The platform master design doc grounds the source's no-annotation as correct.**

Concretely from `design/platform/platform.md` line 175 (§6 FFI layout discipline): "`CLInt`, `CLString`, `CLBool`, `CLFloat`, `CLIO<T>`, `CLOwned<T>` are also layout contracts (the JIT calling convention reads them as raw `i64`). Implementation does not carry `#[non_exhaustive]` on them. Per `/arch`'s resolution of FIXME 0107 (Option A), Principle 14 extends to cover both `#[repr(C)]` and `#[repr(transparent)]`; the implementation is correct."

Note however: `CLOwned<T>` is NOT itself `#[repr(transparent)]` in source. The master design doc lumps it with the CL wrappers, but the public-api confirms it is a plain struct (line 100). The reasoning in §6 of the master design doc is slightly imprecise here: the *underlying* `T: CLHeap` is `#[repr(transparent)]`; `CLOwned<T>` is a plain Rust RAII over that. The doc's conclusion ("implementation is correct; no `#[non_exhaustive]`") nonetheless stands on its own footing — `CLOwned`'s private-field discipline and lack of public construction paths make `#[non_exhaustive]` semantically inert.

**4. What the difference implies.** Two cases:

- The facade's `#[non_exhaustive]` annotation on the struct declaration (line 75) is unimplementable — adding it to source would change the public-API baseline (`public-api.txt:100` would gain a `#[non_exhaustive]` prefix); the platform master design doc says the implementation as-is is correct.
- The §"`#[non_exhaustive]` DTOs" enumeration omits `CLOwned` from both lists. Per the enumeration's stated discipline ("Per-facade `#[non_exhaustive]` DTOs sections enumerate exempt types with a one-line note so the exemption is auditable from the facade spec" — Principle 14 final bullet), the omission is a facade-side gap. `CLOwned`'s correct disposition (no `#[non_exhaustive]`; grounded by the master design doc's reasoning) should be enumerated.

**5. Disposition. Facade moves — two-part edit:**

1. **Remove `#[non_exhaustive]` from the §"Heap-typed values crossed" struct declaration** (line 75) to match source.
2. **Add `CLOwned` to the §"`#[non_exhaustive]` DTOs" enumeration**, in the "Carry `#[non_exhaustive]`" section's complement, with the explicit rationale: "NOT applied — single-field RAII wrapper over `T: CLHeap` (which is `#[repr(transparent)]`); private `inner` field prevents external direct construction; per `/arch`'s FIXME 0107 resolution + `design/platform/platform.md` §6, treated as a layout-adjacent contract. External code cannot construct `CLOwned<T>` directly (the `inner` field is private), so `#[non_exhaustive]` would add no semantic protection."

Grounding: Principle 14 (layout-discipline scope), `design/platform/platform.md` §6 (Option A resolution of FIXME 0107), `public-api.txt:100` (confirming current source shape is `pub struct` without annotation).

**Flip vs prior audit**: prior audit dispositioned this as "facade moves (remove + enumerate as NOT applied)" with rationale "facade-truth-telling on the absence is as important as the presence." Same disposition, but the prior audit did not cite `design/platform/platform.md` §6's master-design-doc grounding for the source's no-annotation choice. This audit's grounding is concrete and reviewable.

**Closes F7.**

---

### Finding F8 — `CLHeap` super-bound `CLType + Copy` (consistent across all three sites)

**1. What the facade expects.** §"Heap-typed values crossed" line 69: `pub trait CLHeap: CLType + Copy`. §"Sealed traits" line 296: `pub trait CLHeap: CLType + Copy`. Both blocks agree.

**2. What the source does.** `lib.rs:432`: `pub trait CLHeap: CLType + Copy`. `public-api.txt:229`: `pub trait cranelisp_platform::CLHeap: cranelisp_platform::CLType + core::marker::Copy`. All three sites agree.

§"Sealed traits" line 292 notes: "Adding the `Sealed` super-bound is a candidate refinement; tracked as a future cleanup, not S67 scope."

**3. What is the design intent.** Grounding: Principle 7 (single source of truth) — one trait, one super-bound, consistent across facade + source + pub-api. The candidate `Sealed` super-bound is correctly out-of-scope per the inline note; it is a tracked future refinement, not a current drift.

**4. What the difference implies.** None — three sites agree.

**5. Disposition. No action.** Per the audit discipline ("Even 'auto-trait noise' gets a one-sentence justification of the no-action call"): the super-bound is consistent across facade + source + public-api per Principle 7; the candidate `Sealed` refinement is correctly annotated as out-of-scope; no facade or source movement required.

**Closes F8.**

---

### Finding F9 — Principle 15 external-audience exception: scope health-check

**1. What the facade expects.** §"Re-exports from `cranelisp-types` (external-audience exception per Principle 15)" (lines 257–269):

```rust
pub use cranelisp_types::SchedulingClass;
pub use cranelisp_types::PlatformError;
```

Two re-exports. Each with per-item justification:

- `SchedulingClass` — Decision 0026 (multi-consumer per Principle 15's heuristic — typecheck, backend, platform, intrinsics all reference it); re-exported here for DLL authors.
- `PlatformError` — Decision 0042 (`CranelispError::Platform` constructed by both platform and `int`'s error-formatting layer); re-exported here for DLL authors constructing platform errors.

The facade closes: "No other re-exports."

**2. What the source does.** `lib.rs:41` `pub use cranelisp_types::SchedulingClass;` + `lib.rs:47` `pub use cranelisp_types::PlatformError;`. `public-api.txt:2–3` confirms both. The `use cranelisp_types::ErrorLocation;` at `lib.rs:48` is a private `use` (internal import), not a `pub use` — does NOT cross the platform boundary; correctly NOT enumerated in the facade re-export block. No other `pub use cranelisp_types::*` lines in the crate.

**3. What is the design intent.** Principle 15 (external-audience exception, lines 21–23): "A facade whose external audience does not (and should not need to) depend on `cranelisp-types` MAY re-export the items its public API uses. The criterion is concrete: an external consumer for whom `cranelisp-types` is not otherwise a natural dependency. Today this applies to `cranelisp-platform` (DLL authors writing out-of-tree crates that depend only on `cranelisp-platform`). Each invocation of the exception is justified inline in the facade spec; it is not a general license."

The exception's bar: (a) external audience identified; (b) audience does not otherwise depend on `cranelisp-types`; (c) per-item justification inline; (d) not a general license.

Checking the two current re-exports against the bar:

1. External audience: ✓ — DLL authors named explicitly.
2. Not otherwise a natural dependency: ✓ — DLL authors crate-depend on `cranelisp-platform` only.
3. Justified inline: ✓ — both have per-item rationale citing the Decision that grounds them (`SchedulingClass` ← 0026; `PlatformError` ← 0042).
4. Not a general license: ✓ — only two items; the closing "No other re-exports." enforces narrowness.

**4. What the difference implies.** Source and facade agree; no drift; the exception is correctly applied. Watch-items for future drift:

- A third re-export appearing without per-item rationale would be exception growth.
- A re-export of an implementation-crate-only type (e.g., `cranelisp-typecheck::CheckError`) would be exception abuse.
- A re-export added for convenience that DLL authors don't actually need (e.g., for some unrelated convenience) would be scope creep.

None of these are present today.

**5. Disposition. No action — exception is correctly applied and narrowly scoped.** Per the audit discipline ("Even 'auto-trait noise' gets a one-sentence justification of the no-action call"): two re-exports each justified inline; "No other re-exports." enforces narrowness; cross-checks against `public-api.txt` confirm no leakage. Annual health-check noted as W2 watch-item below (§5).

**Closes F9.**

---

## 2. Calibration vs prior audit — before/after per finding

The prior `cranelisp-platform-audit-s69.md` (overwritten by this re-author) had a per-finding four-block shape but disposed of findings **without reading the architectural configuration**. Below is the before/after per-finding flip table.

| Finding | Prior disposition | This-audit disposition | Flip? | Grounding the prior audit did not cite |
|---|---|---|---|---|
| F1 (`CLOwned::into_inner`) | Facade moves (remove) | Facade moves (remove) | No | This audit grounds in Decision 0024 + Principle 06; prior audit grounded in "no current consumer" without Principle citation. **Same disposition, stronger grounding.** |
| F2 (`HostContext::default`) | Facade moves (annotate) | Facade moves (annotate) | No | This audit grounds in S67 close baseline-diff discipline (`design/arch/CLAUDE.md`); prior audit grounded in "facade-truth-telling on a real public surface item." **Same disposition, stronger grounding.** |
| F3 (`unsafe impl Send/Sync for PlatformFn`) | Facade moves (annotate with safety justification) | Facade moves (annotate with safety justification) | No | This audit grounds in Principle 18 (structural-invariant visibility) + Principle 13 (facade is the public-surface audit-of-record) + BC §5 invariant 6; prior audit grounded in "load-bearing invariant" without Principle 18 citation. **Same disposition, much stronger grounding via Principle 18.** |
| F4 (`HostContext` Send + Sync; `OwnedPlatformFnDescriptor` !Send + !Sync; `PlatformManifest` !Send + !Sync) | Facade moves (HostContext only); no action (OwnedPlatformFnDescriptor); no mention of PlatformManifest | Facade moves (all three sub-findings) | **FLIP** | Prior audit dispositioned `OwnedPlatformFnDescriptor` as "no action — auto-trait noise" and did not address `PlatformManifest`. This audit grounds in Principle 18 + 13 (every public marker-trait projection in the baseline should be facade-visible) + the asymmetry-with-PlatformFn (intentional design choice that should be facade-visible per BC). **Flip rationale: Principle 18's "structural invariant should be facade-visible" raises the bar above the prior "auto-trait noise" dismissal — even !Send/!Sync projections explain visible asymmetry the facade should declare.** |
| F5 (`CLHeap` method names + receiver) | Facade moves (normalise both blocks to source) | Facade moves (normalise both blocks to source) | No | This audit grounds in Decision 0013 (`&self` receiver mandated by atomic-RC contract) + Principle 7 (one trait, one shape) + Principle 15 external-audience exception (DLL authors deserve facade truth-telling); prior audit grounded in "source is settled and correct." **Same disposition, stronger grounding via Decision 0013.** |
| F6 (`declare_platform!` macro arm) | Facade moves (highest priority) | Facade moves (highest priority) | No | This audit grounds in Decision 0026 (per-fn `scheduling_class` declaration) + S67 W1 PFR (the as-built shape was reshaped in S67 W1; facade's manifest section caught up but macro section did not) + Principle 15 external-audience exception (DLL authors are the explicitly-named audience). Prior audit grounded in "external audience" without Decision 0026 + S67 W1 PFR citation. **Same disposition, much stronger grounding via S67 W1 PFR origin story (this drift is provenanced).** |
| F7 (`CLOwned` `#[non_exhaustive]`) | Facade moves (remove + enumerate as NOT applied) | Facade moves (remove + enumerate as NOT applied) | No | This audit grounds in `design/platform/platform.md` §6's Option A resolution of (now-closed) FIXME 0107 + Principle 14 layout-discipline scope. Prior audit grounded in "single-field RAII; private `inner`" without citing the master design doc. **Same disposition, stronger grounding via master-doc citation.** |
| F8 (`CLHeap` super-bound) | No action | No action | No | This audit grounds in Principle 7; prior audit grounded in "consistent across facade + source + pub-api" without Principle citation. **Same disposition, stronger grounding.** |
| F9 (Principle 15 exception scope) | No action | No action | No | This audit grounds in Principle 15's four-clause test (a–d) applied explicitly to each re-export; prior audit grounded in narrative. **Same disposition, stronger grounding via four-clause test.** |

**Total**: 1 flipped disposition (F4 — the `OwnedPlatformFnDescriptor` + `PlatformManifest` !Send + !Sync sub-findings flip from "no action" to "facade moves (annotate)"). 8 dispositions unchanged in direction but all have stronger grounding citations.

---

## 3. Findings overview

| Finding | Topic | Disposition | Grounding (Decision / Principle) |
|---|---|---|---|
| F1 | `CLOwned::into_inner` — speculative facade method | Facade moves (remove) | Decision 0024 + Principle 06 |
| F2 | `impl Default for HostContext` — unannounced | Facade moves (annotate; bundle with F4 HostContext sub-finding) | S67 close baseline-diff discipline (`design/arch/CLAUDE.md`) |
| F3 | `unsafe impl Send/Sync for PlatformFn` — load-bearing, unannounced | Facade moves (annotate with safety justification) | Principle 18 + Principle 13 + BC §5 invariant 6 + Decision 0026 + 0031 |
| F4 | Send/Sync projections on `HostContext` + `OwnedPlatformFnDescriptor` + `PlatformManifest` (sub-findings) | Facade moves (all three) | Principle 18 + Principle 13 + BC §5 invariant 5 + BC §6.1 |
| F5 | `CLHeap` method names + receiver — internal facade contradiction | Facade moves (normalise both blocks) | Decision 0013 + Principle 7 + Principle 15 external-audience |
| F6 | `declare_platform!` macro arm — out-of-date DLL-author surface | **Facade moves (highest priority)** | Decision 0026 + S67 W1 PFR (provenance) + Principle 15 external-audience |
| F7 | `CLOwned` `#[non_exhaustive]` — speculative + enumeration gap | Facade moves (remove + enumerate as NOT applied) | Principle 14 layout-discipline scope + `design/platform/platform.md` §6 Option A |
| F8 | `CLHeap: CLType + Copy` super-bound — consistent | No action | Principle 7 |
| F9 | Principle 15 exception scope — still narrow | No action (annual health-check) | Principle 15 four-clause test |
| C1 | `CLHeap` receiver/arity mechanical gap | `/qa` enhancement (S70) | Conformance-triad-by-construction limit |
| C2 | `#[non_exhaustive]` annotation mechanical gap | `/qa` enhancement (S70) | Conformance-triad-by-construction limit |
| C3 | `declare_platform!` arm-shape mechanical gap (the F6 category) | `/qa` enhancement (compile-fixture; S70) | Conformance-triad-by-construction limit |
| C4 | `#[repr(C)]` field-order mechanical gap | `/qa` enhancement (cbindgen diff; S70+) | Conformance-triad-by-construction limit |
| C5 | `unsafe impl Send/Sync` mechanical gap | `/qa` enhancement (S70) | Conformance-triad-by-construction limit |

---

## 4. Coverage holes (changes the conformance triad would not catch)

The mechanical conformance suite (text-grep `facade_compliance.rs`; PIF-row coverage; `public_api_relocations.rs` baseline-diff) catches lexical name presence + diff against a frozen baseline, but cannot catch:

### Coverage hole C1 — `CLHeap` method receiver/arity drift
The leaf-name `inc_rc` appears in §"Sealed traits" of the facade and in source's trait impl. If source's `inc_rc(&self)` changed to `inc_rc(self)` tomorrow (breaking change for DLL authors calling through `Deref` on `&CLString`), text-grep would still see the name `inc_rc` and pass. No PIF row asserts the receiver type. Public-api diff would flag the signature change, but only if the baseline is NOT also regenerated in the same commit; a refactor regenerating the baseline alongside the source change makes the drift invisible from the diff history. **Required**: PIF coverage of the structural signature (receiver type + return type) per `CLHeap` method, not just the name presence.

### Coverage hole C2 — `#[non_exhaustive]` annotation appearance/removal
`OwnedPlatformFnDescriptor` carries `#[non_exhaustive]` per `public-api.txt:168` — the only platform-crate type that should. `CLOwned` does not, per F7. The text-grep `facade_compliance.rs` only checks substring presence of the type name in the facade; it does not check the `#[non_exhaustive]` attribute prefix. A regression silently dropping `#[non_exhaustive]` on `OwnedPlatformFnDescriptor` would pass `facade_compliance.rs` and silently break Principle 14 compliance for the post-load owned descriptor's field-set evolution discipline. **Required**: PIF-row coverage of the `#[non_exhaustive]` attribute presence on the types where it is required.

### Coverage hole C3 — `declare_platform!` macro arm drift (the F6 category, generalised)
The macro identifier appears in `public-api.txt:4`. Text-grep is satisfied by the identifier's presence. The arm's argument shape is not asserted by any mechanical test. Any future arm reshape — adding a key, removing a key, changing delimiter type, renaming `functions:` — would be undetectable by the conformance triad. **Required**: either (a) a structural test that parses the macro_rules arm signature and asserts the key set + delimiter shape, or (b) a compile-fixture test that invokes `declare_platform!` with the facade-documented shape and asserts compilation succeeds. (b) is the more durable fix: if the facade's example would not compile, the test fails — exactly the DLL-author scenario the facade should protect.

### Coverage hole C4 — `#[repr(C)]` struct field-order changes
`PlatformManifest` and `PlatformFn` are `#[repr(C)]` per Principle 14's exemption from `#[non_exhaustive]`. A field-order reshuffle that changed byte offsets (e.g., swapping `param_count` and `type_sig`) would NOT be caught by `facade_compliance.rs` (all field names still appear) NOR by `public_api_relocations.rs` (cargo-public-api emits fields as an unordered set, not as a sequence). The only failure mode is runtime: a DLL written against the old layout loads, reads garbage at every offset past the swap, and either crashes or silently misbehaves. `ABI_VERSION` bump is the documented protection but is not mechanically enforced — author discipline only. **Required**: either (a) `cbindgen`-generated C header diff'd against a frozen baseline, or (b) an explicit per-field offset assertion test (`std::mem::offset_of!` per field, asserted against a frozen offset table). (a) is the more durable fix because it surfaces the layout change to DLL authors at integration time.

### Coverage hole C5 — `unsafe impl Send/Sync` removal on `PlatformFn` (the F3 category)
If the `unsafe impl Send for PlatformFn` line in source (`lib.rs:97–98`) were deleted, the IO trampoline holding platform fn pointers across threads would fail to compile — but the *facade* would not have changed (currently the facade does not mention the impl at all per F3). Conversely, adding `unsafe impl Send` on a type that should NOT be Send (e.g., a future heap-pointer-holding wrapper that retains thread-local state) would silently expand the safety surface without facade record. **Required**: PIF-row coverage of `unsafe impl Send/Sync` claims, asserting the impl's presence (or absence) against the facade's documented invariants.

---

## 5. Wave 2 facade-doc work (consolidated edit plan)

Seven findings (F1, F2, F3, F4 ×3 sub-findings, F5, F6, F7) resolve as **facade moves**. Single editing pass on `design/arch/facades/platform.md` covers all of them. Estimate: ~60 minutes of careful editing (slightly more than prior estimate due to the F4 PlatformManifest sub-finding addition and the stronger grounding-citation discipline); no source-side dependency; no cross-crate FIXME.

Edit plan in section order:

1. **§"Heap-typed values crossed between platform and runtime"** (lines 66–96):
   - **F1**: drop the `into_inner` line (line 82).
   - **F5 (first half)**: change `fn rc_inc(self)` → `fn inc_rc(&self)`; change `fn rc_dec(self)` → `fn dec_rc(&self)`. Add the inline note: "method names use the reversed-prefix asymmetric spelling (`inc_rc` forward; `dec_rc` reversed) matching the historical names from `cranelisp-intrinsics`; receiver is `&self` per Decision 0013 (atomic RC borrow)."
   - **F7 (first half)**: remove `#[non_exhaustive]` from the `CLOwned` declaration.

2. **§"Platform manifest and fn descriptor (DLL ABI)"** (lines 98–135):
   - **F3**: add a paragraph after the `PlatformFn` struct naming `unsafe impl Send for PlatformFn` + `unsafe impl Sync for PlatformFn` with the inline safety justification (per Principle 18 + 13 + BC §5 invariant 6; reference `lib.rs:94–98`).
   - **F4 sub-finding (PlatformManifest)**: add a sentence: "`PlatformManifest` auto-projects to `!Send + !Sync` (intentional asymmetry with `PlatformFn`'s explicit `unsafe impl Send/Sync` — the manifest is read once at DLL-load time and not retained; per-descriptor `PlatformFn` values cross thread boundaries via GOT registration)."

3. **§"Host-side descriptors (safe Rust, post-load)"** (lines 137–159):
   - **F4 sub-finding (OwnedPlatformFnDescriptor)**: add one line: "Auto-projects to `!Send + !Sync` (the `ptr: *const u8` field). Correct for single-threaded session ownership per BC §6.1; re-evaluate if cross-thread descriptor retention is introduced (W3 watch-item)."

4. **§"Host context — runtime ↔ platform bridge"** (lines 161–172):
   - **F2**: add a line naming `impl Default for HostContext` delegating to `new()` (idiomatic convenience; no semantic surface beyond `new()`).
   - **F4 sub-finding (HostContext)**: add a sentence: "`HostContext` is `Send + Sync` via auto-trait projection from `AtomicPtr<HostCallbacks>`. The projection is load-bearing for cross-thread platform-fn dispatch per BC §5 invariant 5 (subsequent calls share the static for the session lifetime); any future field addition must preserve `Send + Sync`."

5. **§"`declare_platform!` macro (DLL-author API)"** (lines 203–216):
   - **F6**: replace lines 207–213 with the current 5-key macro arm shape (mirror `lib.rs:741–757`). Add a worked example block reproducing the doc-comment example from `lib.rs:716–740` (the `static HOST`, the `extern "C" fn print_string`, the macro invocation). This is the highest-priority Wave-2 edit per the F6 grounding (external DLL-author audience; first-contact facade; current text does not compile).

6. **§"Sealed traits"** (lines 290–303):
   - **F5 (second half)**: change `fn rc_inc(&self)` → `fn inc_rc(&self)`. The `dec_rc(&self)` and the inline note at line 298 are already correct.

7. **§"`#[non_exhaustive]` DTOs"** (lines 307–318):
   - **F7 (second half)**: add `CLOwned` to the enumeration's complement (or, better, an explicit "Not annotated, rationale" sub-section), with the inline rationale: "NOT applied — single-field RAII wrapper over `T: CLHeap` (which is `#[repr(transparent)]`); private `inner` field prevents external direct construction; per `/arch`'s (closed) FIXME 0107 resolution + `design/platform/platform.md` §6, treated as a layout-adjacent contract."

All edits are in-section to `facades/platform.md`. No source-side dependency.

---

## 6. Wave 3 source-side work

**None.** Every drift resolves as facade-moves. Source is internally consistent and matches:

- Decision 0042 — `PlatformError` adopted per the six-test pin (`lib.rs:868–1029`); `manifest_to_descriptors` returns `Result<…, PlatformError>` with `ErrorLocation::unknown()` at the construction site.
- S67 W1 PFR — `PlatformFn` carries length-prefixed strings + `param_names` parallel arrays + structured per-fn shape; `declare_platform!` macro arm matches.
- Decision 0026 — `scheduling_class` declared per-fn via the macro arm; flows into the C-ABI `PlatformFn.scheduling_class: u32` and the typed `OwnedPlatformFnDescriptor.scheduling_class: SchedulingClass`.
- FIXME 0107 (closed) — `OwnedPlatformFnDescriptor` carries `#[non_exhaustive]`; CL wrappers + `CLOwned` correctly do not.

No FIXME to `/dev (platform)` filed. No source movement required.

---

## 7. Decision 0042 — `PlatformError` adoption verification

**Status: complete.** Re-verified under the new discipline.

**Source-side adoption** (post-S67 W3):
- `lib.rs:43–48`: `pub use cranelisp_types::PlatformError;` re-exported with inline Decision 42 / FIXME 0104 citation.
- `lib.rs:48`: `use cranelisp_types::ErrorLocation;` — internal use for construction-side `ErrorLocation::unknown()` calls.
- `lib.rs:612–696`: `manifest_to_descriptors` returns `Result<(String, String, Vec<OwnedPlatformFnDescriptor>), PlatformError>`. UTF-8 validation failures construct `PlatformError::LoadFailed { dll: PathBuf::new(), cause, location: ErrorLocation::unknown() }` per Decision 42's "construct, int rewrites at call site" protocol.

**Test pin** (six dedicated tests in `lib.rs` §tests, lines 868–1029):

1. `platform_error_load_failed_constructs_and_displays` (lib.rs:868–886) — pins `LoadFailed { dll, cause, location }` variant + Display + `.location()` accessor.
2. `platform_error_manifest_not_found_constructs_and_displays` (lib.rs:890–906) — pins `ManifestNotFound { dll, location }`.
3. `platform_error_abi_version_mismatch_constructs_and_displays` (lib.rs:910–933) — pins `AbiVersionMismatch { dll, expected, found, location }` + Display of all three.
4. `platform_error_dispatch_error_carries_fn_name` (lib.rs:937–955) — pins `DispatchError { fn_name: Symbol, cause, location }`.
5. `platform_error_into_cranelisp_error_preserves_location` (lib.rs:961–977) — pins `From<PlatformError> for CranelispError::Platform(_)` wrapping + span preservation through `CranelispError::span()`.
6. `manifest_to_descriptors_utf8_failure_returns_load_failed_with_unknown_location` (lib.rs:984–1029) — pins the construction-side contract: UTF-8 validation produces `LoadFailed` with `ErrorLocation::unknown()` (synthetic span) + empty `dll` path, awaiting `int`'s call-site rewrite.

**Facade alignment**: §"Errors" (facade lines 218–231) names exactly these four variants with the expected `ErrorLocation` carriers. §"Re-exports from `cranelisp-types`" line 261 names the re-export.

**Verdict**: Decision 0042 is **fully landed** in `cranelisp-platform`. Facade, source, and test pin all agree. No drift. (The Decision 0042 work in `int` — `Sess::format_error` `PlatformError` arm; call-site rewrite of `dll` + `location` — is `int`-side and outside this audit's scope.)

---

## 8. Arbitration briefs

Per the audit discipline, arbitration briefs name **what** the cross-skill question is and **what** would tip the decision either way — not "needs /arch arbitration" alone.

For `cranelisp-platform` at S69, **the audit finds zero such items.** Every drift resolves with the analysis presented above; the facade moves are bounded; no source-side movement is required; no Decision is on uncertain footing. The platform crate is in a structurally healthy position: the bounded context is settled (BC §5 + §6 partition is stable); the public surface matches the live ABI per S67 W1 PFR + Decision 0042 landing; the load-bearing Decisions (0026, 0031, 0042, 0043, 0048) all hold; Principle 14 + Principle 15 (external-audience exception) are correctly applied.

The arbitration briefs that exist in the companion `types-audit-s69.md` (A1 — SymbolTable concurrency discipline; A2 — Macro callable shape; A3 — Decision 39 scope; etc.) ARE load-bearing for the workspace, but they live **upstream** of platform — they touch `cranelisp-types` directly, and platform consumes the resolved shapes (`SchedulingClass`, `PlatformError`) without taking a position on the upstream arbitrations. Platform's facade is correctly insulated from the upstream churn per Principle 3 (dependency flows toward stability).

**This audit's prior version also found zero arbitration items.** Re-verified under the new discipline (reading the configuration before disposing): **zero arbitration items confirmed.**

**Forward-watch items** (not arbitration; just things to track each sprint):

- **W1**: When Decision 0031's "Callback support (forward commitment)" lands (spec §10.10.1 adds `Fn a b` to the platform-ABI permitted-types list), `HostCallbacks` widens to include `rc_inc`, `rc_dec`, `invoke_closure`. At that point: (a) F3's `unsafe impl Send/Sync` discipline for `HostCallbacks` may need re-evaluation; (b) the macro arm in `declare_platform!` may need to extend; (c) the F4 PlatformManifest !Send + !Sync may need re-evaluation if manifest-carried metadata grows in shape. The facade has the durable contract documented (BC §5 invariant 3) but the surface will move.
- **W2**: When out-of-tree platform DLL crates land (cranelisp-stdio first; cranelisp-fs prospective), the F6 macro-arm correction becomes critical-path. The audit assumes facade truth-telling is preventive; if a DLL author hits the F6 drift before Wave 2 lands, the cost is a confused author + a debugging session. Track Wave 2 landing relative to first out-of-tree DLL author work.
- **W3**: If `int` ever becomes multi-threaded (currently single-threaded per session per BC §6.1), the `!Send`/`!Sync` projection on `OwnedPlatformFnDescriptor` (F4 sub-finding) becomes a real constraint, not auto-trait noise. Re-check next audit.
- **W4** (Principle 15 health-check, annual): F9's four-clause test re-applied at each audit. Currently passes; watch for third re-export appearing without per-item rationale, re-export of implementation-crate-only type, or convenience re-export without DLL-author grounding.

---

## Verdict

`cranelisp-platform` is in the healthiest structural position of any implementation crate audited under the per-item-analysis discipline. **All findings resolve as facade-moves, zero source-side moves, zero arbitration items.** This audit's 5-block discipline with explicit configuration grounding flipped **1 prior disposition** (F4's `OwnedPlatformFnDescriptor` + `PlatformManifest` !Send + !Sync sub-findings, from "no action — auto-trait noise" to "facade moves — annotate per Principle 18 + 13"); 8 other dispositions are unchanged in direction but all now carry explicit Decision/Principle citations the prior audit lacked.

The three most consequential flips/strengthenings:

1. **F4 (Send/Sync annotation discipline — flip)**: Principle 18 (enforce architectural invariants structurally) elevates marker-trait projections from "auto-trait noise" to "structural invariants the facade should declare." Adds the previously-overlooked PlatformManifest !Send + !Sync sub-finding (intentional asymmetry with PlatformFn's explicit impls). The facade now must annotate all three Send/Sync projections.
2. **F6 (`declare_platform!` macro arm — grounding strengthened)**: Provenanced to the S67 W1 PFR refactor that updated the manifest section of the facade but did NOT update the macro section in the same pass. Decision 0026 grounds the per-fn `scheduling_class` requirement that makes the five per-fn fields non-optional. The drift now has a documented origin and an unambiguous resolution.
3. **F5 (`CLHeap` method names + receiver — grounding strengthened)**: Decision 0013 (atomic RC `SeqCst` from Ring 1) mandates the `&self` receiver — `self`-by-value is **structurally incorrect** for the borrowed atomic RC operation, not merely a facade preference. The two facade blocks must both normalise to source; this audit grounds the normalisation in the atomic-RC contract rather than in "source is settled."

Decision 0042 (`PlatformError` adoption): fully landed in `cranelisp-platform`, six-test pin verified.

Principle 15 external-audience exception: still narrowly scoped, two re-exports, each justified inline against the four-clause test.

The five mechanical-coverage gaps (C1–C5) are real and largely deferred — they describe what the conformance triad cannot catch by construction. The highest-priority of the five is **C3** (compile-fixture for `declare_platform!`), which would catch any future F6-style drift at PR gate. Queue for S70 `/qa` enhancement scope.

**No FIXMEs filed.** Wave 2 facade-doc edits clear every drift finding in-sprint. If Wave 2 cannot land in S69, a `0NNN-design-platform-facade-refresh-s69.md` FIXME with `target: /design` records the carry; otherwise no carry.
