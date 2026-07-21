# S115 backend design — carrier-state evidence, RC-release sweep, R4/R6 censuses

**Status:** DESIGN (S115 Phase 3, `/design`(backend) narrow). Produces the
`/arch`-required deciding evidence for the GOT-slot carrier-loss pair (SPRINT.md
§Architecture-review §3 / `tests/plan/s115-test-plan.md` §1.5) BEFORE the fix
wave, and the design shapes for the four backend-owned S115 scope inputs: the ONE
RC-release sweep (§2), the 0705 consumer-totality arm (§3), the R4 mangle-family
injectivity census (§4), and the R6 persisted-index validation seam (§5). §6
confirms the W-B5 patch-collapse; §7 dispositions FIXMEs 0696/0697.

**Governing authority:** `design/arch/safety-invariants.md` §4 register rows R4
(keyed-identity injectivity) + R6 (persisted-index trust boundary) — re-audited
this Phase 2, SCHEDULED S115; `design/backend/backend-keyed-consumer.md`
§1.2/§10 (the wrapper-emission keyed-read seam) + `typed-resolution-carrier.md`
§4 (the closed `VarRef`/`ApplyRef` sums); `design/backend/ownership-codegen.md`
§13.7 + `binding-indirection-consume.md` (the consume family this sweep sits
beside). Subordinate to `backend.md` (§8 indexes this doc).

---

## 1. Carrier-state evidence dumps (the gating deliverable)

`/arch` (SPRINT.md §3) ruled the GOT-slot pair presumptively TWO fixes on
opposite sides of the carrier contract and named the deciding step: **for each
repro, dump the carrier state as read at the wrapper-emission seam — `VarRef`
verdict + `ApplyRef` + slot presence — before any fix wave opens.** This section
is that dump, taken at HEAD against the debug binary with a throwaway env-gated
probe at the two seams (`compile_resolved_call`'s `AutoCurry` arm in
`apply.rs`; the `got_entry_at` GOT-terminal in
`control_flow/fn_as_value.rs::emit_wrapper_call` — probe reverted, tree clean).

### 1.1 The wrapper-emission seam (where both repros converge and fail)

Both repros are partial applications (auto-curry: 1 arg applied of a 2-arg
target) and both die at the SAME terminal —
`control_flow/fn_as_value.rs::emit_wrapper_call:600-609`:

```
fn-as-value wrapper for '<name>' reached codegen with no GOT-slot carrier
(S110 W2 keyed read; backend-keyed-consumer.md §1.2/§10)
```

The terminal fires when `target_fq.and_then(|fq| self.ctx.got_entry_at(fq))`
is `None` — i.e. either the carrier is `None` at the seam, or the carrier
resolves to a symbol-table entry that carries **no GOT slot**. The dump
discriminates which, per repro.

The producer path that feeds this seam (verified in
`crates/cranelisp-typecheck/src/program/mono_collect.rs::resolve_auto_curry`,
`:790-821`): an `AutoCurry` with a resolved inner (`has_inner`) derives its
Apply-span carrier from that inner resolution; a plain-fn auto-curry over a
**`VarRef::Global`** callee TRANSPORTS the callee's storage FQ as
`ApplyRef::Dispatch(fq)`; a curry over a **`VarRef::Local`** callee matches
nothing → the `ApplyRef::ViaCallee` epilogue default stands.

### 1.2 Repro A — 0705 AutoCurry-over-a-LOCAL-closure

Source (`PrimitivesOnly`, `--run`), the FIXME 0705 minimal repro:
```clojure
(defn f [] (let [g (fn [a b] 0)] ((g 1) 2)))
(defn main [] (Pure (f)))
```
Dump at the seam:
```
AutoCurry target=g applied=1 total=2  ApplyRef=ViaCallee  inner_trait_resolution=None
emit_wrapper_call GOT-terminal  target_name=g  target_fq=None  got_entry_at=None
```

**Verdict — carrier CORRECT at the seam → BACKEND consumer-totality fix.**
`g` is a `let`-bound local closure; typecheck rightly records the callee `Var`
as `VarRef::Local` (a local closure has no GOT slot), so the Apply is
`ApplyRef::ViaCallee` and the wrapper receives `target_fq=None`. This is the
correct, complete producer output — there is no dispatch FQ to record. The gap
is that the wrapper emitter has **no arm for currying a local closure value**:
it exhausts `func_ids` (miss — `g` is not a compiled unit fn), ctor
(`ctor_meta_at` miss), inline-primitive (miss), and hits the GOT terminal with
`None`. This exactly matches `/arch`'s presumption: **0705 is the backend half.**
The fix (the curry-the-local-closure-value arm) is designed in §3.

### 1.3 Repro B — fn-as-value `'='` face (impl-present trait operator)

Source (`TestStandard`, `--run`), `s114-test-plan.md` §11 item 5 / test
`fn_as_value_carrier_loss::trait_operator_partial_app_impl_present_has_got_carrier`:
```clojure
(defn g [x] (= x))
(defn main [] (Pure (if ((g 3) 3) 5 0)))
```
Dump at the seam:
```
AutoCurry target==  applied=1 total=2  ApplyRef=Dispatch(prelude/=)  inner_trait_resolution=None
emit_wrapper_call GOT-terminal  target_name==  target_fq=Some("prelude/=")  got_entry_at=None
```

**Verdict — carrier WRONG at the seam → TYPECHECK PRODUCER gap. The two do NOT
collapse; the conditional /dev(typecheck) slot FIRES.** The carrier is present
but points at **`prelude/=`** — the Eq trait-method DECLARATION FQ, which is
NOT a slotted callable (`got_entry_at(prelude/=) = None`; only a resolved impl —
the `eq-i64` builtin, or a mangled `=$…` in an impl module — carries a slot).
`inner_trait_resolution=None` is the smoking gun: `resolve_auto_curry` did NOT
resolve the operator to its impl for this instance, so the else-branch
(`mono_collect.rs:807-820`) transported the callee `Var`'s raw
`VarRef::Global(prelude/=)` as the dispatch carrier. Per `/arch` §3: a face
arriving `Global`/`Dispatch` with **no slot carrier** is a typecheck-side fix.

**Discriminating control (decisive).** The DIRECT concrete partial-app — no
generic wrapper — compiles and runs:
```clojure
(defn h [] (= 3))
(defn main [] (Pure (if ((h) 3) 5 0)))     ; → exit 5
```
Dump: `ApplyRef=Dispatch(primitives/eq-i64)  inner_trait_resolution=Some(BuiltinFn{eq-i64})`,
and `got_entry_at(primitives/eq-i64)` HITS. So `resolve_auto_curry`'s late
re-resolution (`mono_collect.rs:770-787`) works when the operand type is
concrete AT the point the auto-curry is resolved. The gap is specifically the
**generic → mono-instance (late-pinning) path**: when the auto-curry over `=`
lives inside a generic `g` monomorphised at Int, the auto-curry's
`trait_resolution` is not re-resolved against the concrete instance types (the
resolution ran in the template context where `= : (Fn [a a] Bool)` is
non-concrete → `try_resolve_trait_method` fails → `inner=None`). This is the
`§1.1.3` map-provenance / check-run-pairing territory
(`backend-keyed-consumer.md`): the mono-instance body's auto-curry carrier is
derived from the enclosing template run, not re-resolved per instance.

**Boundary the dump draws for the typecheck fix:** never transport a
trait-method-DECLARATION FQ (`prelude/=`) as a dispatch carrier — a decl is not
a slotted storage key (the `backend-keyed-consumer.md` §1.1 carrier
value-source rule: a carrier is a resolved storage key, walk-resolved /
mint-resolved / transported, never a raw operator spelling's decl). The
principled cure is to re-resolve the mono-instance auto-curry's `trait_resolution`
against the concrete instance types (yielding `Dispatch(primitives/eq-i64)` /
the mangled impl FQ, both slotted), so `has_inner` is true and the
`record_dispatch_target` path — not the `VarRef::Global` transport — sets the
carrier.

### 1.4 Phase-4 consequence (the gate output)

| Repro | Carrier at seam | Slot present | Verdict | Owner |
|---|---|---|---|---|
| 0705 AutoCurry-over-local | `ApplyRef::ViaCallee` + callee `VarRef::Local`, `target_fq=None` | n/a (correctly none) | carrier CORRECT | **backend** (§3 arm) |
| `'='` fn-as-value (generic-mono) | `ApplyRef::Dispatch(prelude/=)`, `target_fq=Some(prelude/=)` | **absent** (trait-method decl, not a slotted callable) | carrier WRONG (producer) | **typecheck** (mono-instance auto-curry re-resolution) |

The pair does **not** collapse into one backend change-set. Phase 4 holds the
conditional `/dev`(typecheck) slot for the `'='` face; the backend fix wave lands
only 0705's arm (§3). `MC-E1` note (`s115-test-plan.md` §1.5): any pin
colour-change under either change-set is reported to `/qa` as attribution
evidence, not a win/regression.

---

## 2. The RC-release sweep — ONE change-set, three faces (deliverable 2)

Per `s114-test-plan.md` §11 item 4 / §11.1 item 2 (entry-payload leak) + §12
item 6 (0720 ADT-wrapped supersede), `/qa` scopes these as ONE backend sweep
(shared oracle-lane criticality: both poison a future `allocs==deallocs` cell).
Faces and seams:

### 2.1 Face 1+2 — entry-`main` IO-result heap PAYLOAD leak (both toggles)

**Seam:** `compiler/rc_emission.rs::protect_return_value:275-344` — the F-R1
entry-frame suppression (`:303-309`) + the entry-`main` IO teardown it hands to
(`cranelisp_intrinsics::drop::consume_io_tree`, the single trampoline consumer).

**Discriminators (measured at HEAD, `RC_STATS`):**
- Scalar Pure-box `(defn main [] (let [s "hi"] (Pure 9)))` — **balanced**
  (allocs=2 deallocs=2). The W4 F-R1 fix covers this.
- Heap-payload `(defn main [] (let [s "hi"] (Pure s)))` — **leaks 1**
  (allocs=2 deallocs=1; rc_inc=2 rc_dec=1), and **toggle-INDEPENDENT**: identical
  2/1 under `CRANELISP_NO_OWNERSHIP=1`. The payload `s` acquires a second
  reference (the `Pure`-store consuming inc) that no dec balances — the
  trampoline's one `consume_io_tree` dec frees the box shell and decs the payload
  once, but the store-inc's matching dec (the `let`-scope dec of `s`, or a
  payload-recursive teardown dec) is absent.

**Fix shape.** The F-R1 suppression is licensed for the *box* over-inc only; it
must not leave the *payload's* store-inc unbalanced. Two admissible mechanisms
(the `/dev` wave picks the one that keeps the scalar face balanced):
(a) at the entry-`main` fresh-`Pure(payload)` return, do not suppress the
balancing accounting for a HEAP payload — suppress the box protect but let the
`let`-scope dec of the moved-in binding stand (so payload nets to the box's
single owned ref, freed by `consume_io_tree`); or (b) make the entry teardown's
box drop-glue recursively release the heap payload (the payload's own
reference), so the store-inc is balanced at teardown. Face 2 (toggle-ON heap
payload) is the SAME mechanism — the fix covers both; the toggle-OFF face is the
oracle-lane-critical reference-semantics one (pin
`adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2`).

**Hazard (binding, `s115-test-plan.md` §0 risk-2 / arch seq item 4):** must not
weaken the general G2/item-26 protect — the entry-frame suppression is licensed
SOLELY by the entry-`main` single-consumer trampoline contract; a non-`main` fn
or an `Apply` return that MAY alias an argument keeps its protect. `allocs ==
deallocs` EXACTLY (never leak → under-count).

### 2.2 Face 3 — 0720 ADT-wrapped superseded loop-param never released

**Seam:** `compiler/fn_compiler.rs::flush_superseded_heap_params_before_tail_jump
:1210-1233` + its `collect_frame_heap_decs:1069` / `is_heap_type:1327`
classification (`signature_heap_category ∈ {AlwaysHeap, Mixed}`). Called from
`apply.rs::compile_tail_self_call:1948`.

**Discriminators (measured at HEAD, `RC_STATS`, exact `adt_wrapped_supersede_leak_0720`
shape `(deftype G2 (Gr [cells]))`):**
- ADT-wrapped supersede loop, N=200: allocs=403 deallocs=2; N=400: allocs=803
  deallocs=2 — **2 objects/iteration leak** (the `Gr` box AND its `cells` vec),
  residue scales ~2·N. `reuse_hit=0 reuse_miss=0` (the flush's COW accounting
  never engages for this param). **Toggle-independent** (analysis-OFF: allocs=403
  deallocs=3).
- Bare-vec twin `(defn go [v m] … (go (vec-set v 0 m) …))`, N=200: allocs=202
  deallocs=202 — **balanced** (`reuse_miss=200`; the superseded `v` is flushed).

**Isolation (decisive — the flush is the seam, NOT set0's match-consume).** A
variant that supersedes the loop param with an UNRELATED fresh box —
`(defn go [g m] … (go (Gr [9 9]) …))` (no match-extract of `g` in the tail
arg) — leaks IDENTICALLY (403/2, 2/iteration). Since `g` is not consumed by any
op in the tail argument here, the missing release can only be the tail-jump
flush failing to dec the superseded `Gr` loop param. A single-ctor product ADT
(`Gr` wrapping a vec — a real heap box, not value-flattened: 2 allocs/iteration
prove the separate box) is not being released by
`flush_superseded_heap_params_before_tail_jump`, whereas the bare-vec param IS.

**Fix shape.** The flush must release a superseded single-ctor-product ADT loop
param exactly as it releases a bare-vec loop param. Root-cause candidate for
`/dev` to confirm: `is_heap_type(Gr)` / the param-frame `variable_types`
population under-classifies the product-ctor ADT param, so
`collect_frame_heap_decs` filters it out. The dec routes through
`emit_heap_binding_decs:1100` → `emit_rc_dec_with_inline_drop_glue` (the ADT
inline drop-glue path, which recursively decs the `cells` field on rc→0) — so
once the param is admitted to the dec set, BOTH leaked objects are released.

**Hazard (binding):** the MS-P8 param-flush must balance in BOTH conj arms and
honor the existing exemptions — `transfer_skip` (a bare top-level `Var` tail arg
MOVES, no dec), borrowed params, and the analysis-ON in-place-COW exemption
(`param_flush_exempts_inplace_cow`, `:1503` / FIXMEs 0691/0695 — a param SOME
tail arg is an in-place COW rooted at is NOT superseded; toggle-off always
copies so the dec is owed). Admitting the ADT-wrapped param must not disturb the
bare-vec twin (must stay balanced) nor re-introduce the 0691 cross-position UAF.

### 2.3 Sweep acceptance

`allocs == deallocs` EXACTLY at each face (never leak → under-count); the tier-4
safety lane + `RC_STATS` pins are the acceptance instrument (arch seq item 4).
Unit tier per METHOD §2.2 at each seam (`s115-test-plan.md` §6.5): the tail-jump
flush ADT-wrapped-param arm; the entry-frame protect license under both toggles.
The three e2e pins
(`adt_drop_glue_underkey::entry_main_ioresult_heap_payload_toggle_off_leak_r2`,
`adt_wrapped_supersede_leak_0720::{…loop_does_not_leak, …residue_does_not_scale_with_n}`)
flip green; the bare-vec twin GREEN control holds.

---

## 3. 0705 consumer-totality — the curry-the-local-closure arm (deliverable 3)

The §1.2 dump confirms the backend half: an `AutoCurry` whose Apply is
`ApplyRef::ViaCallee` and whose callee `Var` is `VarRef::Local` is a legal
carrier state with **no emission arm**. The unifying commitment (`/arch` §3, P24
corollary prong 3 / P20 exhaustiveness): **the wrapper-emission seam is total
over the closed carrier sum.** After the S114 typed-resolution flip
(`typed-resolution-carrier.md` §4), the carrier sums are CLOSED:
`ApplyRef ∈ {Dispatch(FQ), ViaCallee}` and `VarRef ∈ {Global(FQ), Local{binder,
binding_span}}`. The seam must have an arm for every legal state and a located
producer error for nothing else — **no `_ =>`**.

**The totality over the closed sums (the emission contract at the auto-curry
seam):**

| Carrier state | Emission arm | Status |
|---|---|---|
| `ApplyRef::Dispatch(fq)`, `fq` a slotted callable | GOT-indirect wrapper call (`emit_wrapper_call` GOT terminal) | landed |
| `ApplyRef::Dispatch(fq)`, `fq` in current unit `func_ids` | direct wrapper call | landed |
| `ApplyRef::Dispatch(fq)`, `fq` a ctor / inline-primitive | ctor-construct / inline-emit arms | landed |
| inner `TraitMethod`/`BuiltinFn` resolution | self-derived impl carrier (`emit_curry_target_call`) | landed |
| **`ApplyRef::ViaCallee` + callee `VarRef::Local`** | **curry the LOCAL CLOSURE VALUE (NEW)** | **0705 — owed** |
| `ApplyRef::Dispatch(fq)` with no slot / entry miss | located `CodegenError` (no name-resolver fallback, Rev-2) | landed (the loud terminal) |

**The new arm.** When the auto-curry callee is `VarRef::Local`, the target is a
scope-stack closure value, not a table symbol. The wrapper must capture that
closure value (from `self.variables` / the scope stack, by the local `binder`)
and curry the CLOSURE — i.e. the auto-curry closure captures the applied args
AND the local closure value, and its body forwards all args to the captured
closure via `compile_closure_call` (the GOT-indirect `call_indirect` over the
closure's embedded `CODE_PTR`), NOT via a `target_name` GOT-slot lookup. This is
the auto-curry analogue of the locals-first dispatch already in
`compile_var_apply:913-919` (a shadowing local wins the closure-call path
unconditionally) and `compile_closure_call`; 0705 extends that discipline from
the FULL-application path to the PARTIAL-application (auto-curry) path.

**Totality argument (no `_ =>`).** The `ApplyRef` sum is closed and
`#[non_exhaustive]`-free at the seam (`typed-resolution-carrier.md` §4); the
`VarRef` sum likewise. `ViaCallee` means "the identity rides the callee `Var`" —
so the callee's `VarRef` is the SOLE remaining discriminator, and it is one of
exactly two: `Local` (the new arm — curry the captured closure) or `Global`
(unreachable here — a `Global` callee under a plain-fn auto-curry would have been
transported to `ApplyRef::Dispatch` by `resolve_auto_curry:807`, so a
`ViaCallee` + `Global` is a producer contradiction → located error, the honest
floor). Every legal `(ApplyRef, VarRef)` pair thus has an arm; the illegal pair
is a located producer error. The threading: `compile_auto_curry_call` already
receives `apply_target: Option<&FQSymbol>` (`None` for `ViaCallee`); it must ALSO
receive the callee `Var` node (or its `VarRef`) so the seam can read the `Local`
binder and compile the closure value — a signature widening internal to
`apply.rs`/`fn_as_value.rs`, no cross-crate type change.

**Control (born-green, `s115-test-plan.md` §1.5).** The non-trait local
`(defn f [] (let [g (fn [a b] 0)] ((g 1) 2)))` isolates the arm from trait
dispatch; the FULL application `(let [g (fn [a b] 0)] (g 1 2))` already compiles
(exit 0) and must stay green. Unit tier: the emission-seam totality (each carrier
state → its arm; the illegal state → located error) per METHOD §2.2.

---

## 4. R4 — mangle-family injectivity census (owed O3; deliverable 4)

`safety-invariants.md` §4 R4: every mangle semantic-identity → symbol is
injective, or additionally disambiguator-keyed. Drop-glue is `witnessed`
(CS-1.2). This census covers **every other symbol-mint site**; the two naming
primitives in `compiler/resolution.rs` are the natural home, extended to the
platform/typecheck-boundary mints. Per family: witness exists / disambiguator-keyed
/ OWED-witness (naming the `/dev` build).

| Family | Mint site | Key | Verdict |
|---|---|---|---|
| ADT drop glue / vec elem-dec | `resolution.rs::adt_instantiation_mangle:156` → `adt_drop_glue_name:219`; `build_elem_dec_fn` | `escape_symbol(render_type(…,Qualified,Numbered))` | **witnessed** — `escape_symbol:182` is injective + prefix-free with a total decoder (CS-1.2 model); round-trip battery in `resolution/tests.rs`. Debug-asserts concreteness (S-2). |
| inner-fn discriminators | `resolution.rs::inner_fn_discriminator_for:66` | sanitize (non-injective `[^A-Za-z0-9_]→_`) **+ span** | **disambiguator-keyed** — the sanitize map alone collapses `-`/`.`/`/`/space, but every consumer additionally folds `span.start_span.end` (the mono-instance + create-gate arm); the span breaks sanitize ties. VERIFY: confirm no consumer uses the disc WITHOUT a span fold. |
| closure/curry capture drop glue | `resolution.rs::closure_drop_glue_name:99` / `curry_drop_glue_name:110` | `disc + span` | **disambiguator-keyed** — disc+span, paired identically to the lambda/wrapper body name (FIXME 0350 class closed). Safe. |
| trait-method-value wrapper | `fn_as_value.rs::compile_trait_method_as_value:268` (`__wrap_tmv_{target}_{disc}{span.start}_{span.end}__`) | `target + disc + span` | **disambiguator-keyed** — disc+span. Safe (same discipline). |
| GOT data symbols | `resolution.rs::got_data_symbol_name:50` (`__cranelisp_got_{module.replace('.','_')}`) | flattened module path | **OWED-witness** — the `.`→`_` flatten is NON-injective: module names admit `_` AND `-` (reader.rs:226), so a two-component path `a.b` and a one-component module `a_b` BOTH flatten to `__cranelisp_got_a_b` → two modules share ONE GOT slab data symbol (cross-module wrong-slab dispatch — the R4 class, one level up from drop-glue). Constructible in a multi-module program. **/dev builds:** an injective flatten (escape `.`/`_`/`-` via the `escape_symbol` scheme, or a per-module disambiguator) + a round-trip witness. |
| platform GOT / layout-hash exports | `cranelisp-platform/src/declare.rs:343/223` (`__cranelisp_got_platform_<name>`, `__cranelisp_layout_hash_<name>`) | platform `<name>` verbatim (macro `concat!`) | **disambiguator-keyed by uniqueness** — one platform ⇒ one name, `concat!`'d literal, no flatten; injective iff platform names are unique (a load-time invariant — two loaded platforms sharing a name is a diagnosed load condition, out of R4's mangle scope). **Cross-crate:** the mint lives in `cranelisp-platform`; record the census row there via FIXME if a witness is wanted; no backend action. |
| LinkerSymbol / mangled method keys | **typecheck-side** (`impl$FQType$FQTrait`, `add$Int+Int`; `checker.rs:2630`, the `$`/`+`-joined FQ mangle) — backend consumes verbatim as a Cranelift symbol | `$`/`+`-delimited FQ component join | **OWED-witness, CROSS-CRATE** — injectivity depends on the FQ-component join being unambiguous; `$`/`+` are delimiters and FQ names should not contain them, but a `render_type` containing `+` (arg separators) could alias. The mint is typecheck's; the backend cannot witness it. **Route:** FIXME `target: /arch` (or the R4 typecheck sibling) — the census records the family as owed at its true mint site, not backend `resolution.rs`. |

**Census verdict:** the two backend `resolution.rs` naming primitives are
otherwise witnessed/disambiguator-keyed; the ONE backend-owned OWED-witness is
`got_data_symbol_name` (the flatten collision). The platform and LinkerSymbol
families are owed but mint OUTSIDE backend — recorded here for completeness and
routed cross-crate. `/qa` reserves the §6.2 R4 witness rows against this final
family set (do not pre-guess — the 0660 discipline; the concrete rows land when
this census is the artifact).

**Register-row remedy language (R4):** *"drop-glue witnessed (CS-1.2);
inner-fn/closure/curry/tmv-wrapper disambiguator-keyed (span/disc); GOT data
symbol `got_data_symbol_name` is the ONE backend OWED-witness — the `.`→`_`
flatten is non-injective over `_`/`-`-bearing module names (constructible
cross-slab collision); /dev builds an injective flatten + round-trip witness.
Platform export names (uniqueness-keyed, cranelisp-platform) and typecheck's
`$`-join LinkerSymbol/method mangle (cross-crate, owed at its mint) are routed to
their own homes."*

---

## 5. R6 — persisted-index validation seam (deliverable 5, for /dev(backend, cache))

`safety-invariants.md` §4 R6: every index/key/slot deserialized from
`.meta.json` is validated at load; violation = diagnosed `CacheStale`, never
trusted into emission. Trust-boundary taxonomy (§2 tier 3): cache bytes are
external data — **diagnose and recompile, never `assert!`.**

**The ONE seam.** `cache/serialize.rs::deserialise_meta_with_build_id:248-304`
already carries the single existing per-entry validation loop (`:294-303`,
`callable_got_slot() < GOT_TABLE_SIZE` → `CacheStale::GotSlotOutOfRange`). The
R6 census extends THIS loop (never a parallel walk) with one arm + one
`CacheStale` class per persisted-index family.

**Persisted-index census (the seed list, each → its own `CacheStale` class):**

| Persisted index | Corrupt-bytes hazard | Validation arm | `CacheStale` class |
|---|---|---|---|
| `callable_got_slot()` | OOB slot → `store_slot`/`load_slot` `assert!` panic on disk content | `< GOT_TABLE_SIZE` | `GotSlotOutOfRange` (landed) |
| borrowed sibling slot (`borrowed_sibling_slot`, R5 carrier) | OOB → same GOT panic when its first consumer reads it | `< GOT_TABLE_SIZE` (per-entry, if present) | `SiblingSlotOutOfRange` (NEW) |
| summary param indices — `ResultMode::MayAliasOf(k)` | `k ≥ arity` → `arg_origins[k]` OOB read at the consume seam | `k < def.arity()` (per summary) | `SummaryParamIndexOutOfRange` (NEW) |
| `callees` FQs (feeds the future reverse index) | malformed FQ (empty module/symbol) → resolve/reverse-index corruption | non-empty module + symbol per FQ | `MalformedCalleeFq` (NEW) |
| span keys (`resolved_targets`/mono-view sidecar keys, if persisted) | `start > end` / out-of-source span → keyed-read miss or panic | `start ≤ end` (well-formed span) | `MalformedSpanKey` (NEW) |

**Design constraints for the /dev(backend, cache) change-set:**
- ONE loop, ONE pass over `table.all_symbols()` (extend the existing
  `:294` loop; the per-family arms are cheap field checks, no allocation).
- Every arm diagnoses `CacheStale` (→ recompile) and NEVER `assert!` — the tier-3
  external-data sub-form (contrast the in-process `store_slot` `assert!`).
- The census table lands as a **durable artifact in the cache-submodule rustdoc**
  (`cache/serialize.rs` or `cache/mod.rs` `//!`) per `/arch` revision 3, and
  `/review` verifies census COMPLETENESS against it (no persisted index escapes a
  row).
- Any NEW persisted index added later adds its row + arm in the same change-set
  (the R6 maintenance rule).

**Testability (`s115-test-plan.md` §6.1):** unit tier — corrupt each index
(out-of-range sibling slot; `MayAliasOf(k≥arity)`; malformed `callees` FQ /
span key) → its distinct `CacheStale` class; valid meta round-trips untouched
(false-fire fence). E2e — tamper a persisted `.meta.json` field (summary index)
in a warm cache dir, re-run → recompile + correct output, no crash, no
stale-summary elision.

**Note on 0637 (R5 row).** The sibling-slot VALIDATION is co-landed here (R6),
but the sibling-slot CONSUMER remains parked to its first reader (R5 ruling,
re-affirmed S113 W5 — validating an unread index guards nothing; the co-landing
rule is the mechanism). The R6 arm above validates the sibling slot's RANGE at
load defensively (cheap, uniform with the loop); it does not build the consumer.

---

## 6. W-B5 patch-collapse — S114-endorsed design is current (deliverable 6)

The W-B5 change-set (`binding-indirection-consume.md` §5 item 4 / §W-B5 table
row / §7 wave map) is unchanged and current: **collapse the three fn-return
patches (`skip_var` / `protect_return_value` / `return_cow_source`) onto the ONE
provenance contract** — the "three ad-hoc patches for one flow" 0668 named. It is
the hygiene tail AFTER the consume family flips green; `/review` ENDORSED the
S114 deferral to its own S115 change-set (golden/RC regression risk).

**Acceptance (restated, binding):** NO flips — this is a byte-identical-off
refactor; goldens byte-identical-off and CERTIFIED (the `/qa`/`/testing`
golden-frame re-baseline discipline: extension ≠ re-baseline); the S114
must-hold cells HOLD (`l_c3` ×2, `vec_lifecycle`, A/E ×2); no new RED. It is its
OWN reviewed change-set (not folded into the RC sweep §2, though it touches the
same `fn_compiler.rs` fn-return seam — serialize the change-sets).

**Interaction with §2 and 0696.** The RC-sweep §2.1 entry-payload fix touches
`protect_return_value`, which W-B5 collapses. Land the RC sweep FIRST (a
behavioral fix with its own pins), then W-B5 folds the corrected
`protect_return_value` into the provenance contract (a no-flip refactor over the
already-correct behavior). 0696's re-keying (§7) rides W-B5.

---

## 7. FIXME dispositions (deliverable 7)

### 0697 — R3 whole-match approximation (target: /design) — RESOLVED, recorded, delete

FIXME 0697 (filed by `/review` W4): the `binding-indirection-consume.md` §2
table keys forwarding on "the SELECTED arm" (a runtime notion), but the
implementation `match_forwards_scrutinee` (`fn_compiler.rs:298`) is a STATIC
whole-match predicate (ANY var-pattern arm that forwards its binder), and the R3
suppression is emitted once in the merge block (`match_codegen.rs:180-183`). For
a MIXED constructor+var match whose var-default arm forwards the scrutinee
(`(match (norm o) [(None) (mk-default)] [x x])`), the suppression applies on ALL
paths, so a run selecting the ctor arm never decs the genuinely-consumed temp
scrutinee → leak. Leak-safe polarity (never a dec added); a strict improvement
over the pre-W4 var-arm UAF.

**Resolution:** the approximation, its polarity argument, and the
mechanism-complete alternative are now RECORDED in
`binding-indirection-consume.md` §2 (the whole-match approximation box added this
sprint). The follow-on (per-arm dec placement — move the temp-dec into the
non-forwarding arms before the merge jump) is NAMED and PARKED ("document movable
boundaries decisively, then park" — the boundary is movable when a real
mixed-arm-leak shape forces it). A `/qa` tripwire row for the mixed-arm ×
{ctor-path, var-path} × toggle cells is requested via FIXME (target: /qa) so the
parked boundary is fenced. **0697 DELETED** with this design touch.

### 0696 — F-R1 suppression keys on the bare name "main" (target: /dev) — DESIGN ruled, /dev implements with W-B5

FIXME 0696 (filed by `/review` W4, Suggestion, `target: /dev`): the F-R1
suppression fires on `current_fn_name == "main"` + nullary + tail + fresh
construction (`rc_emission.rs:303-309`) — name-as-identity (the 0632 /
Principle-19 class), safe today ONLY because `body_is_fresh_construction`
independently guarantees the box is fresh, not because of the trampoline
contract the comment claims as sole license.

**Design ruling (this doc; the /dev fix consumes it).** The real license is
**freshness**, not the bare name `main`. Two principled directions, ordered:
(a) key the suppression on the **entry contract** (the module+symbol the
trampoline actually invokes, available from the compile context) rather than the
bare name — removes the Principle-19 over-match; or (b) if freshness is the true
license, generalize to the **item-26 fresh-construction return** (superseding the
`main`-special-case entirely) — a `body_is_fresh_construction` return needs no
protect regardless of the fn name, because scope cleanup cannot touch a fresh
box. Direction (b) is the deeper cure and aligns with §2.1's entry-payload work
(the entry-frame accounting is being re-examined there anyway). **This is a
DESIGN ruling into a `/dev`-targeted FIXME**; 0696 stays in place (only `/dev`
deletes a `/dev`-targeted FIXME) and rides the W-B5 change-set (§6) — its
re-keying is the same three-patch flow W-B5 collapses. No behavioral urgency
(current over-match is leak-fixing, never unsafe). Recommend `/sprint` let
`/dev` action + delete 0696 when W-B5 lands, against direction (a)/(b) as
`/dev`+`/review` weigh the churn.

---

## 8. Testability + cross-references

- Fix-wave unit obligations enumerated in `s115-test-plan.md` §6.5 (§2 tail-jump
  flush arm + entry-frame protect both toggles; §3 wrapper-emission totality per
  carrier state + illegal-state located error).
- No `cranelisp-types` / `CACHE_SCHEMA_VERSION` / public-API change in any §2/§3
  backend change-set (arch §7). §5 R6 adds NEW `CacheStale` variants — a
  backend-internal enum (not persisted), no schema bump. §4's `got_data_symbol_name`
  fix changes an INTERNAL relocation-symbol scheme (no persisted surface); the
  LinkerSymbol/platform families route cross-crate via FIXME.
- Cited by `backend.md` §8; extends `ownership-codegen.md` §13.7 + the
  `binding-indirection-consume.md` consume family (§2.2 flush, §2.1 fn-return).
