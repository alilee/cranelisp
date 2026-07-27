# The concreteness programme, types first — design commission

**Status:** WORKING DESIGN (`/arch`, S119, 2026-07-28) — the design commission for
the user-directed concreteness programme, following `total-concreteness.md`
(which this document amends in one clause: I-ABI → I-EMIT, §1 below).
**Cross-check instrument:** `sprints/concreteness-requirements.md` (40 rows;
the per-row disposition table is §6 — the register is `/sprint`'s; corrections
to it are returned in §7, not edited in place).
**Governs:** the S120 `cranelisp-types` change-set (§3), the wash order (§4),
FIXMEs 0931–0935, and the NC-R re-labelling (FIXME 0936).
**Archive trigger:** the types change-set and the downstream wash land; the
representation contract folds into `module.rs` rustdoc + BC §7 + R11; this file
moves to `design/arch/archive/`.

**Verification statement (R-40).** Every factual claim about source in this
document was read at HEAD by `/arch` during this commission and is cited
file:line; claims inherited from other documents were re-verified, and two were
found wrong (§2, §7). Two runtime experiments were run (REPL, no source
changes); their transcripts are summarised inline at §2.

---

## 1. I-ABI is re-ruled: I-EMIT — no polymorphic callable at the typecheck boundary

### 1.1 What is overridden, and why

`total-concreteness.md` §2 I-ABI permitted a closed roster of four hand-written
callables (`bind`, `race`, `select`, `catch-runtime-error`) that are slot-less
but **polymorphic at the typecheck boundary**: non-concrete schemes on callable
entries, dispatched by ABI name, referenced as-is by the emitted tree. The user
direction (R-25/R-27) overrides that: at every call site the instantiation *is*
known — post-mono every `MonoExpr` node carries a `ConcreteType`
(`crates/cranelisp-types/src/mono_expr.rs`, no `Var` variant by construction) —
so typecheck must emit a **concrete call**, and how the callee is realised is a
backend concern invisible to the tree. The roster licence does not survive under
a new name; the replacement clause has no licence in it:

> **I-EMIT (replaces I-ABI).** The tree typecheck emits contains **no reference
> to a polymorphic callable**. Every emitted call site is fully concrete (node
> concreteness is already structural under I-FRAME), and its **dispatch
> identity** resolves to a concrete realization: (a) a slotted concrete entry,
> (b) an inline lowering at the site — the `PrimitiveBody::Inline` model, where
> the site's own concrete types drive emission — or (c) a **per-instantiation
> concrete instance** of a hand-written runtime body. Polymorphism survives
> only *below* the emitted tree, inside backend/intrinsics realization, where a
> shared uniform body is an enumerated backend-interior contract with declared
> representation dependencies — no longer a typecheck-boundary licence class.

The honest residual, stated plainly rather than re-licensed: the shared Rust
body itself (e.g. `cranelisp-intrinsics::panic`'s `catch-runtime-error`) is
below the type system and remains one body serving many instantiations. That is
not a polymorphic callable at the boundary — the tree references a concrete
instance whose type is closed, and the aliasing of many instances onto one
uniform body is a backend realization choice (exactly the user's "calls to rust
closures which have the details of the type closed": the instance is where the
type closes; today's realization is a name-alias onto the uniform body, and
when layouts specialise the backend changes realization **per instance** with
zero tree change). The enumeration of such bodies, each with its declared
representation dependencies, survives as the **realization roster** — a
backend/bootstrap-interior pin, not an exception clause on any typecheck
invariant (this also discharges R-39 for the class).

### 1.2 Per-member disposition

Verified basis (re-read at source for this ruling): all four are
`DefKind::PrimitiveExtern`, slot-less, seeded in `src/bootstrap.rs` (`bind`
:894, `race` :951, `select` :959, `catch-runtime-error` :1152 — note the prior
ruling's `:925-943` span named the scheme construction, not the inserts);
`callable_got_slot()` answers `None` structurally
(`crates/cranelisp-types/src/module.rs:1445-1471` — `PrimitiveExtern` falls
through). `bind`/`race`/`select` have **no body anywhere** — the backend
intercepts them by name at the `BuiltinFn` apply arm and lowers IO-node
construction inline at the (concrete) call site; `catch-runtime-error` has one
C-ABI body in the intrinsics archive.

| Member | Disposition under I-EMIT |
|---|---|
| `bind`, `race`, `select` | **Re-kind to the inline model.** Their only "body" is already backend inline emission at concrete sites — the honest kind is `Primitive { body: Inline }` (or a bootstrap-seeded equivalent), the `vec-get` family's shape, which is concrete-per-use *by construction* and survives layout specialisation by construction. Value-position use rides the per-concrete-sig `__inlwrap` wrapper family, as for every inline primitive. Their quantified schemes survive as checking artefacts (schemes may quantify; that was never the problem — `total-concreteness.md` §3.4). After the re-kind, no polymorphic callable is referenced by any call to them. Wash home: int (bootstrap seed) + backend (the intercept arm is already the emission), S120/S121. MEASURE-RK: census of value-position uses of the three across the corpus before re-kind (expected ≈ 0; any hit needs its `__inlwrap` before the flip). |
| `catch-runtime-error` | **Per-instantiation concrete facade over one uniform body.** Typecheck emits each call as a concrete call to an instantiation-keyed instance (`build_mangled_name` — P-2, no second grammar); the backend realises every instance, today, as an alias onto the single hand-written body (a name-alias/import — zero new code per instance beyond the entry). The earlier `/arch` objection — "per-type wrapper symbols add names without adding soundness" (`total-concreteness.md` §3.3) — is **overruled in direction by the user**: the name is the point. The instance symbol is where the type is closed; when layouts specialise, realization changes per instance with no tree change and no archaeology. |

### 1.3 NC-R: survives mechanically, mutates in meaning — do not build it to I-ABI's rationale

`/qa`'s NC-R cell (`743126b5`, plan `tests/plan/s119-test-plan.md` §3.7) asserts
mechanically: *the `DefKind::PrimitiveExtern` entries with non-concrete schemes
are exactly {`bind`, `race`, `select`, `catch-runtime-error`}*. That assertion
is **still correct at HEAD and still worth pinning** — the silent-fifth-member
hazard is real today. What dies is the rationale ("the I-ABI roster of
sanctioned polymorphic callables") and the flip trajectory. Re-labelled:

- The cell pins the **backend uniform-realization roster** — the set of by-name
  hand-written bodies whose one compiled body serves multiple concrete
  call-site instantiations. A fifth member REDs until declared with its
  representation dependencies. Same mechanics, new meaning.
- Trajectory: `bind`/`race`/`select` **leave** the set at their inline re-kind
  (S120/S121 wash); `catch-runtime-error` remains as the uniform-realization
  pin (joined by `vec-len` only if 0932 chooses spelling (b) — see §6 R-20:
  this design records a preference for spelling (a) Inline, which keeps the
  roster minimal).

`/testing` may build the cell now with the amended rationale text; FIXME 0936
routes the re-label to `/qa`. It is **not** superseded and it is not a dead
spec — only its I-ABI framing is.

---

## 2. R-24 — resolved at source, and the register's narrowing was wrong

The register recorded R-24 OPEN: for `(deftype (Bx a) [:a v])` +
`(v (Bx 1024))`, `entry_is_monomorphisable_polymorphic` and
`local_parametric_call_triggers` both pass, yet no instance is minted; the
decline was narrowed to `callee_has_keyed_carrier` **or**
`resolve_terminal_fq_scoped`, unproven. This commission resolved it. **Neither
named suspect declines — both pass.** The decline is one step later, in the
collector→mint identity handoff:

1. `infer_var` records the bare accessor reference: not locally shadowed →
   `record_reference_target` (`crates/cranelisp-typecheck/src/infer.rs:415`,
   `checker.rs:1669-1751`) → `resolve_ref_target` → `scope_resolve`, which
   chain-follows the bare-alias `ModuleEntry::Import` (`v` →
   `{module, "Bx.v"}`, installed at `adt.rs:663-672`) to the terminal accessor
   `Def` and records **`VarRef::Global(storage_fq)`** (`checker.rs:1733-1737`).
   So `callee_has_keyed_carrier` (`program/support.rs:28-36`, TRUE for
   `Global`) **passes**.
2. `resolve_terminal_fq_scoped` (`checker.rs:2148-2155`) is the same
   `scope_resolve` walk — it **succeeds**, `home == current_module`, and the
   gate passes (the accessor entry is `UserFn`/`Concrete` over
   `type_vars: [a]` with `ast: Some` — `adt.rs:450-454`, `:621-639`).
3. The collector then pushes **`resolved.fq.symbol`**
   (`program/mono_collect.rs:592`) — the *reference* identity, which for a bare
   member alias is the **written spelling `v`**, not the storage key `Bx.v`
   (`cranelisp-types/src/resolve.rs:565-571`: `fq.symbol =
   canonical_symbol(written name)`; `storage_key` is the separate field).
4. `monomorphise_call` → `get_constrained_fn`, local arm
   (`traits/monomorphise.rs:1171`): a **raw**
   `probe_module_entry_owned(current_module, "v")` — no chain-follow — lands on
   the bare-alias `ModuleEntry::Import`, whose match accepts only
   `ModuleEntry::Def` (`monomorphise.rs:1173-1201`) → `None` →
   `monomorphise_call` returns `Ok(None)` (`monomorphise.rs:91-94`) → the
   driver's `if let Some(mono)` silently skips
   (`mono_collect.rs:347-367`). **Silent no-mint.**

This is the FIXME-0620 alias class — a storage identity composed from a written
spelling — reappearing inside the pass-4 collectors, one line below the very
comment that states the rule ("The name is a trigger, not the identity",
`mono_collect.rs:574-576`). The renamed-import shape (`(import [m [(orig
alias)]])`) declines identically in the imported collector (`:481` pushes the
alias; `get_constrained_fn`'s `Some(h)` arm probes the home for a key that
exists only in the consumer).

**Differential experiment (REPL at HEAD, `CRANELISP_CODEGEN_DUMP='*'`):**

- Control: `(defn iden [x] x)` + `(iden 5)` → `user/iden$Int` minted and
  compiled. The discovery chain works where written spelling == storage key.
- Bare: `(deftype (Bx a) [:a v])` + `(v (Bx 5))` → compiled functions are
  exactly `Bx`, `Bx.v`, `__expr` — **no instance**; the call dispatches through
  the polymorphic template's slot (the defect path).
- Dotted: `(Bx.v (Bx 5))` → **`user/Bx.v$user/Bx$Int` IS minted** (written
  spelling == storage key, so the raw probe hits).

**Second finding — the dotted-minted instance is UNSOUND.** Its CLIF carries
the `<1024`-guarded `atomic_rmw` on the loaded field word (load at `+24`,
`icmp ult v6, 1024`, RC-inc at `v6+8` when ≥1024), and `(Bx.v (Bx 1024))`
crashes the REPL. The generic mono path *can* produce an accessor instance, but
the synthetic-span body defeats the recheck's type annotation, so the instance
still emits residual-category RC. This **corrects R-23's stated mechanism**
("the body re-check cannot produce an instance" — it can; it produces a wrong
one) while **strengthening its conclusion**: accessors must not route through
the generic mono path; A-MINT (re-run the synthesiser at concrete args, with
real concrete node types on the instance view) is the only sound route.

**Does the types-first design depend on which condition declined?** It informed
two decisions. First, R-22's frame is confirmed by evidence: the
discovery-by-walk chain has at least two independent *silent* decline points
(the identity handoff; the `Ok(None)` contract), so specialisation must be
forced by construction — under §3's reshape a non-concrete template is
slot-less, and a missed mint becomes a **loud** missing-slot failure instead of
a silent dispatch through the template's slot (which is what made this defect
invisible: the template HAS a slot today, so the un-minted call "works").
Second, the S120 collection redesign keys identity on the **recorded carrier /
storage key** (`resolved.storage_key`, per the 0620 rule), never the written
spelling — FIXME 0935 records the defect and the fix shape for
`/design`(typecheck), and it bears on S119 W4's MEASURE-1b (§5).

---

## 3. The revised `cranelisp-types` design

Register share: R-1, R-2, R-3, R-5, R-6, R-7, R-8, R-11, R-16, R-29, R-31.
The thesis: land the vocabulary change first so every downstream violation is a
compile error, not a discipline.

### 3.1 D1 — `CallableSlot`: the witness-carrying slot

A new opaque newtype in `module.rs`:

```rust
/// A GOT slot index paired, at mint, with the concreteness check of the
/// scheme it serves. The field is PRIVATE: outside `cranelisp-types` a
/// `CallableSlot` value can only be obtained from
/// `SymbolTable::mint_callable_slot` (fresh, checked), `CallableSlot::rebind`
/// (reuse, re-checked), or deserialization (re-checked at the cache trust
/// boundary — R6). Constructing a slot-carrying kind variant therefore
/// REQUIRES having passed a concreteness check.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(transparent)]
pub struct CallableSlot(usize);

impl CallableSlot {
    pub fn index(&self) -> usize { self.0 }
    /// Checked slot REUSE (the Decision-31 REPL-redefinition carry-forward):
    /// transfers an existing slot to a new scheme iff the scheme is concrete.
    pub fn rebind(self, scheme: &Scheme) -> Result<CallableSlot, NotConcrete> { … }
}
```

The elegant property: **enum-variant fields need no privatisation**.
`UserFnState::Concrete { got_slot: CallableSlot, .. }` keeps a public field —
constructing the variant requires a `CallableSlot` *value*, and only the mint
produces one. The S119 hand-mint spelling (`allocate_got_slot()` then a
`Concrete { got_slot }` literal — `adt.rs:617-628`, `impl_check.rs:1039-1043`)
becomes a **compile error**.

### 3.2 D2 — the ONE fallible mint

```rust
pub enum SlotMintError { NotConcrete(NotConcrete), Exhausted(GotExhausted) }

impl<C: CodeStore, L: LinkerStore> SymbolTable<C, L> {
    /// The ONLY way to obtain a fresh CallableSlot. Checks
    /// `scheme.ty.is_concrete()` AND allocates from `next_got_slot` in one act.
    pub fn mint_callable_slot(&mut self, scheme: &Scheme)
        -> Result<CallableSlot, SlotMintError> { … }
}
```

`allocate_got_slot` demotes to `pub(crate)` (it becomes the mint's interior).
The **fifth slot writer** found during this commission —
`src/platform.rs:351` writes `table.next_got_slot =
platform.descriptors.len()` directly, bypassing allocation entirely (platform
slots are manifest indices) — is re-routed through a manifest-order mint loop
in the int wash; the register's four-carrier count (R-3) under-counted (§7).

**Honesty about the residual (R-38 tiering).** Rust cannot make the cross-field
pairing (entry `scheme` × kind slot) fully unconstructable while `ModuleEntry:
Clone` and serde exist: a slot can be cloned from one entry and stored beside a
different scheme, and serde bypasses every constructor. The design therefore
lands the full ladder, tier by tier: **tier 1** (unconstructable-by-accident:
fresh mints and rebinds are checked, the literal-construction spelling is a
compile error), **tier 3** (trust boundary: the cache-load loop re-checks every
restored slot-carrying entry — §3.6), **tier 5** (continuous measure: NC-1's
universal sweep is the standing falsifier for the scheme-swap residual). Each
grade is recorded on R11's register row when this lands.

### 3.3 D3/D4/D5 — every slot field retypes; the ctor slot becomes state-carried

- `UserFnState::Concrete { got_slot: usize, … }` → `{ got_slot: CallableSlot, … }`
  (`module.rs:2332-2345`).
- `DefKind::Constructor { got_slot: usize, … }` (`module.rs:1992-2048`) →

  ```rust
  Constructor {
      state: CtorState,   // NEW: replaces the mandatory got_slot field
      type_name: FQTypeName, tag: usize, field_count: usize,
      internal: bool, type_def: Option<Box<TypeDefInfo>>,
      mode_summary: Option<ModeSummary>,
  }
  pub enum CtorState {
      /// Declaration-side template of a generic ADT ctor: slot-less,
      /// excluded from codegen, a monomorphisation source. Keeps scheme,
      /// tag, field_count, type facet, pattern/display identity (R-8).
      Template,
      /// A concrete ctor (or minted ctor instance): slotted callable.
      Concrete { got_slot: CallableSlot },
  }
  ```

  Two-state sum, not `Option<CallableSlot>` — mirrors the S84 `UserFnState`
  precedent, keeps the *why* legible at every exhaustive matcher, and removes
  the mandatory-slot independence that made every generic ctor
  slotted-and-polymorphic (R-1/R-2/R-19). `IO.Bind` becomes `Template`
  (`src/bootstrap.rs:760-830` seed); `Tally` stays `Concrete`,
  byte-identical.
- `PrimitiveBody::Extern { got_slot, borrowed_sibling_slot }`
  (`module.rs:2220-2235`) → both fields retype (`CallableSlot`,
  `Option<CallableSlot>`); `DefKind::primitive(got_slot: usize)`
  (`module.rs:2191`) → takes `CallableSlot`.
- `DefKind::PlatformEffect.got_slot` (`module.rs:1884`) → `CallableSlot`;
  combined with the manifest-order mint (D2) this is the structural half of
  R-21 (the parse-side located refusal 0933 remains for diagnostic quality).
- `adt_build::AdtCtorSpec` carries `state: CtorState` (the builder stays PURE;
  callers mint). `build_adt_entries` — the ONE derivation (S110 R-2) — derives
  `Template` vs `Concrete` from the spec scheme's `is_concrete()` and refuses a
  mismatched pairing.

`callable_got_slot()` keeps its `Option<usize>` signature (reads
`slot.index()`), so the ~50 read sites across the workspace that already obey
the read-through discipline do not churn.

### 3.4 D6 — `defined_symbols()` admits no non-concrete scheme (R-31)

The one codegen-compilable filter (`module.rs:782-798`, Decision 22) gains the
predicate: `… AND entry.scheme.ty.is_concrete() AND state != CtorState::Template`.
One filter, one place; a projection, not a second store (the symbol table's
two roles — checking environment and codegen manifest — remain one structure,
per the S119 module-boundary corollary). This is what deletes the
compiled-but-uncalled generic-ctor template bodies (census A: 2,216 admissions)
and makes face 1's deletion site vanish (subsumption already recorded in
`total-concreteness.md` §3.1).

### 3.5 D7 — the substituting ctor-field projection (R-6/R-16)

Beside the model refusal site `ctor_field_concrete_types`
(`heap.rs:310-334` — preserved verbatim), add the instantiation-substituting
sibling pre-approved in shape by the 0929 disposition:

```rust
/// Field types of `ctor` at the concrete instantiation `args`, or a refusal.
/// Unifies the ctor scheme's result ADT params against `args`, applies the
/// substitution to the field types, and converts each via
/// `ConcreteType::from_type` — ONE residual field refuses the whole ctor
/// (the model-site spelling). Never fabricates.
pub fn ctor_field_types_at<C, L>(
    table: &SymbolTable<C, L>, ctor_key: &Symbol, args: &[ConcreteType],
) -> Result<Vec<ConcreteType>, NotConcrete>
```

Backend ctor-field materialisation for category/glue purposes delegates here —
never the hand-rolled `scheme.ty` walk whose fabricating arm is
`context.rs:280` (`unwrap_or(Type::Int)`, family B / R-13). The `CtorField`
carrier shape itself stays backend-interior (`CtorMeta` is `pub(crate)`) and is
`/design`(backend)'s inside the wash window, per the 0929 split — but with this
projection landed, `CtorField { ty: Type }` populated from a declaration has no
remaining legal producer (NC-5's structural leg).

### 3.6 D8 — serde, the cache trust boundary, and the schema window (R-29/R-30)

- `CallableSlot` is `#[serde(transparent)]` — the retype alone is
  byte-identical on the wire. The **`CtorState` sum is a serde shape change**,
  so the types change-set takes ONE `CACHE_SCHEMA_VERSION` bump, shared with
  the whole S120 window per FIXME 0931 item 4. This **answers register open
  item 4**: closing R-2 alone (the witness mint) needed no bump, exactly as
  argued — but the ctor tranche forces the window, and the two land together.
- **Load-boundary re-check (R-29):** serde bypasses every smart constructor,
  so the cache-load loop (`cache/serialize.rs::deserialise_meta_with_build_id`
  — already the ONE per-entry validation loop, with the
  `CacheStale::GotSlotOutOfRange` precedent) gains one arm: a restored
  entry with `callable_got_slot().is_some()` whose scheme fails
  `is_concrete()` ⇒ `CacheStale::NonConcreteSlot` ⇒ diagnosed recompile,
  never a panic on disk content. This is the durable warm-cache guard beyond
  the one-time schema window.

### 3.7 D9 — `ConcreteType` constructibility: sealing DECLINED, with reason (R-5)

Reaffirmed from the 0929 ruling (`f5d30808`, recorded on R18): the variants
stay `pub`. Exhaustive backend matching is a Principle-18 safety feature, and
legitimate known-Int literal construction exists; sealing would compel `_ =>`
arms that hide missed variants — a worse trade. The enforcement is NC-2's
two-family census (pinned allow-list, every entry citing an open defect, a new
site REDs in its own change-set, detection proof per 0768), and the residual
grade is **asserted-with-a-named-falsifier**. Note the census's pressure is
real: every fabrication site named by the register is in `unwrap_or` position,
which the census pattern covers.

### 3.8 D10 — the lenient view: staged retirement (R-7/R-11)

`lenient_from_expr`'s `unwrap_or(ConcreteType::Int)` (`mono_expr.rs:834-838`)
is the types-crate fabrication site (0913). Staged:

1. **S119 CS-3** (already ruled, ships as planned): the typecheck defaulting
   step replaces the fabricating default for the populations it owns, with the
   lenient-fallback census whose zero reading is the flip criterion.
2. **S120 ctor tranche**: generic ctor/accessor templates stop being codegen
   targets (D6), deleting the largest legitimate lenient population; A-MINT
   instances are built with **real concrete node types** (the instance
   synthesiser knows every type — the §2 experiment shows why a placeholder
   view emits unsound RC), so no instance ever reads the placeholder.
3. **End state (S121 target, census-gated):** `lenient_from_expr` DELETES;
   `MonoExpr::from_expr` is the sole view builder (`synthetic_local_from_expr`
   retires with it once synthesis stamps types). R-7's shape — every node
   `ConcreteType`, no variable case — is then the *only* representable body
   view. Templates remain representable as templates (R-8): scheme + `ast`
   persist and travel for cross-module mono; they simply have no view and no
   slot.

### 3.9 The proposed `public-api.txt` delta (enumerated; proposed, not made)

ADD: `CallableSlot` (+ `index`, `rebind`, std trait impls), `SlotMintError`,
`CtorState`, `SymbolTable::mint_callable_slot`, `heap::ctor_field_types_at`.
CHANGE: `UserFnState::Concrete.got_slot` retype; `DefKind::Constructor` field
set (`got_slot` → `state`); `PrimitiveBody::Extern` field retypes;
`DefKind::PlatformEffect.got_slot` retype; `DefKind::primitive` signature.
REMOVE: `SymbolTable::allocate_got_slot` from the public surface
(`pub(crate)`). LATER (census-gated, §3.8): `MonoExpr::lenient_from_expr`,
`MonoExpr::synthetic_local_from_expr` removals.
Unchanged (deliberately): `callable_got_slot()`, `is_callable_target()`,
`defined_symbols()` signatures; `Resolved`; the whole resolution surface.

---

## 4. The wash plan

Types lands first; every downstream crate then fails to compile at exactly its
violation sites. Order per the register (dependency order), sizes from a
source census at HEAD (`got_slot` token mentions, non-test/non-comment:
typecheck 52, backend 46, src 111, types 26, primitives 2, platform 5).

| # | Crate | What breaks / what is built | Size |
|---|---|---|---|
| 1 | **cranelisp-types** | §3 in one change-set + rustdoc + `public-api.txt` + unit rows (mint refusal both polarities; rebind; `CtorState` serde; `ctor_field_types_at` incl. the refusal leg). Schema bump rides. | 1 change-set, ~large |
| 2 | **cranelisp-typecheck** | Every fresh-slot site must mint with the scheme in hand — 10 non-test `allocate_got_slot` callers (`adt.rs` ×2, `builtins.rs` ×3, `program/body.rs` ×2, `finalize.rs` ×2, `register/multi_sig.rs` ×2, `register.rs`, `result.rs` ×2, `impl_check.rs`, `monomorphise.rs`) become `mint_callable_slot` calls; **P-1 stops being a discipline and becomes the vocabulary**. The two hand-mints (F1 `adt.rs:617-628`, F2 `impl_check.rs:1039-1043`) cannot compile over non-concrete schemes — forced into A-MINT / `Template` / `Polymorphic` routes (the S119 CS-1/CS-2 designs apply unchanged). `register_type_def_with_ctor_infos` derives `CtorState` per ctor. Collection redesign: identity from `resolved.storage_key` / the recorded carrier, never `fq.symbol` (FIXME 0935; fixes §2's silent no-mint incl. the renamed-import sibling); F2 trigger over `ApplyRef::Dispatch` per producer-obligations §2.4. Fixture churn (`builtins.rs`, `test_support`). | ~2 change-sets, largest crate share |
| 3 | **cranelisp-backend** | Cache: schema-bump consts + the `CacheStale::NonConcreteSlot` arm + `CtorState` deserialisation arm. `context.rs::extract_constructor` (:260-287) rewrites onto `ctor_field_types_at` — deletes the `unwrap_or(Type::Int)` launder (R-13) and the declaration-channel feed (NC-5 structural leg). `drop_glue.rs:398` → located refusal (R-12); `fn_compiler.rs:1287` → located error, census-gated arm flip (R-9/R17); `fn_compiler.rs:1214` respelled `expect` (R-14). Ctor-template compile arm has no traffic (D6) — face 1's site vanishes. `Constructor { .. }` destructure sites (~15 non-test) re-pattern on `state`. Golden-CLIF re-baselines expected and accepted (REDs unconstrained). | ~2 change-sets |
| 4 | **cranelisp-primitives + intrinsics** | Static table mints (2 sites); **`vec-len` de-slot** per 0932 — preference recorded for spelling (a) `Inline` (element-independent length-word load; keeps the realization roster minimal); `__inlwrap` already covers value position. Intrinsics: no slot surface; `catch-runtime-error` realization contract recorded (§1.2). | small |
| 5 | **src/ (int)** | The large facade change the user accepted: 111 `got_slot` mentions. `bootstrap.rs` — generic ctor seeds (`Option`/`Result`/`Pair`/`SList`/`IO` incl. `Bind`) become `CtorState::Template`; `bind`/`race`/`select` re-kind (§1.2). `platform.rs` — manifest-order mint replaces the `:351` direct cursor write; 0933's located refusal. `save.rs` (7 `Concrete` constructions), `exe.rs`, `redefine.rs` (slot reuse → `rebind`), `worker.rs` (snapshot/cursor logic reads survive; entry construction mints), `macro_clause.rs`, `expander.rs`, `agent/*`, `code.rs`. REPL `__expr` path unchanged (concrete by construction). | ~2–3 change-sets |
| 6 | **tests/** | NC-1 populations (b)/(c) flip GREEN as tranches land; NC-4 flips at A-MINT; NC-5 behavioural leg flips at the context.rs rewrite; NC-R re-labelled (0936); unit-fixture churn tracked per crate above. | with each wave |

Two structural payoffs worth naming: (i) after step 2, a missed instance is a
**loud** missing-slot failure — the silent-fallback-to-template class (§2) is
unrepresentable because the template has no slot to fall back through; (ii)
after step 3, no backend type source remains that a declaration can feed —
body views are concrete by construction, ctor metadata is
instantiation-substituted or refused.

---

## 5. Sprint impact

**S119 ships as planned.** Phase 5 stage 1 (W1, `/testing`) is undispatched and
proceeds unchanged — with ONE brief amendment: NC-R is authored to the §1.3
rationale, not the I-ABI rationale (FIXME 0936). The types change-set (§3) is
**S120 scope**, per the user's own sequencing ("fix cranelisp-types first,
then wash") and the standing must-not-interleave rules; S119's waves do not
build against it.

Landed-obligation review — nothing landed is *actively wrong*; three artefacts
needed amendment and are amended in this change-set or routed:

1. `total-concreteness.md` §2 I-ABI + §3.3 — superseded by §1 here (amended in
   place with a supersession box).
2. BC §7 + `safety-invariants.md` R11 — their I-ABI sentences re-pointed.
3. The register itself — two recorded claims falsified (§7; `/sprint` edits).

Forward-compatibility of the S119 W4 typecheck wave, stated explicitly so
`/dev` is not whipsawed: CS-1's one typecheck-internal mint helper is the
**S119 spelling of the same gate** the S120 types mint makes structural; when
§3 lands, the helper's body becomes a call to `mint_callable_slot` and nothing
above it changes. CS-2 (A-MINT + F2 trigger) is confirmed by §2's experiment —
and **MEASURE-1b's question is now answered before it is run**: the F1 half is
NOT a successor-discovery widening only; the discovery chain declines bare
accessor calls at the identity handoff (0935) and the generic path's instance
is unsound even when reached (dotted). W4's brief should carry both facts.
Face 1, face 4, the 0923 split, tranche A, L-1..3: unaffected.

---

## 6. The 40-row cross-check

Dispositions: **A** = addressed (with the mechanism), **D** = declined with
recorded reason, **F** = deferred with named target.

| Row | Disp. | How |
|---|---|---|
| R-1 | A | `CallableSlot` witness (§3.1) + `CtorState` (§3.3) + D6. Residual (Clone/serde scheme-swap) tiered honestly: tier-1 by-accident-unconstructable, tier-3 cache re-check, tier-5 NC-1 (§3.2). |
| R-2 | A | The slot value itself carries the check — the ⟺ stops being two independent fields; the ctor's mandatory-slot independence is deleted by the state sum. |
| R-3 | A | ONE carrier type + ONE fallible mint (§3.2); `allocate_got_slot` demoted; **fifth writer found and re-routed** (`src/platform.rs:351` direct `next_got_slot` write — register under-counted, §7). |
| R-4 | A | `scheme::mono` over a residual type becomes uncompilable as a mint input (F2 scheme-truth, S119 CS-1; structural at §3). |
| R-5 | D | Sealing declined, reason recorded (§3.7): exhaustive matches + legitimate literals are load-bearing; NC-2 is the enforcement; residual = asserted-with-a-named-falsifier. |
| R-6 | A | `ctor_field_types_at` (§3.5), the only legal derivation; `CtorField` carrier retype is `/design`(backend)'s inside the wash window (0929 split — named target). |
| R-7 | A | Strict `from_expr` propagated; instance views carry real types (the §2 experiment is the why); lenient retirement staged §3.8. |
| R-8 | A | `CtorState::Template` keeps the full declaration payload; `Polymorphic`/`Constrained` untouched; templates serialise and travel for cross-module mono. |
| R-9 | A(F) | Backend wash step 3: located error + census-gated arm flip (R17). Target: S119 W2 / S120 backend. |
| R-10 | F | P25 check or proof owed by `/dev`(typecheck) per the R18 row grading; NC-3(b) is the instrument. Target: S119 W4 / S120 typecheck wash. |
| R-11 | A | Staged §3.8: CS-3 defaulting (S119) → population deletion (S120) → lenient deletion (S121, census-gated). |
| R-12 | A(F) | Located refusal per the `:497-505` pattern; NC-3(d). Target: backend wash. |
| R-13 | A | Deleted by the R-6 delegation — the hand-rolled walk retires (NC-5 structural leg). |
| R-14 | A(F) | Respell `expect`/`filter_map`; low severity; rides the backend wash. |
| R-15 | F | Grading owed by `/design`(int) — 0929 site 5; S120 int wash. Not assumed benign. |
| R-16 | A | Model sites preserved verbatim; the substituting sibling lands BESIDE `ctor_field_concrete_types` with the same one-residual-refuses-all spelling (§3.5). |
| R-17 | A | The mint spelling is a compile error post-§3; A-MINT (S119 CS-2) is the concrete route; the `:592` "intentional" doc is deleted with the mint. |
| R-18 | A | Scheme-truth + `Polymorphic` routing (S119 CS-1/CS-2); the `scheme::mono` launder cannot reach a mint post-§3. |
| R-19 | A | `CtorState` — the mandatory ungated slot is deleted (S120, 0931). |
| R-20 | A | `vec-len` de-slots per 0932; preference recorded: spelling (a) `Inline` (§4 step 4), keeping the realization roster at {`catch-runtime-error`}. |
| R-21 | A | Twice: 0933 parse-side located refusal + structural (a `PlatformEffect` slot requires a mint over a concrete scheme, §3.3). |
| R-22 | A | Direction confirmed by R-24's evidence: post-reshape a missed mint is LOUD (no template slot to fall silently through); collection keys on carriers/storage identity (0935); the full demand-driven-by-construction design is 0931's S120 deliverable. |
| R-23 | A* | A-MINT stands; the register's *mechanism* claim is corrected by experiment (§2, §7): the generic path CAN mint — an UNSOUND instance — which is a stronger reason, not a weaker one. |
| R-24 | **RESOLVED** | §2. Neither named suspect; the decline is the collector→mint identity handoff (`mono_collect.rs:592` written spelling vs `monomorphise.rs:1171` raw storage probe over the bare-alias `Import`). Verified statically + differential experiment. Fix shape in FIXME 0935. |
| R-25 | A | I-EMIT (§1.1) + per-member dispositions (§1.2): `bind`/`race`/`select` inline-model; `catch-runtime-error` per-instantiation concrete facade. |
| R-26 | A(F) | Node-level: already structural (`MonoExpr`). Dispatch-level: no polymorphic callable can be a dispatch target post-wash (templates slot-less + excluded; by-name poly kinds re-kinded/facaded). Any residual dispatch-sum tightening is 0931/S120's to spell. |
| R-27 | A | Realization is backend-interior by ruling; the roster becomes the backend realization contract (§1.1–§1.3). |
| R-28 | A | End state: zero slotted-and-polymorphic, no kind partition, one predicate (NC-1 universal). |
| R-29 | A | `CacheStale::NonConcreteSlot` arm in the ONE validation loop (§3.6), `GotSlotOutOfRange` precedent. |
| R-30 | A | Answered (§3.6): the witness mint alone needed no bump — confirmed — but `CtorState` forces the window; both share the ONE S120 bump (0931 item 4). |
| R-31 | A | D6: `defined_symbols()` gains the `is_concrete()` conjunct — a projection, not a split store. |
| R-32 | A | Confirmed a representation concern: the 0934 payload-glue word stamped at the concrete construction site (closure `DROP_GLUE_PTR` precedent); under I-EMIT/I-FRAME every construction site is concrete, so the stamp is always mintable. Not a type-system residual. |
| R-33 | A | NC-1 stands as re-ruled (0930 resolved by `/qa`, `743126b5`); populations flip per tranche; `_no_unattributed_violations` is the durable sweep. |
| R-34 | A | NC-2 families A+B unchanged; §3.7 reaffirms census-as-enforcement. |
| R-35 | A | NC-5 both legs: behavioural (concrete-or-refuse at `ctor_meta_at`) + structural (the hand-rolled walk retires at the §3.5 delegation). |
| R-36 | A | R17's arm-flip becomes reachable at the S120 tranche: templates stop compiling (D6) and the declaration channel closes (§3.5) — the census can read zero. |
| R-37 | A | Detection proofs per 0768 are already mandated in the plan rows (NC-1/NC-2/NC-R); each §3 unit row carries both polarities. |
| R-38 | A | Every invariant in this design states its tier explicitly (§3.2's ladder is the worked example); no "graded by inspection" claim is made anywhere in it. |
| R-39 | A | I-EMIT has no exception clause; the ex-roster is a backend contract, not an invariant exception; both representation-contingent licences (ctor I-CT′, vec-len) are eliminated, not partitioned. |
| R-40 | A | Verification statement at top; every claim cited file:line; two register errors found by going to source and returned in §7 rather than designed over. |

---

## 7. Register corrections (returned to `/sprint`; not edited in place)

1. **R-24's narrowing is falsified.** "I narrowed the decline to
   `callee_has_keyed_carrier` or `resolve_terminal_fq_scoped`" — both pass
   (verified statically at `checker.rs:1733-1737` / `:2148-2155` and
   confirmed by the §2 differential). The decline is `mono_collect.rs:592`
   (written-spelling identity) × `monomorphise.rs:1171-1201` (raw storage
   probe rejecting the alias `Import`). Suggested row text: point at the
   handoff pair and cite FIXME 0935.
2. **R-23's mechanism claim is wrong in one clause.** "the body re-check
   cannot produce an instance" — it can (dotted spelling mints
   `user/Bx.v$user/Bx$Int` at HEAD); the instance is **unsound** (guarded RC
   on the residual field word; `(Bx.v (Bx 1024))` crashes). The conclusion
   (A-MINT; never route accessors through the generic mono path) is
   *strengthened*.
3. **R-3's carrier census is one short.** A fifth slot-state writer exists:
   `src/platform.rs:351` assigns `next_got_slot` directly (manifest-index
   convention), bypassing `allocate_got_slot`. It is absorbed by §3.2's mint
   demotion + the int-wash manifest-order mint.
4. Editorial: the register's Consequence box says NC-R "should not be built
   until settled" — settled here as §1.3 (mutates, buildable now with the
   amended rationale; FIXME 0936).

## Next skills

- `/sprint` — absorb §7 into the register; carry §5's W4 brief amendments
  (MEASURE-1b pre-answered; NC-R rationale) into the Phase-5 dispatches;
  schedule the §3 types change-set as the S120 opener.
- `/design`(typecheck) — 0931 (ctor tranche) + 0935 (collector identity) over
  this document's §2–§4.
- `/design`(backend + runtime pair) — 0932 with the §4 step-4 preference;
  the `CtorField` carrier ruling inside the wash window (0929).
- `/qa` — 0936 (NC-R re-label); NC-1 population trajectory per §4.
