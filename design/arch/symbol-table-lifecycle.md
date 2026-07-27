# The symbol table, clean sheet — lifecycle-legible design commission

**Status:** WORKING DESIGN (`/arch`, S119, 2026-07-27) — user-commissioned
clean-sheet exercise: *disregard legacy; sketch the optimal symbol table
structure that enables parsing to transition through typechecking and
monomorphisation with GOT assignment, across poly/mono multi-sig defs,
poly/mono trait impls, poly/mono primitives and platform effects.* **The
S119/S120 flip stays HELD while this is before the user.** Decides nothing on
its own; §9 states the migration recommendation for the user to dispose of.

**Relationship to prior rulings:** `concreteness-types-first.md` §3.10–§3.11
are the incumbent rulings this commission re-opens under two user corrections
(absorbed in §1). Where this document converges with a prior ruling, the
conclusion is re-derived here from the requirements, not carried by citation;
where it diverges, the divergence is named (§1, §8, §9). Nothing in this
document is in force until the user rules.

**Verification statement.** Every factual claim about source was read at HEAD
during this commission and is cited `file:line`; claims inherited from prior
documents were re-verified where load-bearing (the staging-GOT, commit-gate,
mono-registration, impl-check, and platform-loader citations were all
re-read).

**Archive trigger:** the user disposes of §9; either the design lands (fold
into `module.rs` rustdoc + BC §7 + `interfaces.md`, then archive) or it is
declined and the file records why beside the ruling that supersedes it.

---

## 1. The two corrections, absorbed first

### 1.1 Infill-by-scan, re-evaluated against the right artefact

The §3.11 ruling-5 refutation argued from the **slab**: a null GOT pointer is
ambiguous between never-allocated and allocated-awaiting-population
(`got.rs:10-14` — workers write pre-assigned disjoint slots after allocation).
That refutation was correct about the slab and irrelevant to the proposal. The
user's model scans the **symbol table entries** for claimed slots: an entry in
a slot-carrying state claims its index whether or not the pointer is written
yet, so "allocated awaiting population" is claimed and the ambiguity does not
arise. **Conceded.**

What survives of the old argument, restated precisely: the scan's free set is
"claimed by no entry", but the safety condition for reuse is "**published** to
no caller" (Principle 22 — compiled callers and heap closures embed the raw
index; there is no un-publish event). The two sets differ exactly when an
entry **stops claiming a slot that callers still embed**. Is that reachable?
Yes — verified transitions, not hypotheticals:

1. **Concrete→template redefinition** (a fn redefined generic): the new entry
   is slot-less; the old slot is frozen with a trap pointer by the commit
   gate (`worker.rs:811-827` doc — "allocating a fresh live slot and freezing
   the old one"; `redefine.rs:399-418`). Post-freeze, no entry claims the
   slot. A scan would re-issue it to a *different* symbol, and stale closures
   would then call the wrong function — silently, which is worse than the
   trap they get today.
2. **`AbiChanging` redefinition** generally: fresh live slot, old slot frozen
   — same shape; today the freeze record lives int-side in the session
   retention pool (`redefine.rs:363` `mark_broken`;
   `design/int/session-transaction.md` §6–§7), invisible to any table scan.

So: **removal-with-live-callers is NOT impossible by construction, and the
scan model therefore needs a tombstone.** D11's
`NotDetermined { prior_slot }` is a tombstone for exactly one window — the
Pass-1→determination interstage — and expires at determination: if the
determination is "template", the slot leaves the entry and today leaves the
table's knowledge entirely. The durable answer is a **table-side retired-slot
record** (§4.3): every de-claiming transition is a *move* of the slot into it
(P22's "displacement is a move into the retention structure", applied to the
index itself, not just the `Code` Arc). With that record, claimed ∪ retired
IS the published set, the scan model is sound, and two stored artefacts
become derivable and delete: the `next_got_slot` cursor (`module.rs:146`) and
the platform loader's direct cursor write (`platform.rs:351`). Whether
allocation then infills gaps or takes max+1 becomes a policy detail with no
correctness content — the correctness lives in the claims-∪-tombstones
authority, which is re-derived from the table at every load. This is the
commission's "re-derived rather than inherited", and it is adopted (§4.3).

### 1.2 Churn discounted — the ModuleEntry-split decline, re-weighed

The §3.11 ruling-3 decline rested on two legs: resolution-vocabulary
coherence and churn. The user strikes the churn leg for the primary data
structure. Re-weighed on the coherence leg alone: the argument that survives
is **narrower than the decline it supported**. What is true (verified:
`module.rs:1722-1733` uniform visibility; `src/imports.rs:881-883` §8.6.4
"local definition" one-arm match; chain-follow terminal = non-`Import`) is
that resolution distinguishes only *terminal-definition vs alias vs
ambiguous, times visibility* — it never inspects `DefKind`. That is an
argument for keeping the resolution vocabulary SMALL and OUTERMOST; it was
never an argument for keeping today's **eight-variant flat enum**, which
mixes the three resolution states with five facet records (`TypeDef`,
`IntrinsicType`, `TraitDecl`, `TraitImpl`, `SpecialForm`) that resolution
treats identically. With churn discounted, the coherent conclusion is the
**three-arm outer layer with facets nested one level down** (§3) — the split
*in the opposite direction* from the one declined: fewer top-level variants,
not more. The kind×field dead-pairing debt conceded in ruling 3
(`Primitive`×`codegen_view`, `PlatformEffect`×`ast`/`code`,
`PrimitiveExtern`×`code`, `Macro`-parent×`codegen_view` —
`module.rs:1201-1358` fields × `module.rs:2148+` kinds) is cured here by the
lifecycle collapse (§4.2): the payloads move onto the states that use them.

---

## 2. Actors and functions (P21), and the axes they pull on

One record per name; these actors read/write it over its life:

| Actor | Function against the record |
|---|---|
| Parse/expand (frontend) | names the entity, fixes its syntactic role (defn / deftype / deftrait / defmacro / import / export) |
| Registration (typecheck pass 1) | creates the binding; provisional signature; redefinition displacement |
| Body check + generalisation (pass 2/3) | **settles** the scheme (P26 settlement point); determines concreteness class |
| Monomorphisation (pass 4) | demands instances from templates at concrete instantiations |
| GOT assignment | mints the callable slot for concrete callables; accepts manifest indices for platform effects |
| Codegen (backend) | consumes view + slot; writes the pointer into the slab |
| Session (int) | redefinition commit gate, freeze/retire, broken-marking, cache save/restore |
| Resolution (every stage) | name → binding; visibility; chain-follow; ambiguity; §8.6.4 |
| REPL introspection | read-only projections |

These pull on five distinguishable axes of the one record:

- **A. Binding axis** — terminal definition / alias / ambiguous (+ visibility).
  The only axis resolution reads.
- **B. Facet axis** — value-callable / type / trait / impl-record /
  special-form. What checking consumers dispatch on.
- **C. Origin axis** — who authored the body and what identity metadata it
  carries: plain defn, multi-sig clause, trait-impl method, minted instance,
  synthesised ctor/accessor, macro clause, Rust primitive, platform fn.
  Fixed at birth.
- **D. Lifecycle axis** — declared → settled(template | concrete) → slotted →
  compiled → retired/broken. The axis the commission wants legible; the axis
  every S82→S119 defect lived on.
- **E. Payloads** — scheme, body AST, view, slot, code, callees, summaries —
  each valid only in specific lifecycle states.

Today's structure nests these as A+B merged (flat `ModuleEntry`,
`module.rs:1192`), C+D merged per-kind (`DefKind` with `UserFnState` /
`CtorState` / `PrimitiveBody` / raw platform slot as four *different* partial
state vocabularies), and E flat on `Def` regardless of state (eleven fields,
several meaningless per kind/state). The clean sheet separates all five.

---

## 3. The outer layer — resolution's vocabulary, and nothing else

```rust
pub struct SymbolTable<C, L> {
    pub path: ModuleFullPath,
    symbols: HashMap<Symbol, Binding<C>>,      // PRIVATE — writes funnel (§4.4)
    retired_slots: Vec<RetiredSlot>,           // serde-visible tombstones (§4.3)
    got: Arc<GotTable>,                        // runtime slab, serde-skip — unchanged role
    // imports/exports/platforms/submodules (structural decls),
    // written_trait_impls, module_preamble, schema_version: unchanged
    // next_got_slot: DELETED — derived (§4.3)
    // next_seq: retained (authorship order allocator)
}

pub struct Binding<C> {
    pub visibility: Visibility,
    pub body: BindingBody<C>,
}

pub enum BindingBody<C> {
    /// Import/re-export edge — visibility discriminates the two, as today
    /// (`module.rs:1389-1408`). Chain-follow's non-terminal.
    Alias { source: FQSymbol },
    /// Collision sentinel, as today (`module.rs:1617`).
    Ambiguous,
    /// A terminal definition in this module — ANY facet.
    Decl(Decl<C>),
}

pub enum Decl<C> {
    Callable(Callable<C>),                     // the value namespace (§4)
    Group(Group),                              // overload base / macro parent (§5.4)
    Type(TypeRecord),                          // sum/enum TypeDef | IntrinsicType
    Trait(TraitRecord),
    ImplShell { trait_name: FQTraitName, impl_type: FQTypeName,
                impl_module: ModuleFullPath, methods: Vec<Symbol> },
    SpecialForm(SpecialFormRecord),            // root "" module only
}
```

**Q5 answered.** Resolution keeps the outermost discriminator — but the
discriminator shrinks to the three states resolution actually distinguishes.
Every resolution-surface consumer (visibility filter, §8.6.4 classification,
chain-follow terminal test, ambiguity handling) matches `BindingBody`'s three
arms and never sees a facet; "the six `DefKind` members are indistinguishable
to resolution" is thereby made **structural** rather than observed — a
resolver takes `&Binding` and cannot dispatch on what it cannot see without
explicitly projecting into `Decl`. The one resolution question that does
consult the callable layer — the precedence stop-condition "is this a
dispatchable call target" (today `is_callable_target()`,
`module.rs:1845-1854`) — remains ONE exported predicate over `Decl`, consumed
by the resolver as a function, not a re-pattern. Resolution is thus a
*projection* in the honest sense: its vocabulary is the store's outer shape
because every stage resolves; the store's depth is invisible to it.

Docstrings, `seq`, `param_names` live inside the `Decl` records that carry
them today (an `Alias` keeps no seq; a documented re-export, if ever wanted,
is a spec question — not silently representable here).

---

## 4. The callable layer — ONE lifecycle machine

### 4.1 The record

```rust
pub struct Callable<C> {
    /// The authoritative scheme: provisional in `Declared`, settled after.
    /// Schemes may quantify — that was never the problem
    /// (`total-concreteness.md` §3.4); concreteness is read from `scheme.ty`.
    pub scheme: Scheme,
    pub param_names: Vec<Symbol>,
    pub docstring: Option<String>,
    pub seq: u64,
    /// Identity/metadata axis — fixed at birth, never state-dependent (§4.5).
    pub origin: CallableOrigin,
    /// Lifecycle axis — the state machine (§4.2).
    pub life: Life<C>,
}
```

### 4.2 The state machine (Q1)

```rust
pub enum Life<C> {
    /// Pass-1 interstage: signature registered, body not settled. Nothing may
    /// call it. `prior` is D11 GENERALISED: the redefinition displacement
    /// moved the previous entry's slot here (a claim AND a tombstone for the
    /// interstage window); the determination point rebinds or retires it.
    Declared { prior: Option<CallableSlot> },

    /// Settled NON-concrete: a monomorphisation source. Slot-less, view-less,
    /// never callable, excluded from codegen by construction (no field for
    /// either capability). Serialises and travels for cross-module mono.
    Template {
        body: TemplateBody,        // Ast(DefnVariant) | Synth(SynthSpec)
                                   // | UniformRust { abi_name: LinkerSymbol }
        kind: TemplateKind,        // Constrained(Box<ConstrainedMeta>) | Parametric
        callees: Vec<FQSymbol>,
    },

    /// Settled concrete: THE slotted state. Constructed only by the
    /// settlement funnel (§4.4), which checks concreteness, builds the view,
    /// and mints/rebinds the slot in ONE act.
    Concrete {
        slot: CallableSlot,
        realization: Realization<C>,   // §4.6 — names the slot's populator
        minted_from: Option<InstanceLink>,   // §5.2 — template back-link
        ast: Option<DefnVariant>,      // regen/introspection source
        callees: Vec<FQSymbol>,
        value_use: bool,
        mode_summary: Option<ModeSummary>,
    },

    /// Settled concrete, dispatched WITHOUT a slot — the two by-name classes.
    /// `Inline`: the only body is backend inline lowering at concrete sites
    /// (today's `PrimitiveBody::Inline`, `module.rs:2598-2603`); value
    /// position rides minted `__inlwrap` instances (ordinary `Concrete`
    /// entries with `minted_from` links). `HostPromised`: by-name
    /// `Linkage::Import` against the key (today's `DefKind::PrimitiveExtern`,
    /// `module.rs:2291`).
    Inline,
    HostPromised,

    /// Recompile-failed under the session transaction: slot RETAINED and
    /// trap-stubbed, no valid body. Makes "slot alive, view gone"
    /// representable exactly once, with provenance — and keeps the slot
    /// CLAIMED for the §4.3 scan. (Today this state lives int-side in
    /// `redefine.rs::mark_broken` + the retention pool; the entry itself
    /// does not say it is broken.)
    Broken { slot: CallableSlot, error: BrokenProvenance },
}
```

Transitions (each a funnel method, §4.4):

```
declare ──────────────► Declared{prior: moved from displaced entry}
Declared ─settle_tmpl─► Template        (prior slot → retired_slots: the tombstone move)
Declared ─settle_conc─► Concrete        (slot = rebind(prior) | mint; view built HERE)
Template ─(demand)────► new entry: Concrete{minted_from}   (§5.2 — a birth, not a transition)
Concrete ─redeclare───► Declared{prior: Some(slot)}        (REPL redefinition)
Concrete ─mark_broken─► Broken{slot}                       (slot retained + trap)
Concrete ─commit gate─► AbiChanging: fresh live mint; old slot → retired_slots
births: install_extern / install_platform / install_inline / install_host_promised
        (primitives + platform: born settled, §5.5–§5.6 — no Declared interstage)
```

**One machine, not four.** Today's four partial vocabularies
(`UserFnState` `module.rs:2688`, `CtorState` `module.rs:838` dormant,
`PrimitiveBody` `module.rs:2578`, `PlatformEffect`'s raw mandatory slot
`module.rs:2246`) each solved a slice of the same problem, and every
population that arrived AFTER a vocabulary was designed grew a bespoke
bridge: the trait-impl `scheme::mono` launder (`impl_check.rs:1043`), the
mono-pass fabrication + hand-alloc (`monomorphise.rs:667`, `:680-688`), the
ctor hand-mints (`adt.rs:617-628`), the platform cursor write
(`platform.rs:351`). The uniformity IS the fix: every population settles
through the same funnel, so there is no seam left at which a fifth hand-mint
can grow. This is deliberately NOT maximal P20 — a per-origin state enum
would make e.g. `Declared × Ctor` unrepresentable — and §7 carries the honest
tier for that residual: origin×state legality is a single enumerated table
checked at the funnels and at the load boundary (the dead cells are all of
the "never constructed" polarity, not the dangerous
"constructed-and-misread" polarity that motivated P20's worked examples).

**D11 disposition: generalised, not replaced.** `Declared { prior }` is
D11's `NotDetermined { prior_slot }` with the same semantics (not a callable
capability; `callable_got_slot()` answers `None`), now serving every checked
population instead of `UserFn` alone. `redef_slots` and the
`existing_callable_slot` `or_else` delete exactly as the D11 ruling
specified.

### 4.3 Slot identity, re-derived (Q2 + correction 1.1)

Derive from the constraints that actually bind:

- The **index** must persist (cached `.o` relocations embed it) and the
  **pointer** must not (session state) → index serde-visible on entries,
  slab runtime-only. *(Forced by the cache contract.)*
- Slot ⇒ concrete; the determinant is the entry's settled scheme → the slot
  lives on the entry's `Concrete` state, beside its determinant. *(Re-derived
  — not by citing `GotTable`'s Clone-as-fresh, which a clean sheet could
  change, but because persisting a symbol→slot map beside slot-carrying
  entries would be a second serialised home for one binding (P7), and
  persisting it INSTEAD of entry-carried slots would split the capability
  from its determinant and re-open the S83-closed pairing. The slab stays a
  pure pointer array; nothing needs it to carry bindings.)*
- Published indices have no un-publish event (P22) → de-claiming transitions
  move the index into a table-side record:

```rust
pub struct RetiredSlot {
    pub slot: CallableSlot,
    pub reason: RetireReason,   // TemplateFlip{symbol} | AbiChanging{symbol} | ...
}
```

- **Allocation authority = claims ∪ tombstones, re-derived at construction.**
  Claims = slots on `Concrete`/`Broken`/foreign states ∪ `Declared.prior` ∪
  `retired_slots`. The mint computes against that set (in practice: derive a
  cursor/free-set once at table construction or cache load, maintain it
  in-memory; the *authority* is the scan, and the load boundary re-runs it as
  a uniqueness + `slot ⇒ is_concrete()` validation — the `CacheStale`
  precedent). Consequences: `next_got_slot` (`module.rs:146`) **deletes**
  (it was a stored cache of a derivable fact — P7); the platform loader's
  direct cursor write (`platform.rs:351`) **deletes** (manifest claims are
  ordinary claims, and a host allocation into a platform module cannot
  collide with them by derivation); infill of never-claimed gaps is *sound*
  under the tombstone rule, and whether to use it is policy, not
  correctness. The `__expr`/`__macro_*` churn case stays same-symbol
  rebind carry-forward, unchanged.
- The commit gate (`worker.rs:811-827`) remains the single live-slot policy
  authority for redefinition classes *(forced by staging/commit concurrency:
  staged tables are parallel worlds whose slots are re-pointed at commit)* —
  its freeze half now lands in `retired_slots` (table-side index tombstone)
  paired with the int-side retention pool (the `Code`/pages half; two halves
  of the one P22 owner, index vs pages, each at the layer that owns it).

`CallableSlot` (the witness, `module.rs:752`) survives unchanged as the
mint's return and the state fields' type; `mint`/`rebind` survive as the
funnel's interior.

### 4.4 The funnels — the table becomes an ADT

`symbols` goes **private** (today `pub`, `module.rs:142`). All state
transitions flow through table methods that enforce the two move invariants:

1. **Slot conservation**: replacing/redefining an entry in a slot-carrying
   state moves the slot — into `Declared.prior` (redefinition) or
   `retired_slots` (template flip, AbiChanging freeze) — never drops it.
2. **Settlement atomicity**: `Concrete` is constructed only by
   `settle_concrete(name, scheme, view, …)`, which checks
   `is_concrete()`, builds/accepts the view, and rebind-or-mints in one act.
   This unifies the two producer orders that coexist today (single-sig
   slot-then-view `program/body.rs:293-298→:366-379`; mono view-then-slot
   `monomorphise.rs:655-694`) — the question `concreteness-types-first.md`
   §3.11 ruling 3 named for the successor commission is answered by making
   the order a non-question: both inputs are parameters of one constructor.

Reads stay free (`get`, iterators, projections). Honesty (§7): Rust cannot
make dropping a `Copy` slot a compile error; the funnel is the
accessor-enforced tier for invariant 1, with the load-boundary uniqueness
scan as its standing seam check (P25 tier 3). Invariant 2 IS
representation-tier: outside the crate there is no other way to obtain the
state.

### 4.5 Origins — identity metadata, orthogonal to state

```rust
pub enum CallableOrigin {
    Plain,                                                    // ordinary defn
    Clause { group: Symbol },                                 // multi-sig clause
    TraitMethod { shell: FQSymbol, trait_name: FQTraitName, impl_type: FQTypeName },
    Ctor { type_name: FQTypeName, tag: usize, field_count: usize,
           internal: bool, type_def: Option<Box<TypeDefInfo>> },   // dual facet as today
    Accessor { type_name: FQTypeName, field: Symbol },
    MacroClause { group: Symbol },
    RustPrimitive,                                            // hand-written body
    PlatformEffect { scheduling_class: SchedulingClass, poll_shape: bool },
}
```

Origin answers "what is this and how is it displayed/pattern-matched/
scheduled"; `Life` answers "where in the pipeline is it and what can be done
with it". A ctor's tag is origin (needed in Template AND Concrete states); a
platform effect's scheduling class is origin (fixed by the manifest); the
trait-method shell pointer is origin. Nothing in `origin` changes across a
lifecycle transition — which is precisely why it must not live inside the
state enum (today `Constructor`'s metadata and its slot share one variant,
forcing the dormant `CtorState` wedge).

### 4.6 Realization — every slot names its populator

```rust
pub enum Realization<C> {
    /// Backend emits this body; codegen writes the pointer.
    Body { view: MonoDefnVariant, #[serde(skip)] code: Option<C> },
    /// Registration stored a hand-written Rust extern shim at the slot
    /// (today's `PrimitiveBody::Extern`), with the optional borrowed sibling.
    ExternShim { borrowed_sibling: Option<CallableSlot> },
    /// The DLL populated the slot (manifest order; the module's GOT wraps the
    /// DLL slab in place — `platform.rs:333-346`).
    Dll,
    /// A per-instantiation facade over ONE uniform hand-written body — the
    /// backend realises it as a name-alias (I-EMIT §1.2,
    /// `catch-runtime-error`). Changing realization per-instance later is a
    /// backend-local change with zero tree change.
    FacadeOf { abi_name: LinkerSymbol },
}
```

`Realization` is the P21/P22 record the slab lacks: for every claimed slot,
*who writes the pointer* is on the entry. `defined_symbols()` — the codegen
manifest — becomes the trivial projection "`Life::Concrete` with
`Realization::Body`": the Decision-22 predicate's `ast.is_some()` +
kind-exclusion conjunction (`module.rs:1152`) and the S120 D6
`is_concrete()` conjunct are all subsumed by construction.

---

## 5. The populations, one by one

### 5.1 Poly and mono single-sig defs

`(defn f …)`: `declare` → body check settles → concrete: `settle_concrete`
(view + mint); non-concrete: `settle_template(Ast(body),
Constrained|Parametric)`. Exactly today's `UserFnState` semantics with D11,
plus view/code relocated into the state that owns them.

### 5.2 Templates vs instances (Q3)

An instance is a **new entry born `Concrete`**, structurally linked:

```rust
pub struct InstanceLink {
    /// STORAGE identity of the template — read from the typed resolution
    /// carrier (`VarRef::Global` / `Resolved::storage_fq()`), never composed
    /// from a written spelling.
    pub template: FQSymbol,
    pub args: Vec<ConcreteType>,
}
```

The demand that travels from the collectors to the minter is typed the same
way (`MonoDemand { template: FQSymbol /*storage*/, args, site }`). This is
the structural close of FIXME 0935's class: the collector cannot push a
written spelling because the demand's field is the carrier-read storage
identity (P24 corollary — the AST name is a trigger for a keyed read of the
recorded verdict, never the identity), and the mint probes
`template.module`'s table by `template.symbol` — a keyed read that cannot
land on a bare-alias `Import` because the storage identity is by definition
the terminal key. The **mangled name** (`f$Int+Int`,
`Bx.v$user/Bx$Int`) demotes from identity to *derived table key + display
name*, minted ONCE at instance registration from the link (P24); no probe
site re-composes it. Dedup grain: `(template, args)` per registering module —
instances register in the **demanding** module's table
(`monomorphise.rs:669` `current_symbol_table_mut`), which is correct under
P17 (a cluster pass must not mutate a foreign module's table) and stays; the
link is what makes cross-module instances of one template *recognisably* the
same entity for tooling and any future sharing decision, where today the
relation exists only in the spelling of a string.

Templates persist and travel as `Life::Template` — serde-visible body +
scheme, no slot to misuse, no view to fabricate. **A missed mint is loud by
construction**: the template has no slot for the call to fall silently
through (the mechanism that made 0935 invisible — `mono_collect.rs:592`'s
written-spelling push declining at `monomorphise.rs:1171`'s raw probe while
the template's slot absorbed the call).

### 5.3 Poly and mono multi-sig defs

The base name is `Decl::Group { kind: Overload, members }`; each clause is
its own `Callable` with `origin: Clause { group }` and the full machine:
concrete clause → `Concrete`; poly clause → `Template` (today's `g$Var`
one-variant template, `multi_sig.rs:70`, kept in substance). Members hold
clause **storage keys + settled signatures** — recorded at the post-drain
settlement point per P26 (the S112 B1 lesson: the finalisation derives all
member records from one `mangle_sig` over settled params). Dispatch selects a
member at typecheck over the complete member enumeration (P24 carve-out 1)
and transports the selected member's storage identity on the carrier; a
poly-clause selection is an instance demand (§5.2) against the clause
template. Structurally impossible now: a slotted base (no slot field on
`Group`), a clause set completed by iteration order (members are the one
complete record), a `$Var` spelling used as a dispatch identity (members are
refs).

### 5.4 Macros

The parent is `Decl::Group { kind: Macro { clauses_meta, macro_sexp } }` —
same shape as the overload base, different dispatch time (expansion) and
payload (`module.rs:2501-2543` semantics preserved: `macro_sexp` is
compile-path data and serialises). Clause bodies are `Callable { origin:
MacroClause, life: Concrete }` under mangled keys, as today. The parent
structurally cannot carry a slot or view.

### 5.5 Poly and mono primitives (declared, hand-written bodies)

- **Concrete extern** (~50 entries, `declarations.rs`): born
  `Concrete { slot: mint(scheme), realization: ExternShim }`. The mint takes
  the declared scheme — a polymorphic extern with a slot is **uncompilable**,
  which retires the `vec-len` transitional licence structurally (it re-kinds
  to `Inline` per the 0932 preference, or to a uniform-body template below).
- **Inline family**: `Life::Inline`; value position rides minted `__inlwrap`
  instances — ordinary `Concrete { minted_from }` entries (§5.2 machinery,
  not a bespoke wrapper path).
- **Polymorphic hand-written body** (`catch-runtime-error`): `Life::Template
  { body: UniformRust { abi_name }, kind: Parametric }`. Instantiation
  demand mints `Concrete { realization: FacadeOf { abi_name }, minted_from }`
  facades — I-EMIT §1.2 lands IN the representation: the realization roster
  (NC-R re-labelled) is the enumeration of `UniformRust` templates, pinned by
  a trivial projection instead of a hand-maintained set.
- **Host-promised** (`discover-tests`): `Life::HostPromised`, by-name import,
  no slot — unchanged in substance.

### 5.6 Platform effects (DLL-manifest-owned indices)

Born `Concrete { slot: manifest-order mint, realization: Dll }` with
`origin: PlatformEffect { scheduling_class, poll_shape }`. The manifest-order
mint claims index *i* for descriptor *i* against the parsed FQ signature —
which must be concrete, so 0933's refusal is the mint's own `NotConcrete`
arm, located at the descriptor. "Slot i == descriptor i" is assertable at
load as a mint-order invariant; the DLL slab wraps in place as the module's
GOT exactly as today (`platform.rs:333-346`); the direct cursor write
(`platform.rs:351`) has nothing left to do (§4.3). One index space, two
allocation authorities, both expressed as mints — the §3.11 ruling-4
conclusion, now carried by the representation.

### 5.7 Trait impls, poly and mono, including HKT

The `(impl Trait Type …)` split survives: discovery shell
(`Decl::ImplShell`, at the trait's home, D45 as amended) + writer-side
persistence (`written_trait_impls`, FIXME 0869 carrier — unchanged) + method
entries in the **writer's** module. The change is that method entries join
the ONE machine with `origin: TraitMethod { shell, … }`:

- a mono impl's method settles `Concrete` through the same funnel as any
  defn;
- an HKT/generic impl's method whose settled type retains residuals settles
  `Template` — **the `scheme::mono` fabrication at `impl_check.rs:1043`
  becomes uncompilable** (there is no way to construct `Concrete` around a
  non-concrete scheme; the witness mint refuses), and per-instantiation
  demand mints instances via §5.2, with the `minted_from` link preserving
  which impl the instance realises.

Trait-method dispatch reads the shell → member storage identity → carrier,
all keyed (P24), unchanged in direction from `backend-keyed-consumer.md`.

### 5.8 Synthesised constructors and field accessors

Born at `deftype` synthesis, settled immediately (no `Declared` interstage —
a funnel-enforced dead cell, §7): concrete ADT → ctor + accessors
`Concrete { realization: Body(synth view) }`; generic ADT →
`Template { body: Synth(SynthSpec) }`, where `SynthSpec` is the declaration
payload the A-MINT re-synthesiser runs at concrete args (the §2 experiment's
lesson: instances must be built with real concrete node types, so the
template stores the *recipe*, not a placeholder view). The product-type dual
facet stays as origin metadata (`Ctor { type_def: Some }`); member bare
aliases (`v` → `Bx.v`) stay `BindingBody::Alias` entries installed by the
member glob. `IO.Bind` is a `Template` with `internal: true` origin — the
0934 payload-glue word stamps at its (always-concrete) construction sites.

### 5.9 Imports, bare aliases, Ambiguous

Unchanged in substance (`Alias` covers import and re-export via visibility;
`Ambiguous` the sentinel). The §8.6.4 conflict rules and the
import-over-def reject key on the three-arm outer layer
(`imports.rs:881-909`), which they already effectively do. The §3.11
ruling-5 verification stands: no slot is ever orphaned by a name going
ambiguous (the poison lands importing-side; the slot lives defining-side).

---

## 6. What becomes structurally impossible (Q4)

Each row names the defect history it retires. "Structural" here means *no
representation exists*; §7 grades the residuals honestly.

| # | Impossible state/act | Today's guard | History it retires |
|---|---|---|---|
| 1 | A slot on any non-concrete entry — kind-free, population-free (`Template`/`Declared`/`Inline`/`HostPromised` have no slot field; `Concrete` requires the witness) | per-kind states + transitional licences (generic ctors, `vec-len`) + NC-1 sweep | S82 0354, S84 `(Box a)` SIGSEGV, S119 census F1/F2 |
| 2 | Hand-minting a slot around the check (`allocate_got_slot` + literal state construction) | mint helper discipline; `allocate_got_slot` still `pub` (`module.rs:1059`) | the two hand-mints; `impl_check.rs:1043` + `monomorphise.rs:667` launders |
| 3 | A silent dispatch through a template (the un-minted call "works") | none — the template HAS a slot today | FIXME 0935's invisibility; FIXME 0381's 317× backstop |
| 4 | Composing an instance/storage identity from a written spelling (demand + link fields are carrier-read storage FQs; the mangled name is derived once, at registration) | comment discipline (`mono_collect.rs:574-576`) — violated one line below itself | 0620 class, 0935, the renamed-import sibling |
| 5 | The template↔instance relation existing only as a string | name-only (`build_mangled_name`) | 0935's collector/mint identity split |
| 6 | A view or `code` on a template / group / platform / extern entry (kind×field dead pairings) | unread-by-convention flat fields | ruling-3's conceded P20 debt |
| 7 | A slotted overload base or macro parent | slot lives on `Def` kinds they happen not to take | latent |
| 8 | Concrete-without-view for backend-emitted bodies (`Realization::Body` carries the view non-optionally; settlement is atomic) | `Option<MonoDefnVariant>` + a located backend `expect` | the "codegen-reached entry with view None" backstop |
| 9 | A dropped slot claim at redefinition (displacement funnels move it into `Declared.prior` or `retired_slots`) | `redef_slots` external stash + commit-gate discipline | FIXME 0479's third missed displacement site; the S82-class drift |
| 10 | Slot allocation colliding with a manifest slot, or the cursor drifting from the claims (allocation authority derived from claims ∪ tombstones) | stored `next_got_slot` + the `platform.rs:351` direct write | the fifth-writer under-count (§7 item 3 of `concreteness-types-first.md`) |
| 11 | Re-issuing a published-but-unclaimed index (freeze = a move into `retired_slots`, visible to the allocation scan) | int-side retention pool only — invisible to the table | the §1.1 scan-model residual; P22's register |
| 12 | "Broken" being invisible in the store (slot alive, no body, no provenance) | int-side trap-stub + registry | S45 embedded-original-error; session-transaction §6 |
| 13 | A polymorphic extern primitive holding a slot (mint refuses the declared scheme) | transitional licence + roster pin | `vec-len` (0932); the I-ABI roster's licence class |
| 14 | A fabricated "concrete" scheme entering the store as concrete (settlement funnel takes the scheme through the witness check; `scheme::mono` over a residual type cannot reach `Concrete`) | R-4/R-18 census + CS-1 helper discipline | the HKT fabrication; R-13's family |

And two loudness conversions (not impossibility, but structural failure-mode
upgrades): a missed mint is a missing-slot hard failure (row 3's dual); a
cache restored against the new shape re-derives the slot authority and
validates uniqueness + concreteness + origin×state legality at the load
boundary (`CacheStale`, never trust — P25 tier 3).

## 7. What remains checked, honestly (the residual ledger)

- **Serde and `Clone` bypass every funnel** (unchanged from §3.2's ladder):
  a slot can in principle be cloned beside a different scheme. Tier 1
  by-accident-unconstructable (witness + funnels), tier 3 load-boundary
  re-derivation + validation, tier 5 the NC-1-successor sweep (now the
  trivial projection "every slot sits in a `Concrete`/`Broken`/foreign state
  whose scheme is concrete").
- **`CallableSlot` is `Copy`; Rust cannot force a moved-out claim to be
  used.** Slot conservation (funnel invariant 1) is accessor-tier; the
  standing check is the load/commit uniqueness scan. Named as a fallback per
  P20, with the funnel as the bridge.
- **Origin×state dead cells** (`Declared × RustPrimitive`,
  `Inline × Plain`, …): funnel-enforced + one enumerated legality function
  asserted at the funnels and the load boundary. Deliberate P6 trade against
  a per-origin state-enum family (§4.2); all dead cells are of the
  never-constructed polarity.
- **Staging clones duplicate claims by design** (a staged table is a
  parallel world; its slots are re-pointed at commit — `worker.rs:811-827`).
  The commit gate remains the arbiter; the funnels apply on both sides.
- **Demander-local instance duplication** across modules is accepted (P17);
  the `InstanceLink` makes it visible and reversible later.

## 8. Constraints: forced vs incumbent

**Genuinely forcing** (named per the commission): the cache round-trip
(indices persist, pointers don't) → serde split as designed; the
`__cranelisp_got_primitives` link symbol (`got.rs:88-120`) → static-backed
slabs stay; P22 published-index permanence → tombstones + rebind-only reuse +
freeze-on-retire; staging/commit concurrency → commit gate stays the live
authority; per-module GOT ABI (`got_base + slot*8` in every mode, P11) → one
index space.

**Incumbent only — dropped by this design**: the `pub symbols` map; the
stored `next_got_slot` cursor; `redef_slots`; the four fragmented state
vocabularies; name-composed instance identity; `GotTable`'s poverty as an
*argument* (it stays poor, but nothing any longer cites its Clone/serde
behaviour as the reason a register can't exist — the reason is P7 + the
determinant argument, §4.3).

## 9. Migration (Q6)

**What survives of the landed work — all of it, in role if not in spelling:**
`CallableSlot` + `mint`/`rebind` (the funnel's interior and witness);
D11 (generalised into `Declared.prior` — same semantics, wider population);
`CtorState` (subsumed: its two states ARE `Template`/`Concrete`; the dormant
enum becomes a stepping stone or deletes unwired); `ctor_field_types_at`;
`WrittenTraitImpl` + enrolment; `got_data_symbol_name`; the S119 CS-1/CS-2/
CS-3 typecheck designs (their gates become the funnel's vocabulary); the
`defined_symbols` D6 conjunct (subsumed by construction); every wash-plan
mint re-route (the sites are the same sites).

**Cost, honestly.** This is the S120 wash's site list (types 26 / typecheck
52 / backend 46 / src 111 / primitives 2 / platform 5 `got_slot` mentions,
plus every `ModuleEntry::Def {` destructure) **plus** the outer-layer re-arm
(three-arm `BindingBody` + facet nesting: every `ModuleEntry::` match in the
workspace re-arms once) **plus** the funnel conversion (every direct
`symbols.insert`/`get_mut`-state-write becomes a method call). Estimate:
1.5–2× the scoped S120 wash — the largest single window of the programme —
in one schema window (`CACHE_SCHEMA_VERSION` +1, wholesale pre-window
invalidation). Wave order unchanged from the wash plan: types → typecheck →
backend → runtime pair → int → tests, with the same two structural payoffs
landing earlier (loud missed mints after the typecheck wave; no
declaration-fed backend type source after the backend wave).

**Recommendation on the flip: RE-TARGET, do not run it as specified.** The
S120 flip as pinned (per-kind slot-field retypes + `CtorState` wire-in + D6
+ D11) is a strict waypoint of this design: every site it would churn, this
churns again with the unified machine — two exhaustive-match sweeps over the
same ~200 sites for one destination. With churn explicitly discounted and P8
(no interim implementations) in force, the honest plan is to land the
unified machine as THE S120 types change-set and run the wash once. If the
user declines this design, the flip as specified remains sound and proceeds
unchanged — nothing here invalidates it; it is the smaller move along the
same direction. A middle option exists (flip first, unify in S121+) and is
recommended against: it ships the per-kind vocabulary as a knowing interim.

**Held pending the user.** Per the commission, the flip stays held until the
user disposes of this sketch: adopt (re-target S120), decline (flip proceeds
as specified), or direct a different cut.

## Next skills

- **USER** — dispose of §9 (adopt / decline / re-cut). Everything below is
  conditional on adoption.
- `/sprint` — if adopted: re-scope the S120 opener to the §4 types
  change-set; the 0931/0932/0933/0935 FIXMEs re-point to this document's
  §5.2/§5.5/§5.6 mechanisms (their substance is preserved, their spellings
  change).
- `/design`(typecheck) — the funnel-consumption design: pass-1 `declare`,
  settlement points, `MonoDemand` carrier, the drain/finalize interaction
  with `Group` members (P26 windows).
- `/design`(backend) — `Realization` consumption; the `FacadeOf` emission
  arm; cache-load validation arms.
- `/qa` — the load-boundary validation matrix (uniqueness, slot⇒concrete,
  origin×state legality, tombstone conservation) as the NC-family successor.
