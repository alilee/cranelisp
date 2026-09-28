# Constructors — canonical `Type.Ctor` and the bare spelling

Owner: `design` narrow-deployed to `cranelisp-typecheck`. Subordinate to
[`typecheck.md`](typecheck.md) and [`adt.md`](adt.md); the constructor sibling
of [`fixme-0365-field-accessor-dotted.md`](fixme-0365-field-accessor-dotted.md).
Reader: anyone changing how typecheck registers, resolves, selects or
exhaustiveness-checks constructors, or changing the dotted-member resolver
that constructors share with field accessors and trait methods.

Required behaviour is in `spec/08-modules.md` §8.5.2 (canonical constructor
name; product dual-facet corner) and §8.6.5 (shared bare constructor names),
and `spec/06-pattern-matching.md` §6.2.1, §6.2.2, §6.2.4 and the §6.2 EBNF
(dotted constructor patterns). The shared resolver also realises derived
dotted access to a trait's methods (`spec/08-modules.md` §8.3.11, §8.5.2;
`spec/07-traits.md` §7.4.2a). Neighbouring authorities this design uses
without restating:

| Subject | Authority |
|---|---|
| The constructor storage-key grammar, every writer and every cross-crate reader | [`design/arch/dotted-ctor-canonical-keys.md`](../arch/dotted-ctor-canonical-keys.md) §1–§3, §10 |
| `SymbolEntry`, `Binding`, `NameCandidate`, settlement funnels | `design/arch/symbol-table-lifecycle.md` §3, §4, §5.8, §5.9 |
| Selecting one declaration from a bare spelling's candidates, value and pattern | [`use-site-candidate-selection.md`](use-site-candidate-selection.md) §5, §7, §9 |
| Concrete versus template constructors and their re-synthesis | [`non-concrete-producer-obligations.md`](non-concrete-producer-obligations.md) |
| Constructor schemes, the product dual facet, internal constructors | [`adt.md`](adt.md) §"Constructor Scheme Generation", §"Product Type Handling"; [`io-types.md`](io-types.md) §1 |

Section numbers are cited from source and sibling designs; retired numbers are
not reused, so gaps are deliberate. The file name predates the subject name
and is kept because it is cited.

## 0. Model

- A **sum or enum constructor** has exactly one declaration: the canonical
  callable binding keyed `member_key(Type, Ctor)` (`Maybe.Some`) in the type's
  home module, carrying `CallableOrigin::Ctor` (owning type, tag, internal
  flag).
- The bare spelling (`Some`) is a `NameCandidate` reference to that binding,
  carrying the `deftype`'s visibility. It is not a second callable, adds no
  slot and no compiled function.
- Same-named constructors of different types coexist as distinct candidates
  of one spelling. No sentinel is installed, no declaration is refused, and the
  dotted form is always valid.
- A **product constructor** keeps its single type-name key with the type
  facet on its origin; it has no dotted key and no bare exposure (§2).
- Value and pattern positions reach the canonical binding through one member
  resolver (§3), so they agree by construction.

## 1. Registration — `crates/cranelisp-typecheck/src/adt.rs::register_type_def_with_ctor_infos`

### 1.1 The canonical key and the bare candidate (sum constructors)

The registration site builds slotless `AdtCtorSpec`s and calls the shared
types builder `build_adt_entries`, which returns ordered `(key, AdtEntrySpec)`
pairs already keyed by the one `member_key` grammar. The site stays thin:

1. **Non-callable binding** (the type record) → installed unchanged through
   `install_binding`.
2. **Callable recipe** at the canonical key → submitted to exactly one
   settlement funnel by scheme concreteness: `install_concrete` with a
   `Realization::Body` built from the recipe, or slotless `install_template`
   carrying `TemplateBody::Synth` for re-synthesis. An existing template is
   kept; an existing concrete or broken entry is retired through
   `retire_abi_changing` before re-settlement. No caller constructs a slot.
3. **Bare exposure** → for a sum constructor only, `expose_candidate(Ctor,
   <home>/Type.Ctor, visibility)`.

What `expose_candidate` guarantees (types-owned, lifecycle §3):

- re-registering the same `deftype` (a REPL re-run) re-exposes the same source,
  which deduplicates, with public dominating private;
- another type's constructor of the same spelling is a distinct source and
  remains a second candidate;
- an unrelated binding or import already at the bare spelling is not replaced;
  the canonical constructor is still minted and reachable, and the spelling's
  candidates are resolved at each use.

Minting the canonical binding unconditionally is the load-bearing choice: the
dotted handle exists and is identical however contested the bare spelling
becomes. Do not re-propose a bare-keyed constructor with a secondary dotted
alias, or a registration-time poison of the bare spelling; the first leaves a
contested constructor without a stable handle, and the second decides at
registration a question only the use site can answer.

### 1.2 The committed-member recogniser

`adt::committed_member_owner` answers "which type owns the member under this
key" for both type-member kinds:

- a constructor's owner is read directly from `CallableOrigin::Ctor.type_name`;
- an accessor's owner is read from its `(Fn [ADT] _)` scheme through
  `committed_accessor_kind`.

It is the one type-member recogniser the dotted resolver (§3.1) and
alternative reconstruction use, so same-cluster and cross-cluster reads agree.

A trait's method is recognised by its own record instead: the owning
`FQTraitName` it carries ([traits §1.4](traits.md#14-method-declarations)).
Each parent kind therefore has exactly one recogniser, and each reads the
owner from the declaration. Do not widen `committed_member_owner` to trait
methods: `reconstruct_accessor_alternatives` enumerates through it, so a trait
method would enter the type-member alternatives it lists.

### 1.3 Diagnostic alternatives

An unsettled bare constructor use reports every surviving canonical
alternative (`Maybe.Some`, `Option.Some`), never iteration order as
precedence. The surviving identities on the pending use are the source of that
list ([`use-site-candidate-selection.md`](use-site-candidate-selection.md) §9).
As built, the pattern path's final ambiguity branch still reconstructs owners
from the table through `reconstruct_accessor_alternatives`, which recognises
constructors through §1.2 but cannot list a surviving non-member candidate
(§8).

### 1.4 What differs from the accessor path

- The builder already produces the constructor recipe; there is no
  per-constructor body synthesis in typecheck.
- The owner is read from `type_name`, not inferred from a scheme.
- The bare candidate carries the `deftype`'s visibility, like an accessor's.
- Constructors have no impl-time interaction; accessors' is
  `fixme-0365-field-accessor-dotted.md` §2.

## 2. Product dual-facet corner (spec §8.5.2)

A product constructor has type name equal to constructor name
(`(deftype Point [:Int x :Int y])`). The builder returns its callable recipe
at the type-name key `Point`, with the completed `TypeDefInfo` carried on
`CallableOrigin::Ctor { type_def: Some(..) }`; the registration site retires
any provisional type-only binding first, so the facet is never
double-registered.

- No `Point.Point` key is minted and no bare candidate is exposed; the bare
  name is the canonical key.
- Splitting the product into a dotted canonical plus a bare exposure would
  break `type_def_view_of`'s "entry as a type" read.
- Two product types cannot share a constructor name without sharing a type
  name, which is a §8.6.4 definition conflict, not a §8.6.5 candidate set.
- The degenerate `Point.Point` does not resolve: the resolver probes a key
  that does not exist (§3.1).

## 3. The one member resolver — value, pattern and dispatch

### 3.1 Shared core — `checker.rs::dotted_member_identity`

One crate-visible core, `dotted_member_identity`, resolves a dotted
`Parent.member` spelling to its storage identity and terminal binding. The
parent is a type or a trait in bare scope:

1. accept exactly one `.`, both sides non-empty, and no `/` (a `/` form is
   module qualification);
2. collect the head's candidates once through ordinary scope resolution, and
   keep only those that can be a parent: types, judged by the same predicate
   type syntax uses, and traits (spec §8.6.5 rule 2). Then count what
   remains. None is not a member reference, several is an ambiguous parent,
   and one is the parent;
3. probe `member_key(Parent, member)` in the **parent's home module**, staging
   over live;
4. accept only when the terminal is owned by that exact parent, judged by the
   parent kind's recogniser (§1.2):

| Parent | Home and key name | Owner recogniser |
|---|---|---|
| Type | Its `FQTypeName` | `adt::committed_member_owner` names that type |
| Trait | Its canonical `FQTraitName` | The method record's owning trait equals that trait |

Rooting the probe in the home module is what makes the dotted form work across
modules. The key is built from the parent's canonical name, never the written
head, so a renamed import still probes the home key. A method imported without
its trait does not make `T.m` resolve: the trait head must itself be in bare
scope (spec §8.3.11).

**The core is the only authority for a dotted spelling.** A bare
`Parent.member` spelling is always a member access: no binder may be dotted
(spec §1.4.4, §5 binder table), and spec §8.5.2 resolves it from the parent,
bypassing bare-name lookup. The core's answer therefore has three outcomes,
and no consumer adds a fourth:

| Outcome | When | Consumer action |
|---|---|---|
| Member | The head keeps exactly one type or trait, and it owns `member` | Use the storage identity and binding |
| Rejected | The head keeps several types or traits (`Ambiguous`, listing them), or the head's candidate walk fails with an error that is not a not-found | Return that error, located at the reference |
| Miss | The head is not found, keeps no type or trait, or its one parent does not own `member` | Report the position's ordinary miss |

- No consumer resolves a dotted spelling as a literal key through bare scope,
  candidate collection or selection. The literal `Parent.member` key is a
  storage key in the parent's home module. Glob imports and the prelude expose
  it, so a literal read bypasses the parent's own candidate contest. In
  ACT-1001 P-1, prelude `T` and imported `T` made the parent ambiguous, yet
  `T.m` reached the prelude impl through the prelude's literal key.
- The core follows `ResolutionScope::resolve_macro_head` in two separate
  respects:
  - **Candidate filtering.** Candidates are filtered by role before they are
    counted. A same-spelled declaration that cannot be a parent does not
    contest the parent. An example is a sum constructor's bare projection
    `Num` beside a product type `Num` (spec §8.6.4). Such a declaration also cannot
    hide the parent.
  - **Error transport.** A not-found error from the walk is a Miss. Every
    other `ResolveError` propagates as Rejected.

  The core selects nothing further: it never chooses among the parents it
  keeps, and never falls back to the literal key. Its `Ambiguous` error lists
  the canonical parents it kept, as §8.6.5 requires.
- The type test is the one type syntax uses
  (`crates/cranelisp-typecheck/src/resolve.rs::resolve_type_candidate`).
  Both positions share one crate-private predicate beside `type_def_view_of`, so a spelling that is ambiguous as a
  type annotation is also ambiguous as a dotted parent. An intrinsic type
  counts as a parent candidate. It owns no members, so as the only parent it is
  a Miss.
- Resolving the head to a unique declaration first and then checking its role
  was rejected. It rejects a legal parent whenever a value shares its
  spelling.
- A spelling containing `/` is not dotted in this sense. Module-qualified
  `m/T.m` keeps the qualified walk, which selects the parent by its module
  (spec §8.5.3, §8.6.6).
- Self-qualification is normalised to the bare spelling before this core
  (`normalize_self_qualified`, S113 ruling (a)). A self-qualified dotted member
  therefore follows the bare rule.

Its consumers, each taking the outcome above:

- value position, including the recorded carrier (§3.2);
- pattern position and the auto-curry guard (§3.3);
- trait-method dispatch (§3.5).

### 3.2 Value position

`infer.rs::infer_var` consults the core once for a dotted spelling that is not
lexically bound, before any bare candidate collection. That one outcome
supplies both the scheme and the `VarRef::Global` storage identity, so typing
and the carrier cannot disagree ([Principle 24](../arch/principles/24-resolve-once.md)).
A dotted spelling never records a gap, because it has no module qualifier.
Like every value attempt, it still writes the empty pending gap before it
returns any outcome ([`typecheck.md` §3.5](typecheck.md#35-qualified-stacked-bounds-and-constructor-patterns)).
Otherwise a gap left by an earlier miss could turn a dotted Rejected or Miss
into a module-load retry.
`checker.rs::lookup` answers a dotted spelling from the core alone. Its
module-scope step never reads the literal key, so no other `lookup` caller can
bypass the parent.
`Color.Red : Color`; `Maybe.Some : (Fn [a] (Maybe a))`; a trait head yields
the method's constrained scheme, as its bare spelling would. First-class use needs
no branch: the canonical binding is an ordinary callable whose lifecycle state
is carried by `Life`, not inferred by the resolver. The internal-constructor
and constrained-value guards in `infer_var` reach the same terminal and read
`internal` from its origin.

### 3.3 Pattern position and the auto-curry guard

`checker.rs::resolve_constructor_entry` takes a `DottedMember` spelling
(exactly one `.`, both sides non-empty, no `/`) through
`dotted_member_identity` before its bare and `/`-qualified
arms. `check_constructor_pattern` and `try_auto_curry` consume it, so
`(Maybe.Some x)` and nullary `Maybe.None` reach the same canonical callable as
value position, for same-module and imported types. `instantiate_ctor`
instantiates from the origin's type and tag and returns the storage identity
recorded in `MethodResolutions.pattern_ctors`. Both consumers keep only a
`CallableOrigin::Ctor` terminal, so a dotted trait method in pattern position
is not a constructor. A Rejected outcome is the pattern's error.
`check_constructor_pattern` returns it rather than its not-a-constructor miss.
The auto-curry arity guard is only a probe and ignores it, because value
position reports the same outcome for the callee.

A **bare** constructor pattern with several candidates is selected by the
scrutinee type ([`dotted-ctor-canonical-keys.md`](../arch/dotted-ctor-canonical-keys.md)
§7) through the pending-pattern lifecycle of
[`use-site-candidate-selection.md`](use-site-candidate-selection.md) §7.

### 3.4 Frontend — no change

`ast_builder.rs::build_pattern` keeps `Pattern::Constructor.name` unsplit: a
parenthesised `(Maybe.Some x)` and a bare uppercase-initial `Maybe.None` both
become constructor patterns carrying the dotted name (§6.2.4). The capability
is entirely typecheck resolution.

### 3.5 Trait-method dispatch

`traits/dispatch.rs::try_resolve_trait_method` branches on the written
callee's shape:

- A dotted spelling goes to the §3.1 core alone. A Rejected outcome is
  returned as the dispatch error, and a Miss or a non-method terminal is "not
  a trait method".
- A bare or qualified spelling uses ordinary scope resolution.

A `T.m` call whose trait is in bare scope only through an import or the
prelude therefore dispatches at the call, exactly as at the trait's home.
Dispatch then reads only the canonical declaration
([traits §7](traits.md#7-method-resolution)).

Dispatch must consult the core itself. Deferred settlement reads the recorded
`VarRef` carrier, but the immediate `infer_apply` dispatch and the auto-curry
drains call this function by spelling. If dispatch read the literal key
instead, those routes could reach a member the carrier route rejects
([Principle 24](../arch/principles/24-resolve-once.md)).

## 4. Exhaustiveness — `crates/cranelisp-typecheck/src/adt.rs::check_exhaustiveness_in_module`

`TypeDefInfo.constructors` keeps bare display names, so two readers there must
account for canonical keying.

### 4.1 Covered-constructor normalisation

Covered pattern names reduce to their terminal segment after both separators —
the `/` module prefix, then the `.` type prefix — before comparison with the
declared names. Without the `.` step a total match written with dotted arms is
reported non-exhaustive.

### 4.2 Internal-constructor probe

Each declared constructor's `internal` flag is read from the canonical
`member_key(Type, Ctor)` binding first, then from the bare key for the product
facet (the only bare fallback `dotted-ctor-canonical-keys.md` §1 admits). A
bare-only probe would miss every sum constructor, default `internal: false`,
and force user matches on `IO` to cover `Bind`/`Pure`/`Effect`.

Exhaustiveness runs after every constructor site in the match has settled and
must not consume the as-written bare names
([`use-site-candidate-selection.md`](use-site-candidate-selection.md) §7).

## 5. Storage keys across crates

`cranelisp_types::type_ctor_names` returns storage keys, and the key meaning is
part of the cache contract
([`dotted-ctor-canonical-keys.md`](../arch/dotted-ctor-canonical-keys.md) §2).
Typecheck's part is to register through the [shared builder](#11-the-canonical-key-and-the-bare-candidate-sum-constructors) so its keys
match every other writer's; it adds no key mapping of its own.

## 6. Keying changes reach every crate's readers

A constructor keying change's blast radius is **every crate's raw probe of a
constructor key**, not the owning crate's. The S109 landing scoped its audit to
typecheck and regressed in the backend and binary readers it had marked
unaffected. Find readers by the storage key they probe, across the workspace,
and change them in the same change-set as the writers
([Principle 8](../arch/principles.md)). The current reader inventory is
[`dotted-ctor-canonical-keys.md`](../arch/dotted-ctor-canonical-keys.md) §3;
it is not duplicated here.

Typecheck's own readers and their disposition:

| Site | Disposition |
|---|---|
| `defined_symbols()` / emission | Only a canonical `Life::Concrete` callable with a body is emitted; the bare candidate adds none, and a template emits nothing. |
| Dotted value and pattern resolution | §3. |
| Bare value and pattern selection | [`use-site-candidate-selection.md`](use-site-candidate-selection.md) §5, §7. |
| Exhaustiveness | §4. |
| `instantiate_ctor` | Reads `TypeDefInfo` at the origin's type identity, never by spelling ([typecheck §3.3](typecheck.md#33-cross-module-lookups)); tag-indexed on it; records the storage identity it resolved into `pattern_ctors` (arch §10). |
| `public_symbols()` → listing, glob export and harvest | Bindings only: `Maybe.Some` is the one listed entry and bare `Some` a candidate reached through `public_name_candidates` (lifecycle §3, §5.8; accessor sibling §1.6.5). Rendering is `repl/spec.md`'s. |
| Mono collection and `callees` | Constructors are not monomorphised, and dotted member references record no `callees` edge. |

## 7. Public surface and quality attributes

- **No feature-specific crossing type.** Typecheck consumes the published
  `AdtEntrySpec`, lifecycle vocabulary, settlement funnels and
  `expose_candidate` unchanged; the member resolver and recognisers are
  crate-private. Constructors add no `public-api.txt` line.
- **Single source of truth (Principle 7).** One `member_key` grammar, one
  shared builder, one member resolver for value, pattern and dispatch (the
  only authority for a dotted spelling, §3.1), one recogniser per parent kind; the canonical callable is the
  sole scheme and metadata source.
- **Structural invariant (Principle 18).** "`Maybe.Some` names exactly one
  thing" holds by construction: the canonical binding is always minted and
  public, and contest is confined to the bare spelling's candidate set.
- **Evidence.** The dotted, contested and product cases are module tests in
  `adt/tests.rs` and the checker and inference test modules;
  `tests/spec_08_modules.rs` and `tests/spec_06_pattern_matching.rs` carry
  end-to-end cases. Coverage status is the spec-side annotation band, which
  `qa` maintains.

## 8. Unresolved obligations

- **Pattern selection is not yet the approved lifecycle.**
  `infer.rs::check_constructor_pattern` still tries a direct
  determined-scrutinee probe before collecting pending candidates, and its
  final ambiguity branch counts raw candidates and builds its hint through
  `reconstruct_accessor_alternatives`. The approved target and its source gap
  are [`use-site-candidate-selection.md`](use-site-candidate-selection.md) §2,
  §7 and §9; implementation is `dev`'s under that design, with no further
  design decision owed here.
- **Stale rationale in source.** Comments and rustdoc on the constructor path
  still name the retired `Def`/`DefKind::Constructor` shape where source now
  reads `CallableOrigin::Ctor`: the `CtorBuild` rustdoc and the §4.2 probe
  comment in `adt.rs`, and the constructor-to-type lookup rustdoc in
  `checker.rs`. Repair is `dev`'s.

## 9. Cross-references

- Source: `crates/cranelisp-typecheck/src/adt.rs`
  (`register_type_def_with_ctor_infos`, `committed_member_owner`,
  `check_exhaustiveness_in_module`); `checker.rs` (`lookup`,
  `dotted_member_identity`, `DottedMember`,
  `resolve_constructor_entry`, `type_def_view_of`, `is_type_candidate`); `infer.rs`
  (`check_constructor_pattern`, `try_auto_curry`, `instantiate_ctor`);
  `traits/dispatch.rs` (`try_resolve_trait_method`);
  `crates/cranelisp-types/src/adt_build.rs` (`build_adt_entries`).
- Designs: the authority table at the top.

## Former section numbers

| Former | Now |
|---|---|
| Header "binding inputs", C1 facade handoff | Authority table; the handoff closed when `AdtEntrySpec<C>` became generic over the code store, and the binding installs unchanged (§1.1) |
| §0 "unifying insight" and the C1 terminology note | §0 and §1.1 |
| §1.1 bare alias and collision arms | §1.1 — alias and registration-time poison retired for candidate exposure |
| §1.2 recognizer recommendation | §1.2, as built |
| §1.3 accessor-owner bookkeeping and rename | §1.3 and §8 |
| §4 items 1–2 | §4.1–§4.2 |
| §5 Obligations A and B | §5; authority is arch §2 |
| §6 cross-crate census and writer inventory | §6; inventory is arch §1 and §3 |
| §8 Phase-4 `/repl` coordination item | Retired: listing is settled by construction (§6) |
