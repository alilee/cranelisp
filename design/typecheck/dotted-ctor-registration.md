# Constructors — canonical `Type.Ctor` and the bare spelling

Owner: `design` narrow-deployed to `cranelisp-typecheck`. Subordinate to
[`typecheck.md`](typecheck.md) and [`adt.md`](adt.md); the constructor sibling
of [`fixme-0365-field-accessor-dotted.md`](fixme-0365-field-accessor-dotted.md).
Reader: anyone changing how typecheck registers, resolves, selects or
exhaustiveness-checks constructors.

Required behaviour is in `spec/08-modules.md` §8.5.2 (canonical constructor
name; product dual-facet corner) and §8.6.5 (shared bare constructor names),
and `spec/06-pattern-matching.md` §6.2.1, §6.2.2, §6.2.4 and the §6.2 EBNF
(dotted constructor patterns). Neighbouring authorities this design uses
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
key" for both member kinds:

- a constructor's owner is read directly from `CallableOrigin::Ctor.type_name`;
- an accessor's owner is read from its `(Fn [ADT] _)` scheme through
  `committed_accessor_kind`.

It is the one recogniser the dotted resolver (§3.1) and alternative
reconstruction use, so same-cluster and cross-cluster reads agree.

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

## 3. The one member resolver — value and pattern position

### 3.1 Shared core — `checker.rs::resolve_dotted_member_entry`

One private core, `dotted_member_identity`, resolves a dotted `Type.member`
spelling to its storage identity and terminal binding:

1. accept exactly one `.`, both sides non-empty, and no `/` (a `/` form is
   module qualification);
2. resolve the head through ordinary scope resolution to a type
   (`type_def_view_of`);
3. probe `member_key(Type, member)` in the **type's home module**, staging over
   live;
4. accept only when `committed_member_owner` names that exact type.

Rooting the probe in the home module is what makes the dotted form work across
modules. `resolve_dotted_member_entry` projects the binding;
`resolve_dotted_member_fq` projects the storage identity recorded as
`VarRef::Global`.

### 3.2 Value position

`checker.rs::lookup` calls `resolve_dotted_member`, which projects the
terminal callable's scheme; `lookup` instantiates it as for any value.
`Color.Red : Color`; `Maybe.Some : (Fn [a] (Maybe a))`. First-class use needs
no branch: the canonical binding is an ordinary callable whose lifecycle state
is carried by `Life`, not inferred by the resolver. The internal-constructor
and constrained-value guards in `infer_var` reach the same terminal and read
`internal` from its origin.

### 3.3 Pattern position and the auto-curry guard

`checker.rs::resolve_constructor_entry` takes a dotted spelling (`.` and no
`/`) through `resolve_dotted_member_entry` before its bare and `/`-qualified
arms. `check_constructor_pattern` and `try_auto_curry` consume it, so
`(Maybe.Some x)` and nullary `Maybe.None` reach the same canonical callable as
value position, for same-module and imported types. `instantiate_ctor`
instantiates from the origin's type and tag and returns the storage identity
recorded in `MethodResolutions.pattern_ctors`.

A **bare** constructor pattern with several candidates is selected by the
scrutinee type ([`dotted-ctor-canonical-keys.md`](../arch/dotted-ctor-canonical-keys.md)
§7) through the pending-pattern lifecycle of
[`use-site-candidate-selection.md`](use-site-candidate-selection.md) §7.

### 3.4 Frontend — no change

`ast_builder.rs::build_pattern` keeps `Pattern::Constructor.name` unsplit: a
parenthesised `(Maybe.Some x)` and a bare uppercase-initial `Maybe.None` both
become constructor patterns carrying the dotted name (§6.2.4). The capability
is entirely typecheck resolution.

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
| `instantiate_ctor` | Tag-indexed on `TypeDefInfo`; records the storage identity it resolved into `pattern_ctors` (arch §10). |
| `public_symbols()` → listing, glob export and harvest | Bindings only: `Maybe.Some` is the one listed entry and bare `Some` a candidate reached through `public_name_candidates` (lifecycle §3, §5.8; accessor sibling §1.6.5). Rendering is `repl/spec.md`'s. |
| Mono collection and `callees` | Constructors are not monomorphised, and dotted member references record no `callees` edge. |

## 7. Public surface and quality attributes

- **No feature-specific crossing type.** Typecheck consumes the published
  `AdtEntrySpec`, lifecycle vocabulary, settlement funnels and
  `expose_candidate` unchanged; the member resolver and recogniser are
  crate-private. Constructors add no `public-api.txt` line.
- **Single source of truth (Principle 7).** One `member_key` grammar, one
  shared builder, one member resolver for value and pattern, one recogniser;
  the canonical callable is the sole scheme and metadata source.
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
  `resolve_dotted_member_entry`, `resolve_constructor_entry`,
  `type_def_view_of`); `infer.rs` (`check_constructor_pattern`,
  `try_auto_curry`, `instantiate_ctor`);
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
