# S121 result-context specialization

Status: **implemented; generated baseline confirmed by the user** (2026-09-07).
The user approved this exact architecture/API packet (“approved”) and confirmed
the generated four-removed/four-added result-context delta (“proceed”), as
recorded in [SPRINT.md](../../sprints/SPRINT.md).
Owner: `arch`. Reader: a reviewer tracing the accepted inter-crate API delta.
Authority: that packet approval and the approved clarification in [spec §3.3.4 and
§3.6.3–§3.6.4](../../spec/03-types.md). Sprint sequencing lives in
[SPRINT.md](../../sprints/SPRINT.md).

The current contract is authoritative in source rustdoc,
[interfaces.md](interfaces.md) §Instance identity funnel,
[bounded-contexts.md](bounded-contexts.md) §2 and §7, and
[symbol-table-lifecycle.md](symbol-table-lifecycle.md) §5.2. This packet retains
the approved proposal and its rationale. Archive it when sprint and QA owners
reconcile their references together; its path stays stable until that handoff.

## 1. Recommendation

Keep the existing division of responsibility. Typecheck determines which
concrete generic instance is needed; the symbol table owns its identity and
publication; backend compiles that already-concrete body.

Change what identifies an instance: record **the concrete choices for the
definition's generic variables**, not the types of its value parameters.

```clojure
(defn g [] (fn [y] 100))
((g) 5)
((g) "heap")
```

`g` has scheme `forall a. Fn([], Fn([a], Int))`.

| Information | First use | Second use |
|---|---|---|
| Value arguments supplied to `g` | `[]` | `[]` |
| Generic substitution | `a = Int` | `a = String` |
| Concrete type of `g` | `Fn([], Fn([Int], Int))` | `Fn([], Fn([String], Int))` |
| Instance identity | `(g, [Int])` | `(g, [String])` |

These identities are explanatory tuples, not proposed linker-name strings.
There are no extra runtime arguments: the two specialized bodies retain the
ordinary calling convention.

```text
Today:     call's value-argument types ──> demand/key ──> instance
           both calls give []             collision

Proposed:  argument + result constraints
                      │
             typecheck settles substitutions
                      │
            MonoDemand(template, type_args, site)
                      │
            InstanceLink(template, type_args)
                      │
       SymbolTable.install_instance ──> concrete body + slot
                                             │
                                   backend keyed compilation
```

This is specialization after HM inference, not overload search added to HM.
An overload arm is selected under the existing overload rules first; its
`CallableTarget::OverloadArm` then identifies the selected generic definition.
Overload-member naming and trait-method qualification do not change.

## 2. Type arguments and settlement

For a particular template scheme, order its generalized variables by first
occurrence in `scheme.ty`, left-to-right and depth-first, visiting function
parameters before the result. Use the existing `collect_var_ids_ordered` walk,
filtered to membership in `scheme.type_vars`; repeated variables appear once
and higher-kinded heads precede their arguments. `type_args[i]` substitutes the
ith variable in that order. The vector has exactly that scheme's number of
generalized variables, including result-only variables. It is **not** ordered
by value-parameter position. For `forall a. Fn([a, a], a)`, an Int instance has
`type_args = [Int]`, not `[Int, Int]`.

This is deliberately **not the raw `scheme.type_vars` order**: current
generalization sorts that vector numerically by inference IDs, which is not a
stable semantic correspondence when an alpha-equivalent scheme is rebuilt.
First occurrence gives alpha-equivalent signatures the same argument positions
without changing `Scheme` or exposing IDs. For `Fn([a, b], a)`, choices for `a`
and `b` occupy positions 0 and 1 regardless of their numeric IDs or written
names. Derivation and replay use the same authoritative scheme
for that template, including the exact checked-body scheme while the current
cluster is unpublished. The existing `Scheme` representation and generalization
order do not change. A non-alpha-equivalent changed template is subject to existing source/cache
invalidation, not reinterpretation of an old vector against a new scheme.

Typecheck owns one private derivation of the vector: instantiate the selected
scheme, reconcile its full function type with settled use information, and
extract each generalized variable's concrete substitution. Existing concrete
type conversion rejects residual variables. Higher-kinded head substitutions
use the existing resolved constructor representation, `ADT(FQTypeName, [])`;
an unresolved `TyConApp` head remains non-concrete.

The minter receives the resulting demand, reconstructs the concrete function
type by substitution into the template scheme, checks constraints and rechecks
the body in the template's defining scope. It carries the same `InstanceLink`
through deduplication, naming and installation, rather than reconstructing
identity from the finished body's parameters.

No concrete identity is published before result context settles (Principle 26).
An unresolved site within an admitted generic definition stays for its concrete
recheck; an unresolved codegen-reaching use takes the existing §3.11 type error.
The change does not add defaults or reject a named generic definition merely
because it has not yet been used.

There are three distinct input shapes to that private derivation:

- Ordinary call: supplied parameter types plus the call expression's result.
- Function value: the reference's whole function type, including its return.
- Partial application: supplied parameters plus the remaining parameters and
  final result of the residual closure; the residual closure is not confused
  with an ordinary function-valued return.

Nested rechecks use their own captured type/resolution maps. The diagnostic
`site` remains a location, never a substitute for missing result information.
In particular, function-value instantiation no longer needs to discard its
real location by passing a synthetic span merely to suppress result pinning.

## 3. Exact approved public API packet

In `cranelisp-types`, retain both non-exhaustive structs and their existing
derive contracts. Replace the two fields and two constructor names below:

```rust
// InstanceLink: remove args and new; retain template and instance_key.
pub type_args: Vec<ConcreteType>;
pub fn from_type_args(
    template: CallableTarget,
    type_args: Vec<ConcreteType>,
) -> Self;

// MonoDemand: remove args and new; retain template, site,
// instance_link and instance_key.
pub type_args: Vec<ConcreteType>;
pub fn from_type_args(
    template: CallableTarget,
    type_args: Vec<ConcreteType>,
    site: Span,
) -> Self;
```

Constructor renaming deliberately forces every existing authoring site to
migrate: the Rust vector type alone cannot distinguish old parameter vectors
from new substitution vectors. This is an incompatible semantic migration,
not a mechanical field rename. No argument-only compatibility constructor or
serde alias is retained. No new exported type or re-export is needed.

`InstanceLink::instance_key` continues to be the sole instance-key encoder,
using template identity and its new vector. Its existing recursive concrete
type encoding is retained; this proposal does not redesign its grammar.
`MonoDemand::instance_link` still removes only the diagnostic site.
`SymbolTable::install_instance` and its instance-key validation keep their
signatures and lifecycle authority.

`cranelisp_typecheck::instantiate_demands` keeps its exact public signature but
now consumes these substitution-based demands. Replay validates generic-vector
length against the selected template scheme, not value-call arity; existing
missing-module gap, stale-demand warning and hard invariant-error dispositions
remain. No new production reload caller is added by this wave.

Confirmed generated baseline: **four removed/four added substantive lines in
types** (two fields, two constructors). Existing marker-trait lines are
unchanged. Typecheck has a semantic contract update but no generated signature
delta; other library signatures and re-exports remain unchanged. The user
confirmed this actual result-context diff on 2026-09-07.

## 4. Producer/consumer map and one standalone wave

Source inspected on 2026-09-07; this is an implementation allocation, not a
claim that the proposed behavior has been measured.

| Crate visit | Existing seam | Work in this wave |
|---|---|---|
| Types | `lifecycle.rs`: `MonoDemand`, `InstanceLink`; `module.rs`: `install_instance` and lifecycle validation | Change the carrier contract and sole key input; migrate local fixtures; pin result-only distinction, same-substitution reuse and site-independent identity. |
| Typecheck | `program/mono_collect.rs`: ordinary/local/imported/dispatch-template collectors, function-value collectors and both drivers | Derive complete substitutions, admit resolved zero-argument calls, preserve full function-value results, normalize auto-curry, use the same identity for dedup and mint. |
| Typecheck, same visit | `traits/monomorphise.rs`: `monomorphise_call`, `instantiate_and_resolve`, inner parametric hops, synthetic templates, `register_mono_entry` | Substitute and recheck from the complete demand; carry its link to installation; retain defining-module scope and constraint checks. |
| Typecheck, same visit | `program/register/multi_sig.rs` selected-template drain; `infer.rs` selected sibling-template path | Feed the selected arm's complete substitutions into that same minter; do not derive an expected instance key from value arguments. |
| Typecheck, same visit | `form.rs`: `instantiate_demands` | Replay the new vector without requiring expression-map or source-span information; migrate stale/valid demand tests. |
| Backend | `cache/mod.rs`, `cache/serialize.rs` | Bump schema and evidence old-sidecar refusal/new-sidecar round-trip. No result inference, generic-key reconstruction or codegen-facade change. |
| Binary/int | `redefine.rs`: `immediate_callable_owner`; `process_form/macro_clause.rs`: `retain_checked_instances` | Preserve template-family ownership and copied links; migrate constructor-using fixtures. Neither production reader interprets the vector. |
| Integration evidence | `tests/shadowing_scope_lookup.rs` result-only closure repro; generic/currying/overload/cache suites | Establish behavioral and negative controls, then reconcile generated-name assertions and affected CLIF fixtures once behavior is settled. |

These are serial crate-shaped implementation visits inside **one wave**, with
no independently shippable argument-only/result-only halves. Types and the
backend schema increment belong to the same coordinated change-set; intermediate
carrier migration is not a release or green-gate claim. Independent review and
the user's generated-API confirmation follow the complete consumer migration.

The backend compiles `MonoExpr`/concrete lifecycle bodies by already-resolved
keys. Cache persists the `InstanceLink` inside `Life::Concrete.minted_from`.
Consequently **`CACHE_SCHEMA_VERSION` changes 25 → 26**: both the serialized
field and meaning of stored instance keys change. Old cache pairs are stale
and rebuilt, not translated. Platform ABI remains unchanged, as do heap
layouts, function calling conventions and platform interfaces. No Cargo
dependency or new cross-crate consumer edge is introduced.

The separate warm-cache compiler defect is not included or presumed repaired by
cache invalidation. It keeps its own failing test and attribution.

## 5. Alternatives and acceptance

Adding a required result type beside the existing parameter vector would also
distinguish these examples. It is a valid alternative, but retains the entire
value signature as the generic identity and requires replay to recover generic
substitutions from it. The recommended vector states those substitutions
directly, reusing the existing carriers without a second signature record.

Adding only a result-based suffix to generated names is insufficient: collection,
deduplication, function-value transport and replay currently lose the same fact.
Type-erased runtime generic closures would require different runtime/ownership
machinery and are unnecessary for the approved rank-1 language behavior.

The narrow falsifier is
`tests/shadowing_scope_lookup.rs::result_only_returned_closure_specializes_at_int_and_string`.
Acceptance also needs the annotated control, rejection of one let-bound closure
used at incompatible types, and rejection of an unresolved runtime use while
admitting its generic definition. Typecheck unit evidence should inspect the
two distinct concrete schemes, links, dispatches and slots—not merely successful
compilation—and cover nonzero-argument result-only variables, returned
containers, function values, partial applications, selected overload arms,
cross-module/nested hops, and replay without a live expression map. Existing
generic/trait/recursion tests protect argument-driven specialization.

Both API gates for this exact packet are satisfied. Implementation and evidence
status live in [SPRINT.md](../../sprints/SPRINT.md). Any additional public item or
language ambiguity returns to the user; this approval grants neither implicitly.
