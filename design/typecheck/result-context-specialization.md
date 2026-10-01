# Result-context specialization

Owner: `design`, narrow-deployed to `cranelisp-typecheck`. Reader: the crate's
implementer and independent reviewer. Status: implementation design under the
user-approved [instance identity funnel](../arch/interfaces.md#instance-identity-funnel)
(result-context approval 2026-09-07), implemented in the typecheck crate. The
current scheme-bearing key contract is the
[full-signature identity design](../arch/s122-overload-reorder-publication.md).
Whole-wave acceptance remains subject to the sprint's independent and cross-crate evidence gates.
Approval and wave readiness are recorded in the [sprint ledger](../../sprints/archive/sprint-122.md);
the archived approval record is not the current gate state.

This elaborates [monomorphisation.md](monomorphisation.md) under
[spec §3.3.4 and §3.6.3–§3.6.4](../../spec/03-types.md). The subsystem document records complete substitution identity and map-free replay. No additional
public item, compiler pass, persistent state, or runtime mechanism is proposed.

## Interior collaboration

The existing collector, mint/recheck engine and instance publisher remain the
three responsibilities. Complete substitutions, rather than value parameters,
are the data passed between them (Principles 7 and 26).

```text
selected template + exact checked scheme + settled use type
                         │
                 private demand derivation
                         │
                    MonoDemand
                         │
           reconstruct complete concrete signature
                         │
          constraints + defining-scope body recheck
                         │
       same InstanceLink → install_instance → dispatch
                         ↑
            replay enters with MonoDemand directly
```

The defining identity is the recorded `CallableTarget`, including an overload
arm when selected. A source name is not a substitute for that target. For an
unpublished local body, collection and minting use the ledger's exact checked
scheme together with its body, not a declaration's pre-settlement snapshot.
Published/imported templates use their owned scheme. No stage independently
regeneralizes a different scheme to interpret an already-derived vector.

## Derivation and use shapes

One crate-private derivation reconciles a fresh instantiation of the selected
scheme with the complete settled function type of the use. It retains the
original-to-fresh variable correspondence, using the existing unification and
substitution operations rather than a second structural type matcher.

All producers supply one of these normalized shapes:

| Use | Function type reconciled with the selected scheme |
|---|---|
| Ordinary application | `Fn(supplied argument types, application result type)` |
| Function reference used as a value | The reference's entire `Fn` type |
| Auto-curry | `Fn(supplied prefix ++ residual closure parameters, residual closure result)` |

The typed auto-curry verdict chooses the third row. Merely observing a `Fn`
result never chooses it: `g : Fn([], Fn([a], Int))` is an ordinary nullary
application returning a function, not an incomplete application of `g`.

The ordering rule is exactly the approved packet's: first structural occurrence
in `scheme.ty`, using `collect_var_ids_ordered`, filtered by generalized-variable
membership. The same private ordering operation serves derivation and replay.
For `forall a. Fn([a, a], a)`, `[Int]` represents the substitution despite two
value parameters. For `forall a b. Fn([a], Fn([b], a))`, `[Int, String]` records
both the argument choice and the result-only choice. Renaming variable IDs does
not change either position. Higher-kinded heads retain the existing resolved
constructor representation specified by the packet.

Extract the substituted fresh variables only after reconciling the complete
shape. Existing `ConcreteType` conversion is the demand-admission boundary;
there is no partial demand or argument-only fallback. Collection does not
publish speculative identities while a use remains unresolved. Generic bodies
retain such sites for concrete recheck; codegen-reaching unresolved uses remain
the existing located ambiguity error. Remove the nullary-call exclusion: a
fully resolved substitution is the criterion, not nonempty value arguments.

Nested-body consumers use the expression and resolution maps captured by that
body's recheck. They must not infer result information from the restored outer
map at an equal span. Preserve existing recheck substitution isolation: creating
an inner instance must not specialize the enclosing generic definition globally.
Real source sites remain diagnostic locations for function values too; they no
longer masquerade as synthetic sites to suppress incorrect return pinning.

## Minting, reuse and replay

The mint engine receives the complete demand and matching template. Reconstruct
its function signature by binding fresh representatives of the ordered generic
variables to `type_args`; verify vector length before any paired iteration.
The existing original-to-fresh mapping also drives constraint verification, so
foreign inference IDs cannot alias caller IDs. Recheck authored bodies in their
defining scope; synthesized constructors/accessors derive their concrete body
from the reconstructed signature through their existing synthesis path.

Carry the demand's `InstanceLink` through naming, recursion, deduplication and
publication. `register_mono_entry` does not reconstruct it from the finished
body's parameter list. The body signature still supplies parameter/result
types and the concrete codegen view; it does not supply generic identity.
Self-recursive calls reuse the active instance only when their selected target
and complete substitution agree. Other inner calls create ordinary demands.
Neither path synthesizes a name from value argument types.

Ordinary source inference keeps its existing constraint propagation, including
overload return back-flow. The minter no longer uses a span lookup after key
creation to discover a missing generic choice. Call/function-value/curry
normalization supplies that information before the key exists.

Replay seeds the same engine without live expression maps. Its synthetic site
prevents span-sidecar writes, not result specialization. Generic-vector length
is checked against the selected scheme, not runtime arity. Existing missing-home
gaps, per-root stale-demand warnings and hard invariant failures keep their
dispositions; a rejected root does not install a partial instance. Repeated
valid demands reuse the existing concrete instance and slot. No reload caller
or rollback mechanism is introduced here.

## One coherent crate visit

Source inspected on 2026-09-07. These are existing ownership seams, not required
new private APIs; the implementation may consolidate private plumbing within
these responsibilities.

| Source under `crates/cranelisp-typecheck/src/` | Complete migration responsibility |
|---|---|
| `program/mono_collect.rs` | Local/imported/constrained/dispatch-template collectors, function-value collection, checked-body scheme selection, both drivers and replay roots use complete demands. Preserve return types currently checked then discarded by function-value collection. |
| `traits/monomorphise.rs` | Derivation/reconstruction, constraint mapping, authored/synthetic mint paths and publication share the link. Nested hops, `record_self_recursion_dispatch` and `resolve_inner_constrained_calls` stop using argument-derived `build_mangled_name` comparisons. |
| `program/register/multi_sig.rs` | Selected-template drain derives the selected arm's demand before dedup; no separately assembled argument-based expected key. Unsettled generic uses remain deferred. |
| `infer.rs` | Selected sibling-template path consumes the same derivation and minter, retaining the existing settled-window behavior. |
| `form.rs` | Map-free replay and its rustdoc describe complete substitutions; the public signature stays unchanged. |

Retire private argument-only instance-name composition where it no longer has
consumers. Do not conflate that cleanup with overload-member naming, which the
approved packet leaves unchanged. Reconcile affected generated-name assertions
only after checking the concrete schemes and links; a renamed golden is not
proof that result context reached the instance.

## Evidence delta for QA

The permanent external falsifier remains
`tests/shadowing_scope_lookup.rs::result_only_returned_closure_specializes_at_int_and_string`.
Unit evidence must distinguish complete concrete schemes, links, dispatches and
slots for identical value arguments with different results; repeated identical
substitutions must reuse the instance. Additional discriminators are structural
variable order under alpha-renaming/repetition/HKT; full function-value versus
auto-curry result shapes; selected overload arms; nested/imported rechecks; and
map-free replay with length/stale controls. Existing argument-driven trait and
recursion tests protect the preserved behavior. QA chooses the smallest useful
allocation across these risks, not a cartesian matrix.

The separate warm-cache defect is neither repaired nor closed by the approved
cache schema change. Typecheck module evidence covers canonical variable order, concrete schemes and
links, distinct slots, repeated substitution reuse, consumer dispatch targets,
function-value/curry/selected-arm paths, imported nested hops and map-free replay.
Execution results and mutation proofs are reported through the sprint handoff.
