# Uniform concrete-signature executable identity

**Uniform identity, readable syntax and exact types API approved (2026-09-10);
implemented and generated baseline confirmed.** The agreed design uses
family-qualified, full-concrete-signature executable identity for ordinary
concrete functions, concrete overload arms and generic realizations.
Withdraw `PreserveAbiFrom` as
the recommended solution to reorder: stable keys let the existing `PreserveAbi`
transaction preserve slots and owners without cross-key publication machinery.

## Ownership clarification (2026-09-10)

This is a symbol-table/types identity correction. Types derives and validates
realization keys and owns their slot/publication relationship. Backend consumes
resolved table targets and GOT slots; it does not decide which realization a
name denotes. Its private native labels exist, but are not that semantic
identity. No backend redesign, new identity wrapper or changed GOT/call ABI is
proposed.

Uniform identity does not require flattening all declaration storage into new
entries. Ordinary authored bindings remain named bindings, and concrete overload
arms remain selected within their owning roster. The canonical concrete key can
be derived uniformly from their owner and settled signature. Generic instances
need that key as their actual separate storage key because a template owns many
realizations. This is where removing ordinal-dependent identity fixes reorder.

The backend's private label adapters only need to remain consistent with the
updated table data. Renaming every ordinary/overload native symbol into the
readable semantic spelling is **not** a prerequisite and is not authorized by
this packet. Existing private native labels may remain where their declaration,
lookup and self-call consumers agree; they must not become a competing authority
for table realization identity.

## Identity and uniqueness

Keep three concepts distinct:

- **Authored binding:** the name users write, export, redefine and inspect, such
  as `user/f`. An overloaded binding owns its whole clause family.
- **Declaration selector:** today's `CallableTarget` selects a binding or a
  generation-local arm for checking and compilation. An old ordinal must still
  be matched to the unique new arm by the existing language-signature comparison.
- **Executable identity:** authored owner plus the complete concrete callable
  type, including arity, ordered parameters and result. No source-order ordinal,
  inference variable ID, parameter name or ownership-analysis mode belongs here.

**Approved readable identity syntax:**

```text
( symbol [ ParamType* ] ReturnType )
Type ::= Int | String | Bool | ... | (Fn [Type*] Type)
```

`symbol` is the fully qualified canonical authored symbol. Parameter and return
types are concrete and recursive; `...` includes the language's existing Float,
nominal and parameterized types, using their fully qualified canonical type
identities. Nested function types use the ordinary existing `(Fn [Type*] Type)`
syntax. An empty parameter list represents a nullary executable. For example:

```text
( user/f [ primitives/Int primitives/Int ] primitives/Int )
( user/maker [] (Fn [primitives/String] primitives/String) )
```

This is executable-identity rendering, not a new language expression grammar.
The subsequent user approval includes the exact Rust API below and its source
migration. The user also confirmed the generated identity baseline; no particular
native-object symbol encoding or wholesale backend renaming is approved.

The earlier `f$Int+Int` example is not the selected grammar. Today's suffix
in `InstanceLink::instance_key` is **generic substitutions**, not parameters.
The legal clauses `a -> Int` and `(a, a) -> Int` both specialize with `[Int]`;
removing only `__armN` would collide. A nullary generic can also return different
concrete function types, so result context must participate in the key.

Use the full recursive `ConcreteType` structure: nominal types and their type
arguments retain fully qualified identities; function parameters and results
retain their structure. The approved readable spelling represents that identity.
If a native toolchain needs a different symbol representation, its deterministic,
unambiguous encoding remains a separate implementation design detail; no
particular escape, framing or alternative readable syntax is approved here.

[Language §5.1.2](../../spec/05-definitions.md) rejects same-arity clauses whose
written parameter signatures can unify, including constrained generic overlap;
different arities are distinguishable. Thus two legal arms cannot both own the
same concrete argument tuple. Including the result also distinguishes legal
result-context realizations of one generic. Constraints still govern template
admission and instance checking; they are not additional executable identity
when owner and full concrete type already identify the legal realization.
Alpha-equivalence and constraint identity remain necessary for matching old and
staged template schemes, using the existing integration comparand.

## Evidence and alternatives

Existing-binary probes in isolated temporary directories are recorded in
`/tmp/s122-signature-identity-probes.json`, using the S122 working-tree binary
against checkpoint `dc78ddbe` (not a pristine checkpoint build):

| Probe | Observation |
|---|---|
| `f ([:a x] 7) ([:a x :a y] 42)` | Accepted; one- and two-argument calls return 7 and 42. |
| Generic and Int-specific same-arity clauses | Definition rejected for overlapping signatures. |
| Nullary `maker` returning `(fn [x] x)` | `(maker)` specializes for Int and String results; calls return 7 and `"ok"`. |

These establish the discriminator requirements, not execution of the proposed
identity scheme. The permanent generic reorder RED/control remains the
acceptance subject in [repl_redefinition.rs](../../tests/repl_redefinition.rs).

| Option | Assessment |
|---|---|
| Keep ordinal keys, add `PreserveAbiFrom` | Smaller immediate types publication extension, but adds mapping/permutation/collision machinery and requires family-edge repair when old keys disappear. Addresses the consequence of unstable names. |
| Stable template-signature key plus substitutions | Can survive reorder, but needs alpha-canonical generic variables, constraints and substitution ordering in executable naming. Still gives ordinary concrete functions a different naming model. |
| Full concrete signature, overload/generic only | Removes the immediate reorder problem, but does not satisfy the user's uniform naming intent. |
| Full concrete signature for all three language callable classes | Recommended. Reuses concrete type identity, keeps same-key publication, and gives all realized functions one naming rule. Requires a coordinated identity/naming migration rather than one publication variant. |

## Bounded migration and public API forecast

Source inspected: [types lifecycle](../../crates/cranelisp-types/src/lifecycle.rs),
[types table](../../crates/cranelisp-types/src/module.rs), typecheck demand
construction/monomorphisation, [worker](../../src/worker.rs),
[redefinition](../../src/redefine.rs), and backend label declaration, self-call
classification and cache object lookup. The generic key/constructor census
covers 18 Rust source/test files; that is not the whole uniform migration.
Backend has three production label consumers in its library, `fn_compiler` and
cache loader. They require compatibility verification against changed table keys,
not an assumed wholesale label rewrite.

Prefer **deriving from the settled signature supplied at the boundary** over
adding loose duplicate `signature` fields to both `InstanceLink` and `MonoDemand`.
Typecheck has the settled use/signature at minting; captured live bindings and
staged templates provide integration's inputs; types installation/validation
already has the instance scheme; backend has the selected target and table.
Do not duplicate substitution or signature canonicalization in integration.
The exact common derivation below applies a demand's substitutions to its
selected template scheme without a second integration-side implementation.

## Exact public API packet — approved 2026-09-10

The shared derivation lives in `cranelisp-types`, beside `InstanceLink` and
`MonoDemand`, re-exported at the crate root. No public table query or additional
stored signature field is needed. Approved Rust contracts:

```rust
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum InstanceKeyError {
    ArgumentCount { expected: usize, actual: usize },
    NotFunction,
    NotConcrete(NotConcrete),
    UnsupportedTemplate,
}

pub fn concrete_callable_key(
    owner: &FQSymbol,
    signature: &ConcreteType,
) -> Result<Symbol, InstanceKeyError>;

impl InstanceLink {
    pub fn instance_key(
        &self,
        template_scheme: &Scheme,
    ) -> Result<Symbol, InstanceKeyError>;
}

impl MonoDemand {
    pub fn instance_key(
        &self,
        template_scheme: &Scheme,
    ) -> Result<Symbol, InstanceKeyError>;
}
```

`InstanceKeyError` implements `Display` and `std::error::Error`; no additional
public conversions, accessors or serialization implementations are proposed.
The existing context-free `instance_key(&self) -> Symbol` methods are replaced,
not retained as competing key rules. The existing `from_type_args` constructors,
`MonoDemand::instance_link`, and all public carrier fields remain unchanged.

**Settled-signature helper.** `concrete_callable_key` accepts a full
`ConcreteType::Fn(parameters, result)` and returns the approved readable identity
using the supplied canonical authored owner. A non-function `ConcreteType`
returns `NotFunction`. It performs no lookup, allocation of GOT slots, trait
selection or publication. Fully qualified nominal identities and recursive
parameterized/function types are retained. Rendering uses ordinary compact
parentheses/brackets, one space between items, and `[]` for no parameters, for
example `(user/f [primitives/Int primitives/Int] primitives/Int)`. This is the
agreed syntax with deterministic whitespace, not another language grammar.

**Template-context methods.** The caller supplies the authoritative scheme of
that exact selected template in its intended generation, not the instance's
already-specialized scheme. The methods share one private derivation:

1. Accept a `Binding` or `OverloadArm` template; a macro clause or unsupported
   target returns `UnsupportedTemplate`. The authored owner is the binding FQ
   or overload family's FQ, never an ordinal-bearing label.
2. Enumerate quantified variables occurring in `scheme.ty` in first-occurrence
   order (parameters then result; repeated occurrences once), using existing
   `collect_var_ids_ordered` and filtering by `scheme.type_vars`, exactly as the
   current demand producer does. Reject a vector-length mismatch with
   `ArgumentCount`; unused quantified variables do not acquire new arguments.
3. Apply the complete concrete substitutions with the existing types-owned
   `apply` operation, including its higher-kinded-head handling. Convert the
   result through `ConcreteType::from_type`; residual variables/heads return
   `NotConcrete`. A concrete non-function result returns `NotFunction`.
4. Delegate to `concrete_callable_key`. `MonoDemand` delegates through its
   `InstanceLink`; diagnostic `site` never affects the key.

This is pure signature projection, not a second instantiation engine: no fresh
inference IDs, unification state, constraint verification or body checks are
introduced. Typecheck retains those responsibilities. Trait constraints still
must pass the existing check before an instance can be installed. These helpers
do not certify that a caller-supplied scheme belongs to the named template;
callers obtain it by the existing keyed template lookup. Typecheck uses the same
quantified-variable ordering, not a second locally maintained order rule.

**Errors and validation.** The helpers never silently omit arguments or fall
back to an ordinal key. A stale reload demand continues through the existing
warning/decline policy; its context-aware key failure does not authorize a
fallback identity. Typecheck attributes malformed signature errors to the
existing demand span and retains the existing Gap/invariant distinction.
A same-language-type redefinition with failed correspondence/derivation still
rejects the entire candidate. Types installation and restored-state validation
format the actual settled instance scheme through the same helper, using the
owner recorded by `InstanceLink`; `InstanceKeyMismatch` remains the existing
key-versus-payload refusal. Typecheck checks agreement between the demand-derived
key and realized signature before handing the body to installation.

**Consumer sequencing.** Integration captures the actual prior key and old
link while the old table exists. It matches the staged arm first, supplies that
arm's staged scheme to the new demand key method, and then masks/rematerializes
using those explicit keys. It never asks the new roster to interpret an old
ordinal. The captured prior key remains available for decline/retirement even
when no staged template survives. This is private preparation data, not a
persistent registry. The schema context for a foreign template comes from the
existing table world before any replaced data is dropped; no name scan or
rendered-type parsing is introduced.

Backend already has `CallableTarget` plus table/arm data at declaration and
cache lookup. The current private label helper copies a direct binding's key,
or generates an internal overload/macro label. Generic-instance storage-key
changes therefore flow through that adapter already. Verify native declaration,
cache lookup and self-call recognition remain coherent, and adapt only a
consumer that still relies on the retired instance-key spelling. There is no
mandatory rewrite of ordinary concrete or overload native labels, no new public
backend query and no replacement of backend selectors or owner-map signatures.

**API/baseline accounting.** This packet changes two existing public method
signatures and their return types, and adds one public function plus one
non-exhaustive error enum and its stated standard trait implementations in the
types baseline. Existing method calls must supply context and handle errors;
this is a source-breaking Rust API change. No other public delta is proposed.
The user confirmed the generated additions/removals on 2026-09-10: types-only
**+20 / −2**, with the other six guarded crate baselines unchanged. This
confirmation is separate from ACT0955 format contraction. No public function or
error is added to typecheck, backend or Binary/int. No `PreserveAbiFrom` addition
and no field/constructor changes are authorized by this packet.

Types must use the same key in instance installation and lifecycle validation.
Typecheck and integration must use it in demand matching, deduplication, masking
and rematerialized lookup. On overload reorder, integration remaps the old
selector before replay, but the instance key stays fixed. Existing stored
callee/ApplyRef/VarRef references keep resolving to that key, so the cross-key
proposal's special family-edge repair is unnecessary for this correction.
Language-type-changing candidates that produce a different concrete key retain
the existing caller-free `ChangeAbi`/retirement policy; no caller recompilation
or weaker ownership-ABI gate is introduced.

The uniform key is types-owned semantic identity, not an instruction to rename
authored declarations or every native label. Existing GOT-indirect dispatch and
whole-family preparation/compilation/publication remain; displaced owners are
retained through the same transaction.

Canonical persisted instance keys change; emitted generic-instance labels that
copy those keys change with them. Use one coherent
semantic cache-version invalidation for old `.meta`/`.o` pairs; do not rely only
on build identity to distinguish dirty development binaries. No serialized
shape addition is needed by the preferred context-bearing approach, but the
cache version value and its frozen test change. The exact types API is approved; its generated baseline changes
are also user-confirmed (2026-09-10);
no new crate dependency, runtime calling convention, heap layout or platform
ABI is proposed. No new backend public query is needed: the existing label-helper consumers
already have the selected target and its table.

Externally fixed platform exports and native entrypoint labels remain ABI
contracts, not language overload names. Macro clause selectors encode ordered
pattern matching rather than type overloads and retain their separate identity;
renaming that protocol is outside this proposal. Compiler-generated helper and
FFI labels may adapt a language executable identity without changing their
external contract. These boundaries do not justify three different naming rules
for the ordinary/concrete-overload/generic language bodies assessed here.

## Verification boundary

Keep the existing reorder RED/control and ABI-rejection controls. Add focused
key controls for repeated-variable arities, nested/result-only types, nominal
identity, alpha-renamed templates, and same-key reorder. Exercise ordinary,
overloaded and generic bodies through JIT and object/cache lookup, including
self-call behavior, old-cache refusal, whole-family rejection and unchanged
caller slots/owners. Reuse existing acceptance fixtures; no broad new framework
or six-way Cartesian test matrix is implied. No implementation or builds were
performed during this assessment.


## Types producer delivery — 2026-09-10

The approved API is implemented in types lifecycle and re-exported at the crate
root. Key type rendering delegates to the existing qualified `render_type`;
installation and restored validation share the actual settled-scheme projection.
No carrier fields, serialization traits or other public operations were added.
The producer-only suite passes 279 module tests and four external tests. A
result-omission plant fails the independent nested-result distinction test and
is restored. At that producer checkpoint, typecheck and integration key callers, backend
cache semantics, and baseline confirmation were serial downstream obligations.
Those identity obligations are now complete, including the user
confirmation of the generated types-only +20/−2 diff; Phase 5 continues.
Source/build evidence is handed to the sprint;
no source outside types was changed by this producer slice.


## Callable class transitions within the existing contract

REPL §18.1 and §18.3 already authorize a caller-free language-type-changing
replacement that adds or removes signatures. A change between the internal
`Decl::Overloaded` roster and an ordinary `Decl::Callable` with `Plain` origin
is therefore admitted by the types publisher after integration's semantic gate.
This does not admit macro, trait, primitive or constructor origin changes.
Cross-class `PreserveAbi` refuses; existing `ChangeAbi` or the states' derived
slot moves retire old claims, mint fresh replacement slots and return displaced
owners through the same atomic candidate. Declined generic realizations retain
their separate explicit absent-key retirement decisions. No public API, stored
field, baseline delta or new language permission is introduced by correcting
this private collision check.
