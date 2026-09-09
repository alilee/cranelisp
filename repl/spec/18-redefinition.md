> [REPL specification index](index.md)

<a id="18-redefinition-semantics--dependent-recompilation-broken-symbols-and-the-frozen-world"></a>

## 18. Redefinition Semantics — Guarded Publication and Stable Identities [S121]

Redefinition is a later compilation cluster proposing a new definition for a
canonical name that is already committed in the live session. A second form for
the same canonical name inside one cluster remains an illegal redefinition
attempt under [`spec/05-definitions.md` §5.13](../../spec/05-definitions.md#513-definition-ordering).

The compiler MUST fully check a proposed replacement before changing live
state. It then applies the rule for that declaration class below. An ordinary
callable redefinition never causes dependent recompilation, creates a broken
symbol, installs a trap in a dependent, or retains an alternative callable
world. A rejected redefinition leaves the complete prior definition live and
leaves its backing source unchanged.

For a callable unit or whole-pair impl, **turn/publication atomicity** means that
the complete candidate MUST be validated and compiled before any part is
published. Failure leaves the complete prior unit live. Resolution and
introspection MUST NOT expose a partial candidate. Calls begun after
successful replacement confirmation MUST see the complete new unit, and after
publication completes no partial overload family or impl candidate remains.
This guarantee does not promise an all-old or all-new generation snapshot for
a computation already running or for calls occurring concurrently during
publication.

Live redefinition of one canonical name MUST preserve its declaration class.
Single-signature and multi-signature `defn` declarations are one callable class
governed by §§18.1–18.3; macros, nominal types, and traits are separate declaration
classes. A cross-class proposal is rejected atomically with the prior
declaration and backing source retained. Changing declaration class requires a
persisted-source reload/restart or a new canonical name. This restriction does
not change the distinct-canonical, same-spelling candidate rule in
[`spec/08-modules.md` §8.6.4](../../spec/08-modules.md#864-module-scope-candidate-registration).

The future-only macro and trait-default template rules (§18.4, §18.6)
deliberately leave already-generated definitions at their materialized bodies
until an explicit recompilation boundary; those definitions are neither stale
nor broken.

### 18.1 Callable Redefinition [Uncovered S121]

Declaration visibility is immutable during live redefinition of an existing
canonical callable. Changing `defn` to `defn-`, or `defn-` to `defn`, MUST be
rejected atomically with the prior definition and backing source retained. A
visibility change requires a persisted-source reload/restart or a new canonical
name.

With visibility unchanged, legality is determined by the callable's
**language type**: its fully resolved type scheme, compared modulo
alpha-renaming of bound type variables. Documentation and compiler-internal
realization details are not part of that language type.

- A replacement with the same language type and an ownership ABI compatible
  under §18.1.2 is legal with or without callers. It replaces the body and
  documentation and patches the callable's existing slot. Calls and callable
  values that already refer through that slot reach the replacement body on
  their next invocation. No dependent is re-typechecked and no redefinition
  report is printed beyond the ordinary definition confirmation. [Tested+Neg
  `tests/repl_redefinition.rs::redefine_body_only_stale_closure_late_binds_new_body`,
  `tests/repl_redefinition.rs::redefine_body_only_neg_no_cascade_report_no_dependent_recompiles`]
- A replacement with a different language type is legal only when the existing
  definition has no blocking dependent under §18.2. If any blocking dependent
  exists, the compiler MUST reject the replacement before publication, retain
  the prior definition and body, and emit a diagnostic containing these items
  in this order:

  1. the canonical target name;
  2. the old language type;
  3. the proposed language type;
  4. every direct blocking dependent after §18.2 normalization and
     deduplication, sorted by canonical name; and
  5. the remedy: retain the old type or introduce a new name.

  Transitive callers MUST NOT be included. The information and its order are
  normative; punctuation and layout are implementation-defined. No dependent
  is re-typechecked or marked broken.
- If the language type changes and there is no blocking dependent, the new
  definition replaces the old one atomically. Later resolution sees only the
  new language type and body.

Documentation is not part of a callable's language type. A documentation-only
edit therefore follows the same-type rule.

For a generic callable, including a member of an overload family, a
same-language-type body edit eagerly rematerializes every existing concrete
realization of that callable. The callable base, or its complete owning family
under §18.3, and all of those realizations form one publication candidate. The
complete candidate MUST validate and compile before publication. On success,
every existing realization slot is patched and future concrete demands use the
new generic template. No dependent caller is re-typechecked or recompiled. If
any part of the candidate fails, the complete prior base or family and all its
prior realizations remain live.

#### 18.1.2 Interim Ownership-ABI Compatibility Gate [Uncovered S121]

Ownership modes and `ModeSummary` remain compiler-internal information and are
not part of a callable's language type. They nevertheless form the ownership
ABI of an existing live Cranelisp callable slot. As an interim compatibility
gate, a live redefinition that would patch such a slot MUST preserve the
`ModeSummary`'s ABI-bearing ownership modes. Caller absence does not waive this
gate for a same-language-type replacement.

The gate applies to an ordinary function slot, each existing overload-member
slot, every existing concrete realization rematerialized with a generic base,
and every existing materialized impl-method slot. If any such slot would change
ownership ABI, the complete candidate unit MUST be rejected before publication;
the complete old unit, bodies, and slots remain live, and the backing source is
retained. No subset of an overload family, base-plus-realizations candidate, or
whole-pair impl is published.

The rejection diagnostic MUST state that the language type is unchanged,
identify the old and proposed ABI-bearing ownership modes from `ModeSummary`
that differ, and explain that the proposed replacement changes the ownership
ABI. This information is normative; diagnostic layout is
implementation-defined.

A caller-free language-type-changing replacement uses a fresh slot and MAY
change ownership mode. Reload or restart likewise recompiles persisted source
as one coherent unit and MAY accept a mode change; this live-slot compatibility
gate does not constrain that reconstruction. Compiler-private macro-clause
callables are excluded because their expansion entry point has the separate,
fixed `MacroClauseAbi`.

### 18.2 Blocking Dependents and Caller Discovery [Uncovered S121]

A **blocking dependent** is a committed, settled definition whose stored
`callees` contains the canonical target, whether the target occurs in direct
call position or as a first-class value. A definition becomes blocking as soon
as it has typechecked and settled; whether code generation has run is
irrelevant. Consequently, a checked definition such as
`(defn apply-f [x] (f x))` and one such as `(defn choose [] f)` both block a
language-type change to `f`.

Blocking dependents are derived on demand by reverse-scanning the committed
live symbol tables. They MUST NOT be maintained as a second persisted callers
index. Before comparison, a concrete specialization or realization is
normalized to the callable definition that owns it, so specialization does not
hide a dependency or count the same authored definition more than once.

For the §18.1 diagnostic only, a compiler-private macro-clause callable is
normalized to the canonical macro parent that owns the clause. The stored
`callees` edge remains on the internal clause callable and continues to prove a
direct blocking dependency. Multiple blocking clauses owned by the same macro
parent are reported once; clauses owned by different macro parents remain
distinct. The §18.1 normalization, deduplication, and canonical-name sort are
then applied to those macro-parent names. A compiler-generated clause name MUST
NOT appear in the diagnostic.

The target's own self-edge is excluded. Direct recursion therefore does not
make an otherwise unused callable its own blocker. No other edge is excluded:
mutual recursion, an ordinary sibling definition, a checked-but-not-codegened
definition, and a definition that stores the callable as a value are all
blocking dependents. The test is direct: because a type-changing replacement
is refused at the first blocking edge, there is no transitive recompilation or
cascade to calculate.

Transient top-level expression results are not definitions and do not create a
stored caller edge. This rule does not introduce runtime reference counting,
live-value inspection, or another dynamic admission check.

### 18.3 Multi-Signature Callable Redefinition [Uncovered S121]

One multi-signature `defn` is one **overload family**. Its language type is the
complete set of clause signatures:

- Editing clause bodies, editing documentation, or reordering clauses while
  preserving that signature set is a same-type redefinition.
- Adding or removing a signature, or changing any signature, is a
  language-type-changing redefinition of the whole family.

A family type change is legal only when no member has a blocking dependent
outside the family. The reverse scan normalizes a dependent on a concrete
member realization to that member and then to its owning family. Self-edges and
sibling calls whose caller and callee belong to the same family do not block
the family replacement; every external call or value use of any member does.
For a rejected family type change, the §18.1 diagnostic's blocker list is the
union of direct external blockers across every member, normalized, deduplicated
and sorted by canonical name. It excludes transitive callers.

The complete family candidate is validated and compiled before it is published
as one unit under the turn/publication atomicity defined above. A rejection
retains the complete prior family; it MUST NOT publish a subset of new clauses,
remove an old clause, or mix generations.

### 18.4 Macro Redefinition [Uncovered S121]

Declaration visibility is likewise immutable during live macro redefinition.
Changing `defmacro` to `defmacro-`, or `defmacro-` to `defmacro`, MUST be
rejected atomically with the prior macro unit and backing source retained. A
visibility change requires a persisted-source reload/restart or a new canonical
name.

Macro invocations are expanded before HM typechecking and do not become stable
runtime caller edges. With visibility unchanged, a successful atomic
`defmacro` redefinition therefore affects **future expansions only**:

- definitions that were already expanded and compiled keep their existing
  expanded bodies until those authored forms are typechecked again;
- subsequent macro invocations use the new macro definition; and
- reload and restart re-expand persisted authored macro calls using the macro
  definition current at that compilation.

The macro parent, active clauses, and defining-module generated realizations
still publish atomically at the checkpoint defined by
[`spec/09-macros.md` §9.12.1](../../spec/09-macros.md#9121-defmacro-compilation-checkpoints).
A failed redefinition leaves the prior macro unit available. Changing macro
arity or clause shape changes which future invocations are accepted but does
not invalidate already-expanded definitions.

Calls and first-class value uses **inside a macro clause body** are ordinary
stored `callees`. They participate in §18.2 when an ordinary callable they use
is proposed with a new language type. Only the source-level invocation of the
macro disappears at expansion and creates no durable macro-use edge.

### 18.5 Type Declaration Re-establishment [Uncovered S121]

A committed nominal `deftype` may be re-established under the same canonical
name only when its runtime and naming structure is identical. Structural
identity requires all of the following:

- the same visibility and product-versus-sum shape;
- alpha-equivalent declared type parameters;
- for a sum, the same constructors in the same order, hence the same tags, with
  the same payload arities and alpha-equivalent payload types; and
- for a product, the same fields in the same order, with the same field and
  generated-accessor names and alpha-equivalent field types.

Type and constructor docstrings are non-structural and update live
documentation. A sum constructor's positional payload labels are also
non-structural: payload extraction is positional, pattern variables are bound
by `match`, and no callable accessor is created. Renaming declaration labels
while preserving payload order and types is legal.

Every other same-name `deftype` change is rejected atomically regardless of
callers. The prior type, constructors, accessors, values and documentation
remain live after rejection. A structurally different nominal type requires a
new name; the implementation MUST NOT reinterpret existing values under an
unversioned changed layout.

### 18.6 Trait Declaration Re-establishment [Uncovered S121]

A committed trait's **interface is immutable**. Re-establishment under the same
canonical name requires equivalent visibility, conventional-versus-
higher-kinded head shape, method set, required-versus-default classification,
method arities, parameter and result types, and constraints. Renaming bound type
variables is permitted when the complete interface remains alpha-equivalent.

Trait and method docstrings are not part of the interface and update live
documentation. A default method's body is a per-impl template, not part of the
interface. A same-interface replacement of that body affects future
realizations only: existing impl methods keep their materialized bodies until
an explicit conforming re-`impl`, reload, or restart materializes the latest
template. Existing impls that explicitly override the method remain governed
by their own bodies.

An interface-changing re-`deftrait` is rejected atomically regardless of
callers or existing impls. The prior trait declaration, method declarations,
impls and dispatch remain live. A different interface requires a new trait
name; the implementation MUST NOT reinterpret existing impls or checked trait
constraints under an unversioned changed interface.

### 18.7 Impl Redefinition — Re-entering an `impl` [S115]

A trait implementation is replaced at whole `(trait, target-type)` pair grain.
A re-`impl` MUST conform completely to the committed trait interface. Once the
whole candidate succeeds, subsequent dispatch for that pair uses its new
method bodies. An omitted default method is materialized from the trait's
current default template. [Tested+Neg
`tests/impl_redefinition_dispatch.rs::reimpl_same_type_hot_reloads_dispatch`,
`tests/impl_redefinition_dispatch.rs::reimpl_omitting_a_method_reverts_it_to_the_trait_default`,
`tests/impl_redefinition_dispatch.rs::reimpl_default_then_override_then_default_cycles`]

A conforming re-`impl` preserves every materialized method's language type. A
candidate that would change one of those types is rejected as non-conforming;
it does not enter the ordinary-callable no-dependent path. Each existing
materialized method remains subject to the interim ownership-ABI compatibility
gate in §18.1.2.

Replacement uses the turn/publication atomicity defined above. The complete
impl candidate is validated and compiled before publication. If any method
fails conformance or a required method is missing, the complete candidate is
rejected and every method of the prior impl continues dispatching. No method
from the failed candidate becomes visible.
[Tested+Neg
`tests/impl_redefinition_dispatch.rs::reimpl_neg_type_changing_body_rejected_and_prior_impl_keeps_dispatching`]

The ordinary impl confirmation line is unchanged and carries no `redefined`
marker. `/info`, `/list`, and every other impl enumeration MUST show exactly one
current impl for the pair, not its replacement history.

### 18.8 Persistence and Reload [Uncovered S121]

The backing file contains only the latest **successful** source for each
definition or declaration under §15.6. A rejected redefinition is never
written. Reload and restart compile that current authored source; they do not
replay the interactive edit history and do not restore obsolete callable
generations, broken-symbol state, cascade reports, or trap stubs.

Two template boundaries qualify §15.4's round-trip rule:

- persisted macro invocations are re-expanded with the macro definition
  current at reload or restart, so an already-compiled pre-redefinition
  expansion is not promised to survive source reconstruction; and
- an impl that omitted a default method re-materializes that method from the
  trait default body current at reload or restart, so a historical generated
  default body is not promised to survive source reconstruction.

These are source-reconstruction rules, not hidden runtime updates. In the live
session, an existing expanded definition or materialized default method changes
only at the explicit future-typecheck or re-`impl` boundaries stated above.
