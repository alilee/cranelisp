---
number: 0863
target: /dev
filed_by: /dev
filed_at: 2026-07-24
sprint_filed: 117
refers_to: design/int/s117-conformance-recovery.md §1.1.2 and §6;
  design/arch/bounded-contexts.md §6; design/arch/fixmes/0800-def-macro-expansion-leaks-internal-thunk-name-and-blocks-call.md;
  tests/spec_11_stdlib.rs::def_definition_echo_lists_every_emitted_definition_in_order;
  tests/spec_11_stdlib.rs::def_info_and_sig_describe_macro_while_bare_use_expands_value
status: open
target_sprint: 121
---

# Macro checkpoints and ordered definition results

## Issue

DF-1 and DF-2 originally assumed that the REPL should project one public value
subject from an entered macro invocation. That premise was corrected on
2026-09-05: `def` emits a backing `defn` and a zero-argument `defmacro`; both
are real definitions, and the macro remains a macro in `/info` and `/sig`.
Only invoking the bare macro exposes the type of its expansion result.

The Sprint 117 projection attempt was also architecturally unsound:

- projection could fail after the compiler had published the successful
  cluster, violating the all-or-nothing turn contract;
- the entered form's public subject was reconstructed by an ambient
  post-publication scan rather than carried as exact expansion provenance;
- the parallel presentation map introduced a second lifecycle store that
  could diverge from canonical introspection.

The rejected implementation was removed. The remaining defect is the singular
definition result: it reports `user/n-def` but drops the second emitted
definition, `user/n ; defmacro`. The correction is an ordered batch, not a
selected subject or inferred presentation type.

## Approved resolution (2026-09-03)

The Sprint 117 cluster-wide transaction proposal is superseded. A `defmacro`
is a source-ordered, module-local compile-time checkpoint:

1. Build and typecheck the parent and every clause, close the complete
   expansion-time dependency and generated-realization closure, and finish
   codegen for that closure before publishing any part of the macro.
2. Publish the parent, all clauses, the defining-module generated-realization
   rows in that closure, and their compiled owners together through the
   existing prepared-commit path and `SymbolTable::publish_compiled_staged`.
   On a shrinking redefinition, that same call also retires the exact surplus
   clause rows through explicit absent-key `ChangeAbi` decisions; omission
   alone never removes a binding.
3. Only after that publication may a later form invoke the macro. A failed
   checkpoint leaves the previously committed macro unchanged; a successful
   checkpoint remains committed even if later expansion, typecheck, or codegen
   fails. In particular, the later §18 dependent cure is not part of checkpoint
   success and cannot roll the macro back if it later refuses.
4. A dependency module is its own publication domain. It may finish and
   publish independently while the defining module waits, and is not absorbed
   into the defining module's transaction.
5. The fully expanded **non-macro** forms still enter one `check_forms` HM
   cluster. That cluster remains all-or-nothing.

There is consequently no cross-module publication set, cluster-wide
`TurnCheckWorld`, unpublished-candidate invocation, temporary/reserved-GOT
candidate stack, or separate macro observation fence. A macro invocation reads
only a committed macro. The existing per-module table cadence provides the
read/write boundary; no new public item or generated baseline line,
cache-schema field, backend contract, or platform interface is required. The
existing `ChangeAbi` decision's approved semantics expand without changing its
shape or either publication method's signature.

The surplus-clause hard stop is resolved at the same boundary. Int derives an
old clause row from the typed `(group, clause_index)` producer identity and the
canonical key constructor, never by parsing a generated-name prefix. For an
old count `N` and staged count `M < N`, only indices `M..N` whose live bindings
are private, slotted `CallableOrigin::MacroClause` rows for that parent may be
submitted for absent-key retirement. The table plans those removals beside the
parent and active replacements, validates the complete candidate, and commits
all or none. Each removed row produces the existing publication record with a
prior slot, no published slot and its displaced owner; its GOT pointer remains
frozen and its old slot is an ABI-changing tombstone. Cache validation checks
the parent active-set and stored clause rows in both directions, so a missing,
surplus or mismatched clause makes the cache stale. A later clause-set growth
therefore creates the returned indices on fresh slots rather than reclaiming a
published generation.

REPL result collection is stack-owned and separate from compilation state.
`TurnDefinitions` records exact canonical identities in emitted order. Macro
rows become published at their checkpoints; ordinary rows remain pending until
the HM/codegen publication succeeds. `EvalResult::Definitions` carries all
published identities to the existing per-binding formatter. There is no
`EnteredMacroProvenance`, `PreparedPresentation`, `presentation_scheme`, dry
macro typecheck, ambient scan, or parallel presentation map.

The implementation needs focused coverage for:

- failure at every macro-checkpoint preparation and backend boundary, proving
  no partial parent, clause, owner, or GOT update survives;
- a successful macro checkpoint followed by a failed later form, proving the
  macro remains available while the non-macro cluster publishes nothing;
- failed macro redefinition, proving the earlier committed macro remains;
- independent dependency-module publication and defining-module retry;
- private emitted definitions;
- zero, one, and multiple emitted definitions in source order;
- dependency retry without duplication or reordering;
- direct ordinary `defmacro` controls; and
- `def` echo listing both bindings, `/info` and `/sig` retaining `defmacro`,
  and bare invocation producing the runtime value.

## Superseded history

The user approved deferral on 2026-07-24 because the local W3c formatter fix
could not provide honest publication atomicity. Sprint 117 then proposed one
prepared transaction spanning Pass 1, dependency modules, macro execution, the
non-macro HM cluster, code owners, GOT cells, and presentation. That proposal
introduced `PreparedMacroTurn` and motivated the seven-step cluster-wide design
formerly recorded here.

On 2026-09-03 the user chose the smaller semantic boundary above: successful
`defmacro` forms are durable source-order checkpoints, while non-macro HM
checking remains cluster-atomic. This section preserves why the former design
existed; it is not implementation authority. The Sprint 117 interior document
is likewise historical wherever it requires the superseded global transaction.

## Context

Binary bounded context §6 and `design/arch/macro-availability-model.md` are
the current architecture authority. The integration owner must reconcile the
interior Sprint 117/121 documents and remove the temporary global machinery;
this FIXME does not prescribe that interior refactor and does not reopen the
stdlib face-3 API question recorded in FIXME 0800.
