---
number: 0863
target: /dev
filed_by: /dev
filed_at: 2026-07-24
sprint_filed: 117
refers_to: design/int/s117-conformance-recovery.md §1.1.2 and §6;
  design/arch/bounded-contexts.md §6; design/arch/fixmes/0800-def-macro-expansion-leaks-internal-thunk-name-and-blocks-call.md;
  tests/spec_11_stdlib.rs::def_definition_echo_names_user_binding_not_internal_thunk;
  tests/spec_11_stdlib.rs::def_info_and_sig_describe_bound_value_not_macro
status: deferred
target_sprint: 118
---

# Cluster-wide prepared macro registration and presentation transaction

## Issue

DF-1 and DF-2 require the REPL to present the public value subject emitted by
an entered macro invocation, rather than the implementation symbols used by
the macro expansion. The Sprint 117 implementation attempt projected that
subject only after the cluster had already published. It reconstructed
provenance by scanning introspection rows and stored the projected scheme in a
parallel `SharedState.presentation_schemes` map.

That attempt made both DF tests green, but review rejected it:

- projection could fail after the compiler had published the successful
  cluster, violating the all-or-nothing turn contract;
- the entered form's public subject was reconstructed by an ambient
  post-publication scan rather than carried as exact expansion provenance;
- the parallel presentation map introduced a second lifecycle store that
  could diverge from canonical introspection.

The rejected implementation and its W3c-only tests were removed. DF-1 and DF-2
are intentionally RED again: the definition echo exposes `user/n-def`, while
`/info n` and `/sig n` classify the public binding as `defmacro`. FIXME 0800
remains the historical symptom record.

## Proposed resolution

Implement the cluster-wide prepared transaction specified by
`design/int/s117-conformance-recovery.md` §1.1.2 and §6:

1. Move the `TurnCheckWorld` ownership boundary before Pass 1.
2. Stage Pass-1 and expansion-emitted macro symbols, introspection records,
   clause-code owners, and related registrations in the candidate turn rather
   than publishing them incrementally.
3. Make every nested `prepare_macro_clause_turn` return an owned prepared
   result that the parent transaction absorbs.
4. Carry exact `EnteredMacroProvenance`, including the emitted public subjects,
   from the expansion that produced them. Do not rediscover identity by
   scanning live or introspection state.
5. Derive `PreparedPresentation` against the settled candidate world before
   backend compilation and publication.
6. Publish once, in the architecture-specified order:
   owners → entries → introspection. On any failure, publish none and clear
   every reserved GOT cell.
7. Store the projection only in canonical
   `Introspection.presentation_scheme`, per Binary bounded context §6. Do not
   recreate a parallel presentation store.

The implementation needs focused coverage for:

- failure at every preparation and backend boundary, proving no partial
  symbols, introspection, owners, presentation, or reserved cells survive;
- private emitted subjects;
- zero, one, and multiple public emitted subjects;
- generic projected values and settled schemes;
- direct ordinary `defmacro` controls;
- DF-1 and DF-2 through echo, `/info`, `/sig`, and bare lookup.

## Deferral rationale

The correct change reopens the reviewed W3a foundational transaction seam and
must move the ownership boundary ahead of Pass 1. It is not safely expressible
as a local REPL formatter correction. The user approved deferral to Sprint 118
on 2026-07-24 so Sprint 117 can retain the reviewed W3a/W3b implementation
without an interim post-publication mechanism.

## Context

The design already records the complete target mechanism in
`design/int/s117-conformance-recovery.md` §1.1.2 and §6. Binary bounded context
§6 is authoritative for the canonical introspection lifecycle. This FIXME is
the deferred `/dev` implementation handoff; it does not reopen the stdlib
face-3 API question recorded in FIXME 0800.
