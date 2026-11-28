# Macro-route diagnostic re-anchoring

A diagnostic raised over macro-expansion output is relocated to the written
form that produced it. `spec/05-definitions.md` §5 requires the diagnostic span
to point at the user's written form. The paired frontend reject is
`design/frontend/binder-head-reject.md`.

## 1. Problem

Macro output carries no source provenance:

- The marshal boundary crosses no spans. As `src/marshal.rs` unmarshals a
  clause's result, it gives each node a unique synthetic span from
  `cranelisp_frontend::next_synthetic_span`, in a band beyond any real source
  length.

The frontend and typecheck therefore report errors over expanded code at
locations that map to no source byte. For `def`, the error also names the
mangled synthesized head rather than the written `fmt/x`.

Do not carry real spans through the marshal boundary. The span-keyed carriers
depend on span uniqueness (`design/arch/backend-keyed-consumer.md` §1.1;
`binder-head-reject.md` §4).

## 2. Seam

Int owns the provenance: it holds each pre-expansion origin form and its real
span. A pure transform, `process_form::reanchor_expansion_diagnostic`, takes
the error, the origin span and the origin form.

- A diagnostic whose location is synthetic (§3) is re-anchored to the origin
  span, and the provenance is appended (§4).
- A diagnostic already located inside the origin form passes through unchanged.

This enriches location only. The reject stays single-sourced in its owning
crate (Principles 7 and 19).

**Build site.** When `process_form` drives `build_program_compat` over
expansion output, a frontend error is re-anchored to the form being processed.
A native form's error is never touched.

### 2.1 Finalize site

The cluster finalize typecheck (`check_program_compat` over the expanded
cluster) routes its errors through `reanchor_finalize_error`, which applies the
same transform.

- An error located inside any origin form is native and returned unchanged.
- Otherwise it is re-anchored to the authored form whose expansion holds the
  error's node (§2.2). A one-form cluster, such as a REPL entry or a `def`,
  has only one candidate.

### 2.2 Attribution in a multi-form cluster

**Status: designed 2026-11-28 (S125 Phase 6b); not in source.** The current
source still falls back to the **first** origin form. That is a defect. A
`--run` file is one cluster, so the error lands on whatever form comes first,
typically an `import`. The REPL processes the same form as its own cluster and
places the error correctly. The same program is then reported at two
locations: one at the macro call, as spec §9.3.5 asks, and one at an unrelated
form. That is a REPL and `--run` divergence, which the root memory's Pipeline
section names a defect. T-ARG-SCOPE's
`--run` cell shows it: `undefined variable: add-i64` reported at
`user.cl:1:1`. The cell's requirement, that the error is located in the
caller's form, is right under §9.3.5.

**The rule.** Synthetic spans come from one atomic counter
(`cranelisp_frontend::next_synthetic_span`), and each allocation is a
zero-width `(v, v)`. A synthetic start value therefore names exactly one node
in the process, and that node sits in exactly one authored form's expansion.
The cluster already carries each pair, as `ExpandedPrefix::forms`, a list of
`OriginatedForm { form, authored }`.

- `reanchor_finalize_error` takes those pairs in place of the bare origin
  list. It anchors to the `authored` form whose expanded `form` contains a
  node whose span starts at the error's start. Matching the start rather than
  the whole span also covers a span merged from synthetic children.
- **No node matches** when the error is located at a span allocated after
  expansion, for example by desugaring during the build. The anchor is then
  the one authored form whose expansion differs from its written text. If
  several do, the anchor is the first of them. It is never a form that
  expanded nothing, such as an `import`. This is a named coarse residual.
- The native check, the message and the `line_col` reset are unchanged (§3,
  §4). The transform stays pure.

| Property | Grade |
|---|---|
| An expansion error is anchored to the form whose expansion produced it | *Structural* given the counter: a synthetic start value is allocated once. *Measured* by R1 and R2 |
| An expansion error is never anchored to a form that expanded nothing | *Measured* by R3 |
| An unattributable error in a cluster with several macro-bearing forms lands on the right one | *Not graded.* It is a named coarse residual. Falsifier: a `--run` diagnostic from a post-expansion synthetic span reported at a different macro-bearing form than the REPL reports |

**Potential extension, triggered by a request for a position inside the
form.** §9.3.5 asks only for the call site. When the culprit symbol is caller
text, the provenance set of
[expansion qualification §2.7](expansion-qualification-scope.md#27-caller-text-is-never-qualified)
could map its synthetic span back to the caller's real span, as a side table
for diagnostics only. That would locate the error at the argument itself. The
side table keeps span-keyed carriers unique, so §1's rule still holds.

## 3. Synthetic-location predicate

Key the re-anchor on location, never on the error class or message; sniffing
the class is a review reject. A location is synthetic when its byte range lies
outside the origin form's real extent:

- zero or negative width (`end <= start`), which includes `Span::SYNTHETIC`; or
- starting before, or ending after, the origin's `[start, end)`.

This catches the unique synthetic band without hard-coding its offset, so a
change to the band cannot silently defeat the seam. Because the test is
int-local, no types-level `Span::is_synthetic` is needed.

## 4. Message

Append provenance and never re-phrase the owning crate's message:

```text
<original message, verbatim>
  in expansion of `(def fmt/x …)`
```

The quoted form is the written origin, truncated to a short flat rendering.
The stale line/column context is cleared, so the formatter recomputes it from
the origin span.

## 5. Scope

The re-anchor covers errors surfaced from the two sites above. Diagnostics
raised during expansion itself already carry the call's real span through
`origin_span` (`src/expander.rs`).

## 6. Evidence

The transform is pure, so its unit cells need no session.

- `src/process_form/tests.rs` covers the build site:
  - `reanchor_synthetic_diagnostic_relocates_and_appends_context`;
  - `reanchor_catches_degenerate_zero_width_synthetic`;
  - `reanchor_leaves_native_span_diagnostic_untouched`.
- The same file covers the finalize site. Today that includes
  `reanchor_finalize_multi_form_falls_back_to_first_origin`, which pins the
  §2.2 defect. `dev`(`src/`) replaces it with these pure cells:
  - **R1 (RED).** In a two-form cluster of an `import` that expanded nothing
    and a `defn` whose expansion holds node `s`, an error at `s` is anchored
    to the `defn`.
  - **R2 (RED).** In a three-form cluster where every form expanded, an error
    at a node of the third form's expansion is anchored to the third.
  - **R3 (RED).** An error at a synthetic span that is in no expansion, in a
    cluster where one of two forms expanded, is anchored to the form that
    expanded and not to the first.
  - The native-error cell stays.

  `tests/spec_09_macros.rs::s125_arg_scope_unimported_argument_refused_run`
  is the end-to-end cell, and it turns green. Size: small. About 30 lines of
  production code in `src/process_form.rs`, the call sites passing
  `prefix.forms`, and three cells. No public API.
- `tests/spec_05_definitions.rs::macro_route_qualified_head_reject_span_at_written_form`
  is the end-to-end written-form cell.
