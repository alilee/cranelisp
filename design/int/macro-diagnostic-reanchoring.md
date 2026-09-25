# Macro-route diagnostic re-anchoring

A diagnostic raised over macro-expansion output is relocated to the written
form that produced it. `spec/05-definitions.md` §5 requires the diagnostic span
to point at the user's written form. The paired frontend reject is
`design/frontend/binder-head-reject.md`.

## 1. Problem

Macro output carries no source provenance:

- `src/marshal.rs` unmarshals every returned `Sexp` with `Span::SYNTHETIC`,
  which is `(0, 0)`.
- `src/expander.rs::rewrite_spans_unique` gives each expansion node a unique
  synthetic span in a band beyond any real source length.

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
- Otherwise it is re-anchored. A `def` or `const` cluster has one origin form,
  which is the exact anchor.
- A multi-form cluster whose synthetic node cannot be attributed to one form
  falls back to the **first** origin form. A coarse real location is better
  than none.

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
- The same file covers the finalize site, including
  `reanchor_finalize_multi_form_falls_back_to_first_origin`.
- `tests/spec_05_definitions.rs::macro_route_qualified_head_reject_span_at_written_form`
  is the end-to-end written-form cell.
