---
number: 0044
title: Cluster-atomic typecheck over binary-owned staging, behind the single `check_forms` entry
status: operative
---

# 0044 — Cluster-atomic typecheck over binary-owned staging

This record is a citation anchor, not an authority. The current contract is
the [typecheck context](../bounded-contexts.md#2-typecheck-cratescranelisp-typecheck)
(the cluster definition and invariants 2, 3a, 7, 10 and 11), the
[`check_forms` narrative](../interfaces.md#check_forms) and the rustdoc on
`check_forms` and `SymbolTableAccess` in `crates/cranelisp-typecheck/src/`.
Exact signatures live only in that rustdoc; this record restates none.

## Ruling in force

- A **cluster** is the unit of non-macro typecheck atomicity: one REPL form, the
  contents of one explicit `begin`, or a file's fully expanded non-macro forms.
  Forward references do not cross separate REPL inputs
  ([spec 5.13](../../../spec/05-definitions.md#513-definition-ordering)).
- Typecheck has one cluster entry, `check_forms`. Signature registration then
  body checking is an ordering inside that call; no pass
  discriminator, accumulator or other working state crosses the boundary.
- The binary owns a per-cluster staging table. Typecheck writes only through the
  supplied accessor and cannot distinguish staging from live. The binary
  publishes staging on whole-cluster success and drops it on any error; on a
  `Gap` it loads the dependency and retries the whole call against fresh
  staging. The live table is unchanged across any failure.
- A source-ordered `defmacro` is a module-local compile-time checkpoint outside
  this rollback domain (amended 2026-09-03). It publishes once its
  expansion-time closure has typechecked and compiled, and a later form's
  failure does not roll it back. It is not a cluster boundary: non-macro forms
  on both sides keep one forward-reference scope. Authority:
  [macro availability](../macro-availability-model.md). The amendment added no
  public API, schema, backend contract or platform interface.

## `SymbolTableAccess` (Approach B is canonical)

`SymbolTableAccess` has two modes. `Live` reads and writes the committed
per-module table. `Cluster` sends current-module writes to the binary's staging
table and reads through the types-owned `View`, which consults staging before
live. The two accessors are the only place the modes differ.

**Approach B — empty staging, unioned reads — is the adopted shape.** Cluster
writes are additive, so staging starts empty, reads union staging over live, and
publication drains staging into live. No table is cloned per cluster.

**Approach A — clone live into staging, replace on publish — is not adopted.**
It costs a clone per cluster and buys initial-equal-to-live staging that no
current workload needs. Adopting it is an orchestration change that needs no
accessor change, and it remains a decision for `arch` and the user.

Two defects fixed the read and state rules this section pins, and their
regressions cite it:

- Cluster-mode reads must union staging and live. Reading live alone loses an
  intra-cluster forward reference to a sibling staged in the same cluster.
- Cross-form working state must not live outside the `check_forms` frame.

## Why this shape

- **Spec-forced.** Top-level forward references and mutual recursion require
  every signature in scope before any body is checked, so a per-form pure entry
  cannot work.
- **One durable write surface**
  ([Principle 07](../principles/07-single-source-of-truth.md)). "In the live
  table" means checked and published, unqualified by mode. Staging is a
  transient frame that nothing else can observe, not a second store.
- **Typecheck stays decoupled**
  ([Principle 01](../principles/01-decoupling-over-convenience.md)). The
  accessor absorbs the staging/live distinction, so registration sites did not
  change and cannot bypass it; module locality (invariant 10) is the
  precondition.
- **One pipeline**
  ([Principle 11](../principles/11-single-pipeline-mode-parameters.md)). A
  REPL form is a one-form cluster and a file is one large cluster on the same
  path.

## Rejected alternatives

Each was tried or argued and must not return without a new ruling:

- **Two public pass functions** (`check_form_signatures`, `check_form_body`).
  Withdrawn 2026-05-13: working state between the passes could not cross two
  free-function calls without a public accumulator.
- **One function with a pass-discriminator parameter.** Every consumer would
  dispatch on the pass ([Principle 02](../principles/02-narrow-interfaces.md)).
  `check_forms` differs: it takes the whole cluster and the caller never names
  a pass.
- **Staging as a mode of `SymbolTable`.** The canonical store would gain a
  second write surface and its live invariant would become mode-qualified.
- **A read-view trait implemented by `&SymbolTable`.** One production caller
  pattern does not earn a trait; `View` is a concrete types-owned value.
- **A cluster-wide macro transaction**, including invoking unpublished macro
  candidates, a temporary GOT candidate stack and a cross-module rollback
  domain. Rejected by the 2026-09-03 amendment.

## Retirement

Two items await extraction into the
[`check_forms` narrative](../interfaces.md#check_forms) before this record
deletes: the Approach A/B ruling and the pass-discriminator, staging-mode and
view-trait rejections. The rest is already in the homes named at the top.

| Citation | Repoint to |
|---|---|
| `tests/regression.rs`, two `// spec:` blocks citing the `SymbolTableAccess` section (regressions for FIXME 0177 and FIXME 0179) | the `check_forms` narrative, once it carries the Approach B ruling |
| `tests/process_form_dispatch.rs`, the `// spec:` continuation line naming this file | typecheck context invariant 11 and [macro availability](../macro-availability-model.md); the adjacent `FIXME(/dev typecheck …)` comment describes the withdrawn two-function split and deletes |
| [Label index](README.md) row 44 | the typecheck context link alone |
