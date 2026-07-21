---
number: 0795
target: /design (int)
filed_by: /dev (src)
filed_at: 2026-07-21
sprint_filed: 115
refers_to: design/int/impl-redefinition-hot-reload.md §3 (+ §5 unit-tier row) —
  the prescribed enrollment mechanism ("for each `method in impl_.methods`")
  is the exact narrowing that left FIXME 0791's explicit->default hole; the
  landed mechanism is a trait-wide prefix scan.
status: open
---

# `impl-redefinition-hot-reload.md` §3 prescribes the per-method enrollment that FIXME 0791 had to widen

## Issue

§3 ("The fix — enroll the mangled method Defs") specifies:

> - for each `method in impl_.methods`, enroll every live `defined_symbols()`
>   entry whose name is the method's mangled form — `{impl_.trait_name}.{method}$…`

The W6 change-set implemented that literally. `/review` then found the hole
(FIXME 0791, repro-confirmed at HEAD `7ce77a7e` by `/dev` before the fix): a
method whose source changes **explicit → default** is not in `impl_.methods`,
and its re-staged default `Defn` is appended to `finalize_cluster`'s WORKING
program (`process_form.rs`), never to the `expanded_program` slice that reaches
`derive_codegen_batch` — so it was never enrolled, `commit_slotted_def` carried
the prior override's code over (AbiPreserving), the `already_compiled` sweep
skipped it, and the **stale override kept dispatching** where spec §7.1.5's
default MUST take over.

The landed mechanism (S115 W6b) keys on the **trait alone**: `{trait}.` prefix +
a `$` in the remainder. §3's own binding contract sentence ("*every mangled
method Def of the impl enters the forced batch*") is still correct; only the
prescribed derivation of that set is superseded.

## Proposed resolution

`/design`(int) revises §3's mechanism bullet to the trait-wide prefix scan and
records **why** the per-method narrowing is not merely equivalent-but-narrower:
the default-synthesis path routes the `Defn` through a program slice the batch
deriver never sees, so `impl_.methods` is not a sound proxy for "the methods
this impl's live table holds". Worth stating as a general caution — an
enrollment set derived from the FORM under-approximates one derived from the
TABLE whenever a pass synthesises entries.

§5's unit-tier row should also name the second pin now standing at that seam
(`worker::tests::derive_codegen_batch_enrolls_omitted_default_method_of_the_impl`,
the omitted-method cell) alongside the existing explicit-method cell.

## Context

`/dev`(src) S115 W6b, resolving FIXMEs 0791 + 0792. Repro before fix confirmed
(METHOD §2.2): `weight` returned `:primitives/Int 55` at HEAD, returns
`:primitives/Int 100` after. The full default → override → default cycle also
verified. `/dev` does not edit `design/int/`, hence this FIXME.
