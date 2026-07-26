---
number: 0906
target: /dev (backend)
filed_by: /dev (backend)
filed_at: 2026-07-26
sprint_filed: 118
refers_to: crates/cranelisp-backend/src/compiler/vec_codegen.rs — the `guarded` arm of the Vec element inc-adapter body (≈:986)
status: open
ruled_at: design/backend/non-concrete-release-contract.md §7.2
---

# A third hand-rolled nullary-skip guard survives in the Vec element inc adapter

> **CARRIED S119 Phase 3, `/design`(backend) —
> `design/backend/non-concrete-release-contract.md` §7.2.** The proposed
> resolution is accepted verbatim and gains a reason beyond Principle 7: rule
> **R-1** of the release contract is precisely that the tag-vs-pointer decision
> has ONE home, because the whole class's memory-unsafety is that decision being
> mistaken for a scalar-vs-pointer test. A third hand-rolled copy is a third
> place that mistake can be re-made silently.
>
> Scope confirmed as filed: fold onto `heap::emit_nullary_skip_guard`; **not
> byte-identical** (block creation order swaps the two labels); lands with a
> **scoped** golden re-baseline for the covered bodies only (extension ≠
> re-baseline, `ownership-inference.md` §6.2); reuse
> `ctor_template_admission_tests::assert_threshold_guarded_rmws` for the
> absolute-polarity pin — it walks arbitrary CLIF text, so no new machinery.

## Severity
Nit

## Issue

FIXME 0905's resolution folded the two guarded RC halves
(`heap::emit_rc_inc_guarded_atomicity` / `emit_rc_dec_guarded_atomicity`) onto
ONE shared predicate, `heap::emit_nullary_skip_guard`, so a polarity gap between
the inc and the dec is unrepresentable rather than merely tested for.

A **third** site still spells the same three-instruction prologue itself: the
`guarded` arm of the Vec element inc-adapter body in `vec_codegen.rs` —

```rust
let threshold = builder.ins().iconst(types::I64, NULLARY_THRESHOLD_I64);
let is_tag = builder.ins().icmp(IntCC::UnsignedLessThan, val, threshold);
let inc_block = builder.create_block();
let ret_block = builder.create_block();
builder.ins().brif(is_tag, ret_block, &[], inc_block, &[]);
```

It is polarity-correct today, and it is a *separate* Cranelift context (an
adapter function body, like the capture-glue mirrors), so it cannot reach the
`&mut self` helpers. But it is the same decision spelled a second time, and
Principle 7 / the crate's ONE-predicate pattern say the decision has one home.

## Proposed resolution

Fold onto `heap::emit_nullary_skip_guard` (the free function takes only
`builder`, `ptr`, `cont_block`, so the separate-context constraint is not a
barrier). **This is NOT byte-identical**: the adapter creates `inc_block` before
`ret_block`, whereas the shared helper requires the continuation block first, so
the two block labels swap. Block creation order IS CLIF block numbering, which
is why the 0905 change-set stopped at the two halves it could fold without
touching the golden corpus. Land this with a scoped golden re-baseline for the
covered bodies (extension ≠ re-baseline — `ownership-inference.md` §6.2).

## Context

- Surfaced while resolving FIXME 0905 (S118). Deliberately left out of that
  change-set to keep the byte-identical-emission claim clean and verifiable
  against `tests/fixtures/clif_baseline/golden/`.
- The 0905 structural instrument
  (`ctor_template_admission_tests.rs::assert_threshold_guarded_rmws`) is
  reusable here: it walks any CLIF text, so a Vec-adapter cell can assert the
  same absolute polarity without new machinery.
