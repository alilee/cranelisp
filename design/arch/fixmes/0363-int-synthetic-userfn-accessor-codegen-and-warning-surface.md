---
number: 0363
target: /int
filed_by: /dev
filed_at: 2026-06-15
sprint_filed: 83
refers_to: src/worker.rs (derive_codegen_batch ~:696 is_uncompiled_synth_def predicate), src/eval.rs / src/repl.rs (typecheck Warning surfacing), tests/spec_05_definitions.rs::generated_field_accessor_resolves_as_free_callable, tests/spec_05_definitions.rs::accessor_is_first_class_value_passable, tests/spec_05_definitions.rs::accessor_neg_synth_does_not_shadow_existing_binding
status: open
---

> **S83 W2 partial resolution (2026-06-15, /dev int).** Gap A is RESOLVED —
> `src/worker.rs::derive_codegen_batch`'s sibling-scan predicate now also matches
> `DefKind::UserFn { fn_state: Concrete { .. } }` with `ast: Some(_)`, so the
> synthetic accessor body is lowered and its GOT slot populated.
> `generated_field_accessor_resolves_as_free_callable` and
> `accessor_is_first_class_value_passable` are GREEN.
>
> Gap B is BLOCKED on FIXME 0365 (`target: /typecheck`). The int receiving end is
> landed (`src/eval.rs::process_form_cluster` threads `ProcessedCluster.warnings`
> into the `EvalResult`; `src/repl.rs::format_eval_result` renders `; warning:`
> lines), but `cranelisp_typecheck::check_forms` returns `Result<(), CheckError>`
> and DISCARDS its `CheckResult` (with warnings) at `form.rs:306` — so the
> `ShadowedName` collision warning never reaches int.
> `accessor_neg_synth_does_not_shadow_existing_binding` stays RED until 0365
> lands the warning across the boundary; then int's `finalize_cluster`
> (`src/process_form.rs:1098`, currently `ProcessedCluster::empty()`) fills
> `ProcessedCluster.warnings` from the surfaced set. This file stays OPEN for
> that final int fill + green flip. See 0365 for the full handoff.

# Synthetic `UserFn` field accessors are not codegen-batched, and typecheck `Warning`s are not surfaced in the REPL (blocks FIXME 0351(a) guards)

## Issue

S83 Wave 2 lands the typecheck-side field-accessor synthesis (FIXME 0351(a),
spec §5.2.6): each product field synthesises a free accessor `field :: (Fn
[ProductType] FieldType)` as a concrete `DefKind::UserFn { fn_state:
Concrete { got_slot } }` with a single-arm `match` body (`ast: Some(..)`),
registered in the type's module beside the ctor (in
`crates/cranelisp-typecheck/src/adt.rs::register_constructors`). Typecheck is
correct: `/sig v` and `/info v` confirm `v :: (Fn [user/Box] primitives/Int)`
resolves with the right type, and `(v ...)` no longer errors `undefined
variable: v`.

Two int-side gaps block the e2e guards from going green:

### Gap A — codegen batch excludes synthetic `UserFn` accessors

`src/worker.rs::derive_codegen_batch` (~:696) selects which symbol-table
entries to compile. Its `is_uncompiled_synth_def` predicate enumerates only:

```rust
ModuleEntry::Def { kind, ast: Some(_), .. }
    if matches!(kind.as_ref(),
        DefKind::Constructor { .. } | DefKind::Primitive { .. })
```

A synthetic `DefKind::UserFn { fn_state: Concrete { .. } }` accessor carrying
`ast: Some(match)` is NOT matched, so its body is never lowered and its GOT slot
is never populated. The call `(v (Box 5))` then resolves the accessor name but
loads an empty slot → it produces NO result (observed: an empty REPL prompt
line, no value, no error).

The backend itself is kind-agnostic — `compile_to_module`
(`crates/cranelisp-backend/src/lib.rs` ~:660) reconstructs a `Defn` from ANY
`ModuleEntry::Def` with `ast: Some`, regardless of `DefKind`. The ONLY gate is
this int-side batch predicate.

**Proposed:** extend the predicate to also match `DefKind::UserFn { fn_state:
UserFnState::Concrete { .. } }` with `ast: Some(_)` (a synthetic concrete UserFn
born in the symbol table without a `Defn` in the program list). The comment at
`:681–695` already CLAIMS the "field-accessor family" is covered — but those are
the slot-less `DefKind::PrimitiveExtern` Trace accessors, which carry no body;
this is the first body-carrying synthetic `UserFn`.

Flips `generated_field_accessor_resolves_as_free_callable` and
`accessor_is_first_class_value_passable` green (the first-class `(let [g v] ..)`
path needs the same slot populated).

### Gap B — typecheck `Warning`s are not displayed in the REPL

The collision guard `accessor_neg_synth_does_not_shadow_existing_binding`
(`(defn v ..)` then `(deftype Box [:Int v])`) requires the REPL to SURFACE a
diagnostic when a synthesised accessor collides with an existing non-accessor
binding (safe disposition — never silent). Typecheck now records this as a
`Warning { kind: WarningKind::ShadowedName, .. }` (in
`program.rs::finalize_check_result_inner`, drained from
`CheckState::deferred_accessor_collisions`). But the REPL eval loop accumulates
warnings (`src/eval.rs` `all_warnings`, `EvalResult::warnings`) and **never
prints them** to stdout/stderr. `src/CLAUDE.md` says "Warnings … are displayed
by the binary crate" — but no display site exists in the REPL read-eval loop.

**Proposed:** render accumulated typecheck `Warning`s to the REPL output (and
`--run` stderr) — e.g. a `; warning: <message>` line per the §1.1 comment style.
This is a general gap (any `UnusedBinding`/`UnreachableArm`/`ShadowedName`
warning is currently invisible in the REPL), surfaced here by the accessor
collision guard.

Flips `accessor_neg_synth_does_not_shadow_existing_binding` green (it greps the
combined output for `error|collision|conflict|already|duplicate|shadow`).

## Operational implication / Context

S83 Phase 5 Wave 2. The typecheck synthesis is committed and regression-free
(full suite 1361 pass / 5 fail = the named guards, no new reds). These two int
gaps are the remaining blockers for 3 of the 0351 guards (the 4th, the
cross-type duplicate, is FIXME 0364; the 5th, self-qualified, is FIXME 0362
/frontend). Unit coverage of the synthesis seam is committed in
`crates/cranelisp-typecheck/src/adt.rs` (`product_field_synthesises_concrete_accessor`,
`accessor_collision_with_nonaccessor_is_refused`,
`cross_type_duplicate_field_folds_into_overload`).
