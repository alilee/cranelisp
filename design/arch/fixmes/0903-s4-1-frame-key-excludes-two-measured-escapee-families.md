---
number: 0903
target: /design (backend)
filed_by: /dev (backend)
filed_at: 2026-07-26
sprint_filed: 118
refers_to: design/backend/transitive-drop-glue.md §4.1 (the ruling) + §10 row 4 +
  §11 no-interim list; crates/cranelisp-backend/src/compiler/fn_compiler.rs::emit_heap_binding_decs
status: open
---

# §4.1's "exactly one class" is falsified — the frame key costs 16 corpus programs

## Issue

FIXME 0891's ruling (§4.1) directs `/dev` to re-key the non-concrete release
admission from the TYPE to the FRAME: admit iff the compiled body is the
synthetic `MonoExpr::ConstrADT` node and the binding is one of that frame's own
parameters; everything else stays a located `release_site_type_error`. §11 makes
a type-keyed gate an explicit `/review` REJECT. The ruling rests on a factual
premise:

> The migration measured exactly one class, and it is legitimate.

**That premise is false.** The gate was implemented exactly as ruled and
measured. The unit negatives went RED-then-GREEN as designed, and the corpus went
the other way.

### Measurement

| Run | Command | Result |
|---|---|---|
| baseline (HEAD `dd0b1c5e`) | `cargo nextest run --no-fail-fast -E 'binary(/^spec_/)'` | 893 run, **8** failed (all pre-existing) |
| ruled frame key | same | 893 run, **24** failed |

**16 NEW failures**, every one a hard `CranelispError::CodegenError` refusing a
program the corpus currently compiles and runs:

- `spec_03_types` (7): `applied_annotation_bare_var_corefers_param`,
  `applied_annotation_bare_var_pins_through_ctor`,
  `defn_param_free_var_nested_in_applied_type`,
  `defn_param_multi_var_applied_annotation`,
  `rank2_argument_applied_at_two_types_neg`,
  `single_poly_instance_used_at_two_types_value_restriction_neg`,
  `unknown_uppercase_type_annotation_nested_still_errors_neg`
- `spec_07_traits` (5): `hkt_functor_impl_on_option_dispatches_via_match`,
  `hkt_impl_on_user_well_kinded_adt_dispatches`,
  `hkt_impl_pairing_head_qualified_resolves_to_slot1_trait_accepts_and_dispatches`,
  `hkt_impl_targets_bare_type_constructor_not_applied_form`,
  `qualified_hkt_impl_trait_reference_resolves_canonical_home_and_dispatches`
- `spec_field_accessor` (2): `control_polymorphic_deftype_level_product_mints_both_accessors_green`,
  `control_same_name_constructor_arm_mints_both_accessors_green`
- `spec_04_expressions` (1): `fn_lambda_param_free_var_annotation`
- `spec_05_definitions` (1): `deftype_product_shortcut_field_names`

### The two further escapee families

Both are ordinary `defn`-shaped frames — not `ConstrADT` bodies — so the ruled
gate refuses them, and neither is a balanced counted-borrow pair, so widening the
gate to admit them is not I-CT-licensed either. Verbatim from the refusals:

1. **Synthetic field accessors of a generic or undeclared-field product.**

   ```
   codegen failed for user/Box.v: release site in 'Box.v' reached a non-concrete
   type ADT(FQTypeName { module: "user", name: "Box" }, [Var(0)])
   ```

   `(deftype Pair [first second])` and `(deftype (Box a) [:a v])` both mint
   accessors whose `self` parameter is the ADT with residual type ARGS. This is
   the same "compiled once per declaration, signature-driven" shape §4.1 argues
   for the ctor — and `concrete-boundary-type.md` §3.1.1 pairs the **ctor and
   accessor** signature paths in one sentence (FIXME 0902 quotes exactly that).
   §4.1 named only the ctor half.

2. **Generic trait-method instances.**

   ```
   codegen failed for user/Functor.fmap$primitives/Option: release site in
   'Functor.fmap$primitives/Option' reached a non-concrete type Fn([Var(9)], Var(8))
   ```

   A closure-typed parameter whose residual vars survive HKT dispatch.

For both, the scope-exit dec is a genuine consuming-convention teardown with no
paired publication: at `old_rc == 1` the shallow `emit_rc_dec_guarded(…,
drop_glue_id: None, …)` deallocs without discharging fields, so **both leak
today** — silently, and have since before this migration. The ruling's
characterisation of a type-keyed gate as "a fallback arm wearing one case's name"
is therefore right in substance and understated in scope: the arm is absorbing at
least three families, not one.

## What /dev did, and why it stopped

Landed in the same commit as this FIXME (all green, `-p cranelisp-backend` 527/527):

- §10 row 4's **positive and edge cells** —
  `compiler/fn_compiler/ctor_template_admission_tests.rs`. They pin I-CT's
  balance (one guarded inc, one balancing guarded dec, both behind the SAME
  `NULLARY_TAG_THRESHOLD` predicate, no glue call) for the generic template, the
  undeclared-field template and the multi-field template, plus the boundary that
  a concrete-field template takes the ordinary `drop<T>` path. They hold under
  either admission key.
- the ruling's **item 3**, the stale-0394 re-points (`signature_heap_category`
  rustdoc + its inline `Err` arm + its `lib.rs` unit cell + the
  `emit_heap_binding_decs` comment + `crates/cranelisp-backend/CLAUDE.md`).
- the measured census, recorded at the seam (`emit_heap_binding_decs` rustdoc)
  and in the crate `CLAUDE.md`, so the next reader does not re-run the
  experiment.

NOT landed: the gate re-key (ruling item 1) and §10 row 4's negatives. A
16-program hard-refusal regression is not landable, and choosing which of the
three families is sanctioned is a design ruling, not an implementation choice.

## Proposed resolution

`/design`(backend) rules over the WHOLE measured class. The three candidate
directions `/dev` can see, none of them costed here:

- **make the signature path concrete** — monomorphise or otherwise pin accessor
  `self` and trait-instance parameters, so the arm has no traffic left and §4.1's
  ctor case becomes genuinely the only one. Couples to FIXME 0902 (`/arch`).
- **mark them `Borrowed`** — an accessor's `self` and a trait instance's fn
  parameter are read-only; a `Borrowed` mode elides both the caller inc and the
  callee dec, so the release never happens. Note this collides head-on with
  §4.1's standing obligation (a `Borrowed` param reaching a **ctor** template
  breaks I-CT in the leak direction), so the two halves must be ruled together.
- **sanction a wider frame set** — "signature-driven compiled-once-per-
  declaration template" as the frame predicate. Cheapest, but it needs a
  soundness statement per family, and for the accessor/trait families that
  statement is currently *false* (they leak).

Whichever lands, `/dev` re-applies the ruled gate. The implementation is
mechanical and was validated end-to-end; it is reproduced below so the re-land is
a paste, not a re-derivation.

### The implemented gate (validated, then reverted)

`fn_compiler.rs`, module level:

```rust
/// The caller's frame verdict at [`FnCompiler::emit_heap_binding_decs`] — the
/// gate on §4.1's single sanctioned non-concrete release. The release body is
/// shared by three seams and §4.1's licence covers exactly one, so the verdict
/// is a PARAMETER rather than something the shared body derives.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum NonConcreteRelease {
    CtorTemplateParams,
    Rejected,
}
```

`FnCompiler` field + `compile_body` (the `fn_has_self_call` precedent — the body
node is in hand before the compiler exists, so no probe and no carrier):

```rust
pub(crate) is_ctor_template: bool,
// ...
let is_ctor_template = matches!(body, MonoExpr::ConstrADT { .. });
```

`inner()` sets it `false` (a ctor template's body opens no inner frame).

`pop_scope_with_cleanup` — the ONLY admitting seam (`scope_stack.len() == 1`
means the frame being popped IS the parameter frame):

```rust
let admission = if self.is_ctor_template && self.scope_stack.len() == 1 {
    NonConcreteRelease::CtorTemplateParams
} else {
    NonConcreteRelease::Rejected
};
self.emit_heap_binding_decs(&to_dec, admission)?;
```

Both `flush_let_scopes_before_tail_jump` and
`flush_superseded_heap_params_before_tail_jump` pass
`NonConcreteRelease::Rejected` explicitly, and the shared body's arm becomes:

```rust
if admission == NonConcreteRelease::CtorTemplateParams
    && cranelisp_types::ConcreteType::from_type(ty).is_err()
{ /* guarded shallow dec */ }
```

### The three negative cells (validated RED → GREEN, then held back)

Falsification observed against the type-keyed gate before the narrowing: all
three FAILED; all four positive/edge cells stayed GREEN, which is exactly why
they cannot substitute for the negatives.

1. `a_non_concrete_binding_in_a_non_ctor_template_frame_is_a_located_error_neg` —
   `(defn f [x] 0)` with `Scheme.ty = Fn([Var(0)], Int)` via
   `insert_user_fn_stub_typed`; body an `IntLit` so the frame is not a ctor
   template and `x` is published nowhere. Under the type-keyed gate it compiled
   silently into a shallow guarded dec; under the frame key it raises
   `release_site_type_error` naming `f` and "no shallow fallback".
2. `the_admission_is_unreachable_from_the_tail_jump_flush_neg` —
   `(defn go [n x] (go 0 n))` with `Scheme.ty = Fn([Int, Var(0)], Int)`, carriers
   from `test_support::call_carriers(body, &module, &["go"])`. The tail argument
   supersedes `x`'s slot, so
   `flush_superseded_heap_params_before_tail_jump` owes the release; it must be
   the located error, since a superseded slot has no publication.
3. `the_admission_gate_is_keyed_on_the_frame_not_the_type_neg` — structural, over
   `include_str!("../fn_compiler.rs")`: the `emit_heap_binding_decs` slice must
   contain `admission: NonConcreteRelease` and
   `admission == NonConcreteRelease::CtorTemplateParams`, and the file must
   contain exactly two
   `emit_heap_binding_decs(&to_dec, NonConcreteRelease::Rejected)` call sites.

## Context

- Found: S118, `/dev`(backend), implementing FIXME 0891's ruling.
- 0891 is set `status: deferred` on this; its item 3 (the stale-0394 re-points)
  and §10 row 4's positive/edge cells shipped.
- Related upstream: FIXME 0902 (`/arch`) — `concrete-boundary-type.md` §3.1.1
  point 2 / BC §3 invariant 9 assert the ctor/accessor signature path's
  `ConcreteType::from_type` "must succeed". The accessor family here is that
  assertion's second half, and it fails the same way.
- Related: `design/arch/safety-invariants.md` §4 — a silent shallow release that
  deallocs without discharging fields is an unasserted-narrowing instance
  (Principle 25); the accessor/trait families are currently in it.

## Acceptance addendum (`/qa`, S118 W8 gate — folded from FIXME 0909 item 3)

The S118 golden re-baseline (FIXME 0908; MANIFEST §Re-baselines, S118 entry)
**blessed a defect sighting of family 1**: `f4_sudoku::user::Grid.cells` — the
synthetic accessor of the undeclared-field product `(deftype Grid [cells])` —
drifted into a SHALLOWER release (the golden's transitive step gone, no glue
call taking it over; the only frame in either lane where a teardown level was
lost). The blessed golden is a leak record, not certification.

**Binding on this FIXME's S119 acceptance:** the implementing fix MUST name the
`f4_sudoku.clif` `user::Grid.cells` frame's re-baseline as its own witness —
that frame is EXPECTED to drift back to a transitive (or glue-routed) release
when the ruling lands, and the scoped, attributed re-capture of that drift is
part of the fix's evidence, planned in the fix's change-set rather than
discovered at the next wave gate. Cell #21
(`exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400`,
12,431 at S118 HEAD, re-attributed to the 0903 families per
`tests/plan/s118-test-plan.md` §11.3) is the companion runtime witness expected
to move with the same fix.
