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
  assertion's second half, and it fails the same way. **RESOLVED S118 W8
  (`/arch`): §3.1.1 point 2 + BC §3 invariant 9 amended — template-path `Err`
  classifies `Mixed` (ratified as-built), the *classification* rule is settled
  upstream of this FIXME's release-side ruling, and the undeclared-field
  declaration-time question is FIXME 0912 (`/spec`).**
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

**Binding on this FIXME's S119 acceptance (AMENDED at P6 close, `/qa`):** the
implementing fix MUST name the `f4_sudoku.clif` `user::Grid.cells` frame's
re-baseline as its own witness — that frame is EXPECTED to drift back to a
transitive (or glue-routed) release when the ruling lands, and the scoped,
attributed re-capture of that drift is part of the fix's evidence, planned in
the fix's change-set rather than discovered at the next wave gate. That
re-baseline is a **static** witness (the frame is compiled-but-uncalled in the
corpus entry — `/port` evidence below) and it STANDS.

The original companion clause naming cell #21
(`exemplar_ownership_residue_s116::sudoku_warm_serial_solve_residue_at_most_1400`)
as this FIXME's runtime witness is **STRUCK — falsified by `/port`'s direct
experiment**: the exemplar never calls `Grid.cells`, and the cell's residue
reduces cleanly to FIXME 0917 (a distinct backend axis). Cell #21 is
re-attributed to 0917 and is NOT this FIXME's acceptance cell
(`tests/plan/s118-test-plan.md` §11.8.1). This ruling's runtime witnesses are
instead: the S119 W1 family marginal guards (`s118-test-plan.md` §11.2,
`PLAN.md` S118-track rows) and — for family 2 — the P6-batch 0916 pair.

**Family-2 severity UPGRADE (P6 close, FIXME 0916, probe-verified):** family 2
is not leak-only. The generic instance RC-manipulates a residual-`Var`-typed
slot behind the nullary-tag guard, and a SCALAR payload whose value ≥
`NULLARY_TAG_THRESHOLD` is treated as a heap pointer — a **wild atomic write
at payload+8** (measured boundary exactly 1023/1024; SIGSEGV on the first
iteration). The nullary-tag guard discriminates tags from pointers, not
scalars from pointers; it cannot license RC ops on unknown-category slots.
The ruling must close the memory-unsafety face, not only the leak — a
resolution that keeps family-2 emission while fixing only the discharge depth
is insufficient. 0916 (retargeted here-adjacent, `/design` backend, S119)
carries the reduced nine-line repro + CLIF evidence.

## `/port` application-scale evidence (S118 Phase 6a, HEAD `501e701f`)

Two things this ruling should weigh, both measured on the Sudoku exemplar with
`CRANELISP_NO_LENIENT=1 CRANELISP_RC_STATS=1`, warm cache. Detail and the raw
tables live in `exemplar/CLAUDE.md` §"Solve-path never-freed leak — CURRENT
STATE".

### 1. The retention is PER-SOLVE LINEAR, not per-session — and it is
### observable at the application surface

A driver loop solving the same puzzle N times in one process:

| N | residue | residue / N |
|---:|---:|---:|
| 0 | 0 | — |
| 1 | 12,376 | 12,376 |
| 4 | 49,504 | 12,376 |
| 8 | 99,008 | 12,376 |
| 64 | 792,064 | 12,376 |
| 128 | 1,584,128 | 12,376 |

Exactly linear, **intercept exactly 0**, identical in the parallel lane. RSS
grows ~1.13 MB per solve and is never reclaimed. At the web marquee, real
`POST /solve` requests grow the server **~1.17 MB/request** monotonically
(55.3 MB after 1 → 125.2 MB after 61 requests), every response correct.
Extrapolated, +1 GB at ~900 requests. **Priority consequence: this class does
not merely leave garbage at exit — it bounds the lifetime of a long-running
Cranelisp program.** Throughput is essentially flat (marginal 32.5 ms/solve at
N≤32, 39 ms at N=128), so nothing else surfaces the problem to a user until the
process dies.

### 2. Family 1's named witness on this path — `Grid.cells` — is NOT the cause

The §11.3 lead ("`grid/Grid.cells` is a synthetic accessor of a generic product
and the backtracking solver calls accessors per cell per pass") is **falsified
on the call-site half**: the exemplar never calls that accessor. Every Grid
field read is `(match g [(Grid cells) …])` — `cell-at` and `set-cell` both
destructure (`exemplar/grid.cl:179,183`). The same is true of the golden
fixture `tests/fixtures/s99/f4_sudoku.cl:49-50`, so the blessed
`f4_sudoku.clif::user::Grid.cells` frame is compiled-but-uncalled in that
corpus entry too — its re-baseline is a *static* witness with no runtime
traffic behind it.

Confirmed by direct experiment rather than inference. Rewriting the declaration
as `(deftype Grid [:(Vec Cell) cells])` (legal today, and the answer to the
"could it use the accessor-minting spelling" question — `Grid` is *already* on
the deftype-level minting spelling per FIXME 0867's finding; what the
annotation changes is only whether the field type is concrete):

- **emission changes exactly as this ruling would want.** Bare spelling emits
  `sig1 = (i64) -> i64`, `fn1 = u0:1`, the inline nullary-guarded atomic dec +
  `fence` + shallow call — the family-1 shape. Typed spelling emits
  `sig1 = (i64)` (void), `fn1 = colocated u0:81`, a single `call fn1(v1)` — the
  canonical glue. The field inc also loses its nullary-tag guard.
- **runtime moves zero blocks.** `solver.cl` warm: 26457/14026 under BOTH
  spellings (residue 12,431, byte-identical); driver loop 25517/13141 at N=1 and
  102065/52561 at N=4 under both.

That is a clean falsification of the "cell #21 is 0903-dominated" lead, and
also a useful soundness note for the ruling: for a **single-field** product
accessor that incs the field before returning it, the shallow and the transitive
release of `self` differ by an inc/dec pair that cancels — the shallow arm is
leak-neutral *there*. Whatever justifies the ruling for family 1, it should not
be "the exemplar measures its cost", because the exemplar measures it at zero.

### 3. Where cell #21's 12,431 actually lives (FIXME 0917)

100% in constraint propagation; `make-grid` alone is exactly balanced.
Reduced to a free-standing 30-line PrimitivesOnly repro with a control: **a
match arm returning a NULLARY constructor (`None`) beside an arm returning a
boxed `(Some …)`, over a let-bound owned heap ADT temporary** — the loop then
frees *nothing at all* (4406 allocs / 4 deallocs at N=1100; the control, which
differs only in that no arm returns the nullary ctor, is exactly balanced).
Mode-uniform (`--run` and `--link`). Filed as FIXME 0917 with the program.

**Consequence for S119 planning:** cell #21 should be re-pointed at 0917 and
should NOT be used as this FIXME's acceptance witness. The `f4_sudoku.clif`
`user::Grid.cells` re-baseline (the addendum's first obligation) stands as
written — it is a static-emission witness and this evidence does not touch it.
