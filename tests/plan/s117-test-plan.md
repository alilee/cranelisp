# Sprint 117 QA plan — conformance, recovery, and production ownership witnesses

**Status:** Phase 3 plan of record
**Authority:** `/qa`; `/testing` authors e2e sources; narrow `/dev` owners
author unit tests
**Evidence date:** 2026-07-23, current `target/debug/cranelisp`, fresh
per-probe directories

## 1. Exit verdict

`/testing` has enough information to draft the failing-first set for
0794/0836, 0800 faces 1–2, 0816, 0817, 0802, and 0839. The user has settled
the trait split: `deftrait` takes a bare-only `trait_binder`; `impl` takes a
bare-or-qualified `trait_ref`, resolved by canonical identity. QT-1/QT-2 are
therefore ungated conformance tests. The already-settled rejection of
qualified `deftrait` binders is an independent negative control and must not
be weakened.

`def` is not a core special form. It is the stdlib zero-argument-macro API
specified by spec §5.7/§9.10 and implemented in `stdlib/defs.cl`. Faces 1–2
remain REPL self-documentation defects under the existing presentation
contract. Face 3 is not a missing language ruling: whether the stdlib `def`
API should make a function-valued expansion directly callable is a
`/stdlib` user-proxy design question. `/qa` attributes and plans its test only
after `/stdlib` selects that API; `/repl` owns truthful presentation and
diagnostics for whichever API is selected.

R-2/0859 can begin without cyber-blocked instrumentation. Existing `/clif`
production artifacts plus ordinary Run/Link/REPL observations are sufficient
to specify witnesses. Their mutation gate is mandatory: changing only the
relevant declaration in `ownership_facts.rs` to a false mode must make at
least one witness fail. If the current `/clif` surface omits the needed RC
distinction, the smallest missing seam is **stable exposure of the already
emitted per-function CLIF**, not a new allocator, RC, ownership-trace, fault,
or detector mode.

## 2. Live verification and attribution

| Finding | Current observation | QA attribution / gate |
|---|---|---|
| 0794 + 0836, qualified conventional impl reference | `(impl text.display/Display Widget …)` is accepted and echoed, but dispatch fails with missing `user/Display.show$user/Widget`; bare imported `Display` works. | Settled conformance defect in `cranelisp-typecheck::traits::impl_check`: method mint/enrolment uses the as-written `TraitRef` while dispatch uses canonical resolved identity. Qualified **declaration binders** remain rejected at frontend parse. |
| 0800, stdlib `def` macro | `(def n 42)` still echoes `user/n-def`; `/info n` and `/sig n` still classify `n` as `defmacro`. | Faces 1–2 are REPL presentation defects over the specified stdlib macro expansion. Keep separate from 0816: no evidence yet that shared Pass-2/3 registration fixes the user-level `def` envelope. Face 3 is a `/stdlib` API/usability choice, not a core-language or `/spec` gap. |
| 0816, expanded `deftype` then `impl` | `(derive-Display (deftype T A B C))` still reports `unknown type T`; the later constructor is undefined. | Registration/staging defect at the expanded `begin` → shared definition registration/check path. §9.6 says each spliced form is treated in sequence; §8.2 registration order supplies the positive contract. No macro-only registrar is allowed. |
| 0817, failed codegen recovery | `vec-flatten` emits the standing generic-value codegen error; a following literal `42` repeats the byte-identical old error and span. | Transaction/recovery defect in the unified v4 session: a failed batch remains eligible on later turns. The embedded `codegen failed for /` label is a second wrong-failing-unit diagnostic and receives its own assertion/defect row. The 0488 trigger is not the owner. |
| 0802, constrained type display | `+` still displays `:(Fn [:Num a :Num a] a) num.num/+`. | Renderer omits the trait's canonical home in constraint position. `display_neg_type_always_qualified` covers concrete `Int` only; its citation on the constrained-variable row is false coverage. |
| 0839, `/info <Type>` impl listing | Built-in `/info Int` has an impl list, but a user `Box` with a live `Display` impl still has no `; impl:` section. | User-type introspection branch in `src`; data exists because `/info <Trait>` enumerates the inverse relation. Deduplication must share the pair identity used by the trait branch. |

No full suite was run. These were isolated subprocess observations, not
certification runs.

## 3. Sprint-wide failing-first e2e set

Every test below is authored by `/testing`, remains failing-not-ignored until
fixed, carries its spec citation, and carries one `// defect:` line.

### 3.1 Trait reference versus declaration binder

| ID | Proposed test | Required assertion |
|---|---|---|
| QT-1 | `qualified_impl_trait_reference_resolves_canonical_home_and_dispatches` | Define/import a foreign trait method, do not import the trait name, implement using `mod/Trait`, and dispatch successfully. Echo names the trait's true home. Exercise REPL and a file twin through Run/Link. |
| QT-2 | `qualified_impl_trait_reference_neg_does_not_mint_written_qualifier_into_method_name` | No missing-entry/codegen error may mention a writer-home trait key; `/info <Trait>` and dispatch agree on the one canonical pair. |
| QT-3 | existing `deftrait_qualified_{bare,parenthesized}_head_rejected_binder_neg` | Preserve as controls. A fix for QT-1 must not accept qualified declaration heads. No new test is needed unless `/testing` finds a missing macro-expanded binder variant. |

QT-1/QT-2 are failing-first ready against the scribed `trait_ref` rule.
QT-3 preserves the distinct `trait_binder` rule.

The ruling correctly invalidated, and `/qa` leaves unrestored pending evidence,
the S117 bands at:

- grammar §2.2.3 and §2.2.4;
- definitions §5.4, §5.4.4, and §5.11.1's method-import edge;
- traits §7.3 (including its resolvable-reference paragraph), §7.3.4,
  §7.3.5 Case 3, and §7.11.2's method-import edge.

QT-1/QT-2 supply the new conventional-reference evidence, but the broader HKT
and method-import bands require their cited matrices to be re-evaluated after
the fix. No band is restored during Phase 3.

### 3.2 Macro publication and staging

| ID | Proposed test | Required assertion |
|---|---|---|
| DF-1 | `def_definition_echo_names_user_binding_not_internal_thunk` | `(def n 42)` confirms `user/n` with value type `Int`; no `n-def` appears. |
| DF-2 | `def_info_and_sig_describe_bound_value_not_macro` | `/info n`, `/sig n`, and bare `n` agree; neither introspection route says `defmacro` or `Sexp`. |
| DF-3 | name reserved after `/stdlib` design | `/stdlib` decides whether its zero-arg macro API offers a callable function-valued binding, another explicit operation, or a deliberate rejection. After that choice, `/qa` specifies the behavioral test and `/repl` ensures presentation/diagnostics describe the stdlib API truthfully rather than pretending `def` is a core special form. |
| MB-1 | `macro_expanded_begin_deftype_then_impl_registers_in_source_order` | A macro returning `(begin (deftype T …) (impl Trait T …))` dispatches in the same turn. Use a minimal hand-authored macro, not workspace stdlib. |
| MB-2 | `macro_expanded_begin_impl_neg_before_deftype_is_rejected` | Reversed source order does not gain forward visibility accidentally. |
| MB-3 | `expanded_and_literal_begin_registration_are_twins` | REPL literal-begin control and macro-expanded form have identical registration result; Run/Link file forms use a macro output (top-level literal `begin` is forbidden in batch). |
| MB-4 | `expanded_begin_trait_family_registration_is_uniform` | Small trait matrix `{user conventional trait with required method, trait with default sibling}` × `{same expansion, pre-defined type}`. Do not use stdlib `Display`/`Eq` implementations as separate mechanism proxies. |

0800 and 0816 remain separate families. They may collapse only after a
reduction demonstrates the same failed registrar or transaction invariant.

### 3.3 Failed-turn transaction and diagnostics

| ID | Proposed test | Required assertion |
|---|---|---|
| TX-1 | `failed_codegen_turn_does_not_poison_following_literal` | In one REPL subprocess, trigger a genuine codegen failure, then evaluate `42`; the later turn returns `:primitives/Int 42` and does not repeat the prior error/span. |
| TX-2 | `failed_codegen_turn_does_not_poison_following_definition_and_call` | After the failure, define and call an unrelated function successfully; this proves registration, typecheck, batch derivation, GOT publication, and evaluation all recover. |
| TX-3 | `failed_codegen_turn_does_not_publish_partial_definition` | The symbol whose compile failed is not callable as stale/partial code and does not contaminate `/info`; a clean redefinition of that same symbol can subsequently compile and run. |
| TX-4 | `failed_codegen_diagnostic_names_actual_failing_unit_not_operator_slash` | The first diagnostic names the actual failing definition or source/module context; it must not say `codegen failed for /` unless `/` is the unit being compiled. |

These are REPL-only because they test sequential turns, but they must use
`CompilerSession`'s v4 path via the public binary. No internal session helper
or REPL-only compiler path is admissible. The trigger may initially use 0488,
but the assertion must be trigger-independent so it survives that defect's
eventual fix.

### 3.4 Display and introspection

| ID | Proposed test | Required assertion |
|---|---|---|
| TD-1 | `constraint_trait_name_displays_canonical_home_neg_no_bare_trait` | Prelude trait (`num.num/Num`) and same-named user/imported trait controls show FQ constraint names; stripping qualified tokens leaves no bare trait in constraint position. |
| TD-2 | `constraint_display_is_identical_across_definition_sig_and_bare_lookup` | Definition echo, `/sig`, and bare lookup use one canonical type renderer. |
| IN-1 | `info_type_lists_each_implemented_trait_once` | `/info Box` lists `Display` after one impl and still exactly once after a re-impl. |
| IN-2 | `info_trait_and_type_impl_views_are_inverse_twins` | The same pair appears once from `/info Trait` and once from `/info Type`; unrelated traits/types are absent. |
| IN-3 | `info_type_impls_include_local_and_imported_traits_in_canonical_order` | Preserve §4.1's local-first/imported ordering and unqualified related-symbol names. |

TD-1 replaces the false constrained-variable coverage claim currently attached
to `display_neg_type_always_qualified`; that old test remains valid for
primitive/function concrete type qualification.

## 4. R-2 / 0859 production witnesses

The witness has three layers:

1. emitted CLIF from the real compiler path for the direct primitive caller,
   which guards the primitive body's representation and lifetime semantics;
2. producer-side emitted CLIF at a control-flow merge or return-adaptation
   point where the inferred result is classified `Fresh` versus non-`Fresh`;
   and
3. value/lifetime behavior through Run, Link, and REPL.

A declaration-table assertion alone never satisfies a row. For inline Vec
operations, direct-call CLIF is deliberately **not** the declaration-mutation
gate: specialised lowering must continue to implement truthful element
materialisation and COW mechanics even when an experiment supplies false
metadata.

| Class / representative | Direct production/body guard | Declaration-sensitive production witness | Observable assertion | Required false mutation |
|---|---|---|---|---|
| Borrowed scalar-result: `str-len`, with `vec-len` sibling | `/clif` for a function calling the primitive with a live variable and with a temporary shows the caller retains the live owner, while the temporary receives its post-call release. Analysis-off control is the conservative all-Owned lowering. | The extern primitive call is already an ordinary moded edge; a second wrapper is optional rather than required for this row. | Reuse the same String/Vec before and after the call; temporary composition succeeds. Run/Link/REPL agree on scalar result and later source use. | Change the representative declaration's param from `Borrowed` to `Owned` or remove it. The existing CLIF polarity assertion must fail even if values happen to remain correct. |
| `AliasOf(0)`: `string-identity` | Returned alias keeps the return protect/ownership transfer and does not materialise a second payload. | The wrapper's inferred result and return adaptation consume the declared leaf result; the existing production wrapper is sufficient. | Source and returned alias remain usable in a scope shape that ends one before the other; Run/Link/REPL return the same string value without UAF. | Change only `AliasOf(0)` to `Fresh`; the existing production artifact witness must fail. |
| `ProjectionOf(0)`: `vec-get` with heap element | Direct CLIF materialises ownership for a heap element projected from the root; the scalar-element control has no heap materialisation. This remains invariant under false declaration mutations and is a body guard, not a declaration gate. | None has been found in the bounded Sprint-117 source shapes. Direct, wrapper, retained-root, return-adaptation, and two-function consumer probes were emission-inert under `ProjectionOf(0) → Fresh`: the escaping heap result is materialised in all relevant shapes. | Project a String, let/drop/reuse the source around the projected value in both relative lifetime orders; all modes preserve the projected value. | Typecheck transfer units retain the semantic evidence: `ProjectionOf(0)` records projected root/site provenance and differs from `Fresh` and from verbatim `AliasOf(0)`. A declaration-sensitive production artifact remains deferred in FIXME 0859; Sprint 117 makes no false production-RC claim. |
| `MayAliasOf(0)`: `vec-set`, with `vec-push` sibling | Direct CLIF pins both truthful inline COW branches: unique input mutates/returns the original allocation; shared input copies and releases according to the existing escape gate. This remains invariant under false declaration mutations and is a body guard. | `r2_may_alias_summary_protects_control_flow_merged_return` compiles a producer whose `if` joins the `vec-set` result with a fresh Vec. The non-`Fresh` summary causes the producer-side merged return to receive a protect increment. | Unique and shared-source programs preserve old/new Vec values as appropriate and return correct contents through Run/Link/REPL. | Change only `MayAliasOf(0)` to `Fresh`; the producer-side merged-return protect disappears and the named CLIF witness REDs. `MayAliasOf(0) → AliasOf(0)` remains semantically distinguished by typecheck transfer units (conditional COW-link/escape provenance versus unconditional aliasing); no distinct production RC is claimed. |

The artifact layer uses `/clif <user-function>` or the committed production
CLIF-golden facility. It compiles ordinary language source and must not
construct `ModeSummary`, `FnCompiler`, or internal sessions in e2e. Observing
only the direct specialised inline Vec body is insufficient as a declaration
gate. Narrow typecheck units own transfer distinctions that are semantically
real but intentionally collapse to the same production RC, and narrow backend
units may parse/count RC calls in emitted CLIF only through normal
wrapper-compilation support.

### 4.1 Mutation acceptance record

Each declaration mutation is applied in isolation and restored before the
next experiment. Acceptance requires:

- truthful declarations: all nine production witnesses remain GREEN — five
  CLIF witnesses, including the direct Vec body guards and the MayAlias
  producer-side merged-return witness, plus four Run/Link/REPL twins;
- `str-len: Borrowed → Owned`: existing Borrowed CLIF polarity RED;
- `string-identity: AliasOf(0) → Fresh`: existing alias-transfer CLIF RED;
- `vec-get: ProjectionOf(0) → Fresh`: direct and bounded interprocedural
  production probes are honestly recorded as emission-inert; the transfer
  unit REDs on loss of projected provenance, and FIXME 0859 remains deferred
  for the missing production-artifact seam;
- `vec-get: ProjectionOf(0) → AliasOf(0)`: typecheck transfer unit RED on
  projected provenance versus verbatim argument origin; no production RC
  difference is claimed;
- `vec-set: MayAliasOf(0) → Fresh`:
  `r2_may_alias_summary_protects_control_flow_merged_return` REDs on removal
  of the producer-side merged-return protect, while the direct unique/shared
  COW body guard remains GREEN; and
- `vec-set: MayAliasOf(0) → AliasOf(0)`: typecheck transfer unit RED on
  conditional COW-link/escape provenance versus unconditional aliasing; no
  production RC difference is claimed.

The no-public-API plan **passes**. These witnesses use the existing
`ModeSummary` carrier, typecheck transfer, ordinary user-function call edges,
normal `/clif`, and current public execution modes. They add no Rust public
API, C ABI, intrinsic catalogue entry, symbol-table schema, typed projection
carrier, compiler mode, or observation hook.

No `CRANELISP_RC_TRACE`, allocator tracing, fault injection, ownership trace,
detector mode, or new diagnostic hook is requested. If `/clif` normalisation
cannot expose the live distinctions, `/design(backend)` must define only the
stable production-artifact seam needed here and return to the user before
implementation.

## 5. Required future `/dev` unit matrices

- **`/dev(typecheck)`**: trait reference resolution
  `{bare imported, FQ same trait, FQ same-spelled foreign trait, nonexistent
  module}` × `{method mint, default synthesis, re-impl forced enrollment}`.
  Declaration-binder parsing is a separate frontend negative matrix.
- **`/dev(frontend/int)`**: macro-expanded top-level sequence
  `{deftype, deftrait, defn, defmacro}` × `{followed by dependent impl/call,
  reversed negative}` through the shared Pass-2/3 registrar. No macro-only
  registration path.
- **`/dev(src)`**: v4 transaction state
  `{typecheck fail, codegen fail, publish fail}` ×
  `{batch membership, symbol publication, GOT/introspection publication,
  next-turn retry}`. Failure rolls back only the failed turn; prior committed
  definitions survive. Failing-unit attribution uses the batch symbol, never
  an incidental expression head.
- **`/dev(src)`**: `/info` inverse-index enumeration
  `{local/imported trait}` × `{first impl, re-impl, rejected re-impl}` with
  exact pair deduplication and ordering.
- **`/dev(types/int)`**: type-render variants
  `{primitive, ADT, Fn, bare var, constrained var}` ×
  `{definition echo, bare lookup, /sig, /info}` × `{local, imported,
  same-spelled foreign}`; every named type/trait renders its canonical home.
- **`/dev(primitives+typecheck+backend)`**: the R-2 class ×
  source-shape × result-use matrices in §4. MayAlias uses the verified
  producer-side `Fresh`/non-`Fresh` merged-return seam. Typecheck transfer
  units distinguish `ProjectionOf` from `Fresh` and `AliasOf` argument origin,
  and `MayAliasOf` conditional COW-link/escape provenance from unconditional
  aliasing where production RC legitimately collapses. Mutation records use
  declaration-only changes and retain direct inline CLIF as body guards.
  Projection's missing declaration-sensitive production artifact remains
  tracked by FIXME 0859 rather than being inferred from emission-inert shapes.

## 6. Historical S115 coverage audit (0804)

The audit confirms that the S115 normative edits listed by 0804 were not
systematically invalidated. Current `[S115]` tags are delivery markers, not
coverage evidence, and several broad `[Tested]` headings predate the changed
meaning.

QA reconciliation completed 2026-07-25:

1. **Restored — trait occurrence and one-tail/default semantics.** §7.1.1 is
   now `[Tested+Neg]` against the non-nullary `Convertible` rejection, nullary
   no-occurrence rejection, self-return control, and bare-parameter control.
   §7.1.5 is `[Tested+Neg]` against inferred and annotated one-tail defaults,
   deleted legacy spelling, and replacement-default dispatch. The broad §7.1
   heading remains `[Uncovered S115 — was Tested]`: the type/value-collision
   “type wins” case and all per-impl constraint variants do not have a focused
   covering matrix.
2. **Left uncovered — method-level-only and marker boundaries.** §7.3.6's
   conventional-trait method-level-variable ruling and §7.1.1's zero-method
   marker-trait rejection have no focused behavioral evidence. Each now uses
   `[Uncovered S115 — was no prior coverage]`.
3. **Partially restored — dotted binders.** The executed dotted-binder matrix
   supports §4.3 let binders and §6.2.4 variable patterns. The broad §5 heading
   remains `[Uncovered S115 — was Tested]` because the 18-row table includes
   unverified macro-expanded and alias/platform rows. §4.5.2 remains
   `[Uncovered S115 — was tests/spec_03_types::annotated_params_int]`: that
   former test covers annotation semantics, not dotted `fn` parameter
   rejection. Newer S117 trait/impl markers were not changed.
4. **Restored — impl hot reload.** §5.4.5 is `[Tested+Neg]` against the four
   permanent `impl_redefinition_dispatch` cells: repeated replacement,
   override/default cycles, omitted-method fallback, and rejected replacement
   preserving the prior impl.
5. **Restored — constructor definition and pattern forms.** §2.2.2,
   §5.2/§5.2.1/§5.2.2/§5.2.5/§5.2.7, and §6.2.1/§6.2.2 now cite the executed
   positive/negative S116 constructor matrix. §4.2.1 remains
   `[Uncovered S115 — was
   tests/spec_04_expressions::data_constructor_undefined_error_names_constructor_strict]`
   because the former test does not cover the changed value-position `(Ctor)`
   non-application ruling.
6. **Partially restored — read-time annotation fold.** §1.8, §2.3.8, §3.9,
   §9.2, and §9.4 now cite the executed reader, macro-argument, and
   quote/quasiquote structural matrices. §1.4.5 remains
   `[Uncovered S115 — was ...]`: the focused cold/warm cache carrier test is
   still a known failing-not-ignored defect (`selected baseline macro
   dependency ... is not executable`). §9.1 remains uncovered because module
   existence does not prove the exact `SexpAnnotated` marshalling halves.

Evidence run: 67/67 across the annotation-macro, dotted-binder, trait-tail,
constructor-form, and impl-redefinition binaries; 8/8 focused frontend
reader/quasiquote units; and 8/9 across nondispatchable-trait plus structural
annotation binaries, with the sole RED the known cache-carrier defect above.
No newer `[Uncovered S117 — was ...]` provenance was overwritten.

## 7. Byte-backed text: future-only verification record

`design/arch/byte-backed-text.md` is non-normative. Sprint 117 adds no spec
coverage and no implementation test. A later, user-approved implementation
sprint should cover Byte bounds, wide/packed Vec representation parity,
literal certification and invalid source/byte inputs, transparent-product
nominal identity and exact-once ownership, Run/Link/REPL display parity,
stdlib code-point/grapheme behavior, and primitive-to-stdlib migration. Those
are design verification ideas, not current PLAN requirements.

## 8. Narrow design surfaces and phase gate

Required before implementation:

- `/design(typecheck)`: canonical trait-reference identity across explicit
  method mint, default synthesis, and re-impl enrollment.
- `/design(frontend/int)`: one macro expansion → ordinary Pass-2/3
  registration/check path, keeping 0800 separate unless reduction proves a
  shared cause.
- `/design(src)`: failed-turn transaction rollback/retry and correct
  failing-unit identity inside `CompilerSession` v4.
- `/design(src)`: inverse impl enumeration for `/info <Type>`.
- `/design(primitives+backend)`: production CLIF witness contract for R-2;
  no diagnostic instrumentation.
- `/stdlib`: choose the face-3 `def` macro/API behavior. This does not block
  faces 1–2 or any compiler conformance track.

**Phase-3 QA verdict:** pass for the compiler/recovery test wave.
`/testing` may draft QT-1/QT-2, DF-1/DF-2, MB, TX, TD, and IN now. DF-3 waits
only for `/stdlib`'s API design, not for `/spec` or a core-language ruling.
R-2 may proceed to a narrow artifact proof without cyber-sensitive hooks.

## 9. Phase-5 gate reconciliation

**Verdict: PASS to proceed to the serialized full `cargo nextest run
--no-fail-fast` gate.** This is not the full-suite verdict.

| Planned family | Gate disposition |
|---|---|
| QT-1/QT-2 plus qualified HKT twin | Delivered and reviewed GREEN. Conventional and HKT impl references consume canonical trait identity; qualified `deftrait` binders remain negative controls. |
| MB-1–MB-4 | Delivered and reviewed GREEN through the shared expansion/registration path. |
| TX-1–TX-4 | Delivered and reviewed GREEN; failed-turn state and exact failing-unit attribution recover through the v4 session. |
| TD-1/TD-2 | Delivered and reviewed GREEN; the constrained-variable coverage row in `repl/spec.md` is restored to the two canonical-renderer witnesses. |
| IN-1–IN-3 | Delivered and reviewed GREEN; type/trait views share canonical pair identity, deduplication, filtering, and ordering. |
| DF-1/DF-2 | **Explicitly deferred and intentionally RED.** The rejected post-publication implementation was removed. FIXME 0863 records the Sprint-118 cluster-wide prepared transaction. |
| DF-3 | Outside Sprint-117's language gate: it remains a later `/stdlib` API choice plus `/repl` presentation obligation, not a compiler RED attributed to this sprint. |
| R-1 | Delivered and reviewed GREEN: one closed primitive declaration inventory and derived projections. |
| R-2 | Nine production witnesses and two transfer units delivered GREEN. Borrowed, Alias, and MayAlias declaration mutation gates are demonstrated. **Projection declaration-sensitive production evidence is explicitly deferred** in FIXME 0859; it is missing evidence, not a failing test and not a regression. |
| R-3/R-4/R-5 | Delivered and reviewed GREEN: runtime-owned Vec-of-String boundary, maintained master design, and structural rustdoc. |
| 0804/0855 records | Completed by target owners; coverage reconciliation retains only evidence-backed bands. |

Static integrity:

- 27 added Sprint-117 `#[test]` functions were inspected; all 27 carry a
  `// spec:` back-reference and none is ignored.
- No in-scope `#[test]`, `// spec:` line, negative assertion, or
  failing-not-ignored guard was removed or weakened. Helper-only function
  reformatting is not counted as a test change.
- Spec→test reconciliation reports zero dead test files and zero missing cited
  functions. Eight evidence-backed S117 invalidation bands were restored;
  the remaining cleared rows are explicit S115 debt, not stale S117 bands.
- The global test→spec checker still reports pre-existing repository-wide
  malformed/mis-cited legacy annotations outside the Sprint-117 changed-test
  set. No added Sprint-117 test is among those findings.
- Cyber exclusions remain intact: no allocator/RC trace, fault injection,
  detector mode, production diagnostic hook, or memory-protection mechanism
  was added.

The exact **Sprint-117 in-scope expected failing-not-ignored set** for the full
gate is:

1. `tests/spec_11_stdlib.rs::def_definition_echo_names_user_binding_not_internal_thunk`;
2. `tests/spec_11_stdlib.rs::def_info_and_sig_describe_bound_value_not_macro`.

FIXME 0859 adds no expected RED: its Projection production-artifact witness
does not yet exist, while all committed R-2 witnesses must remain GREEN. The
full run may also report the repository's pre-existing, open-defect RED guards
outside Sprint 117 (including the S116 structural annotation cold/warm cache
carrier and cyber-excluded memory-safety guards). Those are baseline REDs only
when their exact `// defect:` attribution remains live; any other failure is a
regression and makes the final gate NOT PASS.

### 9.1 First full-gate failure classification

The failure-only rerun reported 35 failures (slow stdlib excluded). This run is
**not** a valid final gate because `/tmp` was 99% full.

| Failure group | Count | Classification |
|---|---:|---|
| `mc_x4_consume_at_distance_0719` | 5 | Environmental, not a semantic result: every failure explicitly reports linker `No space left on device`. Re-run after cleaning the test environment. |
| `launch_grid_corrupt` | 1 | Provisionally environmental: the server exited before listening during the resource-exhausted run. It is also in the load-dependent/corruption family excluded from Sprint 117. Re-run cleanly before attributing it. |
| `mode_gating_origins_are_allowlisted` | 1 | Genuine Sprint-117 gate regression, but not a semantic mode branch. `src/session_v4/lifecycle.rs` still contains the architecture-approved D1 REPL-only introspection-store allocation; rustfmt split `.populates_introspection().then` across lines, while the allowlist matches that contiguous token. Repair the guard to recognise the existing `.populates_introspection()` origin with its current D1 rationale. Do not add a second semantic branch or remove the tripwire. |
| `build_confidence::mode_equiv_macro_user_defined`; `examples::every_example_runs_with_documented_exit` (`18-macros`/`19-threading`) | 2 | Genuine Sprint-117 regression until disproved. These were green confidence/example paths and carry no live `// defect:` attribution. The common `selected baseline macro dependency ... is not executable` signature points at cached macro executable/lease restoration around the W3a owned-baseline/cache lifecycle. FIXME 0863 does **not** cover this: W3c is public-subject presentation and does not excuse cached macro execution failures. |
| `annotation_structural_s116::structural_annotation_cold_warm_cache_round_trip` | 1 | Known failing-not-ignored S116 cache-carrier defect (`class=carrier-loss`, frontend/int cache annotation carrier). Its identical “selected baseline macro dependency ... is not executable” surface may share the macro-cache mechanism above, but its existing attribution remains valid until reduction proves a common owner. It is not DF-1/DF-2 and is not newly excused by FIXME 0863. |
| `spec_11_stdlib` DF-1/DF-2 | 2 | Exact expected Sprint-117 REDs, explicitly deferred by the user in FIXME 0863. |
| Entry/program-result ownership: `adt_drop_glue_underkey` R2 plus three `program_result_owner_s116` | 4 | Expected cyber-excluded/open-defect REDs. Live `// defect:` records name entry/program-result release; Sprint 117 explicitly excluded 0745 and program-result release. |
| Capture/transitive drop glue: three `capture_drop_glue_strands_nested_heap_0760` plus `transitive_drop_glue_s116` | 4 | Expected cyber-excluded/open-defect REDs. Live records name 0760/fixed-depth recursive drop glue, both outside Sprint 117. |
| Owned match temporary: nine `match_owned_temporary_scrutinee_0810` | 9 | Expected cyber-excluded/open-defect REDs. All nine have live `rc-miscount`/`uaf` annotations at `match_codegen`; 0782/0810 family work was explicitly excluded. |
| `exemplar_ownership_residue_s116` | 1 | Expected excluded composite RED: live defect names owned-match-temporary + nested-TCO composition (0840), both outside this sprint. |
| `ms_p8_conj_leak` | 3 | Expected cyber-excluded TCO ownership REDs with live `rc-miscount` attribution. |
| `intrinsics_m3_detection_s116` | 2 | Expected excluded detector-proof failures. The M3 diagnostic production wiring/0848 family was explicitly cyber-blocked. |

Counts reconcile exactly: 6 environmental/provisional + 3 genuine
Sprint-117 blockers + 1 known S116 macro-cache RED + 2 expected W3c REDs + 23
cyber-excluded/open-defect REDs = 35.

**Blockers before a clean-environment rerun:**

1. reclaim sufficient `/tmp` space and verify linker/server startup capacity;
2. repair the mode-gating guard's formatting-fragile match while retaining the
   existing D1 allowlist rationale; and
3. reduce and fix the cached-macro executability regression on
   `mode_equiv_macro_user_defined` plus examples 18/19. If reduction proves
   the S116 structural-annotation RED has the same mechanism, update its
   attribution explicitly; do not silently fold it into W3c/0863.

After those blockers, run the full gate from a clean environment. Any failure
outside the two deferred DF tests and the exact live open-defect groups above
is a regression.

## 10. Phase-6 forward-flow findings

These findings arose while user-proxy skills exercised the shipped Sprint-117
surface. They are inputs to Sprint 118, not a reopening of the completed
Phase-5 implementation gate.

| Finding | Permanent/planned discriminator | QA attribution and disposition |
|---|---|---|
| FIXME 0867 — polymorphic products expose neither their canonical `Type.field` accessor nor the unique bare alias through the production language path | `/testing` owes `polymorphic_product_mints_canonical_and_unique_bare_accessors`: pair `(deftype (Pair a b) (MkPair [:a fst :b snd]))` with a concrete one-field control and assert both `Pair.fst` and bare `fst`; retain the existing duplicate-field ambiguity family as the negative boundary | **Coverage gap confirmed; owner handoff is `/testing` first.** The existing concrete e2e guard does not cover the type-parameter axis. A typecheck unit already proves the intended polymorphic accessor scheme, so assigning a product fix before the e2e reduction would be premature; after the RED lands, `/qa` should attribute the production registration/publication seam to narrow `/dev`. The QA obligation in 0867 is discharged by this plan row, but the finding must be retargeted to `/testing` rather than deleted. |
| FIXME 0868 — cache-restored parent omits a declared private test child | `tests/cache.rs::cache_restored_parent_enrols_private_test_child` | **Narrow RED; `/dev(src)` attribution sound.** The fresh leg discovers and runs exactly one child test. The unchanged cache-hit leg reports no functions in `m.test`. Privacy is held constant; the discriminator isolates declared-submodule enrollment after `cache_restore`, not name visibility or test selection. |
| FIXME 0869 — cache restoration loses sibling-written trait impl discovery | `tests/cache.rs::cache_restores_sibling_written_trait_impls_for_dispatch` | **Narrow RED; cross-crate design review then `/dev(src)` implementation.** Fresh qualified and imported-bare controls both dispatch to exit 7. Their unchanged warm legs both reject the same canonical `main.lib/Show` × `main.impls/W` pair, proving qualification is not causal. The failing seam is restore-time enumeration/enrollment of writer-owned impl facts; a typed cache carrier and schema change require `/arch` approval before `/dev` changes the cache boundary. |

Both committed tests carry `// spec:` and one parseable `// defect:` line,
are not ignored, and failed in a targeted 2026-07-25 run for the recorded warm
seams. They add **two** expected failing-not-ignored tests to the repository
RED set after the Phase-5 gate. FIXME 0867 adds no RED until `/testing` authors
its discriminator.

**Phase-7 QA close verdict:** no Sprint-117-close blocker. Record 0867–0869 as
forward-flow findings and schedule their test/design/implementation sequence
in Sprint 118. Do not count their expected failures as Sprint-117 regressions.

## 11. Phase-7 historical-FIXME reconciliation

Targeted rerun on 2026-07-25: **10/10 GREEN** across MB-1–MB-4, TX-1–TX-4,
and TD-1–TD-2.

- **FIXME 0816 closed.** The reported macro-expanded
  `deftype`-then-`impl` ordering defect is fixed through the shared registrar.
  Its positive, reversed-order negative, literal/expanded twin, and trait-family
  uniformity guards are permanent and green.
- **FIXME 0817 closed.** Failed codegen turns no longer poison later literals
  or definitions, publish partial same-name state, or misname the failing unit
  as `/`. The four independent public-binary guards are permanent and green.
- **FIXME 0802 closed.** Constraint-position trait names render their canonical
  home through definition echo, `/sig`, `/info`, and bare lookup. The exact
  `[Tested+Neg]` annotation is restored at `repl/spec.md` §1.4.
- **FIXME 0800 remains open under `/stdlib`.** FIXME 0863 carries only the
  deferred compiler transaction for faces 1–2. It explicitly does not settle
  face 3, the stdlib API choice for callable function-valued `def` bindings.
  Sprint outcome must therefore name 0800 alongside 0863, not treat 0863 as
  closing the umbrella finding.

## Next skills

- `/sprint` — run the full nextest gate serially and reconcile every RED
  against the exact in-scope set above plus a live open-defect record.
- `/dev` — investigate any unanticipated full-gate regression; do not alter
  the two deferred DF guards.
- `/stdlib` + `/repl` — retain DF-3 as a future API/presentation decision.
- `/testing` — author FIXME 0867's concrete-versus-polymorphic accessor repro
  before `/dev` attribution; keep 0868/0869 permanently failing-not-ignored.
- `/arch` — approve or revise 0869's typed cache-carrier/schema boundary before
  implementation.
- `/qa` — re-attribute 0867 after reduction and issue the final suite verdict
  after the full-gate result.
