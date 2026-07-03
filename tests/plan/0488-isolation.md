# 0488 isolation — per-signature seam attribution (S102 Phase 5, Wave 2)

**Author:** `/qa` · **Date:** 2026-07-03 · **Status:** isolation COMPLETE — all
three signatures attributed; NO fix authored (attribution-only wave per
`sprints/SPRINT.md` §Scope Block A item 3).

**Inputs:** the 3 committed guards (`tests/generic_value_use_mono.rs`), FIXME
`design/arch/fixmes/0488-…-missing-mono.md`, the isolation plan
(`tests/plan/s102-test-plan.md` §3), `tests/CLAUDE.md` §"Isolating Cross-Crate
Failures". Method: fresh-tmpdir REPL probes with `/sig`/`/list` mint
inspection between turns, `CRANELISP_CODEGEN_DUMP='*'` CLIF reads, REPL vs
`--run` cross-mode discriminators, and code-path reading of the pass-4
monomorphisation collectors. **Dirty-dir hazard:** early probes in a REUSED
cwd showed `iden$Int` "minted" at the defn turn — that was `user.cl`
persistence + `.meta.json` cache restore from prior probe sessions, not a
mint. Every finding below was re-verified in a fresh directory per session.

## The seam question, answered

Per the plan §3, for each signature: is the mono instance (i) never requested
(typecheck), (ii) requested but dropped from the codegen batch (src/
`derive_codegen_batch`), or (iii) batched but failing resolution at emission
(backend)?

**All three are category (i) — never requested. Owner: `/dev(typecheck)` for
all three. None attributes to backend `fn_as_value.rs`; 0488 does NOT ride
Wave 11 B3.1.** The two error classes ("undefined function" vs "undefined
variable") do NOT indicate two homes — both are the backend's correct
last-resort fallthrough (`compiler/apply.rs:835` call position,
`compiler/literals.rs:192` value position) after GOT resolution correctly
finds only a slot-less `Polymorphic` template (S84 Phase 4B structural slot
gate: templates carry no GOT slot; only concrete mono instances do). The
error class encodes the *reference position*, not the owning seam.

The signatures do split into TWO root-cause mechanisms (both typecheck-side):
(a)+(b) are **mono-derivation collection misses the reference shape**;
(c) is **defining-module scheme over-generalization** whose downstream
symptom happens to land in the same guard family.

## Signature (a) — FQ call position (`undefined function: user/iden`)

**Repro (fresh dir):** `(defn iden [x] x)` → `(user/iden 5)` → codegen error.
Cross-module twin: `gen.cl` defines generic `iden2`; `(gen/iden2 5)` (with or
without a prior import) → `undefined function: gen/iden2`.

**Evidence:**

- Fresh-dir `/sig iden$Int` probes: **no mono entry exists under any name**
  (`iden$Int`, `user/iden$Int`) after the failing turn. Never minted — not a
  batch or resolution problem. (Contrast: the bare-call control mints
  `iden$Int`, CLIF dump shows `user::iden$Int` + `__expr` with a GOT-indirect
  `call_indirect` through the mono's slot.)
- In the failing session `__expr` never reaches a CLIF dump — its codegen
  aborts at the un-rewritten `user/iden` call site.
- REPL ≡ `--run` (cross-module shape: identical `undefined function:
  gen/iden2`; concrete FQ control `(gen/incr2 5)` exits 0 in both modes) —
  parity places the defect below the session-side derivation.

**Call-chain attribution (typecheck, pass-4 collection —
`crates/cranelisp-typecheck/src/program.rs`):** every pass-4 collector
matches `Expr::Apply { callee: Expr::Var { name } }` where `name` is the raw
source text — for an FQ reference that is the qualified string
(`"user/iden"`). Two sub-causes:

1. **Same-module FQ** — both applicable collectors structurally exclude it:
   `collect_local_parametric_calls` resolves via
   `resolve_terminal_entry_and_home(current_module, name)`
   (`checker.rs:1676`), which probes the module table with the RAW string as
   key (`probe_module_entry_owned` — no `/`-split) → miss;
   `collect_imported_constrained_calls` resolves via the `/`-splitting
   `resolve_terminal_entry_or_prelude`, but its `home !=
   state.current_module` gate (program.rs:3484) excludes the
   home-==-current case.
2. **Cross-module FQ** — the site IS collected
   (`resolve_with_fallback` handles qualified heads; home ≠ current), but
   `monomorphise_call` → `get_constrained_fn(home=Some(h))`
   (`traits/monomorphise.rs:936`) probes
   `resolve_terminal_entry_and_home(h, "gen/iden2")` — again the raw
   qualified string as a table key in the home module → `None` → `Ok(None)`,
   no mint, and pass-4 silently records no dispatch.

   Note for the fixing dev: canonicalise the callee symbol at COLLECTION
   (split qualified → bare terminal symbol + home) rather than teaching each
   downstream layer about `/` — `build_mangled_name("gen/iden2", …)` would
   otherwise mint a `gen/iden2$Int`-named entry that nothing resolves either.

**Confidence:** high (behavioral never-minted evidence + both-mode parity +
line-level code path; the exact-line claims are code-reading, to be pinned by
the /dev unit tests below).

## Signature (b) — imported generic in value position (`undefined variable: iden2`)

**Repro (fresh dir):** `gen.cl` defines generic `iden2`; user:
`(import [gen [iden2]])`, `(defn call1 [f x] (f x))`, `(call1 iden2 5)`.

**Evidence:**

- Fresh-dir probe: `iden2$Int` **absent** after the failing turn (never
  minted). Same-module control (`(call1 iden 5)`) both works AND mints
  `iden$Int`. Imported-CONCRETE control works (concrete fns need no mint).
- REPL ≡ `--run` (identical `undefined variable: iden2`).

**Call-chain attribution (typecheck):** the fn-value-argument mono collector
`collect_parametric_fn_value_args` (program.rs:3611) carries an explicit
**`&& home == state.current_module`** gate (program.rs:3629) — the FIXME-0374
implementation only ever handled LOCAL polymorphic fn-values (its own doc
comment says "resolves … to a LOCAL monomorphisable polymorphic def"). An
imported generic resolves with `home == "gen" ≠ "user"` → excluded → no mint
→ no `rename_var_at_span` rewrite of the fn-value `Var` → backend
fn-as-value lookup lands on the slot-less template → `undefined variable`.
Second touchpoint: the mint call for fn-value sites (program.rs:3415) passes
`home: None` — relaxing the gate alone would mis-root the imported callee's
lookup/body-recheck; the callee's `home` must thread through (the FIXME-0355
module-switch machinery already exists on `monomorphise_call`).

**Confidence:** high (the gate is explicit in source; behavioral evidence
matches exactly; controls bracket the cell).

## Signature (c) — composition over a fold-bodied generic (`undefined function: vcount`)

**Repro (fresh dir):** `gen3.cl` = `vreduce`/`vreduce-loop` (generic fold),
`vconcat` (fold-bodied, passes builtin `vec-push` as a value), `vcount`
(`:Int`-returning generic). Composed turn `(vcount (vconcat [1 2] [3 4 5]))`
fails attributed to the OUTER fn while both bare calls succeed.

**Evidence (the causal chain, each link verified):**

1. **Template scheme is over-general at the DEFINING module's check** — bare
   lookup after import renders `gen3/vconcat` as **`(Fn [a (Vec b)] c)`**:
   result `c` untied from the params, first param degraded to bare `a`.
   Correct inference for the body `(vreduce vec-push va vb)` against
   `vreduce : (Fn [(Fn [a b] a) a (Vec b)] a)` (which HEAD publishes
   CORRECTLY) ties everything: `(Fn [(Vec e) (Vec e)] (Vec e))`. The
   loop-bodied sibling (`vconcat2`, direct self-recursive loop, no
   fold-callee) publishes exactly the tied shape — the fold-callee body is
   the discriminating axis, resolving the "micro-shape-sensitive" residue in
   the guard-file header at the ROOT-CAUSE level (the composed-symptom level
   sensitivity remains as recorded).
2. **Downstream skip:** at the composed turn the inner `(vconcat …)` call's
   result type is a fresh instantiation of the untied `c` — a free var.
   The OUTER `vcount` site then fails pass-4's all-args-concrete guard
   (program.rs:3361 `continue`) → no SigDispatch rewrite → codegen falls
   through to the raw name → slot-less template → `undefined function:
   vcount`. (The INNER site's args are concrete, so `vconcat$Vec+Vec` IS
   minted and rewritten — which is why the error names the outer fn.)
3. **Annotation cure (chain confirmation):** `(vcount :(Vec Int) (vconcat [1
   2] [3 4 5]))` **succeeds** — pinning the free var un-skips the outer site
   and the whole composition compiles and returns 5. Committed as the green
   control `fold_bodied_composition_with_pinning_annotation_control`.
4. REPL ≡ `--run` (identical error).

**Secondary find (for the fixing dev, not a separate guard):** the minted
`vconcat$Vec+Vec` entry's registered scheme is `(Fn [(Vec Int) (Vec Int)]
t16)` — a residual var in a Concrete mono entry. `register_mono_entry`
receives `concrete_ret_ty` captured at P1 (`instantiate_and_resolve`) BEFORE
the P4 body re-check pins it; the `codegen_view`/body are fine (turn 2 runs
correctly), only the entry scheme is stale. Harmless today but it is exactly
the shape the S84 concreteness ruling forbids at a codegen-adjacent surface.

**What remains unknown (the (c) residue):** WHERE gen3's own module check
loses the `va`/result ↔ `vreduce`-accumulator unifications at generalization
— the FIXME-0344 over-unification guard's deliberate subst-isolation is the
prime suspect (the 0488 FIXME's inference-collateral addendum points the same
way), but the exact pass/line needs /dev(typecheck)'s isolating unit test.
The committed scheme guard (`fold_bodied_generic_template_scheme_ties_params_and_result`)
pins the observable one level below the composed symptom, so the residue is
now a unit-tier question, not an e2e reduction question.

**Confidence:** high on the seam (typecheck inference/generalization) and on
the causal chain (links 1–3 each independently verified); medium on the
0344-guard suspicion (unconfirmed at line level).

## Backend + src/ exoneration (why (ii) and (iii) are excluded)

- **(ii) src/ batch derivation** (`src/worker.rs::derive_codegen_batch`):
  reads mono instances from the module symbol table (`$`-named,
  not-yet-compiled sweep). The `/sig` probes show the table never contains
  the instance — there is nothing for the batch to drop. When the table DOES
  contain it (bare-call controls; the dirty-dir cache-restore accident), the
  batch picks it up and the call works. Additionally REPL/`--run` parity on
  all three signatures argues against a session-side derivation divergence.
- **(iii) backend resolution:** the CLIF + code path show the failing name
  reaching `compile_direct_call`/`compile_var` is the RAW un-rewritten
  reference (`user/iden`, `iden2`, `vcount`); GOT resolution correctly
  refuses a slot-less `Polymorphic` template (that slot-less-ness is a
  designed invariant, S84 Phase 4B / Principle 20). The backend cannot
  resolve an instance typecheck never minted nor a call site typecheck never
  rewrote. Caveat: `ownership_fences::curried_partial_and_static_call_of_same_fn_in_one_body_compiles`
  (ledger #25) is a REAL fn_as_value.rs defect from stage-1 drafting — it is
  a DIFFERENT defect (drop-glue identifier collision), not 0488.

## Unit-test shapes for the fixing /dev(typecheck) agent

All via `cranelisp_frontend::parse` + build + `check_forms` per
`tests/CLAUDE.md` §"Isolating Cross-Crate Failures" step 3, in
`crates/cranelisp-typecheck/src/program/tests.rs` beside the existing
`callees_*` / pass-4 tests (TestFixture harness):

| # | Signature | Shape | Assert |
|---|---|---|---|
| U-a1 | (a) same-module FQ | one module `m`: `(defn iden [x] x)` + a form whose body calls `(m/iden 5)` | table contains `iden$Int` (Concrete, slotted) AND the caller's Apply node carries `resolved_call: SigDispatch{iden$Int}` |
| U-a2 | (a) cross-module FQ | fixture module `gen` with polymorphic `iden2`; current module calls `(gen/iden2 5)` (no import — FQ auto-resolution) | mono minted (bare mangled name `iden2$Int`, NOT `gen/iden2$Int`) + SigDispatch on the call node |
| U-b | (b) imported value-use | `gen` with `iden2`; current module: import + `(defn call1 [f x] (f x))` + `(call1 iden2 5)` | `iden2$Int` minted + the fn-value `Var` at the arg span REWRITTEN to the mangled name in the stored caller AST (the `rename_var_at_span` mechanism) |
| U-c1 | (c) root cause | check the `gen3` fold module alone (vreduce, vreduce-loop, vconcat) | `vconcat`'s registered scheme ties result to params: `scheme.ty == Fn([Vec a, Vec a], Vec a)` with ONE quantified var (or: result type's var ∈ param types' vars) |
| U-c2 | (c) secondary | any mono mint whose template result var is pinned only during P4 re-check | `register_mono_entry`'d scheme has a concrete return type (no residual `Var` in a `UserFnState::Concrete` entry's scheme) |

Negative rows: U-a1/U-a2 with a CONCRETE callee assert NO mono mint (concrete
fns don't mint); U-b with a same-module fn-value asserts the existing
behavior unchanged (regression fence for the 0374 path).

## Owner recommendation (for /sprint)

| Sig | Owner | Slot | Notes |
|---|---|---|---|
| (a) | /dev(typecheck) | its own src-free typecheck slot, pairable with (b) | mono-derivation reference-shape coverage: FQ heads. Two sub-causes (collector gates; `get_constrained_fn` home-probe key). Guards: `generic_fn_fq_call_monomorphises_like_bare_call` + NEW `generic_fn_cross_module_fq_call_monomorphises` |
| (b) | /dev(typecheck) | same slot as (a) | one-gate + home-threading change in the same collector family (program.rs:3629 + :3415). Guard: `imported_generic_in_value_position_monomorphises` |
| (c) | /dev(typecheck) | its OWN slot | different mechanism (generalization/0344-guard interplay), higher regression risk (touching the 0344 balance re-opens `polymorphic_accumulator_fold_does_not_over_unify` territory — that guard must stay green). Guards: `composition_over_fold_bodied_imported_generic_monomorphises` + NEW `fold_bodied_generic_template_scheme_ties_params_and_result` (+ annotation-cure green control) |

**None rides Wave 11 B3.1** — /sprint schedules separate typecheck slot(s);
the SPRINT.md Wave-11 note "0488 conditional rider iff isolation attributes
here" resolves to NOT-a-rider. Both slots are emission-affecting by the §6.2
classifier (monomorphisation derivation for green programs) — golden-corpus
interaction: 0488 shapes are corpus-EXCLUDED; the fixes EXTEND the corpus
with the newly-green shapes in the fix change-sets (extension ≠ re-baseline).

## Test deltas this wave (ledger: §"Sprint 102 Phase-5 Stage-1 QA-first RED set" addendum)

- NEW RED ×2: `generic_value_use_mono::{generic_fn_cross_module_fq_call_monomorphises,
  fold_bodied_generic_template_scheme_ties_params_and_result}` (0488 count 3 → 5).
- NEW GREEN controls ×2: `…::{concrete_fn_cross_module_fq_call_control,
  fold_bodied_composition_with_pinning_annotation_control}`.
- The 3 original guards untouched.
