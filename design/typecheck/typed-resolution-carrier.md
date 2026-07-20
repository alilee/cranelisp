# Typed resolution carrier — the typecheck PRODUCER side (S114 Track A)

**DESIGN (S114 Phase 3, `/design`(typecheck); pre-implementation).** The
producer-side pass plan for the `VarRef`/`ApplyRef` carrier flip. Subordinate to
`monomorphisation.md` (the view-build + settlement machinery it extends) and
governed by the binding cross-crate contract `design/arch/typed-resolution-carrier.md`
(where they disagree, the arch doc wins) and Principle 24 §Corollary "resolution
products travel typed". This doc elaborates **only what typecheck does**: the
chokepoint totality flip, binder-identity provenance plumbing, the view-build
gate error widening, the lenient-population census, the F-D2-10 dispatch-completeness
fix that rides the flip, and the B-2 escape-fact half.

**Archive trigger**: the Phase-5 carrier wave lands; this doc's producer contract
folds into the `infer_var` / `record_reference_target` / `build_concrete_codegen_view`
rustdoc and the arch contract archives per its own trigger.

---

## 1. The problem this pass closes

`MonoExpr::{Var,Apply}.resolved_target: Option<FQSymbol>` conflates two states
under one `None`: **local by design** (param / `let` name / match-var / lambda
param — legal) and **unresolved by producer bug** (the S113 check-gate-leak
class). Today the producer records the disambiguation only for the *Global* half:
`infer_var`'s chokepoint (infer.rs:356–360) writes `resolved_targets[span]` for a
table reference and writes **nothing** for a local — the `None` IS the local
signal, and the backend re-derives "is this a local?" by a `variables` consult.
That convention is what the flip retires: typecheck records a **TOTAL, typed
verdict for every reference** — `VarRef::Local` or `VarRef::Global`, `ApplyRef::Dispatch`
or `ApplyRef::ViaCallee` — and "unresolved" simply has no constructor, so a
dropped carrier fails as a LOCATED typecheck error at view-build, never a
codegen-time keyed miss (the wrong phase).

The two closed sums landed dormant S114 Phase 3 (`crates/cranelisp-types/src/mono_expr.rs`).
This pass is their producer.

---

## 2. The producer chokepoints — where the total verdict is recorded

### 2.1 The Var verdict — `infer_var` is the ONE chokepoint (totality holds by construction)

`infer_expr` routes **every** `Expr::Var` through `infer_var` (infer.rs:21). Every
Var that survives inference (i.e. reaches a `codegen_view` body) passes the
recording block at infer.rs:356–360 *after* all rejection gates (undefined /
special-form / internal-ctor / constrained-value / multi-sig-value), so the
recorder sees exactly the successfully-typed references. This is the totality
guarantee at the source: **one chokepoint, reached by every Var, records a verdict
for each.** The flip re-shapes those three-to-four lines from "record Global-or-nothing"
into "record one `VarRef`":

| Case at infer.rs:356–360 | Today | Under the flip → `var_refs[span]` |
|---|---|---|
| dotted `Type.member` (`resolve_dotted_member_fq` hit) | `resolved_targets[span] = fq` | `VarRef::Global(fq)` |
| local, non-self-recursion (`env.lookup` hit) | records **nothing** | `VarRef::Local { binder: name, binding_span }` |
| self-recursion carve-out (`env.lookup` hit + `is_recursion_self_ref`) | `resolved_targets[span] = enclosing-fn FQ` | `VarRef::Global(enclosing-fn FQ)` |
| ordinary resolved ref (`resolve_ref_target` Some) | `resolved_targets[span] = storage_fq()` | `VarRef::Global(storage_fq())` |
| resolved to a non-`Def` terminal / miss (`resolve_ref_target` None, but a scheme was found) | records **nothing** | records **nothing** → the view-build gate raises `Unresolved` |

The self-recursion carve-out stays a **`Global`** verdict, not a `Local`: the
enclosing defn's own recursion binding is an env-local for shadowing purposes but
a *table reference* for the backend (it compiles the non-tail self-call through
the fn's own GOT slot — `checker.rs:1583–1619` rationale). The value it records is
the enclosing fn's storage FQ; the sum variant is `Global`. This preserves the
S110 0616 semantics exactly — only the carrier *type* changes.

`record_reference_target` and the dotted leg both currently write into
`state.method_resolutions.resolved_targets`. Under the flip they write into
`state.method_resolutions.var_refs` (the split, §4). `record_reference_target`'s
signature is unchanged (it already has `state`, `name`, `span`); the local branch
that today `return`s early after the self-recursion carve-out now instead records
`VarRef::Local` before returning (see §3 for the provenance it reads).

**`callees`/`user_fn_refs` is untouched.** The `callees` reverse-index feed (the
`UserFn`-filtered projection at checker.rs:1629–1633) keys off the SAME resolution
and stays `resolved.storage_fq()` — it is a distinct sidecar with its own gate
(self-edges excluded; `UserFn`-only). The flip changes only how the *resolution
verdict* is carried, not the callees derivation.

### 2.2 The Apply verdict — the dispatch chokepoints

An `Apply`'s dispatch identity is recorded at the trait-method / sig-dispatch /
builtin / auto-curry seams (infer.rs:723/809/909/1110, mono_collect.rs:786/790,
monomorphise.rs:440/937/1090) as `resolved_calls[span]` + `resolved_targets[span]`.
Under the flip these become `apply_refs[span]`:

- A dispatch selection recorded at the Apply span → `ApplyRef::Dispatch(storage_fq)`.
- **Every other Apply** — a call whose identity rides its callee (a plain
  user-fn call whose callee `Var` carries the `VarRef`, a computed-closure call,
  a primitive-inline whose `resolved_call` is `BuiltinFn`) → `ApplyRef::ViaCallee`.
  This is a POSITIVE verdict: typecheck asserts it looked at this Apply and there
  is no *Apply-level* dispatch selection here.

The totality obligation on the Apply side is the sharper one, because most
`Apply`s take the `ViaCallee` path and today record nothing at all. The producer
must record `ViaCallee` for them. The natural seam: the Apply-inference epilogue
(the point after `resolve_calls`/`resolve_auto_curry` drain where each Apply span
either has a `resolved_calls` entry or does not) writes `ApplyRef::Dispatch` where
a `resolved_calls`/dispatch selection exists and `ApplyRef::ViaCallee` for every
other checked `Apply` span. **This is the heaviest single mechanical change in the
producer** — a walk over the checked form's Apply spans classifying each — and its
totality is what the view-build gate audits (§5, F-D2-10).

> **Note — `resolved_call` on `Var` is orthogonal.** `MonoExpr::Var.resolved_call:
> Option<Box<ResolvedCall>>` (value-position trait-method reference) stays a
> separate carrier, unchanged. The flip touches `resolved_target`→`resolution`
> and the Apply's `resolved_target`→`dispatch` only.

---

## 3. Binder-identity provenance — the scope-frame → binding-form-span plumbing

`VarRef::Local { binder, binding_span }` needs the span of the **binding form**
that introduced the referenced local. Today the scope stack (`ScopeStack`,
`scope.rs`) carries no span: `frames: Vec<HashMap<Symbol, Scheme>>`. The design
adds the binding-form span **per frame** — because every binder introduced by one
form shares that form's span (a `let`'s bindings share the `let` node; a `fn`/`defn`'s
params share the lambda/defn node; a match-arm's pattern binders share the arm
node). Per-binder spans do not exist on the AST for params, so the **form span is
the honest grain** (arch doc §2(a)).

**Chosen mechanism — a parallel `frame_spans: Vec<Span>` on `ScopeStack`.**

- `push_scope(binding_span: Span)` pushes both a fresh frame and its form span;
  `pop_scope` pops both. The base (module) frame gets `Span::SYNTHETIC` — it never
  sources a `VarRef::Local` (module-level defs resolve via the table → `Global`;
  the base frame holds no user local — the only env-locals are pushed by the six
  binding-form seams below).
- A new reader `binding_form_span(name: &str) -> Option<Span>` walks
  innermost-first (reusing the `lookup_frame` index) and returns that frame's
  `frame_spans[idx]`.
- `record_reference_target`'s local branch reads it:
  `VarRef::Local { binder: name.into(), binding_span: env.binding_form_span(name).unwrap_or(Span::SYNTHETIC) }`.

**Threading `push_scope`'s span parameter — six bounded callsites** (all have a
form span in hand today):

| Seam | Form span |
|---|---|
| `infer_let` (infer.rs:377) | the `let` node `span` |
| `infer_par_bind` (infer.rs:413) | the `ParBind` node `span` |
| `infer_lambda` (infer.rs:514) | the lambda node `span` |
| `infer_match` arm (infer.rs:1223) | `arm.span` (per-arm — the match-arm node) |
| `check_defn_body` (program/body.rs:608) | the defn form span |
| `check_impl_method` body (traits/impl_check.rs:1061) | the impl-method form span |

The `checker.rs::push_scope(&self, state)` wrapper gains the span parameter and
forwards it to `state.env.push_scope(span)`. No `bind` / `lookup` callsite changes
(the frame value type is unchanged) — the minimal-blast-radius property is the
reason this shape was chosen over the alternatives in §8.

**Rejected alternatives** (§8 records the full rationale): changing the frame
value type to `(Scheme, Span)` (touches every `bind`/`lookup` callsite for no
gain, since binders in one frame share the span); a per-binder
`HashMap<Symbol, Span>` (extra storage, same information as the per-frame span).

---

## 4. The `MethodResolutions` split + the view-build gate (error widening)

### 4.1 The sidecar split (total, typed)

`MethodResolutions.resolved_targets: HashMap<Span, FQSymbol>` splits into:

- `var_refs: HashMap<Span, VarRef>` — keyed by `Var` span (§2.1).
- `apply_refs: HashMap<Span, ApplyRef>` — keyed by `Apply` span (§2.2).

The split also retires a latent hazard the shared map carried: `Var` spans and
`Apply` spans lived in one keyspace, and a dispatch recorded at an `Apply` span
that happened to equal a `Var` span (they don't today, but nothing enforced it)
would collide. Two typed maps, two key populations.

The ~30 producer write-sites currently touching `resolved_targets` (checker.rs,
infer.rs, mono_collect.rs, monomorphise.rs, register.rs, callees.rs, body.rs)
re-target to `var_refs` or `apply_refs` per whether the keyed node is a `Var` or
an `Apply`. This is mechanical but wide; §7 pins it as one change-set half.

### 4.2 The view-build gate — `from_expr` reads non-optionally

`MonoExpr::from_expr` currently reads `resolved_targets.get(span).cloned()`
(Option) at the `Var`/`Apply` arms and cannot fail on a resolution miss. Under the
flip:

- `from_expr(expr, pattern_ctors, var_refs, apply_refs) -> Result<MonoExpr, ViewBuildError>`
  where `ViewBuildError { NotConcrete(NotConcrete), Unresolved { span: Span, name: Symbol } }`.
- The `Var` arm reads `var_refs.get(span)` non-optionally: a miss for a real-span
  `Var` is `Err(ViewBuildError::Unresolved { span, name })`. The `Apply` arm reads
  `apply_refs.get(span)` the same way.
- The `NotConcrete` arm is the existing type-incompleteness error, re-wrapped.

**This error IS the F-D2-10 safety net** (§5): a reference typecheck could not
classify surfaces here as a located typecheck-phase error, not a codegen leak.

### 4.3 The strict-first / lenient-fallback reshape — the load-bearing distinction

`build_concrete_codegen_view` (program/support.rs:257) is **strict-first,
lenient-fallback**: on `from_expr` failure it falls back to `lenient_from_expr`.
This fallback exists for legitimate **TYPE** incompleteness (multi-sig `f$Var`
variants, forward-reference result vars the backend resolves from the table). The
flip MUST preserve that fallback for `NotConcrete` **and MUST NOT let it swallow
`Unresolved`**:

```
match from_expr(&variant.body, pattern_ctors, var_refs, apply_refs) {
    Ok(mono_body)                          => Some(view),
    Err(ViewBuildError::NotConcrete(_))    => lenient fallback (type tolerance — as today),
    Err(ViewBuildError::Unresolved{..})    => propagate as a LOCATED typecheck error,
}
```

So `build_concrete_codegen_view`'s return type widens from `Option<MonoDefnVariant>`
to `Result<Option<MonoDefnVariant>, CranelispError>` (its callers — body.rs:353,
register.rs:618/1321 — thread the `?`). The `Unresolved` arm constructs a located
`CranelispError::TypeError` at the reference span with the reference name.

The **mono-instance seam** (`monomorphise.rs:569`) is already hard-error on
`from_expr` failure. Under `ViewBuildError` its `Err` arm splits: `NotConcrete(nc)`
keeps the existing "ambiguous type; add an annotation" message; `Unresolved{span,name}`
becomes a distinct located "unresolved reference in monomorphised body" error
(a producer bug in a minted instance — should never fire on a valid program, the
tier-3 seam-assert altitude but surfaced as an error since a `Result` is in hand).

### 4.4 The lenient seam-assert (`lenient_from_expr`)

`lenient_from_expr` stays **infallible** (its contract is "tolerate types"). Under
the flip its resolution-verdict reads become the §3.5-arch tier-3 seam assertion:
a real-span `Var`/`Apply` with **no** `var_refs`/`apply_refs` entry is an in-process
producer-bug breach (`safety-invariants.md` §2 tier 3), **never** a silently
manufactured `Local`/`ViaCallee`. It must `debug_assert!`-and-conservatively-continue
in a way that does not fabricate a `Local` verdict for what might be a table
reference. See §4.5 — the synthetic all-local population is handled by a *positive*
classification, not by this assert.

### 4.5 Lenient-population census — the legitimate-miss population (→ /arch, FIXME 0685)

The arch contract §3.5 requires this census before wiring the seam-assert. The
live `lenient_from_expr` callsites and their populations:

| Callsite | Population | Resolution total? | Under the flip |
|---|---|---|---|
| `build_concrete_codegen_view` fallback (support.rs:265) | real bodies, `NotConcrete` fallback (multi-sig `f$Var`, forward-ref result var) | **YES** — the paired check-run populated `var_refs`/`apply_refs` for every reference; only TYPES are incomplete | a resolution miss here IS a producer bug → tier-3 seam assert (§4.4) |
| `adt.rs:210` — synthetic **ctor** body (`Expr::ConstrADT`, `Span::SYNTHETIC`) | **all-local** — the only `Var`s are ctor param references; passes empty sidecar maps | N/A — no check-run ran; the map is empty **by construction** | the param `Var`s need `VarRef::Local`; a seam assert would wrongly fire |
| `adt.rs:612` — synthetic **accessor** body (`(match self [(Ctor .. field ..) field])`) | **all-local** — `self` (param) + `field` (match-var); non-empty `pattern_ctors`, empty `resolved_targets` | N/A — synthesised, not check-run | `self`/`field` need `VarRef::Local` |

**There IS a legitimate-miss population: the synthetic all-local bodies (adt.rs
ctor + accessor).** These are the arch doc §3.4 "synthetic bodies construct
`MonoExpr` nodes directly with the `VarRef`/`ApplyRef` in hand" camp — every `Var`
is a **local by construction**, so classifying it `VarRef::Local` is a POSITIVE
verdict, not a silent default masking a table-ref miss. Per §3.5 this comes back
to `/arch` as a FIXME naming the population, because the sanctioned shape is a
`cranelisp-types` API decision (arch-owned): either (a) rebuild these two bodies
by constructing `MonoExpr` directly with `VarRef::Local` for every `Var` (matches
§3.4 literally; larger adt.rs change), or (b) a sanctioned all-local lenient entry
point (`synthetic_local_from_expr`, or a mode signalling "every unmapped reference
here is a local by construction"). **FIXME 0685** files this to `/arch`.

The `binding_span` for these synthetic locals is `Span::SYNTHETIC` (diagnostic-only;
the backend keys `VarRef::Local` by binder name against its scope stack). The
`worker/tests.rs:84` lenient callsite is a `/dev` unit test, not a producer
population — it updates with the flip signature.

---

## 5. F-D2-10 rides the flip — the dispatch-completeness fix the totality obligates

**F-D2-10** (`nullary_return_dispatch_no_impl_rejects_naming_trait_*`, ×4):
`:Widget (zed)` pins a nullary return-type-dispatched trait method's return to a
type with **no impl**; today it accepts at typecheck and leaks `undefined function`
at codegen. The unary sibling (F-D2-7) already rejects cleanly with "no impl of
trait X for type Y" — the mechanism exists at `traits/dispatch.rs:75–90`
(`has_impl_in_home` → located error naming the trait). The nullary case never
reaches that check with a concrete return type: `try_resolve_trait_method`'s
nullary branch (dispatch.rs:53) returns `Ok(None)` (deferring) when the return
type is still a `Var` at Apply-resolution time, and the deferred re-resolution
never re-runs the no-impl check once `:Widget` has pinned the return.

**Under the carrier, the fix is obligatory, not optional.** The Apply-side
totality (§2.2) requires every checked `Apply` to record `ApplyRef::Dispatch` OR
`ApplyRef::ViaCallee`. A nullary return-dispatch that resolves to no impl can
record NEITHER a real dispatch (there is none) nor `ViaCallee` (it IS a dispatch
node) — so the producer MUST decide it at check time. The fix:

1. **Re-attempt the nullary return-dispatch from settled state** (P26 — derive
   from settled, never patch-after-record): at the post-unification epilogue where
   the return type has been pinned (the same settlement point the multi-sig
   consumer harvest uses, mono_collect / the Apply epilogue), re-run
   `try_resolve_trait_method` for the deferred nullary Apply. With the return type
   now concrete (`Widget`), it reaches `has_impl_in_home` (dispatch.rs:75) →
   **no impl → the existing located error naming the owning trait** (`Zeroable`).
2. The error already exists and already names the trait (dispatch.rs:80–89, using
   the threaded `trait_defining_module` — reachable even when the trait was never
   imported, the F-D2-10 method-only variant). No new message.

The **carrier's view-build gate is the safety net, not the primary fix**: were the
dispatch-completeness re-attempt to miss a case, the Apply would reach `from_expr`
with no `apply_refs` entry → `ViewBuildError::Unresolved` → a located typecheck
error (satisfying the "no `undefined function` leak" half). But that generic error
names the *method*, not the *trait* — so the primary fix (step 1) is what satisfies
the test's "diagnostic MUST name the owning trait `Zeroable`" assertion. F1's
insight is precisely this: draining F-D2-10 *before* the carrier would author an
interim gate patch (a bespoke nullary-no-impl guard) that the totality contract
obsoletes; riding the carrier, the fix is "make the dispatch chokepoint total,"
and the located trait-naming error is the settled-state re-resolution's natural
output. The four REDs re-shape per the test plan CA-1: a located typecheck-family
error naming the trait, uniform across REPL/`--run`/`--link`, retaining the
no-codegen-leak negative facet.

---

## 6. B-2 escape-recording — the analysis half is landed; the cache-coherence half rides the window

**Analysis side — LANDED (S113 W5b).** The match-var-pattern escape correction is
in `ownership/transfer.rs:437–489` (§16 row 3): a whole-value `Pattern::Var` arm
that binds the scrutinee and flows it outward re-walks the scrutinee in the
escaping context so its allocation escape is recorded truthfully, curing the false
`escapes=Some(false)` that defeated the backend's P25 absent-default and produced
the `(match (vec-set v 1 99) [r r])` COW-var-pattern UAF. The analysis-ON twins
(`false_fresh_provenance_residual.rs::match_scrutinee_cow_var_pattern_*`) are GREEN
on HEAD; the toggle-OFF face (`b2_match_cow_var_pattern_toggle_off_neg`) is re-attributed
to Track B (a crash surviving analysis-off cannot be owned by the analysis — /qa
0669 verdict). **Track A owns no new `transfer.rs` analysis code** unless Phase-5
evidence shows a variant still mis-records.

**Cache-coherence half — Track A, in the ONE schema window (F4/F7).** The
`escapes` fact is written onto the `MonoExpr` allocation-site nodes
(`escapes: Option<bool>`), which are serde-visible on the persisted `codegen_view`
in `.meta.json`. A warm cache built **before** the S113 W5b analysis fix carries a
stale `escapes=Some(false)` on the match/scrutinee node and would reproduce the
UAF on a cache-hit run post-fix. The cure is invalidation: the `escapes` fact's
meaning is corrected, so caches predating the fix must not be trusted. This is
subsumed by the **carrier's `CACHE_SCHEMA_VERSION` 21→22 bump** — the carrier
reshape already invalidates every `.meta.json`, and the B-2 fact correction shares
that ONE window rather than minting a second bump (the S111 0621 precedent). The
Track-A deliverable is therefore: **verify the escape-fact correction is covered
by the single 21→22 bump** (it is, by riding the same change-set) and pin the
unit-tier match-var-pattern escape test (§9 item 5) — confirm the S113 fix's unit
pin exists at `ownership/transfer.rs`'s test sibling; author it if the fix landed
e2e-only.

---

## 7. The flip change-set boundary — what compiles together

The carrier flip is **ONE coordinated multi-crate wave** (arch: "types + typecheck
+ backend + bump land as ONE serial wave; the tree must not be left broken
mid-wave"). Within that wave, the compile-together set — the boundary below which
the workspace does not compile until every member lands — is:

1. **types** (`cranelisp-types`, `/dev`-on-types within the wave): field flip
   (`MonoExpr::Var.resolution: VarRef`, `MonoExpr::Apply.dispatch: ApplyRef`);
   `MethodResolutions` split (`var_refs` + `apply_refs`); `from_expr`/`lenient_from_expr`
   signature change (typed maps + `ViewBuildError`); `public-api.txt` regen +
   `interfaces.md` §"Method Resolutions". **Plus the FIXME-0685 resolution** (the
   sanctioned synthetic all-local shape — direct construction or `synthetic_local_from_expr`).
2. **typecheck** (this pass): the §2 chokepoint verdicts (Var totality at
   infer.rs:356–360; Apply `ViaCallee`/`Dispatch` totality); the §3 provenance
   plumbing (`ScopeStack.frame_spans` + `push_scope` span threading × 6 seams);
   the §4 `MethodResolutions`-split re-targeting (~30 write-sites); the §4.3
   `build_concrete_codegen_view` `Result`-widening + its callers (`?`-threading);
   the §4.4 lenient seam-assert; the §4.5 synthetic-body construction; the §5
   F-D2-10 dispatch-completeness re-attempt.
3. **backend** (`/design`(backend) + `/dev`-on-backend, the wave's consumer half):
   exhaustive `VarRef`/`ApplyRef` matches replacing the `Option` + `variables`-consult
   convention (arch doc §4). **Not this deployment's design** — sequenced behind
   the 0669 disposition per SPRINT.md; named here only as a wave co-member.
4. **`CACHE_SCHEMA_VERSION` 21→22** (backend cache/mod.rs:354) — the ONE window,
   in this change-set, covering both the carrier reshape and the B-2 escape-fact
   correction (F7). NOT before, NOT a second bump.

The tree compiles only once 1+2+3+4 are all present — the closed sums (no
`#[non_exhaustive]`, no `Option`) mean a partial flip does not type-check, which is
the intended structural forcing (a consumer arm keeping the old convention behind
an exhaustive-looking match is impossible — there is no `None` to match).

**F-D2-10 rides the SAME change-set** (F1): its dispatch-completeness re-attempt
(§5) is a typecheck change inside member 2. The P26 full sweep + the 0653
helper-classification sweep run AFTER (as acceptance, §10).

---

## 8. Design decisions of note + rejected alternatives

- **Binder provenance = per-frame parallel `Vec<Span>`, not a frame-value-type
  change.** Chosen for minimal blast radius: `bind`/`lookup` callsites (dozens,
  incl. every inference seam and the test fixtures) are untouched; only the six
  `push_scope` seams gain a span. **Rejected**: (a) frame value `(Scheme, Span)` —
  touches every bind/lookup for no information gain, since all binders in one frame
  share the form span; (b) a per-binder `HashMap<Symbol, Span>` — redundant
  storage of the same per-form fact. Cite Principle 6 (complexity budget) +
  Principle 1 (decoupling — the span rides beside the frame, not smeared into the
  scheme).
- **The self-recursion binding stays `VarRef::Global`, not `Local`.** It is an
  env-local for shadowing but a table reference for codegen (GOT-slot self-call).
  Modelling it `Local` would send the backend to a scope-stack read that has no
  slot for it — a regression of S110 0616. The sum variant follows the *backend's*
  view (Global), the value is the enclosing fn's storage FQ. Cite Principle 24
  (the storage identity is the resolution product).
- **`ViaCallee` is recorded positively for every non-dispatch Apply**, not left
  absent. Absence is now `Unresolved` — a defect. The Apply epilogue walk that
  stamps `ViaCallee` is the totality's cost, and it is deliberate: it converts "the
  backend infers no-dispatch from a missing entry" into "typecheck asserts it
  looked." Cite the arch doc §2(b) + Principle 18 (the verdict is unforgettable).
- **The `Unresolved`-vs-`NotConcrete` split at `build_concrete_codegen_view` is
  the crux of not regressing the lenient fallback.** `NotConcrete` MUST still fall
  back to lenient (real programs with `f$Var` multi-sig variants depend on it);
  `Unresolved` MUST NOT (it is a resolution miss, the class the carrier exists to
  make loud). Conflating them — e.g. widening the fallback to swallow both — would
  silently re-open the check-gate-leak class one level up. Cite Principle 8 (no
  interim half-measure).
- **F-D2-10 fixed at the dispatch chokepoint (settled-state re-resolution), not at
  the view-build gate.** The gate names the method; the test demands the trait.
  The dispatch chokepoint holds the trait identity. Cite Principle 26 (record from
  settled state) — the re-attempt reads the pinned return type, never patches a
  pre-settlement record.

---

## 9. Unit-tier obligations (/dev, enumerated — test plan §3.4)

E2e cannot reach `from_expr`'s error arm or the lenient seam-assert. The wave's
`/dev` change-sets land unit tests (each fails on revert of its half):

1. `from_expr` with a missing `var_refs` entry for a real-span `Var` →
   `ViewBuildError::Unresolved{span,name}` (and the `apply_refs`/`Apply` sibling).
2. `lenient_from_expr` resolution miss on a REAL body → tier-3 seam assertion
   fires (never a manufactured `Local`/`ViaCallee`). The synthetic all-local
   population is the FIXME-0685 positive-classification path, separately pinned:
   a ctor/accessor body yields `VarRef::Local` for every `Var`.
3. Binder-identity provenance: `VarRef::Local.binding_span` = the binding FORM's
   span for each binder kind (defn/lambda param, `let`, match-arm) — the shadow-frame
   disambiguation grain.
4. The self-recursion carve-out records `VarRef::Global(enclosing-fn FQ)`, not
   `Local` (guards the §2.1 decision).
5. B-2 escape fact: the match-var-pattern transfer records `escapes` truthfully
   (confirm the S113 unit pin exists at the `transfer.rs` test sibling; author if
   e2e-only).

Backend-consumer unit obligations (`VarRef::Local` scope-stack miss = hard
invariant failure carrying the binder identity; `is_self_call` keys on
`VarRef::Global == current fn's storage FQ`) are `/design`(backend)'s enumeration,
noted here for the wave's completeness.

---

## 10. The orthogonal drains + MS-P7 + sequencing (Phase 4)

### 10.1 Orthogonal typecheck REDs (F2 — drain before/interleaved, NOT behind the carrier)

These are inference/harvest defects independent of the `VarRef`/`ApplyRef` field
shape; the P26-settlement discipline (`monomorphisation.md` §11.8) governs them:

- **MC-X4 / MC-X4b** (`mc_x4_multi_sig_return_consumer`, `mc_x4b_untyped_adt_field`)
  — P26-temporal consumer harvest: a poly callee consuming a multi-sig fn's bare
  return keys its mono-instance request PRE-settlement, so the request carries a
  residual `Var` and no ground instance mints (loud keyed miss — the consumer is
  correct). Fix: key the harvest on the **settled ground result** (post-drain),
  per `monomorphisation.md` §11.3.2. The two faces are the partial-fix fence.
  `class=carrier-loss`.
- **MC-X5** — raw-name overload gate (the MC-V1 verdict stands): distinct
  mechanism row, same settlement deployment. Route the overload gate through the
  settled dispatch, not a raw name re-decision.
- **PS-SH1** (`let_shadowed_multi_sig_base_value_ref_resolves_to_local_not_overload`)
  — the multi-sig-base × **value-ref** residual: `infer_var`'s multi-sig-value
  reject (infer.rs:330–342) consults `resolve_entry_scoped` **without** first
  honouring the local-shadow gate, so a `let`-shadowed `h` used in value position
  wrong-rejects as "multi-sig cannot be used as a value." Fix: gate the
  overloaded-value AND constrained-value rejects (infer.rs:309–342) behind
  `env.lookup(name).is_none()` — a locally-bound name is a `Local`, never the
  module overload base. This mirrors `monomorphisation.md` §11.8 Ruling 5 ("the
  overload gate bypasses local scope") to the value-position gate. **Design
  connection to the carrier**: this IS the local-classification the carrier makes
  total — the same "consult the shadow gate first" discipline. It may land in the
  settlement drain independently; the in-file single-sig value-ref twin is the
  GREEN control. `class=wrong-scope-lookup`. NEW ×2 value-ref cells (test plan §3.5).

### 10.2 MS-P7 — evidence brief only, NO fix designed (F5)

MS-P7 (`safety_lane_cow_set_read_returns_set_value_abort_free_red`): REPL/`--run`
correct both toggles; `--link` aborts. 0664 localizes the divergence to the
per-turn-JIT vs `ObjectModule` mode seam. Attribution is **unproven** — no fix is
designed this sprint. The `/design`(typecheck) or `/design`(backend) deployment
that first touches the mode seam produces the **call-chain evidence brief** (test
plan §3.6):

1. **CLIF identity check** — dump the failing fn's IR on both paths (per-turn JIT
   vs the `--link` `ObjectModule` build). Identical IR ⇒ the defect is downstream
   of codegen input (relocation/layout/runtime — owner backend-link or int);
   divergent IR ⇒ the producer INPUT differs per mode — name which (escape facts,
   mono-view instance, check-run pairing per `backend-keyed-consumer.md` §1.1.3)
   and why.
2. **First-divergent-frame naming** — the first frame where the two mode paths
   consume different data, not the abort symptom frame.
3. Only then attribution: typecheck if recorded facts differ at production;
   backend if identical facts consumed differently; int if the view/pairing
   assembly differs per mode.

Until the brief exists MS-P7 stays an attributed-RED carry in no wave's flip set.
/qa adjudicates from the brief.

### 10.3 Sequencing (binding on Phase 4)

1. Carrier change-set = ONE coordinated multi-crate wave (§7), serial handoffs,
   never split across a wave gate.
2. Carrier → **F-D2-10 rides** (same change-set, §5) → **P26 full typecheck sweep
   + 0653 helper-classification sweep AFTER** (the reshape changes the inventory
   they classify; the helper sweep IS the carrier's acceptance check — sweeps are
   migration aids, never the enforcement mechanism, per P24 §Corollary prong 3).
   The P26 sweep appends to the P24 register (`typecheck.md` §9.7 seed).
3. The orthogonal drains (MC-X4/X4b, MC-X5, PS-SH1) land before/interleaved — not
   serialized behind the carrier (F2).
4. Both bump-worthy changes (carrier reshape + B-2 escape-fact correction) in the
   ONE 21→22 window (F7).
5. **0590** (the four `TypeExpr` resolver mirrors, `type-expr-resolver-convergence.md`)
   is sequenced LAST among typecheck deployments and is the sanctioned defer-if-squeezed
   item. Cheap relative-position note for /dev: 0590's never-error `Named` fabrication
   arms live in `traits/type_resolve.rs` (×3) + `form.rs::check_type_expr` — a
   **type-position** resolver family (`TypeExpr → Type`), structurally disjoint
   from this carrier's **value/dispatch-position** verdicts (`Var`/`Apply` spans).
   They do not overlap the carrier's write-sites, so the carrier neither blocks nor
   is blocked by 0590; if the sprint squeezes, 0590 defers with its `_hkt`
   never-error `Named` arms flagged as a latent-defect suspicion (do not design it
   here).

---

## 11. Quality attributes touched

- **Simplicity (P6):** the flip DELETES a convention (the `None`-means-local
  backend re-derivation) and replaces it with a typed verdict — net simpler at the
  seam. The provenance plumbing is the one added mechanism, kept minimal (§8).
- **Maintainability:** a new reference-recording site cannot forget the verdict —
  the closed sums have no `None` to default, and `from_expr`'s required maps make
  the carrier unforgettable (P18). Blast radius is bounded to the one wave.
- **Observability:** `VarRef::Local` carries binder identity into the backend's
  scope-stack-miss hard error (the binder name in the message) — a producer-bug
  miss now names the binding, not an opaque slot.
- **Testability (P5):** the view-build gate is unit-reachable (§9 items 1–2); the
  totality is auditable by the P26 sweep (§10.3.2). E2e sees the F-D2-10 re-shape
  and the CA-2..4 totality positives (test plan §3.2).
- **Concurrency-safety:** untouched — the recording is per-`CheckState`, per
  check-run (the check-run pairing rule, `backend-keyed-consumer.md` §1.1.3, holds
  unchanged).
- **Performance:** one extra `HashMap` insert per reference (was one per Global-ref;
  now one per reference incl. locals) + one Apply-epilogue classification walk. The
  cost is a small constant over an already-walked form; not perf-sensitive.

---

## 12. Handoff — what `/dev`(typecheck) reads first

1. This doc §2 (chokepoint totality) + §3 (provenance plumbing) + §4 (split + gate
   + lenient reshape) — the producer contract.
2. `design/arch/typed-resolution-carrier.md` §3–§5 (binding) + Principle 24
   §Corollary.
3. `crates/cranelisp-types/src/mono_expr.rs` `VarRef`/`ApplyRef` rustdoc (the
   landed dormant sums) — the FIXME-0685 arch resolution must be in hand before
   the `from_expr` signature is touched.
4. Test plan §3.2–§3.4 (the acceptance cells + the enumerated unit-tier obligations).

**Foreseen `/dev` waves (~3):**

- **Wave A — the carrier flip** (the ONE coordinated multi-crate change-set, §7):
  types field-flip + split + `from_expr` widening (co-landed with backend consumer
  and the 21→22 bump); typecheck producer totality + provenance plumbing +
  `build_concrete_codegen_view` `Result`-widening + lenient seam-assert +
  synthetic-body construction; **F-D2-10 dispatch-completeness re-attempt rides
  here**; B-2 escape-fact in the same window. This is one atomic wave (the tree
  does not compile part-way).
- **Wave B — the orthogonal settlement drain** (before/interleaved with A per F2):
  MC-X4/X4b, MC-X5, PS-SH1 — the P26-settlement + shadow-gate fixes (§10.1). Not
  gated on the flip.
- **Wave C — sweeps as acceptance** (after A): the P26 full typecheck sweep + the
  0653 helper-classification sweep (register updates, not code); 0590 defers to
  here or beyond if squeezed.

MS-P7 produces no wave until its evidence brief (§10.2) yields an attribution.

---

## 13. Cross-skill FIXMEs filed

- **0685 → /arch** — the lenient synthetic all-local body population (adt.rs ctor
  + accessor): name the sanctioned §3.4 shape (direct `MonoExpr` construction with
  `VarRef::Local`, or a `synthetic_local_from_expr` / all-local lenient entry
  point) so the flip's `from_expr`/`lenient_from_expr` signature accounts for it.
  Blocks the types-crate half of Wave A.
