# Return-type-poly ambiguity — the unresolved-dispatch signal (R16/R17)

**Status:** DESIGN (S110 Phase 3), pre-implementation. Subordinate to
`traits.md` (§6 constrained polymorphism / §7 dispatch) and `monomorphisation.md`
(the §3.11.1 ambiguity backstop). A **coordinated typecheck+int** change-set:
this note designs the **typecheck-side signal**; the cross-crate **carrier** (how
the signal reaches int's entry/eval seam) is escalated to `/arch` (FIXME 0611)
with the recommendation in §5.

## 1. The defect (S109 W6.3 rows 16/17, carried)

Dispatch WORKS. With `zed : ∀a. Zeroable a => (Fn [] a)` and Int+Float impls,
the S109 decision table rows 13–15 are GREEN:

- `:Int (zed)` → `:primitives/Int 0` — value-position concrete annotation
  resolves return-type dispatch.
- `(add-i64 (zed) 5)` → `:primitives/Int 5` — surrounding CONTEXT resolves it.

The single un-cured row is **16** (and its sibling 17): a bare, un-contextualised
return-type-poly call —

- `(zed)` alone → **§3.11 ambiguous-type error** (the target), but TODAY leaks
  `codegen error … __expr entry has no GOT slot`.
- `:Zeroable (zed)` (row 17) → still ambiguous — a value-position *constraint*
  does not disambiguate; only a concrete type does.

It is purely an **error-quality** defect: the program is genuinely ambiguous and
must be rejected; the message is wrong (an internal codegen leak instead of the
clean §3.11 "add an annotation to pin the type" message that the unpinned-`[]`
sibling already produces).

## 2. Why the naive "result-type-non-concrete" gate over-fires

The S109 W6.3 execution reverted a first attempt: a gate that flagged the
`__expr` result whenever its resolved type was non-concrete **false-positived on
`(add2 3 4)`** — which computes 7 correctly but whose recorded result type at the
span still shows a residual var ("displays unpinned"). The lesson is decisive:

> **The recorded surface type's concreteness is an unreliable ambiguity signal
> for a dispatch position.** An argument-directed dispatch (`(add2 3 4)`, Int+Int)
> RESOLVES its impl and computes fine, yet the abstract method-return var recorded
> at the call span is not always unified back to the concrete return — so
> `!ty.is_concrete()` reads a stale var and false-fires.

The genuine discriminator is not the surface type but the **dispatch outcome**:

| Call | Dispatch selects an impl? | Verdict |
|---|---|---|
| `(add2 3 4)` | YES — arg types (Int+Int) select the impl | computable, NOT ambiguous |
| `(add-i64 (zed) 5)` | YES — context pins `(zed)`'s return to Int | resolvable (row 15) |
| `:Int (zed)` | YES — annotation pins the return (row 13) | resolvable |
| `(zed)` bare | **NO** — return-directed, no arg, no context; the discriminating type stays a free var | **§3.11 ambiguous** |
| `:Zeroable (zed)` | **NO** — a constraint is a satisfaction check, not a concrete type (row 17) | **§3.11 ambiguous** |

## 3. The signal — "dispatch selected NO impl" grounded in resolution outcome

Typecheck already computes this discriminator; the signal harvests it rather than
re-inspecting surface types.

- `dispatch.rs::method_return_dispatch_type` returns `Some(concrete)` **only**
  when the method's return references `Self` AND the call's recorded return type
  is concrete after subst; it returns `None` when "the return type is still an
  unresolved var — the call context has not fixed it yet — defer." The `None`
  path is exactly the bare-`(zed)` case.
- An argument-directed call (`add2`, and `(add-i64 (zed) 5)` once the context
  pins it) resolves to a concrete `ResolvedCall` recorded at its span.

So the signal is:

> **A return-type-polymorphic dispatch site that remains UNRESOLVED after the
> final substitution** — i.e. its return-directed dispatch never selected an impl
> (`method_return_dispatch_type` still `None` / no concrete `ResolvedCall`
> recorded at the span) AND its discriminating type is still a free `Type::Var`
> at finalize.

This is grounded in the resolution *outcome*, not the recorded type's
concreteness, so it is immune to the `(add2 3 4)` false positive: `add2` has a
concrete `ResolvedCall`, so it is never in the signal set; `(add-i64 (zed) 5)`
gets its `(zed)` pinned by unification before finalize, so it too is excluded.

### 3.1 Where the signal is COMPUTED (typecheck, finalize)

At the finalisation boundary (`program/finalize.rs`, after the last
`regeneralize_defn_schemes` + the deferred-trait-call re-resolution, alongside
`find_ambiguous_top_level_form`): walk the finalised bodies and collect each
still-unresolved return-poly dispatch span. This reuses the existing deferral
machinery — a `(zed)` unresolvable during inference is deferred; finalize
re-resolves with the complete subst; whatever is STILL unresolved and
return-poly is the signal.

### 3.2 Where the signal is CONSUMED — two classes, two owners

The value positions split by who can legitimately reject:

**(a) Ordinary value positions inside a checked body** — a `let`-binding, a call
arg, a vec element carrying an unresolved return-poly result. **typecheck rejects
directly at finalize** with the §3.11 message. `find_ambiguous_value_position`
already scans these positions; the change is to make its per-node verdict at a
dispatch position consult the **dispatch-outcome signal** (§3) rather than only
the `!is_concrete()` surface predicate — so a resolved-but-surface-var `(add2 3
4)` in such a position is not flagged, while a genuinely-unresolved `(zed)` is.
This is entirely typecheck-internal.

**(b) The ENTRY / eval RESULT position** — the top expression whose *value* is
demanded by an execution boundary typecheck does not own:
- **REPL `__expr`** — the synthetic eval wrapper (`program/test_driver.rs`
  wraps a top-level `Expr` as a zero-arg `Defn` named `__expr`). Its own body
  RESULT is deliberately OUT of scope for `find_ambiguous_value_position`
  (`finalize.rs:319` — the result is displayed via introspection, and only
  children are verdicted, never the body-result expression itself). But when the
  REPL must *evaluate* `(zed)` to produce a value, `__expr` IS compiled → the
  best-effort `build_concrete_codegen_view` yields `None` on the residual var →
  backend hits the slot-less path → `__expr entry has no GOT slot`. This is the
  leak.
- **`main` (`--run`/`--link`)** — `main` is an ordinary user defn; its BODY-result
  position has the identical gap (children verdicted, the body-result expression
  not). A `main` returning bare `(zed)` leaks the same way.

**Why (b) cannot be a pure-typecheck rejection (Principle 19).** Typecheck must
NOT reject `(defn main [] (zed))` or a bare top-level `(zed)` at check time: a
poly-returning defn is a *legitimate* deferred-polymorphic value in a library or
REPL-introspection context (S109 W6.3 §3.10 / rows 10 — rank-1 poly returns are
legal; they are ambiguous only when an execution boundary DEMANDS a concrete
runnable value). Typecheck carries no entry designation — which module/fn is
`main`, and whether `__expr` is being evaluated-for-value vs introspected, is
int's knowledge. So typecheck **records the signal**; int **applies it** at the
one boundary it owns.

## 4. The typecheck-side deliverable (this note's scope)

1. **Compute the unresolved-return-poly-dispatch set at finalize** (§3.1), keyed
   by span, each carrying the method name + a gap reason (see `DispatchGap` in
   §5).
2. **Class (a):** at `find_ambiguous_value_position`, replace the dispatch-position
   verdict with the outcome-grounded signal so ordinary body positions reject
   genuinely-unresolved `(zed)` with the §3.11 message and DO NOT flag
   arg-resolved `(add2 3 4)`. Reuse the existing §3.11.1 diagnostic wording
   (`monomorphise.rs:515` — "ambiguous type; add an annotation to pin the type
   …") so the suite's ambiguity assertions and the row-16 RED share one message.
3. **Class (b):** publish the still-unresolved set on the carrier (§5) so int's
   `__expr`-eval path and `validate_main` can emit the clean §3.11 error at the
   entry/eval result position instead of letting it fall through to the backend
   GOT-slot leak.

Acceptance (typecheck half): rows 16/17 flip from the `__expr`-no-GOT-slot leak
to the clean §3.11 message; rows 13–15 stay GREEN; `(add2 3 4)` (and every
arg-directed dispatch) stays computable and unflagged — the explicit
false-positive fence from the S109 revert. `/qa` owns the row matrix; the
`(add2 3 4)`-must-not-flag cell is the load-bearing negative.

## 5. The cross-crate carrier — escalated to `/arch` (FIXME 0611)

The class-(b) signal must cross typecheck → int. Options, with this note's
recommendation:

- **(A) — RECOMMENDED — a transient field on `CheckResult`.** `CheckResult` is
  explicitly "NOT a boundary type … carries only diagnostics and optional REPL
  display payload" (`result.rs:14`), typecheck-owned, consumed only by int. A
  `Vec<UnresolvedDispatchSite>` (each `{ span: Span, method: Symbol, gap:
  DispatchGap }`, all typecheck-owned types) is exactly a diagnostic payload.
  int's `__expr`-eval path and `src/exe.rs::validate_main` read it at the
  entry/eval result span. **No `cranelisp-types` edit, no cache-schema bump** (a
  valid program has an EMPTY set — an unresolved dispatch that survived to
  finalize is precisely the error we reject, so nothing worth caching), and
  typecheck stays the sole deriver (Principle 24 — int consumes a *decision*, it
  does not re-run dispatch). Cost: a typecheck `public-api.txt` field add
  (baseline regen, `/dev`).
- **(B) — a serde'd `MethodResolutions` sidecar** (`unresolved_dispatch:
  HashMap<Span, …>`, mirroring the `pattern_ctors` precedent). Rejected as the
  primary: `MethodResolutions` is cached; caching an error-path-only map that is
  always empty for valid programs is a `CACHE_SCHEMA_VERSION` bump for no
  round-trip value.
- **(C) — a new `CranelispError`/`CheckError` variant + int re-derivation.**
  Rejected: int would have to re-inspect the entry result's dispatch state,
  re-deriving the discriminator typecheck already computed (Principle 24
  violation) and re-importing the `(add2 3 4)` false-positive risk into int.

**The `/arch` decision requested:** ratify carrier (A) — the transient
`CheckResult.unresolved_dispatch: Vec<UnresolvedDispatchSite>` field with the
site/`DispatchGap` shape — or rule an alternative. The Phase-2 Rev-4 note flagged
this "may need a types-level carrier (error variant or `CheckResult` field)";
(A) needs a `CheckResult` field but **no types-level carrier** because the site
struct is typecheck-owned and int already depends on typecheck. `/arch` confirms
whether `UnresolvedDispatchSite`/`DispatchGap` should nonetheless live in
`cranelisp-types` (if any future non-int consumer — e.g. backend defence-in-depth
at the slot-less leak site — is anticipated) or stay typecheck-local.

## 6. Principles

- **Principle 24 "Resolve once"** — the dispatch outcome is derived ONCE in
  typecheck's finalize; int reads the resolved decision at its entry/eval seam,
  never re-inspecting dispatch state.
- **Principle 19 (no module privileged by name)** — typecheck does not know
  `main`/`__expr` are special; the entry/eval-boundary application of the signal
  is int's, keeping typecheck entry-agnostic.
- **Principle 7 (single source of truth)** — one §3.11 diagnostic wording shared
  by the mono-instance gate, the value-position scan, and the entry/eval leg.
- **Principle 18 (enforce invariants structurally)** — the signal is grounded in
  the dispatch-resolution outcome (a fact typecheck holds), not a re-derivable
  surface heuristic that drifts between typecheck and int.
