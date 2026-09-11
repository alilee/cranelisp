# Auto-currying — detection, settlement, and the drain seams

Owner: `design`(typecheck). Subordinate to `typecheck.md` §9.6.
Normative source: `spec/04-expressions.md` §4.6.3;
`spec/03-types.md` §3.11.1/§3.11.4 for the ambiguity interaction.

Auto-currying is the language feature where calling a function with fewer arguments than it
declares parameters yields a closure capturing the applied arguments. This document
describes how the crate detects it, where the detection is settled, and what the S121 C3
visit changes.

**Supersedes the pre-implementation sketch this file used to carry.** That version compared
against the retired prototype, named the retired `TypeChecker` type, and proposed adding
`total_count` to `ResolvedCall::AutoCurry` — all landed or obsolete. `sprints/archive/`
holds the historical record; the current shape is §1.

---

## 1. Current state (verified at HEAD 2026-09-01)

### 1.1 Detection — `infer.rs::try_auto_curry`

Detection is a fallback on unification failure inside `infer_apply`, which is the right
trigger because it means "these types do not match as a direct call" without a speculative
branch on the normal path. `try_auto_curry` is defined at `infer.rs:1106` and called from
`infer.rs:983`.

Five outcomes define the detection boundary. Section 2 records the current
free-variable behavior without changing that boundary:

| Exit | Site | Behaviour |
|---|---|---|
| Empty argument list | `infer.rs:1115-1117` | `Ok(None)` — silent. `args.is_empty()` is a bare reference or a zero-arg call, never a curry (§4.6.3). |
| Callee is `Type::Fn` with more parameters than arguments | `infer.rs:1121-1122` | the curry forms: applied args unify with the leading parameters, the result is `Fn(remaining, ret)`, and a record is pushed onto `pending_auto_curry`. |
| **Callee is anything else** | `infer.rs:1123` — `_ => return Ok(None)` | **silent.** This is the arm §2 is about. |
| Callee is a constructor | `infer.rs:1138-1150` | a located arity `TypeError` (spec §5.2.7). A product ctor's scheme is curry-shaped, so without this guard `(Point 1)` would silently return a closure instead of an arity error. Sum ctors hit the same guard. |
| Callee is not a `Var` | `infer.rs:1153-1158` | a hard error. `((fn [a b] …) 1)` must bind the lambda to a variable first (§4.6.3). |

### 1.2 Settlement — `resolve_auto_curry` and its six seams

`mono_collect.rs:815` drains `pending_auto_curry` into `MethodResolutions`. Its signature
takes a **required** `AutoCurryDrain` (`mono_collect.rs:39-49`, variants `Deferrable` and
`Final`, re-exported at `program/mod.rs:51`). There is no defaulting wrapper and no short
convenience name: `Final` — "this seam is settled, nothing is held back" — is the dangerous
polarity, so a new seam must never inherit it for free (FIXME 0775, Principle 18, landed
S115 W4b).

The drain runs at **six** non-equivalent production seams:

| # | Seam | Discipline | Why |
|---|---|---|---|
| 1 | `program/body.rs:92` | `Deferrable` | single-sig body post-pass; the callee's overload set may still be unsettled, so a curry over a multi-sig base is held for the finalize drain |
| 2 | `program/body.rs:467` | `Deferrable` | the same, per multi-sig clause |
| 3 | `program/finalize.rs:632` | `Final` | runs immediately after `resolve_pending_overloads`; the overload sets are settled, so nothing may be held back |
| 4 | `traits/impl_check.rs:923` | `Final` | explicit impl-method body check — a recheck over settled state |
| 5 | `traits/impl_check.rs:1212` | `Final` | default/synthesised impl-method body check — the same |
| 6 | `traits/monomorphise.rs:870` | `Final` | mono-instance body recheck — settled by construction; the instance exists only because its argument types were already concrete |

Seams 1–2 are the two *per-form* body passes; 3 is the *settlement* drain; 4–6 are
*recheck-scoped* — each re-derives from state that is settled before the recheck begins.
That is the whole taxonomy, and §3 makes it a required input rather than prose.

`transfer.rs`-style ordering concerns do not apply here: the drain is idempotent over a
taken list (`mem::take`), so a `Deferrable` seam that holds a record back simply leaves it
for seam 3.

### 1.3 Carriers

- `pending_auto_curry` on `CheckState` — the transient per-check list, included in
  `ReplSnapshot` so REPL error recovery restores it.
- `ResolvedCall::AutoCurry { target_name, applied_count, total_count }` in
  `cranelisp-types` — carries `total_count`, so the backend knows the wrapper closure's
  arity. `target_name` is the variable name; for a let-bound closure the backend reads the
  code pointer from the environment, which is entirely a backend concern.
- The callee-span transport added at S110 W0.1 keeps the curry site's resolution keyed
  (`design/arch/backend-keyed-consumer.md` §1.1.1).

---

## 2. Free variables remain in the ordinary inference context

`spec/04-expressions.md` §4.6.3 now carries the complete rule. Forming a residual
closure does not generalize unresolved monotype variables. They remain in the same
inference context and a later use may constrain them; any variable still unresolved
after inference is handled by the ordinary §3.11 ambiguity rule.

The S122 Q10 discriminator confirms that this is the current implementation behavior,
without a production change:

| Public shape | Current evidence |
|---|---|
| `(defn supplied-free [x :Int y] (add-i64 y 0))` followed by `((supplied-free 5) 3)` | succeeds and returns `3` |
| pass `(supplied-free 5)` to a scalar consumer | rejects and exposes the residual function type |

The exact cells are
`tests/spec_04_expressions.rs::auto_curry_supplied_free_variable_then_apply` and
`auto_curry_supplied_free_variable_forms_residual_control`; both pass in
`/tmp/s122-q10-current-shapes-dc78ddbe.log`. The historical 0799 wrong-reject no
longer reproduces, so its observation-first repair, alternate diagnostic, carrier-arity
mechanism and semantic-fork prose are retired. This pair does not establish that every
historical matrix cell ran, and it does not widen the ambiguity rule. FIXME 0779's drain
polarity evidence was completed separately in §3.

---

## 3. The seam taxonomy — FIXME 0776's typecheck instance, FIXME 0779's evidence

### 3.1 The class, and where the ruling lives

FIXME 0776 proposes a register row: *when one operation runs at more than one settlement
seam, the seams are an enumerated set with a named discipline per seam, and the discipline
is a required input at every call site — never a default, never prose. Growing the set is an
architectural event.* Four instances were cited inside this crate: the three
`pass4_monomorphise` settlement windows (`monomorphisation.md` §11.8.10), this drain's six
seams, the inline-vs-deferred overload dispatch arm, and §11.8.9's own scan discipline.

**The class ruling is `arch`'s and stays with `arch`** — C3 does not author a register row
or a principle. What C3 owes is the *instance*: this crate's two multi-seam operations each
carry an enumerated seam set with a stated per-seam reason, in their design, so the seam →
discipline mapping is checkable rather than folklore.

- The drain's set is §1.2's table. It is complete at six production seams plus one
  test-only call (`program/mono_collect/tests/carriers.rs:734`).
- `pass4_monomorphise`'s set is `monomorphisation.md` §11.8.10's three windows, already
  enumerated with per-window justification and a standing "a fourth forces an `arch` class
  ruling" rule.

The structural half — a **required** `AutoCurryDrain` parameter, so a new seam cannot
inherit `Final` silently — landed S115 W4b and is verified live (`mono_collect.rs:815`).

### 3.2 The detection evidence, and the honest boundary

FIXME 0779 measured the mapping's detection by flipping each seam to the opposite discipline
and running the full typecheck unit tier: **one of six** reddens (`body.rs`'s single-sig
post-pass, via
`mono_collect::tests::autocurry_over_trait_operator_never_carries_the_decl_fq`). The other
five leave the tier green.

`qa` decided the shape at S118 Phase 3 and the S122 evidence implements that decision:

> **Candidate (1) adopted** — a **seam-level polarity cell** driving `resolve_auto_curry`
> directly over a seeded `pending_auto_curry`, testing both disciplines exhaustively at the
> function. The template is the `join_lattice_*` property cells in
> `ownership/transfer/tests.rs`: seam-level property cells over the operand set, with no
> program shape to fight.
>
> **Candidate (2) declined for the recheck seams** — a per-seam behavioural cell needs a
> program whose settled carrier differs by discipline at that seam, which is the hard part
> for seams 4–6 precisely because a recheck is settled by construction. The honest
> disposition is recorded rather than left as a silent gap: **seams 4, 5 and 6 are `Final`
> by construction, not by test.**

`program::mono_collect::tests::auto_curry_drain_polarities_handle_unresolved_trait_decl_carrier`
now drives both disciplines over the same seeded unresolved trait-declaration carrier.
The single-polarity plant fails at deferred count 0 versus 1; the restored implementation
passes 1/1. Evidence is recorded in
`/tmp/s122-0779-polarity-plant-red-dc78ddbe.log` and
`/tmp/s122-0779-polarity-restored-green-dc78ddbe.log`.

That boundary is only honest if the *reason* per seam is written down, which is what §1.2's
table supplies: a recheck derives from state settled before it begins, so there is nothing
for a `Deferrable` polarity to hold back. The unit asserts the function's two polarities;
the table is the construction argument that each seam passes the right one. This is not a
claim of six independent caller-seam behavioral proofs. FIXME 0779 is closed.

### 3.3 The source census points here

`mono_collect.rs` now cites this design instead of maintaining drifting file-and-line
copies. Section 1.2 remains the durable seam census and construction rationale.

---

## 4. What the C3 visit changes

| Item | Class | Where |
|---|---|---|
| The 0799 acceptance path | **current behavior; filing retired** | §2's Q10 public pair; no production change |
| The 0779 seam-level polarity cell | **evidence complete; filing retired** | `program::mono_collect::tests::auto_curry_drain_polarities_handle_unresolved_trait_decl_carrier`; §3.2 |
| The seam → discipline table with per-seam reasons | **current-state wash** | §1.2 of this doc (done) |
| The source census comment | **corrected** | points to §1.2 rather than duplicating line citations |
| The §4.6.3 supplied-free-variable pair | **evidence complete** | `tests/spec_04_expressions.rs`; §2 |
| 0776's register row | **not C3's** | `arch` |

No historical matrix is resurrected from 0799. The 0779 unit and comment repair are
complete, without claiming six caller-seam behavioral proofs.

---

## 5. Edge cases (retained, verified)

**Bare function references (zero args).** `(let [f add] …)` is a normal variable reference,
not a curry; the `args.is_empty()` guard prevents it. For a multi-sig name a bare reference
is a compile error (§4.6.3, and §4.7's restriction), because the compiler cannot determine
which variant is meant.

**Zero-arg functions.** `(defn f [] 42)` — `(f)` is a normal call. There is no curry for a
zero-arg function because there are no fewer than zero arguments to supply.

**Currying a curried result.** `(let [f (add3 1)] (let [g (f 2)] (g 3)))` works because `f`
has type `(Fn [Int Int] Int)`, `(f 2)` supplies 1 of 2, unification fails, and the fallback
fires. The callee is a `Var` naming a let-bound closure rather than a top-level function, so
the record is still pushed and the backend generates a wrapper that captures the old
environment pointer plus the new arguments.

**Operator curry `(+ 1)`.** `+` resolves via trait dispatch to `Num.+`; the callee type after
resolution is `(Fn [Int Int] Int)`, unification against `(Fn [Int] ?ret)` fails, and the
fallback yields `(Fn [Int] Int)`. Constrained polymorphic operators inherit the constraint
and are monomorphised at the call site where concrete types become known (§4.6.3's
`make-adder` example), which is the same inference-context behavior §2 records for the
unconstrained case.

**Product constructors do not auto-curry.** §1.1's constructor guard; see
`adt.md` §"Product Type Handling".

---

## 6. Cross-references

- `spec/04-expressions.md` §4.6.3, §4.7; `spec/03-types.md` §3.11.1,
  §3.11.4
- `monomorphisation.md` §11.8.10 — the sibling multi-seam operation and its standing
  fourth-window rule
- `ownership-inference.md` §16.2 — the enumerated rule-table discipline this taxonomy is an
  instance of; `ownership/transfer/tests.rs::join_lattice_*` — the property-cell template
  0779's cell copies
- `crates/cranelisp-typecheck/CLAUDE.md` §"The two order/settlement seams" — the as-built
  memory for both cures
- `design/arch/backend-keyed-consumer.md` §1.1.1 — the AutoCurry callee-span transport
