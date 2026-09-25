# Auto-currying — detection, settlement and the drain seams

Owner: `design` narrow-deployed to typecheck. Subordinate to `typecheck.md` §9.6.
Required behaviour: `spec/04-expressions.md` §4.6.3 and §4.7; `spec/03-types.md`
§3.11.1 and §3.11.4 for the ambiguity interaction.

Calling a function with fewer arguments than it declares yields a closure over the
applied arguments. This document states how typecheck detects that, where the
detection settles, and why each settlement seam uses its drain discipline.

---

## 1. Detection and settlement

### 1.1 Detection — `infer.rs::try_auto_curry`

Detection is a fallback when a direct call fails to unify inside `infer_apply`, so
the ordinary call path carries no speculative branch. The outcomes are:

| Callee and arguments | Result |
|---|---|
| No arguments | Not a curry: a bare reference or zero-argument call (§4.6.3). |
| Callee type is not `Fn`, or has no more parameters than arguments | Not a curry; the unification failure stands. |
| Callee is a constructor | A located arity error (spec §5.2.7). A product constructor's scheme is curry-shaped, so without this guard `(Point 1)` would return a closure instead of an arity error. Sum constructors take the same guard. |
| Callee is not a named variable | A located error: `((fn [a b] …) 1)` must bind the lambda first (§4.6.3). |
| Named `Fn` callee with more parameters than arguments | The applied arguments unify with the leading parameters, the result is `Fn(remaining, ret)`, and a pending record goes onto `CheckState.pending_auto_curry`. |

### 1.2 Settlement — the drain and its three seams

`program/mono_collect.rs::resolve_auto_curry` drains `pending_auto_curry` into the
resolution maps. It takes a **required** `AutoCurryDrain`:

- `Deferrable` — a pre-settlement seam. A record whose only carrier is still a
  trait-method declaration (its overload set is unsettled) moves to
  `CheckState.deferred_auto_curry` for the settled retry.
- `Final` — a settled seam. Nothing is held back; an unresolved record is resolved
  through its fallback carrier.

`Final` is the dangerous polarity: at a pre-settlement seam it strands an
unresolved trait-operator curry on a fallback carrier, which the backend then
diagnoses as a producer contradiction. So no wrapper supplies a default.

Production drains run at exactly three seams (the finalize one is step 3 of
`monomorphisation.md` §3.3):

| Seam | Discipline | Why |
|---|---|---|
| `candidate_selection.rs::settle_body_work` with `BodySettlementScope::TopLevel` — source single-signature bodies and each multi-signature clause (`program/body.rs::check_defn_body`) | `Deferrable` | The callee's overload set may still be unsettled; the record waits for the settled window. |
| `settle_body_work` with `BodySettlementScope::Isolated` — explicit, synthesised-default and HKT impl methods and mono-instance rechecks (`traits/impl_check.rs::check_defn_body_with_types`) | `Final` | The body is rechecked against already-concrete types, and its resolution maps and module scope are swapped for the recheck, so nothing may be deferred out of it. |
| `program/finalize.rs`, immediately after `resolve_pending_overloads` | `Final` | Overload sets are settled. This is the only drain of `deferred_auto_curry`: the deferred records are spliced back into `pending_auto_curry` first. |

The body kind selects the scope through the two shared body wrappers, and the scope
selects the drain discipline. A new body-check seam therefore reaches a discipline
only by choosing a wrapper or passing an explicit scope; it cannot inherit `Final`
by calling the obvious function.

The drain takes the pending list by value (`mem::take`), so a `Deferrable` seam that
holds a record back leaves it for the finalize drain and needs no ordering against
other drains.

### 1.3 Carriers

- `CheckState.pending_auto_curry` and `CheckState.deferred_auto_curry` are
  transient per-cluster lists; a failed cluster discards them with the rest of its
  state (`typecheck.md` §7.4).
- `ResolvedCall::AutoCurry { target_name, applied_count, total_count, .. }` in
  `cranelisp-types` carries the wrapper's arity to the backend. For a let-bound
  closure the backend reads the code pointer from the environment.
- The pending record keeps the callee variable's span, so the drain transports that
  reference's already-recorded carrier (`design/arch/backend-keyed-consumer.md`
  §1.1.1).

---

## 2. Free variables remain in the ordinary inference context

Forming a residual closure does not generalise unresolved monotype variables
(`spec/04-expressions.md` §4.6.3). They stay in the same inference context, a later
use may constrain them, and a variable still unresolved after inference falls under
the ordinary ambiguity rule of `spec/03-types.md` §3.11. Auto-currying has no
ambiguity rule of its own.

For example, after `(defn supplied-free [x :Int y] (add-i64 y 0))`,
`((supplied-free 5) 3)` returns `3`, and passing `(supplied-free 5)` to a scalar
consumer is rejected with the residual function type. The executing cells are
`tests/spec_04_expressions.rs::auto_curry_supplied_free_variable_then_apply` and
`auto_curry_supplied_free_variable_forms_residual_control`.

---

## 3. The seam taxonomy

### 3.1 The per-operation rule

Where one operation runs at several non-equivalent settlement seams, this crate
enumerates the seams in the operation's design with the discipline and reason for
each, and makes the discipline a required input. Two operations have such a set:

- the auto-curry drain (§1.2); and
- `pass4_monomorphise`'s two settlement windows (`monomorphisation.md` §3.3 and
  §11.8.10), whose standing rule routes any new window to `arch` for a class
  ruling.

Whether that rule becomes a general principle is `arch`'s open decision
(`design/arch/fixmes/0776-arch-settlement-seam-multiplicity-register-row.md`);
this design does not presume it.

### 3.2 Evidence and its boundary

- **Structural.** Omitting the discipline does not compile: `resolve_auto_curry`
  and `settle_body_work` both take it as a required argument.
- **Measured.** `program::mono_collect::tests::auto_curry_drain_polarities_handle_unresolved_trait_decl_carrier`
  drives both disciplines over the same seeded unresolved trait-declaration
  carrier. It was proven to detect: a planted single-polarity drain failed it, and
  the restored drain passed. It is modelled on the ownership join-lattice property
  cells (`crates/cranelisp-typecheck/src/ownership/transfer/tests.rs`,
  `join_lattice_*`).
- **Asserted, with a named falsifier.** That each seam passes the right
  discipline rests on §1.2's reasons, not on a per-seam behavioural cell. The
  isolated recheck seams are `Final` by construction: a recheck starts from settled
  state, so a `Deferrable` polarity would have nothing to hold back, and a
  per-seam cell would need a program whose settled carrier differs by discipline
  there. A production call of either function missing from §1.2's table, or one
  whose discipline contradicts its documented settlement state, refutes the claim.

---

## 4. Edge cases

- **Bare function references.** `(let [f add] …)` is a variable reference, not a
  curry. A bare reference to a multi-signature name is a compile error (§4.6.3,
  §4.7), because the variant cannot be determined.
- **Zero-argument functions.** `(f)` on `(defn f [] 42)` is a normal call; no
  curry is possible.
- **Currying a curried result.** In `(let [f (add3 1)] (let [g (f 2)] (g 3)))`,
  `f` has type `(Fn [Int Int] Int)`; `(f 2)` fails direct unification and the
  fallback fires on the let-bound closure. The backend's wrapper captures the old
  environment pointer plus the new arguments.
- **Operator curry `(+ 1)`.** `+` resolves through trait dispatch; its callee type
  fails direct unification against one argument, and the fallback yields
  `(Fn [Int] Int)`. A constrained operator keeps its constraint and is
  monomorphised where the concrete types become known (§4.6.3's `make-adder`),
  the same inference-context behaviour as §2.
- **Product constructors do not auto-curry** (§1.1; `adt.md` §"Product Type
  Handling").
