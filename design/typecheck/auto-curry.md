# Auto-currying — detection, settlement, and the drain seams

Owner: `design`(typecheck). Subordinate to `typecheck.md` §9.6.
Normative source: `spec/04-expressions.md` §4.6.3 and **§4.6.3.1** (S121);
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

Four exits, and the difference between them is the subject of §2:

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

## 2. FIXME 0799 — the free-type-variable acceptance path

### 2.1 The rule, which the spec now settles

`spec/04-expressions.md` §4.6.3.1 (S121) is decisive and needs no further arbitration:

> A curried closure is an ordinary value, and the ambiguity rule of §3.11 governs it on the
> ordinary terms. **Neither the supplied nor the residual parameter positions need be
> concrete for the curry to form.** … A written parameter annotation is identical to an
> inference-generated variable. Whether a parameter carries a written annotation therefore
> MUST NOT decide whether a curry forms … Rejecting a partial application because a
> parameter was left unannotated is a defect, not an application of this rule.

Three dispositions, all inherited rather than invented:

| Shape | Disposition |
|---|---|
| a reachable use pins the residual variable — `((f 5) 3)`, `(let [h (f 5)] (h 3))` | **accepted**, and monomorphised at that use, producing the same result as the full application `(f 5 3)` |
| unpinned in a codegen-reaching value position | the §3.11.1 ambiguity error, disposition 2 of §3.11.4 |
| bare at the REPL | type display, disposition 3 of §3.11.4 |

**The ambiguity semantics are not changed by this work.** Cell (e) of the filing's matrix —
a curry whose *residual* carries a free variable that nothing pins — stays rejected by the
§3.11 gate, and that rejection is principled. What is a defect is the rejection of cells
(a), (f), (h) and (m), where a reachable use *does* pin the variable.

### 2.2 The measured axis, and the discriminating control

From the filing (HEAD `9088c82e`, `--run`, `PrimitivesOnly`), reduced to the pair that
matters:

| # | Program (`x` unannotated ⇒ free type var) | Result |
|---|---|---|
| a | `(defn g [x y] (add-i64 y 0))` → `((g 5) 3)` | **rejected**: `expected (Fn [Int] Int), got Int` |
| c | `(defn g [:Int x :Int y] …)` → `((g 5) 3)` — annotated twin | exit 3 ✓ |
| **j** | same `g` as (a), non-callee use `(add-i64 (g 5) 1)` | rejected with `got (Fn [Int] Int)` — **the curry DID form** |
| m | same `g`, let-bound then applied | rejected, same message as (a) |

**(j) beside (a) is the discriminating control**: same function, same free parameter, and
the only variable is whether the curried result is applied. The curry demonstrably forms
when the result flows to a non-application use, so the boundary is not deliberate — which
is what makes this a `wrong-reject` rather than a spec fork, and why §4.6.3.1 could be
written without a new user ruling.

### 2.3 The seam is a hypothesis — observe before designing the cure

METHOD §2.2 and the filing both say the same thing, and this design honours it rather than
pre-empting it: **the first act is to observe which arm `try_auto_curry` takes for cell (a),
not to fix from the table.**

The available hypothesis is that the callee type at `infer.rs:1121` is not yet resolved to
`Type::Fn` — because `g`'s scheme instantiates to a type whose shape is still a variable at
that point — so the guard falls through the silent `_ => Ok(None)` at `:1123`. After that an
ordinary apply-unification against a bare type variable cannot enforce arity, the inner node
types as `Int` (a *full* application of a 2-parameter function to 1 argument), and the error
surfaces at the *outer* node with exactly the observed message. It fits every observation,
including the message's location. It is still a hypothesis.

**The design rule, which holds whichever arm is taken:**

> **AC-1. The curry decision is a function of the callee's settled arity, and the callee's
> arity is on its carrier, not on the substituted type at the moment of the guard.**
> `infer_var` already resolves every `Var` once and records a typed verdict
> (`VarRef::Global(FQSymbol)` / `VarRef::Local { binder, .. }`,
> `design/arch/typed-resolution-carrier.md`). A global callee's declared parameter count is
> on its entry's scheme; a local binder's is on the binder. Reading arity from the carrier
> rather than from `apply_subst`'s current answer is Principle 24 at this seam — the type is
> a trigger, the carrier is the identity — and it is what makes the decision independent of
> how much of the callee's type inference has settled by the time the guard runs.

Two consequences follow, and both are stated as obligations rather than as a diff, because
the observation decides which of them is load-bearing:

1. **The silent fallthrough at `infer.rs:1123` stops being silent.** Whatever the arm's
   correct behaviour, an unobservable `Ok(None)` on a callee whose arity is knowable is the
   mechanism that made this invisible. Either it curries (arity known from the carrier), or
   it declines *for a stated reason* that the enclosing error can cite.
2. **Diagnostic quality is part of acceptance, not a nicety.** The present message describes
   the failure of the *application* (`expected (Fn [Int] Int), got Int`) rather than the
   reason the curry did not form, so it sends a reader to the wrong line. Whatever lands
   must say something a user can act on, and the text is pinned by a cell.

**AC-2. What must not change.** The four other exits of §1.1 keep their behaviour exactly:
`args.is_empty()` is not a curry; a constructor callee is an arity error, not a curry; a
non-`Var` callee is an error; and a curry whose residual variable nothing pins still reaches
the §3.11 gate. A fix that makes cell (a) pass by *also* accepting cell (e) has widened the
ambiguity rule and is a `review` reject.

### 2.4 Falsifiers

- **The minimal pair is (a) RED beside (j) GREEN** — one function, two uses. That pair is
  worth more than (a) alone: it pins that the curry *can* form, so a "fix" that simply
  rejects both cannot pass. Cell (c) is the born-green annotated twin control.
- A fix that changes any golden for an already-green `auto_curry_*` cell is a finding.
- A fix that makes cell (e) compile is a reject (AC-2).

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

### 3.2 The detection gap, and the honest boundary

FIXME 0779 measured the mapping's detection by flipping each seam to the opposite discipline
and running the full typecheck unit tier: **one of six** reddens (`body.rs`'s single-sig
post-pass, via
`mono_collect::tests::autocurry_over_trait_operator_never_carries_the_decl_fq`). The other
five leave the tier green.

`qa` decided the shape at S118 Phase 3 and this design consumes that decision:

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

That boundary is only honest if the *reason* per seam is written down, which is what §1.2's
table supplies: a recheck derives from state settled before it begins, so there is nothing
for a `Deferrable` polarity to hold back. The seam-level cell tests that the function's two
polarities are both correct; the table is the argument that each seam passes the right one.
Neither substitutes for the other, and neither is claimed to.

**Owner:** the cell is `dev`(typecheck)'s and lands in this visit (§4). It is the S119-owed
residual 0779 records; there was no typecheck wave in S118.

### 3.3 A stale record inside the instrument

`mono_collect.rs:810-814`'s rustdoc carries the seam census as a table of file:line pairs —
`body.rs:88`, `body.rs:441`, `impl_check.rs:762`/`:1024`, `monomorphise.rs:856`,
`finalize.rs:607` — and **every one has drifted** from the live call sites in §1.2, by
between 4 and 190 lines. The crate `CLAUDE.md` already warns "do not read the census table
as an instrument"; a census whose citations do not resolve is worse than that, it is a
record that will misroute the next reader. The correction is reserved to this visit (§4).

The durable fix is not a better line number. It is that the *set* is enumerated in this
design with its per-seam reason, and the rustdoc cites the design rather than re-listing
sites it cannot keep current.

---

## 4. What the C3 visit changes

| Item | Class | Where |
|---|---|---|
| The 0799 acceptance path | **live implementation**, observation-first | `infer.rs::try_auto_curry` + whatever the observation names; §2.3 |
| The 0779 seam-level polarity cell | **live evidence** | `program/mono_collect/tests/` per the crate `CLAUDE.md` test-home table |
| The seam → discipline table with per-seam reasons | **current-state wash** | §1.2 of this doc (done) |
| `mono_collect.rs:810-814`'s drifted census citations | **live source hygiene**, reserved | §3.3 |
| The §4.6.3 traceability band, including the free-type-variable column | **evidence**, `qa`-owned | `spec/04-expressions.md` §4.6.3/§4.6.3.1 |
| 0776's register row | **not C3's** | `arch` |

The free-type-variable column of the §4.6.3 matrix — all twelve existing `auto_curry_*`
tests curry over a *determined* type, a coverage-by-definition-variants hole — is `qa`'s to
allocate and `test`'s to author. Rows owed, each with its annotated twin: free var in the
supplied position; free var in the residual position (expect the §3.11 gate); free var in
both; ≥3 arity with the free var in a middle position; and the curried result used as a
value (the (j) shape) vs applied (the (a) shape) vs let-bound-then-applied (the (m) shape).

**Adjacency worth checking in one breath:** if the §2.3 observation lands in the drain
machinery rather than in the guard, then 0799 and 0779 are one finding — 0779's detection
gap is why 0799 was invisible — and the polarity cell should be authored to redden on it.

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
`make-adder` example), which is the same accept path §2.1 states for the unconstrained case.

**Product constructors do not auto-curry.** §1.1's constructor guard; see
`adt.md` §"Product Type Handling".

---

## 6. Cross-references

- `spec/04-expressions.md` §4.6.3, §4.6.3.1 (S121), §4.7; `spec/03-types.md` §3.11.1,
  §3.11.4
- `monomorphisation.md` §11.8.10 — the sibling multi-seam operation and its standing
  fourth-window rule
- `ownership-inference.md` §16.2 — the enumerated rule-table discipline this taxonomy is an
  instance of; `ownership/transfer/tests.rs::join_lattice_*` — the property-cell template
  0779's cell copies
- `crates/cranelisp-typecheck/CLAUDE.md` §"The two order/settlement seams" — the as-built
  memory for both cures
- `design/arch/backend-keyed-consumer.md` §1.1.1 — the AutoCurry callee-span transport
- `design/arch/typed-resolution-carrier.md` — the `VarRef`/`ApplyRef` carrier AC-1 reads
