# Inference Engine

Solution design for the Cranelisp type inference engine. Covers Algorithm W implementation, unification, substitution strategy, and per-ring evolution.

## Architecture

The typechecker is structured as a single `TypeChecker` struct with `impl` blocks split across multiple modules using Rust's borrow-splitting pattern. Hot-path functions (`unify`, `fresh_var`) take explicit `&mut Subst` / `&mut TypeId` parameters to avoid `&mut self` conflicts.

### Module Layout

| Module | Responsibility |
|--------|---------------|
| `checker.rs` | `TypeChecker` struct definition, scope ops, fresh var generation, unification delegation |
| `infer.rs` | Expression type inference: one helper method per `Expr` variant |
| `program.rs` | Two-pass batch checking (`check_program`) and REPL input checking (`check_repl_input`) |
| `unify.rs` | Unification algorithm with occurs check |
| `scheme.rs` | Scheme instantiation (`instantiate`) and generalization (`generalize`) |
| `scope.rs` | Lexical scope stack for local bindings |
| `resolve.rs` | `TypeExpr` -> `Type` resolution (annotations, type expressions) |
| `adt.rs` | ADT registration, constructor schemes, exhaustiveness checking |
| `builtins.rs` | Ring 0 primitive type scheme registration |

### Key Design Decisions

**Borrow-splitting over method chaining**: Free functions for `unify` and `fresh_var` take `&mut Subst` / `&mut TypeId` rather than `&mut self`. This avoids borrow conflicts when inference needs both substitution and fresh variable generation simultaneously. The `TypeChecker` methods are thin wrappers.

**Per-variant infer helpers**: `infer_expr` dispatches to `infer_int_lit`, `infer_var`, `infer_lambda`, etc. Each helper is 10-40 lines, independently testable. This addresses the sketch audit finding HIGH-1 (monolithic `infer_expr`).

**Single substitution**: One global `Subst` (HashMap<TypeId, Type>) for the entire compilation unit. No separate "local" substitutions. This matches standard Algorithm W.

## Two-Pass Pipeline

Batch mode (`check_program`) uses two passes:

1. **Pass 1 — Registration**: Register type definitions (`TypeDef`), then register function signatures with fresh type variables. Functions are added to the symbol table with monomorphic schemes containing fresh vars.

2. **Pass 2 — Checking**: Check each function body. Bind parameters to the fresh vars from Pass 1, infer the body type, unify with the return type var. After all bodies are checked, generalize each function's type and update the symbol table.

This supports forward references: function `f` can call function `g` defined later in the same program, because `g`'s signature (with fresh vars) is registered before any bodies are checked.

### REPL Mode

`check_repl_input` handles one definition or expression at a time. For definitions, it does registration + body checking + generalization in a single step (no forward references across REPL inputs). The REPL supports snapshot/restore for error recovery.

### Cross-Defn Generalization Timing (FIXME 0344)

The two-pass shape above has a generalization-timing hazard for **a defn that calls a sibling defn in the same cluster**. Pass 1 registers every signature as `mono(fn_type)` — a *monomorphic* scheme whose param/ret vars are bare fresh vars (`type_vars` empty). Pass 2 checks each body in **source order**, but the per-defn generalized scheme is only written back to the symbol table in `finalize_check_result_inner` Phase 2 (`program.rs` ~line 1102), **after all bodies are checked**.

Consequence: while body B of `caller` is checked, a call to `callee` resolves through `infer_var` → `instantiate` against `callee`'s *still-monomorphic* entry. Because `type_vars` is empty, `instantiate_scheme` returns the entry's `Type::Fn(...)` **verbatim — no fresh copy**. The call's argument types therefore unify *directly into `callee`'s own fresh param vars in the shared global `Subst`*. Those same vars are then unified again by `callee`'s own body (including its recursion) and by every other caller. All such constraints land on one set of vars — they collapse.

This is the textbook behaviour of monomorphic let-rec-group inference: **sound but over-restrictive**. It only manifests when a callee threads a type variable that *should be independently instantiable per call* and that variable is constrained differently across call sites. The fold shape is the canonical trigger: `vec-reduce-loop`'s accumulator `b` is constrained to `Int` by `vec-reduce`'s `(... 0 ...)` call and to `(Vec a)` by any other caller, while `b` is also `f`'s return slot — so `b`, `a`, and `Vec` fuse. `vec-map`/`vec-filter` escape because their loop's accumulator is pinned to `(Vec a)` *at its initial-call argument* (literal `[]`), so every caller already agrees on the type — there is no independently-instantiable accumulator to collapse.

**Design ruling — generalize-before-cross-defn-use, NOT polymorphic recursion.** The fix is to give cross-defn call sites a *generalized* (instantiable) view of the callee. It is **NOT** to make a function's self-reference polymorphic — `check_defn_body` binds the recursion name `mono(fn_type)` (line 1947) and that is **correct and must stay**: polymorphic recursion is undecidable in HM, and the spec's `let`/`fn` polymorphism (spec §3.5.3 / §5) generalizes at the *binding group* boundary, not within a body. The correct seam is to **generalize each defn immediately after its body is checked (in `check_form_body_single_defn`, after line 832 where `trial_scheme` is already computed) and write the generalized scheme back to the symbol-table entry**, so a later-source sibling that calls it instantiates a fresh copy. The same writeback must also cover the *caller-before-callee* source order: a caller checked before its callee's body still sees the monomorphic entry, so the durable correctness guarantee is "generalize the binding group as a unit and re-expose generalized schemes to any cross-defn reference." The minimal implementation is the per-defn post-body writeback (it fixes the common callee-before-caller order and the fold repro); the complete implementation generalizes the strongly-connected-component group and instantiates non-self references. The unit test pins the *observable* contract (correct inferred scheme + a green call), leaving the implementation free to choose the minimal-vs-complete mechanism so long as the scheme is right.

## Written type variables (spec §3.3.1–§3.3.5, shipped model S109 W6.3)

A source author may **write** a type variable in a parameter or return annotation
(`(defn id [:a x] x)`, `:a "hello"`, `:(Box a)`). The engine's treatment of a
written var is fixed by spec §3.3.1–§3.3.5; this section records how that model
is realized in the inference engine and — as important — **what it is not**, so a
future reader does not re-introduce the discarded intermediate models.

### Design evolution — three states, only the last shipped

The model went through three states within S109; **only W6.3 is the engine's
behaviour**, and the two earlier states must not be transcribed back into the
design:

- **W6 (`e401cce9`)** — a written free var minted a *fresh quantified* var
  (flexible-mint). SUPERSEDED.
- **W6.2 (`b2bfb760`)** — a written var was a **rigid skolem EVERYWHERE**, bare
  vars included, with a `suppress_rigid_annotations` flag guarding re-checks and
  an eager `lambda_written_vars` poly-as-value escape check. SUPERSEDED — the
  flag and the eager check are both **deleted from the source**; do not describe
  them as live.
- **W6.3 / W6.3.1 (`c3008d1f`, `750471ac`, `eb6c94e6`)** — the SHIPPED hybrid.

### The shipped hybrid (W6.3)

A written type var is treated on one of two paths, chosen by *what* is written:

1. **Bare var = an ordinary FLEXIBLE inference var carrying a display name.**
   `:a` (standing alone or nested in `:(Box a)`) is exactly an inference-generated
   var that survives generalization, plus a name. The name does two things and no
   more (§3.3.1): it **relates same-named occurrences** (lexical co-reference) and
   it **documents** the displayed scheme. It carries **no rigidity and no checking
   obligation** — the body MAY narrow it to a concrete type, and that is **never an
   error** (spec §3.3.5 rows 2, 4, 11; `(defn f [:a x] :a "hello")` is
   `(Fn [String] String)`). Two bare vars tied by the body simply **merge**.

2. **Constraint at a parameter position = held abstract (rigid).** `:C x` where
   `C` names a trait is a checkable claim (§3.3.2). At a quantified position the
   var is **held abstract over `C`** for the body-check; the body narrowing it to
   a concrete type is a **skolem escape** and is rejected (row 6). Rigidity lives
   **only** on this constraint path.

The one asymmetry between the two paths (a bare `:a` narrowed to `Int` is fine,
row 2; a `:Num x` narrowed to `Int` is an error, row 6) is the whole reason the
hybrid exists: a *caller* relies on the constraint, not on the name.

### Realization in the engine

- **`written_var_scope: Option<HashMap<Symbol, TypeId>>` threads LEXICAL
  CO-REFERENCE only** (`CheckState`, `checker.rs`). It is built in Pass-1
  (`register_defn_signature` → the accumulator's per-defn `defn_var_scopes`),
  installed for the body in `check_defn_body` (`program/body.rs`), and **shared —
  never reset — into nested `fn` closures** by `infer_lambda` (`infer.rs`), so a
  body `:a` co-refers with a param `:a` and an inner `(fn [:a y] …)` co-refers
  with the enclosing `a` (§3.3.1, row 8; FIXME 0588). This scope is *all* a bare
  var carries — a name, never rigidity.

- **`rigid_vars: HashSet<TypeId>` holds ONLY asserted-constraint param vars.**
  `check_defn_body` seeds it, per body, from the param `Type::Var`s that **already
  carry a constraint at Pass-2 entry** — i.e. `resolve_bound_param` recorded the
  assertion `:C x` into `state.active_constraints` during Pass-1. A **bare** `:a`
  param that merely *accrues* a `Num` constraint from body use (row 7) is **not**
  seeded: its var has no constraint until body inference runs (after seeding), so
  it stays **flexible** — the inferred-not-asserted distinction that separates row
  7 (accepted, `Num`-polymorphic) from row 6 (rejected, skolem escape). The set is
  scoped to the owning body and torn down on return (save/clear/restore in
  `program/body.rs` and `traits/impl_check.rs`).

- **`unify::unify_with_rigid(subst, rigid, t1, t2)` + `unify_var` are the ONE
  unification seam** (`unify.rs`; `self.unify` at `checker.rs` always threads
  `state.rigid_vars`; the free 3-arg `unify` is a test-only helper). The asymmetry
  is realized entirely in `unify_var`:
  - a **flexible** var MAY bind to a rigid one — *use-acquisition*, sound;
  - a **rigid** var MUST NOT unify with a **concrete type** — *skolem escape*,
    rejected (row 6);
  - **two rigid vars MERGE** (both stay abstract) — `(defn assert-eq [:Eq a :Eq b]
    (= a b))` is a constraint-polymorphic scheme, **not** an error. (The W6.2
    distinct-rigid-escape rule was removed.)

- **Rigidity is TRANSIENT inference state.** `rigid_vars` and `written_var_scope`
  live on `CheckState`, are per-body, and are **never serialized** — a var is
  rigid only for the duration of one body-check. **No `cranelisp-types` type
  carries rigidity**; there is no schema or cache impact from the model.

#### Structural hardening of the rigid-model invariants (FIXME 0595, S111)

Two places where the rigid model's invariants hold **by convention rather than
structurally** (Principle 18). Neither is live-reachable today (`/review` verified
against current construction sites + error flow), so both are *hardening*, not defect
fixes; they ride the typecheck adjacent-carries track opportunistically (0595 item (1)
is two call edits). Design intent:

1. **The `TyConApp` head-binds must route through `unify_var`.** `unify_with_rigid`'s
   two `TyConApp` arms call `bind_var` **directly** on the head id — `unify.rs:112`
   (`TyConApp(f,_)` vs bare-ADT: `bind_var(subst, f_id, ADT(name,[]))`) and `:134`
   (`TyConApp(f1,_)` vs `TyConApp(f2,_)`: `bind_var(subst, f1, Var(f2))`) — bypassing
   the rigid guard on the convention "HKT constructor variables are never written
   skolems". True today (`Type::TyConApp` is built only in HKT trait-sig resolution,
   whose ids are never in `rigid_vars`; the canonical annotation resolver cannot
   produce a lowercase applied head). But `cranelisp_types::apply` rewrites a head id
   along the substitution and `unify_var`'s rigid arm binds flexible vars TO rigid ids,
   so a kind-confused sig (no kind checker prevents a var used both as head and in
   plain position) could smuggle a rigid id into head position, after which `:112`/`:134`
   bind it silently — a skolem **acquire** in the unsound direction. **Fix:** route both
   head-binds through `unify_var` (closes the gap for two call edits); a
   `debug_assert!(!rigid.contains(&f_id))` at each arm is the acceptable minimal
   alternative.

2. **Rigid-state teardown must be Ok-path-only-symmetric.** `check_defn_body`
   (`program.rs` ~`:3311`→`:3335`), `infer_annotate`, and `infer_lambda` install
   `rigid_vars` / `written_var_scope` and restore them only **past the `?`s** — an
   inference error leaves the state polluted. Benign today (every Pass-2 error aborts
   the whole `check_forms` call and `CheckState` is function-local, so leaked state
   dies with the abort), but `traits/impl_check.rs::check_defn_body_with_types` already
   does the closure-capture save/restore correctly, and the asymmetry is a trap for any
   future continue-after-form-error mode. **Fix:** match the `impl_check` discipline —
   a closure or RAII guard that restores on **both** exit paths — at the other three
   sites, making the invariant structural (Principle 18) rather than convention.

No `cranelisp-types` edit, no schema impact; typecheck-internal. Each fix lands with its
unit pin (`/dev`).

### Rank-1 polymorphic returns — no eager check (§3.3.4/§3.10)

A `defn` whose body **defines a rank-1 polymorphic function value** — returned
(`(defn mk [] (fn [:b y] y))`), let-stored-and-returned, passed uninstantiated, or
applied in place — is a legitimate value. The written `:b` is irrelevant: the
written form is the **same thing** as its unwritten twin, and both are accepted
(§3.3.4 MUST (f), row 10). The former eager `lambda_written_vars` free-var escape
check (added `c3008d1f`, refined `750471ac`) over-rejected the written forms while
their unwritten twins compiled; it was **removed at W6.3** and the
`CheckState::lambda_written_vars` field is **gone** — do not re-add it, and
`resolve_annotation_type_expr_in_module` returns just the `Type` (the minted-id
list that fed the removed check is gone).

The genuine rank-2 / value-restriction limits are enforced **elsewhere by the
type system, not by an eager gate**:

- a single poly instance used at two types (`(let [f (mkid)] (f "x") (f 5))`) →
  the value restriction / **unification** (rows 18);
- a poly value passed and used at two types inside a callee → **unification**
  (rank-2 argument, row 19);
- a result-only var held unresolved at a codegen-reaching use (`(zed)` with no
  context, row 16) → the **§3.11 ambiguity gate** (the R16 result-var
  monomorphisation family). Not yet landed as a check — reported to `/sprint` as a
  coordinated seam (needs a "dispatch selected NO impl" signal; the `main` entry
  leg additionally needs the int entry-validation seam, Principle 19).

### Value-position annotations (§3.3.3)

`infer_annotate` handles annotations on a concrete expression. A bare/concrete
annotation (`:a "hello"`, `:Int (zed)`) is a **flexible unify** — the value's type
unifies with the annotation (pins freely / resolves return-type dispatch). A bare
name that resolves as a **trait** (`:Num 5`) is a **satisfaction check only**
(MUST (c)): accepted **iff** the expr's type implements the trait, changing
nothing — it does not disambiguate return-type dispatch. The check discriminates
three cases on the resolved expr type (FIXME 0597): a **nominal concrete** type →
`has_impl_in_home`; a **concrete but non-nominal** type (a `Fn` — implements
nothing, impls are keyed by type name; `concrete_type_name == None`) → **reject**;
still a `Type::Var` → leave the residual for the §3.11 gate.

### Open design note — constraint-path rigidity in trait-impl method bodies

**(Narrow residual from FIXME 0593; fenced, no live unsoundness — fold into the
S110 FIXME-0590 resolver-convergence round.)** 0593's original worry — that a bare
written-var ascription in an impl-method body would "silently acquire" flexibly —
is **obsoleted by W6.3**: a bare var *is* flexible by design, and a body pinning it
is the intended semantics (§3.3.5 row 4), the same in an ordinary defn body and an
impl-method body (no per-variant divergence). The flag the concern hinged on
(`suppress_rigid_annotations`) no longer exists.

`check_defn_body_with_types` (`traits/impl_check.rs`) — the shared helper for
trait-impl method bodies **and** the monomorphise re-check — receives
already-concrete `param_types` and **clears** `rigid_vars` / `written_var_scope`
for the body, so a body-only written var mints a plain flexible var with no
co-reference and no rigidity. The only residual question is narrow: whether a
constraint on a **non-`Self`** type variable carried by a trait-method signature
should be **held abstract (rigid)** inside the impl-method body (an MUST (b) /
§3.3.2 obligation the current concrete-param path does not seed). It is fenced
today by a parse gap — body annotations do not parse inside impl-method defn
bodies (`(impl Doubler Int (defn twice [n] :a "hello"))` → `parse error:
annotation missing expression`, a FIXME-0591-class position gap). The trigger that
would make it live is the parse-gap closure; resolve the constraint-in-impl-body
question and add the impl-method-body row to the §L matrix (`/qa`) at that point.

## Unification

Standard Algorithm W unification with occurs check:

```
unify(Var(a), t)  = if a in fv(t) then OccursCheckError else subst[a] = t
unify(t, Var(a))  = unify(Var(a), t)
unify(Int, Int)   = ok
unify(Fn(ps1, r1), Fn(ps2, r2)) = unify each (p1, p2), then unify(r1, r2)
unify(ADT(n1, as1), ADT(n2, as2)) = if n1 == n2 then unify each (a1, a2)
unify(_, _)       = TypeError
```

The substitution is applied transitively: looking up `Var(a)` follows the chain until a non-var type is found.

## Scheme Operations

**Instantiation**: Replace quantified type variables with fresh variables. Each call to `instantiate` produces a fresh copy, enabling polymorphic use.

**Generalization**: Collect free variables in a type that do NOT appear free in the environment, and quantify over them. Uses the current substitution to resolve the type before collecting.

```
generalize(env, ty) =
  let resolved = apply(subst, ty)
  let env_fv = free_vars_in_env(env)
  let ty_fv = free_vars(resolved) - env_fv
  Scheme { vars: ty_fv, ty: resolved }
```

## Expression Type Recording

Every `infer_*` method calls `record_expr_type(span, ty)` to associate the inferred type with the expression's source span. The `expr_types` map is resolved through the substitution in `build_check_result` / `build_repl_result` before being returned to the caller.

The backend relies on `expr_types` for heap classification (via `HeapCategory::classify`). Missing entries would cause silent codegen bugs.

### Polymorphic Type Variables in expr_types

In Ring 0-1, `expr_types` may contain `Type::Var` entries for expressions inside polymorphic function bodies. For example, `(defn id [x] x)` records `x` with `Type::Var(N)` — this is correct because `x` has a universally quantified type. The invariant that all `Var` entries must be resolved activates in Ring 2 when monomorphisation produces specialized function bodies with fully concrete types.

## Per-Ring Evolution

### Ring 0 (Core)

- Int, Bool, Float literals and arithmetic
- If/else with branch unification
- Let bindings with sequential scope
- Lambda (non-capturing) and function application
- Pattern matching on nullary ADT constructors
- Forward references via two-pass pipeline

### Ring 1 (Heap) — Current

- String literal inference (`Type::String`)
- Full polymorphic ADT registration with data constructor fields
- Constructor pattern matching with field bindings
- `TypeExpr::Applied` resolution with arity validation
- `WarningKind` enum for typed warnings (M-3)
- `#[must_use]` on public API functions (M-5)

### Ring 2 (Abstraction) — Planned

- Trait declarations and implementations
- Constrained polymorphism (monomorphisation)
- Multi-signature functions
- `debug_assert!` for Type::Var-free expr_types (post-monomorphisation)

### Ring 3 (Meta) — Planned

- Module system integration
- Import resolution
- Cross-module type checking
