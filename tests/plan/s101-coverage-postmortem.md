# S101 coverage post-mortem — why existing coverage missed the three Phase-3 finds

**Author:** `/qa` · **Date:** 2026-07-03 · **Status:** Wave-1 deliverable (user scope
amendment, `sprints/SPRINT.md` §Notes 2026-07-03). Peer of
`tests/plan/s100-ownership-verification.md` (whose §6.1 set was drafted in the same
wave); registered in `tests/CLAUDE.md` §Plan documents.

> **Citation freeze (S109, /qa).** File/line citations in this document
> (`program.rs:NNN`, `infer.rs:NNN`, `save.rs:NNN`, …) are evidence frozen at
> S101 HEAD. The S109 FIXME-0580 decomposition splits
> `crates/cranelisp-typecheck/src/program.rs` into submodules (tests →
> `program/tests.rs`, per `design/typecheck/program-decomposition.md`). Do not
> chase the relocation here — this is a historical post-mortem; current seams
> are named in the live design docs and source.

The S101 Phase-3 design pass surfaced three defects/gaps that the existing ~1800-test
suite had never flagged. Each is an instance of a coverage **category**, not a one-off.
This post-mortem records the per-find root cause of the miss, then executes the
category sweeps assigned to `/qa` (categories 1 and 3) and documents + routes category
2 to `/arch` (Wave 5).

---

## §1. Per-find root cause of the coverage miss

### 1.1 The `Def.callees` gap (FIXME 0470)

**The find.** `callees` records only a subset of statically-resolved user-fn
references: it misses fn-as-value references AND plain direct calls in some seams
(`program.rs:690–752`, `infer.rs:585–604` — the fire's §3.1 source evidence). The
S101 transaction needs the complete edge set; the incomplete one silently
under-approximates the affected set.

**Why coverage missed it.** `callees` is **populated by convention and consumed by
degrading consumers**. Its two pre-S101 consumers — `save.rs::dependency_sort`
(`save.rs:816`, emission ordering for `user.cl` regeneration) and the
macro-resolution densification walk (`process_form/macro_resolution.rs`) — treat a
missing edge as "no constraint": `dependency_sort` falls back to `seq` order, the
walk simply doesn't traverse. **An incomplete `callees` produces no wrong output on
any existing path — only a weaker ordering constraint that authorship-order emission
masks.** No test could fail because no observable ever depended on completeness.
There was no completeness contract, and no consumer that *failed* on violation.
The field's own doc comment says "populated by `finalize_check_result()`" — a
mechanism statement, not a contract.

**The general lesson (category 1).** Metadata fields whose consumers degrade
gracefully accumulate silent incompleteness until a NEW consumer arrives that needs
the full contract — at which point the gap is discovered by design review (lucky,
this time) or by production misbehaviour. The cure is a **completeness-contract
test** attached to the field itself, not to any consumer. Sweep: §2.

### 1.2 The `*code = None` in-flight page free (fire §6.3)

**The find.** The Replace/reload paths (`lifecycle.rs:1069–1076`,
`process_form.rs:702–708`) clear compiled code by `*code = None`, with comments
claiming `kept_jits` retains the pages — but `kept_jits` was dissolved in S58
(Decision 35). Today `*code = None` can drop the **last** `Arc<Jit>` and free
machine-code pages that in-flight frames or heap closures can still execute.

**Why coverage missed it.**
1. **Lifetime-across-suspension is invisible to sequential e2e scripts.** Every
   watcher/reload test drives the reload and then observes the *next* call — which
   resolves through the (re-populated) GOT slot to *new* pages. Only a value or frame
   holding a **direct old code pointer across the reload window** dereferences the
   freed pages, and the suite has no fixture that pins a heap closure / in-flight
   strand across a reload (the same cross-turn-value-carrier gap that constrains
   L-R2(a) — see `tests/repl_redefinition.rs` module header).
2. **The guarding comment substituted for a guard.** The `kept_jits` comments made
   the hazard look handled; comment rot (S58 dissolved the mechanism) turned a true
   statement false with no test attached to the claim.
3. **Recurrence lineage (category 2)** — this is the third instance of the class:
   - S97/S98: launched-effect **argument UAF** (`exemplar_web` bug #2 → FIXME 0486
     → BC §4b **invariant 15**: keep-alive at the `EffectPoll`/`reg` seam).
   - S98: the perturbation false-green lesson on the same bug
     (`memory/feedback_verify_fix_not_symptom_absence.md`).
   - S101: `*code = None` frees **code pages** (not heap values) that a suspended
     computation may re-enter — same shape, new resource kind.
   The class is: **a resource's liveness is judged by the live symbol table /
   current turn, while suspended computations (strands, continuations, heap
   closures, in-flight frames) hold references that outlive the judgement.**

**Routing (per the Wave-1 brief).** `/qa` does NOT sweep this category. The ruling —
structural guard / standing principle vs per-instance fixes — is assigned to `/arch`
in Wave 5 (`sprints/SPRINT.md` §Waves), per the
`memory/feedback_review_root_cause_and_duplication` escalation rule (second-plus
recurrence ⇒ arch-level ruling). The S101-instance cure is in-sprint: the retention
pool (fire §6) moves superseded `Code` to `SharedState.retained_code` instead of
`None`-ing it; L-R1/L-R2's sustained legs and the existing
`launch_*_corrupt.rs` fences are the behavioural guards this class currently has.
What `/arch` should weigh for the standing guard: every `Arc`-drop of an
executable-resource handle (`Code`, DLL handles, GOT slabs) flowing through a path
reachable while user code can be suspended.

### 1.3 The NULL-slot fn-as-value SIGSEGV (`tests/vec_query_value_use.rs`)

**The find (S100 triage, extended this wave).** `vec-get`/`vec-set`/`vec-push` have
allocated-but-NULL GOT slots; every **value-position** use compiles to a call
through NULL → SIGSEGV (or a JIT resolution panic, §3.2).

**Why coverage missed it.** The builtin surface was tested almost exclusively in
**direct-call position** — `spec_appendix_a_builtins.rs` calls each primitive
directly, where the vec family is inline-lowered and the NULL slot is never read.
Value-position coverage existed only incidentally (closures over *user* fns,
stdlib HOFs over *stdlib* wrappers). The use-position axis (direct / HOF-arg /
curried / stored / returned) was never treated as a coverage dimension **per builtin
family**, so a family whose registration was position-dependent (real shim vs NULL
slot) could pass 100% of its tests while being un-callable as a value. The
`vec-len` control (green through the identical wrapper) proves the miss was the
family × position cell, not the mechanism. Sweep: §3.

---

## §2. Category 1 sweep — convention-populated metadata with degrading consumers

Audit target: `ModuleEntry::Def` fields + adjacent symbol-table metadata
(`crates/cranelisp-types/src/module.rs`), asking of each: **is there a completeness/
correctness contract, and does any consumer FAIL (vs degrade) when it is violated?**

| Field | Contract status | Consumers on violation | Verdict |
|---|---|---|---|
| `scheme` | **Contracted.** Typecheck output; every call site resolves against it | Wrong scheme ⇒ type errors/wrong inference — loud, e2e-visible | SOUND — self-enforcing |
| `kind` (incl. `got_slot` on callable variants) | **Contracted structurally** (S83/FIXME 0356: callability-by-representation; `callable_got_slot()` single read-through) | Missing slot on a callable kind is unconstructable | SOUND — Principle 20 exemplar |
| `callees` | **CONVENTION (the 0470 find).** Doc says "populated by finalize_check_result" — no completeness statement | `save.rs::dependency_sort` falls back to `seq`; macro-resolution walk silently doesn't traverse; **S101 transaction would silently under-recompile** | **DEFECT-CLASS — contract tests specified below (§2.1)** |
| `ast` | **Semi-contracted.** Decision 22 predicate `ast.is_some()` gates codegen-compilability | Absent-when-owed ⇒ symbol never compiles — loud. But a *stale* ast after redefinition would silently regenerate wrong `user.cl` source | MOSTLY SOUND; staleness leg rides §15.4 round-trip tests (`repl_persist.rs`) |
| `codegen_view` | **Contracted** (concrete-boundary arc: no `Var` representable; backend consumes non-optionally) | Absent ⇒ codegen cannot proceed — loud | SOUND — structural |
| `code` | `#[serde(skip)]`, session-only | `None` when pages still referenced = the §1.2 find — the consumer (a call through a stale pointer) CRASHES rather than degrades, but only across suspension | Category 2 — routed to `/arch` (§1.2) |
| `param_names` | Convention | Introspection/`/info` display degrade to positional display | LOW RISK — display-only; wrongness is user-visible in REPL output already covered by `repl_introspection.rs` |
| `docstring` | Convention (optional by design) | Display omits | NOT A RISK — `Option` is the honest type |
| `trait_origin` | Convention ("None for non-trait-method") | Trait-method introspection/dispatch bookkeeping silently treats as free fn | **WATCH** — same shape as `callees` (degrading consumers) but scope is introspection + save-ordering, not soundness. No new consumer planned; revisit if one arrives (flag in the S102+ QA-first list when increment I touches summaries) |
| `seq` | **Contracted narrowly** (authorship order for regeneration; Decision 39 removed the drift-prone side-table) | Duplicate/missing seq ⇒ emission order wobbles — caught by `repl_persist.rs` §15.4 round-trip tests | SOUND ENOUGH — has behavioural cover |
| `next_got_slot` | **Contracted** (monotone allocator; persisted) | Regression ⇒ slot collisions ⇒ loud corruption; now ALSO pinned by `repl_persist_redefine.rs` L-R5 | SOUND + newly fenced |
| `Expr::Var.resolved_call` / `inferred_type` | **Semi-contracted** (`check.rs`: canonical on the AST; `None` legal pre-check) | Codegen on an unresolved Var errors loudly; but a *mis*-resolved call silently calls the wrong target | Covered behaviourally (wrong target = wrong output in any value test); acceptable |

**Sweep verdict.** One defect-class field (`callees`, cured by 0470 + the contract
tests below), one category-2 member (`code`, routed), one WATCH (`trait_origin`),
the rest sound — mostly because S69–S83 structural work (Principles 18/20) already
converted convention to representation where it mattered most (`got_slot`,
`codegen_view`). The pattern to keep rejecting: **a `Vec`/`Option` field whose
emptiness is both a legal state and an incompleteness state** — that ambiguity is
what made `callees` untestable. Where a field has that shape, either split the
states (as `fn_state` did) or attach a completeness-contract test.

### 2.1 The `callees` completeness-contract tests (SPECIFIED here; land with Wave 2)

Owner: `/dev`(cranelisp-typecheck) unit tier (per `tests/CLAUDE.md` §Two tiers —
the field is crate-internal state; e2e observability arrives only with the L-R3
cascade report, which the §6.1 lanes already pin). To land in the same change-set
as the 0470 resolution:

1. **Positive — every statically-resolved user-fn reference is recorded.** One
   unit test per reference position, each asserting the edge `caller → callee`
   is present in the checked entry's `callees` after `check`:
   (a) direct call `(defn c [x] (callee x))`;
   (b) fn-as-value argument `(defn c [x] (hof callee x))`;
   (c) fn-as-value returned `(defn c [] callee)`;
   (d) fn-as-value stored `(defn c [] [callee])` (container literal);
   (e) curried partial `(defn c [x] ((callee x)))` — partial application site;
   (f) reference inside a nested lambda `(defn c [] (fn [x] (callee x)))`
   (the L-R2 carrier shape — the closure body's edge must attribute to `c`);
   (g) qualified cross-module reference `(defn c [x] (util/callee x))`.
2. **Negative — no spurious edges.** (a) a *shadowed* name (local param named
   `callee`) records NO edge; (b) primitives/special forms record NO user-fn
   edge; (c) a macro USE does not enter `callees` (macro edges ride their own
   channel — `save.rs:617`); (d) `unrelated` fns sharing the module record no
   edge to each other (the L-R3(b) exactness negative at the unit grain).
3. **Uniformity.** All positions record the same `Vec<FQSymbol>` carrier —
   call-position and value-position edges are indistinguishable to consumers
   (the 0470 resolution shape; `sprints/SPRINT.md` FIXME table).
4. **Consumer-audit guards** (gate note 2): `save.rs::dependency_sort` emission
   order unchanged under the denser edge set (existing `repl_persist.rs` §15.4
   round-trips are the e2e cover; `/dev` adds the unit assertion on
   `dependency_sort` directly); `macro_resolution.rs:491` walk terminates and
   does not mid-cluster-compile a not-yet-codegen'd same-module defn.

`/qa`-side: no new e2e is owed for the field itself — L-R3(b)
(`tests/repl_redefinition.rs::redefine_abi_change_cascade_report_names_exact_affected_set`)
is the end-to-end witness that the edge set is complete AND exact (its
positive+negative needles fail on both under- and over-recording).

---

## §3. Category 3 sweep — use-position × builtin-family matrix

**Method.** Cheap probes (one REPL subprocess per cell, primitives-only prelude,
scripts in the session scratchpad; ~25 cells) across the builtin families of
`spec/appendix-a-builtins.md` §A.3 × use positions: HOF-arg, curried partial,
returned-from-fn, stored-in-container (Vec literal + ADT field). Direct-call
position is already densely covered by `spec_appendix_a_builtins.rs` and was not
re-probed. Probe date 2026-07-03, HEAD 0b0e234.

### 3.1 Matrix results

| Family (representatives) | HOF arg | Curried | Returned | Stored (Vec/ADT) |
|---|---|---|---|---|
| int arith (`add-i64`) | PASS | PASS | PASS | PASS (Vec) |
| int compare (`lt-i64`) | PASS | — | — | — |
| bool (`not`) | PASS | — | — | — |
| float arith (`add-f64`) | PASS | — | — | — |
| bitwise (`bit-and`, S91) | PASS | PASS | — | — |
| string (`str-concat`, `str-len`, `substring`) | PASS | PASS | PASS | — |
| conversion (`int-to-string`) | PASS | — | — | — |
| parse (`parse-int` → Option) | PASS | — | — | — |
| **vec query (`vec-get`)** | **SIGSEGV** (S100 guard) | **PANIC exit 101** (NEW) | **SIGSEGV** (NEW) | **SIGSEGV** (NEW, ADT) |
| **vec query (`vec-set`,`vec-push`)** | **SIGSEGV** (S100 guards) | **PANIC exit 101** (probed; same signature as vec-get — one guard per position suffices) | not probed (same class) | not probed (same class) |
| vec query (`vec-len`, control) | PASS | n/a (arity 1 — a 1-arg application is already saturated) | PASS (via S100 control) | — |
| ctor (`Pure`) | PASS | — | — | — |
| host-promised (`catch-runtime-error`) | PASS | — | — | — |
| user fns + user ADT ctors (baseline) | PASS (whole suite) | PASS | PASS | PASS (ADT probe `adt_stored_fn`) |

**Defects found: the NULL-slot class widens to three more use positions — no NEW
root cause.** Every failing cell traces to the same `insert_vec_query_entries`
NULL slots (S100 triage, qa plan §7). New information for the resolver
(`/backend`, sprint item 1(a)):

- **Curried partials die EARLIER and DIFFERENTLY**: Rust panic
  `can't resolve symbol vec-get` (cranelift-jit `backend.rs:345`, exit 101) when
  the curry wrapper is JIT-compiled — confirming the `/design`(backend) §12.7
  touch-up finding that the vec family is absent from `primitives_inline`, so the
  auto-curry fallback doesn't cover it either. Two failure signatures, one cure.
- Returned-from-fn and stored-in-ADT reach the classic NULL-slot SIGSEGV.

**Tests added (failing-not-ignored, `tests/vec_query_value_use.rs`):**
`vec_get_curried_partial_applies`, `vec_get_returned_from_fn_applies`,
`vec_get_stored_in_adt_field_applies` — one guard per new position on the family
exemplar (the HOF trio already pins the per-member boundary; duplicating all
three members × all positions would add 6 more guards with zero new information).
Ledger: `tests/plan/ledger.md` §"Sprint 101 Wave-1 cat-3 sweep". These join the
qa-plan §7.1 flip protocol: the Wave-3 fix must flip **7** vec-query guards, and
the §7.1 count/wording is superseded accordingly (4 → 7 RED; control unchanged).

### 3.2 What was NOT probed (no silent caps)

- **Platform-DLL effect families** (web/stdio/test-capture effects as values):
  platform effects are `DefKind::PlatformEffect` (non-callable-kind, no slot) and
  the S97/S98 launched-strand corruption work already owns that seam's fences
  (`launch_*_corrupt.rs`); value-use of platform effects is exercised by the
  concurrency suites. Not re-probed here.
- **Macro-phase builtins** (`quote-sexp` in macro bodies) — different phase,
  different machinery; macro coverage rides `spec_09_macros.rs`.
- **`--link` mode** for the new positions — the S100 run-mode guard
  (`vec_get_as_value_run_mode_returns_element`) already pins mode-divergence for
  the class; per-position × per-mode enumeration adds cells without new
  signal. The suite-polarity + L-B2(ii) byte-differential lanes (increment I)
  will sweep modes wholesale.
- **Full member × position enumeration** within failing families — bounded as
  described above (exemplar per position once the root cause is proven shared by
  signature probing).
- **`discover-tests`** as a value — host-promised extern with session-supplied
  body; its own §16 lanes cover discovery; value-use of it is an exotic cell
  with no user story yet (record: untested, accepted).

### 3.3 Standing rule fed back into QA practice

New builtin families (and new REGISTRATION KINDS of existing families — extern
shim vs inline-lowered vs host-promised vs NULL-by-design) get a **value-use row**
in their QA-first drafting list: HOF-arg + curried at minimum, on one family
exemplar. The `vec-len` vs `vec-get` split proves registration kind — not the
language mechanism — is the failure axis, so coverage must key on it.
`tests/plan/PLAN.md` gains this as a drafting-checklist item at its next touch.

---

## §4. Summary of actions

| Category | Action | Where |
|---|---|---|
| 1 (`callees`) | Field inventory done (§2); completeness-contract tests SPECIFIED for Wave 2 `/dev`(typecheck) same-change-set landing | §2.1 |
| 1 (`trait_origin`) | WATCH recorded — revisit when a non-display consumer arrives | §2 table |
| 2 (`*code = None` / lifetime-across-suspension) | Lineage documented (§1.2); ruling routed to `/arch` Wave 5 (already in the sprint plan); NOT swept by `/qa` | §1.2 |
| 3 (NULL-slot class) | Matrix swept (§3.1); 3 new failing-not-ignored guards added; flip protocol widened 4→7; not-probed list recorded (§3.2); standing drafting rule (§3.3) | `tests/vec_query_value_use.rs`, ledger |
